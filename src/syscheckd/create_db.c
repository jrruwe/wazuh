/* Copyright (C) 2015-2019, Wazuh Inc.
 * Copyright (C) 2009 Trend Micro Inc.
 * All right reserved.
 *
 * This program is a free software; you can redistribute it
 * and/or modify it under the terms of the GNU General Public
 * License (version 2) as published by the FSF - Free Software
 * Foundation
 */

#include "shared.h"
#include "syscheck_op.h"
#include "wazuh_modules/wmodules.h"
#include "os_crypto/sha1/sha1_op.h"
#include "os_crypto/sha256/sha256_op.h"
#include "syscheck.h"
#include "syscheck_op.h"

/* Prototypes */
static int read_file(const char *dir_name, const char *linked_file, int dir_position, whodata_evt *evt, int max_depth, char silent)  __attribute__((nonnull(1)));

static int read_dir_diff(char *dir_name);

static void print_file_info(const char * path, struct stat path_stat);
static int type_file(const char *path);
fim_data * fim_get_data (const char * file_name, struct stat file_stat);
char * fim_get_checksum (fim_data * data);
static int fim_insert ();
static int fim_delete (const char *file_name);



pthread_mutex_t lastcheck_mutex = PTHREAD_MUTEX_INITIALIZER;

/* Global variables */
static int __counter = 0;

static int read_dir_diff(char *dir_name) {
    size_t dir_size;
    char *f_name = NULL;
    char *file_name = NULL;
    char *local_dir = NULL;
    int retval = -1;

    os_calloc(PATH_MAX + 2, sizeof(char), f_name);
    os_calloc(PATH_MAX, sizeof(char), file_name);
    os_calloc(PATH_MAX, sizeof(char), local_dir);

    snprintf(local_dir, PATH_MAX - 1, "%s%clocal", DIFF_DIR_PATH, PATH_SEP);

    DIR *dp;
    struct dirent *entry;

    /* Directory should be valid */
    if ((dir_name == NULL) || ((dir_size = strlen(dir_name)) > PATH_MAX)) {
        merror(NULL_ERROR);
        goto end;
    }

    /* Open the directory given */
    dp = opendir(dir_name);
    if (!dp) {
        if (errno == ENOTDIR || (errno == ENOENT && !strcmp(dir_name, local_dir))) {
            retval = 0;
            goto end;
        } else {
            mwarn(FIM_WARN_ACCESS, dir_name, errno, strerror(errno));
            goto end;
        }
    }

    int ret_add;
    while ((entry = readdir(dp)) != NULL) {
        char *s_name;

        /* Ignore . and ..  */
        if ((strcmp(entry->d_name, ".") == 0) ||
            (strcmp(entry->d_name, "..") == 0)) {
            continue;
        }

        strncpy(f_name, dir_name, PATH_MAX);
        s_name = f_name;
        s_name += dir_size;

        /* Check if the file name is already null terminated */
        if (*(s_name - 1) != PATH_SEP) {
            *s_name++ = PATH_SEP;
        }

        *s_name = '\0';
        strncpy(s_name, entry->d_name, PATH_MAX - dir_size - 2);

        if (strcmp(DIFF_GZ_FILE, s_name) == 0) {
            memset(file_name, 0, strlen(file_name));
            memmove(file_name, f_name, strlen(f_name) - strlen(s_name) - 1);
            if (ret_add = OSHash_Add(syscheck.local_hash, file_name, NULL), ret_add != 2) {
                merror(FIM_ERROR_ADD_FILE, file_name);
            }
        } else {
            read_dir_diff(f_name);
        }
    }

    closedir(dp);
    retval = 0;
end:
    free(f_name);
    free(file_name);
    free(local_dir);
    return retval;
}


void remove_local_diff(){

    /* Fill hash table with the content of DIFF_DIR_PATH/local */
    const char LOCALDIR[] = {PATH_SEP, 'l', 'o', 'c', 'a', 'l', '\0'};
    char *local_path = NULL;
    os_calloc(PATH_MAX, sizeof(char), local_path);

    strcpy(local_path, DIFF_DIR_PATH);
    strcat(local_path, LOCALDIR);

    read_dir_diff(local_path);

    unsigned int i = 0;

    /* Delete all monitored files from hash table */
    OSHashNode *curr_node_local, *internal_node;
    OSHashNode *curr_node_fp;

    char *full_path = NULL;
    os_calloc(OS_SIZE_8192, sizeof(char), full_path);

    w_rwlock_rdlock((pthread_rwlock_t *)&syscheck.fp->mutex);
    for (i = 0; i <= syscheck.fp->rows; i++) {
        curr_node_fp = syscheck.fp->table[i];
        if (curr_node_fp && curr_node_fp->key) {
            do {
                *full_path='\0';
                wm_strcat(&full_path, local_path, '\0');
#ifdef WIN32
                char *windows_path;
                windows_path = strchr(curr_node_fp->key, ':');
                wm_strcat(&full_path, windows_path+1, '\0');
#else
                wm_strcat(&full_path, curr_node_fp->key, '\0');
#endif
                if (!OSHash_Get_ex(syscheck.local_hash, full_path)) {
                    mdebug2(FIM_LOCALDIFF_DELETE, full_path);
                    OSHash_Delete_ex(syscheck.local_hash, full_path);
                }
                curr_node_fp=curr_node_fp->next;
            } while(curr_node_fp && curr_node_fp->key);
        }
    }
    w_rwlock_unlock((pthread_rwlock_t *)&syscheck.fp->mutex);
    free(full_path);

    /* Delete local files that aren't monitored */
    for (i = 0; i <= syscheck.local_hash->rows; i++) {
        curr_node_local = syscheck.local_hash->table[i];
        if (curr_node_local && curr_node_local->key) {
            do{
                internal_node = curr_node_local->next;
                mdebug2(FIM_LOCAL_DIFF_DELETE, curr_node_local->key);
                if (rmdir_ex(curr_node_local->key) != 0) {
                    mwarn(FIM_WARN_DELETE, curr_node_local->key);
                }
                remove_empty_folders(curr_node_local->key);
                if (OSHash_Delete_ex(syscheck.local_hash, curr_node_local->key) != 0) {
                    mwarn(FIM_WARN_DELETE_HASH_TABLE, curr_node_local->key);
                }
                curr_node_local = internal_node;
            }
            while(curr_node_local && curr_node_local->key);
        }
    }

    free(local_path);
}

/* Read and generate the integrity data of a file */
static int read_file(const char *file_name, const char *linked_file, int dir_position, whodata_evt *evt, int max_depth, char silent)
{
    syscheck_node *s_node;
    OSMatch *restriction;
    fim_data * data;
    struct stat statbuf;
    int opts;
    char *wd_sum = NULL;
    char *alert_msg = NULL;
    char *esc_linked_file = NULL;
    char *c_sum = NULL;

    os_calloc(OS_SIZE_6144 + 1, sizeof(char), wd_sum);
    opts = syscheck.opts[dir_position];

#ifdef WIN32
        int di = 0;
        char *(defaultfilesn[]) = {
            "C:\\autoexec.bat",
            "C:\\config.sys",
            "C:\\WINDOWS/System32/eventcreate.exe",
            "C:\\WINDOWS/System32/eventtriggers.exe",
            "C:\\WINDOWS/System32/tlntsvr.exe",
            "C:\\WINDOWS/System32/Tasks",
            NULL
        };

        while (defaultfilesn[di] != NULL) {
            if (strcmp(defaultfilesn[di], dir_name) == 0) {
                mdebug1("File ignored by defaultfilesn: '%s'", dir_name);
                return 0;
            }
            di++;
        }
#endif

    if (fim_check_ignore(linked_file ? linked_file : file_name) == 1) {
        os_free(wd_sum);
        return (0);
    }

    restriction = syscheck.filerestrict[dir_position];
    if (fim_check_restrict (file_name, restriction) == 1) {
        mdebug1(FIM_FILE_IGNORE_RESTRICT, file_name);
        os_free(wd_sum);
        os_free(alert_msg);
        free(esc_linked_file);
        return (0);
    }

    if (linked_file) {
        esc_linked_file = escape_syscheck_field((char *) linked_file);
    }

    if (w_stat(file_name, statbuf) < 0) {
        fim_delete (file_name);
        return (0);
    }

    data = fim_get_data(file_name, statbuf);
    if (s_node = (syscheck_node *) OSHash_Get_ex(syscheck.fp, file_name), !s_node) {
        __counter++;
    } else {
        mdebug1(FIM_SCANNING_IRREGFILE, linked_file ? linked_file : file_name);
    }

    os_free(esc_linked_file);
    os_free(wd_sum);
    os_free(alert_msg);
    os_free(c_sum);

    return 0;
}

int read_dir(const char *dir_name, const char *link, int dir_position, whodata_evt *evt, int max_depth, __attribute__((unused))unsigned int is_link, char silent)
{
    DIR *dp;
    struct dirent *entry;
    char *f_name;
    char linked_read_file[PATH_MAX + 1] = {'\0'};
    int opts;
    size_t dir_size;
    short is_nfs;

    minfo("=====================================");
    minfo("~~ read_dir: '%s'", dir_name);

    if (!dir_name) {
        merror(NULL_ERROR);
        return OS_INVALID;
    }

    if(max_depth < 0) {
        mdebug1(FIM_MAX_RECURSION_LEVEL, dir_name);
        return 0;
    }

#ifdef WIN32
    // Check if file is in Windows trash
    if (check_removed_file(dir_name)) {
        mdebug2(FIM_DISCARD_RECYCLEBIN, dir_name);
        return 0;
    }
#endif

    // 3.8 - We can't follow symlinks in Windows
#ifndef WIN32
    if (is_link) {
        switch(read_links(dir_name, dir_position, max_depth, is_link)) {
        case 2:
            mdebug1(FIM_SYMBOLIC_LINK_DISCARDED, dir_name);
            return 0;
        case 0:
            mdebug1(FIM_SYMBOLIC_LINK_ADD, dir_name);
            return 0;
        }
    }
#endif

    opts = syscheck.opts[dir_position];

    /* Directory should be valid */
    if (dir_size = strlen(dir_name), dir_size > PATH_MAX) {
        mdebug1(FIM_PATH_EXEED_MAX, PATH_MAX, dir_name);
        return (-1);
    }

    /* Open the directory given */
    dp = opendir(dir_name);

    /* Should we check for NFS? */
    if (syscheck.skip_nfs && dp) {
        is_nfs = IsNFS(dir_name);
        if (is_nfs != 0) {
            // Error will be -1, and 1 means skipped
            closedir(dp);
            return (is_nfs);
        }
    }

    if (!dp) {
        if (errno == ENOTDIR || errno == ENOENT) {
            //if (read_file(dir_name, link, dir_position, evt, max_depth, silent) == 0) {
            //    return (0);
            //}
            minfo("~~ Call to read file !dp: '%s'", dir_name);
            return (0);
        }
        mdebug1(FIM_PATH_NOT_OPEN, dir_name, strerror(errno));
        return (-1);
    }

    /* Check for real time flag */
    if (opts & CHECK_REALTIME || opts & CHECK_WHODATA) {
#if defined INOTIFY_ENABLED || defined WIN32
        realtime_adddir(dir_name, opts & CHECK_WHODATA);
#else
        mwarn(FIM_WARN_REALTIME_UNSUPPORTED, dir_name);
#endif
    }

    os_calloc(PATH_MAX + 2, sizeof(char), f_name);
    while ((entry = readdir(dp)) != NULL) {
        char *s_name;
        *linked_read_file = '\0';

        /* Ignore . and ..  */
        if ((strcmp(entry->d_name, ".") == 0) ||
                (strcmp(entry->d_name, "..") == 0)) {
            continue;
        }

        strncpy(f_name, dir_name, PATH_MAX);
        s_name =  f_name;
        s_name += dir_size;

        /* Check if the file name is already null terminated */
#ifdef WIN32
        if (*(s_name - 1) != '\\') {
            *s_name++ = '\\';
        }
#else
        if (*(s_name - 1) != '/') {
            *s_name++ = '/';
        }
#endif

        *s_name = '\0';
        strncpy(s_name, entry->d_name, PATH_MAX - dir_size - 2);

#ifdef WIN32
        str_lowercase(f_name);
#endif
        /* Check integrity of the file */

        if (syscheck.converted_links[dir_position]) {
            replace_linked_path(f_name, dir_position, linked_read_file);
        }

        switch(type_file(f_name) & S_IFMT) {
        case S_IFREG:
            minfo("~~ Call to read file rec: '%s'", dir_name);
            //read_file(f_name, *linked_read_file ? linked_read_file : NULL, dir_position, evt, max_depth, silent);
            break;
        case S_IFDIR:
            read_dir(f_name, *linked_read_file ? linked_read_file : NULL, dir_position, evt, max_depth-1, 0, silent);
            break;
        case S_IFLNK:
            minfo("~~ Call to read file link: '%s'", dir_name);
            //read_file(f_name, *linked_read_file ? linked_read_file : NULL, dir_position, evt, max_depth, silent);
            if (opts & CHECK_FOLLOW) {
                read_dir(f_name, *linked_read_file ? linked_read_file : NULL, dir_position, evt, max_depth-1, 0, silent);
            }
            break;
        }
        //read_file(f_name, *linked_read_file ? linked_read_file : NULL, dir_position, evt, max_depth, silent);
    }

    os_free(f_name);
    closedir(dp);
    return (0);
}

int run_dbcheck()
{
    unsigned int i = 0;
    char *alert_msg = NULL;
    OSHash *last_backup;
    int pos;

    os_calloc(OS_SIZE_6144, sizeof(char), alert_msg);

    __counter = 0;
    while (syscheck.dir[i] != NULL) {
        char *clink;
#ifdef WIN_WHODATA
        if (syscheck.wdata.dirs_status[i].status & WD_CHECK_REALTIME) {
            // At this point the directories in whodata mode that have been deconfigured are added to realtime
            syscheck.wdata.dirs_status[i].status &= ~WD_CHECK_REALTIME;
            if (realtime_adddir(syscheck.dir[i], 0) != 1) {
                merror(FIM_ERROR_REALTIME_ADDDIR_FAILED, syscheck.dir[i]);
            } else {
                mdebug1(FIM_REALTIME_MONITORING, syscheck.dir[i]);
            }
        }
#endif
        clink = get_converted_link_path(i);
        read_dir(clink ? clink : syscheck.dir[i], clink ? syscheck.dir[i] : NULL, i, NULL, syscheck.recursion_level[i], 0, '-');
        free(clink);
        i++;
    }

    if (syscheck.dir[0]) {
        char linked_file[PATH_MAX + 1];
        // Check for deleted files
        w_mutex_lock(&lastcheck_mutex);
        last_backup = syscheck.last_check;

        // Prepare last_check for next scan
        syscheck.last_check = OSHash_Duplicate_ex(syscheck.fp);
        w_mutex_unlock(&lastcheck_mutex);

        // Send messages for deleted files
        OSHashNode *curr_node;
        unsigned int *i;

        os_calloc(1, sizeof(unsigned int), i);

        for (curr_node = OSHash_Begin(last_backup, i); curr_node && curr_node->data; curr_node = OSHash_Next(last_backup, i, curr_node)) {
            char *esc_linked_file = NULL;
            if (pos = find_dir_pos(curr_node->key, 1, 0, 0), pos >= 0) {
                *linked_file = '\0';
                if (syscheck.converted_links[pos]) {
                    replace_linked_path(curr_node->key, pos, linked_file);
                }

                if (*linked_file) {
                    esc_linked_file = escape_syscheck_field((char *) linked_file);
                }

                mdebug1(FIM_FILE_MSG_DELETE, curr_node->key);
                snprintf(alert_msg, OS_SIZE_6144 - 1, "-1!:::::::::::%s:%s: %s", syscheck.tag[pos] ? syscheck.tag[pos] : "", esc_linked_file ? esc_linked_file : "", curr_node->key);
                free(esc_linked_file);
                send_syscheck_msg(alert_msg);
            }

#ifndef WIN32
            fim_delete_hashes(strdup(curr_node->key));
#endif
            OSHash_Delete_ex(syscheck.last_check, curr_node->key);
        }
        os_free(i);

        last_backup->free_data_function = NULL;
        OSHash_Free(last_backup);

        // Check and delete backup local/diff
        remove_local_diff();
    }

    free(alert_msg);

    return (0);
}

int create_db()
{
    int i = 0;
    char sym_link_thread = 0;

    if (!syscheck.fp) {
        merror_exit(FIM_CRITICAL_ERROR_DB);
    }

    if (!OSHash_setSize_ex(syscheck.fp, 2048)) {
        merror(LIST_ERROR);
        return (0);
    }
    if (!OSHash_setSize(syscheck.local_hash, 2048)) {
        merror(LIST_ERROR);
        return (0);
    }
#ifndef WIN32
    if (!OSHash_setSize(syscheck.inode_hash, 2048)) {
        merror(LIST_ERROR);
        return (0);
    }
#endif

    if ((syscheck.dir == NULL) || (syscheck.dir[0] == NULL)) {
        merror(FIM_ERROR_NOTHING_TOCKECK);
        return (-1);
    }

    /* Read all available directories */
    __counter = 0;
    do {
        char *clink = get_converted_link_path(i);

        if (syscheck.converted_links[i]) {
            sym_link_thread = 1;
        }

        if (read_dir(clink ? clink : syscheck.dir[i], clink ? syscheck.dir[i] : NULL, i, NULL, syscheck.recursion_level[i], 0, '-') == 0) {
            mdebug2(FIM_FREQUENCY_DIRECTORY, syscheck.dir[i]);
        }
        free(clink);
#ifdef WIN32
        if (syscheck.opts[i] & CHECK_WHODATA) {
#ifdef WIN_WHODATA
            realtime_adddir(syscheck.dir[i], i + 1);
            if (!syscheck.wdata.whodata_setup) {
                syscheck.wdata.whodata_setup = 1;
            }
#endif
        } else if (syscheck.opts[i] & CHECK_REALTIME) {
            realtime_adddir(syscheck.dir[i], 0);
        }
#else
#ifndef INOTIFY_ENABLED
        // Realtime mode on Linux requires inotify
        if (syscheck.opts[i] & CHECK_REALTIME) {
            mwarn(FIM_WARN_REALTIME_UNSUPPORTED, syscheck.dir[i]);
        }
#endif
#endif
        i++;
    } while (syscheck.dir[i] != NULL);

    remove_local_diff();

    w_mutex_lock(&lastcheck_mutex);
    OSHash_Free(syscheck.last_check);
    /* Duplicate hash table to check for deleted files */
    syscheck.last_check = OSHash_Duplicate(syscheck.fp);
    w_mutex_unlock(&lastcheck_mutex);

    if (sym_link_thread) {
        symlink_checker_init();
    }

    return (0);
}

int extract_whodata_sum(whodata_evt *evt, char *wd_sum, int size) {
    int retval = 0;

#ifndef WIN_WHODATA
    if (!evt) {
#else
    if (!evt || evt->scan_directory) {
#endif
        if (snprintf(wd_sum, size, "::::::::::") >= size) {
            retval = 1;
        }
    } else {
        char *process_esc = NULL;
        char *name_esc = evt->user_name;
        char *esc_it = NULL;

        // Escape process
        esc_it = wstr_replace(evt->process_name, ":", "\\:");
        process_esc = wstr_replace(esc_it, " ", "\\ ");

#ifdef WIN32
        // Only Windows agents can have spaces in their names
        name_esc = wstr_replace(evt->user_name, " ", "\\ ");
#endif
        if (snprintf(wd_sum, size, "%s:%s:%s:%s:%s:%s:%s:%s:%s:%i:%lli",
                (evt->user_id)?evt->user_id:"",
                (name_esc)?name_esc:"",
                (evt->group_id)?evt->group_id:"",
                (evt->group_name)?evt->group_name:"",
                (process_esc)?process_esc:"",
                (evt->audit_uid)?evt->audit_uid:"",
                (evt->audit_name)?evt->audit_name:"",
                (evt->effective_uid)?evt->effective_uid:"",
                (evt->effective_name)?evt->effective_name:"",
                evt->ppid,
                (long long unsigned int) evt->process_id
            ) >= size) {
            retval = 1;
            snprintf(wd_sum, size, "::::::::::");
        }

#ifdef WIN32
        free(name_esc);
#endif
        free(process_esc);
        free(esc_it);
    }
    return retval;
}

int fim_check_ignore (const char *file_name) {
    /* Check if the file should be ignored */
    if (syscheck.ignore) {
        int i = 0;
        while (syscheck.ignore[i] != NULL) {
            if (strncasecmp(syscheck.ignore[i], file_name, strlen(syscheck.ignore[i])) == 0) {
                mdebug1(FIM_IGNORE_ENTRY, "file", file_name, syscheck.ignore[i]);
                return (1);
            }
            i++;
        }
    }

    /* Check in the regex entry */
    if (syscheck.ignore_regex) {
        int i = 0;
        while (syscheck.ignore_regex[i] != NULL) {
            if (OSMatch_Execute(file_name, strlen(file_name), syscheck.ignore_regex[i])) {
                mdebug1(FIM_IGNORE_SREGEX, "file", file_name, syscheck.ignore_regex[i]->raw);
                return (1);
            }
            i++;
        }
    }

    return (0);
}

int fim_check_restrict (const char *file_name, OSMatch *restriction) {
    /* Restrict file types */
    if (restriction) {
        if (!OSMatch_Execute(file_name, strlen(file_name), restriction)) {
            return (1);
        }
    }

    return (0);
}

#ifndef WIN32
// Only Linux follow symlinks
int read_links(const char *dir_name, int dir_position, int max_depth, unsigned int is_link) {
    char *dir_name_full;
    char *real_path;
    int opts;

    os_calloc(PATH_MAX + 2, sizeof(char), real_path);
    os_calloc(PATH_MAX + 2, sizeof(char), dir_name_full);

    if (realpath(dir_name, real_path) == NULL) {
        mdebug1(FIM_CHECK_LINK_REALPATH, dir_name);
        free(real_path);
        free(dir_name_full);
        return -1;
    }
    strcat(real_path, "/");
    opts = syscheck.opts[dir_position];

    unsigned int i = 0;
    while (syscheck.dir[i] != NULL) {
        strncpy(dir_name_full, syscheck.dir[i], PATH_MAX);
        strcat(dir_name_full, "/");
            if (strstr(real_path, dir_name_full) != NULL) {
                free(real_path);
                free(dir_name_full);
                return 2;
        }
        i++;
    }
    real_path[strlen(real_path) - 1] = '\0';
    if(syscheck.filerestrict[dir_position]) {
        dump_syscheck_entry(&syscheck,
                            real_path,
                            opts,
                            0,
                            syscheck.filerestrict[dir_position]->raw,
                            max_depth, syscheck.tag[dir_position],
                            -1);
    } else {
        dump_syscheck_entry(&syscheck,
                            real_path,
                            opts,
                            0,
                            NULL,
                            max_depth, syscheck.tag[dir_position],
                            -1);
    }
    /* Check for real time flag */
    if (opts & CHECK_REALTIME || opts & CHECK_WHODATA) {
#ifdef INOTIFY_ENABLED
        realtime_adddir(real_path, opts & CHECK_WHODATA);
#else
        mwarn(FIM_WARN_REALTIME_UNSUPPORTED, dir_name);
#endif
    }

    free(real_path);
    free(dir_name_full);
    return 0;
}

int fim_delete_hashes(char *file_name) {
    char *checksum_inode;
    char *inode_str;
    char *w_inode;
    OSHashNode *s_inode;
    char * inode_path;
    syscheck_node *data;

    if (data = OSHash_Delete_ex(syscheck.fp, file_name), data) {
        os_strdup(data->checksum, checksum_inode);

        if(inode_str = get_attr_from_checksum(checksum_inode, SK_INODE), !inode_str || *inode_str == '\0') {
            unsigned int *inode_it;
            os_calloc(1, sizeof(unsigned int), inode_it);

            //Looking for inode if check_inode = no
            for (s_inode = OSHash_Begin(syscheck.inode_hash, inode_it); s_inode && s_inode->data; s_inode = OSHash_Next(syscheck.inode_hash, inode_it, s_inode)) {
                if(!strcmp(s_inode->data, file_name)){
                    inode_str = s_inode->key;
                    break;
                }
            }
            os_free(inode_it);
        }

        if(inode_str) {
            if (inode_path = OSHash_Get_ex(syscheck.inode_hash, inode_str), inode_path) {
                if(!strcmp(inode_path, file_name)) {
                    if (w_inode = OSHash_Delete_ex(syscheck.inode_hash, inode_str), w_inode) {
                        os_free(w_inode);
                    }
                }
            }
        }

        os_free(checksum_inode);
        os_free(data->checksum);
        os_free(data);
    }
    os_free(file_name);

    return 0;
}

#endif

void replace_linked_path(const char *file_name, int dir_position, char *linked_file) {
    char *dir_path;
    char *real_path;
    size_t dir_size;
    size_t real_size;

    w_rwlock_rdlock((pthread_rwlock_t *)&syscheck.fp->mutex);

    dir_size = strlen(syscheck.dir[dir_position]) + 1;
    real_size = strlen(syscheck.converted_links[dir_position]) + 1;

    os_calloc(dir_size + 2, sizeof(char), dir_path);
    os_calloc(real_size + 2, sizeof(char), real_path);

    snprintf(dir_path, dir_size + 1, "%s/", syscheck.dir[dir_position]);
    snprintf(real_path, real_size + 1, "%s/", syscheck.converted_links[dir_position]);

    w_rwlock_unlock((pthread_rwlock_t *)&syscheck.fp->mutex);

    if (!strncmp(real_path, file_name, real_size)) {
        snprintf(linked_file, PATH_MAX, "%s%s", dir_path, file_name + real_size);
        mdebug2(FIM_WHODATA_REPLACELINK, file_name, linked_file);
    }

    free(dir_path);
    free(real_path);
}

char *get_converted_link_path(int position) {
    char *linked_dir = NULL;

    if (syscheck.converted_links[position]) {
        w_rwlock_rdlock((pthread_rwlock_t *)&syscheck.fp->mutex);
        os_strdup(syscheck.converted_links[position], linked_dir);
        w_rwlock_unlock((pthread_rwlock_t *)&syscheck.fp->mutex);
    }
    return linked_dir;
}

static int type_file(const char *path) {
    struct stat path_stat;

    lstat(path, &path_stat);
    print_file_info(path, path_stat);

    return (path_stat.st_mode);
}

static void print_file_info(const char * path, struct stat path_stat) {
    minfo("-------------------------------------");
    minfo("File: %s", path);
    minfo("Nº hard links: %d", (int)path_stat.st_nlink);
    switch(path_stat.st_mode & S_IFMT) {
    case S_IFBLK:
        minfo("Block special.");
        break;
    case S_IFCHR:
        minfo("Character special.");
        break;
    case S_IFIFO:
        minfo("FIFO special.");
        break;
    case S_IFREG:
        minfo("Regular.");
        break;
    case S_IFDIR:
        minfo("Directory.");
        break;
    case S_IFLNK:
        minfo("Symbolic link.");
        break;
    case S_IFSOCK:
        minfo("Socket.");
        break;
    default:
        minfo("I dont know");
    }
}

// Get data from file
fim_data * fim_get_data (const char * file_name, struct stat file_stat) {
    fim_data * data = NULL;
    int size_name;
    int size_group;

    os_calloc(1, sizeof(fim_data), data);

    size_name = sizeof(get_user(file_name, file_stat.st_uid, NULL)) + 1;
    size_group = sizeof(get_group(file_stat.st_gid)) + 1;
    os_calloc(size_name, sizeof(char), data->user_name);
    os_calloc(size_group, sizeof(char), data->group_name);

    *(data)->hash_md5 = '\0';
    *(data)->hash_sha1 = '\0';
    *(data)->hash_sha256 = '\0';

    data->size = file_stat.st_size;
    data->perm = file_stat.st_mode;
    data->uid = file_stat.st_uid;
    data->gid = file_stat.st_gid;
    data->mtime = file_stat.st_mtime;
    data->inode = file_stat.st_ino;

    snprintf(data->user_name, size_name, "%s", get_user(file_name, file_stat.st_uid, NULL));
    snprintf(data->group_name, size_group, "%s", get_group(file_stat.st_gid));

    if (S_ISREG(file_stat.st_mode)) {
        if (OS_MD5_SHA1_SHA256_File(file_name,
                                    syscheck.prefilter_cmd,
                                    data->hash_md5,
                                    data->hash_sha1,
                                    data->hash_sha256,
                                    OS_BINARY,
                                    syscheck.file_max_size) < 0) {
            mdebug1("Couldn't generate hashes: '%s'", file_name);
            return NULL;
        }
    } else {
        mdebug1("No hashes in symbolic links: '%s'", file_name);
    }

    return data;
}

char * fim_get_checksum (fim_data * data) {
    char *checksum;
    int size;

    os_calloc(OS_SIZE_128, sizeof(char), checksum);

    size = snprintf(checksum,
            OS_SIZE_128,
            "%lu%lu%lu%lu%s%s%lu%lu%s%s%s", 
            data->size,
            data->perm,
            data->uid,
            data->gid,
            data->user_name,
            data->group_name,
            data->mtime,
            data->inode,
            data->hash_sha1,
            data->hash_sha256);

    if (size < 0) {
        merror("Error returned by snprintf()");
        return NULL;
    } else if (size < OS_SIZE_128) {
        return checksum;
    }

    // Need more space
    os_realloc(checksum, size + 1, checksum);
    snprintf(checksum, OS_SIZE_128, checksum);

    return checksum;
}

// Inserts a file in the syscheck hash table structure
static int fim_insert () {

    return 0;
}

// Deletes a path from the syscheck hash table structure and sends a deletion event
static int fim_delete (const char *file_name) {

//    os_calloc(OS_SIZE_6144, sizeof(char), alert_msg);

//    switch (errno) {
//    case ENOENT:
//        mdebug2(FIM_CANNOT_ACCESS_FILE, file_name);
//        /* Fallthrough */

//    case ENOTDIR:
//        /*Deletion message sending*/
//        mdebug1(FIM_FILE_MSG_DELETE, file_name);

//        snprintf(alert_msg, OS_SIZE_6144, "-1!:::::::::::%s:%s:%c %s", syscheck.tag[dir_position] ? syscheck.tag[dir_position] : "", esc_linked_file ? esc_linked_file : "", silent, file_name);
//        send_syscheck_msg(alert_msg);
//#ifndef WIN32
//        fim_delete_hashes(strdup(file_name));
//#else
//        // Delete from hash table
//        if (s_node = OSHash_Delete_ex(syscheck.fp, file_name), s_node) {
//            os_free(s_node->checksum);
//            os_free(s_node);
//        }
//#endif
//        os_free(alert_msg);
//        os_free(wd_sum);
//        free(esc_linked_file);
//        return (0);

//    default:
//        merror(FIM_ERROR_ACCESING, file_name, strerror(errno), errno);
//        os_free(alert_msg);
//        os_free(wd_sum);
//        free(esc_linked_file);
//        return (-1);
//    }
    return 0;
}