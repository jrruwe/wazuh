# Copyright (C) 2015-2019, Wazuh Inc.
# Created by Wazuh, Inc. <info@wazuh.com>.
# This program is a free software; you can redistribute it and/or modify it under the terms of GPLv2

import asyncio
import connexion
import logging

from wazuh.agent import Agent
import wazuh.configuration as configuration
from wazuh.cluster.dapi.dapi import DistributedAPI
from ..models.agent_list_model import AgentList
from ..models.agent_inserted import AgentInserted
from ..models.agent_added import AgentAdded
from wazuh.exception import WazuhException
from ..util import remove_nones_to_dict, exception_handler

loop = asyncio.get_event_loop()
logger = logging.getLogger('wazuh')


@exception_handler
def delete_agents(pretty=False, wait_for_complete=False, list_agents=None, purge=None, status=None, older_than=None):  # noqa: E501
    """Delete agents

    Removes agents, using a list of them or a criterion based on the status or time of the last connection. The Wazuh API must be restarted after removing an agent.  # noqa: E501

    :param pretty: Show results in human-readable format 
    :type pretty: bool
    :param wait_for_complete: Disable timeout response 
    :type wait_for_complete: bool
    :param list_agents: Array of agent ID’s
    :type list_agents: List[str]
    :param purge: Delete an agent from the key store
    :type purge: bool
    :param status: Filters by agent status. Use commas to enter multiple statuses.
    :type status: List[str]
    :param older_than: Filters out disconnected agents for longer than specified. Time in seconds, ‘[n_days]d’, ‘[n_hours]h’, ‘[n_minutes]m’ or ‘[n_seconds]s’. For never connected agents, uses the register date. 
    :type older_than: str

    :rtype: AgentAllItemsAffected
    """

    f_kwargs = {'list_agent_ids': list_agents,
                'purge': purge,
                'status': status,
                'older_than': older_than
                }

    dapi = DistributedAPI(f=Agent.remove_agents,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )
    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def get_all_agents(pretty=False, wait_for_complete=False, offset=0, limit=None, select=None, sort=None, search=None,
                   status=None, q='', older_than=None, os_platform=None, os_version=None, os_name=None, manager=None,
                   version=None, group=None, node_name=None, name=None, ip=None):  # noqa: E501
    """Get all agents

    Returns a list with the available agents. # noqa: E501

    :param pretty: Show results in human-readable format 
    :type pretty: bool
    :param wait_for_complete: Disable timeout response 
    :type wait_for_complete: bool
    :param offset: First element to return in the collection
    :type offset: int
    :param limit: Maximum number of elements to return
    :type limit: int
    :param select: Select which fields to return (separated by comma)
    :type select: List[str]
    :param sort: Sorts the collection by a field or fields (separated by comma). Use +/- at the beginning to list in ascending or descending order. 
    :type sort: str
    :param search: Looks for elements with the specified string
    :type search: str
    :param status: Filters by agent status. Use commas to enter multiple statuses.
    :type status: List[str]
    :param q: Query to filter results by. For example q&#x3D;&amp;quot;status&#x3D;Active&amp;quot;
    :type q: str
    :param older_than: Filters out disconnected agents for longer than specified. Time in seconds, ‘[n_days]d’, ‘[n_hours]h’, ‘[n_minutes]m’ or ‘[n_seconds]s’. For never connected agents, uses the register date. 
    :type older_than: str
    :param os_platform: Filters by OS platform.
    :type os_platform: str
    :param os_version: Filters by OS version.
    :type os_version: str
    :param os_name: Filters by OS name.
    :type os_name: str
    :param manager: Filters by manager hostname to which agents are connected.
    :type manager: str
    :param version: Filters by agents version.
    :type version: str
    :param group: Filters by group of agents.
    :type group: str
    :param node_name: Filters by node name.
    :type node_name: str
    :param name: Filters by agent name.
    :type name: str
    :param ip: Filters by agent IP
    :type ip: str

    :rtype: AllAgents
    """
    f_kwargs = {'offset': offset,
                'limit': limit,
                'sort': sort,
                'search': search,
                'select': select,
                'filters': {
                    'status': status,
                    'older_than': older_than,
                    'os.platform': os_platform,
                    'os.version': os_version,
                    'os.name': os_name,
                    'manager': manager,
                    'version': version,
                    'group': group,
                    'node_name': node_name,
                    'name': name,
                    'ip': ip
                    },
                'q': q
                }

    dapi = DistributedAPI(f=Agent.get_agents_overview,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )
    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def restart_all_agents(pretty=True, wait_for_complete=False):  # noqa: E501
    """Restarts all agents

     # noqa: E501

    :param wait_for_complete: Disable timeout response 
    :type wait_for_complete: bool

    :rtype: CommonResponse
    """

    dapi = DistributedAPI(f=Agent.restart_agents,
                          f_kwargs={'restart_all': True},
                          request_type='distributed_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )
    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def add_agent(pretty=False, wait_for_complete=False):  # noqa: E501
    """
    Add a new agent into the cluster.
    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param name: Agent name.
    :type name: str
    :param ip: If this is not included, the API will get the IP automatically. If you are behind a proxy, you must set the option BehindProxyServer to yes at API configuration. Allowed values: IP, IP/NET, ANY
    :type ip: str
    :param force_time: Remove the old agent with the same IP if disconnected since <force_time> seconds.
    :type force_time: int
    
    :rtype: AgentIdKeyData
    """

    # get body parameters
    if connexion.request.is_json:
        agent_added_model = AgentAdded.from_dict(connexion.request.get_json())
    else:
        return 'ERROR', 400

    f_kwargs = {**{}, **agent_added_model.to_dict()}

    dapi = DistributedAPI(f=Agent.add_agent,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )

    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def delete_agent(agent_id, pretty=False, wait_for_complete=False, purge=False):  # noqa: E501
    """Get an agent

    Returns various information from an agent.'  # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param agent_id: Agent ID. All posible values since 000 onwards.
    :type agent_id: str
    :param purge: Delete an agent from the key store
    :type purge: bool

    :rtype: AgentItemsAffected
    """
    f_kwargs = {'agent_id': agent_id,
                'purge': purge
                }

    dapi = DistributedAPI(f=Agent.remove_agent,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )
    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def get_agent(agent_id, pretty=False, wait_for_complete=False, select=None):  # noqa: E501
    """Get an agent

    Returns various information from an agent.'  # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param agent_id: Agent ID. All posible values since 000 onwards.
    :type agent_id: str
    :param select: Select which fields to return (separated by comma)
    :type select: List[str]

    :rtype: Agent
    """
    f_kwargs = {'agent_id': agent_id,
                'select': select
                }

    dapi = DistributedAPI(f=Agent.get_agent,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )
    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def get_agent_config(agent_id, component, configuration, pretty=False, wait_for_complete=False):  # noqa: E501
    """Get active configuration

    Returns the active configuration the agent is currently using. This can be different from the 
    configuration present in the configuration file, if it has been modified and the agent has 
    not been restarted yet.  # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param agent_id: Agent ID. All posible values since 000 onwards.
    :type agent_id: str
    :param component: Selected agent's component.
    :type component: str
    :param configuration: Selected agent's configuration to read.
    :type configuration: str

    :rtype: AgentConfigurationData
        """
    f_kwargs = {'agent_id': agent_id,
                'component': component,
                'configuration': configuration
                }

    dapi = DistributedAPI(f=Agent.get_config,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='distributed_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )
    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def delete_agent_group(agent_id, pretty=False, wait_for_complete=False):  # noqa: E501
    """Remove all agent groups.

    Removes the group of the agent. The agent will automatically revert to the "default" group.  # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param agent_id: Agent ID. All posible values since 000 onwards.
    :type agent_id: str

    :rtype: CommonResponse
    """
    f_kwargs = {'agent_id': agent_id}

    dapi = DistributedAPI(f=Agent.unset_group,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )
    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def get_sync_agent(agent_id, pretty=False, wait_for_complete=False):  # noqa: E501
    """Get agent configuration sync status.

    Returns whether the agent configuration has been synchronized with the agent 
    or not. This can be useful to check after updating a group configuration.  # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param agent_id: Agent ID. All posible values since 000 onwards.
    :type agent_id: str

    :rtype: AgentSync
    """
    f_kwargs = {'agent_id': agent_id}

    dapi = DistributedAPI(f=Agent.get_sync_group,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )
    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def delete_agent_single_group(agent_id, group_id, pretty=False, wait_for_complete=False):  # noqa: E501
    """Remove a single group of an agent.

    Remove the group of the agent but will leave the rest of its group if it belongs to a multigroup.  # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param agent_id: Agent ID. All posible values since 000 onwards.
    :type agent_id: str
    :param group_id: Group ID.
    :type group_id: str

    :rtype: CommonResponse
    """
    f_kwargs = {'agent_id': agent_id,
                'group_id': group_id}

    dapi = DistributedAPI(f=Agent.unset_group,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )
    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def put_agent_single_group(agent_id, group_id, force_single_group=False, pretty=False, wait_for_complete=False):  # noqa: E501
    """Add agent group.

    Adds an agent to the specified group.  # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param agent_id: Agent ID. All posible values since 000 onwards.
    :type agent_id: str
    :param group_id: Group ID.
    :type group_id: str
    :param force_single_group: Forces the agent to belong to a single group
    :type group_id: bool

    :rtype: CommonResponse
    """
    f_kwargs = {'agent_id': agent_id,
                'group_id': group_id,
                'replace': force_single_group}

    dapi = DistributedAPI(f=Agent.set_group,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )
    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def get_agent_key(agent_id, pretty=False, wait_for_complete=False):  # noqa: E501
    """Get agent key.

    Returns the key of an agent.'  # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param agent_id: Agent ID. All posible values since 000 onwards.
    :type agent_id: str

    :rtype: AgentKey
    """
    f_kwargs = {'agent_id': agent_id}

    dapi = DistributedAPI(f=Agent.get_agent_key,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )
    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def put_restart_agent(agent_id, pretty=False, wait_for_complete=False):  # noqa: E501
    """Restart an agent.

    Restarts the specified agent.'  # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param agent_id: Agent ID. All posible values since 000 onwards.
    :type agent_id: str

    :rtype: 
    """
    f_kwargs = {'agent_id': agent_id}

    dapi = DistributedAPI(f=Agent.restart_agents,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='distributed_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )
    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200

#Not work
def put_upgrade_agent(agent_id, pretty=False, wait_for_complete=False, wpk_repo=None, version=None, use_http=False, force=False ):  # noqa: E501
    """Upgrade agent using online repository.

    Upgrade the agent using a WPK file from online repository.  # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param agent_id: Agent ID. All posible values since 000 onwards.
    :type agent_id: str
    :param wpk_repo: WPK repository.
    :type wpk_repo: str
    :param version: Filters by agents version.
    :type version: str
    :param use_http: Use protocol http. If it's false use https. By default the value is set to false.
    :type use_http: bool
    :param version: Force upgrade.
    :type version: bool

    :rtype: CommonResponse
    """
    f_kwargs = {'agent_id': agent_id,
                'wpk_repo': wpk_repo,
                'version': version,
                'use_http': use_http,
                'force': force}

    dapi = DistributedAPI(f=Agent.upgrade_agent,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='distributed_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )
    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200

#Not work
def put_upgrade_custom_agent(agent_id, pretty=False, wait_for_complete=False, file_path=None, installer=None):  # noqa: E501
    """Upgrade agent using a custom file.

    Upgrade the agent using a local WPK file.'  # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param agent_id: Agent ID. All posible values since 000 onwards.
    :type agent_id: str
    :param file_path: Path to the WPK file. The file must be on a folder on the Wazuh's installation directory (by default, <code>/var/ossec</code>).
    :type file_path: str
    :param installer: Installation script.
    :type installer: str

    :rtype: CommonResponse
    """
    f_kwargs = {'agent_id': agent_id,
                'file_path': file_path,
                'installer': installer}

    dapi = DistributedAPI(f=Agent.upgrade_agent_custom,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='distributed_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )
    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def put_new_agent(agent_name, pretty=False, wait_for_complete=False):  # noqa: E501
    """Add agent (quick method)

    Adds a new agent with name `agent_name`. This agent will use `any` as IP.'  # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param agent_name: Agent name used when the agent was registered.
    :type agent_name: str

    :rtype: AgentIdKeyData
    """
    f_kwargs = {'name': agent_name}

    dapi = DistributedAPI(f=Agent.add_agent,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )
    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def get_agent_upgrade(agent_id, timeout=3, pretty=False, wait_for_complete=False):  # noqa: E501
    """Get upgrade result from agent.

    Returns the upgrade result after updating an agent.'  # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param agent_id: Agent ID. All posible values since 000 onwards.
    :type agent_id: str
    :param timeout: Seconds to wait for the agent to respond.
    :type timeout: int

    :rtype: CommonResponse
    """
    f_kwargs = {'agent_id': agent_id,
                'timeout': timeout}

    dapi = DistributedAPI(f=Agent.get_upgrade_result,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='distributed_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )
    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def delete_multiple_agent_group(list_agents, group_id, pretty=False, wait_for_complete=False):  # noqa: E501
    """Remove multiple agents from a specified group. 
    
    # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param list_agents: Array of agent's IDs.
    :type list_agents: List[str]
    :param group_id: Group ID.
    :type group_id: str

    :rtype: AgentItemsAffected
    """
    f_kwargs = {'agent_id_list': list_agents,
                'group_id': group_id}

    dapi = DistributedAPI(f=Agent.unset_group_list,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )
    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def post_multiple_agent_group(group_id, pretty=False, wait_for_complete=False, agent_id_list=None):  # noqa: E501
    """Add multiple agents to a group
    
    Adds multiple agents to the specified group.    # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param group_id: Group ID.
    :type group_id: str
    :param agent_id_list: List of agents ID.
    :type agent_id_list: List[str]

    :rtype: AgentItemsAffected
    """
    # get body parameters
    if connexion.request.is_json:
        agent_list_model = AgentList.from_dict(connexion.request.get_json())
    else:
        return 'ERROR', 400
    
    f_kwargs = {**{'group_id': group_id}, **agent_list_model.to_dict()}

    dapi = DistributedAPI(f=Agent.set_group_list,
                        f_kwargs=remove_nones_to_dict(f_kwargs),
                        request_type='local_master',
                        is_async=False,
                        wait_for_complete=wait_for_complete,
                        agent_id_list=agent_id_list,
                        pretty=pretty,
                        logger=logger
                        )

    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def delete_list_group(list_groups, pretty=False, wait_for_complete=False):  # noqa: E501
    """Removes a list of groups. 
    
    # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param list_groups: Array of group's IDs.
    :type list_groups: List[str]

    :rtype: AgentGroupDeleted
    """
    f_kwargs = {'group_id': list_groups}

    dapi = DistributedAPI(f=Agent.remove_group,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )

    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def get_list_group(pretty=False, wait_for_complete=False, offset=0, limit=None, sort=None, search=None, hash='md5'):  # noqa: E501
    """Get all groups. 
    
    Returns a list containing basic information about each agent group such as number of agents belonging to the group and the checksums of the configuration and shared files.     # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    ::param offset: First element to return in the collection
    :type offset: int
    :param limit: Maximum number of elements to return
    :type limit: int
    :param sort: Sorts the collection by a field or fields (separated by comma). Use +/- at the beginning to list in ascending or descending order. 
    :type sort: str
    :param search: Looks for elements with the specified string
    :type search: str
    :param hash: Select algorithm to generate the returned checksums.
    :type hash: str

    :rtype: 
    """
    f_kwargs = {'offset': offset,
                'limit': limit, 
                'sort': sort, 
                'search': search, 
                'hash_algorithm': hash}

    dapi = DistributedAPI(f=Agent.get_all_groups,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )

    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def delete_group(group_id, pretty=False, wait_for_complete=False):  # noqa: E501
    """Remove group. 
    
    Removes the group. Agents that were assigned to the removed group will automatically revert to the "default" group.     # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param group_id: Group ID.
    :type group_id: str

    :rtype: AgentGroupDeleted
    """
    f_kwargs = {'group_id': group_id}

    dapi = DistributedAPI(f=Agent.remove_group,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )

    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def get_agent_in_group(group_id, pretty=False, wait_for_complete=False, offset=0, limit=None, select=None, sort=None, search=None, status=None, q=''):  # noqa: E501
    """Remove group. 
    
    Removes the group. Agents that were assigned to the removed group will automatically revert to the "default" group.     # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param group_id: Group ID.
    :type group_id: str
    :param offset: First element to return in the collection
    :type offset: int
    :param limit: Maximum number of elements to return
    :type limit: int
    :param select: Select which fields to return (separated by comma)
    :type select: List[str]
    :param sort: Sorts the collection by a field or fields (separated by comma). Use +/- at the beginning to list in ascending or descending order. 
    :type sort: str
    :param search: Looks for elements with the specified string
    :type search: str
    :param status: Filters by agent status. Use commas to enter multiple statuses.
    :type status: List[str]
    :param q: Query to filter results by. For example q&#x3D;&amp;quot;status&#x3D;Active&amp;quot;
    :type q: str

    :rtype: 
    """
    f_kwargs = {'group_id': group_id,
                'offset': offset,
                'limit': limit,
                'sort': sort,
                'search': search,
                'select': select,
                'filters': {
                    'status': status,
                    },
                'q': q}

    dapi = DistributedAPI(f=Agent.get_agent_group,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )

    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def put_group(group_id, pretty=False, wait_for_complete=False):  # noqa: E501
    """Create a group.

    Creates a new group.  # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param group_id: Group ID.
    :type group_id: str

    :rtype: CommonResponse
    """
    f_kwargs = {'group_id': group_id}

    dapi = DistributedAPI(f=Agent.create_group,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )
    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def get_group_config(group_id, pretty=False, wait_for_complete=False, offset=0, limit=None):  # noqa: E501
    """Get group configuration. 
    
    Returns the group configuration defined in the `agent.conf` file.     # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param group_id: Group ID.
    :type group_id: str
    :param offset: First element to return in the collection
    :type offset: int
    :param limit: Maximum number of elements to return
    :type limit: int

    :rtype: 
    """
    f_kwargs = {'group_id': group_id,
                'offset': offset,
                'limit': limit}

    dapi = DistributedAPI(f=configuration.get_agent_conf,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )

    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def post_group_config(body, group_id, pretty=False, wait_for_complete=False, offset=0, limit=None):  # noqa: E501
    """Update group configuration. 
    
    Update an specified group's configuration. This API call expects a full valid XML file with the shared configuration tags/syntax.     # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param group_id: Group ID.
    :type group_id: str

    :rtype: CommonResponse
    """

    try:
        content_type = connexion.request.headers['Content-type']
    except KeyError:
        return 'Content-type header is mandatory', 400

    # parse body to utf-8
    try:
        body = body.decode('utf-8')
    except UnicodeDecodeError:
        return 'Error parsing body request to UTF-8', 400
    except AttributeError:
        return 'Body is empty', 400

    f_kwargs = {'group_id': group_id,
                'file_data': body}

    dapi = DistributedAPI(f=configuration.upload_group_file,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )

    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def get_group_files(group_id, pretty=False, wait_for_complete=False, offset=0, limit=None, sort=None, search=None, hash='md5'):  # noqa: E501
    """Get group file. 
    
    Return the files placed under the group directory.     # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param group_id: Group ID.
    :type group_id: str
    ::param offset: First element to return in the collection
    :type offset: int
    :param limit: Maximum number of elements to return
    :type limit: int
    :param sort: Sorts the collection by a field or fields (separated by comma). Use +/- at the beginning to list in ascending or descending order. 
    :type sort: str
    :param search: Looks for elements with the specified string
    :type search: str
    :param hash: Select algorithm to generate the returned checksums.
    :type hash: str

    :rtype: 
    """
    f_kwargs = {'group_id': group_id,
                'offset': offset,
                'limit': limit, 
                'sort': sort, 
                'search': search, 
                'hash_algorithm': hash}

    dapi = DistributedAPI(f=Agent.get_group_files,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )

    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def get_group_file(group_id, file_name, pretty=False, wait_for_complete=False, type=None, format=None):  # noqa: E501
    """Get group file. 
    
    Return the files placed under the group directory.     # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param group_id: Group ID.
    :type group_id: str
    ::param file_name: Filename
    :type file_name: int
    :param type: Type of file.
    :type type: str
    :param format: Select output format to return the file. JSON will format the file in JSON format and XML will return the XML raw file in a string.
    :type format: str

    :rtype: 
    """
    f_kwargs = {'group_id': group_id,
                'filename': file_name,
                'type_conf': type, 
                'return_format': format}

    dapi = DistributedAPI(f=configuration.get_file_conf,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )

    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def post_group_file(body, group_id, file_name, pretty=False, wait_for_complete=False, offset=0, limit=None):  # noqa: E501
    """Update group configuration. 
    
    Update an specified group's configuration. This API call expects a full valid XML file with the shared configuration tags/syntax.     # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param group_id: Group ID.
    :type group_id: str
    :param group_id: Group ID.
    :type group_id: str

    :rtype: CommonResponse
    """

    try:
        content_type = connexion.request.headers['Content-type']
    except KeyError:
        return 'Content-type header is mandatory', 400

    # parse body to utf-8
    try:
        body = body.decode('utf-8')
    except UnicodeDecodeError:
        return 'Error parsing body request to UTF-8', 400
    except AttributeError:
        return 'Body is empty', 400
    
    f_kwargs = {'group_id': group_id,
                'file_name': file_name,
                'file_data': body}

    dapi = DistributedAPI(f=configuration.upload_group_file,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )

    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def insert_agent(pretty=False, wait_for_complete=False):  # noqa: E501
    """Get group file. 
    
    Return the files placed under the group directory.     # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param name: Agent name.
    :type name: str
    ::param ip: "If this is not included, the API will get the IP automatically. If you are behind a proxy, you must set the option config.BehindProxyServer to yes at config.js. Allowed values: IP, IP/NET, ANY"
    :type ip: int
    :param id: Agent ID. All posible values since 000 onwards.
    :type id: str
    :param key: Key to use when communicating with the manager. The agent must have the same key on its `client.keys` file.
    :type key: str
    :param force_time: Remove the old agent with the same IP if disconnected since <force_time> seconds.
    :type force_time: int

    :rtype: 
    """
    # get body parameters
    if connexion.request.is_json:
        agent_inserted_model = AgentInserted.from_dict(connexion.request.get_json())
    else:
        return 'ERROR', 400

    f_kwargs = {**{}, **agent_inserted_model.to_dict()}

    dapi = DistributedAPI(f=Agent.insert_agent,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )

    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def get_agent_by_name(agent_name, pretty=False, wait_for_complete=False, select=None):  # noqa: E501
    """Get an agent by its name
    
    Returns various information from an agent called :agent_name.     # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param agent_name: Agent name used when the agent was registered.
    :type agent_name: str
    :param select: Select which fields to return (separated by comma)
    :type select: List[str]

    :rtype: 
    """
    f_kwargs = {'agent_name': agent_name,
                'select': select}
    
    dapi = DistributedAPI(f=Agent.get_agent_by_name,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )

    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def get_agent_no_group(pretty=False, wait_for_complete=False, offset=0, limit=None, select=None, sort=None, search=None, q=''):
    """Get agents without group.

    Returns a list with the available agents without group. # noqa: E501

    :param pretty: Show results in human-readable format 
    :type pretty: bool
    :param wait_for_complete: Disable timeout response 
    :type wait_for_complete: bool
    :param offset: First element to return in the collection
    :type offset: int
    :param limit: Maximum number of elements to return
    :type limit: int
    :param select: Select which fields to return (separated by comma)
    :type select: List[str]
    :param sort: Sorts the collection by a field or fields (separated by comma). Use +/- at the beginning to list in ascending or descending order. 
    :type sort: str
    :param search: Looks for elements with the specified string
    :type search: str
    :param q: Query to filter results by. For example q&#x3D;&amp;quot;status&#x3D;Active&amp;quot;
    :type q: str

    :rtype: 
    """
    f_kwargs = {'offset': offset,
                'limit': limit,
                'select': select,
                'sort': sort,
                'search': search,
                'q': q}
    
    dapi = DistributedAPI(f=Agent.get_agents_without_group,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )

    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def get_agent_outdated(pretty=False, wait_for_complete=False, offset=0, limit=None, sort=None, q=''):
    """Get outdated agents.

    Returns the list of outdated agents. # noqa: E501

    :param pretty: Show results in human-readable format 
    :type pretty: bool
    :param wait_for_complete: Disable timeout response 
    :type wait_for_complete: bool
    :param offset: First element to return in the collection
    :type offset: int
    :param limit: Maximum number of elements to return
    :type limit: int
    :param sort: Sorts the collection by a field or fields (separated by comma). Use +/- at the beginning to list in ascending or descending order. 
    :type sort: str
    :param q: Query to filter results by. For example q&#x3D;&amp;quot;status&#x3D;Active&amp;quot;
    :type q: str

    :rtype: 
    """
    f_kwargs = {'offset': offset,
                'limit': limit,
                'sort': sort,
                'q': q}
    
    dapi = DistributedAPI(f=Agent.get_outdated_agents,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )

    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def restart_list_agents(pretty=False, wait_for_complete=False):  # noqa: E501
    """Restart a list of agents.
    
    # noqa: E501

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param ids: List of agents ID.
    :type ids: List[str]

    :rtype: AgentItemsAffected
    """
    # get body parameters
    if connexion.request.is_json:
        agent_list_model = AgentList.from_dict(connexion.request.get_json())
    else:
        return 'ERROR', 400
    
    dict = agent_list_model.to_dict()
    dict['agent_id'] = dict.pop('ids')
    
    f_kwargs = {**{}, **dict}
    #return f_kwargs
    dapi = DistributedAPI(f=Agent.restart_agents,
                        f_kwargs=remove_nones_to_dict(f_kwargs),
                        request_type='distributed_master',
                        is_async=False,
                        wait_for_complete=wait_for_complete,
                        pretty=pretty,
                        logger=logger
                        )

    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def get_agent_fields(pretty=False, wait_for_complete=False, offset=0, limit=None, select=None, sort=None, search=None, fields=None, q=''):
    """Get distinct fields in agents.

    Returns all the different combinations that agents have for the selected fields. It also indicates the total number of agents that have each combination. # noqa: E501

    :param pretty: Show results in human-readable format 
    :type pretty: bool
    :param wait_for_complete: Disable timeout response 
    :type wait_for_complete: bool
    :param offset: First element to return in the collection
    :type offset: int
    :param limit: Maximum number of elements to return
    :type limit: int
    :param select: Select which fields to return (separated by comma)
    :type select: List[str]
    :param sort: Sorts the collection by a field or fields (separated by comma). Use +/- at the beginning to list in ascending or descending order. 
    :type sort: str
    :param search: Looks for elements with the specified string
    :type search: str
    :param fields: List of fields affecting the operation.
    :type fields: List[str]
    :param q: Query to filter results by. For example q&#x3D;&amp;quot;status&#x3D;Active&amp;quot;
    :type q: str

    :rtype: 
    """
    f_kwargs = {'offset': offset,
                'limit': limit,
                'select': select,
                'sort': sort,
                'search': search,
                'fields': fields,
                'q': q}

    dapi = DistributedAPI(f=Agent.get_distinct_agents,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )

    data = loop.run_until_complete(dapi.distribute_function())
    
    return data, 200


@exception_handler
def get_agent_summary(pretty=False, wait_for_complete=False,):  # noqa: E501
    """Get agents summary.

    Returns a summary of the available agents. # noqa: E501

    :param pretty: Show results in human-readable format 
    :type pretty: bool
    :param wait_for_complete: Disable timeout response 
    :type wait_for_complete: bool

    :rtype: 
    """
    
    dapi = DistributedAPI(f=Agent.get_agents_summary,
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )

    data = loop.run_until_complete(dapi.distribute_function())

    return data, 200


@exception_handler
def get_agent_summary_os(pretty=False, wait_for_complete=False, offset=0, limit=None, sort=None, search=None, q=''):
    """Get OS summary.

    Returns a summary of the OS. # noqa: E501

    :param pretty: Show results in human-readable format 
    :type pretty: bool
    :param wait_for_complete: Disable timeout response 
    :type wait_for_complete: bool
    :param offset: First element to return in the collection
    :type offset: int
    :param limit: Maximum number of elements to return
    :type limit: int
    :param sort: Sorts the collection by a field or fields (separated by comma). Use +/- at the beginning to list in ascending or descending order. 
    :type sort: str
    :param search: Looks for elements with the specified string
    :type search: str
    :param q: Query to filter results by. For example q&#x3D;&amp;quot;status&#x3D;Active&amp;quot;
    :type q: str

    :rtype: 
    """
    f_kwargs = {'offset': offset,
                'limit': limit,
                'sort': sort,
                'search': search,
                'q': q}

    dapi = DistributedAPI(f=Agent.get_os_summary,
                          f_kwargs=remove_nones_to_dict(f_kwargs),
                          request_type='local_master',
                          is_async=False,
                          wait_for_complete=wait_for_complete,
                          pretty=pretty,
                          logger=logger
                          )

    data = loop.run_until_complete(dapi.distribute_function())
    
    return data, 200