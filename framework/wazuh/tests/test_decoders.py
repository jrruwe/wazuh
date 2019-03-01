# Copyright (C) 2015-2019, Wazuh Inc.
# Created by Wazuh, Inc. <info@wazuh.com>.
# This program is a free software; you can redistribute it and/or modify it under the terms of GPLv2

from unittest.mock import patch
import pytest

from wazuh.decoder import Decoder
from wazuh.exception import WazuhException

decoder_ossec_conf = {
    'decoder_dir': ['ruleset/decoders'],
    'decoder_exclude': 'decoders1.xml'
}


def decoders_files(file_path):
    """
    Returns a list of decoders names
    :param file_path: A glob file path containing *.xml in the end.
    :return: A generator
    """
    return map(lambda x: file_path.replace('*.xml', f'decoders{x}.xml'), range(2))


@pytest.mark.parametrize('status', [
    None,
    'all',
    'enabled',
    'disabled',
    'random'
])
@patch('wazuh.decoder.glob', side_effect=decoders_files)
@patch('wazuh.configuration.get_ossec_conf', return_value=decoder_ossec_conf)
def test_get_decoders_file_status(mock_config, mock_glob, status):
    """
    Tests getting decoders file using status filter
    """
    if status == 'random':
        with pytest.raises(WazuhException, match='.* 1202 .*'):
            Decoder.get_decoders_files(status=status)
    else:
        d_files = Decoder.get_decoders_files(status=status)
        if status is None or status == 'all':
            assert d_files['totalItems'] == 2
            assert d_files['items'][0]['status'] == 'enabled'
            assert d_files['items'][1]['status'] == 'disabled'
        else:
            assert d_files['totalItems'] == 1
            assert d_files['items'][0]['status'] == status


@pytest.mark.parametrize('path', [
    None,
    'ruleset/decoders',
    'random'
])
@patch('wazuh.decoder.glob', side_effect=decoders_files)
@patch('wazuh.configuration.get_ossec_conf', return_value=decoder_ossec_conf)
def test_get_decoders_file_path(mock_config, mock_glob, path):
    """
    Tests getting decoders files filtering by path
    """
    d_files = Decoder.get_decoders_files(path=path)
    if path == 'random':
        assert d_files['totalItems'] == 0
        assert len(d_files['items']) == 0
    else:
        assert d_files['totalItems'] == 2
        assert d_files['items'][0]['path'] == 'ruleset/decoders'


@pytest.mark.parametrize('offset, limit', [
    (0, 0),
    (0, 1),
    (0, 500),
    (1, 500),
    (2, 500),
    (3, 500)
])
@patch('wazuh.decoder.glob', side_effect=decoders_files)
@patch('wazuh.configuration.get_ossec_conf', return_value=decoder_ossec_conf)
def test_get_decoders_file_pagination(mock_config, mock_glob, offset, limit):
    """
    Tests getting decoders files using offset and limit
    """
    if limit > 0:
        d_files = Decoder.get_decoders_files(offset=offset, limit=limit)
        limit = d_files['totalItems'] if limit > d_files['totalItems'] else limit
        assert d_files['totalItems'] == 2
        assert len(d_files['items']) == (limit - offset if limit > offset else 0)
    else:
        with pytest.raises(WazuhException, match='.* 1406 .*'):
            Decoder.get_decoders_files(offset=offset, limit=limit)


@pytest.mark.parametrize('sort', [
    None,
    {"fields": ["file"], "order": "asc"},
    {"fields": ["file"], "order": "desc"}
])
@patch('wazuh.decoder.glob', side_effect=decoders_files)
@patch('wazuh.configuration.get_ossec_conf', return_value=decoder_ossec_conf)
def test_get_decoders_file_pagination(mock_config, mock_glob, sort):
    """
    Tests getting decoders files and sorting results
    """
    d_files = Decoder.get_decoders_files(sort=sort)
    if sort is not None:
        assert d_files['items'][0]['file'] == f"decoders{'0' if sort['order'] == 'asc' else '1'}.xml"


@pytest.mark.parametrize('search', [
    None,
    {"value": "1", "negation": 0},
    {"value": "1", "negation": 1}
])
@patch('wazuh.decoder.glob', side_effect=decoders_files)
@patch('wazuh.configuration.get_ossec_conf', return_value=decoder_ossec_conf)
def test_get_decoders_file_pagination(mock_config, mock_glob, search):
    """
    Tests getting decoders files and searching results
    """
    d_files = Decoder.get_decoders_files(search=search)
    if search is not None:
        assert d_files['items'][0]['file'] == f"decoders{'0' if search['negation'] else '1'}.xml"
