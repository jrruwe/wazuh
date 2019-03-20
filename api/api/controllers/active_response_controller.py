
# Copyright (C) 2015-2019, Wazuh Inc.
# Created by Wazuh, Inc. <info@wazuh.com>.
# This program is a free software; you can redistribute it and/or modify it under the terms of GPLv2

import asyncio
import connexion
import logging

import wazuh.active_response as active_response
from wazuh.cluster.dapi.dapi import DistributedAPI
from wazuh.exception import WazuhException
from api.models.active_response_model import ActiveResponse
from api.models.api_response_model import ApiResponse
from api.models.api_response_data_model import ApiResponseData
from api.models.confirmation_message_model import ConfirmationMessage
from api.util import remove_nones_to_dict

loop = asyncio.get_event_loop()
logger = logging.getLogger('wazuh.active_response_controller')


def run_command(pretty=False, wait_for_complete=False, agent_id='000'):
    """
    Runs an Active Response command on a specified agent

    :param pretty: Show results in human-readable format
    :type pretty: bool
    :param wait_for_complete: Disable timeout response
    :type wait_for_complete: bool
    :param agent_id: Agent ID. All posible values since 000 onwards
    :type agent_id: str
    :param command: Command running in the agent. If this value starts by !, then it refers to a script name instead of a command name
    :type command: str
    :param custom: Whether the specified command is a custom command or not
    :type custom: bool
    :param arguments: Command arguments
    :type arguments: str

    :rtype: dict
    """

    # get body parameters
    if connexion.request.is_json:
        active_response_model = ActiveResponse.from_dict(connexion.request.get_json())
    else:
        return ('Error getting body parameters. Please, '
                'follow our guide: https://documentation.wazuh.com/current/user-manual/api/reference.html#active-response',
                400)

    f_kwargs = {**{'agent_id': agent_id}, **active_response_model.to_dict()}

    try:
        dapi = DistributedAPI(f=active_response.run_command,
                              f_kwargs=remove_nones_to_dict(f_kwargs),
                              request_type='distributed_master',
                              is_async=False,
                              wait_for_complete=wait_for_complete,
                              pretty=pretty,
                              logger=logger
                              )
    except ValueError as e:
        return connexion.problem(400, 'Bad parameters', str(e), ext={'input_parameters': {'agent_id': agent_id, 'command': active_response_model.command}})
    except WazuhException as e:
        return connexion.problem(400, 'Bad command', e.message, ext={'input_parameters': {'command': active_response_model.command}})

    data = loop.run_until_complete(dapi.distribute_function())
    api_response = ApiResponse.from_dict(data)
    confirmation_message = ConfirmationMessage.from_dict(data)

    api_response_data = ApiResponseData(api_response=api_response,
                                        confirmation_message=confirmation_message)

    return api_response_data.to_dict(), 200
