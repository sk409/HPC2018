﻿//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#pragma once

//------------------------------------------------------------------------------
namespace hpc {

/// プレイヤーの行動の種類。
enum ActionType
{
    /// 何もしない。
    ActionType_Wait,
    /// 生地を生地置き場から取り出し、オーブンに入れる。
    ActionType_Put,

    ActionType_TERM,
};

} // namespace
// EOF