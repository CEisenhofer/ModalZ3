#pragma once

#include "logging.h"

#ifndef NDEBUG
bool is_logging_enabled = true;

void set_logging(bool enabled) {
    is_logging_enabled = enabled;
}

bool get_logging() {
    return is_logging_enabled;
}

#endif