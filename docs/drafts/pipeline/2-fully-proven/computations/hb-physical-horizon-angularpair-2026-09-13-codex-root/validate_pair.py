#!/usr/bin/env python3
"""Finite-difference and principal-formula checks for exact angular covectors."""

from __future__ import annotations

import json
import math
import os

import mpmath as mp

from horizon_pair import angular_pair_terms, principal_factor
from native_delay import completed_lambda_data, scalar_jets


gamma = float(mp.im(mp.zetazero(1)))
x, y = 0.17, 1.13


def fg(xx, yy):
    f, fx, fy, *_ = scalar_jets(gamma, xx, yy, 55, 45, False, reduce_point=False)
    return 0.5 * f * f, yy * yy * (fx * fx + fy * fy)


f, fx, fy, fxx, fxy, *_ = scalar_jets(gamma, x, y, 55, 45, False, reduce_point=False)
mu = -(gamma * gamma + 0.25)
j = (f * fy, -f * fx)
k = (
    y * (fx * fx + fy * fy) + y * y * (fx * fxy - fy * fxx) + mu * f * fy,
    -y * y * (fx * fxx + fy * fxy),
)
rows = []
for h in (2e-4, 1e-4, 5e-5):
    fy_fd = (fg(x, y + h)[0] - fg(x, y - h)[0]) / (2 * h)
    fx_fd = (fg(x + h, y)[0] - fg(x - h, y)[0]) / (2 * h)
    gy_fd = (fg(x, y + h)[1] - fg(x, y - h)[1]) / (4 * h)
    gx_fd = -(fg(x + h, y)[1] - fg(x - h, y)[1]) / (4 * h)
    rows.append({
        "h": h,
        "J_relative_error": math.hypot(j[0] - fy_fd, j[1] + fx_fd) / max(math.hypot(*j), 1e-300),
        "K_relative_error": math.hypot(k[0] - gy_fd, k[1] - gx_fd) / max(math.hypot(*k), 1e-300),
    })
phase, _ = completed_lambda_data(gamma, 45)
principal_direct = float(angular_pair_terms(gamma, 0.0, y, True, 55, 45)[2].real)
principal_closed = principal_factor(gamma, phase + gamma * math.log(y))
payload = {
    "gamma": gamma,
    "point": [x, y],
    "finite_difference": rows,
    "principal_direct": principal_direct,
    "principal_closed": principal_closed,
    "principal_relative_error": abs(principal_direct - principal_closed) / max(abs(principal_closed), 1e-300),
}
with open("pair-validation.json.tmp", "w") as handle:
    json.dump(payload, handle, indent=2)
os.replace("pair-validation.json.tmp", "pair-validation.json")
