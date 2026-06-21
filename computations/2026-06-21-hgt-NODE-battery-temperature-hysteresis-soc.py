#!/usr/bin/env python3
"""THE-MACHINE NODE test: temperature changes battery hysteresis and OCV-SOC calibration.

NODE:
    Temperature changes alter both hysteresis behavior and OCV-SOC calibration.

Constraint tested:
    Terminal voltage is not a temperature-invariant function of SOC. Temperature
    changes both the equilibrium OCV curve and the hysteresis state magnitude, so
    a calibration learned at one temperature can produce biased SOC estimates at
    another temperature even with the same true SOC trajectory.
"""

from __future__ import annotations

import numpy as np


def ocv(soc: np.ndarray, temp_c: float) -> np.ndarray:
    plateau = 3.28 + 0.16 * np.tanh((soc - 0.52) / 0.065)
    slope = 0.055 * (soc - 0.5)
    temp_shift = -0.0017 * (25.0 - temp_c) + 0.018 * np.sin(np.pi * soc) * ((temp_c - 25.0) / 35.0)
    return plateau + slope + temp_shift


def hysteresis_gain(temp_c: float) -> float:
    return 0.018 + 0.00095 * (25.0 - temp_c) + 0.00022 * max(temp_c - 25.0, 0.0)


def resistance(temp_c: float) -> float:
    return 0.018 * np.exp((25.0 - temp_c) / 36.0)


def simulate(temp_c: float, steps: int = 560, capacity_ah: float = 2.3) -> dict[str, np.ndarray]:
    dt_h = 1.0 / 360.0
    current = np.zeros(steps)
    current[20:170] = 1.0
    current[210:330] = -0.75
    current[370:500] = 0.55
    soc = np.empty(steps)
    hyst = np.empty(steps)
    voltage = np.empty(steps)
    soc[0] = 0.72
    hyst[0] = 0.0
    tau = 42.0 + 2.2 * max(25.0 - temp_c, 0.0)
    gain = hysteresis_gain(temp_c)
    r = resistance(temp_c)
    for k in range(steps):
        if k > 0:
            soc[k] = np.clip(soc[k - 1] - current[k - 1] * dt_h / capacity_ah, 0.02, 0.98)
            target = np.sign(current[k - 1])
            hyst[k] = hyst[k - 1] + (target - hyst[k - 1]) / tau
        voltage[k] = ocv(np.array([soc[k]]), temp_c)[0] + gain * hyst[k] - r * current[k]
    return {"current": current, "soc": soc, "hyst": hyst, "voltage": voltage}


def estimate_soc_from_25c(voltage: np.ndarray) -> np.ndarray:
    grid = np.linspace(0.02, 0.98, 2000)
    ref = ocv(grid, 25.0)
    return np.interp(voltage, ref, grid)


def median_abs_soc_error(temp_c: float, mode: str) -> tuple[float, float, float]:
    sim = simulate(temp_c)
    v = sim["voltage"].copy()
    if mode == "full":
        pass
    elif mode == "ocv_only":
        sim25 = simulate(25.0)
        v = ocv(sim["soc"], temp_c) + hysteresis_gain(25.0) * sim25["hyst"] - resistance(25.0) * sim["current"]
    elif mode == "hysteresis_only":
        v = ocv(sim["soc"], 25.0) + hysteresis_gain(temp_c) * sim["hyst"] - resistance(25.0) * sim["current"]
    else:
        raise ValueError(mode)
    est = estimate_soc_from_25c(v)
    err = est - sim["soc"]
    active = np.abs(sim["current"]) > 0.05
    rest = ~active
    return float(np.median(np.abs(err))), float(np.median(np.abs(err[active]))), float(np.median(np.abs(err[rest])))


def same_soc_voltage_spread(soc_value: float = 0.55) -> tuple[float, float]:
    temps = np.array([-10.0, 0.0, 25.0, 45.0])
    charge = ocv(np.full_like(temps, soc_value, dtype=float), temps) + np.array([hysteresis_gain(t) for t in temps])
    discharge = ocv(np.full_like(temps, soc_value, dtype=float), temps) - np.array([hysteresis_gain(t) for t in temps])
    return float(charge.max() - charge.min()), float(discharge.max() - discharge.min())


def main() -> None:
    print("NODE: temperature changes battery hysteresis and OCV-SOC calibration")
    charge_spread, discharge_spread = same_soc_voltage_spread()
    print(f"same_soc_voltage_spread_charge={charge_spread:.6f}")
    print(f"same_soc_voltage_spread_discharge={discharge_spread:.6f}")
    print("temp mode median_abs_soc_error active_error rest_error hysteresis_gain resistance")
    for temp in [-10.0, 0.0, 25.0, 45.0]:
        for mode in ["full", "ocv_only", "hysteresis_only"]:
            med, active, rest = median_abs_soc_error(temp, mode)
            print(
                f"{temp:6.1f} {mode:15s} {med:.6f} {active:.6f} {rest:.6f} "
                f"{hysteresis_gain(temp):.6f} {resistance(temp):.6f}"
            )
    print(
        "\nInterpretation: the NODE is validated if same-SOC voltages spread with "
        "temperature and a 25C voltage-to-SOC calibration fails off-temperature. "
        "The OCV-only and hysteresis-only ablations separate the two sources."
    )


if __name__ == "__main__":
    main()
