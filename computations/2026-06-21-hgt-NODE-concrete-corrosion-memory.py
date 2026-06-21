#!/usr/bin/env python3
import numpy as np


def simulate(pulse_duration, memory_strength, steps=240):
    pit = 0.02
    acid = 0.0
    rates = []
    for t in range(steps):
        chloride = 1.0 if t < pulse_duration else 0.05
        acid = 0.90 * acid + memory_strength * pit + 0.10 * chloride
        repair = 0.020 / (1.0 + 5.0 * acid)
        growth = (0.006 * chloride + 0.016 * acid) * (1.0 - pit)
        pit = min(1.0, max(0.0, pit + growth - repair))
        rates.append(growth)
    return pit, float(np.mean(rates[-40:])), float(acid)


def main():
    print("NODE: existing corrosion products/pits sustain localized corrosion after chloride reduction")
    print("pulse_duration memory_strength final_pit tail_growth_rate final_acid sustained")
    for pulse in [5, 15, 30, 60, 90]:
        for memory in [0.0, 0.01, 0.03, 0.08]:
            pit, tail, acid = simulate(pulse, memory)
            print(f"{pulse:14d} {memory:.2f} {pit:.6f} {tail:.6f} {acid:.6f} {int(tail > 0.003)}")


if __name__ == "__main__":
    main()
