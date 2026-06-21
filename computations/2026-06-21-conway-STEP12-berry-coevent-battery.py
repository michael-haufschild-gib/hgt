import importlib.util
import pathlib
import random

import mpmath as mp


mp.mp.dps = 40

BASE = pathlib.Path(__file__).with_name("2026-06-21-conway-phase-slip-berry-coevent.py")
spec = importlib.util.spec_from_file_location("berry_coevent", BASE)
berry = importlib.util.module_from_spec(spec)
spec.loader.exec_module(berry)


def main():
    print("STEP12 battery: Berry switch co-event gate")
    print("phase observable: mirror anti-phase; independent observable: mirror magnitude balance")
    t_values = [14.02 + k * (0.28 / 40) for k in range(41)]
    t_values += [20.90 + k * (0.35 / 40) for k in range(41)]
    t_values += [25.00 + k * (0.35 / 40) for k in range(41)]

    for delta in [0.06, 0.12, 0.20, 0.30]:
        print(f"DELTA {delta}")
        rows = [
            berry.evaluate_channel("completed_xi", lambda s: berry.xi_ld(s), t_values, delta=delta),
            berry.evaluate_channel("bare_zeta", lambda s: berry.zeta_ld(s), t_values, delta=delta),
            berry.evaluate_channel("gamma_only", lambda s: berry.gamma_part(s), t_values, delta=delta),
            berry.evaluate_channel(
                "finite60_completed",
                lambda s: complex(berry.gamma_part(s)) + berry.finite_prime_ld(s, 60),
                t_values,
                delta=delta,
            ),
        ]
        # Re-seed per delta so the row is deterministic but independent of the main script.
        rng = random.Random(20260621 + int(delta * 1000))
        cache = {}

        def scrambled(s):
            key = (round(s.real, 6), round(s.imag, 6))
            if key not in cache:
                p = complex(berry.zeta_ld(s))
                theta = rng.random() * 2 * mp.pi
                cache[key] = abs(p) * complex(mp.cos(theta), mp.sin(theta))
            return complex(berry.gamma_part(s)) + cache[key]

        rows.append(berry.evaluate_channel("phase_scrambled_completed", scrambled, t_values, delta=delta))
        for row in rows:
            print(
                " ",
                row["name"],
                f"phase={row['phase']}/{row['total']}",
                f"mag={row['mag']}/{row['total']}",
                f"co={row['co']}/{row['total']}",
                f"phase_only={row['phase_only']}",
                f"mag_only={row['mag_only']}",
                f"mean_resid={row['mean_resid']:.4f}",
            )


if __name__ == "__main__":
    main()
