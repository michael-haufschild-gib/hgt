import numpy as np


def phase_gate(phi, preferred=0.0, sharpness=4.0, floor=0.08):
    return floor + (1.0 - floor) * np.exp(sharpness * np.cos(phi - preferred) - sharpness)


def simulate_wave(n=240, phase_mode="random", coupling=0.72, seed=0):
    rng = np.random.default_rng(seed)
    if phase_mode == "random":
        phi = rng.uniform(0.0, 2.0 * np.pi, n)
    elif phase_mode == "synchronized":
        phi = rng.normal(0.0, 0.08, n) % (2.0 * np.pi)
    elif phase_mode == "blocked":
        phi = (np.pi + rng.normal(0.0, 0.08, n)) % (2.0 * np.pi)
    elif phase_mode == "patchy":
        phi = rng.uniform(0.0, 2.0 * np.pi, n)
        for start in range(20, n, 60):
            phi[start : start + 25] = rng.normal(0.0, 0.08, min(25, n - start)) % (2.0 * np.pi)
    else:
        raise ValueError(phase_mode)

    gate = phase_gate(phi)
    activation = np.full(n, np.inf)
    amplitude = np.zeros(n)
    activation[0] = 0.0
    amplitude[0] = 1.0

    for i in range(1, n):
        inherited = amplitude[i - 1] * coupling
        amplitude[i] = inherited * gate[i]
        if amplitude[i] > 0.10:
            activation[i] = activation[i - 1] + 1.0 / max(amplitude[i], 1e-9)
        else:
            break

    participated = np.isfinite(activation)
    reach = int(participated.sum())
    speed = reach / activation[reach - 1] if reach > 1 else 0.0
    coherence = float(np.mean(np.exp(1j * phi[participated])).real) if reach else 0.0
    return {
        "mode": phase_mode,
        "reach": reach,
        "speed": float(speed),
        "mean_gate": float(gate.mean()),
        "participating_gate": float(gate[participated].mean()) if reach else 0.0,
        "phase_coherence": coherence,
        "final_amplitude": float(amplitude[reach - 1]) if reach else 0.0,
    }


def main():
    print("NODE: cell-cycle heterogeneity gates collective wound-wave participation")
    print("constraint: wave propagation is filtered by an internal phase gate, not by the edge signal alone")
    print("mode          reach  speed    mean_gate  participating_gate  phase_coherence  final_amp")
    for mode in ("synchronized", "random", "patchy", "blocked"):
        rows = [simulate_wave(phase_mode=mode, seed=1000 + k) for k in range(80)]
        keys = ["reach", "speed", "mean_gate", "participating_gate", "phase_coherence", "final_amplitude"]
        mean = {key: np.mean([row[key] for row in rows]) for key in keys}
        print(
            f"{mode:12s}  {mean['reach']:5.1f}  {mean['speed']:7.4f}  {mean['mean_gate']:9.4f}"
            f"  {mean['participating_gate']:18.4f}  {mean['phase_coherence']:15.4f}"
            f"  {mean['final_amplitude']:9.4f}"
        )


if __name__ == "__main__":
    main()
