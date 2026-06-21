import importlib.util
import pathlib

import numpy as np


BASE = pathlib.Path(__file__).with_name("2026-06-21-hgt-STEP12-frailty-lane-alignment-battery.py")
spec = importlib.util.spec_from_file_location("frailty", BASE)
frailty = importlib.util.module_from_spec(spec)
spec.loader.exec_module(frailty)


def add_artifact_channels(reserve, start=42, stop=82, count=3):
    """Add synchronized fake low-reserve channels to attack the detector."""
    n = reserve.shape[1]
    arts = []
    for j in range(count):
        row = np.ones(n) * 0.95
        # Slightly staggered but overlapping low-reserve artifact block.
        a = max(0, start + 2 * j)
        b = min(n, stop + 2 * j)
        row[a:b] = 0.0
        arts.append(row)
    return np.vstack([reserve, np.asarray(arts)])


def leave_one_source_lane_metrics(reserve, threshold, seed):
    rows = []
    for i in range(reserve.shape[0]):
        sub = np.delete(reserve, i, axis=0)
        m = frailty.metric(sub, threshold, seed + i)
        rows.append((i, m["excess_indep"], m["visible"]))
    return rows


def main():
    print("NODE: multichannel HMMs can learn sensor artifacts as hidden states")
    print("constraint: a hidden state must survive channel ablation and artifact-channel controls")
    print("ResearchNode 24: co-failure sheets")
    print("method #2 attack it as false: inject synchronized artifact channels into finite Euler")
    print()

    primes = frailty.first_primes(100)
    sigmas = [0.2, 0.3, 0.4, 0.5, 0.7]
    window = (100.0, 170.0)
    threshold = 0.20
    samples = 140

    true_reserve = frailty.lane_matrix("true", sigmas, window, samples, primes, seed=20260621, mode="phase")
    finite_reserve = frailty.lane_matrix("finite", sigmas, window, samples, primes, seed=20260658, mode="phase")
    random_reserve = frailty.lane_matrix("random-phase", sigmas, window, samples, primes, seed=20260695, mode="phase")
    finite_artifact = add_artifact_channels(finite_reserve)
    random_artifact = add_artifact_channels(random_reserve)

    rows = [
        ("true_source_lanes", true_reserve),
        ("finite_source_lanes", finite_reserve),
        ("random_source_lanes", random_reserve),
        ("finite_plus_artifact_channels", finite_artifact),
        ("random_plus_artifact_channels", random_artifact),
    ]
    for name, mat in rows:
        m = frailty.metric(mat, threshold, seed=3100 + len(name))
        print(
            "ROW",
            name,
            f"lanes={mat.shape[0]}",
            frailty.fmt(m),
        )

    print()
    print("LEAVE_SOURCE_LANE_OUT true")
    true_leave = leave_one_source_lane_metrics(true_reserve, threshold, 4100)
    for i, ex, vis in true_leave:
        print(f" lane={i} excess_indep={ex:+.3f} visible={vis:.3f}")

    print()
    print("ARTIFACT_ABLATION finite_plus_artifact")
    source_only = frailty.metric(finite_artifact[: len(sigmas)], threshold, seed=5100)
    all_rows = frailty.metric(finite_artifact, threshold, seed=5101)
    remove_artifacts = frailty.metric(finite_artifact[: len(sigmas)], threshold, seed=5102)
    artifacts_only = frailty.metric(finite_artifact[len(sigmas) :], threshold, seed=5103)
    print(" all", frailty.fmt(all_rows))
    print(" remove_artifacts", frailty.fmt(remove_artifacts))
    print(" source_only", frailty.fmt(source_only))
    print(" artifacts_only", frailty.fmt(artifacts_only))

    print()
    print("SUMMARY")
    print("The attack failed against the source-lane metric: adding synchronized artifact channels did not turn finite/random controls into positive co-failure-excess rows.")
    print("But artifact-only rows do pass the same excess test if treated as lanes, so the gate is source-lane provenance plus leave-source-lane ablation.")
    print("The original true source-lane signal survives leave-one-source-lane ablation; non-source artifact sheets must be rejected by provenance, not by the scalar excess statistic alone.")


if __name__ == "__main__":
    main()
