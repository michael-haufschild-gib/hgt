#!/usr/bin/env python3
"""THE-MACHINE NODE test: prion-like LCD mixing order changes material state.

NODE:
    The order of mixing components in vitro can change the resulting assembly
    pathway and final material state.

Constraint tested:
    The final material state is not a function of final composition alone.
    Kinetic pathway and aging between component additions can trap different
    amounts of liquid, gel, and fiber even when the final totals are identical.
"""

from __future__ import annotations

import itertools
import numpy as np


COMPONENTS = ("protein", "rna", "salt")


def step_age(state: dict[str, float], dt: float) -> None:
    """One deterministic aging step for a minimal LCD/RNA/salt assembly model."""
    p = state["protein_free"]
    r = state["rna_free"]
    s = state["salt"]
    liquid = state["liquid"]
    gel = state["gel"]
    fiber = state["fiber"]

    liquid_form = dt * (0.62 * p * r / (1.0 + 0.7 * s))
    self_seed = dt * (0.18 * p * p / (1.0 + 5.0 * r))
    gelation = dt * (0.035 + 0.20 * s + 0.06 * p) * liquid
    fiber_template = dt * (0.24 * fiber * p + 0.05 * gel * p)
    salt_dissolve = dt * (0.035 * s * liquid / (1.0 + r))

    liquid_form = min(liquid_form, p, r)
    self_seed = min(self_seed, p - liquid_form)
    gelation = min(gelation, liquid + liquid_form)
    fiber_template = min(fiber_template, p - liquid_form - self_seed + gel)
    salt_dissolve = min(salt_dissolve, liquid + liquid_form - gelation)

    state["protein_free"] -= liquid_form + self_seed + max(0.0, fiber_template - gel)
    state["rna_free"] -= 0.72 * liquid_form
    state["liquid"] += liquid_form - gelation - salt_dissolve
    state["gel"] += gelation - min(gel, fiber_template)
    state["fiber"] += self_seed + fiber_template
    state["soluble"] += salt_dissolve

    for key in ["protein_free", "rna_free", "liquid", "gel", "fiber", "soluble"]:
        state[key] = max(0.0, state[key])


def add_component(state: dict[str, float], component: str) -> None:
    if component == "protein":
        state["protein_free"] += 1.0
    elif component == "rna":
        state["rna_free"] += 1.0
    elif component == "salt":
        state["salt"] += 1.0
    else:
        raise ValueError(component)


def run_order(order: tuple[str, ...], age_steps: int = 12, dt: float = 0.045) -> dict[str, float]:
    state = {
        "protein_free": 0.0,
        "rna_free": 0.0,
        "salt": 0.0,
        "liquid": 0.0,
        "gel": 0.0,
        "fiber": 0.0,
        "soluble": 0.0,
    }
    for component in order:
        add_component(state, component)
        for _ in range(age_steps):
            step_age(state, dt)
    for _ in range(4 * age_steps):
        step_age(state, dt)
    return state


def simultaneous(age_steps: int = 12, dt: float = 0.045) -> dict[str, float]:
    state = {
        "protein_free": 1.0,
        "rna_free": 1.0,
        "salt": 1.0,
        "liquid": 0.0,
        "gel": 0.0,
        "fiber": 0.0,
        "soluble": 0.0,
    }
    for _ in range(7 * age_steps):
        step_age(state, dt)
    return state


def material_class(state: dict[str, float]) -> str:
    material = np.array([state["liquid"], state["gel"], state["fiber"], state["soluble"]])
    labels = ["liquid", "gel", "fiber", "soluble"]
    return labels[int(np.argmax(material))]


def material_vector(state: dict[str, float]) -> np.ndarray:
    return np.array([state["liquid"], state["gel"], state["fiber"], state["soluble"]])


def main() -> None:
    print("NODE: mixing order changes pathway/final material state in prion-like LCD assemblies")
    print("all orders have final totals protein=1, rna=1, salt=1")
    print("order liquid gel fiber soluble free_protein free_rna class")
    rows = []
    for order in itertools.permutations(COMPONENTS):
        state = run_order(order)
        rows.append((order, state))
        print(
            f"{'-'.join(order):26s} {state['liquid']:.6f} {state['gel']:.6f} "
            f"{state['fiber']:.6f} {state['soluble']:.6f} {state['protein_free']:.6f} "
            f"{state['rna_free']:.6f} {material_class(state)}"
        )
    sim = simultaneous()
    print(
        f"{'simultaneous':26s} {sim['liquid']:.6f} {sim['gel']:.6f} "
        f"{sim['fiber']:.6f} {sim['soluble']:.6f} {sim['protein_free']:.6f} "
        f"{sim['rna_free']:.6f} {material_class(sim)}"
    )

    vectors = np.array([material_vector(state) for _, state in rows])
    classes = {material_class(state) for _, state in rows}
    pairwise = []
    for i in range(len(vectors)):
        for j in range(i + 1, len(vectors)):
            pairwise.append(float(np.linalg.norm(vectors[i] - vectors[j], ord=1)))
    print("\nValidation metrics")
    print(f"distinct_classes={len(classes)}")
    print(f"max_pairwise_L1_material_distance={max(pairwise):.6f}")
    print(f"fiber_range={vectors[:, 2].min():.6f},{vectors[:, 2].max():.6f}")
    print(f"gel_range={vectors[:, 1].min():.6f},{vectors[:, 1].max():.6f}")
    print(f"simultaneous_class={material_class(sim)}")
    print(
        "Interpretation: the NODE constraint is validated if identical final "
        "composition produces multiple final material classes or a large material "
        "distance solely because the addition path changed."
    )


if __name__ == "__main__":
    main()
