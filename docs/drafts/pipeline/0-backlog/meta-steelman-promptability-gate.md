# Steelman Promptability Gate

- **ID:** meta-steelman-promptability-gate
- **Stage:** 0-backlog
- **Type:** CONJECTURE / protocol gate
- **Source:** Γ_N order false-positive audit, 2026-06-23
- **Statement:** A promptability ablation is valid only if the cold prompt tests the strongest fair formulation of the candidate after label-stripping. A vague cold prompt can measure model carelessness rather than mathematical non-promptability.

## Motivation

The Γ_N candidate produced a false positive under a weak gate.

Candidate claim:

> Finite Weierstrass approximants `Γ_N = exp(c_N s) / h_N(s)` have linear differential equation order `1` for every finite `N`; the hypertranscendence jump occurs only at `N = infinity`.

Weak cold probe:

> Does `Γ_N` satisfy a polynomial-coefficient ODE, and how does its order behave?

This elicited a wrong guess that the order grows with `N`. That is not evidence of a non-promptable mathematical fact. Once the object is label-stripped to `f(s)=exp(c s)/p(s)`, a careful cold prompt gives the answer immediately:

`p(s) f'(s) + (p'(s)-c p(s)) f(s) = 0`.

Generically the minimal order is `1`, independent of `deg p`.

## Gate

Before counting a failed cold prompt as evidence of non-promptability, run all of:

1. **Label stripping.** Replace project nouns with the simplest mathematical normal form.
2. **Specialist steelman.** Ask the prompt a competent specialist would ask after recognizing the normal form.
3. **Proof-route prompt.** Ask for the theorem or calculation that would prove the candidate, not just the candidate phrasing.
4. **Context ablation.** Test both the native wording and the stripped wording.
5. **False-positive audit.** If the stripped prompt returns the result, the earlier miss was model sloppiness or vocabulary opacity, not mathematical depth.

## Consequence

The Γ_N order fact is clean but not novel:

- `S`: finite approximants of the form `exp(c s)/p(s)` are first-order D-finite.
- `P`: one-line logarithmic derivative.
- `M`: label-stripping reveals the elementary normal form.
- `T`: no nontrivial transfer survives; abrupt order jump is approximant-family bookkeeping, not an intrinsic hypertranscendence invariant.

## Theatre Test

A future candidate cannot pass the promptability gate by making a weak model answer a vague prompt incorrectly. It must survive the strongest stripped prompt that exposes the relevant normal form.

Current status: HOLD as protocol hygiene, not new mathematics. It is significant for the agent workflow because it kills a recurring false-positive mode.
