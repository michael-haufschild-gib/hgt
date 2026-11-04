# A fixed absolute collar budget cannot cover every critical ratio

- **ID:** critical-absolute-collar-budget-continuation
- **Stage:** 5-failed
- **Type:** FALSIFIED; positive survivor formalized
- **Source:** [critical-ratio continuation](../1-in-progress/critical-ratio-continuation.md)

## Exact rejected mechanism

Write L=log N, B_N for the complete tilted-spline matrix,
r₁=B_Nv₁−E₁(c_N)v₁ and M_N=N/linearDefectCutoff(c_N).
The proposed fixed-budget continuation would bound

    (c_N⁷/L) topCollarDualSeventhMass(M_N,N,r₁)/E₁(c_N)

by one constant for all R>0 along c_N≥1, c_N⁸/L→R.
`exists_intrinsic_critical_pole_linear_collar_cost` instead gives one
κ>0, independent of R and clock, such that this quantity is eventually
at least κR². `exists_critical_ratio_exceeding_every_pole_collar_budget`
constructs a canonical critical clock exceeding any prescribed budget.
The obstruction concerns this literal norm and payment. It asserts
neither failure of all-R positivity nor failure of signed continuation.

## Positive survivor and proof

For F(x)=tiltedUnitSpline(256x−254), h(y)=F(exp y), the complete mixed
pairing satisfies, at every R>0,

    (sqrt(L)/c_N)⟨B_Nv₁,x_h,N⟩ → S > 0,
    S=aφ∫₀¹F(x)[1/x−½log(1−x²)−log(2π)]dx.

Its support is [127/128,255/256]. Both prime boundary channels vanish
exactly there; the signed Gamma, center and logarithmic channels yield
the displayed source. The inequality (2π)²(1−x²)<1 proves S>0.
This is a nontrivial signed response retained by the complete form.

The reference-energy pairing tends to zero in the same normalization.
The witness has zero prefix below N/2 and uniformly bounded seventh
collar mass T. Weighted Cauchy–Schwarz gives
DualCollar₇≥S²c_N²/(8TL) eventually. Since E₁≤C_E/c_N⁷,
the normalized cost is at least
`S²/(8C_ET)·(c_N⁸/L)²`, hence at least κR² with
κ=S²/(32C_ET). Monotonicity in the collar endpoint transfers this
bound to M_N≤N/2.

## Status and consequence

Dependency-closed paper proofs and actual-path Lean audits completed:

- `TerminalPolarSourceAboveHalf.lean`: literal complete source on interior terminal windows.
- `TerminalPolarSourceIsNonzero.lean`: explicit positive source and its complete-matrix limit.
- `TheCriticalPoleHasAnIntrinsicCollarCost.lean`: residual source, quadratic lower bound, actual-cutoff transfer and arbitrary-budget counterfamily.

All audited endpoints use exactly `[propext, Classical.choice, Quot.sound]`.
Modules are wired into their programme umbrellas. No external novelty
claim; audit uses only the local corpus.

The source must be retained when paying mixed interactions. Sharper
upper constants in this same absolute norm cannot eliminate its R²
growth. Exact signed payment, changing the comparison energy, and
different decompositions remain live in the parent programme.
