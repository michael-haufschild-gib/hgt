# TG C9.11d — coherent dilation support rigidity

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** TG
- **Parent:** `../1-in-progress/tg-joint-prime-gamma-relative-lift.md`
- **Predecessor:** C9.11c, exact single-scale inverse support

## Hard target

Remove coherent retained/lost decoupling from the actual Ward cubic: for every finite complex source packet in the crossing chamber, `Z†W=0` should force `Z=0`. Neither cofinal completion nor a Hardy-index comparison follows automatically.

## Corpus basis

Deep search `finite dilation combination bounded support largest scale exact inverse support` completed with `partial=false` and complete source inventory; compiler coverage is mostly source-only. `FiniteEulerCalkinIndependence.finiteDilationCombination` is the existing actual finite complex dilation source. Its shell-separation theorem proves coefficient detection on selected packets, not the required exact inverse-support law for arbitrary bounded-band vectors. C9.11c supplies the two-polarization separation and one-scale descent.

## Proved law and paper mechanism

Group identical scales in `H=Σ u_i D_(r_i)` and remove zero combined coefficients. If the resulting source is nonempty, let `R` be its largest scale. For a vector in a bounded physical-plus-Fourier forbidden sum, the proved law is

`H v ∈ T_c ↔ v ∈ T_(c/R)`, where `T_t=A_t+B_t`.

For physical support, isolate the unique term `u_R U_(1/R) f`. Every remaining dilation expands support by at most some `S<R`. Consequently input support at `b` and output support at `c` imply input support at `max(c/R,(S/R)b)`. Finite iteration reaches `c/R`. Fourier transform commutes with every `D_r`, so the same argument handles the second polarization; bounded-support uncertainty prevents cross-polarization cancellation. Apply the law to the adjoint source (conjugated coefficients). If all grouped coefficients vanish, both actual transitions vanish directly.

The gap `S<R` comes from the literal finite packet, not a uniform bound or an assumption on a cofinal limit. Its degeneration for growing packets must be kept visible in the later completion problem.

## Log

- 2026-10-02 — Formulated after single-scale source rigidity passed Lean scratch verification; beginning finite-source proof.


## Complete paper proof

1. Combine equal scales by finite fiberwise summation. Delete zero combined coefficients. This preserves the complete ambient operator and all phase cancellations. The reduced packet has distinct real scales, each above one, and nonzero coefficients.
2. If the reduced packet is nonempty, select its maximum `R`. Put `S=max(1, all remaining scales)`. Then `1≤S<R`. Split `H=u_R U_(1/R)+V`; for `f∈A_t`, every term of `Vf` lies in `A_(St)`.
3. Suppose `Hf∈A_c`, `c>0`. If `f∈A_((R/S)t)` and `c≤Rt`, then `Vf∈A_(Rt)`, hence `u_R U_(1/R)f∈A_(Rt)`. Divide by the nonzero coefficient and apply `U_R`: `f∈A_t`.
4. Choose a finite `n` with `b<(R/S)^n(c/R)`. Descend the preceding implication `n` times. This proves `Hf∈A_c ⇒ f∈A_(c/R)` for any initially bounded physical support. The reverse support implication follows termwise.
5. Fourier transform commutes with `H`, including its complex coefficients. The same exact recovery holds for Fourier support. For `v=f+g∈T_b` and `Hv=h+j∈T_c`, `Hf-h=j-Hg` lies in both bounded polarizations. Fourier uncertainty forces it to vanish. Apply recovery separately to `f,g`, proving the full forbidden-sum law.
6. Convert `Q_bv=0` and `Q_cHv=0` into actual forbidden-sum memberships using the closed-sum theorem. The recovered membership `v∈T_(c/R)` lies in `T_a` when `c≤Ra`. If `v∈K_a`, orthogonality forces `v=0`.
7. On the even carrier, factor the existing coherent transitions exactly as `Z=E H (Q_b-Q_c)` and `W=E H Q_c`, with `E=Q_a-Q_b`. Adjoint formation conjugates every coefficient. From `Z†W=0`, obtain `Q_c H†Z=0` since `EZ=Z`. If the ambient adjoint source is zero, its even restriction is zero, hence `Z=0`. Otherwise apply retained injectivity to each `Zv`. This discharges source nonvanishing internally.
8. The existing complete Ward law gives `Re Tr(B³)=-(3/2)||ZZ†W||²_HS`, with zero locus `Z†W=0`. Therefore, for arbitrary finite complex packets in the crossing chamber,

   `Re Tr(B³)=0 ↔ Z=0`, and `Re Tr(B³)<0 ↔ Z≠0`.

No rank, density, distinct-prime, nonzero-packet, or phase premise remains in the final coherent cubic theorem. The only conditions are the literal geometric chamber and source scales above one. No RH, Xi-zero, continuation or budget premise is used.

## Lean artifacts and audit

- `formal/GaloisForLFunctions/RHTower/SoninFiniteDilationSourceSupport.lean`: nine public declarations, including the exact grouped-source reduction and retained injectivity.
- `formal/GaloisForLFunctions/RHTower/SoninCoherentWardSourceRigidity.lean`: nine public declarations, including exact ambient/even source factorization and the complete coherent cubic zero/sign classification.
- Three existing support helpers in `SoninDilationSourceSupportRecovery` are now public, with descriptive names, so the new proof reuses them.

Final foreground audits passed for both new leaves, the changed support leaf, and its existing `SoninSingleScaleWardRigidity` dependent, using `lake --old env lean <module>.lean -o <matching .olean>`. New leaves are wired into `RHTower.lean`; no umbrella/full build. Separate `/tmp` audit of all 33 public declarations across the four leaves reports exactly `propext`, `Classical.choice`, `Quot.sound`. No holes, raised heartbeat limits, added axioms, or numerical experiments.

Global lint retains the same ten unrelated unwired modules recorded in C9.11c; none of these four leaves is implicated.

## Frontier assessment and next hard problem

C9.11b's coherent retained/lost decoupling question is closed for every finite packet. The surviving cubic cannot hide a nonzero combined transition through interference among finitely many source scales. This is stronger than the single-scale result; it does not establish that every strict aperture transition is nonzero.

There is no largest scale in the full prime-power source, and the proof supplies no cofinal bound on `S/R`. The next attack returns to the actual joint prime–Gamma operator completion in the parent card. The corpus has a literal Gamma scattering multiplier and its tested quantized log differential (`CCMArchimedeanPhaseOperatorProduct`), but a scalar remainder loaded on a canonical probe (`SoninSemilocalCorrectedSource`) does not identify the necessary mixed operator counterterm. Hardy-index comparison and source-derived sub-unit budget remain open; RH remains unresolved.

- 2026-10-02 — Coherent support recovery, exact coefficient reduction and full Ward cubic rigidity formalized; final leaf and axiom audits passed.
