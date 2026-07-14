# Prime--archimedean confined Loschmidt phase window

- **ID:** prime-arch-bernstein-confined-loschmidt-phase-window
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** fixed-window-logarithmic-Weil tomography route
- **Statement:** The endpoint Bernstein Loschmidt purity has an unconditional exponential amplitude ceiling strictly below `3/2`; RH is exactly its bounded zero-excess phase, while failure of RH forces a strict surviving exponent inside the confined interval `(1, 3/2)`.

## Goal

Replace a bare RH equivalence by a positive phase-selection theorem with unconditional quantitative
content on both sides.  The source must itself confine every possible off-line instability before
the RH-bearing endpoint estimate is imposed.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem names recorded, narrow target check green, axiom audit PASS
- [ ] 3 → 4  publication-ready: integrated as the single master theorem of the paper

## Proposed master theorem

Let
\[
C_*:=\text{the completed endpoint curvature},\qquad
R_*:=\frac{C_*}{1-C_*},\qquad
\kappa_*:=\frac{1-C_*}{4-C_*},\qquad
B_*:=1+2\kappa_*<\frac32.
\]
For the endpoint Bernstein coefficient vector `a_M`, put
\[
T_M=\sum_i|a_{M,i}|,
\qquad
\Pi_M=\sum_i a_{M,i}^2.
\]
Prove unconditionally that
\[
\frac{s_0^2}{M+1}\le \Pi_M\le T_M^2
\le A_*^2 B_*^{2M}
\]
for an explicit finite divisor mass `A_*`.  Moreover,
\[
\mathrm{RH}
\iff \forall M\;\Pi_M\le s_0^2
\iff \sup_M\Pi_M<\infty
\iff \forall r>1\;\frac{\Pi_M}{r^M}\to0.
\]
If RH fails, a cancellation-resistant maximal affine packet forces some strict amplitude exponent
`b` with `1 < b ≤ B_*`; equivalently the normalized purity fails to vanish at some energy base
`r=b^2>1`.

## Approach

1. Use the exact divisor formula for each Bernstein coefficient and triangle inequality.
2. For line atoms, the normalized coordinate lies in `[0,1]`, so
   `‖u‖ + ‖1-u‖ = 1`.
3. For off-line atoms, use the proved curvature gap
   `‖z_q‖ ≤ C_*/(4-C_*)`; after division by `R_*`, this is
   `‖u_q‖ ≤ κ_* < 1/4`, hence
   `‖u_q‖ + ‖1-u_q‖ ≤ 1+2κ_* = B_*`.
4. Sum against the absolutely summable reciprocal-square divisor mass.
5. Combine the universal ceiling with the exact Loschmidt Cesaro identity and the already proved
   cancellation-resistant off-line exponential phase.

## Non-circularity

The upper phase confinement uses only the completed endpoint curvature inequalities, the exact
prime--Gamma/Xi value bridge, absolute summability, and finite-dimensional norm estimates.  It does
not assume positivity, self-adjointness, the Weil criterion, or RH.  The remaining endpoint
selection is precisely boundedness of the positive source-defined purity.

## Novelty and significance audit

- **Significance:** if proved, the paper contributes an unconditional quantitative estimate on the
  missing RH observable, not only an equivalence.
- **Novelty:** to be audited conservatively after the proof.  The ingredients are classical norm
  inequalities plus project-specific source geometry; the integrated confined phase law may still
  be a bridge rather than new science.

## Log

- 2026-07-14 — created after the Loschmidt-purity criterion exposed the off-line curvature disk as
  a universal strict phase ceiling.
