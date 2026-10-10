# TG — zero endpoint of the formation-anchored cubic homotopy

- **ID:** TG-END-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** TG Needs "faithful source-to-Hardy identification; all-disc sub-unit bound"; TG-ZF-2
- **Statement:** For a strict-right rectangle D (½<Re s<1, ξ≠0 on ∂D) and anchors x>0,
  T_{D,x} = (R_{D,0} − R_{D,x})³ (Tr = #zeros in D, corpus).
  (a) Zeros in Re ρ ≤ θ < min_D Re s ⇒ ‖T_{D,x}‖₁ → 0 as x→0⁺.
  (b) #zeros in D ≤ ‖T_{D,x}‖₁ for every x (sub-unit gate).
  (c) RH ⟺ ∀D, ‖T_{D,x}‖₁ → 0 ⟺ ∀D ∃x, ‖T_{D,x}‖₁ < 1.

## Proof
- Uniform undamped passage (explicit, monotone defect bounds): Φₓ'/Φₓ → ξ'/ξ uniformly on sets with
  θ+η ≤ Re s, η ≤ Re s ≤ 2−δ, ‖s‖ ≤ M.
- On ∂D (centered): logDeriv of the Gaussian datum and of XiC differ by I·(Φₓ'/Φₓ − ξ'/ξ)(½+zI);
  corpus phase_convergence ⇒ phases and derivatives converge uniformly ⇒ corpus
  tendsto_traceNorm_relativeCubicDefect ⇒ ‖T_{D,x} − (R₀−R₀)³‖₁ → 0.
- Gate: |Tr T| ≤ ‖T‖₁ (corpus norm_opTrace_le_traceNorm), Tr T_{D,x} = card.
- Off-line zero ρ: isolated (identity theorem), square of half-side min(r/4, (Re ρ−½)/2, (1−Re ρ)/2)
  around the centered point is a FormationRectangle containing it.

## Lean
`RHTower/FormationAnchoredCubicEndpoint.lean` (new), uniform passage added to
`RHTower/GaussianFormationUndampedLimit.lean` (`eventually_norm_logDeriv_gaussianFormation_sub_logDeriv_xi_le`,
`norm_tsum_zeroGerm_sub_logDeriv_xi_le`, `norm_gaussianArchimedeanCurrent_sub_MB_le`). Wired after
GaussianFormationUndampedLimit. `lake build --old` exit 0, no warnings; axioms [propext, Classical.choice, Quot.sound].

## Reading
TG's E_base = E_residual + Tr T_D with E_residual ≥ 0 now exists for the Gaussian anchor:
E = ‖T_{D,x}‖₁, residual E − N(D) ≥ 0. The gate "E<1 at one anchor per rectangle" is exactly RH.
The Gaussian source is faithful in trace norm at x→0⁺ iff no zero lies right of the rectangle.
Next: express ‖T_{D,x}‖₁ through the H^{1/2} energy of the relative boundary phase arg(ξ/Φₓ).
