# TG — undamped limit of the Gaussian zero field

- **ID:** TG-ZF-2
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** TG-ZF-1 (exact zero field); germ dichotomy
- **Statement:**
  (a) Re s>0: Φₓ'/Φₓ(s) − Σ_ρ [e^{−πx}/(ρ−½) + E(πx,ρ−s)] → 0 as x→0⁺ (unconditional).
  (b) If every ξ-zero has Re ρ ≤ θ and max(θ,0) < Re s < 2: Φₓ'/Φₓ(s) → ξ'/ξ(s). Under RH on ½<Re s<2.

## Proof
- Archimedean partial fractions (Gauss digamma series): A(z)=h∞'/h∞(z) = ½−(log π)/2−γ/2 + Σ_{n≥0}[1/(2n+4) − 1/(z+2n+2)], Re z>0.
- MB transform termwise (Fubini, Σ1/(n+1)²): A_{y,c}(s) = e^{−y}·const + Σ_n [e^{−y}/(2n+4) − E(y,−s−2n−2)]. Trivial zeros carry the same germs as nontrivial ones.
- Germ defect (e^{−y}−1)/κ + E(y,a) + 1/a, two recursion steps + ‖E(y,b)‖ ≤ ½Γ((r+1)/2)y^{−(r+1)/2}:
  ≤ y‖κ−a‖/(‖κ‖‖a‖) + (2y+2Γ((4−η)/2)y^{η/2})/(‖a‖‖a+2‖), Re a ≤ −η.
- Dominated convergence: trivial zeros against Σ1/(n+2)², nontrivial zeros against Σ|ρ−½|^{−2}.

## Lean
`RHTower/GaussianFormationUndampedLimit.lean` (721 lines), wired after GaussianFormationZeroField.
`lake build --old` exit 0, no warnings. Axioms [propext, Classical.choice, Quot.sound]:
`tendsto_logDeriv_gaussianFormation_sub_zeroGermField`, `tendsto_logDeriv_gaussianFormation_of_zeroFree`,
`tendsto_logDeriv_gaussianFormation_of_riemannHypothesis`, `hasSum_archimedeanMBTerm`, `tendsto_tsum_zeroGerm`.

## Reading
Corpus had Φₓ→ξ only on Re s>1. Now: the passage defect Φₓ'/Φₓ − ξ'/ξ is, up to o(1), the sum of the
nontrivial germ defects alone; left zeros' defects are O(y^{η/2}|ρ−½|^{−2}), so the defect is carried
exactly by the zeros to the right of s. The passage is an exact continuation device up to the zero abscissa.
Open converse: pointwise convergence on a half-plane ⇒ zero-free there (needs local boundedness).
