# TG — exact zero field of the Gaussian Euler–continuum formation

- **ID:** TG-ZF-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** CANNOT-461 (paper zero-field law with O(x) remainder); TG "faithful source-to-Hardy identification"
- **Statement:** For y>0, c>0, Re s+c>1, with E(y,a)=∫₁^∞e^{−yu²}u^{a−1}du (entire, = ½y^{−a/2}Γ(a/2,y)):
  Σ_n Λ(n)n^{−s}e^{−yn²} − E(y,1−s) = A_{y,c}(s) − Σ_ρ [e^{−y}/(ρ−½) + E(y,ρ−s)] (zeros with multiplicity,
  absolutely convergent). For y=πx, c=2, Re s>0:
  Φₓ'/Φₓ(s) = h∞'/h∞(s) − A_{πx,2}(s) + Σ_ρ [e^{−πx}/(ρ−½) + E(πx,ρ−s)]. No remainder.

## Proof
Integrate K(y,w)=½Γ(w/2)y^{−w/2} against ξ'/ξ(s+w) on Re w=c. On that line
ξ'/ξ = 1/z+1/(z−1)+Γℝ'/Γℝ−L(Λ,·) (corpus) and ξ'/ξ = Σ_ρ[1/(ρ−½)+1/(z−ρ)] (corpus, absolutely convergent).
Term bound ‖1/(ρ−½)+1/(z−ρ)‖ ≤ (2|z−½|+2|z−½|²/(Re z−1))|ρ−½|^{−2}, |Im ρ|>1, Σ|ρ−½|^{−2}<∞ ⇒ Fubini.
Kernel facts (Cahen–Mellin, incomplete Mellin, Dirichlet series): RHTower/GaussianMellinBarnesKernel (peer hgt-61).

## Zero germs
- E(y,a) → −1/a as y→0⁺ when Re a<0 (`tendsto_gaussianIncompleteMellin_of_re_neg`): zeros left of s
  give back their pole 1/(s−ρ).
- E(y,a) = ½y^{−a/2}Γ(a/2,y) (`gaussianIncompleteMellin_eq_upperIncGamma`): zeros right of s grow like
  ½|Γ((ρ−s)/2)| y^{−Re(ρ−s)/2} (diffuse divergence of CANNOT-461, now exact).
- Recursion E(y,a) = −e^{−y}/a + (2y/a)E(y,a+2) (`gaussianIncompleteMellin_recursion`).

## Lean
`RHTower/GaussianFormationZeroField.lean` (743 lines), wired after GaussianMellinBarnesKernel in RHTower.lean.
`lake build --old` exit 0, no warnings. Axioms of `logDeriv_gaussianFormation_eq_zeroField`,
`gaussianPrimeCurrent_sub_continuum_eq`, `mellinBarnes_logDeriv_xi`, recursion, germ limit, Γ normal form,
and the kernel facts: [propext, Classical.choice, Quot.sound].

## Reading
TG's source↔divisor transgression is exact: every zero (trivial ones live in A) contributes one universal
germ E(y,ρ−s). Model dominance (cycles 1–3) is a positivity statement on Σ_ρ Re E(πx,ρ−s); RH ⟺ that sum
converges to Re ξ'/ξ > 0 on Re s>½. No producer content; it is the dictionary future TG attacks need.
