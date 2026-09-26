# Route 2: the prime-2 boundary relation is cusp rigidity, not a winding mechanism

- **ID:** route2-prime-two-cusp-rigidity
- **Stage:** 3-formalized (results 4, 5 and the R₂ characterization in Lean; 1–3 paper)
- **Type:** THEOREM (paper) + NO-GO for route 2 claim (ii)
- **Source:** docs/reports/route-proposals/route2.md, claim (ii) and steps 3, 6;
  2F/theta/theta-rational-cusp-boundary-law (Q, eq. (7)-(8)).
- **Statement:** the self-similarity Q(r+1)+Q(r)=½Q(4r) acts on every Mellin transform
  as multiplication by an explicit unit of the strip, so it cannot constrain any zero count.
  Its actual content is regularity at the zero-charge cusps (q≡2 mod 4) — exactly the input
  that separates θ from weakly holomorphic weight-½ θ-multiplier forms, whose even,
  integer-spectrum theta sources have off-line strip zeros.

## Setting

For a : ℕ≥1 → ℂ with Σ|a_n|/n² < ∞ put Q_a(r)=Σ a_n e^{−iπn²r}/n² (Q=Q_1).
R₂ is the identity Q_a(r+1)+Q_a(r)=½Q_a(4r) for all real r.
For F holomorphic on ℍ write R₂(F): F(τ)+F(τ+1)=2F(4τ). θ=θ₃ satisfies R₂(θ).

## Results

1. **Coefficient law [P].** Q_a(r+1)+Q_a(r)−½Q_a(4r)=Σ_m (a_{2m}−a_m)/(2m²)·e^{−4iπm²r}.
   By uniqueness of Fourier coefficients on ℝ/2ℤ, R₂ ⟺ a_{2m}=a_m for all m.
   For discrete positive spectra Σ b_λe^{−iπλr} (λ≥λ₀>0), R₂ forces λ∈{4^k·m : m odd},
   b_{4^k m}=4^{−k}b_m: R₂ alone forces integer frequencies.
2. **Hecke family [P].** For prime p: Σ_{j<p}Q_a(r+2j/p)=p^{-1}Q_{a(p·)}(p²r); the relation
   H_p: Σ_{j<p}Q_a(r+2j/p)=p^{−1}Q_a(p²r) ⟺ a_{pm}=a_m. H_2 is R₂. All H_p ⟺ a constant ⟺ Q_a=a₁Q.
3. **Mellin diagonality (kills claim (ii)) [P].** With A(s)=Σa_n n^{−s}: R₂ ⟺
   (1−2^{−s})A(s)=Σ_{n odd}a_n n^{−s}. Translation by 1 acts on Q as ½Q(4·)−Q, a combination of
   dilations, which the Mellin transform diagonalizes: 𝓜[Q(·+1)]=−(1−2^{1−s})𝓜[Q] with
   1−2^{1−s}≠0 on 0<Re s<1. Every loop or function built from Q by R₂ has, in the strip, the ξ
   zero set plus zeros of explicit polynomials in 2^{−s}. "Invariance of the winding under
   r↦4r" holds trivially and "evaluation at the fixed point" returns ξ. At the fixed points
   {0,2/3,4/3} of r↦4r (mod 2) the boundary series are ζ(s) and ζ(s)(ω̄+(1−ω̄)3^{−s}); the second
   factor has all zeros on Re s=½ because |G(1,3)|²=3.
4. **Cusp rigidity (positive survivor) [P].** Let F be holomorphic on ℍ, F(τ+2)=F(τ),
   F(−1/τ)=√(−iτ)F(τ), |F(iy)−c|≤Me^{−πy} (y≥1). If R₂(F) then
   F(1+iε)=ε^{−1/2}[(F(i/4ε)−c)−(F(i/ε)−c)], so |F(1+iε)|≤2Mε^{−1/2}e^{−π/(4ε)}.
   The constant term cancels because R₂'s factor 2 equals 4^{1/2} (weight ½).
   Hence a weakly holomorphic form in M^!_{1/2}(Γ_θ,v_θ) with R₂ has no pole at the cusp 1, so
   F/θ is a bounded modular function on the compact curve and F=cθ.
   The cusp 1 class (odd/odd rationals) is the source's zero-charge boundary set y₀=2ip/q,
   q≡2 mod 4 (rational-cusp card, (1a)).
5. **Counter-models without R₂ [P, Lean open].** h=θ₂⁴θ₄⁴/θ₃⁸=λ(1−λ) is Γ_θ-invariant,
   holomorphic on ℍ, zero at ∞, pole at cusp 1. For real P, F_P=θP(h) is 2-periodic, has the
   θ inversion law, real integer-spectrum q-expansion, and F_P(iy) behaves like P(0)θ at both
   ends of the imaginary axis. Its source k_P(x)=y^{5/4}(2yΘ''+3Θ')(y), Θ(y)=F_P(iy), y=e^{2x},
   is even, a sum of the same Gaussian atoms φ_{πλ} with λ∈ℤ, analytic on |Im x|<π/4, and
   super-exponentially decaying; Ξ_P is entire, even, real on ℝ. Two real parameters
   (P=1+t₁X+t₂X²) place a zero at any z₀ where Ξ_{θh}(z₀), Ξ_{θh²}(z₀) are ℝ-independent, an
   open dense set of the strip (else Ξ_{θh}/Ξ_{θh²} is real on an open set, hence constant,
   contradicting q-expansions 16q+… vs 256q²+…).

## Relation to the independent r-space kill

`5-failed/theta-dyadic-boundary-winding-rigidity.md` (other session, Lean
`ThetaBoundaryDyadicClassification`) classifies all bounded solutions of R₂ in r-space
(F = Σ4^{-j}A(4^j r), A anti-periodic) and builds R₂-loops of every winding. This card is the
s-space and modular complement: R₂ acts diagonally on Mellin transforms; inside exact
Γ_θ-modularity it is equivalent to regularity at the zero-charge cusp and singles out θ; removing
that regularity (θ·ℝ[h]) produces off-line strip zeros. Both kills leave the same open core: a
non-Mellin-diagonal index map from the literal theta data to the renewal loop. The odd primitive
A has Mellin transform (1−2^{−s})ζ(s)·(Γ-factor), so it carries ζ itself; no such map is known.

## Whole-route consequence

- Claim (ii) as stated is vacuous: R₂ is the 2-Euler factor and acts diagonally.
- Test B for route 2 is met by R₂, but for a different reason than the proposal gives:
  R₂ is the zero-charge cusp regularity (Hamburger's convergence hypothesis in modular form).
  The one-sided gauge k+b·k(·+log 3) also satisfies R₂ (frequencies n², 9n²) with off-line zeros
  (1+b√3·3^{−w}); it breaks FE. The deformation audit must include V=θ·ℝ[h].
- Inside FE + integer spectrum + source-strip analyticity + R₂ the theta source is a single point
  (rigidity); without R₂ the class contains off-line countermodels (Lean).
- The Hecke-semigroup view does not help: Q_s is a common eigenvector of the transfer operators of
  r ↦ n²r (eigenvalues n^{−s}), but so is every Helson series Σχ(n)n^{−s}, which can have prescribed
  off-line zeros (xi §7.2); adding the inversion S returns to ζ. A route-2 mechanism must be analytic and valid on a class that excludes V; the
  only separating datum is growth at zero-charge cusps. Step 3 has no candidate loop left.

## Lean certificate

Modules (all in `formal/GaloisForLFunctions/RHTower/`, wired into `RHTower.lean`; `lake build` of each
target green; lint gate passes; every theorem below prints only `propext`, `Classical.choice`,
`Quot.sound`):

- `ThetaGroupHauptmodulForms`: `thetaGroupHauptmodul_add_two`, `thetaGroupHauptmodul_S`
  (h is Γ_θ-invariant), `thetaGroupForm_add_two`, `thetaGroupForm_S` (θ₃·P(h) has the exact theta
  inversion law), `differentiableAt_thetaGroupForm`.
- `ModularAxisSourceTransform` (generic): for F holomorphic on ℍ with `F(ie^{-2x}) = e^x F(ie^{2x})`
  and `‖F τ − c‖ ≤ M e^{−π im τ}`: `modSource_neg` (even source k_F = T'' − T/4),
  `exists_norm_modSource_le_exp` (beats every exponential), `differentiable_modXi` (entire
  transform), `modXi_neg`.
- `ThetaGroupFormCuspBounds`: `thetaGroupForm_axis`, `thetaGroupBasis_cuspDecay`,
  `norm_thetaGroupHauptmodul_le`, `norm_thetaTwo_le_cusp`.
- `ThetaGroupOffLineStripZero`: `eq_zero_of_fourier_eq_zero` (Fourier injectivity via charFun),
  `modAxis_eq_zero_of_modSource_eq_zero` (ODE recovery), `thetaGroupXi_independent`,
  `exists_strip_point_thetaGroupXi_independent` (open mapping + identity theorem),
  `exists_real_comb_eq`, `thetaGroup_offLine_strip_zero`.
- `ThetaGroupDeformationPrimeTwo`: `thetaGroupXi_zero_eq_XiC` (the undeformed transform is XiC),
  `modXi_thetaGroupDeformation` (= XiC + t₁Ξ₁ + t₂Ξ₂), `thetaGroupDeformation_add_two`,
  `thetaGroupDeformation_S`, `modSource_thetaGroupDeformation_neg`,
  **`thetaGroupDeformation_offLine_strip_zero`** (∃ real t₁,t₂ and z₀ with 0 < im z₀ < ½ and
  Ξ_{t}(z₀) = 0), **`norm_cusp_one_le_of_primeTwo`** (R₂ + inversion ⟹
  ‖F(1+i/y)‖ ≤ 2M√y e^{−πy/4}), **`thetaGroupDeformation_primeTwo_iff`** (R₂ ⟺ t₁ = t₂ = 0).

Not formalized: results 1–3 (coefficient law, Hecke family, Mellin diagonality), full rigidity
M^!_{1/2}(Γ_θ,v_θ) ∩ R₂ = ℂθ (needs the Hauptmodul classification), reality of the deformed source,
source positivity (not expected for the parameters produced).

## Log
- 2026-09-26 — created; results 1–5 on paper.
- 2026-09-26 — Lean: countermodel with off-line strip zero, cusp rigidity, R₂ ⟺ t = 0. Axioms clean.
