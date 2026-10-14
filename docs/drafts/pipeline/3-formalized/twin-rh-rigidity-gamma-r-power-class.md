# Twin RH-rigidity in the Γ_ℝ(s)^d functional-equation class

- **ID:** twin-rh-rigidity-gamma-r-power-class
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean core) + THEOREM (paper corollary)
- **Source:** route-tt-loop-2026-10-13 rows 390, 393, 396, 399
- **Statement:**
  - Let T be a Dirichlet series with real coefficients and a₁=1. Suppose its completed T*(s)=Γ_ℝ(s)^dT(s) has finite order, satisfies T*(1−s)=T*(s), and has poles only at s=0,1, each of order κ.
  - (i) If κ<d, then T* has a zero off the critical line.
  - (ii) If κ=d and every zero of T* is critical, then the Riemann hypothesis holds and T=ζ^d.
  - Hence every twin ζ³+e built from the corpus's abundant degree-3 solutions has an off-line zero, unconditionally.

## Goal
Use the corpus's unconditional Weil-cone rigidity (twisted arc minimum principle) to classify which members of a whole functional-equation class can satisfy RH.

The class C_d of Dirichlet series sharing ζ^d's completed functional equation is infinite-dimensional for d ≥ 3 (`gammaRCube_functional_equation_abundance_vanishing_below`). Even so, it contains at most one RH member, and that member is ζ^d.

So, unlike function fields, fatness of the functional-equation class does not fatten the Weil cone. The fatness lives entirely on non-Euler members, all of which violate RH.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven: paper corollary below. Dependencies: Weil's explicit formula for T (standard), the Lean core, and the prime number theorem bound Σ_{n≤N}Λ(n)=O(N).
- [x] 2 → 3  formalized: `RHTower.WeilConeDegreeTwinRigidity`, wired into `GaloisForLFunctions/RHTower.lean`. Theorems:
  - `weilDegreeFunctional_eq_mul`, `weilPositiveDegree_iff`, `eq_smul_vonMangoldt_of_weilPositiveDegree`, `riemannHypothesis_of_weilPositiveDegree`;
  - `weilDegreePoleFunctional_eq_mul`, `not_forall_re_weilDegreePoleFunctional_nonneg`;
  - axioms: propext, Classical.choice, Quot.sound.
- [ ] 3 → 4  publication-ready

## Approach
- **[L] Scaling.** The degree-d Weil functional d·(pole+arch)−Σ_{n≥2}lam(n)n^{−½}(k(log n)+k(−log n)) equals d·W_1(lam/d).
  - So degree-d positivity ⟺ lam/d is in the full Weil cone of ζ, which is {Λ} under RH and ∅ otherwise (`WeilSpectral.eq_vonMangoldt_of_weilPositiveFull`).
  - Hence degree-d positivity ⟺ RH ∧ lam=dΛ (`weilPositiveDegree_iff`).
- **[L] Pole order κ.** d·arch+κ·pole−prime_lam = d·W^{κ/d}(lam/d), the Weil functional with pole weight κ/d.
  - For κ<d and lam/d−Λ with linearly bounded partial sums, it is negative on some real autocorrelation.
  - This uses the corpus `WeilPoleWeight.not_forall_re_weilPoleWeightFunctional_nonneg`: the twisted-arc null tests have pole term w₀/2>0.
- **[paper] Corollary.**
  - If every zero of T* is critical, Weil's explicit formula for T has archimedean part d·arch and polar part κ·(ĝ(i/2)+ĝ(−i/2)). With critical zeros it gives Weil positivity of λ_T (the coefficients of −T′/T).
  - −T′/T has residue κ at s=1 and no other singularity in Re s>½. So Σ_{n≤N}λ_T(n)=κN+O(N^{½+ε}), and λ_T/d−Λ has linearly bounded partial sums (Σ_{n≤N}Λ(n)=O(N) unconditionally).
  - κ<d contradicts the second Lean theorem.
  - For κ=d the first Lean theorem gives RH and λ_T=dΛ, i.e. −T′/T=−dζ′/ζ, so T=ζ^d because a₁=1.

## No-go closure / open part
- **κ>d (pole weight >1) is OPEN.**
  - The corpus `WeilPoleWeightAboveOneVonMangoldt` excludes only lam=Λ at β>1, because its odd null test Ξ·(iz/2) is not prime-blind.
  - Closing it needs an ODD blind Ξ-divisible family, an odd twisted arc minimum principle. Together with the even family, that would also give a primitive zero face and a pole-free prime-blind criterion (route-tt rows 392, 399).
- **Small perturbations are trivial.** ζ³+εe splits on-line triple zeros into off-line ones at distance ≍|ε|^{1/3}. The theorem's content is global, and equals the thin cone.

## Log
- 2026-10-14 — created at stage 3 from route-tt rows 390, 393. Lean module written, compiled with `lake env lean`, built with `lake build --old`, axioms checked, wired.

## Addendum (route-tt rows 416, 416L) — the pole-order sandwich
- On blind tests every Weil functional drops its prime sum, so W_{d,κ}(λ_T)(g) = d·A(g) + (κ−d)·P(g).
  - A = pole + arch is ζ-free.
  - P is the pole term.
- **[L]** `RHTower.WeilConeDegreePoleSandwich.le_mul_one_add_div_of_blind_pole_neg`: if T ∈ C_d has only critical zeros, then κ ≤ d(1 + A(g)/|P(g)|) for every pole-negative blind PD g.
- Paper corollary: with κ ≥ d (Lean, `not_forall_re_weilDegreePoleFunctional_nonneg`), d ≤ κ ≤ d(1+c*), where c* = inf_{P<0} A/|P| is an absolute ζ-free constant.
  - κ>d is therefore closed for every d < 1/c*.
  - It is closed for all d iff c* = 0, i.e. iff a pole-negative blind null test (the "odd keystone") exists.
  - Route-tt rows 414–415 show that no analytic witness gives one.
- Pole-weight window: {β : cone_β ≠ ∅} = [1+κ₊, 1+c*], where κ₊ = sup_{P>0}(−A/P) ≥ 0 unconditionally (TMP's G₀).
  - RH ⟺ κ₊ = 0 ∧ c* ≥ 0 ∧ pole-free PBAP.
- Open: an explicit upper bound for c* (an explicit pole-negative blind PD test with computed A/|P|). Odd φ supported in (−¼log 2, ¼log 2) gives automatically blind tests with P = −2(∫φe^{x/2})² < 0.

## Addendum (route-tt row 424) — CORRECTION: κ>d is closed; the classification is complete
- The "κ>d OPEN" section above is superseded.
- Corpus `WeilPoleWeight.le_one_of_herglotz_poleWeightFunction` (another lane's module `WeilPoleWeightAtMostOne`): if the pole-weight-β Weil function has a Herglotz continuation to Re s > ½, then β ≤ 1.
  - The proof is a multiplicative Toeplitz density ceiling; no odd null test is needed.
- For T ∈ C_d with only critical zeros, Φ = Ξ_T′/(dΞ_T) is Herglotz on Re s > ½ (Hadamard product, Ξ_T(1−s) = Ξ_T(s)), and Φ = poleWeightFunction(κ/d)(λ_T/d).
- Hence κ ≤ d. Together with κ ≥ d (Lean, TMP null tests), this gives κ = d and T = ζ^d.
- **[L] capstone** `RHTower.WeilConeDegreeHerglotzClassification.pole_order_eq_and_eq_smul_vonMangoldt_of_herglotz`: from Herglotz data, summable weights and linearly bounded deviation, κ = d, RH holds, and lam = dΛ.
  - `lake build --old` OK, axioms clean.
  - Wired in `GaloisForLFunctions/RHTower.lean` after `WeilPoleWeightAtMostOne` (2026-10-14).
- **Final paper statement:** a Dirichlet series with real coefficients, a₁ = 1, gamma factor Γ_ℝ(s)^d, conductor 1, finite order and only critical zeros is ζ^d.
  - Remaining paper inputs: the Hadamard product, Weil's explicit formula, and PNT for T (for the linear bound), plus summability of λ_T for σ > 1.
