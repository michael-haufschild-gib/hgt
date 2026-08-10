# Euler q-Gamma process, random-integer law, zeta-divisor translation — Lean certification

- **ID:** ULF-EQG-1
- **Paper card:** `euler-q-gamma-process-zeta-divisor-translation-law.md`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Model

The local datum at a prime `p` is the real nome `q_p = p^{-σ}` with `σ > 1`, carried by the corpus
structure `RealEulerNome`; the local response is Jackson's `Γ_{q_p}` as the plain function
`qGammaOn`.  The global objects are indexed by `Nat.Primes`, and the arithmetic side is the
Dirichlet series `eqgDirichlet σ w = ∑' m, eqgTerm σ w m`, whose Euler product is the corpus's
`EulerProduct.eulerProduct_hasProd`.  The pulled-back variable is `eqgExponent σ s = σ(1+s)`, and
the analytic continuation is presented by explicit *cuts* `eqgCont σ K` — the zeta ladder truncated
after `K` steps times the Dirichlet series at the shifted argument — rather than by an abstract
continuation, so every statement about it is a finite algebraic identity plus a convergent tail.

Three pieces of general infrastructure were built here and are reusable outside this card:

* **Reciprocal closure of differential algebraicity.**  The jets of `1/g` are the reciprocal
  numerators `A_j` of the jets of `g` divided by `g^{j+1}`; realising the substitution
  `y_j ↦ A_j/g^{j+1}` as a polynomial map and clearing the single denominator `g^{(n+1)·deg P}`
  transports an algebraic differential equation for `f` to one for `1/f`.  That the substitution
  kills no polynomial is proved by testing on the digamma pair `ψ, 1/ψ` on the open locus where
  `ψ` is analytic and invertible, propagating off the poles by the identity theorem, and invoking
  the corpus's Hölder theorem `digamma_jet_annihilator_eq_zero`.
* **Differential algebraicity on a domain.**  The meromorphic jet field bridge is already stated
  for an arbitrary open preconnected infinite domain, so products, quotients and translations of
  domain-local algebraic differential equations are available there; a relation valid on a nonempty
  open subset propagates over the whole preconnected domain, and multiplying by `(s − p)` carries
  it across a single missing point.
* **Genus-one deviation calculus.**  The Euler unit `E₁(w) = (1−w)eʷ` is the Weierstrass
  elementary factor of genus one, so the corpus's `norm_weierstrassFactor_sub_one_le` gives
  `‖E₁(w) − 1‖ = O(‖w‖²)` on the half disc; combined with `‖u⁻¹ − 1‖ ≤ 2‖u − 1‖` and
  `‖uv − 1‖ ≤ a + b + ab` this turns each renormalised piece of the local response into `1 + O(·)`.

## Certified declarations, by theorem

| Theorem | Lean |
|---|---|
| 3.1 (global law), EQG.6/7 | `eqgWeight`, `eqgWeight_mul`, `summable_eqgWeight`, `eqgEulerProduct`, `eqgTotal`, `eqgConst_hasProd`, `eqgMass_hasSum_one` |
| the arithmetic series | `eqgTerm`, `eqgTerm_mul`, `eqgTerm_local_hasSum`, `eqgDirichlet_eulerProduct` |
| 4.1, EQG.11 | `eqgExponent`, `qGammaOn_eqgNome_factor`, `exp_eqgLogUnit_eq_zeta_inv`, `eqgResponse_hasProd`, `eqgDirichlet_eq_lawTransform` |
| EQG.13/14/15 | `eqgLocalFactor_shift`, `eqgDirichlet_shift`, `eqgResponse_translation`, `eqgResponse_zero`, `eqgResponse_one`, `eqgTilt_hasSum_one` |
| 5.1 (ladder) | `tendsto_eqgDirichlet_shift_one`, `eqgDirichlet_ladder_step`, `eqgDirichlet_ladder`, `eqgResponse_ladder` |
| analyticity | `hasDerivAt_eqgDirichlet`, `analyticAt_eqgDirichlet`, `analyticAt_eqgDirichlet_arg` |
| continuation | `meromorphicAt_comp_affine`, `eqgCont`, `eqgCont_eq_response`, `meromorphicAt_eqgCont`, `eqgCont_translation` |
| 6.1, EQG.17 | `meromorphicOrderAt_comp_affine`, `meromorphicOrderAt_zeta_exponent`, `eqgCont_order_transgression` |
| EQG.18 (landing) | `eqgDirichlet_ne_zero`, `analyticAt_eqgCont`, `eqgCont_ne_zero`, `eqgLandingPoint`, `eqgCont_order_at_zeta_zero`, `eqgCont_landing_translate_ne_zero` |
| 8.1 (observer) | `eqgObservable`, `exp_eqgObservable`, `tendsto_eqgObservable_atBot`, `eqgResolvent`, `isCompactOperator_eqgResolvent` |
| GNS realization | `eqgOmega`, `eqgOrbit`, `eqgCharProc_eq_inner`, `eqgCharProc_eq_response`, `exists_eqgOrbit_near_eqgOmega` |
| 7.1 (hypertranscendence) | `recipNum`, `recipNum_eval`, `recipNum_ne_zero`, `recipSub`, `eval_recipSub`, `recipSub_eq_zero_iff`, `differentiallyAlgebraicOn_inv`, `differentiallyAlgebraicOn_mul`, `differentiallyAlgebraicOn_div`, `DifferentiallyAlgebraicOn.comp_add_const`, `analyticAt_jetEval`, `differentiallyAlgebraicOn_mono_of_isPreconnected`, `differentiallyAlgebraic_of_on_compl_singleton`, `hypertranscendental_eqgZetaPullback`, **`not_differentiallyAlgebraicOn_eqgResponse`**, `not_differentiallyAlgebraicOn_eqgCont` |
| 9.1, algebraic core (EQG.20/21/24) | `eqgActivation`, `eqgActivation_diff`, `eqgRenormLocal`, `eqgRenormLocal_exchange`, `eqgRenormLocal_exchange_finset` |
| 9.1, analytic half (EQG.22/25) | `eqgRenormLocal_factorization`, `norm_eqgPowerFactor_sub_one_le`, `eqgRenormPochhammer`, `norm_eqgRenormPochhammer_sub_one_le`, `norm_eqgRenormLocal_sub_one_le`, `summable_eqgRenormLocal_sub_one`, **`multipliable_eqgRenormLocal`**, **`eqgRenormProduct_ne_zero`**, **`hasProdLocallyUniformlyOn_eqgRenormLocal`**, **`differentiableOn_eqgRenormProduct`** |

## What the certification does and does not say

The certified content is the *field theorem*: composition of the local q-Gamma processes forces a
source-normalized translation equation whose Cartier divisor is the pulled-back complete zeta
divisor, the response is hypertranscendental, the arithmetic observable has compact resolvent, and
the genus-one renormalisation erases the whole translation divisor while remaining holomorphic and
zero-free on `Re s > 1/(2σ) − 1`.

None of this is a statement about the location of the zeros.  The divisor transgression
`ord_{a} F^{K+1}_σ = ord_{σ(1+a)} ζ + ord_{a+1} F^{K}_σ` is an identity of orders valid at every
point; the landing theorem places the multiplicity of a zeta zero `ρ` at `a_ρ = ρ/σ − 1` using only
that one step to the right of `a_ρ` lands in the region where `ζ` is holomorphic and zero-free.
Nothing in the card constrains `Re ρ`, and the genus-one erasure is divisor-blind by construction.

## Verification

Targeted foreground `lake env lean` on every new module is green; the universal-law-field umbrella
`GaloisForLFunctions.HTGeometry.UniversalLawField` builds green at 11 575 jobs; `#print axioms` on
`not_differentiallyAlgebraicOn_eqgResponse`, `not_differentiallyAlgebraicOn_eqgCont`,
`multipliable_eqgRenormLocal`, `eqgRenormProduct_ne_zero`,
`hasProdLocallyUniformlyOn_eqgRenormLocal`, `differentiableOn_eqgRenormProduct`,
`eqgCont_order_at_zeta_zero`, `eqgCont_translation`, `isCompactOperator_eqgResolvent` and
`eqgMass_hasSum_one` reports only `propext`, `Classical.choice`, `Quot.sound`.
