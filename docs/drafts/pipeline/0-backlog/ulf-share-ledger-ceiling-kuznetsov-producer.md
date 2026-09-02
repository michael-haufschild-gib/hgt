# Share ledgers are capped; the only created positivity is automorphic: the Kuznetsov producer for the corpus's own missing spectral average

- **ID:** `ULF-SLC-001`
- **Stage:** 0-backlog
- **Type:** CANDIDATE (ceiling theorem for one mechanism family + one producer programme + one open successor conjecture)
- **Source:** learn-from-failure of `ULF-PIO-001` (refuted by `RHTower.polePlane_index_blind`); replaces the
  first draft `ulf-budget-ceiling-vacuum-annihilation.md` (withdrawn: it identified the G-CE critical Ward
  coefficient with a pole vacuum, which the Lean definition contradicts, and it reused the word
  "budget", already fixed in `RHTower.ArchimedeanBudgetConstant` for the Weil archimedean allowance).
  Locks and modules checked: `MobiusGammaXiCoupledErrorDebtCancellationDichotomy`,
  `GammaSewnMobiusXiWardHardyTransport` (`xiAntiCausalWardSchwarzPairResponse`,
  `continuedXiAntiCausalWardResponse`), `MobiusGammaXiGraphNormalComplementTangent`
  (`continuedXiAntiCausalWardResponse_half_eq_zero_iff_rh`), `CCMRectangularDirichletLandau`
  (`xiRightCenteredZero = I·xiSpectralPoint`, i.e. `ρ − 1/2`), `PolePurchaseLogDerivIdentity`,
  `PolePurchaseCollisionGap`, `ZetaZeroFreeRegion`, `ArchimedeanBudgetConstant`,
  `BudgetAndResolutionAreOneResource`, `RiemannGaussian.PairHyperbolicEnergy`,
  `RiemannGaussian.SymmetricQuartetEnergy`, `LandauRelativeRigidity`, the eight `Sieve/Kloosterman*`
  modules of 2026-09-02, `Sieve/StadlmannEquidistributionParameters`; STATUS F340–F364, MUST-112–115,
  F364; frontier map 2026-09-02 (E, RG, D2, HC, LI, G-CE, Stadlmann bridge paragraph).
- **Surviving edge cited (pre-conjecture gate):** E's Ramaré front and T1, where the Kloosterman modules
  state verbatim that the "Kuznetsov–Deshouillers–Iwaniec spectral estimate" is "still missing"
  (`KloostermanSharedHybridCollapse`, `KloostermanHybridResidueParseval`,
  `KloostermanPhysicalResidueModulusBilinear`), and MUST-115's demand for a polarized completion with
  an exact reconstruction law before diagonal scalarization.
- **Statement:** Every RH statement of the form `L = Σ_ρ φ(ρ)` with a fixed weight `φ` (a *share
  ledger*) falls into one of three classes by how `φ` weights an off-line zero
  `ρ = (1+a)/2 + iγ` against its height; in each class any *inequality* on `L` is height- or
  width-limited (Ceilings C1–C3), the only pole-side exception is pole-share cancellation, itself
  capped (C4). Hence an RH producer must be an *exact identity whose arithmetic side is manifestly
  a sum of squares* (created positivity). The corpus contains no created positivity; the one that
  exists in ζ-theory is automorphic (Petersson/Kuznetsov, Katok–Sarnak), and the corpus's newest
  modules already name its absence as the blocker of Route E's cross-modulus cancellation.

## Goal

1. A ceiling theorem, in the genre of `lindelof-method-ceilings.md`, that discharges the
   pre-conjecture gate for every future pole / index / vacuum / scalar-Ward estimate in one stroke.
2. A sharp new no-go on the G-CE edge (its coefficient is a fixed-point ledger, so no estimate on it
   can be a producer).
3. The first *created* positivity in the corpus: the Petersson and Kuznetsov trace formulas and the
   Deshouillers–Iwaniec Kloosterman large sieve, which E/T1/Stadlmann consume directly.
4. The RH-bearing successor, stated as open: a spectral decomposition of the Weil functional into
   created squares.

No RH closure is claimed. Items 1–3 are unconditional theorems; item 4 is the open core.

## What the failure teaches, verified against the Lean definitions

The pole plane of `ULF-PIO-001` is the residue pairing of the two poles of `Λ`; reading the index
from it was reading a *share*: the contribution of a zero to a Hadamard-type sum at a fixed point.
Concretely, the G-CE critical coefficient is such a share sum. From the definitions
(`xiAntiCausalWardSchwarzPairResponse q w = 2((w+z)⁻¹ + (w+z̄)⁻¹)`, `z = ρ − 1/2`, `Re z > 0`,
`Im z > 0` for `q : XiRightUpperZeroCopy`):

```text
d := continuedXiAntiCausalWardResponse (1/2) = Σ_{Re ρ>1/2, Im ρ>0} 2(1/ρ + 1/ρ̄) = 4 Σ_{off-line upper} β/|ρ|².
```

So `d` is four times the off-line part of `Σ_ρ Re(1/ρ)` (Li's `λ₁`, whose full sum is
`1 + γ/2 − log(4π)/2`), evaluated at the second pole `s = 0`. Each off-line zero at height `γ` enters
with weight `≍ 1/γ²`. That is the whole reason `d = 0 ⟺ RH` is an exact receiver while no bound on
`d` can count zeros.

## Share ledgers and their three classes

`L = Σ_ρ φ(ρ)`, absolutely convergent, with `ρ = (1+a)/2 + iγ`, `a = 2Re ρ − 1`.

| Class | weight of an off-line zero | examples in the corpus | what an inequality on `L` can prove |
|---|---|---|---|
| I fixed-point: `φ = Re 1/(s₀−ρ)`-type | `≍ 1/γ²` | G-CE `d` (`s₀ = 0`); `λ₁`; pole functional at real `σ > 1`; HC bounded diagonal per window | no off-line zero with `|ρ − s₀| ≤ C/√ε` |
| II aligned: `s₀ = σ + iγ` moves with the zero | `≍ 1/(σ−β)` against `O(log t)` growth | de la Vallée Poussin pole purchase (`PolePurchase*`, `ZetaZeroFreeRegion`); D2 threshold; quartet radius bound (`SymmetricQuartetEnergy`) | width `≤ c/log t`, `c` capped by C2 |
| III amplified: `φ = 1 − ((ρ−1)/ρ)^n` (Li) or `f̂(ρ)²` at support/width `L` | `exp(n·a/(2|ρ|²))`, resp. `exp(aL/2)` against background `(n/2)log n`, resp. `‖f‖²` | LI all-degree nonnegativity; RG Gaussian widths; Weil form on apertures (O, CCM) | zeros with `|ρ|² ≲ n·a/log n`, resp. `aL ≳ log|ρ|`; RH needs all `n`/`L`, i.e. square-root cancellation at scale `e^{n}` |

**C1 (fixed-point ceiling; Lean-ready on the actual G-CE coefficient).** For every off-line upper
zero, `d ≥ 4β/|ρ|² > 2/|ρ|²`. Hence `d ≤ ε` implies every off-line zero has `|ρ| ≥ √(2/ε)`. No
source-side estimate of the scalar Ward channel is a producer; the G-CE "non-erasing annihilation"
must be an exact identity `d = 0`, which is the receiver itself
(`mobiusGammaXiDebtController_nonerasingCancellation_iff`).

**C2 (aligned trigonometric ceiling).** If `P(θ) = Σ_{k≤K} a_k cos kθ ≥ 0` then `a₁ ≤ 2a₀`; and
with `L = C log t`, `S = Σ_{k≥1}|a_k| ≥ a₁`, for every `η ≥ (3−2√2)/(2L)` and every `δ > 0`,
`a₀/δ + LS ≥ a₁/(δ+η)`. So no nonnegative cosine polynomial and no alignment can certify a zero-free
width beyond `(3−2√2)/(2C log t)`; the pole-purchase family returns `c/log t` at best. (Numerically
checked as guidance; proof is the maximisation of `u(1−u)/(1+u)` at `u = √2 − 1`.)

**C3 (amplified ceiling).** For Li, an off-line pair contributes `−2r^n cos nθ + O(1)` with
`log r = ½ log(1 + |a|/|ρ|²) ≈ |a|/(2|ρ|²)`; it dominates the on-line background `(n/2) log n`
only for `n ≳ 2|ρ|² log|ρ| / |a|`. Any certificate of `λ_n ≥ 0` up to degree `N` therefore excludes
only off-line zeros with `|ρ|² ≲ N|a|/log N`, and its arithmetic side (Bombieri–Lagarias binomial
sums of Stieltjes constants) must be exact to relative precision `r^{−n}`. The same holds for Weil
tests of support `L` and Gaussian widths. This is the ledger form of "open content is signed
arithmetic cancellation".

**C4 (pole-share cancellation is the unique pole-side quantization; two firewalls).** In a family
`F = ζ·ΠL(s,χ)` with nonnegative log-coefficients, a real zero `β₁` of some `L(s,χ₁)` draws the share
`1/(σ−β₁)`, which tends to the whole pole term `1/(σ−1)` as `β₁ → 1`; Landau–Page ("at most one") is
the only classical integer-valued conclusion of a share ledger, and Deuring–Heilbronn repulsion is its
RH-strength limit. Firewall 1: Siegel's theorem, proved by the same ledger on
`ζL(χ₁)L(χ₂)L(χ₁χ₂)`, forces `1 − β₁ ≫_ε q^{−ε}`, so repulsion yields at most fixed strips.
Firewall 2 (Lean-ready from `landau_relative_rigidity`): a nonnegative generalized-prime perturbation
`E = exp(Σ a_j e^{−λ_j s})` with `ζ(β₁)E(β₁) = 0`, `β₁ ∈ (0,1)` real, has abscissa `σ_c ≥ β₁` and is
not analytic at `σ_c`: on the real axis right of `σ_c` the exponent is `≥ 0` so `E ≥ 1`, hence
`E(σ_c) ≠ 0` if analytic, hence `E'/E` would continue the derivative series `−Σ a_jλ_j e^{−λ_j s}`
(same abscissa, nonnegative coefficients) across its Landau point. So `ζE` has no Hadamard ledger and
no surrogate exceptional zero can be manufactured from positive mass. None of C4 is in the corpus.

## Frontier readings (tests, not assertions)

- **G-CE:** class I; C1 applies; the edge is an identity or nothing.
- **RG / O / CCM aperture forms:** class III; the corpus's `W(g) ≥ 0.35·g(0) − 2E(g)` reduces RH to
  `E(g) ≤ 0.17·g(0)` on unbounded widths, i.e. square-root cancellation at scale `e^{width}`.
- **LI:** class III; C3 gives the degree needed per zero.
- **D2:** class II with a fixed threshold `141858/10000`; this is why fixed finite prefixes fail
  cofinally and "successful control must deepen with height".
- **HC:** class I per window; bounded receivers for all windows are RH.
- **Completion index (MUST-65–69), pole plane, twisted Möbius (FAIL-28):** class I; already killed
  in their own vocabulary (F180, CANNOT-100, `polePlane_index_blind`).

## The uncapped class, and where the corpus already needs it

An RH producer must be an exact identity with a manifestly nonnegative arithmetic side. In ζ-theory
the only such identities not manufactured by hand are automorphic: the Petersson and Kuznetsov trace
formulas (Kloosterman sums = spectral side with `|ρ_j(m)ρ_j(n)|`-type squares), and the
Katok–Sarnak/Waldspurger squares `L(1/2, u_j) = c·|θ-lift coefficient|² ≥ 0`. Their known
consequences are unconditional and not RH-equivalent: the Deshouillers–Iwaniec large sieve for
Kloosterman sums, levels of distribution beyond `1/2` (Bombieri–Friedlander–Iwaniec, Zhang, Maynard,
Stadlmann), and Motohashi's fourth-moment formula. The corpus has none of them, and its own newest
modules stop exactly there: `KloostermanSharedHybridCollapse` ("the still-missing Kuznetsov spectral
average"), `KloostermanHybridResidueParseval` ("does not assert the Deshouillers–Iwaniec spectral
estimate"), `KloostermanPhysicalResidueModulusBilinear` ("cancellation-bearing finite carrier for a
later Kuznetsov–Deshouillers–Iwaniec estimate"), and `StadlmannEquidistributionParameters`
("analytic equidistribution conclusions are not postulated here").

**Programme (build it):**
1. Petersson trace formula for holomorphic cusp forms of weight `k ≥ 2` and level `N`: Poincaré
   series, Fourier coefficients, orthonormal basis, `Σ_f |ρ_f(m)ρ_f(n)|`-side equals
   `δ_{mn} + 2πi^{−k} Σ_c S(m,n;c)/c · J_{k−1}(4π√(mn)/c)`. This is the first created positivity
   available to the corpus and needs only holomorphic modular forms.
2. Kuznetsov (Bruggeman–Kuznetsov) formula for `SL₂(ℤ)` and `Γ₀(N)`: Maass spectrum + Eisenstein
   continuous spectrum; this is the object the Kloosterman modules name.
3. Deshouillers–Iwaniec large sieve for Kloosterman sums (their Theorems 9–12 shapes): the input to
   Stadlmann's Lemmas 3, 4, 7 and to the Type-II ranges of MT Lemma 3.5.
4. Consumers already wired: `StadlmannEquidistributionParameters` gates, MT 3.5 complement,
   E's inter-aperture residual, Kloosterman cross-modulus correlation.

## Successor conjecture (open; the correct replacement of `Ind₊ = 1`)

`[CONJECTURE, ULF-SLC-Q]` The Weil functional `W(g)`, `g = f * f̃`, admits an unconditional
decomposition `W(g) = Σ_j |c_j(f)|² + (archimedean/Yoshida part)` with `c_j` produced by an
automorphic spectral identity (a Kuznetsov-type reciprocity between the prime side
`Σ Λ(n)n^{−1/2}(g(log n)+g(−log n))` and a discrete spectrum), so that positivity is created rather
than assumed. First testable instance: express the fixed-aperture Weil form on supports up to
`log 4` (primes `2, 3`) through a Petersson/Kuznetsov identity and check whether the resulting
spectral side is manifestly nonnegative; the corpus's small-aperture theorems (`SuzukiSmallAperture*`,
`archimedean-weil-kernel-sign-and-aperture`) give the archimedean half. If no such decomposition
exists on any fixed support beyond the archimedean one, the created-positivity route stops at averaged
statements (levels of distribution) and RH is untouched by it.

## Falsifiers

- F1 (kills C1's use): a source-side inequality on `d` whose exclusion radius grows faster than
  `ε^{−1/2}`. Excluded by `d ≥ 2/|ρ|²`.
- F2 (kills C2): a nonnegative cosine polynomial certifying width `> (3−2√2)/(2C log t)` with the same
  inputs. Excluded by the algebra.
- F3 (kills C4 firewall 2): a positive-mass perturbation creating a real zero `β₁ < 1` with `ζE`
  analytic on `[β₁, 1)`.
- F4 (kills the successor): every Kuznetsov-type identity for the fixed-aperture Weil form has a
  spectral side that is not sign-definite for some `f`.

## Lean bricks (order; the first four are unconditional and cheap)

1. `gceCriticalCoefficient_eq_four_tsum_re_inv`: `d = 4 Σ_{q : XiRightUpperZeroCopy} Re(1/ρ_q)` from
   `continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs` and `xiRightCenteredZero`.
2. `gceCriticalCoefficient_le_excludes_low_zeros`: `d ≤ ε → ∀ q, 2/ε ≤ |ρ_q|²`.
3. `trigPurchase_ratio_le_two`, `polePurchase_width_cap`: C2.
4. `gdSeries_deriv_same_abscissa`, `no_surrogate_annihilator`: C4 firewall 2, from
   `landau_relative_rigidity`, `gdSeries_no_continuation_at_abscissa`,
   `riemannZeta_ne_zero_of_ofReal_mem_Ioo`.
5. `landauPage_at_most_one_exceptional` (paper first; needs the local Borel–Carathéodory zero-sum
   bound for `L(s,χ)`; `RHTower.ArgumentVariation.borel_caratheodory` exists).
6. Petersson trace formula (weight `k`, level `1` first); then Kuznetsov; then the Kloosterman large
   sieve. Mathlib has modular forms, Eisenstein series, and `ModularForm` spaces but no Poincaré series,
   Petersson inner product, or spectral theory; all three must be built.

## Gates
- [ ] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Hostile audit
- "The ceiling is folklore." The classification with explicit weights is not written anywhere in
  the corpus, C1 on the actual G-CE coefficient is new, C2's constant is new, C4 is absent.
- "Kuznetsov is a receiver dressed up." It is not RH-equivalent: its outputs are unconditional
  theorems the corpus's E/T1/Stadlmann lanes are waiting for, named as missing in today's modules.
- "The successor conjecture is Connes–Consani." CCM builds positivity from a scaling-site operator;
  the successor asks for automorphic spectral positivity (theta-correspondence squares), which the
  corpus has never engaged; it is stated with a falsifier and no closure claim.
- "This does not close RH." Correct, and stated. It closes a family of mechanisms and redirects effort
  to the one created positivity the corpus itself needs.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** —
- **Strongest positive survivor:** —
- **New insight:** —
- **Status:** —

## Log
- 2026-09-02 — first draft (budget/vacuum-annihilation card) withdrawn after checking the G-CE
  definitions and the existing `ArchimedeanBudgetConstant` usage; replaced by this card. Corpus
  searches: no Landau–Page, Deuring–Heilbronn, Siegel, Petersson, Kuznetsov, Katok–Sarnak,
  Motohashi-spectral material; Kloosterman modules and Stadlmann gates present and explicitly waiting
  for the spectral average.

## Lean (2026-09-02, bricks 1–4 closed)

| Brick | Module | Headline theorems | Status |
|---|---|---|---|
| 1–2 | `RHTower/GCECriticalCoefficientHeightBound.lean` | `gceCriticalCoefficient_eq_tsum` (`d = Σ_q ↑(4·Re(1/ρ_q))`), `re_gceCriticalCoefficient_eq_tsum`, `two_div_norm_sq_lt_share`, `gceCriticalCoefficient_le_excludes_low_zeros` (`d.re ≤ ε → 2/ε < |ρ_q|²`), `sqrt_two_div_lt_norm_gceOffLineZero`, `gceOffLineZero_eq_divisorPoint` | `lake env lean` clean, olean, `lake build` green, axioms `propext/choice/Quot.sound` |
| 3 | `HTGeometry/CosinePolynomialPurchaseCap.lean` | `cosinePolynomial_purchase_ratio_le_two` (`a₁ ≤ 2a₀`), `purchase_width_cap` (`η ≥ (3−2√2)/(2L) → a₁/(δ+η) ≤ a₀/δ + L·S`), `integral_cos_mul_cos_nat_mul` | same |
| 4 | `RHTower/NoSurrogateAnnihilator.lean` | `hasDerivAt_gdSeries` (termwise derivative on the open half-plane), `summable_gdTwistTerm_one_of_lt`, `not_summable_gdTwistTerm_one_of_lt`, `no_surrogate_annihilator` (`β₁ ≤ σ_c ∧ ∀ r > 0, ¬ DifferentiableOn ℂ E (ball σ_c r)`) | same |

Wired: `HTGeometry.lean` (after `ConfluentVanishingPolynomial`), `RHTower.lean` (after
`FunctionalEquationParity` and after `NoObstructionOnlyAConstruction`). The no-surrogate theorem
assumes frequencies `λ_j ≥ c > 0` (true for every generalized-prime system with least prime `> 1`);
the derivative-series divergence left of the abscissa uses it.

## Lean (2026-09-02, brick 5 closed: Landau–Page for two quadratic characters)

The pole-side quantization of C4 is now a theorem, by values rather than by Hadamard zero sums:

| Module | Headline theorems |
|---|---|
| `RHTower/DirichletCharacterPartialSumBound.lean` | `norm_dirichletCharacter_sum_range_le` (`‖Σ_{m<n} χ(m)‖ ≤ N`), `norm_sum_ofReal_mul_le_of_bounded_partial` (Abel), `norm_LFunction_le_three_mul_modulus` (`‖L(σ,χ)‖ ≤ 3N`, real `σ > 1`, `χ ≠ 1`) |
| `RHTower/QuadraticCharacterFourfoldProduct.lean` | `hasDerivAt_LFunction_ofReal_of_isQuadratic`, `twistRe_sum_eq` (`Λ(n)n^{-σ}1_N(n)(1+χ₁(n))(1+χ₂(n))`), `hasDerivAt_fourfoldProduct_ofReal` (`F' = −F·W`, `W ≥ 0`), `fourfoldRe_pos`, `fourfoldRe_antitoneOn`, `fourfoldRe_ge` (`(2−π²/6)³ ≤ F(σ)` on `(1,2]`) |
| `RHTower/LandauPageTwoQuadratic.lean` | `norm_deriv_LFunction_le_of_primitive` (Cauchy on the CGL strip: `‖L'(x,χ)‖ ≤ 1728·C·N²` on `[3/4,5/4]`), `norm_LFunction_le_of_real_zero` (mean value), `norm_LFunction_one_le_pole` (`‖L(1+δ,1_N)‖ ≤ 1/δ+2`), `landau_page_two_quadratic`: for distinct primitive quadratic `χ₁, χ₂ mod N` with real zeros `β₁, β₂ ≤ 1`, `landauPageWidth N ≤ max(1−β₁, 1−β₂)`, `landauPageWidth N = (2−π²/6)³/(18·(1728·C·N²)²·N)` |

All `lake env lean` clean with zero warnings; axioms `propext/Classical.choice/Quot.sound`. The width
is `≍ N^{-5}` rather than the classical `c/log N`: the values route pays the conductor-uniform
strip bound `q²(1+|t|)²` instead of a Hadamard zero-sum bound. Sharpening to `c/log N` needs the
local Borel–Carathéodory zero-sum lemma (`ArgumentVariation.borel_caratheodory` exists) and the
partial-summation representation of `L(s,χ)` on `0 < Re s ≤ 1`; both are listed as the next bricks.

## Brick 6 programme (created positivity), scoped against mathlib on 2026-09-02

Available in mathlib: `ModularForm`, `CuspForm`, slash actions, level-one dimension formulas,
`q`-expansions, Eisenstein series with locally uniform convergence for `k ≥ 3`
(`eisensteinSeries_tendstoLocallyUniformly`), and the Petersson *integrand*
(`UpperHalfPlane.petersson`, weight-`0` invariance). Not available anywhere: Poincaré series
of weight `k`, the Petersson inner product as an integral over a fundamental domain, Bessel `J_ν`,
unfolding, Maass forms, Kuznetsov.

- 6a `HolomorphicPoincareSeries`: `P_m(z) = Σ_{Γ∞\Γ} j(γ,z)^{-k} e(m·γz)`, level one, `k ≥ 3`;
  absolute locally uniform convergence by domination with the Eisenstein summand
  (`|e(mγz)| ≤ 1` on `ℍ`), slash invariance, holomorphy, cuspidality for `m ≥ 1`.
- 6b Fourier coefficients of `P_m`: `δ_{mn} + 2πi^{-k} Σ_c S(m,n;c)/c · J_{k-1}(4π√(mn)/c)`; needs
  Bessel `J_ν` as a power series and the classical integral of `(x+iy)^{-k} e(−nx − m/(c²(x+iy)))`.
  Corpus has `Sieve/KloostermanSum` and the Ramanujan-unfolding pattern of the real-analytic
  Poincaré modules (`ThetaCuspHawkingBMEisensteinPoincareRamanujanUnfolding`).
- 6c Petersson inner product on level one: invariant measure `dx dy / y²`, integral over the
  standard fundamental domain, unfolding `⟨f, P_m⟩ = Γ(k−1)/(4πm)^{k−1} · a_f(m)`.
- 6d Petersson formula: orthonormal basis of the finite-dimensional `S_k`, `P_m = Σ_f ⟨P_m,f⟩ f`,
  hence `Σ_f a_f(m) a_f(n)‾ / ⟨f,f⟩ = (4π√(mn))^{k−1}/Γ(k−1) · [δ_{mn} + 2πi^{-k} Σ_c S(m,n;c)/c J_{k−1}(…)]`.
  This is the first created positivity available: the left side is a sum of squares at `m = n`.
- 6e Kuznetsov (Maass spectrum + Eisenstein continuous spectrum) and 6f Deshouillers–Iwaniec:
  require the spectral theory of the hyperbolic Laplacian on `Γ\ℍ`, absent from mathlib; multi-month.

Order of build: 6a → 6c → 6d (holomorphic Petersson formula, self-contained), 6b in parallel,
6e–6f only after a Maass-form foundation exists.
