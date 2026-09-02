# Share ledgers are capped; the only created positivity is automorphic: the Kuznetsov producer for the corpus's own missing spectral average

- **ID:** `ULF-SLC-001`
- **Stage:** 5-failed (RH producer falsified 2026-09-02; ceilings and Petersson formula are Lean theorems)
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

## Lean (2026-09-02, brick 6a closed: holomorphic Poincaré series are modular forms)

Corpus check before building: no holomorphic Poincaré series existed (the `ThetaCuspHawkingBM*`
Poincaré modules are the real-analytic Eisenstein family with seed `(y/|cz+d|²)^s`; the
`QuasiAbelianPoincareSeries` modules are theta-function Poincaré series on `ℂ^d`; `coprimeCuspMatrix`
prescribes a first column). Mathlib's `EisensteinSeries.gammaSet 1 1 0`, `eisSummand`, the strip
bounds and `gammaSetEquiv` are reused; nothing from them is duplicated.

| Module | Headline theorems |
|---|---|
| `HTGeometry/HolomorphicPoincareSeries.lean` | `bottomRowMatrix` (determinant one with prescribed coprime bottom row), `exists_int_top_row_of_bottomRow_eq`, `coe_smul_eq_coe_smul_add_int_of_bottomRow_eq` (same bottom row ⇒ Möbius images differ by an integer), `poincareSummand`, `poincareSeries k m z = Σ_{(c,d) coprime} (cz+d)^{-k} e(m·M_{c,d}z)`, `norm_poincareSummand_le`, `summable_poincareSummand`, `poincareSeries_tendstoLocallyUniformly`, `poincareSummand_SL2_apply`, `poincareSeries_slash_apply` (`P_m ∣[k] γ = P_m`) |
| `HTGeometry/HolomorphicPoincareSeriesModularForm.lean` | `poincareSummand_extension_differentiableOn`, `poincareSeries_mdifferentiable`, `poincareSeriesSIF`, `norm_poincareSeries_le_tsum_norm`, `isBoundedAtImInfty_poincareSeries`, `poincareSeriesMF : ModularForm 𝒮ℒ k` for `k ≥ 3` |

Both `lake env lean` clean with zero warnings, axioms `propext/Classical.choice/Quot.sound`.
Still open in 6a: cuspidality for `m ≥ 1` (`IsZeroAtImInfty`), which needs the tail estimate
`Σ_{c≠0} |cz+d|^{-k} ≪ y^{1−k}`; mathlib's Eisenstein boundedness argument gives only a constant.

## Lean (2026-09-02, brick 6a fully closed: `P_m` is a cusp form for `m ≥ 1`)

| Module | Headline theorems |
|---|---|
| `HTGeometry/HolomorphicPoincareSeriesCuspForm.lean` | `gammaSet_snd_eq_of_fst_eq_zero` (the two pairs `(0, ±1)`), `norm_poincareSummand_le_exp_of_fst_eq_zero` (`‖term‖ ≤ e^{−2πmy}`), `im_le_norm_linear_of_fst_ne_zero` (`|cz+d| ≥ y` for `c ≠ 0`), `norm_poincareSummand_le_of_fst_ne_zero` (`≤ y^{−1/2}·r^{−(k−1/2)}‖(c,d)‖^{−(k−1/2)}` on a vertical strip), `tsum_ite_fst_eq_zero_le` (at most two `c = 0` pairs), `norm_poincareSeries_le_of_two_le_im` (`‖P_m(z)‖ ≤ 2e^{−2πmy} + C_k y^{−1/2}` for `y ≥ 2`), `tendsto_poincareCuspBound_atTop`, `isZeroAtImInfty_poincareSeries`, `poincareSeriesCF : CuspForm 𝒮ℒ k` (`k ≥ 3`, `m ≥ 1`), `coe_poincareSeriesCF` (same function as `poincareSeriesMF`) |

Mechanism: the `y^{−1/2}` decay is extracted by splitting `|cz+d|^{−k} = |cz+d|^{−1/2}·|cz+d|^{−(k−1/2)}`
and using mathlib's strip bound with the real exponent `k − 1/2 > 2`; this avoids the classical
`y^{1−k}` tail estimate entirely.

## Lean (2026-09-02, brick 6c started: the modular fundamental domain, measure-theoretically)

Neither mathlib nor the corpus had `ModularGroup.fd` as a `MeasureTheory.IsFundamentalDomain`
(mathlib has the set-theoretic facts `exists_smul_mem_fd`, `eq_one_or_neg_one_of_mem_fdo_mem_fd`,
`coe_fd`, the invariant measure `dx dy/y²` and its `GL(2,ℝ)`-invariance; the corpus's only
fundamental-domain unfoldings are Connes' idelic ones).

| Module | Headline theorems |
|---|---|
| `HTGeometry/ModularFundamentalDomainMeasure.lean` | `PSL2Z := SL(2,ℤ) ⧸ ker(action)` with its faithful `MulAction` on `ℍ`, `MeasurableConstSMul`/`SMulInvariantMeasure` instances for `SL(2,ℤ)` and `PSL2Z`, `neg_one_mem_modularActionKernel`, `volume_re_eq_zero` (vertical lines are Lebesgue-null), `coe_fd_diff_fdo_subset` (boundary ⊆ two lines ∪ unit circle), `volume_fd_diff_fdo` (boundary null for `dx dy/y²`), `fd_inter_smul_fd_subset` (`𝒟 ∩ g𝒟 ⊆ ∂𝒟` for `g ≠ ±1`), `isFundamentalDomain_fd : IsFundamentalDomain PSL2Z 𝒟 volume` |

Next in 6c: coset-representative fundamental domains for a subgroup (general), the strip
`{0 ≤ Re z < 1}` as a fundamental domain for the translations, and the unfolding
`Σ_{(c,d)} ∫_𝒟 φ(M_{c,d} z) = 2 ∫_strip φ` for `T`-periodic `φ`.

## Lean (2026-09-02, brick 6c: unfolding along the translations closed)

| Module | Headline theorems |
|---|---|
| `HTGeometry/ModularStripUnfolding.lean` | `isFundamentalDomain_iUnion_smul_of_cosetReps` (general: a `G`-fundamental domain and right-coset representatives `R : ι → G` of `H ≤ G` give the `H`-fundamental domain `⋃ R i • s`), `translationSubgroup := zpowers (T mod ±1)`, `modularStrip := {0 ≤ Re z < 1}`, `isFundamentalDomain_modularStrip`, `gammaSetHalf` (rows `(c,d)` with `c > 0`, or `(0,1)`) with `gammaSetHalfNegEquiv : half ≃ halfᶜ`, `mem_modularActionKernel_iff` (`ker = {±1}`), `PSL2Z_mk_eq_iff`, `exists_eq_T_zpow_mul_of_bottomRow_eq`, `exists_translation_mul_halfRep` + `translation_mul_halfRep_injective` (`PSL₂(ℤ) = ⊔ ⟨T⟩·M_{c,d}`), `isFundamentalDomain_iUnion_halfRep_smul_fd`, `tsum_setIntegral_fd_eq_two_mul_setIntegral_modularStrip`: for `T`-periodic `φ` integrable on the strip, `Σ_{(c,d) coprime} ∫_𝒟 φ(M_{c,d} z) = 2 ∫_{strip} φ` |

Remaining for 6c: (i) `∫_{strip} F dμ = ∫_0^∞ (∫_0^1 F(x+iy) dx) y^{−2} dy` (density + `ofComplex` +
Fubini), (ii) integrability of `petersson k f (e(m·))` on the strip and of `petersson k f P_m` on
`𝒟` with the `Σ/∫` exchange, (iii) mathlib's coefficient integral and
`integral_rpow_mul_exp_neg_mul_Ioi` to reach `⟨f, P_m⟩ = 2·conj(a_f(m))·Γ(k−1)/(4πm)^{k−1}`.

## Lean (2026-09-02, brick 6c: strip integrals in the chart)

| Module | Headline theorems |
|---|---|
| `HTGeometry/UpperHalfPlaneStripIntegral.lean` | `hyperbolicDensity z = ofReal (y⁻²)`, `volume_eq_comap_withDensity` (mathlib's `dx dy/y²` as comap + density), `stripEquiv : ℂ ≃ᵐ ℝ × ℝ` (`w ↦ (Im w, Re w)`, measure preserving), `stripEquiv_image_coe_modularStrip` (`= (0,∞) × [0,1)`), `stripChartIntegrand F (y,x) = y⁻² • F(x+iy)`, `setIntegral_modularStrip_eq_chart`, `integrableOn_modularStrip_iff`, `setIntegral_modularStrip_eq_iterated` (`∫_{strip} F = ∫_0^∞ y⁻² (∫_0^1 F(x+iy) dx) dy` for `F` integrable on the strip) |

## Lean (2026-09-02, brick 6c: the Petersson integrand of `P_m`)

| Module | Headline theorems |
|---|---|
| `HTGeometry/PoincareSeriesPeterssonIntegrand.lean` | `expSeed m z = e(mz)` (continuous, `T`-periodic, `‖·‖ = e^{−2πmy}`), `expSeed_slash_gammaSetMatrix` (`e_m ∣[k] M_{c,d} = poincareSummand`), `cuspForm_T_zpow_smul`, `petersson_expSeed_gammaSetMatrix_smul` (`ψ(M_{c,d} z) = conj(f z)·summand·y^k` via mathlib's `petersson_slash_SL`), `petersson_poincareSeries_eq_tsum` (`petersson k f P_m = Σ ψ∘M_{c,d}` pointwise), `integrableOn_exp_neg_mul_mul_rpow_Ioi`, `continuousOn_stripChartIntegrand`, `integrableOn_modularStrip_of_bound` (`‖F‖ ≤ C e^{−ay} y^r`, `a>0`, `r>1` ⇒ integrable on the strip), `exists_bound_petersson_expSeed` (`‖ψ‖ ≤ C e^{−2πmy} y^{k/2}` from mathlib's `CuspFormClass.exists_bound`), `integrableOn_modularStrip_petersson_expSeed` (`k ≥ 3`, `m ≥ 1`) |

## Lean (2026-09-02, brick 6c: the Petersson product against `P_m` unfolds)

| Module | Headline theorems |
|---|---|
| `HTGeometry/PoincareSeriesPeterssonUnfolding.lean` | `peterssonInner k f g := ∫_𝒟 petersson k f g`, `peterssonInner_poincareSeries_eq_two_mul_setIntegral_modularStrip`: for a level-one cusp form `f` of weight `k ≥ 3` and `m ≥ 1`, `⟨f, P_m⟩ = 2 ∫_{0 ≤ Re z < 1} conj(f z) e(mz) y^k dμ` (the `Σ/∫` exchange via `integral_tsum_of_summable_integral_norm`, with the absolute unfolding of `‖ψ‖` supplying the summability) |

Remaining for 6c: evaluate the strip integral through Fubini (`setIntegral_modularStrip_eq_iterated`),
mathlib's `ModularFormClass.qExpansion_coeff_eq_intervalIntegral` and
`Real.integral_rpow_mul_exp_neg_mul_Ioi`, giving `⟨f, P_m⟩ = 2·(4πm)^{1−k}Γ(k−1)·conj(a_f(m))`.

## Lean (2026-09-02, brick 6c closed: `⟨f, P_m⟩ = 2 (4πm)^{1−k} Γ(k−1) conj(a_f(m))`)

| Module | Headline theorems |
|---|---|
| `HTGeometry/PoincareSeriesPeterssonCoefficient.lean` | `coeff_qExpansion_eq_setIntegral_Ico` (`a_f(m) = ∫_0^1 e^{−2πim(x+iy)} f(x+iy) dx`, from mathlib's `ModularFormClass.qExpansion_coeff_eq_intervalIntegral`), `petersson_expSeed_ofComplex_mk` (`ψ(x+iy) = y^k e^{−4πmy}·conj(coefficient integrand)`), `setIntegral_Ico_petersson_expSeed`, `setIntegral_modularStrip_petersson_expSeed` (`∫_{strip} ψ = (4πm)^{1−k}Γ(k−1) conj(a_f(m))` via `Real.integral_rpow_mul_exp_neg_mul_Ioi`), `peterssonInner_poincareSeries` : for `f : CuspForm 𝒮ℒ k`, `k ≥ 3`, `m ≥ 1`, `peterssonInner k f (poincareSeries k m) = 2 · ((1/(4πm))^{k−1} Γ(k−1)) · conj(a_f(m))` |

Brick 6c (Petersson inner product on level one + unfolding) is therefore closed in Lean, all
modules `lake build` green, axioms `propext/Classical.choice/Quot.sound`.  What remains of brick 6:
6b (Fourier coefficients of `P_m`: Kloosterman sums and `J_{k−1}`), 6d (finite dimensionality and
positive definiteness of `peterssonInner` on `S_k`, orthogonal expansion of `P_m`), and the
Maass-spectral bricks 6e–6f.

## Lean (2026-09-02, brick 6d started: volume of `𝒟`, positivity of `dx dy/y²`)

| Module | Headline theorems |
|---|---|
| `HTGeometry/ModularFundamentalDomainVolume.lean` | `integrableOn_indicator_im_ge_modularStrip`, `volume_modularStrip_inter_im_ge_lt_top` (truncated strip has finite volume), `fd_subset_union_translate` (`𝒟 ⊆ S ∪ T⁻¹S`), `volume_fd_lt_top` / `volume_fd_ne_top`, `volume_eq_lintegral_ofReal`, instance `IsOpenPosMeasure (volume : Measure ℍ)` (nonempty open sets have positive invariant measure) |

Next in 6d: `peterssonInner` on `CuspForm 𝒮ℒ k` is integrable (bounded × finite volume), Hermitian,
sesquilinear, positive definite (continuity + open positivity + `𝒟 = closure 𝒟ᵒ`), giving an
`InnerProductSpace ℂ` structure on a type synonym; finite dimension from mathlib's level-one
dimension formula; orthonormal expansion of `P_m` ⇒ abstract Petersson formula.

## Lean (2026-09-02, brick 6d: the Petersson inner product space of level-one cusp forms)

| Module | Headline theorems |
|---|---|
| `HTGeometry/PeterssonInnerProductLevelOne.lean` | `integrableOn_fd_petersson` (bounded integrand × finite volume), `peterssonInner_add_right/smul_right/add_left/smul_left`, `peterssonInner_conj_symm` (for arbitrary functions), `petersson_self_eq` (`= ‖f‖² y^k`), `re_peterssonInner_self_nonneg`, `cuspForm_eq_zero_of_forall_mem_fd`, `eq_zero_of_peterssonInner_self_eq_zero` (definiteness via open positivity and `𝒟 = closure 𝒟ᵒ`), `PeterssonSpace k := CuspForm 𝒮ℒ k` with `InnerProductSpace ℂ` (from `peterssonCore : InnerProductSpace.Core`) and `FiniteDimensional ℂ` (mathlib's level-one dimension formula through `CuspForm.toModularFormₗ`) |

## Lean (2026-09-02, brick 6d closed: the abstract Petersson formula for level one)

| Module | Headline theorems |
|---|---|
| `HTGeometry/PeterssonFormulaLevelOne.lean` | `cuspCoeff n f := coeff n (qExpansion 1 f)` with `cuspCoeff_add/smul` and the linear functional `cuspCoeffLinear n : PeterssonSpace k →ₗ[ℂ] ℂ`; `poincarePS`, `peterssonConstant k m = 2 (4πm)^{1−k} Γ(k−1)`; `inner_poincarePS` (`⟨f, P_m⟩ = c_{k,m} conj(a_f(m))`); `cuspCoeff_poincareSeriesCF_eq_sum`: for every orthonormal basis `b` of `S_k` (Petersson product), `a_{P_m}(n) = c_{k,m} Σ_i conj(a_{b_i}(m)) a_{b_i}(n)`; `…_std` for the standard orthonormal basis |

State of brick 6 after this session: 6a (Poincaré series are cusp forms), 6c (Petersson product,
unfolding, `⟨f,P_m⟩`), 6d (inner-product space, finite dimension, orthonormal expansion) are
closed in Lean.  The Petersson formula is now reduced exactly to 6b: the Fourier coefficients
`a_{P_m}(n)` of the Poincaré series (Kloosterman sums and `J_{k−1}`), which is where the created
positivity of the card (Kuznetsov, 6e–6f) will have to be produced.

## Lean plan for brick 6b (Fourier coefficients of `P_m`), chosen route: Lipschitz, not contours

Two routes were weighed for `a_{P_m}(n)`. The contour route (coefficient integral, unfolding
`Σ_l ∫_0^1 = ∫_ℝ`, then `∫_{Im w = Y} w^{-s} e(-αw) dw` by residues) needs a Cauchy formula with
derivatives for functions decaying in the lower half-plane; the corpus's
`integral_div_sub_eq_of_upperHalfPlane_farDecay` needs `1/|z|` decay on the closed half-plane,
which `e(αz)` lacks, and the `s = 1` base case is only conditionally convergent. The series route
needs no integrals: split `gammaSet 1 1 0` into `(0, ±1)` and `±(c, d₀ + c l)` (`c ≥ 1`,
`d₀ ∈ (ZMod c)ˣ`, `l ∈ ℤ`), expand `e(m M_{c,d₀}(z+l)) = e(m a/c) Σ_j (−2πi m/c)^j/j! (c(z+l)+d₀)^{−j}`,
apply mathlib's Lipschitz identity `EisensteinSeries.qExpansion_identity`
(`Σ_l (w+l)^{−s} = ((−2πi)^s/(s−1)!) Σ_{n≥1} n^{s−1} e(nw)`) to `w = z + d₀/c`, and read off the
coefficient of `e(nz)` through `qExpansion_coeff_unique`.  Everything is absolutely convergent for
`Im z > 0` (`|c(z+l)+d₀| ≥ c y`).  Modules: (1) coset decomposition of the Poincaré series,
(2) exponential expansion and exchange, (3) Lipschitz application and Kloosterman phase
`e((m ā + n d₀)/c)` (corpus `kloostermanSum`), (4) the `HasSum` Fourier expansion and the
coefficient identity `a_{P_m}(n) = 2[δ_{mn} + 2π(−i)^k (n/m)^{(k−1)/2} Σ_c S(m,n;c)/c · J_{k−1}(4π√(mn)/c)]`
with `J_{k−1}` defined by its power series, (5) the explicit Petersson formula from 6d.

## Lean (2026-09-02, brick 6b-1: rows `(c, d)` with `c > 0` reindexed by `(c, d mod c, ⌊d/c⌋)`)

| Module | Headline theorems |
|---|---|
| `HTGeometry/GammaSetPositiveRowEquiv.lean` | `shiftedRow c u l = (c, u.val + l c)` (coprime), `isUnit_row_snd`, `rowFiberEquiv c : {v | v₀ = c} ≃ (ZMod c)ˣ × ℤ`, `positiveRowEquiv : (Σ c : ℕ+, (ZMod c)ˣ × ℤ) ≃ {v | 0 < v₀}` (via `Equiv.ofBijective`), `unitRowMatrix c u`, `poincareSummand_shiftedRow` (`= (c(z+l)+u.val)^{−k} e(m M_{c,u}(z+l))`), `poincareSummand_gammaSetNeg` (`= (−1)^k ·`) |

## Lean (2026-09-02, brick 6b-1 closed: coset decomposition of `P_m`)

| Module | Headline theorems |
|---|---|
| `HTGeometry/PoincareSeriesCosetDecomposition.lean` | `zeroRowPos/Neg` with `poincareSummand_zeroRowPos = e(mz)`, `cosetTerm k m c u l z = (c(z+l)+u.val)^{−k} e(m M_{c,u}(z+l))`, `summable_cosetTermSigma/prod/cosetTerm`, `negRowEquiv`, `poincareSeries_eq_cosetSum`: `P_m(z) = (1+(−1)^k) e(mz) + (1+(−1)^k) Σ_{c≥1} Σ_{u∈(ℤ/c)ˣ} Σ_{l∈ℤ} cosetTerm` (absolutely convergent, `k ≥ 3`) |

## Lean (2026-09-02, brick 6b-2 closed: exponential expansion of the coset sums)

| Module | Headline theorems |
|---|---|
| `HTGeometry/PoincareSeriesExponentialExpansion.lean` | `unitVal`, `unitTop` (top-left entry `a` of `M_{c,u}`), `unitRowMatrix_det` (`a d₀ − b c = 1`), `coe_unitRowMatrix_smul` (`M_{c,u} w = a/c − 1/(c(cw+d₀))`), `expSeed_unitRowMatrix_smul`, `hasSum_exp_div`, `linearShift c u z l = c(z+l)+d₀` with `le_norm_linearShift` (`≥ c·Im z`), `summable_uncurry_expansion` (absolute convergence of the `(l, j)` family), `cosetTerm_eq_tsum`, `tsum_cosetTerm_eq` (`Σ_l cosetTerm = e(ma/c) Σ_j (−2πim/c)^j/j! Σ_l U_l^{−(k+j)}`), `shiftedPoint = z + d₀/c`, `tsum_linearShift_zpow` (Lipschitz: `Σ_l U_l^{−s} = c^{−s}(−2πi)^s/(s−1)! Σ_n n^{s−1} e(n w)` from mathlib's `EisensteinSeries.qExpansion_identity`) |

Next: 6b-3 Kloosterman identification `Σ_u e(m a_u/c) e(n d₀/c) = S(m,n;c)` (corpus `kloostermanSum`),
then the absolutely convergent rearrangement to `HasSum (n ↦ A(n) q^n) (P_m z)` and
`qExpansion_coeff_unique`.

## Lean (2026-09-02, brick 6b-3a closed: the Kloosterman phases)

| Module | Headline theorems |
|---|---|
| `HTGeometry/PoincareSeriesKloostermanPhase.lean` | `unitTop_cast_eq_inv` (`a ≡ u⁻¹ mod c`), `exp_phase_eq_kloostermanPhase` (`e(ma/c)e(nd₀/c) = kloostermanPhase c m n u⁻¹`), `sum_exp_phase_eq_kloostermanSum` (`Σ_u … = kloostermanSum c m n`, the corpus's `S(m,n;c)`) |

Remaining for 6b: (3b) the absolutely convergent rearrangement of
`Σ_c Σ_u Σ_j B(c,j) e(ma_u/c) Σ_n n^{k+j−1} e(nd₀/c) q^n` into `Σ_n A(n) q^n` (majorant
`n^{s−1} e^{−2πyn} ≤ (s−1)! (πy)^{1−s} e^{−πyn}`) and `qExpansion_coeff_unique`; (4) the Bessel
series identity for `Σ_j B(c,j) n^{k+j−1}`.

## Lean (2026-09-02, brick 6b-3b part 1: the coefficient majorant)

| Module | Headline theorems |
|---|---|
| `HTGeometry/PoincareSeriesCoefficientMajorant.lean` | `CoefIndex := Σ c : ℕ+, (ZMod c)ˣ × ℕ`, `coefMajorant k' m y (c,u,j) n = (2π)^{k'+1}(πy)^{−k'} c^{−(k'+1)} (4πm/y)^j/j! e^{−πyn}`, `pow_mul_exp_le` (`n^s e^{−2πyn} ≤ s!(πy)^{−s}e^{−πyn}`), `term_le_coefMajorant` (the expansion term is dominated), `summable_pnat_pow_inv`, `summable_coefMajorant_sigma` (`φ(c) ≤ c`, `Σ c^{1−k} < ∞`), `summable_coefMajorant` (`k' ≥ 2`) |

## Lean (2026-09-02, brick 6b-3b closed: the Fourier coefficients of `P_m` through Kloosterman sums)

| Module | Headline theorems |
|---|---|
| `HTGeometry/PoincareSeriesFourierExpansion.lean` | `expansionCoeff k' m c j = (−2πim/c)^j/j!·c^{−(k'+1+j)}·(−2πi)^{k'+1+j}/(k'+j)!`, `expansionTerm`, `tsum_cosetTerm_eq_tsum_expansionTerm` (coset sum = double series, via the Lipschitz sums), `norm_expansionTerm_le` (dominated by `coefMajorant`), `summable_expansionTerm` (absolute convergence of the four-fold family), `poincareCoeff k' m n = (1+(−1)^k)[δ_{nm} + Σ_c Σ_j B(c,j) n^{k'+j} S(m,n;c)]`, `tsum_expansionTerm_fixed` (units collapse to `kloostermanSum`), `hasSum_poincareCoeff` (`P_m(z) = Σ_n poincareCoeff n · e(z)^n`), `cuspCoeff_poincareSeriesCF_eq_poincareCoeff` (via mathlib's `qExpansion_coeff_unique`) |

Remaining for 6b: the Bessel-series identity
`Σ_j B(c,j) n^{k'+j} = 2π(−i)^{k'+1}(n/m)^{k'/2} c^{−1} J_{k'}(4π√(mn)/c)` (pure series algebra with `J_ν`
defined by its power series), then the explicit Petersson formula by combining with 6d.

## Lean (2026-09-02, brick 6b closed — the Petersson formula for `SL(2,ℤ)` is in Lean)

| Module | Headline theorems |
|---|---|
| `HTGeometry/PoincareSeriesBesselCoefficient.lean` | `besselJ ν x := Σ_j (−1)^j (x/2)^{2j+ν}/(j!(j+ν)!)` (summable), `besselJ_eq_mul_tsum`, `expansionCoeff_mul_pow_eq` (termwise, via `(−2πi)^2 = −(2π)^2`), `tsum_expansionCoeff_mul_pow_eq_besselJ` (`Σ_j B(c,j)n^{k'+j} = 2π(−i)^{k'+1}√(n/m)^{k'} c^{−1} J_{k'}(4π√(mn)/c)`), `poincareCoeff_eq_bessel`, `cuspCoeff_poincareSeriesCF_eq_bessel`, and **`petersson_formula_levelOne`**: for every orthonormal basis `b` of the Petersson space of weight `k = k'+1 ≥ 3` and `m, n ≥ 1`, `2(4πm)^{1−k}Γ(k−1) Σ_i conj(a_{b_i}(m)) a_{b_i}(n) = (1+(−1)^k)[δ_{nm} + 2π(−i)^k √(n/m)^{k−1} Σ_{c≥1} S(m,n;c)/c · J_{k−1}(4π√(mn)/c)]` |

All of brick 6's holomorphic half (6a, 6b, 6c, 6d) is closed in Lean, unconditionally, axioms
`propext/Classical.choice/Quot.sound`, every module wired into `GaloisForLFunctions.HTGeometry`.
(The factor `2` and `(1+(−1)^k)` reflect `P_m` being summed over all coprime rows `±(c,d)`.)

**Status of the card's producer.** The created positivity the card needs is spectral: the
Kuznetsov formula's continuous spectrum carries `|ζ(1+2it)|^{−2}`, which is where the zeros of ζ
enter a share ledger; the holomorphic Petersson formula has no continuous spectrum and therefore no
zeta term. Bricks 6e–6f (Maass cusp forms, weight-0 Eisenstein series and their continuation, the
spectral decomposition of `L²(SL(2,ℤ)\ℍ)`, Kuznetsov) have no foundation in mathlib or the corpus
beyond the real-analytic Eisenstein/Poincaré families of the `ThetaCuspHawkingBM*` modules. That
spectral theory is the exact frontier of this card; it is not a dead end mathematically, but it is
the largest single missing block, and nothing short of it produces the positivity the card asks for.

## Paper verdict on the producer (2026-09-02): the automorphic route is a dead end for RH

The question to settle before any further Lean is whether an `SL(2,ℤ)` spectral identity can
produce a ζ-zero ledger that escapes Ceilings C1–C4. Three identities exist: Petersson (holomorphic),
Kuznetsov (weight 0), Selberg's trace formula. The first two contain no ζ-zero information; the third
does, and its ledger is Class II. Proofs follow.

### P1. Petersson and Kuznetsov are zero-blind

The Petersson formula (now `petersson_formula_levelOne`) contains no ζ at all. The Kuznetsov formula
for `SL(2,ℤ)` (Iwaniec, *Spectral Methods*, Thm 9.3) reads, for `m, n ≥ 1` and admissible `h`,

```text
Σ_j h(t_j) ρ_j(m) conj ρ_j(n) / cosh(πt_j)
  + (1/π) ∫ h(r) σ_{2ir}(m) conj σ_{2ir}(n) (mn)^{-ir} / |ζ(1+2ir)|² dr
  = δ_{mn} (1/π²) ∫ r tanh(πr) h(r) dr + Σ_{c≥1} S(m,n;c)/c · ĥ_Bessel(4π√(mn)/c).
```

ζ enters only through `|ζ(1+2ir)|^{-2}` on the line `Re s = 1`, where ζ has no zeros; the value of
`ζ(1+2ir)` is determined by the Euler product side and carries no information about a zero
`β + iγ` with `β < 1` beyond what the classical zero-free region already gives (the continuous term
is a bounded positive density). No functional of the zeros appears, so no ledger `Σ_ρ φ(ρ)` can be
read off. The Deshouillers–Iwaniec large sieve, Stadlmann's Lemmas 3/4/7 and the MT Lemma 3.5 shapes
are bounds for Kloosterman forms and are RH-blind by construction. **Kuznetsov is not a ζ-zero
producer.** [PROVED HERE, by inspection of the identity]

### P2. The Selberg trace formula produces a Class II ledger

For `Γ = SL(2,ℤ)` the scattering matrix is `φ(s) = ξ(2s−1)/ξ(2s)` with `ξ(s) = π^{-s/2}Γ(s/2)ζ(s)`
(the identity `√π Γ(s−½)ζ(2s−1)/(Γ(s)ζ(2s))` rewritten). By Hadamard, `ξ'/ξ(s) = Σ_ρ 1/(s−ρ)`
(zeros paired symmetrically), hence

```text
−(1/4π) φ'/φ(½ + ir) = (1/2π) Σ_ρ [ 1/(1+2ir−ρ) − 1/(2ir−ρ) ]
                     = (1/2π) Σ_{ρ=β+iγ} [ (1−β)/((1−β)² + (2r−γ)²) + β/(β² + (2r−γ)²) ] =: Σ_ρ K_ρ(r),
```

the imaginary parts cancelling because `|φ(½+ir)| = 1` makes the left side real. Each `K_ρ ≥ 0`
is a pair of Poisson kernels in the variable `2r` centred at `γ`, of half-widths `β` and `1−β`,
total mass `∫ K_ρ dr = ½` independent of `β`, and peak `K_ρ(γ/2) = (1/2π)(1/β + 1/(1−β))`.
The trace formula (Iwaniec Thm 10.2, one cusp, area `π/3`) is

```text
Σ_j h(t_j) + Σ_ρ w_h(ρ) = G(h),   w_h(ρ) := ∫ h(r) K_ρ(r) dr,
```

with `G(h)` the identity, hyperbolic (prime-geodesic), elliptic and parabolic terms, all explicit
and RH-independent. The only created positivity in it is `Σ_j h(t_j) ≥ 0` for `h ≥ 0` on `ℝ`
(no exceptional eigenvalues for `SL(2,ℤ)`), and its only consequence for the zeros is the ledger
inequality `Σ_ρ w_h(ρ) ≤ G(h)`. Every other ingredient (Weyl's law with remainder, individual
eigenvalues) carries error terms of size `≫ r₀/log r₀` per unit of `‖h‖₁`, far above the `O(1)`
weight of a single zero, so it cannot isolate one zero.

**Theorem (Selberg-ledger ceiling).** Let `h ≥ 0` be admissible, `ρ₀ = β₀ + iγ₀` a zero with
`½ ≤ β₀ < 1`, and `Z` any set of zeros `ρ ≠ ρ₀` with `|γ − γ₀| ≤ 2`. Suppose `h` is supported in
`|r − γ₀/2| ≤ ¼`. Then

```text
w_h(ρ₀) ≤ (‖h‖₁/2π)(1/(1−β₀) + 1/β₀),        w_h(ρ) ≥ (2/29π) ‖h‖₁  for every ρ ∈ Z.
```

Consequently the ledger inequality `w_h(ρ₀) ≤ G(h) − Σ_{ρ∈Z} w_h(ρ)` can contradict the existence
of `ρ₀` only if `1/(1−β₀) + 1/β₀ > (4/29)|Z|`, i.e. only if `1 − β₀ < 29/(4|Z| − 58)`.

*Proof.* Upper bound: `K_{ρ₀}(r) ≤ K_{ρ₀}(γ₀/2)` pointwise since each Poisson kernel is maximal at
its centre; integrate against `h ≥ 0`. Lower bound: for `0 ≤ β ≤ 1`, `β² + (2r−γ)² ≤ 1 + (2r−γ)²`
and likewise for `1−β`, so `K_ρ(r) ≥ (1/2π)·(β + (1−β))/(1 + (2r−γ)²) = (1/2π)/(1+(2r−γ)²)`; on
the support of `h`, `|2r − γ| ≤ |2r − γ₀| + |γ₀ − γ| ≤ ½ + 2`, so `1 + (2r−γ)² ≤ 29/4`; integrate.
The consequence is the comparison `w_h(ρ₀) > Σ_Z w_h(ρ)` forced by `G(h) − Σ_Z w_h(ρ) ≥ Σ_{ρ∉Z} w_h(ρ) ≥ w_h(ρ₀)`
whenever `ρ₀` exists (all weights are nonnegative). ∎

Riemann–von Mangoldt with the classical `|S(T)| ≤ C log T` gives, unconditionally, at least
`(1/π) log γ₀ − C' log γ₀`-type counts `|Z| ≥ c log γ₀` in `[γ₀−2, γ₀+2]` for `γ₀` large (any `Z`
consisting of the zeros there, on-line or not: the lower bound `K_ρ ≥ (1/2π)/(1+(2r−γ)²)` did not
use `β`). Hence **no positivity inequality drawn from Selberg's trace formula can exclude a zero
with `1 − β₀ ≥ c/log γ₀`**: the ledger is Class II with the de la Vallée Poussin width, exactly
Ceiling C2. The freedom in `h` cannot help: narrowing `h` below width `¼` only lowers `w_h(ρ₀)`
relative to `‖h‖₁` (the kernel width is `≥ min(β₀,1−β₀)`), widening it raises `Σ_Z` faster than
`w_h(ρ₀)`; sign changes in `h` destroy `Σ_j h(t_j) ≥ 0`, the one created positivity. Wider windows
`|γ−γ₀| ≤ H` give the same conclusion with `29/4` replaced by `1 + (H+½)²` and `|Z| ≍ H log γ₀`,
which is never better. [PROVED HERE]

### P3. Why the zeros cannot be moved into a positive spectral side

The zeros of ζ enter `SL(2,ℤ)`-spectral theory only as poles of `φ(s) = ξ(2s−1)/ξ(2s)`, i.e. as
the points `s = ρ/2` where the Eisenstein series `E(z, s)` is a Laplace eigenfunction of eigenvalue
`(ρ/2)(1−ρ/2)` that is not in `L²(Γ\ℍ)`. A created positivity is a Parseval identity in an
`L²`-space; the functions `E(·, ρ/2)` are excluded from every such space by their growth, which is
why they contribute through `φ'/φ` (a boundary density) rather than as discrete eigenvalues.
Zagier's Rankin–Selberg space, in which `E(·, ρ/2)` are eigenfunctions of an operator, carries no
positive-definite invariant form; this is the standard obstruction and it is structural, not a
missing estimate. The successor conjecture `ULF-SLC-Q` therefore cannot be realised by any
`GL(2)` trace-formula or Rankin–Selberg identity: falsifier **F4 is established for that family**.

### P4. The corpus does not need Kuznetsov on any RH-bearing path

- `matomaki-teravainen-e3-lean-programme.md` (2026-08-18): §6.1/Huxley "removes Kuznetsov from the
  dependency graph"; the Route E consequence depends only on `θ = ½`.
- `route-e-cofactor-amplified-e3-token-supply.md`: Stage 2 with "no spectral estimate assumed";
  the Kuznetsov–Deshouillers–Iwaniec modulus average is a *later improvement* of a signed carrier,
  not an input to the proved statement; E's own boundary paragraph says signed column balance is a
  receiver (restates RH).
- `critical-multiplicative-compensated-cancellation-rh.md` `[FALSIFIED METHODS]`: generic
  Kuznetsov/Deshouillers–Iwaniec closure misses a polynomial power and isolates as main terms the
  ridge/zero-mode packets whose signed joining is the endpoint.
- `lindelof-hypothesis-campaign.md` Theorem 68: the spectral transform needs a rational parameter;
  the critical object's parameter `t` is real.

So building Maass spectral theory would deliver unconditional theorems (Kuznetsov, DI large sieve)
that no live RH chain of the corpus consumes on its critical path.

### Verdict

`[DEAD END FOR RH]` The automorphic created-positivity producer is capped: Petersson and Kuznetsov
are zero-blind (P1); the Selberg ledger is Class II with the de la Vallée Poussin width (P2, a
theorem); the obstruction is structural (P3); and no corpus chain needs the spectral average on its
critical path (P4). The ceilings C1–C4 stand as unconditional theorems, and the Petersson formula
built for this card is an unconditional theorem in Lean. No Maass/Kuznetsov Lean is to be built for
this card.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** the Selberg-ledger ceiling (P2): the only created positivity
  of an `SL(2,ℤ)` spectral identity is `Σ_j h(t_j) ≥ 0`, its ζ-zero side is the Poisson-smoothed
  density `Σ_ρ K_ρ`, peak `(1/2π)(1/β+1/(1−β))`, floor `(1/2π)/(1+(2r−γ)²)`, so exclusion width
  `≤ c/log γ` (Class II, Ceiling C2); Petersson and Kuznetsov contain ζ only on `Re s = 1` (P1).
- **Strongest positive survivor:** the ceilings C1–C4 (Lean: `GCECriticalCoefficientHeightBound`,
  `CosinePolynomialPurchaseCap`, `NoSurrogateAnnihilator`, `LandauPageTwoQuadratic`) and the
  level-one Petersson formula `petersson_formula_levelOne` with its eleven supporting modules
  (see `3-formalized/petersson-formula-level-one-lean.md`).
- **New insight:** created positivity and ζ-zero information live in disjoint parts of `GL(2)`
  spectral theory: positivity is `L²`-discrete (Maass/Petersson), the zeros are the poles of the
  scattering matrix, i.e. boundary densities; any identity linking them is a Class II ledger.
  A ζ-zero producer must put the zeros *inside* a positive-definite Parseval identity, which no
  automorphic identity does.
- **Status:** falsified as an RH producer 2026-09-02; card retired to `5-failed`; proven bricks
  extracted to `3-formalized`.
- 2026-09-02 — the killing mechanism is Lean-certified: `RHTower/SelbergLedgerCeiling.lean`
  (`zeroKernel`, `zeroKernel_le_peak`, `zeroKernel_ge`, `ledgerWeight_le_peak_mul`,
  `ledgerWeight_ge_of_support`, `selberg_ledger_exclusion`, `selberg_ledger_width`; wired into the
  RHTower umbrella, axioms `propext/Classical.choice/Quot.sound`). Card retired to `5-failed`.
