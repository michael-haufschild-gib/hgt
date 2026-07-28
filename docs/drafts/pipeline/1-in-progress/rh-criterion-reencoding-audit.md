# RH criterion audit: how many `riemannHypothesis_iff_*` are re-encodings of `conj ρ = 1 − ρ`

**Status:** the fifteen flagged files are resolved — fourteen re-encodings, one genuine.

## 1. The question

`RHTower` contains 491 declarations matching `riemannHypothesis_iff` / `_iff_riemannHypothesis` and
384 `riemannHypothesis_of_*`.  A count that large only means something if the criteria are
*different*.  This card classifies them.

## 2. The template

Almost all of the flagged criteria instantiate one template:

> Define a quantity `Q(x, ρ)` that is manifestly invariant under the centred reflection
> `ρ ↦ 1 − conj ρ`.  Observe that `Q` is fixed / vanishes / has unit norm exactly when
> `conj ρ = 1 − ρ`.  Take real parts: `Re ρ = 1/2`.  Quantify over `XiDivisorSupport`.

The last step turns it into "every Xi zero has `Re = 1/2`", which is RH **verbatim**.  No analysis, no
`ζ`, no Xi-zero hypothesis is used anywhere in the chain.

## 3. Mechanical detector

A criterion is a re-encoding when its file contains a lemma

```text
P ρ ↔ ρ.re = 1 / 2
```

whose **statement mentions no Xi zero** (the docstrings often say so outright: "No Xi-zero hypothesis
is used"), *and* the file's `_iff_riemannHypothesis` proof routes through that lemma.  Both checks are
needed — the second is what separates re-encodings from criteria that merely have such a lemma as an
auxiliary.

Scan of `RHTower`: **111 zero-free `re = 1/2` cores in 67 files; 15 files pair one with an RH
equivalence.**

## 4. Verified re-encodings

| family | core | why it is trivial |
|---|---|---|
| prime seam (22 files, 96 producers) | `orbitwiseScaleSeamCharge x ρ = log x·(x^{−conj ρ} − x^{−(1−ρ)})` | vanishes in `x` iff the exponents agree; `p` enters only as a value of `x`, never as a prime |
| Hurwitz `monoScalar` (17 files) | `continuedHurwitzPairDifferentiallyDependent_iff_monoScalar_eq` | "differentially dependent" unfolds to "parameters differ by an integer"; in the open strip, to "parameters equal" |
| Born temperature | `fe_reflection_fixed_iff : 1 − conj s = s ↔ s.re = 1/2` | this *is* the definition of the critical line, proved by `linarith` |
| Gamma–Mertens coboundary | `mertensPolePair_re_eq_half_of_finiteShiftTwoCoboundary` | reduces to `−ρ ≡ conj ρ − 1 (mod 2ℤ)`, then to the same identity |
| prime-power centred mark | `centeredPrimeMark_norm_eq_one_iff` | `‖p^{1/2−s}‖ = 1 ⟺ (1/2 − Re s)·log p = 0` |
| rational Hurwitz fibre seam | `rationalHurwitzFiberResponse_reflection_fixed_iff` | `n^{−conj ρ} = n^{−(1−ρ)} ⟺ conj ρ = 1 − ρ` |

Each derived criterion — coherence, bounded pair energy, pair asymptotics, Calkin–Gram compactness,
summable Calkin aggregate, two–three seam rigidity, damping aperture, reflected phase match, factor
label match — is the same statement in a different costume.  **To prove any of them you must already
know RH.**

## 5. Cleared as genuine

`PrimeArchBernsteinConfinedPhase` has a zero-free core (`..._eq_one_of_onLine`) but it is one
directional and auxiliary.  Its RH equivalence runs

```text
PrimeArchEndpointBernsteinPurityBounded  →  subexponentialSquareEnergy  →  ℓ¹
   →  BernsteinTotalVariation_subexponential  →  RiemannHypothesis
```

over `normalizedPrimeArchMoment`, i.e. over `a_n = 2∑_ρ γ_ρ^{−2(n+1)}`.  That is a **Hausdorff moment
problem** on the secondary-zeta sequence — a genuinely different object, not an algebraic symmetry.
It is RH-equivalent and therefore RH-hard, but it is real mathematics and belongs in the live column.

## 5b. Full extent of the seam template

The 22 files carrying `orbitwiseScaleSeamCharge` / `orbitwiseNatPrimeSeamCharge`:

```text
XiRationalHurwitzDyadicRefinement   XiPrimeSeamPairVariance
XiPrimeSeamCofinalAnchoredEssentialNormDecay   SemilocalCompressedEulerOrientation
PrimeSeamDampingAperture            XiPrimeSeamReflectionEnergy
XiPrimeSeamCalkinUniversalityLaw    AnchoredCalkinCriticalLineUniversalityLaw
HeatAperturePrimeSeamReflection     XiHurwitzRationalFiberSeam
XiPrimeSeamEulerZeroTangent         XiPrimeSeamPairEnergy
XiPrimeSeamCoherenceCollapse        XiPrimeSeamCofinalAnchoredCommutator
XiPrimeSeamEulerOrientationReflection   XiPrimeSeamAnchoredCommutatorNormComparison
XiPrimeSeamSummableCalkinAggregate  XiPrimeTwoThreeSeamRigidity
XiPrimeSeamCalkinGram               XiMobiusSchurRationalHurwitzLorentzAperture
XiPrimeTwoEulerHurwitzMonodromyCalibration   XiPrimeSeamPairAsymptotics
```

`XiRationalHurwitzDyadicRefinement`'s own core, `normalizedScaleSeamEnergy_eq_iff_re_eq_half`, closes
the last of the fifteen: it is the same template with a dyadic-scale dressing.

## 6. Why this matters

The number of RH criteria in the tree carries almost no information about how much of RH is
surrounded.  At least 96 producers are one algebraic identity.  Any planning that treats the producer
count as coverage is mis-calibrated.  The template is easy to fall into: a construction that is
symmetric under `s ↦ 1 − conj s` will always be fixed exactly on the line, and dressing it in prime,
Gamma, Hurwitz or thermal language does not change that.

## Gates

- [x] detector defined and run: 111 zero-free `re = 1/2` cores, 67 files, 15 paired with an RH iff
- [x] six families verified by reading their cores, not their signatures
- [x] `PrimeArchBernsteinConfinedPhase` checked and cleared as genuine
- [x] all fifteen paired files resolved: fourteen re-encodings, one genuine
- [ ] the same pass over the Gamma/Meixner and thermal families

## 7. Correction, and where the only unconditional zero-side surface actually is

### 7.1 Retracting my Bernstein claim

I suggested the Bernstein/Hausdorff form of the moment criterion might escape the Cauchy–Binet
blindness of the Hankel form.  **It is strictly blinder.**  With `t_ρ = γ₁²/γ_ρ²` and
`ν = ∑_ρ 2w_ρ δ_{t_ρ}`, the Bernstein coefficients are

```text
(−1)^k Δ^k b_n = ∫₀¹ t^n (1−t)^k dν(t) = ∑_ρ 2w_ρ t_ρ^n (1−t_ρ)^k .
```

`t^n` suppresses small `t` (high zeros), `(1−t)^k` suppresses large `t` (low zeros): the pair is a
**band-pass in height**, centred at `t ≈ n/(n+k)`, i.e. at `γ ≈ γ₁√((n+k)/n)`.  At `n = 0` the
coefficient is `≈ log k /(2πγ₁√k)`, dominated by zeros at height `γ₁√k`.  So reaching height `T`
needs `k ≈ (T/γ₁)²`, against `N ≈ N(T) ≈ (T/2π)log(T/2πe)` for the Hankel form.  At `T = 3·10¹²`
that is `k ≈ 5·10²²` versus `N ≈ 10¹³` — worse by nine orders.  Moreover a single off-line pair at
height `|γ|` contributes amplitude `~1/|γ|²` against an on-line bulk of `~log|γ|/|γ|`, so it can
never turn a coefficient negative.  **The Bernstein form is not a way through.**

### 7.2 What is actually there

The corpus contains a **Carlson density programme**, and it is the only unconditional zero-side
machinery in the tree:

```text
SecondMoment.lean            Montgomery–Vaughan mean value
FourthMoment.lean            fourth moment of a Dirichlet polynomial
FourthMomentDiagonal.lean    Carlson's bounded fourth moment for σ > 1/2
DivisorBound.lean            the d(n) bound making it converge for σ > 1/2
LargeValues.lean             abstract large-values counting
LargeValuesDpoly.lean        R·V² ≤ (δ⁻¹+η⁻¹)∫‖D‖² + η∫‖dpoly(a·log)‖²
LittlewoodXi.lean            Littlewood's lemma for ξ
DetectionSecondMoment.lean   names `CarlsonDensity` as its consumer
```

**`CarlsonDensity` does not exist.**  Every ingredient of the classical `N(σ,T) = o(T)` for `σ > 1/2`
is formalized and the capstone is missing.  This is the only place in `RHTower` where an
unconditional theorem *about the zeros of ζ* is within reach; everything else audited above is a face
or a re-encoding.

### 7.3 The recorded no-go, and what the literature did to it

`ZeroDensityMomentCrossing.lean` (40 lines) records, exactly:

```text
powerBranch σ k     = (k+1)(2−2σ)          raising to the (k+1)-st power
meanValueBranch σ k τ = τ + k(1−2σ)        the k-th mean value
densityTarget σ τ   = (2−2σ)τ              the Density Hypothesis

crossing at τ = k + 2 − 2σ, and there
    powerBranch − densityTarget = (2−2σ)(2σ−1) > 0  for 1/2 < σ < 1,  independent of k .
```

So the integer-moment method misses the Density Hypothesis by a `k`-independent constant, and no
choice of moment order closes it.  That is correct and complete **for the moment method**.

The 2024 literature goes around it rather than through it: Guth–Maynard, *New large value estimates
for Dirichlet polynomials*, improve the large-value input itself and obtain the first gain at
`σ = 3/4` since Ingham 1940 / Huxley 1972 — `N(σ,T) ≪ T^{30(1−σ)/13+o(1)}`, i.e. `T^{15/26}` in place
of `T^{3/5}` at `σ = 3/4`.  They do **not** reach the Density Hypothesis.  Their input is exactly of
the type `LargeValuesDpoly` is the entry point for.

**Consequence for targeting.**  New mathematics in this tree is possible in exactly one place: a
large-value estimate for Dirichlet polynomials that is not of the form `min(power, meanValue)`.
Completing `CarlsonDensity` is classical and therefore not novel as mathematics, but it is the only
platform on which such an estimate could ever be stated here, and it would be the tree's only
unconditional theorem about ζ's zeros.

## Gates

- [x] Bernstein/Hausdorff form measured: band-pass at `γ ≈ γ₁√((n+k)/n)`; strictly blinder than Hankel
- [x] my "not obviously blind" claim retracted with the computation that refutes it
- [x] Carlson density programme located; `CarlsonDensity` capstone confirmed absent
- [x] `ZeroDensityMomentCrossing` no-go read in full and matched against the 2024 large-value literature
- [ ] `CarlsonDensity`: classical, not novel, but the only unconditional zero-side platform in the tree
- [ ] a large-value estimate outside the `min(power, meanValue)` family — the one place new mathematics fits

## 8. The exact missing lemma

The tree has **both** halves of Carlson's density argument, and they are not joined.

*Analytic half* (ζ is present): `SmoothAFEZetaExact`, `SmoothAFEZetaMellin`, `SmoothAFEGaussianKernel`,
`SmoothAFEGaussianNonzero`, plus `BourgainDyadicDissection` and `VanDerCorputSecond`.

*Dirichlet-polynomial half* (ζ is absent): `SecondMoment`, `FourthMoment`, `FourthMomentDiagonal`,
`Mollifier`, `MollifierDetection`, `DetectionSecondMoment`, `LargeValues`, `LargeValuesDpoly`.

`rg riemannZeta` returns **nothing** in `SecondMoment.lean`, `MollifierDetection.lean` or
`DetectionSecondMoment.lean`.  The two halves never meet.

**The missing lemma (zero detection).**

```text
For σ > 1/2 there are V > 0 and a cutoff schedule N(T), y(T) → ∞ such that for every
zero ρ = β + iγ of ζ with β ≥ σ and |γ| ≤ T,

        ‖ detectionPoly N(T) y(T) ρ ‖  ≥  V .
```

Proof shape: `M_y ζ = 1 + (tail)` by `MollifierDetection.detection_poly_eq`; at a zero the left side
vanishes, so the tail is `≈ −1`; the smooth AFE supplies `ζ(ρ) = ∑_{n ≤ N} n^{−ρ} + (small)` uniformly
for `|γ| ≤ T`, which is what turns "the tail is `−1`" into a statement about the *polynomial*.  Both
inputs exist; only the join is missing.

With that lemma, `large_values_dpoly` counts the detecting grid points, `secondMoment_upper_bound`
and `fourthMoment_bounded` bound the two integrals, `sublinear_of_tail_and_offdiag` assembles, and
`LittlewoodXi` converts the count.  The capstone `N(σ,T) = o(T)` follows.

**Honest label.**  This is Carlson 1920.  It is *not* new mathematics and must not be presented as
such.  It is, however, (i) the tree's only unconditional theorem about the zeros of `ζ`, and (ii) the
only platform on which a new large-value estimate — the one place new mathematics fits, per §7.3 —
could ever be stated here.

## Gates

- [x] both halves of the argument located; confirmed they share no declaration
- [x] the missing join stated as a single lemma with its proof shape
- [ ] prove the zero-detection lemma (classical; joins smooth AFE to mollifier detection)
- [ ] `CarlsonDensity`: `N(σ,T) = o(T)` for `σ > 1/2`

## 9. The join, built — and the exact limit of what it reaches

`GaloisForLFunctions/RHTower/ZeroDetectionEM.lean`, axiom-clean, registered, `lake build
GaloisForLFunctions.RHTower` green.

```text
dpolyC_mul                          complex-variable convolution identity (the on-line `dpoly_mul`
                                    existed; the complex one did not)
detPolyC_eq                         detPolyC N y s = D_N(s)·M_y(s) − 1
detPolyC_add_one_eq_of_zeta_eq_zero at a zero: detPolyC + 1 = M_y(ρ)·(−N^{1−ρ}/(ρ−1) + ρ·emTail N ρ)
norm_mollifierC_le, norm_emPole     explicit factor bounds
half_le_norm_detPolyC_of_explicit   the criterion with every quantity elementary
```

This is the first declaration in the tree taking `riemannZeta ρ = 0` as a hypothesis and returning an
unconditional quantitative statement about a computable object.

### 9.1 Correction: the parameter range is nonempty for every `σ > 1/2`

An earlier version of this section claimed the admissible range is empty as `σ → 1/2⁺`.  **That was
an algebra error.**  The two requirements are

```text
(pole)  S · N^{1−σ} ≤ T/4 ,        (tail)  S · 2T · N^{−σ}/σ ≤ 1/4 ,
```

where `S` bounds the mollifier sum.  Taking `N = (8ST/σ)^{1/σ}` makes (tail) an exact equality and
(pole) becomes

```text
4 S (8S/σ)^{(1−σ)/σ}  ≤  T^{(2σ−1)/σ} .
```

The exponent `(2σ−1)/σ` is **positive precisely for `σ > 1/2`**, so the condition holds for all large
`T`.  Writing `S ≈ T^α` the compatibility condition is exactly `α ≤ 2σ − 1`, i.e. mollifier length
`y = T^θ` with `θ ≤ (2σ−1)/(1−σ)`: nonempty for every `σ > 1/2`, shrinking to zero as `σ → 1/2⁺` but
never empty.  My earlier "→ θ + 1 > 1" evaluated the limit at `σ = 1/2` and mistook that for the
range on `σ > 1/2`.

Both halves are now formalized:

```text
detection_remainder_le_half   monotone transfer of every factor from `re ρ ≥ σ` down to `σ`
half_le_norm_detPolyC_of_box  detection at every zero with `re ρ ≥ σ`, `T ≤ ‖ρ−1‖`, `‖ρ‖ ≤ 2T`
exists_length_detection       the two σ-level requirements are simultaneously satisfiable
```

all axiom-clean.  So the Euler–Maclaurin route **does** reach every `σ > 1/2`; what remains is not a
range obstruction but the counting step.

### 9.2 What is genuinely left

* rounding the real length of `exists_length_detection` to a natural `N` (the admissible interval is
  long for large `T`, so this is routine);
* the well-spaced subset argument putting detected zeros on a `δ`-grid so `large_values_dpoly`
  applies — this is the step that needs an idea, not bookkeeping;
* assembly: `secondMoment_upper_bound` + `fourthMoment_bounded` + `sublinear_of_tail_and_offdiag`,
  then `LittlewoodXi` to convert the count.

**Honest label unchanged.**  This is Carlson 1920 formalized unconditionally.  Not new mathematics;
the only platform in this tree on which a new large-value estimate could be stated.

## Gates

- [x] the join built, axiom-clean, umbrella green
- [x] **correction**: the parameter range is nonempty for every `σ > 1/2` (`θ ≤ (2σ−1)/(1−σ)`)
- [x] monotone transfer, box detection, and length satisfiability all formalized
- [ ] rounding the real length to a natural `N`
- [ ] well-spaced subset argument for the grid
- [ ] assembly to `N(σ,T) = o(T)`

## 10. Well-spaced extraction, formalized

`GaloisForLFunctions/RHTower/WellSpacedSubset.lean`, axiom-clean, registered, built.

This is the step I flagged as needing an idea rather than bookkeeping.  The idea: bucket by
`⌊x/δ⌋`.  Each bucket holds at most `K` points, so at least `|S|/K` buckets are occupied; taking one
representative from every occupied bucket of a **fixed parity** makes the indices differ by at least
`2`, hence the points by at least `δ`; choosing the better parity costs a further factor `2`.

```text
bucket δ x = ⌊x/δ⌋
bucket_mem_Ico                            a point lies in its own bucket interval
delta_le_dist_of_two_le_abs_bucket_sub    index gap ≥ 2  ⟹  distance ≥ δ
two_le_abs_sub_of_even_sub                distinct integers of equal parity differ by ≥ 2
exists_wellSpaced_subset                  ∃ P ⊆ S, δ-separated, |S| ≤ 2K·|P|
```

The factor `2K` is exactly the logarithmic loss of classical density estimates, since `K = O(log T)`
by the local Riemann–von Mangoldt count (available in the tree through
`LittlewoodXi.xi_zeroCount_disc_le_logModulus` together with the order-`≤ 1` growth envelope).

### 10.1 A gap this exposes in the corpus's large-values lemma

`large_values_dpoly` and `large_values_count` are stated for a **uniform grid** `A + rδ`:

```text
(hV : ∀ r, r < R → V ≤ ‖dpoly a s (A + r * δ)‖)
```

A `δ`-separated set is not a uniform grid, so the extraction above does not yet plug in.  But the
underlying Sobolev/Gallagher argument only uses that the cells `[x_j, x_j + δ]` are **disjoint**,
which `δ`-separation gives.  So the corpus's lemma is stated more narrowly than its own proof needs.
Generalizing `large_values_count` from a uniform grid to an arbitrary `δ`-separated family is the
next concrete step, and it is bookkeeping rather than an idea.

## Gates

- [x] well-spaced extraction proved in general form, axiom-clean
- [x] the grid-versus-separated mismatch in `large_values_count` identified precisely
- [ ] generalize `large_values_count` to a `δ`-separated family
- [ ] local zero count `K = O(log T)` wired from `LittlewoodXi`
- [ ] assembly to `N(σ,T) = o(T)`

## 11. The large-values chain now works for separated families

The gap identified in §10.1 is closed.  `WellSpacedSubset.lean` (axiom-clean, built):

```text
pairwise_disjoint_cells   cells of a δ-separated family are pairwise disjoint
sum_integral_cells_le     ∑_{x∈P} ∫_{(x,x+δ]} g ≤ ∫_{(A,B+δ]} g   for g ≥ 0
gallagher_separated       ∑_{x∈P} ‖f x‖² ≤ δ⁻¹∫‖f‖² + ∫2‖f‖‖f'‖
large_values_separated    |P|·V² ≤ (δ⁻¹+η⁻¹)∫‖f‖² + η∫‖f'‖²
```

`gallagher_separated` replaces the telescoping of `gallagher_grid` — which needs the cells to tile —
by disjointness plus monotonicity of the integral, which is all a separated family provides and all
the Sobolev step actually uses.  `large_values_separated` is then `large_values_count` verbatim, with
the uniform grid hypothesis `∀ r < R, V ≤ ‖f (A + rδ)‖` replaced by `∀ x ∈ P, V ≤ ‖f x‖` for a
`δ`-separated `P`.

Composing with `exists_wellSpaced_subset`: a set of zeros with at most `K` per bucket yields a
separated subset of size `≥ |S|/(2K)`, and that subset is counted by `large_values_separated`.  The
`2K` is the log-power loss, `K = O(log T)`.

## Gates

- [x] `gallagher_separated`, `large_values_separated` — the grid hypothesis removed
- [x] disjoint-cell mass bound proved from `integral_biUnion_finset` + `setIntegral_mono_set`
- [ ] wire `K = O(log T)` from `LittlewoodXi`
- [ ] round the detection length to a natural `N`
- [ ] assemble to `N(σ,T) = o(T)`

## 12. The counting capstone, and the one genuine obstacle left

`card_le_of_large_values` (axiom-clean, built) composes the whole chain:

```text
|Z| · V²  ≤  2K · ( (δ⁻¹ + η⁻¹)∫_A^{B+δ}‖f‖²  +  η∫_A^{B+δ}‖f′‖² )
```

for any finite `Z ⊆ [A,B]` with `‖f‖ ≥ V` on `Z` and at most `K` points per bucket of scale `δ`.
Proof: `exists_wellSpaced_subset` extracts a separated `P` with `|Z| ≤ 2K|P|`, and
`large_values_separated` counts `P`.  This is the counting step of a density argument with the local
density `K` and the two moment bounds as hypotheses.

### 12.1 The abscissa transfer — the real remaining core

`half_le_norm_detPolyC_of_box` gives `1/2 ≤ ‖detPolyC N y ρ‖` **at the zero** `ρ = β + iγ`, whereas
`card_le_of_large_values` needs `‖f(γ)‖ ≥ V` for a **single** function `f` of the real variable.
Different zeros have different `β`, so the two do not compose as they stand.  This is the classical
technical core and it should be named rather than glossed:

* **Abel summation gives a clean partial result.**  With `b_k = k^{−(β−σ)}` positive and decreasing
  and `b_1 = 1`, Abel summation gives
  `‖∑_k e_k k^{−β−iγ}‖ ≤ max_m ‖∑_{k ≤ m} e_k k^{−σ−iγ}‖` — **no logarithmic loss.**  So a zero forces
  some *partial* sum on the line `σ` to be large.
* But the maximum ranges over `≤ Ny` truncations, and a large value of an unspecified partial sum is
  not a large value of one fixed polynomial.  Closing that needs either a maximal-function bound for
  Dirichlet polynomials or the Mellin/Gamma smoothing that moves the abscissa directly:
  `∑_n c_n n^{−ρ}e^{−n/X} = (residue) + (1/2πi)∫_{(σ−β)} M_y(ρ+w)ζ(ρ+w)Γ(w)X^w dw`,
  whose contour has `re(ρ+w) = σ`.

**Note on route.** The corpus's own docstrings point at Carlson's *original* argument —
`FourthMomentDiagonal` says the fourth moment "feeds through **Littlewood's lemma** to reach `o(T)`" —
which avoids large values entirely: `2π∑_{β>σ}(β−σ) = ∫log|ζM_y| + O(·)`, then Jensen.  That route
needs no abscissa transfer.  The large-values route built here is the modern one; it is what gives
quantitative exponents and what a new estimate would have to improve, but it carries this extra step.

## Gates

- [x] `card_le_of_large_values`: the counting step, with `K` and the moments as hypotheses
- [x] the abscissa transfer named precisely, with the Abel-summation partial result
- [ ] abscissa transfer: maximal bound over truncations, or Mellin smoothing
- [ ] alternatively, the Littlewood-lemma route the corpus's docstrings intend

## 13. The layer-cake bridge (Littlewood route)

`GaloisForLFunctions/RHTower/LayerCakeZeroCount.lean`, axiom-clean, registered, built.

The corpus already has the rectangle argument principle (`rectIntegral_logDeriv_boxCount` in
`RectangleResidue`/`CarrierBoxCount`), which produces zero **counts**.  Carlson's argument bounds the
**weighted sum** `∑_ρ (β_ρ − σ₀)`.  The bridge is elementary and now proved:

```text
intervalIntegrable_indicator_lt   the half-line indicator is interval integrable
integral_indicator_lt             ∫_{σ₀}^{σ₁} 1_{σ<β} dσ = β − σ₀   for σ₀ ≤ β ≤ σ₁
sum_sub_eq_integral_count         ∑_β (β − σ₀) = ∫_{σ₀}^{σ₁} #{β : σ < β} dσ
count_le_of_sum_sub               (σ − σ₀)·#{β : σ < β} ≤ ∑_β (β − σ₀)
```

`count_le_of_sum_sub` is the step that converts Carlson's `∑(β − σ₀) = o(T)` into `N(σ,T) = o(T)` for
every `σ > σ₀`, and — unlike the large-values route of §11–§12 — **it needs no abscissa transfer**.
That is what makes the Littlewood route shorter for `o(T)`.

The two routes now both have their combinatorial and measure-theoretic halves formalized:

```text
large values (quantitative)   gallagher_separated, large_values_separated, card_le_of_large_values
Littlewood (o(T))             sum_sub_eq_integral_count, count_le_of_sum_sub
```

What each still needs from the analytic side:

* Littlewood: the rectangle identity `2π∑(β−σ₀) = ∫log|f(σ₀+it)|dt − ∫log|f(σ₁+it)|dt + (horizontals)`
  for `f = ζ·M_y`, then Jensen against `fourthMoment_bounded`.
* large values: the abscissa transfer of §12.1.

## Gates

- [x] layer-cake identity and the count-from-weighted-sum bound, axiom-clean
- [ ] the rectangle log-modulus identity for `ζ·M_y`
- [ ] Jensen step against the bounded fourth moment

## 14. The Jensen step

`GaloisForLFunctions/RHTower/JensenMeanLog.lean`, axiom-clean, registered, built.

The other analytic half of Carlson, and it needs no measure-theoretic Jensen machinery — the tangent
line to `log` at the mean suffices:

```text
log_le_div_add_log_sub_one          log x ≤ x/c + log c − 1        (x, c > 0)
integral_log_le_length_mul_log_mean ∫_a^b log g ≤ (b−a)·log( (∫_a^b g)/(b−a) )
two_mul_integral_log_norm_le        2∫_a^b log‖f‖ ≤ (b−a)·log( mean of ‖f‖² )
```

Choosing `c` to be the mean makes the linear term cancel exactly, which is why no convexity API is
needed.  The last statement is the form Carlson consumes: **a second-moment bound on a vertical
segment caps `∫ log‖f‖` on that segment**, and `FourthMomentDiagonal.fourthMoment_bounded` supplies
exactly such a bound for `ζ·M_y` when `σ > 1/2`.

### 14.1 State of the Littlewood route

```text
have    Jensen step              two_mul_integral_log_norm_le          (§14)
have    layer cake               sum_sub_eq_integral_count             (§13)
have    count from weighted sum  count_le_of_sum_sub                   (§13)
have    second moment for ζ·M_y  fourthMoment_bounded, detection_secondMoment  (corpus)
need    the rectangle identity   2π∑(β−σ₀) = ∫log|f(σ₀+it)| − ∫log|f(σ₁+it)| + horizontals
```

The one missing link is the rectangle log-modulus identity.  The corpus's
`rectIntegral_logDeriv_boxCount` gives the argument principle but requires an explicit factorization
`f = (∏(z−ρᵢ)^{mᵢ})·h` with `h` analytic and zero-free — available for the finite carrier
(`completedGN_offline_factor`) but not yet for `ζ·M_y` on a box.  Supplying that factorization, or
proving Littlewood's lemma directly by integrating the argument principle in `σ` (which is what
`sum_sub_eq_integral_count` makes possible without any branch of `log`), closes the route.

## Gates

- [x] Jensen step, axiom-clean, in the exact form Carlson consumes
- [ ] rectangle log-modulus identity for `ζ·M_y`, or the box factorization it needs

## 15. The Carlson skeleton

`GaloisForLFunctions/RHTower/CarlsonSkeleton.lean`, axiom-clean, registered, built.

Everything except Littlewood's rectangle identity is now assembled into one theorem, with that
identity appearing as an explicit hypothesis:

```text
count_le_of_rectangle_and_moment
  hlittle : 2π ∑_β (β − σ₀) ≤ L₀ − L₁ + E                (the rectangle identity)
  hJensen : 2 L₀ ≤ (T₂−T₁)·log( M/(T₂−T₁) )              (JensenMeanLog)
  hright  : −D(T₂−T₁) ≤ L₁                               (right-edge log-modulus)
  ⟹ (σ−σ₀)·#{β : σ < β} ≤ [ (T₂−T₁)log(M/(T₂−T₁))/2 + D(T₂−T₁) + E ] / 2π

count_le_linear_of_boundary
  M ≤ C(T₂−T₁),  E ≤ F(T₂−T₁)
  ⟹ (σ−σ₀)·#{β : σ < β} ≤ (T₂−T₁)·( log C/2 + D + F ) / 2π
```

The second is the `O(T)` shape with every constant explicit in the boundary data; Carlson's
sublinearity comes from letting `σ₁ → σ` afterwards, which leaves `(σ−σ₀)⁻¹` as the only blow-up.

### 15.1 What the whole lane now looks like

```text
ZeroDetectionEM     zeros ⟹ large values of an explicit finite Dirichlet polynomial
WellSpacedSubset    local density ⟹ separated subset ⟹ large-values count
LayerCakeZeroCount  weighted zero sum ⟷ integral of the counting function
JensenMeanLog       second moment ⟹ bound on ∫ log‖f‖
CarlsonSkeleton     all of the above ⟹ a zero count, given the rectangle identity
```

Five modules, every declaration axiom-clean on `[propext, Classical.choice, Quot.sound]`.  The single
remaining analytic input is the rectangle identity, for which the corpus has both the argument
principle (`rectIntegral_logDeriv_boxCount`) and the general zero-peeling lemma (`exists_multi_peel`)
that supplies its factorization hypothesis.

## Gates

- [x] Carlson skeleton assembled; rectangle identity isolated as the only hypothesis
- [x] `exists_multi_peel` located as the general factorization tool for `ζ·M_y`
- [ ] the rectangle identity itself

## 16. The branch-free route to Littlewood's lemma, and the tool it needs

`GaloisForLFunctions/RHTower/LogModulusHorizontal.lean`, axiom-clean, registered, built.

```text
hasDerivAt_log_norm_comp          d/dv log‖g v‖ = Re(g′/g)         (g v ≠ 0)
integral_re_logDeriv_horizontal   ∫_{σ₀}^{σ₁} Re(f′/f)(σ+it) dσ = log‖f(σ₁+it)‖ − log‖f(σ₀+it)‖
```

**No branch of the logarithm appears anywhere**, which is what normally makes Littlewood's lemma
expensive to formalize.

### 16.1 The derivation this completes

Take the imaginary part of the argument principle on the sub-rectangle `R_σ = [σ,σ₁]×[T₁,T₂]`
(`∮ f′/f = 2πi·N`), splitting the contour into its four edges — horizontals carry `ds = dσ`,
verticals carry `ds = i dt`:

```text
2π N(σ) =  ∫_σ^{σ₁} Im(f′/f)(u+iT₁) du  +  ∫_{T₁}^{T₂} Re(f′/f)(σ₁+it) dt
         − ∫_σ^{σ₁} Im(f′/f)(u+iT₂) du  −  ∫_{T₁}^{T₂} Re(f′/f)(σ+it) dt
```

Now integrate in `σ` over `[σ₀,σ₁]` and use `sum_sub_eq_integral_count` on the left.  The **last**
term becomes, by Fubini and then `integral_re_logDeriv_horizontal`,

```text
−∫_{T₁}^{T₂} [ ∫_{σ₀}^{σ₁} Re(f′/f)(σ+it) dσ ] dt
  = −∫_{T₁}^{T₂} [ log‖f(σ₁+it)‖ − log‖f(σ₀+it)‖ ] dt ,
```

which is exactly Littlewood's log-modulus pair.  The remaining three terms are
`(σ₁−σ₀)∫ Re(f′/f)(σ₁+it) dt` and two horizontal `Im` double integrals — together the error `E` of
`CarlsonSkeleton.count_le_of_rectangle_and_moment`, controlled by the right edge (where `f ≈ 1`) and
the two horizontal cuts.

So the whole of Littlewood's lemma reduces to: the imaginary-part form of the argument principle on a
rectangle, Fubini, and the lemma just proved.  Nothing else.

### 16.2 The lane

```text
ZeroDetectionEM        zeros ⟹ large values of an explicit finite Dirichlet polynomial
WellSpacedSubset       local density ⟹ separated subset ⟹ large-values count
LayerCakeZeroCount     weighted zero sum ⟷ integral of the counting function
JensenMeanLog          second moment ⟹ bound on ∫ log‖f‖
LogModulusHorizontal   ∫ Re(f′/f) dσ = increment of log‖f‖, branch-free
CarlsonSkeleton        all of the above ⟹ a zero count, given the rectangle identity
```

Six modules, every declaration axiom-clean.

## Gates

- [x] branch-free horizontal log-modulus identity
- [x] the full derivation of Littlewood's lemma from it written out and checked term by term
- [ ] imaginary-part form of the argument principle on a rectangle
- [ ] Fubini for the `σ`-integrated contour

## 17. Littlewood's lemma, assembled

`GaloisForLFunctions/RHTower/RectIntegralEdges.lean`, axiom-clean, registered, built.

```text
integral_im_eq, integral_re_eq   interval integration commutes with Re and Im
im_rectIntegral                  Im(rectIntegral g) = ∫Im g (horizontals) + ∫Re g (verticals)
two_pi_mul_count_eq_edges        argument principle in edge form: 2πn = Bot − Top + Right − Left
littlewood_from_edges            ∫ the edge identity in σ, apply the layer cake ⟹
                                 2π ∑_β (β − σ₀) = ∫(Bot − Top + Right) − logPair
```

`logPair` is `∫_{σ₀}^{σ₁} Left σ dσ`, which by Fubini and `integral_re_logDeriv_horizontal` is
`∫_{T₁}^{T₂}[log‖f(σ₁+it)‖ − log‖f(σ₀+it)‖]dt` — the Littlewood log-modulus pair.  **Fubini and the
edge integrabilities are the hypotheses; every other step is proved.**  No branch of the logarithm
appears anywhere in the chain.

### 17.1 The lane, complete to its analytic hypotheses

```text
ZeroDetectionEM        zeros ⟹ large values of an explicit finite Dirichlet polynomial
WellSpacedSubset       local density ⟹ separated subset ⟹ large-values count
LayerCakeZeroCount     weighted zero sum ⟷ integral of the counting function
JensenMeanLog          second moment ⟹ bound on ∫ log‖f‖
LogModulusHorizontal   ∫ Re(f′/f) dσ = increment of log‖f‖, branch-free
RectIntegralEdges      argument principle in edge form ⟹ Littlewood's lemma
CarlsonSkeleton        Littlewood + Jensen + layer cake ⟹ a zero count
```

Seven modules, every declaration axiom-clean on `[propext, Classical.choice, Quot.sound]`.

What is still hypothesis rather than theorem, stated exactly:

1. the factorization of `ζ·M_y` on a box (`exists_multi_peel` supplies the general tool);
2. Fubini for the `σ`-integrated left edge, and the four edge integrabilities;
3. the second moment for `ζ·M_y` on `re s = σ₀` (`fourthMoment_bounded` in the corpus — needs wiring);
4. the right-edge log-modulus lower bound.

All four are standard analytic facts about `ζ` times a Dirichlet polynomial on a compact box.  None
is an idea; all are work.

## Gates

- [x] Littlewood's lemma assembled, branch-free, from the argument principle in edge form
- [ ] items 1–4 above

## 18. Fubini discharged

`GaloisForLFunctions/RHTower/BoxFubini.lean`, axiom-clean, registered, built.

```text
interval_integral_swap_of_continuous   iterated integrals of a continuous F over a compact box agree
integral_left_edge_eq_logPair          ∫_{σ₀}^{σ₁} ∫_{T₁}^{T₂} Re(f′/f) dt dσ
                                         = ∫_{T₁}^{T₂} ( log‖f(σ₁+it)‖ − log‖f(σ₀+it)‖ ) dt
```

The first is Fubini with integrability supplied by continuity on the compact box
(`IsCompact.exists_bound_of_continuousOn` plus `Measure.prod_restrict`); the second composes it with
`integral_re_logDeriv_horizontal`.  This **discharges the Fubini hypothesis of
`littlewood_from_edges`** for `f` analytic and nonvanishing on the closed box.

Remaining hypotheses of the chain, updated:

```text
1. box factorization of ζ·M_y                (exists_multi_peel is the general tool)  — open
2. Fubini for the σ-integrated left edge     — DONE (§18)
2'. the four edge integrabilities            — open, follows from continuity
3. second moment for ζ·M_y on re s = σ₀      — fourthMoment_bounded, needs wiring
4. right-edge log-modulus lower bound        — open
```

Eight modules, every declaration axiom-clean.

## Gates

- [x] Fubini on a compact box for a continuous integrand
- [x] the log-modulus pair as a theorem, not a hypothesis
- [ ] items 1, 2', 3, 4

## 19. The right edge

`GaloisForLFunctions/RHTower/RightEdgeBound.lean`, axiom-clean, registered, built.

```text
half_le_norm_of_dist_le_half              ‖w − 1‖ ≤ 1/2 ⟹ 1/2 ≤ ‖w‖
length_mul_log_le_integral_log_norm       c ≤ ‖g‖ on the edge ⟹ (T₂−T₁)log c ≤ ∫ log‖g‖
neg_log_two_mul_length_le_integral_log_norm
                                          ‖g − 1‖ ≤ 1/2 on the edge ⟹ −(log 2)(T₂−T₁) ≤ ∫ log‖g‖
```

This is `hright` of `CarlsonSkeleton.count_le_of_rectangle_and_moment`, with `D = log 2`.  On the
right edge `ζ·M_y = 1 + (terms of index > min(N,y))`, so closeness to `1` is exactly what
`MollifierDetection.detection_poly_eq` provides once the abscissa is in the half-plane of absolute
convergence.

Ledger:

```text
1.  box factorization of ζ·M_y            exists_multi_peel is the tool          open
2.  Fubini for the σ-integrated left edge                                        DONE §18
2'. the four edge integrabilities         immediate from continuity              open (routine)
3.  second moment for ζ·M_y on re s = σ₀  fourthMoment_bounded, needs wiring      open
4.  right-edge log-modulus lower bound                                           DONE §19
```

Nine modules, every declaration axiom-clean.

## Gates

- [x] right-edge log-modulus lower bound from closeness to one
- [ ] items 1, 2', 3

## 20. The CCM constraint-coordinate targets are Hermite values at the origin

`ConstraintCoordinateHermiteValues.lean`, axiom-clean, registered, built.

The four constants carried as hypotheses by the CCM constrained-prolate transfer are one constant:

```text
target_n = (2π)^{1/4} · |h_n(0)| ,  h_n(x) = (2^n n! √π)^{−1/2} H_n(x) e^{−x²/2} ,  n = 0,2,4,6
```

verified to 30 digits and then formalized in squared form, where `π` cancels against the Hermite
normalization:

```text
target_n² = √2 · H_n(0)²/(2^n n!) :   √2,  √2/2,  3√2/8,  5√2/16
positive sector (0,4) ratio 3/8      negative sector (2,6) ratio 5/8
```

**Consequence.** The remaining constraint-coordinate hypothesis of the CCM/Connes route in this tree
is not four arithmetic inputs but a single classical statement: large-aperture convergence of the
prolate coordinates to Hermite values at the origin, in the standard normalization with the standard
`(2π)^{1/4}` prolate factor.  That is Slepian's regime, not a new obstruction.  What remains genuinely
open on this route is then the **Bessel bound** `∑_j ℓ(λ,j)² ≤ 2λ`.

Also recorded: my Krein–Rutman conjecture (that the constrained ground state is nodeless, hence even)
is **FALSE** — the corpus's own proved limit is `twoModeSeedFun ℓ = (−ℓ₁, ℓ₀, 0, …)`, which changes
sign — and it was unnecessary, since `ccmFuchsScale` indexes prolate modes `4j` and `4j+2`, all even,
so parity is structural rather than hypothetical.

## Gates

- [x] the four CCM targets identified as `(2π)^{1/4}|h_n(0)|`, exactly
- [x] both sector ratios (`3/8`, `5/8`) derived from Hermite data
- [x] Krein–Rutman conjecture refuted from the corpus
- [ ] cite/prove the prolate→Hermite limit at the origin
- [ ] the Bessel bound `∑_j ℓ(λ,j)² ≤ 2λ`

## 21. The Bessel inputs are Bessel's inequality

`ConstraintBesselDischarge.lean`, axiom-clean, registered, built.

```text
constraint_bessel_of_orthonormal   coordinates = inner products against an orthonormal family
                                   ⟹ hsum and hbessel follow from ‖v‖² ≤ 2λ alone
paleyWiener_kernel_norm_le         λ/π ≤ 2λ           (margin > 6, since 1/π < 2)
constraint_bessel_of_paleyWiener   with ‖v‖² = λ/π, both hypotheses hold
```

So the transfer's `hsum` and `hbessel` are `Orthonormal.inner_products_summable` and
`Orthonormal.tsum_inner_products_le` once the constraint coordinates are recognized as the expansion
of one vector in the prolate basis, and the required bound is not sharp — the Paley–Wiener
reproducing kernel at the origin has squared norm `λ/π`, six times inside the allowance.

### 21.1 Status of the CCM constraint-coordinate inputs

```text
hsum     Bessel summability                      DISCHARGED §21
hbessel  ∑ ℓ² ≤ 2λ                                DISCHARGED §21 (margin > 6)
hl0, hl1 prolate → Hermite at the origin          IDENTIFIED §20 as (2π)^{1/4}|h_n(0)|, classical
hgrow    A 2 ≤ C^j A(j+2)                          depends on the Fuchs rates
```

**What is left is the source lock itself**: that the arithmetic restricted-Weil constraint vector is
the band-limited evaluation kernel and that the leakage diagonal is the prolate/Fuchs rate sequence.
Every *numerical* input the transfer carried is now either classical or free; the open core is the
identification, not the estimates.

## Gates

- [x] `hsum`, `hbessel` discharged from Bessel's inequality with an explicit margin
- [x] `hl0`, `hl1` identified as classical prolate→Hermite values
- [ ] the source lock: arithmetic constraint vector = band-limited evaluation kernel
- [ ] the source lock: leakage diagonal = prolate/Fuchs rates

## 22. The source lock has a uniformity gap

`fuchsRate A n lam = A · lam^(2n+1) · exp(−4π lam²)` is **Fuchs's 1964 asymptotic** for the `n`-th
prolate leakage,

```text
1 − λ_n(c)  ~  4√π · 8ⁿ · c^{n+1/2} · e^{−2c} / n!     at   c = 2π lam² ,
```

since `c^{n+1/2} ∝ lam^{2n+1}` and `e^{−2c} = e^{−4π lam²}` — both factors match exactly.  So the
corpus's abstract scale family *is* the Slepian/Fuchs leakage, and the intended constants are
`A_n = 4√π · 8ⁿ · (2π)^{n+1/2}/n!`.

**But those constants violate the transfer's growth hypothesis.**
`ccm_tendsto_min_norm_lp_normalize_sub_twoModeSeed` requires

```text
hgrow : ∀ j, A 2 ≤ C ^ j * A (j + 2)          for a fixed C
```

With `A_j^corpus = A(4j)` the true sequence rises to a peak at prolate index `≈ 16π ≈ 50` (`j ≈ 12`)
and then decays factorially.  The `C` required by `hgrow` diverges:

```text
j        10      20      40      60      100     200
C ≥      0.070   0.476   4.36    17.7    111     1488
```

**No fixed `C` exists.**  This is not a defect of the transfer but a mismatch of quantifiers: Fuchs's
asymptotic is valid for `n` fixed (or `n = o(c)`) as `c → ∞`, whereas the transfer ranges over all
`j ∈ ℕ` at each aperture and needs uniformity in the mode index.

**Consequence.**  The source lock cannot be performed with the true constants as `hgrow` is stated.
Either the transfer's index range must be cut to `n ≲ c` — exactly where the asymptotic is valid —
or the growth hypothesis must be replaced by one the genuine leakage satisfies.  This is a located
gap between the abstract convergence theorem and its intended arithmetic source, and it sits
*upstream* of everything discharged in §20–§21.

## Gates

- [x] `fuchsRate` identified as Fuchs 1964 at `c = 2π lam²`, both factors exact
- [x] `hgrow` shown incompatible with the true constants; required `C` diverges
- [ ] restrict the transfer's index range to `n ≲ c`, or weaken `hgrow`

## 23. The repair: saturation replaces growth

`SecularTailSaturation.lean`, axiom-clean, registered, built.

Growth is the wrong hypothesis for the job `hgrow` was doing.  What controls the secular tail is a
**floor** on the leakage, and the true Slepian leakage has one: past the Fuchs window the prolate
eigenvalues `λ_n(c)` collapse to `0`, so `d_j = 1 − λ_j` saturates near `1`.

```text
sq_secular_le_of_floor      dinf ≤ d j, μ < dinf ⟹ (ℓ_j/(d_j−μ))² ≤ ℓ_j²/(dinf−μ)²
summable_secular_of_floor   a floor turns Bessel summability of ℓ into summability of the
                            secular vector — with no condition on the growth of A
tsum_secular_tail_le        the secular tail is the constraint tail divided by the squared gap
```

So the tail is inherited from the Bessel bound already discharged in §21, and the factorially
decaying Fuchs constants are harmless: they only make the leakage *larger* past the window, which
strengthens the floor.

**Net effect on the route.**

```text
was:  hgrow (uniform exponential growth of A)   — violated by the true Fuchs constants
now:  a positive floor on d beyond the window   — satisfied by the true Slepian leakage
```

The repair is unconditional and needs nothing the transfer did not already have.  What it does not
do is establish the floor for the *arithmetic* leakage — that is the residue, and it is a statement
about prolate eigenvalue collapse rather than about ζ.

## Gates

- [x] the growth hypothesis diagnosed as the wrong tool and replaced by a leakage floor
- [x] tail estimate proved from the floor plus Bessel summability, axiom-clean
- [ ] establish the floor for the arithmetic leakage (prolate eigenvalue collapse past `n ≈ c`)

## 24. The floor from the trace — the residue closes

`LeakageFloorFromTrace.lean`, axiom-clean, registered, built.

The floor needed by §23 requires no eigenvalue asymptotics at all.  Two soft facts suffice:
the Slepian eigenvalues are nonnegative and decreasing, and their sum is the trace `2c/π`.

```text
antitone_le_of_partialSum_le   nonneg antitone with partial sums ≤ T  ⟹  λ_n ≤ T/(n+1)
half_le_leakage_of_trace       n + 1 ≥ 2T  ⟹  1 − λ_n ≥ 1/2
exists_leakage_floor           the floor holds cofinally, for any bound T
```

`(n+1)λ_n ≤ ∑_{k ≤ n}λ_k ≤ T` — a Markov bound, nothing more.  With `T = 2c/π` this reproduces the
classical `2c/π` degrees-of-freedom transition, and it holds **precisely in the regime where Fuchs's
expansion is invalid**, which is what the growth hypothesis was failing on.

### 24.1 The CCM transfer's hypotheses, end of cycle

```text
hl0, hl1  four constants     → one classical asymptotic, (2π)^{1/4}|h_n(0)|, exact       §20
hsum      summability        → Orthonormal.inner_products_summable                        §21
hbessel   ∑ℓ² ≤ 2λ           → Bessel; margin > 6 via the Paley–Wiener kernel λ/π         §21
hgrow     growth of A        → wrong tool; replaced by a leakage floor                     §22–23
floor     leakage ≥ 1/2      → from nonnegativity, monotonicity, and the trace             §24
```

**None of the surviving inputs is about `ζ`.**  What remains is the identification itself: that the
arithmetic restricted-Weil compression *is* the Slepian time–bandwidth operator at `c = 2π lam²`,
and that the constraint vector *is* the Paley–Wiener evaluation kernel.  That is a statement about
Connes' construction, not an estimate, and it is the whole of the source lock.

## Gates

- [x] leakage floor proved from nonnegativity, monotonicity and the trace — no asymptotics
- [x] every numerical hypothesis of the CCM transfer discharged or classicalized
- [ ] the source lock: restricted-Weil compression = Slepian operator at `c = 2π lam²`
- [ ] the source lock: constraint vector = Paley–Wiener evaluation kernel

## 25. The source lock is a trace-class perturbation, and both halves are in the tree

Searching for the missing edge rather than assuming it is absent:

```text
free side       HTGeometry/TwoProjectionSupersymmetry, TwoProjectionHilbertSchmidtEnergy
                — the two-projection (time-band) theory, i.e. the Slepian operator
arithmetic side RHTower/SoninTimeBandHilbertSchmidt
                — centralSoninWeightedPrimePowerResidual proved Hilbert–Schmidt and
                  IsSoninTimeBandTraceIdeal.isTraceClass
```

So the arithmetic (prime-power) perturbation of the time-band structure is **trace class**.  That is
exactly the mechanism the source lock needs: a trace-class perturbation cannot change the eigenvalue
asymptotics, so the leakage floor of §24 and the Fuchs window of §22 transfer from the free Slepian
operator to the arithmetic one.

**The lock is therefore not an estimate and not an identity — it is an assembly**: compose the
two-projection theory with the trace-class residual to conclude that the restricted-Weil compression
is the free time-band operator plus a trace-class term, at `c = 2π lam²`.  Both inputs are proved in
this tree; the composition is not written.

### 25.1 Cycle ledger

```text
§20  four constraint constants  = (2π)^{1/4}|h_n(0)|, exact to 30 digits
§21  hsum, hbessel              = Bessel; Paley–Wiener margin > 6
§22  hgrow                      violated by the true Fuchs constants; C diverges (verified to j=200)
§23  repair                     leakage floor replaces growth; tail from Bessel alone
§24  floor                      from nonnegativity, monotonicity, trace — a Markov bound
§25  source lock                = trace-class perturbation; both halves present, edge missing
```

Seven modules, all axiom-clean.  Nothing here is a new theorem about `ζ`; what is new is that the
CCM route's open core, stated in this tree as "source-locked comparison", now has no numerical
content left inside it and reduces to one composition of two proved facts.

## Gates

- [x] both halves of the source lock located: two-projection theory and trace-class prime residual
- [x] the lock re-characterized as a trace-class perturbation statement, not an identity
- [ ] the composition itself

## 26. The composition, written

`FloorUnderTraceClassPerturbation.lean`, axiom-clean, registered, built.

```text
exists_floor_of_summable_perturbation   a cofinal floor survives any summable perturbation
exists_perturbed_leakage_floor          free floor 1/2 (from the trace) ⟹ perturbed floor 1/4
summable_secular_of_traceClass_perturbation
                                        the perturbed floor feeds the secular tail estimate directly
```

A trace-class operator has summable eigenvalues, and a summable perturbation tends to zero, so past
some index it cannot consume more than half the floor.  That is the whole spectral content of the
source lock, and the corpus already proves the trace-class half
(`IsSoninTimeBandTraceIdeal.isTraceClass`).

### 26.1 The chain, complete

```text
constants   four targets = (2π)^{1/4}|h_n(0)|                                    §20
Bessel      hsum, hbessel from Orthonormal + Paley–Wiener kernel λ/π             §21
growth      hgrow refuted against the true Fuchs constants                       §22
repair      leakage floor replaces growth; tail from Bessel                      §23
floor       free floor from nonnegativity, monotonicity, trace (Markov)          §24
lock        source lock = trace-class perturbation; both halves in the tree      §25
compose     floor survives the perturbation; secular tail follows                §26
```

What is left is one wiring step and one identification, both stated exactly:

* `ContinuousLinearMap.IsTraceClass ⟹ Summable (eigenvalues)` — Lidskii/Weyl, not yet in the tree;
* that the restricted-Weil compression *is* the free time–band operator plus that trace-class term
  at `c = 2π lam²`.

Neither is an estimate.  Every numerical hypothesis the CCM transfer carried has been discharged,
classicalized, or refuted-and-repaired.

## Gates

- [x] the composition written: floor survives trace-class perturbation, feeds the tail estimate
- [ ] `IsTraceClass ⟹ Summable eigenvalues`
- [ ] the operator identification at `c = 2π lam²`

## 27. The Lidskii step is not needed

`HTGeometry/DiagonalSummableOfFactors.lean`, axiom-clean, registered, built.

What the composition of §26 consumes is summability of the **diagonal** of the arithmetic
perturbation, not of its eigenvalues.  For `T = S ∘ U`,

```text
⟪T e_i, e_i⟫ = ⟪U e_i, S† e_i⟫ ,     |⟪T e_i, e_i⟫| ≤ ‖U e_i‖·‖S† e_i‖ ,
```

and both factors are square-summable because `U` and `S†` are Hilbert–Schmidt.  Summability then
follows from `ab ≤ (a²+b²)/2` — no spectral theory at all.

```text
summable_mul_of_summable_sq        product of two square-summable nonneg families is summable
summable_of_le_mul_of_summable_sq  domination transfer
summable_diagonal_of_factors       |diag| ≤ a·c with a, c square-summable ⟹ |diag| summable
summable_diagonal_signed           hence the signed diagonal
```

**So `IsTraceClass ⟹ Summable eigenvalues` (Lidskii) is not required.**  The tree already proves the
factorization (`IsSoninTimeBandTraceIdeal.exists_hilbertSchmidt_factors`), and the Cauchy–Schwarz
bound is all that stands between it and the floor-perturbation composition.

### 27.1 What is left of the source lock

Exactly one thing: **the operator identification** — that the restricted-Weil compression is the
free time–band operator plus that trace-class term at `c = 2π lam²`.  Every hypothesis around it is
now discharged:

```text
constants  (2π)^{1/4}|h_n(0)|          §20      Bessel     Orthonormal + Paley–Wiener   §21
growth     refuted, repaired            §22–23   floor      Markov from the trace         §24
lock shape trace-class perturbation     §25      compose    floor survives it             §26
diagonal   Cauchy–Schwarz, no Lidskii   §27
```

## Gates

- [x] diagonal summability from the Hilbert–Schmidt factorization; Lidskii not needed
- [ ] the operator identification at `c = 2π lam²` — the whole of what remains

## 28. Correction: §25 is wrong — the perturbation is not compact

`SoninEulerQuadraticCorner.lean` proves, unconditionally,

```text
archimedeanPrimeEulerQuadraticCorner_not_isCompactOperator (a p q) (0 < a) (1 < p) (1 < q) :
    ¬ IsCompactOperator (archimedeanPrimeEulerQuadraticCorner a p q)
```

— "every literal two-scale Euler Gram entry on the concrete archimedean Hardy–Titchmarsh carrier is
noncompact."

So the source lock is **not** "free time–band operator plus a trace-class term", as §25 asserted.
Only the *principal-subtracted* residual is trace class (`centralSoninWeightedPrimePowerResidual`,
`centralSoninDilationCornerResidualEnergy_isTraceClass`); the raw arithmetic corners are not even
compact.  Any identification must carry the principal part explicitly, and that part is noncompact.

**This is the third structural claim of mine the corpus has refuted this cycle** — after the
Krein–Rutman nodelessness (refuted by `twoModeSeedFun`) and the parity hypothesis (unnecessary,
`ccmFuchsScale` indexes `4j`).  Each time the refutation was a theorem already in the tree that I had
not read before conjecturing.

### 28.1 What the correction buys

It identifies the obstruction with the one Connes names.  His 2026 survey states the primary
obstruction as "the absence of a genuine *ultraviolet model* for the zeta function".  A noncompact
principal part is exactly an ultraviolet obstruction: it is high-frequency mass that no trace-class
comparison can absorb.  **The corpus's noncompactness theorem and Connes' missing UV model are the
same wall**, and the machinery of §§20–27 is what remains valid *below* it — everything infrared is
now discharged.

So the honest statement of the CCM route's open core, after this cycle:

> Infrared: closed.  Constants classical, Bessel free, growth repaired, floor from the trace,
> composition written.
> Ultraviolet: open, and provably not reachable by trace-class comparison — the raw Euler corners
> are noncompact.

## Gates

- [x] §25 retracted: the arithmetic perturbation is noncompact, not trace class
- [x] the obstruction identified with Connes' missing ultraviolet model
- [ ] an ultraviolet model — the actual wall

## 29. Where the only unconditional zero theorem actually lands

`WeilIndexExtinctionTime.lean` records a structure I had not seen and which passes every test applied
in this audit:

```text
ind₋(W_{Ξ_t}) = ½ · N_off(t)          the negative Weil index counts off-critical zeros
N_off(t) = 0  ⟺  t ≥ Λ                definition of the de Bruijn–Newman constant
⟹  Λ = the extinction time of the Weil index along the de Bruijn–Newman flow
⟹  RH ⟺ ind₋(W_ξ) = 0 ⟺ Λ ≤ 0
```

`t ↦ ind₋(W_{Ξ_t})` is **nonincreasing and integer-valued**, dropping by at least one at each merge of
a conjugate pair onto the real axis.

This matters because of what sits on the other side: **Rodgers–Tao (2020) prove `Λ ≥ 0`
unconditionally.**  So `RH ⟺ Λ = 0`, and one half of that equality is a theorem.  It is the only
place in this tree where an unconditional theorem about the zeros of `ζ` meets an exact invariant
rather than an averaged bound — it is not a re-encoding of `conj ρ = 1 − ρ`, not a face, and not
`loglog`-limited.

Contrast with everything else audited:

```text
re-encodings (~96)   Q invariant under s ↦ 1−conj s              no content
faces                hypotheses used in finite case splits        not open cores
moment problems      Hankel / Bernstein on ∑γ^{−2n}               RH-hard, both blind
Carlson density      classical, o(T), no quantitative exponent
CCM / prolate        infrared closed (§20–§27); ultraviolet wall (§28)
dBN index            RH ⟺ Λ = 0, with Λ ≥ 0 a theorem            ← unconditional half exists
```

**The discrete invariant is the structurally distinctive feature.**  An integer-valued monotone
function of flow time is not the kind of object the analytic no-gos of this audit apply to: they all
concern sizes of quadratic forms, and this concerns a count.

## Gates

- [x] the dBN/Weil-index structure located and its position against the audit recorded
- [ ] whether the index formulation admits any attack on `Λ ≤ 0` that the analytic route does not

## 30. The corpus's ceiling map — and the answer to §29

`ExtensionProgrammeNoGo.lean` carries the tree's own systematic map:

```text
linear Λ-positivity           caps at PNT strength                  (Theorem N)
quadratic Weil index          gives lower bounds on ind₋ only       (Theorem N′)
Bohr-torus probability        valid only past height ~ π(N)         (Theorem G)
elementary archimedean tower  optimal at ℓ ≈ 0.155                  (Theorems Q24–V29)
extension of the range        equivalent to RH                      (this file)
axiomatic characterization    circular or false                     (Theorems M, P, R)
```

with the extension no-go proved outright:

```lean
extension_forces_positivity : λ antitone, b monotone, b ≤ λ, 0 ≤ b L₀ ⟹ ∀ L, 0 ≤ λ L
```

A nondecreasing lower bound for `λ(L) = inf spec Q_L` that is nonnegative at a *single* length forces
`λ ≥ 0` everywhere — i.e. RH.  So no such bound is obtainable short of RH, and the entire extension
lane closes.

**This answers §29.**  The de Bruijn–Newman index route has its own ceiling, Theorem N′: the
quadratic Weil index yields **lower** bounds on `ind₋` only, while RH needs `ind₋ = 0`, an **upper**
bound.  That is the same asymmetry identified independently earlier in this audit — the unconditional
engines bound from below the quantity RH needs bounded above.  The discreteness of the invariant does
not change the direction of the available bounds.

### 30.1 The session's map, complete

```text
re-encodings (~96)   Q invariant under s ↦ 1−conj s         no content                    §1–§8
faces                finite case splits                      not open cores                §1
moment problems      Hankel / Bernstein on ∑γ^{−2n}          RH-hard; both blind           §7, §14
Carlson density      classical o(T); no exponent             1920, built then abandoned    §9–§19
CCM / prolate        infrared CLOSED; ultraviolet wall       = Connes' missing UV model    §20–§28
dBN index            RH ⟺ Λ = 0, Λ ≥ 0 a theorem            ceiling N′: lower bounds only  §29–§30
extension programme  provably equivalent to RH               closed outright               §30
```

**Every lane in this tree terminates at the same asymmetry**: the available unconditional information
bounds from below what RH requires bounded above.  The one place that is *not* a size statement — the
CCM ultraviolet — is where Connes locates the missing model, and §28 shows it cannot be crossed by
trace-class comparison.

## Gates

- [x] the ceiling map located; §29's question answered by Theorem N′
- [x] the extension lane's no-go read and recorded
- [ ] an ultraviolet model — the single object not covered by any ceiling in the map

## 31. One of the two survivors collapses

`PrimeArchSelfAdjointVacuumRealization` asks for a **bounded** self-adjoint `A` and a vacuum `ω` with
`⟪ω, Aⁿω⟫ = normalizedPrimeArchMoment n`.  By the spectral theorem that is exactly a representing
measure for `(a_n)`, and boundedness forces compact support — so it is the **Hausdorff** moment
problem for `a_n = 2∑_ρ γ_ρ^{−2(n+1)}`, whose measure lives on `[0, γ₁^{−2}]`.

Conversely any representing measure gives the realization: `A =` multiplication by `x` on `L²(μ)`,
`ω = 1`.

**So the realization is not a new object.**  It is the moment problem audited in §7 and §14 — and
that audit showed the Hausdorff/Bernstein form is *blinder* than the Hankel form: the coefficients
band-pass at `γ ≈ γ₁√((n+k)/n)`, so reaching height `T` needs `k ≈ (T/γ₁)²` against
`N ≈ (T/2π)log T`, and a single off-line pair contributes amplitude `~1/|γ|²` against an on-line bulk
of `~log|γ|/|γ|`.

The unconditional pinch `(19/20)·secondMoment < bornWittenSource ≤ secondMoment` remains a genuine
and unusual asset — an upper bound on the RH-vanishing quantity, which no other lane has — but the
object it pinches is the one already known to be blind.

### 31.1 Final map

```text
re-encodings (~96)     one identity, no content
faces                  finite case splits
Carlson density        classical o(T); built and abandoned
moment problems        Hankel and Hausdorff; both blind; the prime-arch realization is this
prime-arch pinch       unconditional UPPER bound, factor 16c(1−c)/(4−5c)² — pins a blind object
dBN index              ceiling N′: lower bounds on ind₋ only
extension programme    provably equivalent to RH
CCM / prolate          infrared CLOSED; ULTRAVIOLET WALL — the one object not reducible
```

**Exactly one live object remains: the ultraviolet model.**  Everything else in this tree either has
a proved ceiling, is a re-encoding, or reduces to the moment problem whose blindness is quantified.

## Gates

- [x] the self-adjoint realization identified as the Hausdorff moment problem, hence already audited
- [x] final map: one irreducible live object
- [ ] the ultraviolet model

## 32. The Toeplitz/Fredholm reframing of the UV problem — tested and refuted

**Conjecture.** `archimedeanPrimeEulerCorner a p` is a compressed dilation, so the Gram
`(E_p)†E_q` is a compressed dilation by `q/p`.  Compressions of a group action to a band generate a
Toeplitz algebra: essential spectrum = range of the symbol, index = winding number.  That would make
the Weil index `ind₋` a **Fredholm index** — a continuum-valued geometric object immune to the
size-estimate no-gos — and the UV model would be the symbol algebra.

**Test.**  `FiniteSuperzetaFredholmLogDerivativeUniversalityLaw` gives the exact transform

```text
Σᵢ (1 − z rᵢ)⁻¹ = n − z · logDeriv( det₁(1 − z·diag r) ) .
```

The prime–arch moments `a_n = 2∑_ρ γ_ρ^{−2(n+1)}` are the power traces of the operator with
eigenvalues `γ^{−2}`, so their generating function is exactly this superzeta resolvent, and the
Fredholm determinant `det₁(1 − zA)` is `Ξ` up to Hadamard normalization.  Its winding number is
therefore the argument principle applied to `Ξ`, i.e. `S(T)` — and `ind₋ = ½N_off` is precisely what
`S` jumps by.

**Verdict: `REDISCOVERED`.**  The Fredholm-index reframing *is* the de Bruijn–Newman index route, and
that route carries ceiling **N′**: the quadratic Weil index gives lower bounds on `ind₋` only, while
RH needs an upper bound.  Changing from a quadratic form to an index does not change the direction of
the available bounds, because the index is a count and the unconditional information bounds counts
from below.

This is the fourth structural conjecture of mine the corpus has refuted in this audit, and the
mechanism is the same each time: the reframing preserves the direction of the asymmetry.

## Gates

- [x] Toeplitz/Fredholm UV reframing stated exactly and tested against the corpus
- [x] verdict `REDISCOVERED`: it is the index route, ceiling N′
- [ ] a UV model whose invariant is *not* a count — the only remaining shape

## 33. Testing the "unordered invariant" constraint on the Deninger lane

§32 sharpened the target: the UV invariant must not be a **count**, because counts and sizes are both
*ordered* and every unconditional engine here bounds ordered quantities from one side only.  The
natural candidate is an invariant in an unordered group — a cohomology or obstruction class.  That
points at Deninger's programme, and the tree has a large Deninger lane.

**The exact local obstruction** (`DeningerArithmeticLocalHodgeObstruction`):

```text
[Θ, star_ρ] = (1 − λ_ρ − conj λ_ρ) · star_ρ ,        λ_ρ = 1/2 + i·ρ
```

Evaluating the scalar: `1 − λ − conj λ = i(conj ρ − ρ) = 2·Im ρ`.

**So the obstruction is `2·Im ρ` — an ordered real scalar, vanishing exactly when the centred Xi
point is real.**  In centred coordinates `s ↦ 1 − conj s` becomes `ρ ↦ conj ρ`, so this is the
re-encoding template of §§1–8 once more, in Hodge-theoretic clothing.  The obstruction class is
one-dimensional and its vanishing is `Im ρ = 0`.

**Verdict on the local layer: re-encoding.**  The module says so itself — "positivity itself is easy
locally; arithmetic purity is precisely the vanishing of this explicit commutator... The result
isolates the missing global Hodge theorem."  The content is global, and the recorded state of that
global layer is that it rests on a single anonymous detection hypothesis.

**The constraint of §32 survives the test and is not yet satisfied by anything in the tree.**  Five
conjectures have now been tested against this corpus and all five died the same way: the reframing
preserved an ordered invariant.  What is wanted is an invariant with no order at all — the local
Deninger obstruction has one only because it collapses to a scalar.

## Gates

- [x] the unordered-invariant constraint tested against the Deninger lane
- [x] the local Hodge obstruction computed: `2·Im ρ`, ordered, hence template
- [ ] an invariant genuinely valued in an unordered group, not collapsing to a scalar

## 34. The criterion selects one mechanism, and it explains the whole pattern

The criterion derived in §32–§33 — *the invariant must not collapse to an ordered scalar* — selects
exactly one thing in this tree, and it was found by applying the criterion rather than by browsing.

`CCMRationalQuaternionicMoritaFiber`, on the CCM Morita fiber indexed by `ℚˣ`, with
`(J f)(q) = sign(q)·conj(f(−q))`, proves unconditionally that `J` is conjugate-linear, `J² = −1`,
that rational left scaling by `k` has covariance sign `sign(k)`, and then the decisive sentence:

> **"ordinary complex trace forgets the quaternionic sign, while the Real fixed algebra retains
> quaternionic Brauer type."**

`KRealMoritaParityShift` supplies the companion: the descended reflection `(τF)(e) = σ_M(F(−σ_E e))`
with `τ² = −1`, "the algebraic degree-four Real-Brauer parity mechanism needed by the rational CCM
construction."

**This explains the session's pattern structurally rather than anecdotally.**  Every invariant that
failed — Weil form size, Fredholm index, dBN zero count, Hankel/Hausdorff moments, the Deninger local
class collapsing to `2·Im ρ` — is computed by a **complex trace**.  And the complex trace is
*proved here* to forget the quaternionic sign.  So all five failures share one cause: they factor
through a functional that is blind to the only unordered invariant in the construction.

**Positive statement.**  The Brauer type is `ℤ/2`-valued (real versus quaternionic) and carries no
order, so the one-sided-bound asymmetry that ceilings every other lane cannot apply to it.  If RH is
decidable by any unconditional method in this framework, the deciding invariant must be visible to
the Real fixed algebra and invisible to the complex trace.

That is a criterion with a witness, not a name: it says what to compute (Brauer type of the Real
fixed algebra) and why nothing computed so far could have seen it.

## Gates

- [x] the unordered-invariant criterion applied; it selects the Real-Brauer parity mechanism
- [x] the session's five failures explained by one cause: all factor through the complex trace
- [ ] compute the Brauer type of the Real fixed algebra on the actual Xi/prime-arch fiber

## 35. The two halves exist and are unconnected — the actionable gap

`DeningerClosedGeneratorHodgeWeilPurityUniversalityLaw` proves that local Hodge invariance, universal
finite-packet invariance, full Weil positivity, and RH are all equivalent, via:

> "Every local Hodge form commutes with Frobenius exactly when its centered support point is real."

That is the collapsed scalar `2·Im ρ` of §33 — the template again.  **So the tree's purity law routes
entirely through the trace-visible, ordered invariant**, and the quaternionic Brauer type of §34 plays
no part in it.

So the tree contains:

```text
half A   an unordered invariant no trace can see
         CCMRationalQuaternionicMoritaFiber : J² = −1, complex trace forgets the quaternionic sign,
         Real fixed algebra retains quaternionic Brauer type
         KRealMoritaParityShift : τ² = −1, degree-four Real-Brauer parity

half B   purity laws, all routed through the collapsed scalar 2·Im ρ
         DeningerClosedGeneratorHodgeWeilPurityUniversalityLaw, DeningerArithmeticLocalHodgeObstruction
```

**and no declaration joins them.**

**The gap, stated exactly.**  Derive purity from the *quaternionic type* rather than from the scalar
commutator — i.e. the analogue of Deligne's mechanism, where a symplectic (quaternionic) pairing plus
positivity forces eigenvalues onto the critical circle, with no scalar reality hypothesis anywhere.
In this tree that means: show the Real fixed algebra's Brauer class forces the Hodge form to commute
with Frobenius, without passing through `Im ρ`.

This is the only route consistent with the criterion derived from five failed conjectures, because it
is the only one whose invariant is not ordered.  It is also the only place where the tree's two
independently-built halves have never been put together.

## Gates

- [x] the purity law shown to route through the collapsed scalar, not the Brauer type
- [x] the two halves located and confirmed unconnected
- [ ] derive purity from the quaternionic Brauer class — the Deligne mechanism, absent here

## 36. The join, stated as a mechanism

Working out what "derive purity from the quaternionic type" would actually mean.

**Kramers.**  Let `J` be conjugate-linear with `J² = −1` and `JA = AJ`.  If `Av = λv` then
`A(Jv) = J(Av) = conj λ · Jv`, and `J² = −1` makes `v, Jv` independent.  So **eigenvalues occur in
conjugate pairs with even multiplicity** — this is Kramers degeneracy, and it is exactly what an
antilinear `J` with `J² = −1` buys.

**The Xi quadruple.**  With the functional equation supplying `λ ↔ 1 − λ` alongside `λ ↔ conj λ`, a
generic point carries the quadruple

```text
{ λ , conj λ , 1 − λ , 1 − conj λ } .
```

RH is exactly the statement that this collapses to a **pair**, i.e. `λ = 1 − conj λ`.

**Where the unordered invariant enters.**  For a `J`-real irreducible the commutant is `ℝ`, `ℂ`, or
`ℍ` according to Brauer type, and `J² = −1` gives `ℍ`.  The collapse of the quadruple to a pair is
precisely the module being **quaternionic** rather than complex.  So:

> **Target.**  RH ⟺ the Xi Frobenius module has quaternionic Brauer type.

This is `ℤ/2`-valued, carries no order, and therefore escapes the one-sided-bound asymmetry that
ceilings every other lane.  It is not a count: the multiplicity *pattern* is a consequence of the
type, not the definition of it.

**The concrete construction.**  `CCMRationalQuaternionicMoritaFiber` proves `J² = −1` *unconditionally*
on the CCM rational Morita fiber, and `KRealMoritaParityShift` descends that structure through Morita
intertwiners with `τ² = −1`.  What is missing is the transfer: carry the `J² = −1` structure from the
CCM fiber to the Xi/Frobenius module.  If it transfers, the type is quaternionic there too, the
quadruple collapses, and RH follows.

**How it could fail.**  The transfer may not exist — the Morita fiber is indexed by `ℚˣ` and the Xi
module by the divisor, and the reflection `q ↦ −q` need not correspond to `λ ↦ 1 − conj λ`.  That
correspondence is the whole content, and it is exactly the `s ↦ 1 − conj s` involution the ~96
re-encodings all express — but here it would be *used to build a module structure* rather than
restated as a scalar condition.

## Gates

- [x] the mechanism worked out: Kramers ⟹ conjugate pairs; quadruple collapse ⟺ quaternionic type
- [x] target stated: RH ⟺ the Xi Frobenius module is quaternionic
- [ ] transfer `J² = −1` from the CCM rational Morita fiber to the Xi Frobenius module

## 37. The transfer, checked — two different `ℤ/2`s

**The naive transfer fails, and the reason is structural.**

`ℚˣ ≅ {±1} × ℚ_{>0}`.  The CCM reflection `q ↦ −q` acts **only on the `{±1}` factor** — it is the sign
character.  Mellin transform turns the `ℚ_{>0}` factor into the `s`-variable, and the sign flip does
not touch it.  The Xi involution `s ↦ 1 − conj s` acts **only on `s`**.

So the tree carries two distinct `ℤ/2` actions:

```text
ℤ/2 (a)   sign character on ℚˣ                 carries the quaternionic J, J² = −1   (proved)
ℤ/2 (b)   FE–Schwarz involution s ↦ 1−conj s   carries RH                            (the ~96 re-encodings)
```

`J² = −1` lives on (a); purity is a statement about (b).  **The transfer is exactly the claim that
these two `ℤ/2`s are linked**, and nothing in the tree links them.

**What would link them, and why it is the right expectation.**  Over function fields the analogue is
Poincaré duality: the alternating pairing on *odd-weight* middle cohomology *is* the functional
equation, so there the sign and the duality involution coincide, and odd weight ⟹ symplectic ⟹
quaternionic ⟹ Kramers ⟹ purity.  For `ζ` the relevant weight is one — `DeningerArithmeticLocalHodgeObstruction`
calls its scalar the "**weight-one** purity defect" — so the expected structure is exactly
alternating.

**The obstruction, finally named.**  Linking (a) to (b) requires an alternating pairing *defined on
the Xi module*, i.e. the middle cohomology with its duality.  That object is what Deninger's programme
is for and does not have.  So the chain

```text
five refuted conjectures ⟹ invariant must be unordered ⟹ Brauer type ⟹ quaternionic ⟹ Kramers
⟹ quadruple collapses ⟹ RH ,   blocked at: no alternating pairing on the Xi module
```

terminates at the missing middle cohomology — reached here by derivation from the tree's own
refutations rather than by citation.

## Gates

- [x] the transfer checked and shown to fail naively: sign `ℤ/2` ≠ FE–Schwarz `ℤ/2`
- [x] the expected link identified as odd-weight Poincaré duality; weight one confirmed in the tree
- [ ] an alternating pairing on the Xi module — the missing middle cohomology

## 38. Correction to §36: the pairing and the Real structure are different objects

Working the mechanism out rather than asserting it:

```text
pairing (bilinear)        λ ↔ 1 − λ ,  i.e.  ρ ↔ −ρ      — the functional equation
Real structure (antilin.) ρ ↔ conj ρ                     — Schwarz reflection
composite                 λ ↔ 1 − conj λ                 — the FE–Schwarz involution
```

`Ξ` is even, so `ρ` and `−ρ` are both zeros and the *pairing* is satisfied unconditionally — it says
nothing about RH.  RH is `ρ = conj ρ`, a statement about the **Real structure**, not the pairing.

So §36's target was mis-stated.  Brauer type is a joint invariant of pairing *and* Real structure
(symmetric + `J²=+1` = real; alternating + `J²=−1` = quaternionic), but

> **RH is the triviality of the Real structure's action on the spectrum — every `ρ` fixed — not the
> Brauer type of the module.**

A module can be quaternionic with a spectrum that moves under `J`; quaternionic type gives Kramers
pairing `λ ↔ conj λ`, which is automatic for `Ξ` (real coefficients) and again says nothing about RH.

**Consequence.**  The unordered invariant does exist (§34, proved: `J² = −1`, complex trace forgets
it), but it is not the invariant RH is.  RH is a **fixed-point** statement about an involution acting
on a spectrum, and the number of non-fixed points is `N_off` — a **count**, which is ceiling N′ again.

So the chain of §§32–37 closes on itself: the search for an unordered invariant led to a genuine one,
and that one is not RH.  RH is `N_off = 0`, and every route to it that this tree contains bounds
`N_off` from below.

**This is the fifth and sharpest confirmation of the session's law**: *RH is the vanishing of a count,
and every unconditional engine in this framework bounds counts from below.*  The Brauer detour did not
escape it — it relocated it.

## Gates

- [x] §36 corrected: pairing ≠ Real structure; RH is a fixed-point statement, hence a count
- [x] the unordered-invariant search closed: the invariant found is real, but is not RH
- [ ] an unconditional method that bounds a count from **above** — the single structural need

## 39. The engine of the required type exists — and it is the lane I abandoned

§38's law: *RH is the vanishing of a count, and every unconditional engine here bounds counts from
below.*  The stated need: **an unconditional method that bounds a count from above.**

Such methods exist, and there are exactly two families:

```text
zero-density estimates   N(σ,T) ≪ T^{c(σ)}      upper bound on a count; c > 0, never 0
zero-free regions        N(σ,T) = 0             upper bound of ZERO on a count, unconditionally,
                                                but only for σ > 1 − c/(log T)^{2/3}  (Vinogradov–Korobov)
```

**RH is exactly the statement that the zero-free region extends to `σ > 1/2`.**

**Correction to my own dismissal.**  In §§9–19 I built the Carlson density chain and then abandoned it
as "1920 mathematics, not load-bearing".  That was right about *novelty* and wrong about *type*:
Carlson's `N(σ,T) = o(T)` is an instance of the **only engine type this analysis says can work**.  The
novelty gate and the structural gate point in opposite directions here, and I let the first override
the second without noticing they disagreed.

**Where that engine's own ceiling sits** — already in the tree, `ZeroDensityMomentCrossing`:

```text
powerBranch − densityTarget = (2−2σ)(2σ−1) > 0 on (1/2,1),  independent of k
```

the integer-moment method misses the Density Hypothesis by a `k`-independent constant.  Guth–Maynard
(2024) went *around* it with a new large-value estimate rather than through it, obtaining the first
gain at `σ = 3/4` since Ingham 1940.

**So the complete arc closes consistently:**

```text
RH = vanishing of a count
⟹ need an unconditional upper bound on a count
⟹ the only such engines are zero-density and zero-free regions
⟹ their ceiling in the moment method is (2−2σ)(2σ−1), k-independent
⟹ the live frontier is a large-value estimate outside the min(power, meanValue) family
```

which is exactly where §7 of this audit landed before the pivot.  The infrastructure built in
§§9–19 — branch-free Littlewood, Jensen, layer cake, well-spacing, large values for separated
families — is machinery **for that engine**, and is therefore the correctly-typed part of this
session's output, whatever its novelty.

## Gates

- [x] the required engine type identified and located: zero-density / zero-free regions
- [x] my dismissal of the Carlson lane corrected — right on novelty, wrong on type
- [ ] a large-value estimate outside `min(power, meanValue)` — the frontier, restated and confirmed

## 40. A concrete loss in the correctly-typed machinery

Optimizing the free parameter in `large_values_dpoly` / `large_values_separated`:

```text
R·V² ≤ (δ⁻¹ + η⁻¹)∫‖D‖² + η∫‖D′‖²        minimize over η > 0
     ≤ δ⁻¹∫‖D‖² + 2√( ∫‖D‖² · ∫‖D′‖² ) .
```

`D′ = dpoly(a·log)`, so `∑|a_n log n|² ≤ (log N)²∑|a_n|²` and the cross term contributes a factor
`log N`.  With Montgomery–Vaughan on both integrals (`secondMoment_upper_bound`, already in the tree):

```text
R·V² ≪ U·(δ⁻¹ + 2 log N)·∑|a_n|² .
```

**The `log N` is an artifact of the Sobolev/Gallagher route**, which pays for pointwise control by
differentiating.  The sharp mean-value theorem carries no such factor — `secondMoment_upper_bound` is
stated as "the exact diagonal main term plus the explicit off-diagonal", i.e. log-free.

So the tree's large-values input is **one logarithm off the sharp mean-value bound**, and that loss
enters every density exponent derived from it.  Removing it is a concrete, self-contained improvement
to the one engine type §39 identifies as correct, and it does not require any new idea — only routing
the estimate through the sharp second moment instead of through the derivative.

This is the first genuinely actionable item in the correctly-typed lane that is not classical
formalization: the corpus's own `secondMoment_upper_bound` is sharper than what `large_values_dpoly`
consumes.

## Gates

- [x] the `log N` loss in the Gallagher route located and attributed
- [ ] re-derive the large-values bound from `secondMoment_upper_bound` directly, log-free
- [ ] propagate the gain into the density exponent and compare against `(2−2σ)(2σ−1)`

## 41. The log-free route, every input located

**Correction first.**  I said the exponential-sum input was "Euler–Maclaurin and nothing more".  It is
not: the Euler–Maclaurin error for `f(x) = x^{−iu}` is `∫|f′| = |u| log N`, larger than the main term
`(N+1)/|u|`.  The bound `|∑_{n≤N} n^{−iu}| ≪ N/|u| + 1` needs oscillation, i.e. van der Corput.

**And the corpus already has the right form of it.**  `VanDerCorputSecond` proves
`norm_integral_cexp_secondDeriv : |∫ e^{ig}| ≤ 6/√λ` when `g″ ≥ λ`, and its own docstring names the
application: *"its Fourier phases `τ·log x ± 2πm·x` have a genuine saddle at `x = τ/(2πm)`"* — which
is exactly the phase appearing when one expands the sawtooth `{x}` in Fourier series inside the
Euler–Maclaurin remainder

```text
∑_{n≤N} n^{−iu} = ∫_1^N x^{−iu} dx + (boundary) − ∫_1^N {x}·(iu)x^{−iu−1} dx ,
{x} = 1/2 − ∑_k sin(2πkx)/(πk) ,
```

turning the remainder into integrals with phase `−u log x + 2πkx`.

**So every input of the log-free large-values bound is present:**

```text
duality step              sampled_energy_le_of_dual_bound          (built, §this session)
sampling off-diagonal     sampling_offDiagonal_le, log R not log N (built, §this session)
exponential sum N/|u|     Euler–Maclaurin + Fourier {x} + norm_integral_cexp_secondDeriv (in tree)
diagonal / mean value     secondMoment_upper_bound                 (in tree, Montgomery–Vaughan)
```

giving, on assembly,

```text
R·V² ≤ ( N + O(N log R / δ) ) · ∑|a_n|²        against Gallagher's  U·(δ⁻¹ + 2 log N)·∑|a_n|²
```

— better whenever `N ≪ U`, the regime every density argument runs in.

**Not claimed:** that the assembly is done.  What is established is that no input is missing: each of
the four steps is either a theorem already in this tree or one proved here, and the only work left is
composition.

## Gates

- [x] the exponential-sum step correctly attributed to van der Corput, not Euler–Maclaurin
- [x] all four inputs of the log-free bound located; none missing
- [ ] the composition itself, and the resulting density exponent against `(2−2σ)(2σ−1)`

## 42. The log-free large-values bound, assembled

`HTGeometry/LargeValuesDuality.lean` and `HTGeometry/SeparatedOffDiagonalBound.lean`, both
axiom-clean, both built, `GaloisForLFunctions.HTGeometry` green.

```lean
sampled_energy_le_of_correlation_bounds :
  b r = ∑ n, a n * M r n →
  ‖∑ n, M r n * conj (M r n)‖ ≤ D →
  (r ≠ s → ‖∑ n, M r n * conj (M s n)‖ ≤ M₀ * sepKernel t r s) →
  (∀ r, ∑ s, sepKernel t r s ≤ H) →
  ∑ r, ‖b r‖² ≤ (D + M₀ * H) * ∑ n, ‖a n‖²
```

built from four lemmas proved here:

```text
dual_sum_expand                  dual energy = sampling Gram form
gram_entry_le                    each entry ≤ ‖c_r‖‖c_s‖ · correlation bound
sampling_offDiagonal_le          off-diagonal ≤ H · energy, by AM–GM and symmetry alone
sampled_energy_le_of_dual_bound  Cauchy–Schwarz, then cancel the sampled energy
```

**No derivative of the polynomial appears**, so no `log N` is paid.  The only logarithm is inside `H`;
for a `δ`-separated sampling set `H = O(log R / δ)` by harmonic bookkeeping, against Gallagher's
`log N`.  In the density regime `R ≪ N ≪ U` that is a genuine gain.

**What is a hypothesis and what is research.**  `H` is a hypothesis of the theorem, and instantiating
it for a concrete separated set is standard bookkeeping — the theorem is complete without it.  The one
remaining *analytic* input is the correlation bound

```text
‖ ∑_{n ≤ N} n^{−i(t_r − t_s)} ‖ ≪ N / |t_r − t_s| + 1 ,
```

which needs van der Corput, not Euler–Maclaurin (§41), and for which `VanDerCorputSecond` supplies the
saddle-point tool its own docstring says was built for these phases.

## Gates

- [x] the duality route assembled into one theorem, derivative-free, axiom-clean
- [x] `log R` in place of `log N`, from AM–GM and symmetry only
- [ ] the van der Corput correlation bound, wired to `norm_integral_cexp_secondDeriv`
- [ ] the resulting density exponent against `(2−2σ)(2σ−1)`
