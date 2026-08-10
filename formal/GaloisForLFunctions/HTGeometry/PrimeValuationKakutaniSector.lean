import GaloisForLFunctions.HTGeometry.PrimeValuationInfiniteSupport
import GaloisForLFunctions.HTGeometry.DivergentSeriesThinning

/-!
# Kakutani purity of the coherent radial twists of the prime-valuation sector

The critical prime-valuation sector is the Kolmogorov product of the geometric laws
`μ_p(k) = (1 - p⁻¹) p^{-k}`.  A coherent radial power twist `p^{ck}` renormalizes each local law to

```text
μ_{p,c}(k) = (1 - p^{-(1-2c)}) p^{-(1-2c)k},
```

which is a probability law for every `c < 1/2`.  The twisted product measure is equivalent to the
critical one exactly when `c = 0`; for every other `c` the two are mutually singular.

The separating events are occupancy events, read at a single scale.  For `c < 0` the twisted
occupancy masses `p^{-(1-2c)}` are summable while the critical masses `p⁻¹` are not, so the two
Borel--Cantelli lemmas already split the sector.  For `0 < c < 1/2` both mass families diverge, and
the separation comes from thinning: a set of primes whose reciprocals converge while their
`(1-2c)`-th powers still diverge, which exists for any divergent series of vanishing positive
terms.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The twisted local laws -/

/-- The radial exponent of the twist: the local ratio is `p^{-(1-2c)}`. -/
def twistExponent (c : ℝ) : ℝ := 1 - 2 * c

theorem twistExponent_pos {c : ℝ} (hc : c < 1 / 2) : 0 < twistExponent c := by
  rw [twistExponent]
  linarith

theorem twistExponent_zero : twistExponent 0 = 1 := by
  rw [twistExponent]
  ring

/-- The local ratio of the twisted valuation law at `p`. -/
def primeTwistRatio (c : ℝ) (p : Nat.Primes) : ℝ := ((p : ℕ) : ℝ) ^ (-twistExponent c)

theorem primeTwistRatio_pos (c : ℝ) (p : Nat.Primes) : 0 < primeTwistRatio c p :=
  Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _

theorem primeTwistRatio_lt_one {c : ℝ} (hc : c < 1 / 2) (p : Nat.Primes) :
    primeTwistRatio c p < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt)
    (by simpa using neg_neg_iff_pos.mpr (twistExponent_pos hc))

theorem primeTwistRatio_zero (p : Nat.Primes) :
    primeTwistRatio 0 p = (((p : ℕ) : ℝ))⁻¹ := by
  rw [primeTwistRatio, twistExponent_zero, Real.rpow_neg_one]

/-- Success parameter of the twisted local law. -/
def primeTwistedParam {c : ℝ} (hc : c < 1 / 2) (p : Nat.Primes) : unitInterval := by
  refine ⟨1 - primeTwistRatio c p, ?_, ?_⟩
  · have := primeTwistRatio_lt_one hc p
    linarith
  · have := primeTwistRatio_pos c p
    linarith

@[simp] theorem primeTwistedParam_coe {c : ℝ} (hc : c < 1 / 2) (p : Nat.Primes) :
    ((primeTwistedParam hc p : unitInterval) : ℝ) = 1 - primeTwistRatio c p := rfl

theorem primeTwistedParam_ne_zero {c : ℝ} (hc : c < 1 / 2) (p : Nat.Primes) :
    primeTwistedParam hc p ≠ 0 := by
  intro h
  have hcoe : ((primeTwistedParam hc p : unitInterval) : ℝ) = 0 := by rw [h]; rfl
  rw [primeTwistedParam_coe] at hcoe
  have := primeTwistRatio_lt_one hc p
  linarith

/-- The twisted local law at `p`: geometric with ratio `p^{-(1-2c)}`. -/
def primeTwistedLaw {c : ℝ} (hc : c < 1 / 2) (p : Nat.Primes) : Measure ℕ :=
  geometricMeasure (primeTwistedParam hc p)

instance instIsProbabilityMeasurePrimeTwistedLaw {c : ℝ} (hc : c < 1 / 2) (p : Nat.Primes) :
    IsProbabilityMeasure (primeTwistedLaw hc p) :=
  isProbabilityMeasure_geometricMeasure

theorem primeTwistedLaw_zero {c : ℝ} (hc : c < 1 / 2) (p : Nat.Primes) :
    primeTwistedLaw hc p {0} = ENNReal.ofReal (1 - primeTwistRatio c p) := by
  rw [primeTwistedLaw, geometricMeasure_singleton (primeTwistedParam_ne_zero hc p) 0]
  simp

/-- The local occupancy mass of the twisted law is exactly its ratio. -/
theorem primeTwistedLaw_compl_zero {c : ℝ} (hc : c < 1 / 2) (p : Nat.Primes) :
    primeTwistedLaw hc p {0}ᶜ = ENNReal.ofReal (primeTwistRatio c p) := by
  have hnn : (0 : ℝ) ≤ 1 - primeTwistRatio c p := by
    have := primeTwistRatio_lt_one hc p
    linarith
  rw [prob_compl_eq_one_sub (measurableSet_singleton 0), primeTwistedLaw_zero,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hnn]
  congr 1
  ring

/-- The twisted prime-valuation sector. -/
def primeTwistedMeasure {c : ℝ} (hc : c < 1 / 2) : Measure (∀ _ : Nat.Primes, ℕ) :=
  Measure.infinitePi (primeTwistedLaw hc)

instance {c : ℝ} (hc : c < 1 / 2) : IsProbabilityMeasure (primeTwistedMeasure hc) := by
  rw [primeTwistedMeasure]
  infer_instance

/-- **At `c = 0` the twist is trivial**: the twisted sector is the critical sector. -/
theorem primeTwistedMeasure_zero (hc : (0 : ℝ) < 1 / 2) :
    primeTwistedMeasure hc = primeValuationMeasure := by
  have hlaw : primeTwistedLaw hc = primeValuationLaw := by
    funext p
    rw [primeTwistedLaw, primeValuationLaw]
    congr 1
    apply Subtype.ext
    rw [primeTwistedParam_coe, primeValuationParam_coe, primeTwistRatio_zero]
  rw [primeTwistedMeasure, primeValuationMeasure, hlaw]

/-! ## The negative twists: summable occupancy -/

theorem summable_primeTwistRatio_of_neg {c : ℝ} (hc : c < 0) :
    Summable (primeTwistRatio c) := by
  have hexp : -twistExponent c < -1 := by
    rw [twistExponent]
    linarith
  exact Nat.Primes.summable_rpow.mpr hexp

theorem tsum_primeTwistedLaw_compl_zero_ne_top {c : ℝ} (hc0 : c < 0) (hc : c < 1 / 2) :
    (∑' p : Nat.Primes, primeTwistedLaw hc p {0}ᶜ) ≠ ∞ := by
  rw [tsum_congr fun p => primeTwistedLaw_compl_zero hc p]
  exact (tsum_ofReal_ne_top_iff_summable _ fun p => (primeTwistRatio_pos c p).le).mpr
    (summable_primeTwistRatio_of_neg hc0)

/-- **Negative radial twists leave the critical sector.** -/
theorem mutuallySingular_primeTwistedMeasure_of_neg {c : ℝ} (hc0 : c < 0) (hc : c < 1 / 2) :
    (primeTwistedMeasure hc).MutuallySingular primeValuationMeasure := by
  classical
  set e : ℕ ≃ Nat.Primes := Classical.choice (inferInstance : Nonempty (ℕ ≃ Nat.Primes)) with he
  refine ⟨{k : ∀ _ : Nat.Primes, ℕ | (occupiedSet k).Infinite},
    measurableSet_infiniteOccupancy e, ?_, ?_⟩
  · rw [primeTwistedMeasure]
    exact measure_infiniteOccupancy_eq_zero (primeTwistedLaw hc) e
      (tsum_primeTwistedLaw_compl_zero_ne_top hc0 hc)
  · rw [← finiteOccupancy_eq_compl]
    exact primeValuationMeasure_finiteSupport

/-! ## The positive twists: thinned occupancy -/

/-- The thinned prime set separating a positive twist from the critical sector: its reciprocals
converge while its `(1-2c)`-th powers diverge. -/
theorem exists_thin_primeSet {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2) :
    ∃ S : Set Nat.Primes,
      Summable (fun p : S => (((p : Nat.Primes) : ℕ) : ℝ)⁻¹) ∧
        ¬ Summable (fun p : S => primeTwistRatio c (p : Nat.Primes)) := by
  classical
  set e : ℕ ≃ Nat.Primes := Classical.choice (inferInstance : Nonempty (ℕ ≃ Nat.Primes)) with he
  set y : ℕ → ℝ := fun n => (((e n : Nat.Primes) : ℕ) : ℝ)⁻¹ with hy
  have hposn : ∀ n : ℕ, (0 : ℝ) < (((e n : Nat.Primes) : ℕ) : ℝ) := by
    intro n
    exact_mod_cast (e n).prop.pos
  have hy0 : ∀ n, 0 < y n := fun n => inv_pos.mpr (hposn n)
  have hdiv : ¬ Summable y := by
    intro hsum
    apply Nat.Primes.not_summable_one_div
    refine (e.summable_iff (f := fun p : Nat.Primes => 1 / (((p : ℕ) : ℝ)))).mp ?_
    refine hsum.congr fun n => ?_
    simp [hy, one_div]
  have hlim : Tendsto y atTop (𝓝 0) := by
    have hinj : Function.Injective (fun n : ℕ => ((e n : Nat.Primes) : ℕ)) := by
      intro m n hmn
      exact e.injective (Subtype.ext hmn)
    have hcof : Tendsto (fun n : ℕ => ((e n : Nat.Primes) : ℕ)) atTop atTop := by
      have := hinj.tendsto_cofinite
      rwa [Nat.cofinite_eq_atTop] at this
    have hcast : Tendsto (fun n : ℕ => (((e n : Nat.Primes) : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hcof
    exact hcast.inv_tendsto_atTop.congr fun n => rfl
  obtain ⟨T, hTsum, hTdiv⟩ :=
    exists_thin_subset hy0 hdiv hlim (twistExponent_pos hc)
      (by rw [twistExponent]; linarith : twistExponent c < 1)
  have hratio : ∀ n : ℕ, primeTwistRatio c (e n) = y n ^ twistExponent c := by
    intro n
    rw [primeTwistRatio, hy, Real.inv_rpow (hposn n).le, ← Real.rpow_neg (hposn n).le]
  have hmemimage : ∀ n : ℕ, (e n ∈ e '' T ↔ n ∈ T) := by
    intro n
    constructor
    · rintro ⟨m, hm, hme⟩
      rwa [e.injective hme] at hm
    · intro hn
      exact ⟨n, hn, rfl⟩
  refine ⟨e '' T, ?_, ?_⟩
  · refine (summable_subtype_iff_indicator (f := fun p : Nat.Primes => (((p : ℕ) : ℝ))⁻¹)
      (s := e '' T)).mpr ?_
    rw [← e.summable_iff]
    have hfun : ((Set.indicator (e '' T) fun p : Nat.Primes => (((p : ℕ) : ℝ))⁻¹) ∘ e)
        = Set.indicator T y := by
      funext n
      by_cases hn : n ∈ T
      · rw [Function.comp_apply, Set.indicator_of_mem ((hmemimage n).mpr hn),
          Set.indicator_of_mem hn]
      · rw [Function.comp_apply,
          Set.indicator_of_notMem (fun hmem => hn ((hmemimage n).mp hmem)),
          Set.indicator_of_notMem hn]
    rw [hfun, ← summable_subtype_iff_indicator]
    exact hTsum
  · intro hcon
    apply hTdiv
    replace hcon := (summable_subtype_iff_indicator
      (f := fun p : Nat.Primes => primeTwistRatio c p) (s := e '' T)).mp hcon
    rw [← e.summable_iff] at hcon
    have hfun : ((Set.indicator (e '' T) fun p : Nat.Primes => primeTwistRatio c p) ∘ e)
        = Set.indicator T fun n => y n ^ twistExponent c := by
      funext n
      by_cases hn : n ∈ T
      · rw [Function.comp_apply, Set.indicator_of_mem ((hmemimage n).mpr hn),
          Set.indicator_of_mem hn, hratio]
      · rw [Function.comp_apply,
          Set.indicator_of_notMem (fun hmem => hn ((hmemimage n).mp hmem)),
          Set.indicator_of_notMem hn]
    rw [hfun] at hcon
    exact (summable_subtype_iff_indicator
      (f := fun n : ℕ => y n ^ twistExponent c) (s := T)).mpr hcon

open Classical in
/-- The thinned occupancy targets. -/
def thinTarget (S : Set Nat.Primes) (p : Nat.Primes) : Set ℕ := if p ∈ S then {0}ᶜ else ∅

theorem primeTwistedLaw_thinTarget {c : ℝ} (hc : c < 1 / 2) (S : Set Nat.Primes)
    (p : Nat.Primes) :
    primeTwistedLaw hc p (thinTarget S p) =
      ENNReal.ofReal (Set.indicator S (primeTwistRatio c) p) := by
  classical
  rw [thinTarget]
  by_cases hp : p ∈ S
  · rw [if_pos hp, Set.indicator_of_mem hp, primeTwistedLaw_compl_zero]
  · rw [if_neg hp, Set.indicator_of_notMem hp, measure_empty, ENNReal.ofReal_zero]

theorem primeValuationLaw_thinTarget (S : Set Nat.Primes) (p : Nat.Primes) :
    primeValuationLaw p (thinTarget S p) =
      ENNReal.ofReal (Set.indicator S (fun q : Nat.Primes => (((q : ℕ) : ℝ))⁻¹) p) := by
  classical
  rw [thinTarget]
  by_cases hp : p ∈ S
  · rw [if_pos hp, Set.indicator_of_mem hp, primeValuationLaw_compl_zero]
  · rw [if_neg hp, Set.indicator_of_notMem hp, measure_empty, ENNReal.ofReal_zero]

/-- **Positive radial twists leave the critical sector.**  Both occupancy families diverge, so the
separating event is read on a thinned set of primes. -/
theorem mutuallySingular_primeTwistedMeasure_of_pos {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2) :
    (primeTwistedMeasure hc).MutuallySingular primeValuationMeasure := by
  classical
  obtain ⟨S, hSsum, hSdiv⟩ := exists_thin_primeSet hc0 hc
  set e : ℕ ≃ Nat.Primes := Classical.choice (inferInstance : Nonempty (ℕ ≃ Nat.Primes)) with he
  have hnnc : ∀ p : Nat.Primes, 0 ≤ Set.indicator S (primeTwistRatio c) p := fun p =>
    Set.indicator_nonneg (fun q _ => (primeTwistRatio_pos c q).le) p
  have hnn0 : ∀ p : Nat.Primes,
      0 ≤ Set.indicator S (fun q : Nat.Primes => (((q : ℕ) : ℝ))⁻¹) p := fun p =>
    Set.indicator_nonneg (fun q _ => by positivity) p
  have hdivc : (∑' p : Nat.Primes, primeTwistedLaw hc p (thinTarget S p)) = ∞ := by
    rw [tsum_congr fun p => primeTwistedLaw_thinTarget hc S p]
    by_contra hne
    exact hSdiv ((summable_subtype_iff_indicator
        (f := fun p : Nat.Primes => primeTwistRatio c p) (s := S)).mpr
      ((tsum_ofReal_ne_top_iff_summable _ hnnc).mp hne))
  have hconv0 : (∑' p : Nat.Primes, primeValuationLaw p (thinTarget S p)) ≠ ∞ := by
    rw [tsum_congr fun p => primeValuationLaw_thinTarget S p]
    refine (tsum_ofReal_ne_top_iff_summable _ hnn0).mpr ?_
    exact (summable_subtype_iff_indicator
      (f := fun q : Nat.Primes => (((q : ℕ) : ℝ))⁻¹) (s := S)).mp hSsum
  refine ⟨{k : ∀ _ : Nat.Primes, ℕ | (localHitSet (thinTarget S) k).Finite},
    measurableSet_finiteHit (thinTarget S) e, ?_, ?_⟩
  · rw [primeTwistedMeasure, finiteHit_eq_compl,
      MeasureTheory.prob_compl_eq_zero_iff (measurableSet_infiniteHit (thinTarget S) e)]
    exact measure_infiniteHit_eq_one (primeTwistedLaw hc) (thinTarget S) e hdivc
  · rw [finiteHit_eq_compl, compl_compl, primeValuationMeasure]
    exact measure_infiniteHit_eq_zero primeValuationLaw (thinTarget S) e hconv0

/-- **Every nonzero coherent radial twist is singular to the critical sector.** -/
theorem mutuallySingular_primeTwistedMeasure {c : ℝ} (hc : c < 1 / 2) (hne : c ≠ 0) :
    (primeTwistedMeasure hc).MutuallySingular primeValuationMeasure := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact mutuallySingular_primeTwistedMeasure_of_neg h hc
  · exact mutuallySingular_primeTwistedMeasure_of_pos h hc

/-- **Kakutani radial-sector purity.**  A coherent radial power twist stays in the measure class of
the critical prime-valuation sector exactly on the critical ray `c = 0`. -/
theorem primeTwistedMeasure_absolutelyContinuous_iff {c : ℝ} (hc : c < 1 / 2) :
    (primeTwistedMeasure hc).AbsolutelyContinuous primeValuationMeasure ↔ c = 0 := by
  constructor
  · intro habs
    by_contra hne
    have hzero := Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular habs
      (mutuallySingular_primeTwistedMeasure hc hne)
    have huniv : (primeTwistedMeasure hc) Set.univ = 1 := measure_univ
    rw [hzero] at huniv
    simp at huniv
  · rintro rfl
    rw [primeTwistedMeasure_zero]

/-- The two-sided form: the twisted sector and the critical sector are equivalent measures exactly
on the critical ray. -/
theorem primeTwistedMeasure_equivalent_iff {c : ℝ} (hc : c < 1 / 2) :
    ((primeTwistedMeasure hc).AbsolutelyContinuous primeValuationMeasure ∧
        primeValuationMeasure.AbsolutelyContinuous (primeTwistedMeasure hc)) ↔ c = 0 := by
  constructor
  · rintro ⟨habs, -⟩
    exact (primeTwistedMeasure_absolutelyContinuous_iff hc).mp habs
  · rintro rfl
    rw [primeTwistedMeasure_zero]
    exact ⟨Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl⟩

/-! ## The Hellinger affinity of two geometric laws -/

private theorem sqrt_pow_of_nonneg {x : ℝ} (h : 0 ≤ x) (k : ℕ) :
    Real.sqrt (x ^ k) = Real.sqrt x ^ k := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 2)) k,
    ← Real.rpow_natCast x k, ← Real.rpow_mul h, ← Real.rpow_mul h]
  ring_nf

private theorem sqrt_lt_one_of_lt_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.sqrt x < 1 := by
  calc Real.sqrt x < Real.sqrt 1 := Real.sqrt_lt_sqrt hx0 hx1
    _ = 1 := Real.sqrt_one

private theorem sqrt_le_one_of_le_one {x : ℝ} (hx1 : x ≤ 1) : Real.sqrt x ≤ 1 := by
  calc Real.sqrt x ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hx1
    _ = 1 := Real.sqrt_one

/-- The Hellinger affinity of the geometric laws with ratios `a` and `b`. -/
def geometricHellingerAffinity (a b : ℝ) : ℝ :=
  Real.sqrt ((1 - a) * (1 - b)) / (1 - Real.sqrt (a * b))

/-- **The affinity is the geometric sum of the pointwise square roots.** -/
theorem hasSum_geometricHellinger {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b)
    (hb1 : b < 1) :
    HasSum (fun k : ℕ => Real.sqrt ((1 - a) * a ^ k * ((1 - b) * b ^ k)))
      (geometricHellingerAffinity a b) := by
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hablt : Real.sqrt (a * b) < 1 := sqrt_lt_one_of_lt_one hab0 (by nlinarith)
  have hgeo : HasSum (fun k : ℕ => Real.sqrt (a * b) ^ k) (1 - Real.sqrt (a * b))⁻¹ :=
    hasSum_geometric_of_lt_one (Real.sqrt_nonneg _) hablt
  have hmul := hgeo.mul_left (Real.sqrt ((1 - a) * (1 - b)))
  refine hmul.congr_fun fun k => ?_
  have hterm : (1 - a) * a ^ k * ((1 - b) * b ^ k) = ((1 - a) * (1 - b)) * (a * b) ^ k := by
    rw [mul_pow]
    ring
  rw [hterm, Real.sqrt_mul (by nlinarith), sqrt_pow_of_nonneg hab0]

/-- **Exact rationalized form of the Hellinger defect.** -/
theorem one_sub_geometricHellingerAffinity {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b)
    (hb1 : b < 1) :
    1 - geometricHellingerAffinity a b =
      (Real.sqrt a - Real.sqrt b) ^ 2 /
        ((1 - Real.sqrt (a * b)) *
          ((1 - Real.sqrt (a * b)) + Real.sqrt ((1 - a) * (1 - b)))) := by
  set u := Real.sqrt a with hu
  set v := Real.sqrt b with hv
  set w := Real.sqrt ((1 - a) * (1 - b)) with hw
  have hu2 : u ^ 2 = a := Real.sq_sqrt ha0
  have hv2 : v ^ 2 = b := Real.sq_sqrt hb0
  have hw2 : w ^ 2 = (1 - a) * (1 - b) := Real.sq_sqrt (by nlinarith)
  have huv : Real.sqrt (a * b) = u * v := Real.sqrt_mul ha0 b
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hablt : Real.sqrt (a * b) < 1 := sqrt_lt_one_of_lt_one hab0 (by nlinarith)
  have hden1 : 1 - u * v ≠ 0 := by
    rw [← huv]
    linarith
  have hwnn : 0 ≤ w := Real.sqrt_nonneg _
  have hden2 : (1 - u * v) + w ≠ 0 := by
    rw [← huv]
    have : 0 < 1 - Real.sqrt (a * b) := by linarith
    linarith
  rw [geometricHellingerAffinity, ← hw, huv]
  rw [eq_div_iff (mul_ne_zero hden1 hden2)]
  field_simp
  nlinarith [hu2, hv2, hw2]

/-- **The lower bound used by the Kakutani sum.** -/
theorem geometricHellinger_defect_ge {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b)
    (hb1 : b < 1) :
    (Real.sqrt a - Real.sqrt b) ^ 2 / 2 ≤ 1 - geometricHellingerAffinity a b := by
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hablt : Real.sqrt (a * b) < 1 := sqrt_lt_one_of_lt_one hab0 (by nlinarith)
  have habnn : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
  have hw1 : Real.sqrt ((1 - a) * (1 - b)) ≤ 1 :=
    sqrt_le_one_of_le_one (by nlinarith)
  have hwnn : 0 ≤ Real.sqrt ((1 - a) * (1 - b)) := Real.sqrt_nonneg _
  have hnum : 0 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 := sq_nonneg _
  have hden_pos : 0 < (1 - Real.sqrt (a * b)) *
      ((1 - Real.sqrt (a * b)) + Real.sqrt ((1 - a) * (1 - b))) := by
    apply mul_pos (by linarith)
    linarith
  have hden_le : (1 - Real.sqrt (a * b)) *
      ((1 - Real.sqrt (a * b)) + Real.sqrt ((1 - a) * (1 - b))) ≤ 2 := by
    nlinarith
  rw [one_sub_geometricHellingerAffinity ha0 ha1 hb0 hb1]
  apply div_le_div_of_nonneg_left hnum hden_pos hden_le

end

end GaloisForLFunctions.HTGeometry
