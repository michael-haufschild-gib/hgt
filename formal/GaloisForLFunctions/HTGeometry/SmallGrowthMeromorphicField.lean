import GaloisForLFunctions.HTGeometry.EntireFieldUpperEndEmbedding
import GaloisForLFunctions.HTGeometry.LogDerivPoissonJensen
import GaloisForLFunctions.HTGeometry.NevanlinnaEntireCharacteristic
import GaloisForLFunctions.HTGeometry.SecondMainTheoremChain
import GaloisForLFunctions.HTGeometry.WeierstrassFactorizationEntire

/-!
# Nagoshi's small-growth meromorphic coefficient field

This module builds the global coefficient carrier used in Dirichlet-series separation.  Its
elements are fractions of entire functions admitting a meromorphic representative whose
Nevanlinna characteristic satisfies `T(r, f) = o(r)`.

The first layer records characteristic invariance under codiscrete equality and closure of the
small-growth condition under addition, multiplication, and inversion.  These statements use the
actual mathlib Nevanlinna characteristic, including its pole-counting term.
-/

open Filter Set Topology Metric ValueDistribution Asymptotics

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Nevanlinna characteristic depends only on a global meromorphic function, not on its values at
the discrete exceptional set where a raw quotient presentation uses Lean's totalized division. -/
theorem characteristic_congr_codiscrete {f g : ℂ → ℂ}
    (hf : Meromorphic f) (hg : Meromorphic g)
    (hfg : f =ᶠ[Filter.codiscrete ℂ] g) {r : ℝ} (hr : r ≠ 0) :
    characteristic f ⊤ r = characteristic g ⊤ r := by
  classical
  have hcircle :
      f =ᶠ[Filter.codiscreteWithin (sphere (0 : ℂ) |r|)] g :=
    hfg.filter_mono (Filter.codiscreteWithin_mono (subset_univ _))
  have hprox : proximity f ⊤ r = proximity g ⊤ r :=
    proximity_congr_codiscreteWithin hcircle hr
  have horder : ∀ z : ℂ, meromorphicOrderAt f z = meromorphicOrderAt g z := by
    intro z
    exact meromorphicOrderAt_congr
      (PoissonJensen.eventuallyEq_nhdsNE_of_codiscreteWithin hfg univ_mem)
  have hdiv : MeromorphicOn.divisor f Set.univ = MeromorphicOn.divisor g Set.univ := by
    ext z
    rw [MeromorphicOn.divisor_apply (fun w _ => hf w) (Set.mem_univ z),
      MeromorphicOn.divisor_apply (fun w _ => hg w) (Set.mem_univ z), horder z]
  rw [characteristic, characteristic]
  change proximity f ⊤ r + logCounting f ⊤ r =
    proximity g ⊤ r + logCounting g ⊤ r
  rw [hprox]
  congr 1
  rw [logCounting_top, logCounting_top, hdiv]

/-- An eventually nonnegative function bounded by a little-o function is itself little-o. -/
theorem isLittleO_of_eventually_nonneg_le {u v : ℝ → ℝ}
    (hv : v =o[atTop] id)
    (hu0 : ∀ᶠ r in atTop, 0 ≤ u r)
    (huv : ∀ᶠ r in atTop, u r ≤ v r) :
    u =o[atTop] id := by
  apply (Asymptotics.IsBigO.of_bound 1 ?_).trans_isLittleO hv
  filter_upwards [hu0, huv] with r hur hle
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hur, one_mul]
  exact hle.trans (le_abs_self (v r))

/-- The sum of two small-characteristic meromorphic functions again has small characteristic. -/
theorem characteristic_add_isLittleO {f g : ℂ → ℂ}
    (hf : Meromorphic f) (hg : Meromorphic g)
    (hTf : characteristic f ⊤ =o[atTop] id)
    (hTg : characteristic g ⊤ =o[atTop] id) :
    characteristic (f + g) ⊤ =o[atTop] id := by
  let v : ℝ → ℝ := fun r =>
    characteristic f ⊤ r + characteristic g ⊤ r + Real.log 2
  have hv : v =o[atTop] id :=
    (hTf.add hTg).add (Asymptotics.isLittleO_const_id_atTop (Real.log 2))
  apply isLittleO_of_eventually_nonneg_le hv
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact characteristic_nonneg hr
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact characteristic_add_top_le hf hg hr

/-- The product of two nonzero small-characteristic meromorphic functions again has small
characteristic. -/
theorem characteristic_mul_isLittleO {f g : ℂ → ℂ}
    (hf : Meromorphic f) (hforder : ∀ z, meromorphicOrderAt f z ≠ ⊤)
    (hg : Meromorphic g) (hgorder : ∀ z, meromorphicOrderAt g z ≠ ⊤)
    (hTf : characteristic f ⊤ =o[atTop] id)
    (hTg : characteristic g ⊤ =o[atTop] id) :
    characteristic (f * g) ⊤ =o[atTop] id := by
  let v : ℝ → ℝ := fun r => characteristic f ⊤ r + characteristic g ⊤ r
  have hv : v =o[atTop] id := hTf.add hTg
  apply isLittleO_of_eventually_nonneg_le hv
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact characteristic_nonneg hr
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact characteristic_mul_top_le hr hf hforder hg hgorder

/-- Reciprocal preserves small Nevanlinna characteristic. -/
theorem characteristic_inv_isLittleO {f : ℂ → ℂ}
    (hf : Meromorphic f) (hTf : characteristic f ⊤ =o[atTop] id) :
    characteristic f⁻¹ ⊤ =o[atTop] id := by
  let C : ℝ := max |Real.log ‖f 0‖|
    |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
  let v : ℝ → ℝ := fun r => characteristic f ⊤ r + C
  have hv : v =o[atTop] id :=
    hTf.add (Asymptotics.isLittleO_const_id_atTop C)
  apply isLittleO_of_eventually_nonneg_le hv
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact characteristic_nonneg hr
  · filter_upwards with r
    have h := characteristic_sub_characteristic_inv_le (f := f) (R := r) hf
    have hright := (abs_le.mp h).1
    dsimp only [v, C]
    linarith

/-! ## Global meromorphic fraction presentations -/

/-- An explicit entire numerator/denominator presentation of a global meromorphic fraction. -/
structure EntireFractionPresentation (x : EntireField ℂ) where
  numerator : entireSubring ℂ
  denominator : entireSubring ℂ
  denominator_ne_zero : denominator ≠ 0
  eq_div : x =
    algebraMap (entireSubring ℂ) (EntireField ℂ) numerator /
      algebraMap (entireSubring ℂ) (EntireField ℂ) denominator

namespace EntireFractionPresentation

/-- Literal meromorphic function represented by an entire fraction. -/
def function {x : EntireField ℂ} (p : EntireFractionPresentation x) : ℂ → ℂ :=
  (p.numerator : ℂ → ℂ) / (p.denominator : ℂ → ℂ)

/-- Every global meromorphic fraction has an entire numerator/denominator presentation. -/
theorem exists_presentation (x : EntireField ℂ) : Nonempty (EntireFractionPresentation x) := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (entireSubring ℂ) x
  exact ⟨a, b, nonZeroDivisors.ne_zero hb, hab.symm⟩

/-- The literal representative is globally meromorphic. -/
theorem meromorphic {x : EntireField ℂ} (p : EntireFractionPresentation x) :
    Meromorphic p.function := by
  intro z
  exact (p.numerator.2 z (Set.mem_univ z)).meromorphicAt.div
    (p.denominator.2 z (Set.mem_univ z)).meromorphicAt

private theorem entire_ne_zero_exists {f : entireSubring ℂ} (hf : f ≠ 0) :
    ∃ z : ℂ, (f : ℂ → ℂ) z ≠ 0 := by
  by_contra h
  push Not at h
  apply hf
  apply Subtype.ext
  exact funext h

/-- A nonzero fraction representative is nowhere locally the zero meromorphic germ. -/
theorem meromorphicOrderAt_ne_top {x : EntireField ℂ}
    (p : EntireFractionPresentation x) (hx : x ≠ 0) (z : ℂ) :
    meromorphicOrderAt p.function z ≠ ⊤ := by
  have hnum : p.numerator ≠ 0 := by
    intro hzero
    apply hx
    rw [p.eq_div, hzero, map_zero, zero_div]
  obtain ⟨u, hu⟩ := entire_ne_zero_exists hnum
  obtain ⟨v, hv⟩ := entire_ne_zero_exists p.denominator_ne_zero
  have hnumDiff : Differentiable ℂ (p.numerator : ℂ → ℂ) :=
    fun w => (p.numerator.2 w (Set.mem_univ w)).differentiableAt
  have hdenDiff : Differentiable ℂ (p.denominator : ℂ → ℂ) :=
    fun w => (p.denominator.2 w (Set.mem_univ w)).differentiableAt
  have hnumOrder := GaloisForLFunctions.analyticOrderAt_ne_top_of_entire hnumDiff hu z
  have hdenOrder := GaloisForLFunctions.analyticOrderAt_ne_top_of_entire hdenDiff hv z
  rw [function, meromorphicOrderAt_div
    (p.numerator.2 z (Set.mem_univ z)).meromorphicAt
    (p.denominator.2 z (Set.mem_univ z)).meromorphicAt,
    (p.numerator.2 z (Set.mem_univ z)).meromorphicOrderAt_eq,
    (p.denominator.2 z (Set.mem_univ z)).meromorphicOrderAt_eq]
  simp [hnumOrder, hdenOrder]

/-- The denominator is nonzero on a codiscrete subset of the plane. -/
theorem denominator_eventually_ne_zero {x : EntireField ℂ}
    (p : EntireFractionPresentation x) :
    ∀ᶠ z in Filter.codiscrete ℂ, (p.denominator : ℂ → ℂ) z ≠ 0 := by
  obtain ⟨u, hu⟩ := entire_ne_zero_exists p.denominator_ne_zero
  have hdenDiff : Differentiable ℂ (p.denominator : ℂ → ℂ) :=
    fun w => (p.denominator.2 w (Set.mem_univ w)).differentiableAt
  have horder : ∀ z : ℂ,
      meromorphicOrderAt (p.denominator : ℂ → ℂ) z ≠ ⊤ := by
    intro z
    rw [(p.denominator.2 z (Set.mem_univ z)).meromorphicOrderAt_eq]
    have hz := GaloisForLFunctions.analyticOrderAt_ne_top_of_entire hdenDiff hu z
    simp [hz]
  exact MeromorphicAt.MeromorphicOn.codiscreteWithin_setOf_ne_zero
    (fun z _ => (p.denominator.2 z (Set.mem_univ z)).meromorphicAt)
    (fun z _ => horder z)

/-- Sum of two entire-fraction presentations. -/
def add {x y : EntireField ℂ} (p : EntireFractionPresentation x)
    (q : EntireFractionPresentation y) : EntireFractionPresentation (x + y) where
  numerator := p.numerator * q.denominator + q.numerator * p.denominator
  denominator := p.denominator * q.denominator
  denominator_ne_zero := mul_ne_zero p.denominator_ne_zero q.denominator_ne_zero
  eq_div := by
    have hp : algebraMap (entireSubring ℂ) (EntireField ℂ) p.denominator ≠ 0 :=
      by simpa only [map_zero] using
        (IsFractionRing.injective (entireSubring ℂ) (EntireField ℂ)).ne
          p.denominator_ne_zero
    have hq : algebraMap (entireSubring ℂ) (EntireField ℂ) q.denominator ≠ 0 :=
      by simpa only [map_zero] using
        (IsFractionRing.injective (entireSubring ℂ) (EntireField ℂ)).ne
          q.denominator_ne_zero
    calc
      x + y =
          algebraMap (entireSubring ℂ) (EntireField ℂ) p.numerator /
              algebraMap (entireSubring ℂ) (EntireField ℂ) p.denominator +
            algebraMap (entireSubring ℂ) (EntireField ℂ) q.numerator /
              algebraMap (entireSubring ℂ) (EntireField ℂ) q.denominator :=
        congrArg₂ (· + ·) p.eq_div q.eq_div
      _ = algebraMap (entireSubring ℂ) (EntireField ℂ)
              (p.numerator * q.denominator + q.numerator * p.denominator) /
            algebraMap (entireSubring ℂ) (EntireField ℂ)
              (p.denominator * q.denominator) := by
        simp only [map_add, map_mul]
        field_simp

/-- The common-denominator sum agrees codiscretely with pointwise addition. -/
theorem function_add_eventuallyEq {x y : EntireField ℂ}
    (p : EntireFractionPresentation x) (q : EntireFractionPresentation y) :
    (p.add q).function =ᶠ[Filter.codiscrete ℂ] p.function + q.function := by
  filter_upwards [p.denominator_eventually_ne_zero,
    q.denominator_eventually_ne_zero] with z hp hq
  change
    ((p.numerator : ℂ → ℂ) z * (q.denominator : ℂ → ℂ) z +
        (q.numerator : ℂ → ℂ) z * (p.denominator : ℂ → ℂ) z) /
        ((p.denominator : ℂ → ℂ) z * (q.denominator : ℂ → ℂ) z) =
      (p.numerator : ℂ → ℂ) z / (p.denominator : ℂ → ℂ) z +
        (q.numerator : ℂ → ℂ) z / (q.denominator : ℂ → ℂ) z
  field_simp

/-- Product of two entire-fraction presentations. -/
def mul {x y : EntireField ℂ} (p : EntireFractionPresentation x)
    (q : EntireFractionPresentation y) : EntireFractionPresentation (x * y) where
  numerator := p.numerator * q.numerator
  denominator := p.denominator * q.denominator
  denominator_ne_zero := mul_ne_zero p.denominator_ne_zero q.denominator_ne_zero
  eq_div := by
    calc
      x * y =
          (algebraMap (entireSubring ℂ) (EntireField ℂ) p.numerator /
              algebraMap (entireSubring ℂ) (EntireField ℂ) p.denominator) *
            (algebraMap (entireSubring ℂ) (EntireField ℂ) q.numerator /
              algebraMap (entireSubring ℂ) (EntireField ℂ) q.denominator) :=
        congrArg₂ (· * ·) p.eq_div q.eq_div
      _ = algebraMap (entireSubring ℂ) (EntireField ℂ)
              (p.numerator * q.numerator) /
            algebraMap (entireSubring ℂ) (EntireField ℂ)
              (p.denominator * q.denominator) := by
        simp only [map_mul]
        ring

/-- The product presentation agrees pointwise off the two denominator divisors. -/
theorem function_mul_eventuallyEq {x y : EntireField ℂ}
    (p : EntireFractionPresentation x) (q : EntireFractionPresentation y) :
    (p.mul q).function =ᶠ[Filter.codiscrete ℂ] p.function * q.function := by
  filter_upwards [p.denominator_eventually_ne_zero,
    q.denominator_eventually_ne_zero] with z hp hq
  change ((p.numerator : ℂ → ℂ) z * (q.numerator : ℂ → ℂ) z) /
      ((p.denominator : ℂ → ℂ) z * (q.denominator : ℂ → ℂ) z) =
    ((p.numerator : ℂ → ℂ) z / (p.denominator : ℂ → ℂ) z) *
      ((q.numerator : ℂ → ℂ) z / (q.denominator : ℂ → ℂ) z)
  field_simp

/-- The numerator of a presentation of a nonzero fraction is nonzero. -/
theorem numerator_ne_zero {x : EntireField ℂ} (p : EntireFractionPresentation x)
    (hx : x ≠ 0) : p.numerator ≠ 0 := by
  intro hzero
  apply hx
  rw [p.eq_div, hzero, map_zero, zero_div]

/-- Reciprocal presentation of a nonzero global meromorphic fraction. -/
def inv {x : EntireField ℂ} (p : EntireFractionPresentation x) (hx : x ≠ 0) :
    EntireFractionPresentation x⁻¹ where
  numerator := p.denominator
  denominator := p.numerator
  denominator_ne_zero := p.numerator_ne_zero hx
  eq_div := by
    calc
      x⁻¹ = (algebraMap (entireSubring ℂ) (EntireField ℂ) p.numerator /
          algebraMap (entireSubring ℂ) (EntireField ℂ) p.denominator)⁻¹ :=
        congrArg Inv.inv p.eq_div
      _ = algebraMap (entireSubring ℂ) (EntireField ℂ) p.denominator /
          algebraMap (entireSubring ℂ) (EntireField ℂ) p.numerator := inv_div _ _

@[simp]
theorem function_inv {x : EntireField ℂ} (p : EntireFractionPresentation x) (hx : x ≠ 0) :
    (p.inv hx).function = p.function⁻¹ := by
  funext z
  change (p.denominator : ℂ → ℂ) z / (p.numerator : ℂ → ℂ) z =
    ((p.numerator : ℂ → ℂ) z / (p.denominator : ℂ → ℂ) z)⁻¹
  exact (inv_div _ _).symm

/-- Additive inverse presentation. -/
def neg {x : EntireField ℂ} (p : EntireFractionPresentation x) :
    EntireFractionPresentation (-x) where
  numerator := -p.numerator
  denominator := p.denominator
  denominator_ne_zero := p.denominator_ne_zero
  eq_div := by
    calc
      -x = -(algebraMap (entireSubring ℂ) (EntireField ℂ) p.numerator /
          algebraMap (entireSubring ℂ) (EntireField ℂ) p.denominator) :=
        congrArg Neg.neg p.eq_div
      _ = algebraMap (entireSubring ℂ) (EntireField ℂ) (-p.numerator) /
          algebraMap (entireSubring ℂ) (EntireField ℂ) p.denominator := by
        rw [map_neg, neg_div]

@[simp]
theorem function_neg {x : EntireField ℂ} (p : EntireFractionPresentation x) :
    p.neg.function = -p.function := by
  funext z
  change (-(p.numerator : ℂ → ℂ)) z / (p.denominator : ℂ → ℂ) z =
    -((p.numerator : ℂ → ℂ) z / (p.denominator : ℂ → ℂ) z)
  rw [Pi.neg_apply, neg_div]

end EntireFractionPresentation

/-! ## The small-growth carrier -/

/-- A global meromorphic fraction has small growth when one entire-fraction representative has
Nevanlinna characteristic `o(r)`.  Codiscrete invariance makes this independent of totalized values
at poles. -/
def HasSmallGrowth (x : EntireField ℂ) : Prop :=
  ∃ p : EntireFractionPresentation x, characteristic p.function ⊤ =o[atTop] id

theorem characteristic_const_isLittleO (c : ℂ) :
    characteristic (fun _ : ℂ => c) ⊤ =o[atTop] id := by
  apply (Asymptotics.isLittleO_const_id_atTop (Real.posLog ‖c‖)).congr'
  · exact Filter.Eventually.of_forall fun r =>
      (GaloisForLFunctions.Nevanlinna.characteristic_const_eq c r).symm
  · exact EventuallyEq.rfl

theorem hasSmallGrowth_zero : HasSmallGrowth (0 : EntireField ℂ) := by
  let p : EntireFractionPresentation (0 : EntireField ℂ) :=
    { numerator := 0
      denominator := 1
      denominator_ne_zero := one_ne_zero
      eq_div := by simp }
  refine ⟨p, ?_⟩
  have hfun : p.function = fun _ : ℂ => 0 := by
    funext z
    change (0 : ℂ) / 1 = 0
    simp
  rw [hfun]
  exact characteristic_const_isLittleO 0

theorem hasSmallGrowth_one : HasSmallGrowth (1 : EntireField ℂ) := by
  let p : EntireFractionPresentation (1 : EntireField ℂ) :=
    { numerator := 1
      denominator := 1
      denominator_ne_zero := one_ne_zero
      eq_div := by simp }
  refine ⟨p, ?_⟩
  have hfun : p.function = fun _ : ℂ => 1 := by
    funext z
    change (1 : ℂ) / 1 = 1
    simp
  rw [hfun]
  exact characteristic_const_isLittleO 1

theorem HasSmallGrowth.add {x y : EntireField ℂ}
    (hx : HasSmallGrowth x) (hy : HasSmallGrowth y) :
    HasSmallGrowth (x + y) := by
  obtain ⟨p, hp⟩ := hx
  obtain ⟨q, hq⟩ := hy
  refine ⟨p.add q, ?_⟩
  have hsum := characteristic_add_isLittleO p.meromorphic q.meromorphic hp hq
  have hchar : characteristic (p.add q).function ⊤
      =ᶠ[atTop] characteristic (p.function + q.function) ⊤ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact characteristic_congr_codiscrete (p.add q).meromorphic
      (p.meromorphic.add q.meromorphic) (p.function_add_eventuallyEq q)
      (ne_of_gt (zero_lt_one.trans_le hr))
  exact hsum.congr' hchar.symm (EventuallyEq.rfl)

theorem HasSmallGrowth.mul {x y : EntireField ℂ}
    (hx : HasSmallGrowth x) (hy : HasSmallGrowth y) :
    HasSmallGrowth (x * y) := by
  by_cases hx0 : x = 0
  · rw [hx0, zero_mul]
    exact hasSmallGrowth_zero
  by_cases hy0 : y = 0
  · rw [hy0, mul_zero]
    exact hasSmallGrowth_zero
  obtain ⟨p, hp⟩ := hx
  obtain ⟨q, hq⟩ := hy
  refine ⟨p.mul q, ?_⟩
  have hprod := characteristic_mul_isLittleO p.meromorphic
    (p.meromorphicOrderAt_ne_top hx0) q.meromorphic
    (q.meromorphicOrderAt_ne_top hy0) hp hq
  have hchar : characteristic (p.mul q).function ⊤
      =ᶠ[atTop] characteristic (p.function * q.function) ⊤ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact characteristic_congr_codiscrete (p.mul q).meromorphic
      (p.meromorphic.mul q.meromorphic) (p.function_mul_eventuallyEq q)
      (ne_of_gt (zero_lt_one.trans_le hr))
  exact hprod.congr' hchar.symm (EventuallyEq.rfl)

theorem HasSmallGrowth.inv {x : EntireField ℂ} (hx : HasSmallGrowth x) :
    HasSmallGrowth x⁻¹ := by
  by_cases hx0 : x = 0
  · rw [hx0, inv_zero]
    exact hasSmallGrowth_zero
  obtain ⟨p, hp⟩ := hx
  refine ⟨p.inv hx0, ?_⟩
  rw [p.function_inv hx0]
  exact characteristic_inv_isLittleO p.meromorphic hp

theorem HasSmallGrowth.neg {x : EntireField ℂ} (hx : HasSmallGrowth x) :
    HasSmallGrowth (-x) := by
  by_cases hx0 : x = 0
  · rw [hx0, neg_zero]
    exact hasSmallGrowth_zero
  obtain ⟨p, hp⟩ := hx
  refine ⟨p.neg, ?_⟩
  let c : ℂ → ℂ := fun _ => -1
  have hcmero : Meromorphic c := fun _ => analyticAt_const.meromorphicAt
  have hcorder : ∀ z, meromorphicOrderAt c z ≠ ⊤ := by
    intro z
    rw [meromorphicOrderAt_const]
    simp [c]
  have hcsmall : characteristic c ⊤ =o[atTop] id :=
    characteristic_const_isLittleO (-1)
  have hprod := characteristic_mul_isLittleO hcmero hcorder p.meromorphic
    (p.meromorphicOrderAt_ne_top hx0) hcsmall hp
  have hfun : c * p.function = -p.function := by
    funext z
    simp [c]
  rw [p.function_neg, ← hfun]
  exact hprod

end

end GaloisForLFunctions.HTGeometry
