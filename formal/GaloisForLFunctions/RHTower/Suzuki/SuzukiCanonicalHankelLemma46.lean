import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelLemma45

/-!
# Suzuki (2012), Lemma 4.6

This module constructs Suzuki's extended Fredholm solution on every larger interval `(0,b)` and
proves uniqueness from the extended integral equation itself.  The central seam is an exact
cross-interval compression identity: restricting the `b`-section fed by the zero extension of an
`a`-source gives the original `a`-section.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-- Restriction from a physical interval `(0,b)` to `(0,a)`, routed through the common positive
half-line carrier. -/
def suzukiPhysicalIntervalRestrictionBetween (a b : ℝ) :
    IntervalL2 0 b →L[ℂ] IntervalL2 0 a :=
  suzukiPositiveIntervalRestriction a ∘L
    (suzukiPhysicalIntervalPositiveIsometry b).toContinuousLinearMap

/-- Extending a smaller interval into a larger one and then onto the positive ray is exactly the
original positive-ray extension. -/
theorem suzukiPhysicalIntervalInclusion_positiveExtension
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (f : IntervalL2 0 a) :
    suzukiPhysicalIntervalPositiveIsometry b
        (suzukiPhysicalIntervalInclusion a b f) =
      suzukiPhysicalIntervalPositiveIsometry a f := by
  let g : SuzukiPositiveL2 := suzukiPhysicalIntervalPositiveIsometry a f
  have hzero : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), b < x → g x = 0 := by
    filter_upwards [suzukiPhysicalIntervalPositiveL2_ae f] with x hx
    intro hbx
    have hgx : g x = suzukiPhysicalIntervalZeroExtendFun f x := by
      change suzukiPhysicalIntervalPositiveL2 f x = _
      exact hx
    rw [hgx]
    rw [suzukiPhysicalIntervalZeroExtendFun_eq_zero_of_notMem]
    intro hmem
    linarith [hmem.2]
  have hrecover : suzukiPhysicalIntervalPositiveIsometry b
      (suzukiPositiveIntervalRestriction b g) = g :=
    suzukiPhysicalInterval_extension_restriction_of_ae_zero
      (lt_of_lt_of_le ha hab) g hzero
  exact hrecover

/-- Restriction is a left inverse of the canonical smaller-to-larger inclusion. -/
@[simp] theorem suzukiPhysicalIntervalRestrictionBetween_inclusion
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (f : IntervalL2 0 a) :
    suzukiPhysicalIntervalRestrictionBetween a b
        (suzukiPhysicalIntervalInclusion a b f) = f := by
  change suzukiPositiveIntervalRestriction a
      (suzukiPhysicalIntervalPositiveIsometry b
        (suzukiPhysicalIntervalInclusion a b f)) = f
  rw [suzukiPhysicalIntervalInclusion_positiveExtension ha hab]
  exact suzukiPositiveIntervalRestriction_extension a f

/-- Cross-interval inclusion and restriction are Hilbert adjoints. -/
theorem inner_suzukiPhysicalIntervalInclusion
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (f : IntervalL2 0 a) (g : IntervalL2 0 b) :
    inner ℂ (suzukiPhysicalIntervalInclusion a b f) g =
      inner ℂ f (suzukiPhysicalIntervalRestrictionBetween a b g) := by
  calc
    inner ℂ (suzukiPhysicalIntervalInclusion a b f) g =
        inner ℂ
          (suzukiPhysicalIntervalPositiveIsometry b
            (suzukiPhysicalIntervalInclusion a b f))
          (suzukiPhysicalIntervalPositiveIsometry b g) :=
      (LinearIsometry.inner_map_map
        (suzukiPhysicalIntervalPositiveIsometry b)
        (suzukiPhysicalIntervalInclusion a b f) g).symm
    _ = inner ℂ (suzukiPhysicalIntervalPositiveIsometry a f)
        (suzukiPhysicalIntervalPositiveIsometry b g) := by
      rw [suzukiPhysicalIntervalInclusion_positiveExtension ha hab]
    _ = inner ℂ f (suzukiPhysicalIntervalRestrictionBetween a b g) := by
      exact inner_suzukiPhysicalIntervalPositive_extension f
        (suzukiPhysicalIntervalPositiveIsometry b g)

/-- Exact nesting law for Suzuki's literal finite Hankel sections. -/
theorem suzukiCompressedHankel_crossInterval
    {omega a b : ℝ} (homega : 1 / 2 < omega)
    (ha : 1 < a) (hab : a ≤ b) (f : IntervalL2 0 a) :
    suzukiPhysicalIntervalRestrictionBetween a b
        (suzukiCompressedHankelOperator omega b homega
          (suzukiPhysicalIntervalInclusion a b f)) =
      suzukiCompressedHankelOperator omega a homega f := by
  let H := suzukiCanonicalPositiveHankelUnitary omega
    (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega)
  apply ext_inner_left ℂ
  intro k
  rw [← inner_suzukiPhysicalIntervalInclusion (by linarith) hab]
  rw [← suzukiCanonicalPositiveHankelCompression_eq_compressedHankel
    homega (lt_of_lt_of_le (lt_trans zero_lt_one ha) hab)]
  change inner ℂ (suzukiPhysicalIntervalInclusion a b k)
      (suzukiPositiveIntervalRestriction b
        (H (suzukiPhysicalIntervalPositiveIsometry b
          (suzukiPhysicalIntervalInclusion a b f)))) = _
  rw [← inner_suzukiPhysicalIntervalPositive_extension]
  rw [suzukiPhysicalIntervalInclusion_positiveExtension (by linarith) hab,
    suzukiPhysicalIntervalInclusion_positiveExtension (by linarith) hab]
  rw [← suzukiCanonicalPositiveHankelCompression_eq_compressedHankel
    homega (by linarith)]
  exact inner_suzukiPhysicalIntervalPositive_extension k
    (H (suzukiPhysicalIntervalPositiveIsometry a f))

/-- Literal larger-interval row `x ↦ h_omega(ax)`. -/
def suzukiHankelBoundarySourceOn
    (omega a b : ℝ) (homega : 1 / 2 < omega) (hb : 1 < b) :
    IntervalL2 0 b :=
  suzukiCompressedHankelRow omega b homega hb a

theorem suzukiHankelBoundarySourceOn_ae
    {omega a b : ℝ} (homega : 1 / 2 < omega)
    (ha : 1 < a) (hab : a ≤ b) :
    (suzukiHankelBoundarySourceOn omega a b homega
      (lt_of_lt_of_le ha hab) : ClosedInterval 0 b → ℂ) =ᵐ[volume]
      fun x => suzukiSourceHFinite omega (a * (x : ℝ)) := by
  exact suzukiCompressedHankelRow_ae homega (lt_of_lt_of_le ha hab)
    (lt_trans zero_lt_one ha) hab

/-- Restricting the literal larger-interval boundary row recovers the original boundary row. -/
theorem suzukiHankelBoundarySourceOn_restriction
    {omega a b : ℝ} (homega : 1 / 2 < omega)
    (ha : 1 < a) (hab : a ≤ b) :
    suzukiPhysicalIntervalRestrictionBetween a b
        (suzukiHankelBoundarySourceOn omega a b homega (lt_of_lt_of_le ha hab)) =
      suzukiHankelBoundarySource omega a homega ha := by
  let rowB := suzukiHankelBoundarySourceOn omega a b homega (lt_of_lt_of_le ha hab)
  let EB : SuzukiPositiveL2 := suzukiPhysicalIntervalPositiveIsometry b rowB
  have hrowRepSub : ∀ᵐ y : ClosedInterval 0 b ∂volume,
      suzukiPhysicalIntervalZeroExtendFun rowB (y : ℝ) =
        suzukiSourceHFinite omega (a * (y : ℝ)) := by
    filter_upwards [suzukiPhysicalIntervalRepresentative_ae rowB,
      suzukiHankelBoundarySourceOn_ae homega ha hab] with y hrep hrow
    rw [suzukiPhysicalIntervalZeroExtendFun_apply, hrep, hrow]
  have hrowRealB : ∀ᵐ y ∂(volume : Measure ℝ).restrict (Icc 0 b),
      suzukiPhysicalIntervalZeroExtendFun rowB y =
        suzukiSourceHFinite omega (a * y) :=
    (ae_restrict_iff_subtype measurableSet_Icc).2 hrowRepSub
  have hrowWhole := (ae_restrict_iff' measurableSet_Icc).mp hrowRealB
  let hmp : MeasurePreserving ((↑) : ClosedInterval 0 a → ℝ)
      (volume : Measure (ClosedInterval 0 a))
      ((volume : Measure ℝ).restrict (Icc 0 a)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hEBReal := (ae_restrict_iff' measurableSet_Ioi).mp
    (suzukiPhysicalIntervalPositiveL2_ae rowB)
  have hEBSub := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae hEBReal)
  have hrowSub := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae hrowWhole)
  have hne := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae (volume.ae_ne (0 : ℝ)))
  apply Lp.ext
  filter_upwards [suzukiPositiveIntervalRestriction_value_ae EB,
    hEBSub, hrowSub, suzukiHankelBoundarySource_ae homega ha, hne] with
      x hres hEB hrow hsource hne
  change suzukiPositiveIntervalRestriction a EB x = _
  rw [hres]
  have hxpos : 0 < (x : ℝ) := lt_of_le_of_ne x.property.1 (Ne.symm hne)
  rw [show EB (x : ℝ) = suzukiPhysicalIntervalZeroExtendFun rowB (x : ℝ) by
    exact hEB hxpos, hrow ⟨x.property.1, le_trans x.property.2 hab⟩, hsource]

/-- Larger-interval boundary `x ↦ h_omega(ax)`. -/
def suzukiHankelExtendedBoundary
    (omega a b : ℝ) (homega : 1 / 2 < omega) (ha : 1 < a) (hab : a ≤ b) :
    IntervalL2 0 b :=
  suzukiHankelBoundarySourceOn omega a b homega (lt_of_lt_of_le ha hab)

@[simp] theorem suzukiHankelExtendedBoundary_restriction
    {omega a b : ℝ} (homega : 1 / 2 < omega) (ha : 1 < a) (hab : a ≤ b) :
    suzukiPhysicalIntervalRestrictionBetween a b
        (suzukiHankelExtendedBoundary omega a b homega ha hab) =
      suzukiHankelBoundarySource omega a homega ha := by
  exact suzukiHankelBoundarySourceOn_restriction homega ha hab

/-- Extended Fredholm equation on `(0,b)`, with its integral depending only on restriction to
`(0,a)`.  This is Suzuki's equation (402) on the larger interval. -/
def SuzukiHankelExtendedEquation
    (epsilon : SuzukiHankelSign) (omega a b : ℝ)
    (homega : 1 / 2 < omega) (ha : 1 < a) (hab : a ≤ b)
    (X : IntervalL2 0 b) : Prop :=
  X = suzukiHankelExtendedBoundary omega a b homega ha hab -
    epsilon.coeff • suzukiCompressedHankelOperator omega b homega
      (suzukiPhysicalIntervalInclusion a b
        (suzukiPhysicalIntervalRestrictionBetween a b X))

/-- Suzuki's extended solution on `(0,b)`. -/
def suzukiHankelPhiExtended
    (epsilon : SuzukiHankelSign) (omega a b : ℝ)
    (homega : 1 / 2 < omega) (ha : 1 < a) (hab : a ≤ b) :
    IntervalL2 0 b :=
  suzukiHankelExtendedBoundary omega a b homega ha hab -
    epsilon.coeff • suzukiCompressedHankelOperator omega b homega
      (suzukiPhysicalIntervalInclusion a b
        (suzukiHankelPhi epsilon omega a homega ha))

/-- The extended solution restricts exactly to Lemma 4.5's solution. -/
theorem suzukiHankelPhiExtended_restriction
    (epsilon : SuzukiHankelSign) {omega a b : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a) (hab : a ≤ b) :
    suzukiPhysicalIntervalRestrictionBetween a b
        (suzukiHankelPhiExtended epsilon omega a b homega ha hab) =
      suzukiHankelPhi epsilon omega a homega ha := by
  rw [suzukiHankelPhiExtended, map_sub, map_smul,
    suzukiHankelExtendedBoundary_restriction homega ha hab,
    suzukiCompressedHankel_crossInterval homega ha hab]
  have hEq := suzukiHankelPhi_resolvent_equation epsilon homega ha
  simpa only [suzukiHankelResolventOperator, ContinuousLinearMap.add_apply,
    one_apply_eq_self, ContinuousLinearMap.smul_apply, smul_eq_mul,
    sub_eq_iff_eq_add] using hEq.symm

/-- The constructed extension satisfies the larger-interval equation. -/
theorem suzukiHankelPhiExtended_equation
    (epsilon : SuzukiHankelSign) {omega a b : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a) (hab : a ≤ b) :
    SuzukiHankelExtendedEquation epsilon omega a b homega ha hab
      (suzukiHankelPhiExtended epsilon omega a b homega ha hab) := by
  rw [SuzukiHankelExtendedEquation,
    suzukiHankelPhiExtended_restriction epsilon homega ha hab]
  rfl

/-- Any larger-interval solution restricts to the unique Lemma 4.5 solution. -/
theorem suzukiHankelExtendedEquation_restriction
    (epsilon : SuzukiHankelSign) {omega a b : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a) (hab : a ≤ b)
    {X : IntervalL2 0 b}
    (hX : SuzukiHankelExtendedEquation epsilon omega a b homega ha hab X) :
    suzukiPhysicalIntervalRestrictionBetween a b X =
      suzukiHankelPhi epsilon omega a homega ha := by
  rw [SuzukiHankelExtendedEquation] at hX
  have hres := congrArg (suzukiPhysicalIntervalRestrictionBetween a b) hX
  rw [map_sub, map_smul,
    suzukiHankelExtendedBoundary_restriction homega ha hab,
    suzukiCompressedHankel_crossInterval homega ha hab] at hres
  apply suzukiHankel_resolvent_unique epsilon homega ha
  simpa only [suzukiHankelResolventOperator, ContinuousLinearMap.add_apply,
    one_apply_eq_self, ContinuousLinearMap.smul_apply, smul_eq_mul,
    eq_sub_iff_add_eq] using (eq_sub_iff_add_eq.mp hres)

/-- Uniqueness of Suzuki's extended solution on every `(0,b)`. -/
theorem suzukiHankelPhiExtended_unique
    (epsilon : SuzukiHankelSign) {omega a b : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a) (hab : a ≤ b)
    {X : IntervalL2 0 b}
    (hX : SuzukiHankelExtendedEquation epsilon omega a b homega ha hab X) :
    X = suzukiHankelPhiExtended epsilon omega a b homega ha hab := by
  rw [hX, suzukiHankelPhiExtended,
    suzukiHankelExtendedEquation_restriction epsilon homega ha hab hX]

/-- Pointwise-a.e. form of Suzuki's extended equation.  The integral is over `(0,b)` after the
canonical zero extension of the `(0,a)` solution, exactly representing the source's `∫₀ᵃ`. -/
theorem suzukiHankelPhiExtended_integral_equation_ae
    (epsilon : SuzukiHankelSign) {omega a b : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a) (hab : a ≤ b) :
    ∀ᵐ x : ClosedInterval 0 b ∂volume,
      suzukiHankelPhiExtended epsilon omega a b homega ha hab x +
          epsilon.coeff * ∫ y : ClosedInterval 0 b,
            suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
              suzukiPhysicalIntervalInclusion a b
                (suzukiHankelPhi epsilon omega a homega ha) y ∂volume =
        suzukiSourceHFinite omega (a * (x : ℝ)) := by
  let hb : 1 < b := lt_of_lt_of_le ha hab
  let phi := suzukiHankelPhi epsilon omega a homega ha
  let inc := suzukiPhysicalIntervalInclusion a b phi
  let T := suzukiCompressedHankelOperator omega b homega
  have hEq : suzukiHankelPhiExtended epsilon omega a b homega ha hab =
      suzukiHankelExtendedBoundary omega a b homega ha hab -
        epsilon.coeff • T inc := rfl
  have hsub := Lp.coeFn_sub
    (suzukiHankelExtendedBoundary omega a b homega ha hab)
    (epsilon.coeff • T inc)
  rw [← hEq] at hsub
  filter_upwards [hsub, Lp.coeFn_smul epsilon.coeff (T inc),
    suzukiCompressedHankelOperator_coeFn omega b homega (by linarith) inc,
    suzukiHankelBoundarySourceOn_ae homega ha hab] with
      x hxsub hxsmul hT hsource
  change suzukiHankelPhiExtended epsilon omega a b homega ha hab x +
      epsilon.coeff * (∫ y : ClosedInterval 0 b,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) * inc y ∂volume) = _
  rw [hxsub, Pi.sub_apply, hxsmul, Pi.smul_apply, smul_eq_mul, hT]
  change suzukiHankelBoundarySourceOn omega a b homega hb x -
      epsilon.coeff * (∫ y : ClosedInterval 0 b,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) * inc y ∂volume) +
      epsilon.coeff * (∫ y : ClosedInterval 0 b,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) * inc y ∂volume) = _
  rw [hsource]
  ring

/-- The canonical zero extension of the real Lemma 4.5 solution is real a.e. on every larger
interval. -/
theorem suzukiPhysicalIntervalInclusion_phi_real_ae
    (epsilon : SuzukiHankelSign) {omega a b : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a) (hab : a ≤ b) :
    ∀ᵐ y : ClosedInterval 0 b ∂volume,
      (suzukiPhysicalIntervalInclusion a b
        (suzukiHankelPhi epsilon omega a homega ha) y).im = 0 := by
  let phi := suzukiHankelPhi epsilon omega a homega ha
  let EA : SuzukiPositiveL2 := suzukiPhysicalIntervalPositiveIsometry a phi
  have hzeroSub : ∀ᵐ y : ClosedInterval 0 a ∂volume,
      (suzukiPhysicalIntervalZeroExtendFun phi (y : ℝ)).im = 0 := by
    filter_upwards [suzukiPhysicalIntervalRepresentative_ae phi,
      suzukiHankelPhi_real_ae epsilon homega ha] with y hrep hreal
    rw [suzukiPhysicalIntervalZeroExtendFun_apply, hrep]
    exact hreal
  have hzeroIcc : ∀ᵐ y ∂(volume : Measure ℝ).restrict (Icc 0 a),
      (suzukiPhysicalIntervalZeroExtendFun phi y).im = 0 :=
    (ae_restrict_iff_subtype measurableSet_Icc).2 hzeroSub
  have hzeroConditional := (ae_restrict_iff' measurableSet_Icc).mp hzeroIcc
  have hzeroWhole : ∀ᵐ y ∂(volume : Measure ℝ),
      (suzukiPhysicalIntervalZeroExtendFun phi y).im = 0 := by
    filter_upwards [hzeroConditional] with y hy
    by_cases hmem : y ∈ Icc 0 a
    · exact hy hmem
    · rw [suzukiPhysicalIntervalZeroExtendFun_eq_zero_of_notMem phi hmem]
      simp
  have hEAConditional := (ae_restrict_iff' measurableSet_Ioi).mp
    (suzukiPhysicalIntervalPositiveL2_ae phi)
  let hmp : MeasurePreserving ((↑) : ClosedInterval 0 b → ℝ)
      (volume : Measure (ClosedInterval 0 b))
      ((volume : Measure ℝ).restrict (Icc 0 b)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hEASub := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae hEAConditional)
  have hzeroSubB := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae hzeroWhole)
  have hne := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae (volume.ae_ne (0 : ℝ)))
  filter_upwards [suzukiPhysicalIntervalInclusion_ae a b phi,
    hEASub, hzeroSubB, hne] with y hinc hEA hzero hne
  rw [hinc]
  have hypos : 0 < (y : ℝ) := lt_of_le_of_ne y.property.1 (Ne.symm hne)
  rw [hEA hypos]
  exact hzero

/-- Suzuki's extended solution is real-valued almost everywhere. -/
theorem suzukiHankelPhiExtended_real_ae
    (epsilon : SuzukiHankelSign) {omega a b : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a) (hab : a ≤ b) :
    ∀ᵐ x : ClosedInterval 0 b ∂volume,
      (suzukiHankelPhiExtended epsilon omega a b homega ha hab x).im = 0 := by
  let inc := suzukiPhysicalIntervalInclusion a b
    (suzukiHankelPhi epsilon omega a homega ha)
  filter_upwards [suzukiHankelPhiExtended_integral_equation_ae epsilon homega ha hab] with x heq
  let I : ℂ := ∫ y : ClosedInterval 0 b,
    suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) * inc y ∂volume
  have hI : (starRingEnd ℂ) I = I := by
    dsimp only [I]
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [suzukiPhysicalIntervalInclusion_phi_real_ae
      epsilon homega ha hab] with y hy
    rw [map_mul, conj_suzukiSourceHFinite]
    rw [Complex.conj_eq_iff_im.mpr hy]
  have hsource : (starRingEnd ℂ)
      (suzukiSourceHFinite omega (a * (x : ℝ))) =
      suzukiSourceHFinite omega (a * (x : ℝ)) :=
    conj_suzukiSourceHFinite omega (a * (x : ℝ))
  have hcoeff : (starRingEnd ℂ) epsilon.coeff = epsilon.coeff := by
    simpa only [starRingEnd_apply] using SuzukiHankelSign.star_coeff epsilon
  apply Complex.conj_eq_iff_im.mp
  have hxEq : suzukiHankelPhiExtended epsilon omega a b homega ha hab x =
      suzukiSourceHFinite omega (a * (x : ℝ)) - epsilon.coeff * I := by
    apply eq_sub_iff_add_eq.mpr
    exact heq
  rw [hxEq, map_sub, map_mul, hsource, hcoeff, hI]

/-! ## Global continuous extension for `omega > 1` -/

/-- Literal extension formula (404.1) on the positive half-line. -/
def suzukiHankelPhiGlobal
    (epsilon : SuzukiHankelSign) (omega a : ℝ)
    (homega : 1 < omega) (ha : 1 < a) (x : ℝ) : ℂ :=
  suzukiSourceHFinite omega (a * x) - epsilon.coeff *
    ∫ y : ClosedInterval 0 a,
      suzukiSourceHFinite omega (x * (y : ℝ)) *
        suzukiHankelPhi epsilon omega a (by linarith) ha y ∂volume

/-- Restricting any sufficiently large literal row gives the corresponding literal kernel row
on the integration interval. -/
theorem suzukiPhysicalIntervalRestrictionBetween_row_ae
    {omega a B x : ℝ} (homega : 1 / 2 < omega)
    (ha : 0 < a) (hB : 1 < B) (haB : a ≤ B) (hx : 0 < x) (hxB : x ≤ B) :
    (suzukiPhysicalIntervalRestrictionBetween a B
      (suzukiCompressedHankelRow omega B homega hB x) : ClosedInterval 0 a → ℂ) =ᵐ[volume]
        fun y => suzukiSourceHFinite omega (x * (y : ℝ)) := by
  let rowB := suzukiCompressedHankelRow omega B homega hB x
  let EB : SuzukiPositiveL2 := suzukiPhysicalIntervalPositiveIsometry B rowB
  have hrowRepSub : ∀ᵐ y : ClosedInterval 0 B ∂volume,
      suzukiPhysicalIntervalZeroExtendFun rowB (y : ℝ) =
        suzukiSourceHFinite omega (x * (y : ℝ)) := by
    filter_upwards [suzukiPhysicalIntervalRepresentative_ae rowB,
      suzukiCompressedHankelRow_ae homega hB hx hxB] with y hrep hrow
    rw [suzukiPhysicalIntervalZeroExtendFun_apply, hrep, hrow]
  have hrowRealB : ∀ᵐ y ∂(volume : Measure ℝ).restrict (Icc 0 B),
      suzukiPhysicalIntervalZeroExtendFun rowB y =
        suzukiSourceHFinite omega (x * y) :=
    (ae_restrict_iff_subtype measurableSet_Icc).2 hrowRepSub
  have hrowWhole := (ae_restrict_iff' measurableSet_Icc).mp hrowRealB
  let hmp : MeasurePreserving ((↑) : ClosedInterval 0 a → ℝ)
      (volume : Measure (ClosedInterval 0 a))
      ((volume : Measure ℝ).restrict (Icc 0 a)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hEBReal := (ae_restrict_iff' measurableSet_Ioi).mp
    (suzukiPhysicalIntervalPositiveL2_ae rowB)
  have hEBSub := hmp.quasiMeasurePreserving.ae (ae_restrict_of_ae hEBReal)
  have hrowSub := hmp.quasiMeasurePreserving.ae (ae_restrict_of_ae hrowWhole)
  have hne := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae (volume.ae_ne (0 : ℝ)))
  filter_upwards [suzukiPositiveIntervalRestriction_value_ae EB,
    hEBSub, hrowSub, hne] with y hres hEB hrow hne
  change suzukiPositiveIntervalRestriction a EB y = _
  rw [hres]
  have hypos : 0 < (y : ℝ) := lt_of_le_of_ne y.property.1 (Ne.symm hne)
  rw [show EB (y : ℝ) = suzukiPhysicalIntervalZeroExtendFun rowB (y : ℝ) by
    exact hEB hypos, hrow ⟨y.property.1, le_trans y.property.2 haB⟩]

/-- Pairing a restricted large row with an `a`-interval source is exactly the literal integral. -/
theorem suzukiRestrictedLargeRow_pairing_eq_integral
    {omega a B x : ℝ} (homega : 1 / 2 < omega)
    (ha : 0 < a) (hB : 1 < B) (haB : a ≤ B) (hx : 0 < x) (hxB : x ≤ B)
    (f : IntervalL2 0 a) :
    (complexMulBilinear.lpPairing volume 2 2
      (suzukiPhysicalIntervalRestrictionBetween a B
        (suzukiCompressedHankelRow omega B homega hB x))) f =
      ∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega (x * (y : ℝ)) * f y ∂volume := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [suzukiPhysicalIntervalRestrictionBetween_row_ae
    homega ha hB haB hx hxB] with y hy
  rw [hy]
  simp [complexMulBilinear]

/-- On every larger compact interval, restriction of the continuous row field followed by pairing
with an `a`-interval source is a continuous scalar function.  This is the local compactness bridge
used to obtain continuity of Suzuki's literal half-line formula. -/
def suzukiRestrictedLargeRowPairingContinuous
    (omega a B : ℝ) (homega : 1 / 2 < omega)
    (hB : 1 < B) (f : IntervalL2 0 a) : C(ClosedInterval 0 B, ℂ) where
  toFun x :=
    (complexMulBilinear.lpPairing volume 2 2
      (suzukiPhysicalIntervalRestrictionBetween a B
        (suzukiCompressedHankelRowContinuous omega B homega hB x))) f
  continuous_toFun :=
    ((ContinuousLinearMap.apply ℂ ℂ) f).continuous.comp
      ((complexMulBilinear.lpPairing volume 2 2).continuous.comp
        ((suzukiPhysicalIntervalRestrictionBetween a B).continuous.comp
          (suzukiCompressedHankelRowContinuous omega B homega hB).continuous))

/-- The compact continuous pairing is the literal kernel integral at every positive point of the
larger interval. -/
theorem suzukiRestrictedLargeRowPairingContinuous_eq_integral
    {omega a B : ℝ} (homega : 1 / 2 < omega)
    (ha : 0 < a) (hB : 1 < B) (haB : a ≤ B)
    (f : IntervalL2 0 a) (x : ClosedInterval 0 B) (hx : 0 < (x : ℝ)) :
    suzukiRestrictedLargeRowPairingContinuous omega a B homega hB f x =
      ∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) * f y ∂volume := by
  exact suzukiRestrictedLargeRow_pairing_eq_integral homega ha hB haB hx x.property.2 f

/-- Suzuki's literal formula (404.1) is continuous on the entire positive half-line.  Continuity is
proved locally by placing both the fixed integration interval and the evaluation point inside one
larger compact Hankel section. -/
theorem continuousOn_suzukiHankelPhiGlobal
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) :
    ContinuousOn (suzukiHankelPhiGlobal epsilon omega a homega ha) (Ioi 0) := by
  let homegaHalf : 1 / 2 < omega := by linarith
  let phi := suzukiHankelPhi epsilon omega a homegaHalf ha
  intro x hx
  let B : ℝ := max a x + 1
  have hB : 1 < B := by
    dsimp only [B]
    linarith [le_max_left a x]
  have haB : a ≤ B := by
    dsimp only [B]
    linarith [le_max_left a x]
  have hxB : x < B := by
    dsimp only [B]
    linarith [le_max_right a x]
  let localPair : ℝ → ℂ := fun z =>
    (complexMulBilinear.lpPairing volume 2 2
      (suzukiPhysicalIntervalRestrictionBetween a B
        (suzukiCompressedHankelRow omega B homegaHalf hB z))) phi
  have hpairOn : ContinuousOn localPair (Icc 0 B) := by
    change ContinuousOn (fun z : ℝ =>
      ((ContinuousLinearMap.apply ℂ ℂ) phi)
        ((complexMulBilinear.lpPairing volume 2 2)
          (suzukiPhysicalIntervalRestrictionBetween a B
            (suzukiCompressedHankelRow omega B homegaHalf hB z)))) (Icc 0 B)
    exact ((ContinuousLinearMap.apply ℂ ℂ) phi).continuous.comp_continuousOn
      ((complexMulBilinear.lpPairing volume 2 2).continuous.comp_continuousOn
        ((suzukiPhysicalIntervalRestrictionBetween a B).continuous.comp_continuousOn
          (continuousOn_suzukiCompressedHankelRow homegaHalf hB)))
  have hpairAt : ContinuousAt localPair x :=
    (hpairOn.mono fun z hz => ⟨hz.1.le, hz.2.le⟩).continuousAt
      (isOpen_Ioo.mem_nhds ⟨hx, hxB⟩)
  let localFormula : ℝ → ℂ := fun z =>
    suzukiSourceHFinite omega (a * z) - epsilon.coeff * localPair z
  have hsourceAt : ContinuousAt (fun z : ℝ => suzukiSourceHFinite omega (a * z)) x :=
    (continuousAt_suzukiSourceHFinite homega (mul_pos (by linarith) hx)).comp
      (continuousAt_const.mul continuousAt_id)
  have hlocalAt : ContinuousAt localFormula x := by
    exact hsourceAt.sub (continuousAt_const.mul hpairAt)
  have heq : suzukiHankelPhiGlobal epsilon omega a homega ha =ᶠ[𝓝 x] localFormula := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hx, hxB⟩] with z hz
    rw [suzukiHankelPhiGlobal]
    change suzukiSourceHFinite omega (a * z) - epsilon.coeff *
        (∫ y : ClosedInterval 0 a,
          suzukiSourceHFinite omega (z * (y : ℝ)) * phi y ∂volume) =
      suzukiSourceHFinite omega (a * z) - epsilon.coeff * localPair z
    rw [show localPair z = ∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega (z * (y : ℝ)) * phi y ∂volume by
      dsimp only [localPair]
      exact suzukiRestrictedLargeRow_pairing_eq_integral homegaHalf (by linarith)
        hB haB hz.1 hz.2.le phi]
  exact (hlocalAt.congr_of_eventuallyEq heq).continuousWithinAt

/-- The global formula retains the sharp support gap forced by `h_omega(t)=0` for `t ≤ 1`. -/
theorem suzukiHankelPhiGlobal_eq_zero_below_reciprocal
    (epsilon : SuzukiHankelSign) {omega a x : ℝ}
    (homega : 1 < omega) (ha : 1 < a) (hx0 : 0 ≤ x) (hxa : x ≤ 1 / a) :
    suzukiHankelPhiGlobal epsilon omega a homega ha x = 0 := by
  rw [suzukiHankelPhiGlobal]
  have hsource : suzukiSourceHFinite omega (a * x) = 0 := by
    rw [suzukiSourceHFinite, if_neg]
    exact not_lt_of_ge (by
      calc
        a * x ≤ a * (1 / a) := mul_le_mul_of_nonneg_left hxa (by linarith)
        _ = 1 := by field_simp)
  have hintegrand : (fun y : ClosedInterval 0 a =>
      suzukiSourceHFinite omega (x * (y : ℝ)) *
        suzukiHankelPhi epsilon omega a (by linarith) ha y) = fun _ => 0 := by
    funext y
    rw [suzukiSourceHFinite, if_neg, zero_mul]
    exact not_lt_of_ge (by
      calc
        x * (y : ℝ) ≤ (1 / a) * a :=
          mul_le_mul hxa y.property.2 y.property.1 (one_div_nonneg.mpr (by linarith))
        _ = 1 := by field_simp)
  rw [hsource, hintegrand]
  simp

/-- The literal extension is continuous even at the endpoint `0`; this is stronger than the
paper's stated `C⁰(0,∞)` conclusion. -/
theorem continuousOn_suzukiHankelPhiGlobal_nonnegative
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) :
    ContinuousOn (suzukiHankelPhiGlobal epsilon omega a homega ha) (Ici 0) := by
  intro x hx
  change 0 ≤ x at hx
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · have hainv : 0 < 1 / a := one_div_pos.mpr (lt_trans zero_lt_one ha)
    have hev : suzukiHankelPhiGlobal epsilon omega a homega ha =ᶠ[𝓝[Ici 0] 0]
        fun _ => 0 := by
      have hsmall : ∀ᶠ z in 𝓝[Ici 0] 0, z ∈ Iio (1 / a) :=
        Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds hainv)
      filter_upwards [hsmall, self_mem_nhdsWithin] with z hz hz0
      exact suzukiHankelPhiGlobal_eq_zero_below_reciprocal epsilon homega ha hz0 hz.le
    exact continuousWithinAt_const.congr_of_eventuallyEq hev
      (suzukiHankelPhiGlobal_eq_zero_below_reciprocal epsilon homega ha le_rfl
        (one_div_nonneg.mpr (by linarith)))
  · exact ((continuousOn_suzukiHankelPhiGlobal epsilon homega ha).continuousAt
      (isOpen_Ioi.mem_nhds hxpos)).continuousWithinAt

/-- Continuous global extension as a function on `[0,∞)`. -/
def suzukiHankelPhiGlobalContinuous
    (epsilon : SuzukiHankelSign) (omega a : ℝ)
    (homega : 1 < omega) (ha : 1 < a) : C(Ici (0 : ℝ), ℂ) where
  toFun x := suzukiHankelPhiGlobal epsilon omega a homega ha (x : ℝ)
  continuous_toFun := continuousOn_iff_continuous_restrict.mp
    (continuousOn_suzukiHankelPhiGlobal_nonnegative epsilon homega ha)

/-- Formula (404.1) agrees pointwise on `[0,a]` with Lemma 4.5's continuous representative. -/
theorem suzukiHankelPhiGlobal_eq_continuousRepresentative
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) (x : ClosedInterval 0 a) :
    suzukiHankelPhiGlobal epsilon omega a homega ha (x : ℝ) =
      suzukiHankelPhiContinuous epsilon omega a homega ha x := by
  rw [suzukiHankelPhiGlobal, suzukiHankelPhiContinuous,
    ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    suzukiHankelBoundarySourceContinuous_apply,
    suzukiCompressedHankelContinuousOutput_eq_integral (by linarith) ha]
  rfl

/-- The global extension is pointwise real-valued on `[0,∞)`. -/
theorem suzukiHankelPhiGlobal_real
    (epsilon : SuzukiHankelSign) {omega a x : ℝ}
    (homega : 1 < omega) (ha : 1 < a) :
    (suzukiHankelPhiGlobal epsilon omega a homega ha x).im = 0 := by
  let homegaHalf : 1 / 2 < omega := by linarith
  rw [suzukiHankelPhiGlobal]
  apply Complex.conj_eq_iff_im.mp
  have hIntegral :
      (starRingEnd ℂ) (∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega (x * (y : ℝ)) *
          suzukiHankelPhi epsilon omega a homegaHalf ha y ∂volume) =
      ∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega (x * (y : ℝ)) *
          suzukiHankelPhi epsilon omega a homegaHalf ha y ∂volume := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [suzukiHankelPhi_real_ae epsilon homegaHalf ha] with y hy
    rw [map_mul, conj_suzukiSourceHFinite]
    exact congrArg (suzukiSourceHFinite omega (x * (y : ℝ)) * ·)
      (Complex.conj_eq_iff_im.mpr hy)
  have hcoeff : (starRingEnd ℂ) epsilon.coeff = epsilon.coeff := by
    simpa only [starRingEnd_apply] using SuzukiHankelSign.star_coeff epsilon
  rw [map_sub, conj_suzukiSourceHFinite, map_mul, hcoeff, hIntegral]

/-- Restriction of a continuous nonnegative-half-line function to Suzuki's compact interval. -/
def suzukiGlobalContinuousRestriction
    (a : ℝ) (X : C(Ici (0 : ℝ), ℂ)) : C(ClosedInterval 0 a, ℂ) where
  toFun y := X ⟨(y : ℝ), y.property.1⟩
  continuous_toFun := X.continuous.comp
    (continuous_subtype_val.subtype_mk fun y => y.property.1)

/-- Literal global form of Suzuki's equation (402), with the unknown itself under the integral. -/
def SuzukiHankelGlobalContinuousEquation
    (epsilon : SuzukiHankelSign) (omega a : ℝ)
    (X : C(Ici (0 : ℝ), ℂ)) : Prop :=
  ∀ x : Ici (0 : ℝ),
    X x + epsilon.coeff * ∫ y : ClosedInterval 0 a,
      suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
        suzukiGlobalContinuousRestriction a X y ∂volume =
      suzukiSourceHFinite omega (a * (x : ℝ))

/-- The continuous global extension satisfies equation (402) pointwise on `[0,∞)`. -/
theorem suzukiHankelPhiGlobalContinuous_equation
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) :
    SuzukiHankelGlobalContinuousEquation epsilon omega a
      (suzukiHankelPhiGlobalContinuous epsilon omega a homega ha) := by
  let homegaHalf : 1 / 2 < omega := by linarith
  intro x
  have hrest :
      (suzukiGlobalContinuousRestriction a
        (suzukiHankelPhiGlobalContinuous epsilon omega a homega ha) :
          ClosedInterval 0 a → ℂ) =ᵐ[volume]
        (suzukiHankelPhi epsilon omega a homegaHalf ha : ClosedInterval 0 a → ℂ) := by
    filter_upwards [suzukiHankelPhiContinuous_ae epsilon homega ha] with y hy
    change suzukiHankelPhiGlobal epsilon omega a homega ha (y : ℝ) = _
    rw [suzukiHankelPhiGlobal_eq_continuousRepresentative epsilon homega ha]
    exact hy
  have hIntegral :
      (∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          suzukiGlobalContinuousRestriction a
            (suzukiHankelPhiGlobalContinuous epsilon omega a homega ha) y ∂volume) =
      ∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          suzukiHankelPhi epsilon omega a homegaHalf ha y ∂volume := by
    apply integral_congr_ae
    filter_upwards [hrest] with y hy
    rw [hy]
  change suzukiHankelPhiGlobal epsilon omega a homega ha (x : ℝ) +
      epsilon.coeff * (∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          suzukiGlobalContinuousRestriction a
            (suzukiHankelPhiGlobalContinuous epsilon omega a homega ha) y ∂volume) = _
  rw [suzukiHankelPhiGlobal, hIntegral]
  ring

/-- `L²(0,a)` class of the compact restriction of a continuous global candidate. -/
def suzukiGlobalContinuousRestrictionL2
    (a : ℝ) (X : C(Ici (0 : ℝ), ℂ)) : IntervalL2 0 a :=
  ContinuousMap.toLp 2 volume ℂ (suzukiGlobalContinuousRestriction a X)

theorem suzukiGlobalContinuousRestrictionL2_ae
    (a : ℝ) (X : C(Ici (0 : ℝ), ℂ)) :
    (suzukiGlobalContinuousRestrictionL2 a X : ClosedInterval 0 a → ℂ) =ᵐ[volume]
      suzukiGlobalContinuousRestriction a X := by
  exact ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
    (μ := (volume : Measure (ClosedInterval 0 a)))
    (suzukiGlobalContinuousRestriction a X)

/-- Canonical `L²` restriction between nested compact intervals agrees with direct restriction of
a continuous half-line function. -/
theorem suzukiPhysicalIntervalRestrictionBetween_globalContinuousRestrictionL2
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (X : C(Ici (0 : ℝ), ℂ)) :
    suzukiPhysicalIntervalRestrictionBetween a b
        (suzukiGlobalContinuousRestrictionL2 b X) =
      suzukiGlobalContinuousRestrictionL2 a X := by
  let fB := suzukiGlobalContinuousRestrictionL2 b X
  let fA := suzukiGlobalContinuousRestrictionL2 a X
  let EB : SuzukiPositiveL2 := suzukiPhysicalIntervalPositiveIsometry b fB
  let Xfun : ℝ → ℂ := fun y => if hy : 0 ≤ y then X ⟨y, hy⟩ else 0
  have hBRepSub : ∀ᵐ y : ClosedInterval 0 b ∂volume,
      suzukiPhysicalIntervalZeroExtendFun fB (y : ℝ) =
        Xfun (y : ℝ) := by
    filter_upwards [suzukiPhysicalIntervalRepresentative_ae fB,
      suzukiGlobalContinuousRestrictionL2_ae b X] with y hrep hcoe
    rw [suzukiPhysicalIntervalZeroExtendFun_apply, hrep, hcoe]
    change X ⟨(y : ℝ), y.property.1⟩ =
      (if hy : 0 ≤ (y : ℝ) then X ⟨(y : ℝ), hy⟩ else 0)
    rw [dif_pos y.property.1]
  have hBRepReal : ∀ᵐ y ∂(volume : Measure ℝ).restrict (Icc 0 b),
      suzukiPhysicalIntervalZeroExtendFun fB y = Xfun y :=
    (ae_restrict_iff_subtype measurableSet_Icc).2 hBRepSub
  have hBRepWhole := (ae_restrict_iff' measurableSet_Icc).mp hBRepReal
  let hmp : MeasurePreserving ((↑) : ClosedInterval 0 a → ℝ)
      (volume : Measure (ClosedInterval 0 a))
      ((volume : Measure ℝ).restrict (Icc 0 a)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hEBReal := (ae_restrict_iff' measurableSet_Ioi).mp
    (suzukiPhysicalIntervalPositiveL2_ae fB)
  have hEBSub := hmp.quasiMeasurePreserving.ae (ae_restrict_of_ae hEBReal)
  have hBRepSubA := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae hBRepWhole)
  have hne := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae (volume.ae_ne (0 : ℝ)))
  apply Lp.ext
  filter_upwards [suzukiPositiveIntervalRestriction_value_ae EB,
    hEBSub, hBRepSubA, suzukiGlobalContinuousRestrictionL2_ae a X, hne] with
      y hres hEB hBRep hARep hne
  change suzukiPositiveIntervalRestriction a EB y = fA y
  rw [hres]
  have hypos : 0 < (y : ℝ) := lt_of_le_of_ne y.property.1 (Ne.symm hne)
  rw [show EB (y : ℝ) = suzukiPhysicalIntervalZeroExtendFun fB (y : ℝ) by
    exact hEB hypos, hBRep ⟨y.property.1, le_trans y.property.2 hab⟩, hARep]
  change (if hy : 0 ≤ (y : ℝ) then X ⟨(y : ℝ), hy⟩ else 0) =
    X ⟨(y : ℝ), y.property.1⟩
  rw [dif_pos y.property.1]

/-- The complex bilinear `L²` pairing is the Hilbert inner product against the conjugated first
argument. -/
theorem complexLpPairing_eq_inner_star
    {a : ℝ} (u v : IntervalL2 0 a) :
    (complexMulBilinear.lpPairing volume 2 2) u v = inner ℂ (star u) v := by
  rw [ContinuousLinearMap.lpPairing_eq_integral, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star u] with x hx
  rw [hx, Pi.star_apply]
  simp [complexMulBilinear, RCLike.inner_apply, mul_comm]

/-- Every literal compact Hankel row is fixed by conjugation. -/
theorem star_suzukiCompressedHankelRow
    {omega B x : ℝ} (homega : 1 / 2 < omega)
    (hB : 1 < B) (hx : 0 < x) (hxB : x ≤ B) :
    star (suzukiCompressedHankelRow omega B homega hB x) =
      suzukiCompressedHankelRow omega B homega hB x := by
  let row := suzukiCompressedHankelRow omega B homega hB x
  apply Lp.ext
  filter_upwards [Lp.coeFn_star row,
    suzukiCompressedHankelRow_ae homega hB hx hxB] with y hstar hrow
  change (star row : IntervalL2 0 B) y = row y
  rw [hstar, Pi.star_apply, hrow]
  simpa only [starRingEnd_apply] using
    conj_suzukiSourceHFinite omega (x * (y : ℝ))

/-- Restriction of a literal row remains fixed by conjugation. -/
theorem star_suzukiPhysicalIntervalRestrictionBetween_row
    {omega a B x : ℝ} (homega : 1 / 2 < omega)
    (ha : 0 < a) (hB : 1 < B) (haB : a ≤ B) (hx : 0 < x) (hxB : x ≤ B) :
    star (suzukiPhysicalIntervalRestrictionBetween a B
      (suzukiCompressedHankelRow omega B homega hB x)) =
      suzukiPhysicalIntervalRestrictionBetween a B
        (suzukiCompressedHankelRow omega B homega hB x) := by
  let row := suzukiPhysicalIntervalRestrictionBetween a B
    (suzukiCompressedHankelRow omega B homega hB x)
  apply Lp.ext
  filter_upwards [Lp.coeFn_star row,
    suzukiPhysicalIntervalRestrictionBetween_row_ae homega ha hB haB hx hxB] with
      y hstar hrow
  change (star row : IntervalL2 0 a) y = row y
  rw [hstar, Pi.star_apply, hrow]
  simpa only [starRingEnd_apply] using
    conj_suzukiSourceHFinite omega (x * (y : ℝ))

/-- Exact reduction of the larger-interval integral against a canonical zero extension to the
original interval. -/
theorem suzukiIntegral_physicalIntervalInclusion
    {omega a B : ℝ} (homega : 1 / 2 < omega)
    (ha : 0 < a) (hB : 1 < B) (haB : a ≤ B)
    (f : IntervalL2 0 a) (x : ClosedInterval 0 B) (hx : 0 < (x : ℝ)) :
    (∫ y : ClosedInterval 0 B,
      suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
        suzukiPhysicalIntervalInclusion a B f y ∂volume) =
      ∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) * f y ∂volume := by
  let rowB := suzukiCompressedHankelRow omega B homega hB (x : ℝ)
  let rowA := suzukiPhysicalIntervalRestrictionBetween a B rowB
  rw [← suzukiCompressedHankelContinuousOutput_eq_integral homega hB]
  change (complexMulBilinear.lpPairing volume 2 2) rowB
      (suzukiPhysicalIntervalInclusion a B f) = _
  calc
    (complexMulBilinear.lpPairing volume 2 2) rowB
        (suzukiPhysicalIntervalInclusion a B f) =
        inner ℂ rowB (suzukiPhysicalIntervalInclusion a B f) := by
      rw [complexLpPairing_eq_inner_star,
        star_suzukiCompressedHankelRow homega hB hx x.property.2]
    _ = (starRingEnd ℂ)
        (inner ℂ (suzukiPhysicalIntervalInclusion a B f) rowB) := by
      exact (inner_conj_symm rowB (suzukiPhysicalIntervalInclusion a B f)).symm
    _ = (starRingEnd ℂ) (inner ℂ f rowA) := by
      rw [inner_suzukiPhysicalIntervalInclusion ha haB]
    _ = inner ℂ rowA f := inner_conj_symm rowA f
    _ = (complexMulBilinear.lpPairing volume 2 2) rowA f := by
      rw [complexLpPairing_eq_inner_star,
        star_suzukiPhysicalIntervalRestrictionBetween_row homega ha hB haB hx x.property.2]
    _ = ∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) * f y ∂volume :=
      suzukiRestrictedLargeRow_pairing_eq_integral homega ha hB haB hx x.property.2 f

/-- Any continuous global solution of (402), restricted to `(0,a)`, solves the exact finite
Fredholm equation in `L²(0,a)`. -/
theorem suzukiGlobalContinuousRestrictionL2_resolvent_equation
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a)
    {X : C(Ici (0 : ℝ), ℂ)}
    (hX : SuzukiHankelGlobalContinuousEquation epsilon omega a X) :
    suzukiHankelResolventOperator epsilon omega a homega
        (suzukiGlobalContinuousRestrictionL2 a X) =
      suzukiHankelBoundarySource omega a homega ha := by
  let f := suzukiGlobalContinuousRestrictionL2 a X
  let T := suzukiCompressedHankelOperator omega a homega
  have hf : (f : ClosedInterval 0 a → ℂ) =ᵐ[volume]
      suzukiGlobalContinuousRestriction a X :=
    suzukiGlobalContinuousRestrictionL2_ae a X
  have heq : ∀ᵐ x : ClosedInterval 0 a ∂volume,
      f x + epsilon.coeff * ∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) * f y ∂volume =
          suzukiSourceHFinite omega (a * (x : ℝ)) := by
    filter_upwards [hf] with x hfx
    have hIntegral :
        (∫ y : ClosedInterval 0 a,
          suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) * f y ∂volume) =
        ∫ y : ClosedInterval 0 a,
          suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
            suzukiGlobalContinuousRestriction a X y ∂volume := by
      apply integral_congr_ae
      filter_upwards [hf] with y hy
      rw [hy]
    rw [hIntegral, hfx]
    exact hX ⟨(x : ℝ), x.property.1⟩
  change f + epsilon.coeff • T f = suzukiHankelBoundarySource omega a homega ha
  apply Lp.ext
  filter_upwards [Lp.coeFn_add f (epsilon.coeff • T f),
    Lp.coeFn_smul epsilon.coeff (T f),
    suzukiCompressedHankelOperator_coeFn omega a homega (by linarith) f,
    suzukiHankelBoundarySource_ae homega ha, heq] with
      x hadd hsmul hT hsource hxEq
  rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul, hT, hsource]
  exact hxEq

/-- Hence every continuous global solution has precisely Lemma 4.5's `L²(0,a)` restriction. -/
theorem suzukiGlobalContinuousRestrictionL2_eq_phi
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a)
    {X : C(Ici (0 : ℝ), ℂ)}
    (hX : SuzukiHankelGlobalContinuousEquation epsilon omega a X) :
    suzukiGlobalContinuousRestrictionL2 a X =
      suzukiHankelPhi epsilon omega a homega ha := by
  apply suzukiHankel_resolvent_unique epsilon homega ha
  exact suzukiGlobalContinuousRestrictionL2_resolvent_equation epsilon homega ha hX

/-- Uniqueness of Suzuki's continuous extended solution follows from finite Fredholm uniqueness,
not from building the explicit formula into the uniqueness predicate. -/
theorem suzukiHankelPhiGlobalContinuous_unique
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a)
    {X : C(Ici (0 : ℝ), ℂ)}
    (hX : SuzukiHankelGlobalContinuousEquation epsilon omega a X) :
    X = suzukiHankelPhiGlobalContinuous epsilon omega a homega ha := by
  let homegaHalf : 1 / 2 < omega := by linarith
  let G := suzukiHankelPhiGlobalContinuous epsilon omega a homega ha
  have hG : SuzukiHankelGlobalContinuousEquation epsilon omega a G :=
    suzukiHankelPhiGlobalContinuous_equation epsilon homega ha
  have hXL2 : suzukiGlobalContinuousRestrictionL2 a X =
      suzukiHankelPhi epsilon omega a homegaHalf ha :=
    suzukiGlobalContinuousRestrictionL2_eq_phi epsilon homegaHalf ha hX
  have hGL2 : suzukiGlobalContinuousRestrictionL2 a G =
      suzukiHankelPhi epsilon omega a homegaHalf ha :=
    suzukiGlobalContinuousRestrictionL2_eq_phi epsilon homegaHalf ha hG
  have hrest : (suzukiGlobalContinuousRestriction a X : ClosedInterval 0 a → ℂ) =ᵐ[volume]
      suzukiGlobalContinuousRestriction a G := by
    have hXrep := suzukiGlobalContinuousRestrictionL2_ae a X
    have hGrep := suzukiGlobalContinuousRestrictionL2_ae a G
    rw [hXL2] at hXrep
    rw [hGL2] at hGrep
    exact hXrep.symm.trans hGrep
  apply ContinuousMap.ext
  intro x
  have hIntegral :
      (∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          suzukiGlobalContinuousRestriction a X y ∂volume) =
      ∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          suzukiGlobalContinuousRestriction a G y ∂volume := by
    apply integral_congr_ae
    filter_upwards [hrest] with y hy
    rw [hy]
  have hxX : X x = suzukiSourceHFinite omega (a * (x : ℝ)) -
      epsilon.coeff * ∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          suzukiGlobalContinuousRestriction a X y ∂volume :=
    eq_sub_iff_add_eq.mpr (hX x)
  have hxG : G x = suzukiSourceHFinite omega (a * (x : ℝ)) -
      epsilon.coeff * ∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          suzukiGlobalContinuousRestriction a G y ∂volume :=
    eq_sub_iff_add_eq.mpr (hG x)
  rw [hxX, hxG, hIntegral]

/-- Every continuous half-line solution restricts on `[0,b]` to a solution of Suzuki's exact
larger-interval `L²` equation. -/
theorem suzukiGlobalContinuousRestrictionL2_extendedEquation
    (epsilon : SuzukiHankelSign) {omega a b : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a) (hab : a ≤ b)
    {X : C(Ici (0 : ℝ), ℂ)}
    (hX : SuzukiHankelGlobalContinuousEquation epsilon omega a X) :
    SuzukiHankelExtendedEquation epsilon omega a b homega ha hab
      (suzukiGlobalContinuousRestrictionL2 b X) := by
  let fB := suzukiGlobalContinuousRestrictionL2 b X
  let fA := suzukiGlobalContinuousRestrictionL2 a X
  let phi := suzukiHankelPhi epsilon omega a homega ha
  let T := suzukiCompressedHankelOperator omega b homega
  have hfA : fA = phi :=
    suzukiGlobalContinuousRestrictionL2_eq_phi epsilon homega ha hX
  have hres : suzukiPhysicalIntervalRestrictionBetween a b fB = phi := by
    rw [suzukiPhysicalIntervalRestrictionBetween_globalContinuousRestrictionL2
      (by linarith) hab]
    exact hfA
  have hphiX : (phi : ClosedInterval 0 a → ℂ) =ᵐ[volume]
      suzukiGlobalContinuousRestriction a X := by
    have hrep := suzukiGlobalContinuousRestrictionL2_ae a X
    change (fA : ClosedInterval 0 a → ℂ) =ᵐ[volume]
      suzukiGlobalContinuousRestriction a X at hrep
    rw [hfA] at hrep
    exact hrep
  rw [SuzukiHankelExtendedEquation, hres]
  change fB = suzukiHankelExtendedBoundary omega a b homega ha hab -
    epsilon.coeff • T (suzukiPhysicalIntervalInclusion a b phi)
  let hmpB : MeasurePreserving ((↑) : ClosedInterval 0 b → ℝ)
      (volume : Measure (ClosedInterval 0 b))
      ((volume : Measure ℝ).restrict (Icc 0 b)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hne := hmpB.quasiMeasurePreserving.ae
    (ae_restrict_of_ae (volume.ae_ne (0 : ℝ)))
  apply Lp.ext
  filter_upwards [suzukiGlobalContinuousRestrictionL2_ae b X,
    Lp.coeFn_sub (suzukiHankelExtendedBoundary omega a b homega ha hab)
      (epsilon.coeff • T (suzukiPhysicalIntervalInclusion a b phi)),
    Lp.coeFn_smul epsilon.coeff (T (suzukiPhysicalIntervalInclusion a b phi)),
    suzukiCompressedHankelOperator_coeFn omega b homega (by linarith)
      (suzukiPhysicalIntervalInclusion a b phi),
    suzukiHankelBoundarySourceOn_ae homega ha hab,
    hne] with
      x hfB hsub hsmul hT hboundary hxne
  rw [hfB, hsub, Pi.sub_apply, hsmul, Pi.smul_apply, smul_eq_mul, hT]
  change (suzukiGlobalContinuousRestriction b X) x =
    suzukiHankelBoundarySourceOn omega a b homega (lt_of_lt_of_le ha hab) x -
      epsilon.coeff * ∫ y : ClosedInterval 0 b,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          suzukiPhysicalIntervalInclusion a b phi y ∂volume
  rw [hboundary]
  have hxpos : 0 < (x : ℝ) :=
    lt_of_le_of_ne x.property.1 (Ne.symm hxne)
  have hIntegralA :
      (∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) * phi y ∂volume) =
      ∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          suzukiGlobalContinuousRestriction a X y ∂volume := by
    apply integral_congr_ae
    filter_upwards [hphiX] with y hy
    rw [hy]
  apply eq_sub_iff_add_eq.mpr
  rw [suzukiIntegral_physicalIntervalInclusion homega (by linarith)
    (by linarith) hab phi x hxpos, hIntegralA]
  exact hX ⟨(x : ℝ), x.property.1⟩

/-- Finite and global constructions in Lemma 4.6 are the same solution: every compact restriction
of formula (404.1) is exactly the previously constructed extended `L²` class. -/
theorem suzukiHankelPhiGlobalContinuous_restrictionL2
    (epsilon : SuzukiHankelSign) {omega a b : ℝ}
    (homega : 1 < omega) (ha : 1 < a) (hab : a ≤ b) :
    suzukiGlobalContinuousRestrictionL2 b
        (suzukiHankelPhiGlobalContinuous epsilon omega a homega ha) =
      suzukiHankelPhiExtended epsilon omega a b (by linarith) ha hab := by
  apply suzukiHankelPhiExtended_unique epsilon (by linarith) ha hab
  exact suzukiGlobalContinuousRestrictionL2_extendedEquation epsilon (by linarith) ha hab
    (suzukiHankelPhiGlobalContinuous_equation epsilon homega ha)

/-- **Suzuki (2012), Lemma 4.6, finite-interval clause, exact bundled form.** -/
theorem suzuki2012_lemma_four_six
    (epsilon : SuzukiHankelSign) {omega a b : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a) (hab : a < b) :
    SuzukiHankelExtendedEquation epsilon omega a b homega ha hab.le
        (suzukiHankelPhiExtended epsilon omega a b homega ha hab.le) ∧
    (∀ X : IntervalL2 0 b,
      SuzukiHankelExtendedEquation epsilon omega a b homega ha hab.le X →
      X = suzukiHankelPhiExtended epsilon omega a b homega ha hab.le) ∧
    (∀ᵐ x : ClosedInterval 0 b ∂volume,
      (suzukiHankelPhiExtended epsilon omega a b homega ha hab.le x).im = 0) ∧
    (suzukiPhysicalIntervalRestrictionBetween a b
        (suzukiHankelPhiExtended epsilon omega a b homega ha hab.le) =
      suzukiHankelPhi epsilon omega a homega ha) ∧
    (∀ᵐ x : ClosedInterval 0 b ∂volume,
      suzukiHankelPhiExtended epsilon omega a b homega ha hab.le x +
          epsilon.coeff * ∫ y : ClosedInterval 0 b,
            suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
              suzukiPhysicalIntervalInclusion a b
                (suzukiHankelPhi epsilon omega a homega ha) y ∂volume =
        suzukiSourceHFinite omega (a * (x : ℝ))) := by
  exact ⟨suzukiHankelPhiExtended_equation epsilon homega ha hab.le,
    fun _ hX => suzukiHankelPhiExtended_unique epsilon homega ha hab.le hX,
    suzukiHankelPhiExtended_real_ae epsilon homega ha hab.le,
    suzukiHankelPhiExtended_restriction epsilon homega ha hab.le,
    suzukiHankelPhiExtended_integral_equation_ae epsilon homega ha hab.le⟩

/-- **Suzuki (2012), Lemma 4.6, continuous clause.**  The formal result is stronger at the
endpoint: the unique solution is continuous and real on all of `[0,∞)`, not only continuous on
`(0,∞)`. -/
theorem suzuki2012_lemma_four_six_continuous
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) :
    SuzukiHankelGlobalContinuousEquation epsilon omega a
        (suzukiHankelPhiGlobalContinuous epsilon omega a homega ha) ∧
    (∀ X : C(Ici (0 : ℝ), ℂ),
      SuzukiHankelGlobalContinuousEquation epsilon omega a X →
      X = suzukiHankelPhiGlobalContinuous epsilon omega a homega ha) ∧
    (∀ x : Ici (0 : ℝ),
      (suzukiHankelPhiGlobalContinuous epsilon omega a homega ha x).im = 0) ∧
    (∀ x : ClosedInterval 0 a,
      suzukiHankelPhiGlobalContinuous epsilon omega a homega ha
          ⟨(x : ℝ), x.property.1⟩ =
        suzukiHankelPhiContinuous epsilon omega a homega ha x) ∧
    (∀ x : Ici (0 : ℝ), (x : ℝ) ≤ 1 / a →
      suzukiHankelPhiGlobalContinuous epsilon omega a homega ha x = 0) := by
  exact ⟨suzukiHankelPhiGlobalContinuous_equation epsilon homega ha,
    fun _ hX => suzukiHankelPhiGlobalContinuous_unique epsilon homega ha hX,
    fun x => suzukiHankelPhiGlobal_real epsilon homega ha,
    fun x => suzukiHankelPhiGlobal_eq_continuousRepresentative epsilon homega ha x,
    fun x hx => suzukiHankelPhiGlobal_eq_zero_below_reciprocal epsilon homega ha x.property hx⟩

end RHTower
