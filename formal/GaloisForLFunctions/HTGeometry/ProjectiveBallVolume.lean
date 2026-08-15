import Mathlib

/-!
# The uniform measure of a projective ball

The uniform probability of a ball in complex projective space is the normalized Lebesgue volume of
the cone it spans, intersected with the unit ball.  That cone is invariant under the unitary group,
which acts by real-linear maps of determinant one, so the computation may be made at one coordinate
centre.

There the cone is a union of Euclidean balls of one lower complex dimension whose radius is the
minimum of the cone radius and the ball radius, and integrating that radius in plane polar
coordinates leaves two elementary one-variable integrals.
-/

open MeasureTheory Metric Set
open scoped Pointwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section SquaredNorm

variable {n : ℕ}

/-- Squared Euclidean norm of a complex tuple. -/
def sqNorm (x : Fin n → ℂ) : ℝ := ∑ i, ‖x i‖ ^ 2

theorem sqNorm_nonneg (x : Fin n → ℂ) : 0 ≤ sqNorm x := by
  refine Finset.sum_nonneg fun i _ => by positivity

theorem sqNorm_smul (c : ℝ) (x : Fin n → ℂ) : sqNorm (c • x) = c ^ 2 * sqNorm x := by
  rw [sqNorm, sqNorm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ‖(c : ℂ) * x i‖ ^ 2 = _
  rw [norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]

theorem finrank_pi_complex (n : ℕ) : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

/-- The sublevel sets of the squared norm are the scalings of the unit ball. -/
theorem sqNorm_le_eq_smul {t : ℝ} (ht : 0 < t) :
    {x : Fin n → ℂ | sqNorm x ≤ t} =
      Real.sqrt t • {x : Fin n → ℂ | sqNorm x ≤ 1} := by
  ext x
  constructor
  · intro hx
    refine ⟨(Real.sqrt t)⁻¹ • x, ?_, ?_⟩
    · show sqNorm ((Real.sqrt t)⁻¹ • x) ≤ 1
      rw [sqNorm_smul]
      have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
      have hpos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
      rw [inv_pow, hsq, inv_mul_le_one₀ ht]
      exact hx
    · show Real.sqrt t • ((Real.sqrt t)⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr ht)), one_smul]
  · rintro ⟨y, hy, rfl⟩
    show sqNorm (Real.sqrt t • y) ≤ t
    rw [sqNorm_smul, Real.sq_sqrt ht.le]
    have hy' : sqNorm y ≤ 1 := hy
    nlinarith [sqNorm_nonneg y, ht.le, hy']

theorem measurable_sqNorm : Measurable (sqNorm : (Fin n → ℂ) → ℝ) := by
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_pi_apply i).norm).pow_const 2

theorem measurableSet_sqNorm_le (t : ℝ) :
    MeasurableSet {x : Fin n → ℂ | sqNorm x ≤ t} :=
  measurable_sqNorm measurableSet_Iic

/-- **Scaling law for the squared-norm sublevel volume.** -/
theorem volume_sqNorm_le {t : ℝ} (ht : 0 ≤ t) :
    volume {x : Fin n → ℂ | sqNorm x ≤ t} =
      ENNReal.ofReal (t ^ n) * volume {x : Fin n → ℂ | sqNorm x ≤ 1} := by
  rcases eq_or_lt_of_le ht with rfl | htpos
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · have huniv : {x : Fin 0 → ℂ | sqNorm x ≤ (0 : ℝ)} = Set.univ := by
        ext x
        simp [sqNorm]
      have huniv1 : {x : Fin 0 → ℂ | sqNorm x ≤ (1 : ℝ)} = Set.univ := by
        ext x
        simp [sqNorm]
      rw [huniv, huniv1]
      simp
    · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      haveI : Nontrivial (Fin n → ℂ) := by infer_instance
      have hzero : {x : Fin n → ℂ | sqNorm x ≤ (0 : ℝ)} = {0} := by
        ext x
        constructor
        · intro hx
          have hle : sqNorm x ≤ 0 := hx
          have hge : 0 ≤ sqNorm x := sqNorm_nonneg x
          have hsum : sqNorm x = 0 := le_antisymm hle hge
          have hterm : ∀ i : Fin n, ‖x i‖ ^ 2 = 0 := by
            intro i
            refine le_antisymm ?_ (by positivity)
            have := Finset.single_le_sum (f := fun i : Fin n => ‖x i‖ ^ 2)
              (fun j _ => by positivity) (Finset.mem_univ i)
            rw [← sqNorm, hsum] at this
            exact this
          funext i
          have := hterm i
          have hnorm : ‖x i‖ = 0 := by nlinarith [norm_nonneg (x i), this]
          simpa using hnorm
        · rintro rfl
          show sqNorm (0 : Fin n → ℂ) ≤ 0
          simp [sqNorm]
      rw [hzero, measure_singleton, zero_pow (by omega)]
      simp
  · rw [sqNorm_le_eq_smul htpos,
      Measure.addHaar_smul volume (Real.sqrt t) {x : Fin n → ℂ | sqNorm x ≤ 1},
      finrank_pi_complex]
    congr 1
    congr 1
    rw [abs_of_nonneg (by positivity), pow_mul, Real.sq_sqrt htpos.le]


/-- Scaling law in the form that also covers negative levels. -/
theorem volume_sqNorm_le' (hn : 0 < n) (t : ℝ) :
    volume {x : Fin n → ℂ | sqNorm x ≤ t} =
      (ENNReal.ofReal t) ^ n * volume {x : Fin n → ℂ | sqNorm x ≤ 1} := by
  by_cases ht : 0 ≤ t
  · rw [volume_sqNorm_le ht, ← ENNReal.ofReal_pow ht]
  · have ht' : t < 0 := not_le.mp ht
    have hempty : {x : Fin n → ℂ | sqNorm x ≤ t} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le ht' (sqNorm_nonneg x)
    rw [hempty, measure_empty, ENNReal.ofReal_of_nonpos ht'.le, zero_pow (by omega), zero_mul]

end SquaredNorm

section ConeSlice

variable {n : ℕ}

/-- The cone over a projective ball centred on the first coordinate axis, cut by the unit ball. -/
def coneBallSet (n : ℕ) (s : ℝ) : Set (Fin (n + 1) → ℂ) :=
  {x | sqNorm x ≤ 1 ∧ s * sqNorm x ≤ ‖x 0‖ ^ 2}

/-- The squared radius of the slice of the cone above one first-coordinate value. -/
def sliceLevel (s a : ℝ) : ℝ := min (1 - a ^ 2) (((1 - s) / s) * a ^ 2)

theorem sqNorm_succ (x : Fin (n + 1) → ℂ) :
    sqNorm x = ‖x 0‖ ^ 2 + sqNorm (fun j : Fin n => x j.succ) := by
  rw [sqNorm, sqNorm, Fin.sum_univ_succ]

theorem measurableSet_coneProduct (s : ℝ) :
    MeasurableSet {p : ℂ × (Fin n → ℂ) |
      ‖p.1‖ ^ 2 + sqNorm p.2 ≤ 1 ∧ s * (‖p.1‖ ^ 2 + sqNorm p.2) ≤ ‖p.1‖ ^ 2} := by
  have h1 : Measurable fun p : ℂ × (Fin n → ℂ) => ‖p.1‖ ^ 2 + sqNorm p.2 :=
    (measurable_fst.norm.pow_const 2).add (measurable_sqNorm.comp measurable_snd)
  have h2 : Measurable fun p : ℂ × (Fin n → ℂ) => ‖p.1‖ ^ 2 :=
    measurable_fst.norm.pow_const 2
  exact (h1 measurableSet_Iic).inter (measurableSet_le (h1.const_mul s) h2)

/-- **Slice decomposition of the cone.**  The cone over a projective ball is the union of Euclidean
balls of one lower complex dimension, whose squared radius is the smaller of the ball level and the
cone level. -/
theorem volume_coneBallSet (hn : 0 < n) {s : ℝ} (hs : 0 < s) :
    volume (coneBallSet n s) =
      (∫⁻ u : ℂ, (ENNReal.ofReal (sliceLevel s ‖u‖)) ^ n) *
        volume {y : Fin n → ℂ | sqNorm y ≤ 1} := by
  classical
  set A : Set (ℂ × (Fin n → ℂ)) := {p |
    ‖p.1‖ ^ 2 + sqNorm p.2 ≤ 1 ∧ s * (‖p.1‖ ^ 2 + sqNorm p.2) ≤ ‖p.1‖ ^ 2} with hA
  have hAmeas : MeasurableSet A := measurableSet_coneProduct s
  have hpres := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0
  have hpre : coneBallSet n s =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0) ⁻¹' A := by
    ext x
    show (sqNorm x ≤ 1 ∧ s * sqNorm x ≤ ‖x 0‖ ^ 2) ↔ _
    rw [hA]
    show _ ↔ (‖x 0‖ ^ 2 + sqNorm (fun j : Fin n => x j.succ) ≤ 1 ∧
      s * (‖x 0‖ ^ 2 + sqNorm (fun j : Fin n => x j.succ)) ≤ ‖x 0‖ ^ 2)
    rw [← sqNorm_succ]
  rw [hpre, hpres.measure_preimage hAmeas.nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_apply hAmeas]
  have hslice : ∀ u : ℂ, (Prod.mk u ⁻¹' A) = {y : Fin n → ℂ | sqNorm y ≤ sliceLevel s ‖u‖} := by
    intro u
    ext y
    show (‖u‖ ^ 2 + sqNorm y ≤ 1 ∧ s * (‖u‖ ^ 2 + sqNorm y) ≤ ‖u‖ ^ 2) ↔
      sqNorm y ≤ sliceLevel s ‖u‖
    have hrewrite : ((1 - s) / s) * ‖u‖ ^ 2 = ((1 - s) * ‖u‖ ^ 2) / s :=
      div_mul_eq_mul_div _ _ _
    rw [sliceLevel, le_min_iff, hrewrite, le_div_iff₀ hs]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by nlinarith [h2]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by nlinarith [h2]⟩
  have hpoint : ∀ u : ℂ, volume (Prod.mk u ⁻¹' A) =
      (ENNReal.ofReal (sliceLevel s ‖u‖)) ^ n * volume {y : Fin n → ℂ | sqNorm y ≤ 1} := by
    intro u
    rw [hslice u, volume_sqNorm_le' hn]
  simp_rw [hpoint]
  rw [lintegral_mul_const _ (by
    refine Measurable.pow_const ?_ n
    exact ENNReal.measurable_ofReal.comp
      (((measurable_norm.pow_const 2).const_sub 1).min
        ((measurable_norm.pow_const 2).const_mul _)))]

end ConeSlice

section Radial

/-- **Radial reduction.**  A radial nonnegative function integrates over the plane as its
one-dimensional radial integral times the full angle. -/
theorem lintegral_radial (f : ℝ → ENNReal) (hf : Measurable f) :
    (∫⁻ z : ℂ, f ‖z‖) =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ a in Set.Ioi (0 : ℝ), ENNReal.ofReal a * f a := by
  have hpolar := Complex.lintegral_comp_polarCoord_symm (fun z : ℂ => f ‖z‖)
  rw [← hpolar]
  have hnorm : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • f ‖Complex.polarCoord.symm p‖ = ENNReal.ofReal p.1 * f p.1 := by
    rintro ⟨a, θ⟩ ⟨ha, -⟩
    have ha' : (0 : ℝ) < a := ha
    have hunit : ‖((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)‖ = 1 := by
      have hexp : ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) =
          Complex.exp ((θ : ℂ) * Complex.I) := by
        rw [Complex.exp_mul_I]
        simp
      rw [hexp, Complex.norm_exp]
      simp
    have hn : ‖Complex.polarCoord.symm (a, θ)‖ = a := by
      rw [Complex.polarCoord_symm_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ha', hunit, mul_one]
    rw [hn, smul_eq_mul]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hnorm]
  have htarget : polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi := rfl
  rw [htarget, Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [lintegral_prod _ (by
    refine (ENNReal.measurable_ofReal.comp measurable_fst).mul (hf.comp measurable_fst)
      |>.aemeasurable)]
  have hinner : ∀ a : ℝ, (∫⁻ _θ in Set.Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal a * f a) = ENNReal.ofReal (2 * Real.pi) * (ENNReal.ofReal a * f a) := by
    intro a
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
    rw [mul_comm]
    congr 1
    congr 1
    ring
  simp_rw [hinner]
  rw [lintegral_const_mul (ENNReal.ofReal (2 * Real.pi))
    (f := fun a : ℝ => ENNReal.ofReal a * f a) (ENNReal.measurable_ofReal.mul hf)]

end Radial

section RadialIntegrals

variable {n : ℕ}

theorem hasDerivAt_ballPrimitive (n : ℕ) (a : ℝ) :
    HasDerivAt (fun x : ℝ => -(1 - x ^ 2) ^ (n + 1) / (2 * ((n : ℝ) + 1)))
      (a * (1 - a ^ 2) ^ n) a := by
  have hbase : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * a)) a := by
    have h := (hasDerivAt_pow 2 a).const_sub 1
    simpa using h
  have hpow := hbase.pow (n + 1)
  simp only [Nat.add_sub_cancel] at hpow
  have hneg := hpow.neg
  have hdiv := hneg.div_const (2 * ((n : ℝ) + 1))
  refine hdiv.congr_deriv ?_
  have hne : (2 : ℝ) * ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

theorem integral_ball_primitive (n : ℕ) (b : ℝ) :
    (∫ a in (0 : ℝ)..b, a * (1 - a ^ 2) ^ n) =
      (1 - (1 - b ^ 2) ^ (n + 1)) / (2 * ((n : ℝ) + 1)) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_ballPrimitive n x)
    ((continuous_id.mul (((continuous_const.sub (continuous_pow 2))).pow n)).intervalIntegrable
      _ _)]
  simp
  ring

theorem integral_cone_primitive (n : ℕ) (k b : ℝ) :
    (∫ a in (0 : ℝ)..b, k ^ n * a ^ (2 * n + 1)) =
      k ^ n * b ^ (2 * n + 2) / (2 * ((n : ℝ) + 1)) := by
  rw [intervalIntegral.integral_const_mul, integral_pow]
  have hcast : ((2 * n + 1 : ℕ) : ℝ) + 1 = 2 * ((n : ℝ) + 1) := by
    push_cast
    ring
  rw [hcast, zero_pow (by omega)]
  ring


theorem lintegral_ofReal_indicator (g : ℝ → ℝ)
    (hg : ∀ a ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ g a) (hcont : ContinuousOn g (Set.Icc 0 1))
    (hzero : ∀ a : ℝ, 1 ≤ a → ENNReal.ofReal a * (ENNReal.ofReal (g a)) ^ n = 0)
    (hpos : ∀ a ∈ Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal a * (ENNReal.ofReal (g a)) ^ n = ENNReal.ofReal (a * g a ^ n)) :
    (∫⁻ a in Set.Ioi (0 : ℝ), ENNReal.ofReal a * (ENNReal.ofReal (g a)) ^ n) =
      ENNReal.ofReal (∫ a in (0 : ℝ)..1, a * g a ^ n) := by
  classical
  have hfun : ∀ a ∈ Set.Ioi (0 : ℝ),
      ENNReal.ofReal a * (ENNReal.ofReal (g a)) ^ n =
        Set.indicator (Set.Ioo (0 : ℝ) 1) (fun a => ENNReal.ofReal (a * g a ^ n)) a := by
    intro a ha
    have ha' : (0 : ℝ) < a := ha
    by_cases h1 : a < 1
    · have hmem : a ∈ Set.Ioo (0 : ℝ) 1 := ⟨ha', h1⟩
      rw [Set.indicator_of_mem hmem]
      exact hpos a hmem
    · rw [Set.indicator_of_notMem (fun hmem => h1 hmem.2)]
      exact hzero a (not_lt.mp h1)
  rw [setLIntegral_congr_fun measurableSet_Ioi hfun,
    lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]
  have hsub : Set.Ioo (0 : ℝ) 1 ∩ Set.Ioi 0 = Set.Ioo (0 : ℝ) 1 := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ioi]
    tauto
  rw [hsub]
  have hcontOn : ContinuousOn (fun a : ℝ => a * g a ^ n) (Set.Icc 0 1) :=
    continuousOn_id.mul (hcont.pow n)
  have hint : IntegrableOn (fun a : ℝ => a * g a ^ n) (Set.Ioo (0 : ℝ) 1) :=
    (hcontOn.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] fun a : ℝ => a * g a ^ n := by
    refine (ae_restrict_iff' measurableSet_Ioo).mpr ?_
    refine Filter.Eventually.of_forall fun a ha => ?_
    have h1 : (0 : ℝ) ≤ a := le_of_lt ha.1
    have h2 : (0 : ℝ) ≤ g a := hg a ha
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Ioc_eq_integral_Ioo]


theorem lintegral_radial_ball (hn : 0 < n) :
    (∫⁻ a in Set.Ioi (0 : ℝ), ENNReal.ofReal a * (ENNReal.ofReal (1 - a ^ 2)) ^ n) =
      ENNReal.ofReal (1 / (2 * ((n : ℝ) + 1))) := by
  rw [lintegral_ofReal_indicator (fun a => 1 - a ^ 2)
    (fun a ha => by nlinarith [ha.1, ha.2])
    ((continuous_const.sub (continuous_pow 2)).continuousOn)
    (fun a ha => by
      have h1 : 1 - a ^ 2 ≤ 0 := by nlinarith [ha]
      rw [ENNReal.ofReal_of_nonpos h1, zero_pow (by omega), mul_zero])
    (fun a ha => by
      have h1 : (0 : ℝ) ≤ 1 - a ^ 2 := by nlinarith [ha.1, ha.2]
      rw [← ENNReal.ofReal_pow h1, ← ENNReal.ofReal_mul (le_of_lt ha.1)])]
  rw [integral_ball_primitive n 1]
  norm_num

theorem sliceLevel_nonneg {s a : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha0 : 0 < a) (ha1 : a < 1) :
    0 ≤ sliceLevel s a := by
  rw [sliceLevel, le_min_iff]
  constructor
  · nlinarith [ha0, ha1]
  · have : (0 : ℝ) < (1 - s) / s := div_pos (by linarith) hs0
    positivity

theorem continuous_sliceLevel (s : ℝ) : Continuous (sliceLevel s) :=
  (continuous_const.sub (continuous_pow 2)).min (continuous_const.mul (continuous_pow 2))

theorem continuousOn_sliceLevel (s : ℝ) : ContinuousOn (sliceLevel s) (Set.Icc 0 1) :=
  (continuous_sliceLevel s).continuousOn

theorem sliceLevel_eq_cone {s a : ℝ} (hs0 : 0 < s) (ha : a ^ 2 ≤ s) :
    sliceLevel s a = ((1 - s) / s) * a ^ 2 := by
  rw [sliceLevel, min_eq_right]
  rw [div_mul_eq_mul_div, div_le_iff₀ hs0]
  nlinarith [ha]

theorem sliceLevel_eq_ball {s a : ℝ} (hs0 : 0 < s) (ha : s ≤ a ^ 2) :
    sliceLevel s a = 1 - a ^ 2 := by
  rw [sliceLevel, min_eq_left]
  rw [div_mul_eq_mul_div, le_div_iff₀ hs0]
  nlinarith [ha]

theorem lintegral_radial_cone (hn : 0 < n) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (∫⁻ a in Set.Ioi (0 : ℝ), ENNReal.ofReal a * (ENNReal.ofReal (sliceLevel s a)) ^ n) =
      ENNReal.ofReal ((1 - s) ^ n / (2 * ((n : ℝ) + 1))) := by
  rw [lintegral_ofReal_indicator (sliceLevel s)
    (fun a ha => sliceLevel_nonneg hs0 hs1 ha.1 ha.2)
    (continuousOn_sliceLevel s)
    (fun a ha => by
      have h1 : sliceLevel s a ≤ 0 := by
        rw [sliceLevel]
        refine le_trans (min_le_left _ _) ?_
        nlinarith [ha]
      rw [ENNReal.ofReal_of_nonpos h1, zero_pow (by omega), mul_zero])
    (fun a ha => by
      have h1 : (0 : ℝ) ≤ sliceLevel s a := sliceLevel_nonneg hs0 hs1 ha.1 ha.2
      rw [← ENNReal.ofReal_pow h1, ← ENNReal.ofReal_mul (le_of_lt ha.1)])]
  congr 1
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0.le
  have hsqpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  have hsqlt : Real.sqrt s < 1 := by
    nlinarith [hsq, hsqpos]
  have hcont : ContinuousOn (fun a : ℝ => a * sliceLevel s a ^ n) (Set.Icc 0 1) :=
    continuousOn_id.mul ((continuousOn_sliceLevel s).pow n)
  have hint1 : IntervalIntegrable (fun a : ℝ => a * sliceLevel s a ^ n) volume 0
      (Real.sqrt s) := by
    refine (hcont.mono ?_).intervalIntegrable_of_Icc hsqpos.le
    exact Set.Icc_subset_Icc le_rfl hsqlt.le
  have hint2 : IntervalIntegrable (fun a : ℝ => a * sliceLevel s a ^ n) volume
      (Real.sqrt s) 1 := by
    refine (hcont.mono ?_).intervalIntegrable_of_Icc hsqlt.le
    exact Set.Icc_subset_Icc hsqpos.le le_rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have hfirst : (∫ a in (0 : ℝ)..Real.sqrt s, a * sliceLevel s a ^ n) =
      ∫ a in (0 : ℝ)..Real.sqrt s, ((1 - s) / s) ^ n * a ^ (2 * n + 1) := by
    refine intervalIntegral.integral_congr fun a ha => ?_
    rw [Set.uIcc_of_le hsqpos.le] at ha
    have ha2 : a ^ 2 ≤ s := by
      have h1 : 0 ≤ a := ha.1
      have h2 : a ≤ Real.sqrt s := ha.2
      nlinarith [hsq]
    show a * sliceLevel s a ^ n = _
    rw [sliceLevel_eq_cone hs0 ha2, mul_pow, ← pow_mul]
    ring_nf
  have hsecond : (∫ a in (Real.sqrt s : ℝ)..1, a * sliceLevel s a ^ n) =
      ∫ a in (Real.sqrt s : ℝ)..1, a * (1 - a ^ 2) ^ n := by
    refine intervalIntegral.integral_congr fun a ha => ?_
    rw [Set.uIcc_of_le hsqlt.le] at ha
    have ha2 : s ≤ a ^ 2 := by
      have h1 : Real.sqrt s ≤ a := ha.1
      nlinarith [hsq, hsqpos]
    show a * sliceLevel s a ^ n = _
    rw [sliceLevel_eq_ball hs0 ha2]
  rw [hfirst, hsecond, integral_cone_primitive n ((1 - s) / s) (Real.sqrt s)]
  have hball1 : (∫ a in (Real.sqrt s : ℝ)..1, a * (1 - a ^ 2) ^ n) =
      (1 - s) ^ (n + 1) / (2 * ((n : ℝ) + 1)) := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (a := (0 : ℝ)) (b := Real.sqrt s) (c := 1)
      (f := fun a : ℝ => a * (1 - a ^ 2) ^ n) (μ := volume)
      ((continuous_id.mul ((continuous_const.sub (continuous_pow 2)).pow n)).intervalIntegrable _ _)
      ((continuous_id.mul ((continuous_const.sub (continuous_pow 2)).pow n)).intervalIntegrable _ _)
    rw [integral_ball_primitive n (Real.sqrt s), integral_ball_primitive n 1, hsq] at hsplit
    norm_num at hsplit
    have hne : (2 : ℝ) * ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp at hsplit ⊢
    linarith [hsplit]
  have hsqpow : Real.sqrt s ^ (2 * n + 2) = s ^ (n + 1) := by
    rw [show 2 * n + 2 = 2 * (n + 1) by ring, pow_mul, hsq]
  rw [hball1, hsqpow, div_pow]
  have hne : (2 : ℝ) * ((n : ℝ) + 1) ≠ 0 := by positivity
  have hspow : (s : ℝ) ^ n ≠ 0 := pow_ne_zero n (ne_of_gt hs0)
  field_simp
  ring

end RadialIntegrals

section Assembly

variable {n : ℕ}

theorem volume_ballSet_succ (hn : 0 < n) :
    volume {x : Fin (n + 1) → ℂ | sqNorm x ≤ 1} =
      (∫⁻ u : ℂ, (ENNReal.ofReal (1 - ‖u‖ ^ 2)) ^ n) *
        volume {y : Fin n → ℂ | sqNorm y ≤ 1} := by
  classical
  set A : Set (ℂ × (Fin n → ℂ)) := {p | ‖p.1‖ ^ 2 + sqNorm p.2 ≤ 1} with hA
  have hAmeas : MeasurableSet A := by
    have h1 : Measurable fun p : ℂ × (Fin n → ℂ) => ‖p.1‖ ^ 2 + sqNorm p.2 :=
      (measurable_fst.norm.pow_const 2).add (measurable_sqNorm.comp measurable_snd)
    exact h1 measurableSet_Iic
  have hpres := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0
  have hpre : {x : Fin (n + 1) → ℂ | sqNorm x ≤ 1} =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0) ⁻¹' A := by
    ext x
    show sqNorm x ≤ 1 ↔ _
    rw [hA]
    show _ ↔ ‖x 0‖ ^ 2 + sqNorm (fun j : Fin n => x j.succ) ≤ 1
    rw [← sqNorm_succ]
  rw [hpre, hpres.measure_preimage hAmeas.nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_apply hAmeas]
  have hpoint : ∀ u : ℂ, volume (Prod.mk u ⁻¹' A) =
      (ENNReal.ofReal (1 - ‖u‖ ^ 2)) ^ n * volume {y : Fin n → ℂ | sqNorm y ≤ 1} := by
    intro u
    have hslice : (Prod.mk u ⁻¹' A) = {y : Fin n → ℂ | sqNorm y ≤ 1 - ‖u‖ ^ 2} := by
      ext y
      show ‖u‖ ^ 2 + sqNorm y ≤ 1 ↔ sqNorm y ≤ 1 - ‖u‖ ^ 2
      constructor <;> intro h <;> linarith
    rw [hslice, volume_sqNorm_le' hn]
  simp_rw [hpoint]
  rw [lintegral_mul_const _ (by
    refine Measurable.pow_const ?_ n
    exact ENNReal.measurable_ofReal.comp ((measurable_norm.pow_const 2).const_sub 1))]

/-- **Uniform measure of a projective ball at a coordinate centre.**  The cone over a projective
ball around the first coordinate axis fills exactly the prescribed fraction of the unit ball. -/
theorem volume_coneBallSet_eq (hn : 0 < n) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    volume (coneBallSet n s) =
      ENNReal.ofReal ((1 - s) ^ n) * volume {x : Fin (n + 1) → ℂ | sqNorm x ≤ 1} := by
  have hcone := volume_coneBallSet hn hs0
  have hball := volume_ballSet_succ (n := n) hn
  have hradial1 : (∫⁻ u : ℂ, (ENNReal.ofReal (sliceLevel s ‖u‖)) ^ n) =
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal ((1 - s) ^ n / (2 * ((n : ℝ) + 1))) := by
    rw [lintegral_radial (fun a => (ENNReal.ofReal (sliceLevel s a)) ^ n)
      ((ENNReal.measurable_ofReal.comp (continuous_sliceLevel s).measurable).pow_const n),
      lintegral_radial_cone hn hs0 hs1]
  have hradial2 : (∫⁻ u : ℂ, (ENNReal.ofReal (1 - ‖u‖ ^ 2)) ^ n) =
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (1 / (2 * ((n : ℝ) + 1))) := by
    rw [lintegral_radial (fun a => (ENNReal.ofReal (1 - a ^ 2)) ^ n)
      ((ENNReal.measurable_ofReal.comp ((measurable_id.pow_const 2).const_sub 1)).pow_const n),
      lintegral_radial_ball hn]
  rw [hcone, hradial1, hball, hradial2]
  have hnn : (0 : ℝ) ≤ (1 - s) ^ n := by positivity
  have hden : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
  have hsplit : ((1 - s) ^ n / (2 * ((n : ℝ) + 1))) = (1 - s) ^ n * (1 / (2 * ((n : ℝ) + 1))) := by
    field_simp
  rw [hsplit, ENNReal.ofReal_mul hnn]
  ring

end Assembly

section GeneralCentre

open scoped Matrix

variable {n : ℕ}

/-- The Hermitian pairing of two complex tuples. -/
def innerC (φ x : Fin n → ℂ) : ℂ := ∑ i, (starRingEnd ℂ) (φ i) * x i

theorem innerC_self (x : Fin n → ℂ) : innerC x x = (sqNorm x : ℂ) := by
  rw [innerC, sqNorm]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

theorem innerC_mulVec {U : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1) (x y : Fin n → ℂ) :
    innerC (U.mulVec x) (U.mulVec y) = innerC x y := by
  classical
  have hexpand : innerC (U.mulVec x) (U.mulVec y) =
      ∑ j, ∑ k, (starRingEnd ℂ) (x j) * y k * (Uᴴ * U) j k := by
    rw [innerC]
    have hterm : ∀ i : Fin n,
        (starRingEnd ℂ) ((U.mulVec x) i) * (U.mulVec y) i =
          ∑ j, ∑ k, (starRingEnd ℂ) (U i j) * (starRingEnd ℂ) (x j) * (U i k * y k) := by
      intro i
      rw [Matrix.mulVec, Matrix.mulVec]
      show (starRingEnd ℂ) (∑ j, U i j * x j) * (∑ k, U i k * y k) = _
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.conjTranspose_apply, Complex.star_def]
    ring
  rw [hexpand, hU]
  rw [innerC]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j]
  · rw [Matrix.one_apply_eq, mul_one]
  · intro k _ hkj
    rw [Matrix.one_apply_ne (Ne.symm hkj), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem sqNorm_mulVec {U : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1) (x : Fin n → ℂ) :
    sqNorm (U.mulVec x) = sqNorm x := by
  have h := innerC_mulVec hU x x
  rw [innerC_self, innerC_self] at h
  exact_mod_cast h

theorem det_unitary_norm {U : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1) :
    Complex.normSq U.det = 1 := by
  have h := congrArg Matrix.det hU
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
  have hc : ((Complex.normSq U.det : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    simpa using h
  exact_mod_cast hc

theorem volume_preimage_mulVec {U : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1)
    (s : Set (Fin n → ℂ)) : volume (U.mulVec ⁻¹' s) = volume s := by
  have hdet : LinearMap.det ((Matrix.toLin' U).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]
    exact det_unitary_norm hU
  have hmap : ⇑((Matrix.toLin' U).restrictScalars ℝ) = U.mulVec := by
    funext x
    rfl
  rw [← hmap, Measure.addHaar_preimage_linearMap volume (by rw [hdet]; norm_num) s, hdet]
  simp

/-- The cone over the projective ball of squared cosine level `s` at a general centre. -/
def coneBallAt (n : ℕ) (φ : Fin n → ℂ) (s : ℝ) : Set (Fin n → ℂ) :=
  {x | sqNorm x ≤ 1 ∧ s * sqNorm x ≤ ‖innerC φ x‖ ^ 2}

theorem coneBallAt_single (n : ℕ) (s : ℝ) :
    coneBallAt (n + 1) (Pi.single 0 1) s = coneBallSet n s := by
  ext x
  have hinner : innerC (Pi.single 0 1 : Fin (n + 1) → ℂ) x = x 0 := by
    rw [innerC, Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj]
      simp
    · intro h
      exact absurd (Finset.mem_univ 0) h
  show (sqNorm x ≤ 1 ∧ s * sqNorm x ≤ ‖innerC (Pi.single 0 1 : Fin (n + 1) → ℂ) x‖ ^ 2) ↔ _
  rw [hinner]
  exact Iff.rfl

theorem volume_coneBallAt_eq_coneBallSet {φ : Fin (n + 1) → ℂ} {U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ}
    (hU : Uᴴ * U = 1) (hUφ : U.mulVec (Pi.single 0 1) = φ) (s : ℝ) :
    volume (coneBallAt (n + 1) φ s) = volume (coneBallSet n s) := by
  have hpre : U.mulVec ⁻¹' (coneBallAt (n + 1) φ s) = coneBallSet n s := by
    ext x
    show (sqNorm (U.mulVec x) ≤ 1 ∧ s * sqNorm (U.mulVec x) ≤ ‖innerC φ (U.mulVec x)‖ ^ 2) ↔ _
    rw [sqNorm_mulVec hU, ← hUφ, innerC_mulVec hU]
    have hinner : innerC (Pi.single 0 1 : Fin (n + 1) → ℂ) x = x 0 := by
      rw [innerC, Finset.sum_eq_single 0]
      · simp
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj]
        simp
      · intro h
        exact absurd (Finset.mem_univ 0) h
    rw [hinner]
    exact Iff.rfl
  rw [← hpre, volume_preimage_mulVec hU]

end GeneralCentre

section UnitaryExtension

open scoped Matrix

variable {n : ℕ}

theorem exists_unitary_col {φ : Fin (n + 1) → ℂ} (hφ : sqNorm φ = 1) :
    ∃ U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, Uᴴ * U = 1 ∧
      U.mulVec (Pi.single 0 1) = φ := by
  classical
  set E := EuclideanSpace ℂ (Fin (n + 1))
  set v : E := (WithLp.equiv 2 (Fin (n + 1) → ℂ)).symm φ with hv
  have hvnorm : ‖v‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have : (∑ i, ‖v i‖ ^ 2) = 1 := hφ
    rw [this, Real.sqrt_one]
  have hcard : Module.finrank ℂ E = Fintype.card (Fin (n + 1)) := by
    simp [E]
  have horth : Orthonormal ℂ (({0} : Set (Fin (n + 1))).restrict (fun _ : Fin (n + 1) => v)) := by
    constructor
    · intro i
      simpa using hvnorm
    · intro i j hij
      exact absurd (Subtype.ext (by
        have hi := i.2
        have hj := j.2
        simp only [Set.mem_singleton_iff] at hi hj
        rw [hi, hj])) hij
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (𝕜 := ℂ) (E := E) hcard horth
  have hb0 : b 0 = v := hb 0 rfl
  refine ⟨Matrix.of fun i j => (b j) i, ?_, ?_⟩
  · ext j k
    have hinner : (inner ℂ (b j) (b k) : ℂ) = ∑ i, (starRingEnd ℂ) ((b j) i) * (b k) i := by
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [RCLike.inner_apply, mul_comm]
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hsum : (∑ i, (Matrix.of fun i j => (b j) i)ᴴ j i *
        (Matrix.of fun i j => (b j) i) i k) = ∑ i, (starRingEnd ℂ) ((b j) i) * (b k) i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.conjTranspose_apply, Matrix.of_apply, Complex.star_def]
    rw [hsum, ← hinner, orthonormal_iff_ite.mp b.orthonormal j k]
  · funext i
    show (∑ j, (Matrix.of fun i j => (b j) i) i j *
      ((Pi.single 0 1 : Fin (n + 1) → ℂ) j)) = φ i
    rw [Finset.sum_eq_single 0]
    · rw [Pi.single_eq_same, mul_one]
      show (b 0) i = φ i
      rw [hb0]
      rfl
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ 0) h

/-- **Uniform measure of a projective ball.**  The cone over a projective ball of squared cosine
level `s` fills exactly the fraction `(1-s)^n` of the unit ball, at every centre. -/
theorem volume_coneBallAt_eq (hn : 0 < n) {φ : Fin (n + 1) → ℂ} (hφ : sqNorm φ = 1)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    volume (coneBallAt (n + 1) φ s) =
      ENNReal.ofReal ((1 - s) ^ n) * volume {x : Fin (n + 1) → ℂ | sqNorm x ≤ 1} := by
  obtain ⟨U, hU, hUφ⟩ := exists_unitary_col hφ
  rw [volume_coneBallAt_eq_coneBallSet hU hUφ, volume_coneBallSet_eq hn hs0 hs1]

/-- The projective ball in trace-distance form. -/
def projectiveBallCone (n : ℕ) (φ : Fin (n + 1) → ℂ) (r : ℝ) : Set (Fin (n + 1) → ℂ) :=
  {x | sqNorm x ≤ 1 ∧ sqNorm x - ‖innerC φ x‖ ^ 2 ≤ r ^ 2 * sqNorm x}

/-- **Trace-distance form of the projective ball measure.**  The uniform probability of the
projective ball of trace-distance radius `r` is `r^{2n}`. -/
theorem volume_projectiveBallCone (hn : 0 < n) {φ : Fin (n + 1) → ℂ} (hφ : sqNorm φ = 1)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    volume (projectiveBallCone n φ r) =
      ENNReal.ofReal (r ^ (2 * n)) * volume {x : Fin (n + 1) → ℂ | sqNorm x ≤ 1} := by
  have hs0 : 0 < 1 - r ^ 2 := by nlinarith
  have hs1 : 1 - r ^ 2 < 1 := by nlinarith
  have hset : projectiveBallCone n φ r = coneBallAt (n + 1) φ (1 - r ^ 2) := by
    ext x
    show (sqNorm x ≤ 1 ∧ sqNorm x - ‖innerC φ x‖ ^ 2 ≤ r ^ 2 * sqNorm x) ↔
      (sqNorm x ≤ 1 ∧ (1 - r ^ 2) * sqNorm x ≤ ‖innerC φ x‖ ^ 2)
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by nlinarith [h2]⟩
  rw [hset, volume_coneBallAt_eq hn hφ hs0 hs1]
  congr 2
  rw [show (1 : ℝ) - (1 - r ^ 2) = r ^ 2 by ring, ← pow_mul, mul_comm]

end UnitaryExtension

section BallVolumeBounds

variable {n : ℕ}

theorem unitBall_subset_pi : {x : Fin n → ℂ | sqNorm x ≤ 1} ⊆
    Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : ℂ) 1 := by
  intro x hx i _
  rw [Metric.mem_closedBall, dist_zero_right]
  have hle : ‖x i‖ ^ 2 ≤ 1 := by
    refine le_trans ?_ hx
    exact Finset.single_le_sum (f := fun j : Fin n => ‖x j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
  nlinarith [norm_nonneg (x i), hle]

theorem pi_subset_unitBall (hn : 0 < n) :
    (Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : ℂ) ((n : ℝ) ^ (-(1:ℝ)/2))) ⊆
      {x : Fin n → ℂ | sqNorm x ≤ 1} := by
  intro x hx
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hbound : ∀ i : Fin n, ‖x i‖ ^ 2 ≤ 1 / (n : ℝ) := by
    intro i
    have hi := hx i (Set.mem_univ i)
    rw [Metric.mem_closedBall, dist_zero_right] at hi
    have hpow : ((n : ℝ) ^ (-(1:ℝ)/2)) ^ 2 = 1 / (n : ℝ) := by
      rw [← Real.rpow_natCast ((n : ℝ) ^ (-(1:ℝ)/2)) 2, ← Real.rpow_mul hn0.le]
      norm_num
      rw [Real.rpow_neg_one]
    calc ‖x i‖ ^ 2 ≤ ((n : ℝ) ^ (-(1:ℝ)/2)) ^ 2 := by
          exact pow_le_pow_left₀ (norm_nonneg _) hi 2
      _ = 1 / (n : ℝ) := hpow
  show sqNorm x ≤ 1
  rw [sqNorm]
  calc (∑ i, ‖x i‖ ^ 2) ≤ ∑ _i : Fin n, (1 / (n : ℝ)) := Finset.sum_le_sum fun i _ => hbound i
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

theorem volume_unitBall_lt_top : volume {x : Fin n → ℂ | sqNorm x ≤ 1} < ⊤ := by
  refine lt_of_le_of_lt (measure_mono unitBall_subset_pi) ?_
  rw [volume_pi_pi]
  refine ENNReal.prod_lt_top fun i _ => ?_
  exact measure_closedBall_lt_top

theorem volume_unitBall_pos (hn : 0 < n) : 0 < volume {x : Fin n → ℂ | sqNorm x ≤ 1} := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  refine lt_of_lt_of_le ?_ (measure_mono (pi_subset_unitBall hn))
  rw [volume_pi_pi]
  refine CanonicallyOrderedAdd.prod_pos.mpr fun i _ => ?_
  refine measure_closedBall_pos volume 0 ?_
  positivity

end BallVolumeBounds

section CoveringBound

variable {n : ℕ}

/-- **Covering-number lower bound for projective space.**  Every family of projective balls of
trace-distance radius `r` that covers projective space has at least `r^{-2n}` members. -/
theorem one_le_card_mul_pow (hn : 0 < n) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (t : Finset (Fin (n + 1) → ℂ)) (hunit : ∀ φ ∈ t, sqNorm φ = 1)
    (hcover : ∀ x : Fin (n + 1) → ℂ, sqNorm x ≤ 1 →
      ∃ φ ∈ t, sqNorm x - ‖innerC φ x‖ ^ 2 ≤ r ^ 2 * sqNorm x) :
    1 ≤ (t.card : ℝ) * r ^ (2 * n) := by
  classical
  set V := volume {x : Fin (n + 1) → ℂ | sqNorm x ≤ 1} with hV
  have hVpos : 0 < V := volume_unitBall_pos (by omega)
  have hVtop : V < ⊤ := volume_unitBall_lt_top
  have hsub : {x : Fin (n + 1) → ℂ | sqNorm x ≤ 1} ⊆
      ⋃ φ ∈ t, projectiveBallCone n φ r := by
    intro x hx
    obtain ⟨φ, hφt, hφ⟩ := hcover x hx
    exact Set.mem_iUnion₂.mpr ⟨φ, hφt, ⟨hx, hφ⟩⟩
  have hle : V ≤ ∑ φ ∈ t, volume (projectiveBallCone n φ r) :=
    le_trans (measure_mono hsub) (measure_biUnion_finset_le t _)
  have hterm : ∀ φ ∈ t, volume (projectiveBallCone n φ r) = ENNReal.ofReal (r ^ (2 * n)) * V :=
    fun φ hφ => volume_projectiveBallCone hn (hunit φ hφ) hr0 hr1
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, ← mul_assoc] at hle
  have hcancel : (1 : ENNReal) ≤ (t.card : ENNReal) * ENNReal.ofReal (r ^ (2 * n)) := by
    refine (ENNReal.mul_le_mul_iff_left hVpos.ne' hVtop.ne).mp ?_
    rw [one_mul]
    exact hle
  have hnn : (0 : ℝ) ≤ (t.card : ℝ) * r ^ (2 * n) := by positivity
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_one] at hcancel
  exact (ENNReal.ofReal_le_ofReal_iff hnn).mp hcancel

end CoveringBound

end

end GaloisForLFunctions.HTGeometry
