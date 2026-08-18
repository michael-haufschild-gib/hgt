import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Bounded homogeneous seam coupling has a rigid half-logarithmic trace

Let `X` be a Banach space, `L₀ > 0`, let `T : [L₀,∞) → B(X)` be uniformly bounded by `C`, and let
`F : [L₀,∞) → X` be continuous and satisfy the homogeneous boundary Volterra system

`(2L I + T(L)) F(L) = ∫_{L₀}^L F(t) dt`

for every `L` beyond an onset.  Conjugating the primitive `Y(L) = ∫_{L₀}^L F` by the indicial power,
`U(L) = L^{-1/2} Y(L)`, the equation becomes exactly

`U'(L) = -(1/2) L^{-3/2} T(L) F(L)`,  `‖U'(L)‖ ≤ C/(2L(2L-C)) · ‖U(L)‖`,

an integrable homogeneous perturbation of the trivial equation.  Hence `U` is bounded, `U'` is
integrable, `U` has a limit, and the limit cannot vanish unless `U` vanishes identically on the
terminal half-line.  Transporting back gives the dichotomy: either `F` vanishes identically on a
terminal half-line, or `√L F(L)` converges to a nonzero vector.  No commutativity, positivity,
finite dimensionality or normality of the coupling is used — only the uniform bound.
-/

namespace HTGeometry

open MeasureTheory Set Filter Topology

/-- Data of a homogeneous bounded-coupling boundary Volterra system on a Banach space. -/
structure BoundedSeamData (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  /-- The base point of the boundary half-line. -/
  base : ℝ
  /-- The onset beyond which the Volterra equation holds. -/
  onset : ℝ
  /-- A uniform bound for the coupling. -/
  bound : ℝ
  /-- The pointwise bounded coupling. -/
  coupling : ℝ → (X →L[ℝ] X)
  /-- The seam profile. -/
  profile : ℝ → X
  base_pos : 0 < base
  base_le_onset : base ≤ onset
  coupling_bound : ∀ L, base ≤ L → ‖coupling L‖ ≤ bound
  profile_cont : ContinuousOn profile (Ici base)
  equation : ∀ L, onset ≤ L →
    (2 * L) • profile L + coupling L (profile L) = ∫ t in base..L, profile t

namespace BoundedSeamData

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable (S : BoundedSeamData X)

/-- The primitive `Y(L) = ∫_{L₀}^L F`. -/
noncomputable def primitive (L : ℝ) : X := ∫ t in S.base..L, S.profile t

/-- The half-logarithmic conjugation `U(L) = L^{-1/2} Y(L)`. -/
noncomputable def halfLog (L : ℝ) : X := L ^ (-(1 / 2) : ℝ) • S.primitive L

theorem bound_nonneg : 0 ≤ S.bound :=
  le_trans (norm_nonneg _) (S.coupling_bound S.base le_rfl)

theorem intervalIntegrable_profile {a b : ℝ} (ha : S.base ≤ a) (hb : S.base ≤ b) :
    IntervalIntegrable S.profile volume a b := by
  refine (S.profile_cont.mono ?_).intervalIntegrable
  intro t ht
  rcases le_total a b with h | h
  · rw [uIcc_of_le h] at ht
    exact le_trans ha ht.1
  · rw [uIcc_of_ge h] at ht
    exact le_trans hb ht.1

theorem hasDerivAt_primitive [CompleteSpace X] {L : ℝ} (hL : S.base < L) :
    HasDerivAt S.primitive (S.profile L) L := by
  have hmem : Ici S.base ∈ 𝓝 L := Ici_mem_nhds hL
  have hcont : ContinuousAt S.profile L := S.profile_cont.continuousAt hmem
  have hmeas : StronglyMeasurableAtFilter S.profile (𝓝 L) volume := by
    refine ContinuousAt.stronglyMeasurableAtFilter (s := Ioi S.base) isOpen_Ioi ?_ L hL
    intro x hx
    exact S.profile_cont.continuousAt (Ici_mem_nhds hx)
  exact intervalIntegral.integral_hasDerivAt_right
    (S.intervalIntegrable_profile le_rfl hL.le) hmeas hcont

theorem continuousOn_primitive [CompleteSpace X] : ContinuousOn S.primitive (Ioi S.base) :=
  fun _ hL => ((S.hasDerivAt_primitive hL).continuousAt).continuousWithinAt

/-- The coupling term, extracted from the Volterra equation. -/
theorem coupling_apply_eq {L : ℝ} (hL : S.onset ≤ L) :
    S.coupling L (S.profile L) = S.primitive L - (2 * L) • S.profile L := by
  have h := S.equation L hL
  rw [primitive]
  linear_combination (norm := module) h

/-- The a priori bound on the profile in terms of the primitive. -/
theorem norm_profile_le {L : ℝ} (hL : S.onset ≤ L) :
    ‖S.profile L‖ * (2 * L - S.bound) ≤ ‖S.primitive L‖ := by
  have hLpos : 0 < L := lt_of_lt_of_le S.base_pos (le_trans S.base_le_onset hL)
  have hcoup : ‖S.coupling L (S.profile L)‖ ≤ S.bound * ‖S.profile L‖ := by
    refine le_trans ((S.coupling L).le_opNorm _) ?_
    exact mul_le_mul_of_nonneg_right (S.coupling_bound L (le_trans S.base_le_onset hL))
      (norm_nonneg _)
  have hsplit : (2 * L) • S.profile L = S.primitive L - S.coupling L (S.profile L) := by
    have h := S.equation L hL
    rw [primitive]
    linear_combination (norm := module) h
  have hnorm : ‖(2 * L) • S.profile L‖ = (2 * L) * ‖S.profile L‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hle : (2 * L) * ‖S.profile L‖ ≤ ‖S.primitive L‖ + S.bound * ‖S.profile L‖ := by
    rw [← hnorm, hsplit]
    exact le_trans (norm_sub_le _ _) (by linarith [hcoup])
  nlinarith [hle]

/-! ## The half-logarithmic conjugation -/

theorem primitive_eq_smul_halfLog {L : ℝ} (hL : 0 < L) :
    S.primitive L = L ^ (1 / 2 : ℝ) • S.halfLog L := by
  rw [halfLog, smul_smul, ← Real.rpow_add hL]
  norm_num

theorem norm_primitive_eq {L : ℝ} (hL : 0 < L) :
    ‖S.primitive L‖ = L ^ (1 / 2 : ℝ) * ‖S.halfLog L‖ := by
  rw [primitive_eq_smul_halfLog S hL, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hL _)]

/-- The derivative of the conjugated primitive, before using the equation. -/
theorem hasDerivAt_halfLog_raw [CompleteSpace X] {L : ℝ} (hL : S.base < L) :
    HasDerivAt S.halfLog
      (L ^ (-(1 / 2) : ℝ) • S.profile L
        + (-(1 / 2) * L ^ ((-(1 / 2) : ℝ) - 1)) • S.primitive L) L := by
  have hLpos : 0 < L := lt_trans S.base_pos hL
  have hpow : HasDerivAt (fun t : ℝ => t ^ (-(1 / 2) : ℝ))
      ((-(1 / 2)) * L ^ ((-(1 / 2) : ℝ) - 1)) L :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hLpos))
  exact hpow.smul (S.hasDerivAt_primitive hL)

/-- **The conjugated equation.**  The half-logarithmic conjugation turns the Volterra system into
a homogeneous equation driven only by the bounded coupling. -/
theorem hasDerivAt_halfLog [CompleteSpace X] {L : ℝ} (hbase : S.base < L) (hL : S.onset ≤ L) :
    HasDerivAt S.halfLog
      ((-(1 / 2) * L ^ (-(3 / 2) : ℝ)) • S.coupling L (S.profile L)) L := by
  have hLpos : 0 < L := lt_trans S.base_pos hbase
  have hraw := S.hasDerivAt_halfLog_raw hbase
  have hexp : ((-(1 / 2) : ℝ) - 1) = -(3 / 2) := by norm_num
  have h1 : L ^ (1 : ℝ) * L ^ (-(3 / 2) : ℝ) = L ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_add hLpos]
    norm_num
  rw [Real.rpow_one] at h1
  have hval : L ^ (-(1 / 2) : ℝ) • S.profile L
      + (-(1 / 2) * L ^ ((-(1 / 2) : ℝ) - 1)) • S.primitive L
      = (-(1 / 2) * L ^ (-(3 / 2) : ℝ)) • S.coupling L (S.profile L) := by
    rw [S.coupling_apply_eq hL, hexp]
    have hab : L ^ (-(1 / 2) : ℝ) = -(2 * L) * (-(1 / 2) * L ^ (-(3 / 2) : ℝ)) := by
      linear_combination -h1
    rw [hab]
    module
  rwa [hval] at hraw

/-- The integrable majorant of the conjugated equation. -/
noncomputable def perturbationRate (S : BoundedSeamData X) (L : ℝ) : ℝ :=
  S.bound / (2 * L * (2 * L - S.bound))

/-- **The integrable homogeneous bound.**  The conjugated derivative is bounded by an
`O(L^{-2})` multiple of the conjugated profile. -/
theorem norm_halfLog_deriv_le {L : ℝ} (hL : S.onset ≤ L) (hC : S.bound < 2 * L) :
    ‖(-(1 / 2) * L ^ (-(3 / 2) : ℝ)) • S.coupling L (S.profile L)‖
      ≤ S.perturbationRate L * ‖S.halfLog L‖ := by
  have hLpos : 0 < L := lt_of_lt_of_le S.base_pos (le_trans S.base_le_onset hL)
  have hCnn : 0 ≤ S.bound := S.bound_nonneg
  have hden : 0 < 2 * L - S.bound := by linarith
  have hcoup : ‖S.coupling L (S.profile L)‖ ≤ S.bound * ‖S.profile L‖ := by
    refine le_trans ((S.coupling L).le_opNorm _) ?_
    exact mul_le_mul_of_nonneg_right (S.coupling_bound L (le_trans S.base_le_onset hL))
      (norm_nonneg _)
  have hprof : ‖S.profile L‖ * (2 * L - S.bound) ≤ ‖S.primitive L‖ := S.norm_profile_le hL
  have hpow : (0 : ℝ) < L ^ (-(3 / 2) : ℝ) := Real.rpow_pos_of_pos hLpos _
  have hnorm : ‖(-(1 / 2) * L ^ (-(3 / 2) : ℝ)) • S.coupling L (S.profile L)‖
      = (1 / 2 * L ^ (-(3 / 2) : ℝ)) * ‖S.coupling L (S.profile L)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (by nlinarith)]
    ring
  have hmul : L ^ (-(3 / 2) : ℝ) * L ^ (1 / 2 : ℝ) = L⁻¹ := by
    rw [← Real.rpow_add hLpos]
    norm_num
    rw [show (-1 : ℝ) = ((-1 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    simp
  rw [hnorm, S.norm_primitive_eq hLpos] at *
  rw [perturbationRate]
  have hstep : (1 / 2 * L ^ (-(3 / 2) : ℝ)) * ‖S.coupling L (S.profile L)‖
      ≤ (1 / 2 * L ^ (-(3 / 2) : ℝ)) * (S.bound * ‖S.profile L‖) := by
    refine mul_le_mul_of_nonneg_left hcoup (by positivity)
  refine le_trans hstep ?_
  have hF : ‖S.profile L‖ ≤ L ^ (1 / 2 : ℝ) * ‖S.halfLog L‖ / (2 * L - S.bound) := by
    rw [le_div_iff₀ hden]
    exact hprof
  have hstep2 : (1 / 2 * L ^ (-(3 / 2) : ℝ)) * (S.bound * ‖S.profile L‖)
      ≤ (1 / 2 * L ^ (-(3 / 2) : ℝ)) *
        (S.bound * (L ^ (1 / 2 : ℝ) * ‖S.halfLog L‖ / (2 * L - S.bound))) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF hCnn) (by positivity)
  refine le_trans hstep2 ?_
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hfinal : (1 / 2 * L ^ (-(3 / 2) : ℝ)) *
      (S.bound * (L ^ (1 / 2 : ℝ) * ‖S.halfLog L‖ / (2 * L - S.bound)))
      = S.bound / (2 * L * (2 * L - S.bound)) * ‖S.halfLog L‖ := by
    have hmul' : L ^ (-(3 / 2) : ℝ) * L ^ (1 / 2 : ℝ) * L = 1 := by
      rw [hmul]
      field_simp
    field_simp
    linear_combination (S.bound * ‖S.halfLog L‖) * hmul'
  rw [hfinal]

/-! ## The terminal half-line -/

/-- The terminal threshold: beyond it the perturbation mass is at most a quarter. -/
noncomputable def threshold (S : BoundedSeamData X) : ℝ :=
  max (S.base + 1) (max S.onset (2 * S.bound + 1))

theorem base_lt_threshold : S.base < S.threshold :=
  lt_of_lt_of_le (by linarith) (le_max_left _ _)

theorem onset_le_threshold : S.onset ≤ S.threshold :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem two_mul_bound_lt_threshold : 2 * S.bound < S.threshold :=
  lt_of_lt_of_le (by linarith) (le_trans (le_max_right _ _) (le_max_right _ _))

theorem threshold_pos : 0 < S.threshold := lt_trans S.base_pos S.base_lt_threshold

theorem bound_lt_two_mul {L : ℝ} (hL : S.threshold ≤ L) : S.bound < 2 * L := by
  have h := S.two_mul_bound_lt_threshold
  have := S.bound_nonneg
  linarith

theorem bound_le {L : ℝ} (hL : S.threshold ≤ L) : S.bound ≤ L := by
  have h := S.two_mul_bound_lt_threshold
  have := S.bound_nonneg
  linarith

/-- The integrable majorant `C/(2t²)` of the perturbation rate. -/
noncomputable def perturbationMajorant (S : BoundedSeamData X) (t : ℝ) : ℝ :=
  S.bound / 2 * t ^ (-2 : ℝ)

theorem perturbationRate_nonneg {L : ℝ} (hL : S.threshold ≤ L) : 0 ≤ S.perturbationRate L := by
  have hLpos : 0 < L := lt_of_lt_of_le S.threshold_pos hL
  have hden : 0 < 2 * L - S.bound := by linarith [S.bound_lt_two_mul hL]
  rw [perturbationRate]
  exact div_nonneg S.bound_nonneg (mul_nonneg (by linarith) hden.le)

theorem perturbationRate_le_majorant {L : ℝ} (hL : S.threshold ≤ L) :
    S.perturbationRate L ≤ S.perturbationMajorant L := by
  have hLpos : 0 < L := lt_of_lt_of_le S.threshold_pos hL
  have hCnn : 0 ≤ S.bound := S.bound_nonneg
  have hden : 0 < 2 * L - S.bound := by linarith [S.bound_lt_two_mul hL]
  have hLC : S.bound ≤ L := S.bound_le hL
  have hsq : L ^ (-2 : ℝ) = (L ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hLpos.le, Real.rpow_natCast]
  have hrw : S.bound / 2 * (L ^ 2)⁻¹ = S.bound / (2 * L ^ 2) := by
    field_simp
  have hcmp : 2 * L ^ 2 ≤ 2 * L * (2 * L - S.bound) := by nlinarith
  rw [perturbationRate, perturbationMajorant, hsq, hrw]
  gcongr

theorem continuousOn_perturbationMajorant :
    ContinuousOn S.perturbationMajorant (Ici S.threshold) := by
  refine ContinuousOn.mul continuousOn_const ?_
  exact continuousOn_id.rpow_const fun t ht =>
    Or.inl (ne_of_gt (lt_of_lt_of_le S.threshold_pos ht))

theorem integral_perturbationMajorant {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ t in a..b, S.perturbationMajorant t = S.bound / 2 * (a⁻¹ - b⁻¹) := by
  have hzero : (0 : ℝ) ∉ uIcc a b := by
    intro hmem
    rcases le_total a b with h | h
    · rw [uIcc_of_le h] at hmem
      exact absurd hmem.1 (not_le.2 ha)
    · rw [uIcc_of_ge h] at hmem
      exact absurd hmem.1 (not_le.2 hb)
  have hpow : ∫ t in a..b, t ^ (-2 : ℝ) = a⁻¹ - b⁻¹ := by
    rw [integral_rpow (Or.inr ⟨by norm_num, hzero⟩),
      show (-2 : ℝ) + 1 = -((1 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg ha.le, Real.rpow_neg hb.le, Real.rpow_natCast, Real.rpow_natCast]
    simp
    ring
  simp only [perturbationMajorant]
  rw [intervalIntegral.integral_const_mul, hpow]

theorem integral_perturbationMajorant_le {a b : ℝ} (ha : S.threshold ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, S.perturbationMajorant t ≤ 1 / 4 := by
  have hapos : 0 < a := lt_of_lt_of_le S.threshold_pos ha
  have hbpos : 0 < b := lt_of_lt_of_le hapos hab
  have hCnn : 0 ≤ S.bound := S.bound_nonneg
  have hthr : 2 * S.bound < a := lt_of_lt_of_le S.two_mul_bound_lt_threshold ha
  rw [S.integral_perturbationMajorant hapos hbpos]
  have hinv : a⁻¹ - b⁻¹ ≤ a⁻¹ := by
    have hbi : (0 : ℝ) < b⁻¹ := by positivity
    linarith
  have hstep : S.bound / 2 * (a⁻¹ - b⁻¹) ≤ S.bound / 2 * a⁻¹ :=
    mul_le_mul_of_nonneg_left hinv (by positivity)
  refine le_trans hstep ?_
  rw [inv_eq_one_div, div_mul_div_comm, mul_one,
    div_le_iff₀ (by positivity : (0 : ℝ) < 2 * a)]
  linarith

/-! ## The conjugated derivative on the terminal half-line -/

/-- The derivative of the conjugated primitive. -/
noncomputable def halfLogDeriv (S : BoundedSeamData X) (t : ℝ) : X :=
  (-(1 / 2) * t ^ (-(3 / 2) : ℝ)) • S.coupling t (S.profile t)

theorem hasDerivAt_halfLog_terminal [CompleteSpace X] {L : ℝ} (hL : S.threshold ≤ L) :
    HasDerivAt S.halfLog (S.halfLogDeriv L) L :=
  S.hasDerivAt_halfLog (lt_of_lt_of_le S.base_lt_threshold hL)
    (le_trans S.onset_le_threshold hL)

theorem halfLogDeriv_eq {L : ℝ} (hL : S.threshold ≤ L) :
    S.halfLogDeriv L
      = (-(1 / 2) * L ^ (-(3 / 2) : ℝ)) • (S.primitive L - (2 * L) • S.profile L) := by
  rw [halfLogDeriv, S.coupling_apply_eq (le_trans S.onset_le_threshold hL)]

theorem norm_halfLogDeriv_le {L : ℝ} (hL : S.threshold ≤ L) :
    ‖S.halfLogDeriv L‖ ≤ S.perturbationRate L * ‖S.halfLog L‖ :=
  S.norm_halfLog_deriv_le (le_trans S.onset_le_threshold hL) (S.bound_lt_two_mul hL)

theorem continuousOn_halfLogDeriv [CompleteSpace X] :
    ContinuousOn S.halfLogDeriv (Ici S.threshold) := by
  have hsub : Ici S.threshold ⊆ Ioi S.base := fun t ht =>
    lt_of_lt_of_le S.base_lt_threshold ht
  have hprim : ContinuousOn S.primitive (Ici S.threshold) := S.continuousOn_primitive.mono hsub
  have hprof : ContinuousOn S.profile (Ici S.threshold) :=
    S.profile_cont.mono fun t ht => le_trans S.base_lt_threshold.le ht
  have hpow : ContinuousOn (fun t : ℝ => -(1 / 2) * t ^ (-(3 / 2) : ℝ)) (Ici S.threshold) :=
    continuousOn_const.mul (continuousOn_id.rpow_const fun t ht =>
      Or.inl (ne_of_gt (lt_of_lt_of_le S.threshold_pos ht)))
  have hbody : ContinuousOn (fun t : ℝ => S.primitive t - (2 * t) • S.profile t)
      (Ici S.threshold) :=
    hprim.sub ((continuousOn_const.mul continuousOn_id).smul hprof)
  exact (hpow.smul hbody).congr fun t ht => S.halfLogDeriv_eq ht

theorem continuousOn_halfLog [CompleteSpace X] :
    ContinuousOn S.halfLog (Ici S.threshold) :=
  fun _ hL => ((S.hasDerivAt_halfLog_terminal hL).continuousAt).continuousWithinAt

theorem intervalIntegrable_halfLogDeriv [CompleteSpace X] {a b : ℝ}
    (ha : S.threshold ≤ a) (hb : S.threshold ≤ b) :
    IntervalIntegrable S.halfLogDeriv volume a b := by
  refine (S.continuousOn_halfLogDeriv.mono ?_).intervalIntegrable
  intro t ht
  rcases le_total a b with h | h
  · rw [uIcc_of_le h] at ht
    exact le_trans ha ht.1
  · rw [uIcc_of_ge h] at ht
    exact le_trans hb ht.1

theorem halfLog_sub_eq_integral [CompleteSpace X] {a b : ℝ}
    (ha : S.threshold ≤ a) (hb : S.threshold ≤ b) :
    S.halfLog b - S.halfLog a = ∫ t in a..b, S.halfLogDeriv t := by
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt ?_
    (S.intervalIntegrable_halfLogDeriv ha hb)).symm
  intro t ht
  refine S.hasDerivAt_halfLog_terminal ?_
  rcases le_total a b with h | h
  · rw [uIcc_of_le h] at ht
    exact le_trans ha ht.1
  · rw [uIcc_of_ge h] at ht
    exact le_trans hb ht.1

/-! ## The a priori bound -/

/-- **Uniform bound on the conjugated profile.**  The integrable perturbation cannot amplify the
conjugated profile beyond twice its terminal value. -/
theorem norm_halfLog_le_two_mul [CompleteSpace X] {L : ℝ} (hL : S.threshold ≤ L) :
    ‖S.halfLog L‖ ≤ 2 * ‖S.halfLog S.threshold‖ := by
  have hcont : ContinuousOn (fun t => ‖S.halfLog t‖) (Icc S.threshold L) :=
    (S.continuousOn_halfLog.mono (Icc_subset_Ici_self)).norm
  obtain ⟨s, hs, hmax⟩ := (isCompact_Icc (a := S.threshold) (b := L)).exists_isMaxOn
    ⟨S.threshold, ⟨le_rfl, hL⟩⟩ hcont
  have hkey : ∀ t ∈ Icc S.threshold L,
      ‖S.halfLog t‖ ≤ ‖S.halfLog S.threshold‖ + ‖S.halfLog s‖ / 4 := by
    intro t ht
    have hint1 : IntervalIntegrable (fun r => ‖S.halfLogDeriv r‖) volume S.threshold t :=
      (S.intervalIntegrable_halfLogDeriv le_rfl ht.1).norm
    have hint2 : IntervalIntegrable
        (fun r => S.perturbationMajorant r * ‖S.halfLog s‖) volume S.threshold t := by
      refine ((S.continuousOn_perturbationMajorant.mono ?_).mul continuousOn_const).intervalIntegrable
      intro r hr
      rw [uIcc_of_le ht.1] at hr
      exact hr.1
    have hstep : ‖S.halfLog t - S.halfLog S.threshold‖
        ≤ ∫ r in S.threshold..t, S.perturbationMajorant r * ‖S.halfLog s‖ := by
      rw [S.halfLog_sub_eq_integral le_rfl ht.1]
      refine le_trans (intervalIntegral.norm_integral_le_integral_norm ht.1) ?_
      refine intervalIntegral.integral_mono_on ht.1 hint1 hint2 fun r hr => ?_
      have hrthr : S.threshold ≤ r := hr.1
      have hrL : r ≤ L := le_trans hr.2 ht.2
      have h1 : ‖S.halfLogDeriv r‖ ≤ S.perturbationRate r * ‖S.halfLog r‖ :=
        S.norm_halfLogDeriv_le hrthr
      have h2 : ‖S.halfLog r‖ ≤ ‖S.halfLog s‖ := hmax ⟨hrthr, hrL⟩
      have h3 : S.perturbationRate r ≤ S.perturbationMajorant r :=
        S.perturbationRate_le_majorant hrthr
      have h4 : 0 ≤ S.perturbationRate r := S.perturbationRate_nonneg hrthr
      calc ‖S.halfLogDeriv r‖ ≤ S.perturbationRate r * ‖S.halfLog r‖ := h1
        _ ≤ S.perturbationRate r * ‖S.halfLog s‖ := by
            exact mul_le_mul_of_nonneg_left h2 h4
        _ ≤ S.perturbationMajorant r * ‖S.halfLog s‖ := by
            exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    have hmass : (∫ r in S.threshold..t, S.perturbationMajorant r) ≤ 1 / 4 :=
      S.integral_perturbationMajorant_le le_rfl ht.1
    have hfac : (∫ r in S.threshold..t, S.perturbationMajorant r * ‖S.halfLog s‖)
        = (∫ r in S.threshold..t, S.perturbationMajorant r) * ‖S.halfLog s‖ :=
      intervalIntegral.integral_mul_const _ _
    rw [hfac] at hstep
    have hbound : (∫ r in S.threshold..t, S.perturbationMajorant r) * ‖S.halfLog s‖
        ≤ (1 / 4) * ‖S.halfLog s‖ :=
      mul_le_mul_of_nonneg_right hmass (norm_nonneg _)
    have htri : ‖S.halfLog t‖ ≤ ‖S.halfLog S.threshold‖ + ‖S.halfLog t - S.halfLog S.threshold‖ := by
      have := norm_add_le (S.halfLog S.threshold) (S.halfLog t - S.halfLog S.threshold)
      simpa using this
    linarith [le_trans hstep hbound]
  have hsmax := hkey s hs
  have hsle : ‖S.halfLog s‖ ≤ 2 * ‖S.halfLog S.threshold‖ := by
    linarith [norm_nonneg (S.halfLog S.threshold)]
  exact le_trans (hmax ⟨hL, le_rfl⟩ : ‖S.halfLog L‖ ≤ ‖S.halfLog s‖) hsle

/-! ## The terminal limit -/

theorem integrableOn_perturbationMajorant :
    IntegrableOn S.perturbationMajorant (Ioi S.threshold) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (c := S.threshold) (by norm_num)
    S.threshold_pos
  exact h.const_mul (S.bound / 2)

theorem integrableOn_halfLogDeriv [CompleteSpace X] :
    IntegrableOn S.halfLogDeriv (Ioi S.threshold) := by
  refine Integrable.mono'
    (g := fun t => (2 * ‖S.halfLog S.threshold‖) * S.perturbationMajorant t)
    (S.integrableOn_perturbationMajorant.const_mul _) ?_ ?_
  · exact (S.continuousOn_halfLogDeriv.mono Ioi_subset_Ici_self).aestronglyMeasurable
      measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hthr : S.threshold ≤ t := le_of_lt ht
    have hrate : 0 ≤ S.perturbationRate t := S.perturbationRate_nonneg hthr
    calc ‖S.halfLogDeriv t‖ ≤ S.perturbationRate t * ‖S.halfLog t‖ := S.norm_halfLogDeriv_le hthr
      _ ≤ S.perturbationMajorant t * (2 * ‖S.halfLog S.threshold‖) :=
          mul_le_mul (S.perturbationRate_le_majorant hthr) (S.norm_halfLog_le_two_mul hthr)
            (norm_nonneg _) (le_trans hrate (S.perturbationRate_le_majorant hthr))
      _ = (2 * ‖S.halfLog S.threshold‖) * S.perturbationMajorant t := by ring

/-- The terminal half-logarithmic trace of the conjugated primitive. -/
noncomputable def halfLogLimit (S : BoundedSeamData X) [CompleteSpace X] : X :=
  S.halfLog S.threshold + ∫ t in Ioi S.threshold, S.halfLogDeriv t

theorem tendsto_halfLog [CompleteSpace X] :
    Tendsto S.halfLog atTop (𝓝 S.halfLogLimit) := by
  have hconv := intervalIntegral_tendsto_integral_Ioi (b := fun L : ℝ => L) (l := atTop)
    S.threshold S.integrableOn_halfLogDeriv tendsto_id
  have hshift := (tendsto_const_nhds (x := S.halfLog S.threshold) (f := atTop)).add hconv
  rw [halfLogLimit]
  refine hshift.congr' ?_
  filter_upwards [eventually_ge_atTop S.threshold] with L hL
  rw [← S.halfLog_sub_eq_integral le_rfl hL]
  abel

theorem norm_halfLog_sub_le [CompleteSpace X] {a b : ℝ} (ha : S.threshold ≤ a) (hab : a ≤ b) :
    ‖S.halfLog b - S.halfLog a‖ ≤ (1 / 4) * (2 * ‖S.halfLog S.threshold‖) := by
  have hthr : S.threshold ≤ b := le_trans ha hab
  have hint1 : IntervalIntegrable (fun r => ‖S.halfLogDeriv r‖) volume a b :=
    (S.intervalIntegrable_halfLogDeriv ha hthr).norm
  have hint2 : IntervalIntegrable
      (fun r => S.perturbationMajorant r * (2 * ‖S.halfLog S.threshold‖)) volume a b := by
    refine ((S.continuousOn_perturbationMajorant.mono ?_).mul
      continuousOn_const).intervalIntegrable
    intro r hr
    rw [uIcc_of_le hab] at hr
    exact le_trans ha hr.1
  have hstep : ‖S.halfLog b - S.halfLog a‖
      ≤ ∫ r in a..b, S.perturbationMajorant r * (2 * ‖S.halfLog S.threshold‖) := by
    rw [S.halfLog_sub_eq_integral ha hthr]
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm hab) ?_
    refine intervalIntegral.integral_mono_on hab hint1 hint2 fun r hr => ?_
    have hrthr : S.threshold ≤ r := le_trans ha hr.1
    have hrate : 0 ≤ S.perturbationRate r := S.perturbationRate_nonneg hrthr
    calc ‖S.halfLogDeriv r‖ ≤ S.perturbationRate r * ‖S.halfLog r‖ := S.norm_halfLogDeriv_le hrthr
      _ ≤ S.perturbationMajorant r * (2 * ‖S.halfLog S.threshold‖) :=
          mul_le_mul (S.perturbationRate_le_majorant hrthr) (S.norm_halfLog_le_two_mul hrthr)
            (norm_nonneg _) (le_trans hrate (S.perturbationRate_le_majorant hrthr))
  have hfac : (∫ r in a..b, S.perturbationMajorant r * (2 * ‖S.halfLog S.threshold‖))
      = (∫ r in a..b, S.perturbationMajorant r) * (2 * ‖S.halfLog S.threshold‖) :=
    intervalIntegral.integral_mul_const _ _
  rw [hfac] at hstep
  refine le_trans hstep ?_
  exact mul_le_mul_of_nonneg_right (S.integral_perturbationMajorant_le ha hab)
    (by positivity)

/-- **The trace cannot be destroyed.**  The conjugated profile stays at least half its terminal
value. -/
theorem norm_halfLog_threshold_le [CompleteSpace X] {L : ℝ} (hL : S.threshold ≤ L) :
    ‖S.halfLog S.threshold‖ / 2 ≤ ‖S.halfLog L‖ := by
  have h := S.norm_halfLog_sub_le le_rfl hL
  have htri : ‖S.halfLog S.threshold‖
      ≤ ‖S.halfLog L‖ + ‖S.halfLog L - S.halfLog S.threshold‖ := by
    have hsub := norm_sub_le (S.halfLog L) (S.halfLog L - S.halfLog S.threshold)
    simpa using hsub
  linarith

theorem norm_halfLogLimit_ge [CompleteSpace X] :
    ‖S.halfLog S.threshold‖ / 2 ≤ ‖S.halfLogLimit‖ := by
  refine ge_of_tendsto S.tendsto_halfLog.norm ?_
  filter_upwards [eventually_ge_atTop S.threshold] with L hL
  exact S.norm_halfLog_threshold_le hL

/-! ## Terminal vanishing -/

theorem halfLog_eq_zero_of_threshold [CompleteSpace X] (h0 : S.halfLog S.threshold = 0) {L : ℝ}
    (hL : S.threshold ≤ L) : S.halfLog L = 0 := by
  have h := S.norm_halfLog_le_two_mul hL
  rw [h0, norm_zero, mul_zero] at h
  exact norm_le_zero_iff.1 h

theorem primitive_eq_zero_of_threshold [CompleteSpace X] (h0 : S.halfLog S.threshold = 0) {L : ℝ}
    (hL : S.threshold ≤ L) : S.primitive L = 0 := by
  rw [S.primitive_eq_smul_halfLog (lt_of_lt_of_le S.threshold_pos hL),
    S.halfLog_eq_zero_of_threshold h0 hL, smul_zero]

theorem profile_eq_zero_of_threshold [CompleteSpace X] (h0 : S.halfLog S.threshold = 0) {L : ℝ}
    (hL : S.threshold < L) : S.profile L = 0 := by
  have hderiv := S.hasDerivAt_primitive (lt_trans S.base_lt_threshold hL)
  have hzero : HasDerivAt S.primitive 0 L := by
    have heq : S.primitive =ᶠ[𝓝 L] fun _ => (0 : X) := by
      filter_upwards [Ioi_mem_nhds hL] with t ht
      exact S.primitive_eq_zero_of_threshold h0 (le_of_lt ht)
    exact (hasDerivAt_const L (0 : X)).congr_of_eventuallyEq heq
  exact hderiv.unique hzero

/-! ## The half-logarithmic trace -/

theorem primitive_eq_of {L : ℝ} (hL : S.onset ≤ L) :
    S.primitive L = (2 * L) • S.profile L + S.coupling L (S.profile L) :=
  (S.equation L hL).symm

theorem halfLog_eq_sqrt_inv_smul {L : ℝ} (hL : 0 < L) :
    S.halfLog L = (Real.sqrt L)⁻¹ • S.primitive L := by
  rw [halfLog, Real.sqrt_eq_rpow, ← Real.rpow_neg hL.le]

/-- The remainder separating the trace from the conjugated profile. -/
noncomputable def traceRemainder (S : BoundedSeamData X) (L : ℝ) : X :=
  ((2 * Real.sqrt L)⁻¹) • S.coupling L (S.profile L)

/-- **The trace identity.**  `√L F(L)` differs from half the conjugated profile by the bounded
coupling remainder. -/
theorem sqrt_smul_profile_eq {L : ℝ} (hL : S.threshold ≤ L) :
    Real.sqrt L • S.profile L = (1 / 2 : ℝ) • S.halfLog L - S.traceRemainder L := by
  have hLpos : 0 < L := lt_of_lt_of_le S.threshold_pos hL
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.2 hLpos
  have hLsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLpos.le
  rw [S.halfLog_eq_sqrt_inv_smul hLpos, S.primitive_eq_of (le_trans S.onset_le_threshold hL),
    traceRemainder]
  match_scalars
  · field_simp
    linear_combination hLsq
  · field_simp
    ring

theorem norm_traceRemainder_le [CompleteSpace X] {L : ℝ} (hL : S.threshold ≤ L) :
    ‖S.traceRemainder L‖ ≤ S.bound * ‖S.halfLog S.threshold‖ / (2 * L - S.bound) := by
  have hLpos : 0 < L := lt_of_lt_of_le S.threshold_pos hL
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.2 hLpos
  have hCnn : 0 ≤ S.bound := S.bound_nonneg
  have hden : 0 < 2 * L - S.bound := by linarith [S.bound_lt_two_mul hL]
  have honset : S.onset ≤ L := le_trans S.onset_le_threshold hL
  have hcoup : ‖S.coupling L (S.profile L)‖ ≤ S.bound * ‖S.profile L‖ := by
    refine le_trans ((S.coupling L).le_opNorm _) ?_
    exact mul_le_mul_of_nonneg_right (S.coupling_bound L (le_trans S.base_le_onset honset))
      (norm_nonneg _)
  have hprof : ‖S.profile L‖ * (2 * L - S.bound) ≤ ‖S.primitive L‖ := S.norm_profile_le honset
  have hY : ‖S.primitive L‖ = Real.sqrt L * ‖S.halfLog L‖ := by
    rw [S.norm_primitive_eq hLpos, Real.sqrt_eq_rpow]
  have hUbound : ‖S.halfLog L‖ ≤ 2 * ‖S.halfLog S.threshold‖ := S.norm_halfLog_le_two_mul hL
  have hnorm : ‖S.traceRemainder L‖
      = (2 * Real.sqrt L)⁻¹ * ‖S.coupling L (S.profile L)‖ := by
    rw [traceRemainder, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hF : ‖S.profile L‖ ≤ Real.sqrt L * ‖S.halfLog L‖ / (2 * L - S.bound) := by
    rw [le_div_iff₀ hden, ← hY]
    exact hprof
  rw [hnorm]
  have hstep : (2 * Real.sqrt L)⁻¹ * ‖S.coupling L (S.profile L)‖
      ≤ (2 * Real.sqrt L)⁻¹ * (S.bound * (Real.sqrt L * ‖S.halfLog L‖ / (2 * L - S.bound))) := by
    refine mul_le_mul_of_nonneg_left (le_trans hcoup ?_) (by positivity)
    exact mul_le_mul_of_nonneg_left hF hCnn
  refine le_trans hstep ?_
  have hval : (2 * Real.sqrt L)⁻¹ *
      (S.bound * (Real.sqrt L * ‖S.halfLog L‖ / (2 * L - S.bound)))
      = S.bound * ‖S.halfLog L‖ / (2 * (2 * L - S.bound)) := by
    field_simp
  rw [hval, div_le_div_iff₀ (by positivity) hden]
  have hkey := mul_le_mul_of_nonneg_left hUbound (mul_nonneg hCnn hden.le)
  nlinarith [hkey]

theorem tendsto_traceRemainder [CompleteSpace X] :
    Tendsto S.traceRemainder atTop (𝓝 0) := by
  have hden : Tendsto (fun L : ℝ => 2 * L - S.bound) atTop atTop := by
    refine Filter.tendsto_atTop_add_const_right _ (-S.bound) ?_
    exact Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_id
  have hzero : Tendsto
      (fun L : ℝ => S.bound * ‖S.halfLog S.threshold‖ / (2 * L - S.bound)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hden
  refine squeeze_zero_norm' ?_ hzero
  filter_upwards [eventually_ge_atTop S.threshold] with L hL
  exact S.norm_traceRemainder_le hL

/-- **The half-logarithmic trace exists.**  `√L F(L)` converges to half the terminal value of the
conjugated profile. -/
theorem tendsto_sqrt_smul_profile [CompleteSpace X] :
    Tendsto (fun L => Real.sqrt L • S.profile L) atTop (𝓝 ((1 / 2 : ℝ) • S.halfLogLimit)) := by
  have hmain := (S.tendsto_halfLog.const_smul (1 / 2 : ℝ)).sub S.tendsto_traceRemainder
  rw [sub_zero] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop S.threshold] with L hL
  exact (S.sqrt_smul_profile_eq hL).symm

/-- **Bounded seam half-log rigidity.**  Every solution of the homogeneous bounded-coupling
boundary Volterra system has a half-logarithmic trace, and the trace vanishes exactly when the
profile vanishes identically on the terminal half-line. -/
theorem halfLog_trace_dichotomy [CompleteSpace X] :
    ∃ β : X, Tendsto (fun L => Real.sqrt L • S.profile L) atTop (𝓝 β) ∧
      (β = 0 ↔ ∀ L, S.threshold < L → S.profile L = 0) := by
  refine ⟨(1 / 2 : ℝ) • S.halfLogLimit, S.tendsto_sqrt_smul_profile, ?_, ?_⟩
  · intro hβ L hL
    have hlim : S.halfLogLimit = 0 := by
      have : (1 / 2 : ℝ) • S.halfLogLimit = 0 := hβ
      simpa using this
    have hthr : ‖S.halfLog S.threshold‖ / 2 ≤ 0 := by
      have := S.norm_halfLogLimit_ge
      rw [hlim, norm_zero] at this
      exact this
    have h0 : S.halfLog S.threshold = 0 := by
      have hnn : 0 ≤ ‖S.halfLog S.threshold‖ := norm_nonneg _
      exact norm_le_zero_iff.1 (by linarith)
    exact S.profile_eq_zero_of_threshold h0 hL
  · intro hzero
    have hev : Tendsto (fun L => Real.sqrt L • S.profile L) atTop (𝓝 0) := by
      refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : X)) (f := atTop))
      filter_upwards [eventually_gt_atTop S.threshold] with L hL
      rw [hzero L hL, smul_zero]
    exact tendsto_nhds_unique S.tendsto_sqrt_smul_profile hev

/-! ## Sharpness of the nonzero-trace alternative -/

/-- The explicit scalar profile `t^{-1/2} + 4 max(0, 2-t)`. -/
noncomputable def sharpProfile (t : ℝ) : ℝ := t ^ (-(1 / 2) : ℝ) + 4 * max 0 (2 - t)

theorem continuousOn_sharpProfile : ContinuousOn sharpProfile (Ici (1 : ℝ)) := by
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_id.rpow_const fun t ht => Or.inl ?_
    have h1 : (1 : ℝ) ≤ t := ht
    simp only [id_eq]
    linarith
  · exact continuousOn_const.mul
      (by fun_prop : Continuous (fun t : ℝ => max 0 (2 - t))).continuousOn

theorem integral_sharpProfile_rpow {L : ℝ} (hL : 1 ≤ L) :
    ∫ t in (1 : ℝ)..L, t ^ (-(1 / 2) : ℝ) = 2 * Real.sqrt L - 2 := by
  have hzero : (0 : ℝ) ∉ uIcc (1 : ℝ) L := by
    rw [uIcc_of_le hL]
    intro hmem
    linarith [hmem.1]
  rw [integral_rpow (Or.inr ⟨by norm_num, hzero⟩)]
  have hexp : (-(1 / 2) : ℝ) + 1 = 1 / 2 := by norm_num
  rw [hexp, Real.one_rpow, ← Real.sqrt_eq_rpow]
  ring

theorem integral_sharpProfile_bump {L : ℝ} (hL : 2 ≤ L) :
    ∫ t in (1 : ℝ)..L, max 0 (2 - t) = 1 / 2 := by
  have hsplit : (∫ t in (1 : ℝ)..L, max 0 (2 - t))
      = (∫ t in (1 : ℝ)..2, max 0 (2 - t)) + ∫ t in (2 : ℝ)..L, max 0 (2 - t) := by
    refine (intervalIntegral.integral_add_adjacent_intervals ?_ ?_).symm
    · exact (by fun_prop : Continuous (fun t : ℝ =>
        max 0 (2 - t))).continuousOn.intervalIntegrable
    · exact (by fun_prop : Continuous (fun t : ℝ =>
        max 0 (2 - t))).continuousOn.intervalIntegrable
  have hleft : (∫ t in (1 : ℝ)..2, max 0 (2 - t)) = 1 / 2 := by
    have hcongr : (∫ t in (1 : ℝ)..2, max 0 (2 - t)) = ∫ t in (1 : ℝ)..2, (2 - t) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
      exact max_eq_right (by linarith [ht.2])
    rw [hcongr, intervalIntegral.integral_sub intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id, intervalIntegral.integral_const, integral_id]
    norm_num
  have hright : (∫ t in (2 : ℝ)..L, max 0 (2 - t)) = 0 := by
    have hcongr : (∫ t in (2 : ℝ)..L, max 0 (2 - t)) = ∫ t in (2 : ℝ)..L, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hL] at ht
      exact max_eq_left (by linarith [ht.1])
    rw [hcongr, intervalIntegral.integral_const]
    simp
  rw [hsplit, hleft, hright, add_zero]

theorem integral_sharpProfile {L : ℝ} (hL : 2 ≤ L) :
    ∫ t in (1 : ℝ)..L, sharpProfile t = 2 * Real.sqrt L := by
  have h1 : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) volume 1 L := by
    refine (ContinuousOn.intervalIntegrable ?_)
    refine continuousOn_id.rpow_const fun t ht => Or.inl ?_
    rw [uIcc_of_le (by linarith : (1 : ℝ) ≤ L)] at ht
    have h1 : (1 : ℝ) ≤ t := ht.1
    simp only [id_eq]
    linarith
  have h2 : IntervalIntegrable (fun t : ℝ => 4 * max 0 (2 - t)) volume 1 L :=
    (by fun_prop : Continuous (fun t : ℝ => 4 * max 0 (2 - t))).continuousOn.intervalIntegrable
  have hsum : (∫ t in (1 : ℝ)..L, sharpProfile t)
      = (∫ t in (1 : ℝ)..L, t ^ (-(1 / 2) : ℝ)) + ∫ t in (1 : ℝ)..L, 4 * max 0 (2 - t) := by
    simp only [sharpProfile]
    exact intervalIntegral.integral_add h1 h2
  rw [hsum, integral_sharpProfile_rpow (by linarith),
    intervalIntegral.integral_const_mul, integral_sharpProfile_bump hL]
  ring

theorem sharpProfile_of_two_le {L : ℝ} (hL : 2 ≤ L) :
    sharpProfile L = L ^ (-(1 / 2) : ℝ) := by
  rw [sharpProfile, max_eq_left (by linarith), mul_zero, add_zero]

/-- The sharp scalar model: zero coupling, and the exact critical exponent. -/
noncomputable def sharpSeam : BoundedSeamData ℝ where
  base := 1
  onset := 2
  bound := 0
  coupling := fun _ => 0
  profile := sharpProfile
  base_pos := one_pos
  base_le_onset := by norm_num
  coupling_bound := by
    intro L _
    simp
  profile_cont := continuousOn_sharpProfile
  equation := by
    intro L hL
    have hLpos : (0 : ℝ) < L := by linarith
    rw [integral_sharpProfile hL, sharpProfile_of_two_le hL]
    have hsq : Real.sqrt L = L ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow L
    have hmul : L * L ^ (-(1 / 2) : ℝ) = L ^ (1 / 2 : ℝ) := by
      have h := Real.rpow_add hLpos 1 (-(1 / 2))
      rw [Real.rpow_one] at h
      rw [show (1 : ℝ) + -(1 / 2) = 1 / 2 by norm_num] at h
      exact h.symm
    simp only [zero_apply, add_zero, smul_eq_mul]
    rw [hsq]
    linear_combination 2 * hmul

/-- **Sharpness.**  The nonzero-trace alternative is realized by an explicit scalar solution with
zero coupling: its half-logarithmic trace is `1`. -/
theorem tendsto_sharpSeam_trace :
    Tendsto (fun L => Real.sqrt L • sharpSeam.profile L) atTop (𝓝 1) := by
  refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop))
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with L hL
  have hLpos : (0 : ℝ) < L := by linarith
  have hsq : Real.sqrt L = L ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow L
  have hmul : L ^ (1 / 2 : ℝ) * L ^ (-(1 / 2) : ℝ) = 1 := by
    rw [← Real.rpow_add hLpos]
    norm_num
  show (1 : ℝ) = Real.sqrt L • sharpSeam.profile L
  have hprof : sharpSeam.profile L = L ^ (-(1 / 2) : ℝ) := sharpProfile_of_two_le hL
  rw [hprof, hsq, smul_eq_mul, hmul]

end BoundedSeamData

end HTGeometry
