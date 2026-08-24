import GaloisForLFunctions.RHTower.GammaVerticalPolar
import GaloisForLFunctions.HTGeometry.DigammaSecondOrderVertical
import GaloisForLFunctions.HTGeometry.GammaLogDeriv

/-!
# Second-order critical-line Gamma phase

The second-order vertical digamma estimate is integrable.  Legendre duplication removes the
otherwise undetermined integration constant: the critical-line phase remainder is exactly the
difference of the line-one remainders at heights `2t` and `t`.  This gives the constant-sensitive
Stirling phase estimate needed by explicit Kapustin gauges.
-/

open Complex Filter Topology intervalIntegral MeasureTheory

noncomputable section

namespace RHTower

/-- A second-order real-part estimate on the vertical line through `1`. -/
theorem abs_re_digamma_one_sub_log_le {t : ℝ} (ht : 2 ≤ t) :
    |(Complex.digamma ((1 : ℂ) + (t : ℂ) * I)).re - Real.log t| ≤ 8 / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  let z : ℂ := (1 : ℂ) + (t : ℂ) * I
  have hzsq : ‖z‖ ^ 2 = t ^ 2 + 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [z]
    ring
  have hznorm0 : 0 < ‖z‖ := by
    rw [norm_pos_iff]
    intro hz
    have hre := congrArg Complex.re hz
    simp [z] at hre
  have hnormge : t ≤ ‖z‖ := by
    have hsquare : t ^ 2 ≤ ‖z‖ ^ 2 := by rw [hzsq]; norm_num
    nlinarith [norm_nonneg z]
  have hnormle : ‖z‖ ≤ t + 1 / (2 * t) := by
    have hupper0 : 0 ≤ t + 1 / (2 * t) := by positivity
    have hsquare : ‖z‖ ^ 2 ≤ (t + 1 / (2 * t)) ^ 2 := by
      rw [hzsq]
      field_simp [ht0.ne']
      nlinarith
    exact (sq_le_sq₀ (norm_nonneg z) hupper0).mp hsquare
  have hlognonneg : 0 ≤ Real.log ‖z‖ - Real.log t :=
    sub_nonneg.mpr (Real.log_le_log ht0 hnormge)
  have hratio0 : 0 < ‖z‖ / t := div_pos hznorm0 ht0
  have hratiole : ‖z‖ / t ≤ 1 + 1 / (2 * t ^ 2) := by
    rw [div_le_iff₀ ht0]
    calc
      ‖z‖ ≤ t + 1 / (2 * t) := hnormle
      _ = (1 + 1 / (2 * t ^ 2)) * t := by field_simp [ht0.ne']
  have hlogupper : Real.log ‖z‖ - Real.log t ≤ 1 / (2 * t ^ 2) := by
    rw [← Real.log_div hznorm0.ne' ht0.ne']
    exact le_trans (Real.log_le_sub_one_of_pos hratio0) (by linarith)
  have hlogabs : |Real.log ‖z‖ - Real.log t| ≤ 1 / (2 * t ^ 2) := by
    rw [abs_of_nonneg hlognonneg]
    exact hlogupper
  have hrem := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_add_half_inv_le
    (by norm_num : (0 : ℝ) < 1) ht
  change ‖Complex.digamma z - Complex.log z + 1 / (2 * z)‖ ≤ (20 / 3) / t ^ 2 at hrem
  have hreRem : |(Complex.digamma z - Complex.log z + 1 / (2 * z)).re| ≤
      (20 / 3) / t ^ 2 := le_trans (Complex.abs_re_le_norm _) hrem
  have hinvre : (1 / (2 * z) : ℂ).re = 1 / (2 * (1 + t ^ 2)) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    simp [z]
    field_simp
  have hinvnonneg : 0 ≤ (1 / (2 * z) : ℂ).re := by rw [hinvre]; positivity
  have hinvle : |(1 / (2 * z) : ℂ).re| ≤ 1 / (2 * t ^ 2) := by
    rw [abs_of_nonneg hinvnonneg, hinvre]
    gcongr
    nlinarith
  have hdecomp :
      (Complex.digamma z).re - Real.log t =
        (Complex.digamma z - Complex.log z + 1 / (2 * z)).re +
          (Real.log ‖z‖ - Real.log t) - (1 / (2 * z) : ℂ).re := by
    rw [Complex.add_re, Complex.sub_re, Complex.log_re]
    ring
  rw [show ((1 : ℂ) + (t : ℂ) * I) = z from rfl, hdecomp]
  calc
    |(Complex.digamma z - Complex.log z + 1 / (2 * z)).re +
          (Real.log ‖z‖ - Real.log t) - (1 / (2 * z) : ℂ).re| ≤
        |(Complex.digamma z - Complex.log z + 1 / (2 * z)).re| +
          |Real.log ‖z‖ - Real.log t| + |(1 / (2 * z) : ℂ).re| := by
      calc
        _ ≤ |(Complex.digamma z - Complex.log z + 1 / (2 * z)).re +
              (Real.log ‖z‖ - Real.log t)| + |(1 / (2 * z) : ℂ).re| := abs_sub _ _
        _ ≤ _ := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (20 / 3) / t ^ 2 + 1 / (2 * t ^ 2) + 1 / (2 * t ^ 2) := by
      gcongr
    _ ≤ 8 / t ^ 2 := by
      field_simp [ht0.ne']
      nlinarith

/-- Stirling main-term remainder for the continuous vertical Gamma phase. -/
def gammaVerticalPhaseRemainder (σ t : ℝ) : ℝ :=
  gammaVerticalPhase σ t - (t * Real.log t - t)

theorem hasDerivAt_gammaVerticalPhaseRemainder {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    HasDerivAt (gammaVerticalPhaseRemainder σ)
      ((Complex.digamma ((σ : ℂ) + (t : ℂ) * I)).re - Real.log t) t := by
  have hmain := (Real.hasDerivAt_mul_log ht.ne').sub (hasDerivAt_id t)
  have hphase := hasDerivAt_gammaVerticalPhase hσ t
  change HasDerivAt (fun u => gammaVerticalPhase σ u - (u * Real.log u - u)) _ t
  exact (hphase.sub hmain).congr_deriv (by ring)

/-- Legendre duplication at the level of the continuous vertical phases. -/
theorem gammaVerticalPhase_half_add_one (t : ℝ) :
    gammaVerticalPhase (1 / 2) t + gammaVerticalPhase 1 t +
        t * (2 * Real.log 2) = gammaVerticalPhase 1 (2 * t) := by
  let F : ℝ → ℝ := fun u => gammaVerticalPhase (1 / 2) u + gammaVerticalPhase 1 u +
    u * (2 * Real.log 2) - gammaVerticalPhase 1 (2 * u)
  have hF : ∀ u : ℝ, HasDerivAt F 0 u := by
    intro u
    let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I
    have hcond : ∀ n : ℕ, 2 * s ≠ -(n : ℂ) := by
      intro n h
      have hre := congrArg Complex.re h
      simp [s] at hre
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hdup := HTGeometry.digamma_duplication s hcond
    have htwo : 2 * s = (1 : ℂ) + ((2 * u : ℝ) : ℂ) * I := by
      dsimp [s]
      push_cast
      ring
    have hadd : s + 1 / 2 = (1 : ℂ) + (u : ℂ) * I := by
      dsimp [s]
      push_cast
      ring
    rw [htwo, hadd] at hdup
    have hdupRe :
        2 * (Complex.digamma ((1 : ℂ) + ((2 * u : ℝ) : ℂ) * I)).re =
          (Complex.digamma (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)).re +
            (Complex.digamma ((1 : ℂ) + (u : ℂ) * I)).re + 2 * Real.log 2 := by
      have := congrArg Complex.re hdup
      have hlogtwoRe : (Complex.log (2 : ℂ)).re = Real.log 2 := by
        rw [Complex.log_re]
        norm_num
      norm_num at this
      rw [hlogtwoRe] at this
      simpa [s] using this
    have hhalf := hasDerivAt_gammaVerticalPhase (by norm_num : (0 : ℝ) < 1 / 2) u
    have hone := hasDerivAt_gammaVerticalPhase (by norm_num : (0 : ℝ) < 1) u
    have hlinear : HasDerivAt (fun x : ℝ => x * (2 * Real.log 2))
        (2 * Real.log 2) u := by
      simpa only [id_eq, one_mul] using (hasDerivAt_id u).mul_const (2 * Real.log 2)
    have hscale : HasDerivAt (fun x : ℝ => 2 * x) 2 u := by
      simpa using (hasDerivAt_id u).const_mul 2
    have hdouble := (hasDerivAt_gammaVerticalPhase (by norm_num : (0 : ℝ) < 1) (2 * u)).comp
      u hscale
    have hzero :
        (Complex.digamma (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)).re +
            (Complex.digamma ((1 : ℂ) + (u : ℂ) * I)).re + 2 * Real.log 2 -
              (Complex.digamma ((1 : ℂ) + ((2 * u : ℝ) : ℂ) * I)).re * 2 = 0 := by
      rw [← hdupRe]
      ring
    have hraw := ((hhalf.add hone).add hlinear).sub hdouble
    refine (hraw.congr_deriv hzero).congr_of_eventuallyEq ?_
    filter_upwards [] with x
    rfl
  have hconst : F t = F 0 := by
    refine is_const_of_fderiv_eq_zero (fun x => (hF x).differentiableAt) (fun x => ?_) t 0
    have hx := (hF x).hasFDerivAt.fderiv
    rw [hx]
    ext
    simp
  have hFzero : F t = 0 := by simpa [F, gammaVerticalPhase] using hconst
  dsimp [F] at hFzero
  linarith

/-- Duplication identifies the critical-line remainder without any unknown integration constant. -/
theorem gammaVerticalPhaseRemainder_half_eq_sub {t : ℝ} (ht : 0 < t) :
    gammaVerticalPhaseRemainder (1 / 2) t =
      gammaVerticalPhaseRemainder 1 (2 * t) - gammaVerticalPhaseRemainder 1 t := by
  rw [gammaVerticalPhaseRemainder, gammaVerticalPhaseRemainder,
    gammaVerticalPhaseRemainder, ← gammaVerticalPhase_half_add_one t]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht.ne']
  ring

/-- Constant-sensitive critical-line Stirling phase estimate. -/
theorem abs_gammaVerticalPhase_half_sub_main_le {t : ℝ} (ht : 2 ≤ t) :
    |gammaVerticalPhase (1 / 2) t - (t * Real.log t - t)| ≤ 8 / t := by
  have ht0 : 0 < t := by linarith
  have h2t : t ≤ 2 * t := by linarith
  let e : ℝ → ℝ := fun u =>
    (Complex.digamma ((1 : ℂ) + (u : ℂ) * I)).re - Real.log u
  have hecont : ContinuousOn e (Set.uIcc t (2 * t)) := by
    refine (continuous_digammaVerticalRe (by norm_num : (0 : ℝ) < 1)).continuousOn.sub ?_
    refine Real.continuousOn_log.mono fun u hu => ?_
    rw [Set.uIcc_of_le h2t, Set.mem_Icc] at hu
    exact Set.mem_compl_singleton_iff.mpr (by linarith [hu.1])
  have hint :
      ∫ u in t..(2 * t), e u =
        gammaVerticalPhaseRemainder 1 (2 * t) - gammaVerticalPhaseRemainder 1 t := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro u hu
      rw [Set.uIcc_of_le h2t, Set.mem_Icc] at hu
      simpa [e] using hasDerivAt_gammaVerticalPhaseRemainder (by norm_num : (0 : ℝ) < 1)
        (lt_of_lt_of_le ht0 hu.1)
    · exact hecont.intervalIntegrable
  have hbound : ∀ u ∈ Set.uIoc t (2 * t), ‖e u‖ ≤ 8 / t ^ 2 := by
    intro u hu
    rw [Set.uIoc_of_le h2t] at hu
    have hu2 : 2 ≤ u := ht.trans hu.1.le
    have heu : |e u| ≤ 8 / u ^ 2 := by simpa [e] using abs_re_digamma_one_sub_log_le hu2
    rw [Real.norm_eq_abs]
    refine heu.trans ?_
    have hsquare : t ^ 2 ≤ u ^ 2 := by nlinarith [ht0, hu.1.le]
    exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos ht0) hsquare
  have hintegral := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs, hint] at hintegral
  have habs : |2 * t - t| = t := by
    rw [show 2 * t - t = t by ring, abs_of_pos ht0]
  rw [habs] at hintegral
  rw [show (8 / t ^ 2) * t = 8 / t by field_simp [ht0.ne']] at hintegral
  change |gammaVerticalPhaseRemainder (1 / 2) t| ≤ 8 / t
  rw [gammaVerticalPhaseRemainder_half_eq_sub ht0]
  exact hintegral

end RHTower
