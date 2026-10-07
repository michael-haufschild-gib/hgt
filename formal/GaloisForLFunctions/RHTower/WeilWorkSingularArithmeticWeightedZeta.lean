import GaloisForLFunctions.RHTower.ZetaVerticalMeanSquare

/-!
# Fractionally weighted zeta mass on the actual vertical line

The unconditional dyadic second moment makes the zeta norm integrable against
every weight `t^(-1-η)` at positive height, for `η > 0`. This is the weighted
mass needed to sharpen the ordinary quotient-coefficient sums in WP03.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

/-- Dyadic mass of order `T log³ T` is integrable against any strictly stronger
than harmonic power weight. The conclusion concerns the actual function. -/
theorem integrableOn_mul_rpow_of_dyadic_logCube {F : ℝ → ℝ} {C η : ℝ}
    (hF : ContinuousOn F (Ici 2)) (hF0 : ∀ t : ℝ, 0 ≤ F t) (hC : 0 ≤ C)
    (hη : 0 < η)
    (hbound : ∀ T : ℝ, 2 ≤ T →
      ∫ t in T..(2 * T), F t ≤ C * T * (1 + Real.log T) ^ 3) :
    IntegrableOn (fun t : ℝ => F t * t ^ (-1 - η)) (Ici 2) := by
  let S : ℕ → Set ℝ := fun n => Icc ((2 : ℝ) ^ (n + 1)) (2 * (2 : ℝ) ^ (n + 1))
  let r : ℝ := 2 ^ (-η)
  let D : ℝ := C * (1 + Real.log 2) ^ 3
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeom : Summable (fun n : ℕ => D * ((n + 1 : ℕ) : ℝ) ^ 3 * r ^ (n + 1)) := by
    have h := ((summable_nat_add_iff 1).mpr
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3 hr1)).mul_left D
    simpa only [mul_assoc] using h
  have hT : ∀ n : ℕ, (2 : ℝ) ≤ 2 ^ (n + 1) := by
    intro n
    have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith
  have hsub : ∀ n : ℕ, S n ⊆ Ici (2 : ℝ) := fun n _ hx => (hT n).trans hx.1
  have hw : ContinuousOn (fun t : ℝ => F t * t ^ (-1 - η)) (Ici 2) :=
    hF.mul (continuousOn_id.rpow_const fun t ht => Or.inl (by
      have : (2 : ℝ) ≤ t := ht
      change t ≠ 0
      linarith))
  have hi : ∀ n : ℕ, IntegrableOn (fun t : ℝ => F t * t ^ (-1 - η)) (S n) :=
    fun n => (hw.mono (hsub n)).integrableOn_Icc
  have hmass : ∀ n : ℕ,
      ∫ t in S n, ‖F t * t ^ (-1 - η)‖ ≤
        D * ((n + 1 : ℕ) : ℝ) ^ 3 * r ^ (n + 1) := by
    intro n
    let T : ℝ := 2 ^ (n + 1)
    have hT2 : 2 ≤ T := hT n
    have hT0 : 0 < T := by linarith
    have hTT : T ≤ 2 * T := by linarith
    have hFT : IntegrableOn F (S n) := (hF.mono (hsub n)).integrableOn_Icc
    have hpoint : ∀ᵐ t ∂volume.restrict (S n),
        F t * t ^ (-1 - η) ≤ F t * T ^ (-1 - η) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hT0 ht.1 (by linarith)) (hF0 t)
    have hB := hbound T hT2
    rw [intervalIntegral.integral_of_le hTT, ← integral_Icc_eq_integral_Ioc] at hB
    have hpow : T * T ^ (-1 - η) = T ^ (-η) := by
      nth_rw 1 [← Real.rpow_one T]
      rw [← Real.rpow_add hT0]
      congr 1
      ring
    have hTr : T ^ (-η) = r ^ (n + 1) := by
      dsimp [T, r]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
        Real.rpow_mul (by norm_num), Real.rpow_natCast]
    have hlog : (1 + Real.log T) ^ 3 ≤
        (((n + 1 : ℕ) : ℝ) * (1 + Real.log 2)) ^ 3 := by
      apply pow_le_pow_left₀
      · have := Real.log_nonneg (show 1 ≤ T by linarith)
        linarith
      · dsimp [T]
        rw [Real.log_pow]
        have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        linarith
    calc
      _ = ∫ t in S n, F t * t ^ (-1 - η) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact mul_nonneg (hF0 t) (Real.rpow_nonneg (hT0.le.trans ht.1) _)
      _ ≤ (∫ t in S n, F t) * T ^ (-1 - η) := by
        simpa only [integral_mul_const] using
          integral_mono_ae (hi n) (hFT.mul_const (T ^ (-1 - η))) hpoint
      _ ≤ (C * T * (1 + Real.log T) ^ 3) * T ^ (-1 - η) :=
        mul_le_mul_of_nonneg_right hB (by positivity)
      _ = C * (1 + Real.log T) ^ 3 * T ^ (-η) := by rw [← hpow]; ring
      _ ≤ C * ((((n + 1 : ℕ) : ℝ) * (1 + Real.log 2)) ^ 3) * T ^ (-η) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hC) (by positivity)
      _ = D * ((n + 1 : ℕ) : ℝ) ^ 3 * r ^ (n + 1) := by
        rw [hTr]
        dsimp [D]
        ring
  have hsum : Summable (fun n : ℕ => ∫ t in S n, ‖F t * t ^ (-1 - η)‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hmass hgeom
  apply (integrableOn_iUnion_of_summable_integral_norm hi hsum).mono_set
  intro x hx
  have hx2 : (2 : ℝ) ≤ x := hx
  obtain ⟨n, hlo, hhi⟩ := exists_nat_pow_near (x := x / 2) (y := (2 : ℝ))
    (by linarith) (by norm_num)
  refine mem_iUnion.mpr ⟨n, ?_⟩
  change 2 ^ (n + 1) ≤ x ∧ x ≤ 2 * 2 ^ (n + 1)
  constructor
  · rw [pow_succ]
    linarith
  · linarith

/-- Continuity of the zeta norm on the actual positive-height ray avoids the
pole without imposing any zero-free condition. -/
theorem continuousOn_norm_zeta_positive_line (σ : ℝ) :
    ContinuousOn (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖) (Ici 2) := by
  intro t ht
  have hne : (σ : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro h
    have h' := congrArg Complex.im h
    simp at h'
    have : (2 : ℝ) ≤ t := ht
    linarith
  have hline : Continuous (fun u : ℝ => (σ : ℂ) + (u : ℂ) * I) :=
    continuous_const.add (Complex.continuous_ofReal.mul_const I)
  have hAt : ContinuousAt (fun u : ℝ => riemannZeta ((σ : ℂ) + (u : ℂ) * I)) t :=
    (differentiableAt_riemannZeta hne).continuousAt.comp
      (f := fun u : ℝ => (σ : ℂ) + (u : ℂ) * I) hline.continuousAt
  exact hAt.norm.continuousWithinAt

/-- Every strictly stronger than harmonic power weight is integrable against
the zeta norm on any actual vertical line in the right critical strip. -/
theorem integrableOn_norm_zeta_mul_rpow_Ici {σ η : ℝ}
    (hσ : 1 / 2 ≤ σ) (hσ3 : σ ≤ 3) (hη : 0 < η) :
    IntegrableOn (fun t : ℝ =>
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ * t ^ (-1 - η)) (Ici 2) := by
  obtain ⟨C, hC, hmoment⟩ := exists_integral_normSq_zeta_vertical_le
  have hc := continuousOn_norm_zeta_positive_line σ
  refine integrableOn_mul_rpow_of_dyadic_logCube hc (fun _ => norm_nonneg _)
    (show 0 ≤ 1 + C by linarith) hη (C := 1 + C) ?_
  intro T hT
  have hTT : T ≤ 2 * T := by linarith
  have hcont : ContinuousOn (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖)
      (uIcc T (2 * T)) := by
    rw [uIcc_of_le hTT]
    exact hc.mono fun _ ht => hT.trans ht.1
  have hint := hcont.intervalIntegrable (μ := volume)
  have hsq : IntervalIntegrable (fun t : ℝ =>
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume T (2 * T) :=
    (hcont.pow 2).intervalIntegrable
  have hpoint : ∀ t ∈ Icc T (2 * T),
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        1 + ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    intro t _
    nlinarith [sq_nonneg (‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ - 1)]
  have hlog : 1 ≤ (1 + Real.log T) ^ 3 :=
    one_le_pow₀ (by have := Real.log_nonneg (show 1 ≤ T by linarith); linarith)
  calc
    _ ≤ ∫ t in T..(2 * T), (1 + ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) :=
      intervalIntegral.integral_mono_on hTT hint ((intervalIntegrable_const).add hsq) hpoint
    _ = T + ∫ t in T..(2 * T), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
      rw [intervalIntegral.integral_add intervalIntegrable_const hsq]
      simp [intervalIntegral.integral_const]
      ring
    _ ≤ T + C * T * (1 + Real.log T) ^ 3 := add_le_add le_rfl (hmoment T hT σ hσ hσ3)
    _ ≤ (1 + C) * T * (1 + Real.log T) ^ 3 := by nlinarith

/-- Off the pole's abscissa the entire actual zeta line is continuous. -/
theorem continuous_norm_zeta_line {σ : ℝ} (hσ : σ ≠ 1) :
    Continuous (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hne : (σ : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro h
    apply hσ
    simpa using congrArg Complex.re h
  have hline : Continuous (fun u : ℝ => (σ : ℂ) + (u : ℂ) * I) :=
    continuous_const.add (Complex.continuous_ofReal.mul_const I)
  exact ((differentiableAt_riemannZeta hne).continuousAt.comp
    (f := fun u : ℝ => (σ : ℂ) + (u : ℂ) * I) hline.continuousAt).norm

/-- The fractional weighted zeta mass is finite on the full actual line,
including both signs of height and the compact central interval. -/
theorem integrable_norm_zeta_mul_weight {σ η : ℝ}
    (hσ : 1 / 2 ≤ σ) (hσ3 : σ ≤ 3) (hσ1 : σ ≠ 1) (hη : 0 < η) :
    Integrable (fun t : ℝ =>
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ * (2 + |t|) ^ (-1 - η)) := by
  let F : ℝ → ℝ := fun t =>
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ * (2 + |t|) ^ (-1 - η)
  have hF : Continuous F :=
    (continuous_norm_zeta_line hσ1).mul
      ((continuous_const.add continuous_abs).rpow_const fun t => Or.inl (by
        change (2 : ℝ) + |t| ≠ 0
        positivity))
  have hF0 : ∀ t : ℝ, 0 ≤ F t := fun t => by dsimp [F]; positivity
  have hpos : IntegrableOn F (Ici 2) := by
    refine (integrableOn_norm_zeta_mul_rpow_Ici hσ hσ3 hη).mono'
      hF.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht2 : (2 : ℝ) ≤ t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 t)]
    dsimp [F]
    rw [abs_of_nonneg (by linarith : 0 ≤ t)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)) (norm_nonneg _)
  have heven : ∀ t : ℝ, F (-t) = F t := by
    intro t
    have hconj : (σ : ℂ) + ((-t : ℝ) : ℂ) * I =
        (starRingEnd ℂ) ((σ : ℂ) + (t : ℂ) * I) := by
      apply Complex.ext <;> simp
    dsimp [F]
    rw [hconj, riemannZeta_conj, Complex.norm_conj, abs_neg]
  have hneg : IntegrableOn F (Iic (-2)) := by
    have h := IntegrableOn.comp_neg_Iic (c := (-2 : ℝ)) (by simpa using hpos)
    exact h.congr_fun (fun t _ => heven t) measurableSet_Iic
  have hcenter : IntegrableOn F (Icc (-2) 2) := hF.continuousOn.integrableOn_Icc
  apply integrableOn_univ.mp
  apply ((hneg.union hcenter).union hpos).mono_set
  intro t _
  by_cases hleft : t ≤ -2
  · exact Or.inl (Or.inl hleft)
  by_cases hright : 2 ≤ t
  · exact Or.inr hright
  exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)

end RHTower.WeilSingularArithmetic
