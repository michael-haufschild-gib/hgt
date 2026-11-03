import GaloisForLFunctions.SelbergClass.OrdinaryMellinGammaDecay

/-!
# Far-left bounds for the ordinary exponential Mellin kernel

The reflected sine product consumes only the fraction `degree` of the Mellin
Gamma decay. Below degree one, the remaining exponential is integrable in height.
-/

noncomputable section
open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.SelbergClass

/-- Mellin kernel for the ordinary exponential series. -/
def ordinaryMellinIntegrand (F : ExtendedSelbergClass) (s z u : ℂ) : ℂ :=
  z ^ (-u) * (Complex.Gamma u * F (s + u))

/-- The height-independent factor in the far-left majorant. -/
def ordinaryLeftMajorant (F : ExtendedSelbergClass) (s : ℂ) (x : ℝ) (k : ℕ) : ℝ :=
  x ^ k * F.gammaData.Q ^ ((1 - 2 * (s - 1 / 2).re) + 2 * (k : ℝ)) *
    (ordinaryGammaProduct F.gammaData s k / Real.Gamma ((k : ℝ) + 3 / 2))

theorem ordinaryLeftMajorant_nonneg (F : ExtendedSelbergClass) (s : ℂ)
    {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : 0 ≤ ordinaryLeftMajorant F s x k := by
  exact mul_nonneg (mul_nonneg (pow_nonneg hx _) (Real.rpow_nonneg F.gammaData.Q_pos.le _))
    (div_nonneg (ordinaryGammaProduct_nonneg _ _ _) (Real.Gamma_pos_of_pos (by positivity)).le)

private theorem pairShift_re_leftLine (D : SelbergGammaData) (s : ℂ) (k : ℕ) (t : ℝ)
    (i : Fin D.rank ⊕ Fin D.rank) :
    (D.pairShift (s + leftLine k t) i).re =
      ordinaryGammaRate D i * (k : ℝ) + (D.pairShift (s - 1 / 2) i).re := by
  cases i with
  | inl j =>
      simp [SelbergGammaData.pairShift, SelbergGammaData.shiftUp, ordinaryGammaRate,
        leftLine, Complex.mul_re]
      ring
  | inr j =>
      simp [SelbergGammaData.pairShift, SelbergGammaData.shiftDown, ordinaryGammaRate,
        leftLine, Complex.mul_re]
      ring

/-- The Gamma and sine exponentials leave decay rate `π(1-degree)/2`. -/
theorem eventually_norm_ordinaryMellinIntegrand_left_le
    (F : ExtendedSelbergClass) (hd : 0 < F.gammaData.degree) (s : ℂ)
    {x : ℝ} (hx : 0 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k : ℕ in atTop, ∀ t : ℝ,
      ‖ordinaryMellinIntegrand F s (x : ℂ) (leftLine k t)‖ ≤
        C * ordinaryLeftMajorant F s x k *
          Real.exp (-(Real.pi * (1 - F.gammaData.degree) * |t| / 2)) := by
  classical
  obtain ⟨M, hM, hMb⟩ := F.exists_bound_re_ge (σ := 2) (by norm_num)
  set CS : ℝ := (2 : ℝ) ^ F.gammaData.rank *
    Real.exp (Real.pi * ∑ j, |(F.gammaData.mu j).im|) *
    Real.exp (Real.pi * (∑ j, F.gammaData.lambda j) * |s.im|) with hCS
  have hCSpos : 0 < CS := by positivity
  set C : ℝ := x ^ (1 / 2 : ℝ) * (Real.pi * Real.sqrt 2) * CS *
    ((2 * Real.pi) ^ F.gammaData.rank)⁻¹ * M with hC
  refine ⟨C, mul_nonneg (by positivity) hM, ?_⟩
  have hsumlam : ∑ j, F.gammaData.lambda j = F.gammaData.degree / 2 := by
    rw [SelbergGammaData.degree]; ring
  have hre_bot : Tendsto (fun k : ℕ => (s - 1 / 2).re - (k : ℝ)) atTop atBot := by
    exact (tendsto_atBot_add_const_left atTop (s - 1 / 2).re
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)).congr fun k => by
        simp [sub_eq_add_neg]
  have hX_top : ∀ i, Tendsto (fun k : ℕ => ordinaryGammaRate F.gammaData i * (k : ℝ) +
      (F.gammaData.pairShift (s - 1 / 2) i).re) atTop atTop := by
    intro i
    exact tendsto_atTop_add_const_right _ _
      (tendsto_natCast_atTop_atTop.const_mul_atTop (ordinaryGammaRate_pos _ i))
  have hev : ∀ᶠ k : ℕ in atTop, (s - 1 / 2).re - (k : ℝ) ≤ -1 ∧
      (∀ j, F.gammaData.lambda j * ((s - 1 / 2).re - (k : ℝ)) <
        1 - (F.gammaData.mu j).re) ∧
      (∀ i, 0 < ordinaryGammaRate F.gammaData i * (k : ℝ) +
        (F.gammaData.pairShift (s - 1 / 2) i).re) := by
    refine (hre_bot.eventually_le_atBot (-1)).and ((Filter.eventually_all.2 fun j => ?_).and
      (Filter.eventually_all.2 fun i => (hX_top i).eventually_gt_atTop 0))
    filter_upwards [hre_bot.eventually_lt_atBot
      ((1 - (F.gammaData.mu j).re) / F.gammaData.lambda j)] with k hk
    rwa [lt_div_iff₀ (F.gammaData.lambda_pos j), mul_comm] at hk
  filter_upwards [hev] with k ⟨hkre, hkμ, hkX⟩ t
  set u := leftLine k t with hu
  set w := s + u with hw
  have hwre : w.re = (s - 1 / 2).re - (k : ℝ) := by
    simp [hw, hu, leftLine]; ring
  have hwim : w.im = s.im + t := by simp [hw, hu, leftLine]
  have hFE := F.value_eq_asymmetric_of_farLeft (s := w)
    (by rw [hwre]; linarith) (fun j => by rw [hwre]; exact hkμ j)
  have hpow : ‖(x : ℂ) ^ (-u)‖ = x ^ ((k : ℝ) + 1 / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    congr 1
    simp [hu, leftLine, add_comm]
  have hΓu : ‖Complex.Gamma u‖ ≤ Real.pi * Real.sqrt 2 *
      Real.exp (-(Real.pi * |t| / 2)) / Real.Gamma ((k : ℝ) + 3 / 2) := by
    have hu' : u = -(k : ℂ) - 1 / 2 + (t : ℂ) * I := by
      rw [hu, leftLine]; push_cast; ring
    rw [hu']
    exact norm_Gamma_neg_half_line_le_exp k t
  have hS : ‖F.gammaData.asymmetricS w‖ ≤
      CS * Real.exp (Real.pi * F.gammaData.degree * |t| / 2) := by
    refine (F.gammaData.norm_asymmetricS_le w).trans ?_
    have hexpo : Real.pi * (∑ j, F.gammaData.lambda j) * |s.im + t| ≤
        Real.pi * (∑ j, F.gammaData.lambda j) * |s.im| +
          Real.pi * F.gammaData.degree * |t| / 2 := by
      calc _ ≤ Real.pi * (∑ j, F.gammaData.lambda j) * (|s.im| + |t|) :=
            mul_le_mul_of_nonneg_left (abs_add_le _ _) (by rw [hsumlam]; positivity)
        _ = _ := by rw [hsumlam]; ring
    rw [hwim, hCS, mul_assoc _ (Real.exp (Real.pi * (∑ j, F.gammaData.lambda j) * |s.im|)),
      ← Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexpo) (by positivity)
  have hR : ‖selbergConjugateReflection F w‖ ≤ M := by
    rw [selbergConjugateReflection, norm_star]
    apply hMb
    rw [Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re, hwre]
    linarith only [hkre]
  have hH : ‖F.gammaData.asymmetricH w‖ ≤
      ((2 * Real.pi) ^ F.gammaData.rank)⁻¹ *
        F.gammaData.Q ^ ((1 - 2 * (s - 1 / 2).re) + 2 * (k : ℝ)) *
          ordinaryGammaProduct F.gammaData s k := by
    have hnorm := F.gammaData.norm_asymmetricH_shift hd w 0
    simp only [Nat.cast_zero, zero_div, sub_zero, mul_zero, add_zero,
      Complex.ofReal_zero, zero_add] at hnorm
    rw [hnorm, hwre, show 1 - 2 * ((s - 1 / 2).re - (k : ℝ)) =
      (1 - 2 * (s - 1 / 2).re) + 2 * (k : ℝ) by ring]
    refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod
      (fun i _ => norm_nonneg _) fun i _ => ?_)
        (mul_nonneg (by positivity) (Real.rpow_nonneg F.gammaData.Q_pos.le _))
    have hre := pairShift_re_leftLine F.gammaData s k t i
    change (F.gammaData.pairShift w i).re = _ at hre
    have hbound := norm_Gamma_le_Gamma_re (by rw [hre]; exact hkX i)
    refine hbound.trans_eq ?_
    rw [hre]
    have harg : (((ordinaryGammaRate F.gammaData i * (k : ℝ) : ℝ) : ℂ) +
        ((F.gammaData.pairShift (s - 1 / 2) i).re : ℂ)) =
        ((ordinaryGammaRate F.gammaData i * (k : ℝ) +
          (F.gammaData.pairShift (s - 1 / 2) i).re : ℝ) : ℂ) := by push_cast; rfl
    rw [harg, Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.Gamma_pos_of_pos (hkX i))]
  have hΓk : 0 < Real.Gamma ((k : ℝ) + 3 / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hSb : 0 ≤ CS * Real.exp (Real.pi * F.gammaData.degree * |t| / 2) := by positivity
  have hHb : 0 ≤ ((2 * Real.pi) ^ F.gammaData.rank)⁻¹ *
      F.gammaData.Q ^ ((1 - 2 * (s - 1 / 2).re) + 2 * (k : ℝ)) *
        ordinaryGammaProduct F.gammaData s k :=
    mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg F.gammaData.Q_pos.le _))
      (ordinaryGammaProduct_nonneg _ _ _)
  have hΓb : 0 ≤ Real.pi * Real.sqrt 2 * Real.exp (-(Real.pi * |t| / 2)) /
      Real.Gamma ((k : ℝ) + 3 / 2) := div_nonneg (by positivity) hΓk.le
  have hb := mul_le_mul_of_nonneg_left
    (mul_le_mul hΓu
      (mul_le_mul (mul_le_mul hS hH (norm_nonneg _) hSb) hR (norm_nonneg _)
        (mul_nonneg hSb hHb)) (by positivity) hΓb)
      (Real.rpow_nonneg hx.le ((k : ℝ) + 1 / 2))
  rw [ordinaryMellinIntegrand, ← hw, hFE]
  simp only [norm_mul]
  rw [F.gammaData.norm_invariantRootNumber, one_mul, hpow]
  refine hb.trans_eq ?_
  have hxpow : x ^ ((k : ℝ) + 1 / 2) = x ^ (1 / 2 : ℝ) * x ^ k := by
    rw [Real.rpow_add hx, Real.rpow_natCast]; ring
  have hexp : Real.exp (-(Real.pi * |t| / 2)) *
      Real.exp (Real.pi * F.gammaData.degree * |t| / 2) =
        Real.exp (-(Real.pi * (1 - F.gammaData.degree) * |t| / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc _ = C * ordinaryLeftMajorant F s x k *
      (Real.exp (-(Real.pi * |t| / 2)) *
        Real.exp (Real.pi * F.gammaData.degree * |t| / 2)) := by
          rw [hxpow, hC, ordinaryLeftMajorant]
          ring
    _ = _ := by rw [hexp]

end GaloisForLFunctions.SelbergClass
