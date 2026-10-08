import GaloisForLFunctions.RHTower.WeilWorkQuantizationTwistContour

/-!
# Exact resonant Dirichlet terms for spectral quantization

Preserve the exponential scaling at each arithmetic resonance. The absolute
kernel bound supplies a summable majorant, so erasing the resonant terms
leaves a vanishing radial series without a uniform frequency-separation
assumption. These analytic lemmas support the actual-source resonance law;
they do not assert a periodic representation of the source phase.
-/

open Complex Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RHTower.WeilSpectral
open TruncatedRadial AbelianTwist RightEdgeKernel IntegerMassRigidity HamburgerStability

/-- The arithmetic resonance retains its exponential scaling factor. -/
theorem quantization_twist_term_resonant (a : ℕ → ℂ) {ω : ℝ} {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hres : Real.log n + ω / 2 = Real.log m) (s : ℂ) :
    LSeries.term a s n * linTwist ω s =
      ((Real.exp (ω / 4) : ℝ) : ℂ) * a n * (m : ℂ) ^ (-s) := by
  have hn0 : n ≠ 0 := by omega
  rw [LSeries.term_of_ne_zero hn0, natCast_cpow_eq_exp hn, natCast_cpow_eq_exp hm]
  unfold linTwist
  rw [div_eq_mul_inv, ← Complex.exp_neg, Complex.ofReal_exp]
  calc a n * cexp (-((Real.log n : ℂ) * s)) *
        cexp (-((↑(ω / 2) : ℂ) * (s - 1 / 2))) =
      a n * cexp (-((Real.log n : ℂ) * s) - ((↑(ω / 2) : ℂ) * (s - 1 / 2))) := by
        rw [mul_assoc, ← Complex.exp_add]; congr 2
    _ = a n * cexp ((↑(ω / 4) : ℂ) + (Real.log m : ℂ) * (-s)) := by
      congr 2
      rw [← hres]
      push_cast
      ring
    _ = _ := by rw [Complex.exp_add]; ring

/-- Each shifted resonant right-edge term is exactly the common main kernel. -/
theorem quantization_twEdgeTerm_resonant (a : ℕ → ℂ) {ω : ℝ} {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hres : Real.log n + ω / 2 = Real.log m)
    (τ : ℂ) (B : ℝ) :
    twEdgeTerm a ω τ B n = ((Real.exp (ω / 4) : ℝ) : ℂ) * a n *
      ∫ y in Iic B, (m : ℂ) ^ (-edgePt y) * offKernel τ (edgePt y) := by
  unfold twEdgeTerm
  simp only [quantization_twist_term_resonant a hm hn hres, mul_assoc]
  rw [integral_const_mul, integral_const_mul]

/-- Fixed nonresonant frequencies vanish after radial scaling. -/
theorem tendsto_quantization_twEdgeTerm_nonres (a : ℕ → ℂ) (ω : ℝ)
    {m n : ℕ} (hm : 1 ≤ m)
    (hres : Real.log n + ω / 2 ≠ Real.log m) {B : ℝ} (hB : B ≤ -1) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * twEdgeTerm a ω ((ε : ℂ) + (m : ℂ) * I) B n)
      (𝓝[>] 0) (𝓝 0) := by
  by_cases hn0 : n = 0
  · subst n
    simp only [twEdgeTerm, LSeries.term_zero, zero_mul, integral_zero, mul_zero]
    exact tendsto_const_nhds
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  let τ : ℝ → ℂ := fun ε => (ε : ℂ) + (m : ℂ) * I
  let ℓ : ℝ := Real.log n + ω / 2
  have ht : Tendsto (fun ε : ℝ => ‖τ ε‖) (𝓝[>] 0) (𝓝 (m : ℝ)) := by
    have hc : Continuous fun ε : ℝ => ‖τ ε‖ := by dsimp [τ]; fun_prop
    simpa [τ] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hl := ((Real.continuousAt_log hmpos.ne').tendsto.comp ht).sub_const ℓ
  have hd : |Real.log m - ℓ| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hres.symm)
  have hp := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).tendsto (m : ℝ) |>.comp ht
  let H : ℝ → ℝ := fun ε => ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ * Real.exp (-(ω / 2)) *
    (2 * ‖τ ε‖ ^ (1 / 2 : ℝ) / |Real.log ‖τ ε‖ - ℓ| +
      4 * ‖τ ε‖ ^ (1 / 2 : ℝ) / Real.pi)
  have hH : Tendsto H (𝓝[>] 0) (𝓝 (‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ * Real.exp (-(ω / 2)) *
      (2 * (m : ℝ) ^ (1 / 2 : ℝ) / |Real.log m - ℓ| +
        4 * (m : ℝ) ^ (1 / 2 : ℝ) / Real.pi))) :=
    (((hp.const_mul 2).div hl.abs hd).add ((hp.const_mul 4).div_const Real.pi)).const_mul _
  have hlim : Tendsto (fun ε : ℝ => ε * H ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_id.mono_left nhdsWithin_le_nhds).mul hH
  apply squeeze_zero_norm' _ hlim
  have hne := hl.abs.eventually (eventually_ne_nhds hd)
  filter_upwards [self_mem_nhdsWithin, hne] with ε (hε : 0 < ε) hεne
  have hτre : 0 < (τ ε).re := by simpa [τ] using hε
  have he1 : Real.exp (B * ((Real.pi - ((Real.pi : ℂ) * τ ε ^ 2).arg) / 2)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [Complex.arg_le_pi ((Real.pi : ℂ) * τ ε ^ 2)])
  have he2 : Real.exp (Real.pi * B) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le (by linarith))
  have hne' : Real.log ‖τ ε‖ ≠ ℓ := by intro h; simp [h] at hεne
  have hb := norm_twEdgeTerm_le a ω hτre hn hne' hB
  have hb' : ‖twEdgeTerm a ω (τ ε) B n‖ ≤ H ε := by
    apply hb.trans
    calc _ ≤ ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ * Real.exp (-(ω / 2)) *
        (2 * ‖τ ε‖ ^ (1 / 2 : ℝ) * 1 / |Real.log ‖τ ε‖ - ℓ| +
          4 * ‖τ ε‖ ^ (1 / 2 : ℝ) * 1 / Real.pi) := by
            gcongr
      _ = H ε := by simp [H]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  exact mul_le_mul_of_nonneg_left hb' hε.le

/-- Every Dirichlet term has a summable radial majorant, including resonances. -/
theorem norm_quantization_twEdgeTerm_radial_le (a : ℕ → ℂ) (ω : ℝ)
    {m : ℕ} (hm : 1 ≤ m) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {B : ℝ} (hB : B ≤ -1) (n : ℕ) :
    ‖(ε : ℂ) * twEdgeTerm a ω ((ε : ℂ) + (m : ℂ) * I) B n‖ ≤
      ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ * Real.exp (-(ω / 2)) *
        (4 * Real.pi ^ (3 / 4 : ℝ) * ((m : ℝ) + 1) ^ 2) := by
  let τ : ℂ := (ε : ℂ) + (m : ℂ) * I
  let δ : ℝ := ε / ‖τ‖
  let Q : ℝ := 4 * Real.pi ^ (3 / 4 : ℝ)
  let D : ℝ := ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ * Real.exp (-(ω / 2))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hτre : τ.re = ε := by simp [τ]
  have hτ1 : 1 ≤ ‖τ‖ := by
    have h := Complex.abs_im_le_norm τ
    have him : τ.im = m := by simp [τ]
    rw [him, abs_of_nonneg (by positivity)] at h
    linarith
  have hτM : ‖τ‖ ≤ (m : ℝ) + 1 := by
    have h := norm_add_le (ε : ℂ) ((m : ℂ) * I)
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast,
      Real.norm_eq_abs, abs_of_pos hε] at h
    exact h.trans (by linarith)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hεδ : ε / δ = ‖τ‖ := by dsimp [δ]; field_simp
  have hb : ‖twEdgeTerm a ω τ B n‖ ≤ D * Q * ‖τ‖ * (Real.exp (δ * B) / δ) := by
    have hint := (integrableOn_exp_mul_Iic hδ B).const_mul (D * Q * ‖τ‖)
    refine (norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Iic).mpr
      (Eventually.of_forall fun y hy => ?_))).trans (le_of_eq ?_)
    · have hy' : y ≤ B := hy
      rw [norm_mul, norm_mul, norm_term_edgePt, norm_linTwist_edgePt]
      have hk := norm_offKernel_le (by simpa [τ] using hε) hτ1
        (x := 3 / 2) (y := y) (by norm_num) le_rfl
        (by rw [abs_of_neg (by linarith)]; linarith)
      rw [abs_of_neg (by linarith : y < 0), hτre] at hk
      have ht := mul_le_mul_of_nonneg_left hk hD
      calc _ ≤ D * (Q * ‖τ‖ * Real.exp (-(-y * (ε / ‖τ‖)))) := ht
        _ = D * Q * ‖τ‖ * Real.exp (δ * y) := by
          dsimp [δ]
          rw [show -(-y * (ε / ‖τ‖)) = ε / ‖τ‖ * y by ring]
          ring
    · rw [integral_const_mul, integral_exp_mul_Iic hδ]
  have he : Real.exp (δ * B) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonneg_of_nonpos hδ.le (by linarith))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  calc ε * ‖twEdgeTerm a ω τ B n‖ ≤ ε * (D * Q * ‖τ‖ * (Real.exp (δ * B) / δ)) :=
        mul_le_mul_of_nonneg_left hb hε.le
    _ = D * Q * ‖τ‖ * Real.exp (δ * B) * (ε / δ) := by ring
    _ ≤ D * Q * ((m : ℝ) + 1) * 1 * ((m : ℝ) + 1) := by rw [hεδ]; gcongr
    _ = _ := by dsimp [D, Q]; ring

/-- Erasing exactly the arithmetic resonances leaves a vanishing radial sum. -/
theorem tendsto_quantization_nonresonant_edge_sum {a : ℕ → ℂ}
    (ha : Summable fun n => ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖)
    (ω : ℝ) {m : ℕ} (hm : 1 ≤ m) {B : ℝ} (hB : B ≤ -1) :
    Tendsto (fun ε : ℝ => ∑' n : ℕ,
      if 1 ≤ n ∧ Real.log n + ω / 2 = Real.log m then (0 : ℂ)
      else (ε : ℂ) * twEdgeTerm a ω ((ε : ℂ) + (m : ℂ) * I) B n)
      (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    (𝓕 := 𝓝[>] (0 : ℝ))
    (f := fun (ε : ℝ) (n : ℕ) => if 1 ≤ n ∧ Real.log n + ω / 2 = Real.log m then (0 : ℂ)
      else (ε : ℂ) * twEdgeTerm a ω ((ε : ℂ) + (m : ℂ) * I) B n)
    (g := fun _ => (0 : ℂ))
    (bound := fun (n : ℕ) => ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ *
      (Real.exp (-(ω / 2)) * (4 * Real.pi ^ (3 / 4 : ℝ) * ((m : ℝ) + 1) ^ 2)))
    (ha.mul_right _) (fun n => ?_) ?_
  · simpa using h
  · by_cases hr : 1 ≤ n ∧ Real.log n + ω / 2 = Real.log m
    · simp only [if_pos hr]; exact tendsto_const_nhds
    · simp only [hr, if_false]
      by_cases hn : n = 0
      · subst n
        simp only [twEdgeTerm, LSeries.term_zero, zero_mul, integral_zero, mul_zero]
        exact tendsto_const_nhds
      · exact tendsto_quantization_twEdgeTerm_nonres a ω hm
          (fun he => hr ⟨Nat.one_le_iff_ne_zero.mpr hn, he⟩) hB
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε n
    by_cases hr : 1 ≤ n ∧ Real.log n + ω / 2 = Real.log m
    · simp only [if_pos hr, norm_zero]
      show 0 ≤ _
      positivity
    · simp only [hr, if_false]
      simpa only [mul_assoc] using norm_quantization_twEdgeTerm_radial_le a ω hm hε.1 hε.2.le hB n

end RHTower.WeilSpectral
