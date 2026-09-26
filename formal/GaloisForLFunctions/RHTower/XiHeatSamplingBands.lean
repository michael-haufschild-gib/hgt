import GaloisForLFunctions.RHTower.RiemannVonMangoldt
import GaloisForLFunctions.RHTower.XiGaussianHeatTraceCriterion

/-!
# Actual Xi zeros in separated heat-scale bands

The unconditional zero-counting asymptotic supplies a divisor copy between
height T and height 3T at every sufficiently large T. Dilated copies of this
window provide separated sampling nodes for polynomial heat energies.
-/

namespace RHTower
noncomputable section
open Filter Topology

/-- Every sufficiently large multiplicative height band contains an actual divisor copy. -/
theorem eventually_exists_xiSpectralPoint_in_triple_band :
    ∀ᶠ T : ℝ in atTop, ∃ q : XiZeroCopy,
      T < (xiSpectralPoint q).re ∧ (xiSpectralPoint q).re ≤ 3 * T := by
  classical
  obtain ⟨T₀, hT₀, hN⟩ := exists_xiZeroCount_close (1 / (8 * Real.pi)) (by positivity)
  filter_upwards [eventually_ge_atTop T₀] with T hT
  have hT1 : 1 < T := by linarith
  have hT0 : 0 < T := by linarith
  have hA := abs_le.mp (hN T hT)
  have hB := abs_le.mp (hN (3 * T) (by linarith))
  let k : ℝ := 1 / (8 * Real.pi)
  have hk : 0 < k := by dsimp [k]; positivity
  have he : 1 / (2 * Real.pi) = 4 * k := by dsimp [k]; ring
  rw [he] at hA hB
  change -(k * (T * Real.log T)) ≤ _ ∧ _ ≤ k * (T * Real.log T) at hA
  change -(k * (3 * T * Real.log (3 * T))) ≤ _ ∧
    _ ≤ k * (3 * T * Real.log (3 * T)) at hB
  have hlog := Real.log_le_log hT0 (show T ≤ 3 * T by linarith)
  have hprod : 3 * k * (3 * T * Real.log T) ≤
      3 * k * (3 * T * Real.log (3 * T)) := by gcongr
  have hpos : 0 < k * (T * Real.log T) :=
    mul_pos hk (mul_pos hT0 (Real.log_pos hT1))
  have hcount : (xiZeroCount T : ℝ) < (xiZeroCount (3 * T) : ℝ) := by
    nlinarith only [hA.2, hB.1, hprod, hpos]
  have hnot : ¬ xiSupportsPos (3 * T) ⊆ xiSupportsPos T := by
    intro hsub
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun ρ => (xiSupportMultiplicity ρ : ℝ)) (fun _ _ _ => Nat.cast_nonneg _)
    have e1 := congrArg (fun n : ℤ => (n : ℝ)) (xiZeroCount_eq_pos_sum hT0.le)
    have e3 := congrArg (fun n : ℤ => (n : ℝ))
      (xiZeroCount_eq_pos_sum (show 0 ≤ 3 * T by positivity))
    push_cast at e1 e3
    rw [← e1, ← e3] at hle
    exact (not_le_of_gt hcount) hle
  obtain ⟨ρ, hρ, hρnot⟩ := Finset.not_subset.mp hnot
  have hρmem := mem_xiSupportsPos.mp hρ
  have hρupper : (ρ : ℂ).im ≤ 3 * T := by
    simpa only [abs_of_pos hρmem.2] using hρmem.1
  have hρlower : T < (ρ : ℂ).im := by
    by_contra h
    apply hρnot
    rw [mem_xiSupportsPos]
    exact ⟨by rw [abs_of_pos hρmem.2]; exact le_of_not_gt h, hρmem.2⟩
  have hm : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
    have := xi_divisor_pos_on_support ρ
    omega
  refine ⟨⟨ρ, ⟨0, hm⟩⟩, ?_⟩
  simpa only [xiSpectralPoint_re_eq] using And.intro hρlower hρupper

/-- The squared nodes at the heat scale have a uniform three-band separation. -/
theorem eventually_exists_xiHeat_three_separated_nodes :
    ∀ᶠ τ : ℝ in atBot, ∃ q : Fin 3 → XiZeroCopy,
      let z := fun i => (Real.exp τ : ℂ) * xiSpectralPoint (q i) ^ 2
      (∀ i, ‖z i‖ ≤ 2305) ∧
        1 ≤ (z 1).re - (z 0).re ∧ 1 ≤ (z 2).re - (z 1).re := by
  have hT : Tendsto (fun τ : ℝ => Real.exp (-τ / 2)) atBot atTop := by
    apply Real.tendsto_exp_atTop.comp
    convert tendsto_neg_atBot_atTop.atTop_mul_const (show (0 : ℝ) < 1 / 2 by positivity)
      using 1
    ext τ
    ring
  have h0 := hT.eventually eventually_exists_xiSpectralPoint_in_triple_band
  have h1 := (hT.const_mul_atTop (show (0 : ℝ) < 4 by positivity)).eventually
    eventually_exists_xiSpectralPoint_in_triple_band
  have h2 := (hT.const_mul_atTop (show (0 : ℝ) < 16 by positivity)).eventually
    eventually_exists_xiSpectralPoint_in_triple_band
  filter_upwards [h0, h1, h2, eventually_le_atBot (0 : ℝ)] with τ h0 h1 h2 hτ
  obtain ⟨q0, hq0L, hq0U⟩ := h0
  obtain ⟨q1, hq1L, hq1U⟩ := h1
  obtain ⟨q2, hq2L, hq2U⟩ := h2
  let t := Real.exp τ
  let T := Real.exp (-τ / 2)
  have ht : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := by simpa [t] using Real.exp_le_exp.mpr hτ
  have hT0 : 0 < T := Real.exp_pos _
  have htT : t * T ^ 2 = 1 := by
    dsimp [t, T]
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  have hb (q : XiZeroCopy) (L U : ℝ) (hL : 0 ≤ L)
      (hl : L * T ≤ (xiSpectralPoint q).re)
      (hu : (xiSpectralPoint q).re ≤ U * T) :
      L ^ 2 - 1 ≤ (((t : ℂ) * xiSpectralPoint q ^ 2).re) ∧
      (((t : ℂ) * xiSpectralPoint q ^ 2).re) ≤ U ^ 2 ∧
      ‖(t : ℂ) * xiSpectralPoint q ^ 2‖ ≤ U ^ 2 + 1 := by
    have hs : (xiSpectralPoint q).im ^ 2 < 1 / 4 := by
      have him : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by
        simp [xiSpectralPoint]
      rw [him, neg_sq]
      exact xi_divisor_support_centered_re_sq_lt_quarter q.1
    have hreal0 : 0 ≤ (xiSpectralPoint q).re := (mul_nonneg hL hT0.le).trans hl
    have hU0 : 0 ≤ U * T := hreal0.trans hu
    have hlow := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (mul_nonneg hL hT0.le) hreal0).2 hl) ht.le
    have hupp := mul_le_mul_of_nonneg_left ((sq_le_sq₀ hreal0 hU0).2 hu) ht.le
    have hscale (x : ℝ) : t * (x * T) ^ 2 = x ^ 2 := by
      calc _ = x ^ 2 * (t * T ^ 2) := by ring
           _ = _ := by rw [htT, mul_one]
    rw [hscale] at hlow hupp
    have him0 := mul_nonneg ht.le (sq_nonneg (xiSpectralPoint q).im)
    have him1 : t * (xiSpectralPoint q).im ^ 2 ≤ 1 := by
      have hm := mul_le_mul_of_nonneg_left hs.le ht.le
      nlinarith
    have hre : ((t : ℂ) * xiSpectralPoint q ^ 2).re =
        t * ((xiSpectralPoint q).re ^ 2 - (xiSpectralPoint q).im ^ 2) := by
      simp [pow_two, Complex.mul_re]
    have hn : ‖(t : ℂ) * xiSpectralPoint q ^ 2‖ =
        t * ((xiSpectralPoint q).re ^ 2 + (xiSpectralPoint q).im ^ 2) := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
        Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [hre, hn]
    constructor
    · nlinarith
    constructor <;> nlinarith
  have b0 := hb q0 1 3 (by positivity) (by simpa [T] using hq0L.le)
    (by simpa [T] using hq0U)
  have b1 := hb q1 4 12 (by positivity) hq1L.le (by dsimp [T]; linarith)
  have b2 := hb q2 16 48 (by positivity) hq2L.le (by dsimp [T]; linarith)
  refine ⟨![q0, q1, q2], ?_⟩
  dsimp only
  constructor
  · intro i
    dsimp only [t] at b0 b1 b2
    fin_cases i
    · change ‖(Real.exp τ : ℂ) * xiSpectralPoint q0 ^ 2‖ ≤ 2305
      linarith [b0.2.2]
    · change ‖(Real.exp τ : ℂ) * xiSpectralPoint q1 ^ 2‖ ≤ 2305
      linarith [b1.2.2]
    · change ‖(Real.exp τ : ℂ) * xiSpectralPoint q2 ^ 2‖ ≤ 2305
      linarith [b2.2.2]
  · change 1 ≤ ((Real.exp τ : ℂ) * xiSpectralPoint q1 ^ 2).re -
        ((Real.exp τ : ℂ) * xiSpectralPoint q0 ^ 2).re ∧
      1 ≤ ((Real.exp τ : ℂ) * xiSpectralPoint q2 ^ 2).re -
        ((Real.exp τ : ℂ) * xiSpectralPoint q1 ^ 2).re
    dsimp only [t] at b0 b1 b2
    constructor <;> linarith [b0.2.1, b1.1, b1.2.1, b2.1]

end
end RHTower
