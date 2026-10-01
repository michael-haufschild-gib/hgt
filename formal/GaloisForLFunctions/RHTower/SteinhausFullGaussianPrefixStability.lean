import GaloisForLFunctions.RHTower.SteinhausFullGaussianCofactorTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics


open Filter Topology Finset
noncomputable section
namespace RHTower

private theorem X_eq_of_phase_prefix {B n : ℕ} (hn : n ≤ B)
    {ω ω' : SteinhausModel.Omega} (hphase : ∀ p ≤ B, ω p = ω' p) :
    SteinhausModel.X n ω = SteinhausModel.X n ω' := by
  classical
  by_cases hn0 : n = 0
  · subst n
    simp [SteinhausModel.X]
  unfold SteinhausModel.X
  congr 3
  apply sum_congr rfl
  intro p hp
  rw [hphase p ((Nat.le_of_dvd (Nat.pos_of_ne_zero hn0)
    (Nat.dvd_of_mem_primeFactors hp)).trans hn)]

/-- A sufficiently long finite phase prefix preserves the full Gaussian cofactor within any
requested error, simultaneously at every positive scale below a fixed upper bound. -/
theorem exists_fullGaussianCofactor_uniform_prefix_stability
    (s : ℂ) (U : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ (R : ℝ), 0 < R → R ≤ U →
      ∀ ω ω' : SteinhausModel.Omega, (∀ p ≤ B, ω p = ω' p) →
        ‖steinhausFullGaussianCofactor s R ω - steinhausFullGaussianCofactor s R ω'‖ < ε := by
  let A : ℝ := |s.re| + 2
  have hA : 0 < A := by dsimp only [A]; positivity
  have hsA : s.re < A := by dsimp only [A]; linarith [le_abs_self s.re]
  obtain ⟨C, hC, htail⟩ := exists_norm_steinhausFullGaussianCofactor_sub_of_prefix_le hA
  have hpow : Tendsto (fun B : ℕ => (B : ℝ) ^ (s.re - A)) atTop (𝓝 0) := by
    simpa only [show -(A - s.re) = s.re - A by ring, Function.comp_def] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hsA)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun B : ℕ => (B : ℝ)) atTop atTop)
  have hlim : Tendsto (fun B : ℕ =>
      C * U ^ A * ((B : ℝ) ^ (s.re - A) / (A - s.re))) atTop (𝓝 0) := by
    simpa only [zero_div, mul_zero] using (hpow.div_const (A - s.re)).const_mul (C * U ^ A)
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hε))
  let B := max 1 B₀
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨B, hB, fun R hR hRU ω ω' hphase => ?_⟩
  have hpref : ∀ n : ℕ, n ≤ B → SteinhausModel.X n ω = SteinhausModel.X n ω' :=
    fun n hn => X_eq_of_phase_prefix hn hphase
  calc
    _ ≤ C * R ^ A * ((B : ℝ) ^ (s.re - A) / (A - s.re)) :=
      htail s R hR hsA B hB ω ω' hpref
    _ ≤ C * U ^ A * ((B : ℝ) ^ (s.re - A) / (A - s.re)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hR.le hRU hA.le) hC)
        (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sub_pos.mpr hsA).le)
    _ < ε := hB₀ B (le_max_right _ _)

end RHTower
