import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCrossErrorOfTheBulkEntries
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheLogarithmicCenterRowCancelsThePole
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheShellPairSumsAreRiemannSums
import GaloisForLFunctions.HTGeometry.HarmonicLogWindow

/-!
# Terminal windows read the polar center

The exact polar center row is a harmonic boundary expression. A terminal
weight vanishing at the top endpoint pays its apparent reciprocal singularity.
The limiting boundary logarithm is continuous after multiplication by that weight.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory

/-- The polar center profile, including its terminal boundary logarithm. -/
def polarCenterProfile (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  F x / x - F x * Real.log (1 - x ^ 2) / 2

/-- The exact polar center row after dividing its receiving coordinate by its square root. -/
def polarCenterRow (N n : ℕ) : ℝ :=
  (N : ℝ) / n + (harmonic N : ℝ) -
    ((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 + 3 / (4 * (n : ℝ))

private theorem continuousOn_terminal_boundary_log
    {F : ℝ → ℝ} {LF : ℝ} (hLF : 0 ≤ LF)
    (hFL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|) (hF1 : F 1 = 0) :
    ContinuousOn (fun x => F x * Real.log (1 - x ^ 2)) (Set.Icc 0 1) := by
  have hcont := continuousOn_of_abs_sub_le hFL
  intro x hx
  by_cases hx1 : x = 1
  · subst x
    change Tendsto (fun x => F x * Real.log (1 - x ^ 2))
      (𝓝[Set.Icc 0 1] 1) (𝓝 (F 1 * Real.log (1 - 1 ^ 2)))
    simp only [hF1, zero_mul]
    have hg : Continuous (fun x : ℝ => (1 - x ^ 2) * Real.log (1 - x ^ 2)) :=
      Real.continuous_mul_log.comp (continuous_const.sub (continuous_id.pow 2))
    have hlim : Tendsto (fun x : ℝ => LF * ‖(1 - x ^ 2) * Real.log (1 - x ^ 2)‖)
        (𝓝[Set.Icc (0 : ℝ) 1] 1) (𝓝 (LF * ‖(1 - (1 : ℝ) ^ 2) * Real.log (1 - 1 ^ 2)‖)) :=
      (((hg.tendsto 1).norm).const_mul LF).mono_left nhdsWithin_le_nhds
    simp only [one_pow, sub_self, zero_mul, norm_zero, mul_zero] at hlim
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hdist : 1 - x ≤ 1 - x ^ 2 := by
      nlinarith only [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
    have hsq : 0 ≤ 1 - x ^ 2 := (sub_nonneg.mpr hx.2).trans hdist
    have hf := hFL x hx 1 ⟨zero_le_one, le_rfl⟩
    rw [hF1, sub_zero, abs_of_nonpos (sub_nonpos.mpr hx.2), neg_sub] at hf
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hsq]
    exact (mul_le_mul_of_nonneg_right
      (hf.trans (mul_le_mul_of_nonneg_left hdist hLF)) (abs_nonneg _)).trans_eq (by ring)
  · have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    have hsq : 1 - x ^ 2 ≠ 0 := by
      have hp := mul_pos (sub_pos.mpr hxlt) (by linarith [hx.1] : 0 < 1 + x)
      nlinarith only [hp]
    have ht : ContinuousAt (fun z : ℝ => 1 - z ^ 2) x := by fun_prop
    exact (hcont x hx).mul (ht.log hsq).continuousWithinAt

/-- Vanishing at the terminal endpoint regularizes the polar logarithm. -/
theorem continuousOn_polarCenterProfile
    {F : ℝ → ℝ} {LF δ : ℝ} (hLF : 0 ≤ LF)
    (hFL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|) (hF1 : F 1 = 0)
    (hδ : 0 < δ) (hzero : ∀ x, 0 ≤ x → x ≤ δ → F x = 0) :
    ContinuousOn (polarCenterProfile F) (Set.Icc 0 1) := by
  have hcont := continuousOn_of_abs_sub_le hFL
  have hdiv : ContinuousOn (fun x => F x / x) (Set.Icc 0 1) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      change Tendsto (fun x => F x / x) (𝓝[Set.Icc 0 1] 0) (𝓝 (F 0 / 0))
      simp only [div_zero]
      have hev : (fun x : ℝ => F x / x) =ᶠ[𝓝[Set.Icc 0 1] 0] fun _ => 0 := by
        filter_upwards [(gt_mem_nhds hδ).filter_mono nhdsWithin_le_nhds,
          self_mem_nhdsWithin] with x hxδ hx
        rw [hzero x hx.1 hxδ.le, zero_div]
      exact tendsto_const_nhds.congr' hev.symm
    · exact (hcont x hx).div continuousWithinAt_id hx0
  exact hdiv.sub ((continuousOn_terminal_boundary_log hLF hFL hF1).div_const 2)

/-- A Lipschitz weight vanishing at the terminal endpoint gives a uniform harmonic-row error. -/
theorem abs_terminal_polarCenter_row_sub_le
    {F : ℝ → ℝ} {BF LF δ : ℝ} (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
    (hFL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|) (hF1 : F 1 = 0)
    (hδ : 0 < δ) (hzero : ∀ x, 0 ≤ x → x ≤ δ → F x = 0)
    {N n : ℕ} (hN : 1 ≤ N) (hn : n ∈ Icc 1 N) :
    |F ((n : ℝ) / N) * ((N : ℝ) / n + (harmonic N : ℝ) -
        ((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 + 3 / (4 * (n : ℝ))) -
      polarCenterProfile F ((n : ℝ) / N)| ≤ (2 * BF + LF + BF / δ) / N := by
  have hBF : 0 ≤ BF := (abs_nonneg _).trans (hF 0)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hnN := (mem_Icc.mp hn).2
  have hx : (n : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hN0).mpr (by exact_mod_cast hnN)⟩
  by_cases htop : n = N
  · subst n
    simp only [div_self hN0.ne', hF1, zero_mul, polarCenterProfile, zero_div, sub_zero, abs_zero]
    positivity
  have hnn : 1 ≤ N - n := by omega
  have hnn0 : (0 : ℝ) < (N - n : ℕ) := by exact_mod_cast hnn
  have hnp0 : (0 : ℝ) < (N + n : ℕ) := by exact_mod_cast (show 0 < N + n by omega)
  let e : ℕ → ℝ := fun k => (harmonic k : ℝ) - Real.log k - Real.eulerMascheroniConstant
  have he (k : ℕ) (hk : 1 ≤ k) : |e k| ≤ 1 / (k : ℝ) :=
    HTGeometry.abs_harmonic_sub_log_sub_eulerMascheroni_le hk
  have h₁ : |F ((n : ℝ) / N) * e N| ≤ BF / N := by
    rw [abs_mul]
    exact (mul_le_mul (hF _) (he N hN) (abs_nonneg _) hBF).trans_eq (by ring)
  have h₂ : |F ((n : ℝ) / N) * e (N - n)| ≤ LF / N := by
    have hf := hFL _ hx 1 ⟨zero_le_one, le_rfl⟩
    rw [hF1, sub_zero, abs_of_nonpos (sub_nonpos.mpr hx.2), neg_sub] at hf
    have hb : 1 - (n : ℝ) / N = ((N - n : ℕ) : ℝ) / N := by
      rw [Nat.cast_sub hnN]
      field_simp
    rw [hb] at hf
    rw [abs_mul]
    exact (mul_le_mul hf (he (N - n) hnn) (abs_nonneg _) (by positivity)).trans_eq
      (by field_simp)
  have h₃ : |F ((n : ℝ) / N) * e (N + n)| ≤ BF / N := by
    rw [abs_mul]
    have hk : 1 / ((N + n : ℕ) : ℝ) ≤ 1 / (N : ℝ) :=
      one_div_le_one_div_of_le hN0 (by exact_mod_cast (Nat.le_add_right N n))
    exact (mul_le_mul (hF _) ((he (N + n) (by omega)).trans hk) (abs_nonneg _) hBF).trans_eq
      (by ring)
  have h₄ : |3 * F ((n : ℝ) / N) / (4 * (n : ℝ))| ≤ (BF / δ) / N := by
    by_cases hFx : F ((n : ℝ) / N) = 0
    · rw [hFx, mul_zero, zero_div, abs_zero]
      positivity
    have hxδ : δ < (n : ℝ) / N := lt_of_not_ge fun hle => hFx (hzero _ hx.1 hle)
    have hδN : δ * (N : ℝ) ≤ n := ((lt_div_iff₀ hN0).mp hxδ).le
    have hinv : 1 / (n : ℝ) ≤ 1 / (δ * N) :=
      one_div_le_one_div_of_le (by positivity) hδN
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3),
      abs_of_pos (by positivity : (0 : ℝ) < 4 * n)]
    calc
      _ ≤ 3 * BF / (4 * n) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hF _) (by norm_num)) (by positivity)
      _ = (3 / 4 : ℝ) * (BF / n) := by ring
      _ ≤ 1 * (BF / n) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = BF * (1 / n) := by ring
      _ ≤ BF * (1 / (δ * N)) := mul_le_mul_of_nonneg_left hinv hBF
      _ = _ := by ring
  have hlog : Real.log (1 - ((n : ℝ) / N) ^ 2) =
      Real.log ((N - n : ℕ) : ℝ) + Real.log ((N + n : ℕ) : ℝ) - 2 * Real.log N := by
    have heq : 1 - ((n : ℝ) / N) ^ 2 =
        (((N - n : ℕ) : ℝ) * ((N + n : ℕ) : ℝ)) / (N : ℝ) ^ 2 := by
      rw [Nat.cast_sub hnN, Nat.cast_add]
      field_simp
      ring
    rw [heq, Real.log_div (mul_ne_zero hnn0.ne' hnp0.ne') (pow_ne_zero 2 hN0.ne'),
      Real.log_mul hnn0.ne' hnp0.ne', Real.log_pow]
    norm_num
  have heq : F ((n : ℝ) / N) * ((N : ℝ) / n + (harmonic N : ℝ) -
        ((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 + 3 / (4 * (n : ℝ))) -
      polarCenterProfile F ((n : ℝ) / N) =
      F ((n : ℝ) / N) * e N - F ((n : ℝ) / N) * e (N - n) / 2 -
        F ((n : ℝ) / N) * e (N + n) / 2 + 3 * F ((n : ℝ) / N) / (4 * n) := by
    dsimp only [polarCenterProfile, e]
    rw [hlog]
    field_simp
    ring
  rw [heq]
  have hb₂ : |F ((n : ℝ) / N) * e (N - n) / 2| ≤ LF / N / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right h₂ (by norm_num)
  have hb₃ : |F ((n : ℝ) / N) * e (N + n) / 2| ≤ BF / N / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right h₃ (by norm_num)
  have htri := (abs_add_le _ _).trans (add_le_add
    ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add h₁ hb₂)) hb₃)) h₄)
  exact htri.trans (calc
    _ = (BF + LF / 2 + BF / 2 + BF / δ) / N := by ring
    _ ≤ (2 * BF + LF + BF / δ) / N :=
      div_le_div_of_nonneg_right (by linarith only [hBF, hLF]) hN0.le)

/-- The exact harmonic polar center row converges against every terminal Lipschitz test. -/
theorem tendsto_terminal_polarCenterRow_mean
    {F : ℝ → ℝ} {BF LF δ : ℝ} (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
    (hFL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|) (hF1 : F 1 = 0)
    (hδ : 0 < δ) (hzero : ∀ x, 0 ≤ x → x ≤ δ → F x = 0) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) * polarCenterRow N n) / N)
      atTop (𝓝 (∫ x in (0 : ℝ)..1, polarCenterProfile F x)) := by
  let D : ℝ := 2 * BF + LF + BF / δ
  have hriem : Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, polarCenterProfile F ((n : ℝ) / N)) / N) atTop
      (𝓝 (∫ x in (0 : ℝ)..1, polarCenterProfile F x)) := by
    have h := tendsto_riemannSum_of_continuousOn (continuousOn_polarCenterProfile hLF hFL hF1 hδ hzero)
    exact h.congr fun N => by
      rw [← sum_range_succ_eq_sum_Icc (fun n : ℕ => polarCenterProfile F ((n : ℝ) / N))]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
  have hz : Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) * polarCenterRow N n) / N -
        (∑ n ∈ Icc 1 N, polarCenterProfile F ((n : ℝ) / N)) / N) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat D)
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Real.norm_eq_abs, ← sub_div, ← sum_sub_distrib, abs_div, abs_of_pos hN0]
    calc
      _ ≤ (∑ _n ∈ Icc 1 N, D / N) / N := div_le_div_of_nonneg_right
        ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn =>
          abs_terminal_polarCenter_row_sub_le hF hLF hFL hF1 hδ hzero hN hn)) hN0.le
      _ = D / N := by
        rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        field_simp
  simpa only [zero_add, sub_add_cancel] using hz.add hriem

/-- The literal full polar-center pairing has the boundary-logarithm profile. -/
theorem tendsto_terminal_fullPolarCenter_pair
    {F : ℝ → ℝ} {BF LF δ : ℝ} (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
    (hFL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|) (hF1 : F 1 = 0)
    (hδ : 0 < δ) (hzero : ∀ x, 0 ≤ x → x ≤ δ → F x = 0) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / Real.sqrt n *
      ∑ j ∈ Icc 1 N,
        ((Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) - archimedeanCenterKernel n j) /
          Real.sqrt j) / N) atTop (𝓝 (∫ x in (0 : ℝ)..1, polarCenterProfile F x)) := by
  apply (tendsto_terminal_polarCenterRow_mean hF hLF hFL hF1 hδ hzero).congr
  intro N
  congr 1
  apply sum_congr rfl
  intro n hn
  rw [sum_pole_minus_center_div_sqrt hn]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hsn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  have hs : Real.sqrt (n : ℝ) * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have heq (b : ℝ) : F ((n : ℝ) / N) / Real.sqrt n *
      ((N : ℝ) / Real.sqrt n + Real.sqrt n * b) =
      F ((n : ℝ) / N) * ((N : ℝ) / (Real.sqrt n * Real.sqrt n) + b) := by
    field_simp [hsn]
  rw [heq, hs]
  dsimp only [polarCenterRow]
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminal_polarCenterRow_mean
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminal_fullPolarCenter_pair
