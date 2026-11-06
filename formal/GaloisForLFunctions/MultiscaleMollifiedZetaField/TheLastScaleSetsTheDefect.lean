import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.DiscCorridorDivergenceAndDetectorSharpness
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheOffLineLogarithmIsThePrimeField

/-!
# The last scale sets the defect

Let `Ψ` be any normalized mollifier of length `y ≤ V^θ`, `θ < ½`, with coefficients bounded by one.
On `Re s = ½ + a/L`, `L = log V`,

`∫_V^{2V} |ζΨ − 1|² dt ≥ c (e^{−2θa}/a) V`

(`exists_eventually_shiftedDefect_ge`), uniformly in `Ψ`, for every depth `a ≥ 4` with
`e^{−2θa}/a ≥ K/L`.

**Mechanism.** Every prime `p > y` has coefficient `b_1 = 1` in `ζΨ`, whatever `Ψ` is. The primes of
`(V^θ, V^{θ+1/a}]` carry reciprocal mass `≍ 1/a` by Mertens, and on `Re s = ½ + a/L` they are damped
by exactly `e^{−2θa}`, up to a constant. They survive in the mean square by the Gaussian floor.

**The rate is `2θ`.** It is the rate of the primes just above the mollifier, not the rate `2` of the
primes near `V`, and the factor `1/a` is their mass.

**Consequence for detectors.** The occupancy criterion needs shifted defect `≤ C e^{−ra} V/L` for all
`a` beyond half the depth. Below `a₀ = (1−ε) log L/(2θ)` the floor exceeds `C V/L` for every `C`
(`eventually_shiftedDefect_gt_below_threshold`). No polynomial mollifier of length `V^θ` is therefore
a detector at depth below `(1−ε) (log log V)/θ`. A barrier on smaller primes cannot change this, since
it does not touch the coefficients at `p > y`.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open RHTower

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The Mertens constant of the sharp second theorem. -/
def mertensError : ℝ := 2 * Sieve.mertensFirstConst + 1 / 2

theorem mertensError_pos : 0 < mertensError := by
  unfold mertensError
  have := Sieve.mertensFirstConst_nonneg
  linarith

/-- The two ends of the last-scale block. -/
theorem last_scale_block_bounds {θ a L : ℝ} (ha : 1 ≤ a) (hL8 : 8 * a ≤ L) (hθL : 1 ≤ θ * L) :
    Real.exp (θ * L) ≤ (⌈Real.exp (θ * L)⌉₊ : ℝ) ∧
      (⌈Real.exp (θ * L)⌉₊ : ℝ) ≤ 2 * Real.exp (θ * L) ∧
      (⌊Real.exp ((θ + 1 / a) * L)⌋₊ : ℝ) ≤ Real.exp ((θ + 1 / a) * L) ∧
      Real.exp ((θ + 1 / a) * L) / 2 ≤ (⌊Real.exp ((θ + 1 / a) * L)⌋₊ : ℝ) ∧
      ⌈Real.exp (θ * L)⌉₊ ≤ ⌊Real.exp ((θ + 1 / a) * L)⌋₊ := by
  have ha0 : 0 < a := by linarith
  have hL0 : 0 < L := by linarith
  have hLa : 8 ≤ L / a := by
    rw [le_div_iff₀ ha0]
    exact hL8
  have hexp1 : 2 ≤ Real.exp (θ * L) := by
    have := Real.add_one_le_exp (θ * L)
    linarith
  have hsplit : Real.exp ((θ + 1 / a) * L) = Real.exp (θ * L) * Real.exp (L / a) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
  have hbig : 8 ≤ Real.exp (L / a) := by
    have := Real.add_one_le_exp (L / a)
    linarith
  have hge : 16 ≤ Real.exp ((θ + 1 / a) * L) := by
    rw [hsplit]
    nlinarith [Real.exp_pos (θ * L), Real.exp_pos (L / a)]
  have hc := Nat.le_ceil (Real.exp (θ * L))
  have hc2 := Nat.ceil_lt_add_one (show 0 ≤ Real.exp (θ * L) by positivity)
  have hf := Nat.floor_le (show 0 ≤ Real.exp ((θ + 1 / a) * L) by positivity)
  have hf2 := Nat.lt_floor_add_one (Real.exp ((θ + 1 / a) * L))
  refine ⟨hc, by linarith, hf, by linarith, ?_⟩
  have hf3 : Real.exp (θ * L) * Real.exp (L / a) < (⌊Real.exp ((θ + 1 / a) * L)⌋₊ : ℝ) + 1 := by
    rw [← hsplit]
    exact hf2
  have hlt : (⌈Real.exp (θ * L)⌉₊ : ℝ) ≤ (⌊Real.exp ((θ + 1 / a) * L)⌋₊ : ℝ) := by
    nlinarith [Real.exp_pos (θ * L), Real.exp_pos (L / a)]
  exact_mod_cast hlt

/-- **The mass of the last-scale block.** The primes of `(V^θ, V^{θ+1/a}]` carry reciprocal mass at
least `1/(6a)`. -/
theorem sum_prime_inv_block_ge {θ a L : ℝ} (hθ : θ < 1 / 2) (ha : 1 ≤ a) (hL8 : 8 * a ≤ L)
    (hθL : 1 ≤ θ * L) (hCm : 12 * mertensError * a ≤ θ * L) :
    1 / (6 * a) ≤ Sieve.mertensS ⌊Real.exp ((θ + 1 / a) * L)⌋₊ -
      Sieve.mertensS ⌈Real.exp (θ * L)⌉₊ := by
  have ha0 : 0 < a := by linarith
  have hL0 : 0 < L := by linarith
  have hθ0 : 0 < θ := by
    by_contra h
    have : θ * L ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hL0.le
    linarith
  obtain ⟨h1, h2, h3, h4, h5⟩ := last_scale_block_bounds ha hL8 hθL
  generalize ⌈Real.exp (θ * L)⌉₊ = A at h1 h2 h5 ⊢
  generalize ⌊Real.exp ((θ + 1 / a) * L)⌋₊ = B at h3 h4 h5 ⊢
  have hl2 := Real.log_two_lt_d9
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA2 : (2 : ℝ) ≤ A := by
    have := Real.add_one_le_exp (θ * L)
    linarith
  have hB2 : (2 : ℝ) ≤ B := by
    have : (A : ℝ) ≤ B := by exact_mod_cast h5
    linarith
  have hAnat : 2 ≤ A := by exact_mod_cast hA2
  have hBnat : 2 ≤ B := by exact_mod_cast hB2
  -- sizes of the logarithms
  have hlogA1 : θ * L ≤ Real.log A := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have hlogA2 : Real.log A ≤ θ * L + Real.log 2 := by
    have := Real.log_le_log (by linarith) h2
    rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp, add_comm] at this
  have hlogB1 : (θ + 1 / a) * L - Real.log 2 ≤ Real.log B := by
    have := Real.log_le_log (by positivity) h4
    rwa [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at this
  have hlogA0 : 0 < Real.log A := by linarith
  have hLa : L / a = 1 / a * L := by ring
  have hgap : L / (2 * a) ≤ Real.log B - Real.log A := by
    have e : (θ + 1 / a) * L = θ * L + L / a := by ring
    rw [e] at hlogB1
    have h8 : 8 ≤ L / a := by
      rw [le_div_iff₀ ha0]
      exact hL8
    have e2 : L / (2 * a) = (L / a) / 2 := by
      field_simp
    rw [e2]
    linarith
  have hlogAL : Real.log A ≤ L := by nlinarith
  -- the ratio of the logarithms
  have hratio : 1 + 1 / (2 * a) ≤ Real.log B / Real.log A := by
    rw [le_div_iff₀ hlogA0]
    have h6 : Real.log A * (1 / (2 * a)) ≤ L / (2 * a) := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right hlogAL (by positivity)
    nlinarith
  have hlogB0 : 0 < Real.log B := by
    have : (0 : ℝ) ≤ L / (2 * a) := by positivity
    linarith
  have hlogratio : 1 / (3 * a) ≤ Real.log (Real.log B) - Real.log (Real.log A) := by
    rw [← Real.log_div hlogB0.ne' hlogA0.ne']
    have hx : 0 < 1 + 1 / (2 * a) := by positivity
    have h7 := Real.one_sub_inv_le_log_of_pos hx
    have h8 : 1 / (3 * a) ≤ 1 - (1 + 1 / (2 * a))⁻¹ := by
      have e : 1 - (1 + 1 / (2 * a))⁻¹ = 1 / (2 * a + 1) := by
        field_simp
        ring
      rw [e]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    exact h8.trans (h7.trans (Real.log_le_log hx hratio))
  -- Mertens at the two ends
  have hMA := abs_le.mp (Sieve.abs_mertensS_sub_logLog_sub_const_le hAnat)
  have hMB := abs_le.mp (Sieve.abs_mertensS_sub_logLog_sub_const_le hBnat)
  unfold Sieve.logLog at hMA hMB
  have hE0 := mertensError_pos
  have hθL0 : 0 < θ * L := by linarith
  have herrA : (2 * Sieve.mertensFirstConst + 1 / 2) / Real.log A ≤ mertensError / (θ * L) :=
    div_le_div_of_nonneg_left hE0.le hθL0 hlogA1
  have hBA : θ * L ≤ Real.log B := by linarith [show (0 : ℝ) ≤ L / (2 * a) by positivity]
  have herrB : (2 * Sieve.mertensFirstConst + 1 / 2) / Real.log B ≤ mertensError / (θ * L) :=
    div_le_div_of_nonneg_left hE0.le hθL0 hBA
  have herr : 2 * (mertensError / (θ * L)) ≤ 1 / (6 * a) := by
    rw [← mul_div_assoc, div_le_div_iff₀ hθL0 (by positivity)]
    nlinarith
  have e3 : 1 / (3 * a) = 2 * (1 / (6 * a)) := by
    field_simp
    norm_num
  linarith [hMA.1, hMA.2, hMB.1, hMB.2]

/-- A prime of the last-scale block is damped by at most `e^{−2θa−2}` on `Re s = ½ + a/L`. -/
theorem prime_rpow_ge {θ a L : ℝ} {p : ℕ} (hL0 : 0 < L) (ha0 : 0 < a) (hp : 1 ≤ p)
    (hpY : (p : ℝ) ≤ Real.exp ((θ + 1 / a) * L)) :
    Real.exp (-2) * Real.exp (-(2 * θ * a)) * (1 / (p : ℝ)) ≤
      (p : ℝ) ^ (-2 * (1 / 2 + a / L)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hlogp : Real.log p ≤ (θ + 1 / a) * L := by
    have := Real.log_le_log hp0 hpY
    rwa [Real.log_exp] at this
  rw [Real.rpow_def_of_pos hp0, one_div, ← Real.exp_log hp0, ← Real.exp_neg, Real.log_exp,
    ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 : Real.log p * (a / L) ≤ (θ + 1 / a) * a := by
    calc Real.log p * (a / L) ≤ (θ + 1 / a) * L * (a / L) :=
          mul_le_mul_of_nonneg_right hlogp (by positivity)
      _ = (θ + 1 / a) * a := by
          field_simp
  have h2 : (θ + 1 / a) * a = θ * a + 1 := by
    field_simp
  have e : Real.log p * (-2 * (1 / 2 + a / L)) = -Real.log p - 2 * (Real.log p * (a / L)) := by
    ring
  rw [e]
  nlinarith

/-- **The truncated energy of `ζΨ`.** The primes of the last-scale block lift it above one by
`e^{−2} e^{−2θa}/(6a)`. -/
theorem energy_ge_last_scale {θ a L : ℝ} (hθ : θ < 1 / 2) (ha : 4 ≤ a) (hL8 : 8 * a ≤ L)
    (hθL : 1 ≤ θ * L) (hCm : 12 * mertensError * a ≤ θ * L) {y : ℕ} (hy : 1 ≤ y)
    (hyle : (y : ℝ) ≤ Real.exp (θ * L)) {b : ℕ → ℂ} (hb1 : b 1 = 1) :
    1 + Real.exp (-2) * Real.exp (-(2 * θ * a)) * (1 / (6 * a)) ≤
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp ((3 / 4 + (1 - 3 / 4) / 4) * L)⌋₊,
        ‖mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L)) := by
  have ha1 : 1 ≤ a := by linarith
  have ha0 : 0 < a := by linarith
  have hL0 : 0 < L := by linarith
  obtain ⟨h1, h2, h3, h4, h5⟩ := last_scale_block_bounds ha1 hL8 hθL
  have hmass := sum_prime_inv_block_ge hθ ha1 hL8 hθL hCm
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌊Real.exp ((3 / 4 + (1 - 3 / 4) / 4) * L)⌋₊ := ⟨_, rfl⟩
  rw [← hM]
  have hBM : ⌊Real.exp ((θ + 1 / a) * L)⌋₊ ≤ M := by
    rw [hM]
    refine Nat.floor_le_floor (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ hL0.le))
    have h1a : 1 / a ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) ha
    linarith
  generalize ⌈Real.exp (θ * L)⌉₊ = A at h1 h2 h5 hmass
  generalize ⌊Real.exp ((θ + 1 / a) * L)⌋₊ = B at h3 h4 h5 hmass hBM
  have hB1 : 1 ≤ B := by
    have hA2 : (1 : ℝ) ≤ A := by
      have := Real.one_le_exp (show 0 ≤ θ * L by linarith)
      linarith
    have : (A : ℝ) ≤ B := by exact_mod_cast h5
    exact_mod_cast hA2.trans this
  obtain ⟨Pset, hPset⟩ : ∃ s : Finset ℕ, s = (Finset.Ioc A B).filter Nat.Prime := ⟨_, rfl⟩
  have hsum1 : ∑ p ∈ Pset, 1 / (p : ℝ) = Sieve.mertensS B - Sieve.mertensS A := by
    rw [hPset]
    exact ConjugateDiagonalGeometry.NearLineLogMean.sum_Ioc_prime_inv_eq_mertensS_sub' h5
  have hsub : insert 1 Pset ⊆ Finset.Icc 1 M := by
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hp
    · exact Finset.mem_Icc.mpr ⟨le_rfl, hB1.trans hBM⟩
    · rw [hPset] at hp
      obtain ⟨hnA, hnB⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
      exact Finset.mem_Icc.mpr ⟨by omega, hnB.trans hBM⟩
  have h1not : 1 ∉ Pset := by
    rw [hPset]
    exact fun h => Nat.not_prime_one (Finset.mem_filter.mp h).2
  have hnn : ∀ n ∈ Finset.Icc 1 M, ∀ _ : n ∉ insert 1 Pset,
      0 ≤ ‖mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L)) := fun n _ _ =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn)
  rw [Finset.sum_insert h1not]
  have hone : ‖mollifiedZetaCoeff b y 1‖ ^ 2 * ((1 : ℕ) : ℝ) ^ (-2 * (1 / 2 + a / L)) = 1 := by
    rw [mollifiedZetaCoeff_one hy, hb1]
    simp
  rw [hone]
  refine add_le_add le_rfl ?_
  have hterm : ∀ p ∈ Pset, Real.exp (-2) * Real.exp (-(2 * θ * a)) * (1 / (p : ℝ)) ≤
      ‖mollifiedZetaCoeff b y p‖ ^ 2 * (p : ℝ) ^ (-2 * (1 / 2 + a / L)) := by
    intro p hp
    rw [hPset] at hp
    obtain ⟨hpIoc, hpp⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpA, hpB⟩ := Finset.mem_Ioc.mp hpIoc
    have hyp : y < p := by
      have h6 : (y : ℝ) ≤ A := hyle.trans h1
      have h7 : y ≤ A := by exact_mod_cast h6
      omega
    rw [mollifiedZetaCoeff_prime hy hpp hyp, hb1, norm_one, one_pow, one_mul]
    exact prime_rpow_ge hL0 ha0 hpp.one_lt.le
      ((by exact_mod_cast hpB : (p : ℝ) ≤ B).trans h3)
  refine le_trans ?_ (Finset.sum_le_sum hterm)
  rw [← Finset.mul_sum, hsum1]
  exact mul_le_mul_of_nonneg_left hmass (by positivity)

/-- `e² ≤ 8`. -/
theorem exp_two_le_eight : Real.exp 2 ≤ 8 := by
  have h3 : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h4 := Real.exp_one_lt_d9
  have h5 := Real.exp_pos 1
  rw [h3]
  nlinarith

/-- The hypotheses of the Gaussian floor, read off from the size of the floor. -/
theorem floor_scale_conditions {g L m K : ℝ} (hK : 200000 ≤ K) (hL : 128 ≤ L) (hg : K / L ≤ g)
    (hm : m = Real.exp (-2) * g * (1 / 6)) (hm1 : m ≤ 1) :
    32 / (m / 4 / (1 + m)) ≤ (1 - 3 / 4) / 4 * L := by
  have hL0 : 0 < L := by linarith
  have hgpos : 0 < g := lt_of_lt_of_le (by positivity) hg
  have hm0 : 0 < m := by
    rw [hm]
    positivity
  have he : 1 / 8 ≤ Real.exp (-2) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos 2) exp_two_le_eight
  have hmlow : g / 48 ≤ m := by
    rw [hm]
    nlinarith
  have hgL : K ≤ g * L := by
    rwa [div_le_iff₀ hL0] at hg
  have hmL : 4096 ≤ m * L := by
    have : g / 48 * L ≤ m * L := mul_le_mul_of_nonneg_right hmlow hL0.le
    nlinarith
  have e : 32 / (m / 4 / (1 + m)) = 128 * (1 + m) / m := by
    field_simp
    ring
  rw [e, div_le_iff₀ hm0]
  nlinarith

/-- The supremum condition of the Gaussian floor at floor size `≥ 1/(48 L)`. -/
theorem sup_condition_le {L m : ℝ} (hL0 : 0 < L) (hmLow : 1 / (48 * L) ≤ m)
    (hsupV : Real.exp (6 * L) * Real.exp (-(1 / 128 * Real.exp (1 / 8 * L))) ≤ 1 / (99 * 1152)) :
    99 * (Real.exp (5 * L) * Real.exp (-(1 / 128 * Real.exp ((1 - 3 / 4) / 2 * L)))) ≤
      m / 4 / 6 := by
  have e1 : (1 - 3 / 4 : ℝ) / 2 = 1 / 8 := by norm_num
  rw [e1]
  have hsplit : Real.exp (5 * L) = Real.exp (-L) * Real.exp (6 * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (-L) ≤ 1 / L := by
    rw [Real.exp_neg, one_div]
    refine inv_anti₀ hL0 ?_
    have := Real.add_one_le_exp L
    linarith
  have h4 : Real.exp (5 * L) * Real.exp (-(1 / 128 * Real.exp (1 / 8 * L))) ≤
      1 / L * (1 / (99 * 1152)) := by
    rw [hsplit, mul_assoc]
    exact mul_le_mul h2 hsupV (by positivity) (by positivity)
  have h5 : 99 * (1 / L * (1 / (99 * 1152))) = 1 / (48 * L) / 24 := by
    field_simp
    norm_num
  calc 99 * (Real.exp (5 * L) * Real.exp (-(1 / 128 * Real.exp (1 / 8 * L))))
      ≤ 99 * (1 / L * (1 / (99 * 1152))) := mul_le_mul_of_nonneg_left h4 (by norm_num)
    _ = 1 / (48 * L) / 24 := h5
    _ ≤ m / 4 / 6 := by linarith

/-- The first moment of the mollified error is negligible against the floor. -/
theorem first_moment_error_le {V L θ m : ℝ} {y : ℕ} (hV16 : 16 ≤ V) (hL0 : 0 < L) (hθ0 : 0 < θ)
    (hθ : θ < 1 / 2) (hyle : (y : ℝ) ≤ V ^ θ) (hmLow : 1 / (48 * L) ≤ m)
    (hlogV : 98 * 192 * L ≤ V ^ (1 / 2 - θ)) :
    2 * (2 + (y : ℝ) * (45 * Real.sqrt V + 8)) ≤ m / 4 * V := by
  have hV0 : 0 < V := by linarith
  have hsqrt : Real.sqrt V = V ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow V
  have hsq4 : 4 ≤ Real.sqrt V := by
    rw [show (4 : ℝ) = Real.sqrt 16 by norm_num]
    exact Real.sqrt_le_sqrt hV16
  have hpow1 : 1 ≤ V ^ (θ + 1 / 2) := Real.one_le_rpow (by linarith) (by linarith)
  have hyprod : (y : ℝ) * (45 * Real.sqrt V + 8) ≤ 47 * V ^ (θ + 1 / 2) := by
    calc (y : ℝ) * (45 * Real.sqrt V + 8)
        ≤ V ^ θ * (45 * Real.sqrt V + 2 * Real.sqrt V) :=
          mul_le_mul hyle (by linarith) (by positivity) (by positivity)
      _ = 47 * (V ^ θ * V ^ (1 / 2 : ℝ)) := by
          rw [hsqrt]
          ring
      _ = 47 * V ^ (θ + 1 / 2) := by rw [← Real.rpow_add hV0]
  have hLpow : 98 * 192 * L * V ^ (θ + 1 / 2) ≤ V := by
    calc 98 * 192 * L * V ^ (θ + 1 / 2) ≤ V ^ (1 / 2 - θ) * V ^ (θ + 1 / 2) :=
          mul_le_mul_of_nonneg_right hlogV (by positivity)
      _ = V := by
          rw [← Real.rpow_add hV0]
          have : (1 / 2 - θ + (θ + 1 / 2)) = 1 := by ring
          rw [this, Real.rpow_one]
  have h1 : 2 * (2 + (y : ℝ) * (45 * Real.sqrt V + 8)) ≤ 98 * V ^ (θ + 1 / 2) := by linarith
  have h2 : 1 / (192 * L) * V ≤ m / 4 * V := by
    refine mul_le_mul_of_nonneg_right ?_ hV0.le
    have e : 1 / (192 * L) = 1 / (48 * L) / 4 := by
      field_simp
      norm_num
    rw [e]
    linarith
  have h3 : 98 * V ^ (θ + 1 / 2) ≤ 1 / (192 * L) * V := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    nlinarith
  linarith

/-- From the second moment and the first moment to the defect. -/
theorem defect_ge_of_second_moment {b : ℕ → ℂ} {y : ℕ} {V σ m : ℝ} (hV16 : 16 ≤ V) (hy : 1 ≤ y)
    (hb1 : b 1 = 1) (hb : ∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1) (hσ_lo : 1 / 2 ≤ σ) (hσ_hi : σ ≤ 2)
    (herr : 2 * (2 + (y : ℝ) * (45 * Real.sqrt V + 8)) ≤ m / 4 * V)
    (hmain : (1 + m - m / 4) * V ≤ ∫ t in V..(2 * V),
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) * edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) :
    m / 2 * V ≤ ∫ t in V..(2 * V),
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) * edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I) - 1‖ ^ 2 := by
  have hV0 : 0 < V := by linarith
  have hid := ConjugateDiagonalGeometry.NearLineLogMean.integral_norm_zetaMollified_sub_one_sq_eq
    b y (σ := σ) hV0 (show V ≤ 2 * V by linarith)
  have h1st := norm_integral_zeta_mul_edPoly_sub_one_block_le hy hb1 hb hσ_lo hσ_hi
    (show 4 ≤ V by linarith) le_rfl (by linarith) (by linarith) le_rfl (show V ≤ 2 * V by linarith)
  have hre := (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans h1st)
  rw [hid]
  have e2 : 2 * V - V = V := by ring
  rw [e2]
  nlinarith

/-- **The second moment floor at the last scale.** -/
theorem second_moment_floor_last_scale {θ a L K m : ℝ} {y : ℕ} {b : ℕ → ℂ} (hθ : θ < 1 / 2)
    (ha : 4 ≤ a) (hL128 : 128 ≤ L) (hKa : K * a ≤ L) (hK2 : 200000 ≤ K) (hθL : 1 ≤ θ * L)
    (hCm : 12 * mertensError * a ≤ θ * L) (hy : 1 ≤ y) (hyle2 : (y : ℝ) ≤ Real.exp (θ * L))
    (hb1 : b 1 = 1) (hb : ∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1)
    (hm : m = Real.exp (-2) * (Real.exp (-(2 * θ * a)) / a) * (1 / 6))
    (hgL : K / L ≤ Real.exp (-(2 * θ * a)) / a)
    (hsupV : Real.exp (6 * L) * Real.exp (-(1 / 128 * Real.exp (1 / 8 * L))) ≤ 1 / (99 * 1152)) :
    (1 + m - m / 4) * Real.exp L ≤ ∫ t in (Real.exp L)..(2 * Real.exp L),
      ‖riemannZeta (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 y) (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hL0 : 0 < L := by linarith
  have ha0 : 0 < a := by linarith
  have hL8 : 8 * a ≤ L := by nlinarith
  have hEn := energy_ge_last_scale hθ ha hL8 hθL hCm hy hyle2 hb1
  have hEneq : Real.exp (-2) * Real.exp (-(2 * θ * a)) * (1 / (6 * a)) = m := by
    rw [hm]
    field_simp
  rw [hEneq] at hEn
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = Real.exp (-(2 * θ * a)) / a := ⟨_, rfl⟩
  rw [← hg] at hm hgL
  have hgpos : 0 < g := by
    rw [hg]
    positivity
  have hm0 : 0 < m := by
    rw [hm]
    positivity
  have he1 : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hgle : g ≤ 1 / a := by
    have hKL : K / L ≤ 1 / a := by
      rw [div_le_div_iff₀ hL0 ha0, one_mul]
      exact hKa
    rw [hg]
    refine div_le_div_of_nonneg_right ?_ ha0.le
    have h2θ : 0 ≤ θ := by
      by_contra h
      have := mul_nonpos_of_nonpos_of_nonneg (not_le.mp h).le hL0.le
      linarith
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hg1 : g ≤ 1 := hgle.trans (by
    rw [div_le_one ha0]
    linarith)
  have hm1 : m ≤ 1 := by
    rw [hm]
    nlinarith
  have hcond := floor_scale_conditions hK2 hL128 hgL hm hm1
  have he8 : 1 / 8 ≤ Real.exp (-2) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos 2) exp_two_le_eight
  have hgLow : 1 / L ≤ g := le_trans (div_le_div_of_nonneg_right (by linarith) hL0.le) hgL
  have hmLow : 1 / (48 * L) ≤ m := by
    have h1 : g / 48 ≤ m := by
      rw [hm]
      nlinarith
    have h2 : 1 / (48 * L) = (1 / L) / 48 := by
      field_simp
    rw [h2]
    linarith
  have hsup2 := sup_condition_le hL0 hmLow hsupV
  have hmain := ConjugateDiagonalGeometry.NearLineLogMean.gaussFloor_general_at_scale
    (a := a) (θ₁ := 3 / 4) (L := L) (D₀ := 1 + m) (δ := m / 4) ha0.le (by norm_num) (by norm_num)
    (by linarith) (by positivity) (by linarith) (by nlinarith) (by linarith) hcond hsup2 hy
    (hyle2.trans (Real.exp_le_exp.mpr (by nlinarith))) hb hEn
  exact hmain

/-- **The last scale sets the defect.** Uniformly over all normalized mollifiers of length
`y ≤ V^θ`, `θ < ½`, and all depths `a ≥ 4` with `e^{−2θa}/a ≥ K/log V`,
`∫_V^{2V} |ζΨ(½ + a/log V + it) − 1|² dt ≥ (e^{−2}/12) (e^{−2θa}/a) V`. -/
theorem exists_eventually_shiftedDefect_ge {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2) :
    ∃ K : ℝ, 200000 ≤ K ∧ ∀ᶠ V : ℝ in atTop, ∀ a : ℝ, 4 ≤ a →
      K / Real.log V ≤ Real.exp (-(2 * θ * a)) / a → ∀ y : ℕ, 1 ≤ y → (y : ℝ) ≤ V ^ θ →
      ∀ b : ℕ → ℂ, b 1 = 1 → (∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1) →
        Real.exp (-2) / 12 * (Real.exp (-(2 * θ * a)) / a) * V ≤
          ∫ t in V..(2 * V),
            ‖riemannZeta (((1 / 2 + a / Real.log V : ℝ) : ℂ) + (t : ℂ) * I) *
              edPoly b (Finset.Icc 1 y)
                (((1 / 2 + a / Real.log V : ℝ) : ℂ) + (t : ℂ) * I) - 1‖ ^ 2 := by
  have hE0 := mertensError_pos
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 200000 + 96 * mertensError / θ := ⟨_, rfl⟩
  have hK2 : 200000 ≤ K := by
    have : 0 ≤ 96 * mertensError / θ := by positivity
    rw [hK]
    linarith
  have hKθ : 96 * mertensError ≤ K * θ := by
    have h : 96 * mertensError / θ ≤ K := by
      rw [hK]
      linarith
    rwa [div_le_iff₀ hθ0] at h
  refine ⟨K, hK2, ?_⟩
  have hsup := eventually_exp_mul_exp_neg_exp_le (k := 6) (C := 1 / 128) (δ := 1 / 8)
    (ε := 1 / (99 * 1152)) (by norm_num) (by norm_num) (by norm_num)
  have hlogo := (isLittleO_log_rpow_atTop (show 0 < 1 / 2 - θ by linarith)).bound
    (show (0 : ℝ) < 1 / (98 * 192) by norm_num)
  filter_upwards [Real.tendsto_log_atTop.eventually hsup,
    Real.tendsto_log_atTop.eventually_ge_atTop (128 + 8 / θ), hlogo, eventually_ge_atTop 16]
    with V hsupV hLV hlogV hV16 a ha hgL y hy hyle b hb1 hb
  have hV0 : 0 < V := by linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log V := ⟨_, rfl⟩
  rw [← hL] at hsupV hLV hgL hlogV ⊢
  have h8θ : 0 ≤ 8 / θ := by positivity
  have hL128 : 128 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have ha0 : 0 < a := by linarith
  have hexpL : Real.exp L = V := by
    rw [hL, Real.exp_log hV0]
  have hgle : Real.exp (-(2 * θ * a)) / a ≤ 1 / a :=
    div_le_div_of_nonneg_right (Real.exp_le_one_iff.mpr (by nlinarith)) ha0.le
  have hKa : K * a ≤ L := by
    have h1 : K / L ≤ 1 / a := hgL.trans hgle
    rwa [div_le_div_iff₀ hL0 ha0, one_mul] at h1
  have hθL : 1 ≤ θ * L := by
    have h1 : 8 / θ ≤ L := by linarith
    rw [div_le_iff₀ hθ0] at h1
    nlinarith
  have hCm : 12 * mertensError * a ≤ θ * L := by
    have h1 : (K * θ) * a ≤ L * θ := by
      have := mul_le_mul_of_nonneg_right hKa hθ0.le
      nlinarith
    nlinarith
  have hyle2 : (y : ℝ) ≤ Real.exp (θ * L) := by
    rw [mul_comm, Real.exp_mul, hexpL]
    exact hyle
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = Real.exp (-2) * (Real.exp (-(2 * θ * a)) / a) * (1 / 6) := ⟨_, rfl⟩
  have hmain := second_moment_floor_last_scale hθ ha hL128 hKa hK2 hθL hCm hy hyle2 hb1 hb hm hgL hsupV
  rw [hexpL] at hmain
  have he8 : 1 / 8 ≤ Real.exp (-2) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos 2) exp_two_le_eight
  have hgLow : 1 / L ≤ Real.exp (-(2 * θ * a)) / a :=
    le_trans (div_le_div_of_nonneg_right (by linarith) hL0.le) hgL
  have hmLow : 1 / (48 * L) ≤ m := by
    have h1 : (Real.exp (-(2 * θ * a)) / a) / 48 ≤ m := by
      rw [hm]
      have hg0 : 0 < Real.exp (-(2 * θ * a)) / a := by positivity
      nlinarith
    have h2 : 1 / (48 * L) = (1 / L) / 48 := by
      field_simp
    rw [h2]
    linarith
  have hlogV2 : 98 * 192 * L ≤ V ^ (1 / 2 - θ) := by
    simp only [Real.norm_eq_abs] at hlogV
    rw [abs_of_pos hL0, abs_of_pos (by positivity)] at hlogV
    have := mul_le_mul_of_nonneg_left hlogV (show (0 : ℝ) ≤ 98 * 192 by norm_num)
    have e : (98 * 192 : ℝ) * (1 / (98 * 192) * V ^ (1 / 2 - θ)) = V ^ (1 / 2 - θ) := by
      field_simp
    linarith
  have herr := first_moment_error_le hV16 hL0 hθ0 hθ hyle hmLow hlogV2
  have hσ_lo : 1 / 2 ≤ 1 / 2 + a / L := by
    have : 0 ≤ a / L := by positivity
    linarith
  have hσ_hi : 1 / 2 + a / L ≤ 2 := by
    have : a / L ≤ 1 := (div_le_one hL0).mpr (by nlinarith)
    linarith
  have hfinal := defect_ge_of_second_moment hV16 hy hb1 hb hσ_lo hσ_hi herr hmain
  have e0 : Real.exp (-2) / 12 * (Real.exp (-(2 * θ * a)) / a) = m / 2 := by
    rw [hm]
    ring
  rw [e0]
  exact hfinal

/-- **No polynomial detector below the threshold.** For every `C`, every normalized mollifier of
length `y ≤ V^θ`, and every depth `4 ≤ a ≤ (1−ε) log log V/(2θ)`, the shifted defect exceeds
`C V/log V`, the size the occupancy criterion needs. -/
theorem eventually_shiftedDefect_gt_below_threshold {θ ε C : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : 0 < C) :
    ∀ᶠ V : ℝ in atTop, ∀ a : ℝ, 4 ≤ a →
      a ≤ (1 - ε) * Real.log (Real.log V) / (2 * θ) → ∀ y : ℕ, 1 ≤ y → (y : ℝ) ≤ V ^ θ →
      ∀ b : ℕ → ℂ, b 1 = 1 → (∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1) →
        C * V / Real.log V <
          ∫ t in V..(2 * V),
            ‖riemannZeta (((1 / 2 + a / Real.log V : ℝ) : ℂ) + (t : ℂ) * I) *
              edPoly b (Finset.Icc 1 y)
                (((1 / 2 + a / Real.log V : ℝ) : ℂ) + (t : ℂ) * I) - 1‖ ^ 2 := by
  obtain ⟨K, hK2, hfloor⟩ := exists_eventually_shiftedDefect_ge hθ0 hθ
  obtain ⟨K', hK'⟩ : ∃ K' : ℝ, K' = max K (97 * C) * ((1 - ε) / (2 * θ) / ε + 1) := ⟨_, rfl⟩
  have hc1 : 0 < (1 - ε) / (2 * θ) / ε := by
    have : 0 < 1 - ε := by linarith
    positivity
  have hmaxK : 0 < max K (97 * C) := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hK'pos : 0 < K' := by
    rw [hK']
    positivity
  -- `exp(εu)` beats `u`
  have hbeat : Tendsto (fun x : ℝ => Real.exp x / x ^ 1) atTop atTop := Real.tendsto_exp_div_pow_atTop 1
  have hu : Tendsto (fun V : ℝ => ε * Real.log (Real.log V)) atTop atTop :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).const_mul_atTop hε
  have hev := (hbeat.comp hu).eventually_ge_atTop (max K (97 * C) * ((1 - ε) / (2 * θ) / ε + 1))
  filter_upwards [hfloor, hev, hu.eventually_gt_atTop 0, Real.tendsto_log_atTop.eventually_gt_atTop 1,
    eventually_gt_atTop 1] with V hV hbig huV hL1 hV1
  intro a ha haU y hy hyle b hb1 hb
  simp only [Function.comp_apply, pow_one] at hbig
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log V := ⟨_, rfl⟩
  rw [← hL] at hL1 hbig huV haU ⊢
  have hV0 : 0 < V := by linarith
  have hL0 : 0 < L := by linarith
  obtain ⟨u, hu'⟩ : ∃ u : ℝ, u = Real.log L := ⟨_, rfl⟩
  have huε : 0 < ε * Real.log L := huV
  rw [← hu'] at haU huε
  have ha0 : 0 < a := by linarith
  have hu0 : 0 < u := (mul_pos_iff_of_pos_left hε).mp huε
  rw [← hu'] at hbig
  rw [le_div_iff₀ huε] at hbig
  -- the size of the floor
  have hexp : Real.exp (-(2 * θ * a)) ≥ Real.exp (ε * u) / L := by
    have h1 : 2 * θ * a ≤ (1 - ε) * u := by
      rw [le_div_iff₀ (by positivity)] at haU
      linarith
    have h2 : Real.exp (ε * u) / L = Real.exp (-((1 - ε) * u)) := by
      have hLexp : L = Real.exp u := by
        rw [hu', Real.exp_log hL0]
      rw [hLexp, ← Real.exp_sub]
      congr 1
      ring
    rw [h2]
    exact Real.exp_le_exp.mpr (by linarith)
  have hstep : max K (97 * C) / L ≤ Real.exp (-(2 * θ * a)) / a := by
    rw [ge_iff_le] at hexp
    have h1 : Real.exp (ε * u) / L / a ≤ Real.exp (-(2 * θ * a)) / a :=
      div_le_div_of_nonneg_right hexp ha0.le
    refine le_trans ?_ h1
    rw [div_div, div_le_div_iff₀ hL0 (by positivity)]
    have haU2 : a ≤ (1 - ε) / (2 * θ) / ε * (ε * u) := by
      rw [le_div_iff₀ (by positivity)] at haU
      have e : (1 - ε) / (2 * θ) / ε * (ε * u) = (1 - ε) * u / (2 * θ) := by
        field_simp
      rw [e, le_div_iff₀ (by positivity)]
      exact haU
    have h3 : max K (97 * C) * a ≤ Real.exp (ε * u) := by
      have h4 : max K (97 * C) * a ≤ max K (97 * C) * ((1 - ε) / (2 * θ) / ε * (ε * u)) :=
        mul_le_mul_of_nonneg_left haU2 hmaxK.le
      have h5 : max K (97 * C) * ((1 - ε) / (2 * θ) / ε * (ε * u)) ≤
          max K (97 * C) * ((1 - ε) / (2 * θ) / ε + 1) * (ε * u) := by
        have : 0 ≤ max K (97 * C) * (ε * u) := by positivity
        nlinarith
      linarith
    nlinarith
  have hKL : K / L ≤ Real.exp (-(2 * θ * a)) / a :=
    (div_le_div_of_nonneg_right (le_max_left _ _) hL0.le).trans hstep
  have hmain := hV a ha (by rw [← hL]; exact hKL) y hy hyle b hb1 hb
  rw [← hL] at hmain
  refine lt_of_lt_of_le ?_ hmain
  have hCL : 97 * C / L ≤ Real.exp (-(2 * θ * a)) / a :=
    (div_le_div_of_nonneg_right (le_max_right _ _) hL0.le).trans hstep
  have he8 : 1 / 8 ≤ Real.exp (-2) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos 2) exp_two_le_eight
  have hmul : C / L * (97 / 96) ≤ Real.exp (-2) / 12 * (Real.exp (-(2 * θ * a)) / a) := by
    have h1 : 1 / 96 * (97 * C / L) ≤ 1 / 96 * (Real.exp (-(2 * θ * a)) / a) :=
      mul_le_mul_of_nonneg_left hCL (by norm_num)
    have h2 : 1 / 96 * (Real.exp (-(2 * θ * a)) / a) ≤
        Real.exp (-2) / 12 * (Real.exp (-(2 * θ * a)) / a) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      linarith
    have e : C / L * (97 / 96) = 1 / 96 * (97 * C / L) := by ring
    linarith
  have hpos : 0 < C / L * V := by positivity
  have e : C * V / L = C / L * V := by ring
  rw [e]
  have h3 := mul_le_mul_of_nonneg_right hmul hV0.le
  nlinarith

end GaloisForLFunctions.MultiscaleMollifiedZetaField
