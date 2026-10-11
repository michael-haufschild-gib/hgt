import GaloisForLFunctions.HTGeometry.FejerLatticeVanishing
import GaloisForLFunctions.HTGeometry.LorentzOrderedSums

/-!
# Fejér-weighted exponential sums over near-lattices

The Fejér kernel `K_c(Δ) = ∫_{−1}^{1} (1 − |β|) e^{iβcΔ} dβ = sinc(cΔ/2)²` (`fejerKernel_eq`) is
`c`-Lipschitz (`norm_fejerKernel_sub_le`) and `≤ 4/(cΔ)²` (`fejerKernel_le_inv_sq`).

**Theorem** (`norm_sum_fejer_nearLattice_le`). Let `Δ_m` (`|m| ≤ M`) satisfy
`|Δ_m − mg| ≤ |m| g ε`, and let the phase `θ` be non-resonant: `x₀ = −θg/(2π)` is at distance
`≥ cg/(2π)` from every integer. Then

`‖Σ_{|m| ≤ M} e^{−iθΔ_m} K_c(Δ_m)‖ ≤ 16/(c²g²(M+1)) + (|θ| + |c|) g ε M (M+1)`... (stated with the
explicit tail sum).

The ideal lattice sum over all of `ℤ` vanishes (`tsum_sinc_sq_mul_fourier_eq_zero`). The finite sum
is therefore minus the tail beyond `M` plus a Lipschitz drift error.
-/

noncomputable section

open Real Complex MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- The Fejér kernel `K_c(Δ) = ∫_{−1}^{1} (1 − |β|) e^{iβcΔ} dβ`. -/
def fejerKernel (c Δ : ℝ) : ℂ :=
  ∫ β in (-1 : ℝ)..1, ((triangleFn 1 β : ℝ) : ℂ) * Complex.exp ((β * c * Δ : ℝ) * I)

/-- `K_c(Δ) = sinc(cΔ/2)²`. -/
theorem fejerKernel_eq (c Δ : ℝ) : fejerKernel c Δ = ((Real.sinc (c * Δ / 2) ^ 2 : ℝ) : ℂ) := by
  unfold fejerKernel
  rcases eq_or_ne (c * Δ) 0 with h0 | h0
  · have : ∀ β : ℝ, Complex.exp ((β * c * Δ : ℝ) * I) = 1 := fun β => by
      rw [show β * c * Δ = β * (c * Δ) by ring, h0, mul_zero]; simp
    simp only [this, mul_one]
    rw [integral_triangleFn one_pos, show c * Δ / 2 = 0 by rw [h0]; ring, Real.sinc_zero]
    simp
  · have hω : -(c * Δ) ≠ 0 := neg_ne_zero.mpr h0
    have h := integral_triangleFn_cexp one_pos hω
    have e : ∀ β : ℝ, Complex.exp ((β * c * Δ : ℝ) * I) =
        Complex.exp (-((-(c * Δ)) * β : ℝ) * I) := fun β => by congr 1; push_cast; ring
    simp only [e]
    rw [h]
    congr 1
    have hθ : c * Δ / 2 ≠ 0 := by intro h'; apply h0; linarith
    rw [Real.sinc_of_ne_zero hθ, mul_one, Real.cos_neg]
    have hc : Real.cos (c * Δ) = 1 - 2 * Real.sin (c * Δ / 2) ^ 2 := by
      rw [show c * Δ = 2 * (c * Δ / 2) by ring, Real.cos_two_mul, Real.cos_sq']; ring_nf
    rw [hc, neg_sq]
    field_simp
    ring

theorem norm_fejerKernel_le_one (c Δ : ℝ) : ‖fejerKernel c Δ‖ ≤ 1 := by
  rw [fejerKernel_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := Real.abs_sinc_le_one (c * Δ / 2)
  nlinarith [abs_nonneg (Real.sinc (c * Δ / 2)), sq_abs (Real.sinc (c * Δ / 2))]

/-- `K_c(Δ) ≤ 4/(cΔ)²`. -/
theorem norm_fejerKernel_le_inv_sq {c Δ : ℝ} (h : c * Δ ≠ 0) :
    ‖fejerKernel c Δ‖ ≤ 4 / (c * Δ) ^ 2 := by
  rw [fejerKernel_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hθ : c * Δ / 2 ≠ 0 := by intro h'; apply h; linarith
  have hs := abs_sinc_le_inv hθ
  have : Real.sinc (c * Δ / 2) ^ 2 ≤ (1 / |c * Δ / 2|) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hs 2
  refine this.trans (le_of_eq ?_)
  rw [div_pow, abs_div, div_pow, sq_abs, abs_two]
  field_simp
  ring

/-- `‖e^{iy} − e^{iy'}‖ ≤ |y − y'|`. -/
theorem norm_cexp_I_sub_le (y y' : ℝ) :
    ‖Complex.exp ((y : ℂ) * I) - Complex.exp ((y' : ℂ) * I)‖ ≤ |y - y'| := by
  have h : Complex.exp ((y : ℂ) * I) - Complex.exp ((y' : ℂ) * I) =
      Complex.exp ((y' : ℂ) * I) * (Complex.exp (I * ((y - y' : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_exp_I_mul_ofReal_sub_one,
    Real.norm_eq_abs, abs_mul, abs_two]
  have := Real.abs_sin_le_abs (x := (y - y') / 2)
  rw [abs_div, abs_two] at this
  linarith

/-- **`K_c` is `|c|`-Lipschitz.** -/
theorem norm_fejerKernel_sub_le (c Δ Δ' : ℝ) :
    ‖fejerKernel c Δ - fejerKernel c Δ'‖ ≤ |c| * |Δ - Δ'| * 2 := by
  unfold fejerKernel
  rw [← intervalIntegral.integral_sub]
  · refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := |c| * |Δ - Δ'|)
      fun β hβ => ?_).trans (le_of_eq (by norm_num))
    rw [Set.uIoc_of_le (by norm_num)] at hβ
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (triangleFn_nonneg 1 β)]
    have h1 := triangleFn_le_one one_pos β
    have h2 := norm_cexp_I_sub_le (β * c * Δ) (β * c * Δ')
    have hβ1 : |β| ≤ 1 := abs_le.mpr ⟨by linarith [hβ.1], hβ.2⟩
    have h3 : |β * c * Δ - β * c * Δ'| ≤ |c| * |Δ - Δ'| := by
      rw [show β * c * Δ - β * c * Δ' = β * (c * (Δ - Δ')) by ring, abs_mul, abs_mul]
      exact mul_le_of_le_one_left (by positivity) hβ1
    calc triangleFn 1 β * ‖Complex.exp ((β * c * Δ : ℝ) * I) - Complex.exp ((β * c * Δ' : ℝ) * I)‖
        ≤ 1 * (|c| * |Δ - Δ'|) := by
          apply mul_le_mul h1 (h2.trans h3) (norm_nonneg _) zero_le_one
      _ = |c| * |Δ - Δ'| := one_mul _
  · apply Continuous.intervalIntegrable
    have := continuous_triangleFn 1; fun_prop
  · apply Continuous.intervalIntegrable
    have := continuous_triangleFn 1; fun_prop


/-- Tails of `Σ 1/n²` over the naturals: `Σ_{n ≥ M} 1/(n+1)² ≤ 2/(M+1)`. -/
theorem tsum_ite_inv_sq_le (M : ℕ) :
    ∑' n : ℕ, (if M ≤ n then 1 / ((n : ℝ) + 1) ^ 2 else 0) ≤ 2 / ((M : ℝ) + 1) := by
  have hsum : Summable (fun n : ℕ => (if M ≤ n then 1 / ((n : ℝ) + 1) ^ 2 else 0)) := by
    refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => ?_)
      ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two))
    split_ifs
    · push_cast; exact le_rfl
    · positivity
  refine hsum.tsum_le_of_sum_le fun S => ?_
  -- compare with the finite sum over `Ioo M (N + 2)` of `1/i²`
  set N := S.sup id with hN
  have hS : S ⊆ Finset.range (N + 1) := fun n hn => Finset.mem_range.mpr
    (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))
  calc ∑ n ∈ S, (if M ≤ n then 1 / ((n : ℝ) + 1) ^ 2 else 0)
      ≤ ∑ n ∈ Finset.range (N + 1), (if M ≤ n then 1 / ((n : ℝ) + 1) ^ 2 else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg hS fun n _ _ => by split_ifs <;> positivity
    _ = ∑ i ∈ Finset.Ioo M (N + 2), ((i : ℝ) ^ 2)⁻¹ := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
        refine Finset.sum_bij (fun n _ => n + 1) ?_ ?_ ?_ ?_
        · intro n hn
          rw [Finset.mem_filter, Finset.mem_range] at hn
          rw [Finset.mem_Ioo]; omega
        · intro a _ b _ h; omega
        · intro i hi
          rw [Finset.mem_Ioo] at hi
          refine ⟨i - 1, ?_, by omega⟩
          rw [Finset.mem_filter, Finset.mem_range]; omega
        · intro n _
          push_cast; rw [one_div]
    _ ≤ 2 / ((M : ℝ) + 1) := sum_Ioo_inv_sq_le M (N + 2)

/-- Tails over `ℤ`: `Σ_{|m| > M} 1/m² ≤ 4/(M+1)`. -/
theorem tsum_int_ite_inv_sq_le (M : ℕ) :
    ∑' m : ℤ, (if (M : ℤ) < |m| then 1 / ((m : ℝ)) ^ 2 else 0) ≤ 4 / ((M : ℝ) + 1) := by
  set f : ℤ → ℝ := fun m => if (M : ℤ) < |m| then 1 / ((m : ℝ)) ^ 2 else 0 with hf
  have hpos : ∀ n : ℕ, f ((n : ℤ) + 1) = if M ≤ n then 1 / ((n : ℝ) + 1) ^ 2 else 0 := by
    intro n
    simp only [hf]
    have : |((n : ℤ) + 1)| = (n : ℤ) + 1 := abs_of_nonneg (by positivity)
    rw [this]
    by_cases h : M ≤ n
    · rw [if_pos (by omega), if_pos h]; push_cast; ring
    · rw [if_neg (by omega), if_neg h]
  have hneg : ∀ n : ℕ, f (-((n : ℤ) + 1)) = if M ≤ n then 1 / ((n : ℝ) + 1) ^ 2 else 0 := by
    intro n
    simp only [hf, abs_neg]
    have : |((n : ℤ) + 1)| = (n : ℤ) + 1 := abs_of_nonneg (by positivity)
    rw [this]
    by_cases h : M ≤ n
    · rw [if_pos (by omega), if_pos h]; push_cast; ring
    · rw [if_neg (by omega), if_neg h]
  have hs : Summable (fun n : ℕ => (if M ≤ n then 1 / ((n : ℝ) + 1) ^ 2 else 0)) := by
    refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => ?_)
      ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two))
    split_ifs
    · push_cast; exact le_rfl
    · positivity
  have hsp : Summable (fun n : ℕ => f ((n : ℤ) + 1)) := by
    simp only [hpos]; exact hs
  have hsn : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) := by
    simp only [hneg]; exact hs
  have h0 : f 0 = 0 := by simp [hf]
  have e1 : (fun n : ℕ => f ((n : ℤ) + 1)) =
      fun n : ℕ => (if M ≤ n then 1 / ((n : ℝ) + 1) ^ 2 else 0) := funext hpos
  have e2 : (fun n : ℕ => f (-((n : ℤ) + 1))) =
      fun n : ℕ => (if M ≤ n then 1 / ((n : ℝ) + 1) ^ 2 else 0) := funext hneg
  have := tsum_ite_inv_sq_le M
  calc ∑' m : ℤ, f m = ∑' n : ℕ, f ((n : ℤ) + 1) + f 0 + ∑' n : ℕ, f (-((n : ℤ) + 1)) :=
        tsum_of_add_one_of_neg_add_one hsp hsn
    _ = 2 * ∑' n : ℕ, (if M ≤ n then 1 / ((n : ℝ) + 1) ^ 2 else 0) := by
        rw [e1, e2, h0]; ring
    _ ≤ 2 * (2 / ((M : ℝ) + 1)) := by linarith
    _ = 4 / ((M : ℝ) + 1) := by ring

/-- The ideal lattice sum over `ℤ` vanishes off resonance. -/
theorem tsum_fejer_lattice_eq_zero {c g θ : ℝ} (hc : 0 < c) (hg : 0 < g)
    (hres : ∀ n : ℤ, c * g / (2 * Real.pi) ≤ |-(θ * g) / (2 * Real.pi) + n|) :
    ∑' m : ℤ, Complex.exp (-(θ * (m * g)) * I) * fejerKernel c (m * g) = 0 := by
  have ha : 0 < c * g / (2 * Real.pi) := by positivity
  have h := tsum_sinc_sq_mul_fourier_eq_zero ha hres
  rw [← h]
  congr 1; funext m
  rw [fejerKernel_eq, fourier_coe_apply, mul_comm]
  congr 1
  · congr 2; field_simp
  · congr 1; push_cast; field_simp

/-- **Fejér sums over near-lattices.** -/
theorem norm_sum_fejer_nearLattice_le {c g θ ε : ℝ} (M : ℕ) (hc : 0 < c) (hg : 0 < g)
    (hε : 0 ≤ ε) (hres : ∀ n : ℤ, c * g / (2 * Real.pi) ≤ |-(θ * g) / (2 * Real.pi) + n|)
    (Δ : ℤ → ℝ) (hΔ : ∀ m : ℤ, |m| ≤ M → |Δ m - m * g| ≤ |m| * g * ε) :
    ‖∑ m ∈ Finset.Icc (-(M : ℤ)) M, Complex.exp (-(θ * Δ m) * I) * fejerKernel c (Δ m)‖ ≤
      16 / (c ^ 2 * g ^ 2 * ((M : ℝ) + 1)) + (|θ| + 2 * c) * g * ε * (2 * M + 1) * M := by
  classical
  set ideal : ℤ → ℂ := fun m => Complex.exp (-(θ * (m * g)) * I) * fejerKernel c (m * g) with hideal
  set S := Finset.Icc (-(M : ℤ)) M with hS
  -- the ideal finite sum is minus its tail
  have hbound : ∀ m : ℤ, m ≠ 0 → ‖ideal m‖ ≤ 4 / (c * g) ^ 2 * (1 / (m : ℝ) ^ 2) := by
    intro m hm
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have h3 : ‖Complex.exp (-(θ * (m * g)) * I)‖ = 1 := by
      rw [show (-(θ * (m * g)) : ℂ) * I = ((-(θ * (m * g)) : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    rw [hideal]
    dsimp only
    rw [norm_mul, h3, one_mul]
    have hcm : c * (m * g) ≠ 0 := by positivity
    refine (norm_fejerKernel_le_inv_sq hcm).trans (le_of_eq ?_)
    field_simp
  have hsumm : Summable ideal := by
    refine Summable.of_norm_bounded_eventually (g := fun m : ℤ => 4 / (c * g) ^ 2 * (1 / (m : ℝ) ^ 2))
      ((Real.summable_one_div_int_pow.mpr one_lt_two).mul_left _) ?_
    filter_upwards [(Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with m hm
    exact hbound m hm
  have htot := tsum_fejer_lattice_eq_zero hc hg hres
  have hsplit := hsumm.sum_add_tsum_compl (s := S)
  rw [htot] at hsplit
  have hideal_sum : ‖∑ m ∈ S, ideal m‖ ≤ 16 / (c ^ 2 * g ^ 2 * ((M : ℝ) + 1)) := by
    have heq : ∑ m ∈ S, ideal m = -∑' m : ↑((S : Set ℤ)ᶜ), ideal m := by
      linear_combination hsplit
    rw [heq, norm_neg]
    -- bound the complement tail
    have hle : ∀ m : ↑((S : Set ℤ)ᶜ), ‖ideal m‖ ≤
        4 / (c * g) ^ 2 * (if (M : ℤ) < |(m : ℤ)| then 1 / ((m : ℤ) : ℝ) ^ 2 else 0) := by
      intro m
      have hm : (M : ℤ) < |(m : ℤ)| := by
        have := m.2
        simp only [Set.mem_compl_iff, Finset.mem_coe, hS, Finset.mem_Icc, not_and_or,
          not_le] at this
        rcases this with h | h
        · rw [abs_of_neg (by omega)]; omega
        · rw [abs_of_pos (by omega)]; omega
      rw [if_pos hm]
      exact hbound m (by intro h; rw [h, abs_zero] at hm; omega)
    have hgs : Summable (fun m : ℤ => 4 / (c * g) ^ 2 *
        (if (M : ℤ) < |m| then 1 / (m : ℝ) ^ 2 else 0)) := by
      refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
        ((Real.summable_one_div_int_pow.mpr one_lt_two).mul_left (4 / (c * g) ^ 2))
      · split_ifs
        · positivity
        · simp
      · split_ifs
        · exact le_rfl
        · simp only [mul_zero]; positivity
    calc ‖∑' m : ↑((S : Set ℤ)ᶜ), ideal m‖
        ≤ ∑' m : ↑((S : Set ℤ)ᶜ), 4 / (c * g) ^ 2 *
            (if (M : ℤ) < |(m : ℤ)| then 1 / ((m : ℤ) : ℝ) ^ 2 else 0) :=
          tsum_of_norm_bounded (hgs.subtype _).hasSum hle
      _ ≤ ∑' m : ℤ, 4 / (c * g) ^ 2 * (if (M : ℤ) < |m| then 1 / (m : ℝ) ^ 2 else 0) :=
          Summable.tsum_subtype_le _ _ (fun m => by split_ifs <;> positivity) hgs
      _ = 4 / (c * g) ^ 2 * ∑' m : ℤ, (if (M : ℤ) < |m| then 1 / (m : ℝ) ^ 2 else 0) :=
          tsum_mul_left
      _ ≤ 4 / (c * g) ^ 2 * (4 / ((M : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (tsum_int_ite_inv_sq_le M) (by positivity)
      _ = 16 / (c ^ 2 * g ^ 2 * ((M : ℝ) + 1)) := by field_simp; ring
  -- the drift
  have hdrift : ∀ m ∈ S, ‖Complex.exp (-(θ * Δ m) * I) * fejerKernel c (Δ m) - ideal m‖ ≤
      (|θ| + 2 * c) * (|(m : ℝ)| * g * ε) := by
    intro m hm
    have hmM : |m| ≤ M := by
      rw [hS, Finset.mem_Icc] at hm; rw [abs_le]; omega
    have hd := hΔ m hmM
    rw [hideal]
    have e1 : Complex.exp (-(θ * Δ m) * I) * fejerKernel c (Δ m) -
        Complex.exp (-(θ * (m * g)) * I) * fejerKernel c (m * g) =
        (Complex.exp (-(θ * Δ m) * I) - Complex.exp (-(θ * (m * g)) * I)) * fejerKernel c (Δ m) +
          Complex.exp (-(θ * (m * g)) * I) * (fejerKernel c (Δ m) - fejerKernel c (m * g)) := by ring
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖Complex.exp (-(θ * Δ m) * I) - Complex.exp (-(θ * (m * g)) * I)‖ ≤
        |θ| * |Δ m - m * g| := by
      have := norm_cexp_I_sub_le (-(θ * Δ m)) (-(θ * (m * g)))
      push_cast at this
      refine this.trans (le_of_eq ?_)
      rw [show -(θ * Δ m) - -(θ * (m * g)) = -(θ * (Δ m - m * g)) by ring, abs_neg, abs_mul]
    have h2 := norm_fejerKernel_le_one c (Δ m)
    have h3 : ‖Complex.exp (-(θ * (m * g)) * I)‖ = 1 := by
      rw [show (-(θ * (m * g)) : ℂ) * I = ((-(θ * (m * g)) : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    have h4 := norm_fejerKernel_sub_le c (Δ m) (m * g)
    rw [h3, one_mul, abs_of_pos hc] at *
    have hmabs : |(m : ℝ)| = ((|m| : ℤ) : ℝ) := by push_cast; rfl
    calc ‖Complex.exp (-(θ * Δ m) * I) - Complex.exp (-(θ * (m * g)) * I)‖ * ‖fejerKernel c (Δ m)‖ +
          ‖fejerKernel c (Δ m) - fejerKernel c (m * g)‖
        ≤ |θ| * |Δ m - m * g| * 1 + c * |Δ m - m * g| * 2 :=
          add_le_add (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h4
      _ = (|θ| + 2 * c) * |Δ m - m * g| := by ring
      _ ≤ (|θ| + 2 * c) * (|(m : ℝ)| * g * ε) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine hd.trans (le_of_eq ?_)
          push_cast; rfl
  have hdrift_sum : ‖∑ m ∈ S, (Complex.exp (-(θ * Δ m) * I) * fejerKernel c (Δ m) - ideal m)‖ ≤
      (|θ| + 2 * c) * g * ε * (2 * M + 1) * M := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum hdrift).trans ?_
    have hcard : (S.card : ℝ) = 2 * M + 1 := by
      rw [hS, Int.card_Icc, show (M : ℤ) + 1 - -(M : ℤ) = ((2 * M + 1 : ℕ) : ℤ) by push_cast; ring,
        Int.toNat_natCast]
      push_cast; ring
    have hm : ∀ m ∈ S, (|θ| + 2 * c) * (|(m : ℝ)| * g * ε) ≤ (|θ| + 2 * c) * g * ε * M := by
      intro m hm
      rw [hS, Finset.mem_Icc] at hm
      have : |(m : ℝ)| ≤ M := by
        rw [abs_le]; constructor <;> exact_mod_cast (by omega : _)
      have h0 : 0 ≤ (|θ| + 2 * c) * g * ε := by positivity
      nlinarith
    refine (Finset.sum_le_sum hm).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring
  calc ‖∑ m ∈ S, Complex.exp (-(θ * Δ m) * I) * fejerKernel c (Δ m)‖
      = ‖∑ m ∈ S, ideal m + ∑ m ∈ S, (Complex.exp (-(θ * Δ m) * I) * fejerKernel c (Δ m) - ideal m)‖ := by
        rw [← Finset.sum_add_distrib]; congr 1; refine Finset.sum_congr rfl fun m _ => by ring
    _ ≤ ‖∑ m ∈ S, ideal m‖ +
        ‖∑ m ∈ S, (Complex.exp (-(θ * Δ m) * I) * fejerKernel c (Δ m) - ideal m)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hideal_sum hdrift_sum


/-- `K_c` is even. -/
theorem fejerKernel_neg (c Δ : ℝ) : fejerKernel c (-Δ) = fejerKernel c Δ := by
  rw [fejerKernel_eq, fejerKernel_eq]
  congr 2
  rw [show c * -Δ / 2 = -(c * Δ / 2) by ring]
  unfold Real.sinc
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (neg_eq_zero.mp h1) h2
  · exact absurd (by rw [h2, neg_zero]) h1
  · rw [Real.sin_neg, neg_div_neg_eq]

/-- Far from the centre, `‖K_c(Δ)‖ ≤ (8/(c²τ²)) f_τ(Δ)` when `|Δ| ≥ τ`. -/
theorem norm_fejerKernel_le_lorentz {c τ Δ : ℝ} (hc : 0 < c) (hτ : 0 < τ) (hΔ : τ ≤ |Δ|) :
    ‖fejerKernel c Δ‖ ≤ 8 / (c ^ 2 * τ ^ 2) * lorentzF τ Δ := by
  have hΔ0 : Δ ≠ 0 := by intro h; rw [h, abs_zero] at hΔ; linarith
  have hcΔ : c * Δ ≠ 0 := mul_ne_zero hc.ne' hΔ0
  refine (norm_fejerKernel_le_inv_sq hcΔ).trans ?_
  have hsq : τ ^ 2 ≤ Δ ^ 2 := by rw [← sq_abs Δ]; exact pow_le_pow_left₀ hτ.le hΔ 2
  unfold lorentzF
  rw [mul_pow, div_le_iff₀ (by positivity)]
  rw [show 8 / (c ^ 2 * τ ^ 2) * (τ ^ 2 / (τ ^ 2 + Δ ^ 2)) * (c ^ 2 * Δ ^ 2) =
    8 * Δ ^ 2 / (τ ^ 2 + Δ ^ 2) by field_simp]
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **The Fejér pair sum at one point of a near-lattice.** Let `y` be the ordinates, `B` the index
set, `n` with `[n − M, n + M] ⊆ B`; let the near-lattice and non-resonance hypotheses of
`norm_sum_fejer_nearLattice_le` hold for `Δ_m = y_{n+m} − y_n`, and let the indices of `B` outside
`[n − M, n + M]` be at distance `≥ τ₂` from `y_n` with Lorentzian mass `≤ Λ`. Then
`‖Σ_{k ∈ B} e^{iθ(y_n − y_k)} w(y_n − y_k) K_c(y_n − y_k)‖` is bounded by the near-lattice terms
plus the weight correction plus `(8/(c²τ₂²)) Λ`, where `w(Δ) = 4/(4 + Δ²)`. -/
theorem norm_fejer_pair_sum_le {c g θ ε τ₂ Λ : ℝ} (M n : ℕ) (hc : 0 < c) (hg : 0 < g)
    (hε : 0 ≤ ε) (hτ₂ : 0 < τ₂) (hMn : M ≤ n) {y : ℕ → ℝ} {B : Finset ℕ}
    (hB : Finset.Icc (n - M) (n + M) ⊆ B)
    (hres : ∀ ℓ : ℤ, c * g / (2 * Real.pi) ≤ |-(θ * g) / (2 * Real.pi) + ℓ|)
    (hnear : ∀ m : ℤ, |m| ≤ M → |(y (n + m).toNat - y n) - m * g| ≤ |m| * g * ε)
    (hfar : ∀ k ∈ B, k ∉ Finset.Icc (n - M) (n + M) → τ₂ ≤ |y n - y k|)
    (hmass : ∑ k ∈ B.filter (fun k => k ∉ Finset.Icc (n - M) (n + M)),
      lorentzF τ₂ (y n - y k) ≤ Λ) :
    ‖∑ k ∈ B, Complex.exp ((θ * (y n - y k) : ℝ) * I) * ((4 / (4 + (y n - y k) ^ 2) : ℝ) : ℂ) *
        fejerKernel c (y n - y k)‖ ≤
      16 / (c ^ 2 * g ^ 2 * ((M : ℝ) + 1)) + (|θ| + 2 * c) * g * ε * (2 * M + 1) * M +
        (2 * M + 1) * (M * g * (1 + ε)) ^ 2 / 4 + 8 / (c ^ 2 * τ₂ ^ 2) * Λ := by
  classical
  set F : ℝ → ℂ := fun Δ => Complex.exp ((θ * Δ : ℝ) * I) * ((4 / (4 + Δ ^ 2) : ℝ) : ℂ) *
    fejerKernel c Δ with hF
  set N := Finset.Icc (n - M) (n + M) with hN
  have hsplit : ∑ k ∈ B, F (y n - y k) = ∑ k ∈ N, F (y n - y k) +
      ∑ k ∈ B.filter (fun k => k ∉ N), F (y n - y k) := by
    rw [← Finset.sum_filter_add_sum_filter_not B (fun k => k ∈ N)]
    congr 1
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hB]
  rw [hsplit]
  -- the far part
  have hfarb : ‖∑ k ∈ B.filter (fun k => k ∉ N), F (y n - y k)‖ ≤ 8 / (c ^ 2 * τ₂ ^ 2) * Λ := by
    refine (norm_sum_le _ _).trans ?_
    have hpt : ∀ k ∈ B.filter (fun k => k ∉ N), ‖F (y n - y k)‖ ≤
        8 / (c ^ 2 * τ₂ ^ 2) * lorentzF τ₂ (y n - y k) := by
      intro k hk
      rw [Finset.mem_filter] at hk
      have hd := hfar k hk.1 hk.2
      rw [hF]; dsimp only
      rw [norm_mul, norm_mul, show ((θ * (y n - y k) : ℝ) : ℂ) * I =
        ((θ * (y n - y k) : ℝ) : ℂ) * I from rfl, Complex.norm_exp_ofReal_mul_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have hw : 4 / (4 + (y n - y k) ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith [sq_nonneg (y n - y k)]
      have hK := norm_fejerKernel_le_lorentz hc hτ₂ hd
      calc 4 / (4 + (y n - y k) ^ 2) * ‖fejerKernel c (y n - y k)‖
          ≤ 1 * ‖fejerKernel c (y n - y k)‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg _)
        _ ≤ 8 / (c ^ 2 * τ₂ ^ 2) * lorentzF τ₂ (y n - y k) := by rw [one_mul]; exact hK
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hmass (by positivity)
  -- the near part, reindexed by `m ∈ [−M, M]`
  set Δ : ℤ → ℝ := fun m => y (n + m).toNat - y n with hΔ
  have hreindex : ∑ k ∈ N, F (y n - y k) =
      ∑ m ∈ Finset.Icc (-(M : ℤ)) M, F (-(Δ m)) := by
    symm
    refine Finset.sum_nbij' (fun m => (n + m).toNat) (fun k => (k : ℤ) - n) ?_ ?_ ?_ ?_ ?_
    · intro m hm
      rw [Finset.mem_Icc] at hm
      rw [hN, Finset.mem_Icc]; omega
    · intro k hk
      rw [hN, Finset.mem_Icc] at hk
      rw [Finset.mem_Icc]; omega
    · intro m hm
      rw [Finset.mem_Icc] at hm
      omega
    · intro k hk
      rw [hN, Finset.mem_Icc] at hk
      omega
    · intro m _
      simp only [hΔ]; congr 1; ring
  rw [hreindex]
  have hsplit2 : ∑ m ∈ Finset.Icc (-(M : ℤ)) M, F (-(Δ m)) =
      ∑ m ∈ Finset.Icc (-(M : ℤ)) M, Complex.exp (-(θ * Δ m) * I) * fejerKernel c (Δ m) +
      ∑ m ∈ Finset.Icc (-(M : ℤ)) M, Complex.exp (-(θ * Δ m) * I) *
        (((4 / (4 + (Δ m) ^ 2) : ℝ) : ℂ) - 1) * fejerKernel c (Δ m) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hF]; dsimp only
    rw [fejerKernel_neg, neg_sq]
    push_cast
    ring_nf
  rw [hsplit2]
  have hL := norm_sum_fejer_nearLattice_le M hc hg hε hres Δ hnear
  have hw : ‖∑ m ∈ Finset.Icc (-(M : ℤ)) M, Complex.exp (-(θ * Δ m) * I) *
        (((4 / (4 + (Δ m) ^ 2) : ℝ) : ℂ) - 1) * fejerKernel c (Δ m)‖ ≤
      (2 * M + 1) * (M * g * (1 + ε)) ^ 2 / 4 := by
    refine (norm_sum_le _ _).trans ?_
    have hpt : ∀ m ∈ Finset.Icc (-(M : ℤ)) M, ‖Complex.exp (-(θ * Δ m) * I) *
        (((4 / (4 + (Δ m) ^ 2) : ℝ) : ℂ) - 1) * fejerKernel c (Δ m)‖ ≤ (M * g * (1 + ε)) ^ 2 / 4 := by
      intro m hm
      have hmM : |m| ≤ M := by rw [Finset.mem_Icc] at hm; rw [abs_le]; omega
      have hd := hnear m hmM
      have hΔb : |Δ m| ≤ M * g * (1 + ε) := by
        have h1 : |Δ m| ≤ |(m : ℝ)| * g + |(m : ℝ)| * g * ε := by
          have := abs_sub_abs_le_abs_sub (Δ m) (m * g)
          rw [abs_mul, abs_of_pos hg] at this
          have h3 : |((|m| : ℤ) : ℝ)| = |(m : ℝ)| := by push_cast; rw [abs_abs]
          push_cast at hd
          linarith
        have h2 : |(m : ℝ)| ≤ M := by
          have : ((|m| : ℤ) : ℝ) ≤ M := by exact_mod_cast hmM
          push_cast at this; exact this
        have h4 := mul_le_mul_of_nonneg_right h2 (show 0 ≤ g * (1 + ε) by positivity)
        nlinarith
      rw [norm_mul, norm_mul, show (-(θ * Δ m) : ℂ) * I = ((-(θ * Δ m) : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, one_mul]
      have hK := norm_fejerKernel_le_one c (Δ m)
      have hw1 : ‖(((4 / (4 + (Δ m) ^ 2) : ℝ) : ℂ) - 1)‖ ≤ (Δ m) ^ 2 / 4 := by
        rw [show (((4 / (4 + (Δ m) ^ 2) : ℝ) : ℂ) - 1) = (((4 / (4 + (Δ m) ^ 2) - 1 : ℝ)) : ℂ) by
          push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
        rw [show 4 / (4 + (Δ m) ^ 2) - 1 = -((Δ m) ^ 2 / (4 + (Δ m) ^ 2)) by field_simp; ring,
          abs_neg, abs_of_nonneg (by positivity)]
        exact div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by nlinarith [sq_nonneg (Δ m)])
      have hsq : (Δ m) ^ 2 ≤ (M * g * (1 + ε)) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hΔb 2
      calc ‖(((4 / (4 + (Δ m) ^ 2) : ℝ) : ℂ) - 1)‖ * ‖fejerKernel c (Δ m)‖
          ≤ (Δ m) ^ 2 / 4 * 1 := mul_le_mul hw1 hK (norm_nonneg _) (by positivity)
        _ ≤ (M * g * (1 + ε)) ^ 2 / 4 := by linarith
    refine (Finset.sum_le_sum hpt).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, Int.card_Icc,
      show (M : ℤ) + 1 - -(M : ℤ) = ((2 * M + 1 : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]
    push_cast; ring
  calc ‖(∑ m ∈ Finset.Icc (-(M : ℤ)) M, Complex.exp (-(θ * Δ m) * I) * fejerKernel c (Δ m) +
        ∑ m ∈ Finset.Icc (-(M : ℤ)) M, Complex.exp (-(θ * Δ m) * I) *
          (((4 / (4 + (Δ m) ^ 2) : ℝ) : ℂ) - 1) * fejerKernel c (Δ m)) +
        ∑ k ∈ B.filter (fun k => k ∉ N), F (y n - y k)‖
      ≤ ‖∑ m ∈ Finset.Icc (-(M : ℤ)) M, Complex.exp (-(θ * Δ m) * I) * fejerKernel c (Δ m)‖ +
        ‖∑ m ∈ Finset.Icc (-(M : ℤ)) M, Complex.exp (-(θ * Δ m) * I) *
          (((4 / (4 + (Δ m) ^ 2) : ℝ) : ℂ) - 1) * fejerKernel c (Δ m)‖ +
        ‖∑ k ∈ B.filter (fun k => k ∉ N), F (y n - y k)‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ _ := by linarith


/-- **The Fejér kernel under a Lorentzian:** `‖K_c(Δ)‖ ≤ 2 f_{2/c}(Δ)`. -/
theorem norm_fejerKernel_le_two_lorentzF {c : ℝ} (hc : 0 < c) (Δ : ℝ) :
    ‖fejerKernel c Δ‖ ≤ 2 * lorentzF (2 / c) Δ := by
  have hσ : 0 < 2 / c := by positivity
  rcases le_or_gt (|Δ|) (2 / c) with h | h
  · have hΔ2 : Δ ^ 2 ≤ (2 / c) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    refine (norm_fejerKernel_le_one c Δ).trans ?_
    unfold lorentzF
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith
  · have hΔ0 : Δ ≠ 0 := by intro h0; rw [h0, abs_zero] at h; linarith
    refine (norm_fejerKernel_le_inv_sq (mul_ne_zero hc.ne' hΔ0)).trans ?_
    have hΔ2 : (2 / c) ^ 2 ≤ Δ ^ 2 := by rw [← sq_abs Δ]; exact pow_le_pow_left₀ hσ.le h.le 2
    unfold lorentzF
    rw [mul_pow, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have hc2 : (2 / c) ^ 2 * c ^ 2 = 4 := by field_simp; norm_num
    nlinarith [mul_le_mul_of_nonneg_left hΔ2 (sq_nonneg c), sq_nonneg Δ, sq_nonneg c]

end GaloisForLFunctions.HTGeometry
