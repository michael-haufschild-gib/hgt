import GaloisForLFunctions.RHTower.WeilAbscissaRigidity
import GaloisForLFunctions.RHTower.WeilDeviationTranslationBound

/-!
# One-sided positive-definite null potentials vanish

For log-bounded `u` with `u(0) = u(1) = 0`, the null potential is
`ψ_u(y) = Σ_n u(n)(K(y + log n) + K(y − log n))` (`WeilRegular.nullPotential`), where `K = Φ ⋆ Φ̃`
is the autocorrelation of Riemann's kernel.  Its Fourier transform is `Ξ²·Σ_n u(n) 2cos(t log n)`,
so `ψ_u` is positive definite exactly when `Ξ²·Σ u(n)cos(t log n)` is a positive measure.

**Theorem** (`eq_zero_of_positiveDefinite_nullPotential_of_nonneg`).  If `ψ_u` is positive definite
and `u ≥ 0`, then `u = 0`.  Also `eq_zero_of_positiveDefinite_nullPotential_of_nonpos`: if `ψ_u` is
positive definite and `u ≤ 0`, then `u = 0`.

So every nonzero sequence with a positive-definite null potential takes both signs: the one-sided
form of the annihilator question is equivalent to the two-sided one.

**Proof** (`u ≥ 0`).
* Positive definiteness gives `ψ_u(y) ≤ ψ_u(0)` for every `y`.
* Every term of `ψ_u` is nonnegative, and `K ≥ m > 0` on `[−1, 1]`.  At `y = k + 1/2` the terms with
  `⌊log n⌋ = k` give `m Σ_{⌊log n⌋ = k} u(n) ≤ ψ_u(0)`.
* Hence `Σ u(n) n^{−1/4} ≤ (ψ_u(0)/m) Σ_k e^{−k/4} < ∞`, and absolute-abscissa rigidity
  (`eq_zero_of_positiveDefinite_nullPotential_of_rpow_summable`, at `σ = 1/4 < 1/2`) gives `u = 0`.
-/

open Real Finset GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.WeilAbscissa

open RHTower.WeilRegular

/-- The autocorrelation of Riemann's kernel is bounded below on `[−1, 1]`. -/
theorem exists_riemannAutocorr_ge :
    ∃ m : ℝ, 0 < m ∧ ∀ y : ℝ, |y| ≤ 1 → m ≤ riemannAutocorr y := by
  obtain ⟨y₀, hy₀, hmin⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_isMinOn
    (Set.nonempty_Icc.mpr (by norm_num))
    RHTower.WeilExcess.continuous_riemannAutocorr.continuousOn
  exact ⟨riemannAutocorr y₀, RHTower.WeilExcess.riemannAutocorr_pos y₀, fun y hy =>
    hmin (Set.mem_Icc.mpr (abs_le.mp hy))⟩

theorem summable_nullPotential_term {u : ℕ → ℝ} (hu0 : u 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |u n| ≤ 2 * Real.log n + A) (y : ℝ) :
    Summable fun n : ℕ =>
      u n * (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)) := by
  obtain ⟨C₁, -, hC₁⟩ := RHTower.WeilExcess.exists_riemannAutocorr_le
  exact Summable.of_norm_bounded
    ((RHTower.WeilExcess.summable_log_add_mul_inv_sq hA).mul_left _)
    (RHTower.WeilExcess.norm_potential_term_le RHTower.WeilExcess.riemannAutocorr_nonneg hC₁
      ha hu0 hA (le_refl |y|))

/-- For a nonnegative sequence, `m · Σ_{n ∈ F} u(n) ≤ ψ_u(0)` whenever every `log n`, `n ∈ F`, lies
within distance `1` of one point `y`. -/
theorem mul_sum_le_nullPotential_zero {u : ℕ → ℝ} (hu0 : u 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |u n| ≤ 2 * Real.log n + A) (hnn : ∀ n, 0 ≤ u n)
    (hPD : PositiveDefiniteOnReal fun y => ((nullPotential u y : ℝ) : ℂ))
    {m : ℝ} (hm : ∀ y : ℝ, |y| ≤ 1 → m ≤ riemannAutocorr y)
    (y : ℝ) (F : Finset ℕ) (hF : ∀ n ∈ F, |y - Real.log n| ≤ 1) :
    m * ∑ n ∈ F, u n ≤ nullPotential u 0 := by
  have hterm : ∀ n, 0 ≤ u n * (riemannAutocorr (y + Real.log n) +
      riemannAutocorr (y - Real.log n)) := fun n =>
    mul_nonneg (hnn n) (add_nonneg (RHTower.WeilExcess.riemannAutocorr_nonneg _)
      (RHTower.WeilExcess.riemannAutocorr_nonneg _))
  have h1 : m * ∑ n ∈ F, u n ≤ ∑ n ∈ F, u n * (riemannAutocorr (y + Real.log n) +
      riemannAutocorr (y - Real.log n)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hK := hm _ (hF n hn)
    have hK' := RHTower.WeilExcess.riemannAutocorr_nonneg (y + Real.log n)
    nlinarith [hnn n]
  have h2 := (summable_nullPotential_term hu0 hA ha y).sum_le_tsum F (fun n _ => hterm n)
  have h3 : nullPotential u y ≤ nullPotential u 0 := by
    have h := hPD.norm_le y
    rw [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re] at h
    exact le_trans (le_abs_self _) h
  unfold nullPotential at h3 ⊢
  linarith

/-- A nonnegative sequence with a positive-definite null potential has `Σ u(n) n^{−1/4} < ∞`. -/
theorem summable_mul_rpow_of_positiveDefinite_nullPotential_of_nonneg {u : ℕ → ℝ}
    (hu0 : u 0 = 0) {A : ℝ} (hA : 0 ≤ A) (ha : ∀ n, |u n| ≤ 2 * Real.log n + A)
    (hnn : ∀ n, 0 ≤ u n) (hPD : PositiveDefiniteOnReal fun y => ((nullPotential u y : ℝ) : ℂ)) :
    Summable fun n : ℕ => |u n| * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨m, hm0, hm⟩ := exists_riemannAutocorr_ge
  set B : ℝ := nullPotential u 0 / m with hBdef
  set q : ℝ := Real.exp (-(1 / 4 : ℝ)) with hqdef
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    have h := Real.exp_lt_exp.mpr (show -(1 / 4 : ℝ) < 0 by norm_num)
    rwa [Real.exp_zero] at h
  set k : ℕ → ℕ := fun n => ⌊Real.log n⌋₊ with hkdef
  -- the block bound
  have hblock : ∀ (j : ℕ) (F : Finset ℕ), (∀ n ∈ F, k n = j) → ∑ n ∈ F, u n ≤ B := by
    intro j F hF
    rw [hBdef, le_div_iff₀ hm0, mul_comm]
    refine mul_sum_le_nullPotential_zero hu0 hA ha hnn hPD hm (j + 1 / 2) F fun n hn => ?_
    have hkn := hF n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · have hj : j = 0 := by simp [hkdef] at hkn; omega
      subst hj
      norm_num
    · have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
      have h1 : (j : ℝ) ≤ Real.log n := by
        rw [← hkn]; exact Nat.floor_le hlog
      have h2 : Real.log n < j + 1 := by
        rw [← hkn]; exact Nat.lt_floor_add_one _
      rw [abs_le]; constructor <;> linarith
  -- the weight bound on a block
  have hweight : ∀ n : ℕ, 0 < n → (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤ q ^ (k n) := by
    intro n hn
    have hpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    rw [Real.rpow_def_of_pos hpos, hqdef, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have := Nat.floor_le hlog
    simp only [hkdef] at this ⊢
    nlinarith
  refine summable_of_sum_range_le (c := B * (1 - q)⁻¹) (fun n => by positivity) fun M => ?_
  have hB : 0 ≤ B := by
    rw [hBdef]
    refine div_nonneg ?_ hm0.le
    have := mul_sum_le_nullPotential_zero hu0 hA ha hnn hPD hm 0 ∅ (by simp)
    simpa using this
  calc ∑ n ∈ range M, |u n| * (n : ℝ) ^ (-(1 / 4 : ℝ))
      ≤ ∑ n ∈ range M, u n * q ^ (k n) := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [abs_of_nonneg (hnn n)]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [hu0]
        · exact mul_le_mul_of_nonneg_left (hweight n hn) (hnn n)
    _ = ∑ j ∈ (range M).image k,
          ∑ n ∈ (range M).filter (fun n : ℕ => k n = j), u n * q ^ j := by
        rw [← Finset.sum_fiberwise_of_maps_to (g := k) (t := (range M).image k)
          (fun n hn => Finset.mem_image_of_mem k hn)]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun n hn => ?_
        rw [(Finset.mem_filter.mp hn).2]
    _ ≤ ∑ j ∈ (range M).image k, B * q ^ j := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right
          (hblock j _ fun (n : ℕ) hn => (Finset.mem_filter.mp hn).2)
          (pow_nonneg hq0 j)
    _ ≤ ∑' j : ℕ, B * q ^ j :=
        ((summable_geometric_of_lt_one hq0 hq1).mul_left B).sum_le_tsum _
          (fun j _ => mul_nonneg hB (pow_nonneg hq0 j))
    _ = B * (1 - q)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]

/-- **Nonnegative sequences with positive-definite null potential vanish.** -/
theorem eq_zero_of_positiveDefinite_nullPotential_of_nonneg {u : ℕ → ℝ} (hu0 : u 0 = 0)
    (hu1 : u 1 = 0) {A : ℝ} (hA : 0 ≤ A) (ha : ∀ n, |u n| ≤ 2 * Real.log n + A)
    (hnn : ∀ n, 0 ≤ u n) (hPD : PositiveDefiniteOnReal fun y => ((nullPotential u y : ℝ) : ℂ)) :
    u = 0 :=
  eq_zero_of_positiveDefinite_nullPotential_of_rpow_summable hu0 hu1 hA ha (by norm_num)
    (summable_mul_rpow_of_positiveDefinite_nullPotential_of_nonneg hu0 hA ha hnn hPD) hPD

/-- **Nonpositive sequences with positive-definite null potential vanish.**  Here `ψ_u ≤ 0`, so the
bound `|ψ_u| ≤ ψ_u(0)` forces `ψ_u(0) = 0`, and every term of `ψ_u(0)` has a sign. -/
theorem eq_zero_of_positiveDefinite_nullPotential_of_nonpos {u : ℕ → ℝ} (hu0 : u 0 = 0)
    {A : ℝ} (hA : 0 ≤ A) (ha : ∀ n, |u n| ≤ 2 * Real.log n + A) (hnp : ∀ n, u n ≤ 0)
    (hPD : PositiveDefiniteOnReal fun y => ((nullPotential u y : ℝ) : ℂ)) :
    u = 0 := by
  have hs := summable_nullPotential_term hu0 hA ha 0
  have hterm : ∀ n, u n * (riemannAutocorr (0 + Real.log n) +
      riemannAutocorr (0 - Real.log n)) ≤ 0 := fun n =>
    mul_nonpos_of_nonpos_of_nonneg (hnp n) (add_nonneg
      (RHTower.WeilExcess.riemannAutocorr_nonneg _) (RHTower.WeilExcess.riemannAutocorr_nonneg _))
  have hle : nullPotential u 0 ≤ 0 := tsum_nonpos hterm
  have hge : 0 ≤ nullPotential u 0 := by
    have h := hPD.norm_le 0
    rw [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re] at h
    exact le_trans (abs_nonneg _) h
  have h0 : nullPotential u 0 = 0 := le_antisymm hle hge
  unfold nullPotential at h0
  have hsum0 : HasSum (fun n : ℕ => -(u n * (riemannAutocorr (0 + Real.log n) +
      riemannAutocorr (0 - Real.log n)))) 0 := by
    have h := hs.hasSum.neg
    rwa [h0, neg_zero] at h
  have hall := (hasSum_zero_iff_of_nonneg fun n => neg_nonneg.mpr (hterm n)).mp hsum0
  funext n
  have hn := neg_eq_zero.mp (congrFun hall n)
  have hK : 0 < riemannAutocorr (0 + Real.log n) + riemannAutocorr (0 - Real.log n) :=
    add_pos (RHTower.WeilExcess.riemannAutocorr_pos _) (RHTower.WeilExcess.riemannAutocorr_pos _)
  exact (mul_eq_zero.mp hn).resolve_right hK.ne'

end RHTower.WeilAbscissa
