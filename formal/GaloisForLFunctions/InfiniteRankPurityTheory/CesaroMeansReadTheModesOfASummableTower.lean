import Mathlib
import GaloisForLFunctions.HTGeometry.DirichletSimultaneousApproximation

/-!
# Cesàro means read the modes of a summable tower

A **summable tower** is a family of modes `z_i` in the closed unit disc with weights `c_i`,
`Σ ‖c_i‖ < ∞`; its level sums are `S(ν) = Σ_i c_i z_i^ν`. The rank is arbitrary. Two tools replace
the finite-rank Vandermonde determinant.

* **Cesàro means** (`tendsto_cesaro_towerSum`). For `‖w‖ = 1`,
  `(1/N) Σ_{ν<N} S(ν) w^{−ν} → Σ_{z_i = w} c_i`, the total weight at the point `w`: the mean of a
  geometric sequence of ratio `r ≠ 1`, `‖r‖ ≤ 1`, is `O(1/N)`, and the weights dominate. Hence level
  sums tending to zero carry no weight on the unit circle (`merged_eq_zero_of_tendsto_zero`).
* **Almost periods** (`exists_almostPeriod`). If all modes are unimodular, then for every `ε > 0`
  there are arbitrarily large `τ` with `‖S(ν + τ) − S(ν)‖ ≤ ε` for all `ν`: Dirichlet's simultaneous
  approximation on finitely many modes, the tail paid in weight.
-/

open Filter Topology Finset

namespace GaloisForLFunctions.InfiniteRankPurityTheory

variable {ι : Type*}

/-- The level sum `S(ν) = Σ_i c_i z_i^ν` of the tower with modes `z` and weights `c`. -/
noncomputable def towerSum (c z : ι → ℂ) (ν : ℕ) : ℂ := ∑' i, c i * z i ^ ν

theorem norm_towerTerm_le {c z : ι → ℂ} (hz : ∀ i, ‖z i‖ ≤ 1) (ν : ℕ) (i : ι) :
    ‖c i * z i ^ ν‖ ≤ ‖c i‖ := by
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hz i))

theorem summable_towerTerm {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖) (hz : ∀ i, ‖z i‖ ≤ 1)
    (ν : ℕ) : Summable fun i => c i * z i ^ ν :=
  Summable.of_norm_bounded hc (norm_towerTerm_le hz ν)

theorem norm_towerSum_le {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖) (hz : ∀ i, ‖z i‖ ≤ 1)
    (ν : ℕ) : ‖towerSum c z ν‖ ≤ ∑' i, ‖c i‖ :=
  tsum_of_norm_bounded hc.hasSum (norm_towerTerm_le hz ν)

/-! ### Means of geometric sequences -/

theorem norm_geomMean_le_one {r : ℂ} (hr : ‖r‖ ≤ 1) (N : ℕ) :
    ‖(∑ ν ∈ range N, r ^ ν) / (N : ℂ)‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    rw [norm_div, Complex.norm_natCast, div_le_one hNpos]
    calc ‖∑ ν ∈ range N, r ^ ν‖ ≤ ∑ ν ∈ range N, ‖r ^ ν‖ := norm_sum_le _ _
      _ ≤ ∑ _ν ∈ range N, (1 : ℝ) := by
          refine Finset.sum_le_sum fun ν _ => ?_
          rw [norm_pow]
          exact pow_le_one₀ (norm_nonneg _) hr
      _ = N := by simp

theorem tendsto_geomMean_zero {r : ℂ} (hr : ‖r‖ ≤ 1) (hr1 : r ≠ 1) :
    Tendsto (fun N : ℕ => (∑ ν ∈ range N, r ^ ν) / (N : ℂ)) atTop (𝓝 0) := by
  have hne : 0 < ‖r - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hr1)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound : ∀ N : ℕ, ‖(∑ ν ∈ range N, r ^ ν) / (N : ℂ)‖ ≤ (2 / ‖r - 1‖) / N := by
    intro N
    rw [geom_sum_eq hr1, norm_div, norm_div, Complex.norm_natCast]
    have h2 : ‖r ^ N - 1‖ ≤ 2 := by
      calc ‖r ^ N - 1‖ ≤ ‖r ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by
            rw [norm_pow, norm_one]
            exact add_le_add (pow_le_one₀ (norm_nonneg _) hr) le_rfl
        _ = 2 := by norm_num
    gcongr
  refine squeeze_zero (fun _ => norm_nonneg _) hbound ?_
  exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

theorem tendsto_geomMean_one :
    Tendsto (fun N : ℕ => (∑ ν ∈ range N, (1 : ℂ) ^ ν) / (N : ℂ)) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hN)
  simp [div_self hN0]

/-! ### Cesàro means -/

/-- **Cesàro means read the weight at a point of the circle.** -/
theorem tendsto_cesaro_towerSum {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hz : ∀ i, ‖z i‖ ≤ 1) {w : ℂ} (hw : ‖w‖ = 1) :
    Tendsto (fun N : ℕ => (∑ ν ∈ range N, towerSum c z ν * w⁻¹ ^ ν) / (N : ℂ)) atTop
      (𝓝 (∑' i, if z i = w then c i else 0)) := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    exact zero_ne_one hw
  have hzw : ∀ i, ‖z i * w⁻¹‖ ≤ 1 := by
    intro i
    rw [norm_mul, norm_inv, hw, inv_one, mul_one]
    exact hz i
  have hterm : ∀ N : ℕ, (∑ ν ∈ range N, towerSum c z ν * w⁻¹ ^ ν) / (N : ℂ) =
      ∑' i, c i * ((∑ ν ∈ range N, (z i * w⁻¹) ^ ν) / (N : ℂ)) := by
    intro N
    have h1 : ∀ ν ∈ range N, towerSum c z ν * w⁻¹ ^ ν = ∑' i, c i * (z i * w⁻¹) ^ ν := by
      intro ν _
      rw [towerSum, ← tsum_mul_right]
      refine tsum_congr fun i => ?_
      rw [mul_pow]
      ring
    rw [Finset.sum_congr rfl h1, ← Summable.tsum_finsetSum
      (fun ν _ => summable_towerTerm hc hzw ν), ← tsum_div_const]
    refine tsum_congr fun i => ?_
    rw [← Finset.mul_sum, mul_div_assoc]
  refine Tendsto.congr (fun N => (hterm N).symm) ?_
  refine tendsto_tsum_of_dominated_convergence (bound := fun i => ‖c i‖) hc ?_ ?_
  · intro i
    by_cases h : z i = w
    · have h1 : z i * w⁻¹ = 1 := by rw [h, mul_inv_cancel₀ hw0]
      simp only [h, if_true]
      rw [mul_inv_cancel₀ hw0]
      simpa using tendsto_geomMean_one.const_mul (c i)
    · have hr1 : z i * w⁻¹ ≠ 1 := by
        intro h1
        apply h
        calc z i = z i * w⁻¹ * w := by rw [mul_assoc, inv_mul_cancel₀ hw0, mul_one]
          _ = w := by rw [h1, one_mul]
      simp only [h, if_false]
      simpa using (tendsto_geomMean_zero (hzw i) hr1).const_mul (c i)
  · refine Eventually.of_forall fun N i => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_geomMean_le_one (hzw i) N)

/-- **Level sums tending to zero carry no weight on the unit circle.** -/
theorem merged_eq_zero_of_tendsto_zero {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hz : ∀ i, ‖z i‖ ≤ 1) (h0 : Tendsto (towerSum c z) atTop (𝓝 0)) {w : ℂ} (hw : ‖w‖ = 1) :
    (∑' i, if z i = w then c i else 0) = 0 := by
  have h1 : Tendsto (fun ν : ℕ => towerSum c z ν * w⁻¹ ^ ν) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero] at h0 ⊢
    refine h0.congr fun ν => ?_
    rw [norm_mul, norm_pow, norm_inv, hw, inv_one, one_pow, mul_one]
  have h2 := h1.cesaro_smul
  have h3 : (fun n : ℕ => ((n : ℝ)⁻¹ : ℝ) • ∑ i ∈ range n, towerSum c z i * w⁻¹ ^ i) =
      fun N : ℕ => (∑ ν ∈ range N, towerSum c z ν * w⁻¹ ^ ν) / (N : ℂ) := by
    funext n
    rw [Complex.real_smul, div_eq_inv_mul]
    push_cast
    rfl
  rw [h3] at h2
  exact tendsto_nhds_unique (tendsto_cesaro_towerSum hc hz hw) h2

/-! ### Almost periods -/

/-- A unimodular number whose angle, multiplied by `τ`, is within `η` of an integer number of turns
has `τ`-th power within `2πη` of `1`. -/
theorem norm_pow_sub_one_le_of_angle {z : ℂ} (hz : ‖z‖ = 1) {τ : ℕ} {m : ℤ} {η : ℝ}
    (h : |(τ : ℝ) * (z.arg / (2 * Real.pi)) - m| ≤ η) : ‖z ^ τ - 1‖ ≤ 2 * Real.pi * η := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hzexp : z = Complex.exp (z.arg * Complex.I) := by
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hz, Complex.ofReal_one, one_mul] at this
    exact this.symm
  set x : ℝ := 2 * Real.pi * ((τ : ℝ) * (z.arg / (2 * Real.pi)) - m) with hx
  have hpow : z ^ τ = Complex.exp (Complex.I * x) := by
    have hm : Complex.exp ((m : ℂ) * (2 * Real.pi * Complex.I)) = 1 :=
      Complex.exp_int_mul_two_pi_mul_I m
    have e : (τ : ℂ) * (z.arg * Complex.I) =
        Complex.I * x + (m : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [hx]
      push_cast
      field_simp
      ring
    conv_lhs => rw [hzexp]
    rw [← Complex.exp_nat_mul, e, Complex.exp_add, hm, mul_one]
  rw [hpow]
  calc ‖Complex.exp (Complex.I * x) - 1‖ ≤ ‖x‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * |(τ : ℝ) * (z.arg / (2 * Real.pi)) - m| := by
        rw [hx, Real.norm_eq_abs, abs_mul, abs_of_pos hpi]
    _ ≤ 2 * Real.pi * η := by gcongr

/-- Finitely many unimodular numbers have arbitrarily large common almost periods. -/
theorem exists_common_return (F : Finset ι) {z : ι → ℂ} (hz : ∀ i, ‖z i‖ = 1) {δ : ℝ}
    (hδ : 0 < δ) (T : ℕ) :
    ∃ τ : ℕ, T ≤ τ ∧ 1 ≤ τ ∧ ∀ i ∈ F, ‖z i ^ τ - 1‖ ≤ δ := by
  classical
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set T' : ℕ := max T 1 with hT'
  have hT'1 : 1 ≤ T' := le_max_right _ _
  have hT'pos : (0 : ℝ) < T' := by exact_mod_cast hT'1
  set Q : ℕ := ⌈2 * Real.pi * T' / δ⌉₊ + 1 with hQ
  have hQ1 : 1 ≤ Q := by omega
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ1
  have hQbig : 2 * Real.pi * T' / δ ≤ Q := by
    have := Nat.le_ceil (2 * Real.pi * T' / δ)
    rw [hQ]
    push_cast
    linarith
  obtain ⟨k, hk1, -, hk⟩ := GaloisForLFunctions.HTGeometry.exists_dirichlet_simultaneous
    (fun i : F => (z i).arg / (2 * Real.pi)) Q hQ1
  refine ⟨T' * k, ?_, ?_, fun i hi => ?_⟩
  · calc T ≤ T' := le_max_left _ _
      _ = T' * 1 := (mul_one _).symm
      _ ≤ T' * k := Nat.mul_le_mul_left _ hk1
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · obtain ⟨m, hm⟩ := hk ⟨i, hi⟩
    have hang : |((T' * k : ℕ) : ℝ) * ((z i).arg / (2 * Real.pi)) - ((T' : ℤ) * m : ℤ)| ≤
        T' / Q := by
      have e : ((T' * k : ℕ) : ℝ) * ((z i).arg / (2 * Real.pi)) - ((T' : ℤ) * m : ℤ) =
          T' * ((k : ℝ) * ((z i).arg / (2 * Real.pi)) - m) := by
        push_cast
        ring
      rw [e, abs_mul, abs_of_pos hT'pos]
      calc (T' : ℝ) * |(k : ℝ) * ((z i).arg / (2 * Real.pi)) - m| ≤ T' * (1 / Q) := by
            exact mul_le_mul_of_nonneg_left hm.le hT'pos.le
        _ = T' / Q := by ring
    have h1 := norm_pow_sub_one_le_of_angle (hz i) hang
    have h2 : 2 * Real.pi * ((T' : ℝ) / Q) ≤ δ := by
      rw [div_le_iff₀ hδ] at hQbig
      rw [← mul_div_assoc, div_le_iff₀ hQpos]
      linarith
    exact h1.trans h2

/-- **Almost periods.** A summable tower with unimodular modes has, for every `ε > 0`, arbitrarily
large `τ` with `‖S(ν + τ) − S(ν)‖ ≤ ε` at every level `ν`. -/
theorem exists_almostPeriod {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hz : ∀ i, ‖z i‖ = 1) {ε : ℝ} (hε : 0 < ε) (T : ℕ) :
    ∃ τ : ℕ, T ≤ τ ∧ 1 ≤ τ ∧ ∀ ν : ℕ, ‖towerSum c z (ν + τ) - towerSum c z ν‖ ≤ ε := by
  classical
  have hzle : ∀ i, ‖z i‖ ≤ 1 := fun i => (hz i).le
  set C : ℝ := ∑' i, ‖c i‖ with hC
  have hC0 : 0 ≤ C := tsum_nonneg fun _ => norm_nonneg _
  -- a finite set carrying all but `ε/4` of the weight
  obtain ⟨F, hF⟩ : ∃ F : Finset ι, ∑' i : {i // i ∉ F}, ‖c i‖ < ε / 4 :=
    ((tendsto_order.1 (tendsto_tsum_compl_atTop_zero fun i => ‖c i‖)).2 _
      (by positivity)).exists
  set δ : ℝ := ε / (2 * (C + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨τ, hτT, hτ1, hτ⟩ := exists_common_return F hz hδpos T
  refine ⟨τ, hτT, hτ1, fun ν => ?_⟩
  -- the difference as one series
  have hdiff : towerSum c z (ν + τ) - towerSum c z ν = ∑' i, c i * z i ^ ν * (z i ^ τ - 1) := by
    rw [towerSum, towerSum, ← (summable_towerTerm hc hzle _).tsum_sub
      (summable_towerTerm hc hzle _)]
    refine tsum_congr fun i => ?_
    rw [pow_add]
    ring
  have hterm : ∀ i, ‖c i * z i ^ ν * (z i ^ τ - 1)‖ = ‖c i‖ * ‖z i ^ τ - 1‖ := by
    intro i
    rw [norm_mul, norm_mul, norm_pow, hz i, one_pow, mul_one]
  have hle2 : ∀ i, ‖z i ^ τ - 1‖ ≤ 2 := by
    intro i
    calc ‖z i ^ τ - 1‖ ≤ ‖z i ^ τ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz i, one_pow, norm_one]; norm_num
  have hsum : Summable fun i => ‖c i‖ * ‖z i ^ τ - 1‖ :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun i => mul_le_mul_of_nonneg_left (hle2 i) (norm_nonneg _)) (hc.mul_right 2)
  rw [hdiff]
  calc ‖∑' i, c i * z i ^ ν * (z i ^ τ - 1)‖ ≤ ∑' i, ‖c i‖ * ‖z i ^ τ - 1‖ := by
        refine tsum_of_norm_bounded hsum.hasSum fun i => ?_
        rw [hterm i]
    _ = ∑ i ∈ F, ‖c i‖ * ‖z i ^ τ - 1‖ + ∑' i : {i // i ∉ F}, ‖c i‖ * ‖z i ^ τ - 1‖ :=
        (hsum.sum_add_tsum_subtype_compl F).symm
    _ ≤ δ * C + 2 * (ε / 4) := by
        apply add_le_add
        · calc ∑ i ∈ F, ‖c i‖ * ‖z i ^ τ - 1‖ ≤ ∑ i ∈ F, ‖c i‖ * δ :=
                Finset.sum_le_sum fun i hi =>
                  mul_le_mul_of_nonneg_left (hτ i hi) (norm_nonneg _)
            _ = δ * ∑ i ∈ F, ‖c i‖ := by rw [← Finset.sum_mul, mul_comm]
            _ ≤ δ * C :=
                mul_le_mul_of_nonneg_left
                  (hc.sum_le_tsum F fun i _ => norm_nonneg _) hδpos.le
        · calc ∑' i : {i // i ∉ F}, ‖c i‖ * ‖z i ^ τ - 1‖
                ≤ ∑' i : {i // i ∉ F}, ‖c i‖ * 2 := by
                  refine (hsum.subtype _).tsum_le_tsum (fun i => ?_) ((hc.mul_right 2).subtype _)
                  exact mul_le_mul_of_nonneg_left (hle2 i) (norm_nonneg _)
            _ = 2 * ∑' i : {i // i ∉ F}, ‖c i‖ := by rw [tsum_mul_right, mul_comm]
            _ ≤ 2 * (ε / 4) := by linarith [hF.le]
    _ ≤ ε := by
        have h1 : δ * C ≤ ε / 2 := by
          rw [hδ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        linarith

end GaloisForLFunctions.InfiniteRankPurityTheory
