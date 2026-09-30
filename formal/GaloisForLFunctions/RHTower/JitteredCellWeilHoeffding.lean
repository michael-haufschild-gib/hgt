import GaloisForLFunctions.RHTower.JitteredCellWeilTerms

/-!
# Independent uniform atoms: Hoeffding bounds for sums of cell terms

The positions `u k ∈ [0, 1]` of the atoms in the cells are independent and uniform: `cellLaw` is
the infinite product of the uniform law on `[0, 1]`.  Under `cellLaw` the cell terms
`u ↦ cellTerm N k (u k) t` are independent (`iIndepFun_cellTerm`), have mean zero
(`integral_cellTerm_coord`, from `integral_cellTerm_eq_zero`), and are bounded by any `r` that bounds
`|cellTerm N k v t|` on `v ∈ [0, 1]`.  Hoeffding's lemma makes each of them sub-Gaussian with
parameter `r²`, and Hoeffding's inequality bounds the upper tail of a finite sum
(`measureReal_sum_cellTerm_ge_le`):

`P(ε ≤ Σ_{k<K} cellTerm N k (u k) t) ≤ exp(−ε²/(2 Σ_{k<K} r_k²))`.

The variance proxy is estimated in `sum_osc_sq_le` (cells up to `K₀`, bound `2/(N√a)`) through
`Σ_{k<L} 1/(N+k) ≤ log((N+L−1)/(N−1))`, and in `sum_Ico_invPow_sq_le` (the remaining cells,
bound `invPow`).
-/

open MeasureTheory ProbabilityTheory Set Real

noncomputable section

namespace RHTower
namespace RandomCellWeil

/-- The uniform law on `[0, 1]`. -/
abbrev unitLaw : Measure ℝ := (volume : Measure ℝ).restrict (Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure unitLaw := ⟨by simp [unitLaw, Real.volume_Icc]⟩

/-- Independent uniform positions, one in each cell. -/
def cellLaw : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => unitLaw)

instance : IsProbabilityMeasure cellLaw := by
  unfold cellLaw
  infer_instance

theorem map_eval_cellLaw (k : ℕ) : Measure.map (fun u : ℕ → ℝ => u k) cellLaw = unitLaw :=
  Measure.infinitePi_map_eval (fun _ : ℕ => unitLaw) k

theorem iIndepFun_cellTerm (N : ℕ) (t : ℝ) :
    iIndepFun (fun k (u : ℕ → ℝ) => cellTerm N k (u k) t) cellLaw :=
  iIndepFun_infinitePi (P := fun _ : ℕ => unitLaw) (X := fun k v => cellTerm N k v t)
    (fun k => measurable_cellTerm k t)

theorem ae_mem_Icc_cellLaw (k : ℕ) : ∀ᵐ u ∂cellLaw, u k ∈ Icc (0 : ℝ) 1 := by
  have h1 : ∀ᵐ v ∂unitLaw, v ∈ Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
  rw [← map_eval_cellLaw k] at h1
  exact ae_of_ae_map (measurable_pi_apply k).aemeasurable h1

theorem measure_not_mem_Icc (k : ℕ) : cellLaw {u : ℕ → ℝ | u k ∉ Icc (0 : ℝ) 1} = 0 := by
  have h := ae_mem_Icc_cellLaw k
  rw [ae_iff] at h
  simpa using h

theorem measure_exists_not_mem_Icc :
    cellLaw {u : ℕ → ℝ | ∃ k, u k ∉ Icc (0 : ℝ) 1} = 0 := by
  have : {u : ℕ → ℝ | ∃ k, u k ∉ Icc (0 : ℝ) 1} = ⋃ k, {u : ℕ → ℝ | u k ∉ Icc (0 : ℝ) 1} := by
    ext u; simp
  rw [this]
  exact measure_iUnion_null (fun k => measure_not_mem_Icc k)

theorem integral_cellTerm_coord {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (t : ℝ) :
    ∫ u, cellTerm N k (u k) t ∂cellLaw = 0 := by
  have hm : AEStronglyMeasurable (fun v => cellTerm N k v t)
      (Measure.map (fun u : ℕ → ℝ => u k) cellLaw) :=
    (measurable_cellTerm k t).aestronglyMeasurable
  have h := integral_map (μ := cellLaw) (φ := fun u : ℕ → ℝ => u k)
    (measurable_pi_apply k).aemeasurable hm
  rw [← h, map_eval_cellLaw k, unitLaw, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]
  exact integral_cellTerm_eq_zero hN k t

/-- Hoeffding's lemma for one cell term: a bound `r` on `[0, 1]` gives sub-Gaussian parameter `r²`. -/
theorem hasSubgaussianMGF_cellTerm {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (t : ℝ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : ∀ v ∈ Icc (0 : ℝ) 1, |cellTerm N k v t| ≤ r) :
    HasSubgaussianMGF (fun u : ℕ → ℝ => cellTerm N k (u k) t) (r ^ 2).toNNReal cellLaw := by
  have hmem : ∀ᵐ u ∂cellLaw, cellTerm N k (u k) t ∈ Icc (-r) r := by
    filter_upwards [ae_mem_Icc_cellLaw k] with u hu
    exact abs_le.mp (hr (u k) hu)
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    ((measurable_cellTerm k t).comp (measurable_pi_apply k)).aemeasurable hmem
    (integral_cellTerm_coord hN k t)
  have hpar : ((‖r - -r‖₊ / 2) ^ 2 : NNReal) = (r ^ 2).toNNReal := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (sq_nonneg r)]
    push_cast
    rw [Real.norm_eq_abs, show r - -r = 2 * r by ring, abs_mul, abs_two, abs_of_nonneg hr0]
    ring
  rwa [hpar] at h

/-- **Hoeffding's inequality for cell sums.** -/
theorem measureReal_sum_cellTerm_ge_le {N : ℕ} (hN : 1 ≤ N) (t : ℝ) (K : ℕ) (r : ℕ → ℝ)
    (hr0 : ∀ k, 0 ≤ r k) (hr : ∀ k ∈ Finset.range K, ∀ v ∈ Icc (0 : ℝ) 1, |cellTerm N k v t| ≤ r k)
    {ε : ℝ} (hε : 0 ≤ ε) :
    cellLaw.real {u | ε ≤ ∑ k ∈ Finset.range K, cellTerm N k (u k) t}
      ≤ Real.exp (-ε ^ 2 / (2 * ∑ k ∈ Finset.range K, r k ^ 2)) := by
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (iIndepFun_cellTerm N t)
    (c := fun k => (r k ^ 2).toNNReal) (s := Finset.range K)
    (fun k hk => hasSubgaussianMGF_cellTerm hN k t (hr0 k) (hr k hk)) hε
  have hsum : ((∑ k ∈ Finset.range K, (r k ^ 2).toNNReal : NNReal) : ℝ)
      = ∑ k ∈ Finset.range K, r k ^ 2 := by
    push_cast
    exact Finset.sum_congr rfl (fun k _ => Real.coe_toNNReal _ (sq_nonneg _))
  rwa [hsum] at h

/-- `Σ_{k<L} 1/(M+k) ≤ log((M+L−1)/(M−1))` for `M ≥ 2`. -/
theorem sum_range_inv_le_log (M : ℕ) (hM : 2 ≤ M) (L : ℕ) :
    ∑ k ∈ Finset.range L, (1 : ℝ) / ((M + k : ℕ) : ℝ)
      ≤ Real.log ((((M + L : ℕ) : ℝ) - 1) / ((M : ℝ) - 1)) := by
  have hM1 : (1 : ℝ) < M := by exact_mod_cast (show 1 < M by omega)
  induction L with
  | zero => simp [div_self (show (M : ℝ) - 1 ≠ 0 by linarith)]
  | succ L ih =>
    rw [Finset.sum_range_succ]
    have hpos : (0 : ℝ) < ((M + L : ℕ) : ℝ) - 1 := by
      have : (1 : ℝ) < ((M + L : ℕ) : ℝ) := by exact_mod_cast (show 1 < M + L by omega)
      linarith
    have hm : (0 : ℝ) < ((M + L : ℕ) : ℝ) := by linarith
    have hstep : (1 : ℝ) / ((M + L : ℕ) : ℝ)
        ≤ Real.log (((M + L : ℕ) : ℝ) / (((M + L : ℕ) : ℝ) - 1)) := by
      have h := Real.one_sub_inv_le_log_of_pos (x := ((M + L : ℕ) : ℝ) / (((M + L : ℕ) : ℝ) - 1))
        (by positivity)
      have : 1 - ((((M + L : ℕ) : ℝ) / (((M + L : ℕ) : ℝ) - 1)))⁻¹ = 1 / ((M + L : ℕ) : ℝ) := by
        field_simp
        ring
      linarith
    have e : ((M + (L + 1) : ℕ) : ℝ) - 1 = ((M + L : ℕ) : ℝ) := by push_cast; ring
    rw [e]
    have hsplit : Real.log (((M + L : ℕ) : ℝ) / ((M : ℝ) - 1))
        = Real.log ((((M + L : ℕ) : ℝ) - 1) / ((M : ℝ) - 1))
          + Real.log (((M + L : ℕ) : ℝ) / (((M + L : ℕ) : ℝ) - 1)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    rw [hsplit]
    linarith

/-- The oscillatory part of the variance proxy:
`Σ_{k<L} (2/(N√a_k))² ≤ (4/N) log((N+L−1)/(N−1))`. -/
theorem sum_osc_sq_le {N : ℕ} (hN : 2 ≤ N) (L : ℕ) :
    ∑ k ∈ Finset.range L, (2 * (N : ℝ)⁻¹ / Real.sqrt (cellLeft N k)) ^ 2
      ≤ 4 * (N : ℝ)⁻¹ * Real.log ((((N + L : ℕ) : ℝ) - 1) / ((N : ℝ) - 1)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hterm : ∀ k ∈ Finset.range L, (2 * (N : ℝ)⁻¹ / Real.sqrt (cellLeft N k)) ^ 2
      = 4 * (N : ℝ)⁻¹ * ((1 : ℝ) / ((N + k : ℕ) : ℝ)) := by
    intro k _
    have ha := cellLeft_pos (N := N) (by omega) k
    rw [div_pow, Real.sq_sqrt ha.le, cellLeft]
    have hm : (0 : ℝ) < ((N + k : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((N + k : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ N + k by omega)
      linarith
    field_simp
    norm_num
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_range_inv_le_log N hN L) (by positivity)

/-- The smooth part of the variance proxy: for `K₀ ≤ k < K`,
`Σ invPow(N+k)² ≤ invPow(N+K₀) · 2/√(N+K₀−1)`. -/
theorem sum_Ico_invPow_sq_le (M : ℕ) (hM : 2 ≤ M) (L : ℕ) :
    ∑ k ∈ Finset.range L, invPow ((M + k : ℕ) : ℝ) ^ 2
      ≤ invPow (M : ℝ) * (2 / Real.sqrt ((M : ℝ) - 1)) := by
  have hmono : ∀ k : ℕ, invPow ((M + k : ℕ) : ℝ) ≤ invPow (M : ℝ) := by
    intro k
    unfold invPow
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    apply one_div_le_one_div_of_le (mul_pos hM0 (Real.sqrt_pos.mpr hM0))
    have hle : (M : ℝ) ≤ ((M + k : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right M k
    exact mul_le_mul hle (Real.sqrt_le_sqrt hle) (Real.sqrt_nonneg _) (by linarith)
  have hsq : ∀ k ∈ Finset.range L, invPow ((M + k : ℕ) : ℝ) ^ 2
      ≤ invPow (M : ℝ) * invPow ((M + k : ℕ) : ℝ) := by
    intro k _
    rw [sq]
    exact mul_le_mul_of_nonneg_right (hmono k) (invPow_nonneg (by positivity))
  refine (Finset.sum_le_sum hsq).trans ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (invPow_nonneg (by positivity))
  refine (sum_range_invPow_le M hM L).trans ?_
  have : 0 ≤ 2 / Real.sqrt (((M + L : ℕ) : ℝ) - 1) := by positivity
  linarith

end RandomCellWeil
end RHTower
