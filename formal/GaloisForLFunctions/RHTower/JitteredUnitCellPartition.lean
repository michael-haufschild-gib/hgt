import GaloisForLFunctions.RHTower.JitteredUnitCellLaplace

/-!
# Unit cells: partition functions at a dyadic height

Fix a height scale `T` and the integer net `t_i = T + i`, `i < T`, of `[T, 2T)`.  With the field
`f_i = field (64T²) u t_i` of `64T²` unit cells, the partition function is
`W_λ(u) = Σ_{i<T} e^{λ f_i(u)}`.

* `unitSum`: the full cell sum `Σ_k Y_k(u_k, t)`, equal to `cellSum 1 u t`; the truncation error
  is at most `(|t| + 1/2)·2/√K` (`abs_unitSum_sub_field_le`).
* `integral_W`, `integral_W_sq`: `E W_λ = Σ_i E e^{λ f_i}` and `E W_λ² = Σ_{i,i'} E e^{λ(f_i+f_{i'})}`.
* `integral_W_sq_le`: for `λ = 6/5` the off-diagonal pairs are bounded by `e^{54λ²+330} (E W)²`
  (bounded covariance at separation `≥ 1`), and the diagonal by
  `T^{λ²/2 − 1} e^{29λ² + 330} (E W)²`, which is `≤ (E W)²` for `T` large since `λ² < 2`.
* `measure_ge_half_integral_ge`: Paley–Zygmund `P(W ≥ E W/2) ≥ (E W)²/(4 E W²)`, proved from the
  pointwise bound `W ≤ E W/2 + (W²/(2a) + a/2) 1_{W ≥ E W/2}`.
-/

open Real MeasureTheory ProbabilityTheory Set Filter

noncomputable section

namespace RHTower
namespace RandomCellWeil

/-! ### The full unit-cell sum -/

/-- The full unit-cell sum `Σ_k Y_k(u_k, t)`. -/
def unitSum (u : ℕ → ℝ) (t : ℝ) : ℝ := ∑' k, unitTerm k (u k) t

theorem unitSum_eq_cellSum (u : ℕ → ℝ) (t : ℝ) : unitSum u t = cellSum 1 u t := by
  unfold unitSum cellSum
  exact tsum_congr (fun k => unitTerm_eq_cellTerm k (u k) t)

theorem summable_invPow_succ : Summable (fun k : ℕ => invPow ((k : ℝ) + 1)) := by
  have h := summable_invPow 2 le_rfl
  have e : (fun k : ℕ => invPow (((2 + k : ℕ) : ℝ))) = fun k : ℕ => invPow (((k + 1 : ℕ) : ℝ) + 1) := by
    funext k; congr 1; push_cast; ring
  rw [e] at h
  exact (summable_nat_add_iff 1 (f := fun k : ℕ => invPow ((k : ℝ) + 1))).mp (by simpa using h)

theorem summable_unitTerm {u : ℕ → ℝ} (hu : ∀ k, u k ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    Summable (fun k => unitTerm k (u k) t) := by
  apply Summable.of_norm_bounded (summable_invPow_succ.mul_left (|t| + 1 / 2))
  intro k
  rw [Real.norm_eq_abs]
  exact abs_unitTerm_le_smooth k (hu k) t

/-- Truncation error: `|unitSum − field K| ≤ (|t| + 1/2)·2/√K` for `K ≥ 1`. -/
theorem abs_unitSum_sub_field_le {u : ℕ → ℝ} (hu : ∀ k, u k ∈ Icc (0 : ℝ) 1) (t : ℝ) {K : ℕ}
    (hK : 1 ≤ K) :
    |unitSum u t - field K u t| ≤ (|t| + 1 / 2) * (2 / Real.sqrt K) := by
  have hs := summable_unitTerm hu t
  have hsplit := hs.sum_add_tsum_nat_add K
  have hdiff : unitSum u t - field K u t = ∑' i : ℕ, unitTerm (i + K) (u (i + K)) t := by
    unfold unitSum field
    rw [← hsplit]
    ring
  rw [hdiff]
  have hbd : ∀ i : ℕ, ‖unitTerm (i + K) (u (i + K)) t‖
      ≤ (|t| + 1 / 2) * invPow (((K + 1) + i : ℕ) : ℝ) := by
    intro i
    rw [Real.norm_eq_abs]
    have h := abs_unitTerm_le_smooth (i + K) (hu (i + K)) t
    have e : ((i + K : ℕ) : ℝ) + 1 = (((K + 1) + i : ℕ) : ℝ) := by push_cast; ring
    rwa [e] at h
  have hsum2 : Summable (fun i : ℕ => (|t| + 1 / 2) * invPow (((K + 1) + i : ℕ) : ℝ)) :=
    (summable_invPow (K + 1) (by omega)).mul_left _
  have hnorm : Summable (fun i : ℕ => ‖unitTerm (i + K) (u (i + K)) t‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbd hsum2
  have htsum := tsum_invPow_le (K + 1) (by omega)
  have e2 : ((K + 1 : ℕ) : ℝ) - 1 = (K : ℝ) := by push_cast; ring
  rw [e2] at htsum
  calc |∑' i : ℕ, unitTerm (i + K) (u (i + K)) t|
      ≤ ∑' i : ℕ, ‖unitTerm (i + K) (u (i + K)) t‖ := by
        rw [← Real.norm_eq_abs]; exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' i : ℕ, (|t| + 1 / 2) * invPow (((K + 1) + i : ℕ) : ℝ) := hnorm.tsum_le_tsum hbd hsum2
    _ = (|t| + 1 / 2) * ∑' i : ℕ, invPow (((K + 1) + i : ℕ) : ℝ) := tsum_mul_left
    _ ≤ (|t| + 1 / 2) * (2 / Real.sqrt K) := mul_le_mul_of_nonneg_left htsum (by positivity)

/-! ### Boundedness and integrability -/

theorem ae_forall_mem_Icc : ∀ᵐ u ∂cellLaw, ∀ k, u k ∈ Icc (0 : ℝ) 1 :=
  ae_all_iff.mpr ae_mem_Icc_cellLaw

theorem abs_field_le {u : ℕ → ℝ} (hu : ∀ k, u k ∈ Icc (0 : ℝ) 1) (K : ℕ) (t : ℝ) :
    |field K u t| ≤ 2 * K := by
  unfold field
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ Finset.range K, |unitTerm k (u k) t| ≤ ∑ _k ∈ Finset.range K, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        refine (abs_unitTerm_le_osc k (hu k) t).trans ?_
        rw [div_le_iff₀ (Real.sqrt_pos.mpr (by positivity))]
        have : (1 : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) := by
          rw [Real.le_sqrt (by norm_num) (by positivity)]
          have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          linarith
        linarith
    _ = 2 * K := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem integrable_exp_field (K : ℕ) (t l : ℝ) :
    Integrable (fun u => Real.exp (l * field K u t)) cellLaw := by
  refine Integrable.of_bound (C := Real.exp (|l| * (2 * K)))
    ((Real.measurable_exp.comp (measurable_const.mul (measurable_field K t))).aestronglyMeasurable) ?_
  filter_upwards [ae_forall_mem_Icc] with u hu
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc l * field K u t ≤ |l * field K u t| := le_abs_self _
    _ = |l| * |field K u t| := abs_mul _ _
    _ ≤ |l| * (2 * K) := mul_le_mul_of_nonneg_left (abs_field_le hu K t) (abs_nonneg l)

theorem integrable_exp_field_pair (K : ℕ) (t t' l : ℝ) :
    Integrable (fun u => Real.exp (l * (field K u t + field K u t'))) cellLaw := by
  refine Integrable.of_bound (C := Real.exp (|l| * (4 * K)))
    ((Real.measurable_exp.comp (measurable_const.mul
      ((measurable_field K t).add (measurable_field K t')))).aestronglyMeasurable) ?_
  filter_upwards [ae_forall_mem_Icc] with u hu
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have h1 := abs_field_le hu K t
  have h2 := abs_field_le hu K t'
  calc l * (field K u t + field K u t') ≤ |l * (field K u t + field K u t')| := le_abs_self _
    _ = |l| * |field K u t + field K u t'| := abs_mul _ _
    _ ≤ |l| * (4 * K) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg l)
        calc |field K u t + field K u t'| ≤ |field K u t| + |field K u t'| := abs_add_le _ _
          _ ≤ 4 * K := by linarith

/-! ### Partition functions -/

/-- The block truncation length `64 T²`. -/
def blockLen (T : ℕ) : ℕ := 64 * T ^ 2

/-- The partition function `W_λ(u) = Σ_{i<T} e^{λ f(u, T+i)}` of the block `[T, 2T)`. -/
def partW (T : ℕ) (l : ℝ) (u : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range T, Real.exp (l * field (blockLen T) u ((T : ℝ) + i))

theorem partW_pos {T : ℕ} (hT : 1 ≤ T) (l : ℝ) (u : ℕ → ℝ) : 0 < partW T l u :=
  Finset.sum_pos (fun i _ => Real.exp_pos _) (Finset.nonempty_range_iff.mpr (by omega))

theorem measurable_partW (T : ℕ) (l : ℝ) : Measurable (partW T l) := by
  unfold partW
  exact Finset.measurable_sum _ (fun i _ =>
    Real.measurable_exp.comp (measurable_const.mul (measurable_field _ _)))

theorem integrable_partW (T : ℕ) (l : ℝ) : Integrable (partW T l) cellLaw := by
  unfold partW
  exact integrable_finsetSum _ (fun i _ => integrable_exp_field _ _ _)

theorem integral_partW (T : ℕ) (l : ℝ) :
    ∫ u, partW T l u ∂cellLaw
      = ∑ i ∈ Finset.range T, mgf (fun u => field (blockLen T) u ((T : ℝ) + i)) cellLaw l := by
  unfold partW mgf
  exact integral_finsetSum _ (fun i _ => integrable_exp_field _ _ _)

theorem partW_sq (T : ℕ) (l : ℝ) (u : ℕ → ℝ) :
    partW T l u ^ 2 = ∑ i ∈ Finset.range T, ∑ i' ∈ Finset.range T,
      Real.exp (l * (field (blockLen T) u ((T : ℝ) + i) + field (blockLen T) u ((T : ℝ) + i'))) := by
  unfold partW
  rw [sq, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro i' _
  rw [← Real.exp_add]
  ring_nf

theorem integrable_partW_sq (T : ℕ) (l : ℝ) : Integrable (fun u => partW T l u ^ 2) cellLaw := by
  simp_rw [partW_sq]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun i' _ => integrable_exp_field_pair _ _ _ _))

theorem integral_partW_sq (T : ℕ) (l : ℝ) :
    ∫ u, partW T l u ^ 2 ∂cellLaw
      = ∑ i ∈ Finset.range T, ∑ i' ∈ Finset.range T,
          mgf (fun u => field (blockLen T) u ((T : ℝ) + i) + field (blockLen T) u ((T : ℝ) + i'))
            cellLaw l := by
  simp_rw [partW_sq]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun i' _ => integrable_exp_field_pair _ _ _ _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun i' _ => integrable_exp_field_pair _ _ _ _)]
  rfl


/-! ### Variance window on a block -/

theorem cellCov_self (k : ℕ) (t : ℝ) : cellCov k t t = cellVar k t := by
  unfold cellCov cellVar
  congr 1
  funext v
  ring

theorem fieldCov_self (K : ℕ) (t : ℝ) : fieldCov K t t = fieldVar K t := by
  unfold fieldCov fieldVar
  exact Finset.sum_congr rfl (fun k _ => cellCov_self k t)

theorem blockLen_ge {T : ℕ} (hT : 16 ≤ T) : 2 * (T : ℝ) ≤ blockLen T ∧ 23 ≤ blockLen T := by
  unfold blockLen
  constructor
  · push_cast
    have : (16 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  · have : 16 * 16 ≤ T * T := Nat.mul_le_mul hT hT
    nlinarith

theorem netPoint_bounds {T i : ℕ} (hi : i < T) :
    (T : ℝ) ≤ (T : ℝ) + i ∧ (T : ℝ) + i ≤ 2 * T := by
  have : (i : ℝ) ≤ T := by exact_mod_cast hi.le
  constructor <;> [exact le_add_of_nonneg_right (Nat.cast_nonneg i); linarith]

theorem fieldVar_block_ge {T i : ℕ} (hT : 16 ≤ T) (hi : i < T) :
    (1 / 2) * Real.log T - 19 ≤ fieldVar (blockLen T) ((T : ℝ) + i) := by
  obtain ⟨h1, h2⟩ := netPoint_bounds hi
  have hT' : (16 : ℝ) ≤ T := by exact_mod_cast hT
  have hK := (blockLen_ge hT).1
  have h := fieldVar_ge (t := (T : ℝ) + i) (by linarith) (K := blockLen T) (by linarith)
  have hlog : Real.log T ≤ Real.log ((T : ℝ) + i) := Real.log_le_log (by linarith) h1
  linarith

theorem fieldVar_block_le {T i : ℕ} (hT : 16 ≤ T) (hi : i < T) :
    fieldVar (blockLen T) ((T : ℝ) + i) ≤ (1 / 2) * Real.log T + 5 := by
  obtain ⟨h1, h2⟩ := netPoint_bounds hi
  have hT' : (16 : ℝ) ≤ T := by exact_mod_cast hT
  have hK := (blockLen_ge hT).1
  have h := fieldVar_le (t := (T : ℝ) + i) (by linarith) (K := blockLen T) (by linarith)
  have hlog : Real.log ((T : ℝ) + i + 1) ≤ Real.log T + 2 := by
    have h3 : (T : ℝ) + i + 1 ≤ Real.exp 2 * T := by
      have he : (7 : ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp (2 : ℝ)
        have h2' : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        have he1 := Real.exp_one_gt_d9
        nlinarith
      nlinarith
    calc Real.log ((T : ℝ) + i + 1) ≤ Real.log (Real.exp 2 * T) :=
          Real.log_le_log (by linarith) h3
      _ = Real.log T + 2 := by
          rw [Real.log_mul (Real.exp_pos 2).ne' (by linarith), Real.log_exp]; ring
  linarith

/-- `mgf` from its logarithm. -/
theorem mgf_field_pos (K : ℕ) (t l : ℝ) : 0 < mgf (fun u => field K u t) cellLaw l := by
  rw [mgf_field]; exact prod_integral_exp_pos K t l

theorem mgf_field_pair_pos (K : ℕ) (t t' l : ℝ) :
    0 < mgf (fun u => field K u t + field K u t') cellLaw l := by
  rw [mgf_field_pair]
  exact Finset.prod_pos (fun k _ => lt_of_lt_of_le one_pos
    (integral_exp_ge_one (continuousOn_pairTerm k t t') (integral_pairTerm_eq_zero k t t') l))

theorem mgf_block_ge {T i : ℕ} (hT : 16 ≤ T) (hi : i < T) {l : ℝ} (hl : |l| ≤ 12 / 5) :
    Real.exp (l ^ 2 * ((1 / 2) * Real.log T - 19) / 2 - 100)
      ≤ mgf (fun u => field (blockLen T) u ((T : ℝ) + i)) cellLaw l := by
  have hpos := mgf_field_pos (blockLen T) ((T : ℝ) + i) l
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  have h := log_mgf_field_ge (blockLen_ge hT).2 ((T : ℝ) + i) hl
  have hv := fieldVar_block_ge hT hi
  have hl2 : 0 ≤ l ^ 2 := sq_nonneg l
  have := mul_le_mul_of_nonneg_left hv hl2
  linarith

theorem mgf_block_le {T i : ℕ} (hT : 16 ≤ T) (hi : i < T) {l : ℝ} (hl : |l| ≤ 12 / 5) :
    mgf (fun u => field (blockLen T) u ((T : ℝ) + i)) cellLaw l
      ≤ Real.exp (l ^ 2 * ((1 / 2) * Real.log T + 5) / 2 + 120) := by
  have hpos := mgf_field_pos (blockLen T) ((T : ℝ) + i) l
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  have h := log_mgf_field_le (blockLen_ge hT).2 ((T : ℝ) + i) hl
  have hv := fieldVar_block_le hT hi
  have hl2 : 0 ≤ l ^ 2 := sq_nonneg l
  have := mul_le_mul_of_nonneg_left hv hl2
  linarith

/-! ### The second moment -/

/-- The off-diagonal constant `e^{330 + 30·(6/5)²}`. -/
def pairConst : ℝ := Real.exp (330 + 30 * (6 / 5) ^ 2)

theorem pairConst_pos : 0 < pairConst := Real.exp_pos _

/-- Off-diagonal pairs: `E e^{λ(f_i + f_{i'})} ≤ C · E e^{λ f_i} · E e^{λ f_{i'}}` for `i ≠ i'`,
`λ = 6/5`. -/
theorem mgf_pair_offdiag_le {T i i' : ℕ} (hT : 16 ≤ T) (hi : i < T) (hi' : i' < T) (hne : i ≠ i') :
    mgf (fun u => field (blockLen T) u ((T : ℝ) + i) + field (blockLen T) u ((T : ℝ) + i'))
        cellLaw (6 / 5)
      ≤ pairConst * mgf (fun u => field (blockLen T) u ((T : ℝ) + i)) cellLaw (6 / 5)
          * mgf (fun u => field (blockLen T) u ((T : ℝ) + i')) cellLaw (6 / 5) := by
  set K := blockLen T
  set t : ℝ := (T : ℝ) + i
  set t' : ℝ := (T : ℝ) + i'
  have hl : |(6 / 5 : ℝ)| ≤ 6 / 5 := by norm_num
  have hl' : |(6 / 5 : ℝ)| ≤ 12 / 5 := by norm_num
  have hT' : (16 : ℝ) ≤ T := by exact_mod_cast hT
  obtain ⟨h1, h2⟩ := netPoint_bounds hi
  obtain ⟨h1', h2'⟩ := netPoint_bounds hi'
  have hsep : 1 ≤ |t - t'| := by
    have : (i : ℝ) ≠ i' := by exact_mod_cast hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : (i : ℝ) + 1 ≤ i' := by exact_mod_cast h
      rw [abs_sub_comm, abs_of_pos (by simp only [t, t']; linarith)]; simp only [t, t']; linarith
    · have : (i' : ℝ) + 1 ≤ i := by exact_mod_cast h
      rw [abs_of_pos (by simp only [t, t']; linarith)]; simp only [t, t']; linarith
  have hK : (T : ℝ) ≤ K := by have := (blockLen_ge hT).1; linarith
  have hcov := abs_fieldCov_le hT' h1 h2 h1' h2' hsep hK
  have hpair := log_mgf_field_pair_le (blockLen_ge hT).2 t t' hl
  have hA := log_mgf_field_ge (blockLen_ge hT).2 t hl'
  have hB := log_mgf_field_ge (blockLen_ge hT).2 t' hl'
  have hposA := mgf_field_pos K t (6 / 5)
  have hposB := mgf_field_pos K t' (6 / 5)
  have hposP := mgf_field_pair_pos K t t' (6 / 5)
  rw [← Real.exp_log hposP, ← Real.exp_log hposA, ← Real.exp_log hposB, pairConst,
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hc := (abs_le.mp hcov).2
  nlinarith

theorem mgf_pair_diag_le {T i : ℕ} (hT : 16 ≤ T) (hi : i < T) :
    mgf (fun u => field (blockLen T) u ((T : ℝ) + i) + field (blockLen T) u ((T : ℝ) + i))
        cellLaw (6 / 5)
      ≤ Real.exp (2 * (6 / 5) ^ 2 * ((1 / 2) * Real.log T + 5) + 130) := by
  set K := blockLen T
  set t : ℝ := (T : ℝ) + i
  have hl : |(6 / 5 : ℝ)| ≤ 6 / 5 := by norm_num
  have hpair := log_mgf_field_pair_le (blockLen_ge hT).2 t t hl
  rw [fieldCov_self] at hpair
  have hv := fieldVar_block_le hT hi
  have hposP := mgf_field_pair_pos K t t (6 / 5)
  rw [← Real.exp_log hposP]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- **Second moment.** For `T ≥ 16` with `log T ≥ 1328`: `E W² ≤ (C + 1)(E W)²` at `λ = 6/5`. -/
theorem integral_partW_sq_le {T : ℕ} (hT : 16 ≤ T) (hlogT : 1328 ≤ Real.log T) :
    ∫ u, partW T (6 / 5) u ^ 2 ∂cellLaw ≤ (pairConst + 1) * (∫ u, partW T (6 / 5) u ∂cellLaw) ^ 2 := by
  rw [integral_partW_sq, integral_partW]
  set m : ℕ → ℝ := fun i => mgf (fun u => field (blockLen T) u ((T : ℝ) + i)) cellLaw (6 / 5)
  set D : ℝ := Real.exp (2 * (6 / 5) ^ 2 * ((1 / 2) * Real.log T + 5) + 130)
  have hm0 : ∀ i, 0 ≤ m i := fun i => (mgf_field_pos _ _ _).le
  have hpt : ∀ i ∈ Finset.range T, ∀ i' ∈ Finset.range T,
      mgf (fun u => field (blockLen T) u ((T : ℝ) + i) + field (blockLen T) u ((T : ℝ) + i'))
        cellLaw (6 / 5) ≤ pairConst * m i * m i' + (if i = i' then D else 0) := by
    intro i hi i' hi'
    have hi2 := Finset.mem_range.mp hi
    have hi2' := Finset.mem_range.mp hi'
    by_cases h : i = i'
    · subst h
      simp only [if_true]
      have h1 := mgf_pair_diag_le hT hi2
      have h0 : 0 ≤ pairConst * m i * m i :=
        mul_nonneg (mul_nonneg pairConst_pos.le (hm0 i)) (hm0 i)
      exact h1.trans (le_add_of_nonneg_left h0)
    · simp only [h, if_false, add_zero]
      exact mgf_pair_offdiag_le hT hi2 hi2' h
  have hsum : ∑ i ∈ Finset.range T, ∑ i' ∈ Finset.range T,
      mgf (fun u => field (blockLen T) u ((T : ℝ) + i) + field (blockLen T) u ((T : ℝ) + i'))
        cellLaw (6 / 5)
      ≤ pairConst * (∑ i ∈ Finset.range T, m i) ^ 2 + T * D := by
    calc _ ≤ ∑ i ∈ Finset.range T, ∑ i' ∈ Finset.range T,
          (pairConst * m i * m i' + (if i = i' then D else 0)) :=
          Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun i' hi' => hpt i hi i' hi'))
      _ = pairConst * (∑ i ∈ Finset.range T, m i) ^ 2 + T * D := by
          simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_range]
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          congr 1
          · apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro i' _; ring
          · rw [Finset.sum_congr rfl (fun x hx => if_pos (Finset.mem_range.mp hx)),
              Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine hsum.trans ?_
  -- the diagonal is at most `(Σ m)²`
  have hT' : (16 : ℝ) ≤ T := by exact_mod_cast hT
  have hlow : (T : ℝ) * Real.exp ((6 / 5) ^ 2 * ((1 / 2) * Real.log T - 19) / 2 - 100)
      ≤ ∑ i ∈ Finset.range T, m i := by
    calc (T : ℝ) * Real.exp ((6 / 5) ^ 2 * ((1 / 2) * Real.log T - 19) / 2 - 100)
        = ∑ _i ∈ Finset.range T, Real.exp ((6 / 5) ^ 2 * ((1 / 2) * Real.log T - 19) / 2 - 100) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.range T, m i := Finset.sum_le_sum (fun i hi =>
          mgf_block_ge hT (Finset.mem_range.mp hi) (by norm_num))
  have hTpos : (0 : ℝ) < T := by linarith
  set b : ℝ := (6 / 5) ^ 2 * ((1 / 2) * Real.log T - 19) / 2 - 100 with hb
  have hkey : D ≤ (T : ℝ) * Real.exp b ^ 2 := by
    have e : (T : ℝ) * Real.exp b ^ 2 = Real.exp (Real.log T + 2 * b) := by
      rw [Real.exp_add, Real.exp_log hTpos, show Real.exp b ^ 2 = Real.exp (2 * b) by
        rw [← Real.exp_nat_mul]; norm_num]
    rw [e]
    apply Real.exp_le_exp.mpr
    rw [hb]
    nlinarith
  have hdiag : (T : ℝ) * D ≤ (∑ i ∈ Finset.range T, m i) ^ 2 := by
    refine le_trans ?_ (pow_le_pow_left₀ (by positivity) hlow 2)
    rw [mul_pow, sq (T : ℝ), mul_assoc]
    exact mul_le_mul_of_nonneg_left hkey hTpos.le
  nlinarith [pairConst_pos]


/-! ### Paley–Zygmund and Markov -/

/-- **Paley–Zygmund.** `P(W ≥ E W/2) ≥ (E W)²/(4 E W²)` for `W ≥ 0`. -/
theorem measureReal_ge_half_integral_ge {W : (ℕ → ℝ) → ℝ} (hW : Measurable W)
    (hi : Integrable W cellLaw) (hi2 : Integrable (fun u => W u ^ 2) cellLaw)
    (hm : 0 < ∫ u, W u ∂cellLaw) (hs : 0 < ∫ u, W u ^ 2 ∂cellLaw) :
    (∫ u, W u ∂cellLaw) ^ 2 / (4 * ∫ u, W u ^ 2 ∂cellLaw)
      ≤ cellLaw.real {u | (∫ w, W w ∂cellLaw) / 2 ≤ W u} := by
  set m := ∫ u, W u ∂cellLaw with hmdef
  set sv := ∫ u, W u ^ 2 ∂cellLaw with hsdef
  set A := {u | m / 2 ≤ W u} with hA
  have hAm : MeasurableSet A := measurableSet_le measurable_const hW
  set a := 2 * sv / m with hadef
  have ha : 0 < a := by positivity
  have hpt : ∀ u, W u ≤ m / 2 + (W u ^ 2 / (2 * a) + (a / 2) * A.indicator (1 : (ℕ → ℝ) → ℝ) u) := by
    intro u
    by_cases hu : u ∈ A
    · rw [Set.indicator_of_mem hu, Pi.one_apply]
      have h1 : W u ≤ W u ^ 2 / (2 * a) + a / 2 := by
        rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (W u - a)]
      have : 0 ≤ m / 2 := by positivity
      linarith
    · rw [Set.indicator_of_notMem hu]
      have h1 : W u < m / 2 := by simpa [hA] using hu
      have : 0 ≤ W u ^ 2 / (2 * a) := by positivity
      linarith
  have i1 : Integrable (fun u => W u ^ 2 / (2 * a)) cellLaw := hi2.div_const _
  have i2 : Integrable (fun u => (a / 2) * A.indicator (1 : (ℕ → ℝ) → ℝ) u) cellLaw :=
    ((integrable_const (1 : ℝ)).indicator hAm).const_mul _
  have i12 : Integrable (fun u => W u ^ 2 / (2 * a) + (a / 2) * A.indicator (1 : (ℕ → ℝ) → ℝ) u)
      cellLaw := i1.add i2
  have hint : Integrable (fun u => m / 2 + (W u ^ 2 / (2 * a)
      + (a / 2) * A.indicator (1 : (ℕ → ℝ) → ℝ) u)) cellLaw := (integrable_const _).add i12
  have hmono := integral_mono hi hint hpt
  have hR : ∫ u, (m / 2 + (W u ^ 2 / (2 * a) + (a / 2) * A.indicator (1 : (ℕ → ℝ) → ℝ) u)) ∂cellLaw
      = m / 2 + (sv / (2 * a) + (a / 2) * cellLaw.real A) := by
    rw [integral_add (integrable_const _) i12, integral_add i1 i2, integral_const, integral_div,
      integral_const_mul, integral_indicator_one hAm]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    rfl
  rw [hR] at hmono
  change m ≤ _ at hmono
  rw [div_le_iff₀ (by positivity)]
  rw [hadef] at hmono
  have hsa : sv / (2 * (2 * sv / m)) = m / 4 := by field_simp; ring
  rw [hsa] at hmono
  have : m / 4 ≤ sv / m * cellLaw.real A := by
    have e : 2 * sv / m / 2 * cellLaw.real A = sv / m * cellLaw.real A := by ring
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hm] at this
  nlinarith

/-- **Markov.** `P(W ≥ c E W) ≤ 1/c`. -/
theorem measureReal_ge_mul_integral_le {W : (ℕ → ℝ) → ℝ} (hW0 : ∀ u, 0 ≤ W u)
    (hi : Integrable W cellLaw) (hm : 0 < ∫ u, W u ∂cellLaw) {c : ℝ} (hc : 0 < c) :
    cellLaw.real {u | c * ∫ w, W w ∂cellLaw ≤ W u} ≤ 1 / c := by
  have h := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hW0) hi
    (c * ∫ w, W w ∂cellLaw)
  rw [le_div_iff₀ hc]
  have hpos : 0 < c * ∫ w, W w ∂cellLaw := mul_pos hc hm
  nlinarith

/-! ### The block event -/

/-- The threshold `c = 8(C + 1)` of the Markov step. -/
def markovConst : ℝ := 8 * (pairConst + 1)

theorem markovConst_pos : 0 < markovConst := by unfold markovConst; linarith [pairConst_pos]

/-- The event that `W_{6/5}` is at least half its mean and `W_{11/10}` below `c` times its mean. -/
def blockEvent (T : ℕ) : Set (ℕ → ℝ) :=
  {u | (∫ w, partW T (6 / 5) w ∂cellLaw) / 2 ≤ partW T (6 / 5) u} \
    {u | markovConst * ∫ w, partW T (11 / 10) w ∂cellLaw ≤ partW T (11 / 10) u}

theorem measurableSet_blockEvent (T : ℕ) : MeasurableSet (blockEvent T) :=
  (measurableSet_le measurable_const (measurable_partW T _)).diff
    (measurableSet_le measurable_const (measurable_partW T _))

theorem integral_partW_pos {T : ℕ} (hT : 1 ≤ T) (l : ℝ) : 0 < ∫ u, partW T l u ∂cellLaw := by
  rw [integral_partW]
  exact Finset.sum_pos (fun i _ => mgf_field_pos _ _ _) (Finset.nonempty_range_iff.mpr (by omega))

theorem integral_partW_sq_pos {T : ℕ} (hT : 1 ≤ T) (l : ℝ) :
    0 < ∫ u, partW T l u ^ 2 ∂cellLaw := by
  rw [integral_pos_iff_support_of_nonneg (fun u => sq_nonneg _) (integrable_partW_sq T l)]
  have : Function.support (fun u => partW T l u ^ 2) = Set.univ := by
    ext u
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact pow_ne_zero 2 (partW_pos hT l u).ne'
  rw [this, measure_univ]
  exact one_pos

/-- **The block event has probability at least `1/(8(C+1))`.** -/
theorem measureReal_blockEvent_ge {T : ℕ} (hT : 16 ≤ T) (hlogT : 1328 ≤ Real.log T) :
    1 / (8 * (pairConst + 1)) ≤ cellLaw.real (blockEvent T) := by
  have hT1 : 1 ≤ T := by omega
  have hm := integral_partW_pos hT1 (6 / 5)
  have hs := integral_partW_sq_pos hT1 (6 / 5)
  have hPZ := measureReal_ge_half_integral_ge (measurable_partW T (6 / 5))
    (integrable_partW T _) (integrable_partW_sq T _) hm hs
  have h2 := integral_partW_sq_le hT hlogT
  have hC : 0 < pairConst + 1 := by linarith [pairConst_pos]
  have hA : 1 / (4 * (pairConst + 1)) ≤ cellLaw.real
      {u | (∫ w, partW T (6 / 5) w ∂cellLaw) / 2 ≤ partW T (6 / 5) u} := by
    refine le_trans ?_ hPZ
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hB := measureReal_ge_mul_integral_le (fun u => (partW_pos hT1 (11 / 10) u).le)
    (integrable_partW T (11 / 10)) (integral_partW_pos hT1 (11 / 10)) markovConst_pos
  have hsub : cellLaw.real {u | (∫ w, partW T (6 / 5) w ∂cellLaw) / 2 ≤ partW T (6 / 5) u}
      ≤ cellLaw.real (blockEvent T) + cellLaw.real
        {u | markovConst * ∫ w, partW T (11 / 10) w ∂cellLaw ≤ partW T (11 / 10) u} := by
    unfold blockEvent
    refine le_trans (measureReal_mono (Set.subset_union_left.trans
      (le_of_eq (Set.sdiff_union_self).symm))) (measureReal_union_le _ _)
  unfold markovConst at hB hsub
  have e : 1 / (4 * (pairConst + 1)) - 1 / (8 * (pairConst + 1)) = 1 / (8 * (pairConst + 1)) := by
    field_simp; ring
  linarith


/-! ### A large value on the block event -/

/-- On the block event some net point carries `f ≥ 10 (log(E W_{6/5}/2) − log(c E W_{11/10}))`. -/
theorem exists_field_ge_of_blockEvent {T : ℕ} (hT : 1 ≤ T) {u : ℕ → ℝ} (hu : u ∈ blockEvent T) :
    ∃ i < T, 10 * (Real.log ((∫ w, partW T (6 / 5) w ∂cellLaw) / 2)
        - Real.log (markovConst * ∫ w, partW T (11 / 10) w ∂cellLaw))
      ≤ field (blockLen T) u ((T : ℝ) + i) := by
  obtain ⟨hA, hB⟩ := hu
  simp only [Set.mem_setOf_eq, not_le] at hA hB
  have hne : (Finset.range T).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
  set f : ℕ → ℝ := fun i => field (blockLen T) u ((T : ℝ) + i)
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' hne f
  set M := (Finset.range T).sup' hne f
  have hle : ∀ j ∈ Finset.range T, f j ≤ M := fun j hj => Finset.le_sup' f hj
  have hW : partW T (6 / 5) u ≤ Real.exp (M / 10) * partW T (11 / 10) u := by
    unfold partW
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := hle j hj
    change 6 / 5 * f j ≤ M / 10 + 11 / 10 * f j
    linarith
  have hm2 := integral_partW_pos hT (6 / 5)
  have hm1 := integral_partW_pos hT (11 / 10)
  have hW1 := partW_pos hT (11 / 10) u
  have hc := markovConst_pos
  refine ⟨i, Finset.mem_range.mp hi, ?_⟩
  show _ ≤ f i
  rw [← hmax]
  have hpos2 : 0 < (∫ w, partW T (6 / 5) w ∂cellLaw) / 2 := half_pos hm2
  have hlog1 : Real.log ((∫ w, partW T (6 / 5) w ∂cellLaw) / 2) ≤ Real.log (partW T (6 / 5) u) :=
    Real.log_le_log hpos2 hA
  have hlog2 : Real.log (partW T (11 / 10) u)
      ≤ Real.log (markovConst * ∫ w, partW T (11 / 10) w ∂cellLaw) :=
    Real.log_le_log hW1 hB.le
  have hlog3 : Real.log (partW T (6 / 5) u) ≤ M / 10 + Real.log (partW T (11 / 10) u) := by
    have := Real.log_le_log (partW_pos hT (6 / 5) u) hW
    rwa [Real.log_mul (Real.exp_pos _).ne' hW1.ne', Real.log_exp] at this
  linarith

/-- The block means: `E W_{6/5} ≥ T e^{(36/25)(½ log T − 19)/2 − 100}` and
`E W_{11/10} ≤ T e^{(121/100)(½ log T + 5)/2 + 120}`. -/
theorem integral_partW_six_fifths_ge {T : ℕ} (hT : 16 ≤ T) :
    (T : ℝ) * Real.exp ((6 / 5) ^ 2 * ((1 / 2) * Real.log T - 19) / 2 - 100)
      ≤ ∫ u, partW T (6 / 5) u ∂cellLaw := by
  rw [integral_partW]
  calc (T : ℝ) * Real.exp ((6 / 5) ^ 2 * ((1 / 2) * Real.log T - 19) / 2 - 100)
      = ∑ _i ∈ Finset.range T, Real.exp ((6 / 5) ^ 2 * ((1 / 2) * Real.log T - 19) / 2 - 100) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum (fun i hi => mgf_block_ge hT (Finset.mem_range.mp hi) (by norm_num))

theorem integral_partW_eleven_tenths_le {T : ℕ} (hT : 16 ≤ T) :
    ∫ u, partW T (11 / 10) u ∂cellLaw
      ≤ (T : ℝ) * Real.exp ((11 / 10) ^ 2 * ((1 / 2) * Real.log T + 5) / 2 + 120) := by
  rw [integral_partW]
  calc _ ≤ ∑ _i ∈ Finset.range T, Real.exp ((11 / 10) ^ 2 * ((1 / 2) * Real.log T + 5) / 2 + 120) :=
        Finset.sum_le_sum (fun i hi => mgf_block_le hT (Finset.mem_range.mp hi) (by norm_num))
    _ = (T : ℝ) * Real.exp ((11 / 10) ^ 2 * ((1 / 2) * Real.log T + 5) / 2 + 120) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The block constant `C₀ = 2400 + 10 log(2c)`. -/
def blockConst : ℝ := 2400 + 10 * Real.log (2 * markovConst)

/-- **Block theorem.** On the block event (probability `≥ 1/(8(C+1))`, for `T ≥ 16` with
`log T ≥ 1328`), every configuration in `[0, 1]^ℕ` has an integer height `n ∈ [T, 2T)` with
`unitSum u n ≥ (23/40) log T − C₀`. -/
theorem exists_unitSum_ge_of_blockEvent {T : ℕ} (hT : 16 ≤ T) {u : ℕ → ℝ} (hu : u ∈ blockEvent T)
    (hu01 : ∀ k, u k ∈ Icc (0 : ℝ) 1) :
    ∃ n : ℕ, T ≤ n ∧ n < 2 * T ∧ (23 / 40) * Real.log T - blockConst ≤ unitSum u n := by
  have hT1 : 1 ≤ T := by omega
  obtain ⟨i, hi, hf⟩ := exists_field_ge_of_blockEvent hT1 hu
  refine ⟨T + i, by omega, by omega, ?_⟩
  have hT' : (16 : ℝ) ≤ T := by exact_mod_cast hT
  have hTpos : (0 : ℝ) < T := by linarith
  have hlow := integral_partW_six_fifths_ge hT
  have hup := integral_partW_eleven_tenths_le hT
  have hc := markovConst_pos
  have hm1 := integral_partW_pos hT1 (11 / 10)
  -- the logarithmic gap
  have hgap : (23 / 40) * Real.log T - (2399 + 10 * Real.log (2 * markovConst))
      ≤ 10 * (Real.log ((∫ w, partW T (6 / 5) w ∂cellLaw) / 2)
        - Real.log (markovConst * ∫ w, partW T (11 / 10) w ∂cellLaw)) := by
    have hA : Real.log T + ((6 / 5) ^ 2 * ((1 / 2) * Real.log T - 19) / 2 - 100) - Real.log 2
        ≤ Real.log ((∫ w, partW T (6 / 5) w ∂cellLaw) / 2) := by
      have := Real.log_le_log (by positivity)
        (div_le_div_of_nonneg_right hlow (by norm_num : (0 : ℝ) ≤ 2))
      rwa [Real.log_div (by positivity) (by norm_num), Real.log_mul hTpos.ne'
        (Real.exp_pos _).ne', Real.log_exp] at this
    have hB : Real.log (markovConst * ∫ w, partW T (11 / 10) w ∂cellLaw)
        ≤ Real.log markovConst + Real.log T
          + ((11 / 10) ^ 2 * ((1 / 2) * Real.log T + 5) / 2 + 120) := by
      have h1 := Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hup hc.le)
      have hR : Real.log (markovConst * ((T : ℝ) *
          Real.exp ((11 / 10) ^ 2 * ((1 / 2) * Real.log T + 5) / 2 + 120)))
          = Real.log markovConst + Real.log T
            + ((11 / 10) ^ 2 * ((1 / 2) * Real.log T + 5) / 2 + 120) := by
        rw [Real.log_mul hc.ne' (by positivity), Real.log_mul hTpos.ne' (Real.exp_pos _).ne',
          Real.log_exp]
        ring
      exact h1.trans (le_of_eq hR)
    have hl2 : Real.log (2 * markovConst) = Real.log 2 + Real.log markovConst :=
      Real.log_mul (by norm_num) hc.ne'
    nlinarith
  -- the truncation error
  have htail := abs_unitSum_sub_field_le hu01 ((T : ℝ) + i) (K := blockLen T)
    (by have := (blockLen_ge hT).2; omega)
  have hsqrt : Real.sqrt (blockLen T : ℝ) = 8 * T := by
    unfold blockLen
    push_cast
    rw [show (64 : ℝ) * T ^ 2 = (8 * T) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hsqrt] at htail
  have hi' : (i : ℝ) < T := by exact_mod_cast hi
  have hterr : (|(T : ℝ) + i| + 1 / 2) * (2 / (8 * T)) ≤ 1 := by
    rw [abs_of_nonneg (by positivity), mul_div_assoc', div_le_one (by positivity)]
    nlinarith
  have htl := (abs_le.mp (htail.trans hterr)).1
  have e : ((T + i : ℕ) : ℝ) = (T : ℝ) + i := by push_cast; ring
  rw [e]
  unfold blockConst
  linarith

end RandomCellWeil
end RHTower
