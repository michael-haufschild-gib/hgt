import GaloisForLFunctions.HTGeometry.ZeroListBridge
import GaloisForLFunctions.HTGeometry.ExponentialSumAsymptotics
import GaloisForLFunctions.HTGeometry.PermutohedralAlternantFactorization

/-!
# Strict total positivity of the exponential kernel

For strictly increasing reals `x_1 < ⋯ < x_r` and `t_1 < ⋯ < t_r` the determinant
`det(e^{x_i t_j})` is strictly positive.  Letting the first node `t_1 = s` vary and expanding along
that column writes the determinant as an exponential sum `Σ_i (-1)^i M_i e^{x_i s}` whose
coefficients are signed minors, positive by induction.  The sum vanishes at the `r - 1` other
nodes, so by Laguerre's rule it has no zero to their left; near `-∞` it has the sign of the
coefficient of the smallest exponent, which is `+M_1 > 0`.

Consequently, for pairwise distinct grades `λ` and `0 < t_1 < ⋯ < t_r`,
`det(e^{-λ_i t_j})/Δ_r(λ) > 0` with `Δ_r = Π_{i<j}(λ_i - λ_j)` `(AFD.5)`: sorting the grades
changes numerator and denominator by the same sign.
-/

open Filter Topology Set Finset

namespace GaloisForLFunctions.HTGeometry

/-- The exponential kernel matrix `(e^{x_i t_j})`. -/
noncomputable def expNodeMatrix {r : ℕ} (x t : Fin r → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun i j => Real.exp (x i * t j)

theorem expSum_mul_exp_neg {m : ℕ} (c a : Fin m → ℝ) (α s : ℝ) :
    Real.exp (-(α * s)) * expSum c a s = expSum c (fun i => a i - α) s := by
  simp only [expSum, Finset.mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_left_comm, ← Real.exp_add]
  ring_nf

/-- **Strict total positivity**: `det(e^{x_i t_j}) > 0` for strictly increasing `x` and `t`. -/
theorem det_expKernel_pos : ∀ {r : ℕ} {x t : Fin r → ℝ}, StrictMono x → StrictMono t →
    0 < (expNodeMatrix x t).det
  | 0, x, t, _, _ => by simp [expNodeMatrix]
  | r + 1, x, t, hx, ht => by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · rw [expNodeMatrix, Matrix.det_fin_one]
      exact Real.exp_pos _
    -- the minors are positive
    set M : Fin (r + 1) → ℝ := fun i =>
      (expNodeMatrix (x ∘ i.succAbove) (t ∘ Fin.succ)).det with hM
    have hMpos : ∀ i, 0 < M i := fun i =>
      det_expKernel_pos (hx.comp (Fin.strictMono_succAbove i)) (ht.comp (Fin.strictMono_succ))
    set c : Fin (r + 1) → ℝ := fun i => (-1) ^ (i : ℕ) * M i
    have hc : ∀ i, c i ≠ 0 := fun i => mul_ne_zero (pow_ne_zero _ (by norm_num)) (hMpos i).ne'
    -- the determinant with first node `s`
    set A : ℝ → Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ := fun s =>
      Matrix.of fun i j => Real.exp (x i * (if j = 0 then s else t j))
    have hA : ∀ s, (A s).det = expSum c x s := fun s => by
      rw [Matrix.det_succ_column (A s) 0, expSum]
      refine sum_congr rfl fun i _ => ?_
      have hsub : (A s).submatrix i.succAbove (Fin.succAbove 0) =
          expNodeMatrix (x ∘ i.succAbove) (t ∘ Fin.succ) := by
        ext a b
        simp only [A, Matrix.submatrix_apply, Matrix.of_apply, expNodeMatrix, Function.comp_apply,
          Fin.succAbove_zero, Fin.succ_ne_zero, ↓reduceIte]
      rw [hsub]
      simp only [A, c, M, Matrix.of_apply, ↓reduceIte, Fin.val_zero, add_zero]
      ring
    have hA0 : A (t 0) = expNodeMatrix x t := by
      ext i j
      simp only [A, expNodeMatrix, Matrix.of_apply]
      split_ifs with h
      · rw [h]
      · rfl
    have hzero : ∀ j : Fin r, expSum c x (t j.succ) = 0 := fun j => by
      rw [← hA]
      refine Matrix.det_zero_of_column_eq (Fin.succ_ne_zero j).symm fun k => ?_
      simp [A, Fin.succ_ne_zero]
    -- no zero to the left of the second node
    set j₀ : Fin r := ⟨0, hr⟩
    have hnz : ∀ s < t j₀.succ, expSum c x s ≠ 0 := by
      intro s hs h0
      set Z : Finset ℝ := insert s (univ.image fun j : Fin r => t j.succ)
      have hZ : ∀ y ∈ Z, expSum c x y = 0 := by
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact h0
        · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
          exact hzero j
      have hcard : Z.card = r + 1 := by
        rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _
          (fun a b h => Fin.succ_injective _ (ht.injective h)), card_univ, Fintype.card_fin]
        intro hmem
        obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hmem
        have : t j₀.succ ≤ t j.succ :=
          ht.monotone (Fin.succ_le_succ_iff.2 (Fin.le_def.2 (Nat.zero_le _)))
        linarith
      have := card_zeros_le_expSum (Nat.succ_pos r) c x hx hc Z hZ
      omega
    -- the sign at `-∞`
    have hlim := tendsto_expSum_shift_atBot c x 0 fun i hi => hx (Fin.pos_iff_ne_zero.2 hi)
    have hc0 : 0 < c 0 := by simp only [c, Fin.val_zero, pow_zero, one_mul]; exact hMpos 0
    obtain ⟨s₀, hs₀⟩ := (eventually_atBot.1 (hlim.eventually (eventually_gt_nhds hc0)))
    set s : ℝ := min s₀ (t 0 - 1)
    have hspos : 0 < expSum c x s := by
      have h1 := hs₀ s (min_le_left _ _)
      rw [← expSum_mul_exp_neg] at h1
      exact pos_of_mul_pos_right h1 (Real.exp_pos _).le
    have hst : s < t 0 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have ht01 : t 0 < t j₀.succ := ht (Fin.succ_pos _)
    rw [← hA0, hA]
    by_contra hneg
    push Not at hneg
    have hcont : ContinuousOn (expSum c x) (Icc s (t 0)) :=
      (contDiff_expSum c x).continuous.continuousOn
    obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc' hst.le hcont ⟨hneg, hspos.le⟩
    exact hnz y (lt_of_le_of_lt hy.2 ht01) hy0

/-- **Lemma 3.1, `(AFD.5)`**: for pairwise distinct grades and `t` strictly increasing,
`det(e^{-λ_i t_j})/Δ_r(λ) > 0`. -/
theorem det_expKernel_neg_div_delta_pos {r : ℕ} {lam t : Fin r → ℝ}
    (hlam : Function.Injective lam) (ht : StrictMono t) :
    0 < (expNodeMatrix (fun i => -lam i) t).det / Permutohedral.delta lam := by
  -- sort `-λ` increasingly
  set σ := Tuple.sort fun i => -lam i
  have hmono : Monotone ((fun i => -lam i) ∘ σ) := Tuple.monotone_sort _
  have hinj : Function.Injective ((fun i => -lam i) ∘ σ) :=
    (neg_injective.comp hlam).comp σ.injective
  have hsm : StrictMono ((fun i => -lam i) ∘ σ) := hmono.strictMono_of_injective hinj
  have hdet : (expNodeMatrix ((fun i => -lam i) ∘ σ) t).det =
      (Equiv.Perm.sign σ : ℤ) • (expNodeMatrix (fun i => -lam i) t).det := by
    rw [show expNodeMatrix ((fun i => -lam i) ∘ σ) t =
        (expNodeMatrix (fun i => -lam i) t).submatrix σ id
      by ext i j; rfl, Matrix.det_permute, zsmul_eq_mul]
  have hdelta : Permutohedral.delta (lam ∘ σ) =
      (Equiv.Perm.sign σ : ℤ) • Permutohedral.delta lam := by
    rw [Permutohedral.delta_eq_neg_one_pow_mul, Permutohedral.delta_eq_neg_one_pow_mul,
      vandermondeProd_comp, mul_smul_comm]
  have hpos1 := det_expKernel_pos hsm ht
  have hpos2 : 0 < Permutohedral.delta (lam ∘ σ) := by
    rw [Permutohedral.delta]
    refine prod_pos fun i _ => prod_pos fun j hj => ?_
    have := hsm (mem_Ioi.1 hj)
    simp only [Function.comp_apply] at this ⊢
    linarith
  rw [hdet] at hpos1
  rw [hdelta] at hpos2
  have hu : ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 ∨ ((Equiv.Perm.sign σ : ℤ) : ℝ) = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [zsmul_eq_mul] at hpos1 hpos2
  rcases hu with h | h
  · rw [h, one_mul] at hpos1 hpos2
    exact div_pos hpos1 hpos2
  · rw [h, neg_one_mul, neg_pos] at hpos1 hpos2
    exact div_pos_of_neg_of_neg hpos1 hpos2

end GaloisForLFunctions.HTGeometry
