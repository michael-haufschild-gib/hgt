import GaloisForLFunctions.HTGeometry.GeometricDecayFredholmDeterminant

/-!
# Uniform perturbation bounds for geometric Fredholm determinants

Replacing one row at a time bounds finite determinant differences without an
inverse assumption. Geometric entry bounds make the resulting estimate uniform
in matrix size, so it passes to the actual Fredholm limit. The constant is
`|λ| S² exp(|λ| C S²)`, where `S=(1−η)⁻¹`.
-/

open Complex Matrix Finset Filter Topology
open GaloisForLFunctions.HTGeometry
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerDeterminantBounds

/-- Replacing rows one at a time bounds the determinant difference by one changed row
and the unchanged row majorants. No inverse matrix is required. -/
theorem norm_det_sub_le_rows {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (c d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i)
    (hA : ∀ i, ∑ j, ‖A i j‖ ≤ c i) (hB : ∀ i, ∑ j, ‖B i j‖ ≤ c i)
    (hAB : ∀ i, ∑ j, ‖A i j-B i j‖ ≤ d i) :
    ‖A.det-B.det‖ ≤ ∑ i, d i * ∏ j ∈ Finset.univ.erase i, c j := by
  let f := (Matrix.detRowAlternating : (ι → ℂ) [⋀^ι]→ₗ[ℂ] ℂ)
  have hrow (M : Matrix ι ι ℂ) : ‖M.det‖ ≤ ∏ i, ∑ j, ‖M i j‖ := by
    simpa only [Matrix.det_transpose, Matrix.transpose_apply] using
      GeomFredholm.norm_det_le_prod_colSum M.transpose
  have hfinite (s : Finset ι) :
      ‖f A-f (s.piecewise B A)‖ ≤ ∑ i ∈ s, d i * ∏ j ∈ Finset.univ.erase i, c j := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
      have hs : s.piecewise B A = Function.update (s.piecewise B A) i (A i) := by
        simp [his]
      have hsi : (insert i s).piecewise B A =
          Function.update (s.piecewise B A) i (B i) := s.piecewise_insert _ _ _
      have hstep : ‖f (s.piecewise B A)-f ((insert i s).piecewise B A)‖ ≤
          d i * ∏ j ∈ Finset.univ.erase i, c j := by
        rw [hs, hsi, ← f.map_update_sub]
        change ‖Matrix.det (Function.update (s.piecewise B A) i (A i-B i))‖ ≤ _
        refine (hrow _).trans ?_
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
        apply mul_le_mul
        · simpa using hAB i
        · apply Finset.prod_le_prod
          · intro j hj
            exact Finset.sum_nonneg fun _ _ => norm_nonneg _
          · intro j hj
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
            by_cases hjs : j ∈ s
            · simpa [hjs] using hB j
            · simpa [hjs] using hA j
        · exact Finset.prod_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
        · exact hd i
      calc
        ‖f A-f ((insert i s).piecewise B A)‖ ≤
            ‖f A-f (s.piecewise B A)‖ +
              ‖f (s.piecewise B A)-f ((insert i s).piecewise B A)‖ := by
          rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
          exact dist_triangle _ _ _
        _ ≤ (∑ j ∈ s, d j * ∏ k ∈ Finset.univ.erase j, c k) +
            d i * ∏ j ∈ Finset.univ.erase i, c j := add_le_add ih hstep
        _ = _ := by rw [Finset.sum_insert his]; exact add_comm _ _
  simpa only [Finset.piecewise_univ, f, Matrix.det] using hfinite Finset.univ

open GeomFredholm

/-- Dimension-independent determinant perturbation constant for geometric matrices. -/
def perturbationConstant (lam : ℂ) (C η : ℝ) : ℝ :=
  ‖lam‖ * linSum η ^ 2 * Real.exp (‖lam‖ * C * linSum η ^ 2)

private theorem scaled_row_sum_bound {M : ℕ → ℕ → ℂ} {C η : ℝ}
    (hM : GeomDecay M C η) (lam : ℂ) (N : ℕ) (i : ℕ) :
    ∑ j : Fin N, ‖lam * M i j‖ ≤ ‖lam‖ * C * linSum η * η^i := by
  calc
    _ ≤ ∑ j : Fin N, ‖lam‖ * (C * η^i * η^(j : ℕ)) :=
      Finset.sum_le_sum fun j _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hM.bound i j) (norm_nonneg _)
    _ = ‖lam‖ * C * η^i * ∑ j ∈ Finset.range N, η^j := by
      rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ‖lam‖ * (C * η^i * η^j)) N,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ ‖lam‖ * C * η^i * linSum η := mul_le_mul_of_nonneg_left
      (sum_range_pow_le_linSum hM.rate_nonneg hM.rate_lt_one N)
      (by have := hM.const_nonneg; have := hM.rate_nonneg; positivity)
    _ = _ := by ring

private theorem identity_sub_row_sum_bound {M : ℕ → ℕ → ℂ} {C η : ℝ}
    (hM : GeomDecay M C η) (lam : ℂ) (N : ℕ) (i : Fin N) :
    ∑ j : Fin N, ‖(1-lam • trunc M N) i j‖ ≤
      Real.exp (‖lam‖ * C * linSum η * η^(i : ℕ)) := by
  have hsum : ∑ j : Fin N, ‖(1-lam • trunc M N) i j‖ ≤
      1 + ‖lam‖ * C * linSum η * η^(i : ℕ) := by
    calc
      _ ≤ ∑ j : Fin N, (‖(1 : Matrix (Fin N) (Fin N) ℂ) i j‖ + ‖lam * M i j‖) :=
        Finset.sum_le_sum fun j _ => norm_sub_le _ _
      _ = 1 + ∑ j : Fin N, ‖lam * M i j‖ := by
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single i]
        · simp
        · intro j hj hji
          simp [hji.symm]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
      _ ≤ _ := add_le_add le_rfl (scaled_row_sum_bound hM lam N i)
  exact hsum.trans (by simpa only [add_comm] using
    (Real.add_one_le_exp (‖lam‖ * C * linSum η * η^(i : ℕ))))


/-- Geometric entrywise perturbations control finite determinants uniformly in their size. -/
theorem norm_truncDet_sub_le {M N : ℕ → ℕ → ℂ} {C η δ : ℝ}
    (hM : GeomDecay M C η) (hN : GeomDecay N C η) (hδ : 0 ≤ δ)
    (hMN : ∀ i j, ‖M i j-N i j‖ ≤ δ*η^i*η^j) (lam : ℂ) (n : ℕ) :
    ‖truncDet M lam n-truncDet N lam n‖ ≤ δ*perturbationConstant lam C η := by
  have hC := hM.const_nonneg
  have hη := hM.rate_nonneg
  have hS := (linSum_pos hM.rate_lt_one).le
  have hdiff : GeomDecay (fun i j => M i j-N i j) δ η :=
    ⟨hδ, hη, hM.rate_lt_one, hMN⟩
  let c : Fin n → ℝ := fun i => Real.exp (‖lam‖*C*linSum η*η^(i : ℕ))
  let d : Fin n → ℝ := fun i => ‖lam‖*δ*linSum η*η^(i : ℕ)
  have hd (i : Fin n) : 0 ≤ d i := by dsimp only [d]; positivity
  have hrowdiff (i : Fin n) :
      ∑ j : Fin n, ‖(1-lam • trunc M n) i j-(1-lam • trunc N n) i j‖ ≤ d i := by
    have he (j : Fin n) :
        (1-lam • trunc M n) i j-(1-lam • trunc N n) i j =
          (-lam)*(M i j-N i j) := by
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, trunc, Matrix.of_apply]
      ring
    simp only [he]
    simpa only [norm_neg, d] using scaled_row_sum_bound hdiff (-lam) n i
  have hdet := norm_det_sub_le_rows (1-lam • trunc M n) (1-lam • trunc N n) c d hd
    (identity_sub_row_sum_bound hM lam n) (identity_sub_row_sum_bound hN lam n) hrowdiff
  have hprod (i : Fin n) : ∏ j ∈ Finset.univ.erase i, c j ≤
      Real.exp (‖lam‖*C*linSum η^2) := by
    dsimp only [c]
    rw [← Real.exp_sum, Real.exp_le_exp]
    calc
      _ ≤ ∑ j : Fin n, ‖lam‖*C*linSum η*η^(j : ℕ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ => by positivity)
      _ = ‖lam‖*C*linSum η * ∑ j ∈ Finset.range n, η^j := by
        rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ‖lam‖*C*linSum η*η^j) n,
          Finset.mul_sum]
      _ ≤ ‖lam‖*C*linSum η * linSum η := mul_le_mul_of_nonneg_left
        (sum_range_pow_le_linSum hη hM.rate_lt_one n) (by positivity)
      _ = _ := by ring
  refine hdet.trans ?_
  calc
    _ ≤ ∑ i : Fin n, d i * Real.exp (‖lam‖*C*linSum η^2) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hprod i) (hd i)
    _ = (‖lam‖*δ*linSum η * ∑ i ∈ Finset.range n, η^i) *
        Real.exp (‖lam‖*C*linSum η^2) := by
      rw [← Finset.sum_mul]
      congr 1
      dsimp only [d]
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ‖lam‖*δ*linSum η*η^i) n,
        Finset.mul_sum]
    _ ≤ (‖lam‖*δ*linSum η*linSum η)*Real.exp (‖lam‖*C*linSum η^2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (sum_range_pow_le_linSum hη hM.rate_lt_one n) (by positivity)) (Real.exp_pos _).le
    _ = _ := by unfold perturbationConstant; ring

/-- A dimension-independent Lipschitz bound for the actual Fredholm limit. -/
theorem norm_fdet_sub_le {M N : ℕ → ℕ → ℂ} {C η δ : ℝ}
    (hM : GeomDecay M C η) (hN : GeomDecay N C η) (hδ : 0 ≤ δ)
    (hMN : ∀ i j, ‖M i j-N i j‖ ≤ δ*η^i*η^j) (lam : ℂ) :
    ‖fdet M lam-fdet N lam‖ ≤ δ*perturbationConstant lam C η := by
  exact le_of_tendsto ((tendsto_truncDet hM lam).sub (tendsto_truncDet hN lam)).norm
    (Eventually.of_forall fun n => norm_truncDet_sub_le hM hN hδ hMN lam n)

#print axioms norm_det_sub_le_rows
#print axioms norm_truncDet_sub_le
#print axioms norm_fdet_sub_le

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerDeterminantBounds
