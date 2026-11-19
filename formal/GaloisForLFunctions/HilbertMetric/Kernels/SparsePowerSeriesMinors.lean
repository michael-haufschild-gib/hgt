import GaloisForLFunctions.HTGeometry.ValuatedRectangularCompound
import GaloisForLFunctions.HTGeometry.GeneralizedVandermondePositive
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Topology.Instances.Matrix

/-!
# Strict positivity for sparse power-series kernels

Ordered Cauchy–Binet expansion writes every sampled minor as a sum of generalized
Vandermonde products. A single nonzero term gives strict positivity in the series
limit.
-/

namespace GaloisForLFunctions.HilbertMetric
open Matrix Finset Filter Topology HTGeometry
open scoped Classical
noncomputable section

variable {ι κ τ R : Type*} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
  [Fintype τ] [LinearOrder τ] [CommRing R] {k : ℕ}

private theorem orderedCompound_entry (A : Matrix ι κ R) (r : Fin k ↪o ι) (c : Fin k ↪o κ) :
    rectangularCompound k A (Set.powersetCard.ofFinEmbEquiv r) (Set.powersetCard.ofFinEmbEquiv c) =
      (A.submatrix r c).det := by
  rw [rectangularCompound_apply,← det_transpose (A.submatrix r c)]
  congr 1
  ext i j
  simp [subsetEnum]

/-- Every ordered minor of a product is a sum over intermediate ordered point sets.
The intermediate set appears only once, without a factorial factor. -/
theorem orderedMinor_product (A : Matrix ι κ R) (B : Matrix κ τ R)
    (r : Fin k ↪o ι) (c : Fin k ↪o τ) :
    ((A*B).submatrix r c).det = ∑ S : Set.powersetCard κ k,
      (A.submatrix r (subsetEnum S)).det * (B.submatrix (subsetEnum S) c).det := by
  rw [← orderedCompound_entry,rectangularCompound_mul,Matrix.mul_apply]
  refine sum_congr rfl fun S _ => ?_
  let e := Set.powersetCard.ofFinEmbEquiv.symm S
  have hA := orderedCompound_entry A r e
  have hB := orderedCompound_entry B e c
  simp only [e,Equiv.apply_symm_apply] at hA hB
  rw [hA,hB]
  rfl

/-- For nonnegative minors, a product minor is positive exactly when one
intermediate ordered set transmits positive minors in both factors. -/
theorem orderedMinor_product_pos_iff (A : Matrix ι κ ℝ) (B : Matrix κ τ ℝ)
    (r : Fin k ↪o ι) (c : Fin k ↪o τ)
    (hA : ∀ e : Fin k ↪o κ, 0 ≤ (A.submatrix r e).det)
    (hB : ∀ e : Fin k ↪o κ, 0 ≤ (B.submatrix e c).det) :
    0 < ((A*B).submatrix r c).det ↔ ∃ e : Fin k ↪o κ,
      0 < (A.submatrix r e).det ∧ 0 < (B.submatrix e c).det := by
  rw [orderedMinor_product]
  have hnn (S : Set.powersetCard κ k) : 0 ≤ (A.submatrix r (subsetEnum S)).det *
      (B.submatrix (subsetEnum S) c).det :=
    mul_nonneg (hA (Set.powersetCard.ofFinEmbEquiv.symm S)) (hB _)
  constructor
  · intro h
    by_contra! hn
    have hz (S : Set.powersetCard κ k) : (A.submatrix r (subsetEnum S)).det *
        (B.submatrix (subsetEnum S) c).det = 0 := by
      let e := Set.powersetCard.ofFinEmbEquiv.symm S
      by_cases ha : 0 < (A.submatrix r e).det
      · exact mul_eq_zero_of_right _ (le_antisymm (hn e ha) (hB e))
      · exact mul_eq_zero_of_left (le_antisymm (le_of_not_gt ha) (hA e)) _
    simp only [hz,sum_const_zero,lt_self_iff_false] at h
  · rintro ⟨e,ha,hb⟩
    apply sum_pos' (fun S _ => hnn S)
    refine ⟨Set.powersetCard.ofFinEmbEquiv e,mem_univ _,?_⟩
    have hse : subsetEnum (Set.powersetCard.ofFinEmbEquiv e) = ⇑e := by
      funext i; simp [subsetEnum]
    rw [hse]; exact mul_pos ha hb

private def powerMinorTerm {n : ℕ} (e : ℕ ↪o ℕ) (a : ℕ → ℝ)
    (x y : Fin n → ℝ) (J : Fin n → ℕ) :=
  (genVandermonde (fun i => e (J i)) x).det *
    ((∏ i, a (J i)) * (genVandermonde (fun i => e (J i)) y).det)

/-- Finite Cauchy--Binet expansion of a sparse power kernel. The sum runs
over increasing exponent selections, each with its own product of coefficients. -/
theorem powerKernel_det_sum {n : ℕ} (e : ℕ ↪o ℕ) (a : ℕ → ℝ)
    (x y : Fin n → ℝ) (N : ℕ) :
    (of fun i j => ∑ m ∈ range N, a m*(x i*y j)^(e m)).det =
      ∑ S : Set.powersetCard (Fin N) n, powerMinorTerm e a x y (fun i => (subsetEnum S i).val) := by
  let A : Matrix (Fin n) (Fin N) ℝ := of fun i m => (x i)^(e m.val)
  let B : Matrix (Fin N) (Fin n) ℝ := of fun m j => a m.val*(y j)^(e m.val)
  have he : (of fun i j => ∑ m ∈ range N, a m*(x i*y j)^(e m)) = A*B := by
    ext i j
    simp only [A,B,of_apply,mul_apply]
    rw [Fin.sum_univ_eq_sum_range (fun m => x i ^ e m * (a m * y j ^ e m)) N]
    apply sum_congr rfl
    intro m _
    ring
  rw [he]
  have h := orderedMinor_product A B (OrderIso.refl (Fin n)).toOrderEmbedding (OrderIso.refl (Fin n)).toOrderEmbedding
  change (A*B).det = _ at h
  rw [h]
  refine sum_congr rfl fun S _ => ?_
  let r (i : Fin n) := e (subsetEnum S i).val
  change (genVandermonde r x).transpose.det *
    (of fun i j => a (subsetEnum S i).val * genVandermonde r y i j).det = _
  rw [det_transpose,det_mul_column]
  rfl

private theorem powerMinorTerm_pos {n : ℕ} (e : ℕ ↪o ℕ) (a : ℕ → Set.Ioi (0:ℝ))
    (x y : Fin n ↪o Set.Ioi (0:ℝ)) (J : Fin n → ℕ) (hJ : StrictMono J) :
    0 < powerMinorTerm e (fun i => (a i).val) (fun i => (x i).val) (fun i => (y i).val) J := by
  apply mul_pos
  · exact det_genVandermonde_pos _ _ _ (e.strictMono.comp hJ)
      (fun _ _ h => x.strictMono h) (fun i => (x i).property)
  · exact mul_pos (prod_pos fun i _ => (a (J i)).property)
      (det_genVandermonde_pos _ _ _ (e.strictMono.comp hJ)
        (fun _ _ h => y.strictMono h) (fun i => (y i).property))

/-- Keeping the initial exponent block gives a uniform lower bound, independent
of the truncation degree. It remains strictly positive in the infinite limit. -/
private theorem powerKernel_partial_lower {n N : ℕ} (hn : n ≤ N)
    (e : ℕ ↪o ℕ) (a : ℕ → Set.Ioi (0:ℝ)) (x y : Fin n ↪o Set.Ioi (0:ℝ)) :
    powerMinorTerm e (fun m => (a m).val) (fun i => (x i).val) (fun i => (y i).val) Fin.val ≤
      (of fun i j => ∑ m ∈ range N, (a m).val*((x i).val*(y j).val)^(e m)).det := by
  rw [powerKernel_det_sum e (fun m => (a m).val) (fun i => (x i).val) (fun i => (y i).val)]
  let J : Fin n ↪o Fin N := Fin.castLEOrderEmb hn
  have h := single_le_sum (s := univ) (f := fun S : Set.powersetCard (Fin N) n =>
      powerMinorTerm e (fun m => (a m).val) (fun i => (x i).val) (fun i => (y i).val)
        (fun i => (subsetEnum S i).val))
    (fun S _ => (powerMinorTerm_pos e a x y _ (fun _ _ hij =>
      (Set.powersetCard.ofFinEmbEquiv.symm S).strictMono hij)).le)
    (mem_univ (Set.powersetCard.ofFinEmbEquiv J))
  simpa only [subsetEnum,Equiv.symm_apply_apply,J,Fin.castLEOrderEmb_apply,Fin.val_castLE] using h

/-- Convergence at the sampled products suffices for the lower bound from
the first exponent block. This includes power series of finite radius. -/
theorem seriesMinor_grid_lower {n : ℕ} (e : ℕ ↪o ℕ) (a : ℕ → Set.Ioi (0:ℝ))
    (x y : Fin n ↪o Set.Ioi (0:ℝ)) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, HasSum (fun m => (a m).val*((x i).val*(y j).val)^(e m)) (M i j)) :
    (genVandermonde (fun i : Fin n => e i.val) (fun i => (x i).val)).det *
      ((∏ i : Fin n, (a i.val).val) *
        (genVandermonde (fun i : Fin n => e i.val) (fun i => (y i).val)).det) ≤ M.det := by
  have hmat : Tendsto (fun N : ℕ => (of fun i j => ∑ m ∈ range N,
      (a m).val*((x i).val*(y j).val)^(e m))) atTop (𝓝 M) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => (hM i j).tendsto_sum_nat
  exact ge_of_tendsto ((continuous_id.matrix_det.tendsto M).comp hmat)
    ((eventually_ge_atTop n).mono fun _ h => powerKernel_partial_lower h e a x y)

/-- Absolutely monotone product kernels with infinitely many positive
coefficients are strictly totally positive on independent positive grids,
including sparse exponent sequences. -/
theorem sparseSeriesKernel_det_pos {n : ℕ} (e : ℕ ↪o ℕ) (a : ℕ → Set.Ioi (0:ℝ))
    (f : ℝ → ℝ) (hf : ∀ t ∈ Set.Ioi (0:ℝ), HasSum (fun m => (a m).val*t^(e m)) (f t))
    (x y : Fin n ↪o Set.Ioi (0:ℝ)) :
    0 < (of fun i j => f ((x i).val*(y j).val)).det :=
  (powerMinorTerm_pos e a x y Fin.val Fin.val_strictMono).trans_le
    (seriesMinor_grid_lower e a x y _ fun i j => hf _
      (Set.mem_Ioi.mpr (mul_pos (Set.mem_Ioi.mp (x i).property) (Set.mem_Ioi.mp (y j).property))))

/-- Every rectangular-grid minor of the hyperbolic cosine product kernel is positive. -/
theorem coshProduct_det_pos {n : ℕ} (x y : Fin n ↪o Set.Ioi (0:ℝ)) :
    0 < (of fun i j => Real.cosh ((x i).val*(y j).val)).det := by
  let e := OrderEmbedding.ofStrictMono (fun m : ℕ => 2*m) (by intro i j h; dsimp only; omega)
  let a (m : ℕ) : Set.Ioi (0:ℝ) := ⟨((2*m).factorial:ℝ)⁻¹,show (0:ℝ) < _ by positivity⟩
  apply sparseSeriesKernel_det_pos e a
  intro t _
  simpa only [e,a,OrderEmbedding.coe_ofStrictMono,div_eq_inv_mul] using Real.hasSum_cosh t

/-- The odd part of the exponential has strictly positive minors too. -/
theorem sinhProduct_det_pos {n : ℕ} (x y : Fin n ↪o Set.Ioi (0:ℝ)) :
    0 < (of fun i j => Real.sinh ((x i).val*(y j).val)).det := by
  let e := OrderEmbedding.ofStrictMono (fun m : ℕ => 2*m+1) (by intro i j h; dsimp only; omega)
  let a (m : ℕ) : Set.Ioi (0:ℝ) := ⟨((2*m+1).factorial:ℝ)⁻¹,show (0:ℝ) < _ by positivity⟩
  apply sparseSeriesKernel_det_pos e a
  intro t _
  simpa only [e,a,OrderEmbedding.coe_ofStrictMono,div_eq_inv_mul] using Real.hasSum_sinh t

end
end GaloisForLFunctions.HilbertMetric
