import GaloisForLFunctions.HyperbolicArakelovTheory.TheGroundStateEnergyOfTheAdelicCarrier
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Finite Dirichlet Green kernels of the adelic carrier

Finite compression of the actual weighted adjacency gives a positive definite
precision matrix. Its inverse has nonnegative entries by a maximum principle
for the negative part of a charge. Dirichlet kernels increase under enlargement
and lie below the global product barrier.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators

namespace GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
open FullAdelic CoupledProductObstruction

/-- Dirichlet precision on a finite set of actual vertices. -/
def precisionMatrix (F : Finset FiniteVertices) : Matrix F F ℝ :=
  fun y z => (if y = z then edge else 0) - adjacencyKernel y.1 z.1

def precision (F : Finset FiniteVertices) (f : FiniteVertices → ℝ)
    (y : FiniteVertices) : ℝ := edge * f y - adjacency (finiteSource F f) y

private def extendCharge (F : Finset FiniteVertices) (v : F → ℝ)
    (y : FiniteVertices) : ℝ := if hy : y ∈ F then v ⟨y, hy⟩ else 0

private theorem extendCharge_val (F : Finset FiniteVertices) (v : F → ℝ) (y : F) :
    extendCharge F v y.1 = v y := dif_pos y.2

theorem precisionMatrix_mulVec (F : Finset FiniteVertices) (f : FiniteVertices → ℝ)
    (y : F) : (precisionMatrix F *ᵥ (fun z : F => f z.1)) y = precision F f y.1 := by
  rw [precision, adjacency_finiteSource]
  change (∑ z : F, ((if y = z then edge else 0) - adjacencyKernel y.1 z.1) * f z.1) = _
  simp only [sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  congr 1
  exact Finset.sum_coe_sort F (fun z => adjacencyKernel y.1 z * f z)

theorem precisionMatrix_energy (F : Finset FiniteVertices) (f : FiniteVertices → ℝ) :
    (fun y : F => f y.1) ⬝ᵥ (precisionMatrix F *ᵥ (fun y : F => f y.1)) = energy F f := by
  simp only [dotProduct, precisionMatrix_mulVec, precision, mul_sub]
  rw [Finset.sum_coe_sort F (fun x => f x * (edge * f x) -
    f x * adjacency (finiteSource F f) x), Finset.sum_sub_distrib]
  unfold energy
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Positive definiteness is supplied by the actual carrier energy theorem. -/
theorem precisionMatrix_posDef (F : Finset FiniteVertices) : (precisionMatrix F).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · change (precisionMatrix F).conjTranspose = precisionMatrix F
    ext y z
    simp only [Matrix.conjTranspose_apply, star_trivial]
    change ((if z = y then edge else 0) - adjacencyKernel z.1 y.1) =
      (if y = z then edge else 0) - adjacencyKernel y.1 z.1
    rw [adjacencyKernel_symm]
    simp only [eq_comm]
  · intro v hv
    let f := extendCharge F v
    have hf : (fun y : F => f y.1) = v := funext (extendCharge_val F v)
    rw [star_trivial, ← hf, precisionMatrix_energy]
    apply (energy_pos_iff F f).mpr
    by_contra hn
    apply hv
    funext y
    by_contra hy
    exact hn ⟨y.1, y.2, by simpa only [f, extendCharge_val, Pi.zero_apply] using hy⟩

theorem energy_eq_precision (F : Finset FiniteVertices) (f : FiniteVertices → ℝ) :
    energy F f = ∑ y ∈ F, f y * precision F f y := by
  simp only [energy, precision, mul_sub, Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Testing against the negative part proves the finite maximum principle. -/
theorem precision_maximum (F : Finset FiniteVertices) (f : FiniteVertices → ℝ)
    (hf : ∀ y ∈ F, 0 ≤ precision F f y) : ∀ y ∈ F, 0 ≤ f y := by
  intro y hy
  by_contra hn
  have hneg : f y < 0 := lt_of_not_ge hn
  let v : FiniteVertices → ℝ := fun z => min (f z) 0
  have hv (z : FiniteVertices) : v z ≤ 0 := min_le_right _ _
  have hvf : v ≤ f := fun z => min_le_left _ _
  have hdiag (z : FiniteVertices) : v z * f z = v z ^ 2 := by
    dsimp only [v]
    by_cases hz : f z ≤ 0
    · rw [min_eq_left hz]; ring
    · rw [min_eq_right (le_of_not_ge hz)]; ring
  have hrow (z : FiniteVertices) : v z * precision F v z ≤ v z * precision F f z := by
    have hsum := adjacency_mono (finiteSource_inDomain F v) (finiteSource_inDomain F f)
      (show finiteSource F v ≤ finiteSource F f from fun w => by
        unfold finiteSource
        split_ifs
        · exact hvf w
        · exact le_rfl) z
    have hm := mul_le_mul_of_nonpos_left hsum (hv z)
    unfold precision
    nlinarith only [hm, congrArg (fun r : ℝ => edge * r) (hdiag z)]
  have hle : energy F v ≤ 0 := by
    rw [energy_eq_precision]
    exact (Finset.sum_le_sum (fun z _ => hrow z)).trans
      (Finset.sum_nonpos (fun z hz => mul_nonpos_of_nonpos_of_nonneg (hv z) (hf z hz)))
  have hpos := (energy_pos_iff F v).mpr
    ⟨y, hy, by dsimp only [v]; rw [min_eq_left hneg.le]; exact hneg.ne⟩
  exact (not_le_of_gt hpos) hle

theorem precision_sub (F : Finset FiniteVertices) (f g : FiniteVertices → ℝ)
    (y : FiniteVertices) : precision F (f - g) y = precision F f y - precision F g y := by
  simp only [precision, adjacency_finiteSource, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

theorem precision_comparison (F : Finset FiniteVertices) (f g : FiniteVertices → ℝ)
    (h : ∀ y ∈ F, precision F f y ≤ precision F g y) : ∀ y ∈ F, f y ≤ g y := by
  have hp := precision_maximum F (g - f) (fun y hy => by
    rw [precision_sub]; exact sub_nonneg.mpr (h y hy))
  intro y hy
  exact sub_nonneg.mp (hp y hy)

/-- Extend the inverse precision kernel by zero in both variables. -/
def dirichletGreen (F : Finset FiniteVertices) (x y : FiniteVertices) : ℝ :=
  if hy : y ∈ F then
    if hx : x ∈ F then (precisionMatrix F)⁻¹ ⟨y, hy⟩ ⟨x, hx⟩ else 0
  else 0

theorem dirichletGreen_outside (F : Finset FiniteVertices) (x y : FiniteVertices)
    (hy : y ∉ F) : dirichletGreen F x y = 0 := dif_neg hy

theorem finiteSource_dirichletGreen (F : Finset FiniteVertices) (x : FiniteVertices) :
    finiteSource F (dirichletGreen F x) = dirichletGreen F x := by
  funext y
  unfold finiteSource
  by_cases hy : y ∈ F
  · rw [if_pos hy]
  · rw [if_neg hy, dirichletGreen_outside F x y hy]

theorem dirichletGreen_inDomain (F : Finset FiniteVertices) (x : FiniteVertices) :
    InDomain (dirichletGreen F x) := by
  simpa only [finiteSource_dirichletGreen] using finiteSource_inDomain F (dirichletGreen F x)

theorem dirichletGreen_source (F : Finset FiniteVertices) (x y : FiniteVertices)
    (hy : y ∈ F) : precision F (dirichletGreen F x) y = pointMass x y := by
  by_cases hx : x ∈ F
  · have hv : (fun z : F => dirichletGreen F x z.1) =
        fun z => (precisionMatrix F)⁻¹ z ⟨x, hx⟩ := by
      funext z
      simp only [dirichletGreen, dif_pos z.2, dif_pos hx]
    have hp := precisionMatrix_mulVec F (dirichletGreen F x) ⟨y, hy⟩
    rw [hv] at hp
    have hm := congrArg (fun M : Matrix F F ℝ => M ⟨y, hy⟩ ⟨x, hx⟩)
      (Matrix.mul_nonsing_inv (precisionMatrix F)
        (isUnit_iff_ne_zero.mpr (precisionMatrix_posDef F).det_pos.ne'))
    rw [← hp]
    change (∑ z : F, precisionMatrix F ⟨y, hy⟩ z * (precisionMatrix F)⁻¹ z ⟨x, hx⟩) = _
    rw [show (∑ z : F, precisionMatrix F ⟨y, hy⟩ z * (precisionMatrix F)⁻¹ z ⟨x, hx⟩) =
      (1 : Matrix F F ℝ) ⟨y, hy⟩ ⟨x, hx⟩ from hm]
    simp only [Matrix.one_apply, Subtype.mk.injEq, pointMass, eq_comm]
  · have hxy : x ≠ y := fun h => hx (h ▸ hy)
    simp only [precision, adjacency_finiteSource, dirichletGreen, dif_neg hx,
      dite_eq_ite, ite_self, mul_zero, Finset.sum_const_zero, sub_self, pointMass, if_neg hxy]

theorem dirichletGreen_symm (F : Finset FiniteVertices) (x y : FiniteVertices) :
    dirichletGreen F x y = dirichletGreen F y x := by
  by_cases hx : x ∈ F <;> by_cases hy : y ∈ F
  · simp only [dirichletGreen, dif_pos hx, dif_pos hy]
    simpa only [star_trivial] using
      ((precisionMatrix_posDef F).inv.isHermitian.apply ⟨y, hy⟩ ⟨x, hx⟩).symm
  all_goals simp [dirichletGreen, hx, hy]

/-- Every finite Dirichlet inverse is entrywise nonnegative. -/
theorem dirichletGreen_nonneg (F : Finset FiniteVertices) (x y : FiniteVertices) :
    0 ≤ dirichletGreen F x y := by
  by_cases hy : y ∈ F
  · apply precision_maximum F (dirichletGreen F x) _ y hy
    intro z hz
    rw [dirichletGreen_source F x z hz]
    unfold pointMass
    split_ifs <;> norm_num
  · rw [dirichletGreen_outside F x y hy]

/-- The product barrier controls all Dirichlet domains with the same bound. -/
theorem dirichletGreen_le_barrier (F : Finset FiniteVertices) (x y : FiniteVertices) :
    dirichletGreen F x y ≤ barrier x y := by
  by_cases hy : y ∈ F
  · apply precision_comparison F (dirichletGreen F x) (barrier x) _ y hy
    intro z hz
    rw [dirichletGreen_source F x z hz]
    have hm := adjacency_mono (finiteSource_inDomain F (barrier x)) (barrier_inDomain x)
      (show finiteSource F (barrier x) ≤ barrier x from fun w => by
        unfold finiteSource
        split_ifs
        · exact le_rfl
        · exact barrier_nonneg x w) z
    have hb := barrier_source x z
    unfold precision
    linarith only [hm, hb]
  · rw [dirichletGreen_outside F x y hy]
    exact barrier_nonneg x y

/-- Enlarging a Dirichlet domain increases its Green kernel pointwise. -/
theorem dirichletGreen_mono (x y : FiniteVertices) :
    Monotone (fun F : Finset FiniteVertices => dirichletGreen F x y) := by
  intro F E hFE
  change dirichletGreen F x y ≤ dirichletGreen E x y
  by_cases hy : y ∈ F
  · apply precision_comparison F (dirichletGreen F x) (dirichletGreen E x) _ y hy
    intro z hz
    rw [dirichletGreen_source F x z hz]
    have hm := adjacency_mono (finiteSource_inDomain F (dirichletGreen E x))
      (finiteSource_inDomain E (dirichletGreen E x))
      (show finiteSource F (dirichletGreen E x) ≤ finiteSource E (dirichletGreen E x) from
        fun w => by
          unfold finiteSource
          by_cases hw : w ∈ F
          · rw [if_pos hw, if_pos (hFE hw)]
          · rw [if_neg hw]
            split_ifs
            · exact dirichletGreen_nonneg E x w
            · exact le_rfl) z
    have he := dirichletGreen_source E x z (hFE hz)
    unfold precision at he ⊢
    linarith only [hm, he]
  · rw [dirichletGreen_outside F x y hy]
    exact dirichletGreen_nonneg E x y

theorem sum_finiteSource_mul (S F : Finset FiniteVertices) (hSF : S ⊆ F)
    (f g : FiniteVertices → ℝ) :
    (∑ y ∈ F, finiteSource S f y * g y) = ∑ y ∈ S, f y * g y := by
  symm
  calc
    (∑ y ∈ S, f y * g y) = ∑ y ∈ S, finiteSource S f y * g y := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [finiteSource, if_pos hy]
    _ = ∑ y ∈ F, finiteSource S f y * g y :=
      Finset.sum_subset hSF (fun y _ hy => by rw [finiteSource, if_neg hy, zero_mul])

/-- Inverse precision positivity persists on every smaller charge configuration. -/
theorem dirichletGreen_quadratic_nonneg (S F : Finset FiniteVertices) (hSF : S ⊆ F)
    (f : FiniteVertices → ℝ) :
    0 ≤ ∑ y ∈ S, f y * (∑ x ∈ S, f x * dirichletGreen F x y) := by
  let v : F → ℝ := fun y => finiteSource S f y.1
  have hrow (y : F) : ((precisionMatrix F)⁻¹ *ᵥ v) y =
      ∑ x ∈ S, f x * dirichletGreen F x y.1 := by
    calc
      _ = ∑ x ∈ F, finiteSource S f x * dirichletGreen F x y.1 := by
        rw [← Finset.sum_coe_sort F (fun x => finiteSource S f x * dirichletGreen F x y.1)]
        change (∑ x : F, (precisionMatrix F)⁻¹ y x * v x) = _
        apply Finset.sum_congr rfl
        intro x _
        simp only [dirichletGreen, dif_pos y.2, dif_pos x.2, v]
        ring
      _ = _ := sum_finiteSource_mul S F hSF f _
  have he : v ⬝ᵥ ((precisionMatrix F)⁻¹ *ᵥ v) =
      ∑ y ∈ S, f y * (∑ x ∈ S, f x * dirichletGreen F x y) := by
    simp only [dotProduct, hrow, v]
    rw [Finset.sum_coe_sort F (fun y => finiteSource S f y *
      (∑ x ∈ S, f x * dirichletGreen F x y))]
    exact sum_finiteSource_mul S F hSF f _
  rw [← he]
  by_cases hv : v = 0
  · rw [hv]
    simp only [dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero, le_refl]
  · simpa only [star_trivial] using ((precisionMatrix_posDef F).inv.dotProduct_mulVec_pos hv).le

#print axioms precisionMatrix_posDef
#print axioms precision_maximum
#print axioms dirichletGreen_source
#print axioms dirichletGreen_nonneg
#print axioms dirichletGreen_le_barrier
#print axioms dirichletGreen_mono
#print axioms dirichletGreen_quadratic_nonneg

end GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
