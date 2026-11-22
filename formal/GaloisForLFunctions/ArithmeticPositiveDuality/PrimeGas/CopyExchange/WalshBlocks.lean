import GaloisForLFunctions.HTGeometry.HypercubeWalshDiagonalisation
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import GaloisForLFunctions.FamilyContinuationTheory.TheMetaplecticVoronoiExponentInvariants

/-!
# Walsh transformations on a Hilbert sum of finite occupation cubes

Each block is a finite normalized Walsh transform. Parseval in every block
gives an isometry of the entire square-summable family, with itself as inverse.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange

open GaloisForLFunctions.HTGeometry

abbrev Vertex (n : ℕ) := Fin n → Bool
abbrev BlockIndex {ι : Type*} (d : ι → ℕ) := Σ i, Vertex (d i)
abbrev BlockGas {ι : Type*} (d : ι → ℕ) := lp (fun _ : BlockIndex d => ℂ) 2

variable {ι : Type*} (d : ι → ℕ)

private def transform (f : BlockIndex d → ℂ) (x : BlockIndex d) : ℂ :=
  (Walsh.walshMatrix (d x.1)).mulVec (fun y => f ⟨x.1,y⟩) x.2

private theorem block_norm (f : BlockIndex d → ℂ) (i : ι) :
    ∑' x : Vertex (d i), ‖transform d f ⟨i,x⟩‖^2 = ∑' x : Vertex (d i), ‖f ⟨i,x⟩‖^2 := by
  simp only [tsum_fintype]
  change (∑ x, ‖(Walsh.walshMatrix (d i)).mulVec (fun y => f ⟨i,y⟩) x‖^2) = _
  exact FamilyContinuationTheory.Budget.sum_norm_sq_mulVec_unitary (Walsh.walshMatrix (d i))
    (Walsh.walshMatrix_conjTranspose_mul (d i)) (fun y : Vertex (d i) => f ⟨i,y⟩)

private theorem transform_summable (f : BlockGas d) :
    Summable (fun x => ‖transform d f x‖^2) := by
  have hs := (summable_sigma_of_nonneg (fun x : BlockIndex d => sq_nonneg ‖f x‖)).mp
    (HilbertSchmidt.summable_coe_sq f)
  apply (summable_sigma_of_nonneg (fun x : BlockIndex d => sq_nonneg ‖transform d f x‖)).mpr
  exact ⟨fun _ => (hasSum_fintype _).summable,hs.2.congr fun i => (block_norm d f i).symm⟩

private def walshFun (f : BlockGas d) : BlockGas d :=
  ⟨transform d f, (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)).mpr
    (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using transform_summable d f)⟩

private theorem transform_twice (f : BlockGas d) : walshFun d (walshFun d f) = f := by
  apply lp.ext
  funext ⟨i,x⟩
  change (Walsh.walshMatrix (d i)).mulVec ((Walsh.walshMatrix (d i)).mulVec (fun t => f ⟨i,t⟩)) x = _
  rw [Matrix.mulVec_mulVec, Walsh.walshMatrix_mul_self, Matrix.one_mulVec]

/-- Orthogonal sum of the normalized Walsh transforms in cubes of variable dimensions. -/
def blockWalsh : BlockGas d ≃ₗᵢ[ℂ] BlockGas d where
  toFun := walshFun d
  invFun := walshFun d
  left_inv := transform_twice d
  right_inv := transform_twice d
  map_add' f g := by
    apply lp.ext
    funext ⟨i,x⟩
    exact congrFun (Matrix.mulVec_add _ (fun y => f ⟨i,y⟩) (fun y => g ⟨i,y⟩)) x
  map_smul' c f := by
    apply lp.ext
    funext ⟨i,x⟩
    exact congrFun (Matrix.mulVec_smul _ c (fun y => f ⟨i,y⟩)) x
  norm_map' f := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [HilbertSchmidt.lp_norm_sq_eq, HilbertSchmidt.lp_norm_sq_eq]
    change ∑' x, ‖transform d f x‖^2 = _
    rw [(transform_summable d f).tsum_sigma, (HilbertSchmidt.summable_coe_sq f).tsum_sigma]
    exact tsum_congr (block_norm d f)

theorem blockWalsh_apply (f : BlockGas d) (i : ι) (x : Vertex (d i)) :
    blockWalsh d f ⟨i,x⟩ = ∑ y, Walsh.walshMatrix (d i) x y * f ⟨i,y⟩ := rfl

/-- Flipping the specified output bits multiplies a Walsh column by their input parity. -/
def flipBits {n : ℕ} (t x : Vertex n) : Vertex n := fun i => if t i then !(x i) else x i

theorem walsh_flip {n : ℕ} (t x y : Vertex n) :
    Walsh.walshMatrix n (flipBits t x) y = Walsh.walshMatrix n x y * Walsh.cubeSign t y := by
  have h : Walsh.cubeSign (flipBits t x) y = Walsh.cubeSign x y * Walsh.cubeSign t y := by
    rw [Walsh.cubeSign, Walsh.cubeSign, Walsh.cubeSign, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    cases ht : t i <;> cases hx : x i <;> cases hy : y i <;> simp [flipBits,ht,hx,Walsh.boolSign]
  rw [Walsh.walshMatrix_apply,Walsh.walshMatrix_apply,h,mul_assoc]

theorem cubeSign_eq_card {n : ℕ} (t y : Vertex n) :
    Walsh.cubeSign t y = (-1 : ℂ)^(Finset.univ.filter (fun i => (t i && y i) = true)).card := by
  rw [← Finset.prod_const, Finset.prod_filter]
  rfl

/-- The vacuum coordinate on a zero-dimensional block is unchanged. -/
theorem blockWalsh_empty (f : BlockGas d) (i : ι) (x : Vertex (d i)) (hi : d i = 0) :
    blockWalsh d f ⟨i,x⟩ = f ⟨i,x⟩ := by
  rw [blockWalsh_apply]
  have hempty (a : Fin (d i)) : False := by
    have ha := a.isLt
    omega
  have he : ∀ y : Vertex (d i), y = x := by
    intro y
    funext a
    exact (hempty a).elim
  rw [Finset.sum_eq_single x]
  · have hz : Walsh.walshMatrix (d i) x x = 1 := by
      have hsign : Walsh.cubeSign x x = 1 := Finset.prod_eq_one fun a _ => (hempty a).elim
      simp [Walsh.walshMatrix_apply, Walsh.cubeNorm,hsign,hi]
    rw [hz,one_mul]
  · exact fun y _ h => (h (he y)).elim
  · simp

#print axioms blockWalsh
#print axioms walsh_flip
#print axioms cubeSign_eq_card
#print axioms blockWalsh_empty

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange
