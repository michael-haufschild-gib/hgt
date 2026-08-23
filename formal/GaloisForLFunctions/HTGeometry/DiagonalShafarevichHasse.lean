import GaloisForLFunctions.HTGeometry.ShafarevichGluing

/-!
# Diagonal Shafarevich Hasse obstruction

For two diagonal scalar actions, the product kernel is exactly the sum of the individual kernels.
Consequently the rank-one Hasse/Shafarevich obstruction `ker(ST)/(ker S + ker T)` vanishes.  This
packages the corpus's elementwise splitting theorem as the literal quotient obstruction.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Pointwise diagonal multiplication on a function space. -/
def functionDiagonalMultiplier {ι K : Type*} [Field K] (a : ι → K) :
    (ι → K) →ₗ[K] (ι → K) where
  toFun x i := a i * x i
  map_add' x y := by
    funext i
    exact mul_add _ _ _
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem functionDiagonalMultiplier_apply
    {ι K : Type*} [Field K] (a x : ι → K) (i : ι) :
    functionDiagonalMultiplier a x i = a i * x i := rfl

/-- The global product-kernel is exactly the sum of its two local diagonal kernels. -/
theorem functionDiagonalMultiplier_mul_ker_eq_sup
    {ι K : Type*} [Field K] (a b : ι → K) :
    LinearMap.ker (functionDiagonalMultiplier (a * b)) =
      LinearMap.ker (functionDiagonalMultiplier a) ⊔
        LinearMap.ker (functionDiagonalMultiplier b) := by
  apply le_antisymm
  · intro x hx
    have hpoint : ∀ i, a i * b i * x i = 0 := by
      intro i
      have hi := congrFun (LinearMap.mem_ker.mp hx) i
      simpa [functionDiagonalMultiplier, mul_assoc] using hi
    obtain ⟨y, z, hxyz, hy, hz⟩ := (diagonalKer_mul_eq_sum_ker a b x).mp hpoint
    have hyker : y ∈ LinearMap.ker (functionDiagonalMultiplier a) := by
      rw [LinearMap.mem_ker]
      funext i
      simpa [functionDiagonalMultiplier] using hy i
    have hzker : z ∈ LinearMap.ker (functionDiagonalMultiplier b) := by
      rw [LinearMap.mem_ker]
      funext i
      simpa [functionDiagonalMultiplier] using hz i
    have hysup : y ∈ LinearMap.ker (functionDiagonalMultiplier a) ⊔
        LinearMap.ker (functionDiagonalMultiplier b) :=
      (show LinearMap.ker (functionDiagonalMultiplier a) ≤
          LinearMap.ker (functionDiagonalMultiplier a) ⊔
            LinearMap.ker (functionDiagonalMultiplier b) from le_sup_left) hyker
    have hzsup : z ∈ LinearMap.ker (functionDiagonalMultiplier a) ⊔
        LinearMap.ker (functionDiagonalMultiplier b) :=
      (show LinearMap.ker (functionDiagonalMultiplier b) ≤
          LinearMap.ker (functionDiagonalMultiplier a) ⊔
            LinearMap.ker (functionDiagonalMultiplier b) from le_sup_right) hzker
    rw [hxyz]
    exact Submodule.add_mem _ hysup hzsup
  · refine sup_le ?_ ?_
    · intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      funext i
      have hi := congrFun hx i
      have hi' : a i * x i = 0 := by simpa using hi
      change a i * b i * x i = 0
      calc
        a i * b i * x i = b i * (a i * x i) := by ring
        _ = 0 := by rw [hi']; simp
    · intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      funext i
      have hi := congrFun hx i
      have hi' : b i * x i = 0 := by simpa using hi
      change a i * b i * x i = 0
      calc
        a i * b i * x i = a i * (b i * x i) := by ring
        _ = 0 := by rw [hi']; simp

/-- Rank-one diagonal Shafarevich obstruction: product-kernel classes modulo the sum of the two
local kernels. -/
abbrev DiagonalShafarevichObstruction {ι K : Type*} [Field K] (a b : ι → K) :=
  LinearMap.ker (functionDiagonalMultiplier (a * b)) ⧸
    (LinearMap.ker (functionDiagonalMultiplier a) ⊔
      LinearMap.ker (functionDiagonalMultiplier b)).comap
        (LinearMap.ker (functionDiagonalMultiplier (a * b))).subtype

/-- The rank-one diagonal Shafarevich obstruction always vanishes. -/
theorem diagonalShafarevichObstruction_subsingleton
    {ι K : Type*} [Field K] (a b : ι → K) :
    Subsingleton (DiagonalShafarevichObstruction a b) := by
  change Subsingleton
    (LinearMap.ker (functionDiagonalMultiplier (a * b)) ⧸
      (LinearMap.ker (functionDiagonalMultiplier a) ⊔
        LinearMap.ker (functionDiagonalMultiplier b)).comap
          (LinearMap.ker (functionDiagonalMultiplier (a * b))).subtype)
  rw [Submodule.Quotient.subsingleton_iff]
  rw [← functionDiagonalMultiplier_mul_ker_eq_sup]
  exact Submodule.comap_subtype_self _

/-- Elementwise vanishing of every rank-one diagonal Shafarevich obstruction class. -/
theorem diagonalShafarevichObstruction_eq_zero
    {ι K : Type*} [Field K] (a b : ι → K)
    (x : DiagonalShafarevichObstruction a b) : x = 0 :=
  @Subsingleton.elim _ (diagonalShafarevichObstruction_subsingleton a b) x 0

end


end GaloisForLFunctions
