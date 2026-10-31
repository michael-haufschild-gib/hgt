import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnRepresentation

/-!
# The nondegenerate Hermitian form on kernel columns

The pairing of columns at `g` and `h` is `k(g⁻¹h)`. Hermitian symmetry makes
finite column expansions independent of their coefficients. Pairing with a
column is evaluation, proving nondegeneracy; left translation preserves the form.
-/

open Complex Finset
open scoped ComplexConjugate
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [Group G]

/-- A kernel column as a vector in the full column space. -/
def kernelColumnPoint (k : G → ℂ) (g : G) : kernelColumnSpan k :=
  ⟨kernelColumn k g, Submodule.subset_span ⟨g, rfl⟩⟩

private theorem exists_column_coefficients (k : G → ℂ) (v : kernelColumnSpan k) :
    ∃ c : G →₀ ℂ, Finsupp.linearCombination ℂ (kernelColumn k) c = (v : G → ℂ) := by
  have hv := v.property
  change (v : G → ℂ) ∈ Submodule.span ℂ (Set.range (kernelColumn k)) at hv
  rw [← Finsupp.range_linearCombination] at hv
  exact hv

private def columnCoefficients (k : G → ℂ) (v : kernelColumnSpan k) : G →₀ ℂ :=
  Classical.choose (exists_column_coefficients k v)

private theorem columnCoefficients_spec (k : G → ℂ) (v : kernelColumnSpan k) :
    Finsupp.linearCombination ℂ (kernelColumn k) (columnCoefficients k v) = (v : G → ℂ) :=
  Classical.choose_spec (exists_column_coefficients k v)

private theorem columnCoefficients_eval (k : G → ℂ) (v : kernelColumnSpan k) (g : G) :
    ∑ h ∈ (columnCoefficients k v).support,
      columnCoefficients k v h * kernelColumn k h g = (v : G → ℂ) g := by
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] using congrFun (columnCoefficients_spec k v) g

/-- The canonical Hermitian pairing of columns, expressed through finite column expansions. -/
def kernelColumnPairing (k : G → ℂ) (v : kernelColumnSpan k) :
    kernelColumnSpan k →ₗ[ℂ] ℂ where
  toFun w := ∑ g ∈ (columnCoefficients k v).support,
    conj (columnCoefficients k v g) * (w : G → ℂ) g
  map_add' w z := by
    simp only [Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c w := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    apply sum_congr rfl
    intro g _
    ring

private theorem kernelColumn_conj {k : G → ℂ} (hk : IsHermKernel k) (g h : G) :
    conj (kernelColumn k g h) = kernelColumn k h g := by
  change conj (k (h⁻¹ * g)) = k (g⁻¹ * h)
  rw [← hk]
  congr 1
  group

/-- Pairing with a column is conjugate evaluation. -/
theorem kernelColumnPairing_point_right {k : G → ℂ} (hk : IsHermKernel k)
    (v : kernelColumnSpan k) (g : G) :
    kernelColumnPairing k v (kernelColumnPoint k g) = conj ((v : G → ℂ) g) := by
  rw [← columnCoefficients_eval k v g, map_sum]
  apply sum_congr rfl
  intro h _
  rw [map_mul, kernelColumn_conj hk]
  rfl

private theorem columnCoefficients_expansion (k : G → ℂ) (v : kernelColumnSpan k) :
    ∑ g ∈ (columnCoefficients k v).support,
      columnCoefficients k v g • kernelColumnPoint k g = v := by
  apply Subtype.ext
  funext g
  simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, kernelColumnPoint] using columnCoefficients_eval k v g

/-- Every column-space vector is a finite linear combination of kernel columns. -/
theorem exists_kernelColumnPoint_sum (k : G → ℂ) (v : kernelColumnSpan k) :
    ∃ (s : Finset G) (c : G → ℂ), ∑ g ∈ s, c g • kernelColumnPoint k g = v :=
  ⟨(columnCoefficients k v).support, columnCoefficients k v, columnCoefficients_expansion k v⟩

/-- Finite column expansions can be indexed by a finite initial segment. -/
theorem exists_kernelColumnPoint_fin_sum (k : G → ℂ) (v : kernelColumnSpan k) :
    ∃ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
      ∑ j, c j • kernelColumnPoint k (x j) = v := by
  classical
  obtain ⟨s, c, hc⟩ := exists_kernelColumnPoint_sum k v
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  refine ⟨Fintype.card s, fun j => (e j : G), fun j => c (e j), ?_⟩
  calc
    ∑ j, c (e j) • kernelColumnPoint k (e j) =
        ∑ g : s, c g • kernelColumnPoint k g :=
      e.sum_comp (fun g : s => c g • kernelColumnPoint k g)
    _ = ∑ g ∈ s, c g • kernelColumnPoint k g :=
      Finset.sum_attach s (fun g => c g • kernelColumnPoint k g)
    _ = v := hc

/-- The column pairing is Hermitian even when the kernel is indefinite. -/
theorem kernelColumnPairing_conj_symm {k : G → ℂ} (hk : IsHermKernel k)
    (v w : kernelColumnSpan k) :
    kernelColumnPairing k v w = conj (kernelColumnPairing k w v) := by
  conv_lhs => rw [← columnCoefficients_expansion k w]
  simp only [map_sum, map_smul, kernelColumnPairing_point_right hk,
    smul_eq_mul]
  change (∑ g ∈ (columnCoefficients k w).support,
    columnCoefficients k w g * conj ((v : G → ℂ) g)) =
    conj (∑ g ∈ (columnCoefficients k w).support,
      conj (columnCoefficients k w g) * (v : G → ℂ) g)
  simp only [map_sum, map_mul, conj_conj]

theorem kernelColumnPairing_add_left {k : G → ℂ} (hk : IsHermKernel k)
    (v w z : kernelColumnSpan k) :
    kernelColumnPairing k (v + w) z = kernelColumnPairing k v z + kernelColumnPairing k w z := by
  rw [kernelColumnPairing_conj_symm hk, map_add, map_add,
    ← kernelColumnPairing_conj_symm hk, ← kernelColumnPairing_conj_symm hk]

theorem kernelColumnPairing_smul_left {k : G → ℂ} (hk : IsHermKernel k)
    (c : ℂ) (v w : kernelColumnSpan k) :
    kernelColumnPairing k (c • v) w = conj c * kernelColumnPairing k v w := by
  rw [kernelColumnPairing_conj_symm hk, map_smul, smul_eq_mul,
    map_mul, ← kernelColumnPairing_conj_symm hk]

/-- The canonical column pairing as a sesquilinear form. -/
def kernelColumnSesquilinear (k : G → ℂ) (hk : IsHermKernel k) :
    kernelColumnSpan k →ₗ⋆[ℂ] kernelColumnSpan k →ₗ[ℂ] ℂ where
  toFun := kernelColumnPairing k
  map_add' v w := by
    ext z
    exact kernelColumnPairing_add_left hk v w z
  map_smul' c v := by
    ext w
    change kernelColumnPairing k (c • v) w = conj c * kernelColumnPairing k v w
    exact kernelColumnPairing_smul_left hk c v w

/-- Pairing a column with a vector reads the corresponding function value. -/
theorem kernelColumnPairing_point_left {k : G → ℂ} (hk : IsHermKernel k)
    (g : G) (v : kernelColumnSpan k) :
    kernelColumnPairing k (kernelColumnPoint k g) v = (v : G → ℂ) g := by
  rw [kernelColumnPairing_conj_symm hk, kernelColumnPairing_point_right hk, conj_conj]

/-- Pairing a finite column expansion with a vector reads its evaluations. -/
theorem kernelColumnPairing_sum_points {k : G → ℂ} (hk : IsHermKernel k)
    {ι : Type*} [Fintype ι] (x : ι → G) (c : ι → ℂ) (w : kernelColumnSpan k) :
    kernelColumnPairing k (∑ j, c j • kernelColumnPoint k (x j)) w =
      ∑ j, conj (c j) * (w : G → ℂ) (x j) := by
  rw [kernelColumnPairing_conj_symm hk, map_sum]
  simp only [map_smul, smul_eq_mul, kernelColumnPairing_point_right hk,
    map_sum, map_mul, conj_conj]

/-- The column realization has no radical. -/
theorem kernelColumnPairing_nondegenerate {k : G → ℂ} (hk : IsHermKernel k)
    (v : kernelColumnSpan k) (hv : ∀ w, kernelColumnPairing k w v = 0) : v = 0 := by
  apply Subtype.ext
  funext g
  change (v : G → ℂ) g = 0
  simpa only [kernelColumnPairing_point_left hk, Pi.zero_apply] using hv (kernelColumnPoint k g)

theorem kernelColumnRepresentation_point (k : G → ℂ) (a g : G) :
    kernelColumnRepresentation k a (kernelColumnPoint k g) = kernelColumnPoint k (a * g) := by
  apply Subtype.ext
  exact kernelColumnTranslate_column k a g

/-- The group action preserves the canonical column pairing. -/
theorem kernelColumnPairing_invariant {k : G → ℂ} (hk : IsHermKernel k)
    (a : G) (v w : kernelColumnSpan k) :
    kernelColumnPairing k (kernelColumnRepresentation k a v)
      (kernelColumnRepresentation k a w) = kernelColumnPairing k v w := by
  have he (g : G) : kernelColumnPairing k (kernelColumnRepresentation k a v)
      (kernelColumnRepresentation k a (kernelColumnPoint k g)) =
        kernelColumnPairing k v (kernelColumnPoint k g) := by
    rw [kernelColumnRepresentation_point, kernelColumnPairing_point_right hk,
      kernelColumnPairing_point_right hk]
    congr 1
    change (v : G → ℂ) (a⁻¹ * (a * g)) = (v : G → ℂ) g
    rw [inv_mul_cancel_left]
  conv_lhs => rw [← columnCoefficients_expansion k w]
  conv_rhs => rw [← columnCoefficients_expansion k w]
  simp only [map_sum, map_smul, he]

#print axioms kernelColumnPairing_conj_symm
#print axioms kernelColumnPairing_nondegenerate
#print axioms kernelColumnPairing_invariant
end GaloisForLFunctions.HeckeKreinToeplitz
