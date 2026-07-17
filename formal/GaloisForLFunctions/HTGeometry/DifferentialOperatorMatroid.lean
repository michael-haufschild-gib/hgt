import GaloisForLFunctions.HTGeometry.DifferentialFamilyMatroid
import GaloisForLFunctions.HTGeometry.DifferentialMatroidRank
import GaloisForLFunctions.HTGeometry.DifferentialOperatorToeplitzRank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.Module

/-!
# The exact differential-operator row matroid

The Toeplitz theorem identifies independent operator outputs with linearly independent polynomial
operator rows.  This file upgrades that finite-packet statement to an equality of genuine
matroids.  Polynomial rows are localized to the fraction field of the operator ring and represented
by homogeneous linear forms in an algebraically independent polynomial family.  The resulting
linear matroid is then exactly the differential-family matroid of the operator outputs.

Consequently every dependent row family has the correct rank as well: the nonlinear differential
rank of any packet of outputs is the ordinary linear rank of its operator rows over the fraction
field.  This is the arbitrary-dependent-family packaging needed by the structural differential-
matroid cards.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Matrix MvPolynomial Set
open scoped Classical Differential

noncomputable section

universe u

/-- The homogeneous linear polynomial represented by a finite coordinate vector. -/
def linearFormPolynomial
    {K κ : Type u} [Field K] [Fintype κ] (v : κ → K) : MvPolynomial κ K :=
  ∑ j, MvPolynomial.C (v j) * MvPolynomial.X j

/-- Forming a homogeneous linear polynomial is a linear map on coefficient vectors. -/
def linearFormPolynomialLinearMap
    (K κ : Type u) [Field K] [Fintype κ] :
    (κ → K) →ₗ[K] MvPolynomial κ K where
  toFun := linearFormPolynomial
  map_add' v w := by
    simp [linearFormPolynomial, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp [linearFormPolynomial, Finset.smul_sum, MvPolynomial.smul_eq_C_mul, mul_assoc]

@[simp]
theorem linearFormPolynomialLinearMap_apply
    {K κ : Type u} [Field K] [Fintype κ] (v : κ → K) :
    linearFormPolynomialLinearMap K κ v = linearFormPolynomial v := rfl

/-- A finite coefficient vector is recovered from its homogeneous linear polynomial. -/
theorem linearFormPolynomial_injective
    (K κ : Type u) [Field K] [Fintype κ] [DecidableEq κ] :
    Function.Injective (linearFormPolynomialLinearMap K κ) := by
  intro v w hvw
  funext j
  have heval := congrArg
    (MvPolynomial.eval (fun k : κ => if k = j then (1 : K) else 0)) hvw
  simpa [linearFormPolynomial] using heval

/-- Algebraic independence of homogeneous linear forms is exactly linear independence of their
coefficient rows. -/
theorem algebraicIndependent_linearFormPolynomial_iff_linearIndependent
    {K ι κ : Type u} [Field K]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (v : ι → κ → K) :
    AlgebraicIndependent K (fun i => linearFormPolynomial (v i)) ↔
      LinearIndependent K v := by
  constructor
  · intro h
    have hforms : LinearIndependent K (fun i => linearFormPolynomial (v i)) :=
      h.linearIndependent
    have hker : LinearMap.ker (linearFormPolynomialLinearMap K κ) = ⊥ :=
      LinearMap.ker_eq_bot.mpr (linearFormPolynomial_injective K κ)
    exact ((linearFormPolynomialLinearMap K κ).linearIndependent_iff hker).mp hforms
  · intro h
    let M : Matrix ι κ K := v
    have hpoly := algebraicIndependent_matrixLinearForms_of_linearIndependent_rows
      M h MvPolynomial.X (MvPolynomial.algebraicIndependent_X κ K)
    simpa [M, matrixLinearForms, linearFormPolynomial] using hpoly

/-- The ordinary vector matroid represented by a finite family of finite-dimensional rows.

It is constructed inside mathlib's algebraic matroid by sending a row to its homogeneous linear
polynomial.  This avoids adding independent matroid axioms: algebraic independence of the linear
forms is already a certified matroid, and the preceding theorem identifies it with row linear
independence. -/
def linearFamilyMatroid
    {K ι κ : Type u} [Field K] [Fintype ι] [Fintype κ]
    (v : ι → κ → K) : Matroid ι :=
  (AlgebraicIndependent.matroid K (MvPolynomial κ K)).comap
    (fun i => linearFormPolynomial (v i))

@[simp]
theorem linearFamilyMatroid_ground
    {K ι κ : Type u} [Field K] [Fintype ι] [Fintype κ]
    (v : ι → κ → K) :
    (linearFamilyMatroid v).E = Set.univ := by
  simp [linearFamilyMatroid]

/-- Independent sets of the represented row matroid are precisely linearly independent
subfamilies. -/
theorem linearFamilyMatroid_indep_iff
    {K ι κ : Type u} [Field K]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (v : ι → κ → K) (I : Set ι) :
    (linearFamilyMatroid v).Indep I ↔
      LinearIndependent K (fun i : I => v i) := by
  let f : ι → MvPolynomial κ K := fun i => linearFormPolynomial (v i)
  rw [linearFamilyMatroid, Matroid.comap_indep_iff,
    AlgebraicIndependent.matroid_indep_iff]
  constructor
  · rintro ⟨himage, hinj⟩
    have himage' : AlgebraicIndependent K
        (fun p : f '' I => (p : MvPolynomial κ K)) := by
      simpa [AlgebraicIndepOn] using himage
    have hfamily : AlgebraicIndependent K (fun i : I => f i) :=
      (algebraicIndependent_image (R := K) hinj).mpr himage'
    exact (algebraicIndependent_linearFormPolynomial_iff_linearIndependent
      (fun i : I => v i)).mp (by simpa [f] using hfamily)
  · intro hrows
    have hfamily : AlgebraicIndependent K (fun i : I => f i) := by
      simpa [f] using
        (algebraicIndependent_linearFormPolynomial_iff_linearIndependent
          (fun i : I => v i)).mpr hrows
    have hinj : Set.InjOn f I := by
      intro a ha b hb hab
      exact congrArg Subtype.val
        (hfamily.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)
    have himage : AlgebraicIndependent K
        (fun p : f '' I => (p : MvPolynomial κ K)) :=
      (algebraicIndependent_image (R := K) hinj).mp hfamily
    exact ⟨by simpa [AlgebraicIndepOn] using himage, hinj⟩

/-- On a finite packet, the extended rank of the represented row matroid is the ordinary vector-
space dimension of the row span. -/
theorem linearFamilyMatroid_eRk_finset
    {K ι κ : Type u} [Field K]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (v : ι → κ → K) (I : Finset ι) :
    (linearFamilyMatroid v).eRk (↑I : Set ι) =
      (Module.finrank K
        (Submodule.span K (v '' (↑I : Set ι))) : ℕ∞) := by
  let M := linearFamilyMatroid v
  obtain ⟨B, hB⟩ := M.exists_isBasis (↑I : Set ι)
  have hBfin : B.Finite := (Finset.finite_toSet I).subset hB.subset
  letI : Fintype B := hBfin.fintype
  have hBind : LinearIndepOn K v B := by
    exact (linearFamilyMatroid_indep_iff v B).mp hB.indep
  have hspan : Submodule.span K (v '' B) =
      Submodule.span K (v '' (↑I : Set ι)) := by
    apply le_antisymm
    · exact Submodule.span_mono (Set.image_mono hB.subset)
    · apply Submodule.span_le.mpr
      intro y hy
      obtain ⟨i, hi, rfl⟩ := hy
      apply hBind.mem_span_iff.mpr
      intro hinsert
      have hMInsert : M.Indep (insert i B) :=
        (linearFamilyMatroid_indep_iff v (insert i B)).mpr hinsert
      exact hB.mem_of_insert_indep hi hMInsert
  have hfinrank : Module.finrank K (Submodule.span K (v '' B)) = Fintype.card B := by
    have hrange : Set.range (fun i : B => v i) = v '' B := by
      ext y
      simp
    rw [← hrange]
    exact finrank_span_eq_card hBind
  change M.eRk (↑I : Set ι) = _
  calc
    M.eRk (↑I : Set ι) = B.encard := hB.eRk_eq_encard
    _ = (Fintype.card B : ℕ∞) := by rw [Set.coe_fintypeCard]
    _ = (Module.finrank K (Submodule.span K (v '' B)) : ℕ∞) := by
      exact_mod_cast hfinrank.symm
    _ = (Module.finrank K
        (Submodule.span K (v '' (↑I : Set ι))) : ℕ∞) := by rw [hspan]

/-- Localize a polynomial operator row to the fraction field `Frac(C[X])`. -/
def localizeOperatorRow
    {C κ : Type u} [Field C] (v : κ → Polynomial C) :
    κ → FractionRing (Polynomial C) :=
  fun j => algebraMap (Polynomial C) (FractionRing (Polynomial C)) (v j)

/-- Pointwise localization of polynomial rows is a linear map over the polynomial ring. -/
def localizeOperatorRowLinearMap
    (C κ : Type u) [Field C] :
    (κ → Polynomial C) →ₗ[Polynomial C] (κ → FractionRing (Polynomial C)) where
  toFun := localizeOperatorRow
  map_add' v w := by
    funext j
    simp [localizeOperatorRow]
  map_smul' c v := by
    funext j
    simp [localizeOperatorRow, Algebra.smul_def]

@[simp]
theorem localizeOperatorRowLinearMap_apply
    {C κ : Type u} [Field C] (v : κ → Polynomial C) :
    localizeOperatorRowLinearMap C κ v = localizeOperatorRow v := rfl

/-- Pointwise localization of polynomial rows is injective. -/
theorem localizeOperatorRow_injective
    (C κ : Type u) [Field C] :
    Function.Injective (localizeOperatorRowLinearMap C κ) := by
  intro v w hvw
  funext j
  exact (FaithfulSMul.algebraMap_injective
    (Polynomial C) (FractionRing (Polynomial C))) (congrFun hvw j)

/-- Polynomial row independence is unchanged after passing to the operator fraction field. -/
theorem linearIndependent_localizeOperatorRow_iff
    {C ι κ : Type u} [Field C]
    (L : ι → κ → Polynomial C) :
    LinearIndependent (FractionRing (Polynomial C))
        (fun i => localizeOperatorRow (L i)) ↔
      LinearIndependent (Polynomial C) L := by
  let f := localizeOperatorRowLinearMap C κ
  have hker : LinearMap.ker f = ⊥ :=
    LinearMap.ker_eq_bot.mpr (localizeOperatorRow_injective C κ)
  calc
    LinearIndependent (FractionRing (Polynomial C))
        (fun i => localizeOperatorRow (L i)) ↔
        LinearIndependent (Polynomial C)
          (fun i => localizeOperatorRow (L i)) :=
      (LinearIndependent.iff_fractionRing
        (R := Polynomial C) (K := FractionRing (Polynomial C))).symm
    _ ↔ LinearIndependent (Polynomial C) L := by
      simpa [f, Function.comp_def] using
        (f.linearIndependent_iff (v := L) hker)

/-- The ordinary row matroid of polynomial differential operators, computed over the fraction
field of `C[X]`. -/
def differentialOperatorRowMatroid
    {C ι κ : Type u} [Field C] [Fintype ι] [Fintype κ]
    (L : ι → κ → Polynomial C) : Matroid ι :=
  linearFamilyMatroid (fun i => localizeOperatorRow (L i))

@[simp]
theorem differentialOperatorRowMatroid_ground
    {C ι κ : Type u} [Field C] [Fintype ι] [Fintype κ]
    (L : ι → κ → Polynomial C) :
    (differentialOperatorRowMatroid L).E = Set.univ := by
  simp [differentialOperatorRowMatroid]

/-- Independence in the operator-row matroid is polynomial row independence, equivalently row
independence over the fraction field. -/
theorem differentialOperatorRowMatroid_indep_iff
    {C ι κ : Type u} [Field C]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (L : ι → κ → Polynomial C) (I : Set ι) :
    (differentialOperatorRowMatroid L).Indep I ↔
      LinearIndependent (Polynomial C) (fun i : I => L i) := by
  rw [differentialOperatorRowMatroid, linearFamilyMatroid_indep_iff,
    linearIndependent_localizeOperatorRow_iff]

/-- **Exact represented differential-operator matroid law.**

On a differentially independent source family, the genuine differential-family matroid of every
finite polynomial operator-row packet is exactly its ordinary row matroid over `Frac(C[X])`.
This equality includes arbitrary dependent packets and therefore upgrades the earlier independent-
set criterion to the complete nonlinear rank law. -/
theorem differentialFamilyMatroid_differentialOperatorRows_eq
    {C K ι κ : Type u}
    [Field C] [Field K] [Algebra C K]
    [Differential C] [Differential K] [DifferentialAlgebra C K] [CharZero K]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (L : ι → κ → Polynomial C)
    (x : κ → K) (hx : DifferentialIndependent C x) :
    differentialFamilyMatroid (F := C) (differentialOperatorRowApply L x) =
      differentialOperatorRowMatroid L := by
  apply Matroid.ext_indep
  · simp [GaloisForLFunctions.differentialFamilyMatroid]
  · intro I _
    rw [differentialFamilyMatroid_indep_iff,
      differentialOperatorRowMatroid_indep_iff]
    simpa only [differentialOperatorRowApply] using
      (differentialIndependent_differentialOperatorRows_iff
        hconst (fun i : I => L i) x hx)

/-- Every finite packet has the same differential-matroid rank as its localized polynomial rows. -/
theorem differentialOperatorRows_eRk_eq
    {C K ι κ : Type u}
    [Field C] [Field K] [Algebra C K]
    [Differential C] [Differential K] [DifferentialAlgebra C K] [CharZero K]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (L : ι → κ → Polynomial C)
    (x : κ → K) (hx : DifferentialIndependent C x) (I : Set ι) :
    (differentialFamilyMatroid (F := C)
        (differentialOperatorRowApply L x)).eRk I =
      (differentialOperatorRowMatroid L).eRk I := by
  rw [differentialFamilyMatroid_differentialOperatorRows_eq hconst L x hx]

/-- **Numerical differential-operator rank law.**  The differential rank of an arbitrary finite
output packet is the vector-space dimension of the span of its localized polynomial operator
rows. -/
theorem differentialOperatorRows_eRk_eq_finrank_span
    {C K ι κ : Type u}
    [Field C] [Field K] [Algebra C K]
    [Differential C] [Differential K] [DifferentialAlgebra C K] [CharZero K]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (L : ι → κ → Polynomial C)
    (x : κ → K) (hx : DifferentialIndependent C x) (I : Finset ι) :
    (differentialFamilyMatroid (F := C)
        (differentialOperatorRowApply L x)).eRk (↑I : Set ι) =
      (Module.finrank (FractionRing (Polynomial C))
        (Submodule.span (FractionRing (Polynomial C))
          ((fun i => localizeOperatorRow (L i)) '' (↑I : Set ι))) : ℕ∞) := by
  rw [differentialFamilyMatroid_differentialOperatorRows_eq hconst L x hx]
  exact linearFamilyMatroid_eRk_finset
    (fun i => localizeOperatorRow (L i)) I

/-- Nat-valued gluing ranks agree on every finite operator-output packet. -/
theorem differentialOperatorRows_matroidRank_eq
    {C K ι κ : Type u}
    [Field C] [Field K] [Algebra C K]
    [Differential C] [Differential K] [DifferentialAlgebra C K] [CharZero K]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (L : ι → κ → Polynomial C)
    (x : κ → K) (hx : DifferentialIndependent C x) (I : Finset ι) :
    (MatroidGluing.matroidRank
      (differentialFamilyMatroid (F := C)
        (differentialOperatorRowApply L x))).ρ I =
      (MatroidGluing.matroidRank (differentialOperatorRowMatroid L)).ρ I := by
  rw [differentialFamilyMatroid_differentialOperatorRows_eq hconst L x hx]

/-- Nat-valued form of the numerical differential-operator rank law. -/
theorem differentialOperatorRows_matroidRank_eq_finrank_span
    {C K ι κ : Type u}
    [Field C] [Field K] [Algebra C K]
    [Differential C] [Differential K] [DifferentialAlgebra C K] [CharZero K]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (L : ι → κ → Polynomial C)
    (x : κ → K) (hx : DifferentialIndependent C x) (I : Finset ι) :
    (MatroidGluing.matroidRank
      (differentialFamilyMatroid (F := C)
        (differentialOperatorRowApply L x))).ρ I =
      Module.finrank (FractionRing (Polynomial C))
        (Submodule.span (FractionRing (Polynomial C))
          ((fun i => localizeOperatorRow (L i)) '' (↑I : Set ι))) := by
  rw [MatroidGluing.matroidRank_rho,
    differentialOperatorRows_eRk_eq_finrank_span hconst L x hx]
  simp

end

end GaloisForLFunctions.HTGeometry
