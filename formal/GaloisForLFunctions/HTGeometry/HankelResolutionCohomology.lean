import GaloisForLFunctions.HTGeometry.HankelIncidenceCech
import GaloisForLFunctions.HTGeometry.ProjTwistedComparison

/-!
# The structure sheaf of the Hankel incidence variety has no higher cohomology

`Y = Proj B_j` with `B_j = T/(ℓ_0, …, ℓ_{j-1})` (`j + r ≤ N`; `j = N - r` is the full system), the incidence variety of binary forms `G` of degree
`≤ r` annihilating a moment vector.  The evaluation charts `D₊(G(k))`, `k = 0, …, r`, cover `Y`
(the coefficients of `G` are linear combinations of its values at `r + 1` nodes), so the Čech
computation `hankelCech_exactAt` and Leray's theorem on `Proj` give

`H^q(Y, 𝒪_Y) = 0` for every `q > 0`,

and every global section of `𝒪_Y` comes from a polynomial in the moments.

* `HTGeometry.HankelY`, `HTGeometry.iSup_hankelChart_eq_top`.
* `HTGeometry.hankelY_cohomology_vanishing`.
* `HTGeometry.hankelY_globalSection_surjective`.
-/

namespace HTGeometry

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open GaloisForLFunctions.HTGeometry.StableCoordinate.HomogeneousQuotient

universe u

variable {K : Type u} [Field K] {r N : ℕ}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

local notation "𝒵" => projGrading K (Fin (r + 1)) (Fin N)

variable (K r N) in
/-- **The Hankel incidence variety** `Y = Proj B_j`. -/
noncomputable abbrev HankelY (j : ℕ) : Scheme.{u} := Proj (quotGrading K r N j)

/-- The coefficients of `G` are combinations of its values at the nodes. -/
theorem zv_eq_sum_chartForm [CharZero K] (i : Fin (r + 1)) :
    zv K r N i = ∑ k, (nodeMatrix K r)⁻¹ i k • chartForm K r N (node K k) := by
  have h := DFunLike.congr_fun (vandermondeSubst_comp (K := K) (r := r) (N := N)) (zv K r N i)
  rw [AlgHom.comp_apply, vandermondeSubstInv_zv, map_sum] at h
  simp only [map_smul, vandermondeSubst_zv] at h
  exact h.symm

/-- **The evaluation charts cover the incidence variety.** -/
theorem iSup_hankelChart_eq_top [CharZero K] (j : ℕ) :
    ⨆ k, Proj.basicOpen (quotGrading K r N j) (qChart K r N j k) = ⊤ := by
  refine Proj.iSup_basicOpen_eq_top' _ _ (fun k => ⟨1, qChart_mem j k⟩) ?_
  rw [eq_top_iff]
  rintro x -
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction a using MvPolynomial.induction_on with
  | C c =>
    have : Ideal.Quotient.mk (hankelIdeal K r N j) (MvPolynomial.C c)
        = algebraMap (quotGrading K r N j 0) _ ⟨_, mk_mem_piece 𝒵 _
          (show MvPolynomial.C c ∈ 𝒵 0 from MvPolynomial.isWeightedHomogeneous_C _ _)⟩ := rfl
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq =>
    rw [map_add]
    exact Subalgebra.add_mem _ hp hq
  | mul_X p v hp =>
    rw [map_mul]
    refine Subalgebra.mul_mem _ hp ?_
    rcases v with i | n
    · rw [show (MvPolynomial.X (Sum.inl i) : IncRing K r N) = zv K r N i from rfl,
        zv_eq_sum_chartForm, map_sum]
      refine Subalgebra.sum_mem _ fun k _ => ?_
      rw [MvPolynomial.smul_eq_C_mul, map_mul]
      refine Subalgebra.mul_mem _ ?_ (Algebra.subset_adjoin ⟨k, rfl⟩)
      have : Ideal.Quotient.mk (hankelIdeal K r N j) (MvPolynomial.C ((nodeMatrix K r)⁻¹ i k))
          = algebraMap (quotGrading K r N j 0) _ ⟨_, mk_mem_piece 𝒵 _
            (show MvPolynomial.C ((nodeMatrix K r)⁻¹ i k) ∈ 𝒵 0 from
              MvPolynomial.isWeightedHomogeneous_C _ _)⟩ := rfl
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
    · have : Ideal.Quotient.mk (hankelIdeal K r N j) (MvPolynomial.X (Sum.inr n))
          = algebraMap (quotGrading K r N j 0) _ ⟨_, mk_mem_piece 𝒵 _ (vv_mem (K := K) (r := r) n)⟩ :=
        rfl
      rw [this]
      exact Subalgebra.algebraMap_mem _ _

/-- **`H^q(Y, 𝒪_Y) = 0` for every `q > 0`** on the Hankel incidence variety. -/
theorem hankelY_cohomology_vanishing [CharZero K] {j : ℕ}
    [CategoryTheory.HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} (HankelY K r N j))] (hj : j + r ≤ N)
    (q : ℕ) (x : RHTower.deningerSheafCohomology.{u} ⊤ (schemeAbSheaf (HankelY K r N j)) (q + 1)) :
    x = 0 := by
  have h1 := iSup_hankelChart_eq_top (K := K) (r := r) (N := N) j
  have h2 : ∀ p : ℕ, (twCech (quotGrading K r N j) (qChart K r N j)
      (qChart_mem j) 0).ExactAt (p + 1) :=
    fun p => hankelCech_exactAt j hj 0 (p + 1) (Nat.zero_le _)
  exact proj_cohomology_vanishing (𝒜 := quotGrading K r N j) (w := qChart K r N j)
    (qChart_mem j) h1 h2 q x

/-- **Every global section of `𝒪_Y` comes from a degree-zero element of `B`.** -/
theorem hankelY_globalSection_surjective [CharZero K] {j : ℕ} (hj : j + r ≤ N) :
    Function.Surjective
      ((projCompare (𝒜 := quotGrading K r N j) (qChart_mem j)).app ∅) := by
  have h1 := iSup_hankelChart_eq_top (K := K) (r := r) (N := N) j
  have h0 := hankelCech_exactAt (K := K) (r := r) (N := N) j hj 0 0 le_rfl
  exact proj_globalSection_surjective (𝒜 := quotGrading K r N j)
    (w := qChart K r N j) (qChart_mem j) h1 h0

end HTGeometry
