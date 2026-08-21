import GaloisForLFunctions.HTGeometry.AffineChainComplex
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Barycentric subdivision of affine chains

For affine chains on a real vector space, the barycentric subdivision operator is defined by the
recursion

  `Sd v = b(v) ∗ Sd (∂ v)`,

where `b(v)` is the barycenter of the vertices of `v` and `∗` is the cone operator; in degree zero
it is the identity.  The recursion is well founded because the boundary lowers the degree, and the
cone identity `∂ (b ∗ c) + b ∗ (∂ c) = c` is exactly what makes `Sd` a chain map.

The subdivision of a simplex whose vertices lie in a convex set again has all its vertices in that
convex set, since barycenters of subsets of the vertices are convex combinations of them.
-/

open CategoryTheory Simplicial AlgebraicTopology Opposite

namespace GaloisForLFunctions.HTGeometry

universe u

variable (R : Type u) [CommRing R] (E : Type u) [AddCommGroup E] [Module ℝ E]

/-- The barycenter of the vertices of an affine simplex. -/
noncomputable def bary {n : ℕ} (v : Fin (n + 1) → E) : E :=
  (((n : ℝ) + 1)⁻¹) • ∑ i, v i

omit [AddCommGroup E] [Module ℝ E] in
/-- The boundary of a cone on a `0`-simplex is the difference of the two endpoints. -/
theorem d_coneMap_single_zero (b : E) (v : Fin 1 → E) :
    ((affChainComplex R E).d 1 0).hom ((coneMap R E b 0).hom (Finsupp.single v (1 : R)))
      = (Finsupp.single v (1 : R) : (Fin 1 → E) →₀ R)
        - Finsupp.single (fun _ : Fin 1 => b) (1 : R) := by
  rw [coneMap_single, d_single, Fin.sum_univ_succ]
  have h0 : Finsupp.single
      ((Fin.cons b v : Fin 2 → E) ∘ (0 : Fin 2).succAbove) ((-1 : R) ^ ((0 : Fin 2) : ℕ))
      = Finsupp.single v (1 : R) := by
    rw [cons_comp_succAbove_zero]
    norm_num
  have h1 : ∀ j : Fin 1, Finsupp.single
      ((Fin.cons b v : Fin 2 → E) ∘ (j.succ).succAbove) ((-1 : R) ^ ((j.succ : Fin 2) : ℕ))
      = -Finsupp.single (fun _ : Fin 1 => b) (1 : R) := by
    intro j
    have hfun : (Fin.cons b v : Fin 2 → E) ∘ (j.succ).succAbove = fun _ : Fin 1 => b := by
      funext k
      have : k = 0 := Subsingleton.elim _ _
      subst this
      simp
    rw [hfun, show ((j.succ : Fin 2) : ℕ) = 1 by simp]
    rw [← Finsupp.single_neg]
    congr 1
    norm_num
  rw [h0, Finset.sum_congr rfl (fun j _ => h1 j)]
  simp [sub_eq_add_neg]

/-- The barycentric subdivision operator on affine chains. -/
noncomputable def sd : ∀ n : ℕ, (affChainComplex R E).X n ⟶ (affChainComplex R E).X n
  | 0 => 𝟙 _
  | (n + 1) => ModuleCat.ofHom (Finsupp.linearCombination R fun v : Fin (n + 2) → E =>
      (coneMap R E (bary E v) n).hom ((sd n).hom
        (((affChainComplex R E).d (n + 1) n).hom (Finsupp.single v (1 : R)))))

@[simp] theorem sd_zero : sd R E 0 = 𝟙 _ := rfl

theorem sd_single {n : ℕ} (v : Fin (n + 2) → E) :
    (sd R E (n + 1)).hom (Finsupp.single v (1 : R))
      = (coneMap R E (bary E v) n).hom ((sd R E n).hom
          (((affChainComplex R E).d (n + 1) n).hom (Finsupp.single v (1 : R)))) := by
  show (Finsupp.linearCombination R fun w : Fin (n + 2) → E =>
      (coneMap R E (bary E w) n).hom ((sd R E n).hom
        (((affChainComplex R E).d (n + 1) n).hom (Finsupp.single w (1 : R)))))
      (Finsupp.single v (1 : R)) = _
  rw [Finsupp.linearCombination_single, one_smul]

omit [AddCommGroup E] [Module ℝ E] in
/-- **The cone identity for arbitrary chains**: `∂ (b ∗ c) + b ∗ (∂ c) = c`. -/
theorem d_coneMap_add {n : ℕ} (b : E) (c : (Fin (n + 2) → E) →₀ R) :
    ((affChainComplex R E).d (n + 2) (n + 1)).hom ((coneMap R E b (n + 1)).hom c)
      + (coneMap R E b n).hom (((affChainComplex R E).d (n + 1) n).hom c)
      = (c : (Fin (n + 2) → E) →₀ R) := by
  have hmap : (((affChainComplex R E).d (n + 2) (n + 1)).hom.comp
        (coneMap R E b (n + 1)).hom)
      + ((coneMap R E b n).hom.comp ((affChainComplex R E).d (n + 1) n).hom)
      = LinearMap.id (R := R) (M := (Fin (n + 2) → E) →₀ R) := by
    refine Finsupp.lhom_ext' fun v => LinearMap.ext_ring ?_
    show ((affChainComplex R E).d (n + 2) (n + 1)).hom
        ((coneMap R E b (n + 1)).hom (Finsupp.single v (1 : R)))
      + (coneMap R E b n).hom
          (((affChainComplex R E).d (n + 1) n).hom (Finsupp.single v (1 : R)))
      = Finsupp.single v (1 : R)
    exact d_coneMap_single R E b v
  exact LinearMap.congr_fun hmap c

/-! ## The augmentation and the chain map property -/

theorem sd_zero_apply (c : (Fin 1 → E) →₀ R) : (sd R E 0).hom c = c := rfl

/-- The augmentation of a `0`-chain: the sum of its coefficients. -/
noncomputable def aug : ((Fin 1 → E) →₀ R) →ₗ[R] R :=
  Finsupp.linearCombination R (fun _ : Fin 1 → E => (1 : R))

omit [AddCommGroup E] [Module ℝ E] in
theorem aug_single (u : Fin 1 → E) (r : R) : aug R E (Finsupp.single u r) = r := by
  rw [aug, Finsupp.linearCombination_single, smul_eq_mul, mul_one]

omit [AddCommGroup E] [Module ℝ E] in
/-- The augmentation of a boundary vanishes. -/
theorem aug_d (c : (Fin 2 → E) →₀ R) :
    aug R E (((affChainComplex R E).d 1 0).hom c) = 0 := by
  have hmap : (aug R E).comp ((affChainComplex R E).d 1 0).hom
      = (0 : ((Fin 2 → E) →₀ R) →ₗ[R] R) := by
    refine Finsupp.lhom_ext' fun v => LinearMap.ext_ring ?_
    show aug R E (((affChainComplex R E).d 1 0).hom (Finsupp.single v (1 : R))) = 0
    rw [d_single, map_sum, Fin.sum_univ_two]
    rw [aug_single, aug_single]
    norm_num
  exact LinearMap.congr_fun hmap c

omit [AddCommGroup E] [Module ℝ E] in
/-- The boundary of a cone on a `0`-chain. -/
theorem d_coneMap_zero (b : E) (c : (Fin 1 → E) →₀ R) :
    ((affChainComplex R E).d 1 0).hom ((coneMap R E b 0).hom c)
      = c - (aug R E c) • (Finsupp.single (fun _ : Fin 1 => b) (1 : R)) := by
  have hmap : (((affChainComplex R E).d 1 0).hom.comp (coneMap R E b 0).hom)
      = LinearMap.id (R := R) (M := (Fin 1 → E) →₀ R)
        - (aug R E).smulRight (Finsupp.single (fun _ : Fin 1 => b) (1 : R)) := by
    refine Finsupp.lhom_ext' fun v => LinearMap.ext_ring ?_
    show ((affChainComplex R E).d 1 0).hom ((coneMap R E b 0).hom (Finsupp.single v (1 : R)))
      = Finsupp.single v (1 : R)
        - (aug R E (Finsupp.single v (1 : R))) •
            (Finsupp.single (fun _ : Fin 1 => b) (1 : R))
    rw [d_coneMap_single_zero, aug_single, one_smul]
  exact LinearMap.congr_fun hmap c

/-- **The subdivision operator is a chain map.** -/
theorem d_sd : ∀ (n : ℕ) (c : (Fin (n + 2) → E) →₀ R),
    ((affChainComplex R E).d (n + 1) n).hom ((sd R E (n + 1)).hom c)
      = (sd R E n).hom (((affChainComplex R E).d (n + 1) n).hom c) := by
  intro n
  induction n with
  | zero =>
    intro c
    have hmap : (((affChainComplex R E).d 1 0).hom.comp (sd R E 1).hom)
        = ((sd R E 0).hom.comp ((affChainComplex R E).d 1 0).hom) := by
      refine Finsupp.lhom_ext' fun v => LinearMap.ext_ring ?_
      show ((affChainComplex R E).d 1 0).hom ((sd R E 1).hom (Finsupp.single v (1 : R)))
        = (sd R E 0).hom (((affChainComplex R E).d 1 0).hom (Finsupp.single v (1 : R)))
      rw [sd_single, sd_zero_apply, d_coneMap_zero, aug_d]
      simp
    exact LinearMap.congr_fun hmap c
  | succ n ih =>
    intro c
    have hmap : (((affChainComplex R E).d (n + 2) (n + 1)).hom.comp (sd R E (n + 2)).hom)
        = ((sd R E (n + 1)).hom.comp ((affChainComplex R E).d (n + 2) (n + 1)).hom) := by
      refine Finsupp.lhom_ext' fun v => LinearMap.ext_ring ?_
      show ((affChainComplex R E).d (n + 2) (n + 1)).hom
            ((sd R E (n + 2)).hom (Finsupp.single v (1 : R)))
        = (sd R E (n + 1)).hom
            (((affChainComplex R E).d (n + 2) (n + 1)).hom (Finsupp.single v (1 : R)))
      rw [sd_single]
      have hdd : ((affChainComplex R E).d (n + 1) n).hom
          (((affChainComplex R E).d (n + 2) (n + 1)).hom (Finsupp.single v (1 : R))) = 0 := by
        have h := (affChainComplex R E).d_comp_d (n + 2) (n + 1) n
        have h3 : ((affChainComplex R E).d (n + 2) (n + 1) ≫
            (affChainComplex R E).d (n + 1) n).hom (Finsupp.single v (1 : R)) = 0 := by
          rw [h]
          simp
        exact h3
      have hdX : ((affChainComplex R E).d (n + 1) n).hom
          ((sd R E (n + 1)).hom
            (((affChainComplex R E).d (n + 2) (n + 1)).hom (Finsupp.single v (1 : R)))) = 0 := by
        rw [ih, hdd, map_zero]
      have hcone := d_coneMap_add R E (bary E v)
        ((sd R E (n + 1)).hom
          (((affChainComplex R E).d (n + 2) (n + 1)).hom (Finsupp.single v (1 : R))))
      rw [hdX, map_zero, add_zero] at hcone
      exact hcone
    exact LinearMap.congr_fun hmap c

/-! ## Linear map form of the operators

Working with `ModuleCat` morphisms makes the carrier appear as a coercion, which blocks the
elaboration of differences of chains.  The following wrappers name the same maps as honest linear
maps between the `Finsupp` modules; all of them are definitional. -/

/-- The boundary as a linear map. -/
noncomputable def affBd (n : ℕ) :
    ((Fin (n + 2) → E) →₀ R) →ₗ[R] ((Fin (n + 1) → E) →₀ R) :=
  ((affChainComplex R E).d (n + 1) n).hom

/-- The cone operator as a linear map. -/
noncomputable def affCone (b : E) (n : ℕ) :
    ((Fin (n + 1) → E) →₀ R) →ₗ[R] ((Fin (n + 2) → E) →₀ R) :=
  (coneMap R E b n).hom

/-- The subdivision operator as a linear map. -/
noncomputable def affSd (n : ℕ) :
    ((Fin (n + 1) → E) →₀ R) →ₗ[R] ((Fin (n + 1) → E) →₀ R) :=
  (sd R E n).hom

theorem affSd_zero (c : (Fin 1 → E) →₀ R) : affSd R E 0 c = c := rfl

theorem affSd_single {n : ℕ} (v : Fin (n + 2) → E) :
    affSd R E (n + 1) (Finsupp.single v (1 : R))
      = affCone R E (bary E v) n (affSd R E n (affBd R E n (Finsupp.single v (1 : R)))) :=
  sd_single R E v

omit [AddCommGroup E] [Module ℝ E] in
theorem affBd_affCone (b : E) {n : ℕ} (c : (Fin (n + 2) → E) →₀ R) :
    affBd R E (n + 1) (affCone R E b (n + 1) c) + affCone R E b n (affBd R E n c) = c :=
  d_coneMap_add R E b c

theorem affBd_affSd {n : ℕ} (c : (Fin (n + 2) → E) →₀ R) :
    affBd R E n (affSd R E (n + 1) c) = affSd R E n (affBd R E n c) :=
  d_sd R E n c

omit [AddCommGroup E] [Module ℝ E] in
theorem affBd_affBd {n : ℕ} (c : (Fin (n + 3) → E) →₀ R) :
    affBd R E n (affBd R E (n + 1) c) = 0 := by
  have h := (affChainComplex R E).d_comp_d (n + 2) (n + 1) n
  have h3 : ((affChainComplex R E).d (n + 2) (n + 1) ≫
      (affChainComplex R E).d (n + 1) n).hom c = 0 := by
    rw [h]
    simp
  exact h3

/-! ## The chain homotopy from the subdivision to the identity -/

/-- The chain homotopy exhibiting the subdivision as homotopic to the identity. -/
noncomputable def affT :
    ∀ n : ℕ, ((Fin (n + 1) → E) →₀ R) →ₗ[R] ((Fin (n + 2) → E) →₀ R)
  | 0 => 0
  | (n + 1) => Finsupp.linearCombination R fun v : Fin (n + 2) → E =>
      affCone R E (bary E v) (n + 1)
        (affSd R E (n + 1) (Finsupp.single v (1 : R)) - Finsupp.single v (1 : R)
          - affT n (affBd R E n (Finsupp.single v (1 : R))))

theorem affT_zero (c : (Fin 1 → E) →₀ R) : affT R E 0 c = 0 := rfl

theorem affT_single {n : ℕ} (v : Fin (n + 2) → E) :
    affT R E (n + 1) (Finsupp.single v (1 : R))
      = affCone R E (bary E v) (n + 1)
        (affSd R E (n + 1) (Finsupp.single v (1 : R)) - Finsupp.single v (1 : R)
          - affT R E n (affBd R E n (Finsupp.single v (1 : R)))) := by
  show (Finsupp.linearCombination R fun w : Fin (n + 2) → E =>
      affCone R E (bary E w) (n + 1)
        (affSd R E (n + 1) (Finsupp.single w (1 : R)) - Finsupp.single w (1 : R)
          - affT R E n (affBd R E n (Finsupp.single w (1 : R)))))
      (Finsupp.single v (1 : R)) = _
  rw [Finsupp.linearCombination_single, one_smul]

/-- **The subdivision is chain homotopic to the identity.** -/
theorem affBd_affT : ∀ (n : ℕ) (c : (Fin (n + 2) → E) →₀ R),
    affBd R E (n + 1) (affT R E (n + 1) c) + affT R E n (affBd R E n c)
      = affSd R E (n + 1) c - c := by
  intro n
  induction n with
  | zero =>
    intro c
    have hmap : ((affBd R E 1).comp (affT R E 1)) + ((affT R E 0).comp (affBd R E 0))
        = affSd R E 1 - LinearMap.id := by
      refine Finsupp.lhom_ext' fun v => LinearMap.ext_ring ?_
      show affBd R E 1 (affT R E 1 (Finsupp.single v (1 : R)))
          + affT R E 0 (affBd R E 0 (Finsupp.single v (1 : R)))
        = affSd R E 1 (Finsupp.single v (1 : R)) - Finsupp.single v (1 : R)
      rw [affT_single, affT_zero, sub_zero, add_zero]
      have hW : affBd R E 0
          (affSd R E 1 (Finsupp.single v (1 : R)) - Finsupp.single v (1 : R)) = 0 := by
        rw [map_sub, affBd_affSd, affSd_zero, sub_self]
      have hcone := affBd_affCone R E (bary E v)
        (affSd R E 1 (Finsupp.single v (1 : R)) - Finsupp.single v (1 : R))
      rw [hW, map_zero, add_zero] at hcone
      exact hcone
    exact LinearMap.congr_fun hmap c
  | succ n ih =>
    intro c
    have hmap : ((affBd R E (n + 2)).comp (affT R E (n + 2)))
        + ((affT R E (n + 1)).comp (affBd R E (n + 1)))
        = affSd R E (n + 2) - LinearMap.id := by
      refine Finsupp.lhom_ext' fun v => LinearMap.ext_ring ?_
      show affBd R E (n + 2) (affT R E (n + 2) (Finsupp.single v (1 : R)))
          + affT R E (n + 1) (affBd R E (n + 1) (Finsupp.single v (1 : R)))
        = affSd R E (n + 2) (Finsupp.single v (1 : R)) - Finsupp.single v (1 : R)
      rw [affT_single]
      set W := affSd R E (n + 2) (Finsupp.single v (1 : R)) - Finsupp.single v (1 : R)
        - affT R E (n + 1) (affBd R E (n + 1) (Finsupp.single v (1 : R))) with hWdef
      have hW : affBd R E (n + 1) W = 0 := by
        have hddX : affBd R E n (affBd R E (n + 1) (Finsupp.single v (1 : R))) = 0 :=
          affBd_affBd R E _
        have ihX := ih (affBd R E (n + 1) (Finsupp.single v (1 : R)))
        rw [hddX, map_zero, add_zero] at ihX
        rw [hWdef, map_sub, map_sub, affBd_affSd, ihX]
        abel
      have hcone := affBd_affCone R E (bary E v) W
      rw [hW, map_zero, add_zero] at hcone
      rw [hcone, hWdef]
      abel
    exact LinearMap.congr_fun hmap c

end GaloisForLFunctions.HTGeometry
