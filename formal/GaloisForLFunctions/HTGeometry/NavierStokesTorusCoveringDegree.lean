import GaloisForLFunctions.HTGeometry.NavierStokesTorusHaarCovering
import GaloisForLFunctions.HTGeometry.SmithNormalFormMatrix
import GaloisForLFunctions.HTGeometry.TorusMonomialFamily
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.NavierStokesTorusCoveringDegree

noncomputable section

open GaloisForLFunctions.HTGeometry.NavierStokesTorusHaarCovering

variable {r : ℕ}

/-!
The paper's torus is presented additively, whereas root-of-unity cardinality is most naturally
available on the complex unit circle.  The explicit conjugacy below keeps those two presentations
separate until their kernels have been proved equivalent.
-/

/-- Monomial action of an integer matrix on a product of complex unit circles. -/
def circleTorusMonomialHom (M : Matrix (Fin r) (Fin r) ℤ) :
    (Fin r → Circle) →* (Fin r → Circle) where
  toFun u := fun i ↦ ∏ j, (u j) ^ (M i j)
  map_one' := by
    funext i
    simp
  map_mul' u v := by
    funext i
    simp [mul_zpow, Finset.prod_mul_distrib]

theorem coe_circleTorusMonomialHom (M : Matrix (Fin r) (Fin r) ℤ)
    (u : Fin r → Circle) (i : Fin r) :
    ((circleTorusMonomialHom M u i : Circle) : ℂ) =
      monomialFamily M (fun j ↦ ((u j : Circle) : ℂ)) i := by
  rw [monomialFamily_apply]
  change Circle.coeHom (∏ j, (u j) ^ (M i j)) =
    ∏ j, Circle.coeHom (u j) ^ (M i j)
  simpa only [map_zpow] using map_prod Circle.coeHom
    (fun j ↦ (u j) ^ (M i j)) Finset.univ

theorem circleTorusMonomialHom_mul (M N : Matrix (Fin r) (Fin r) ℤ) :
    circleTorusMonomialHom (M * N) =
      (circleTorusMonomialHom M).comp (circleTorusMonomialHom N) := by
  refine MonoidHom.ext fun u ↦ ?_
  funext i
  apply Subtype.ext
  have hne : ∀ j, ((u j : Circle) : ℂ) ≠ 0 := fun j ↦ Circle.coe_ne_zero (u j)
  have hmid : (fun j ↦ (((circleTorusMonomialHom N u) j : Circle) : ℂ)) =
      monomialFamily N (fun j ↦ ((u j : Circle) : ℂ)) := by
    funext j
    exact coe_circleTorusMonomialHom N u j
  calc
    (((circleTorusMonomialHom (M * N) u i : Circle) : ℂ)) =
        monomialFamily (M * N) (fun j ↦ ((u j : Circle) : ℂ)) i :=
      coe_circleTorusMonomialHom _ _ _
    _ = monomialFamily M (monomialFamily N (fun j ↦ ((u j : Circle) : ℂ))) i := by
      rw [monomialFamily_mul _ _ hne]
    _ = monomialFamily M
        (fun j ↦ (((circleTorusMonomialHom N u) j : Circle) : ℂ)) i := by rw [hmid]
    _ = (((circleTorusMonomialHom M (circleTorusMonomialHom N u) i : Circle) : ℂ)) :=
      (coe_circleTorusMonomialHom _ _ _).symm

@[simp] theorem circleTorusMonomialHom_one :
    circleTorusMonomialHom (1 : Matrix (Fin r) (Fin r) ℤ) = MonoidHom.id _ := by
  refine MonoidHom.ext fun u ↦ ?_
  funext i
  apply Subtype.ext
  have h := coe_circleTorusMonomialHom (1 : Matrix (Fin r) (Fin r) ℤ) u i
  rw [show monomialFamily (1 : Matrix (Fin r) (Fin r) ℤ)
      (fun j ↦ ((u j : Circle) : ℂ)) = (fun j ↦ ((u j : Circle) : ℂ)) from
    monomialFamily_one _] at h
  exact h

/-- A unimodular matrix acts bijectively on the compact circle torus. -/
theorem circleTorusMonomialHom_bijective_of_isUnit_det
    {M : Matrix (Fin r) (Fin r) ℤ} (hu : IsUnit M.det) :
    Function.Bijective (circleTorusMonomialHom M) := by
  obtain ⟨v, hv⟩ := (Matrix.isUnit_iff_isUnit_det M).mpr hu
  have hMN : M * (↑v⁻¹ : Matrix (Fin r) (Fin r) ℤ) = 1 := by
    rw [← hv]
    exact v.mul_inv
  have hNM : (↑v⁻¹ : Matrix (Fin r) (Fin r) ℤ) * M = 1 := by
    rw [← hv]
    exact v.inv_mul
  constructor
  · intro a b hab
    have h := congrArg (circleTorusMonomialHom (↑v⁻¹ : Matrix (Fin r) (Fin r) ℤ)) hab
    rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, ← circleTorusMonomialHom_mul,
      hNM, circleTorusMonomialHom_one] at h
    exact h
  · intro z
    refine ⟨circleTorusMonomialHom (↑v⁻¹ : Matrix (Fin r) (Fin r) ℤ) z, ?_⟩
    have h : (circleTorusMonomialHom M).comp
        (circleTorusMonomialHom (↑v⁻¹ : Matrix (Fin r) (Fin r) ℤ)) = MonoidHom.id _ := by
      rw [← circleTorusMonomialHom_mul, hMN, circleTorusMonomialHom_one]
    exact DFunLike.congr_fun h z

/-- Coordinatewise integer power map on the compact circle torus. -/
def circleTorusPowerHom (d : Fin r → ℤ) : (Fin r → Circle) →* (Fin r → Circle) where
  toFun u := fun i ↦ (u i) ^ (d i)
  map_one' := by
    funext i
    simp
  map_mul' u v := by
    funext i
    simp [mul_zpow]

theorem circleTorusMonomialHom_diagonal (d : Fin r → ℤ) :
    circleTorusMonomialHom (Matrix.diagonal d) = circleTorusPowerHom d := by
  ext u i
  simp [circleTorusMonomialHom, circleTorusPowerHom, Matrix.diagonal_apply]

theorem circle_zpow_eq_one_iff_toUnits_mem_rootsOfUnity (a : Circle) (d : ℤ) :
    a ^ d = 1 ↔ toUnits a ∈ rootsOfUnity d.natAbs Circle := by
  rw [mem_rootsOfUnity]
  change a ^ d = 1 ↔ (toUnits a) ^ d.natAbs = 1
  rw [← map_pow, ← map_one (toUnits : Circle ≃* Circleˣ),
    (toUnits : Circle ≃* Circleˣ).injective.eq_iff]
  rcases le_or_gt 0 d with hpos | hneg
  · rw [← zpow_natCast, show ((d.natAbs : ℕ) : ℤ) = d by omega]
  · rw [← zpow_natCast, show ((d.natAbs : ℕ) : ℤ) = -d by omega,
      zpow_neg, inv_eq_one]

theorem mem_ker_circleTorusPowerHom_iff_natAbs {d : Fin r → ℤ}
    (u : Fin r → Circle) :
    u ∈ (circleTorusPowerHom d).ker ↔
      ∀ i, toUnits (u i) ∈ rootsOfUnity ((d i).natAbs) Circle := by
  simp only [MonoidHom.mem_ker, circleTorusPowerHom]
  constructor
  · intro h i
    apply (circle_zpow_eq_one_iff_toUnits_mem_rootsOfUnity (u i) (d i)).mp
    simpa using congrFun h i
  · intro h
    funext i
    simpa using (circle_zpow_eq_one_iff_toUnits_mem_rootsOfUnity (u i) (d i)).mpr (h i)

def kerCircleTorusPowerHomEquiv {d : Fin r → ℤ} :
    ↥((circleTorusPowerHom d).ker) ≃
      (∀ i, ↥(rootsOfUnity ((d i).natAbs) Circle)) where
  toFun u := fun i ↦ ⟨toUnits ((u : Fin r → Circle) i),
    ((mem_ker_circleTorusPowerHom_iff_natAbs _).mp u.2) i⟩
  invFun v := ⟨fun i ↦ toUnits.symm (v i : Circleˣ),
    (mem_ker_circleTorusPowerHom_iff_natAbs _).mpr fun i ↦ by
      simpa only [toUnits_symm_apply, toUnits_val_apply] using (v i).2⟩
  left_inv u := by
    apply Subtype.ext
    funext i
    rfl
  right_inv v := by
    funext i
    apply Subtype.ext
    exact (toUnits : Circle ≃* Circleˣ).apply_symm_apply (v i : Circleˣ)

theorem card_ker_circleTorusPowerHom {d : Fin r → ℤ} (hd : ∀ i, d i ≠ 0) :
    Nat.card ((circleTorusPowerHom d).ker) = ∏ i, (d i).natAbs := by
  classical
  have hcard : ∀ i, Nat.card (↥(rootsOfUnity ((d i).natAbs) Circle)) = (d i).natAbs := by
    intro i
    have hpos : 0 < (d i).natAbs := Int.natAbs_pos.mpr (hd i)
    letI : NeZero ((d i).natAbs) := ⟨hpos.ne'⟩
    exact HasEnoughRootsOfUnity.natCard_rootsOfUnity Circle ((d i).natAbs)
  rw [Nat.card_congr kerCircleTorusPowerHomEquiv, Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ ↦ hcard i

/-- Kernel cardinality of a nonsingular integer map on the compact circle torus. -/
theorem card_ker_circleTorusMonomialHom {M : Matrix (Fin r) (Fin r) ℤ}
    (hM : M.det ≠ 0) :
    Nat.card ((circleTorusMonomialHom M).ker) = M.det.natAbs := by
  classical
  obtain ⟨U, V, d, hU, hV, hd, hMUDV⟩ := exists_unimodular_diagonal M hM
  have hUinj : Function.Injective (circleTorusMonomialHom U) :=
    (circleTorusMonomialHom_bijective_of_isUnit_det hU).1
  have hVbij : Function.Bijective (circleTorusMonomialHom V) :=
    circleTorusMonomialHom_bijective_of_isUnit_det hV
  have hker : (circleTorusMonomialHom M).ker =
      ((circleTorusPowerHom d).ker).comap (circleTorusMonomialHom V) := by
    ext u
    simp only [MonoidHom.mem_ker, Subgroup.mem_comap, ← circleTorusMonomialHom_diagonal]
    constructor
    · intro h
      rw [hMUDV, circleTorusMonomialHom_mul, circleTorusMonomialHom_mul] at h
      apply hUinj
      rw [map_one]
      exact h
    · intro h
      rw [hMUDV, circleTorusMonomialHom_mul, circleTorusMonomialHom_mul]
      change circleTorusMonomialHom U
        (circleTorusMonomialHom (Matrix.diagonal d) (circleTorusMonomialHom V u)) = 1
      rw [h, map_one]
  have hprod : (∏ i, (d i).natAbs) = M.det.natAbs := by
    have hdet : M.det = U.det * (∏ i, d i) * V.det := by
      rw [hMUDV, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    have hUabs : U.det.natAbs = 1 := Int.isUnit_iff.mp hU |>.elim
      (fun h ↦ by rw [h]; rfl) (fun h ↦ by rw [h]; rfl)
    have hVabs : V.det.natAbs = 1 := Int.isUnit_iff.mp hV |>.elim
      (fun h ↦ by rw [h]; rfl) (fun h ↦ by rw [h]; rfl)
    rw [hdet, Int.natAbs_mul, Int.natAbs_mul, hUabs, hVabs, one_mul, mul_one]
    exact (map_prod Int.natAbsHom d Finset.univ).symm
  rw [hker, ← hprod, ← card_ker_circleTorusPowerHom hd]
  let ev : (Fin r → Circle) ≃* (Fin r → Circle) :=
    MulEquiv.ofBijective (circleTorusMonomialHom V) hVbij
  have hcomap : ((circleTorusPowerHom d).ker).comap (circleTorusMonomialHom V) =
      ((circleTorusPowerHom d).ker).comap (ev : (Fin r → Circle) →* (Fin r → Circle)) := rfl
  rw [hcomap, Subgroup.comap_equiv_eq_map_symm]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _
    (ev.symm : (Fin r → Circle) ≃* (Fin r → Circle)).injective).toEquiv).symm

/-- Existing integer torus map, bundled additively. -/
def torusIntegerAddHom (M : Matrix (Fin r) (Fin r) ℤ) :
    UnitAddTorus (Fin r) →+ UnitAddTorus (Fin r) where
  toFun := torusIntegerHom (M : Fin r → Fin r → ℤ)
  map_zero' := torusIntegerHom_zero _
  map_add' := torusIntegerHom_add _

/-- Coordinatewise identification of the additive unit torus with the complex unit circle. -/
def unitAddTorusCircleEquiv : UnitAddTorus (Fin r) ≃ (Fin r → Circle) where
  toFun x := fun i ↦ AddCircle.homeomorphCircle one_ne_zero (x i)
  invFun z := fun i ↦ (AddCircle.homeomorphCircle one_ne_zero).symm (z i)
  left_inv x := by
    funext i
    exact (AddCircle.homeomorphCircle one_ne_zero).symm_apply_apply (x i)
  right_inv z := by
    funext i
    exact (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply (z i)

theorem toCircle_sum_zsmul (c : Fin r → ℤ) (x : UnitAddTorus (Fin r)) :
    AddCircle.toCircle (∑ j, c j • x j) = ∏ j, AddCircle.toCircle (x j) ^ (c j) := by
  classical
  induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, AddCircle.toCircle_add,
        AddCircle.toCircle_zsmul, ih]

theorem unitAddTorusCircleEquiv_torusIntegerHom
    (M : Matrix (Fin r) (Fin r) ℤ) (x : UnitAddTorus (Fin r)) :
    unitAddTorusCircleEquiv (torusIntegerHom (M : Fin r → Fin r → ℤ) x) =
      circleTorusMonomialHom M (unitAddTorusCircleEquiv x) := by
  funext i
  change AddCircle.homeomorphCircle one_ne_zero (∑ j, M i j • x j) =
    ∏ j, (AddCircle.homeomorphCircle one_ne_zero (x j)) ^ (M i j)
  simp_rw [AddCircle.homeomorphCircle_apply]
  exact toCircle_sum_zsmul (fun j ↦ M i j) x

/-- Conjugacy identifies kernels of additive and multiplicative presentations of the compact torus. -/
def torusIntegerKernelEquiv (M : Matrix (Fin r) (Fin r) ℤ) :
    ↥((torusIntegerAddHom M).ker) ≃ ↥((circleTorusMonomialHom M).ker) where
  toFun x := ⟨unitAddTorusCircleEquiv x, by
    change circleTorusMonomialHom M (unitAddTorusCircleEquiv x) = 1
    rw [← unitAddTorusCircleEquiv_torusIntegerHom]
    change unitAddTorusCircleEquiv ((torusIntegerAddHom M) x) = 1
    rw [x.2]
    funext i
    simp [unitAddTorusCircleEquiv, AddCircle.homeomorphCircle_apply]⟩
  invFun z := ⟨unitAddTorusCircleEquiv.symm z, by
    apply unitAddTorusCircleEquiv.injective
    change unitAddTorusCircleEquiv
        (torusIntegerHom (M : Fin r → Fin r → ℤ) (unitAddTorusCircleEquiv.symm z)) =
      unitAddTorusCircleEquiv 0
    rw [unitAddTorusCircleEquiv_torusIntegerHom, unitAddTorusCircleEquiv.apply_symm_apply]
    rw [z.2]
    funext i
    simp [unitAddTorusCircleEquiv, AddCircle.homeomorphCircle_apply]⟩
  left_inv x := by
    apply Subtype.ext
    exact unitAddTorusCircleEquiv.symm_apply_apply (x : UnitAddTorus (Fin r))
  right_inv z := by
    apply Subtype.ext
    exact unitAddTorusCircleEquiv.apply_symm_apply (z : Fin r → Circle)

/-- Nonsingular integer endomorphism of the additive unit torus has `|det M|` deck points. -/
theorem card_ker_torusIntegerAddHom {M : Matrix (Fin r) (Fin r) ℤ} (hM : M.det ≠ 0) :
    Nat.card ((torusIntegerAddHom M).ker) = M.det.natAbs := by
  rw [Nat.card_congr (torusIntegerKernelEquiv M)]
  exact card_ker_circleTorusMonomialHom hM

/-- **Lemma 6.2, covering-degree form.** The `n`-fold Navier--Stokes phase covering has exactly
`14^n` deck points. -/
theorem card_ker_navierStokesCoverMatrix_pow (n : ℕ) :
    Nat.card ((torusIntegerAddHom
      (navierStokesCoverMatrix ^ n : Matrix (Fin 2) (Fin 2) ℤ)).ker) = 14 ^ n := by
  calc
    Nat.card ((torusIntegerAddHom
        (navierStokesCoverMatrix ^ n : Matrix (Fin 2) (Fin 2) ℤ)).ker) =
        ((navierStokesCoverMatrix ^ n).det).natAbs :=
      card_ker_torusIntegerAddHom (det_pow_navierStokesCoverMatrix_ne_zero n)
    _ = 14 ^ n := by
      rw [Matrix.det_pow, det_navierStokesCoverMatrix]
      simp

end

end GaloisForLFunctions.HTGeometry.NavierStokesTorusCoveringDegree
