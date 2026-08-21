/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebra
import GaloisForLFunctions.HTGeometry.ABHN.BrauerFoundations

/-!
# Simple quadratic cyclic Galois algebras

For a cyclic Galois extension of degree two and a nonzero parameter, the raw cyclic quotient is
simple.  The proof is direct: the quotient has a two-coefficient normal form, and commutation
with one coefficient on which the nontrivial Galois automorphism acts nontrivially isolates the
second coefficient.  This produces a unit in every nonzero two-sided ideal.

This supplies the non-norm part of the cyclic-algebra construction in degree two.  The analogous
arbitrary-degree normal-form descent remains separate infrastructure.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open Multiplicative

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

/-- Coefficients of a quadratic cyclic algebra acting diagonally in its companion
representation. -/
noncomputable def quadraticCyclicCoefficientMatrix (b : L) : Matrix (Fin 2) (Fin 2) L :=
  !![b, 0; 0, cyclicGaloisGenerator K L b]

/-- The companion matrix of the cyclic generator for a quadratic parameter. -/
noncomputable def quadraticCyclicGeneratorMatrix (a : K) : Matrix (Fin 2) (Fin 2) L :=
  !![0, algebraMap K L a; 1, 0]

/-- The diagonal coefficient action is a ring homomorphism. -/
noncomputable def quadraticCyclicCoefficientMatrixHom : L →+* Matrix (Fin 2) (Fin 2) L where
  toFun := quadraticCyclicCoefficientMatrix K L
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [quadraticCyclicCoefficientMatrix]
  map_mul' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quadraticCyclicCoefficientMatrix, Matrix.mul_apply]
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [quadraticCyclicCoefficientMatrix]
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [quadraticCyclicCoefficientMatrix]

/-- The companion matrix implements the generator action on coefficients. -/
theorem quadraticCyclicMatrix_base_comm (hdeg : Module.finrank K L = 2) (a : K) (b : L) :
    quadraticCyclicCoefficientMatrix K L (cyclicGaloisGenerator K L b) *
        quadraticCyclicGeneratorMatrix K L a =
      quadraticCyclicGeneratorMatrix K L a * quadraticCyclicCoefficientMatrix K L b := by
  have hsq : cyclicGaloisGenerator K L ^ 2 = 1 := by
    rw [← hdeg]
    exact cyclicGaloisGenerator_pow_finrank K L
  have hsq_apply : cyclicGaloisGenerator K L (cyclicGaloisGenerator K L b) = b := by
    change (cyclicGaloisGenerator K L ^ 2) b = b
    rw [hsq]
    rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quadraticCyclicCoefficientMatrix, quadraticCyclicGeneratorMatrix, Matrix.mul_apply,
      hsq_apply, mul_comm]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The companion matrix satisfies the quadratic parameter relation. -/
theorem quadraticCyclicMatrix_square (hdeg : Module.finrank K L = 2) (a : K) :
    quadraticCyclicGeneratorMatrix K L a ^ Module.finrank K L =
      quadraticCyclicCoefficientMatrix K L (algebraMap K L a) := by
  rw [hdeg, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quadraticCyclicCoefficientMatrix, quadraticCyclicGeneratorMatrix, Matrix.mul_apply]

/-- Matrix commutation for every nonnegative power of the cyclic generator. -/
theorem quadraticCyclicMatrix_power_comm (hdeg : Module.finrank K L = 2) (a : K)
    (q : ℕ) (b : L) :
    quadraticCyclicCoefficientMatrix K L ((cyclicGaloisGenerator K L ^ q) b) *
        quadraticCyclicGeneratorMatrix K L a ^ q =
      quadraticCyclicGeneratorMatrix K L a ^ q * quadraticCyclicCoefficientMatrix K L b := by
  induction q generalizing b with
  | zero => simp [quadraticCyclicCoefficientMatrix]
  | succ q ih =>
    rw [pow_succ, pow_succ]
    change quadraticCyclicCoefficientMatrix K L ((cyclicGaloisGenerator K L ^ q)
        (cyclicGaloisGenerator K L b)) *
          (quadraticCyclicGeneratorMatrix K L a ^ q * quadraticCyclicGeneratorMatrix K L a) = _
    rw [← mul_assoc, ih]
    rw [mul_assoc, quadraticCyclicMatrix_base_comm K L hdeg a]
    rw [← mul_assoc]

/-- The companion matrices satisfy the full skew commutation family needed by the universal
cyclic-algebra lift. -/
theorem quadraticCyclicMatrix_actions_commute (hdeg : Module.finrank K L = 2) (a : K)
    (m : Multiplicative ℕ) (b : L) :
    quadraticCyclicCoefficientMatrix K L
        ((cyclicPowerRingAut (cyclicGaloisGenerator K L).toRingEquiv m) b) *
      cyclicPowerMonoidHom (quadraticCyclicGeneratorMatrix K L a) m =
    cyclicPowerMonoidHom (quadraticCyclicGeneratorMatrix K L a) m *
      quadraticCyclicCoefficientMatrix K L b := by
  simp only [cyclicPowerRingAut, cyclicPowerMonoidHom]
  change quadraticCyclicCoefficientMatrix K L
      (((cyclicGaloisGenerator K L).toRingEquiv ^ toAdd m) b) *
        quadraticCyclicGeneratorMatrix K L a ^ toAdd m =
      quadraticCyclicGeneratorMatrix K L a ^ toAdd m * quadraticCyclicCoefficientMatrix K L b
  simpa [AlgEquiv.coe_pow] using
    quadraticCyclicMatrix_power_comm K L hdeg a (toAdd m) b

/-- A companion-matrix representation of the quadratic raw cyclic algebra. -/
noncomputable def quadraticCyclicGaloisAlgebraRepresentation
    (hdeg : Module.finrank K L = 2) (a : K) :
    cyclicGaloisAlgebra K L a →+* Matrix (Fin 2) (Fin 2) L :=
  cyclicAlgebraLift (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
    (algebraMap K L a) (quadraticCyclicCoefficientMatrixHom K L)
    (quadraticCyclicGeneratorMatrix K L a)
    (quadraticCyclicMatrix_actions_commute K L hdeg a)
    (quadraticCyclicMatrix_square K L hdeg a)

/-- A quadratic raw cyclic Galois algebra is nontrivial, including for parameters that are not
norms. -/
theorem quadraticCyclicGaloisAlgebra_one_ne_zero (hdeg : Module.finrank K L = 2) (a : K) :
    (1 : cyclicGaloisAlgebra K L a) ≠ 0 := by
  intro h
  have hmap := congrArg (quadraticCyclicGaloisAlgebraRepresentation K L hdeg a) h
  rw [map_one, map_zero] at hmap
  exact one_ne_zero hmap

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The bounded normal form in degree two has exactly the expected two coefficients. -/
theorem quadraticCyclicGaloisAlgebra_normalForm (hdeg : Module.finrank K L = 2) (a : K)
    (v : Fin (Module.finrank K L) → L) :
    let i0 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 0
    let i1 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 1
    cyclicGaloisAlgebraNormalFormLinearMap K L a v =
      cyclicGaloisAlgebraC K L a (v i0) +
        cyclicGaloisAlgebraC K L a (v i1) * cyclicGaloisAlgebraX K L a := by
  classical
  dsimp
  let i0 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 0
  let i1 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 1
  have hi01 : i0 ≠ i1 := by
    intro h
    have hval := congrArg Fin.val h
    simp [i0, i1] at hval
  have hcover (i : Fin (Module.finrank K L)) : i = i0 ∨ i = i1 := by
    have hi : i.val < 2 := by simpa [hdeg] using i.isLt
    have hcases : i.val = 0 ∨ i.val = 1 := by omega
    rcases hcases with h | h
    · left
      apply Fin.ext
      simpa [i0] using h
    · right
      apply Fin.ext
      simpa [i1] using h
  have hv : v = Pi.single i0 (v i0) + Pi.single i1 (v i1) := by
    funext i
    rcases hcover i with rfl | rfl
    · simp [hi01]
    · simp [hi01]
  rw [hv, map_add, cyclicGaloisAlgebraNormalFormLinearMap_single,
    cyclicGaloisAlgebraNormalFormLinearMap_single]
  simp [i0, i1]

/-- The quadratic generator moves some coefficient. -/
theorem quadraticCyclicGaloisGenerator_exists_not_fixed (hdeg : Module.finrank K L = 2) :
    ∃ b : L, cyclicGaloisGenerator K L b ≠ b := by
  by_contra h
  push Not at h
  have hgen : cyclicGaloisGenerator K L = 1 := by
    ext b
    exact h b
  have hbad : (1 : ℕ) = 2 := by
    simpa [hgen, hdeg] using cyclicGaloisGenerator_orderOf K L
  omega

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Commuting a quadratic normal form with a coefficient isolates its nonconstant coefficient. -/
theorem quadraticCyclicGaloisAlgebra_commutator_normalForm (a : K) (c0 c1 b : L) :
    (cyclicGaloisAlgebraC K L a c0 +
        cyclicGaloisAlgebraC K L a c1 * cyclicGaloisAlgebraX K L a) *
        cyclicGaloisAlgebraC K L a b -
      cyclicGaloisAlgebraC K L a b *
        (cyclicGaloisAlgebraC K L a c0 +
          cyclicGaloisAlgebraC K L a c1 * cyclicGaloisAlgebraX K L a) =
      cyclicGaloisAlgebraC K L a (c1 * (cyclicGaloisGenerator K L b - b)) *
        cyclicGaloisAlgebraX K L a := by
  rw [add_mul, mul_add, mul_assoc, cyclicAlgebraX_mul_cyclicAlgebraC]
  rw [cyclicAlgebraC_comm L (cyclicGaloisGenerator K L).toRingEquiv
    (Module.finrank K L) (algebraMap K L a) c0 b]
  simp only [← mul_assoc]
  rw [cyclicAlgebraC_mul, cyclicAlgebraC_mul, cyclicAlgebraC_mul]
  calc
    _ = (cyclicGaloisAlgebraC K L a (c1 * (cyclicGaloisGenerator K L b)) -
        cyclicGaloisAlgebraC K L a (b * c1)) * cyclicGaloisAlgebraX K L a := by
      rw [sub_mul, sub_eq_add_neg]
      simp only [cyclicGaloisAlgebraC, cyclicGaloisAlgebraX]
      have hsig : (cyclicGaloisGenerator K L).toRingEquiv b =
          cyclicGaloisGenerator K L b := rfl
      rw [hsig]
      abel
    _ = _ := by
      congr 1
      change cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
          (Module.finrank K L) (algebraMap K L a) (c1 * (cyclicGaloisGenerator K L b)) -
        cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
          (Module.finrank K L) (algebraMap K L a) (b * c1) =
        cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
          (Module.finrank K L) (algebraMap K L a)
            (c1 * (cyclicGaloisGenerator K L b - b))
      rw [← map_sub]
      ring_nf

/-- Every nonzero parameter quadratic cyclic Galois algebra is a simple ring. -/
theorem isSimpleRing_cyclicGaloisAlgebra_of_finrank_eq_two
    (hdeg : Module.finrank K L = 2) (a : K) (ha : a ≠ 0) :
    IsSimpleRing (cyclicGaloisAlgebra K L a) := by
  letI : Nontrivial (cyclicGaloisAlgebra K L a) :=
    ⟨0, 1, (quadraticCyclicGaloisAlgebra_one_ne_zero K L hdeg a).symm⟩
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro I
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  rw [← I.one_mem_iff]
  obtain ⟨x, hxI, hx0 : x ≠ 0⟩ :=
    SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI : (⊥ : TwoSidedIdeal
      (cyclicGaloisAlgebra K L a)) < I)
  let i0 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 0
  let i1 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 1
  have one_mem_of_isUnit_mem : ∀ {z : cyclicGaloisAlgebra K L a}, IsUnit z → z ∈ I →
      (1 : cyclicGaloisAlgebra K L a) ∈ I := by
    intro z hz hzI
    have hu : (↑(hz.unit⁻¹) : cyclicGaloisAlgebra K L a) * z = 1 := by
      calc
        (↑(hz.unit⁻¹) : cyclicGaloisAlgebra K L a) * z =
            (↑(hz.unit⁻¹) : cyclicGaloisAlgebra K L a) * (hz.unit : cyclicGaloisAlgebra K L a) :=
          congrArg (fun w : cyclicGaloisAlgebra K L a =>
            (↑(hz.unit⁻¹) : cyclicGaloisAlgebra K L a) * w) hz.unit_spec.symm
        _ = 1 := Units.inv_mul hz.unit
    rw [← hu]
    exact I.mul_mem_left _ _ hzI
  obtain ⟨v, hv⟩ := cyclicGaloisAlgebraNormalFormLinearMap_surjective K L a x
  have hform : cyclicGaloisAlgebraNormalFormLinearMap K L a v =
      cyclicGaloisAlgebraC K L a (v i0) +
        cyclicGaloisAlgebraC K L a (v i1) * cyclicGaloisAlgebraX K L a := by
    simpa [i0, i1] using quadraticCyclicGaloisAlgebra_normalForm K L hdeg a v
  have hxform : x = cyclicGaloisAlgebraC K L a (v i0) +
      cyclicGaloisAlgebraC K L a (v i1) * cyclicGaloisAlgebraX K L a :=
    hv.symm.trans hform
  by_cases h1 : v i1 = 0
  · have h0 : v i0 ≠ 0 := by
      intro h0
      apply hx0
      rw [← hv]
      have hvzero : v = 0 := by
        funext i
        have hi : i = i0 ∨ i = i1 := by
          have hlt : i.val < 2 := by simpa [hdeg] using i.isLt
          have hcases : i.val = 0 ∨ i.val = 1 := by omega
          rcases hcases with h | h
          · left
            apply Fin.ext
            simpa [i0] using h
          · right
            apply Fin.ext
            simpa [i1] using h
        rcases hi with rfl | rfl <;> simp [h0, h1]
      rw [hvzero, map_zero]
    have hcx : IsUnit (cyclicGaloisAlgebraC K L a (v i0)) := by
      change IsUnit (cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
        (Module.finrank K L) (algebraMap K L a) (v i0))
      exact IsUnit.map _ (Ne.isUnit h0)
    apply one_mem_of_isUnit_mem (z := x)
    · rw [hxform, h1]
      change IsUnit ((cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
        (Module.finrank K L) (algebraMap K L a)) (v i0) +
          (cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
            (Module.finrank K L) (algebraMap K L a)) 0 * cyclicGaloisAlgebraX K L a)
      rw [map_zero, zero_mul, add_zero]
      exact hcx
    · exact hxI
  · obtain ⟨b, hb⟩ := quadraticCyclicGaloisGenerator_exists_not_fixed K L hdeg
    have hd : v i1 * (cyclicGaloisGenerator K L b - b) ≠ 0 :=
      mul_ne_zero h1 (sub_ne_zero.mpr hb)
    have hcomm : x * cyclicGaloisAlgebraC K L a b -
        cyclicGaloisAlgebraC K L a b * x ∈ I :=
      I.sub_mem (I.mul_mem_right _ _ hxI) (I.mul_mem_left _ _ hxI)
    have hunit_mem : cyclicGaloisAlgebraC K L a
        (v i1 * (cyclicGaloisGenerator K L b - b)) * cyclicGaloisAlgebraX K L a ∈ I := by
      rw [hxform] at hcomm
      rw [quadraticCyclicGaloisAlgebra_commutator_normalForm K L a (v i0) (v i1) b] at hcomm
      exact hcomm
    apply one_mem_of_isUnit_mem (z := cyclicGaloisAlgebraC K L a
      (v i1 * (cyclicGaloisGenerator K L b - b)) * cyclicGaloisAlgebraX K L a)
    · apply IsUnit.mul
      · change IsUnit (cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
          (Module.finrank K L) (algebraMap K L a)
            (v i1 * (cyclicGaloisGenerator K L b - b)))
        exact IsUnit.map _ (Ne.isUnit hd)
      · exact cyclicGaloisAlgebraX_isUnit K L a ha
    · exact hunit_mem

/-- Every degree-two cohomological unit parameter has a simple raw quadratic cyclic algebra. -/
theorem isSimpleRing_cyclicGaloisAlgebra_of_finrank_eq_two_unitParameter
    (hdeg : Module.finrank K L = 2) (a : Additive Kˣ) :
    IsSimpleRing (cyclicGaloisAlgebra K L (a.toMul : K)) :=
  isSimpleRing_cyclicGaloisAlgebra_of_finrank_eq_two K L hdeg (a.toMul : K) a.toMul.ne_zero

omit [IsGalois K L] in
/-- A nonzero coefficient times the quadratic cyclic generator is a unit. -/
theorem quadraticCyclicGaloisAlgebra_coefficient_mul_X_isUnit
    (a : K) (ha : a ≠ 0) (d : L) (hd : d ≠ 0) :
    IsUnit (cyclicGaloisAlgebraC K L a d * cyclicGaloisAlgebraX K L a) := by
  apply IsUnit.mul
  · change IsUnit (cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
      (Module.finrank K L) (algebraMap K L a) d)
    exact IsUnit.map _ (Ne.isUnit hd)
  · exact cyclicGaloisAlgebraX_isUnit K L a ha

/-- Every central element of a nonzero quadratic cyclic algebra comes from the base field. -/
theorem quadraticCyclicGaloisAlgebra_center_exists_base
    (hdeg : Module.finrank K L = 2) (a : K) (ha : a ≠ 0)
    (x : cyclicGaloisAlgebra K L a)
    (hx : ∀ y : cyclicGaloisAlgebra K L a, y * x = x * y) :
    ∃ k : K, x = algebraMap K (cyclicGaloisAlgebra K L a) k := by
  letI : Nontrivial (cyclicGaloisAlgebra K L a) :=
    ⟨0, 1, (quadraticCyclicGaloisAlgebra_one_ne_zero K L hdeg a).symm⟩
  let i0 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 0
  let i1 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 1
  obtain ⟨v, hv⟩ := cyclicGaloisAlgebraNormalFormLinearMap_surjective K L a x
  have hform : cyclicGaloisAlgebraNormalFormLinearMap K L a v =
      cyclicGaloisAlgebraC K L a (v i0) +
        cyclicGaloisAlgebraC K L a (v i1) * cyclicGaloisAlgebraX K L a := by
    simpa [i0, i1] using quadraticCyclicGaloisAlgebra_normalForm K L hdeg a v
  have hxform : x = cyclicGaloisAlgebraC K L a (v i0) +
      cyclicGaloisAlgebraC K L a (v i1) * cyclicGaloisAlgebraX K L a :=
    hv.symm.trans hform
  obtain ⟨b, hb⟩ := quadraticCyclicGaloisGenerator_exists_not_fixed K L hdeg
  have hcomm : x * cyclicGaloisAlgebraC K L a b -
      cyclicGaloisAlgebraC K L a b * x = 0 :=
    sub_eq_zero.mpr (hx _).symm
  have h1 : v i1 = 0 := by
    by_contra h1
    have hd : v i1 * (cyclicGaloisGenerator K L b - b) ≠ 0 :=
      mul_ne_zero h1 (sub_ne_zero.mpr hb)
    have hzero : cyclicGaloisAlgebraC K L a
        (v i1 * (cyclicGaloisGenerator K L b - b)) * cyclicGaloisAlgebraX K L a = 0 := by
      rw [hxform, quadraticCyclicGaloisAlgebra_commutator_normalForm] at hcomm
      exact hcomm
    have hu := quadraticCyclicGaloisAlgebra_coefficient_mul_X_isUnit K L a ha _ hd
    rw [hzero] at hu
    exact not_isUnit_zero hu
  have hx0 : x = cyclicGaloisAlgebraC K L a (v i0) := by
    rw [hxform, h1]
    change (cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
      (Module.finrank K L) (algebraMap K L a)) (v i0) +
        (cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
          (Module.finrank K L) (algebraMap K L a)) 0 * cyclicGaloisAlgebraX K L a = _
    rw [map_zero, zero_mul, add_zero]
    rfl
  have hX : cyclicGaloisAlgebraX K L a * cyclicGaloisAlgebraC K L a (v i0) =
      cyclicGaloisAlgebraC K L a (v i0) * cyclicGaloisAlgebraX K L a := by
    rw [← hx0]
    exact hx _
  have hdiffEq : cyclicGaloisAlgebraC K L a (cyclicGaloisGenerator K L (v i0)) *
      cyclicGaloisAlgebraX K L a =
      cyclicGaloisAlgebraC K L a (v i0) * cyclicGaloisAlgebraX K L a := by
    change cyclicAlgebraC (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
        (algebraMap K L a) (cyclicGaloisGenerator K L (v i0)) *
        cyclicAlgebraX (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
          (algebraMap K L a) =
      cyclicAlgebraC (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
        (algebraMap K L a) (v i0) *
        cyclicAlgebraX (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
          (algebraMap K L a)
    rw [← show (cyclicGaloisGenerator K L).toRingEquiv (v i0) =
      cyclicGaloisGenerator K L (v i0) from rfl]
    rw [← cyclicAlgebraX_mul_cyclicAlgebraC]
    exact hX
  have hfix : cyclicGaloisGenerator K L (v i0) = v i0 := by
    by_contra hne
    have hzero : cyclicGaloisAlgebraC K L
        a (cyclicGaloisGenerator K L (v i0) - v i0) * cyclicGaloisAlgebraX K L a = 0 := by
      change (cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
        (Module.finrank K L) (algebraMap K L a)
          (cyclicGaloisGenerator K L (v i0) - v i0)) * cyclicGaloisAlgebraX K L a = 0
      rw [map_sub, sub_mul]
      exact sub_eq_zero.mpr hdiffEq
    have hu := quadraticCyclicGaloisAlgebra_coefficient_mul_X_isUnit K L a ha _
      (sub_ne_zero.mpr hne)
    rw [hzero] at hu
    exact not_isUnit_zero hu
  have hfixed : ∀ sigma : Gal(L/K), sigma (v i0) = v i0 := by
    intro sigma
    let H : Subgroup Gal(L/K) := MulAction.stabilizer Gal(L/K) (v i0)
    have hgen : cyclicGaloisGenerator K L ∈ H := by
      change cyclicGaloisGenerator K L (v i0) = v i0
      exact hfix
    exact MulAction.mem_stabilizer_iff.mp
      ((Subgroup.zpowers_le.mpr hgen) (cyclicGaloisGenerator_spec K L sigma))
  obtain ⟨k, hk⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (v i0)).mpr hfixed
  refine ⟨k, ?_⟩
  rw [hx0, cyclicGaloisAlgebra_algebraMap_apply]
  exact congrArg (cyclicGaloisAlgebraC K L a) hk.symm

/-- A nonzero quadratic cyclic Galois algebra has center exactly its base field. -/
theorem quadraticCyclicGaloisAlgebra_isCentral
    (hdeg : Module.finrank K L = 2) (a : K) (ha : a ≠ 0) :
    Algebra.IsCentral K (cyclicGaloisAlgebra K L a) where
  out := by
    intro x hx
    rw [Algebra.mem_bot]
    obtain ⟨k, hk⟩ := quadraticCyclicGaloisAlgebra_center_exists_base K L hdeg a ha x
      (Subalgebra.mem_center_iff.mp hx)
    exact ⟨k, hk.symm⟩

/-- The raw cyclic algebra for every nonzero quadratic parameter is a finite-dimensional central
simple algebra. -/
noncomputable def quadraticCyclicGaloisAlgebraCSA
    (hdeg : Module.finrank K L = 2) (a : K) (ha : a ≠ 0) : CSA K where
  carrier := cyclicGaloisAlgebra K L a
  isCentral := quadraticCyclicGaloisAlgebra_isCentral K L hdeg a ha
  isSimple := isSimpleRing_cyclicGaloisAlgebra_of_finrank_eq_two K L hdeg a ha
  fin_dim := cyclicGaloisAlgebra_finiteDimensional K L a

/-- A degree-two cohomological unit parameter canonically determines a quadratic central simple
algebra. -/
noncomputable def quadraticCyclicGaloisH2ParameterCSA
    (hdeg : Module.finrank K L = 2) (a : Additive Kˣ) : CSA K :=
  quadraticCyclicGaloisAlgebraCSA K L hdeg (a.toMul : K) a.toMul.ne_zero

end GaloisForLFunctions.HTGeometry.ABHN
