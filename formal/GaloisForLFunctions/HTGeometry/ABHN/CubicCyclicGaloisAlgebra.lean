/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraIdealReduction
import GaloisForLFunctions.HTGeometry.ABHN.BrauerFoundations

/-!
# Simple cubic cyclic Galois algebras

For a cyclic Galois extension of degree three and a nonzero parameter, the raw cyclic quotient is
simple. A cubic companion representation proves that the quotient is nontrivial. Every nonzero
two-sided ideal contains a normal form; one or two twisted commutators isolate one nonzero
coefficient, hence a unit. This extends the closed quadratic cyclic-algebra bridge to degree
three without assuming normal-form uniqueness.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open Multiplicative

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

/-- Coefficients of a cubic cyclic algebra acting diagonally in its companion representation. -/
noncomputable def cubicCyclicCoefficientMatrix (b : L) : Matrix (Fin 3) (Fin 3) L :=
  !![b, 0, 0; 0, (cyclicGaloisGenerator K L ^ 2) b, 0;
    0, 0, cyclicGaloisGenerator K L b]

/-- The companion matrix of the cubic cyclic generator. -/
noncomputable def cubicCyclicGeneratorMatrix (a : K) : Matrix (Fin 3) (Fin 3) L :=
  !![0, 0, algebraMap K L a; 1, 0, 0; 0, 1, 0]

/-- The cubic diagonal coefficient action is a ring homomorphism. -/
noncomputable def cubicCyclicCoefficientMatrixHom : L →+* Matrix (Fin 3) (Fin 3) L where
  toFun := cubicCyclicCoefficientMatrix K L
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cubicCyclicCoefficientMatrix]
  map_mul' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cubicCyclicCoefficientMatrix, Matrix.mul_apply, Fin.sum_univ_succ, pow_two]
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cubicCyclicCoefficientMatrix]
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cubicCyclicCoefficientMatrix, pow_two]

/-- The cubic companion matrix implements the Galois generator action on coefficients. -/
theorem cubicCyclicMatrix_base_comm (hdeg : Module.finrank K L = 3) (a : K) (b : L) :
    cubicCyclicCoefficientMatrix K L (cyclicGaloisGenerator K L b) *
        cubicCyclicGeneratorMatrix K L a =
      cubicCyclicGeneratorMatrix K L a * cubicCyclicCoefficientMatrix K L b := by
  have hcub : cyclicGaloisGenerator K L ^ 3 = 1 := by
    rw [← hdeg]
    exact cyclicGaloisGenerator_pow_finrank K L
  have hcub_apply : (cyclicGaloisGenerator K L ^ 3) b = b := by
    rw [hcub]
    rfl
  have hcub_apply' : cyclicGaloisGenerator K L
      (cyclicGaloisGenerator K L (cyclicGaloisGenerator K L b)) = b := by
    change (cyclicGaloisGenerator K L ^ 3) b = b
    exact hcub_apply
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicCyclicCoefficientMatrix, cubicCyclicGeneratorMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ, pow_two, hcub_apply', mul_comm]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The cubic companion matrix satisfies the cubic parameter relation. -/
theorem cubicCyclicMatrix_cube (hdeg : Module.finrank K L = 3) (a : K) :
    cubicCyclicGeneratorMatrix K L a ^ Module.finrank K L =
      cubicCyclicCoefficientMatrix K L (algebraMap K L a) := by
  rw [hdeg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicCyclicCoefficientMatrix, cubicCyclicGeneratorMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ, pow_succ, Algebra.smul_def]

/-- Matrix commutation for every nonnegative power of the cubic cyclic generator. -/
theorem cubicCyclicMatrix_power_comm (hdeg : Module.finrank K L = 3) (a : K)
    (q : ℕ) (b : L) :
    cubicCyclicCoefficientMatrix K L ((cyclicGaloisGenerator K L ^ q) b) *
        cubicCyclicGeneratorMatrix K L a ^ q =
      cubicCyclicGeneratorMatrix K L a ^ q * cubicCyclicCoefficientMatrix K L b := by
  induction q generalizing b with
  | zero => simp [cubicCyclicCoefficientMatrix]
  | succ q ih =>
    rw [pow_succ, pow_succ]
    change cubicCyclicCoefficientMatrix K L ((cyclicGaloisGenerator K L ^ q)
        (cyclicGaloisGenerator K L b)) *
          (cubicCyclicGeneratorMatrix K L a ^ q * cubicCyclicGeneratorMatrix K L a) = _
    rw [← mul_assoc, ih]
    rw [mul_assoc, cubicCyclicMatrix_base_comm K L hdeg a]
    rw [← mul_assoc]

/-- The cubic companion matrices satisfy the skew commutation family for the universal lift. -/
theorem cubicCyclicMatrix_actions_commute (hdeg : Module.finrank K L = 3) (a : K)
    (m : Multiplicative ℕ) (b : L) :
    cubicCyclicCoefficientMatrix K L
        ((cyclicPowerRingAut (cyclicGaloisGenerator K L).toRingEquiv m) b) *
      cyclicPowerMonoidHom (cubicCyclicGeneratorMatrix K L a) m =
    cyclicPowerMonoidHom (cubicCyclicGeneratorMatrix K L a) m *
      cubicCyclicCoefficientMatrix K L b := by
  simp only [cyclicPowerRingAut, cyclicPowerMonoidHom]
  change cubicCyclicCoefficientMatrix K L
      (((cyclicGaloisGenerator K L).toRingEquiv ^ toAdd m) b) *
        cubicCyclicGeneratorMatrix K L a ^ toAdd m =
      cubicCyclicGeneratorMatrix K L a ^ toAdd m * cubicCyclicCoefficientMatrix K L b
  simpa [AlgEquiv.coe_pow] using
    cubicCyclicMatrix_power_comm K L hdeg a (toAdd m) b

/-- A companion-matrix representation of the raw cubic cyclic Galois algebra. -/
noncomputable def cubicCyclicGaloisAlgebraRepresentation
    (hdeg : Module.finrank K L = 3) (a : K) :
    cyclicGaloisAlgebra K L a →+* Matrix (Fin 3) (Fin 3) L :=
  cyclicAlgebraLift (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
    (algebraMap K L a) (cubicCyclicCoefficientMatrixHom K L)
    (cubicCyclicGeneratorMatrix K L a)
    (cubicCyclicMatrix_actions_commute K L hdeg a)
    (cubicCyclicMatrix_cube K L hdeg a)

/-- A cubic raw cyclic Galois algebra is nontrivial, including for non-norm parameters. -/
theorem cubicCyclicGaloisAlgebra_one_ne_zero (hdeg : Module.finrank K L = 3) (a : K) :
    (1 : cyclicGaloisAlgebra K L a) ≠ 0 := by
  intro h
  have hmap := congrArg (cubicCyclicGaloisAlgebraRepresentation K L hdeg a) h
  rw [map_one, map_zero] at hmap
  exact one_ne_zero hmap

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A bounded cubic normal form has its three expected coefficients. -/
theorem cubicCyclicGaloisAlgebra_normalForm (hdeg : Module.finrank K L = 3) (a : K)
    (v : Fin (Module.finrank K L) → L) :
    let i0 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 0
    let i1 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 1
    let i2 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 2
    cyclicGaloisAlgebraNormalFormLinearMap K L a v =
      cyclicGaloisAlgebraC K L a (v i0) +
        cyclicGaloisAlgebraC K L a (v i1) * cyclicGaloisAlgebraX K L a +
          cyclicGaloisAlgebraC K L a (v i2) * cyclicGaloisAlgebraX K L a ^ 2 := by
  classical
  dsimp
  let i0 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 0
  let i1 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 1
  let i2 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 2
  have hi01 : i0 ≠ i1 := by
    intro h
    have hval := congrArg Fin.val h
    simp [i0, i1] at hval
  have hi02 : i0 ≠ i2 := by
    intro h
    have hval := congrArg Fin.val h
    simp [i0, i2] at hval
  have hi12 : i1 ≠ i2 := by
    intro h
    have hval := congrArg Fin.val h
    simp [i1, i2] at hval
  have hcover (i : Fin (Module.finrank K L)) : i = i0 ∨ i = i1 ∨ i = i2 := by
    have hi : i.val < 3 := by simpa [hdeg] using i.isLt
    have hcases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases hcases with h | h | h
    · left
      apply Fin.ext
      simpa [i0] using h
    · right; left
      apply Fin.ext
      simpa [i1] using h
    · right; right
      apply Fin.ext
      simpa [i2] using h
  have hv : v = Pi.single i0 (v i0) + Pi.single i1 (v i1) + Pi.single i2 (v i2) := by
    funext i
    rcases hcover i with rfl | rfl | rfl <;> simp [hi01, hi02, hi12]
  rw [hv, map_add, map_add, cyclicGaloisAlgebraNormalFormLinearMap_single,
    cyclicGaloisAlgebraNormalFormLinearMap_single,
    cyclicGaloisAlgebraNormalFormLinearMap_single]
  simp [i0, i1, i2]

/-- Every nonzero cubic cyclic Galois algebra is simple. -/
theorem isSimpleRing_cyclicGaloisAlgebra_of_finrank_eq_three
    (hdeg : Module.finrank K L = 3) (a : K) (ha : a ≠ 0) :
    IsSimpleRing (cyclicGaloisAlgebra K L a) := by
  letI : Nontrivial (cyclicGaloisAlgebra K L a) :=
    ⟨0, 1, (cubicCyclicGaloisAlgebra_one_ne_zero K L hdeg a).symm⟩
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
  let i2 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 2
  have hi01 : i0 ≠ i1 := by
    intro h
    have hval := congrArg Fin.val h
    simp [i0, i1] at hval
  have hi02 : i0 ≠ i2 := by
    intro h
    have hval := congrArg Fin.val h
    simp [i0, i2] at hval
  have hi12 : i1 ≠ i2 := by
    intro h
    have hval := congrArg Fin.val h
    simp [i1, i2] at hval
  have hcover (i : Fin (Module.finrank K L)) : i = i0 ∨ i = i1 ∨ i = i2 := by
    have hi : i.val < 3 := by simpa [hdeg] using i.isLt
    have hcases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases hcases with h | h | h
    · left
      apply Fin.ext
      simpa [i0] using h
    · right; left
      apply Fin.ext
      simpa [i1] using h
    · right; right
      apply Fin.ext
      simpa [i2] using h
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
  have normal_mem_twisted (j : Fin (Module.finrank K L)) (b : L)
      (u : Fin (Module.finrank K L) → L)
      (huI : cyclicGaloisAlgebraNormalFormLinearMap K L a u ∈ I) :
      cyclicGaloisAlgebraNormalFormLinearMap K L a
          (cyclicGaloisAlgebraTwistedCommutatorCoefficients K L j b u) ∈ I := by
    rw [← cyclicGaloisAlgebraNormalForm_twistedCommutator]
    exact I.sub_mem (I.mul_mem_right _ _ huI) (I.mul_mem_left _ _ huI)
  by_cases h2 : v i2 = 0
  · by_cases h1 : v i1 = 0
    · have h0 : v i0 ≠ 0 := by
        intro h0
        apply hx0
        rw [← hv]
        have hvzero : v = 0 := by
          funext i
          rcases hcover i with rfl | rfl | rfl <;> simp [h0, h1, h2]
        rw [hvzero, map_zero]
      have hsupp : cyclicGaloisAlgebraCoefficientSupport K L v = {i0} := by
        ext i
        rcases hcover i with rfl | rfl | rfl <;>
          simp [mem_cyclicGaloisAlgebraCoefficientSupport, h0, h1, h2, hi01.symm, hi02.symm]
      have hu : IsUnit (cyclicGaloisAlgebraNormalFormLinearMap K L a v) :=
        cyclicGaloisAlgebraNormalForm_isUnit_of_coefficientSupport_card_eq_one K L a ha v
          (by rw [hsupp]; simp)
      exact one_mem_of_isUnit_mem hu (by simpa [hv] using hxI)
    · obtain ⟨b, hb⟩ := cyclicGaloisGenerator_pow_exists_apply_ne K L i1 i0 hi01.symm
      let w := cyclicGaloisAlgebraTwistedCommutatorCoefficients K L i0 b v
      have hwI : cyclicGaloisAlgebraNormalFormLinearMap K L a w ∈ I := by
        exact normal_mem_twisted i0 b v (by simpa [hv] using hxI)
      have hw1 : w i1 ≠ 0 := by
        exact cyclicGaloisAlgebraTwistedCommutatorCoefficients_apply_ne_zero K L i0 i1 b v h1 hb
      have hw0 : w i0 = 0 :=
        cyclicGaloisAlgebraTwistedCommutatorCoefficients_apply_self K L i0 b v
      have hw2 : w i2 = 0 := by
        simp [w, cyclicGaloisAlgebraTwistedCommutatorCoefficients, h2]
      have hsupp : cyclicGaloisAlgebraCoefficientSupport K L w = {i1} := by
        ext i
        rcases hcover i with rfl | rfl | rfl <;>
          simp [mem_cyclicGaloisAlgebraCoefficientSupport, hw0, hw1, hw2, hi01, hi12.symm]
      have hu : IsUnit (cyclicGaloisAlgebraNormalFormLinearMap K L a w) :=
        cyclicGaloisAlgebraNormalForm_isUnit_of_coefficientSupport_card_eq_one K L a ha w
          (by rw [hsupp]; simp)
      exact one_mem_of_isUnit_mem hu hwI
  · obtain ⟨b0, hb0⟩ := cyclicGaloisGenerator_pow_exists_apply_ne K L i2 i0 hi02.symm
    obtain ⟨b1, hb1⟩ := cyclicGaloisGenerator_pow_exists_apply_ne K L i2 i1 hi12.symm
    let w := cyclicGaloisAlgebraTwistedCommutatorCoefficients K L i0 b0 v
    let z := cyclicGaloisAlgebraTwistedCommutatorCoefficients K L i1 b1 w
    have hwI : cyclicGaloisAlgebraNormalFormLinearMap K L a w ∈ I := by
      exact normal_mem_twisted i0 b0 v (by simpa [hv] using hxI)
    have hzI : cyclicGaloisAlgebraNormalFormLinearMap K L a z ∈ I := by
      exact normal_mem_twisted i1 b1 w hwI
    have hw2 : w i2 ≠ 0 := by
      exact cyclicGaloisAlgebraTwistedCommutatorCoefficients_apply_ne_zero K L i0 i2 b0 v h2 hb0
    have hz2 : z i2 ≠ 0 := by
      exact cyclicGaloisAlgebraTwistedCommutatorCoefficients_apply_ne_zero K L i1 i2 b1 w hw2 hb1
    have hz0 : z i0 = 0 := by
      have hw0 : w i0 = 0 :=
        cyclicGaloisAlgebraTwistedCommutatorCoefficients_apply_self K L i0 b0 v
      simp [z, cyclicGaloisAlgebraTwistedCommutatorCoefficients, hw0]
    have hz1 : z i1 = 0 :=
      cyclicGaloisAlgebraTwistedCommutatorCoefficients_apply_self K L i1 b1 w
    have hsupp : cyclicGaloisAlgebraCoefficientSupport K L z = {i2} := by
      ext i
      rcases hcover i with rfl | rfl | rfl <;>
        simp [mem_cyclicGaloisAlgebraCoefficientSupport, hz0, hz1, hz2, hi02, hi12]
    have hu : IsUnit (cyclicGaloisAlgebraNormalFormLinearMap K L a z) :=
      cyclicGaloisAlgebraNormalForm_isUnit_of_coefficientSupport_card_eq_one K L a ha z
        (by rw [hsupp]; simp)
    exact one_mem_of_isUnit_mem hu hzI

omit [IsGalois K L] in
/-- A nonzero coefficient times the cubic cyclic generator is a unit. -/
theorem cubicCyclicGaloisAlgebra_coefficient_mul_X_isUnit
    (a : K) (ha : a ≠ 0) (d : L) (hd : d ≠ 0) :
    IsUnit (cyclicGaloisAlgebraC K L a d * cyclicGaloisAlgebraX K L a) := by
  apply IsUnit.mul
  · change IsUnit (cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
      (Module.finrank K L) (algebraMap K L a) d)
    exact IsUnit.map _ (Ne.isUnit hd)
  · exact cyclicGaloisAlgebraX_isUnit K L a ha

/-- Every central element of a nonzero cubic cyclic algebra comes from the base field.

Commuting with coefficients makes the degree-zero twisted commutator vanish. A second twisted
commutator isolates a putative quadratic coefficient as a unit, forcing it to vanish; the same
argument removes the linear coefficient. -/
theorem cubicCyclicGaloisAlgebra_center_exists_base
    (hdeg : Module.finrank K L = 3) (a : K) (ha : a ≠ 0)
    (x : cyclicGaloisAlgebra K L a)
    (hx : ∀ y : cyclicGaloisAlgebra K L a, y * x = x * y) :
    ∃ k : K, x = algebraMap K (cyclicGaloisAlgebra K L a) k := by
  letI : Nontrivial (cyclicGaloisAlgebra K L a) :=
    ⟨0, 1, (cubicCyclicGaloisAlgebra_one_ne_zero K L hdeg a).symm⟩
  let i0 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 0
  let i1 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 1
  let i2 : Fin (Module.finrank K L) := Fin.cast hdeg.symm 2
  have hi01 : i0 ≠ i1 := by
    intro h
    have hval := congrArg Fin.val h
    simp [i0, i1] at hval
  have hi02 : i0 ≠ i2 := by
    intro h
    have hval := congrArg Fin.val h
    simp [i0, i2] at hval
  have hi12 : i1 ≠ i2 := by
    intro h
    have hval := congrArg Fin.val h
    simp [i1, i2] at hval
  have hcover (i : Fin (Module.finrank K L)) : i = i0 ∨ i = i1 ∨ i = i2 := by
    have hi : i.val < 3 := by simpa [hdeg] using i.isLt
    have hcases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases hcases with h | h | h
    · left
      apply Fin.ext
      simpa [i0] using h
    · right; left
      apply Fin.ext
      simpa [i1] using h
    · right; right
      apply Fin.ext
      simpa [i2] using h
  obtain ⟨v, hv⟩ := cyclicGaloisAlgebraNormalFormLinearMap_surjective K L a x
  have hform : cyclicGaloisAlgebraNormalFormLinearMap K L a v =
      cyclicGaloisAlgebraC K L a (v i0) +
        cyclicGaloisAlgebraC K L a (v i1) * cyclicGaloisAlgebraX K L a +
          cyclicGaloisAlgebraC K L a (v i2) * cyclicGaloisAlgebraX K L a ^ 2 := by
    simpa [i0, i1, i2] using cubicCyclicGaloisAlgebra_normalForm K L hdeg a v
  have hxform : x = cyclicGaloisAlgebraC K L a (v i0) +
      cyclicGaloisAlgebraC K L a (v i1) * cyclicGaloisAlgebraX K L a +
        cyclicGaloisAlgebraC K L a (v i2) * cyclicGaloisAlgebraX K L a ^ 2 :=
    hv.symm.trans hform
  have normal_twisted_zero (b : L) :
      cyclicGaloisAlgebraNormalFormLinearMap K L a
          (cyclicGaloisAlgebraTwistedCommutatorCoefficients K L i0 b v) = 0 := by
    rw [← cyclicGaloisAlgebraNormalForm_twistedCommutator, hv]
    change x * cyclicGaloisAlgebraC K L a b - cyclicGaloisAlgebraC K L a b * x = 0
    exact sub_eq_zero.mpr (hx _).symm
  have h2 : v i2 = 0 := by
    by_contra h2
    obtain ⟨b0, hb0⟩ := cyclicGaloisGenerator_pow_exists_apply_ne K L i2 i0 hi02.symm
    obtain ⟨b1, hb1⟩ := cyclicGaloisGenerator_pow_exists_apply_ne K L i2 i1 hi12.symm
    let w := cyclicGaloisAlgebraTwistedCommutatorCoefficients K L i0 b0 v
    let z := cyclicGaloisAlgebraTwistedCommutatorCoefficients K L i1 b1 w
    have hwzero : cyclicGaloisAlgebraNormalFormLinearMap K L a w = 0 := by
      exact normal_twisted_zero b0
    have hzzero : cyclicGaloisAlgebraNormalFormLinearMap K L a z = 0 := by
      rw [← cyclicGaloisAlgebraNormalForm_twistedCommutator, hwzero]
      simp
    have hw2 : w i2 ≠ 0 := by
      exact cyclicGaloisAlgebraTwistedCommutatorCoefficients_apply_ne_zero K L i0 i2 b0 v h2 hb0
    have hz2 : z i2 ≠ 0 := by
      exact cyclicGaloisAlgebraTwistedCommutatorCoefficients_apply_ne_zero K L i1 i2 b1 w hw2 hb1
    have hz0 : z i0 = 0 := by
      have hw0 : w i0 = 0 :=
        cyclicGaloisAlgebraTwistedCommutatorCoefficients_apply_self K L i0 b0 v
      simp [z, cyclicGaloisAlgebraTwistedCommutatorCoefficients, hw0]
    have hz1 : z i1 = 0 :=
      cyclicGaloisAlgebraTwistedCommutatorCoefficients_apply_self K L i1 b1 w
    have hsupp : cyclicGaloisAlgebraCoefficientSupport K L z = {i2} := by
      ext i
      rcases hcover i with rfl | rfl | rfl <;>
        simp [mem_cyclicGaloisAlgebraCoefficientSupport, hz0, hz1, hz2, hi02, hi12]
    have hu : IsUnit (cyclicGaloisAlgebraNormalFormLinearMap K L a z) :=
      cyclicGaloisAlgebraNormalForm_isUnit_of_coefficientSupport_card_eq_one K L a ha z
        (by rw [hsupp]; simp)
    rw [hzzero] at hu
    exact not_isUnit_zero hu
  have h1 : v i1 = 0 := by
    by_contra h1
    obtain ⟨b, hb⟩ := cyclicGaloisGenerator_pow_exists_apply_ne K L i1 i0 hi01.symm
    let w := cyclicGaloisAlgebraTwistedCommutatorCoefficients K L i0 b v
    have hwzero : cyclicGaloisAlgebraNormalFormLinearMap K L a w = 0 := by
      exact normal_twisted_zero b
    have hw1 : w i1 ≠ 0 := by
      exact cyclicGaloisAlgebraTwistedCommutatorCoefficients_apply_ne_zero K L i0 i1 b v h1 hb
    have hw0 : w i0 = 0 :=
      cyclicGaloisAlgebraTwistedCommutatorCoefficients_apply_self K L i0 b v
    have hw2 : w i2 = 0 := by
      simp [w, cyclicGaloisAlgebraTwistedCommutatorCoefficients, h2]
    have hsupp : cyclicGaloisAlgebraCoefficientSupport K L w = {i1} := by
      ext i
      rcases hcover i with rfl | rfl | rfl <;>
        simp [mem_cyclicGaloisAlgebraCoefficientSupport, hw0, hw1, hw2, hi01, hi12.symm]
    have hu : IsUnit (cyclicGaloisAlgebraNormalFormLinearMap K L a w) :=
      cyclicGaloisAlgebraNormalForm_isUnit_of_coefficientSupport_card_eq_one K L a ha w
        (by rw [hsupp]; simp)
    rw [hwzero] at hu
    exact not_isUnit_zero hu
  have hx0 : x = cyclicGaloisAlgebraC K L a (v i0) := by
    rw [hxform, h1, h2]
    change (cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
      (Module.finrank K L) (algebraMap K L a)) (v i0) +
        (cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
          (Module.finrank K L) (algebraMap K L a)) 0 * cyclicGaloisAlgebraX K L a +
          (cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
            (Module.finrank K L) (algebraMap K L a)) 0 * cyclicGaloisAlgebraX K L a ^ 2 = _
    rw [map_zero, zero_mul, add_zero, zero_mul, add_zero]
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
    have hu := cubicCyclicGaloisAlgebra_coefficient_mul_X_isUnit K L a ha _
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

/-- A nonzero cubic cyclic Galois algebra has center exactly its base field. -/
theorem cubicCyclicGaloisAlgebra_isCentral
    (hdeg : Module.finrank K L = 3) (a : K) (ha : a ≠ 0) :
    Algebra.IsCentral K (cyclicGaloisAlgebra K L a) where
  out := by
    intro x hx
    rw [Algebra.mem_bot]
    obtain ⟨k, hk⟩ := cubicCyclicGaloisAlgebra_center_exists_base K L hdeg a ha x
      (Subalgebra.mem_center_iff.mp hx)
    exact ⟨k, hk.symm⟩

/-- The raw cyclic algebra for every nonzero cubic parameter is a finite-dimensional central
simple algebra. -/
noncomputable def cubicCyclicGaloisAlgebraCSA
    (hdeg : Module.finrank K L = 3) (a : K) (ha : a ≠ 0) : CSA K where
  carrier := cyclicGaloisAlgebra K L a
  isCentral := cubicCyclicGaloisAlgebra_isCentral K L hdeg a ha
  isSimple := isSimpleRing_cyclicGaloisAlgebra_of_finrank_eq_three K L hdeg a ha
  fin_dim := cyclicGaloisAlgebra_finiteDimensional K L a

/-- A degree-three cohomological unit parameter canonically determines a cubic central simple
algebra. -/
noncomputable def cubicCyclicGaloisH2ParameterCSA
    (hdeg : Module.finrank K L = 3) (a : Additive Kˣ) : CSA K :=
  cubicCyclicGaloisAlgebraCSA K L hdeg (a.toMul : K) a.toMul.ne_zero

end GaloisForLFunctions.HTGeometry.ABHN
