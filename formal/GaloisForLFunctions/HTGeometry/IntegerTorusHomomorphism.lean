import GaloisForLFunctions.HTGeometry.UniversalClockSamplingPhaseLaw

/-!
# Integer homomorphisms of finite unit tori

An integer matrix defines a continuous homomorphism of unit tori, and every Fourier monomial pulls
back along it to the Fourier monomial of the transposed integer vector.  A left inverse over the
integers makes the homomorphism injective.

A frequency vector obtained from another one by an integer matrix factors the phase flow through
that homomorphism.  This is the reduction step which expresses the orbit of a rationally dependent
frequency vector as the image of the orbit of a rationally independent one.
-/

open Filter MeasureTheory Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Circle

variable {ι : Type*}

/-- A character of the unit circle is additive in its argument. -/
theorem fourier_point_add (m : ℤ) (a b : UnitAddCircle) :
    fourier m (a + b) = fourier m a * fourier m b := by
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective b
  have hadd : ((u : ℝ) : UnitAddCircle) + ((v : ℝ) : UnitAddCircle) = ((u + v : ℝ) : UnitAddCircle) :=
    (map_add (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) u v).symm
  rw [hadd, fourier_coe_apply, fourier_coe_apply, fourier_coe_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Scaling the argument of a circle character multiplies its index. -/
theorem fourier_point_zsmul (m c : ℤ) (a : UnitAddCircle) :
    fourier m (c • a) = fourier (m * c) a := by
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
  have hc : c • ((u : ℝ) : UnitAddCircle) = ((c * u : ℝ) : UnitAddCircle) := by
    rw [← zsmul_eq_mul]
    exact (map_zsmul (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) c u).symm
  rw [hc, fourier_coe_apply, fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- A character of a sum of points is the product of its values. -/
theorem fourier_point_sum (s : Finset ι) (m : ℤ) (x : ι → UnitAddCircle) :
    fourier m (∑ j ∈ s, x j) = ∏ j ∈ s, fourier m (x j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, fourier_point_add, ih]

/-- The value at one point of a sum of character indices is the product of the values. -/
theorem fourier_sum_index (s : Finset ι) (c : ι → ℤ) (a : UnitAddCircle) :
    fourier (∑ i ∈ s, c i) a = ∏ i ∈ s, fourier (c i) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.prod_insert hb, fourier_add, ih]

end Circle

variable {d k : Type*} [Fintype d] [Fintype k]

/-- The homomorphism of unit tori attached to an integer matrix. -/
def torusIntegerHom (M : d → k → ℤ) (x : UnitAddTorus k) : UnitAddTorus d :=
  fun i => ∑ j, M i j • x j

omit [Fintype d] in
@[simp] theorem torusIntegerHom_apply (M : d → k → ℤ) (x : UnitAddTorus k) (i : d) :
    torusIntegerHom M x i = ∑ j, M i j • x j := rfl

omit [Fintype d] in
theorem continuous_torusIntegerHom (M : d → k → ℤ) :
    Continuous (torusIntegerHom (d := d) (k := k) M) := by
  refine continuous_pi fun i => ?_
  exact continuous_finsetSum _ fun j _ => (continuous_zsmul (M i j)).comp (continuous_apply j)

omit [Fintype d] in
theorem torusIntegerHom_add (M : d → k → ℤ) (x y : UnitAddTorus k) :
    torusIntegerHom M (x + y) = torusIntegerHom M x + torusIntegerHom M y := by
  funext i
  show ∑ j, M i j • (x j + y j) = (∑ j, M i j • x j) + ∑ j, M i j • y j
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => smul_add (M i j) (x j) (y j)

omit [Fintype d] in
@[simp] theorem torusIntegerHom_zero (M : d → k → ℤ) :
    torusIntegerHom (d := d) (k := k) M 0 = 0 := by
  funext i
  show ∑ _j, (_ : UnitAddCircle) = 0
  exact Finset.sum_eq_zero fun j _ => smul_zero (M i j)

omit [Fintype d] [Fintype k] in
/-- A real vector represents a point of the unit torus. -/
theorem exists_real_lift (x : UnitAddTorus k) :
    ∃ y : k → ℝ, ∀ j, ((y j : ℝ) : UnitAddCircle) = x j :=
  ⟨fun j => (QuotientAddGroup.mk_surjective (x j)).choose,
    fun j => (QuotientAddGroup.mk_surjective (x j)).choose_spec⟩

omit [Fintype d] in
theorem coe_sum_mul (c : k → ℤ) (y : k → ℝ) :
    ((∑ j, (c j : ℝ) * y j : ℝ) : UnitAddCircle)
      = ∑ j, c j • ((y j : ℝ) : UnitAddCircle) := by
  show QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)) (∑ j, (c j : ℝ) * y j) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← zsmul_eq_mul]
  exact map_zsmul (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) (c j) (y j)

/-- **Pullback of a Fourier monomial.**  A character of the target torus pulls back along an
integer homomorphism to the character of the transposed integer vector. -/
theorem mFourier_torusIntegerHom (M : d → k → ℤ) (n : d → ℤ) (x : UnitAddTorus k) :
    UnitAddTorus.mFourier n (torusIntegerHom M x)
      = UnitAddTorus.mFourier (fun j => ∑ i, n i * M i j) x := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, torusIntegerHom_apply]
  calc ∏ i, fourier (n i) (∑ j, M i j • x j)
      = ∏ i, ∏ j, fourier (n i * M i j) (x j) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [fourier_point_sum]
        exact Finset.prod_congr rfl fun j _ => fourier_point_zsmul _ _ _
    _ = ∏ j, ∏ i, fourier (n i * M i j) (x j) := Finset.prod_comm
    _ = ∏ j, fourier (∑ i, n i * M i j) (x j) :=
        Finset.prod_congr rfl fun j _ => (fourier_sum_index _ _ _).symm

/-- **Injectivity from an integer left inverse.** -/
theorem torusIntegerHom_injective [DecidableEq k] (M : d → k → ℤ) (A : k → d → ℤ)
    (hA : ∀ j j' : k, (∑ i, A j i * M i j') = if j = j' then 1 else 0) :
    Function.Injective (torusIntegerHom (d := d) (k := k) M) := by
  classical
  have key : ∀ (x : UnitAddTorus k) (j : k), ∑ i, A j i • torusIntegerHom M x i = x j := by
    intro x j
    have hstep : ∀ i : d, A j i • torusIntegerHom M x i = ∑ j', (A j i * M i j') • x j' := by
      intro i
      rw [torusIntegerHom_apply, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j' _ => (mul_smul (A j i) (M i j') (x j')).symm
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i, Finset.sum_comm]
    have hcol : ∀ j' : k,
        (∑ i, (A j i * M i j') • x j') = (if j = j' then (1 : ℤ) else 0) • x j' := by
      intro j'
      rw [← Finset.sum_smul, hA j j']
    rw [Finset.sum_congr rfl fun j' (_ : j' ∈ Finset.univ) => hcol j']
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl, one_smul]
    · intro j' _ hj'
      rw [if_neg (Ne.symm hj'), zero_smul]
    · intro hcon
      exact absurd (Finset.mem_univ j) hcon
  intro x₁ x₂ h
  funext j
  rw [← key x₁ j, ← key x₂ j, h]

/-- **Factorization of a phase flow.**  A frequency vector written over another one by an integer
matrix has its phase flow the image of the other phase flow. -/
theorem finiteClockPhasePoint_eq_torusIntegerHom
    (omega : d → ℝ) (gamma : k → ℝ) (M : d → k → ℤ)
    (hM : ∀ i, omega i = ∑ j, (M i j : ℝ) * gamma j) (t : ℝ) :
    finiteClockPhasePoint omega t = torusIntegerHom M (finiteClockPhasePoint gamma t) := by
  funext i
  show ((t * omega i / (2 * Real.pi) : ℝ) : UnitAddCircle)
    = ∑ j, M i j • ((t * gamma j / (2 * Real.pi) : ℝ) : UnitAddCircle)
  rw [← coe_sum_mul]
  congr 1
  rw [hM i, Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

end

end GaloisForLFunctions.HTGeometry
