import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic

/-!
# Four elementary factors over finite commutative rings

Chinese remaindering over the finite maximal spectrum makes a unimodular row
entry invertible after one shear. An explicit three-factor identity at that
unit entry gives four alternating full unipotent factors. The construction
also proves surjectivity on SL₂ for ring surjections onto finite rings.
-/

namespace GaloisForLFunctions.HTGeometry.FiniteRingSl2
noncomputable section
variable {R : Type*} [CommRing R]

/-- Finite rings have only finitely many maximal ideals, including the zero ring. -/
theorem finite_maximalSpectrum [Finite R] : Finite (MaximalSpectrum R) := by
  letI : Finite (Ideal R) := Finite.of_injective (fun I : Ideal R => (I : Set R)) SetLike.coe_injective
  exact Finite.of_injective MaximalSpectrum.asIdeal (fun x y h => MaximalSpectrum.ext h)

/-- Chinese remaindering chooses one shear making a unimodular row entry a unit. -/
theorem exists_isUnit_add_mul [Finite (MaximalSpectrum R)] {a b : R}
    (hab : IsCoprime a b) : ∃ t : R, IsUnit (a+t*b) := by
  classical
  let e (m : MaximalSpectrum R) : R := if a ∈ m.asIdeal then 1 else 0
  obtain ⟨t,ht⟩ := Ideal.exists_forall_sub_mem_ideal
    (fun _ _ h => MaximalSpectrum.isCoprime_of_ne h) e
  refine ⟨t,?_⟩
  by_contra hu
  obtain ⟨I,hI,hm⟩ := exists_max_ideal_of_mem_nonunits hu
  let m : MaximalSpectrum R := ⟨I,hI⟩
  have htm : t-e m ∈ I := ht m
  by_cases ha : a ∈ I
  · have ht1 : t-1 ∈ I := by simpa [e,m,ha] using htm
    have hb : b ∈ I := by
      have h := I.sub_mem (I.sub_mem hm ha) (I.mul_mem_right b ht1)
      convert h using 1
      ring
    obtain ⟨x,y,hxy⟩ := hab
    have hone : (1:R) ∈ I := by
      rw [← hxy]
      exact I.add_mem (I.mul_mem_left x ha) (I.mul_mem_left y hb)
    exact hI.ne_top (I.eq_top_of_isUnit_mem hone isUnit_one)
  · have ht0 : t ∈ I := by simpa [e,m,ha] using htm
    apply ha
    have h := I.sub_mem hm (I.mul_mem_right b ht0)
    simpa using h

def upper (x : R) : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![1,x;0,1],by simp [Matrix.det_fin_two]⟩

def lower (x : R) : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![1,0;x,1],by simp [Matrix.det_fin_two]⟩

@[simp]
theorem upper_add (x y : R) : upper (x+y)=upper x*upper y := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [upper,Matrix.SpecialLinearGroup.coe_mul,add_comm]

@[simp]
theorem lower_add (x y : R) : lower (x+y)=lower x*lower y := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [lower,Matrix.SpecialLinearGroup.coe_mul]

@[simp]
theorem upper_zero : upper (0:R)=1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [upper]

@[simp]
theorem lower_zero : lower (0:R)=1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [lower]

/-- A unit lower-left entry gives an explicit three-factor decomposition over a ring. -/
theorem factorization_of_unit (M : Matrix.SpecialLinearGroup (Fin 2) R)
    (u : Rˣ) (hu : M 1 0=(u:R)) :
    M=upper ((M 0 0-1)*(↑u⁻¹:R))*lower (M 1 0)*upper ((M 1 1-1)*(↑u⁻¹:R)) := by
  have hi : M 1 0*(↑u⁻¹:R)=1 := by rw [hu]; simp
  have hd := Matrix.SpecialLinearGroup.det_coe M
  rw [Matrix.det_fin_two] at hd
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [upper,lower,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  · linear_combination -(M 0 0-1)*hi
  · linear_combination -(↑u⁻¹:R)*hd - M 0 1*hi -
      (M 0 0-1)*(M 1 1-1)*(↑u⁻¹:R)*hi
  · linear_combination -(M 1 1-1)*hi

/-- Every determinant-one matrix over a ring with finite maximal spectrum has four elementary factors. -/
theorem exists_four_factors [Finite (MaximalSpectrum R)]
    (M : Matrix.SpecialLinearGroup (Fin 2) R) :
    ∃ x y z w : R, M=upper x*lower y*upper z*lower w := by
  obtain ⟨t,ht⟩ := exists_isUnit_add_mul (Matrix.SpecialLinearGroup.isCoprime_row M 1)
  have he : (M*lower t) 1 0=M 1 0+t*M 1 1 := by
    simp [lower,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,mul_comm]
  obtain ⟨u,hu⟩ := ht
  have hfac := factorization_of_unit (M*lower t) u (he.trans hu.symm)
  refine ⟨((M*lower t) 0 0-1)*(↑u⁻¹:R),(M*lower t) 1 0,
    ((M*lower t) 1 1-1)*(↑u⁻¹:R),-t,?_⟩
  rw [← hfac,mul_assoc,← lower_add,add_neg_cancel,lower_zero,mul_one]

/-- The four-factor bound applies to every finite commutative ring. -/
theorem exists_four_factors_finite [Finite R]
    (M : Matrix.SpecialLinearGroup (Fin 2) R) :
    ∃ x y z w : R, M=upper x*lower y*upper z*lower w := by
  letI := finite_maximalSpectrum (R:=R)
  exact exists_four_factors M

/-- The complete upper unipotent subgroup, parametrized by the additive ring. -/
def upperHom : Multiplicative R →* Matrix.SpecialLinearGroup (Fin 2) R where
  toFun x := upper x.toAdd
  map_one' := upper_zero
  map_mul' x y := upper_add x.toAdd y.toAdd

/-- The complete lower unipotent subgroup, parametrized by the additive ring. -/
def lowerHom : Multiplicative R →* Matrix.SpecialLinearGroup (Fin 2) R where
  toFun x := lower x.toAdd
  map_one' := lower_zero
  map_mul' x y := lower_add x.toAdd y.toAdd

variable {S : Type*} [CommRing S]

@[simp]
theorem map_upper (f : R →+* S) (x : R) :
    Matrix.SpecialLinearGroup.map f (upper x)=upper (f x) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map,upper]

@[simp]
theorem map_lower (f : R →+* S) (x : R) :
    Matrix.SpecialLinearGroup.map f (lower x)=lower (f x) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map,lower]

/-- A surjective ring map onto a finite commutative ring induces a surjection on SL₂. -/
theorem map_surjective [Finite S] (f : R →+* S) (hf : Function.Surjective f) :
    Function.Surjective (Matrix.SpecialLinearGroup.map (n:=Fin 2) f) := by
  intro M
  obtain ⟨x,y,z,w,hM⟩ := exists_four_factors_finite M
  obtain ⟨a,ha⟩ := hf x
  obtain ⟨b,hb⟩ := hf y
  obtain ⟨c,hc⟩ := hf z
  obtain ⟨d,hd⟩ := hf w
  refine ⟨upper a*lower b*upper c*lower d,?_⟩
  simpa only [map_mul,map_upper,map_lower,ha,hb,hc,hd] using hM.symm

end
end GaloisForLFunctions.HTGeometry.FiniteRingSl2
