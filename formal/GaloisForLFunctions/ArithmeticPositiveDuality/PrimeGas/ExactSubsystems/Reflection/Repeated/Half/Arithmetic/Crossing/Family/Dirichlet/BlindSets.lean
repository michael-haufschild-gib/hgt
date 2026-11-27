import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Calibration

/-! # The lattice of attainable blind sets on integer shells -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet

open Set

/-- The set of positive false positives of one asymmetric finite shell spectrum. -/
def Attainable (S : Set ℝ) := ∃ (n : ℕ) (a : Fin n → ℕ+),
  ¬Reflects (energy ∘ a) ∧ blind (energy ∘ a)=S

/-- Reciprocal closure of the real root locus of a Dirichlet polynomial. -/
def locus (P : PolynomialRing) := {t : ℝ | 0<t ∧ (value t P=0 ∨ value (-t) P=0)}

private theorem locus_attainable {P : PolynomialRing} (hp : P ≠ 0) : Attainable (locus P) := by
  obtain ⟨n,a,asym,hit⟩ := polynomial_spectrum P hp
  refine ⟨n,a,asym,Set.ext fun t => ?_⟩
  constructor
  · rintro ⟨ht,h,_⟩
    exact ⟨ht,(hit t ht).mp h⟩
  · rintro ⟨ht,h⟩
    exact ⟨ht,(hit t ht).mpr h,asym⟩

/-- A physical certificate has the same roots at both signs. -/
theorem certificate_sign {n : ℕ} {a : Fin n → ℕ+} (ha : ¬Reflects (energy ∘ a)) (t : ℝ) :
    value (-t) (certificate a)=0 ↔ value t (certificate a)=0 := by
  rw [certificate_root _ (size_of_asymmetric _ ha),certificate_root _ (size_of_asymmetric _ ha)]
  simp only [agrees,neg_neg]
  exact eq_comm

private theorem certificate_set {S : Set ℝ} (h : Attainable S) :
    ∃ P : PolynomialRing, P ≠ 0 ∧ (∀ t, value (-t) P=0 ↔ value t P=0) ∧
      ∀ t, t ∈ S ↔ 0<t ∧ value t P=0 := by
  obtain ⟨n,a,asym,rfl⟩ := h
  refine ⟨certificate a,certificate_ne_zero a asym,certificate_sign asym,fun t => ?_⟩
  rw [certificate_root _ (size_of_asymmetric _ asym)]
  change (0<t ∧ agrees (energy ∘ a) t ∧ ¬Reflects (energy ∘ a)) ↔ _
  exact ⟨fun h => ⟨h.1,h.2.1⟩,fun h => ⟨h.1,h.2,asym⟩⟩

theorem attainable_iff (S : Set ℝ) :
    Attainable S ↔ ∃ P : PolynomialRing, P ≠ 0 ∧ S=locus P := by
  constructor
  · intro h
    obtain ⟨P,hP,sign,mem⟩ := certificate_set h
    exact ⟨P,hP,Set.ext fun t => by simpa only [locus,mem_setOf_eq,sign,or_self] using mem t⟩
  · rintro ⟨P,hP,rfl⟩
    exact locus_attainable hP

theorem attainable_empty : Attainable ∅ := by
  simpa [locus] using (locus_attainable (one_ne_zero : (1 : PolynomialRing) ≠ 0))

theorem squares_root (P Q : PolynomialRing) (t : ℝ) :
    value t (P^2+Q^2)=0 ↔ value t P=0 ∧ value t Q=0 := by
  rw [map_add,map_pow,map_pow]
  constructor
  · intro h
    exact ⟨by nlinarith only [h,sq_nonneg (value t Q)],by nlinarith only [h,sq_nonneg (value t P)]⟩
  · rintro ⟨a,b⟩
    rw [a,b]
    ring

/-- Products and sums of squares realize exact unions and intersections of
positive false positives, including all incidental roots of the input spectra. -/
theorem attainable_union_inter {S T : Set ℝ} (hs : Attainable S) (ht : Attainable T) :
    Attainable (S ∪ T) ∧ Attainable (S ∩ T) := by
  obtain ⟨P,hP,pSign,pMem⟩ := certificate_set hs
  obtain ⟨Q,hQ,qSign,qMem⟩ := certificate_set ht
  have nonzero : P^2+Q^2 ≠ 0 := by
    obtain ⟨u,_,hu,_⟩ := detecting_order hP
    intro zero
    exact hu ((squares_root P Q u).mp (by rw [zero,map_zero])).1
  constructor
  · refine (attainable_iff _).mpr ⟨P*Q,mul_ne_zero hP hQ,Set.ext fun t => ?_⟩
    simp only [mem_union,locus,mem_setOf_eq,pMem,qMem,map_mul,mul_eq_zero,pSign,qSign,or_self]
    tauto
  · refine (attainable_iff _).mpr ⟨P^2+Q^2,nonzero,Set.ext fun t => ?_⟩
    simp only [mem_inter_iff,locus,mem_setOf_eq,pMem,qMem,squares_root,pSign,qSign,or_self]
    tauto

#print axioms attainable_iff
#print axioms attainable_empty
#print axioms attainable_union_inter

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet
