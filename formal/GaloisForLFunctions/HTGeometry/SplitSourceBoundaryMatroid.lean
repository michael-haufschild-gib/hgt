import GaloisForLFunctions.HTGeometry.SourceBoundaryQuotientMatroid
import GaloisForLFunctions.HTGeometry.CoordinatewiseDifferentialFamilyMatroid

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open scoped Classical Differential

noncomputable section

universe u

/-- The differential-family matroid of an arbitrary additive primitive family is represented by
its simultaneous source-coboundary quotient. -/
theorem automorphismFamily_differentialFamilyMatroid_eq_sourceBoundaryQuotientMatroid
    {I κ C K L : Type u}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    [CharZero K] [CharZero L]
    (tau : I → DifferentialAlgEquiv C K) (sigma : I → L ≃+* L)
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (hcomp : ∀ i k, sigma i (algebraMap K L k) =
      algebraMap K L ((tau i).toAlgEquiv k))
    (hderiv : ∀ i y, sigma i y′ = (sigma i y)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ z : L, (∀ i, sigma i z = z) →
      ∃ c : C, algebraMap C L c = z)
    (x : κ → L) (b : I → κ → K)
    (hshift : ∀ i j, sigma i (x j) =
      x j + algebraMap K L (b i j)) :
    differentialFamilyMatroid (F := K) x =
      sourceBoundaryQuotientMatroid hconst tau (fun j i ↦ b i j) := by
  apply Matroid.ext_indep
  · simp [differentialFamilyMatroid]
  · intro S _
    rw [differentialFamilyMatroid_indep_iff,
      sourceBoundaryQuotientMatroid_indep_iff_no_jet_telescoping]
    exact
      GaloisForLFunctions.automorphismFamily_differentialIndependent_iff_no_constant_simultaneous_jet_telescoping
        (fun i ↦ (tau i).toAlgEquiv.toRingEquiv) sigma hcomp hderiv hCfixed hfixed
        (fun s : S ↦ x s) (fun i (s : S) ↦ b i s) (fun i s ↦ hshift i s)

/-- The complete raw mixed additive/multiplicative differential matroid is represented by the
single localized simultaneous source-boundary quotient of its additive and logarithmic source
increments. -/
theorem automorphismFamily_mixedRaw_differentialFamilyMatroid_eq_sourceBoundaryQuotientMatroid
    {I A B C K L : Type u}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    [CharZero K] [CharZero L]
    (tau : I → DifferentialAlgEquiv C K) (sigma : I → L ≃+* L)
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (hcomp : ∀ i k, sigma i (algebraMap K L k) =
      algebraMap K L ((tau i).toAlgEquiv k))
    (hderiv : ∀ i y, sigma i y′ = (sigma i y)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ z : L, (∀ i, sigma i z = z) →
      ∃ c : C, algebraMap C L c = z)
    (u : A → L) (x : B → L)
    (p : I → A → K) (q : I → B → K)
    (hx : ∀ b, x b ≠ 0) (hq : ∀ i b, q i b ≠ 0)
    (hadd : ∀ i a, sigma i (u a) =
      u a + algebraMap K L (p i a))
    (hmul : ∀ i b, sigma i (x b) =
      algebraMap K L (q i b) * x b) :
    differentialFamilyMatroid (F := K) (Sum.elim u x) =
      sourceBoundaryQuotientMatroid hconst tau
        (fun j i ↦ Sum.elim (p i) (fun b ↦ (q i b)′ / q i b) j) := by
  let z : A ⊕ B → L := Sum.elim u (fun b ↦ (x b)′ / x b)
  let omega : I → A ⊕ B → K :=
    fun i ↦ Sum.elim (p i) (fun b ↦ (q i b)′ / q i b)
  have hshift : ∀ i j, sigma i (z j) =
      z j + algebraMap K L (omega i j) := by
    intro i j
    cases j with
    | inl a => simpa [z, omega] using hadd i a
    | inr b =>
        simpa [z, omega] using
          ringEquiv_deriv_div_self_of_mul (sigma i) (hderiv i)
            (x b) (q i b) (hx b) (hq i b) (hmul i b)
  calc
    differentialFamilyMatroid (F := K) (Sum.elim u x) =
        differentialFamilyMatroid (F := K) z := by
      simpa [z] using
        differentialFamilyMatroid_sumElim_deriv_div_self_eq (F := K) u x
    _ = sourceBoundaryQuotientMatroid hconst tau (fun j i ↦ omega i j) :=
      automorphismFamily_differentialFamilyMatroid_eq_sourceBoundaryQuotientMatroid
        tau sigma hconst hcomp hderiv hCfixed hfixed z omega hshift
    _ = sourceBoundaryQuotientMatroid hconst tau
        (fun j i ↦ Sum.elim (p i) (fun b ↦ (q i b)′ / q i b) j) := by
      rfl

end

end GaloisForLFunctions.HTGeometry
