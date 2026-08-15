import GaloisForLFunctions.HTGeometry.PencilRealizationLaw

/-!
# The intrinsic hypertranscendental realization dimension

A complex is realized in `d` variables when there are `ℚ`-independent translation steps, one constant
direction, and an entire scalar source on `ℂ^d` whose annihilator among difference operators is
exactly the Stanley--Reisner ideal and for which the differential matroid of every finite family of
operator outputs is the Stanley--Reisner quotient-class matroid.  The intrinsic realization dimension
is the least such `d`; a periodic-pencil separation in dimension `d` realizes the complex there.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Bottcher
open scoped Classical Differential

noncomputable section

variable {α : Type} [Fintype α] [DecidableEq α]

local instance htDimComplexDifferential : Differential ℂ := ⟨0⟩

/-- **`d` variables realize the complex.**  There are `ℚ`-independent translation steps, a constant
direction and an entire scalar source whose annihilator is the Stanley--Reisner ideal and for which
the differential matroid of every finite family of operator outputs is the Stanley--Reisner
quotient-class matroid. -/
def HTRealizableDim (facets : Finset (Finset α)) (d : ℕ) : Prop :=
  ∃ (ω : α → (Fin d → ℂ)) (w : Fin d → ℂ) (Y : facets → (Fin d → ℂ) → ℂ)
    (hY : ∀ A, AnalyticOnNhd ℂ (Y A) Set.univ),
    LinearIndependent ℚ ω ∧
    (∀ (A : facets) (v : α), v ∉ A.1 → ∀ z, Y A (z + ω v) = Y A z) ∧
    (∀ P : MvPolynomial α ℂ,
      seedCarrierPoly ω (fun y => ∑ A : facets, Y A y) P = 0 ↔
        P ∈ stanleyReisnerIdeal ℂ facets) ∧
    letI := meroFieldGenDirDifferential w (isOpen_univ (X := Fin d → ℂ))
      isPreconnected_univ_gen Set.univ_nonempty
    haveI := meroFieldGenDirDifferentialAlgebra w
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (dd : translationSubmonoid (Polynomial ℂ) α) (n : ℕ) (Q : ι → ℕ → MvPolynomial α ℂ),
      differentialFamilyMatroid (F := ℂ)
          (fun i => entireGerm (fun z => opCarrier w ω (fun y => ∑ A : facets, Y A y) n (Q i)
            (z - ∑ v, (translationDenominatorExponent dd v : ℤ) • ω v))
            (analyticOnNhd_opCarrier_sub w ω
              (Finset.analyticOnNhd_fun_sum _ fun A _ => hY A) n (Q i) _))
        = stanleyReisnerLaurentMatroid dd facets
          (fun j => Ideal.Quotient.mk (stanleyReisnerIdeal (Polynomial ℂ) facets)
            (opPoly n (Q j)))

/-- The intrinsic hypertranscendental realization dimension. -/
def htDim (facets : Finset (Finset α)) : ℕ := sInf {d | HTRealizableDim facets d}

set_option maxHeartbeats 4000000 in
/-- **A periodic-pencil separation realizes its complex in the same dimension.** -/
theorem htRealizableDim_of_pencil {d : ℕ} (facets : Finset (Finset α))
    (Lf : Finset α → ((Fin d → ℂ) →ₗ[ℂ] ℂ)) (a : α → (Fin d → ℂ)) (w : Fin d → ℂ)
    (hindep : LinearIndependent ℚ a)
    (hw : ∀ A ∈ facets, Lf A w ≠ 0)
    (houtside : ∀ A ∈ facets, ∀ v ∉ A, Complex.exp (Lf A (a v)) = 1)
    (hinside : ∀ A ∈ facets, ∀ g : α → ℤ,
      Complex.exp (∑ v ∈ A, (g v : ℂ) * Lf A (a v)) = 1 → ∀ v ∈ A, g v = 0) :
    HTRealizableDim facets d := by
  classical
  obtain ⟨Y, hY, hper, hind⟩ :=
    exists_pencilSource_orbit_jointlyDirHypertranscendental facets Lf a w hw houtside hinside
  exact ⟨a, w, Y, hY, hindep, hper,
    fun P => pencilOrbit_seedCarrier_eq_zero_iff a w Y hY hper hind P,
    fun ι _ _ dd n Q => pencilOrbit_matroid_eq a w Y hY hper hind ι dd n Q⟩

/-- **The intrinsic realization dimension is at most any periodic-pencil dimension.** -/
theorem htDim_le_of_pencil {d : ℕ} (facets : Finset (Finset α))
    (Lf : Finset α → ((Fin d → ℂ) →ₗ[ℂ] ℂ)) (a : α → (Fin d → ℂ)) (w : Fin d → ℂ)
    (hindep : LinearIndependent ℚ a)
    (hw : ∀ A ∈ facets, Lf A w ≠ 0)
    (houtside : ∀ A ∈ facets, ∀ v ∉ A, Complex.exp (Lf A (a v)) = 1)
    (hinside : ∀ A ∈ facets, ∀ g : α → ℤ,
      Complex.exp (∑ v ∈ A, (g v : ℂ) * Lf A (a v)) = 1 → ∀ v ∈ A, g v = 0) :
    htDim facets ≤ d :=
  Nat.sInf_le (htRealizableDim_of_pencil facets Lf a w hindep hw houtside hinside)

end

end GaloisForLFunctions.HTGeometry
