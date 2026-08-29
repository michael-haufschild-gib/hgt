import GaloisForLFunctions.HTGeometry.QOrbitResidueEuler
import GaloisForLFunctions.HTGeometry.QDifferenceLaurentOneVariable

/-!
# Hypertranscendence of a `q`-primitive from one nonzero `q`-discrete residue

If the increment of an additive `q`-primitive has a nonzero `q`-discrete residue at its top pole
order along one multiplicative orbit, then no constant-coefficient Euler character of the increment
is a dilation coboundary, so the exact differential Ostrowski criterion makes the primitive
differentially transcendental over `k(w)`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

open scoped RatFunc

noncomputable section

variable {k : Type*} [Field k]

/-- **No constant-coefficient jet character of an increment with a nonzero top `q`-residue is a
dilation coboundary.** -/
theorem no_jetTelescoper_of_top_qOrbitResidue [CharZero k] {β : k} (hβ : β ≠ 0)
    (hβtor : ∀ n : ℤ, n ≠ 0 → β ^ n ≠ 1) {a : k} (ha : a ≠ 0) (r : RatFunc k)
    {D : ℕ} (hD : 0 < D)
    (hvanish : ∀ e : ℕ, D < e → qOrbitResidue β a e r = 0)
    (hres : qOrbitResidue β a D r ≠ 0) :
    letI := cylinderDifferential (1 : k)
    ∀ c : (Unit × ℕ) →₀ k, c ≠ 0 → ∀ y : RatFunc k,
      ratFuncScale β hβ y - y ≠
        Finsupp.linearCombination (RatFunc k)
          (fun p : Unit × ℕ => differentialJet p.2 r)
          (Finsupp.mapRange (algebraMap k (RatFunc k)) (map_zero _) c) := by
  letI := cylinderDifferential (1 : k)
  intro c hc y heq
  obtain ⟨α, N, hαN, hcomb⟩ := exists_eulerCombination_of_jetCombination_oneVar c hc r
  rw [hcomb] at heq
  refine not_dilationTelescoped_eulerCombination hβ ha hβtor hD r hvanish hres N α hαN ⟨y, ?_⟩
  rw [heq, eulerCombination]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [algebraMap_eq_toRF_C]

/-- **Hypertranscendence of a `q`-primitive with a nonzero top residue.** -/
theorem hypertranscendentalOver_of_qPrimitive_top_residue [CharZero k] {β : k} (hβ : β ≠ 0)
    (hβtor : ∀ n : ℤ, n ≠ 0 → β ^ n ≠ 1) {a : k} (ha : a ≠ 0) (r : RatFunc k)
    {D : ℕ} (hD : 0 < D)
    (hvanish : ∀ e : ℕ, D < e → qOrbitResidue β a e r = 0)
    (hres : qOrbitResidue β a D r ≠ 0)
    (u : LaurentSeries k)
    (hshift : innerDilation β hβ u = u + algebraMap (RatFunc k) (LaurentSeries k) r) :
    letI := cylinderDifferential (1 : k)
    letI := innerDifferential (k := k)
    HypertranscendentalOver (RatFunc k) u := by
  letI := cylinderDifferential (1 : k)
  letI := innerDifferential (k := k)
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  exact differentialIndependent_of_oneVariable_primitive β hβ hβtor u r hshift
    (no_jetTelescoper_of_top_qOrbitResidue hβ hβtor ha r hD hvanish hres)

end

end GaloisForLFunctions.HTGeometry
