import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerInverseCycles
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerPrimitiveOrbitProduct
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! The actual Mayer Euler product over inverse-unoriented primitive classes,
with the exact cardinality of each orientation fiber as exponent. -/

open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerFredholm MayerOrbitWords MayerOrbitProduct MayerInverseCycles
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerUnorientedProduct

/-- The geometric Euler factor of an inverse-unoriented primitive class. -/
def factor (w z : ℂ) (u : UnorientedOrbit) (m : ℕ) : ℂ :=
  1-z^(2*unorientedPairLength u) *
    Complex.exp (-(w/2+(m : ℂ))*(unorientedTranslationLength u : ℂ))

theorem factor_unoriented (w z : ℂ) (c : Orbit) (m : ℕ) :
    factor w z (unoriented c) m = 1-orbitWeight w z c m := by
  rw [factor,unorientedPairLength_mk,unorientedTranslationLength_mk,
    orbitWeight_eq_translationLength]

private def indexMap (p : Orbit × ℕ) : UnorientedOrbit × ℕ := (unoriented p.1,p.2)

/-- A fiber at a fixed mode consists exactly of the one or two orientations. -/
private def fiberEquiv (q : UnorientedOrbit × ℕ) :
    ↥(orientations q.1) ≃ {p : Orbit × ℕ // indexMap p=q} where
  toFun c := ⟨(c.val,q.2),Prod.ext ((mem_orientations c.val q.1).mp c.property) rfl⟩
  invFun p := ⟨p.val.1,(mem_orientations p.val.1 q.1).mpr
    (congrArg Prod.fst p.property)⟩
  left_inv c := by rfl
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl (congrArg Prod.snd p.property).symm

private theorem hasProd_fiber (w z : ℂ) (q : UnorientedOrbit × ℕ) :
    HasProd (fun p : {p : Orbit × ℕ // indexMap p=q} =>
      1-orbitWeight w z p.val.1 p.val.2) (factor w z q.1 q.2 ^ multiplicity q.1) := by
  have hc : HasProd (fun _ : ↥(orientations q.1) => factor w z q.1 q.2)
      (factor w z q.1 q.2 ^ multiplicity q.1) := by
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_coe,multiplicity] using
      (hasProd_fintype (fun _ : ↥(orientations q.1) => factor w z q.1 q.2))
  apply (fiberEquiv q).hasProd_iff.mp
  apply hc.congr_fun
  intro c
  change 1-orbitWeight w z c.val q.2 = factor w z q.1 q.2
  rw [← factor_unoriented,(mem_orientations c.val q.1).mp c.property]

private theorem hasProd_quotient {w z A : ℂ}
    (hp : HasProd (fun p : Orbit × ℕ => 1-orbitWeight w z p.1 p.2) A) :
    HasProd (fun q : UnorientedOrbit × ℕ => factor w z q.1 q.2 ^ multiplicity q.1) A := by
  have hs : HasProd (fun p : (q : UnorientedOrbit × ℕ) ×
      {p : Orbit × ℕ // indexMap p=q} => 1-orbitWeight w z p.2.val.1 p.2.val.2) A :=
    (Equiv.sigmaFiberEquiv indexMap).hasProd_iff.mpr hp
  exact hs.sigma (fun q => hasProd_fiber w z q)

private theorem multipliable_modes {w z : ℂ}
    (hs : Summable (fun p : Orbit × ℕ => ‖orbitWeight w z p.1 p.2‖))
    (u : UnorientedOrbit) :
    Multipliable (fun m : ℕ => factor w z u m ^ multiplicity u) := by
  have hn : Summable (fun m : ℕ => ‖orbitWeight w z (chosenOrientation u) m‖) :=
    hs.comp_injective (i := fun m : ℕ => (chosenOrientation u,m))
      (fun _ _ h => congrArg Prod.snd h)
  have hc : Summable (fun m : ℕ => orbitWeight w z (chosenOrientation u) m) := hn.of_norm
  have hf : Multipliable (fun m : ℕ => 1-orbitWeight w z (chosenOrientation u) m) := by
    simpa only [sub_eq_add_neg] using Complex.multipliable_one_add_of_summable hc.neg
  have he (m : ℕ) : factor w z u m = 1-orbitWeight w z (chosenOrientation u) m := by
    calc
      factor w z u m = factor w z (unoriented (chosenOrientation u)) m :=
        congrArg (fun v => factor w z v m) (unoriented_chosenOrientation u).symm
      _ = 1-orbitWeight w z (chosenOrientation u) m := factor_unoriented w z _ m
  simpa only [he] using hf.pow (multiplicity u)

private theorem quotient_products {w z A : ℂ}
    (hs : Summable (fun p : Orbit × ℕ => ‖orbitWeight w z p.1 p.2‖))
    (hp : HasProd (fun p : Orbit × ℕ => 1-orbitWeight w z p.1 p.2) A) :
    HasProd (fun q : UnorientedOrbit × ℕ => factor w z q.1 q.2 ^ multiplicity q.1) A ∧
      (∀ u : UnorientedOrbit, Multipliable (fun m : ℕ => factor w z u m ^ multiplicity u)) ∧
      A = ∏' u : UnorientedOrbit, ∏' m : ℕ, (factor w z u m ^ multiplicity u) := by
  have hq := hasProd_quotient hp
  have hm := multipliable_modes hs
  have ho : HasProd (fun u : UnorientedOrbit => ∏' m : ℕ,
      (factor w z u m ^ multiplicity u)) A :=
    hq.prod_fiberwise (fun u => (hm u).hasProd)
  exact ⟨hq,hm,ho.tprod_eq.symm⟩

/-- The local determinant product retains the exact orientation multiplicity. -/
theorem exists_signed_determinant_unorientedProduct {w : ℂ} (hw : 1 < w.re) :
    ∃ R > 0, ∀ z : ℂ, ‖z‖ < R →
      HasProd (fun q : UnorientedOrbit × ℕ => factor w z q.1 q.2 ^ multiplicity q.1)
        (determinant w (zero_lt_one.trans hw) z * determinant w (zero_lt_one.trans hw) (-z)) ∧
      (∀ u : UnorientedOrbit, Multipliable (fun m : ℕ => factor w z u m ^ multiplicity u)) ∧
      determinant w (zero_lt_one.trans hw) z * determinant w (zero_lt_one.trans hw) (-z) =
        ∏' u : UnorientedOrbit, ∏' m : ℕ, (factor w z u m ^ multiplicity u) := by
  obtain ⟨R,hR,h⟩ := exists_signed_determinant_eulerProduct hw
  refine ⟨R,hR,fun z hz => ?_⟩
  exact quotient_products (h z hz).1 (h z hz).2.1

/-- The inverse-unoriented product converges on the closed unit spectral disk. -/
theorem signed_determinant_unorientedProduct_on_closed_unit {w z : ℂ}
    (hw : 2 < w.re) (hz : ‖z‖ ≤ 1) :
    HasProd (fun q : UnorientedOrbit × ℕ => factor w z q.1 q.2 ^ multiplicity q.1)
      (determinant w (show 0 < w.re by linarith only [hw]) z *
        determinant w (show 0 < w.re by linarith only [hw]) (-z)) ∧
    (∀ u : UnorientedOrbit, Multipliable (fun m : ℕ => factor w z u m ^ multiplicity u)) ∧
    determinant w (show 0 < w.re by linarith only [hw]) z *
        determinant w (show 0 < w.re by linarith only [hw]) (-z) =
      ∏' u : UnorientedOrbit, ∏' m : ℕ, (factor w z u m ^ multiplicity u) := by
  have h := signed_determinant_eulerProduct_on_closed_unit hw hz
  exact quotient_products h.1 h.2.1

/-- At spectral parameter one, the geometric factor has exponent one or two. -/
theorem signed_determinant_one_eq_unorientedProduct {w : ℂ} (hw : 2 < w.re) :
    determinant w (show 0 < w.re by linarith only [hw]) 1 *
      determinant w (show 0 < w.re by linarith only [hw]) (-1) =
      ∏' u : UnorientedOrbit, ∏' m : ℕ,
        ((1-Complex.exp (-(w/2+(m : ℂ))*(unorientedTranslationLength u : ℂ))) ^
          multiplicity u) := by
  have h := signed_determinant_unorientedProduct_on_closed_unit (z := 1) hw
    (by simpa only [norm_one] using (le_refl (1 : ℝ)))
  simpa only [factor,one_pow,one_mul] using h.2.2

#print axioms factor_unoriented
#print axioms exists_signed_determinant_unorientedProduct
#print axioms signed_determinant_unorientedProduct_on_closed_unit
#print axioms signed_determinant_one_eq_unorientedProduct

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerUnorientedProduct
