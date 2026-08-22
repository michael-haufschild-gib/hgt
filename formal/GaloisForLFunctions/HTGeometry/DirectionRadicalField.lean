import GaloisForLFunctions.HTGeometry.PowerSeriesSqrtBranch
import GaloisForLFunctions.HTGeometry.BlockDiscriminantIndependence
import GaloisForLFunctions.HTGeometry.BlockFlipRealization
import GaloisForLFunctions.HTGeometry.CubeSwapGaloisAssembly
import Mathlib.RingTheory.LaurentSeries

/-!
# The radical field of one transverse direction

The block discriminants of a single transverse coupling are squares in the Laurent series field —
the square root is the binomial series, pinned by its constant term — but not in the field of
rational functions.  Adjoining those square roots inside the Laurent series gives the splitting
field of the direction's characteristic polynomial, with its block flips.

## Main results

* `ratFuncToLaurent` — the base field inside the Laurent series.
* `directionRadical` — the square root of a block discriminant with prescribed constant term.
* `exists_directionFlip` — every block flip is realized on the radical field.
-/

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type} [Field A]

/-- The rational function field inside the Laurent series field. -/
def ratFuncToLaurent (A : Type) [Field A] : RatFunc A →+* LaurentSeries A :=
  IsFractionRing.lift (A := Polynomial A) (K := RatFunc A)
    (g := (algebraMap (PowerSeries A) (LaurentSeries A)).comp
      (Polynomial.coeToPowerSeries.ringHom))
    (by
      have h1 : Function.Injective ⇑(algebraMap (PowerSeries A) (LaurentSeries A)) :=
        IsFractionRing.injective (PowerSeries A) (LaurentSeries A)
      have h2 : Function.Injective
          ⇑(Polynomial.coeToPowerSeries.ringHom (R := A)) := Polynomial.coe_injective A
      exact h1.comp h2)

/-- The square root of the block discriminant `δ² + 4u²`, with constant term `δ`. -/
def directionRadicalSeries (h2 : (2 : A) ≠ 0) {δ : A} (hδ : δ ≠ 0) : PowerSeries A :=
  Classical.choose (exists_powerSeries_sqrt_branch h2
    (PowerSeries.C (δ * δ) + PowerSeries.C (4 : A) * PowerSeries.X ^ 2) δ hδ (by simp))

theorem directionRadicalSeries_sq (h2 : (2 : A) ≠ 0) {δ : A} (hδ : δ ≠ 0) :
    directionRadicalSeries h2 hδ * directionRadicalSeries h2 hδ
      = PowerSeries.C (δ * δ) + PowerSeries.C (4 : A) * PowerSeries.X ^ 2 :=
  (Classical.choose_spec (exists_powerSeries_sqrt_branch h2
    (PowerSeries.C (δ * δ) + PowerSeries.C (4 : A) * PowerSeries.X ^ 2) δ hδ (by simp))).1

theorem constantCoeff_directionRadicalSeries (h2 : (2 : A) ≠ 0) {δ : A} (hδ : δ ≠ 0) :
    PowerSeries.constantCoeff (R := A) (directionRadicalSeries h2 hδ) = δ :=
  (Classical.choose_spec (exists_powerSeries_sqrt_branch h2
    (PowerSeries.C (δ * δ) + PowerSeries.C (4 : A) * PowerSeries.X ^ 2) δ hδ (by simp))).2

/-- The base field structure the radical field is built over. -/
scoped instance ratFuncLaurentAlgebra : Algebra (RatFunc A) (LaurentSeries A) :=
  (ratFuncToLaurent A).toAlgebra

theorem algebraMap_ratFunc_laurent (x : RatFunc A) :
    algebraMap (RatFunc A) (LaurentSeries A) x = ratFuncToLaurent A x := rfl

theorem ratFuncToLaurent_polynomial (p : Polynomial A) :
    ratFuncToLaurent A (algebraMap (Polynomial A) (RatFunc A) p)
      = algebraMap (PowerSeries A) (LaurentSeries A) (Polynomial.coeToPowerSeries.ringHom p) := by
  rw [ratFuncToLaurent]
  exact IsFractionRing.lift_algebraMap _ p

/-- The square root of a block discriminant, inside the Laurent series field. -/
def directionRadical (h2 : (2 : A) ≠ 0) {δ : A} (hδ : δ ≠ 0) : LaurentSeries A :=
  algebraMap (PowerSeries A) (LaurentSeries A) (directionRadicalSeries h2 hδ)

theorem directionRadical_sq (h2 : (2 : A) ≠ 0) {δ : A} (hδ : δ ≠ 0) :
    directionRadical h2 hδ * directionRadical h2 hδ
      = algebraMap (RatFunc A) (LaurentSeries A)
        (algebraMap (Polynomial A) (RatFunc A)
          (Polynomial.C (δ * δ) + Polynomial.C (4 : A) * Polynomial.X ^ 2)) := by
  rw [directionRadical, ← map_mul, directionRadicalSeries_sq]
  rw [algebraMap_ratFunc_laurent, ratFuncToLaurent_polynomial]
  congr 1
  simp [Polynomial.coeToPowerSeries.ringHom]

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The radical field of one transverse direction. -/
def directionField (h2 : (2 : A) ≠ 0) {δ : ι → A} (hδ : ∀ z, δ z ≠ 0) :
    IntermediateField (RatFunc A) (LaurentSeries A) :=
  IntermediateField.adjoin (RatFunc A) (Set.range fun z => directionRadical h2 (hδ z))

/-- The radicals, inside the field they generate. -/
def directionFieldRadical (h2 : (2 : A) ≠ 0) {δ : ι → A} (hδ : ∀ z, δ z ≠ 0) (z : ι) :
    ↥(directionField h2 hδ) :=
  ⟨directionRadical h2 (hδ z), IntermediateField.subset_adjoin _ _ ⟨z, rfl⟩⟩

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem directionFieldRadical_sq (h2 : (2 : A) ≠ 0) {δ : ι → A} (hδ : ∀ z, δ z ≠ 0) (z : ι) :
    directionFieldRadical h2 hδ z * directionFieldRadical h2 hδ z
      = algebraMap (RatFunc A) ↥(directionField h2 hδ)
        (algebraMap (Polynomial A) (RatFunc A)
          (Polynomial.C (δ z * δ z) + Polynomial.C (4 : A) * Polynomial.X ^ 2)) := by
  apply Subtype.ext
  show directionRadical h2 (hδ z) * directionRadical h2 (hδ z) = _
  rw [directionRadical_sq]
  rfl

/-- **Every radical flip of one transverse direction is realized.** -/
theorem exists_directionFlip (h2 : (2 : A) ≠ 0) {δ : ι → A}
    (hδ : ∀ z, δ z ≠ 0) (hinj : Function.Injective δ) (hne : ∀ z z', δ z ≠ -δ z') (z₀ : ι) :
    ∃ σ : ↥(directionField h2 hδ) ≃ₐ[RatFunc A] ↥(directionField h2 hδ),
      (∀ z, z ≠ z₀ → σ (directionFieldRadical h2 hδ z) = directionFieldRadical h2 hδ z) ∧
      σ (directionFieldRadical h2 hδ z₀) = -(directionFieldRadical h2 hδ z₀) := by
  classical
  set g : ι → LaurentSeries A := fun z => directionRadical h2 (hδ z) with hg
  set L : IntermediateField (RatFunc A) (LaurentSeries A) := directionField h2 hδ with hLdef
  set ρ : ι → ↥L := directionFieldRadical h2 hδ with hρ
  set enum : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with henum
  have h2L : (2 : ↥L) ≠ 0 := by
    intro hcon
    have h1 : (2 : RatFunc A) = 0 :=
      (algebraMap (RatFunc A) ↥L).injective (by rw [map_ofNat, map_zero]; exact hcon)
    have h3 : (2 : Polynomial A) = 0 :=
      (IsFractionRing.injective (Polynomial A) (RatFunc A))
        (by rw [map_ofNat, map_zero]; exact h1)
    exact h2 (Polynomial.C_eq_zero.mp (by rw [map_ofNat]; exact h3))
  have hsq : ∀ z, ρ z * ρ z ∈ baseRange (RatFunc A) ↥L := by
    intro z
    rw [hρ, directionFieldRadical_sq]
    exact ⟨_, rfl⟩
  have hprodeq : ∀ T : Finset ι, (∏ z ∈ T, ρ z * ρ z)
      = algebraMap (RatFunc A) ↥L (algebraMap (Polynomial A) (RatFunc A)
          (∏ z ∈ T, (Polynomial.C (δ z * δ z) + Polynomial.C (4 : A) * Polynomial.X ^ 2))) := by
    intro T
    rw [map_prod, map_prod]
    exact Finset.prod_congr rfl fun z _ => by rw [hρ, directionFieldRadical_sq]
  have hindep : ∀ T : Finset ι, T.Nonempty →
      ¬ IsSqIn (baseRange (RatFunc A) ↥L) (∏ z ∈ T, ρ z * ρ z) := by
    intro T hT hcon
    obtain ⟨w, hwmem, hw⟩ := hcon
    obtain ⟨v, hv⟩ := hwmem
    haveI : Nonempty T := hT.to_subtype
    rw [hprodeq T, ← hv] at hw
    have hinj' : Function.Injective
        (algebraMap (RatFunc A) ↥L) := (algebraMap (RatFunc A) ↥L).injective
    have hsquare : algebraMap (Polynomial A) (RatFunc A)
        (∏ z ∈ T, (Polynomial.C (δ z * δ z) + Polynomial.C (4 : A) * Polynomial.X ^ 2))
        = v * v := hinj' (by rw [hw, map_mul])
    refine not_isSquare_prod_sq_add_four_sq' (K := A) h2
      (δ := fun z : T => δ (z : ι)) (fun a b hab => Subtype.ext (hinj hab))
      (fun a b => hne _ _) ⟨v, ?_⟩
    rw [← hsquare]
    congr 1
    rw [← Finset.prod_coe_sort T]
    exact Finset.prod_congr rfl fun z _ => by
      rw [map_ofNat, ← Polynomial.C_pow]
      ring_nf
  have htop : radicalStage (baseRange (RatFunc A) ↥L)
      (fun n => if h : n < Fintype.card ι then ρ (enum.symm ⟨n, h⟩) else 1)
      (Fintype.card ι) = ⊤ := by
    have himage : (fun n => if h : n < Fintype.card ι then ρ (enum.symm ⟨n, h⟩) else 1) ''
        (Set.Iio (Fintype.card ι)) = Set.range ρ := by
      ext w
      constructor
      · rintro ⟨n, hn, rfl⟩
        have hn' : n < Fintype.card ι := hn
        refine ⟨enum.symm ⟨n, hn'⟩, ?_⟩
        show ρ (enum.symm ⟨n, hn'⟩)
          = (if h : n < Fintype.card ι then ρ (enum.symm ⟨n, h⟩) else 1)
        rw [dif_pos hn']
      · rintro ⟨z, rfl⟩
        refine ⟨((enum z : Fin (Fintype.card ι)) : ℕ), (enum z).2, ?_⟩
        show (if h : ((enum z : Fin (Fintype.card ι)) : ℕ) < Fintype.card ι then
            ρ (enum.symm ⟨((enum z : Fin (Fintype.card ι)) : ℕ), h⟩) else 1) = ρ z
        rw [dif_pos (enum z).2]
        congr 1
        simp
    have hadjoin : IntermediateField.adjoin (RatFunc A) (Set.range ρ) = ⊤ :=
      adjoin_range_corestrict_eq_top g
    rw [radicalStage, himage]
    have := congrArg IntermediateField.toSubfield hadjoin
    exact this
  obtain ⟨σ, hfix, hneg⟩ :=
    exists_algEquiv_neg_of_index (F := RatFunc A) ρ h2L enum hsq hindep htop Fintype.card_pos z₀
  exact ⟨σ, hfix, hneg⟩

end

end GaloisForLFunctions.HTGeometry
