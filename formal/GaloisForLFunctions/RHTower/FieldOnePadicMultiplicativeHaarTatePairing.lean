import GaloisForLFunctions.RHTower.FieldOnePadicRamifiedTatePairing
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Multiplicative p-adic unit Haar form of Tate's local equation

This file supplies the multiplicative-measure infrastructure absent from the
additive Fourier development. It proves exact Haar quadrature through any
finite multiplicative quotient, constructs probability Haar measure on
`ℤ_pˣ`, proves reduction `ℤ_pˣ → (ZMod (p^n))ˣ` is continuous and onto at
every depth (including depth zero), and establishes exact quadrature on that
quotient.

Combining this with the arbitrary-test ramified Fourier pairing gives the
multiplicative-unit Haar functional equation for every residue-level test and
every exact-conductor primitive character. Thus angular integration now uses
the literal compact factor of `ℚ_pˣ`, rather than additive unit-ball measure.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory MeasureTheory.Measure Set TopologicalSpace
open scoped BigOperators

/-- Translation of representatives in a finite multiplicative quotient only
permutes the quotient classes. -/
theorem fieldOneFiniteMulQuotient_average_eq
    {G Q : Type*} [CommGroup G] [CommGroup Q] [Fintype Q]
    (q : G →* Q) (hq : Function.Surjective q)
    (rep : Q → G) (hrep : ∀ r, q (rep r) = r)
    (f : G → ℂ)
    (hclass : ∀ {x y : G}, q x = q y → f x = f y)
    (x : G) :
    ∑ r : Q, f (rep r * x) = ∑ r : Q, f (rep r) := by
  obtain ⟨s, hs⟩ := hq (q x)
  apply Finset.sum_equiv (Equiv.mulRight (q x))
  · simp
  · intro r _
    apply hclass
    rw [map_mul, hrep, hrep]
    rfl

/-- Exact quadrature through a finite multiplicative quotient of a compact
Haar probability group. -/
theorem fieldOneFiniteMulQuotient_sampleSum_eq_nsmul_integral
    {G Q : Type*} [CommGroup G] [CommGroup Q] [Fintype Q]
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [IsTopologicalGroup G]
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (hμ : μ Set.univ = 1)
    (q : G →* Q) (hq : Function.Surjective q)
    (rep : Q → G) (hrep : ∀ r, q (rep r) = r)
    (f : G → ℂ) (hf : Integrable f μ)
    (hclass : ∀ {x y : G}, q x = q y → f x = f y) :
    ∑ r : Q, f (rep r) =
      Fintype.card Q • (∫ x, f x ∂μ) := by
  calc
    ∑ r : Q, f (rep r) =
        ∫ _ : G, (∑ r : Q, f (rep r)) ∂μ := by
      rw [integral_const, Measure.real, hμ]
      simp
    _ = ∫ x : G, (∑ r : Q, f (rep r * x)) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        (fieldOneFiniteMulQuotient_average_eq q hq rep hrep f hclass x).symm
    _ = ∑ r : Q, ∫ x : G, f (rep r * x) ∂μ := by
      apply integral_finsetSum
      intro r _
      exact hf.comp_mul_left _
    _ = ∑ _r : Q, ∫ x : G, f x ∂μ := by
      apply Finset.sum_congr rfl
      intro r _
      exact integral_mul_left_eq_self f _
    _ = Fintype.card Q • (∫ x, f x ∂μ) := by
      rw [Finset.sum_const, Finset.card_univ]

variable (p : ℕ) [Fact p.Prime]

noncomputable instance fieldOnePadicUnitMeasurableSpace :
    MeasurableSpace ℤ_[p]ˣ := borel ℤ_[p]ˣ

instance fieldOnePadicUnitBorelSpace : BorelSpace ℤ_[p]ˣ := ⟨rfl⟩

def fieldOnePadicUnitPositiveCompacts : PositiveCompacts ℤ_[p]ˣ := ⊤

def fieldOnePadicUnitNormalizedHaar : Measure ℤ_[p]ˣ :=
  Measure.haarMeasure (fieldOnePadicUnitPositiveCompacts p)

instance fieldOnePadicUnitNormalizedHaar_isHaar :
    IsHaarMeasure (fieldOnePadicUnitNormalizedHaar p) := by
  unfold fieldOnePadicUnitNormalizedHaar
  infer_instance

@[simp] theorem fieldOnePadicUnitNormalizedHaar_univ :
    fieldOnePadicUnitNormalizedHaar p Set.univ = 1 := by
  exact Measure.haarMeasure_self

def fieldOnePadicUnitReduction (n : ℕ) :
    ℤ_[p]ˣ →* (ZMod (p ^ n))ˣ :=
  Units.map (PadicInt.toZModPow n).toMonoidHom

theorem fieldOnePadicUnitReduction_continuous (n : ℕ) :
    Continuous (fieldOnePadicUnitReduction p n) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact (fieldOnePadicInt_toZModPow_continuous p n).comp Units.continuous_val
  · exact (fieldOnePadicInt_toZModPow_continuous p n).comp Units.continuous_coe_inv

theorem fieldOnePadicUnitReduction_surjective (n : ℕ) :
    Function.Surjective (fieldOnePadicUnitReduction p n) := by
  by_cases hn : n = 0
  · subst n
    letI : Subsingleton (ZMod (p ^ 0)) :=
      ZMod.subsingleton_iff.mpr (by simp)
    intro u
    refine ⟨1, ?_⟩
    apply Units.ext
    exact Subsingleton.elim _ _
  · intro u
    have hcoprimePow : u.val.val.Coprime (p ^ n) :=
      ZMod.val_coe_unit_coprime u
    have hcoprime : p.Coprime u.val.val := by
      exact ((Nat.coprime_pow_right_iff (Nat.pos_of_ne_zero hn) u.val.val p).mp
        hcoprimePow).symm
    have hunit : IsUnit ((u.val.val : ℕ) : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact hcoprime
    refine ⟨hunit.unit, ?_⟩
    apply Units.ext
    simp only [fieldOnePadicUnitReduction, Units.coe_map]
    rw [IsUnit.unit_spec]
    calc
      PadicInt.toZModPow n ((u.val.val : ℕ) : ℤ_[p]) =
          (u.val.val : ZMod (p ^ n)) := by exact map_natCast _ _
      _ = u.val := ZMod.natCast_zmod_val u.val

noncomputable def fieldOnePadicUnitResidueRep (n : ℕ) :
    (ZMod (p ^ n))ˣ → ℤ_[p]ˣ :=
  fun r => Classical.choose (fieldOnePadicUnitReduction_surjective p n r)

theorem fieldOnePadicUnitResidueRep_spec (n : ℕ)
    (r : (ZMod (p ^ n))ˣ) :
    fieldOnePadicUnitReduction p n
      (fieldOnePadicUnitResidueRep p n r) = r :=
  Classical.choose_spec (fieldOnePadicUnitReduction_surjective p n r)

theorem fieldOnePadicUnit_sampleSum_eq_nsmul_integral
    (n : ℕ) (f : ℤ_[p]ˣ → ℂ)
    (hf : Integrable f (fieldOnePadicUnitNormalizedHaar p))
    (hclass : ∀ {x y : ℤ_[p]ˣ},
      fieldOnePadicUnitReduction p n x =
        fieldOnePadicUnitReduction p n y → f x = f y) :
    ∑ r : (ZMod (p ^ n))ˣ,
        f (fieldOnePadicUnitResidueRep p n r) =
      Fintype.card (ZMod (p ^ n))ˣ •
        (∫ u, f u ∂fieldOnePadicUnitNormalizedHaar p) := by
  exact fieldOneFiniteMulQuotient_sampleSum_eq_nsmul_integral
    (fieldOnePadicUnitNormalizedHaar p)
    (fieldOnePadicUnitNormalizedHaar_univ p)
    (fieldOnePadicUnitReduction p n)
    (fieldOnePadicUnitReduction_surjective p n)
    (fieldOnePadicUnitResidueRep p n)
    (fieldOnePadicUnitResidueRep_spec p n)
    f hf hclass

/-- A sum weighted by a multiplicative character is supported on units. -/
theorem fieldOneSum_mulChar_eq_sum_units
    {R : Type*} [CommMonoidWithZero R] [Fintype R]
    [DecidableEq R] (χ : MulChar R ℂ) (f : R → ℂ) :
    ∑ x : R, f x * χ x = ∑ u : Rˣ, f u * χ u := by
  let e : Rˣ ↪ R := ⟨((↑) : Rˣ → R), Units.val_injective⟩
  let U : Finset R := Finset.univ.map e
  have hsubset : U ⊆ Finset.univ := Finset.subset_univ U
  calc
    _ = ∑ x ∈ U, f x * χ x := by
      symm
      apply Finset.sum_subset hsubset
      intro x _ hxU
      have hnonunit : ¬IsUnit x := by
        intro hx
        apply hxU
        exact Finset.mem_map.mpr ⟨hx.unit, Finset.mem_univ _, hx.unit_spec⟩
      rw [MulChar.map_nonunit χ hnonunit, mul_zero]
    _ = _ := by
      simp only [U, e, Finset.sum_map,
        Function.Embedding.coeFn_mk]

/-- Pullback of a finite residue test to the compact p-adic unit group. -/
def fieldOnePadicUnitResidueLift (n : ℕ)
    (f : ZMod (p ^ n) → ℂ) : ℤ_[p]ˣ → ℂ :=
  fun u => f ((fieldOnePadicUnitReduction p n u :
    (ZMod (p ^ n))ˣ) : ZMod (p ^ n))

theorem continuous_fieldOnePadicUnitResidueLift (n : ℕ)
    (f : ZMod (p ^ n) → ℂ) :
    Continuous (fieldOnePadicUnitResidueLift p n f) := by
  exact (continuous_of_discreteTopology : Continuous
    (fun u : (ZMod (p ^ n))ˣ => f u)).comp
      (fieldOnePadicUnitReduction_continuous p n)

theorem integrable_fieldOnePadicUnitResidueLift (n : ℕ)
    (f : ZMod (p ^ n) → ℂ) :
    Integrable (fieldOnePadicUnitResidueLift p n f)
      (fieldOnePadicUnitNormalizedHaar p) := by
  exact (continuous_fieldOnePadicUnitResidueLift p n f).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem fieldOnePadicUnitResidueLift_integral
    (n : ℕ) (f : ZMod (p ^ n) → ℂ) :
    ∫ u, fieldOnePadicUnitResidueLift p n f u
        ∂fieldOnePadicUnitNormalizedHaar p =
      ((Fintype.card (ZMod (p ^ n))ˣ : ℕ) : ℂ)⁻¹ *
        ∑ r : (ZMod (p ^ n))ˣ, f r := by
  have hclass : ∀ {x y : ℤ_[p]ˣ},
      fieldOnePadicUnitReduction p n x =
        fieldOnePadicUnitReduction p n y →
      fieldOnePadicUnitResidueLift p n f x =
        fieldOnePadicUnitResidueLift p n f y := by
    intro x y hxy
    unfold fieldOnePadicUnitResidueLift
    rw [hxy]
  have hquad := fieldOnePadicUnit_sampleSum_eq_nsmul_integral
    p n (fieldOnePadicUnitResidueLift p n f)
    (integrable_fieldOnePadicUnitResidueLift p n f) hclass
  have hsamples :
      (∑ r : (ZMod (p ^ n))ˣ,
        fieldOnePadicUnitResidueLift p n f
          (fieldOnePadicUnitResidueRep p n r)) =
      ∑ r : (ZMod (p ^ n))ˣ, f r := by
    apply Finset.sum_congr rfl
    intro r _
    unfold fieldOnePadicUnitResidueLift
    rw [fieldOnePadicUnitResidueRep_spec]
  rw [hsamples] at hquad
  rw [hquad]
  simp only [nsmul_eq_mul]
  have hcard : ((Fintype.card (ZMod (p ^ n))ˣ : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- Multiplicative-unit Haar form of the arbitrary-test ramified local
functional equation. -/
theorem fieldOnePadicPrimitiveAngular_unitHaarPairing
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (f : ZMod (p ^ n) → ℂ) :
    ∫ u, fieldOnePadicUnitResidueLift p n
        (fun k => (((p ^ n : ℕ) : ℂ)⁻¹ * ZMod.dft f k) * χ.1 k) u
        ∂fieldOnePadicUnitNormalizedHaar p =
      (((p ^ n : ℕ) : ℂ)⁻¹ * gaussSum χ.1 ZMod.stdAddChar) *
        ∫ u, fieldOnePadicUnitResidueLift p n
          (fun j => f j * χ.1⁻¹ (-j)) u
          ∂fieldOnePadicUnitNormalizedHaar p := by
  rw [fieldOnePadicUnitResidueLift_integral,
    fieldOnePadicUnitResidueLift_integral]
  have hleft := fieldOneSum_mulChar_eq_sum_units χ.1
    (fun k : ZMod (p ^ n) => ((p ^ n : ℕ) : ℂ)⁻¹ * ZMod.dft f k)
  have hright := fieldOneSum_mulChar_eq_sum_units χ.1⁻¹
    (fun j : ZMod (p ^ n) => f (-j))
  have hright' :
      (∑ u : (ZMod (p ^ n))ˣ, f u * χ.1⁻¹ (-u.val)) =
        ∑ j : ZMod (p ^ n), f j * χ.1⁻¹ (-j) := by
    have hunitNeg :
        (∑ u : (ZMod (p ^ n))ˣ, f u * χ.1⁻¹ (-u.val)) =
          ∑ u : (ZMod (p ^ n))ˣ, f (-u.val) * χ.1⁻¹ u.val := by
      exact Fintype.sum_equiv
        (Equiv.mulLeft (-1 : (ZMod (p ^ n))ˣ)) _ _ (fun u => by simp)
    have hfullNeg :
        (∑ j : ZMod (p ^ n), f j * χ.1⁻¹ (-j)) =
          ∑ j : ZMod (p ^ n), f (-j) * χ.1⁻¹ j := by
      exact Fintype.sum_equiv (Equiv.neg (ZMod (p ^ n))) _ _
        (fun j => by simp)
    exact hunitNeg.trans (hright.symm.trans hfullNeg.symm)
  rw [← hleft]
  have hleftFactor :
      (∑ k : ZMod (p ^ n),
        (((p ^ n : ℕ) : ℂ)⁻¹ * ZMod.dft f k) * χ.1 k) =
      ((p ^ n : ℕ) : ℂ)⁻¹ *
        ∑ k : ZMod (p ^ n), ZMod.dft f k * χ.1 k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring_nf
  rw [hleftFactor, hright']
  rw [fieldOneFinitePrimitiveAngular_dft_pairing p n χ f]
  ring_nf

end
end GaloisForLFunctions.RHTower

