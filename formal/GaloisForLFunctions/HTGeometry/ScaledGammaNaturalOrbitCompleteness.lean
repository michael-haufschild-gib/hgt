import GaloisForLFunctions.HTGeometry.ScaledGammaBorelResidue
import GaloisForLFunctions.HTGeometry.GammaComplexLatticeCharge
import GaloisForLFunctions.HTGeometry.MeromorphicGammaScaleDifferential

namespace GaloisForLFunctions.HTGeometry

open Complex
open Bottcher
open _root_.HTGeometry
open Filter Set Topology
open scoped BigOperators

noncomputable section

local instance scaledGammaOrbitDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance scaledGammaOrbitComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance scaledGammaOrbitComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance scaledGammaOrbitDifferential : Differential (meroField Set.univ) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance scaledGammaOrbitRatFuncAlgebra : Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (Bottcher.ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance scaledGammaOrbitRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance scaledGammaOrbitDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance scaledGammaOrbitCharZero : CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

/-- Positive-scale factor family with natural scales. -/
def naturalScaleGammaFactor {d : ℕ} (n : Fin d → ℕ) (a : Fin d → ℂ)
    (m : Fin d → ℤ) (hn : ∀ i, 0 < n i) (i : Fin d) : PositiveAffineGammaFactor where
  scale := n i
  offset := a i
  multiplicity := m i
  scale_pos := by exact_mod_cast hn i

/-- Gauss-refined slots of a natural-scale Gamma family. -/
abbrev NaturalScaleGammaSlot {d : ℕ} (n : Fin d → ℕ) := Σ i, Fin (n i)

/-- Unit-scale shift attached to one Gauss-refined slot. -/
def naturalScaleGammaSlotShift {d : ℕ} (n : Fin d → ℕ)
    (a : Fin d → ℂ) (x : NaturalScaleGammaSlot n) : ℂ :=
  (a x.1 + (x.2 : ℕ)) / n x.1

/-- Integer-translation equivalence of refined Gamma slots. -/
abbrev naturalScaleGammaSlotRel {d : ℕ} (n : Fin d → ℕ)
    (a : Fin d → ℂ) (x y : NaturalScaleGammaSlot n) : Prop :=
  gammaShiftOrbitRel (naturalScaleGammaSlotShift n a) x y

theorem naturalScaleGammaSlotRel_refl {d : ℕ} (n : Fin d → ℕ)
    (a : Fin d → ℂ) (x : NaturalScaleGammaSlot n) :
    naturalScaleGammaSlotRel n a x x := ⟨0, by simp⟩

theorem naturalScaleGammaSlotRel_symm {d : ℕ} (n : Fin d → ℕ)
    (a : Fin d → ℂ) {x y : NaturalScaleGammaSlot n} :
    naturalScaleGammaSlotRel n a x y → naturalScaleGammaSlotRel n a y x := by
  rintro ⟨q, hq⟩
  refine ⟨-q, ?_⟩
  push_cast
  linear_combination -hq

theorem naturalScaleGammaSlotRel_trans {d : ℕ} (n : Fin d → ℕ)
    (a : Fin d → ℂ) {x y z : NaturalScaleGammaSlot n} :
    naturalScaleGammaSlotRel n a x y → naturalScaleGammaSlotRel n a y z →
      naturalScaleGammaSlotRel n a x z := by
  rintro ⟨q, hq⟩ ⟨r, hr⟩
  refine ⟨q + r, ?_⟩
  push_cast
  linear_combination hq + hr

/-- Canonical integer-translation setoid on refined slots. -/
def naturalScaleGammaSlotSetoid {d : ℕ} (n : Fin d → ℕ)
    (a : Fin d → ℂ) : Setoid (NaturalScaleGammaSlot n) :=
  gammaShiftOrbitSetoid (naturalScaleGammaSlotShift n a)

/-- Canonical finite set of shift orbits after simultaneous Gauss refinement. -/
abbrev NaturalScaleGammaOrbit {d : ℕ} (n : Fin d → ℕ)
    (a : Fin d → ℂ) := GammaShiftOrbit (naturalScaleGammaSlotShift n a)

noncomputable instance naturalScaleGammaOrbitDecidableEq {d : ℕ} (n : Fin d → ℕ)
    (a : Fin d → ℂ) : DecidableEq (NaturalScaleGammaOrbit n a) :=
  gammaShiftOrbitDecidableEq _

noncomputable instance naturalScaleGammaOrbitFintype {d : ℕ} (n : Fin d → ℕ)
    (a : Fin d → ℂ) : Fintype (NaturalScaleGammaOrbit n a) :=
  gammaShiftOrbitFintype _

/-- Exponential phase of a canonical refined shift orbit. -/
def naturalScaleGammaOrbitPhase {d : ℕ} (n : Fin d → ℕ)
    (a : Fin d → ℂ) : NaturalScaleGammaOrbit n a → ℂ :=
  Quotient.lift
    (fun x : NaturalScaleGammaSlot n =>
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * naturalScaleGammaSlotShift n a x))
    (by
      intro x y hxy
      obtain ⟨q, hq⟩ := hxy
      rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨-q, ?_⟩
      push_cast
      linear_combination
        (-2 * (Real.pi : ℂ) * Complex.I) * hq)

theorem naturalScaleGammaOrbitPhase_ne_zero {d : ℕ} (n : Fin d → ℕ)
    (a : Fin d → ℂ) (c : NaturalScaleGammaOrbit n a) :
    naturalScaleGammaOrbitPhase n a c ≠ 0 := by
  induction c using Quotient.inductionOn
  exact Complex.exp_ne_zero _

theorem naturalScaleGammaOrbitPhase_injective {d : ℕ} (n : Fin d → ℕ)
    (a : Fin d → ℂ) : Function.Injective (naturalScaleGammaOrbitPhase n a) := by
  intro c e hce
  induction c using Quotient.inductionOn with
  | _ x =>
    induction e using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      change Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
          naturalScaleGammaSlotShift n a x) =
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
          naturalScaleGammaSlotShift n a y) at hce
      rw [Complex.exp_eq_exp_iff_exists_int] at hce
      obtain ⟨q, hq⟩ := hce
      refine ⟨-q, ?_⟩
      have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
        exact mul_ne_zero (mul_ne_zero (by norm_num)
          (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
      apply (mul_left_cancel₀ hpi)
      push_cast at hq ⊢
      linear_combination -hq

/-- Total signed multiplicity on one canonical refined shift orbit. -/
abbrev naturalScaleGammaOrbitCharge {d : ℕ} (n : Fin d → ℕ)
    (a : Fin d → ℂ) (m : Fin d → ℤ)
    (c : NaturalScaleGammaOrbit n a) : ℤ :=
  gammaShiftOrbitCharge (naturalScaleGammaSlotShift n a) (fun x => m x.1) c

/-- Complex form of one canonical refined orbit charge. -/
def naturalScaleGammaOrbitChargeC {d : ℕ} (n : Fin d → ℕ)
    (a : Fin d → ℂ) (m : Fin d → ℤ)
    (c : NaturalScaleGammaOrbit n a) : ℂ :=
  ∑ x, if Quotient.mk'' x = c then (m x.1 : ℂ) else 0

theorem naturalScaleGammaOrbitChargeC_eq_cast {d : ℕ} (n : Fin d → ℕ)
    (a : Fin d → ℂ) (m : Fin d → ℤ)
    (c : NaturalScaleGammaOrbit n a) :
    naturalScaleGammaOrbitChargeC n a m c = (naturalScaleGammaOrbitCharge n a m c : ℂ) := by
  rw [naturalScaleGammaOrbitChargeC, naturalScaleGammaOrbitCharge,
    gammaShiftOrbitCharge]
  push_cast
  rfl

/-- Fourier character of all unit-scale slots created by simultaneous Gauss refinement. -/
def naturalScaleGammaRefinedCharacter {d : ℕ} (n : Fin d → ℕ)
    (a : Fin d → ℂ) (m : Fin d → ℤ) (ell : ℤ) : ℂ :=
  ∑ x : NaturalScaleGammaSlot n, (m x.1 : ℂ) *
    Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (ell : ℂ) *
      naturalScaleGammaSlotShift n a x)

theorem naturalScaleGammaOrbitPhase_mk_pow {d : ℕ} (n : Fin d → ℕ)
    (a : Fin d → ℂ) (x : NaturalScaleGammaSlot n) (k : ℕ) :
    naturalScaleGammaOrbitPhase n a (Quotient.mk'' x) ^ k =
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) *
        naturalScaleGammaSlotShift n a x) := by
  rw [naturalScaleGammaOrbitPhase, Quotient.lift_mk, ← Complex.exp_nat_mul]
  congr 1
  ring

theorem naturalScaleGammaOrbitPhase_mk_zpow {d : ℕ} (n : Fin d → ℕ)
    (a : Fin d → ℂ) (x : NaturalScaleGammaSlot n) (ell : ℤ) :
    naturalScaleGammaOrbitPhase n a (Quotient.mk'' x) ^ ell =
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (ell : ℂ) *
        naturalScaleGammaSlotShift n a x) := by
  rw [naturalScaleGammaOrbitPhase, Quotient.lift_mk]
  rw [show -2 * (Real.pi : ℂ) * Complex.I * (ell : ℂ) *
        naturalScaleGammaSlotShift n a x =
      (ell : ℂ) * (-2 * (Real.pi : ℂ) * Complex.I *
        naturalScaleGammaSlotShift n a x) by ring,
    Complex.exp_int_mul]

/-- Regrouping refined Gauss slots by their canonical integer-translation orbit. -/
theorem naturalScaleGammaOrbitMoment_eq_refinedCharacter {d : ℕ}
    (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ) (k : ℕ) :
    ∑ c : NaturalScaleGammaOrbit n a,
        naturalScaleGammaOrbitChargeC n a m c *
          naturalScaleGammaOrbitPhase n a c ^ k =
      naturalScaleGammaRefinedCharacter n a m k := by
  classical
  rw [naturalScaleGammaRefinedCharacter]
  calc
    ∑ c : NaturalScaleGammaOrbit n a,
        naturalScaleGammaOrbitChargeC n a m c *
          naturalScaleGammaOrbitPhase n a c ^ k =
      ∑ c : NaturalScaleGammaOrbit n a,
        ∑ x : NaturalScaleGammaSlot n,
          if Quotient.mk'' x = c then
            (m x.1 : ℂ) * naturalScaleGammaOrbitPhase n a (Quotient.mk'' x) ^ k else 0 := by
            apply Finset.sum_congr rfl
            intro c hc
            rw [naturalScaleGammaOrbitChargeC, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hxc : Quotient.mk'' x = c
            · simp only [if_pos hxc]
              rw [hxc]
            · simp only [if_neg hxc, zero_mul]
    _ = ∑ x : NaturalScaleGammaSlot n,
          (m x.1 : ℂ) * naturalScaleGammaOrbitPhase n a (Quotient.mk'' x) ^ k := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.sum_eq_single (Quotient.mk'' x)]
            · simp
            · intro c hc hcx
              simp [hcx.symm]
            · intro hnot
              exact (hnot (Finset.mem_univ _)).elim
    _ = ∑ x : NaturalScaleGammaSlot n, (m x.1 : ℂ) *
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) *
            naturalScaleGammaSlotShift n a x) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [naturalScaleGammaOrbitPhase_mk_pow]

/-- Laurent-moment regrouping, including negative Borel lattice frequencies. -/
theorem naturalScaleGammaOrbitLaurentMoment_eq_refinedCharacter {d : ℕ}
    (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ) (ell : ℤ) :
    ∑ c : NaturalScaleGammaOrbit n a,
        naturalScaleGammaOrbitChargeC n a m c *
          naturalScaleGammaOrbitPhase n a c ^ ell =
      naturalScaleGammaRefinedCharacter n a m ell := by
  classical
  rw [naturalScaleGammaRefinedCharacter]
  calc
    ∑ c : NaturalScaleGammaOrbit n a,
        naturalScaleGammaOrbitChargeC n a m c *
          naturalScaleGammaOrbitPhase n a c ^ ell =
      ∑ c : NaturalScaleGammaOrbit n a,
        ∑ x : NaturalScaleGammaSlot n,
          if Quotient.mk'' x = c then
            (m x.1 : ℂ) * naturalScaleGammaOrbitPhase n a (Quotient.mk'' x) ^ ell else 0 := by
            apply Finset.sum_congr rfl
            intro c hc
            rw [naturalScaleGammaOrbitChargeC, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hxc : Quotient.mk'' x = c
            · simp only [if_pos hxc]
              rw [hxc]
            · simp only [if_neg hxc, zero_mul]
    _ = ∑ x : NaturalScaleGammaSlot n,
          (m x.1 : ℂ) * naturalScaleGammaOrbitPhase n a (Quotient.mk'' x) ^ ell := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.sum_eq_single (Quotient.mk'' x)]
            · simp
            · intro c hc hcx
              simp [hcx.symm]
            · intro hnot
              exact (hnot (Finset.mem_univ _)).elim
    _ = ∑ x : NaturalScaleGammaSlot n, (m x.1 : ℂ) *
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (ell : ℂ) *
            naturalScaleGammaSlotShift n a x) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [naturalScaleGammaOrbitPhase_mk_zpow]

/-- The refined character is the sum of the Gauss packets of the original natural-scale
factors. -/
theorem naturalScaleGammaRefinedCharacter_eq_sum_gauss {d : ℕ}
    (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ) (ell : ℤ) :
    naturalScaleGammaRefinedCharacter n a m ell =
      ∑ i, gaussExpandedComplexGammaCharge 1 (a i) (m i) (n i) ell := by
  classical
  rw [naturalScaleGammaRefinedCharacter, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  rw [gaussExpandedComplexGammaCharge, one_mul, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r hr
  rw [naturalScaleGammaSlotShift]

/-- Complex-slope view of one positive natural-scale factor. -/
def naturalScaleComplexGammaFactor {d : ℕ} (n : Fin d → ℕ) (a : Fin d → ℂ)
    (m : Fin d → ℤ) (hn : ∀ i, 0 < n i) (i : Fin d) : ComplexAffineGammaFactor where
  slope := n i
  offset := a i
  multiplicity := m i
  slope_ne_zero := by exact_mod_cast (hn i).ne'

theorem gaussExpandedComplexGammaCharge_eq_naturalScaleFactorCharge
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hn : ∀ i, 0 < n i) (ell : ℤ) (hell : ell ≠ 0) (i : Fin d) :
    gaussExpandedComplexGammaCharge 1 (a i) (m i) (n i) ell =
      complexGammaFactorChargeAt (naturalScaleComplexGammaFactor n a m hn i) (ell : ℂ) := by
  classical
  by_cases hd : (n i : ℤ) ∣ ell
  · obtain ⟨q, rfl⟩ := hd
    have hq : q ≠ 0 := by
      intro hq
      subst q
      simp at hell
    have hsupport : (((n i : ℤ) * q : ℤ) : ℂ) ∈
        complexGammaIntegerLattice (naturalScaleComplexGammaFactor n a m hn i).slope := by
      exact ⟨q, hq, by simp [naturalScaleComplexGammaFactor]; ring⟩
    rw [complexGammaFactorChargeAt, if_pos hsupport,
      gaussExpandedComplexGammaCharge_eq_original (hn i) 1 (a i) (m i) q]
    rw [complexGammaChargeTerm]
    have hnC : (n i : ℂ) ≠ 0 := by exact_mod_cast (hn i).ne'
    have hratio : ((((n i : ℤ) * q : ℤ) : ℂ)) / (n i : ℂ) = (q : ℂ) := by
      push_cast
      field_simp
    simp only [naturalScaleComplexGammaFactor]
    rw [hratio]
    ring
  · have hsupport : (ell : ℂ) ∉
        complexGammaIntegerLattice (naturalScaleComplexGammaFactor n a m hn i).slope := by
      rintro ⟨q, hq, heq⟩
      apply hd
      refine ⟨q, ?_⟩
      simp only [naturalScaleComplexGammaFactor] at heq
      have hZ : ell = q * (n i : ℤ) := by exact_mod_cast heq
      simpa [mul_comm] using hZ
    rw [complexGammaFactorChargeAt, if_neg hsupport,
      gaussExpandedComplexGammaCharge_eq_zero_of_not_dvd (hn i) 1 (a i) (m i) ell hd]

/-- Intrinsic positive-real charge contribution of one natural-scale factor. -/
def naturalScalePositiveGammaFactorChargeAt
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (t : ℝ) (i : Fin d) : ℂ := by
  classical
  exact if ∃ k : ℤ, k ≠ 0 ∧ t = (k : ℝ) * (n i : ℝ) then
    (m i : ℂ) * (n i : ℂ) *
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
        (((t / (n i : ℝ) : ℝ)) : ℂ) * a i)
  else 0

theorem scaledGammaNaturalFactorCharge_eq_complexFactorCharge
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hn : ∀ i, 0 < n i) (t : ℝ) (i : Fin d) :
    naturalScalePositiveGammaFactorChargeAt n a m t i =
      complexGammaFactorChargeAt (naturalScaleComplexGammaFactor n a m hn i) (t : ℂ) := by
  classical
  rw [naturalScalePositiveGammaFactorChargeAt]
  by_cases hs : ∃ k : ℤ, k ≠ 0 ∧ t = (k : ℝ) * (n i : ℝ)
  · have hs0 := hs
    obtain ⟨k, hk, htk⟩ := hs
    have hc : (t : ℂ) ∈
        complexGammaIntegerLattice (naturalScaleComplexGammaFactor n a m hn i).slope := by
      exact ⟨k, hk, by simp [naturalScaleComplexGammaFactor]; exact_mod_cast htk⟩
    rw [if_pos hs0, complexGammaFactorChargeAt, if_pos hc]
    simp only [naturalScaleComplexGammaFactor]
    norm_cast
  · have hc : (t : ℂ) ∉
        complexGammaIntegerLattice (naturalScaleComplexGammaFactor n a m hn i).slope := by
      rintro ⟨k, hk, htk⟩
      apply hs
      refine ⟨k, hk, ?_⟩
      simp only [naturalScaleComplexGammaFactor] at htk
      exact_mod_cast htk
    rw [if_neg hs, complexGammaFactorChargeAt, if_neg hc]

/-- Exact Gauss-refinement invariance of the scaled residue character for every nonzero integer
frequency. -/
theorem scaledGammaAlienChargeAt_naturalScale_integer_eq_refinedCharacter
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hn : ∀ i, 0 < n i) (ell : ℤ) (hell : ell ≠ 0) :
    scaledGammaAlienChargeAt (naturalScaleGammaFactor n a m hn) (ell : ℝ) =
      naturalScaleGammaRefinedCharacter n a m ell := by
  rw [naturalScaleGammaRefinedCharacter_eq_sum_gauss,
    scaledGammaAlienChargeAt]
  apply Finset.sum_congr rfl
  intro i hi
  rw [gaussExpandedComplexGammaCharge_eq_naturalScaleFactorCharge n a m hn ell hell i]
  change naturalScalePositiveGammaFactorChargeAt n a m (ell : ℝ) i =
    complexGammaFactorChargeAt (naturalScaleComplexGammaFactor n a m hn i) (ell : ℂ)
  exact scaledGammaNaturalFactorCharge_eq_complexFactorCharge n a m hn ell i

theorem scaledGammaAlienChargeAt_naturalScale_eq_zero_of_not_integer
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hn : ∀ i, 0 < n i) {t : ℝ} (ht : ¬ ∃ ell : ℤ, t = (ell : ℝ)) :
    scaledGammaAlienChargeAt (naturalScaleGammaFactor n a m hn) t = 0 := by
  rw [scaledGammaAlienChargeAt]
  apply Finset.sum_eq_zero
  intro i hi
  have hsupport : ¬ ∃ k : ℤ, k ≠ 0 ∧
      t = (k : ℝ) * (naturalScaleGammaFactor n a m hn i).scale := by
    rintro ⟨k, hk, htk⟩
    apply ht
    refine ⟨k * (n i : ℤ), ?_⟩
    simp only [naturalScaleGammaFactor] at htk
    rw [htk]
    push_cast
    rfl
  rw [if_neg hsupport]

/-- **Automatic common-scale completeness.**  For every finite positive natural-scale Gamma
family, vanishing of the actual scaled residue character is equivalent to cancellation of every
canonical shift-orbit charge produced by simultaneous Gauss refinement.  No reduced-block or
chosen-representative hypothesis remains. -/
theorem scaledGammaAlienChargeZero_naturalScale_iff_orbitCharge_zero
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hn : ∀ i, 0 < n i) :
    ScaledGammaAlienChargeZero (naturalScaleGammaFactor n a m hn) ↔
      ∀ c : NaturalScaleGammaOrbit n a, naturalScaleGammaOrbitCharge n a m c = 0 := by
  classical
  constructor
  · intro hzero
    let O := NaturalScaleGammaOrbit n a
    let e : O ≃ Fin (Fintype.card O) := Fintype.equivFin O
    let node : Fin (Fintype.card O) → ℂ :=
      fun j => naturalScaleGammaOrbitPhase n a (e.symm j)
    let charge : Fin (Fintype.card O) → ℤ :=
      fun j => naturalScaleGammaOrbitCharge n a m (e.symm j)
    have hnode : Function.Injective node :=
      (naturalScaleGammaOrbitPhase_injective n a).comp e.symm.injective
    have hnode0 : ∀ j, node j ≠ 0 :=
      fun j => naturalScaleGammaOrbitPhase_ne_zero n a (e.symm j)
    have hmom : ∀ k : Fin (Fintype.card O),
        commonComplexGammaCharge 1 node charge ((k : ℕ) + 1) = 0 := by
      intro k
      let ell : ℤ := ((k : ℕ) + 1 : ℕ)
      have hell : ell ≠ 0 := by
        dsimp [ell]
        omega
      have hz := hzero (ell : ℝ) (by exact_mod_cast hell)
      rw [scaledGammaAlienChargeAt_naturalScale_integer_eq_refinedCharacter
        n a m hn ell hell] at hz
      rw [← naturalScaleGammaOrbitMoment_eq_refinedCharacter n a m ((k : ℕ) + 1)] at hz
      rw [commonComplexGammaCharge, one_mul]
      change ∑ j : Fin (Fintype.card O),
          (naturalScaleGammaOrbitCharge n a m (e.symm j) : ℂ) *
            naturalScaleGammaOrbitPhase n a (e.symm j) ^ ((k : ℕ) + 1) = 0
      calc
        ∑ j : Fin (Fintype.card O),
            (naturalScaleGammaOrbitCharge n a m (e.symm j) : ℂ) *
              naturalScaleGammaOrbitPhase n a (e.symm j) ^ ((k : ℕ) + 1) =
          ∑ c : O, (naturalScaleGammaOrbitCharge n a m c : ℂ) *
              naturalScaleGammaOrbitPhase n a c ^ ((k : ℕ) + 1) :=
                by simpa using (Equiv.sum_comp e.symm
                  (fun c : O => (naturalScaleGammaOrbitCharge n a m c : ℂ) *
                    naturalScaleGammaOrbitPhase n a c ^ ((k : ℕ) + 1)))
        _ = 0 := by
          rw [← hz]
          apply Finset.sum_congr rfl
          intro c hc
          rw [naturalScaleGammaOrbitChargeC_eq_cast]
    have hcharge : charge = 0 :=
      (commonComplexGammaCharge_zero_iff (by norm_num : (1 : ℂ) ≠ 0)
        hnode hnode0 charge).mp hmom
    intro c
    have hc := congrFun hcharge (e c)
    simpa [charge] using hc
  · intro hcharge t ht0
    by_cases ht : ∃ ell : ℤ, t = (ell : ℝ)
    · obtain ⟨ell, rfl⟩ := ht
      have hell : ell ≠ 0 := by
        intro hell
        subst ell
        simp at ht0
      rw [scaledGammaAlienChargeAt_naturalScale_integer_eq_refinedCharacter
        n a m hn ell hell,
        ← naturalScaleGammaOrbitLaurentMoment_eq_refinedCharacter n a m ell]
      apply Finset.sum_eq_zero
      intro c hc
      rw [naturalScaleGammaOrbitChargeC_eq_cast, hcharge c]
      simp
    · exact scaledGammaAlienChargeAt_naturalScale_eq_zero_of_not_integer n a m hn ht

/-- Automatic analytic classification of the genuine Gauss-refined shifted-Gamma product. -/
theorem differentialAlgebraicOver_gammaNatScaleFamilyRefinedMero_iff_orbitCharge
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (gammaNatScaleFamilyRefinedMero n a m) ↔
      ∀ c : NaturalScaleGammaOrbit n a,
        naturalScaleGammaOrbitCharge n a m c = 0 := by
  rw [gammaNatScaleFamilyRefinedMero_eq_slotProduct]
  exact differentialAlgebraicOver_gammaFintypeOrbitProductMero_iff_orbitCharge
    (naturalScaleGammaSlotShift n a) (fun x => m x.1)

/-- A genuine finite positive-integer-scale Gamma product is differentially algebraic exactly
when every automatically constructed Gauss/refurrence orbit charge vanishes. -/
theorem differentialAlgebraicOver_gammaNatScaleFamilyMero_iff_orbitCharge
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hn : ∀ i, 0 < n i) :
    DifferentialAlgebraicOver (RatFunc ℂ) (gammaNatScaleFamilyMero n a m) ↔
      ∀ c : NaturalScaleGammaOrbit n a,
        naturalScaleGammaOrbitCharge n a m c = 0 := by
  rw [differentialAlgebraicOver_gammaNatScaleFamilyMero_iff_refined n a m hn,
    differentialAlgebraicOver_gammaNatScaleFamilyRefinedMero_iff_orbitCharge]

/-- The actual Borel-residue character and genuine meromorphic differential-algebraicity have
the same kernel for every finite positive-integer-scale Gamma family. -/
theorem scaledGammaAlienChargeZero_naturalScale_iff_differentialAlgebraic
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hn : ∀ i, 0 < n i) :
    ScaledGammaAlienChargeZero (naturalScaleGammaFactor n a m hn) ↔
      DifferentialAlgebraicOver (RatFunc ℂ) (gammaNatScaleFamilyMero n a m) := by
  rw [scaledGammaAlienChargeZero_naturalScale_iff_orbitCharge_zero,
    differentialAlgebraicOver_gammaNatScaleFamilyMero_iff_orbitCharge n a m hn]

/-- A commensurable positive-scale block written as positive common unit `delta` times natural
scales. -/
def commonUnitScaleGammaFactor {d : ℕ} (delta : ℝ) (n : Fin d → ℕ)
    (a : Fin d → ℂ) (m : Fin d → ℤ) (hdelta : 0 < delta)
    (hn : ∀ i, 0 < n i) (i : Fin d) : PositiveAffineGammaFactor where
  scale := delta * n i
  offset := a i
  multiplicity := m i
  scale_pos := mul_pos hdelta (by exact_mod_cast hn i)

/-- Genuine meromorphic product of a common positive unit scale times natural scales. -/
def commonUnitScaleGammaFamilyMero {d : ℕ} (delta : ℝ) (n : Fin d → ℕ)
    (a : Fin d → ℂ) (m : Fin d → ℤ) (hdelta : 0 < delta)
    (hn : ∀ i, 0 < n i) : meroField Set.univ :=
  ∏ i, gammaScaleShiftMero
    ((delta : ℂ) * (n i : ℂ))
    (mul_ne_zero (by exact_mod_cast hdelta.ne')
      (Nat.cast_ne_zero.mpr (hn i).ne')) (a i) ^ m i

/-- Common-unit scaling is literal coordinate dilation of the natural-scale Gamma family. -/
theorem commonUnitScaleGammaFamilyMero_eq_complexScale
    {d : ℕ} (delta : ℝ) (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hdelta : 0 < delta) (hn : ∀ i, 0 < n i) :
    commonUnitScaleGammaFamilyMero delta n a m hdelta hn =
      complexScaleMeroEquiv (delta : ℂ) (by exact_mod_cast hdelta.ne')
        (gammaNatScaleFamilyMero n a m) := by
  classical
  rw [commonUnitScaleGammaFamilyMero, gammaNatScaleFamilyMero, map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [map_zpow₀, gammaNatScaleMero_eq_gammaScaleShiftMero (hn i),
    complexScaleMeroEquiv_gammaScaleShiftMero]
  congr 2
  ring

/-- Genuine common-unit-scale Gamma products are DA exactly in the canonical zero-charge sector. -/
theorem differentialAlgebraicOver_commonUnitScaleGammaFamilyMero_iff_orbitCharge
    {d : ℕ} (delta : ℝ) (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hdelta : 0 < delta) (hn : ∀ i, 0 < n i) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (commonUnitScaleGammaFamilyMero delta n a m hdelta hn) ↔
      ∀ c : NaturalScaleGammaOrbit n a,
        naturalScaleGammaOrbitCharge n a m c = 0 := by
  rw [commonUnitScaleGammaFamilyMero_eq_complexScale,
    differentialAlgebraicOver_complexScaleMeroEquiv_iff,
    differentialAlgebraicOver_gammaNatScaleFamilyMero_iff_orbitCharge n a m hn]

/-- Common positive rescaling transports the full scaled residue character by the same scalar. -/
theorem scaledGammaAlienChargeAt_commonUnitScale
    {d : ℕ} (delta : ℝ) (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hdelta : 0 < delta) (hn : ∀ i, 0 < n i) (t : ℝ) :
    scaledGammaAlienChargeAt (commonUnitScaleGammaFactor delta n a m hdelta hn) (delta * t) =
      (delta : ℂ) * scaledGammaAlienChargeAt (naturalScaleGammaFactor n a m hn) t := by
  classical
  rw [scaledGammaAlienChargeAt, scaledGammaAlienChargeAt, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hdelta0 : delta ≠ 0 := hdelta.ne'
  have hsupport :
      (∃ k : ℤ, k ≠ 0 ∧
        delta * t = (k : ℝ) * (commonUnitScaleGammaFactor delta n a m hdelta hn i).scale) ↔
      (∃ k : ℤ, k ≠ 0 ∧
        t = (k : ℝ) * (naturalScaleGammaFactor n a m hn i).scale) := by
    simp only [commonUnitScaleGammaFactor, naturalScaleGammaFactor]
    constructor
    · rintro ⟨k, hk, heq⟩
      refine ⟨k, hk, ?_⟩
      apply (mul_left_cancel₀ hdelta0)
      linear_combination heq
    · rintro ⟨k, hk, heq⟩
      refine ⟨k, hk, ?_⟩
      linear_combination delta * heq
  by_cases hs : ∃ k : ℤ, k ≠ 0 ∧
      t = (k : ℝ) * (naturalScaleGammaFactor n a m hn i).scale
  · have hs' := hsupport.mpr hs
    rw [if_pos hs, if_pos hs']
    simp only [commonUnitScaleGammaFactor, naturalScaleGammaFactor]
    have hratio : delta * t / (delta * (n i : ℝ)) = t / (n i : ℝ) := by
      field_simp
    rw [hratio]
    push_cast
    ring
  · have hs' : ¬ ∃ k : ℤ, k ≠ 0 ∧
        delta * t = (k : ℝ) *
          (commonUnitScaleGammaFactor delta n a m hdelta hn i).scale :=
      hsupport.not.mpr hs
    rw [if_neg hs, if_neg hs', mul_zero]

theorem scaledGammaAlienChargeZero_commonUnitScale_iff_naturalScale
    {d : ℕ} (delta : ℝ) (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hdelta : 0 < delta) (hn : ∀ i, 0 < n i) :
    ScaledGammaAlienChargeZero (commonUnitScaleGammaFactor delta n a m hdelta hn) ↔
      ScaledGammaAlienChargeZero (naturalScaleGammaFactor n a m hn) := by
  constructor
  · intro hzero t ht
    have hdt : delta * t ≠ 0 := mul_ne_zero hdelta.ne' ht
    have hz := hzero (delta * t) hdt
    rw [scaledGammaAlienChargeAt_commonUnitScale delta n a m hdelta hn t] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast hdelta.ne')
  · intro hzero u hu
    have ht : u / delta ≠ 0 := div_ne_zero hu hdelta.ne'
    have hz := hzero (u / delta) ht
    have hu' : delta * (u / delta) = u := by field_simp
    rw [← hu', scaledGammaAlienChargeAt_commonUnitScale delta n a m hdelta hn,
      hz, mul_zero]

/-- **Commensurable-block scaled character completeness without a reduced presentation.** -/
theorem scaledGammaAlienChargeZero_commonUnitScale_iff_orbitCharge_zero
    {d : ℕ} (delta : ℝ) (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hdelta : 0 < delta) (hn : ∀ i, 0 < n i) :
    ScaledGammaAlienChargeZero (commonUnitScaleGammaFactor delta n a m hdelta hn) ↔
      ∀ c : NaturalScaleGammaOrbit n a, naturalScaleGammaOrbitCharge n a m c = 0 := by
  rw [scaledGammaAlienChargeZero_commonUnitScale_iff_naturalScale,
    scaledGammaAlienChargeZero_naturalScale_iff_orbitCharge_zero]

/-- The actual scaled Borel-residue character and genuine meromorphic
differential-algebraicity have the same kernel for every commensurable positive-scale block. -/
theorem scaledGammaAlienChargeZero_commonUnitScale_iff_differentialAlgebraic
    {d : ℕ} (delta : ℝ) (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hdelta : 0 < delta) (hn : ∀ i, 0 < n i) :
    ScaledGammaAlienChargeZero
        (commonUnitScaleGammaFactor delta n a m hdelta hn) ↔
      DifferentialAlgebraicOver (RatFunc ℂ)
        (commonUnitScaleGammaFamilyMero delta n a m hdelta hn) := by
  rw [scaledGammaAlienChargeZero_commonUnitScale_iff_orbitCharge_zero,
    differentialAlgebraicOver_commonUnitScaleGammaFamilyMero_iff_orbitCharge]

/-! ## Canonical rational-commensurability decomposition -/

/-- Positive rational commensurability of real Gamma scales. -/
def PositiveGammaScaleCommensurate (x y : ℝ) : Prop :=
  ∃ q : ℚ, 0 < q ∧ x = (q : ℝ) * y

theorem positiveGammaScaleCommensurate_refl (x : ℝ) :
    PositiveGammaScaleCommensurate x x := by
  exact ⟨1, by norm_num, by norm_num⟩

theorem positiveGammaScaleCommensurate_symm {x y : ℝ} :
    PositiveGammaScaleCommensurate x y → PositiveGammaScaleCommensurate y x := by
  rintro ⟨q, hq, hxy⟩
  refine ⟨q⁻¹, inv_pos.mpr hq, ?_⟩
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  push_cast
  rw [hxy]
  field_simp

theorem positiveGammaScaleCommensurate_trans {x y z : ℝ} :
    PositiveGammaScaleCommensurate x y → PositiveGammaScaleCommensurate y z →
      PositiveGammaScaleCommensurate x z := by
  rintro ⟨q, hq, hxy⟩ ⟨r, hr, hyz⟩
  refine ⟨q * r, mul_pos hq hr, ?_⟩
  push_cast
  rw [hxy, hyz]
  ring

/-- Scale-commensurability setoid of an arbitrary positive affine Gamma family. -/
def positiveGammaScaleSetoid {d : ℕ} (f : Fin d → PositiveAffineGammaFactor) :
    Setoid (Fin d) where
  r i j := PositiveGammaScaleCommensurate (f i).scale (f j).scale
  iseqv := {
    refl := fun i => positiveGammaScaleCommensurate_refl _
    symm := by
      intro i j h
      exact positiveGammaScaleCommensurate_symm h
    trans := by
      intro i j k h₁ h₂
      exact positiveGammaScaleCommensurate_trans h₁ h₂ }

/-- Canonical finite rational-commensurability classes of a Gamma factor family. -/
abbrev PositiveGammaScaleClass {d : ℕ} (f : Fin d → PositiveAffineGammaFactor) :=
  Quotient (positiveGammaScaleSetoid f)

noncomputable instance positiveGammaScaleClassDecidableEq {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) : DecidableEq (PositiveGammaScaleClass f) :=
  Classical.decEq _

noncomputable instance positiveGammaScaleClassFintype {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) : Fintype (PositiveGammaScaleClass f) :=
  Fintype.ofSurjective (fun i : Fin d => Quotient.mk'' i)
    (fun c => ⟨c.out, Quotient.out_eq c⟩)

/-- Indices in one canonical rational-commensurability class. -/
abbrev PositiveGammaScaleClassFiber {d : ℕ} (f : Fin d → PositiveAffineGammaFactor)
    (c : PositiveGammaScaleClass f) := {i : Fin d // Quotient.mk'' i = c}

noncomputable instance positiveGammaScaleClassFiberNonempty {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (c : PositiveGammaScaleClass f) :
    Nonempty (PositiveGammaScaleClassFiber f c) :=
  ⟨⟨c.out, Quotient.out_eq c⟩⟩

/-- Canonical positive rational ratio to the quotient representative. -/
noncomputable def positiveGammaScaleClassRatio {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (c : PositiveGammaScaleClass f)
    (i : PositiveGammaScaleClassFiber f c) : ℚ := by
  have heq : (Quotient.mk'' (i : Fin d) : PositiveGammaScaleClass f) =
      Quotient.mk'' c.out := i.property.trans (Quotient.out_eq c).symm
  have hrel := Quotient.exact heq
  exact Classical.choose hrel

theorem positiveGammaScaleClassRatio_spec {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (c : PositiveGammaScaleClass f)
    (i : PositiveGammaScaleClassFiber f c) :
    0 < positiveGammaScaleClassRatio f c i ∧
      (f i).scale = (positiveGammaScaleClassRatio f c i : ℝ) * (f c.out).scale := by
  have heq : (Quotient.mk'' (i : Fin d) : PositiveGammaScaleClass f) =
      Quotient.mk'' c.out := i.property.trans (Quotient.out_eq c).symm
  have hrel := Quotient.exact heq
  exact Classical.choose_spec hrel

/-- Positive common denominator of all rational scale ratios in one class. -/
noncomputable def positiveGammaScaleClassDenominator {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (c : PositiveGammaScaleClass f) : ℕ :=
  ∏ i : PositiveGammaScaleClassFiber f c, (positiveGammaScaleClassRatio f c i).den

theorem positiveGammaScaleClassDenominator_pos {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (c : PositiveGammaScaleClass f) :
    0 < positiveGammaScaleClassDenominator f c := by
  rw [positiveGammaScaleClassDenominator]
  exact Finset.prod_pos fun i _ => (positiveGammaScaleClassRatio f c i).pos

theorem positiveGammaScaleClassRatio_den_dvd {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (c : PositiveGammaScaleClass f)
    (i : PositiveGammaScaleClassFiber f c) :
    (positiveGammaScaleClassRatio f c i).den ∣
      positiveGammaScaleClassDenominator f c := by
  rw [positiveGammaScaleClassDenominator]
  exact Finset.dvd_prod_of_mem
    (fun j : PositiveGammaScaleClassFiber f c => (positiveGammaScaleClassRatio f c j).den)
    (Finset.mem_univ i)

/-- Positive integer obtained by clearing the denominator of one class ratio. -/
noncomputable def positiveGammaScaleClassInteger {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (c : PositiveGammaScaleClass f)
    (i : PositiveGammaScaleClassFiber f c) : ℤ :=
  (positiveGammaScaleClassRatio f c i).num *
    (positiveGammaScaleClassDenominator f c /
      (positiveGammaScaleClassRatio f c i).den : ℕ)

theorem positiveGammaScaleClassDenominator_mul_ratio {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (c : PositiveGammaScaleClass f)
    (i : PositiveGammaScaleClassFiber f c) :
    ((positiveGammaScaleClassDenominator f c : ℕ) : ℚ) *
        positiveGammaScaleClassRatio f c i =
      (positiveGammaScaleClassInteger f c i : ℚ) := by
  let q := positiveGammaScaleClassRatio f c i
  let D := positiveGammaScaleClassDenominator f c
  obtain ⟨u, hu⟩ : q.den ∣ D := positiveGammaScaleClassRatio_den_dvd f c i
  rw [positiveGammaScaleClassInteger]
  have hdiv : positiveGammaScaleClassDenominator f c /
      (positiveGammaScaleClassRatio f c i).den = u := by
    rw [show positiveGammaScaleClassDenominator f c =
      (positiveGammaScaleClassRatio f c i).den * u from hu]
    exact Nat.mul_div_cancel_left _ (positiveGammaScaleClassRatio f c i).pos
  rw [hdiv, show positiveGammaScaleClassDenominator f c =
    (positiveGammaScaleClassRatio f c i).den * u from hu]
  push_cast
  linear_combination (u : ℚ) * Rat.mul_den_eq_num q

theorem positiveGammaScaleClassInteger_pos {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (c : PositiveGammaScaleClass f)
    (i : PositiveGammaScaleClassFiber f c) :
    0 < positiveGammaScaleClassInteger f c i := by
  have hD : (0 : ℚ) < positiveGammaScaleClassDenominator f c := by
    exact_mod_cast positiveGammaScaleClassDenominator_pos f c
  have hq := (positiveGammaScaleClassRatio_spec f c i).1
  have hprod : (0 : ℚ) <
      (positiveGammaScaleClassDenominator f c : ℚ) *
        positiveGammaScaleClassRatio f c i := mul_pos hD hq
  rw [positiveGammaScaleClassDenominator_mul_ratio f c i] at hprod
  exact_mod_cast hprod

/-- Natural scale of one original factor inside its canonical commensurability class. -/
noncomputable def canonicalPositiveGammaNaturalScale {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (i : Fin d) : ℕ :=
  Int.toNat (positiveGammaScaleClassInteger f (Quotient.mk'' i) ⟨i, rfl⟩)

theorem canonicalPositiveGammaNaturalScale_pos {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (i : Fin d) :
    0 < canonicalPositiveGammaNaturalScale f i := by
  rw [canonicalPositiveGammaNaturalScale]
  have hz := positiveGammaScaleClassInteger_pos f (Quotient.mk'' i) ⟨i, rfl⟩
  apply Nat.pos_of_ne_zero
  intro hzero
  have hle := Int.toNat_eq_zero.mp hzero
  omega

/-- Canonical positive common scale of one rational-commensurability class. -/
noncomputable def canonicalPositiveGammaCommonUnit {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (c : PositiveGammaScaleClass f) : ℝ :=
  (f c.out).scale / positiveGammaScaleClassDenominator f c

theorem canonicalPositiveGammaCommonUnit_pos {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (c : PositiveGammaScaleClass f) :
    0 < canonicalPositiveGammaCommonUnit f c := by
  exact div_pos (f c.out).scale_pos (by exact_mod_cast positiveGammaScaleClassDenominator_pos f c)

/-- Every arbitrary positive scale is exactly its class unit times a positive natural scale. -/
theorem positiveGammaScale_eq_canonicalCommonUnit_mul_naturalScale {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (i : Fin d) :
    (f i).scale = canonicalPositiveGammaCommonUnit f (Quotient.mk'' i) *
      canonicalPositiveGammaNaturalScale f i := by
  let c : PositiveGammaScaleClass f := Quotient.mk'' i
  let ii : PositiveGammaScaleClassFiber f c := ⟨i, rfl⟩
  let q := positiveGammaScaleClassRatio f c ii
  let D := positiveGammaScaleClassDenominator f c
  let z := positiveGammaScaleClassInteger f c ii
  have hz : 0 ≤ z := (positiveGammaScaleClassInteger_pos f c ii).le
  have hnZ : ((Int.toNat z : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz
  have hclearQ := positiveGammaScaleClassDenominator_mul_ratio f c ii
  have hclearR : (D : ℝ) * (q : ℝ) = (Int.toNat z : ℝ) := by
    have hclearZ : (D : ℚ) * q = (Int.toNat z : ℚ) := by
      rw [hclearQ]
      exact_mod_cast hnZ.symm
    exact_mod_cast hclearZ
  have hratio := (positiveGammaScaleClassRatio_spec f c ii).2
  have hD0 : (D : ℝ) ≠ 0 := by
    exact_mod_cast (positiveGammaScaleClassDenominator_pos f c).ne'
  change (f i).scale = (f c.out).scale / D * Int.toNat z
  rw [hratio]
  calc
    (q : ℝ) * (f c.out).scale =
        ((D : ℝ) * (q : ℝ)) / D * (f c.out).scale := by
          field_simp
    _ = (Int.toNat z : ℝ) / D * (f c.out).scale := by rw [hclearR]
    _ = (f c.out).scale / D * Int.toNat z := by ring

/-- Canonical enumeration of the factors in one commensurability class. -/
noncomputable def positiveGammaScaleClassFiberEquivFin {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (c : PositiveGammaScaleClass f) :
    PositiveGammaScaleClassFiber f c ≃ Fin (Fintype.card (PositiveGammaScaleClassFiber f c)) :=
  Fintype.equivFin _

/-- Original factor family restricted to one canonical class. -/
noncomputable def positiveGammaScaleClassFactor {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (c : PositiveGammaScaleClass f) :
    Fin (Fintype.card (PositiveGammaScaleClassFiber f c)) → PositiveAffineGammaFactor :=
  fun j => f ((positiveGammaScaleClassFiberEquivFin f c).symm j)

/-- Natural scale vector of one canonical class. -/
noncomputable def positiveGammaScaleClassNaturalScale {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (c : PositiveGammaScaleClass f) :
    Fin (Fintype.card (PositiveGammaScaleClassFiber f c)) → ℕ :=
  fun j => canonicalPositiveGammaNaturalScale f
    ((positiveGammaScaleClassFiberEquivFin f c).symm j)

noncomputable def positiveGammaScaleClassOffset {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (c : PositiveGammaScaleClass f) :
    Fin (Fintype.card (PositiveGammaScaleClassFiber f c)) → ℂ :=
  fun j => (f ((positiveGammaScaleClassFiberEquivFin f c).symm j)).offset

noncomputable def positiveGammaScaleClassMultiplicity {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (c : PositiveGammaScaleClass f) :
    Fin (Fintype.card (PositiveGammaScaleClassFiber f c)) → ℤ :=
  fun j => (f ((positiveGammaScaleClassFiberEquivFin f c).symm j)).multiplicity

theorem positiveGammaScaleClassNaturalScale_pos {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (c : PositiveGammaScaleClass f) :
    ∀ j, 0 < positiveGammaScaleClassNaturalScale f c j :=
  fun j => canonicalPositiveGammaNaturalScale_pos f
    ((positiveGammaScaleClassFiberEquivFin f c).symm j)

theorem positiveAffineGammaFactor_ext
    {x y : PositiveAffineGammaFactor}
    (hscale : x.scale = y.scale) (hoffset : x.offset = y.offset)
    (hmultiplicity : x.multiplicity = y.multiplicity) : x = y := by
  cases x
  cases y
  simp_all

theorem positiveGammaScaleClassFactor_eq_commonUnitScale {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (c : PositiveGammaScaleClass f) :
    positiveGammaScaleClassFactor f c =
      commonUnitScaleGammaFactor
        (canonicalPositiveGammaCommonUnit f c)
        (positiveGammaScaleClassNaturalScale f c)
        (positiveGammaScaleClassOffset f c)
        (positiveGammaScaleClassMultiplicity f c)
        (canonicalPositiveGammaCommonUnit_pos f c)
        (positiveGammaScaleClassNaturalScale_pos f c) := by
  funext j
  apply positiveAffineGammaFactor_ext
  · change (f ((positiveGammaScaleClassFiberEquivFin f c).symm j)).scale =
        canonicalPositiveGammaCommonUnit f c *
          canonicalPositiveGammaNaturalScale f
            ((positiveGammaScaleClassFiberEquivFin f c).symm j)
    have h := positiveGammaScale_eq_canonicalCommonUnit_mul_naturalScale f
      ((positiveGammaScaleClassFiberEquivFin f c).symm j)
    rw [((positiveGammaScaleClassFiberEquivFin f c).symm j).property] at h
    exact h
  · rfl
  · rfl

/-- Intrinsic contribution of one positive affine Gamma factor at a real Borel frequency. -/
noncomputable def positiveGammaFactorChargeAt
    (f : PositiveAffineGammaFactor) (t : ℝ) : ℂ := by
  classical
  exact if ∃ k : ℤ, k ≠ 0 ∧ t = (k : ℝ) * f.scale then
    (f.multiplicity : ℂ) * (f.scale : ℂ) *
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
        (((t / f.scale : ℝ)) : ℂ) * f.offset)
  else 0

theorem scaledGammaAlienChargeAt_eq_sum_factorCharge {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (t : ℝ) :
    scaledGammaAlienChargeAt f t = ∑ i, positiveGammaFactorChargeAt (f i) t := by
  rfl

/-- Nonzero integer lattice of a positive real Gamma scale. -/
def positiveGammaIntegerLattice (scale t : ℝ) : Prop :=
  ∃ k : ℤ, k ≠ 0 ∧ t = (k : ℝ) * scale

/-- The full arbitrary-scale character is the exact finite sum of its canonical
commensurability-class characters. -/
theorem sum_scaledGammaAlienChargeAt_classFactor_eq {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) (t : ℝ) :
    ∑ c : PositiveGammaScaleClass f,
        scaledGammaAlienChargeAt (positiveGammaScaleClassFactor f c) t =
      scaledGammaAlienChargeAt f t := by
  classical
  simp_rw [scaledGammaAlienChargeAt_eq_sum_factorCharge]
  calc
    ∑ c : PositiveGammaScaleClass f,
        ∑ j, positiveGammaFactorChargeAt (positiveGammaScaleClassFactor f c j) t =
      ∑ c : PositiveGammaScaleClass f,
        ∑ i : PositiveGammaScaleClassFiber f c,
          positiveGammaFactorChargeAt (f i) t := by
            apply Finset.sum_congr rfl
            intro c hc
            simpa [positiveGammaScaleClassFactor] using
              (Equiv.sum_comp (positiveGammaScaleClassFiberEquivFin f c).symm
                (fun i : PositiveGammaScaleClassFiber f c =>
                  positiveGammaFactorChargeAt (f i) t))
    _ = ∑ c : PositiveGammaScaleClass f,
          ∑ i : Fin d, if Quotient.mk'' i = c then
            positiveGammaFactorChargeAt (f i) t else 0 := by
            apply Finset.sum_congr rfl
            intro c hc
            rw [← Finset.sum_filter]
            symm
            exact Finset.sum_subtype
              (Finset.univ.filter fun i : Fin d => Quotient.mk'' i = c)
              (fun i => by simp) (fun i => positiveGammaFactorChargeAt (f i) t)
    _ = ∑ i : Fin d, positiveGammaFactorChargeAt (f i) t := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_eq_single (Quotient.mk'' i)]
            · simp
            · intro c hc hci
              simp [hci.symm]
            · intro hnot
              exact (hnot (Finset.mem_univ _)).elim

theorem positiveGammaFactorChargeAt_eq_zero_of_not_lattice
    (f : PositiveAffineGammaFactor) {t : ℝ}
    (ht : ¬ positiveGammaIntegerLattice f.scale t) :
    positiveGammaFactorChargeAt f t = 0 := by
  rw [positiveGammaFactorChargeAt]
  rw [if_neg]
  simpa [positiveGammaIntegerLattice] using ht

/-- A common nonzero lattice frequency forces positive rational commensurability of the scales. -/
theorem positiveGammaScaleCommensurate_of_common_lattice
    {x y t : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxt : positiveGammaIntegerLattice x t)
    (hyt : positiveGammaIntegerLattice y t) :
    PositiveGammaScaleCommensurate x y := by
  obtain ⟨k, hk, htk⟩ := hxt
  obtain ⟨l, hl, htl⟩ := hyt
  let q : ℚ := (l : ℚ) / (k : ℚ)
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hy0 : y ≠ 0 := hy.ne'
  have hcross : (k : ℝ) * x = (l : ℝ) * y := htk.symm.trans htl
  have hqcast : (q : ℝ) = x / y := by
    dsimp [q]
    push_cast
    field_simp
    nlinarith
  have hqposR : (0 : ℝ) < (q : ℝ) := by
    rw [hqcast]
    exact div_pos hx hy
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hqposR
  refine ⟨q, hqpos, ?_⟩
  rw [hqcast]
  field_simp

theorem scaledGammaAlienChargeAt_classFactor_eq_zero_of_no_lattice
    {d : ℕ} (f : Fin d → PositiveAffineGammaFactor)
    (c : PositiveGammaScaleClass f) {t : ℝ}
    (ht : ∀ j, ¬ positiveGammaIntegerLattice
      (positiveGammaScaleClassFactor f c j).scale t) :
    scaledGammaAlienChargeAt (positiveGammaScaleClassFactor f c) t = 0 := by
  rw [scaledGammaAlienChargeAt_eq_sum_factorCharge]
  apply Finset.sum_eq_zero
  intro j hj
  exact positiveGammaFactorChargeAt_eq_zero_of_not_lattice _ (ht j)

/-- Different canonical scale classes cannot contribute at the same nonzero Borel frequency. -/
theorem scaledGammaAlienChargeAt_classFactor_eq_zero_of_other_class_lattice
    {d : ℕ} (f : Fin d → PositiveAffineGammaFactor)
    {c e : PositiveGammaScaleClass f} (hce : e ≠ c)
    {t : ℝ}
    (hc : ∃ j, positiveGammaIntegerLattice
      (positiveGammaScaleClassFactor f c j).scale t) :
    scaledGammaAlienChargeAt (positiveGammaScaleClassFactor f e) t = 0 := by
  obtain ⟨j, hj⟩ := hc
  apply scaledGammaAlienChargeAt_classFactor_eq_zero_of_no_lattice
  intro k hk
  apply hce
  let ij : PositiveGammaScaleClassFiber f c :=
    (positiveGammaScaleClassFiberEquivFin f c).symm j
  let ik : PositiveGammaScaleClassFiber f e :=
    (positiveGammaScaleClassFiberEquivFin f e).symm k
  have hcomm : PositiveGammaScaleCommensurate (f ij).scale (f ik).scale :=
    positiveGammaScaleCommensurate_of_common_lattice
      (f ij).scale_pos (f ik).scale_pos (by
        simpa [positiveGammaScaleClassFactor, ij] using hj) (by
        simpa [positiveGammaScaleClassFactor, ik] using hk)
  have hquot : (Quotient.mk'' (ij : Fin d) : PositiveGammaScaleClass f) =
      Quotient.mk'' (ik : Fin d) := Quotient.sound hcomm
  exact ik.property.symm.trans (hquot.symm.trans ij.property)

/-- Vanishing of the arbitrary-scale character is exactly blockwise vanishing on every canonical
rational-commensurability class. -/
theorem scaledGammaAlienChargeZero_iff_classFactor_zero
    {d : ℕ} (f : Fin d → PositiveAffineGammaFactor) :
    ScaledGammaAlienChargeZero f ↔
      ∀ c : PositiveGammaScaleClass f,
        ScaledGammaAlienChargeZero (positiveGammaScaleClassFactor f c) := by
  constructor
  · intro hzero c t ht0
    by_cases hc : ∃ j,
        positiveGammaIntegerLattice (positiveGammaScaleClassFactor f c j).scale t
    · have hsum : (∑ e : PositiveGammaScaleClass f,
          scaledGammaAlienChargeAt (positiveGammaScaleClassFactor f e) t) = 0 := by
        rw [sum_scaledGammaAlienChargeAt_classFactor_eq]
        exact hzero t ht0
      rw [Finset.sum_eq_single c] at hsum
      · exact hsum
      · intro e he hec
        exact scaledGammaAlienChargeAt_classFactor_eq_zero_of_other_class_lattice
          f hec hc
      · intro hcnot
        exact (hcnot (Finset.mem_univ _)).elim
    · exact scaledGammaAlienChargeAt_classFactor_eq_zero_of_no_lattice f c
        (fun j => by simpa using fun hj => hc ⟨j, hj⟩)
  · intro hblocks t ht0
    rw [← sum_scaledGammaAlienChargeAt_classFactor_eq]
    exact Finset.sum_eq_zero fun c _ => hblocks c t ht0

/-- One canonical commensurability block is detected exactly by its automatically constructed
Gauss-refined shift-orbit charges. -/
theorem scaledGammaAlienChargeZero_classFactor_iff_orbitCharge_zero
    {d : ℕ} (f : Fin d → PositiveAffineGammaFactor)
    (c : PositiveGammaScaleClass f) :
    ScaledGammaAlienChargeZero (positiveGammaScaleClassFactor f c) ↔
      ∀ q : NaturalScaleGammaOrbit
          (positiveGammaScaleClassNaturalScale f c)
          (positiveGammaScaleClassOffset f c),
        naturalScaleGammaOrbitCharge
          (positiveGammaScaleClassNaturalScale f c)
          (positiveGammaScaleClassOffset f c)
          (positiveGammaScaleClassMultiplicity f c) q = 0 := by
  rw [positiveGammaScaleClassFactor_eq_commonUnitScale,
    scaledGammaAlienChargeZero_commonUnitScale_iff_orbitCharge_zero]

/-- **Arbitrary positive-scale character completeness.**  The actual scaled alien character of
every finite positive affine Gamma family vanishes exactly when every canonical Gauss/refurrence
orbit charge in every rational-commensurability class vanishes.  All classes, common units,
natural refinements, and orbit quotients are constructed from the input family. -/
theorem scaledGammaAlienChargeZero_iff_canonicalOrbitCharges
    {d : ℕ} (f : Fin d → PositiveAffineGammaFactor) :
    ScaledGammaAlienChargeZero f ↔
      ∀ c : PositiveGammaScaleClass f,
        ∀ q : NaturalScaleGammaOrbit
          (positiveGammaScaleClassNaturalScale f c)
          (positiveGammaScaleClassOffset f c),
        naturalScaleGammaOrbitCharge
          (positiveGammaScaleClassNaturalScale f c)
          (positiveGammaScaleClassOffset f c)
          (positiveGammaScaleClassMultiplicity f c) q = 0 := by
  rw [scaledGammaAlienChargeZero_iff_classFactor_zero]
  apply forall_congr'
  intro c
  exact scaledGammaAlienChargeZero_classFactor_iff_orbitCharge_zero f c

/-- Positive form: any surviving canonical orbit charge is detected at a nonzero Borel
frequency by the original arbitrary-scale factor family. -/
theorem exists_scaledGammaAlienChargeAt_ne_zero_of_canonicalOrbitCharge_ne_zero
    {d : ℕ} (f : Fin d → PositiveAffineGammaFactor)
    {c : PositiveGammaScaleClass f}
    {q : NaturalScaleGammaOrbit
      (positiveGammaScaleClassNaturalScale f c)
      (positiveGammaScaleClassOffset f c)}
    (hq : naturalScaleGammaOrbitCharge
      (positiveGammaScaleClassNaturalScale f c)
      (positiveGammaScaleClassOffset f c)
      (positiveGammaScaleClassMultiplicity f c) q ≠ 0) :
    ∃ t : ℝ, t ≠ 0 ∧ scaledGammaAlienChargeAt f t ≠ 0 := by
  by_contra h
  push Not at h
  have hzero : ScaledGammaAlienChargeZero f := h
  have hall := (scaledGammaAlienChargeZero_iff_canonicalOrbitCharges f).mp hzero c q
  exact hq hall

/-- Closed Borel-residue/character capstone for arbitrary finite positive-scale Gamma packets. -/
theorem scaledGammaBorelResidueCharacter_capstone :
    ∀ {d : ℕ} (f : Fin d → PositiveAffineGammaFactor),
      (∀ t : ℝ, t ≠ 0 →
        Tendsto
          (fun ξ : ℂ =>
            (ξ - 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) *
              scaledGammaBorelPolarPart f ξ)
          (nhdsWithin (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
            ({2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)}ᶜ))
          (nhds ((2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) *
            scaledGammaAlienChargeAt f t))) ∧
      (ScaledGammaAlienChargeZero f ↔
        ∀ c : PositiveGammaScaleClass f,
          ∀ q : NaturalScaleGammaOrbit
            (positiveGammaScaleClassNaturalScale f c)
            (positiveGammaScaleClassOffset f c),
          naturalScaleGammaOrbitCharge
            (positiveGammaScaleClassNaturalScale f c)
            (positiveGammaScaleClassOffset f c)
            (positiveGammaScaleClassMultiplicity f c) q = 0) := by
  intro d f
  exact ⟨fun t ht => scaledGammaBorelPolarPart_residue f t ht,
    scaledGammaAlienChargeZero_iff_canonicalOrbitCharges f⟩

end

end GaloisForLFunctions.HTGeometry
