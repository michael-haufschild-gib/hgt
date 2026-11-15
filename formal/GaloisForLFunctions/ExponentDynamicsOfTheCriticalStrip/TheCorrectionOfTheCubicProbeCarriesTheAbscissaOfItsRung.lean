import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.MixedTowersOfLeversStayAboveTheBestCentre
import GaloisForLFunctions.FamilyContinuationTheory.GrossencharacterLFunctionsHaveZerosInTheRightHalfStrip

/-!
# The correction of the cubic probe carries the abscissa of its rung

The cubic probe of `K = ℚ(ω)` has the frame `(c, k) = (3, 6)`: its correction, continued to
`Re s > ½`, vanishes exactly where the Grössencharacter `L`-function of the rung vanishes at the
dilated argument `6s − 3`. This module turns the zero-locus identity into an identity of
abscissas, with no hypothesis:

* `correctionAbscissa_eq`: the abscissa of the zeros of the correction in `Re s > ½` is
  `(3 + Θ_rung)/6`, where `Θ_rung` is the abscissa of the zeros of the rung in `Re w > 0`. It does
  not depend on the finite set of primes of the probe.
* `correctionAbscissa_le_iff`: the frame is exact in both directions,
  `Θ_corr ≤ (3 + b)/6 ⇔ Θ_rung ≤ b`.
* `seven_twelfths_le_correctionAbscissa`, `correctionAbscissa_le_two_thirds`: with
  `½ ≤ Θ_rung ≤ 1`, the two ends of the frame.
* `correctionAbscissa_le_thirtyOne_fortyEighths_iff`: a zero-free half-plane `Re w > 7/8` for the
  rung is the same statement as a zero-free half-plane `Re s > 31/48` for the correction.

The lever of the frame is therefore a ruler between two abscissas: it moves a bound for the
rung to the correction and back without loss, and it produces a bound for neither. A seed for the
family of the rungs is what the tower of the frame lacks.
-/

noncomputable section

open Complex Filter Topology Set NumberField IsDedekindDomain
open scoped BigOperators Classical ComplexConjugate

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

open HeckeLFunctions MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
open FamilyContinuationTheory

local instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ

local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

/-- The real parts of the zeros of the rung in `Re w > 0`. -/
def rungZeroDepths (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ) : Set ℝ :=
  {x : ℝ | ∃ w : ℂ, 0 < w.re ∧ grossenLFunction 𝔪 ψ k w = 0 ∧ w.re = x}

/-- The **abscissa of the rung**: the supremum of the real parts of the zeros of the
Grössencharacter `L`-function in `Re w > 0`. -/
def rungAbscissa (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ) : ℝ :=
  sSup (rungZeroDepths 𝔪 ψ k)

/-- The real parts of the zeros of the correction in `Re s > ½`. -/
def correctionZeroDepths (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O)) : Set ℝ :=
  {x : ℝ | ∃ s : ℂ, 1 / 2 < s.re ∧ continuedProbeCorrection 𝔪 η S s = 0 ∧ s.re = x}

/-- The **abscissa of the correction** of the cubic probe: the supremum of the real parts of its
zeros in `Re s > ½`. -/
def correctionAbscissa (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O)) : ℝ :=
  sSup (correctionZeroDepths 𝔪 η S)

/-! ### The rung -/

theorem rungZeroDepths_nonempty (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ} (hk : 1 ≤ k) :
    (rungZeroDepths 𝔪 ψ k).Nonempty := by
  obtain ⟨w, hw1, -, -, hw0⟩ := exists_zero_grossenLFunction_right_half_strip_im_gt 𝔪 ψ hk 0
  exact ⟨w.re, w, by linarith, hw0, rfl⟩

theorem lt_one_of_mem_rungZeroDepths (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ}
    (hk : 1 ≤ k) {x : ℝ} (hx : x ∈ rungZeroDepths 𝔪 ψ k) : x < 1 := by
  obtain ⟨w, -, hw0, rfl⟩ := hx
  by_contra hge
  exact grossenLFunction_ne_zero_of_one_le_re 𝔪 ψ hk (not_lt.mp hge) hw0

theorem bddAbove_rungZeroDepths (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ} (hk : 1 ≤ k) :
    BddAbove (rungZeroDepths 𝔪 ψ k) :=
  ⟨1, fun _ hx => (lt_one_of_mem_rungZeroDepths 𝔪 ψ hk hx).le⟩

/-- The abscissa of a rung lies in `[½, 1]`. -/
theorem half_le_rungAbscissa (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ} (hk : 1 ≤ k) :
    1 / 2 ≤ rungAbscissa 𝔪 ψ k := by
  obtain ⟨w, hw1, -, -, hw0⟩ := exists_zero_grossenLFunction_right_half_strip_im_gt 𝔪 ψ hk 0
  exact hw1.trans (le_csSup (bddAbove_rungZeroDepths 𝔪 ψ hk) ⟨w, by linarith, hw0, rfl⟩)

theorem rungAbscissa_le_one (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) {k : ℕ} (hk : 1 ≤ k) :
    rungAbscissa 𝔪 ψ k ≤ 1 :=
  csSup_le (rungZeroDepths_nonempty 𝔪 ψ hk) fun _ hx =>
    (lt_one_of_mem_rungZeroDepths 𝔪 ψ hk hx).le

/-! ### The frame -/

/-- The real part of the dilated argument. -/
theorem re_six_mul_sub_three (s : ℂ) : (6 * s - 3).re = 6 * s.re - 3 := by
  simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]

/-- **The zero depths of the correction are the images of the zero depths of the rung** under
the frame map `x ↦ (3 + x)/6`. -/
theorem correctionZeroDepths_eq_image (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O)) :
    correctionZeroDepths 𝔪 η S = (fun x : ℝ => (3 + x) / 6) '' rungZeroDepths 𝔪 (η ^ 6) 1 := by
  ext x
  constructor
  · rintro ⟨s, hs, hs0, rfl⟩
    refine ⟨(6 * s - 3).re, ⟨6 * s - 3, ?_, (continuedProbeCorrection_eq_zero_iff 𝔪 η S hs).mp hs0,
      rfl⟩, ?_⟩
    · rw [re_six_mul_sub_three]
      linarith
    · show (3 + (6 * s - 3).re) / 6 = s.re
      rw [re_six_mul_sub_three]
      ring
  · rintro ⟨y, ⟨w, hw, hw0, rfl⟩, rfl⟩
    obtain ⟨s, hs⟩ : ∃ s : ℂ, s = (w + 3) / 6 := ⟨_, rfl⟩
    have hs6 : 6 * s - 3 = w := by
      rw [hs]
      ring
    have hre : w.re = 6 * s.re - 3 := by rw [← hs6, re_six_mul_sub_three]
    have hshalf : 1 / 2 < s.re := by linarith
    refine ⟨s, hshalf, ?_, ?_⟩
    · rw [continuedProbeCorrection_eq_zero_iff 𝔪 η S hshalf, hs6]
      exact hw0
    · show s.re = (3 + w.re) / 6
      rw [hre]
      ring

/-- **The correction carries the abscissa of its rung**: `Θ_corr = (3 + Θ_rung)/6`, for every
finite set of primes of the probe. -/
theorem correctionAbscissa_eq (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O)) :
    correctionAbscissa 𝔪 η S = (3 + rungAbscissa 𝔪 (η ^ 6) 1) / 6 := by
  have hmono : Monotone fun x : ℝ => (3 + x) / 6 := fun a b hab => by
    show (3 + a) / 6 ≤ (3 + b) / 6
    linarith
  have hcont : ContinuousAt (fun x : ℝ => (3 + x) / 6) (sSup (rungZeroDepths 𝔪 (η ^ 6) 1)) :=
    ((continuous_const.add continuous_id).div_const 6).continuousAt
  unfold correctionAbscissa rungAbscissa
  rw [correctionZeroDepths_eq_image]
  exact (hmono.map_csSup_of_continuousAt hcont (rungZeroDepths_nonempty 𝔪 (η ^ 6) le_rfl)
    (bddAbove_rungZeroDepths 𝔪 (η ^ 6) le_rfl)).symm

/-- The abscissa of the correction in the notation of frames. -/
theorem correctionAbscissa_eq_pairingStep (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O)) :
    correctionAbscissa 𝔪 η S = pairingStep 3 6 (rungAbscissa 𝔪 (η ^ 6) 1) :=
  correctionAbscissa_eq 𝔪 η S

/-- **The frame is exact in both directions**: a bound `b` for the rung is the bound
`(3 + b)/6` for the correction, and conversely. -/
theorem correctionAbscissa_le_iff (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O)) (b : ℝ) :
    correctionAbscissa 𝔪 η S ≤ (3 + b) / 6 ↔ rungAbscissa 𝔪 (η ^ 6) 1 ≤ b := by
  rw [correctionAbscissa_eq]
  constructor <;> intro h <;> linarith

/-- The lower end of the frame: the correction has zeros up to `Re s = 7/12` at least. -/
theorem seven_twelfths_le_correctionAbscissa (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O)) : 7 / 12 ≤ correctionAbscissa 𝔪 η S := by
  rw [correctionAbscissa_eq]
  linarith [half_le_rungAbscissa 𝔪 (η ^ 6) (k := 1) le_rfl]

/-- The upper end of the frame. -/
theorem correctionAbscissa_le_two_thirds (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O)) : correctionAbscissa 𝔪 η S ≤ 2 / 3 := by
  rw [correctionAbscissa_eq]
  linarith [rungAbscissa_le_one 𝔪 (η ^ 6) (k := 1) le_rfl]

/-- **A seed for the rung is a half-plane of the correction**: the rung has no zero in
`Re w > 7/8` iff the correction has none in `Re s > 31/48`. -/
theorem correctionAbscissa_le_thirtyOne_fortyEighths_iff (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O)) :
    correctionAbscissa 𝔪 η S ≤ 31 / 48 ↔ rungAbscissa 𝔪 (η ^ 6) 1 ≤ 7 / 8 := by
  have h := correctionAbscissa_le_iff 𝔪 η S (7 / 8)
  have e : (3 + 7 / 8 : ℝ) / 6 = 31 / 48 := by norm_num
  rwa [e] at h

/-- The abscissa of the correction does not depend on the finite set of primes of the probe. -/
theorem correctionAbscissa_eq_of_finsets (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S S' : Finset (HeightOneSpectrum O)) :
    correctionAbscissa 𝔪 η S = correctionAbscissa 𝔪 η S' := by
  rw [correctionAbscissa_eq, correctionAbscissa_eq]

#print axioms correctionAbscissa_eq
#print axioms correctionAbscissa_le_iff

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
