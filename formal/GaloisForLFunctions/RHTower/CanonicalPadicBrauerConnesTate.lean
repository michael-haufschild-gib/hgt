import GaloisForLFunctions.HTGeometry.ABHN.CanonicalNonarchimedeanLocalBrauerInvariant
import GaloisForLFunctions.RHTower.PadicBrauerUnramifiedTate

/-!
# Canonical local Brauer phases in the Connes--Tate source

The arithmetic-Frobenius-normalized invariant `Br(ℚ_p) ≃ ℚ/ℤ` supplies a canonical unit-circle
phase. This file identifies it with the value at a uniformizer of an actual continuous unramified
character of `ℚ_p^*`, then identifies its twisted Euler factor with the convergent local Tate
integral. The untwisted `ζ_p` source is recovered exactly for the split Brauer class.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- Arithmetic-Frobenius-normalized local Brauer phase. -/
def canonicalPadicBrauerPhase (p : ℕ) [Fact p.Prime] :
    AddChar (BrauerGroup ℚ_[p]) ℂ :=
  brauerInvariantStdAddChar ℚ_[p]
    (canonicalPadicBrauerGroupAddEquivRatModInt p)

theorem canonicalPadicBrauerPhase_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (canonicalPadicBrauerPhase p) :=
  brauerInvariantStdAddChar_injective ℚ_[p]
    (canonicalPadicBrauerGroupAddEquivRatModInt p)

theorem norm_canonicalPadicBrauerPhase
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p]) :
    ‖canonicalPadicBrauerPhase p b‖ = 1 := by
  change ‖ratModIntStdAddChar
    (canonicalPadicBrauerGroupAddEquivRatModInt p b)‖ = 1
  simp [ratModIntStdAddChar]

theorem canonicalPadicBrauerPhase_eq_one_iff
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p]) :
    canonicalPadicBrauerPhase p b = 1 ↔ b = 0 := by
  constructor
  · intro hb
    apply canonicalPadicBrauerPhase_injective p
    exact hb.trans (canonicalPadicBrauerPhase p).map_zero_eq_one.symm
  · rintro rfl
    exact (canonicalPadicBrauerPhase p).map_zero_eq_one

/-- Unique local Brauer class with prescribed Frobenius-canonical invariant. -/
def canonicalPadicBrauerClassOfInvariant
    (p : ℕ) [Fact p.Prime] (q : RatModInt) : BrauerGroup ℚ_[p] :=
  (canonicalPadicBrauerGroupAddEquivRatModInt p).symm q

@[simp] theorem canonicalPadicBrauerClassOfInvariant_invariant
    (p : ℕ) [Fact p.Prime] (q : RatModInt) :
    canonicalPadicBrauerGroupAddEquivRatModInt p
        (canonicalPadicBrauerClassOfInvariant p q) = q :=
  (canonicalPadicBrauerGroupAddEquivRatModInt p).apply_symm_apply q

/-- Prescribed `ℚ/ℤ` phase is realized by its unique canonical local Brauer class. -/
theorem canonicalPadicBrauerPhase_classOfInvariant
    (p : ℕ) [Fact p.Prime] (q : RatModInt) :
    canonicalPadicBrauerPhase p (canonicalPadicBrauerClassOfInvariant p q) =
      ratModIntStdAddChar q := by
  change ratModIntStdAddChar
    (canonicalPadicBrauerGroupAddEquivRatModInt p
      (canonicalPadicBrauerClassOfInvariant p q)) = ratModIntStdAddChar q
  rw [canonicalPadicBrauerClassOfInvariant_invariant]

/-- Recoordinates the old choice-normalized local class so its old coordinate is the new
arithmetic-Frobenius coordinate. This is used only to reuse already formalized Tate analysis. -/
def canonicalPadicBrauerRecoordinate (p : ℕ) [Fact p.Prime] :
    BrauerGroup ℚ_[p] ≃+ BrauerGroup ℚ_[p] :=
  (canonicalPadicBrauerGroupAddEquivRatModInt p).trans
    (nonarchimedeanLocalBrauerGroupAddEquivRatModInt ℚ_[p]).symm

@[simp] theorem chosenPadicBrauerInvariant_recoordinate
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p]) :
    nonarchimedeanLocalBrauerGroupAddEquivRatModInt ℚ_[p]
        (canonicalPadicBrauerRecoordinate p b) =
      canonicalPadicBrauerGroupAddEquivRatModInt p b := by
  exact (nonarchimedeanLocalBrauerGroupAddEquivRatModInt ℚ_[p]).apply_symm_apply _

theorem chosenPadicBrauerPhase_recoordinate
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p]) :
    padicBrauerInvariantStdAddChar p
        (canonicalPadicBrauerRecoordinate p b) =
      canonicalPadicBrauerPhase p b := by
  change ratModIntStdAddChar
      (nonarchimedeanLocalBrauerGroupAddEquivRatModInt ℚ_[p]
        (canonicalPadicBrauerRecoordinate p b)) =
    ratModIntStdAddChar (canonicalPadicBrauerGroupAddEquivRatModInt p b)
  rw [chosenPadicBrauerInvariant_recoordinate]

/-- Canonical unramified character of `ℚ_p^*`. Recoordination cancels the old arbitrary
coordinate before entering the already established continuous character. -/
def canonicalPadicBrauerUnramifiedCharacter
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p]) : ℚ_[p]ˣ →* ℂ :=
  padicBrauerUnramifiedCharacter p (canonicalPadicBrauerRecoordinate p b)

theorem continuous_canonicalPadicBrauerUnramifiedCharacter
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p]) :
    Continuous (canonicalPadicBrauerUnramifiedCharacter p b) :=
  continuous_padicBrauerUnramifiedCharacter p
    (canonicalPadicBrauerRecoordinate p b)

theorem canonicalPadicBrauerUnramifiedCharacter_apply_chart
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p])
    (m : ℤ) (u : ℤ_[p]ˣ) :
    canonicalPadicBrauerUnramifiedCharacter p b
        (fieldOnePadicValuationUnitContinuousMulEquiv p
          (Multiplicative.ofAdd m, u)) =
      (canonicalPadicBrauerPhase p b) ^ m := by
  rw [canonicalPadicBrauerUnramifiedCharacter,
    padicBrauerUnramifiedCharacter_apply_chart,
    chosenPadicBrauerPhase_recoordinate]

/-- Canonical Brauer phase is the source-side unramified Tate character evaluated at the
valuation-one uniformizer coordinate. -/
theorem canonicalPadicBrauerUnramifiedCharacter_uniformizer
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p]) :
    canonicalPadicBrauerUnramifiedCharacter p b
        (fieldOnePadicValuationUnitContinuousMulEquiv p
          (Multiplicative.ofAdd (1 : ℤ), (1 : ℤ_[p]ˣ))) =
      canonicalPadicBrauerPhase p b := by
  rw [canonicalPadicBrauerUnramifiedCharacter_apply_chart, zpow_one]

theorem canonicalPadicBrauerUnramifiedCharacter_is_unramified
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p]) (u : ℤ_[p]ˣ) :
    canonicalPadicBrauerUnramifiedCharacter p b
        (fieldOnePadicValuationUnitContinuousMulEquiv p
          (Multiplicative.ofAdd (0 : ℤ), u)) = 1 := by
  rw [canonicalPadicBrauerUnramifiedCharacter_apply_chart, zpow_zero]

theorem canonicalPadicBrauerUnramifiedCharacter_eq_one_iff
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p]) :
    canonicalPadicBrauerUnramifiedCharacter p b = 1 ↔ b = 0 := by
  rw [canonicalPadicBrauerUnramifiedCharacter]
  rw [padicBrauerUnramifiedCharacter_eq_one_iff]
  exact (canonicalPadicBrauerRecoordinate p).map_eq_zero_iff

/-- Frobenius-canonical Brauer twist of the local Euler factor. -/
def canonicalPadicBrauerTwistedLocalEulerFactor
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p]) (q : ℂ) : ℂ :=
  brauerInvariantTwistedLocalEulerFactor ℚ_[p]
    (canonicalPadicBrauerGroupAddEquivRatModInt p) b q

theorem canonicalPadicBrauerTwistedLocalEulerFactor_eq_recoordinate
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p]) (q : ℂ) :
    canonicalPadicBrauerTwistedLocalEulerFactor p b q =
      padicBrauerTwistedLocalEulerFactor p
        (canonicalPadicBrauerRecoordinate p b) q := by
  unfold canonicalPadicBrauerTwistedLocalEulerFactor
  unfold padicBrauerTwistedLocalEulerFactor
  unfold brauerInvariantTwistedLocalEulerFactor
  change localEulerFactor (canonicalPadicBrauerPhase p b * q) =
    localEulerFactor
      (padicBrauerInvariantStdAddChar p
        (canonicalPadicBrauerRecoordinate p b) * q)
  rw [chosenPadicBrauerPhase_recoordinate]

/-- On every nonnegative valuation shell, canonical phase is literally value of unramified
source character multiplying spectral weight. -/
theorem connesPadicUnitBallProfile_canonicalBrauer_eq_unramifiedCharacter
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p])
    (q : ℂ) (n : ℕ) (u : ℤ_[p]ˣ) :
    connesPadicUnitBallProfile
        (canonicalPadicBrauerPhase p b * q) (n : ℤ) =
      canonicalPadicBrauerUnramifiedCharacter p b
          (fieldOnePadicValuationUnitContinuousMulEquiv p
            (Multiplicative.ofAdd (n : ℤ), u)) * q ^ n := by
  rw [connesPadicUnitBallProfile, if_pos (Int.natCast_nonneg n), Int.toNat_natCast,
    mul_pow, canonicalPadicBrauerUnramifiedCharacter_apply_chart, zpow_natCast]

/-- Canonical Brauer-twisted Euler factor is an actual convergent Connes--Tate integral. -/
theorem canonicalPadicBrauerTwistedLocalEulerFactor_eq_tateIntegral
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p])
    (s : {z : ℂ // 0 < z.re}) :
    canonicalPadicBrauerTwistedLocalEulerFactor p b ((p : ℂ) ^ (-(s : ℂ))) =
      ∫ a, connesPadicRadial p
        (connesPadicUnitBallProfile
          (canonicalPadicBrauerPhase p b * (p : ℂ) ^ (-(s : ℂ)))) a
        ∂fieldOnePadicMultiplicativeHaar p := by
  rw [canonicalPadicBrauerTwistedLocalEulerFactor_eq_recoordinate]
  simpa only [chosenPadicBrauerPhase_recoordinate] using
    padicBrauerTwistedLocalEulerFactor_eq_tateIntegral p
      (canonicalPadicBrauerRecoordinate p b) s.property

theorem canonicalPadicBrauerTwistedLocalEulerFactor_eq_untwisted_iff
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p])
    (q : ℂˣ) :
    canonicalPadicBrauerTwistedLocalEulerFactor p b (q : ℂ) =
      localEulerFactor (q : ℂ) ↔ b = 0 := by
  exact brauerInvariantTwistedLocalEulerFactor_eq_untwisted_iff ℚ_[p]
    (canonicalPadicBrauerGroupAddEquivRatModInt p) b q.ne_zero

/-- Sharp RH-source gate: canonical twisted Tate integral is ordinary `ζ_p` integral exactly
for split Brauer class. -/
theorem canonicalPadicBrauerTwistedTateIntegral_eq_untwisted_iff
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p])
    (s : {z : ℂ // 0 < z.re}) :
    (∫ a, connesPadicRadial p
        (connesPadicUnitBallProfile
          (canonicalPadicBrauerPhase p b * (p : ℂ) ^ (-(s : ℂ)))) a
        ∂fieldOnePadicMultiplicativeHaar p) =
      ∫ a : ℚ_[p]ˣ, Set.indicator {x : ℚ_[p]ˣ | ‖(x : ℚ_[p])‖ ≤ 1}
        (fun x : ℚ_[p]ˣ => ((‖(x : ℚ_[p])‖ : ℝ) : ℂ) ^ (s : ℂ)) a
          ∂fieldOnePadicMultiplicativeHaar p ↔ b = 0 := by
  rw [← canonicalPadicBrauerTwistedLocalEulerFactor_eq_tateIntegral p b s,
    connes_padic_tate_local_zeta p s.property]
  let q : ℂˣ := Units.mk0 ((p : ℂ) ^ (-(s : ℂ)))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by
      exact_mod_cast (Fact.out : p.Prime).ne_zero)))
  exact canonicalPadicBrauerTwistedLocalEulerFactor_eq_untwisted_iff p b q

end


end GaloisForLFunctions.RHTower
