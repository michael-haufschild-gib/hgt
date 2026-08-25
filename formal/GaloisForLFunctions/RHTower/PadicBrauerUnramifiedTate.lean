/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalBrauerInvariant
import GaloisForLFunctions.HTGeometry.ABHN.RatModIntCircleCharacter
import GaloisForLFunctions.RHTower.BrauerTorsionTwistedLocalEuler
import GaloisForLFunctions.RHTower.ConnesUnramifiedLocalZeta

/-!
# Local Brauer classes as unramified Tate characters

A chosen additive invariant `Br(ℚ_p) ≃ ℚ/ℤ`, followed by the standard faithful circle character,
produces a finite-order phase.  This file extends that phase to a continuous multiplicative
character of `ℚ_p^*`, proves it is trivial on `ℤ_p^*`, and identifies its shell profile with an
actual convergent Connes--Tate local integral.

For every `s` in the right half-plane, the resulting integrals distinguish all local Brauer
classes.  A twisted integral is the ordinary local Tate zeta integral exactly when its Brauer
class is zero.  On each factorial cyclic slice, the full construction is literally the finite
torsion twist already used by the cyclic Brauer theory.

The invariant equivalence presently uses compatible choices in the unramified cyclic exhaustion.
Thus these are certified unramified characters, but no Frobenius-normalized arithmetic canonicity
is claimed here.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- Faithful circle character induced by an additive Brauer invariant. -/
def brauerInvariantStdAddChar
    (K : Type*) [Field K] (inv : BrauerGroup K ≃+ RatModInt) :
    AddChar (BrauerGroup K) ℂ :=
  ratModIntStdAddChar.compAddMonoidHom inv.toAddMonoidHom

theorem brauerInvariantStdAddChar_injective
    (K : Type*) [Field K] (inv : BrauerGroup K ≃+ RatModInt) :
    Function.Injective (brauerInvariantStdAddChar K inv) :=
  ratModIntStdAddChar_injective.comp inv.injective

/-- Euler factor twisted by the circle phase of a full Brauer invariant. -/
def brauerInvariantTwistedLocalEulerFactor
    (K : Type*) [Field K] (inv : BrauerGroup K ≃+ RatModInt)
    (b : BrauerGroup K) (q : ℂ) : ℂ :=
  localEulerFactor (brauerInvariantStdAddChar K inv b * q)

theorem brauerInvariantTwistedLocalEulerFactor_zero
    (K : Type*) [Field K] (inv : BrauerGroup K ≃+ RatModInt) (q : ℂ) :
    brauerInvariantTwistedLocalEulerFactor K inv 0 q = localEulerFactor q := by
  rw [brauerInvariantTwistedLocalEulerFactor]
  rw [(brauerInvariantStdAddChar K inv).map_zero_eq_one]
  simp

/-- At every nonzero Euler coordinate, the twisted factor remembers the full Brauer class. -/
theorem brauerInvariantTwistedLocalEulerFactor_injective
    (K : Type*) [Field K] (inv : BrauerGroup K ≃+ RatModInt)
    {q : ℂ} (hq : q ≠ 0) :
    Function.Injective (fun b : BrauerGroup K =>
      brauerInvariantTwistedLocalEulerFactor K inv b q) := by
  intro b c hbc
  apply brauerInvariantStdAddChar_injective K inv
  unfold brauerInvariantTwistedLocalEulerFactor localEulerFactor at hbc
  have hden : 1 - brauerInvariantStdAddChar K inv b * q =
      1 - brauerInvariantStdAddChar K inv c * q := inv_inj.mp hbc
  have hmul : brauerInvariantStdAddChar K inv b * q =
      brauerInvariantStdAddChar K inv c * q := sub_right_inj.mp hden
  exact mul_right_cancel₀ hq hmul

/-- Full twisted factor is untwisted exactly at the zero Brauer class. -/
theorem brauerInvariantTwistedLocalEulerFactor_eq_untwisted_iff
    (K : Type*) [Field K] (inv : BrauerGroup K ≃+ RatModInt)
    (b : BrauerGroup K) {q : ℂ} (hq : q ≠ 0) :
    brauerInvariantTwistedLocalEulerFactor K inv b q = localEulerFactor q ↔ b = 0 := by
  rw [← brauerInvariantTwistedLocalEulerFactor_zero K inv q]
  exact (brauerInvariantTwistedLocalEulerFactor_injective K inv hq).eq_iff

/-- Full invariant of a factorial Brauer slice, retained in its finite torsion subgroup. -/
def localBrauerFactorialTorsionInvariant
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ)
    (x : localBrauerFactorialSlice K n) :
    ratModIntNTorsion (localBrauerFactorialDegree n) :=
  zmodRatModIntAddHomToNTorsion (localBrauerFactorialDegree n)
    (localBrauerFactorialDegree_ne_zero n)
    ((localBrauerFactorialCompatibleAddEquiv K n).symm x)

/-- Restriction of the full Brauer twist to every factorial slice is literally the existing
finite torsion twist. -/
theorem brauerInvariantTwistedLocalEulerFactor_factorialStage
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hTop : ⨆ n, localBrauerFactorialSlice K n = ⊤)
    (n : ℕ) (x : localBrauerFactorialSlice K n) (q : ℂ) :
    brauerInvariantTwistedLocalEulerFactor K
        (localBrauerGroupAddEquivRatModIntOfFactorialExhaustion K hTop)
        (x : BrauerGroup K) q =
      torsionInvariantTwistedLocalEulerFactor
        (localBrauerFactorialDegree n)
        (localBrauerFactorialDegree_ne_zero n)
        (localBrauerFactorialTorsionInvariant K n x) q := by
  unfold brauerInvariantTwistedLocalEulerFactor
  congr 2
  change ratModIntStdAddChar
      (localBrauerInvariantOfFactorialExhaustion K hTop (x : BrauerGroup K)) = _
  rw [localBrauerInvariantOfFactorialExhaustion_apply_stage K hTop n x]
  rw [← ratModIntStdAddChar_subtype_eq_ratModIntNTorsionStdAddChar
    (localBrauerFactorialDegree n) (localBrauerFactorialDegree_ne_zero n)
    (localBrauerFactorialTorsionInvariant K n x)]
  rfl

/-- Chosen nonarchimedean local invariant followed by the standard circle character. -/
def padicBrauerInvariantStdAddChar (p : ℕ) [Fact p.Prime] :
    AddChar (BrauerGroup ℚ_[p]) ℂ :=
  brauerInvariantStdAddChar ℚ_[p]
    (nonarchimedeanLocalBrauerGroupAddEquivRatModInt ℚ_[p])

theorem padicBrauerInvariantStdAddChar_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (padicBrauerInvariantStdAddChar p) :=
  brauerInvariantStdAddChar_injective ℚ_[p]
    (nonarchimedeanLocalBrauerGroupAddEquivRatModInt ℚ_[p])

/-- Certified local phase is one exactly at the zero Brauer class. -/
theorem padicBrauerInvariantStdAddChar_eq_one_iff
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p]) :
    padicBrauerInvariantStdAddChar p b = 1 ↔ b = 0 := by
  constructor
  · intro hb
    apply padicBrauerInvariantStdAddChar_injective p
    calc
      padicBrauerInvariantStdAddChar p b = 1 := hb
      _ = padicBrauerInvariantStdAddChar p 0 :=
        (padicBrauerInvariantStdAddChar p).map_zero_eq_one.symm
  · rintro rfl
    exact (padicBrauerInvariantStdAddChar p).map_zero_eq_one

theorem padicBrauerInvariantStdAddChar_ne_zero
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p]) :
    padicBrauerInvariantStdAddChar p b ≠ 0 := by
  intro hzero
  have hnorm : ‖padicBrauerInvariantStdAddChar p b‖ = 1 := by
    change ‖ratModIntStdAddChar
      (nonarchimedeanLocalBrauerGroupAddEquivRatModInt ℚ_[p] b)‖ = 1
    simp [ratModIntStdAddChar]
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- Every local Brauer phase has finite order. -/
theorem padicBrauerInvariantStdAddChar_exists_finiteOrder
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p]) :
    ∃ n : ℕ, n ≠ 0 ∧ (padicBrauerInvariantStdAddChar p b) ^ n = 1 := by
  obtain ⟨n, hn, htorsion⟩ := ratModInt_exists_nonzero_nsmul_eq_zero
    (nonarchimedeanLocalBrauerGroupAddEquivRatModInt ℚ_[p] b)
  refine ⟨n, hn, ?_⟩
  rw [← (padicBrauerInvariantStdAddChar p).map_nsmul_eq_pow]
  change ratModIntStdAddChar
    (nonarchimedeanLocalBrauerGroupAddEquivRatModInt ℚ_[p] (n • b)) = 1
  rw [map_nsmul, htorsion]
  exact ratModIntStdAddChar.map_zero_eq_one

/-- Character on valuation-unit coordinates attached to a local Brauer phase. -/
def padicBrauerUnramifiedChartCharacter
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p]) :
    Multiplicative ℤ × ℤ_[p]ˣ →* ℂ where
  toFun x := (padicBrauerInvariantStdAddChar p b) ^ x.1.toAdd
  map_one' := by simp
  map_mul' x y := by
    change (padicBrauerInvariantStdAddChar p b) ^ (x.1.toAdd + y.1.toAdd) = _
    exact zpow_add₀ (padicBrauerInvariantStdAddChar_ne_zero p b) _ _

/-- Continuous unramified multiplicative character of `ℚ_p^*` determined by a local Brauer
phase. -/
def padicBrauerUnramifiedCharacter
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p]) : ℚ_[p]ˣ →* ℂ :=
  (padicBrauerUnramifiedChartCharacter p b).comp
    (fieldOnePadicValuationUnitContinuousMulEquiv p).symm.toMonoidHom

theorem continuous_padicBrauerUnramifiedCharacter
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p]) :
    Continuous (padicBrauerUnramifiedCharacter p b) := by
  have hpow : Continuous (fun m : Multiplicative ℤ =>
      (padicBrauerInvariantStdAddChar p b) ^ m.toAdd) :=
    continuous_of_discreteTopology
  have hchart : Continuous (padicBrauerUnramifiedChartCharacter p b) := by
    exact hpow.comp continuous_fst
  exact hchart.comp (fieldOnePadicValuationUnitContinuousMulEquiv p).continuous_symm

theorem padicBrauerUnramifiedCharacter_apply_chart
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p])
    (m : ℤ) (u : ℤ_[p]ˣ) :
    padicBrauerUnramifiedCharacter p b
        (fieldOnePadicValuationUnitContinuousMulEquiv p
          (Multiplicative.ofAdd m, u)) =
      (padicBrauerInvariantStdAddChar p b) ^ m := by
  rw [padicBrauerUnramifiedCharacter, MonoidHom.comp_apply]
  change (padicBrauerInvariantStdAddChar p b) ^
      (((fieldOnePadicValuationUnitContinuousMulEquiv p).symm
        (fieldOnePadicValuationUnitContinuousMulEquiv p
          (Multiplicative.ofAdd m, u))).1.toAdd) = _
  rw [(fieldOnePadicValuationUnitContinuousMulEquiv p).symm_apply_apply]
  rfl

/-- Brauer character is trivial on the unit subgroup. -/
theorem padicBrauerUnramifiedCharacter_is_unramified
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p]) (u : ℤ_[p]ˣ) :
    padicBrauerUnramifiedCharacter p b
        (fieldOnePadicValuationUnitContinuousMulEquiv p
          (Multiplicative.ofAdd (0 : ℤ), u)) = 1 := by
  rw [padicBrauerUnramifiedCharacter_apply_chart]
  exact zpow_zero _

/-- Value on the chosen uniformizer is exactly the certified Brauer phase. -/
theorem padicBrauerUnramifiedCharacter_uniformizer
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p]) :
    padicBrauerUnramifiedCharacter p b
        (fieldOnePadicValuationUnitContinuousMulEquiv p
          (Multiplicative.ofAdd (1 : ℤ), (1 : ℤ_[p]ˣ))) =
      padicBrauerInvariantStdAddChar p b := by
  rw [padicBrauerUnramifiedCharacter_apply_chart]
  exact zpow_one _

/-- Entire unramified character is trivial exactly at the zero Brauer class. -/
theorem padicBrauerUnramifiedCharacter_eq_one_iff
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p]) :
    padicBrauerUnramifiedCharacter p b = 1 ↔ b = 0 := by
  constructor
  · intro hchar
    apply (padicBrauerInvariantStdAddChar_eq_one_iff p b).mp
    rw [← padicBrauerUnramifiedCharacter_uniformizer p b]
    exact DFunLike.congr_fun hchar _
  · rintro rfl
    apply MonoidHom.ext
    intro a
    obtain ⟨⟨m, u⟩, rfl⟩ :=
      (fieldOnePadicValuationUnitContinuousMulEquiv p).surjective a
    rw [show m = Multiplicative.ofAdd m.toAdd from
      (Multiplicative.ofAdd.apply_symm_apply m).symm]
    rw [padicBrauerUnramifiedCharacter_apply_chart,
      (padicBrauerInvariantStdAddChar p).map_zero_eq_one]
    simp

/-- Connes unit-ball profile is exactly the Brauer character value times the spectral weight on
every nonnegative valuation shell. -/
theorem connesPadicUnitBallProfile_brauer_eq_unramifiedCharacter
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p])
    (q : ℂ) (n : ℕ) (u : ℤ_[p]ˣ) :
    connesPadicUnitBallProfile
        (padicBrauerInvariantStdAddChar p b * q) (n : ℤ) =
      padicBrauerUnramifiedCharacter p b
          (fieldOnePadicValuationUnitContinuousMulEquiv p
            (Multiplicative.ofAdd (n : ℤ), u)) * q ^ n := by
  rw [connesPadicUnitBallProfile, if_pos (Int.natCast_nonneg n), Int.toNat_natCast,
    mul_pow, padicBrauerUnramifiedCharacter_apply_chart, zpow_natCast]

/-- Full local Brauer class twist of the `p`-adic Euler factor. -/
def padicBrauerTwistedLocalEulerFactor
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p]) (q : ℂ) : ℂ :=
  brauerInvariantTwistedLocalEulerFactor ℚ_[p]
    (nonarchimedeanLocalBrauerGroupAddEquivRatModInt ℚ_[p]) b q

/-- Brauer-twisted Euler factor is the actual convergent unramified Connes--Tate integral. -/
theorem padicBrauerTwistedLocalEulerFactor_eq_tateIntegral
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p])
    {s : ℂ} (hs : 0 < s.re) :
    padicBrauerTwistedLocalEulerFactor p b ((p : ℂ) ^ (-s)) =
      ∫ a, connesPadicRadial p
        (connesPadicUnitBallProfile
          (padicBrauerInvariantStdAddChar p b * (p : ℂ) ^ (-s))) a
        ∂fieldOnePadicMultiplicativeHaar p := by
  rw [connes_padic_unitBall_geometric p]
  · rfl
  · have hphase : ‖padicBrauerInvariantStdAddChar p b‖ = 1 := by
      change ‖ratModIntStdAddChar
        (nonarchimedeanLocalBrauerGroupAddEquivRatModInt ℚ_[p] b)‖ = 1
      simp [ratModIntStdAddChar]
    rw [norm_mul, hphase, one_mul]
    exact connes_padic_norm_cpow_neg_lt_one p hs

theorem padicBrauerTwistedLocalEulerFactor_injective
    (p : ℕ) [Fact p.Prime] {q : ℂ} (hq : q ≠ 0) :
    Function.Injective (fun b : BrauerGroup ℚ_[p] =>
      padicBrauerTwistedLocalEulerFactor p b q) :=
  brauerInvariantTwistedLocalEulerFactor_injective ℚ_[p]
    (nonarchimedeanLocalBrauerGroupAddEquivRatModInt ℚ_[p]) hq

/-- On the right half-plane, Brauer-twisted Tate integrals distinguish all local Brauer classes. -/
theorem padicBrauerTwistedTateIntegral_injective
    (p : ℕ) [Fact p.Prime] {s : ℂ} (hs : 0 < s.re) :
    Function.Injective (fun b : BrauerGroup ℚ_[p] =>
      ∫ a, connesPadicRadial p
        (connesPadicUnitBallProfile
          (padicBrauerInvariantStdAddChar p b * (p : ℂ) ^ (-s))) a
        ∂fieldOnePadicMultiplicativeHaar p) := by
  intro b c hbc
  apply padicBrauerTwistedLocalEulerFactor_injective p
    (q := (p : ℂ) ^ (-s))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by
      exact_mod_cast (Fact.out : p.Prime).ne_zero)))
  change padicBrauerTwistedLocalEulerFactor p b ((p : ℂ) ^ (-s)) =
    padicBrauerTwistedLocalEulerFactor p c ((p : ℂ) ^ (-s))
  rw [padicBrauerTwistedLocalEulerFactor_eq_tateIntegral p b hs,
    padicBrauerTwistedLocalEulerFactor_eq_tateIntegral p c hs]
  exact hbc

/-- Brauer-twisted Tate integral equals the ordinary local zeta integral exactly for the zero
Brauer class. -/
theorem padicBrauerTwistedTateIntegral_eq_untwisted_iff
    (p : ℕ) [Fact p.Prime] (b : BrauerGroup ℚ_[p])
    {s : ℂ} (hs : 0 < s.re) :
    (∫ a, connesPadicRadial p
        (connesPadicUnitBallProfile
          (padicBrauerInvariantStdAddChar p b * (p : ℂ) ^ (-s))) a
        ∂fieldOnePadicMultiplicativeHaar p) =
      ∫ a : ℚ_[p]ˣ, Set.indicator {x : ℚ_[p]ˣ | ‖(x : ℚ_[p])‖ ≤ 1}
        (fun x : ℚ_[p]ˣ => ((‖(x : ℚ_[p])‖ : ℝ) : ℂ) ^ s) a
          ∂fieldOnePadicMultiplicativeHaar p ↔ b = 0 := by
  rw [← padicBrauerTwistedLocalEulerFactor_eq_tateIntegral p b hs,
    connes_padic_tate_local_zeta p hs]
  exact brauerInvariantTwistedLocalEulerFactor_eq_untwisted_iff ℚ_[p]
    (nonarchimedeanLocalBrauerGroupAddEquivRatModInt ℚ_[p]) b
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by
      exact_mod_cast (Fact.out : p.Prime).ne_zero)))

end

end GaloisForLFunctions.RHTower
