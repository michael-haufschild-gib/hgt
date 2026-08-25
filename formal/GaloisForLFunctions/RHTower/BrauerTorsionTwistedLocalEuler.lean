import GaloisForLFunctions.Core
import GaloisForLFunctions.HTGeometry.ABHN.ContinuousGaloisH2BrauerFaithful
import GaloisForLFunctions.HTGeometry.ABHN.RatModIntTorsionDirectedSystem
import GaloisForLFunctions.RHTower.ConnesTateLocalZeta

/-!
# Finite Brauer phases as twisted local Euler factors

An additive map from a torsion Brauer group to `ℂ` is necessarily zero.  The faithful nonlinear
replacement is the standard circle character of the finite local invariant.  Multiplying a local
Euler coordinate `q` by this root of unity produces the twisted factor

`(1 - χ(z) q)⁻¹`.

For `q ≠ 0` this factor remembers the complete finite invariant, is stable under refinement of
torsion denominator, and agrees with the untwisted factor exactly for the split Brauer class.  At
`q = p⁻ˢ` the untwisted factor is the actual Connes--Tate local zeta integral.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- The local Euler factor twisted by the standard phase of a finite `ℚ/ℤ` invariant. -/
def torsionInvariantTwistedLocalEulerFactor
    (n : ℕ) (hn : n ≠ 0) (z : ratModIntNTorsion n) (q : ℂ) : ℂ :=
  localEulerFactor (ratModIntNTorsionStdAddChar n hn z * q)

/-- The twisting Euler root has order dividing the torsion denominator. -/
theorem torsionInvariantTwistedLocalEulerFactor_root_pow_eq_one
    (n : ℕ) (hn : n ≠ 0) (z : ratModIntNTorsion n) :
    (ratModIntNTorsionStdAddChar n hn z) ^ n = 1 :=
  ratModIntNTorsionStdAddChar_pow_eq_one n hn z

/-- Zero invariant recovers the untwisted local Euler factor. -/
theorem torsionInvariantTwistedLocalEulerFactor_zero
    (n : ℕ) (hn : n ≠ 0) (q : ℂ) :
    torsionInvariantTwistedLocalEulerFactor n hn 0 q = localEulerFactor q := by
  rw [torsionInvariantTwistedLocalEulerFactor]
  rw [(ratModIntNTorsionStdAddChar n hn).map_zero_eq_one]
  simp

/-- At any nonzero Euler coordinate, the twisted factor faithfully remembers the finite local
invariant. -/
theorem torsionInvariantTwistedLocalEulerFactor_injective
    (n : ℕ) (hn : n ≠ 0) {q : ℂ} (hq : q ≠ 0) :
    Function.Injective (fun z : ratModIntNTorsion n =>
      torsionInvariantTwistedLocalEulerFactor n hn z q) := by
  intro z w hzw
  apply ratModIntNTorsionStdAddChar_injective n hn
  unfold torsionInvariantTwistedLocalEulerFactor localEulerFactor at hzw
  have hden : 1 - ratModIntNTorsionStdAddChar n hn z * q =
      1 - ratModIntNTorsionStdAddChar n hn w * q := inv_inj.mp hzw
  have hmul : ratModIntNTorsionStdAddChar n hn z * q =
      ratModIntNTorsionStdAddChar n hn w * q := sub_right_inj.mp hden
  exact mul_right_cancel₀ hq hmul

/-- The twisted factor is untwisted exactly at zero invariant. -/
theorem torsionInvariantTwistedLocalEulerFactor_eq_untwisted_iff
    (n : ℕ) (hn : n ≠ 0) (z : ratModIntNTorsion n) {q : ℂ} (hq : q ≠ 0) :
    torsionInvariantTwistedLocalEulerFactor n hn z q = localEulerFactor q ↔ z = 0 := by
  rw [← torsionInvariantTwistedLocalEulerFactor_zero n hn q]
  exact (torsionInvariantTwistedLocalEulerFactor_injective n hn hq).eq_iff

/-- Refining the finite invariant denominator leaves the twisted Euler factor unchanged. -/
theorem torsionInvariantTwistedLocalEulerFactor_inclusion
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ∣ n)
    (z : ratModIntNTorsion m) (q : ℂ) :
    torsionInvariantTwistedLocalEulerFactor n hn
        (ratModIntNTorsionInclusion hmn z) q =
      torsionInvariantTwistedLocalEulerFactor m hm z q := by
  unfold torsionInvariantTwistedLocalEulerFactor
  rw [ratModIntNTorsionStdAddChar_inclusion hm hn hmn]

/-- A finite cyclic Brauer class is split exactly when its twisted Euler factor is untwisted. -/
theorem finiteCyclicBrauer_eq_split_iff_twistedLocalEulerFactor_eq_untwisted
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hn : n ≠ 0)
    (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (z : ratModIntNTorsion n) {q : ℂ} (hq : q ≠ 0) :
    finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e z =
        brauerSplitClass K ↔
      torsionInvariantTwistedLocalEulerFactor n hn z q = localEulerFactor q := by
  rw [finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap_eq_split_iff,
    torsionInvariantTwistedLocalEulerFactor_eq_untwisted_iff n hn z hq]

/-- Equality of finite cyclic Brauer classes is equivalent to equality of their twisted local
Euler factors at any nonzero coordinate. -/
theorem finiteCyclicBrauer_eq_iff_twistedLocalEulerFactor_eq
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hn : n ≠ 0)
    (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (z w : ratModIntNTorsion n) {q : ℂ} (hq : q ≠ 0) :
    finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e z =
        finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e w ↔
      torsionInvariantTwistedLocalEulerFactor n hn z q =
        torsionInvariantTwistedLocalEulerFactor n hn w q := by
  constructor
  · intro h
    have hzw := finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap_injective K L n e h
    rw [hzw]
  · intro h
    have hzw := torsionInvariantTwistedLocalEulerFactor_injective n hn hq h
    rw [hzw]

/-- At a prime Euler coordinate, splitness is exactly equality with the actual Connes--Tate local
zeta integral. -/
theorem finiteCyclicBrauer_eq_split_iff_twistedPrimeLocalEulerFactor_eq_tate
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hn : n ≠ 0)
    (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (z : ratModIntNTorsion n) (p : ℕ) [Fact p.Prime] {s : ℂ} (hs : 0 < s.re) :
    finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e z =
        brauerSplitClass K ↔
      torsionInvariantTwistedLocalEulerFactor n hn z ((p : ℂ) ^ (-s)) =
        ∫ a : ℚ_[p]ˣ, Set.indicator {b : ℚ_[p]ˣ | ‖(b : ℚ_[p])‖ ≤ 1}
          (fun b : ℚ_[p]ˣ => ((‖(b : ℚ_[p])‖ : ℝ) : ℂ) ^ s) a
            ∂fieldOnePadicMultiplicativeHaar p := by
  rw [connes_padic_tate_local_zeta p hs]
  change _ ↔ torsionInvariantTwistedLocalEulerFactor n hn z ((p : ℂ) ^ (-s)) =
    localEulerFactor ((p : ℂ) ^ (-s))
  apply finiteCyclicBrauer_eq_split_iff_twistedLocalEulerFactor_eq_untwisted
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by
    exact_mod_cast (Fact.out : p.Prime).ne_zero))

/-- A nonsplit finite cyclic Brauer class produces a local Euler factor different from the actual
untwisted Connes--Tate factor, and conversely. -/
theorem finiteCyclicBrauer_ne_split_iff_twistedPrimeLocalEulerFactor_ne_tate
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hn : n ≠ 0)
    (e : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion n)
    (z : ratModIntNTorsion n) (p : ℕ) [Fact p.Prime] {s : ℂ} (hs : 0 < s.re) :
    finiteGaloisContinuousCyclicH2TorsionInvariantBrauerMap K L n e z ≠
        brauerSplitClass K ↔
      torsionInvariantTwistedLocalEulerFactor n hn z ((p : ℂ) ^ (-s)) ≠
        ∫ a : ℚ_[p]ˣ, Set.indicator {b : ℚ_[p]ˣ | ‖(b : ℚ_[p])‖ ≤ 1}
          (fun b : ℚ_[p]ˣ => ((‖(b : ℚ_[p])‖ : ℝ) : ℂ) ^ s) a
            ∂fieldOnePadicMultiplicativeHaar p :=
  not_congr (finiteCyclicBrauer_eq_split_iff_twistedPrimeLocalEulerFactor_eq_tate
    K L n hn e z p hs)

end

end GaloisForLFunctions.RHTower
