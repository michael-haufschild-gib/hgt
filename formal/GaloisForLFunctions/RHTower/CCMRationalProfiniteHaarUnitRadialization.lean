import GaloisForLFunctions.RHTower.CCMRationalIntegralFiniteAdeleCongruenceRing
import GaloisForLFunctions.RHTower.CCMRationalStrongClassSpaceHaarMellin
import GaloisForLFunctions.RHTower.CCMRationalZModUnitInvariantMobius

/-!
# Profinite Haar radialization on finite congruence quotients

Let `ψ` be a continuous function on the actual integral finite adeles which
is constant modulo `N Z-hat`.  Sampling `ψ` on diagonal residues after right
multiplication by a profinite unit and averaging over normalized Haar measure
produces a function on `ZMod N`.

The main theorem proves that this averaged function is invariant under every
unit of `ZMod N`.  The proof lifts the finite unit to a literal profinite unit,
uses multiplicative stability of adelic congruence, and then changes variables
in Haar measure.  Combined with the Möbius module, this is the exact finite
Tate radialization law.
-/

noncomputable section

open MeasureTheory Topology
open scoped Classical RestrictedProduct algebraMap

namespace GaloisForLFunctions.RHTower

private abbrev U := CCMRationalProfiniteUnit
private abbrev IntegralFiniteAdeles :=
  ccmRationalIntegralFiniteAdelesAddSubgroup

local instance : MeasurableSpace U := borel U
local instance : BorelSpace U := ⟨rfl⟩
local instance : IsFiniteMeasureOnCompacts ccmRationalProfiniteUnitHaar := by
  unfold ccmRationalProfiniteUnitHaar
  infer_instance
local instance : ccmRationalProfiniteUnitHaar.IsMulLeftInvariant := by
  unfold ccmRationalProfiniteUnitHaar
  infer_instance

@[simp]
theorem ccmRationalProfiniteUnitIntegralVal_mul (u v : U) :
    ccmRationalProfiniteUnitIntegralVal (u * v) =
      ccmRationalIntegralFiniteAdeleMul
        (ccmRationalProfiniteUnitIntegralVal u)
        (ccmRationalProfiniteUnitIntegralVal v) := by
  apply Subtype.ext
  rfl

theorem ccmRationalIntegralFiniteAdeleMul_assoc
    (x y z : IntegralFiniteAdeles) :
    ccmRationalIntegralFiniteAdeleMul
        (ccmRationalIntegralFiniteAdeleMul x y) z =
      ccmRationalIntegralFiniteAdeleMul x
        (ccmRationalIntegralFiniteAdeleMul y z) := by
  apply Subtype.ext
  exact mul_assoc _ _ _

theorem ccmRationalIntegralFiniteAdeleDiagonal_mul
    (m n : ℤ) :
    ccmRationalIntegralFiniteAdeleMul
        (ccmRationalIntegralFiniteAdeleDiagonal m)
        (ccmRationalIntegralFiniteAdeleDiagonal n) =
      ccmRationalIntegralFiniteAdeleDiagonal (m * n) := by
  apply Subtype.ext
  change algebraMap ℤ CCMRationalFiniteAdele m *
      algebraMap ℤ CCMRationalFiniteAdele n =
    algebraMap ℤ CCMRationalFiniteAdele (m * n)
  rw [map_mul]

/-- Profinite-unit sample of one residue class. -/
def ccmRationalProfiniteHaarResidueSample
    (N : ℕ) (ψ : IntegralFiniteAdeles → ℂ)
    (r : ZMod N) (u : U) : ℂ :=
  ψ (ccmRationalIntegralFiniteAdeleMul
    (ccmRationalIntegralFiniteAdeleDiagonal (r.val : ℤ))
    (ccmRationalProfiniteUnitIntegralVal u))

/-- Normalized profinite Haar average of residue samples. -/
def ccmRationalProfiniteHaarResidueAverage
    (N : ℕ) (ψ : IntegralFiniteAdeles → ℂ) (r : ZMod N) : ℂ :=
  ∫ u : U, ccmRationalProfiniteHaarResidueSample N ψ r u
    ∂ccmRationalProfiniteUnitHaar

theorem continuous_ccmRationalProfiniteHaarResidueSample
    (N : ℕ) (ψ : IntegralFiniteAdeles → ℂ) (hψ : Continuous ψ)
    (r : ZMod N) :
    Continuous (ccmRationalProfiniteHaarResidueSample N ψ r) := by
  apply hψ.comp
  rw [continuous_induced_rng]
  change Continuous (fun u : U =>
    (ccmRationalIntegralFiniteAdeleDiagonal (r.val : ℤ)).1 *
      (u.1 : CCMRationalFiniteAdele))
  fun_prop

theorem integrable_ccmRationalProfiniteHaarResidueSample
    (N : ℕ) (ψ : IntegralFiniteAdeles → ℂ) (hψ : Continuous ψ)
    (r : ZMod N) :
    Integrable (ccmRationalProfiniteHaarResidueSample N ψ r)
      ccmRationalProfiniteUnitHaar := by
  exact
    (continuous_ccmRationalProfiniteHaarResidueSample N ψ hψ r).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- A congruence-class function takes equal values on congruent integral
finite adeles. -/
def CCMRationalIntegralFiniteAdeleCongruenceInvariant
    (N : ℕ) (ψ : IntegralFiniteAdeles → ℂ) : Prop :=
  ∀ ⦃x y : IntegralFiniteAdeles⦄,
    CCMRationalIntegralFiniteAdeleCongruent N x y → ψ x = ψ y

/-- Pointwise transport underlying Haar unit invariance. -/
theorem ccmRationalProfiniteHaarResidueSample_unit_transport
    (N : ℕ) (hN : N ≠ 0)
    (ψ : IntegralFiniteAdeles → ℂ)
    (hclass : CCMRationalIntegralFiniteAdeleCongruenceInvariant N ψ)
    (a : (ZMod N)ˣ) (r : ZMod N) :
    ∃ w : U, ∀ u : U,
      ccmRationalProfiniteHaarResidueSample N ψ
          ((a : ZMod N) * r) u =
        ccmRationalProfiniteHaarResidueSample N ψ r (w * u) := by
  letI : NeZero N := ⟨hN⟩
  obtain ⟨w, hw⟩ :=
    ccmRationalZModUnit_exists_profiniteUnit_integralCongruent N hN a
  refine ⟨w, fun u => ?_⟩
  let da := ccmRationalIntegralFiniteAdeleDiagonal
    ((a : ZMod N).val : ℤ)
  let dr := ccmRationalIntegralFiniteAdeleDiagonal (r.val : ℤ)
  let du := ccmRationalProfiniteUnitIntegralVal u
  let dw := ccmRationalProfiniteUnitIntegralVal w
  have hcast :
      ((((a : ZMod N) * r).val : ℕ) : ZMod N) =
        (((a : ZMod N).val * r.val : ℕ) : ZMod N) := by
    calc
      ((((a : ZMod N) * r).val : ℕ) : ZMod N) =
          (a : ZMod N) * r := ZMod.natCast_zmod_val _
      _ = (((a : ZMod N).val : ℕ) : ZMod N) *
          ((r.val : ℕ) : ZMod N) := by
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      _ = (((a : ZMod N).val * r.val : ℕ) : ZMod N) := by
        rw [Nat.cast_mul]
  have hdiag :=
    ccmRationalIntegralFiniteAdeleDiagonal_congruent_of_intCast_eq
      (N := N) (m := (((a : ZMod N) * r).val : ℤ))
      (n := ((a : ZMod N).val * r.val : ℕ)) (by
        exact_mod_cast hcast)
  have hdiagU := hdiag.mul_right du
  have hwLeft := hw.mul_left dr
  have hwLeftU := hwLeft.mul_right du
  have hmiddle :
      ccmRationalIntegralFiniteAdeleMul
          (ccmRationalIntegralFiniteAdeleDiagonal
            (((a : ZMod N).val * r.val : ℕ) : ℤ)) du =
        ccmRationalIntegralFiniteAdeleMul
          (ccmRationalIntegralFiniteAdeleMul dr da) du := by
    rw [ccmRationalIntegralFiniteAdeleDiagonal_mul]
    congr 3
    push_cast
    ring
  have hright :
      ccmRationalIntegralFiniteAdeleMul
          (ccmRationalIntegralFiniteAdeleMul dr dw) du =
        ccmRationalIntegralFiniteAdeleMul dr
          (ccmRationalProfiniteUnitIntegralVal (w * u)) := by
    rw [ccmRationalProfiniteUnitIntegralVal_mul,
      ccmRationalIntegralFiniteAdeleMul_assoc]
  apply hclass
  have hfirst := hdiagU
  rw [hmiddle] at hfirst
  have htotal := hfirst.trans hwLeftU.symm
  rw [hright] at htotal
  simpa [ccmRationalProfiniteHaarResidueSample, dr, du, dw] using htotal

/-- **Profinite Haar radialization law.** Haar averaging projects every
continuous congruence-class function to the unit-invariant sector of
`ZMod N`. -/
theorem ccmRationalProfiniteHaarResidueAverage_unitInvariant
    (N : ℕ) (hN : N ≠ 0)
    (ψ : IntegralFiniteAdeles → ℂ)
    (hclass : CCMRationalIntegralFiniteAdeleCongruenceInvariant N ψ) :
    CCMRationalZModUnitInvariant N
      (ccmRationalProfiniteHaarResidueAverage N ψ) := by
  intro a r
  obtain ⟨w, hw⟩ :=
    ccmRationalProfiniteHaarResidueSample_unit_transport
      N hN ψ hclass a r
  rw [ccmRationalProfiniteHaarResidueAverage,
    ccmRationalProfiniteHaarResidueAverage]
  have hfun :
      ccmRationalProfiniteHaarResidueSample N ψ ((a : ZMod N) * r) =
        fun u => ccmRationalProfiniteHaarResidueSample N ψ r (w * u) := by
    funext u
    exact hw u
  rw [hfun]
  exact integral_mul_left_eq_self
    (ccmRationalProfiniteHaarResidueSample N ψ r) w

end GaloisForLFunctions.RHTower
