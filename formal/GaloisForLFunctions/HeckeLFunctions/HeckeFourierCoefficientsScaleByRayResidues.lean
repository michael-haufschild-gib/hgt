import GaloisForLFunctions.HeckeLFunctions.HeckeFiniteFourierCoefficientsAreGaussSums

/-!
# Hecke Fourier coefficients scale by ray residues

Represent a field element prime to the modulus by a unit numerator and
unit denominator. The integral Gauss scaling law then gives covariance
under this actual ray residue whenever both frequencies belong to the
trace-dual ideal. Multiplication by an element of the base ideal also
transfers a frequency to the unit base. Comparing actual residue trace
characters gives the exact finite-character factor in that transfer.
-/

noncomputable section
open NumberField
open scoped Classical
namespace GaloisForLFunctions.HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)
  {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤) (hb0 : b ≠ ⊥)
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K
local notation "Jdual" => FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI)

local instance : Finite (𝓞 K ⧸ 𝔪.fin) :=
  𝔪.fin.finiteQuotientOfFreeOfNeBot 𝔪.fin_ne_bot
local instance : Fintype (𝓞 K ⧸ 𝔪.fin) := Fintype.ofFinite _

include hb0

/-- Unit fractions extend the primitive Gauss scaling law to elements prime to the modulus. -/
theorem finiteHeckeFourierCoefficient_mul_primeTo (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (α : primeToUnits 𝔪)
    (a a' : Jdual) (ha' : (a' : K) = (α : Kˣ) * (a : K)) :
    finiteHeckeFourierCoefficient 𝔪 hb ψ (a' : K) =
      (finiteResidueCharacter 𝔪 ψ (reduce 𝔪 α) : ℂ)⁻¹ *
        finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K) := by
  obtain ⟨r, s, _, hrs, hfrac⟩ := exists_unit_fraction 𝔪 α.2
  have hr := fun v hv => (hrs v hv).1
  have hs := fun v hv => (hrs v hv).2
  have hmul : (s : K) * (a' : K) = (r : K) * (a : K) := by
    rw [ha', ← mul_assoc]
    change (algebraMap (𝓞 K) K s * (α : Kˣ)) * (a : K) =
      algebraMap (𝓞 K) K r * (a : K)
    rw [hfrac]
  have h := congrArg (finiteHeckeFourierCoefficient 𝔪 hb ψ) hmul
  rw [finiteHeckeFourierCoefficient_smul 𝔪 hb hb0 ψ hψ a' s,
    finiteHeckeFourierCoefficient_smul 𝔪 hb hb0 ψ hψ a r] at h
  simp only [MulChar.inv_apply_eq_inv, Ring.inverse_eq_inv] at h
  rw [← coe_unitMod 𝔪 hs, ← coe_unitMod 𝔪 hr,
    finiteHeckeWeight_unit, finiteHeckeWeight_unit] at h
  have hv : (finiteResidueCharacter 𝔪 ψ (unitMod 𝔪 hs) : ℂ) ≠ 0 := Units.ne_zero _
  rw [reduce_eq 𝔪 α hr hs hfrac, map_mul, map_inv, Units.val_mul,
    Units.val_inv_eq_inv_val, mul_inv_rev, inv_inv]
  calc
    finiteHeckeFourierCoefficient 𝔪 hb ψ (a' : K) =
        (finiteResidueCharacter 𝔪 ψ (unitMod 𝔪 hs) : ℂ) *
          ((finiteResidueCharacter 𝔪 ψ (unitMod 𝔪 hs) : ℂ)⁻¹ *
            finiteHeckeFourierCoefficient 𝔪 hb ψ (a' : K)) := by
      rw [← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    _ = _ := by rw [h, mul_assoc]

/-- Multiplying a dual frequency by an element of its base ideal gives a unit-base frequency. -/
def heckeTraceFrequencyToUnitBase (a : Jdual) (x : 𝓞 K) (hx : x ∈ b) :
    FractionalIdeal.dual ℤ ℚ ((𝔪.fin * ⊤ : Ideal (𝓞 K)) : FI) :=
  ⟨(x : K) * (a : K), by
    rw [Ideal.mul_top]
    apply (FractionalIdeal.mem_dual (FractionalIdeal.coeIdeal_ne_zero.mpr 𝔪.fin_ne_bot)).mpr
    intro y hy
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 K))).mp hy
    have hmb : ((𝔪.fin * b : Ideal (𝓞 K)) : FI) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr (mul_ne_zero 𝔪.fin_ne_bot hb0)
    obtain ⟨n, hn⟩ := (FractionalIdeal.mem_dual hmb).mp a.2
      (algebraMap (𝓞 K) K (r * x))
      (FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors (𝓞 K)) (Ideal.mul_mem_mul hr hx))
    refine ⟨n, ?_⟩
    change (n : ℚ) = Algebra.trace ℚ K ((a : K) * algebraMap (𝓞 K) K (r * x)) at hn
    change (n : ℚ) = Algebra.trace ℚ K
      ((algebraMap (𝓞 K) K x * (a : K)) * algebraMap (𝓞 K) K r)
    rw [map_mul (algebraMap (𝓞 K) K)] at hn
    convert hn using 1
    congr 1
    ring⟩

/-- Base-ideal transfer is a multiplicative shift of the actual residue trace character. -/
theorem heckeResidueTraceCharacter_toUnitBase (a : Jdual) (x : 𝓞 K) (hx : x ∈ b) :
    heckeResidueTraceCharacter 𝔪 (b := ⊤) (by simp) (by simp)
        (heckeTraceFrequencyToUnitBase 𝔪 hb0 a x hx) =
      (heckeResidueTraceCharacter 𝔪 hb hb0 a).mulShift (Ideal.Quotient.mk 𝔪.fin x) := by
  ext ρ
  change numberFieldTracePhase (residueRep 𝔪 (𝔟 := ⊤) (by simp) ρ : K)
      ((x : K) * (a : K)) =
    numberFieldTracePhase (residueRep 𝔪 hb (Ideal.Quotient.mk 𝔪.fin x * ρ) : K) (a : K)
  rw [← numberFieldTracePhase_mul_left]
  symm
  have h := numberFieldTracePhase_eq_of_quotient_eq 𝔪 hb hb0 a
    (residueRep_mem hb _) (b.mul_mem_right (residueRep 𝔪 (𝔟 := ⊤) (by simp) ρ) hx)
    (by rw [mk_residueRep, map_mul, mk_residueRep])
  simpa only [map_mul] using h

/-- The primitive Fourier coefficient transfers to the unit base with its exact finite factor. -/
theorem finiteHeckeFourierCoefficient_toUnitBase (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (a : Jdual) (x : 𝓞 K) (hx : x ∈ b) :
    finiteHeckeFourierCoefficient 𝔪 (b := ⊤) (by simp) ψ ((x : K) * (a : K)) =
      (finiteHeckeWeight 𝔪 ψ)⁻¹ (Ideal.Quotient.mk 𝔪.fin x) *
        finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K) := by
  change finiteHeckeFourierCoefficient 𝔪 (b := ⊤) (by simp) ψ
    (heckeTraceFrequencyToUnitBase 𝔪 hb0 a x hx : K) = _
  rw [finiteHeckeFourierCoefficient_eq_gaussSum 𝔪 (b := ⊤) (by simp) (by simp),
    finiteHeckeFourierCoefficient_eq_gaussSum 𝔪 hb hb0,
    heckeResidueTraceCharacter_toUnitBase 𝔪 hb hb0 a x hx]
  exact FiniteRing.gaussSum_mulShift_eq_of_isPrimitive
    ((finiteHeckeWeight_isPrimitive_iff 𝔪 ψ).mpr hψ) _ _

end GaloisForLFunctions.HeckeLFunctions
