import GaloisForLFunctions.RHTower.PrimeDepthBVWoldAsymptoticStokesGaugeModulus
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# Source-pointed normal jet of the resolved BV--Wold degeneration

Every resolved relative frame tends to the identity at fixed prime and infinite
Wold depth, and its associated-graded action is independent of centered rate.
Finite source splittings retain more information. Dividing their transverse
displacement by the canonical vanishing BV--Wold potential gives an intrinsic
normal extension cocycle: every right splitting recovers the same map
`c \mapsto a c` at every prime/depth cell.

Thus ordinary asymptotic frames collapse while their source-pointed first normal
jet survives. On Xi divisor support, line reflection negates this jet and its
fixed locus is exactly the critical line. This is a coordinate/conservation
theorem, not a source-side proof that all Xi jets vanish.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- First normal coordinate of distinguished-splitting displacement. -/
def primeDepthBVWoldSourcePointedNormalJet
    (a : ℝ) (i : PrimeDepthBVWoldCell) : ℝ :=
  ((primeDepthBVWoldSourceRelativeGauge a i
          (primeDepthBVWoldFixedVerticalSplitting 1) -
        primeDepthBVWoldFixedVerticalSplitting 1).1.re) /
    primeDepthBVWoldNormalizedPotential i

/-- Normalization recovers hidden extension modulus exactly at every finite cell. -/
theorem primeDepthBVWoldSourcePointedNormalJet_eq
    (a : ℝ) (i : PrimeDepthBVWoldCell) :
    primeDepthBVWoldSourcePointedNormalJet a i = a := by
  rw [primeDepthBVWoldSourcePointedNormalJet,
    primeDepthBVWoldSourceRelativeGauge_fixedVerticalSplitting]
  simp [primeDepthBVWoldFixedVerticalSplitting,
    primeDepthBVWoldHorizontalInclusion]
  field_simp [(primeDepthBVWoldNormalizedPotential_pos i).ne']

/-! ## Splitting-independent extension cocycle -/

/-- Normalized horizontal displacement of an arbitrary quotient splitting. -/
def primeDepthBVWoldSourceNormalExtensionCocycle
    (a : ℝ) (i : PrimeDepthBVWoldCell)
    (s : ℂ →ₗ[ℂ] (ℂ × ℂ)) (c : ℂ) : ℂ :=
  (primeDepthBVWoldSourceRelativeGauge a i (s c) - s c).1 /
    (primeDepthBVWoldNormalizedPotential i : ℂ)

/-- Every right splitting produces the same extension cocycle `c ↦ a c`. -/
theorem primeDepthBVWoldSourceNormalExtensionCocycle_eq_of_rightInverse
    (a : ℝ) (i : PrimeDepthBVWoldCell)
    (s : ℂ →ₗ[ℂ] (ℂ × ℂ))
    (hs : primeDepthBVWoldVerticalQuotient.comp s = LinearMap.id)
    (c : ℂ) :
    primeDepthBVWoldSourceNormalExtensionCocycle a i s c = (a : ℂ) * c := by
  have hsc := LinearMap.congr_fun hs c
  change (s c).2 = c at hsc
  rw [primeDepthBVWoldSourceNormalExtensionCocycle,
    primeDepthBVWoldSourceRelativeGauge_apply]
  simp only [Prod.fst_sub]
  rw [hsc]
  push_cast
  field_simp [(primeDepthBVWoldNormalizedPotential_pos i).ne']
  ring

/-- The normal extension cocycle is independent of every choice of right splitting. -/
theorem primeDepthBVWoldSourceNormalExtensionCocycle_splitting_independent
    (a : ℝ) (i : PrimeDepthBVWoldCell)
    (s t : ℂ →ₗ[ℂ] (ℂ × ℂ))
    (hs : primeDepthBVWoldVerticalQuotient.comp s = LinearMap.id)
    (ht : primeDepthBVWoldVerticalQuotient.comp t = LinearMap.id)
    (c : ℂ) :
    primeDepthBVWoldSourceNormalExtensionCocycle a i s c =
      primeDepthBVWoldSourceNormalExtensionCocycle a i t c := by
  rw [primeDepthBVWoldSourceNormalExtensionCocycle_eq_of_rightInverse a i s hs c,
    primeDepthBVWoldSourceNormalExtensionCocycle_eq_of_rightInverse a i t ht c]

/-- The intrinsic normal cocycle is either zero or coefficient-faithful; it is
faithful exactly away from neutral displacement. -/
theorem primeDepthBVWoldSourceNormalExtensionCocycle_injective_iff
    (a : ℝ) (i : PrimeDepthBVWoldCell)
    (s : ℂ →ₗ[ℂ] (ℂ × ℂ))
    (hs : primeDepthBVWoldVerticalQuotient.comp s = LinearMap.id) :
    Function.Injective
        (primeDepthBVWoldSourceNormalExtensionCocycle a i s) ↔
      a ≠ 0 := by
  constructor
  · intro hinjective ha
    subst a
    have hzero_one : (0 : ℂ) = 1 := hinjective (by
      rw [primeDepthBVWoldSourceNormalExtensionCocycle_eq_of_rightInverse
          0 i s hs 0,
        primeDepthBVWoldSourceNormalExtensionCocycle_eq_of_rightInverse
          0 i s hs 1]
      norm_num)
    norm_num at hzero_one
  · intro ha c d hcd
    rw [primeDepthBVWoldSourceNormalExtensionCocycle_eq_of_rightInverse
        a i s hs c,
      primeDepthBVWoldSourceNormalExtensionCocycle_eq_of_rightInverse
        a i s hs d] at hcd
    have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    exact mul_left_cancel₀ haC hcd

/-- Vanishing of the whole intrinsic normal cocycle detects neutral
displacement without choosing a source coordinate. -/
theorem primeDepthBVWoldSourceNormalExtensionCocycle_eq_zero_iff
    (a : ℝ) (i : PrimeDepthBVWoldCell)
    (s : ℂ →ₗ[ℂ] (ℂ × ℂ))
    (hs : primeDepthBVWoldVerticalQuotient.comp s = LinearMap.id) :
    (∀ c, primeDepthBVWoldSourceNormalExtensionCocycle a i s c = 0) ↔
      a = 0 := by
  constructor
  · intro h
    have h_one := h 1
    rw [primeDepthBVWoldSourceNormalExtensionCocycle_eq_of_rightInverse
      a i s hs 1] at h_one
    simpa using h_one
  · rintro rfl c
    rw [primeDepthBVWoldSourceNormalExtensionCocycle_eq_of_rightInverse
      0 i s hs c]
    norm_num

/-- Normal jet survives unchanged along infinite depth. -/
theorem tendsto_primeDepthBVWoldSourcePointedNormalJet
    (a : ℝ) (p : Nat.Primes) :
    Tendsto (fun e : ℕ =>
      primeDepthBVWoldSourcePointedNormalJet a (p, e))
      atTop (nhds a) := by
  simp [primeDepthBVWoldSourcePointedNormalJet_eq]

/-- Normal jet is conserved across all prime/depth source cells. -/
theorem primeDepthBVWoldSourcePointedNormalJet_cell_independent
    (a : ℝ) (i j : PrimeDepthBVWoldCell) :
    primeDepthBVWoldSourcePointedNormalJet a i =
      primeDepthBVWoldSourcePointedNormalJet a j := by
  rw [primeDepthBVWoldSourcePointedNormalJet_eq,
    primeDepthBVWoldSourcePointedNormalJet_eq]

/-- Ordinary frame collapses while its blown-up source-pointed normal jet survives. -/
theorem primeDepthBVWoldSourceFrameCollapse_normalJetSurvival
    (a : ℝ) (p : Nat.Primes) (z : ℂ × ℂ) :
    Tendsto
        (fun e : ℕ => primeDepthBVWoldSourceRelativeGauge a (p, e) z)
        atTop (nhds z) ∧
      Tendsto
        (fun e : ℕ => primeDepthBVWoldSourcePointedNormalJet a (p, e))
        atTop (nhds a) := by
  exact ⟨primeDepthBVWoldSourceRelativeGauge_tendsto_id a p z,
    tendsto_primeDepthBVWoldSourcePointedNormalJet a p⟩

/-- Xi specialization of source-pointed normal jet. -/
def primeDepthBVWoldXiSourcePointedNormalJet
    (rho : XiDivisorSupport) (i : PrimeDepthBVWoldCell) : ℝ :=
  primeDepthBVWoldSourcePointedNormalJet
    (primeDepthBVWoldXiCenteredRate rho) i

theorem primeDepthBVWoldXiSourcePointedNormalJet_eq_centeredRate
    (rho : XiDivisorSupport) (i : PrimeDepthBVWoldCell) :
    primeDepthBVWoldXiSourcePointedNormalJet rho i =
      primeDepthBVWoldXiCenteredRate rho := by
  exact primeDepthBVWoldSourcePointedNormalJet_eq _ _

/-- **Source/spectral anomaly identification.**  On every multiplicity copy,
the splitting-independent BV--Wold normal extension cocycle is exactly minus
twice the transverse centered spectral coordinate.  This holds coefficientwise
at every prime/depth cell, so the two routes carry one and the same odd normal
class rather than merely sharing its zero locus. -/
theorem primeDepthBVWoldXiSourceNormalExtensionCocycle_eq_spectralIm
    (q : XiZeroCopy) (i : PrimeDepthBVWoldCell)
    (s : ℂ →ₗ[ℂ] (ℂ × ℂ))
    (hs : primeDepthBVWoldVerticalQuotient.comp s = LinearMap.id)
    (c : ℂ) :
    primeDepthBVWoldSourceNormalExtensionCocycle
        (primeDepthBVWoldXiCenteredRate q.1) i s c =
      -2 * ((xiSpectralPoint q).im : ℂ) * c := by
  rw [primeDepthBVWoldSourceNormalExtensionCocycle_eq_of_rightInverse
    (primeDepthBVWoldXiCenteredRate q.1) i s hs c]
  rw [primeDepthBVWoldXiCenteredRate, xiSpectralPoint]
  norm_num [Complex.mul_im]
  ring

theorem primeDepthBVWoldXiSourcePointedNormalJet_eq_zero_iff
    (rho : XiDivisorSupport) (i : PrimeDepthBVWoldCell) :
    primeDepthBVWoldXiSourcePointedNormalJet rho i = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [primeDepthBVWoldXiSourcePointedNormalJet_eq_centeredRate,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Functional-equation reflection reverses extension normal coordinate. -/
theorem primeDepthBVWoldXiSourcePointedNormalJet_reflection
    (rho : XiDivisorSupport) (i : PrimeDepthBVWoldCell) :
    primeDepthBVWoldXiSourcePointedNormalJet (xiZeroLineConjEquiv rho) i =
      -primeDepthBVWoldXiSourcePointedNormalJet rho i := by
  rw [primeDepthBVWoldXiSourcePointedNormalJet_eq_centeredRate,
    primeDepthBVWoldXiSourcePointedNormalJet_eq_centeredRate,
    primeDepthBVWoldXiCenteredRate_reflection]

/-- Critical line is fixed locus of reflection on surviving normal jet. -/
theorem primeDepthBVWoldXiSourcePointedNormalJet_reflection_fixed_iff
    (rho : XiDivisorSupport) (i : PrimeDepthBVWoldCell) :
    primeDepthBVWoldXiSourcePointedNormalJet (xiZeroLineConjEquiv rho) i =
        primeDepthBVWoldXiSourcePointedNormalJet rho i ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [primeDepthBVWoldXiSourcePointedNormalJet_reflection]
  constructor
  · intro h
    apply (primeDepthBVWoldXiSourcePointedNormalJet_eq_zero_iff rho i).mp
    linarith
  · intro h
    have hz :=
      (primeDepthBVWoldXiSourcePointedNormalJet_eq_zero_iff rho i).mpr h
    rw [hz]
    norm_num

/-- Global vanishing of source-pointed normal jets. -/
def PrimeDepthBVWoldXiSourcePointedNormalJetsVanish : Prop :=
  ∀ rho : XiDivisorSupport, ∀ i : PrimeDepthBVWoldCell,
    primeDepthBVWoldXiSourcePointedNormalJet rho i = 0

/-- RH is exactly global vanishing of surviving extension normal coordinate. -/
theorem primeDepthBVWoldXiSourcePointedNormalJetsVanish_iff_riemannHypothesis :
    PrimeDepthBVWoldXiSourcePointedNormalJetsVanish ↔ RiemannHypothesis := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half]
  constructor
  · intro h z hz
    let rho : XiDivisorSupport :=
      ⟨z, mem_xi_divisor_support_of_eq_zero hz⟩
    exact (primeDepthBVWoldXiSourcePointedNormalJet_eq_zero_iff
      rho primeDepthBVWoldWitnessZero).mp
      (h rho primeDepthBVWoldWitnessZero)
  · intro h rho i
    exact (primeDepthBVWoldXiSourcePointedNormalJet_eq_zero_iff rho i).mpr
      (h (rho : ℂ) (xi_eq_zero_of_mem_divisor_support rho))

end

end RHTower
