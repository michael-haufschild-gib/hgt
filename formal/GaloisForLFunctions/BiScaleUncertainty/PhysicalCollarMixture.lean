import GaloisForLFunctions.BiScaleUncertainty.SignedGramCapacity
import Mathlib.Tactic.Module

/-!
# Physical convex mixtures and full-Gram displacement bounds

Convex mixing preserves the actual measurable collar allocation. The singular
origin anchor cancels from packet displacements. Uniform physical mass bounds
then control their squared norm without discarding signed cross-coset entries.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators CompactlySupported
open RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
noncomputable section
variable {n : ℕ}

def mixture (ρ η : PhysicalCollarPartition n) (τ : Icc (0 : ℝ) 1) : PhysicalCollarPartition n where
  share k x := (1 - (τ : ℝ)) * ρ.share k x + (τ : ℝ) * η.share k x
  measurable_share k := ((ρ.measurable_share k).const_mul _).add ((η.measurable_share k).const_mul _)
  nonneg k x := add_nonneg (mul_nonneg (sub_nonneg.mpr τ.property.2) (ρ.nonneg k x))
    (mul_nonneg τ.property.1 (η.nonneg k x))
  supported := by
    intro k x hx
    rw [ρ.supported k x hx, η.supported k x hx]
    ring
  partition := by
    intro x
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ρ.partition, η.partition]
    ring

theorem mixture_density (ρ η : PhysicalCollarPartition n) (τ : Icc (0 : ℝ) 1) (k : ℕ) (x : ℝ) :
    (ρ.mixture η τ).density k x = (1 - (τ : ℝ)) * ρ.density k x + (τ : ℝ) * η.density k x := by
  unfold density mixture
  ring

theorem mixture_weight (ρ η : PhysicalCollarPartition n) (τ : Icc (0 : ℝ) 1)
    (σ : Bool) (k : ℕ) (y : ℝ) :
    (ρ.mixture η τ).weight σ k y = (1 - (τ : ℝ)) * ρ.weight σ k y + (τ : ℝ) * η.weight σ k y :=
  ρ.mixture_density η τ k _

def gramPacket (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (y : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  AnchoredGram.packet f (signedGramNodes n) (fun p => ρ.weight p.1 p.2 y)
    signedGramShift (archLevySinhWeight y)

theorem mixture_gramPacket (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    (τ : Icc (0 : ℝ) 1) (y : ℝ) :
    (ρ.mixture η τ).gramPacket f y =
      (1 - ((τ : ℝ) : ℂ)) • ρ.gramPacket f y + ((τ : ℝ) : ℂ) • η.gramPacket f y := by
  unfold gramPacket AnchoredGram.packet
  simp only [mixture_weight, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one, add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
  module

theorem mixture_gramPacket_displacement (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    (τ : Icc (0 : ℝ) 1) (y : ℝ) :
    ρ.gramPacket f y - (ρ.mixture η τ).gramPacket f y =
      ((τ : ℝ) : ℂ) • (ρ.gramPacket f y - η.gramPacket f y) := by
  rw [ρ.mixture_gramPacket η f τ y]
  module

theorem mixture_gramPacket_displacement_sq (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    (τ : Icc (0 : ℝ) 1) (y : ℝ) :
    ‖ρ.gramPacket f y - (ρ.mixture η τ).gramPacket f y‖ ^ 2 =
      (τ : ℝ) ^ 2 * ‖ρ.gramPacket f y - η.gramPacket f y‖ ^ 2 := by
  rw [ρ.mixture_gramPacket_displacement η f τ y, norm_smul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

def fibreMassBound (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ) * (2 * logarithmicCollarWeightBound n)

def transportedMass (n : ℕ) : ℝ :=
  ∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), archLevySinhWeight x

theorem fibreMassBound_pos (n : ℕ) : 0 < fibreMassBound n := by
  unfold fibreMassBound
  positivity [logarithmicCollarWeightBound_pos n]

theorem mass_nonneg (ρ : PhysicalCollarPartition n) (y : ℝ) : 0 ≤ ρ.mass y :=
  Finset.sum_nonneg fun k _ => add_nonneg (ρ.weight_nonneg false k y) (ρ.weight_nonneg true k y)

theorem transportedMass_nonneg (n : ℕ) : 0 ≤ transportedMass n := by
  rw [transportedMass, ← (equalMultiplicity n).integral_mass]
  exact integral_nonneg ((equalMultiplicity n).mass_nonneg)

/-- The common singular anchor disappears before the triangle inequality. -/
theorem gramPacket_displacement_le (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (y : ℝ) :
    ‖ρ.gramPacket f y - η.gramPacket f y‖ ≤ Real.sqrt (autocorr f 0) * (ρ.mass y + η.mass y) := by
  let a := AnchoredGram.packet f (signedGramNodes n) (fun p => ρ.weight p.1 p.2 y) signedGramShift 0
  let b := AnchoredGram.packet f (signedGramNodes n) (fun p => η.weight p.1 p.2 y) signedGramShift 0
  have he : ρ.gramPacket f y - η.gramPacket f y = a - b := by
    simp only [gramPacket, AnchoredGram.packet, a, b, Complex.ofReal_zero, zero_smul, zero_add]
    abel
  have ha := AnchoredGram.packet_zero_anchor_norm_le f (signedGramNodes n)
    (fun p => ρ.weight p.1 p.2 y) signedGramShift (fun p _ => ρ.weight_nonneg p.1 p.2 y)
  have hb := AnchoredGram.packet_zero_anchor_norm_le f (signedGramNodes n)
    (fun p => η.weight p.1 p.2 y) signedGramShift (fun p _ => η.weight_nonneg p.1 p.2 y)
  rw [ρ.signedGram_mass y] at ha
  rw [η.signedGram_mass y] at hb
  rw [he]
  have hd := norm_sub_le a b
  change ‖a‖ ≤ _ at ha
  change ‖b‖ ≤ _ at hb
  nlinarith only [ha, hb, hd]

/-- Full measured-Gram displacement has an integrable linear mass majorant. -/
theorem gramPacket_displacement_sq_le (ρ η : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (y : ℝ) :
    ‖ρ.gramPacket f y - η.gramPacket f y‖ ^ 2 ≤
      2 * autocorr f 0 * fibreMassBound n * (ρ.mass y + η.mass y) := by
  have hn := ρ.gramPacket_displacement_le η f y
  have hm := add_nonneg (ρ.mass_nonneg y) (η.mass_nonneg y)
  have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hm)).mpr hn
  rw [mul_pow, Real.sq_sqrt (autocorr_zero_nonneg f)] at hsq
  have hmass : ρ.mass y + η.mass y ≤ 2 * fibreMassBound n := by
    have hρ := ρ.mass_le_bound y
    have hη := η.mass_le_bound y
    change ρ.mass y ≤ fibreMassBound n at hρ
    change η.mass y ≤ fibreMassBound n at hη
    linarith only [hρ, hη]
  have hmul := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmass hm)
    (autocorr_zero_nonneg f)
  nlinarith only [hsq, hmul]

end
end GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
