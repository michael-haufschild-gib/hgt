import GaloisForLFunctions.RHTower.ThetaDivisorCardinalSource
import GaloisForLFunctions.RHTower.CHMDGraphDivisorPairing
import GaloisForLFunctions.RHTower.CHMDStage16ZeroSideSymmetriesAndXiConvolutionAnnihilation

/-!
# Exact zero-orbit readout of the admitted cardinal sources

The source transform and the explicit-formula convention are identified using
evenness. Real scalar packets retain both conjugate orbit incidences and both
polar cancellations. Their full zero sums have finite support.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower
open WeilSpectral CHMDStage16

theorem paperFT_eq_sourceTransform_neg (f : ℝ → ℂ) (z : ℂ) :
    paperFT f z = sourceTransform f (-z) := by
  unfold paperFT sourceTransform
  apply integral_congr_ae
  filter_upwards [] with x
  rw [show -I * (-z) * (x : ℂ) = I * z * x by ring]
  exact mul_comm _ _

theorem paperFT_eq_sourceTransform_of_even {f : ℝ → ℂ} (he : ∀ x, f (-x) = f x) (z : ℂ) :
    paperFT f z = sourceTransform f z := by
  rw [paperFT_eq_sourceTransform_neg, sourceTransform_neg_eq_of_even he]

def unsignedOrbitIndicator (a z : ℂ) : ℝ := if z = a ∨ z = -a then 1 else 0

theorem unsignedOrbitIndicator_nonneg (a z : ℂ) : 0 ≤ unsignedOrbitIndicator a z := by
  unfold unsignedOrbitIndicator
  split_ifs <;> norm_num

def cardinalRealSource (a c : ℂ) (x : ℝ) : ℝ := (c * divisorCardinalSource a x).re

def cardinalOrbitValue (a c z : ℂ) : ℂ :=
  (c * (unsignedOrbitIndicator a z : ℂ) +
    conj c * (unsignedOrbitIndicator a (conj z) : ℂ)) / 2

theorem cardinalRealSource_paperFT {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0)
    (c : ℂ) {z : ℂ} (hzero : XiC z = 0) :
    paperFT (fun x => (cardinalRealSource a c x : ℂ)) z = cardinalOrbitValue a c z := by
  obtain ⟨hs, _, _, he, _⟩ := divisorCardinalSource_regularity ha hz
  have hec : ∀ x, c * divisorCardinalSource a (-x) = c * divisorCardinalSource a x :=
    fun x => by rw [he x]
  have hzec : XiC (conj z) = 0 := by rw [XiC_conj, hzero, map_zero]
  change paperFT (fun x => ((c * divisorCardinalSource a x).re : ℂ)) z = _
  rw [paperFT_eq_sourceTransform_of_even (fun x => by rw [hec x]),
    sourceTransform_ofReal_re (hs.const_mul c) hec, sourceTransform_const_mul,
    sourceTransform_const_mul, divisorCardinalSource_transform ha hz hzero,
    divisorCardinalSource_transform ha hz hzec]
  unfold cardinalOrbitValue unsignedOrbitIndicator
  split_ifs <;> simp

theorem cardinalOrbitValue_conj (a c z : ℂ) :
    cardinalOrbitValue a c (conj z) = conj (cardinalOrbitValue a c z) := by
  simp only [cardinalOrbitValue, map_add, map_mul, map_div₀, conj_conj, map_ofNat,
    Complex.conj_ofReal]
  ring

theorem cardinalOrbitValue_sq_re (a c z : ℂ) :
    (cardinalOrbitValue a c z ^ 2).re =
      c.re ^ 2 * ((unsignedOrbitIndicator a z + unsignedOrbitIndicator a (conj z))/2)^2 -
      c.im ^ 2 * ((unsignedOrbitIndicator a z - unsignedOrbitIndicator a (conj z))/2)^2 := by
  simp only [cardinalOrbitValue, pow_two, Complex.div_re, Complex.mul_re,
    Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num
  ring

theorem cardinalRealSource_poles {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0) (c : ℂ) :
    paperFT (fun x => (cardinalRealSource a c x : ℂ)) (I/2) = 0 ∧
      paperFT (fun x => (cardinalRealSource a c x : ℂ)) (-I/2) = 0 := by
  obtain ⟨hs, _, _, he, _⟩ := divisorCardinalSource_regularity ha hz
  have hec : ∀ x, c * divisorCardinalSource a (-x) = c * divisorCardinalSource a x :=
    fun x => by rw [he x]
  have hp := divisorCardinalSource_poles ha hz
  have hc₁ : conj (I/2 : ℂ) = -I/2 := by simp only [map_div₀, map_ofNat, conj_I]
  have hc₂ : conj (-I/2 : ℂ) = I/2 := by simp only [map_div₀, map_ofNat, map_neg, conj_I, neg_neg]
  constructor <;>
    change paperFT (fun x => ((c * divisorCardinalSource a x).re : ℂ)) _ = _
  all_goals
    rw [paperFT_eq_sourceTransform_of_even (fun x => by rw [hec x]),
      sourceTransform_ofReal_re (hs.const_mul c) hec]
    simp only [sourceTransform_const_mul, hc₁, hc₂, hp.1, hp.2, mul_zero, map_zero,
      add_zero, zero_div]

theorem gammaOf_carrier_injective :
    Function.Injective (fun ρ : zetaZeroConfig.carrier => gammaOf (ρ : ℂ)) := by
  intro ρ σ h
  apply Subtype.ext
  unfold gammaOf at h
  have hs : (ρ : ℂ) - 1/2 = (σ : ℂ) - 1/2 := (div_left_inj' I_ne_zero).mp h
  exact sub_left_injective hs

def cardinalOrbit (a : ℂ) : Set ℂ := {a, -a, conj a, -conj a}

theorem cardinalOrbit_finite (a : ℂ) : (cardinalOrbit a).Finite := by
  simp [cardinalOrbit]

theorem unsignedOrbitIndicator_pair_eq_zero {a z : ℂ} (hz : z ∉ cardinalOrbit a) :
    unsignedOrbitIndicator a z = 0 ∧ unsignedOrbitIndicator a (conj z) = 0 := by
  have hza : ¬ (z = a ∨ z = -a) := by
    intro h
    apply hz
    rcases h with h | h <;> simp [cardinalOrbit, h]
  have hzb : ¬ (conj z = a ∨ conj z = -a) := by
    intro h
    rcases h with h | h
    · have he := congrArg conj h
      simp only [conj_conj] at he
      exact hz (by simp [cardinalOrbit, he])
    · have he := congrArg conj h
      simp only [conj_conj, map_neg] at he
      exact hz (by simp [cardinalOrbit, he])
  simp [unsignedOrbitIndicator, hza, hzb]

theorem cardinalOrbitValue_eq_zero {a c z : ℂ} (hz : z ∉ cardinalOrbit a) :
    cardinalOrbitValue a c z = 0 := by
  obtain ⟨h1, h2⟩ := unsignedOrbitIndicator_pair_eq_zero hz
  simp [cardinalOrbitValue, h1, h2]

theorem summable_of_cardinalOrbit_support {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    {a : ℂ} {f : zetaZeroConfig.carrier → E}
    (hf : ∀ ρ : zetaZeroConfig.carrier, gammaOf (ρ : ℂ) ∉ cardinalOrbit a → f ρ = 0) : Summable f := by
  have hs : ((fun ρ : zetaZeroConfig.carrier => gammaOf (ρ : ℂ)) ⁻¹' cardinalOrbit a).Finite :=
    (cardinalOrbit_finite a).preimage gammaOf_carrier_injective.injOn
  apply summable_of_hasFiniteSupport
  apply hs.subset
  intro ρ hρ
  by_contra h
  exact hρ (hf ρ h)

theorem summable_cardinalRealSource_W {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0) (c : ℂ) :
    Summable (fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand
      (fun x => (cardinalRealSource a c x : ℂ)) (fun x => (cardinalRealSource a c x : ℂ)) ρ) := by
  apply summable_of_cardinalOrbit_support (a := a)
  intro ρ hρ
  rw [ZeroConfig.Wsummand, cardinalRealSource_paperFT ha hz c (XiC_gammaOf_eq_zero ρ),
    cardinalOrbitValue_eq_zero hρ, mul_zero, zero_mul]

end RHTower
