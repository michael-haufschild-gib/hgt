import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingGaussianDivisibilityEndpoint
import GaloisForLFunctions.RHTower.RationalHurwitzLorentzBoost

/-!
# Theta-cusp Hawking modular-boost and persistent-partner endpoint

Bisognano--Wichmann modular evolution is a Lorentz boost, while the Hawking thermal channel is
obtained only after restricting a doubled pure state to one horizon sector.  The theta source has
exactly this doubled geometry.  At source coordinate `x`, aperture `a` sends the even datum
`(k(x), 0)` through the boost of rapidity `-a*x`.  Its light-cone coordinates are the actual
opposite theta rays

`(exp(-a*x) k(x), exp(a*x) k(x))`.

The full aperture evolution is therefore a reversible boost group preserving the Krein norm.  It
is not the serial composition of reduced amplifiers with a fresh partner vacuum at every aperture
slice: coherent rapidities add, whereas reduced gains multiply.  Their difference is a strictly
positive partner-memory term when both slices are nontrivial.

Fourier observation of one ray is exactly the continued Xi amplitude.  Nondecrease of every
observed power is equivalent to RH, but is not proved by boost conservation: Fourier observation
can destroy the pointwise future-cone order.  Thus the honest remaining Hawking endpoint is to
derive observed passivity while retaining the partner, rather than postulating a Markov channel
in the aperture parameter.
-/

open Complex Real Matrix
open scoped FourierTransform

noncomputable section

namespace RHTower

/-! ## Exact doubled-source modular boost -/

/-- Wedge-modular boost carried by aperture `a` at source coordinate `x`. -/
def thetaCuspHawkingSourceBoost (a x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  lorentzBoost (-(a * x))

/-- Even/odd quadratures of the aperture-tilted doubled theta source. -/
def thetaCuspHawkingSourceEvenOdd (a x : ℝ) : Fin 2 → ℝ :=
  (thetaCuspHawkingSourceBoost a x).mulVec ![thetaCuspFullSource x, 0]

/-- Opposite horizon rays obtained from the even/odd source quadratures. -/
def thetaCuspHawkingSourceRays (a x : ℝ) : Fin 2 → ℝ :=
  lightConeChart.mulVec (thetaCuspHawkingSourceEvenOdd a x)

/-- The even/odd theta quadratures are the visible/partner squeeze coordinates. -/
theorem thetaCuspHawkingSourceEvenOdd_eq (a x : ℝ) :
    thetaCuspHawkingSourceEvenOdd a x =
      ![Real.cosh (a * x) * thetaCuspFullSource x,
        -Real.sinh (a * x) * thetaCuspFullSource x] := by
  funext i
  fin_cases i <;>
    simp [thetaCuspHawkingSourceEvenOdd, thetaCuspHawkingSourceBoost,
      lorentzBoost, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The light-cone coordinates are the literal reciprocal exponential theta rays. -/
theorem thetaCuspHawkingSourceRays_eq (a x : ℝ) :
    thetaCuspHawkingSourceRays a x =
      ![Real.exp (-a * x) * thetaCuspFullSource x,
        Real.exp (a * x) * thetaCuspFullSource x] := by
  rw [thetaCuspHawkingSourceRays, thetaCuspHawkingSourceEvenOdd_eq]
  funext i
  fin_cases i <;>
    simp [lightConeChart, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Real.cosh_eq, Real.sinh_eq] <;>
    ring

/-- Real part of the physical tilted source on one ray. -/
theorem thetaCuspRightLineSource_re
    (a : ℝ) (ha : |a| < 1) (x : ℝ) :
    (thetaCuspRightLineSource a ha x).re =
      Real.exp (-a * x) * thetaCuspFullSource x := by
  rw [thetaCuspRightLineSource_apply]
  norm_cast

/-- Real part of the physical tilted source on the reflected ray. -/
theorem thetaCuspRightLineSource_neg_re
    (a : ℝ) (ha : |a| < 1) (x : ℝ) :
    (thetaCuspRightLineSource a ha (-x)).re =
      Real.exp (a * x) * thetaCuspFullSource x := by
  rw [thetaCuspRightLineSource_apply]
  norm_cast
  rw [thetaCuspFullSource_neg]
  congr 2
  ring

/-- Inside the Fourier--Laplace strip, the first boost ray is the actual source at `x`. -/
theorem thetaCuspHawkingSourceRays_zero_eq_rightLineSource
    (a : ℝ) (ha : |a| < 1) (x : ℝ) :
    thetaCuspHawkingSourceRays a x 0 =
      (thetaCuspRightLineSource a ha x).re := by
  rw [thetaCuspHawkingSourceRays_eq]
  exact (thetaCuspRightLineSource_re a ha x).symm

/-- Inside the Fourier--Laplace strip, the second boost ray is the reflected horizon partner. -/
theorem thetaCuspHawkingSourceRays_one_eq_rightLineSource_neg
    (a : ℝ) (ha : |a| < 1) (x : ℝ) :
    thetaCuspHawkingSourceRays a x 1 =
      (thetaCuspRightLineSource a ha (-x)).re := by
  rw [thetaCuspHawkingSourceRays_eq]
  exact (thetaCuspRightLineSource_neg_re a ha x).symm

/-- Aperture addition is exact source-side boost composition. -/
theorem thetaCuspHawkingSourceBoost_add (a c x : ℝ) :
    thetaCuspHawkingSourceBoost (a + c) x =
      thetaCuspHawkingSourceBoost c x * thetaCuspHawkingSourceBoost a x := by
  rw [thetaCuspHawkingSourceBoost, thetaCuspHawkingSourceBoost,
    thetaCuspHawkingSourceBoost, lorentzBoost_mul]
  congr 1
  ring

/-- Product of opposite light-cone rays is independent of aperture. -/
theorem thetaCuspHawkingSourceRays_product (a x : ℝ) :
    thetaCuspHawkingSourceRays a x 0 * thetaCuspHawkingSourceRays a x 1 =
      thetaCuspFullSource x ^ (2 : ℕ) := by
  rw [thetaCuspHawkingSourceRays_eq]
  simp
  calc
    Real.exp (-(a * x)) * thetaCuspFullSource x *
          (Real.exp (a * x) * thetaCuspFullSource x) =
        (Real.exp (-(a * x)) * Real.exp (a * x)) *
          thetaCuspFullSource x ^ (2 : ℕ) := by ring
    _ = thetaCuspFullSource x ^ (2 : ℕ) := by
      rw [← Real.exp_add]
      simp

/-- Krein purity of every local doubled-source fibre. -/
theorem thetaCuspHawkingSourceEvenOdd_kreinPurity (a x : ℝ) :
    thetaCuspHawkingSourceEvenOdd a x 0 ^ (2 : ℕ) -
        thetaCuspHawkingSourceEvenOdd a x 1 ^ (2 : ℕ) =
      thetaCuspFullSource x ^ (2 : ℕ) := by
  rw [thetaCuspHawkingSourceEvenOdd_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith [Real.cosh_sq_sub_sinh_sq (a * x)]

/-! ## Persistent partner versus Markov reset -/

/-- Reduced one-sector amplifier gain of a two-mode squeeze at rapidity `r`. -/
def thetaCuspHawkingModularGain (r : ℝ) : ℝ :=
  Real.cosh r ^ (2 : ℕ)

/-- Partner occupation generated by the same pure two-mode squeeze. -/
def thetaCuspHawkingModularPartnerNumber (r : ℝ) : ℝ :=
  Real.sinh r ^ (2 : ℕ)

/-- Exact local CCR balance of visible gain and partner production. -/
theorem thetaCuspHawkingModularGain_sub_partnerNumber (r : ℝ) :
    thetaCuspHawkingModularGain r - thetaCuspHawkingModularPartnerNumber r = 1 := by
  exact Real.cosh_sq_sub_sinh_sq r

/-- Gain missed by replacing the persistent partner with a fresh vacuum between two boost
slices. -/
def thetaCuspHawkingPartnerMemoryDefect (r s : ℝ) : ℝ :=
  thetaCuspHawkingModularGain (r + s) -
    thetaCuspHawkingModularGain r * thetaCuspHawkingModularGain s

/-- Exact coherent partner-memory cross term. -/
theorem thetaCuspHawkingPartnerMemoryDefect_eq (r s : ℝ) :
    thetaCuspHawkingPartnerMemoryDefect r s =
      2 * Real.cosh r * Real.cosh s * Real.sinh r * Real.sinh s +
        Real.sinh r ^ (2 : ℕ) * Real.sinh s ^ (2 : ℕ) := by
  rw [thetaCuspHawkingPartnerMemoryDefect, thetaCuspHawkingModularGain,
    thetaCuspHawkingModularGain, thetaCuspHawkingModularGain, Real.cosh_add]
  ring

/-- Two nontrivial future boost slices have strictly positive partner memory. -/
theorem thetaCuspHawkingPartnerMemoryDefect_pos
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    0 < thetaCuspHawkingPartnerMemoryDefect r s := by
  rw [thetaCuspHawkingPartnerMemoryDefect_eq]
  have hsr : 0 < Real.sinh r := Real.sinh_pos_iff.mpr hr
  have hss : 0 < Real.sinh s := Real.sinh_pos_iff.mpr hs
  positivity

/-- Coherent aperture evolution cannot equal serial reduced-amplifier evolution with a reset
partner. -/
theorem thetaCuspHawkingCoherentGain_gt_markovReset
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    thetaCuspHawkingModularGain r * thetaCuspHawkingModularGain s <
      thetaCuspHawkingModularGain (r + s) := by
  have hmemory := thetaCuspHawkingPartnerMemoryDefect_pos hr hs
  rw [thetaCuspHawkingPartnerMemoryDefect] at hmemory
  linarith

/-- Source-specialized strict Markov-reset obstruction at positive apertures and positive ray
coordinate. -/
theorem thetaCuspHawkingSourceGain_gt_markovReset
    {a c x : ℝ} (ha : 0 < a) (hc : 0 < c) (hx : 0 < x) :
    thetaCuspHawkingModularGain (a * x) * thetaCuspHawkingModularGain (c * x) <
      thetaCuspHawkingModularGain ((a + c) * x) := by
  have h := thetaCuspHawkingCoherentGain_gt_markovReset
    (mul_pos ha hx) (mul_pos hc hx)
  simpa [add_mul] using h

/-! ## Fourier observation and the RH boundary -/

/-- Physical one-ray Fourier observation of the modularly boosted theta source. -/
def thetaCuspHawkingModularObservedAmplitude
    (a : ℝ) (ha : |a| < 1) (b : ℝ) : ℂ :=
  FourierTransform.fourier (thetaCuspRightLineSource a ha)
    (b / (2 * Real.pi))

/-- The modularly observed source amplitude is exactly completed Xi on that aperture line. -/
theorem thetaCuspHawkingModularObservedAmplitude_eq_xi
    (a : ℝ) (ha : |a| < 1) (b : ℝ) :
    thetaCuspHawkingModularObservedAmplitude a ha b =
      xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) := by
  exact fourier_thetaCuspRightLineSource_scaled ha b

/-- The physical Fourier observation is the source-normalized Hawking strip pair amplitude. -/
theorem thetaCuspHawkingModularObservedAmplitude_eq_stripPairAmplitude
    (a : ℝ) (ha : |a| < 1) (b : ℝ) :
    thetaCuspHawkingModularObservedAmplitude a ha b =
      thetaCuspHawkingStripPairAmplitude a b := by
  rw [thetaCuspHawkingModularObservedAmplitude_eq_xi,
    thetaCuspHawkingStripPairAmplitude, thetaCuspHawkingDeembeddedPairAmplitude, XiC]
  congr 1
  rw [sub_mul, mul_assoc, I_mul_I]
  ring

/-- No power backflow after Fourier observation of the persistent-partner modular source flow. -/
def ThetaCuspHawkingModularObservedPassive : Prop :=
  ∀ a₁ a₂ : ℝ, 0 < a₁ → a₁ ≤ a₂ → a₂ < 1 / 2 → ∀ b : ℝ,
    normSq (thetaCuspHawkingStripPairAmplitude a₁ b) ≤
      normSq (thetaCuspHawkingStripPairAmplitude a₂ b)

/-- Observed modular passivity is exactly finite divisibility of the reduced Hawking amplifiers.
The equivalence does not manufacture the causal intermediate channel. -/
theorem thetaCuspHawkingModularObservedPassive_iff_amplifierCPDivisible :
    ThetaCuspHawkingModularObservedPassive ↔
      ThetaCuspHawkingAmplifierCPDivisible := by
  constructor
  · intro hpass a₁ a₂ ha₁ ha₁₂ ha₂ b
    apply (quantumLimitedAmplifierDivides_iff_le
      (thetaCuspHawkingAmplifierGain_isQuantumLimited a₁ b)).2
    unfold thetaCuspHawkingAmplifierGain
    simpa [add_comm] using add_le_add_left (hpass a₁ a₂ ha₁ ha₁₂ ha₂ b) 1
  · intro hcp a₁ a₂ ha₁ ha₁₂ ha₂ b
    have hgain := (quantumLimitedAmplifierDivides_iff_le
      (thetaCuspHawkingAmplifierGain_isQuantumLimited a₁ b)).1
        (hcp a₁ a₂ ha₁ ha₁₂ ha₂ b)
    unfold thetaCuspHawkingAmplifierGain at hgain
    linarith

/-- **Modular Hawking endpoint.** RH is equivalent to absence of observed power backflow for the
exact doubled theta-source boost.  The open producer is the source-specific passage from coherent
partner dynamics to this observed passivity law. -/
theorem thetaCuspHawkingModularObservedPassive_iff_riemannHypothesis :
    ThetaCuspHawkingModularObservedPassive ↔ RiemannHypothesis :=
  thetaCuspHawkingModularObservedPassive_iff_amplifierCPDivisible.trans
    thetaCuspHawkingAmplifierCPDivisible_iff_riemannHypothesis

end RHTower
