import GaloisForLFunctions.RHTower.QuantumRecurrenceForecastNoGoLaw
import GaloisForLFunctions.RHTower.RealCharacterDenseL2

/-!
# Cyclic Hilbert-space quantum recurrence no-go law

Every spectral probability law is realized here as a normalized cyclic
stationary history in its own `L²` Hilbert space.  The history is generated
by a reversible pointwise phase action, its transition amplitudes are exactly
the characteristic function of the spectrum, and its return fidelity is
therefore exactly the survival form factor.

Consequently, the positive-energy complete-jet recurrence obstruction is not
an artefact of treating probability spectra abstractly: it persists for
normalized cyclic Hilbert-space quantum clock histories.
-/

open Complex Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace RHTower

/-- Pointwise spectral phase evolution at time `a`. -/
def spectralPhaseEvolution (a x : ℝ) (z : ℂ) : ℂ :=
  realProbCharacter a x * z

@[simp] theorem spectralPhaseEvolution_zero (x : ℝ) (z : ℂ) :
    spectralPhaseEvolution 0 x z = z := by
  simp [spectralPhaseEvolution, realProbCharacter]

theorem spectralPhaseEvolution_add (a b x : ℝ) (z : ℂ) :
    spectralPhaseEvolution (a + b) x z =
      spectralPhaseEvolution a x (spectralPhaseEvolution b x z) := by
  simp only [spectralPhaseEvolution, realProbCharacter, add_mul]
  have hexp :
      (((a * x + b * x : ℝ) : ℂ) * Complex.I) =
        (((a * x : ℝ) : ℂ) * Complex.I) +
          (((b * x : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hexp, Complex.exp_add]
  ring

@[simp] theorem spectralPhaseEvolution_neg_cancel
    (a x : ℝ) (z : ℂ) :
    spectralPhaseEvolution (-a) x
        (spectralPhaseEvolution a x z) = z := by
  rw [← spectralPhaseEvolution_add]
  simp

theorem spectralPhaseEvolution_preserves_norm
    (a x : ℝ) (z : ℂ) :
    ‖spectralPhaseEvolution a x z‖ = ‖z‖ := by
  rw [spectralPhaseEvolution, norm_mul, norm_realProbCharacter, one_mul]

theorem spectralPhaseEvolution_preserves_inner
    (a x : ℝ) (z w : ℂ) :
    inner ℂ (spectralPhaseEvolution a x z)
        (spectralPhaseEvolution a x w) =
      inner ℂ z w := by
  simp only [spectralPhaseEvolution, RCLike.inner_apply, map_mul]
  have hunit :
      realProbCharacter a x *
          (starRingEnd ℂ) (realProbCharacter a x) = 1 := by
    rw [Complex.mul_conj]
    norm_num [Complex.normSq_eq_norm_sq, norm_realProbCharacter]
  calc
    _ = (realProbCharacter a x *
          (starRingEnd ℂ) (realProbCharacter a x)) *
          (w * (starRingEnd ℂ) z) := by ring
    _ = _ := by rw [hunit]; simp

theorem spectralPhaseEvolution_preserves_innerIntegral
    (mu : Measure ℝ) (a : ℝ) (f g : ℝ → ℂ) :
    (∫ x, inner ℂ (spectralPhaseEvolution a x (f x))
          (spectralPhaseEvolution a x (g x)) ∂mu) =
      ∫ x, inner ℂ (f x) (g x) ∂mu := by
  apply integral_congr_ae
  filter_upwards with x
  exact spectralPhaseEvolution_preserves_inner a x (f x) (g x)

theorem spectralPhaseEvolution_realProbCharacter
    (a s x : ℝ) :
    spectralPhaseEvolution a x (realProbCharacter s x) =
      realProbCharacter (s + a) x := by
  simp only [spectralPhaseEvolution, realProbCharacter, add_mul]
  have hexp :
      (((s * x + a * x : ℝ) : ℂ) * Complex.I) =
        (((s * x : ℝ) : ℂ) * Complex.I) +
          (((a * x : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hexp, Complex.exp_add]
  ring

/-- Exact transition-amplitude law for the spectral clock history. -/
theorem inner_realProbCharacterLp_eq_charFun
    (mu : Measure ℝ) [IsFiniteMeasure mu] (s t : ℝ) :
    inner ℂ (realProbCharacterLp mu s) (realProbCharacterLp mu t) =
      charFun mu (t - s) := by
  rw [L2.inner_def, charFun_apply_real]
  apply integral_congr_ae
  filter_upwards [realProbCharacterLp_ae mu s,
    realProbCharacterLp_ae mu t] with x hs ht
  rw [hs, ht]
  simp only [RCLike.inner_apply]
  rw [realProbCharacter, realProbCharacter]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I]
  simp
  ring

/-- Every state on a spectral probability clock history has unit norm. -/
theorem norm_realProbCharacterLp_probability
    (mu : ProbabilityMeasure ℝ) (t : ℝ) :
    ‖realProbCharacterLp (mu : Measure ℝ) t‖ = 1 := by
  have hsq :
      ‖realProbCharacterLp (mu : Measure ℝ) t‖ ^ 2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ),
      inner_realProbCharacterLp_eq_charFun, sub_self, charFun_zero]
    simp
  nlinarith [norm_nonneg (realProbCharacterLp (mu : Measure ℝ) t)]

theorem inner_realProbCharacterLp_stationary
    (mu : Measure ℝ) [IsFiniteMeasure mu] (a s t : ℝ) :
    inner ℂ (realProbCharacterLp mu (s + a))
        (realProbCharacterLp mu (t + a)) =
      inner ℂ (realProbCharacterLp mu s)
        (realProbCharacterLp mu t) := by
  rw [inner_realProbCharacterLp_eq_charFun,
    inner_realProbCharacterLp_eq_charFun]
  congr 1
  ring

theorem spectralPhaseEvolution_generates_realProbCharacterLp
    (mu : Measure ℝ) [IsFiniteMeasure mu] (a s : ℝ) :
    (fun x =>
      spectralPhaseEvolution a x
        ((realProbCharacterLp mu s : ℝ →ₘ[mu] ℂ) x)) =ᵐ[mu]
      (realProbCharacterLp mu (s + a) : ℝ →ₘ[mu] ℂ) := by
  filter_upwards [realProbCharacterLp_ae mu s,
    realProbCharacterLp_ae mu (s + a)] with x hs hsa
  rw [hs, hsa]
  exact spectralPhaseEvolution_realProbCharacter a s x

/-- A normalized, stationary, cyclic Hilbert-space quantum clock whose
spectral measure is `mu`.  The final field records generation by the
reversible norm- and inner-product-preserving phase action above. -/
structure CyclicStationaryHilbertClock (mu : ProbabilityMeasure ℝ) where
  state : ℝ → Lp ℂ 2 (mu : Measure ℝ)
  normalized : ∀ t : ℝ, ‖state t‖ = 1
  overlap :
    ∀ s t : ℝ,
      inner ℂ (state s) (state t) =
        charFun (mu : Measure ℝ) (t - s)
  stationary :
    ∀ a s t : ℝ,
      inner ℂ (state (s + a)) (state (t + a)) =
        inner ℂ (state s) (state t)
  cyclic : IsCyclicFamily (𝕜 := ℂ) state
  phaseGenerated :
    ∀ a s : ℝ,
      (fun x =>
        spectralPhaseEvolution a x
          ((state s : ℝ →ₘ[(mu : Measure ℝ)] ℂ) x)) =ᵐ[(mu : Measure ℝ)]
        (state (s + a) : ℝ →ₘ[(mu : Measure ℝ)] ℂ)

/-- Canonical cyclic stationary Hilbert clock of every probability spectrum. -/
def probabilitySpectrumHilbertClock (mu : ProbabilityMeasure ℝ) :
    CyclicStationaryHilbertClock mu where
  state := realProbCharacterLp (mu : Measure ℝ)
  normalized := norm_realProbCharacterLp_probability mu
  overlap := inner_realProbCharacterLp_eq_charFun (mu : Measure ℝ)
  stationary := inner_realProbCharacterLp_stationary (mu : Measure ℝ)
  cyclic := isCyclicFamily_realProbCharacterLp (mu : Measure ℝ)
  phaseGenerated :=
    spectralPhaseEvolution_generates_realProbCharacterLp
      (mu : Measure ℝ)

theorem every_probability_spectrum_has_cyclicStationaryHilbertClock
    (mu : ProbabilityMeasure ℝ) :
    Nonempty (CyclicStationaryHilbertClock mu) :=
  ⟨probabilitySpectrumHilbertClock mu⟩

/-- Complete local transition-amplitude jet of the canonical Hilbert clock. -/
def hilbertClockOverlapJet (mu : ProbabilityMeasure ℝ) : ℕ → ℂ :=
  fun n =>
    iteratedDeriv n
      (fun t =>
        inner ℂ
          ((probabilitySpectrumHilbertClock mu).state 0)
          ((probabilitySpectrumHilbertClock mu).state t)) 0

theorem hilbertClockOverlapJet_eq_charFunJet
    (mu : ProbabilityMeasure ℝ) :
    hilbertClockOverlapJet mu =
      fun n =>
        iteratedDeriv n (charFun (mu : Measure ℝ)) 0 := by
  have hoverlap :
      (fun t =>
        inner ℂ
          ((probabilitySpectrumHilbertClock mu).state 0)
          ((probabilitySpectrumHilbertClock mu).state t)) =
        charFun (mu : Measure ℝ) := by
    funext t
    simpa using (probabilitySpectrumHilbertClock mu).overlap 0 t
  funext n
  rw [hilbertClockOverlapJet, hoverlap]

theorem survivalFormFactor_eq_hilbertClock_overlap_normSq
    (mu : ProbabilityMeasure ℝ) (t : ℝ) :
    survivalFormFactor (mu : Measure ℝ) t =
      (Complex.normSq
        (inner ℂ
          ((probabilitySpectrumHilbertClock mu).state 0)
          ((probabilitySpectrumHilbertClock mu).state t)) : ℂ) := by
  rw [survivalFormFactor_eq_normSq]
  have hoverlap :
      charFun (mu : Measure ℝ) t =
        inner ℂ
          ((probabilitySpectrumHilbertClock mu).state 0)
          ((probabilitySpectrumHilbertClock mu).state t) := by
    simpa using ((probabilitySpectrumHilbertClock mu).overlap 0 t).symm
  exact congrArg (fun z : ℂ => (Complex.normSq z : ℂ)) hoverlap

/-- **Hilbert-clock complete-local-data no-go law.**  At every positive
log-energy variance, no predicate on the complete local transition-amplitude
jet can decide positive-plateau recurrence for all normalized cyclic
stationary Hilbert clocks with strictly positive spectra and all moments. -/
theorem no_universal_positiveEnergy_completeHilbertClockJet_recurrenceClassifier
    (v : NNReal) (hv : 0 < v) :
    ¬ ∃ classifier : (ℕ → ℂ) → Prop,
      ∀ mu : ProbabilityMeasure ℝ,
        HasStrictlyPositiveEnergy (mu : Measure ℝ) →
        HasAllEnergyMoments (mu : Measure ℝ) →
        (classifier (hilbertClockOverlapJet mu) ↔
          HasPersistentMeanRecurrence (mu : Measure ℝ)) := by
  rintro ⟨classifier, hclassifier⟩
  apply no_universal_positiveEnergy_completeJet_recurrenceClassifier v hv
  refine ⟨classifier, ?_⟩
  intro mu hpositive hall
  rw [← hilbertClockOverlapJet_eq_charFunJet mu]
  exact hclassifier mu hpositive hall

end RHTower
