import GaloisForLFunctions.HTGeometry.CurveCodebook

/-!
# Selection information of a deterministic encoder

A deterministic encoder into a countable alphabet has a genuine conditional word law: the point
mass at the encoded word.  Its integral over a measurable set of states is the joint mass of that
set and the word, so it really is the conditional law, and its entropy vanishes at every state.
Selection information — word entropy minus conditional entropy — is therefore the whole word
entropy.

Change of variables through the encoder turns the expected robust complexity into the expected word
length of the word law, so the exact gate-cost decomposition applies to the first-shortest-word
encoder of a continuum of requests.
-/

open scoped BigOperators Classical
open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section ChangeOfVariables

variable {X : Type*} [MeasurableSpace X]
variable {beta : Type*} [Countable beta] [MeasurableSpace beta] [MeasurableSingletonClass beta]

theorem measurable_of_countable_domain (g : beta → ℝ) : Measurable g := by
  intro s _
  exact (Set.to_countable (g ⁻¹' s)).measurableSet

/-- **Change of variables for a discrete deterministic encoder.**  The expectation of a function of
the encoded word is the word-law average of that function. -/
theorem integral_comp_encoder (mu : Measure X) [IsFiniteMeasure mu]
    (f : X → beta) (hf : Measurable f) (g : beta → ℝ)
    (hint : Integrable (fun x => g (f x)) mu) :
    ∫ x, g (f x) ∂mu = ∑' b, mu.real (f ⁻¹' {b}) * g b := by
  classical
  have hg : Measurable g := measurable_of_countable_domain g
  have hmapint : Integrable g (mu.map f) := by
    rw [integrable_map_measure hg.aestronglyMeasurable hf.aemeasurable]
    exact hint
  have hstep : ∫ x, g (f x) ∂mu = ∫ b, g b ∂(mu.map f) :=
    (integral_map hf.aemeasurable hg.aestronglyMeasurable).symm
  rw [hstep, integral_countable hmapint]
  refine tsum_congr fun b => ?_
  have hval : (mu.map f).real {b} = mu.real (f ⁻¹' {b}) := by
    unfold Measure.real
    rw [Measure.map_apply hf (measurableSet_singleton b)]
  rw [smul_eq_mul, hval]

end ChangeOfVariables

section DeterministicKernel

variable {X : Type*} {beta : Type*}

/-- The conditional word law of a deterministic encoder: a point mass at the encoded word. -/
def detKernel (f : X → beta) : X → beta → ℝ := fun x b => if f x = b then 1 else 0

theorem detKernel_nonneg (f : X → beta) (x : X) (b : beta) : 0 ≤ detKernel f x b := by
  unfold detKernel
  split_ifs <;> norm_num

theorem hasSum_detKernel (f : X → beta) (x : X) : HasSum (detKernel f x) 1 := by
  classical
  have hbase := hasSum_ite_eq (f x) (1 : ℝ)
  refine hbase.congr_fun fun b => ?_
  unfold detKernel
  by_cases hb : f x = b
  · rw [if_pos hb, if_pos hb.symm]
  · rw [if_neg hb, if_neg (fun h => hb h.symm)]

/-- **A deterministic encoder has zero conditional entropy at every state.** -/
theorem entropy_detKernel (f : X → beta) (x : X) : entropy (detKernel f x) = 0 := by
  classical
  unfold entropy
  have hterm : ∀ b : beta, -(detKernel f x b * Real.log (detKernel f x b)) = 0 := by
    intro b
    unfold detKernel
    by_cases hb : f x = b
    · rw [if_pos hb]; simp
    · rw [if_neg hb]; simp
  rw [tsum_congr hterm, tsum_zero]

end DeterministicKernel

section Conditioning

variable {X : Type*} [MeasurableSpace X]
variable {beta : Type*} [MeasurableSpace beta] [MeasurableSingletonClass beta]

/-- **The deterministic kernel is the genuine conditional law.**  Its integral over a measurable
set of states is the joint mass of that set and the word. -/
theorem setIntegral_detKernel (mu : Measure X) (f : X → beta) (hf : Measurable f)
    (b : beta) {A : Set X} (_hA : MeasurableSet A) :
    ∫ x in A, detKernel f x b ∂mu = mu.real (A ∩ f ⁻¹' {b}) := by
  classical
  have hind : (fun x => detKernel f x b) = Set.indicator (f ⁻¹' {b}) (fun _ => (1 : ℝ)) := by
    funext x
    unfold detKernel
    by_cases hx : f x = b
    · rw [if_pos hx, Set.indicator_of_mem (by simpa using hx)]
    · rw [if_neg hx, Set.indicator_of_notMem (by simpa using hx)]
  rw [hind, MeasureTheory.setIntegral_indicator (hf (measurableSet_singleton b))]
  simp [Measure.real]

end Conditioning

section SelectionInformation

variable {X : Type*} [MeasurableSpace X]
variable {beta : Type*}

/-- The word law of a deterministic encoder. -/
def encoderLaw (mu : Measure X) (f : X → beta) : beta → ℝ := fun b => mu.real (f ⁻¹' {b})

/-- Conditional entropy of the word given the state, for a given conditional word law. -/
def condEntropyEncoder (mu : Measure X) (p : X → beta → ℝ) : ℝ := ∫ x, entropy (p x) ∂mu

theorem condEntropyEncoder_detKernel (mu : Measure X) (f : X → beta) :
    condEntropyEncoder mu (detKernel f) = 0 := by
  unfold condEntropyEncoder
  simp [entropy_detKernel]

/-- **Selection information of a deterministic encoder**: the word entropy minus the conditional
entropy of the word given the state. -/
def selectionInfo (mu : Measure X) (f : X → beta) : ℝ :=
  entropy (encoderLaw mu f) - condEntropyEncoder mu (detKernel f)

/-- **A deterministic encoder carries all of its word entropy as selection information.** -/
theorem selectionInfo_eq_entropy (mu : Measure X) (f : X → beta) :
    selectionInfo mu f = entropy (encoderLaw mu f) := by
  unfold selectionInfo
  rw [condEntropyEncoder_detKernel, sub_zero]

end SelectionInformation

section TheoremB

variable {Γ : Type*} [Fintype Γ] [Encodable Γ]
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [MeasurableSpace (List Γ)] [MeasurableSingletonClass (List Γ)]

omit [Fintype Γ] in
/-- The expected robust complexity is the expected word length of the encoder law. -/
theorem integral_wordComplexity_eq_expectedLength (mu : Measure X) [IsProbabilityMeasure mu]
    (endpoint : List Γ → X) (eps : ℝ)
    (hint : Integrable (fun x => ((wordComplexity endpoint eps x : ℕ) : ℝ)) mu) :
    ∫ x, ((wordComplexity endpoint eps x : ℕ) : ℝ) ∂mu =
      expectedLength (encoderLaw mu (firstQualifying endpoint eps)) := by
  have hfun : (fun x => ((wordComplexity endpoint eps x : ℕ) : ℝ)) =
      fun x => (((firstQualifying endpoint eps x).length : ℕ) : ℝ) := by
    funext x
    rw [wordComplexity_eq_length_firstQualifying]
  rw [hfun] at hint ⊢
  rw [integral_comp_encoder mu (firstQualifying endpoint eps)
    (measurable_firstQualifying endpoint eps) (fun w : List Γ => ((w.length : ℕ) : ℝ)) hint]
  rfl

/-- **Theorem B `(10)`.**  For the first-shortest-word encoder the expected circuit complexity
splits exactly into selection information, synthesis divergence, and the killing constant. -/
theorem gateCost_firstQualifying (mu : Measure X) [IsProbabilityMeasure mu]
    (endpoint : List Γ → X) (eps : ℝ) {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hM : 0 < Fintype.card Γ)
    (hint : Integrable (fun x => ((wordComplexity endpoint eps x : ℕ) : ℝ)) mu)
    (hlen : Summable fun w : List Γ =>
      encoderLaw mu (firstQualifying endpoint eps) w * ((w.length : ℕ) : ℝ))
    (hent : Summable fun w : List Γ =>
      -(encoderLaw mu (firstQualifying endpoint eps) w *
        Real.log (encoderLaw mu (firstQualifying endpoint eps) w)))
    (hrel : Summable fun w : List Γ =>
      encoderLaw mu (firstQualifying endpoint eps) w *
        Real.log (encoderLaw mu (firstQualifying endpoint eps) w / wordPrior a w)) :
    Real.log ((Fintype.card Γ : ℝ) / a) * ∫ x, ((wordComplexity endpoint eps x : ℕ) : ℝ) ∂mu
      = selectionInfo mu (firstQualifying endpoint eps)
        + relEntropy (encoderLaw mu (firstQualifying endpoint eps)) (wordPrior a)
        + Real.log (1 - a) := by
  have hq : ∀ w : List Γ, 0 ≤ encoderLaw mu (firstQualifying endpoint eps) w :=
    fun w => measureReal_nonneg
  have hsum : HasSum (encoderLaw mu (firstQualifying endpoint eps)) 1 :=
    hasSum_encoderLaw mu (firstQualifying endpoint eps)
      (measurableSet_preimage_firstQualifying endpoint eps)
  have hgate := gateCost_eq_entropy_add_relEntropy (Γ := Γ) ha ha1 hM hq hsum hlen hent hrel
  rw [integral_wordComplexity_eq_expectedLength mu endpoint eps hint,
    selectionInfo_eq_entropy]
  linarith [hgate]

end TheoremB

end

end GaloisForLFunctions.HTGeometry
