import GaloisForLFunctions.HTGeometry.ConstitutiveTimeReversalLikelihoodCocycle

/-!
# Observer-fibre chirality conservation and sufficient reversal

Directed KL asymmetry is treated as a signed formation current.  Deterministic observation splits
that current into visible chirality and a vertical fibre current.  The current composes exactly
through observer chains.  A sufficient observer has zero vertical current; if its endpoint laws are
exchanged by an involution, any strictly ordered formation chronology selects equal endpoints.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory InformationTheory ProbabilityTheory

/-- Directed KL asymmetry of an ordered pair of finite-information laws. -/
noncomputable def klChirality {Ω : Type*} [MeasurableSpace Ω]
    (P R : Measure Ω) : ℝ :=
  (klDiv P R).toReal - (klDiv R P).toReal

theorem klChirality_swap {Ω : Type*} [MeasurableSpace Ω] (P R : Measure Ω) :
    klChirality R P = -klChirality P R := by
  simp [klChirality]

/-- Signed information current lost into the fibres of a deterministic observer. -/
noncomputable def observerFibreChirality {Ω Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y]
    (P R : Measure Ω) (q : Ω → Y) : ℝ :=
  klChirality P R - klChirality (P.map q) (R.map q)

/-- **Observer-current conservation.**  Source chirality is visible chirality plus fibre current. -/
theorem klChirality_observer_conservation {Ω Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y]
    (P R : Measure Ω) (q : Ω → Y) :
    klChirality P R = klChirality (P.map q) (R.map q) +
      observerFibreChirality P R q := by
  simp [observerFibreChirality]

/-- **Serial composition law.**  Fibre currents add exactly through an observer chain. -/
theorem observerFibreChirality_comp {Ω Y Z : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableSpace Z]
    (P R : Measure Ω) {q : Ω → Y} {r : Y → Z}
    (hq : Measurable q) (hr : Measurable r) :
    observerFibreChirality P R (r ∘ q) =
      observerFibreChirality P R q +
        observerFibreChirality (P.map q) (R.map q) r := by
  rw [observerFibreChirality, observerFibreChirality, observerFibreChirality,
    Measure.map_map hr hq, Measure.map_map hr hq]
  ring

/-- Forward conditional KL term in the exact disintegration chain rule. -/
noncomputable def conditionalForwardKL {Ω Y : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace Y] [MeasurableEq Y]
    (P R : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure R] (q : Ω → Y) : ENNReal :=
  klDiv ((jointLaw P q).fst ⊗ₘ (jointLaw P q).condKernel)
    ((jointLaw P q).fst ⊗ₘ (jointLaw R q).condKernel)

/-- The abstract current is exactly the difference of the two conditional KL losses. -/
theorem observerFibreChirality_eq_conditionalDifference
    {Ω Y : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace Y] [MeasurableEq Y]
    (P R : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure R]
    {q : Ω → Y} (hq : Measurable q)
    (hPmap : klDiv (P.map q) (R.map q) ≠ ⊤)
    (hPcond : conditionalForwardKL P R q ≠ ⊤)
    (hRmap : klDiv (R.map q) (P.map q) ≠ ⊤)
    (hRcond : conditionalForwardKL R P q ≠ ⊤) :
    observerFibreChirality P R q =
      (conditionalForwardKL P R q).toReal -
        (conditionalForwardKL R P q).toReal := by
  have hforward := klDiv_eq_map_add_cond P R hq
  have hreverse := klDiv_eq_map_add_cond R P hq
  have hPcond' :
      klDiv ((jointLaw P q).fst ⊗ₘ (jointLaw P q).condKernel)
        ((jointLaw P q).fst ⊗ₘ (jointLaw R q).condKernel) ≠ ⊤ := by
    simpa [conditionalForwardKL] using hPcond
  have hRcond' :
      klDiv ((jointLaw R q).fst ⊗ₘ (jointLaw R q).condKernel)
        ((jointLaw R q).fst ⊗ₘ (jointLaw P q).condKernel) ≠ ⊤ := by
    simpa [conditionalForwardKL] using hRcond
  rw [observerFibreChirality, klChirality, hforward, hreverse,
    ENNReal.toReal_add hPmap hPcond', ENNReal.toReal_add hRmap hRcond']
  simp only [conditionalForwardKL, klChirality]
  ring

/-- A measurable involution is a measurable embedding. -/
theorem measurableEmbedding_of_measurable_involution {Ω : Type*} [MeasurableSpace Ω]
    {θ : Ω → Ω} (hθ : Measurable θ) (hinv : ∀ x, θ (θ x) = x) :
    MeasurableEmbedding θ where
  injective := by
    intro x y hxy
    simpa [hinv] using congrArg θ hxy
  measurable := hθ
  measurableSet_image' := by
    intro s hs
    have himage : θ '' s = θ ⁻¹' s := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [hinv] using hy
      · intro hx
        exact ⟨θ x, hx, hinv x⟩
    rw [himage]
    exact hθ hs

/-- An involution exchanging two laws kills their directed KL asymmetry. -/
theorem klChirality_eq_zero_of_reversal {Ω : Type*} [MeasurableSpace Ω]
    (P R : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure R]
    {θ : Ω → Ω} (hθ : Measurable θ) (hinv : ∀ x, θ (θ x) = x)
    (hP : P.map θ = R) (hR : R.map θ = P) :
    klChirality P R = 0 := by
  have hkl := klDiv_map_measurableEmbedding
    (measurableEmbedding_of_measurable_involution hθ hinv) P R
  rw [hP, hR] at hkl
  simp [klChirality, hkl]

/-- A deterministic observer is pair-sufficient when it preserves both directed KL costs. -/
def IsKLPairSufficient {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (P R : Measure Ω) (q : Ω → Y) : Prop :=
  klDiv (P.map q) (R.map q) = klDiv P R ∧
    klDiv (R.map q) (P.map q) = klDiv R P

theorem observerFibreChirality_eq_zero_of_pairSufficient {Ω Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y]
    (P R : Measure Ω) (q : Ω → Y) (h : IsKLPairSufficient P R q) :
    observerFibreChirality P R q = 0 := by
  rcases h with ⟨hforward, hreverse⟩
  simp [observerFibreChirality, klChirality, hforward, hreverse]

/-- Sufficient observation transports observed reversal back to zero source chirality. -/
theorem klChirality_eq_zero_of_sufficient_reversal {Ω Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y]
    (P R : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure R]
    {q : Ω → Y} (_hq : Measurable q) (hsuff : IsKLPairSufficient P R q)
    {θ : Y → Y} (hθ : Measurable θ) (hinv : ∀ y, θ (θ y) = y)
    (hP : (P.map q).map θ = R.map q) (hR : (R.map q).map θ = P.map q) :
    klChirality P R = 0 := by
  have hobs : klChirality (P.map q) (R.map q) = 0 :=
    klChirality_eq_zero_of_reversal (P.map q) (R.map q) hθ hinv hP hR
  have hcurrent := observerFibreChirality_eq_zero_of_pairSufficient P R q hsuff
  rw [klChirality_observer_conservation P R q, hobs, hcurrent, add_zero]

/-- A family whose KL chirality reconstructs its strict parameter order. -/
structure StrictKLChronology (I Ω : Type*) [LinearOrder I] [MeasurableSpace Ω] where
  law : I → Measure Ω
  finite : ∀ t, IsFiniteMeasure (law t)
  strict : ∀ s t, s < t ↔ 0 < klChirality (law s) (law t)

/-- Complete comparison datum: sufficient observation followed by an involutive endpoint swap. -/
structure SufficientReversalComparison {I Ω : Type*} [LinearOrder I] [MeasurableSpace Ω]
    (C : StrictKLChronology I Ω) (s t : I) (Y : Type*) [MeasurableSpace Y] where
  q : Ω → Y
  measurable_q : Measurable q
  sufficient : IsKLPairSufficient (C.law s) (C.law t) q
  reversal : Y → Y
  measurable_reversal : Measurable reversal
  reversal_involutive : ∀ y, reversal (reversal y) = y
  map_left : ((C.law s).map q).map reversal = (C.law t).map q
  map_right : ((C.law t).map q).map reversal = (C.law s).map q

/-- **Selection capstone.**  Sufficient involutive reversal selects equal formation parameters. -/
theorem sufficientReversalSelection {I Ω Y : Type*} [LinearOrder I]
    [MeasurableSpace Ω] [MeasurableSpace Y]
    (C : StrictKLChronology I Ω) (s t : I)
    (K : SufficientReversalComparison C s t Y) : s = t := by
  letI : IsFiniteMeasure (C.law s) := C.finite s
  letI : IsFiniteMeasure (C.law t) := C.finite t
  have hzero : klChirality (C.law s) (C.law t) = 0 :=
    klChirality_eq_zero_of_sufficient_reversal (C.law s) (C.law t)
      K.measurable_q K.sufficient K.measurable_reversal K.reversal_involutive
      K.map_left K.map_right
  rcases lt_trichotomy s t with hst | hst | hst
  · have hpos := (C.strict s t).mp hst
    linarith
  · exact hst
  · have hpos := (C.strict t s).mp hst
    rw [klChirality_swap, hzero, neg_zero] at hpos
    linarith

end GaloisForLFunctions.HTGeometry
