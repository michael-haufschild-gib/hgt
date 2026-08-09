import GaloisForLFunctions.HTGeometry.ConstitutiveAdaptiveProcompletion

/-!
# Adaptive transcript cost and experimental coercivity

The canonical effective support attached to a finite adaptive run is not merely one mimic.  It is
contained in every exact transcript mimic and therefore minimizes every nonnegative additive
coordinate cost.  Canonical prefix experiments against the coherent all-true boundary profile
force exact support size `N`; exhaustive experiments consequently escape every bounded effective
support budget.
-/

namespace GaloisForLFunctions.HTGeometry

open ConstitutiveAdaptiveExperiment

universe u

/-- Exact transcript mimicry: agreement at every coordinate encountered on the virtual run. -/
def ConstitutiveTranscriptMimic {Result : Type u}
    (T : ConstitutiveAdaptiveExperiment Result) (b : ConstitutiveBooleanProfile)
    (F : Finset ℕ) : Prop :=
  ∀ n ∈ queryTrace T b, finiteLawProfile F n = b n

/-- The canonical adaptive support realizes the complete selected transcript. -/
theorem mimickingSupport_isTranscriptMimic {Result : Type u}
    (T : ConstitutiveAdaptiveExperiment Result) (b : ConstitutiveBooleanProfile) :
    ConstitutiveTranscriptMimic T b (mimickingSupport T b) := by
  intro n hn
  exact finiteLawProfile_mimickingSupport_eq T b n hn

/-- Every exact transcript mimic contains the canonical mimicking support. -/
theorem mimickingSupport_subset_of_transcriptMimic {Result : Type u}
    (T : ConstitutiveAdaptiveExperiment Result) (b : ConstitutiveBooleanProfile)
    (F : Finset ℕ) (hF : ConstitutiveTranscriptMimic T b F) :
    mimickingSupport T b ⊆ F := by
  intro n hn
  have hnTrace : n ∈ queryTrace T b := (Finset.mem_filter.mp hn).1
  have hnTrue : b n = true := (Finset.mem_filter.mp hn).2
  have hprofile : finiteLawProfile F n = true := (hF n hnTrace).trans hnTrue
  exact (finiteLawProfile_eq_true_iff F n).1 hprofile

/-- Nonnegative additive cost of a finite effective law. -/
def finiteLawCost (weight : ℕ → ℕ) (F : Finset ℕ) : ℕ :=
  F.sum weight

/-- The canonical mimicking support minimizes every nonnegative additive coordinate cost. -/
theorem mimickingSupport_cost_minimal {Result : Type u}
    (weight : ℕ → ℕ) (T : ConstitutiveAdaptiveExperiment Result)
    (b : ConstitutiveBooleanProfile) (F : Finset ℕ)
    (hF : ConstitutiveTranscriptMimic T b F) :
    finiteLawCost weight (mimickingSupport T b) ≤ finiteLawCost weight F := by
  unfold finiteLawCost
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (mimickingSupport_subset_of_transcriptMimic T b F hF)
    (fun _ _ _ ↦ Nat.zero_le _)

/-- Prefix experiment querying `N - 1, ..., 0` along its all-true branch. -/
def constitutiveAllTruePrefixExperiment : ℕ → ConstitutiveAdaptiveExperiment Unit
  | 0 => .outcome ()
  | n + 1 => .query n (.outcome ()) (constitutiveAllTruePrefixExperiment n)

/-- The selected coordinate trace of the prefix experiment is exactly `range N`. -/
theorem queryTrace_allTruePrefixExperiment (N : ℕ) :
    queryTrace (constitutiveAllTruePrefixExperiment N) constitutiveAllTrueProfile =
      Finset.range N := by
  induction N with
  | zero => simp [constitutiveAllTruePrefixExperiment, queryTrace]
  | succ n ih =>
      simp [constitutiveAllTruePrefixExperiment, queryTrace, constitutiveAllTrueProfile,
        ih, Finset.range_add_one]

/-- Against the all-true profile, the canonical prefix mimic is exactly `range N`. -/
theorem mimickingSupport_allTruePrefixExperiment (N : ℕ) :
    mimickingSupport (constitutiveAllTruePrefixExperiment N) constitutiveAllTrueProfile =
      Finset.range N := by
  simp [mimickingSupport, queryTrace_allTruePrefixExperiment, constitutiveAllTrueProfile]

/-- Exact cardinal coercivity: the canonical prefix mimic has size `N`, and every transcript
mimic has at least `N` coordinates. -/
theorem allTruePrefix_exact_minimumCard (N : ℕ) :
    (mimickingSupport (constitutiveAllTruePrefixExperiment N)
        constitutiveAllTrueProfile).card = N ∧
      ∀ F : Finset ℕ,
        ConstitutiveTranscriptMimic (constitutiveAllTruePrefixExperiment N)
            constitutiveAllTrueProfile F →
          N ≤ F.card := by
  constructor
  · simp [mimickingSupport_allTruePrefixExperiment]
  · intro F hF
    have hsubset := mimickingSupport_subset_of_transcriptMimic
      (constitutiveAllTruePrefixExperiment N) constitutiveAllTrueProfile F hF
    have hcard := Finset.card_le_card hsubset
    simpa [mimickingSupport_allTruePrefixExperiment] using hcard

/-- Exact weighted coercivity: the prefix sum is achieved by the canonical mimic and lower-bounds
every other exact transcript realization. -/
theorem allTruePrefix_exact_minimumCost (weight : ℕ → ℕ) (N : ℕ) :
    finiteLawCost weight
        (mimickingSupport (constitutiveAllTruePrefixExperiment N)
          constitutiveAllTrueProfile) =
        (Finset.range N).sum weight ∧
      ∀ F : Finset ℕ,
        ConstitutiveTranscriptMimic (constitutiveAllTruePrefixExperiment N)
            constitutiveAllTrueProfile F →
          (Finset.range N).sum weight ≤ finiteLawCost weight F := by
  constructor
  · simp [finiteLawCost, mimickingSupport_allTruePrefixExperiment]
  · intro F hF
    have hmin := mimickingSupport_cost_minimal weight
      (constitutiveAllTruePrefixExperiment N) constitutiveAllTrueProfile F hF
    simpa [finiteLawCost, mimickingSupport_allTruePrefixExperiment] using hmin

/-- A coordinate cost whose exact prefix costs escape every natural budget. -/
structure ConstitutiveCoerciveWeight where
  weight : ℕ → ℕ
  prefix_unbounded : ∀ budget : ℕ, ∃ N : ℕ, budget < (Finset.range N).sum weight

/-- Every coercive coordinate cost forces all effective realizations of sufficiently exhaustive
all-true transcripts beyond any prescribed action budget. -/
theorem coerciveWeight_forces_unbounded_allTrueMimicCost
    (W : ConstitutiveCoerciveWeight) :
    ∀ budget : ℕ, ∃ N : ℕ, ∀ F : Finset ℕ,
      ConstitutiveTranscriptMimic (constitutiveAllTruePrefixExperiment N)
          constitutiveAllTrueProfile F →
        budget < finiteLawCost W.weight F := by
  intro budget
  obtain ⟨N, hN⟩ := W.prefix_unbounded budget
  refine ⟨N, ?_⟩
  intro F hF
  exact hN.trans_le ((allTruePrefix_exact_minimumCost W.weight N).2 F hF)

/-- Exhaustive all-true experiments escape every bounded finite-support budget. -/
theorem allTruePrefix_unbounded_minimumCard :
    ∀ budget : ℕ, ∃ N : ℕ, ∀ F : Finset ℕ,
      ConstitutiveTranscriptMimic (constitutiveAllTruePrefixExperiment N)
          constitutiveAllTrueProfile F →
        budget < F.card := by
  intro budget
  refine ⟨budget + 1, ?_⟩
  intro F hF
  have hmin := (allTruePrefix_exact_minimumCard (budget + 1)).2 F hF
  omega

end GaloisForLFunctions.HTGeometry
