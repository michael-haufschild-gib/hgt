import GaloisForLFunctions.RHTower.GomesClarkSourceReweighting

/-!
# Calibration removes the unknown-anchor source ambiguity

The observation bank alone remembers a weighted source. Independent total-mass calibration
recovers both the original source and the anchor magnitude, except for sources concentrated
at zero, where every anchor has the same observations. Positivity upgrades a zero Stieltjes
bank to a single-value certificate. These are experimental reconstruction applications of
arXiv:2607.24901 to the corpus's Clark and Stieltjes kernels.
-/

noncomputable section
open MeasureTheory GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

namespace RHTower

/-- Each individual Stieltjes observation is nonnegative for every finite positive source. -/
theorem gomesStieltjesValue_nonneg (μ : FiniteMeasure HausdorffSourceSpace)
    (t : Set.Ioi (-1 : ℝ)) : 0 ≤ gomesHausdorffStieltjesRecord μ t := by
  apply integral_nonneg
  intro y
  exact div_nonneg y.property.1 (le_of_lt (gomesHausdorffStieltjes_denominator_pos t y))

/-- One zero Stieltjes value already certifies that the entire source is its invisible atom. -/
theorem gomesStieltjesValue_zero_iff_atom (μ : FiniteMeasure HausdorffSourceSpace)
    (t : Set.Ioi (-1 : ℝ)) :
    gomesHausdorffStieltjesRecord μ t = 0 ↔ μ = μ.mass • gomesHausdorffZeroAtom := by
  rw [← gomesHausdorffStieltjesRecord_zero_iff_atom]
  constructor
  · intro h
    have he : stieltjesKernel (t : ℝ) =ᵐ[(μ : Measure HausdorffSourceSpace)] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun y => div_nonneg y.property.1 (le_of_lt (gomesHausdorffStieltjes_denominator_pos t y)))
        (integrable_of_continuous _ (gomesHausdorffStieltjesTest t).continuous)).mp h
    funext s
    apply integral_eq_zero_of_ae
    filter_upwards [he] with y hy
    have hy0 : (y : ℝ) = 0 :=
      (div_eq_zero_iff.mp hy).resolve_right (ne_of_gt (gomesHausdorffStieltjes_denominator_pos t y))
    simp [stieltjesKernel, hy0]
  · intro h
    exact congrFun h t

/-- A source with any mass away from zero gives a strictly positive value at every parameter. -/
theorem gomesStieltjesValue_pos_iff (μ : FiniteMeasure HausdorffSourceSpace)
    (t : Set.Ioi (-1 : ℝ)) :
    0 < gomesHausdorffStieltjesRecord μ t ↔ μ ≠ μ.mass • gomesHausdorffZeroAtom := by
  constructor
  · intro h ha
    have hz := (gomesStieltjesValue_zero_iff_atom μ t).mpr ha
    linarith
  · intro h
    exact lt_of_le_of_ne (gomesStieltjesValue_nonneg μ t)
      (fun hz => h ((gomesStieltjesValue_zero_iff_atom μ t).mp hz.symm))

/-- Every anchor sees a zero-endpoint atom only through its total mass. -/
theorem gomesClarkAnchorRecord_zeroAtom (c : ℝ) (w : ℝ≥0) :
    gomesClarkAnchorRecord c (w • gomesHausdorffZeroAtom) = fun _ => (w : ℝ) := by
  funext t
  have h := gomesHausdorffZeroCompletion_report 0 w (gomesClarkAnchorTest c t)
  simpa [gomesClarkAnchorTest, gomesClarkAnchorRecord, gomesHausdorffZero, stieltjesKernel] using h

/-- Independent mass information repairs reconstruction even at the zero anchor. -/
theorem gomesClarkAnchor_mass_reconstruction (c : ℝ)
    (μ ν : FiniteMeasure HausdorffSourceSpace) :
    (gomesClarkAnchorRecord c μ = gomesClarkAnchorRecord c ν ∧ μ.mass = ν.mass) ↔ μ = ν := by
  constructor
  · rintro ⟨he, hm⟩
    rcases (gomesClarkAnchorRecord_classification c μ ν).mp he with h | ⟨_, h⟩
    · exact h
    · exact (gomesClarkFixedRecord_mass_reconstruction μ ν).mp ⟨h, hm⟩
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- Source and anchor are jointly reconstructed by a calibrated bank, with the exact degeneracy. -/
theorem gomesClarkAnchor_calibrated_classification (c d : ℝ)
    (μ ν : FiniteMeasure HausdorffSourceSpace) :
    (gomesClarkAnchorRecord c μ = gomesClarkAnchorRecord d ν ∧ μ.mass = ν.mass) ↔
      μ = ν ∧ (c = d ∨ c = -d ∨ μ = μ.mass • gomesHausdorffZeroAtom) := by
  have hnonzero : ∀ (a : {a : ℝ // a ≠ 0}) (b : ℝ)
      (ρ σ : FiniteMeasure HausdorffSourceSpace),
      (a : ℝ) ^ 2 ≠ b ^ 2 → gomesClarkAnchorRecord a ρ = gomesClarkAnchorRecord b σ →
      ρ.mass = σ.mass → ρ = σ ∧ ρ = ρ.mass • gomesHausdorffZeroAtom := by
    intro a b ρ σ hab he hm
    have hv := congrFun he (gomesClarkAnchorBaseParameter a)
    rw [gomesClarkAnchorRecord_base, gomesClarkAnchorRecord_mass_split, hm] at hv
    have hz : gomesHausdorffStieltjesRecord σ (gomesClarkAnchorBaseParameter a) = 0 := by
      have hp : (b ^ 2 - (a : ℝ) ^ 2) *
          gomesHausdorffStieltjesRecord σ (gomesClarkAnchorBaseParameter a) = 0 := by
        dsimp [gomesClarkAnchorBaseParameter] at hv ⊢
        linarith
      exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr (Ne.symm hab))
    have hs := (gomesStieltjesValue_zero_iff_atom σ (gomesClarkAnchorBaseParameter a)).mp hz
    have he' : gomesClarkAnchorRecord a ρ = gomesClarkAnchorRecord a σ := by
      calc
        gomesClarkAnchorRecord a ρ = gomesClarkAnchorRecord b σ := he
        _ = gomesClarkAnchorRecord a σ := by rw [hs, gomesClarkAnchorRecord_zeroAtom,
          gomesClarkAnchorRecord_zeroAtom]
    have hρσ := ((gomesClarkAnchorRecord_injective_iff a).mpr a.property) he'
    exact ⟨hρσ, by simpa only [hρσ] using hs⟩
  constructor
  · rintro ⟨he, hm⟩
    by_cases hsq : c ^ 2 = d ^ 2
    · have hs := sq_eq_sq_iff_eq_or_eq_neg.mp hsq
      have ha := (gomesClarkAnchorRecord_parameter_classification c d).mpr hs ν
      have hμν := (gomesClarkAnchor_mass_reconstruction c μ ν).mp ⟨he.trans ha.symm, hm⟩
      exact ⟨hμν, hs.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
    · by_cases hc : c = 0
      · have hd : d ≠ 0 := by intro hd; exact hsq (by rw [hc, hd])
        obtain ⟨hνμ, hν⟩ := hnonzero ⟨d, hd⟩ c ν μ (Ne.symm hsq) he.symm hm.symm
        exact ⟨hνμ.symm, Or.inr (Or.inr (by simpa only [hνμ] using hν))⟩
      · obtain ⟨hμν, hμ⟩ := hnonzero ⟨c, hc⟩ d μ ν hsq he hm
        exact ⟨hμν, Or.inr (Or.inr hμ)⟩
  · rintro ⟨rfl, hcd | hcd | hμ⟩
    · exact ⟨by rw [hcd], rfl⟩
    · exact ⟨by rw [hcd, gomesClarkAnchorRecord_neg], rfl⟩
    · refine ⟨?_, rfl⟩
      rw [hμ, gomesClarkAnchorRecord_zeroAtom, gomesClarkAnchorRecord_zeroAtom]

/-- Arbitrarily local calibrated observations have the same exact joint reconstruction law. -/
theorem gomesClarkAnchor_local_calibrated_classification (r : Set.Ioc (0 : ℝ) 1) (c d : ℝ)
    (μ ν : FiniteMeasure HausdorffSourceSpace) :
    (gomesClarkGerm r (gomesClarkAnchorRecord c μ) =
        gomesClarkGerm r (gomesClarkAnchorRecord d ν) ∧ μ.mass = ν.mass) ↔
      μ = ν ∧ (c = d ∨ c = -d ∨ μ = μ.mass • gomesHausdorffZeroAtom) := by
  rw [gomesClarkAnchorGerm_eq_iff_full, gomesClarkAnchor_calibrated_classification]

/-- For a fixed source, the sign ambiguity is exhaustive unless every point lies at zero. -/
theorem gomesClarkAnchor_singleSource_classification (c d : ℝ)
    (μ : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkAnchorRecord c μ = gomesClarkAnchorRecord d μ ↔
      c = d ∨ c = -d ∨ μ = μ.mass • gomesHausdorffZeroAtom := by
  simpa only [and_true, true_and] using gomesClarkAnchor_calibrated_classification c d μ μ

/-- A compensating reweighting preserves mass exactly for equal anchor magnitudes or zero atoms. -/
theorem gomesClarkReanchor_mass_classification (c d : {c : ℝ // c ≠ 0})
    (μ : FiniteMeasure HausdorffSourceSpace) :
    (gomesClarkReanchor c d μ).mass = μ.mass ↔
      (c : ℝ) = d ∨ (c : ℝ) = -(d : ℝ) ∨ μ = μ.mass • gomesHausdorffZeroAtom := by
  have he := (gomesClarkReanchor_observation c d μ).symm
  constructor
  · intro hm
    have h := (gomesClarkAnchor_calibrated_classification c d μ (gomesClarkReanchor c d μ)).mp
      ⟨he, hm.symm⟩
    exact h.2
  · intro h
    have hrec := (gomesClarkAnchor_singleSource_classification c d μ).mpr h
    have hsource := (gomesClarkReanchor_unique c d μ μ).mp hrec
    rw [← hsource]

/-- Mass-preserving compensation cannot change the source at all. -/
theorem gomesClarkReanchor_fixed_iff_mass (c d : {c : ℝ // c ≠ 0})
    (μ : FiniteMeasure HausdorffSourceSpace) :
    gomesClarkReanchor c d μ = μ ↔ (gomesClarkReanchor c d μ).mass = μ.mass := by
  constructor
  · intro h
    rw [h]
  · intro hm
    exact ((gomesClarkAnchor_calibrated_classification c d μ (gomesClarkReanchor c d μ)).mp
      ⟨(gomesClarkReanchor_observation c d μ).symm, hm.symm⟩).1.symm

/-- Changing only the anchor changes a single observation by an exact positive-kernel factor. -/
theorem gomesClarkAnchorValue_difference (c d : ℝ)
    (μ : FiniteMeasure HausdorffSourceSpace) (t : Set.Ioi (-1 : ℝ)) :
    gomesClarkAnchorRecord d μ t - gomesClarkAnchorRecord c μ t =
      (d ^ 2 - c ^ 2) * gomesHausdorffStieltjesRecord μ t := by
  rw [gomesClarkAnchorRecord_mass_split, gomesClarkAnchorRecord_mass_split]
  ring

/-- With the source fixed, a single observation detects the full anchor ambiguity. -/
theorem gomesClarkAnchor_singleValue_classification (c d : ℝ)
    (μ : FiniteMeasure HausdorffSourceSpace) (t : Set.Ioi (-1 : ℝ)) :
    gomesClarkAnchorRecord c μ t = gomesClarkAnchorRecord d μ t ↔
      c = d ∨ c = -d ∨ μ = μ.mass • gomesHausdorffZeroAtom := by
  constructor
  · intro he
    have hz : (d ^ 2 - c ^ 2) * gomesHausdorffStieltjesRecord μ t = 0 := by
      rw [← gomesClarkAnchorValue_difference, he, sub_self]
    rcases mul_eq_zero.mp hz with h | h
    · have hs := sq_eq_sq_iff_eq_or_eq_neg.mp (sub_eq_zero.mp h).symm
      exact hs.elim Or.inl (fun h => Or.inr (Or.inl h))
    · exact Or.inr (Or.inr ((gomesStieltjesValue_zero_iff_atom μ t).mp h))
  · intro h
    exact congrFun ((gomesClarkAnchor_singleSource_classification c d μ).mpr h) t

/-- For a fixed source, equality at one parameter forces equality of the entire anchor bank. -/
theorem gomesClarkAnchor_singleValue_eq_iff_bank (c d : ℝ)
    (μ : FiniteMeasure HausdorffSourceSpace) (t : Set.Ioi (-1 : ℝ)) :
    gomesClarkAnchorRecord c μ t = gomesClarkAnchorRecord d μ t ↔
      gomesClarkAnchorRecord c μ = gomesClarkAnchorRecord d μ := by
  rw [gomesClarkAnchor_singleValue_classification, gomesClarkAnchor_singleSource_classification]

/-- A single observation orders anchor magnitudes strictly unless the source is invisible at zero. -/
theorem gomesClarkAnchorValue_lt_iff (c d : ℝ)
    (μ : FiniteMeasure HausdorffSourceSpace) (t : Set.Ioi (-1 : ℝ)) :
    gomesClarkAnchorRecord c μ t < gomesClarkAnchorRecord d μ t ↔
      c ^ 2 < d ^ 2 ∧ μ ≠ μ.mass • gomesHausdorffZeroAtom := by
  rw [← sub_pos, gomesClarkAnchorValue_difference, mul_pos_iff]
  constructor
  · rintro (⟨hs, hr⟩ | ⟨_, hr⟩)
    · exact ⟨sub_pos.mp hs, (gomesStieltjesValue_pos_iff μ t).mp hr⟩
    · exact False.elim (not_lt_of_ge (gomesStieltjesValue_nonneg μ t) hr)
  · rintro ⟨hs, hμ⟩
    exact Or.inl ⟨sub_pos.mpr hs, (gomesStieltjesValue_pos_iff μ t).mpr hμ⟩

end RHTower
