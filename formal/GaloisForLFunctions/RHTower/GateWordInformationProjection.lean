import GaloisForLFunctions.RHTower.CircuitPreparationActionEntropy
import GaloisForLFunctions.RHTower.GateWordComplexityLaws
import GaloisForLFunctions.RHTower.DiscreteMarkovRenewal

/-!
# Information projection onto a first-hit gate language

The geometric gate prior assigns to a word the weight of its uniform description, discounted by the
fugacity.  Conditioning it on a prefix-free first-hit language is an information projection: among
all laws supported on that language, the conditioned prior uniquely minimizes relative entropy
against the prior, and the minimal value is the surprisal of the first-hit mass.

Expanding the minimal divergence separates it into a mean synthesis length weighted by the
description cost of one letter and the entropy of the successful routes.  This is the exact
energy--multiplicity form of the first-hit free energy.
-/

open scoped ENNReal

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.RHTower

section GeneralProjection

variable {ι : Type*}

/-- A prior conditioned on an event. -/
noncomputable def conditionedWeight (π : ι → ℝ) (E : Set ι) : ι → ℝ :=
  fun i => Set.indicator E π i / ∑' j, Set.indicator E π j

theorem summable_indicator_of_summable {π : ι → ℝ} (hπ0 : ∀ i, 0 ≤ π i) (hπsum : Summable π)
    (E : Set ι) : Summable (Set.indicator E π) := by
  classical
  refine hπsum.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
  · by_cases hi : i ∈ E
    · rw [Set.indicator_of_mem hi]; exact hπ0 i
    · rw [Set.indicator_of_notMem hi]
  · by_cases hi : i ∈ E
    · rw [Set.indicator_of_mem hi]
    · rw [Set.indicator_of_notMem hi]; exact hπ0 i

theorem conditionedWeight_nonneg {π : ι → ℝ} (hπ0 : ∀ i, 0 ≤ π i) (E : Set ι) (i : ι) :
    0 ≤ conditionedWeight π E i := by
  classical
  have hind : ∀ j : ι, 0 ≤ Set.indicator E π j :=
    Set.indicator_nonneg (fun j _ => hπ0 j)
  exact div_nonneg (hind i) (tsum_nonneg hind)

theorem conditionedWeight_eq_zero (π : ι → ℝ) {E : Set ι} {i : ι} (hi : i ∉ E) :
    conditionedWeight π E i = 0 := by
  rw [conditionedWeight, Set.indicator_of_notMem hi, zero_div]

theorem conditionedWeight_pos {π : ι → ℝ} (hπpos : ∀ i, 0 < π i) {E : Set ι} {i : ι} (hi : i ∈ E)
    (hE : 0 < ∑' j, Set.indicator E π j) : 0 < conditionedWeight π E i := by
  rw [conditionedWeight, Set.indicator_of_mem hi]
  exact div_pos (hπpos i) hE

theorem summable_conditionedWeight {π : ι → ℝ} (hπ0 : ∀ i, 0 ≤ π i) (hπsum : Summable π)
    (E : Set ι) : Summable (conditionedWeight π E) :=
  (summable_indicator_of_summable hπ0 hπsum E).div_const _

theorem tsum_conditionedWeight {π : ι → ℝ} {E : Set ι} (hE : 0 < ∑' j, Set.indicator E π j) :
    (∑' i, conditionedWeight π E i) = 1 := by
  simp only [conditionedWeight]
  rw [tsum_div_const, div_self hE.ne']

/-- The conditioned prior has relative entropy exactly the surprisal of the conditioning event. -/
theorem discreteRelativeEntropy_conditionedWeight {π : ι → ℝ} (hπpos : ∀ i, 0 < π i)
    {E : Set ι} (hE : 0 < ∑' j, Set.indicator E π j) :
    discreteRelativeEntropy (conditionedWeight π E) π =
      -Real.log (∑' j, Set.indicator E π j) := by
  classical
  have hterm : ∀ i : ι, conditionedWeight π E i * Real.log (conditionedWeight π E i / π i) =
      conditionedWeight π E i * -Real.log (∑' j, Set.indicator E π j) := by
    intro i
    by_cases hi : i ∈ E
    · congr 1
      have hval : Set.indicator E π i / (∑' j, Set.indicator E π j) / π i =
          (∑' j, Set.indicator E π j)⁻¹ := by
        rw [Set.indicator_of_mem hi, div_div, mul_comm, ← div_div, div_self (hπpos i).ne',
          one_div]
      simp only [conditionedWeight]
      rw [hval, Real.log_inv]
    · rw [conditionedWeight_eq_zero π hi, zero_mul, zero_mul]
  rw [discreteRelativeEntropy, tsum_congr hterm, tsum_mul_right,
    tsum_conditionedWeight hE, one_mul]

/-- **Information projection.**  The surprisal of an event under a strictly positive prior is the
least relative entropy of a law supported on that event, and the conditioned prior attains it. -/
theorem isLeast_discreteRelativeEntropy {π : ι → ℝ} (hπpos : ∀ i, 0 < π i)
    (hπsum : Summable π) {E : Set ι} (hE : 0 < ∑' j, Set.indicator E π j) :
    IsLeast {d : ℝ | ∃ Q : ι → ℝ, (∀ i, 0 ≤ Q i) ∧ Summable Q ∧ (∑' i, Q i) = 1 ∧
        (∀ i, i ∉ E → Q i = 0) ∧ Summable (fun i => Q i * Real.log (Q i / π i)) ∧
        d = discreteRelativeEntropy Q π}
      (-Real.log (∑' j, Set.indicator E π j)) := by
  classical
  have hcond := discreteRelativeEntropy_conditionedWeight hπpos hE
  have hcondTerm : ∀ i : ι, conditionedWeight π E i * Real.log (conditionedWeight π E i / π i) =
      conditionedWeight π E i * -Real.log (∑' j, Set.indicator E π j) := by
    intro i
    by_cases hi : i ∈ E
    · congr 1
      have hval : Set.indicator E π i / (∑' j, Set.indicator E π j) / π i =
          (∑' j, Set.indicator E π j)⁻¹ := by
        rw [Set.indicator_of_mem hi, div_div, mul_comm, ← div_div, div_self (hπpos i).ne',
          one_div]
      simp only [conditionedWeight]
      rw [hval, Real.log_inv]
    · rw [conditionedWeight_eq_zero π hi, zero_mul, zero_mul]
  constructor
  · refine ⟨conditionedWeight π E, conditionedWeight_nonneg (fun i => (hπpos i).le) E,
      summable_conditionedWeight (fun i => (hπpos i).le) hπsum E,
      tsum_conditionedWeight hE,
      fun i hi => conditionedWeight_eq_zero π hi, ?_, hcond.symm⟩
    have hbase := (summable_conditionedWeight (fun i => (hπpos i).le) hπsum E).mul_right
      (-Real.log (∑' j, Set.indicator E π j))
    simpa only [hcondTerm] using hbase
  · rintro d ⟨Q, hQ0, hQsum, hQtot, hQsupp, hQD, rfl⟩
    have hsupp : Function.support Q ⊆ E := by
      intro i hi
      by_contra hiE
      exact hi (hQsupp i hiE)
    have hsuppD : Function.support (fun i => Q i * Real.log (Q i / π i)) ⊆ E := by
      intro i hi
      by_contra hiE
      exact hi (by simp only [hQsupp i hiE, zero_mul])
    have hEqterm : ∀ i : E,
        Q (i : ι) * Real.log (Q (i : ι) / conditionedWeight π E (i : ι)) =
          Q (i : ι) * Real.log (Q (i : ι) / π (i : ι)) +
            Q (i : ι) * Real.log (∑' j, Set.indicator E π j) := by
      intro i
      by_cases hQi : Q (i : ι) = 0
      · rw [hQi]; ring
      · have hQpos : 0 < Q (i : ι) := lt_of_le_of_ne (hQ0 _) (Ne.symm hQi)
        have hcpos := conditionedWeight_pos hπpos i.2 hE
        have hwe : π (i : ι) = conditionedWeight π E (i : ι) * ∑' j, Set.indicator E π j := by
          rw [conditionedWeight, Set.indicator_of_mem i.2, div_mul_cancel₀ _ hE.ne']
        rw [hwe, ← div_div, Real.log_div (ne_of_gt (div_pos hQpos hcpos)) hE.ne']
        ring
    have h1 : Summable fun i : E => Q (i : ι) * Real.log (Q (i : ι) / π (i : ι)) :=
      hQD.subtype (fun i => i ∈ E)
    have h2 : Summable fun i : E => Q (i : ι) * Real.log (∑' j, Set.indicator E π j) :=
      (hQsum.subtype (fun i => i ∈ E)).mul_right _
    have hsummableG : Summable fun i : E =>
        Q (i : ι) * Real.log (Q (i : ι) / conditionedWeight π E (i : ι)) :=
      (h1.add h2).congr fun i => (hEqterm i).symm
    have hgibbs : 0 ≤ ∑' i : E, Q (i : ι) *
        Real.log (Q (i : ι) / conditionedWeight π E (i : ι)) := by
      refine discreteRelativeEntropy_nonneg (fun i : E => Q (i : ι))
        (fun i : E => conditionedWeight π E (i : ι)) (fun i => hQ0 _)
        (fun i => conditionedWeight_pos hπpos i.2 hE) (hQsum.subtype _)
        ((summable_conditionedWeight (fun i => (hπpos i).le) hπsum E).subtype _) ?_ ?_ hsummableG
      · rw [tsum_subtype_eq_of_support_subset hsupp, hQtot]
      · refine (tsum_subtype_eq_of_support_subset ?_).trans
          (tsum_conditionedWeight hE)
        intro i hi
        by_contra hiE
        exact hi (conditionedWeight_eq_zero π hiE)
    have hcongr : (∑' i : E, Q (i : ι) *
          Real.log (Q (i : ι) / conditionedWeight π E (i : ι))) =
        ∑' i : E, (Q (i : ι) * Real.log (Q (i : ι) / π (i : ι)) +
          Q (i : ι) * Real.log (∑' j, Set.indicator E π j)) := tsum_congr hEqterm
    have hadd : (∑' i : E, (Q (i : ι) * Real.log (Q (i : ι) / π (i : ι)) +
          Q (i : ι) * Real.log (∑' j, Set.indicator E π j))) =
        (∑' i : E, Q (i : ι) * Real.log (Q (i : ι) / π (i : ι))) +
          ∑' i : E, Q (i : ι) * Real.log (∑' j, Set.indicator E π j) := h1.tsum_add h2
    have hconst : (∑' i : E, Q (i : ι) * Real.log (∑' j, Set.indicator E π j)) =
        Real.log (∑' j, Set.indicator E π j) := by
      rw [tsum_mul_right, tsum_subtype_eq_of_support_subset hsupp, hQtot, one_mul]
    have hsplit : (∑' i : E, Q (i : ι) * Real.log (Q (i : ι) / π (i : ι))) =
        (∑' i : E, Q (i : ι) * Real.log (Q (i : ι) / conditionedWeight π E (i : ι))) -
          Real.log (∑' j, Set.indicator E π j) := by
      rw [hcongr, hadd, hconst]
      ring
    rw [discreteRelativeEntropy, ← tsum_subtype_eq_of_support_subset hsuppD, hsplit]
    linarith

end GeneralProjection

section WordCounting

variable {Γ : Type*} [Fintype Γ]

/-- A length-indexed weight summed over all words is the weight summed against the number of words
of each length. -/
theorem tsum_list_length_apply (f : ℕ → ℝ≥0∞) :
    (∑' w : List Γ, f w.length) = ∑' n : ℕ, (Fintype.card Γ : ℝ≥0∞) ^ n * f n := by
  classical
  rw [tsum_list_regroup (fun w : List Γ => f w.length)]
  refine tsum_congr fun n => ?_
  letI : Fintype {l : List Γ // l.length = n} := inferInstanceAs (Fintype (List.Vector Γ n))
  have hval : ∀ l : {l : List Γ // l.length = n}, f (l : List Γ).length = f n := by
    rintro ⟨l, hl⟩
    rw [hl]
  have hcard : (Fintype.card {l : List Γ // l.length = n} : ℝ≥0∞) =
      (Fintype.card Γ : ℝ≥0∞) ^ n := by
    have := card_vector (α := Γ) n
    rw [show Fintype.card {l : List Γ // l.length = n} = Fintype.card Γ ^ n from this]
    push_cast
    rfl
  rw [tsum_congr hval, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]

end WordCounting

section GatePrior

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] [Nonempty Γ] {X : Type*}

/-- The geometric gate prior on synthesis words. -/
noncomputable def gatePrior (Γ : Type*) [Fintype Γ] (a : ℝ) (w : List Γ) : ℝ :=
  (1 - a) * (a / Fintype.card Γ) ^ w.length

/-- The extended-nonnegative form of the geometric gate prior. -/
noncomputable def gatePriorENN (Γ : Type*) [Fintype Γ] (a : ℝ) (w : List Γ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - a) * (ENNReal.ofReal a / (Fintype.card Γ : ℝ≥0∞)) ^ w.length

theorem gatePrior_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (w : List Γ) :
    0 < gatePrior Γ a w := by
  have hM : (0 : ℝ) < Fintype.card Γ := by exact_mod_cast Fintype.card_pos (α := Γ)
  exact mul_pos (by linarith) (pow_pos (div_pos ha0 hM) _)

theorem gatePrior_eq_toReal {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (w : List Γ) :
    gatePrior Γ a w = (gatePriorENN Γ a w).toReal := by
  rw [gatePriorENN, gatePrior, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_ofReal ha0, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - a)]

theorem gatePriorENN_ne_top {a : ℝ} (w : List Γ) : gatePriorENN Γ a w ≠ ⊤ := by
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ?_)
  exact ENNReal.div_ne_top ENNReal.ofReal_ne_top (by simp)

/-- The geometric gate prior has unit total mass. -/
theorem tsum_gatePriorENN {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (∑' w : List Γ, gatePriorENN Γ a w) = 1 := by
  have hMne : (Fintype.card Γ : ℝ≥0∞) ≠ 0 := by simp
  have hMtop : (Fintype.card Γ : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hstep : ∀ n : ℕ, (Fintype.card Γ : ℝ≥0∞) ^ n *
      (ENNReal.ofReal a / (Fintype.card Γ : ℝ≥0∞)) ^ n = (ENNReal.ofReal a) ^ n := by
    intro n
    rw [← mul_pow, ENNReal.mul_div_cancel hMne hMtop]
  have halt : ENNReal.ofReal a < 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha0 |>.mpr ha1
  have hsub : ENNReal.ofReal (1 - a) = 1 - ENNReal.ofReal a := by
    rw [ENNReal.ofReal_sub _ ha0, ENNReal.ofReal_one]
  simp only [gatePriorENN]
  rw [ENNReal.tsum_mul_left,
    tsum_list_length_apply (fun n => (ENNReal.ofReal a / (Fintype.card Γ : ℝ≥0∞)) ^ n),
    tsum_congr hstep, ENNReal.tsum_geometric, hsub]
  exact ENNReal.mul_inv_cancel (tsub_pos_of_lt halt).ne' (by simp)

theorem summable_gatePrior {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Summable (gatePrior Γ a) := by
  have h := ENNReal.summable_toReal (f := gatePriorENN Γ a)
    (by rw [tsum_gatePriorENN ha0 ha1]; exact ENNReal.one_ne_top)
  exact h.congr fun w => (gatePrior_eq_toReal ha0 ha1.le w).symm

theorem tsum_gatePrior {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (∑' w : List Γ, gatePrior Γ a w) = 1 := by
  rw [tsum_congr (fun w => gatePrior_eq_toReal (Γ := Γ) ha0 ha1.le w),
    ← ENNReal.tsum_toReal_eq (fun w => gatePriorENN_ne_top w), tsum_gatePriorENN ha0 ha1]
  simp

/-- The prior mass of the first-hit language is the discounted first-hit mass, tilted by the
normalization of the geometric prior. -/
theorem tsum_indicator_gatePrior (act : Γ → X → X) (χ : X) (A : Set X) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (∑' w : List Γ, Set.indicator {w : List Γ | FirstHitWord act χ A w} (gatePrior Γ a) w) =
      (1 - a) * firstHitMassReal act χ A a := by
  classical
  have haE : ENNReal.ofReal a ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ha1.le
  have hFtop : firstHitMass act χ A (ENNReal.ofReal a) ≠ ⊤ := firstHitMass_ne_top act χ A haE
  have hENN : (∑' w : List Γ, Set.indicator {w : List Γ | FirstHitWord act χ A w}
      (gatePriorENN Γ a) w) =
      ENNReal.ofReal (1 - a) * firstHitMass act χ A (ENNReal.ofReal a) := by
    have hterm : ∀ w : List Γ, Set.indicator {w : List Γ | FirstHitWord act χ A w}
        (gatePriorENN Γ a) w = ENNReal.ofReal (1 - a) *
          Set.indicator {w : List Γ | FirstHitWord act χ A w}
            (fun w => (ENNReal.ofReal a / (Fintype.card Γ : ℝ≥0∞)) ^ w.length) w := by
      intro w
      by_cases hw : FirstHitWord act χ A w
      · rw [Set.indicator_of_mem (show w ∈ {w : List Γ | FirstHitWord act χ A w} from hw),
          Set.indicator_of_mem (show w ∈ {w : List Γ | FirstHitWord act χ A w} from hw),
          gatePriorENN]
      · rw [Set.indicator_of_notMem (show w ∉ {w : List Γ | FirstHitWord act χ A w} from hw),
          Set.indicator_of_notMem (show w ∉ {w : List Γ | FirstHitWord act χ A w} from hw),
          mul_zero]
    rw [tsum_congr hterm, ENNReal.tsum_mul_left, firstHitMass]
  have hind : ∀ w : List Γ, Set.indicator {w : List Γ | FirstHitWord act χ A w}
      (gatePrior Γ a) w =
      (Set.indicator {w : List Γ | FirstHitWord act χ A w} (gatePriorENN Γ a) w).toReal := by
    intro w
    by_cases hw : FirstHitWord act χ A w
    · rw [Set.indicator_of_mem (show w ∈ {w : List Γ | FirstHitWord act χ A w} from hw),
        Set.indicator_of_mem (show w ∈ {w : List Γ | FirstHitWord act χ A w} from hw),
        gatePrior_eq_toReal ha0 ha1.le]
    · rw [Set.indicator_of_notMem (show w ∉ {w : List Γ | FirstHitWord act χ A w} from hw),
        Set.indicator_of_notMem (show w ∉ {w : List Γ | FirstHitWord act χ A w} from hw)]
      simp
  have hne : ∀ w : List Γ, Set.indicator {w : List Γ | FirstHitWord act χ A w}
      (gatePriorENN Γ a) w ≠ ⊤ := by
    intro w
    by_cases hw : FirstHitWord act χ A w
    · rw [Set.indicator_of_mem (show w ∈ {w : List Γ | FirstHitWord act χ A w} from hw)]
      exact gatePriorENN_ne_top w
    · rw [Set.indicator_of_notMem (show w ∉ {w : List Γ | FirstHitWord act χ A w} from hw)]
      simp
  rw [tsum_congr hind, ← ENNReal.tsum_toReal_eq hne, hENN, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - a), firstHitMassReal]

/-- **Loop-free synthesis divergence.**  Among all laws supported on the first-hit language, the
least relative entropy against the geometric gate prior is the surprisal of the tilted first-hit
mass, and the conditioned prior attains it. -/
theorem isLeast_gateSynthesisDivergence (act : Γ → X → X) (χ : X) (A : Set X) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hpos : 0 < firstHitMassReal act χ A a) :
    IsLeast {d : ℝ | ∃ Q : List Γ → ℝ, (∀ w, 0 ≤ Q w) ∧ Summable Q ∧ (∑' w, Q w) = 1 ∧
        (∀ w, ¬ FirstHitWord act χ A w → Q w = 0) ∧
        Summable (fun w => Q w * Real.log (Q w / gatePrior Γ a w)) ∧
        d = discreteRelativeEntropy Q (gatePrior Γ a)}
      (-Real.log ((1 - a) * firstHitMassReal act χ A a)) := by
  have hmass : (0 : ℝ) < ∑' w : List Γ,
      Set.indicator {w : List Γ | FirstHitWord act χ A w} (gatePrior Γ a) w := by
    rw [tsum_indicator_gatePrior act χ A ha0.le ha1]
    exact mul_pos (by linarith) hpos
  have h := isLeast_discreteRelativeEntropy (π := gatePrior Γ a)
    (fun w => gatePrior_pos ha0 ha1 w) (summable_gatePrior ha0.le ha1)
    (E := {w : List Γ | FirstHitWord act χ A w}) hmass
  rw [tsum_indicator_gatePrior act χ A ha0.le ha1] at h
  exact h

end GatePrior

section EnergyMultiplicity

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] [Nonempty Γ] {X : Type*}

/-- The conditioned gate prior on the first-hit language. -/
noncomputable def firstHitLaw (act : Γ → X → X) (χ : X) (A : Set X) (a : ℝ) : List Γ → ℝ :=
  conditionedWeight (gatePrior Γ a) {w : List Γ | FirstHitWord act χ A w}

/-- The mean synthesis length of a successful first-hit route. -/
noncomputable def meanSynthesisLength (act : Γ → X → X) (χ : X) (A : Set X) (a : ℝ) : ℝ :=
  ∑' w : List Γ, firstHitLaw act χ A a w * w.length

/-- The entropy of the successful first-hit routes. -/
noncomputable def routeEntropy (act : Γ → X → X) (χ : X) (A : Set X) (a : ℝ) : ℝ :=
  -∑' w : List Γ, firstHitLaw act χ A a w * Real.log (firstHitLaw act χ A a w)

theorem gatePrior_nonneg {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (w : List Γ) :
    0 ≤ gatePrior Γ a w := by
  have hM : (0 : ℝ) ≤ Fintype.card Γ := Nat.cast_nonneg _
  exact mul_nonneg (by linarith) (pow_nonneg (div_nonneg ha0 hM) _)

theorem firstHitLaw_nonneg (act : Γ → X → X) (χ : X) (A : Set X) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (w : List Γ) : 0 ≤ firstHitLaw act χ A a w :=
  conditionedWeight_nonneg (fun v => gatePrior_nonneg (Γ := Γ) ha0 ha1 v) _ w

theorem firstHitLaw_eq_zero (act : Γ → X → X) (χ : X) (A : Set X) (a : ℝ) {w : List Γ}
    (hw : ¬ FirstHitWord act χ A w) : firstHitLaw act χ A a w = 0 :=
  conditionedWeight_eq_zero _ (show w ∉ {w : List Γ | FirstHitWord act χ A w} from hw)

theorem firstHitLaw_of_mem (act : Γ → X → X) (χ : X) (A : Set X) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) {w : List Γ} (hw : FirstHitWord act χ A w) :
    firstHitLaw act χ A a w =
      (a / Fintype.card Γ) ^ w.length / firstHitMassReal act χ A a := by
  rw [firstHitLaw, conditionedWeight,
    Set.indicator_of_mem (show w ∈ {w : List Γ | FirstHitWord act χ A w} from hw),
    tsum_indicator_gatePrior act χ A ha0 ha1, gatePrior]
  exact mul_div_mul_left _ _ (sub_ne_zero_of_ne (ne_of_lt ha1).symm)

theorem firstHitLaw_le (act : Γ → X → X) (χ : X) (A : Set X) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (w : List Γ) :
    firstHitLaw act χ A a w ≤
      (a / Fintype.card Γ) ^ w.length / firstHitMassReal act χ A a := by
  have hM : (0 : ℝ) < Fintype.card Γ := by exact_mod_cast Fintype.card_pos (α := Γ)
  have hFnn : 0 ≤ firstHitMassReal act χ A a := ENNReal.toReal_nonneg
  by_cases hw : FirstHitWord act χ A w
  · exact le_of_eq (firstHitLaw_of_mem act χ A ha0 ha1 hw)
  · rw [firstHitLaw_eq_zero act χ A a hw]
    exact div_nonneg (pow_nonneg (div_nonneg ha0 hM.le) _) hFnn

/-- The length-weighted geometric prior is summable over all synthesis words. -/
theorem summable_length_mul_geometric {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Summable (fun w : List Γ => (w.length : ℝ) * (a / Fintype.card Γ) ^ w.length) := by
  have hM : (0 : ℝ) < Fintype.card Γ := by exact_mod_cast Fintype.card_pos (α := Γ)
  have hreal : Summable (fun n : ℕ => (n : ℝ) * a ^ n) := by
    have hnorm : ‖a‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg ha0]
      exact ha1
    have := summable_pow_mul_geometric_of_norm_lt_one (k := 1) (r := a) hnorm
    simpa using this
  have hnn : ∀ n : ℕ, 0 ≤ (n : ℝ) * a ^ n := fun n =>
    mul_nonneg (Nat.cast_nonneg n) (pow_nonneg ha0 n)
  have hcount : (∑' w : List Γ,
      ENNReal.ofReal ((w.length : ℝ) * (a / Fintype.card Γ) ^ w.length)) =
      ENNReal.ofReal (∑' n : ℕ, (n : ℝ) * a ^ n) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hnn hreal,
      tsum_list_length_apply (Γ := Γ)
        (fun n => ENNReal.ofReal ((n : ℝ) * (a / Fintype.card Γ) ^ n))]
    refine tsum_congr fun n => ?_
    have hcast : (Fintype.card Γ : ℝ≥0∞) ^ n = ENNReal.ofReal ((Fintype.card Γ : ℝ) ^ n) := by
      rw [ENNReal.ofReal_pow hM.le, ENNReal.ofReal_natCast]
    rw [hcast, ← ENNReal.ofReal_mul (pow_nonneg hM.le n)]
    congr 1
    rw [div_pow, mul_comm ((Fintype.card Γ : ℝ) ^ n) _, mul_assoc,
      div_mul_cancel₀ _ (pow_ne_zero n hM.ne')]
  have hne : (∑' w : List Γ,
      ENNReal.ofReal ((w.length : ℝ) * (a / Fintype.card Γ) ^ w.length)) ≠ ⊤ := by
    rw [hcount]
    exact ENNReal.ofReal_ne_top
  have h := ENNReal.summable_toReal hne
  refine h.congr fun w => ?_
  rw [ENNReal.toReal_ofReal
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg ha0 hM.le) _))]

theorem summable_firstHitLaw_length (act : Γ → X → X) (χ : X) (A : Set X) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Summable (fun w : List Γ => firstHitLaw act χ A a w * w.length) := by
  have hM : (0 : ℝ) < Fintype.card Γ := by exact_mod_cast Fintype.card_pos (α := Γ)
  have hFnn : 0 ≤ firstHitMassReal act χ A a := ENNReal.toReal_nonneg
  have hbase := (summable_length_mul_geometric (Γ := Γ) ha0 ha1).mul_left
    (firstHitMassReal act χ A a)⁻¹
  refine hbase.of_nonneg_of_le (fun w => ?_) (fun w => ?_)
  · exact mul_nonneg (firstHitLaw_nonneg act χ A ha0 ha1.le w) (Nat.cast_nonneg _)
  · have hle := firstHitLaw_le act χ A ha0 ha1 w
    calc firstHitLaw act χ A a w * (w.length : ℝ)
        ≤ ((a / Fintype.card Γ) ^ w.length / firstHitMassReal act χ A a) * (w.length : ℝ) :=
          mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)
      _ = (firstHitMassReal act χ A a)⁻¹ *
          ((w.length : ℝ) * (a / Fintype.card Γ) ^ w.length) := by
          rw [div_eq_mul_inv]
          ring

end EnergyMultiplicity

end GaloisForLFunctions.RHTower
