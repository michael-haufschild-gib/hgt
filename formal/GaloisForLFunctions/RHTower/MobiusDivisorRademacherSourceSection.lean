import GaloisForLFunctions.RHTower.MobiusDivisorBernoulliPrimeEnergy

/-!
# Literal prime-selection energy as a sign-section mean square

Every retained fibre is one Walsh coefficient of the source observed through
independent signs on unprocessed prime labels. This identity does not estimate
the exceptional completed all-plus section or prove RH.
-/

noncomputable section
open Finset
namespace RHTower

/-- Sign of a retained label at one Boolean sign assignment. -/
def retainedSign {α : Type*} [DecidableEq α] (R S : Finset α) : ℝ :=
  ∏ i ∈ S, if i ∈ R then -1 else 1

private theorem retainedSign_orthogonality {α : Type*} [DecidableEq α]
    (U R T : Finset α) (hR : R ⊆ U) (hT : T ⊆ U) :
    (∑ S ∈ U.powerset, retainedSign R S * retainedSign T S) =
      if R = T then (2 : ℝ) ^ U.card else 0 := by
  classical
  have hsum :
      (∑ S ∈ U.powerset, retainedSign R S * retainedSign T S) =
        ∏ i ∈ U, (1 +
          ((if i ∈ R then (-1 : ℝ) else 1) *
            (if i ∈ T then (-1 : ℝ) else 1))) := by
    rw [Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro S hS
    simp only [retainedSign, Finset.prod_mul_distrib]
  rw [hsum]
  by_cases h : R = T
  · subst T
    rw [if_pos rfl]
    have hterm (i : α) :
        1 + (if i ∈ R then (-1 : ℝ) else 1) *
          (if i ∈ R then (-1 : ℝ) else 1) = 2 := by
      by_cases hi : i ∈ R <;> norm_num [hi]
    simp_rw [hterm]
    simp
  · rw [if_neg h]
    have hdiff : ∃ i : α, ¬ (i ∈ R ↔ i ∈ T) := by
      by_contra hn
      apply h
      ext i
      by_contra hi
      exact hn ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hdiff
    have hiU : i ∈ U := by
      by_cases hiR : i ∈ R
      · exact hR hiR
      · have hiT : i ∈ T := by
          by_contra hiT
          exact hi (by simp [hiR, hiT])
        exact hT hiT
    apply Finset.prod_eq_zero hiU
    by_cases hiR : i ∈ R <;> by_cases hiT : i ∈ T <;> simp_all

private theorem retainedSign_parseval {α : Type*} [DecidableEq α]
    (U : Finset α) (F : Finset α → ℝ) :
    (∑ S ∈ U.powerset,
      (∑ R ∈ U.powerset, F R * retainedSign R S) ^ 2) =
      (2 : ℝ) ^ U.card * ∑ R ∈ U.powerset, F R ^ 2 := by
  classical
  have hexpand (S : Finset α) :
      (∑ R ∈ U.powerset, F R * retainedSign R S) ^ 2 =
        ∑ R ∈ U.powerset, ∑ T ∈ U.powerset,
          F R * F T * (retainedSign R S * retainedSign T S) := by
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro R hR
    apply Finset.sum_congr rfl
    intro T hT
    ring
  simp_rw [hexpand]
  have horth (R T : Finset α) (hR : R ∈ U.powerset) (hT : T ∈ U.powerset) :
      (∑ S ∈ U.powerset, retainedSign R S * retainedSign T S) =
        if R = T then (2 : ℝ) ^ U.card else 0 :=
    retainedSign_orthogonality U R T (Finset.mem_powerset.mp hR)
      (Finset.mem_powerset.mp hT)
  calc
    (∑ S ∈ U.powerset, ∑ R ∈ U.powerset, ∑ T ∈ U.powerset,
      F R * F T * (retainedSign R S * retainedSign T S)) =
      ∑ R ∈ U.powerset, ∑ T ∈ U.powerset, ∑ S ∈ U.powerset,
        F R * F T * (retainedSign R S * retainedSign T S) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro R hR
          rw [Finset.sum_comm]
    _ = ∑ R ∈ U.powerset, ∑ T ∈ U.powerset,
          F R * F T *
            (∑ S ∈ U.powerset, retainedSign R S * retainedSign T S) := by
          apply Finset.sum_congr rfl
          intro R hR
          apply Finset.sum_congr rfl
          intro T hT
          rw [Finset.mul_sum]
    _ = ∑ R ∈ U.powerset, F R ^ 2 * (2 : ℝ) ^ U.card := by
          apply Finset.sum_congr rfl
          intro R hR
          calc
            (∑ T ∈ U.powerset,
              F R * F T *
                (∑ S ∈ U.powerset, retainedSign R S * retainedSign T S)) =
                ∑ T ∈ U.powerset,
                  if R = T then F R * F T * (2 : ℝ) ^ U.card else 0 := by
                    apply Finset.sum_congr rfl
                    intro T hT
                    rw [horth R T hR hT]
                    split_ifs <;> ring
            _ = F R ^ 2 * (2 : ℝ) ^ U.card := by simp [hR]; ring
    _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro R hR
          ring

/-- A finite source observed with independent signs on its unprocessed labels. -/
def retainedTwistedSource {α ι : Type*} [DecidableEq α]
    (I : Finset ι) (a : ι → Finset α) (c : ι → ℝ)
    (P S : Finset α) : ℝ :=
  ∑ i ∈ I, c i * retainedSign (a i \ P) S

theorem subsetLabelEnergy_eq_retainedSign_meanSq
    {α ι : Type*} [DecidableEq α]
    (U : Finset α) (I : Finset ι) (a : ι → Finset α)
    (c : ι → ℝ) (P : Finset α)
    (ha : ∀ i ∈ I, a i ⊆ U) :
    subsetLabelEnergy U I a c P =
      (∑ S ∈ U.powerset,
        (retainedTwistedSource I a c P S) ^ 2) /
        (2 : ℝ) ^ U.card := by
  classical
  have hrepr (S : Finset α) :
      retainedTwistedSource I a c P S =
        ∑ R ∈ U.powerset,
          subsetLabelFibre I a c P R * retainedSign R S := by
    unfold retainedTwistedSource subsetLabelFibre
    calc
      (∑ i ∈ I, c i * retainedSign (a i \ P) S) =
        ∑ i ∈ I, ∑ R ∈ U.powerset,
          (if a i \ P = R then c i else 0) * retainedSign R S := by
          apply Finset.sum_congr rfl
          intro i hi
          have hmem : a i \ P ∈ U.powerset :=
            Finset.mem_powerset.mpr ((Finset.sdiff_subset).trans (ha i hi))
          simp [hmem]
      _ = ∑ R ∈ U.powerset, ∑ i ∈ I,
            (if a i \ P = R then c i else 0) * retainedSign R S :=
          Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl
          intro R hR
          rw [Finset.sum_mul]
  unfold subsetLabelEnergy
  simp_rw [hrepr]
  rw [retainedSign_parseval]
  have htwo : (2 : ℝ) ^ U.card ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- The literal Möbius--divisor source on one retained-prime sign section. -/
def mobiusDivisorSignSection (M : ℕ) (P S : Finset ℕ) : ℝ :=
  retainedTwistedSource (mobiusDivisorSelectionIndices M)
    Nat.primeFactors (mobiusDivisorDilationChannel M) P S

theorem mobiusDivisorSelectionEnergy_eq_signSection_meanSq (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorSelectionEnergy M P =
      (∑ S ∈ (mobiusDivisorSelectionPrimes M).powerset,
        (mobiusDivisorSignSection M P S) ^ 2) /
        (2 : ℝ) ^ (mobiusDivisorSelectionPrimes M).card := by
  have hlabels : ∀ d ∈ mobiusDivisorSelectionIndices M,
      d.primeFactors ⊆ mobiusDivisorSelectionPrimes M := by
    intro d hd p hp
    obtain ⟨hd, hds⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd1, hdM⟩ := Finset.mem_Icc.mp hd
    have hpd := Nat.le_of_mem_primeFactors hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), (Nat.mem_primeFactors.mp hp).1⟩
  simpa only [mobiusDivisorSelectionEnergy, mobiusDivisorSignSection] using
    (subsetLabelEnergy_eq_retainedSign_meanSq
      (mobiusDivisorSelectionPrimes M) (mobiusDivisorSelectionIndices M)
      Nat.primeFactors (mobiusDivisorDilationChannel M) P hlabels)

end RHTower
