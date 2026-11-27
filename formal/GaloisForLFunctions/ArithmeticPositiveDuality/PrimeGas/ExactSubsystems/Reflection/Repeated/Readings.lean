import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Powers

/-! # Power sums of repeated observations with a common thermal bath -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated

open Finset _root_.HTGeometry

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- Independent joint measurement of the ordered copies and one thermal spectator. -/
def observed (P : X → ℝ) (k : ℕ) (B : Z → ℝ) (b : ℝ) (z : (Fin k → X) × Z) :=
  copyWeight P k z.1 * finiteGibbsStateWeight b B z.2

theorem observed_moment (P : X → ℝ) (k j : ℕ) (B : Z → ℝ) (b : ℝ) :
    moment (observed P k B b) j = (moment P j)^k * moment (finiteGibbsStateWeight b B) j := by
  rw [← moment_copies]
  unfold moment
  rw [Fintype.sum_prod_type,sum_mul]
  simp only [observed,mul_pow,mul_sum]

private theorem moment_nonneg {P : X → ℝ} (hp : ∀ x, 0 ≤ P x) (j : ℕ) : 0 ≤ moment P j :=
  sum_nonneg fun x _ => pow_nonneg (hp x) _

theorem moment_pos [Nonempty X] {P : X → ℝ} (hp : ∀ x, 0 < P x) (j : ℕ) : 0 < moment P j :=
  sum_pos (fun x _ => pow_pos (hp x) _) univ_nonempty

/-- Each moment order survives positive replication and a nonempty Gibbs bath individually. -/
theorem observed_eq_iff {P : X → ℝ} {Q : Y → ℝ} (hp : ∀ x, 0 ≤ P x) (hq : ∀ y, 0 ≤ Q y)
    (k j : ℕ) (B : Z → ℝ) (b : ℝ) :
    moment (observed P k B b) j = moment (observed Q k B b) j ↔
      k=0 ∨ IsEmpty Z ∨ moment P j = moment Q j := by
  rw [observed_moment,observed_moment]
  rcases isEmpty_or_nonempty Z with he | hn
  · letI := he
    simp only [moment,univ_eq_empty,sum_empty,mul_zero,he,true_or,or_true]
  · letI := hn
    have bath := moment_pos (finiteGibbsStateWeight_pos b B) j
    rw [(mul_left_injective₀ bath.ne').eq_iff,or_iff_right (not_isEmpty_of_nonempty Z)]
    by_cases hk : k=0
    · simp only [hk,pow_zero,true_or]
    · rw [or_iff_right hk,pow_left_inj₀ (moment_nonneg hp j) (moment_nonneg hq j) hk]

theorem observed_matches_iff {P : X → ℝ} {Q : Y → ℝ} (hp : ∀ x, 0 ≤ P x) (hq : ∀ y, 0 ≤ Q y)
    (k : ℕ) (B : Z → ℝ) (b : ℝ) :
    Matches (observed P k B b) (observed Q k B b) ↔ k=0 ∨ IsEmpty Z ∨ Matches P Q := by
  constructor
  · intro h
    by_cases hk : k=0
    · exact Or.inl hk
    by_cases hz : IsEmpty Z
    · exact Or.inr (Or.inl hz)
    refine Or.inr (Or.inr ((matches_iff_moments _ _).mpr fun j _ => ?_))
    exact (((observed_eq_iff hp hq k j B b).mp (moment_congr h j)).resolve_left hk).resolve_left hz
  · intro h
    apply (matches_iff_moments _ _).mpr
    intro j _
    exact (observed_eq_iff hp hq k j B b).mpr (h.imp_right (Or.imp_right (fun hm => moment_congr hm j)))

/-- Subtracting log moments cancels the bath exactly and multiplies the one-copy contrast
by the number of copies. -/
theorem observed_log_contrast [Nonempty X] [Nonempty Y] [Nonempty Z] {P : X → ℝ} {Q : Y → ℝ}
    (hp : ∀ x, 0 < P x) (hq : ∀ y, 0 < Q y) (k j : ℕ) (B : Z → ℝ) (b : ℝ) :
    Real.log (moment (observed P k B b) j) - Real.log (moment (observed Q k B b) j) =
      (k : ℝ) * (Real.log (moment P j) - Real.log (moment Q j)) := by
  have hz := (moment_pos (finiteGibbsStateWeight_pos b B) j).ne'
  rw [observed_moment,observed_moment,Real.log_mul (pow_pos (moment_pos hp j) k).ne' hz,
    Real.log_mul (pow_pos (moment_pos hq j) k).ne' hz,Real.log_pow,Real.log_pow]
  ring

#print axioms observed_moment
#print axioms observed_eq_iff
#print axioms observed_matches_iff
#print axioms observed_log_contrast

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated
