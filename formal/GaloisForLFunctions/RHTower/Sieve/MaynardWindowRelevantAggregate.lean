import GaloisForLFunctions.RHTower.Sieve.MaynardPerronRelevantWindow

/-!
# Two-sided support relevance for the adjacent Perron window

An adjacent-prefix difference annihilates boxes on both sides: boxes beginning above the upper
cutoff and boxes ending below the lower window edge.  The existing Perron relevance predicate only
recorded the first condition.  Two-sided relevance forces every surviving degree-`k` box's lower
edge into the fixed interval `(N / 2^(2k), X]`, restoring scale comparability with the physical
prime window.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- A box meets both support sides of the adjacent physical window. -/
def IsHeathBrownBoxWindowRelevant
    (N : ℝ) (X k : ℕ) {L : ℕ} (box : HeathBrownBoxChoice L X k) : Prop :=
  IsHeathBrownBoxPerronRelevant X k box ∧
    N < (groupedDyadicUpper
      (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ)

/-- Eligible aggregate restricted to boxes meeting the physical window. -/
def heathBrownWindowRelevantEligibleDyadicAggregate
    (L X k : ℕ) (T0 t N : ℝ) (s : ℂ) : ℂ := by
  classical
  exact ∑ box : HeathBrownBoxChoice L X k,
    if IsHeathBrownBoxEligible L X k T0 t box ∧
        IsHeathBrownBoxWindowRelevant N X k box then
      heathBrownBoxTerm L X k box s
    else 0

theorem windowRelevant_heathBrownBox_coreLower_le
    {L X k : ℕ} {N : ℝ} {box : HeathBrownBoxChoice L X k}
    (hbox : IsHeathBrownBoxWindowRelevant N X k box) :
    (groupedDyadicLower
      (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ≤ X :=
  perronRelevant_heathBrownBox_coreLower_le hbox.1

theorem groupedDyadicUpper_heathBrownBoxFactorExponent_eq_coreUpper
    {k m : ℕ} (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ) (q : ℕ) :
    groupedDyadicUpper (heathBrownBoxFactorExponent a b q) =
      heathBrownDyadicCoreUpper (k - m) a b q := by
  simp [groupedDyadicUpper, heathBrownBoxFactorExponent, heathBrownDyadicCoreUpper,
    mul_assoc]

theorem card_heathBrownBoxFactorIndex_le_two_mul
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k) :
    Fintype.card (HeathBrownBoxFactorIndex k box.m) ≤ 2 * k := by
  change Fintype.card (HeathBrownBoxFactorIndex k (box.1 : ℕ)) ≤ 2 * k
  rw [card_heathBrownBoxFactorIndex box.1.isLt]
  omega

/-- **Physical scale sandwich, lower side.**  The `2k` dyadic widths are the entire loss. -/
theorem windowRelevant_heathBrownBox_coreLower_gt
    {L X k : ℕ} {N : ℝ} {box : HeathBrownBoxChoice L X k}
    (hbox : IsHeathBrownBoxWindowRelevant N X k box) :
    N / (2 ^ (2 * k) : ℝ) <
      (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) := by
  let q := heathBrownBoxFactorExponent box.a box.b box.q
  let A : ℝ := (groupedDyadicLower q : ℝ)
  let w : ℕ := Fintype.card (HeathBrownBoxFactorIndex k box.m)
  have hA : 0 ≤ A := by positivity
  have hw : w ≤ 2 * k := card_heathBrownBoxFactorIndex_le_two_mul box
  have hpowNat : 2 ^ w ≤ 2 ^ (2 * k) :=
    Nat.pow_le_pow_right (n := 2) (by omega) hw
  have hpow : (2 ^ w : ℝ) ≤ (2 ^ (2 * k) : ℝ) := by exact_mod_cast hpowNat
  have hupper : N < A * (2 ^ w : ℝ) := by
    rw [show A * (2 ^ w : ℝ) = (groupedDyadicUpper q : ℝ) by
      dsimp [A, w]
      norm_cast
      exact (groupedDyadicUpper_eq_lower_mul_twoPow q).symm]
    exact hbox.2
  have hwide : N < A * (2 ^ (2 * k) : ℝ) :=
    hupper.trans_le (mul_le_mul_of_nonneg_left hpow hA)
  exact (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ (2 * k))).2 (by
    simpa [mul_comm] using hwide)

/-- Large-value selector for the two-sided aggregate. -/
theorem exists_large_windowRelevant_eligible_heathBrownBox
    (L X k : ℕ) (hk : 0 < k) (T0 t N : ℝ) (s : ℂ) {V : ℝ}
    (hV : 0 < V)
    (hlarge : V ≤
      ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N s‖) :
    ∃ box : HeathBrownBoxChoice L X k,
      IsHeathBrownBoxEligible L X k T0 t box ∧
      IsHeathBrownBoxWindowRelevant N X k box ∧
      V ≤ (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
        ‖heathBrownBoxTerm L X k box s‖ := by
  classical
  letI : Nonempty (HeathBrownBoxChoice L X k) :=
    nonempty_heathBrownBoxChoice L X k hk
  let f : HeathBrownBoxChoice L X k → ℂ := fun box =>
    if IsHeathBrownBoxEligible L X k T0 t box ∧
        IsHeathBrownBoxWindowRelevant N X k box then
      heathBrownBoxTerm L X k box s
    else 0
  have hsum : heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N s =
      ∑ box ∈ (Finset.univ : Finset (HeathBrownBoxChoice L X k)), f box := by
    simp [heathBrownWindowRelevantEligibleDyadicAggregate, f]
  obtain ⟨box, _hbox, hbox⟩ := exists_mem_card_mul_norm_ge
    (Finset.univ : Finset (HeathBrownBoxChoice L X k)) Finset.univ_nonempty f
      (hlarge.trans_eq (congrArg norm hsum))
  have hboth : IsHeathBrownBoxEligible L X k T0 t box ∧
      IsHeathBrownBoxWindowRelevant N X k box := by
    by_contra hnot
    simp [f, hnot] at hbox
    linarith
  refine ⟨box, hboth.1, hboth.2, ?_⟩
  simpa [f, hboth] using hbox

end RHTower.Sieve
