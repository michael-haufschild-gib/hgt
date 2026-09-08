import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeFibres

/-!
# Exact late-prime amplitude windows for genuine two-step energy control

A late prime changes only the head; a middle prime also changes the full
transverse field. Their best global order has one exact scalar minimax
profile with the complete middle-prime energy gain as a parameter.
The sharp continuous optimum and ceiling window retain the unavoidable
first-step cost. The final theorem tests an actual unused late coefficient;
continuous feasibility alone does not assert source supply or a complete
prime order. No numerical observation enters these proofs.
-/

noncomputable section
open Finset
namespace RHTower

/-- Best internal two-step gain: one global first choice and the common endpoint. -/
def latePrimePairGain (f a G b : ℝ) : ℝ :=
  max (min (-2*f*b) G) (G-2*(f+a)*b)

/-- When the middle-first step exceeds the budget, both late-first constraints are necessary. -/
theorem latePrimePairGain_le_iff {f a G b H : ℝ} (hH : H < G) :
    latePrimePairGain f a G b ≤ H ↔ -2*f*b ≤ H ∧ G-2*(f+a)*b ≤ H := by
  simp only [latePrimePairGain, max_le_iff, min_le_iff]
  constructor
  · rintro ⟨h, he⟩
    rcases h with h | h
    · exact ⟨h, he⟩
    · exact (not_le_of_gt hH h).elim
  · rintro ⟨h, he⟩
    exact ⟨Or.inl h, he⟩

/-- Exact amplitude window for two genuine prefixes under a fixed ceiling. -/
theorem latePrimePairGain_le_iff_mem_interval {f a G b H : ℝ}
    (hf : f < 0) (hfa : 0 < f+a) (hH : H < G) :
    latePrimePairGain f a G b ≤ H ↔
      (G-H)/(2*(f+a)) ≤ b ∧ b ≤ H/(-2*f) := by
  rw [latePrimePairGain_le_iff hH,
    div_le_iff₀ (by positivity : 0 < 2*(f+a)),
    le_div_iff₀ (by nlinarith : 0 < -2*f)]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith only [h₁,h₂]

/-- Continuous feasibility is exactly a scalar budget inequality; it does not assert discrete supply. -/
theorem latePrimePair_interval_nonempty_iff {f a G H : ℝ}
    (hf : f < 0) (hfa : 0 < f+a) :
    (G-H)/(2*(f+a)) ≤ H/(-2*f) ↔ -f*G ≤ a*H := by
  rw [div_le_div_iff₀ (by positivity : 0 < 2*(f+a)) (by nlinarith : 0 < -2*f)]
  constructor <;> intro h <;> nlinarith only [h]

/-- The late-first gain and endpoint meet at the exact continuous optimum. -/
theorem latePrimePairGain_at_balance {f a t : ℝ}
    (hfa : 0 ≤ f+a) (ht : 0 ≤ t) :
    latePrimePairGain f a (2*a*t) t = -2*f*t := by
  have h : -2*f*t ≤ 2*a*t := by nlinarith [mul_nonneg hfa ht]
  unfold latePrimePairGain
  rw [min_eq_left h, show 2*a*t-2*(f+a)*t = -2*f*t by ring, max_self]

/-- Every amplitude pays at least the exact balance cost, including amplitudes absent from the source. -/
theorem latePrimePairGain_balance_lower {f a t b : ℝ}
    (hf : f ≤ 0) (hfa : 0 ≤ f+a) (ht : 0 ≤ t) :
    -2*f*t ≤ latePrimePairGain f a (2*a*t) b := by
  rcases le_total b t with hbt | htb
  · apply le_trans _ (le_max_right _ _)
    nlinarith [mul_nonneg hfa (sub_nonneg.mpr hbt)]
  · apply le_trans _ (le_max_left _ _)
    apply le_min
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hf (sub_nonneg.mpr htb)]
    · nlinarith [mul_nonneg hfa ht]

/-- In the strict adverse-head regime, the continuous optimum is unique. -/
theorem latePrimePairGain_eq_balance_iff {f a t b : ℝ}
    (hf : f < 0) (hfa : 0 < f+a) (ht : 0 < t) :
    latePrimePairGain f a (2*a*t) b = -2*f*t ↔ b = t := by
  constructor
  · intro he
    have hG : -2*f*t < 2*a*t := by nlinarith [mul_pos hfa ht]
    obtain ⟨h₁,h₂⟩ := (latePrimePairGain_le_iff hG).mp he.le
    apply le_antisymm
    · by_contra hn
      have hb := lt_of_not_ge hn
      nlinarith [mul_neg_of_neg_of_pos hf (sub_pos.mpr hb)]
    · by_contra hn
      have hb := lt_of_not_ge hn
      nlinarith [mul_pos hfa (sub_pos.mpr hb)]
  · rintro rfl
    exact latePrimePairGain_at_balance hfa.le ht.le

/-- Sharp continuous minimum and unique optimal amplitude, with all transverse costs retained in G. -/
theorem latePrimePairGain_optimal {f a G b : ℝ}
    (hf : f < 0) (hfa : 0 < f+a) (hG : 0 < G) :
    -f*G/a ≤ latePrimePairGain f a G b ∧
      (latePrimePairGain f a G b = -f*G/a ↔ b = G/(2*a)) := by
  have ha : 0 < a := by linarith
  have ht : 0 < G/(2*a) := div_pos hG (by positivity)
  have hg : 2*a*(G/(2*a)) = G := by field_simp
  have hv : -2*f*(G/(2*a)) = -f*G/a := by field_simp
  have hlo := latePrimePairGain_balance_lower (b := b) hf.le hfa.le ht.le
  have heq := latePrimePairGain_eq_balance_iff (b := b) hf hfa ht
  rw [hg,hv] at hlo heq
  exact ⟨hlo,heq⟩

/-- The signed actual energy gain from the best order of two primes. -/
def mobiusDivisorPairGain (M : ℕ) (P : Finset ℕ) (p q : ℕ) : ℝ :=
  max (min (mobiusDivisorSelectionEnergy M (insert p P))
    (mobiusDivisorSelectionEnergy M (insert q P)))
    (mobiusDivisorSelectionEnergy M (insert p (insert q P))) -
      mobiusDivisorSelectionEnergy M P

/-- Exact late/middle minimax formula for the complete actual source, with no transverse sign assumption. -/
theorem mobiusDivisorPairGain_late_eq {M p : ℕ} (hp : p.Prime)
    (hpM : p < M) (hM : M ≤ 2*p) (P : Finset ℕ) (hpP : p ∉ P)
    (q : ℕ) (hpq : p ≠ q) :
    mobiusDivisorPairGain M P p q = latePrimePairGain
      (mobiusDivisorSelectionFibre M P ∅) (mobiusDivisorSelectionFibre M P {q})
      (mobiusDivisorSelectionEnergy M (insert q P)-mobiusDivisorSelectionEnergy M P)
      (divisorUnsignedDilationChannel M p) := by
  have hpP' : p ∉ insert q P := by simp [hpq,hpP]
  have hc : mobiusDivisorDilationChannel M p = -divisorUnsignedDilationChannel M p := by
    rw [mobiusDivisorDilationChannel_eq_moebius_unsigned, ArithmeticFunction.moebius_apply_prime hp]
    push_cast
    ring
  have h₁ := mobiusDivisorSelectionEnergy_insert_late_prime hp hpM hM P hpP
  have h₂ := mobiusDivisorSelectionEnergy_insert_late_prime hp hpM hM (insert q P) hpP'
  rw [mobiusDivisorSelectionFibre_insert] at h₂
  simp only [notMem_empty,if_false,insert_empty_eq] at h₂
  rw [hc] at h₁ h₂
  have e₁ : mobiusDivisorSelectionEnergy M (insert p P) =
      mobiusDivisorSelectionEnergy M P +
        -2*mobiusDivisorSelectionFibre M P ∅*divisorUnsignedDilationChannel M p := by
    linarith only [h₁]
  have e₂ : mobiusDivisorSelectionEnergy M (insert q P) =
      mobiusDivisorSelectionEnergy M P +
        (mobiusDivisorSelectionEnergy M (insert q P)-mobiusDivisorSelectionEnergy M P) := by ring
  have e₃ : mobiusDivisorSelectionEnergy M (insert p (insert q P)) =
      mobiusDivisorSelectionEnergy M P +
        ((mobiusDivisorSelectionEnergy M (insert q P)-mobiusDivisorSelectionEnergy M P)-
          2*(mobiusDivisorSelectionFibre M P ∅+mobiusDivisorSelectionFibre M P {q})*
            divisorUnsignedDilationChannel M p) := by linarith only [h₂]
  unfold mobiusDivisorPairGain latePrimePairGain
  rw [e₃, e₁]
  conv_lhs => arg 1; arg 1; arg 2; rw [e₂]
  rw [min_add_add_left, max_add_add_left]
  ring

/-- Exact actual-source admissibility window under the current energy budget. -/
theorem mobiusDivisorPairGain_late_le_iff {M p : ℕ} (hp : p.Prime)
    (hpM : p < M) (hM : M ≤ 2*p) (P : Finset ℕ) (hpP : p ∉ P)
    (q : ℕ) (hpq : p ≠ q) (H : ℝ)
    (hf : mobiusDivisorSelectionFibre M P ∅ < 0)
    (hfa : 0 < mobiusDivisorSelectionFibre M P ∅+mobiusDivisorSelectionFibre M P {q})
    (hH : H < mobiusDivisorSelectionEnergy M (insert q P)-mobiusDivisorSelectionEnergy M P) :
    mobiusDivisorPairGain M P p q ≤ H ↔
      (mobiusDivisorSelectionEnergy M (insert q P)-mobiusDivisorSelectionEnergy M P-H)/
        (2*(mobiusDivisorSelectionFibre M P ∅+mobiusDivisorSelectionFibre M P {q})) ≤
          divisorUnsignedDilationChannel M p ∧
      divisorUnsignedDilationChannel M p ≤ H/(-2*mobiusDivisorSelectionFibre M P ∅) := by
  rw [mobiusDivisorPairGain_late_eq hp hpM hM P hpP q hpq]
  exact latePrimePairGain_le_iff_mem_interval hf hfa hH

end RHTower
