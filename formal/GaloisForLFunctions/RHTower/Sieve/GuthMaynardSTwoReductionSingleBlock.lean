import GaloisForLFunctions.RHTower.Sieve.GuthMaynardSTwoReductionAssembly

/-!
# Guth–Maynard (6.1) with a single dyadic block

Guth–Maynard state (6.1) as `S₂ ⪅ (N²/M) Σ_{t₁,t₂∈W} |Σ_{m∼M} a_m m^{i(t₁−t₂)}|²` "for some choice of
`M ⪅ T/N` and some coefficients `|a_m| ≤ 1`".  From the summed form `gmS2_le_sixOne` this follows
by taking the largest of its `≪ T^{2ε}` dyadic terms (`#classes ≤ (2/ε + 1) T^ε` by the corpus
`natLog_two_floor_le`, `#blocks per class ≤ (15 + 4/ε) T^ε`), or the block `M = 1`, `a₁ = 1`, whose
pair sum is `|W|²` and which carries the term `N²|W|²` (`gmS2_le_sixOne_single`).
-/

set_option autoImplicit false

open Complex Finset

noncomputable section

namespace RHTower.GuthMaynard

open Sieve

/-- The block `{1}`: its pair sum is `|W|²`. -/
theorem hbPairSum_dyadicSegmentBlock_one (W : Finset ℝ) :
    hbPairSum W (dyadicSegmentBlock 1 0) (fun _ => ((1 : ℝ) : ℂ)) = (W.card : ℝ) ^ 2 := by
  have hblock : dyadicSegmentBlock 1 0 = {1} := by
    decide
  rw [hblock]
  simp [hbPairSum, hbPoly, hbPhase, sq]

/-- The number of long classes is at most `(2/ε + 1) T^ε`. -/
theorem card_gmLongClasses_le {ε N T : ℝ} (hε : 0 < ε) (hT : 1 ≤ T) :
    ((gmLongClasses ε N T).card : ℝ) ≤ (2 / ε + 1) * T ^ ε := by
  have hT0 : 0 < T := by linarith
  have h1 : ((gmLongClasses ε N T).card : ℝ) ≤ gmClassCount T := by
    have : (gmLongClasses ε N T).card ≤ gmClassCount T := by
      unfold gmLongClasses
      exact (Finset.card_filter_le _ _).trans (Finset.card_range _).le
    exact_mod_cast this
  have h2 := Sieve.natLog_two_floor_le hT
  have h3 : Real.log T ≤ T ^ ε / ε := Real.log_le_rpow_div hT0.le hε
  have hTe : 1 ≤ T ^ ε := Real.one_le_rpow hT hε.le
  unfold gmClassCount at h1
  push_cast at h1
  have h4 : 2 * (T ^ ε / ε) = 2 / ε * T ^ ε := by ring
  nlinarith

/-- The index set of the summed (6.1): pairs `(k, j)` of a long class and one of its blocks. -/
def gmSixOneIndex (ε N T : ℝ) : Finset (Σ _ : ℕ, ℕ) :=
  (gmLongClasses ε N T).sigma fun k => Finset.range (Nat.log 2 (gmClassLength ε N k) + 1)

/-- The `(k, j)` term of the summed (6.1). -/
def gmSixOneTerm (ε N : ℝ) (W : Finset ℝ) (p : Σ _ : ℕ, ℕ) : ℝ :=
  N ^ 2 / 2 ^ p.2 * hbPairSum W (dyadicSegmentBlock (gmClassLength ε N p.1) p.2)
    (fun _ => ((1 : ℝ) : ℂ))

theorem gmSixOneSum_eq_sum_index (ε N T : ℝ) (W : Finset ℝ) :
    gmSixOneSum ε N T W = ∑ p ∈ gmSixOneIndex ε N T, gmSixOneTerm ε N W p := by
  rw [gmSixOneSum, gmSixOneIndex, Finset.sum_sigma]
  rfl

/-- At most `(2/ε + 1)(15 + 4/ε) T^{2ε}` dyadic terms. -/
theorem card_gmSixOneIndex_le {ε N T : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hN : 1 ≤ N)
    (hT : 1 ≤ T) :
    ((gmSixOneIndex ε N T).card : ℝ) ≤ (2 / ε + 1) * (15 + 4 / ε) * (T ^ ε) ^ 2 := by
  have hTe : 0 ≤ T ^ ε := Real.rpow_nonneg (by linarith) ε
  have hblocks : ∀ k ∈ gmLongClasses ε N T,
      ((Nat.log 2 (gmClassLength ε N k) + 1 : ℕ) : ℝ) ≤ (15 + 4 / ε) * T ^ ε := by
    intro k hk
    obtain ⟨hkK, _⟩ := Finset.mem_filter.mp hk
    have hk2 := two_pow_le_of_lt_count hT (Finset.mem_range.mp hkK)
    obtain ⟨hM1, hM8, _⟩ := gmClassLength_spec hε hε1 hN hT hk2
    exact log_count_le hε hT hM1 hM8
  rw [gmSixOneIndex, Finset.card_sigma]
  simp only [Finset.card_range]
  push_cast
  calc ∑ k ∈ gmLongClasses ε N T, ((Nat.log 2 (gmClassLength ε N k) : ℝ) + 1)
      ≤ ∑ _k ∈ gmLongClasses ε N T, (15 + 4 / ε) * T ^ ε :=
        Finset.sum_le_sum fun k hk => by exact_mod_cast hblocks k hk
    _ = ((gmLongClasses ε N T).card : ℝ) * ((15 + 4 / ε) * T ^ ε) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 / ε + 1) * T ^ ε) * ((15 + 4 / ε) * T ^ ε) :=
        mul_le_mul_of_nonneg_right (card_gmLongClasses_le hε hT) (by positivity)
    _ = (2 / ε + 1) * (15 + 4 / ε) * (T ^ ε) ^ 2 := by ring

/-- Every index of the summed (6.1) is a dyadic block `2^j ≤ M ≤ (2T)^{1+ε}/N + 1`. -/
theorem gmSixOneIndex_block_spec {ε N T : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hN : 1 ≤ N)
    (hT : 1 ≤ T) {p : Σ _ : ℕ, ℕ} (hp : p ∈ gmSixOneIndex ε N T) :
    1 ≤ gmClassLength ε N p.1 ∧ 2 ^ p.2 ≤ gmClassLength ε N p.1 ∧
      (gmClassLength ε N p.1 : ℝ) ≤ (2 * T) ^ (1 + ε) / N + 1 := by
  obtain ⟨hk, hj⟩ := Finset.mem_sigma.mp hp
  obtain ⟨hkK, _⟩ := Finset.mem_filter.mp hk
  have hk2 := two_pow_le_of_lt_count hT (Finset.mem_range.mp hkK)
  obtain ⟨hM1, _, _⟩ := gmClassLength_spec hε hε1 hN hT hk2
  have hN0 : 0 < N := by linarith
  refine ⟨hM1, ?_, ?_⟩
  · have hjl : p.2 ≤ Nat.log 2 (gmClassLength ε N p.1) :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact (Nat.pow_le_pow_right (by norm_num) hjl).trans (Nat.pow_log_le_self 2 (by omega))
  · have hx0 : 0 < ((2 : ℝ) ^ (p.1 + 1)) ^ (1 + ε) / N := by positivity
    have h1 := Nat.ceil_lt_add_one hx0.le
    have hle : (2 : ℝ) ^ (p.1 + 1) ≤ 2 * T := by rw [pow_succ]; linarith
    have h2 : ((2 : ℝ) ^ (p.1 + 1)) ^ (1 + ε) / N ≤ (2 * T) ^ (1 + ε) / N :=
      div_le_div_of_nonneg_right (Real.rpow_le_rpow (by positivity) hle (by linarith)) hN0.le
    unfold gmClassLength
    linarith

/-- **Guth–Maynard (6.1) for `ζ`, single-block form.**  For every `ε ∈ (0,1]` there is `C ≥ 0` such
that for all `T ≥ 1`, `N ≥ 1` and every `T^ε`-separated `W ⊂ [0,T]` there are `M ≥ 1` and a dyadic
block `j` (`2^j ≤ M ≤ (2T)^{1+ε}/N + 1`) with
`‖S₂‖ ≤ C (T^ε)^6 (N²/2^j) Σ_{t₁,t₂∈W} |Σ_{m ∈ [2^j, 2^{j+1}) ∩ [1,M]} m^{i(t₁−t₂)}|²`. -/
theorem gmS2_le_sixOne_single (w : CGLRealSmoothBump) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T N : ℝ) (W : Finset ℝ), 1 ≤ T → 1 ≤ N →
      IsSeparated (T ^ ε) W → (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) →
      ∃ M j : ℕ, 1 ≤ M ∧ 2 ^ j ≤ M ∧ (M : ℝ) ≤ (2 * T) ^ (1 + ε) / N + 1 ∧
        ‖gmS2 w N W‖ ≤ C * (T ^ ε) ^ 6 *
          (N ^ 2 / 2 ^ j * hbPairSum W (dyadicSegmentBlock M j) (fun _ => ((1 : ℝ) : ℂ))) := by
  obtain ⟨C, hC0, hC⟩ := gmS2_le_sixOne w hε hε1
  set c : ℝ := (2 / ε + 1) * (15 + 4 / ε) with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨C * (c + 1), by positivity, ?_⟩
  intro T N W hT hN hsep hW
  have hT0 : 0 < T := by linarith
  have hTe1 : 1 ≤ T ^ ε := Real.one_le_rpow hT hε.le
  have hbound := hC T N W hT hN hsep hW
  rw [gmSixOneSum_eq_sum_index] at hbound
  have hcard := card_gmSixOneIndex_le hε hε1 hN hT
  -- the block `M = 1` carries `N²|W|²`
  set b₀ : ℝ := N ^ 2 / 2 ^ 0 * hbPairSum W (dyadicSegmentBlock 1 0) (fun _ => ((1 : ℝ) : ℂ))
    with hb₀
  have hb₀eq : b₀ = N ^ 2 * (W.card : ℝ) ^ 2 := by
    rw [hb₀, hbPairSum_dyadicSegmentBlock_one, pow_zero, div_one]
  have h6 : (1 : ℝ) ≤ (T ^ ε) ^ 6 := one_le_pow₀ hTe1
  have hT4 : 0 ≤ (T ^ ε) ^ 4 := by positivity
  have hone : (1 : ℕ) ≤ 1 ∧ 2 ^ 0 ≤ 1 ∧ ((1 : ℕ) : ℝ) ≤ (2 * T) ^ (1 + ε) / N + 1 := by
    refine ⟨le_rfl, le_rfl, ?_⟩
    have : 0 ≤ (2 * T) ^ (1 + ε) / N := by positivity
    push_cast; linarith
  rcases (gmSixOneIndex ε N T).eq_empty_or_nonempty with hI | hI
  · -- no long class: only the block `M = 1`
    refine ⟨1, 0, hone.1, hone.2.1, hone.2.2, ?_⟩
    rw [hI, Finset.sum_empty, mul_zero, mul_zero, zero_add, ← hb₀eq] at hbound
    have hb0 : 0 ≤ b₀ := by rw [hb₀eq]; positivity
    have h1 : 1 ≤ (c + 1) * (T ^ ε) ^ 6 :=
      one_le_mul_of_one_le_of_one_le (by linarith) h6
    calc ‖gmS2 w N W‖ ≤ C * b₀ := hbound
      _ = C * 1 * b₀ := by ring
      _ ≤ C * ((c + 1) * (T ^ ε) ^ 6) * b₀ := by gcongr
      _ = C * (c + 1) * (T ^ ε) ^ 6 * b₀ := by ring
  · obtain ⟨p₀, hp₀, hmax⟩ := Finset.exists_max_image (gmSixOneIndex ε N T)
      (gmSixOneTerm ε N W) hI
    have hterm0 : 0 ≤ gmSixOneTerm ε N W p₀ :=
      mul_nonneg (by positivity) (hbPairSum_nonneg _ _ _)
    have hsum : ∑ p ∈ gmSixOneIndex ε N T, gmSixOneTerm ε N W p ≤
        c * (T ^ ε) ^ 2 * gmSixOneTerm ε N W p₀ := by
      calc ∑ p ∈ gmSixOneIndex ε N T, gmSixOneTerm ε N W p
          ≤ ((gmSixOneIndex ε N T).card : ℝ) * gmSixOneTerm ε N W p₀ := by
            have := Finset.sum_le_card_nsmul _ _ _ hmax
            simpa [nsmul_eq_mul] using this
        _ ≤ c * (T ^ ε) ^ 2 * gmSixOneTerm ε N W p₀ :=
            mul_le_mul_of_nonneg_right hcard hterm0
    have hmain : ‖gmS2 w N W‖ ≤ C * c * (T ^ ε) ^ 6 * gmSixOneTerm ε N W p₀ + C * b₀ := by
      rw [hb₀eq]
      calc ‖gmS2 w N W‖ ≤ C * ((T ^ ε) ^ 4 * ∑ p ∈ gmSixOneIndex ε N T, gmSixOneTerm ε N W p) +
            C * (N ^ 2 * (W.card : ℝ) ^ 2) := hbound
        _ ≤ C * ((T ^ ε) ^ 4 * (c * (T ^ ε) ^ 2 * gmSixOneTerm ε N W p₀)) +
            C * (N ^ 2 * (W.card : ℝ) ^ 2) := by gcongr
        _ = _ := by ring
    have hb0 : 0 ≤ b₀ := by rw [hb₀eq]; positivity
    rcases le_total b₀ (gmSixOneTerm ε N W p₀) with hle | hle
    · obtain ⟨hM1, hjM, hMT⟩ := gmSixOneIndex_block_spec hε hε1 hN hT hp₀
      refine ⟨gmClassLength ε N p₀.1, p₀.2, hM1, hjM, hMT, ?_⟩
      change ‖gmS2 w N W‖ ≤ C * (c + 1) * (T ^ ε) ^ 6 * gmSixOneTerm ε N W p₀
      have : C * b₀ ≤ C * (T ^ ε) ^ 6 * gmSixOneTerm ε N W p₀ := by
        have := mul_le_mul_of_nonneg_left hle hC0
        nlinarith [mul_nonneg hC0 hterm0]
      nlinarith
    · refine ⟨1, 0, hone.1, hone.2.1, hone.2.2, ?_⟩
      change ‖gmS2 w N W‖ ≤ C * (c + 1) * (T ^ ε) ^ 6 * b₀
      have : C * c * (T ^ ε) ^ 6 * gmSixOneTerm ε N W p₀ ≤ C * c * (T ^ ε) ^ 6 * b₀ :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      have : C * b₀ ≤ C * (T ^ ε) ^ 6 * b₀ := by nlinarith [mul_nonneg hC0 hb0]
      nlinarith

end RHTower.GuthMaynard
