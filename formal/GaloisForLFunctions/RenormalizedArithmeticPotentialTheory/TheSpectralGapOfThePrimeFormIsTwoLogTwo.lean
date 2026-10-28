import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheValuationChainOfFinitelyManyPrimesHasGapTwoLogTwo
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePrimeFormHasASpectralGapBelowItsPole

/-!
# The spectral gap of the prime form is `2 log 2`

(Work in progress: the two-scale decomposition of `[1, N]`.)
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-! ### 1. Smooth and rough parts -/

theorem smoothSet_zero (N : ℕ) : smoothSet 0 N = (Icc 1 N).filter (· = 1) := by
  ext a
  simp only [mem_smoothSet, mem_filter, mem_Icc, not_lt_zero']
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    by_contra hne
    obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd hne
    exact h3 p (Nat.mem_primeFactors.mpr ⟨hp, hpa, by omega⟩)
  · rintro ⟨⟨h1, h2⟩, rfl⟩
    exact ⟨h1, h2, by simp⟩

theorem smoothSet_succ_of_not_prime {Q : ℕ} (hQ : ¬ Q.Prime) (N : ℕ) :
    smoothSet (Q + 1) N = smoothSet Q N := by
  ext a
  simp only [mem_smoothSet]
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun h p hp => ?_,
    fun h p hp => (h p hp).trans (Nat.lt_succ_self Q)⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp (h p hp) with h' | h'
  · exact h'
  · exact absurd (h' ▸ Nat.prime_of_mem_primeFactors hp) hQ

theorem smoothSet_filter_not_dvd {Q : ℕ} (hQ : Q.Prime) (N : ℕ) :
    (smoothSet (Q + 1) N).filter (fun u => ¬ Q ∣ u) = smoothSet Q N := by
  ext a
  simp only [mem_filter, mem_smoothSet]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    refine ⟨h1, h2, fun p hp => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp (h3 p hp) with h' | h'
    · exact h'
    · exact absurd (h' ▸ (Nat.mem_primeFactors.mp hp).2.1) h4
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2, fun p hp => (h3 p hp).trans (Nat.lt_succ_self Q)⟩, fun hd => ?_⟩
    have := h3 Q (Nat.mem_primeFactors.mpr ⟨hQ, hd, by omega⟩)
    omega

/-- **Smooth and rough parts**: `[1, N] = ⊔_{a Q-smooth} a · R(Q, N/a)`. -/
theorem sum_Icc_eq_smooth_rough (Q N : ℕ) (φ : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, φ n = ∑ a ∈ smoothSet Q N, ∑ b ∈ roughInterval Q (N / a), φ (a * b) := by
  induction Q with
  | zero =>
    rw [smoothSet_zero, sum_filter]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    rw [← sum_filter, show (Icc 1 N).filter (· = 1) = {1} by
      ext a; simp only [mem_filter, mem_Icc, mem_singleton]; omega, sum_singleton, Nat.div_one,
      roughInterval_zero]
    simp
  | succ Q ih =>
    by_cases hQ : Q.Prime
    · rw [ih, sum_smoothSet_eq_ladders hQ (Nat.lt_succ_self Q)
        (fun a' => ∑ b ∈ roughInterval (Q + 1) (N / a'), φ (a' * b)),
        smoothSet_filter_not_dvd hQ]
      refine sum_congr rfl fun a ha => ?_
      have ha1 := (mem_smoothSet.mp ha).1
      rw [sum_roughInterval_eq_levels hQ, sum_filter]
      -- both sides run over the levels `j` with `a Q^j ≤ N`
      have hN : N / a ≤ N := Nat.div_le_self _ _
      rw [← sum_subset (range_subset_range.mpr (show N / a + 1 ≤ N + 1 by omega))
        (fun j _ hj => ?_)]
      · refine sum_congr rfl fun j _ => ?_
        rw [Nat.div_div_eq_div_mul]
        split_ifs with hj
        · exact sum_congr rfl fun b _ => by rw [mul_assoc]
        · refine sum_eq_zero fun b hb => absurd (mem_roughInterval.mp hb) fun h => ?_
          have h1 := (Nat.le_div_iff_mul_le (Nat.mul_pos (by omega) (pow_pos hQ.pos j))).mp
            (h.1.trans h.2.1)
          exact hj (by rw [one_mul] at h1; exact h1)
      · rw [if_neg]
        intro hj'
        have : Q ^ j ≤ N / a := (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hj')
        have : j < Q ^ j := Nat.lt_pow_self hQ.one_lt
        exact hj (mem_range.mpr (by omega))
    · rw [smoothSet_succ_of_not_prime hQ, ih]
      exact sum_congr rfl fun a _ => by rw [roughInterval_succ_of_not_prime hQ]

/-! ### 2. The walk energy and its large primes -/

open ArithmeticFunction in
/-- The multiplicative-walk energy of `y` on `[1, N]` along the prime powers `t` selected by `s`:
`Σ_{mt ≤ N, s(t)} Λ(t)/(mt) (y_{mt} − y_m)²`. -/
def walkEnergy (N : ℕ) (s : ℕ → Prop) [DecidablePred s] (y : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m),
    if s t then Λ t / ((m * t : ℕ) : ℝ) * (y (m * t) - y m) ^ 2 else 0

open ArithmeticFunction in
/-- The walk energy of the `Q`-rough numbers of `[1, X]` along the prime powers of primes `≥ Q`. -/
def roughEnergy (Q X : ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ b ∈ roughInterval Q X, ∑ t ∈ Icc 1 (X / b),
    if Q ≤ t.minFac then Λ t / ((b * t : ℕ) : ℝ) * (g (b * t) - g b) ^ 2 else 0

open ArithmeticFunction in
/-- **The large primes act within the fibres**: the walk energy along primes `≥ Q` is
`Σ_a (1/a) · roughEnergy(Q, N/a)(y(a ·))`. -/
theorem walkEnergy_large_eq (Q N : ℕ) (y : ℕ → ℝ) :
    walkEnergy N (fun t => Q ≤ t.minFac) y =
      ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) * roughEnergy Q (N / a) (fun n => y (a * n)) := by
  rw [walkEnergy, sum_Icc_eq_smooth_rough Q N]
  refine sum_congr rfl fun a ha => ?_
  have ha1 := (mem_smoothSet.mp ha).1
  rw [roughEnergy, mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [mul_sum, Nat.div_div_eq_div_mul]
  refine sum_congr rfl fun t _ => ?_
  split_ifs
  · push_cast
    rw [mul_assoc]
    field_simp
    rw [mul_assoc]
  · rw [mul_zero]

open ArithmeticFunction in
/-- **Base edges**: `log Q · Glauber(Q, X) ≤ roughEnergy(Q, X)` for `Q ≥ 2`. -/
theorem log_mul_glauberForm_le_roughEnergy {Q : ℕ} (hQ : 2 ≤ Q) (X : ℕ) (g : ℕ → ℝ) :
    Real.log Q * glauberForm Q X g ≤ roughEnergy Q X g := by
  set T : ℕ → ℕ → ℝ := fun u t =>
    if Q ≤ t.minFac then Λ t / ((u * t : ℕ) : ℝ) * (g (u * t) - g u) ^ 2 else 0
  have hT : ∀ u t, 0 ≤ T u t := fun u t => by
    simp only [T]
    split_ifs
    · exact mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)) (sq_nonneg _)
    · exact le_rfl
  have hlQ : 0 ≤ Real.log Q := Real.log_natCast_nonneg Q
  -- each prime `q ≥ Q` contributes `log q ≥ log Q` times its ladder variances
  have hqL : ∀ q ∈ (Icc Q X).filter Nat.Prime, ∀ u ∈ (roughInterval Q X).filter (fun u => ¬ q ∣ u),
      Real.log Q * ladderVar q u X g ≤
        ∑ i ∈ (ladder q u X).filter (fun i => 1 ≤ i), T u (q ^ i) := by
    intro q hq u hu
    obtain ⟨hqI, hqp⟩ := mem_filter.mp hq
    have hQq : Q ≤ q := (mem_Icc.mp hqI).1
    have hu1 : 1 ≤ u := (mem_roughInterval.mp (mem_filter.mp hu).1).1
    have hl : Real.log Q ≤ Real.log q :=
      Real.log_le_log (by exact_mod_cast (show 0 < Q by omega)) (by exact_mod_cast hQq)
    calc Real.log Q * ladderVar q u X g ≤ Real.log q * ladderVar q u X g :=
          mul_le_mul_of_nonneg_right hl (ladderVar_nonneg _ _ _ _)
      _ ≤ Real.log q * ∑ i ∈ (ladder q u X).filter (fun i => 1 ≤ i),
          1 / ((u * q ^ i : ℕ) : ℝ) * (g (u * q ^ i) - g u) ^ 2 :=
          mul_le_mul_of_nonneg_left (ladderVar_le_base_edges q u X g)
            (Real.log_nonneg (by exact_mod_cast hqp.one_lt.le))
      _ = ∑ i ∈ (ladder q u X).filter (fun i => 1 ≤ i), T u (q ^ i) := by
          rw [mul_sum]
          refine sum_congr rfl fun i hi => ?_
          have hi1 := (mem_filter.mp hi).2
          simp only [T]
          rw [if_pos (by rw [hqp.pow_minFac (by omega)]; exact hQq),
            vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hqp]
          ring
  -- distinct prime powers below `X/u`
  have hu : ∀ u ∈ roughInterval Q X, ∑ q ∈ (Icc Q X).filter Nat.Prime,
      ∑ i ∈ (ladder q u X).filter (fun i => 1 ≤ i), T u (q ^ i) ≤
        ∑ t ∈ Icc 1 (X / u), T u t := by
    intro u hu
    have hu1 := (mem_roughInterval.mp hu).1
    rw [sum_sigma']
    rw [← sum_image (s := ((Icc Q X).filter Nat.Prime).sigma
        (fun q => (ladder q u X).filter (fun i => 1 ≤ i))) (g := fun z => z.1 ^ z.2)]
    · refine sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) (fun t _ _ => hT u t)
      obtain ⟨⟨q, i⟩, hz, rfl⟩ := mem_image.mp ht
      obtain ⟨hq, hi⟩ := mem_sigma.mp hz
      have hqp := (mem_filter.mp hq).2
      have hiX := (mem_filter.mp (mem_filter.mp hi).1).2
      refine mem_Icc.mpr ⟨Nat.one_le_pow _ _ hqp.pos, ?_⟩
      rw [Nat.le_div_iff_mul_le (by omega), mul_comm]
      exact hiX
    · rintro ⟨q₁, i₁⟩ h₁ ⟨q₂, i₂⟩ h₂ heq
      obtain ⟨hq₁, hi₁⟩ := mem_sigma.mp h₁
      obtain ⟨hq₂, -⟩ := mem_sigma.mp h₂
      obtain ⟨rfl, rfl⟩ := prime_pow_inj (mem_filter.mp hq₁).2 (mem_filter.mp hq₂).2
        (mem_filter.mp hi₁).2 heq
      rfl
  rw [glauberForm, mul_sum]
  calc ∑ q ∈ (Icc Q X).filter Nat.Prime, Real.log Q *
        ∑ u ∈ (roughInterval Q X).filter (fun u => ¬ q ∣ u), ladderVar q u X g
      ≤ ∑ q ∈ (Icc Q X).filter Nat.Prime, ∑ u ∈ roughInterval Q X,
          ∑ i ∈ (ladder q u X).filter (fun i => 1 ≤ i), T u (q ^ i) := by
        refine sum_le_sum fun q hq => ?_
        rw [mul_sum]
        refine (sum_le_sum fun u hu => hqL q hq u hu).trans ?_
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          fun u _ _ => sum_nonneg fun i _ => hT u _
    _ = ∑ u ∈ roughInterval Q X, ∑ q ∈ (Icc Q X).filter Nat.Prime,
          ∑ i ∈ (ladder q u X).filter (fun i => 1 ≤ i), T u (q ^ i) := sum_comm
    _ ≤ ∑ u ∈ roughInterval Q X, ∑ t ∈ Icc 1 (X / u), T u t := sum_le_sum hu
    _ = roughEnergy Q X g := rfl

/-- **Within the fibres**: `Σ_a (1/a) Var_{R(Q, N/a)}(y(a ·)) ≤ (K/log Q) E_{large}(y)`. -/
theorem sum_fibreVar_le {K : ℝ} (hK : 0 ≤ K)
    (hKt : ∀ Q X : ℕ, ∀ f : ℕ → ℝ, harmonicVar Q X f ≤ K * glauberForm Q X f) {Q : ℕ} (hQ : 2 ≤ Q)
    (N : ℕ) (y : ℕ → ℝ) :
    ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) * harmonicVar Q (N / a) (fun n => y (a * n)) ≤
      K / Real.log Q * walkEnergy N (fun t => Q ≤ t.minFac) y := by
  have hlQ : 0 < Real.log Q := Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  rw [walkEnergy_large_eq, mul_sum]
  refine sum_le_sum fun a _ => ?_
  have hfib := hKt Q (N / a) (fun n => y (a * n))
  have hb := log_mul_glauberForm_le_roughEnergy hQ (N / a) (fun n => y (a * n))
  have hG : glauberForm Q (N / a) (fun n => y (a * n)) ≤
      roughEnergy Q (N / a) (fun n => y (a * n)) / Real.log Q := by
    rw [le_div_iff₀ hlQ, mul_comm]; exact hb
  calc 1 / (a : ℝ) * harmonicVar Q (N / a) (fun n => y (a * n))
      ≤ 1 / (a : ℝ) * (K * (roughEnergy Q (N / a) (fun n => y (a * n)) / Real.log Q)) :=
        mul_le_mul_of_nonneg_left (hfib.trans (mul_le_mul_of_nonneg_left hG hK)) (by positivity)
    _ = K / Real.log Q * (1 / (a : ℝ) * roughEnergy Q (N / a) (fun n => y (a * n))) := by ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
