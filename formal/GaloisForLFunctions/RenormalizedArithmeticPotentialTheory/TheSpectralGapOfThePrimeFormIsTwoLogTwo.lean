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

/-! ### 3. The small primes in both fibrations -/

/-- The two fibrations of `[1, N]`: over the smooth part and over the rough part. -/
theorem sum_smooth_rough_comm (Q N : ℕ) (φ : ℕ → ℕ → ℝ) :
    ∑ a ∈ smoothSet Q N, ∑ b ∈ roughInterval Q (N / a), φ a b =
      ∑ b ∈ roughInterval Q N, ∑ a ∈ smoothSet Q (N / b), φ a b := by
  refine sum_comm' fun a b => ?_
  simp only [mem_smoothSet, mem_roughInterval]
  constructor
  · rintro ⟨⟨ha1, -, has⟩, hb1, hbN, hbr⟩
    have hab : b * a ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp hbN
    exact ⟨⟨ha1, (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hab), has⟩, hb1,
      hbN.trans (Nat.div_le_self _ _), hbr⟩
  · rintro ⟨⟨ha1, haN, has⟩, hb1, -, hbr⟩
    have hab : a * b ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp haN
    exact ⟨⟨ha1, haN.trans (Nat.div_le_self _ _), has⟩, hb1,
      (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hab), hbr⟩

/-- The small-prime edges leaving `m`, indexed by `(p, k)`: `Σ_{p < Q, mp^k ≤ N} log p/(mp^k) (y_{mp^k} − y_m)²`. -/
def smallEdge (Q N : ℕ) (y : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ p ∈ (range Q).filter Nat.Prime, ∑ k ∈ range (N + 1),
    if 1 ≤ k ∧ m * p ^ k ≤ N then Real.log p / ((m * p ^ k : ℕ) : ℝ) * (y (m * p ^ k) - y m) ^ 2
    else 0

open ArithmeticFunction in
/-- Distinct `(p, k)` give distinct prime powers, so the small edges of `m` are edges of the walk. -/
theorem smallEdge_le {m : ℕ} (hm : 1 ≤ m) (Q N : ℕ) (y : ℕ → ℝ) :
    smallEdge Q N y m ≤ ∑ t ∈ Icc 1 (N / m),
      if t.minFac < Q then Λ t / ((m * t : ℕ) : ℝ) * (y (m * t) - y m) ^ 2 else 0 := by
  set T : ℕ → ℝ := fun t =>
    if t.minFac < Q then Λ t / ((m * t : ℕ) : ℝ) * (y (m * t) - y m) ^ 2 else 0
  have hT : ∀ t, 0 ≤ T t := fun t => by
    simp only [T]
    split_ifs
    · exact mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)) (sq_nonneg _)
    · exact le_rfl
  have hterm : ∀ p ∈ (range Q).filter Nat.Prime, ∀ k ∈ range (N + 1),
      (if 1 ≤ k ∧ m * p ^ k ≤ N then
        Real.log p / ((m * p ^ k : ℕ) : ℝ) * (y (m * p ^ k) - y m) ^ 2 else 0) =
        if 1 ≤ k ∧ m * p ^ k ≤ N then T (p ^ k) else 0 := by
    intro p hp k _
    have hpp := (mem_filter.mp hp).2
    have hpQ := mem_range.mp (mem_filter.mp hp).1
    split_ifs with hk
    · simp only [T]
      rw [if_pos (by rw [hpp.pow_minFac (by omega)]; exact hpQ), vonMangoldt_apply_pow (by omega),
        vonMangoldt_apply_prime hpp]
    · rfl
  rw [smallEdge, sum_congr rfl fun p hp => sum_congr rfl (hterm p hp)]
  simp only [← sum_filter]
  rw [sum_sigma']
  rw [← sum_image (s := ((range Q).filter Nat.Prime).sigma
      (fun p => (range (N + 1)).filter (fun k => 1 ≤ k ∧ m * p ^ k ≤ N))) (g := fun z => z.1 ^ z.2)]
  · refine sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) (fun t _ _ => hT t)
    obtain ⟨⟨p, k⟩, hz, rfl⟩ := mem_image.mp ht
    obtain ⟨hp, hk⟩ := mem_sigma.mp hz
    have hpp := (mem_filter.mp hp).2
    have hk' := (mem_filter.mp hk).2
    exact mem_Icc.mpr ⟨Nat.one_le_pow _ _ hpp.pos,
      (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hk'.2)⟩
  · rintro ⟨p₁, k₁⟩ h₁ ⟨p₂, k₂⟩ h₂ heq
    obtain ⟨hp₁, hk₁⟩ := mem_sigma.mp h₁
    obtain ⟨hp₂, -⟩ := mem_sigma.mp h₂
    obtain ⟨rfl, rfl⟩ := prime_pow_inj (mem_filter.mp hp₁).2 (mem_filter.mp hp₂).2
      (mem_filter.mp hk₁).2.1 heq
    rfl

theorem sum_smallEdge_le (Q N : ℕ) (y : ℕ → ℝ) :
    ∑ m ∈ Icc 1 N, smallEdge Q N y m ≤ walkEnergy N (fun t => t.minFac < Q) y :=
  sum_le_sum fun m hm => smallEdge_le (mem_Icc.mp hm).1 Q N y

/-- The smooth energy as a sum over edges `a → a p^k` (any range `R ≥ X` of exponents). -/
theorem smoothEnergy_eq_edges (Q : ℕ) {X R : ℕ} (hXR : X ≤ R) (h : ℕ → ℝ) :
    smoothEnergy Q X h = ∑ p ∈ (range Q).filter Nat.Prime, ∑ a ∈ smoothSet Q X, ∑ k ∈ range (R + 1),
      if 1 ≤ k ∧ a * p ^ k ≤ X then
        Real.log p / ((a * p ^ k : ℕ) : ℝ) * (h (a * p ^ k) - h a) ^ 2 else 0 := by
  refine sum_congr rfl fun p hp => ?_
  have hpp := (mem_filter.mp hp).2
  have hpQ := mem_range.mp (mem_filter.mp hp).1
  rw [sum_smoothSet_eq_ladders hpp hpQ]
  refine sum_congr rfl fun u hu => ?_
  have hu1 := (mem_smoothSet.mp (mem_filter.mp hu).1).1
  rw [sum_filter]
  refine sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [← sum_filter, ← sum_filter]
    refine sum_nbij' (fun j => j - i) (fun k => i + k) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [mem_filter, mem_range] at hj ⊢
      refine ⟨by omega, by omega, ?_⟩
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hj.2.1.le]
      exact hj.2.2
    · intro k hk
      simp only [mem_filter, mem_range] at hk ⊢
      have h1 : u * p ^ (i + k) ≤ X := by rw [pow_add, ← mul_assoc]; exact hk.2.2
      have h2 : p ^ (i + k) ≤ X := le_trans (Nat.le_mul_of_pos_left _ (by omega)) h1
      have h3 : i + k < p ^ (i + k) := Nat.lt_pow_self hpp.one_lt
      exact ⟨by omega, by omega, h1⟩
    · intro j hj
      simp only [mem_filter, mem_range] at hj
      omega
    · intro k _
      simp
    · intro j hj
      simp only [mem_filter, mem_range] at hj
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hj.2.1.le]
  · refine sum_eq_zero fun j _ => if_neg fun hj => hi ?_
    exact le_trans (Nat.mul_le_mul_left u (Nat.pow_le_pow_right hpp.pos hj.1.le)) hj.2

/-- **Fibre over the rough part**: the small edges of `a b` are the `b`-rescaled smooth chain. -/
theorem sum_smallEdge_fibre_rough (Q N : ℕ) {b : ℕ} (hb : 1 ≤ b) (y : ℕ → ℝ) :
    ∑ a ∈ smoothSet Q (N / b), smallEdge Q N y (a * b) =
      1 / (b : ℝ) * smoothEnergy Q (N / b) (fun a => y (a * b)) := by
  rw [smoothEnergy_eq_edges Q (Nat.div_le_self N b), mul_sum]
  simp only [smallEdge]
  rw [sum_comm]
  refine sum_congr rfl fun p hp => ?_
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.pos
  rw [mul_sum]
  refine sum_congr rfl fun a ha => ?_
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (mem_smoothSet.mp ha).1
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  have hc : a * b * p ^ k ≤ N ↔ a * p ^ k ≤ N / b := by
    rw [Nat.le_div_iff_mul_le (by omega), mul_right_comm]
  by_cases hk : 1 ≤ k ∧ a * p ^ k ≤ N / b
  · rw [if_pos ⟨hk.1, hc.mpr hk.2⟩, if_pos hk, mul_right_comm a b (p ^ k)]
    push_cast
    field_simp
  · rw [if_neg fun h' => hk ⟨h'.1, hc.mp h'.2⟩, if_neg hk, mul_zero]

/-- **Fibre over the smooth part**: the small edges out of the fibre of `a` along `p^k` pair the
fibre of `a` with that of `a p^k`. -/
theorem sum_smallEdge_fibre_smooth (Q N : ℕ) {a : ℕ} (ha : 1 ≤ a) (y : ℕ → ℝ) :
    ∑ b ∈ roughInterval Q (N / a), smallEdge Q N y (a * b) =
      ∑ p ∈ (range Q).filter Nat.Prime, ∑ k ∈ range (N + 1),
        if 1 ≤ k then Real.log p / ((a * p ^ k : ℕ) : ℝ) *
          ∑ b ∈ roughInterval Q (N / (a * p ^ k)), 1 / (b : ℝ) * (y (a * p ^ k * b) - y (a * b)) ^ 2
        else 0 := by
  simp only [smallEdge]
  rw [sum_comm]
  refine sum_congr rfl fun p hp => ?_
  have hpp := (mem_filter.mp hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  by_cases hk : 1 ≤ k
  · rw [if_pos hk, mul_sum]
    simp only [hk, true_and]
    rw [← sum_filter]
    have hapk : 0 < a * p ^ k := Nat.mul_pos (by omega) (pow_pos hpp.pos k)
    have hset : (roughInterval Q (N / a)).filter (fun b => a * b * p ^ k ≤ N) =
        roughInterval Q (N / (a * p ^ k)) := by
      ext b
      simp only [mem_filter, mem_roughInterval]
      have e : a * b * p ^ k = b * (a * p ^ k) := by ring
      constructor
      · rintro ⟨⟨h1, -, h3⟩, h4⟩
        exact ⟨h1, (Nat.le_div_iff_mul_le hapk).mpr (e ▸ h4), h3⟩
      · rintro ⟨h1, h2, h3⟩
        have h4 := (Nat.le_div_iff_mul_le hapk).mp h2
        have h5 : b * a ≤ N := le_trans (Nat.mul_le_mul_left b (Nat.le_mul_of_pos_right a
          (pow_pos hpp.pos k))) h4
        exact ⟨⟨h1, (Nat.le_div_iff_mul_le (by omega)).mpr h5, h3⟩, e ▸ h4⟩
    rw [hset]
    refine sum_congr rfl fun b hb => ?_
    have hb0 : (0 : ℝ) < b := by exact_mod_cast (mem_roughInterval.mp hb).1
    rw [mul_right_comm a b (p ^ k)]
    push_cast
    field_simp
  · rw [if_neg hk]
    exact sum_eq_zero fun b _ => if_neg fun h => hk h.1

/-- The walk energy splits into its small- and large-prime parts, which in the pole gauge add up to
the pole defect. -/
theorem walkEnergy_small_add_large (Q N : ℕ) (x : ℕ → ℝ) :
    walkEnergy N (fun t => t.minFac < Q) (poleGauge x) +
      walkEnergy N (fun t => Q ≤ t.minFac) (poleGauge x) = poleDefect N x := by
  rw [walkEnergy, walkEnergy, ← sum_add_distrib, poleDefect]
  refine sum_congr rfl fun m hm => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun t ht => ?_
  rw [sq_sub_div_sqrt_eq (mem_Icc.mp hm).1 (mem_Icc.mp ht).1 x]
  by_cases h : t.minFac < Q
  · rw [if_pos h, if_neg (not_le.mpr h), add_zero]; ring
  · rw [if_neg h, if_pos (not_lt.mp h), zero_add]; ring

/-! ### 4. The halo and the shells -/

/-- **The halo of the smooth parts**: `Σ_n (1/n) log(a(n)) (y_n − c)² ≤ 2 D_S + 2 M_Q Σ_n (1/n)(y_n − c)²`,
with `a(n)` the `Q`-smooth part of `n`. -/
theorem sum_log_mul_fibre_le (Q N : ℕ) (y : ℕ → ℝ) (c : ℝ) :
    ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) * Real.log a *
        ∑ b ∈ roughInterval Q (N / a), 1 / (b : ℝ) * (y (a * b) - c) ^ 2 ≤
      2 * walkEnergy N (fun t => t.minFac < Q) y +
        2 * ladderConstant Q * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (y n - c) ^ 2 := by
  have e1 : ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) * Real.log a *
        ∑ b ∈ roughInterval Q (N / a), 1 / (b : ℝ) * (y (a * b) - c) ^ 2 =
      ∑ b ∈ roughInterval Q N, 1 / (b : ℝ) * ∑ a ∈ smoothSet Q (N / b),
        1 / (a : ℝ) * Real.log a * (y (a * b) - c) ^ 2 := by
    simp only [mul_sum]
    rw [sum_smooth_rough_comm]
    exact sum_congr rfl fun b _ => sum_congr rfl fun a _ => by ring
  have e2 : ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (y n - c) ^ 2 =
      ∑ b ∈ roughInterval Q N, 1 / (b : ℝ) * ∑ a ∈ smoothSet Q (N / b),
        1 / (a : ℝ) * (y (a * b) - c) ^ 2 := by
    rw [sum_Icc_eq_smooth_rough Q N, sum_smooth_rough_comm]
    simp only [mul_sum]
    exact sum_congr rfl fun b _ => sum_congr rfl fun a _ => by push_cast; ring
  have e3 : ∑ b ∈ roughInterval Q N, 1 / (b : ℝ) * smoothEnergy Q (N / b) (fun a => y (a * b) - c) ≤
      walkEnergy N (fun t => t.minFac < Q) y := by
    have : ∑ b ∈ roughInterval Q N, 1 / (b : ℝ) * smoothEnergy Q (N / b) (fun a => y (a * b) - c) =
        ∑ m ∈ Icc 1 N, smallEdge Q N y m := by
      rw [sum_Icc_eq_smooth_rough Q N, sum_smooth_rough_comm]
      refine sum_congr rfl fun b hb => ?_
      rw [smoothEnergy_sub_const Q (N / b) (fun a => y (a * b)) c,
        ← sum_smallEdge_fibre_rough Q N (mem_roughInterval.mp hb).1]
    rw [this]
    exact sum_smallEdge_le Q N y
  rw [e1, e2, mul_sum, mul_sum, ← sum_add_distrib]
  have hstep : ∀ b ∈ roughInterval Q N, 1 / (b : ℝ) * ∑ a ∈ smoothSet Q (N / b),
        1 / (a : ℝ) * Real.log a * (y (a * b) - c) ^ 2 ≤
      2 * (1 / (b : ℝ) * smoothEnergy Q (N / b) (fun a => y (a * b) - c)) +
        2 * ladderConstant Q * (1 / (b : ℝ) * ∑ a ∈ smoothSet Q (N / b),
          1 / (a : ℝ) * (y (a * b) - c) ^ 2) := by
    intro b _
    have h := sum_log_mul_sq_le_smoothEnergy Q (N / b) (fun a => y (a * b) - c)
    have hb : (0 : ℝ) ≤ 1 / (b : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h hb]
  calc ∑ b ∈ roughInterval Q N, 1 / (b : ℝ) * ∑ a ∈ smoothSet Q (N / b),
        1 / (a : ℝ) * Real.log a * (y (a * b) - c) ^ 2
      ≤ ∑ b ∈ roughInterval Q N, (2 * (1 / (b : ℝ) * smoothEnergy Q (N / b)
          (fun a => y (a * b) - c)) + 2 * ladderConstant Q * (1 / (b : ℝ) *
            ∑ a ∈ smoothSet Q (N / b), 1 / (a : ℝ) * (y (a * b) - c) ^ 2)) := sum_le_sum hstep
    _ = 2 * ∑ b ∈ roughInterval Q N, 1 / (b : ℝ) * smoothEnergy Q (N / b)
          (fun a => y (a * b) - c) + ∑ b ∈ roughInterval Q N, 2 * ladderConstant Q *
            (1 / (b : ℝ) * ∑ a ∈ smoothSet Q (N / b), 1 / (a : ℝ) * (y (a * b) - c) ^ 2) := by
        rw [sum_add_distrib, mul_sum]
    _ ≤ _ := by linarith [e3]

/-- **Shells are thin**: the rough mass of `(Y/t, Y]` is at most `1 + log t`. -/
theorem roughHarmonic_sub_div_le (Q Y : ℕ) {t : ℕ} (ht : 1 ≤ t) :
    roughHarmonic Q Y - roughHarmonic Q (Y / t) ≤ 1 + Real.log t := by
  have hsub : (roughInterval Q Y).filter (fun K => Y / t < K) ⊆
      (roughInterval 0 Y).filter (fun K => Y / t < K) := fun K hK => by
    obtain ⟨hK1, hK2⟩ := mem_filter.mp hK
    exact mem_filter.mpr ⟨by rw [roughInterval_zero]; exact mem_Icc.mpr
      ⟨(mem_roughInterval.mp hK1).1, (mem_roughInterval.mp hK1).2.1⟩, hK2⟩
  rw [roughHarmonic_sub_eq (Nat.div_le_self Y t)]
  refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
  rw [← roughHarmonic_sub_eq (Nat.div_le_self Y t)]
  have h1 := roughHarmonic_le_one_add_log 0 Y
  have h2 : Real.log ((Y / t : ℕ) + 1) ≤ roughHarmonic 0 (Y / t) := by
    have h := log_add_one_le_harmonic (Y / t)
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    rw [roughHarmonic, roughInterval_zero]
    simpa [one_div] using h
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hlt : 0 ≤ Real.log t := Real.log_natCast_nonneg t
  have h3 : Real.log Y ≤ Real.log t + Real.log ((Y / t : ℕ) + 1) := by
    rcases Nat.eq_zero_or_pos Y with hY | hY
    · rw [hY, Nat.cast_zero, Real.log_zero]
      exact add_nonneg hlt (Real.log_nonneg (by linarith [(Nat.cast_nonneg (Y / t) : (0 : ℝ) ≤ _)]))
    · rw [← Real.log_mul ht0.ne' (by positivity)]
      refine Real.log_le_log (by exact_mod_cast hY) ?_
      have := Nat.lt_mul_div_succ Y (show 0 < t by omega)
      exact_mod_cast this.le
  linarith

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
