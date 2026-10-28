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
  simp only [mem_smoothSet, mem_filter, mem_Icc, not_lt_zero]
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
theorem walkEnergy_nonneg (N : ℕ) (s : ℕ → Prop) [DecidablePred s] (y : ℕ → ℝ) :
    0 ≤ walkEnergy N s y :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => by
    split_ifs
    · exact mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)) (sq_nonneg _)
    · exact le_rfl

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
/-- The small edges of `m` are exactly the walk edges `m → mt` with `t` a power of a prime `< Q`:
distinct `(p, k)` give distinct prime powers, and `Λ` vanishes off the prime powers. -/
theorem smallEdge_eq {m : ℕ} (hm : 1 ≤ m) (Q N : ℕ) (y : ℕ → ℝ) :
    smallEdge Q N y m = ∑ t ∈ Icc 1 (N / m),
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
  · refine sum_subset (fun t ht => ?_) (fun t ht hti => ?_)
    · obtain ⟨⟨p, k⟩, hz, rfl⟩ := mem_image.mp ht
      obtain ⟨hp, hk⟩ := mem_sigma.mp hz
      have hpp := (mem_filter.mp hp).2
      have hk' := (mem_filter.mp hk).2
      exact mem_Icc.mpr ⟨Nat.one_le_pow _ _ hpp.pos,
        (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hk'.2)⟩
    · -- a nonzero term is a prime power `p^k` with `p < Q`, hence in the image
      simp only [T]
      by_contra hne
      have hQ : t.minFac < Q := by by_contra h; exact hne (if_neg h)
      have hΛ : Λ t ≠ 0 := fun h => hne (by rw [if_pos hQ, h, zero_div, zero_mul])
      obtain ⟨p, k, hpp, hk0, rfl⟩ := (isPrimePow_nat_iff _).mp (vonMangoldt_ne_zero_iff.mp hΛ)
      have htN := (mem_Icc.mp ht).2
      have hkp : k < p ^ k := Nat.lt_pow_self hpp.one_lt
      have hpkN : p ^ k ≤ N := htN.trans (Nat.div_le_self N m)
      refine hti (mem_image.mpr ⟨⟨p, k⟩, mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_range.mpr ?_, hpp⟩,
        mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (hkp.le.trans hpkN)),
          Nat.succ_le_of_lt hk0, ?_⟩⟩, rfl⟩)
      · rwa [hpp.pow_minFac hk0.ne'] at hQ
      · rw [mul_comm]; exact (Nat.le_div_iff_mul_le (by omega)).mp htN
  · rintro ⟨p₁, k₁⟩ h₁ ⟨p₂, k₂⟩ h₂ heq
    obtain ⟨hp₁, hk₁⟩ := mem_sigma.mp h₁
    obtain ⟨hp₂, -⟩ := mem_sigma.mp h₂
    obtain ⟨rfl, rfl⟩ := prime_pow_inj (mem_filter.mp hp₁).2 (mem_filter.mp hp₂).2
      (mem_filter.mp hk₁).2.1 heq
    rfl

/-- The small-prime part of the walk energy is the sum of the small edges. -/
theorem sum_smallEdge_eq (Q N : ℕ) (y : ℕ → ℝ) :
    ∑ m ∈ Icc 1 N, smallEdge Q N y m = walkEnergy N (fun t => t.minFac < Q) y :=
  sum_congr rfl fun _ hm => smallEdge_eq (mem_Icc.mp hm).1 Q N y

theorem sum_smallEdge_le (Q N : ℕ) (y : ℕ → ℝ) :
    ∑ m ∈ Icc 1 N, smallEdge Q N y m ≤ walkEnergy N (fun t => t.minFac < Q) y :=
  (sum_smallEdge_eq Q N y).le

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
  rw [e1, e2]
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
    _ = 2 * ∑ b ∈ roughInterval Q N, 1 / (b : ℝ) * smoothEnergy Q (N / b)
          (fun a => y (a * b) - c) + 2 * ladderConstant Q * ∑ b ∈ roughInterval Q N,
            1 / (b : ℝ) * ∑ a ∈ smoothSet Q (N / b), 1 / (a : ℝ) * (y (a * b) - c) ^ 2 := by
        congr 1
        exact (mul_sum _ _ _).symm
    _ ≤ _ := by linarith [e3]

/-- **Shells are thin**: the rough mass of `(Y/t, Y]` is at most `1 + log t`. -/
theorem roughHarmonic_sub_div_le (Q Y : ℕ) {t : ℕ} (ht : 1 ≤ t) :
    roughHarmonic Q Y - roughHarmonic Q (Y / t) ≤ 1 + Real.log t := by
  have hsub : (roughInterval Q Y).filter (fun K => Y / t < K) ⊆
      (roughInterval 0 Y).filter (fun K => Y / t < K) := fun K hK => by
    obtain ⟨hK1, hK2⟩ := mem_filter.mp hK
    have hK3 : K ∈ roughInterval 0 Y := by
      rw [roughInterval_zero]
      exact mem_Icc.mpr ⟨(mem_roughInterval.mp hK1).1, (mem_roughInterval.mp hK1).2.1⟩
    exact mem_filter.mpr ⟨hK3, hK2⟩
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

/-! ### 5. Jensen across the fibres -/

/-- The mean of `y` on the fibre `a · R(Q, N/a)`. -/
def fibreMean (Q N : ℕ) (y : ℕ → ℝ) (a : ℕ) : ℝ :=
  wMean (roughInterval Q (N / a)) (fun b => 1 / (b : ℝ)) (fun b => y (a * b))

/-- **One edge of the smooth chain.** For `a t ≤ X ≤ N`, the jump of the fibre means along `a → a t`
is paid by the walk edges between the two fibres, up to the commutation error of the shell
`(N/(at), N/a]`: `F(N)(h_{at} − h_a)² ≤ (F(N)/F(N/X))((1 + η) e + (1 + 1/η)((1 + log t)/F(N/X)) V_a)`. -/
theorem roughHarmonic_mul_sq_fibreMean_sub_le {Q N X a t : ℕ} (ha : 1 ≤ a) (ht : 1 ≤ t)
    (hX : a * t ≤ X) (hXN : X ≤ N) {η : ℝ} (hη : 0 < η) (y : ℕ → ℝ) :
    roughHarmonic Q N * (fibreMean Q N y (a * t) - fibreMean Q N y a) ^ 2 ≤
      roughHarmonic Q N / roughHarmonic Q (N / X) *
        ((1 + η) * ∑ b ∈ roughInterval Q (N / (a * t)), 1 / (b : ℝ) * (y (a * t * b) - y (a * b)) ^ 2 +
          (1 + 1 / η) * ((1 + Real.log t) / roughHarmonic Q (N / X)) *
            harmonicVar Q (N / a) (fun b => y (a * b))) := by
  have hat : 0 < a * t := Nat.mul_pos (by omega) (by omega)
  have hNX : 1 ≤ N / X := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hXat : N / X ≤ N / (a * t) := Nat.div_le_div_left hX hat
  have hata : N / (a * t) ≤ N / a := Nat.div_le_div_left (Nat.le_mul_of_pos_right a (by omega)) (by omega)
  have hG1 : 1 ≤ roughHarmonic Q (N / X) := one_le_roughHarmonic Q hNX
  have hGF' : roughHarmonic Q (N / X) ≤ roughHarmonic Q (N / (a * t)) := roughHarmonic_mono hXat
  have hF'Fa : roughHarmonic Q (N / (a * t)) ≤ roughHarmonic Q (N / a) := roughHarmonic_mono hata
  have hF'pos : 0 < roughHarmonic Q (N / (a * t)) := by linarith
  have hshell : roughHarmonic Q (N / a) - roughHarmonic Q (N / (a * t)) ≤ 1 + Real.log t := by
    have := roughHarmonic_sub_div_le Q (N / a) ht
    rwa [Nat.div_div_eq_div_mul] at this
  set h₁ := wMean (roughInterval Q (N / (a * t))) (fun b => 1 / (b : ℝ)) (fun b => y (a * b))
  have hd : fibreMean Q N y (a * t) - h₁ = wMean (roughInterval Q (N / (a * t)))
      (fun b => 1 / (b : ℝ)) (fun b => y (a * t * b) - y (a * b)) := by
    simp only [h₁, fibreMean, wMean, mul_sub, sum_sub_distrib, sub_div]
  -- Jensen on the common fibre
  have hi : roughHarmonic Q (N / (a * t)) * (fibreMean Q N y (a * t) - h₁) ^ 2 ≤
      ∑ b ∈ roughInterval Q (N / (a * t)), 1 / (b : ℝ) * (y (a * t * b) - y (a * b)) ^ 2 := by
    have := sum_mul_sq_wMean_sub_le (s := roughInterval Q (N / (a * t)))
      (w := fun b : ℕ => 1 / (b : ℝ)) (v := fun b => y (a * t * b) - y (a * b))
      (fun b _ => by positivity) 0
    simp only [sub_zero] at this
    rw [hd]
    exact this
  -- the nested means of the fibre of `a`
  have hii : roughHarmonic Q (N / (a * t)) * (h₁ - fibreMean Q N y a) ^ 2 * roughHarmonic Q (N / a) ≤
      harmonicVar Q (N / a) (fun b => y (a * b)) *
        (roughHarmonic Q (N / a) - roughHarmonic Q (N / (a * t))) :=
    mul_sq_wMean_sub_le (w := fun b : ℕ => 1 / (b : ℝ)) (fun b _ => by positivity)
      (roughInterval_mono hata) hF'pos
  have hV : 0 ≤ harmonicVar Q (N / a) (fun b => y (a * b)) := harmonicVar_nonneg _ _ _
  have hii' : roughHarmonic Q (N / (a * t)) * (h₁ - fibreMean Q N y a) ^ 2 ≤
      (1 + Real.log t) / roughHarmonic Q (N / X) * harmonicVar Q (N / a) (fun b => y (a * b)) := by
    have h1 := hii.trans (mul_le_mul_of_nonneg_left hshell hV)
    have hpos : 0 ≤ roughHarmonic Q (N / (a * t)) * (h₁ - fibreMean Q N y a) ^ 2 :=
      mul_nonneg hF'pos.le (sq_nonneg _)
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left (hGF'.trans hF'Fa) hpos]
  have hiii := add_sq_le_of_pos hη (fibreMean Q N y (a * t) - h₁) (h₁ - fibreMean Q N y a)
  rw [show fibreMean Q N y (a * t) - h₁ + (h₁ - fibreMean Q N y a) =
    fibreMean Q N y (a * t) - fibreMean Q N y a by ring] at hiii
  have hF0 := roughHarmonic_nonneg Q N
  have hρ : 0 ≤ roughHarmonic Q N / roughHarmonic Q (N / X) := div_nonneg hF0 (by linarith)
  have hFG : roughHarmonic Q N ≤ roughHarmonic Q N / roughHarmonic Q (N / X) *
      roughHarmonic Q (N / (a * t)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    exact mul_le_mul_of_nonneg_left hGF' hF0
  have hη1 : 0 ≤ 1 + η := by linarith
  have hη2 : 0 ≤ 1 + 1 / η := by positivity
  calc roughHarmonic Q N * (fibreMean Q N y (a * t) - fibreMean Q N y a) ^ 2
      ≤ roughHarmonic Q N / roughHarmonic Q (N / X) * roughHarmonic Q (N / (a * t)) *
          (fibreMean Q N y (a * t) - fibreMean Q N y a) ^ 2 :=
        mul_le_mul_of_nonneg_right hFG (sq_nonneg _)
    _ ≤ roughHarmonic Q N / roughHarmonic Q (N / X) * (roughHarmonic Q (N / (a * t)) *
          ((1 + η) * (fibreMean Q N y (a * t) - h₁) ^ 2 +
            (1 + 1 / η) * (h₁ - fibreMean Q N y a) ^ 2)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hiii hF'pos.le) hρ
    _ = roughHarmonic Q N / roughHarmonic Q (N / X) *
          ((1 + η) * (roughHarmonic Q (N / (a * t)) * (fibreMean Q N y (a * t) - h₁) ^ 2) +
            (1 + 1 / η) * (roughHarmonic Q (N / (a * t)) * (h₁ - fibreMean Q N y a) ^ 2)) := by ring
    _ ≤ roughHarmonic Q N / roughHarmonic Q (N / X) *
          ((1 + η) * ∑ b ∈ roughInterval Q (N / (a * t)), 1 / (b : ℝ) * (y (a * t * b) - y (a * b)) ^ 2 +
            (1 + 1 / η) * ((1 + Real.log t) / roughHarmonic Q (N / X) *
              harmonicVar Q (N / a) (fun b => y (a * b)))) := by
        gcongr
    _ = _ := by ring

/-- `Σ_{k ≥ 1} (log p/p^k)(1 + log p^k) ≤ 8 log p`. -/
theorem sum_log_div_pow_mul_le {p : ℕ} (hp : p.Prime) (R : ℕ) :
    ∑ k ∈ range (R + 1), (if 1 ≤ k then
      Real.log p / (p : ℝ) ^ k * (1 + Real.log ((p ^ k : ℕ) : ℝ)) else 0) ≤ 8 * Real.log p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hs2 : 4 / 3 ≤ √2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs0 : 0 < √2 := by positivity
  set r := 1 / √2
  have hr0 : 0 ≤ r := by positivity
  have hr34 : r ≤ 3 / 4 := by rw [div_le_iff₀ hs0]; linarith
  have hterm : ∀ k, (if 1 ≤ k then
      Real.log p / (p : ℝ) ^ k * (1 + Real.log ((p ^ k : ℕ) : ℝ)) else 0) ≤ 2 * Real.log p * r ^ k := by
    intro k
    split_ifs
    · push_cast
      set t : ℝ := (p : ℝ) ^ k
      have ht1 : 1 ≤ t := one_le_pow₀ (by linarith)
      have ht0 : 0 < t := by linarith
      have hst : 0 < √t := Real.sqrt_pos.mpr ht0
      have hlog : 1 + Real.log t ≤ 2 * √t := by
        have h1 := Real.log_le_sub_one_of_pos hst
        rw [Real.log_sqrt ht0.le] at h1
        linarith
      have hsq : √2 ^ k ≤ √t := by
        rw [Real.le_sqrt (by positivity) ht0.le, ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
        exact pow_le_pow_left₀ (by norm_num) hp2 k
      have hl0 : 0 ≤ 1 + Real.log t := by have := Real.log_nonneg ht1; linarith
      have hq : (1 + Real.log t) / t ≤ 2 / √2 ^ k := by
        rw [div_le_div_iff₀ ht0 (by positivity)]
        calc (1 + Real.log t) * √2 ^ k ≤ 2 * √t * √t :=
              mul_le_mul hlog hsq (by positivity) (by positivity)
          _ = 2 * t := by rw [mul_assoc, Real.mul_self_sqrt ht0.le]
      calc Real.log p / t * (1 + Real.log t) = Real.log p * ((1 + Real.log t) / t) := by ring
        _ ≤ Real.log p * (2 / √2 ^ k) := mul_le_mul_of_nonneg_left hq hlp
        _ = 2 * Real.log p * r ^ k := by simp only [r, div_pow, one_pow]; ring
    · exact mul_nonneg (mul_nonneg (by norm_num) hlp) (pow_nonneg hr0 k)
  have hg : ∑ k ∈ range (R + 1), r ^ k ≤ 4 := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := R + 1) hr0 (by linarith)
    rw [← range_eq_Ico, pow_zero] at this
    refine this.trans ?_
    rw [div_le_iff₀ (by linarith)]
    linarith
  calc _ ≤ ∑ k ∈ range (R + 1), 2 * Real.log p * r ^ k := sum_le_sum fun k _ => hterm k
    _ = 2 * Real.log p * ∑ k ∈ range (R + 1), r ^ k := by rw [mul_sum]
    _ ≤ 2 * Real.log p * 4 := mul_le_mul_of_nonneg_left hg (by positivity)
    _ = 8 * Real.log p := by ring

/-- **The smooth chain of fibre means is paid by the small primes.** For `1 ≤ X ≤ N` and `η > 0`,
`F(N) E_X(h) ≤ (F(N)/F(N/X))((1 + η) D_S + (1 + 1/η)(8 L_Q/F(N/X)) Σ_a V_a/a)`. -/
theorem roughHarmonic_mul_smoothEnergy_le {Q N X : ℕ} (hX1 : 1 ≤ X) (hXN : X ≤ N) {η : ℝ}
    (hη : 0 < η) (y : ℕ → ℝ) :
    roughHarmonic Q N * smoothEnergy Q X (fibreMean Q N y) ≤
      roughHarmonic Q N / roughHarmonic Q (N / X) *
        ((1 + η) * walkEnergy N (fun t => t.minFac < Q) y +
          (1 + 1 / η) * (8 * logSum Q / roughHarmonic Q (N / X)) *
            ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) * harmonicVar Q (N / a) (fun b => y (a * b))) := by
  set F := roughHarmonic Q N
  set G := roughHarmonic Q (N / X)
  have hNX : 1 ≤ N / X := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hG1 : 1 ≤ G := one_le_roughHarmonic Q hNX
  have hρ : 0 ≤ F / G := div_nonneg (roughHarmonic_nonneg Q N) (by linarith)
  have hη1 : 0 ≤ 1 + η := by linarith
  have hc₂ : 0 ≤ F / G * (1 + 1 / η) / G := by positivity
  set e : ℕ → ℕ → ℕ → ℝ := fun a p k => ∑ b ∈ roughInterval Q (N / (a * p ^ k)),
    1 / (b : ℝ) * (y (a * p ^ k * b) - y (a * b)) ^ 2
  have he : ∀ a p k, 0 ≤ e a p k := fun a p k => sum_nonneg fun b _ => by positivity
  set A : ℕ → ℕ → ℕ → ℝ := fun p a k => if 1 ≤ k then Real.log p / ((a * p ^ k : ℕ) : ℝ) * e a p k else 0
  have hA : ∀ p a k, 0 ≤ A p a k := fun p a k => by
    simp only [A]; split_ifs
    · exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg _)) (he a p k)
    · exact le_rfl
  set B : ℕ → ℝ := fun a => 1 / (a : ℝ) * harmonicVar Q (N / a) (fun b => y (a * b))
  have hB : ∀ a, 0 ≤ B a := fun a => mul_nonneg (by positivity) (harmonicVar_nonneg _ _ _)
  set C : ℕ → ℕ → ℝ := fun p k => if 1 ≤ k then
    Real.log p / (p : ℝ) ^ k * (1 + Real.log ((p ^ k : ℕ) : ℝ)) else 0
  have hterm : ∀ p ∈ (range Q).filter Nat.Prime, ∀ a ∈ smoothSet Q X, ∀ k ∈ range (N + 1),
      F * (if 1 ≤ k ∧ a * p ^ k ≤ X then Real.log p / ((a * p ^ k : ℕ) : ℝ) *
        (fibreMean Q N y (a * p ^ k) - fibreMean Q N y a) ^ 2 else 0) ≤
      F / G * (1 + η) * A p a k + F / G * (1 + 1 / η) / G * (B a * C p k) := by
    intro p hp a ha k _
    have hpp := (mem_filter.mp hp).2
    have ha1 := (mem_smoothSet.mp ha).1
    have hlp := Real.log_natCast_nonneg p
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
    by_cases hk : 1 ≤ k ∧ a * p ^ k ≤ X
    · rw [if_pos hk]
      simp only [A, C, B, if_pos hk.1]
      have hedge := roughHarmonic_mul_sq_fibreMean_sub_le (Q := Q) ha1 (Nat.one_le_pow _ _ hpp.pos)
        hk.2 hXN hη y
      have hw0 : 0 ≤ Real.log p / ((a * p ^ k : ℕ) : ℝ) := by positivity
      have hw : Real.log p / ((a * p ^ k : ℕ) : ℝ) = 1 / (a : ℝ) * (Real.log p / (p : ℝ) ^ k) := by
        push_cast; field_simp
      calc F * (Real.log p / ((a * p ^ k : ℕ) : ℝ) *
            (fibreMean Q N y (a * p ^ k) - fibreMean Q N y a) ^ 2)
          = Real.log p / ((a * p ^ k : ℕ) : ℝ) *
              (F * (fibreMean Q N y (a * p ^ k) - fibreMean Q N y a) ^ 2) := by ring
        _ ≤ Real.log p / ((a * p ^ k : ℕ) : ℝ) * (F / G * ((1 + η) * e a p k +
              (1 + 1 / η) * ((1 + Real.log ((p ^ k : ℕ) : ℝ)) / G) *
                harmonicVar Q (N / a) (fun b => y (a * b)))) :=
            mul_le_mul_of_nonneg_left hedge hw0
        _ = _ := by rw [hw]; ring
    · rw [if_neg hk, mul_zero]
      have hC : 0 ≤ C p k := by
        simp only [C]; split_ifs
        · exact mul_nonneg (div_nonneg hlp (by positivity))
            (by have := Real.log_natCast_nonneg (p ^ k); linarith)
        · exact le_rfl
      exact add_nonneg (mul_nonneg (mul_nonneg hρ hη1) (hA p a k))
        (mul_nonneg hc₂ (mul_nonneg (hB a) hC))
  -- the first part: the walk edges between fibres
  have hS1 : ∑ p ∈ (range Q).filter Nat.Prime, ∑ a ∈ smoothSet Q X, ∑ k ∈ range (N + 1), A p a k ≤
      walkEnergy N (fun t => t.minFac < Q) y := by
    have hsub : smoothSet Q X ⊆ smoothSet Q N := fun a ha => by
      obtain ⟨h1, h2, h3⟩ := mem_smoothSet.mp ha
      exact mem_smoothSet.mpr ⟨h1, h2.trans hXN, h3⟩
    calc ∑ p ∈ (range Q).filter Nat.Prime, ∑ a ∈ smoothSet Q X, ∑ k ∈ range (N + 1), A p a k
        ≤ ∑ p ∈ (range Q).filter Nat.Prime, ∑ a ∈ smoothSet Q N, ∑ k ∈ range (N + 1), A p a k :=
          sum_le_sum fun p _ => sum_le_sum_of_subset_of_nonneg hsub fun a _ _ =>
            sum_nonneg fun k _ => hA p a k
      _ = ∑ a ∈ smoothSet Q N, ∑ b ∈ roughInterval Q (N / a), smallEdge Q N y (a * b) := by
          rw [sum_comm]
          exact sum_congr rfl fun a ha =>
            (sum_smallEdge_fibre_smooth Q N (mem_smoothSet.mp ha).1 y).symm
      _ = ∑ m ∈ Icc 1 N, smallEdge Q N y m := (sum_Icc_eq_smooth_rough Q N _).symm
      _ ≤ _ := sum_smallEdge_le Q N y
  -- the second part: the commutation errors
  have hS2 : ∑ p ∈ (range Q).filter Nat.Prime, ∑ a ∈ smoothSet Q X, ∑ k ∈ range (N + 1), B a * C p k ≤
      8 * logSum Q * ∑ a ∈ smoothSet Q N, B a := by
    have hsub : smoothSet Q X ⊆ smoothSet Q N := fun a ha => by
      obtain ⟨h1, h2, h3⟩ := mem_smoothSet.mp ha
      exact mem_smoothSet.mpr ⟨h1, h2.trans hXN, h3⟩
    calc ∑ p ∈ (range Q).filter Nat.Prime, ∑ a ∈ smoothSet Q X, ∑ k ∈ range (N + 1), B a * C p k
        ≤ ∑ p ∈ (range Q).filter Nat.Prime, ∑ a ∈ smoothSet Q X, B a * (8 * Real.log p) := by
          refine sum_le_sum fun p hp => sum_le_sum fun a _ => ?_
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left (sum_log_div_pow_mul_le (mem_filter.mp hp).2 N) (hB a)
      _ = 8 * logSum Q * ∑ a ∈ smoothSet Q X, B a := by
          rw [sum_comm, logSum, mul_sum]
          refine sum_congr rfl fun a _ => ?_
          rw [← mul_sum, ← mul_sum]
          ring
      _ ≤ 8 * logSum Q * ∑ a ∈ smoothSet Q N, B a :=
          mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub fun a _ _ => hB a)
            (by have := logSum_nonneg Q; linarith)
  calc F * smoothEnergy Q X (fibreMean Q N y)
      = ∑ p ∈ (range Q).filter Nat.Prime, ∑ a ∈ smoothSet Q X, ∑ k ∈ range (N + 1), F * (if 1 ≤ k ∧ a * p ^ k ≤ X then
          Real.log p / ((a * p ^ k : ℕ) : ℝ) *
            (fibreMean Q N y (a * p ^ k) - fibreMean Q N y a) ^ 2 else 0) := by
        rw [smoothEnergy_eq_edges Q hXN]
        simp only [mul_sum]
    _ ≤ ∑ p ∈ (range Q).filter Nat.Prime, ∑ a ∈ smoothSet Q X, ∑ k ∈ range (N + 1),
          (F / G * (1 + η) * A p a k + F / G * (1 + 1 / η) / G * (B a * C p k)) :=
        sum_le_sum fun p hp => sum_le_sum fun a ha => sum_le_sum fun k hk => hterm p hp a ha k hk
    _ = F / G * (1 + η) * ∑ p ∈ (range Q).filter Nat.Prime, ∑ a ∈ smoothSet Q X,
            ∑ k ∈ range (N + 1), A p a k +
          F / G * (1 + 1 / η) / G * ∑ p ∈ (range Q).filter Nat.Prime, ∑ a ∈ smoothSet Q X,
            ∑ k ∈ range (N + 1), B a * C p k := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun p _ => ?_
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun a _ => ?_
        rw [mul_sum, mul_sum, ← sum_add_distrib]
    _ ≤ F / G * (1 + η) * walkEnergy N (fun t => t.minFac < Q) y +
          F / G * (1 + 1 / η) / G * (8 * logSum Q * ∑ a ∈ smoothSet Q N, B a) :=
        add_le_add (mul_le_mul_of_nonneg_left hS1 (mul_nonneg hρ hη1))
          (mul_le_mul_of_nonneg_left hS2 hc₂)
    _ = _ := by ring

/-! ### 6. The two scales together -/

/-- **The two-scale inequality.** For `2 ≤ X ≤ N`, if the fibre means `h` of `y` satisfy
`g₁ Var_X(h) ≤ E_X(h)` on the `Q`-smooth chain of `[1, X]` and `2 M_Q ≤ log X`, then with `F = F(N)`,
`G = F(N/X)`, `U = Σ_a V_a/a` and `c` the mean of `h` on `[1, X]`:
`g₁ (1 − 2M_Q/log X) Σ_n (y_n − c)²/n ≤ g₁ U + (F/G)((1 + η) D_S + (1 + 1/η)(8 L_Q/G) U)
+ (2 g₁/log X) D_S`. -/
theorem two_scale_le {Q N X : ℕ} (hX : 2 ≤ X) (hXN : X ≤ N) {g₁ η : ℝ} (hg₁ : 0 < g₁) (hη : 0 < η)
    (y : ℕ → ℝ) (hA : g₁ * smoothVar Q X (fibreMean Q N y) ≤ smoothEnergy Q X (fibreMean Q N y))
    (hL : 2 * ladderConstant Q ≤ Real.log X) :
    g₁ * ((1 - 2 * ladderConstant Q / Real.log X) * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) *
      (y n - wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) (fibreMean Q N y)) ^ 2) ≤
      g₁ * ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) * harmonicVar Q (N / a) (fun b => y (a * b)) +
        roughHarmonic Q N / roughHarmonic Q (N / X) *
          ((1 + η) * walkEnergy N (fun t => t.minFac < Q) y +
            (1 + 1 / η) * (8 * logSum Q / roughHarmonic Q (N / X)) *
              ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) * harmonicVar Q (N / a) (fun b => y (a * b))) +
        2 * g₁ / Real.log X * walkEnergy N (fun t => t.minFac < Q) y := by
  set h := fibreMean Q N y
  set c := wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) h
  set U := ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) * harmonicVar Q (N / a) (fun b => y (a * b))
  set W := ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (y n - c) ^ 2
  set DS := walkEnergy N (fun t => t.minFac < Q) y
  set L := Real.log X
  set M := ladderConstant Q
  set F := roughHarmonic Q N
  have hL0 : 0 < L := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hF0 : 0 ≤ F := roughHarmonic_nonneg Q N
  have hV : harmonicVar 0 N y ≤ W := by
    have := wVar_le (s := Icc 1 N) (w := fun n : ℕ => 1 / (n : ℝ)) (v := y)
      (fun n _ => by positivity) c
    rw [harmonicVar, roughInterval_zero]
    exact this
  -- total variance over the fibres of the smooth part
  have hfib : ∀ a ∈ smoothSet Q N, ∑ b ∈ roughInterval Q (N / a), 1 / (b : ℝ) * (y (a * b) - c) ^ 2 =
      harmonicVar Q (N / a) (fun b => y (a * b)) + roughHarmonic Q (N / a) * (h a - c) ^ 2 :=
    fun a _ => sum_mul_sub_sq_eq (s := roughInterval Q (N / a)) (w := fun b : ℕ => 1 / (b : ℝ))
      (v := fun b => y (a * b)) (fun b _ => by positivity) c
  have hW : W = U + ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) * (roughHarmonic Q (N / a) * (h a - c) ^ 2) := by
    calc W = ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (y n - c) ^ 2 := rfl
      _ = ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) *
          ∑ b ∈ roughInterval Q (N / a), 1 / (b : ℝ) * (y (a * b) - c) ^ 2 := by
          rw [sum_Icc_eq_smooth_rough Q N]
          refine sum_congr rfl fun a _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun b _ => ?_
          push_cast
          ring
      _ = ∑ a ∈ smoothSet Q N, (1 / (a : ℝ) * harmonicVar Q (N / a) (fun b => y (a * b)) +
          1 / (a : ℝ) * (roughHarmonic Q (N / a) * (h a - c) ^ 2)) :=
          sum_congr rfl fun a ha => by rw [hfib a ha]; ring
      _ = _ := sum_add_distrib
  -- below and above the horizon `X`
  have hset : (smoothSet Q N).filter (fun a => a ≤ X) = smoothSet Q X := by
    ext a
    simp only [mem_filter, mem_smoothSet]
    constructor
    · rintro ⟨⟨h1, -, h3⟩, h4⟩; exact ⟨h1, h4, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2.trans hXN, h3⟩, h2⟩
  have hsplit := sum_filter_add_sum_filter_not (smoothSet Q N) (fun a => a ≤ X)
    (fun a => 1 / (a : ℝ) * (roughHarmonic Q (N / a) * (h a - c) ^ 2))
  rw [hset] at hsplit
  have hA1 : ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (roughHarmonic Q (N / a) * (h a - c) ^ 2) ≤
      F * smoothVar Q X h := by
    rw [show smoothVar Q X h = ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (h a - c) ^ 2 from rfl, mul_sum]
    refine sum_le_sum fun a _ => ?_
    have hFa : roughHarmonic Q (N / a) ≤ F := roughHarmonic_mono (Nat.div_le_self N a)
    have hz : 0 ≤ 1 / (a : ℝ) * (h a - c) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hFa hz]
  set S : ℕ → ℝ := fun a => ∑ b ∈ roughInterval Q (N / a), 1 / (b : ℝ) * (y (a * b) - c) ^ 2
  have hS0 : ∀ a, 0 ≤ S a := fun a => sum_nonneg fun b _ => by positivity
  have hA2 : ∑ a ∈ (smoothSet Q N).filter (fun a => ¬ a ≤ X),
      1 / (a : ℝ) * (roughHarmonic Q (N / a) * (h a - c) ^ 2) ≤
        1 / L * ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) * Real.log a * S a := by
    rw [mul_sum]
    calc _ ≤ ∑ a ∈ (smoothSet Q N).filter (fun a => ¬ a ≤ X),
          1 / L * (1 / (a : ℝ) * Real.log a * S a) := by
          refine sum_le_sum fun a ha => ?_
          have hXa : X < a := not_le.mp (mem_filter.mp ha).2
          have hJ : roughHarmonic Q (N / a) * (h a - c) ^ 2 ≤ S a := by
            have := sum_mul_sq_wMean_sub_le (s := roughInterval Q (N / a))
              (w := fun b : ℕ => 1 / (b : ℝ)) (v := fun b => y (a * b)) (fun b _ => by positivity) c
            exact this
          have hla : L ≤ Real.log a := Real.log_le_log (by positivity) (by exact_mod_cast hXa.le)
          have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
          have h1 : S a ≤ Real.log a / L * S a := by
            have : 1 ≤ Real.log a / L := by rw [le_div_iff₀ hL0]; linarith
            nlinarith [hS0 a]
          calc 1 / (a : ℝ) * (roughHarmonic Q (N / a) * (h a - c) ^ 2) ≤ 1 / (a : ℝ) * S a :=
                mul_le_mul_of_nonneg_left hJ (by positivity)
            _ ≤ 1 / (a : ℝ) * (Real.log a / L * S a) := mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = 1 / L * (1 / (a : ℝ) * Real.log a * S a) := by ring
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun a ha _ => by
          have := Real.log_natCast_nonneg a
          have := hS0 a
          positivity
  have hhalo : ∑ a ∈ smoothSet Q N, 1 / (a : ℝ) * Real.log a * S a ≤ 2 * DS + 2 * M * W :=
    sum_log_mul_fibre_le Q N y c
  have hE := roughHarmonic_mul_smoothEnergy_le (Q := Q) (show 1 ≤ X by omega) hXN hη y
  have hFsv : g₁ * (F * smoothVar Q X h) ≤ F / roughHarmonic Q (N / X) *
      ((1 + η) * DS + (1 + 1 / η) * (8 * logSum Q / roughHarmonic Q (N / X)) * U) := by
    calc g₁ * (F * smoothVar Q X h) = F * (g₁ * smoothVar Q X h) := by ring
      _ ≤ F * smoothEnergy Q X h := mul_le_mul_of_nonneg_left hA hF0
      _ ≤ _ := hE
  have hW2 : (1 - 2 * M / L) * W ≤ U + F * smoothVar Q X h + 2 / L * DS := by
    have h1 : W ≤ U + F * smoothVar Q X h + 1 / L * (2 * DS + 2 * M * W) := by
      have := mul_le_mul_of_nonneg_left hhalo (show 0 ≤ 1 / L by positivity)
      linarith
    have e : 1 / L * (2 * DS + 2 * M * W) = 2 / L * DS + 2 * M / L * W := by ring
    rw [e] at h1
    linarith
  have hM0 : 0 ≤ 1 - 2 * M / L := by
    rw [sub_nonneg, div_le_one hL0]; exact hL
  calc g₁ * ((1 - 2 * M / L) * W) ≤ g₁ * (U + F * smoothVar Q X h + 2 / L * DS) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hg₁.le
    _ = g₁ * U + g₁ * (F * smoothVar Q X h) + 2 * g₁ / L * DS := by ring
    _ ≤ _ := by linarith [hFsv]

/-! ### 7. The gap -/

/-- The arithmetic of the final step: the two-scale inequality with its parameters in range gives
`(2 log 2 − ε) Var ≤ D_S + D_L`. -/
theorem gap_of_two_scale {ε g₁ τ κ L M V U DS DL ρ c : ℝ} (hε : 0 < ε)
    (hεl : ε < 2 * Real.log 2) (hg₁ : g₁ = 2 * Real.log 2 - ε / 2) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 2)
    (hτε : τ ≤ ε / 24) (hML : 2 * M / L ≤ τ) (h2L : 2 / L ≤ τ) (hV0 : 0 ≤ V)
    (hU0 : 0 ≤ U) (hDS0 : 0 ≤ DS) (hDL0 : 0 ≤ DL) (hρ : ρ ≤ 1 + τ) (hc : ρ * c ≤ g₁)
    (hκ : κ ≤ 1 / 8) (hU : U ≤ κ * DL)
    (hcore : g₁ * ((1 - 2 * M / L) * V) ≤ g₁ * U + ρ * ((1 + τ) * DS + c * U) + 2 * g₁ / L * DS) :
    (2 * Real.log 2 - ε) * V ≤ DS + DL := by
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hg₁0 : 0 < g₁ := by rw [hg₁]; linarith
  have hg0 : 0 < 2 * Real.log 2 - ε := by linarith
  have hA : g₁ * (1 - τ) * V ≤ g₁ * DL / 4 + ((1 + τ) ^ 2 + g₁ * τ) * DS := by
    have e1 : g₁ * (1 - τ) * V ≤ g₁ * ((1 - 2 * M / L) * V) := by
      have : (1 - τ) * V ≤ (1 - 2 * M / L) * V := mul_le_mul_of_nonneg_right (by linarith) hV0
      calc g₁ * (1 - τ) * V = g₁ * ((1 - τ) * V) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this hg₁0.le
    have e3 : ρ * (1 + τ) * DS ≤ (1 + τ) ^ 2 * DS := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρ (by linarith)) hDS0
    have e4 : ρ * c * U ≤ g₁ * U := mul_le_mul_of_nonneg_right hc hU0
    have e5 : 2 * g₁ / L * DS ≤ g₁ * τ * DS := by
      rw [show 2 * g₁ / L = g₁ * (2 / L) by ring]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2L hg₁0.le) hDS0
    have e6 : U ≤ DL / 8 := by
      have := mul_le_mul_of_nonneg_right hκ hDL0
      linarith
    have e7 := mul_le_mul_of_nonneg_left e6 hg₁0.le
    calc g₁ * (1 - τ) * V ≤ g₁ * ((1 - 2 * M / L) * V) := e1
      _ ≤ _ := hcore
      _ = g₁ * U + (ρ * (1 + τ) * DS + ρ * c * U) + 2 * g₁ / L * DS := by ring
      _ ≤ g₁ * U + ((1 + τ) ^ 2 * DS + g₁ * U) + g₁ * τ * DS :=
          add_le_add (add_le_add le_rfl (add_le_add e3 e4)) e5
      _ ≤ g₁ * DL / 4 + ((1 + τ) ^ 2 + g₁ * τ) * DS := by linarith
  have hnum : (2 * Real.log 2 - ε) * ((1 + τ) ^ 2 + g₁ * τ) ≤ g₁ * (1 - τ) := by
    have hb : 2 * (2 * Real.log 2 - ε) + (2 * Real.log 2 - ε) * τ +
        (2 * Real.log 2 - ε) * g₁ + g₁ ≤ 12 := by
      have h1 : (2 * Real.log 2 - ε) * τ ≤ 1 := by nlinarith
      have h2 : (2 * Real.log 2 - ε) * g₁ ≤ 2 := by rw [hg₁]; nlinarith
      rw [hg₁] at h2 ⊢
      linarith
    have hb' := mul_le_mul_of_nonneg_left hb hτ0.le
    have e : (2 * Real.log 2 - ε) * ((1 + τ) ^ 2 + g₁ * τ) = (2 * Real.log 2 - ε) +
        τ * (2 * (2 * Real.log 2 - ε) + (2 * Real.log 2 - ε) * τ + (2 * Real.log 2 - ε) * g₁) := by
      ring
    rw [e]
    have e' : g₁ * (1 - τ) = (2 * Real.log 2 - ε) + ε / 2 - τ * g₁ := by rw [hg₁]; ring
    rw [e']
    nlinarith
  have hg4 : (2 * Real.log 2 - ε) / 4 ≤ 1 - τ := by linarith
  have hpos : 0 < g₁ * (1 - τ) := mul_pos hg₁0 (by linarith)
  refine le_of_mul_le_mul_left ?_ hpos
  calc g₁ * (1 - τ) * ((2 * Real.log 2 - ε) * V) = (2 * Real.log 2 - ε) * (g₁ * (1 - τ) * V) := by
        ring
    _ ≤ (2 * Real.log 2 - ε) * (g₁ * DL / 4 + ((1 + τ) ^ 2 + g₁ * τ) * DS) :=
        mul_le_mul_of_nonneg_left hA hg0.le
    _ = g₁ * ((2 * Real.log 2 - ε) / 4) * DL + (2 * Real.log 2 - ε) * ((1 + τ) ^ 2 + g₁ * τ) * DS := by
        ring
    _ ≤ g₁ * (1 - τ) * DL + g₁ * (1 - τ) * DS :=
        add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg4 hg₁0.le) hDL0)
          (mul_le_mul_of_nonneg_right hnum hDS0)
    _ = g₁ * (1 - τ) * (DS + DL) := by ring

/-- A prime cutoff `Q ≥ 2` with `K/log Q ≤ 1/8`. -/
theorem exists_cutoff_div_log_le (K : ℝ) : ∃ Q : ℕ, 2 ≤ Q ∧ K / Real.log Q ≤ 1 / 8 := by
  refine ⟨⌈Real.exp (8 * K)⌉₊ + 2, by omega, ?_⟩
  have hQ : Real.exp (8 * K) ≤ ((⌈Real.exp (8 * K)⌉₊ + 2 : ℕ) : ℝ) := by
    have := Nat.le_ceil (Real.exp (8 * K))
    push_cast
    linarith
  have hlQ0 : 0 < Real.log ((⌈Real.exp (8 * K)⌉₊ + 2 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < ⌈Real.exp (8 * K)⌉₊ + 2 by omega))
  have h3 : 8 * K ≤ Real.log ((⌈Real.exp (8 * K)⌉₊ + 2 : ℕ) : ℝ) := by
    calc 8 * K = Real.log (Real.exp (8 * K)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) hQ
  rw [div_le_iff₀ hlQ0]
  linarith

/-- A horizon `X ≥ X₀` with `2M/log X ≤ τ`, `2/log X ≤ τ` and `2M ≤ log X`. -/
theorem exists_horizon {M τ : ℝ} (hM : 0 ≤ M) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (X₀ : ℕ) :
    ∃ X : ℕ, X₀ ≤ X ∧ 2 ≤ X ∧ 2 * M / Real.log X ≤ τ ∧ 2 / Real.log X ≤ τ ∧
      2 * M ≤ Real.log X := by
  set X := max X₀ (⌈Real.exp (2 * (M + 1) / τ)⌉₊ + 2)
  have hX2 : 2 ≤ X := le_trans (by omega) (le_max_right _ _)
  have hL0 : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have h1 : Real.exp (2 * (M + 1) / τ) ≤ X := by
    have := Nat.le_ceil (Real.exp (2 * (M + 1) / τ))
    have h2 : ((⌈Real.exp (2 * (M + 1) / τ)⌉₊ + 2 : ℕ) : ℝ) ≤ X := by
      exact_mod_cast le_max_right _ _
    push_cast at h2
    linarith
  have h3 : 2 * (M + 1) / τ ≤ Real.log X := by
    calc _ = Real.log (Real.exp (2 * (M + 1) / τ)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) h1
  rw [div_le_iff₀ hτ0] at h3
  refine ⟨X, le_max_left _ _, hX2, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hL0]; nlinarith
  · rw [div_le_iff₀ hL0]; nlinarith
  · nlinarith

/-- The rough mass beyond a fixed horizon grows: `F_Q(N/X) ≥ G₀` eventually in `N`. -/
theorem eventually_le_roughHarmonic_div {Q X : ℕ} (hQ : 1 ≤ Q) (hX : 1 ≤ X) (G₀ : ℝ) :
    ∃ N₀ : ℕ, X ≤ N₀ ∧ ∀ N, N₀ ≤ N → G₀ ≤ roughHarmonic Q (N / X) := by
  set m := RHTower.mertensPrimeProduct (Q - 1)
  have hm : 0 < m := mertensPrimeProduct_pos _
  set T := ⌈Real.exp (G₀ / m)⌉₊
  refine ⟨X * (T + 1), Nat.le_mul_of_pos_right X (by omega), fun N hN => ?_⟩
  have hNX : T + 1 ≤ N / X := (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hN)
  have h1 := mertensPrimeProduct_mul_log_le_roughHarmonic (Q - 1) (N / X)
  rw [show Q - 1 + 1 = Q by omega] at h1
  have h2 : Real.exp (G₀ / m) ≤ ((N / X : ℕ) : ℝ) + 1 := by
    have := Nat.le_ceil (Real.exp (G₀ / m))
    have h3 : ((T + 1 : ℕ) : ℝ) ≤ ((N / X : ℕ) : ℝ) := by exact_mod_cast hNX
    push_cast at h3
    linarith
  have h4 : G₀ / m ≤ Real.log (((N / X : ℕ) : ℝ) + 1) := by
    calc G₀ / m = Real.log (Real.exp (G₀ / m)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) h2
  rw [div_le_iff₀ hm] at h4
  linarith

/-- The mass ratio `F(N)/F(N/X)` and the commutation coefficient, once `F(N/X)` is large. -/
theorem ratio_bounds {F G L τ lS g₁ : ℝ} (hτ0 : 0 < τ) (hg₁ : 0 < g₁) (hlS : 0 ≤ lS)
    (hL : 0 ≤ L) (hFG : F ≤ G + (1 + L))
    (hG : (1 + L) / τ + 16 * (1 + 1 / τ) * lS / g₁ ≤ G) (hτ1 : τ ≤ 1 / 2) :
    F / G ≤ 1 + τ ∧ F / G * ((1 + 1 / τ) * (8 * lS / G)) ≤ g₁ := by
  have hA : 0 < (1 + L) / τ := by positivity
  have hB : 0 ≤ 16 * (1 + 1 / τ) * lS / g₁ := by positivity
  have hG0 : 0 < G := by linarith
  have h1 : 1 + L ≤ G * τ := (div_le_iff₀ hτ0).mp (by linarith)
  have h2 : 16 * (1 + 1 / τ) * lS ≤ G * g₁ := (div_le_iff₀ hg₁).mp (by linarith)
  have hρ : F / G ≤ 1 + τ := by
    rw [div_le_iff₀ hG0]
    linarith
  refine ⟨hρ, ?_⟩
  have hc : (1 + 1 / τ) * (8 * lS / G) ≤ g₁ / 2 := by
    rw [show (1 + 1 / τ) * (8 * lS / G) = 16 * (1 + 1 / τ) * lS / (2 * G) by field_simp; ring,
      div_le_iff₀ (by positivity)]
    linarith
  have hc0 : 0 ≤ (1 + 1 / τ) * (8 * lS / G) := by positivity
  have := mul_le_mul hρ hc hc0 (by linarith)
  nlinarith

/-- **The multiplicative walk has Poincaré constant `2 log 2`.** For every `ε > 0`, eventually in
`N`, `(2 log 2 − ε) Var_{1/n, [1, N]}(√n x) ≤ D_N(x)` for every `x`. Fix `Q` with `K/log Q ≤ 1/8`
(tensorization of the rough parts), a horizon `X` where the `Q`-smooth chain has gap
`2 log 2 − ε/2`, and `N` with `F_Q(N/X)` large; then `two_scale_le`. -/
theorem eventually_mul_harmonicVar_le_poleDefect {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ x : ℕ → ℝ,
      (2 * Real.log 2 - ε) * harmonicVar 0 N (poleGauge x) ≤ poleDefect N x := by
  by_cases hεl : 2 * Real.log 2 ≤ ε
  · exact ⟨0, fun N _ x => le_trans (mul_nonpos_of_nonpos_of_nonneg (by linarith)
      (harmonicVar_nonneg _ _ _)) (poleDefect_nonneg N x)⟩
  replace hεl := not_le.mp hεl
  have hg₁ : 0 < 2 * Real.log 2 - ε / 2 := by linarith
  have hτ0 : 0 < min (1 / 2 : ℝ) (ε / 24) := lt_min (by norm_num) (by linarith)
  obtain ⟨K, hK, hKt⟩ := exists_harmonicVar_le_glauberForm_rough
  obtain ⟨Q, hQ2, hκ⟩ := exists_cutoff_div_log_le K
  obtain ⟨X₀, hX₀⟩ := eventually_smoothVar_le_smoothEnergy Q (show 0 < ε / 2 by linarith)
  obtain ⟨X, hXX₀, hX2, hML, h2L, h2ML⟩ := exists_horizon (ladderConstant_nonneg Q) hτ0
    (le_trans (min_le_left _ _) (by norm_num)) X₀
  obtain ⟨N₀, hXN₀, hN₀⟩ := eventually_le_roughHarmonic_div (show 1 ≤ Q by omega)
    (show 1 ≤ X by omega) ((1 + Real.log X) / min (1 / 2 : ℝ) (ε / 24) +
      16 * (1 + 1 / min (1 / 2 : ℝ) (ε / 24)) * logSum Q / (2 * Real.log 2 - ε / 2))
  refine ⟨N₀, fun N hN x => ?_⟩
  have hXN : X ≤ N := hXN₀.trans hN
  have hL0 : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  obtain ⟨hρ, hc⟩ := ratio_bounds (F := roughHarmonic Q N) (G := roughHarmonic Q (N / X)) hτ0 hg₁
    (logSum_nonneg Q) hL0.le
    (by have := roughHarmonic_sub_div_le Q N (show 1 ≤ X by omega); linarith) (hN₀ N hN)
    (min_le_left _ _)
  have hcore := two_scale_le hX2 hXN hg₁ hτ0 (poleGauge x) (hX₀ X hXX₀ _) h2ML
  have hU := sum_fibreVar_le hK.le hKt hQ2 N (poleGauge x)
  have hVW : harmonicVar 0 N (poleGauge x) ≤ ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (poleGauge x n -
      wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) (fibreMean Q N (poleGauge x))) ^ 2 := by
    rw [harmonicVar, roughInterval_zero]
    exact wVar_le (fun n _ => by positivity) _
  rw [← walkEnergy_small_add_large Q N x]
  have hW := gap_of_two_scale hε hεl rfl hτ0 (min_le_left _ _) (min_le_right _ _) hML h2L
    (sum_nonneg fun n _ => by positivity)
    (sum_nonneg fun a _ => mul_nonneg (by positivity) (harmonicVar_nonneg _ _ _))
    (walkEnergy_nonneg _ _ _) (walkEnergy_nonneg _ _ _) hρ hc hκ hU hcore
  exact (mul_le_mul_of_nonneg_left hVW (by linarith)).trans hW

open GaloisForLFunctions.ArithmeticElectrostatics in
/-- **The prime form is at most `log N − γ − 2 log 2` below its pole.** For every `ε > 0`,
eventually in `N`, every `x` orthogonal to `n^{−1/2}` satisfies
`P_N(x) ≤ (log N − γ − 2 log 2 + ε)|x|²`. -/
theorem eventually_atomicWeilForm_le_two_log_two {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ x : ℕ → ℝ, ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 →
      atomicWeilForm N x ≤
        (Real.log N - Real.eulerMascheroniConstant - 2 * Real.log 2 + ε) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  set ε₁ := min (1 / 2 : ℝ) (ε / 6)
  have hε₁ : 0 < ε₁ := lt_min (by norm_num) (by linarith)
  have hε₁2 : ε₁ ≤ 1 / 2 := min_le_left _ _
  have hε₁6 : ε₁ ≤ ε / 6 := min_le_right _ _
  obtain ⟨N₁, hN₁⟩ := eventually_atomicWeilForm_add_poleDefect_le hε₁
  obtain ⟨N₂, hN₂⟩ := eventually_mul_harmonicVar_le_poleDefect (show 0 < ε / 2 by linarith)
  refine ⟨max N₁ N₂, fun N hN x hx => ?_⟩
  have h1 := hN₁ N (le_of_max_le_left hN) x
  have h2 := hN₂ N (le_of_max_le_right hN) x
  rw [harmonicVar_poleGauge_eq hx] at h2
  have hS : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 1 - ε₁ by linarith)
  have h4 : ε₁ * (1 + 2 * Real.log 2) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ ε / 2 * ∑ n ∈ Icc 1 N, x n ^ 2 :=
    mul_le_mul_of_nonneg_right (by nlinarith) hS
  have h5 : 0 ≤ ε₁ * (ε / 2) * ∑ n ∈ Icc 1 N, x n ^ 2 := by positivity
  nlinarith

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
