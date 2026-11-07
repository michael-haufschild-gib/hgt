import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheHalfScaleOfTheRate
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheLedgerIsBlindToTheLiouvilleTwin
import GaloisForLFunctions.RigidArithmeticOfCuts.TheLiouvilleChebyshevIdentity
import GaloisForLFunctions.RHTower.MoebiusApproximantResidual

/-!
# A producer bounds the Mertens function

Read a producer against a bounded weight `a`, with partial sums `A(n)`. Its multiplicity is `m` on the window and
nonnegative elsewhere, so

`m (A(n) − A(⌊n/B⌋)) = ledger(a) − Σ_{d ≤ n} a(d) (g − m 1_{[1,B)})(⌊n/d⌋)`.

The last sum is at most `n T + 2 w √n`, where `T` is the excess: above `√n` the fibres of `d ↦ ⌊n/d⌋` have the pronic size,
and below `√n` the peak pays. Summing over the scales `n/Bʲ`, the factor `1/(1 − 1/B)` turns `T/m` into the rate exactly.

The ledger of `μ` is the constant `−w`, because `Σ_d μ(d) ⌊N/d⌋ = 1`. Hence

`|M(n)| ≤ ε n + 12 (w/m) √n + K`,

with constant `1` in front of the rate, and with no zero of `ζ` and no analysis in the proof. The ledger of `λ` is
`Σ_k c(k) ⌊√(n/k)⌋`, so the same rate bounds the Liouville sum `L(n)`.

So **a certificate of a rate is a proof of a bound on `M(x)`**, in three lines. No family of stencils can certify a rate
independently of the Mertens function: past `n ≍ K² log⁶ K`, every producer of rate `ε` has `|M(n)| ≤ 3 ε n`.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

variable {c : ℕ →₀ ℤ} {m B : ℕ}

/-- The multiplicity above its window: `g − m 1_{r < B}`. -/
def producerSlack (c : ℕ →₀ ℤ) (m B r : ℕ) : ℝ :=
  (stepWeight c r : ℝ) - (if r < B then (m : ℝ) else 0)

namespace IsProducer

theorem producerSlack_nonneg (hP : IsProducer c m B) {r : ℕ} (hr : 1 ≤ r) :
    0 ≤ producerSlack c m B r := by
  rw [producerSlack]
  split_ifs with h
  · have : (m : ℝ) ≤ stepWeight c r := by exact_mod_cast hP.window r (mem_Ico.mpr ⟨hr, h⟩)
    linarith
  · have : (0 : ℝ) ≤ stepWeight c r := by exact_mod_cast hP.nonneg r
    linarith

theorem producerSlack_le_peak (hP : IsProducer c m B) (r : ℕ) :
    producerSlack c m B r ≤ peak c := by
  have h : (stepWeight c r : ℝ) ≤ peak c := by exact_mod_cast hP.stepWeight_le_peak r
  have h0 : (0 : ℝ) ≤ if r < B then (m : ℝ) else 0 := by
    split_ifs <;> positivity
  rw [producerSlack]
  linarith

/-- The slack on `[1, Q]`, weighted by the pronic density, is at most the excess. -/
theorem sum_Icc_producerSlack_le (hP : IsProducer c m B) (Q : ℕ) :
    ∑ r ∈ Icc 1 Q, producerSlack c m B r / ((r : ℝ) * ((r : ℝ) + 1)) ≤ excess c m B := by
  have hre : ∑ r ∈ Icc 1 Q, producerSlack c m B r / ((r : ℝ) * ((r : ℝ) + 1)) =
      ∑ j ∈ range Q, excessTerm m B c j := by
    induction Q with
    | zero => simp
    | succ Q ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih, excessTerm, producerSlack]
      push_cast
      congr 2
      ring
  rw [hre]
  exact sum_le_hasSum _ (fun j _ => hP.excessTerm_nonneg j) hP.hasSum_excess

end IsProducer

/-- `n/k < ⌊n/k⌋ + 1`. -/
private lemma div_lt_natDiv_add_one (n k : ℕ) : (n : ℝ) / k < ((n / k : ℕ) : ℝ) + 1 := by
  have h := Nat.lt_floor_add_one ((n : ℝ) / k)
  rwa [Nat.floor_div_eq_div] at h

/-- The fibre of `d ↦ ⌊n/d⌋` over `r` has pronic size, up to one point. -/
private lemma card_fibre_le {s : Finset ℕ} (hs : ∀ d ∈ s, 0 < d) (n : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    ((s.filter fun d => n / d = r).card : ℝ) ≤ (n : ℝ) / ((r : ℝ) * ((r : ℝ) + 1)) + 1 := by
  have hsub : s.filter (fun d => n / d = r) ⊆ Ioc (n / (r + 1)) (n / r) := by
    intro d hd
    obtain ⟨hds, hdr⟩ := mem_filter.mp hd
    have hd0 := hs d hds
    refine mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul (by omega)).mpr ?_, (Nat.le_div_iff_mul_le hr).mpr ?_⟩
    · have := Nat.lt_mul_div_succ n hd0
      rw [hdr] at this
      exact this
    · have := Nat.mul_div_le n d
      rw [hdr] at this
      exact this
  have hcard := card_le_card hsub
  rw [Nat.card_Ioc] at hcard
  have hle : n / (r + 1) ≤ n / r := Nat.div_le_div_left (by omega) hr
  have hcast : ((s.filter fun d => n / d = r).card : ℝ) ≤ ((n / r : ℕ) : ℝ) - ((n / (r + 1) : ℕ) : ℝ) := by
    have : ((s.filter fun d => n / d = r).card : ℝ) ≤ ((n / r - n / (r + 1) : ℕ) : ℝ) := by
      exact_mod_cast hcard
    rwa [Nat.cast_sub hle] at this
  have h1 : ((n / r : ℕ) : ℝ) ≤ (n : ℝ) / r := Nat.cast_div_le
  have h2 := div_lt_natDiv_add_one n (r + 1)
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hval : (n : ℝ) / r - (n : ℝ) / ((r + 1 : ℕ) : ℝ) = (n : ℝ) / ((r : ℝ) * ((r : ℝ) + 1)) := by
    push_cast
    field_simp
    ring
  linarith

/-- **The slack of a producer along floors.** `Σ_{d ≤ n} (g − m 1_{[1,B)})(⌊n/d⌋) ≤ n T + 2 w √n`. -/
theorem IsProducer.sum_producerSlack_le (hP : IsProducer c m B) (n : ℕ) :
    ∑ d ∈ Ioc 0 n, producerSlack c m B (n / d) ≤
      (n : ℝ) * excess c m B + 2 * (peak c : ℝ) * √(n : ℝ) := by
  classical
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = Nat.sqrt n := ⟨_, rfl⟩
  have hQn : Q ≤ n := hQ ▸ Nat.sqrt_le_self n
  have hw0 : (0 : ℝ) ≤ peak c := by
    have h : (m : ℝ) ≤ peak c := by exact_mod_cast hP.le_peak
    have := hP.m_pos
    linarith
  have hQR : (Q : ℝ) ≤ √(n : ℝ) := hQ ▸ Real.nat_sqrt_le_real_sqrt
  have hfirst : ∑ d ∈ Ioc 0 Q, producerSlack c m B (n / d) ≤ (Q : ℝ) * peak c := by
    have h := sum_le_card_nsmul (Ioc 0 Q) (fun d => producerSlack c m B (n / d)) (peak c : ℝ)
      fun d _ => hP.producerSlack_le_peak _
    simpa [nsmul_eq_mul] using h
  have hmaps : ∀ d ∈ Ioc Q n, n / d ∈ Icc 1 Q := by
    intro d hd
    obtain ⟨h1, h2⟩ := mem_Ioc.mp hd
    have hd0 : 0 < d := by omega
    refine mem_Icc.mpr ⟨(Nat.one_le_div_iff hd0).mpr h2, ?_⟩
    have hlt : n < (Q + 1) * d := by
      have h3 : n < (Q + 1) * (Q + 1) := by
        have := Nat.lt_succ_sqrt n
        rw [← hQ] at this
        exact this
      exact lt_of_lt_of_le h3 (Nat.mul_le_mul_left _ h1)
    have := (Nat.div_lt_iff_lt_mul hd0).mpr hlt
    omega
  have hsecond : ∑ d ∈ Ioc Q n, producerSlack c m B (n / d) ≤
      (n : ℝ) * excess c m B + (Q : ℝ) * peak c := by
    rw [← sum_fiberwise_of_maps_to hmaps]
    have hinner : ∀ r ∈ Icc 1 Q, ∑ d ∈ (Ioc Q n).filter (fun d => n / d = r),
        producerSlack c m B (n / d) ≤
          (n : ℝ) * (producerSlack c m B r / ((r : ℝ) * ((r : ℝ) + 1))) + peak c := by
      intro r hr
      have hr1 := (mem_Icc.mp hr).1
      have hrR : (0 : ℝ) < r := by exact_mod_cast hr1
      have hconst : ∑ d ∈ (Ioc Q n).filter (fun d => n / d = r), producerSlack c m B (n / d) =
          ((Ioc Q n).filter fun d => n / d = r).card * producerSlack c m B r := by
        rw [sum_congr rfl fun d hd => by rw [(mem_filter.mp hd).2], sum_const, nsmul_eq_mul]
      have hs0 := hP.producerSlack_nonneg hr1
      have hcard := card_fibre_le (s := Ioc Q n) (fun d hd => by
        have := (mem_Ioc.mp hd).1
        omega) n hr1
      rw [hconst]
      calc _ ≤ ((n : ℝ) / ((r : ℝ) * ((r : ℝ) + 1)) + 1) * producerSlack c m B r :=
            mul_le_mul_of_nonneg_right hcard hs0
        _ = (n : ℝ) * (producerSlack c m B r / ((r : ℝ) * ((r : ℝ) + 1))) +
            producerSlack c m B r := by ring
        _ ≤ _ := by linarith [hP.producerSlack_le_peak r]
    refine (sum_le_sum hinner).trans ?_
    rw [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
    have := mul_le_mul_of_nonneg_left (hP.sum_Icc_producerSlack_le Q) (Nat.cast_nonneg n)
    linarith
  rw [← sum_Ioc_consecutive _ (Nat.zero_le Q) hQn]
  have h3 : (Q : ℝ) * peak c ≤ √(n : ℝ) * peak c := mul_le_mul_of_nonneg_right hQR hw0
  linarith

/-- **The window law for a bounded weight.** -/
theorem IsProducer.mul_abs_sum_Ioc_le (hP : IsProducer c m B) {a : ℕ → ℝ} (ha : ∀ d, |a d| ≤ 1) (n : ℕ) :
    (m : ℝ) * |∑ d ∈ Ioc (n / B) n, a d| ≤
      |ledger c a n| + (n : ℝ) * excess c m B + 2 * (peak c : ℝ) * √(n : ℝ) := by
  have hB0 : 0 < B := by have := hP.two_le_B; omega
  have hdec : ledger c a n = ∑ d ∈ Ioc 0 n, a d * producerSlack c m B (n / d) +
      (m : ℝ) * ∑ d ∈ Ioc (n / B) n, a d := by
    have hle : n / B ≤ n := Nat.div_le_self n B
    have hwin : ∑ d ∈ Ioc 0 n, a d * (if n / d < B then (m : ℝ) else 0) =
        (m : ℝ) * ∑ d ∈ Ioc (n / B) n, a d := by
      rw [← sum_Ioc_consecutive _ (Nat.zero_le _) hle, mul_sum]
      have h1 : ∑ d ∈ Ioc 0 (n / B), a d * (if n / d < B then (m : ℝ) else 0) = 0 := by
        refine sum_eq_zero fun d hd => ?_
        obtain ⟨hd0, hdB⟩ := mem_Ioc.mp hd
        have : ¬ n / d < B := by
          rw [not_lt, Nat.le_div_iff_mul_le hd0]
          have := (Nat.le_div_iff_mul_le hB0).mp hdB
          rwa [mul_comm] at this
        simp [this]
      have h2 : ∑ d ∈ Ioc (n / B) n, a d * (if n / d < B then (m : ℝ) else 0) =
          ∑ d ∈ Ioc (n / B) n, (m : ℝ) * a d := by
        refine sum_congr rfl fun d hd => ?_
        obtain ⟨hd0, -⟩ := mem_Ioc.mp hd
        have hd1 : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hd0
        have : n / d < B := by
          rw [Nat.div_lt_iff_lt_mul hd1, mul_comm]
          exact (Nat.div_lt_iff_lt_mul hB0).mp hd0
        rw [if_pos this]
        ring
      rw [h1, h2, zero_add]
    rw [← hwin, ← sum_add_distrib, ledger]
    refine sum_congr rfl fun d _ => ?_
    rw [producerSlack]
    ring
  have hrest : |∑ d ∈ Ioc 0 n, a d * producerSlack c m B (n / d)| ≤
      ∑ d ∈ Ioc 0 n, producerSlack c m B (n / d) := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
    obtain ⟨hd0, hdn⟩ := mem_Ioc.mp hd
    have hs0 := hP.producerSlack_nonneg ((Nat.one_le_div_iff hd0).mpr hdn)
    rw [abs_mul, abs_of_nonneg hs0]
    exact mul_le_of_le_one_left hs0 (ha d)
  have hm := hP.m_pos
  have hval : (m : ℝ) * |∑ d ∈ Ioc (n / B) n, a d| =
      |ledger c a n - ∑ d ∈ Ioc 0 n, a d * producerSlack c m B (n / d)| := by
    rw [hdec, add_sub_cancel_left, abs_mul, abs_of_pos hm]
  rw [hval]
  have h1 := abs_sub (ledger c a n) (∑ d ∈ Ioc 0 n, a d * producerSlack c m B (n / d))
  have h2 := hP.sum_producerSlack_le n
  linarith

/-- `√⌊n/B⌋ ≤ ¾ √n` for `B ≥ 2`. -/
private lemma sqrt_div_le (n : ℕ) {B : ℕ} (hB : 2 ≤ B) : √((n / B : ℕ) : ℝ) ≤ 3 / 4 * √(n : ℝ) := by
  have hle : ((n / B : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
    have h1 : ((n / B : ℕ) : ℝ) ≤ (n : ℝ) / B := Nat.cast_div_le
    have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
    have h2 : (n : ℝ) / B ≤ (n : ℝ) / 2 := div_le_div_of_nonneg_left (Nat.cast_nonneg n) (by norm_num) hBR
    linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt hn0]
  nlinarith

/-- The arithmetic of one scale in the descent from `n` to `⌊n/B⌋`. -/
private lemma descent_step {ε d n q s s' Y K X T m : ℝ} (hε : 0 ≤ ε) (hm : 0 < m) (hd : d = 1 - 1 / B)
    (hB : (0 : ℝ) < B) (hq : q ≤ n / B) (hs : s' ≤ 3 / 4 * s) (hY : 0 ≤ Y) (hT : T = m * d * ε)
    (hstep : m * X ≤ n * T + Y * m * s) :
    ε * q + 4 * Y * s' + K + X ≤ ε * n + 4 * Y * s + K := by
  have hX : X ≤ n * (d * ε) + Y * s := by
    have h1 : m * X ≤ m * (n * (d * ε) + Y * s) := by
      calc m * X ≤ n * T + Y * m * s := hstep
        _ = _ := by rw [hT]; ring
    exact le_of_mul_le_mul_left h1 hm
  have h2 : ε * q ≤ ε * (n / B) := mul_le_mul_of_nonneg_left hq hε
  have h3 : 4 * Y * s' ≤ 4 * Y * (3 / 4 * s) := mul_le_mul_of_nonneg_left hs (by positivity)
  have h4 : ε * (n / B) + n * (d * ε) = ε * n := by
    rw [hd]
    field_simp
    ring
  linarith

/-- **A rate bounds every weight with a small ledger.** If `|a| ≤ 1` and `|ledger(a)| ≤ E √n` on `n ≥ K`, then
`|A(n)| ≤ ε n + 4 ((2 w + E)/m) √n + K`, with constant `1` on the rate. -/
theorem IsProducer.abs_sum_le_of_ledger (hP : IsProducer c m B) {K : ℕ} {a : ℕ → ℝ} (ha : ∀ d, |a d| ≤ 1)
    {E : ℝ} (hE0 : 0 ≤ E) (hE : ∀ n, K ≤ n → |ledger c a n| ≤ E * √(n : ℝ)) (n : ℕ) :
    |∑ d ∈ Ioc 0 n, a d| ≤ rate c m B * n +
      4 * ((2 * (peak c : ℝ) + E) / m) * √(n : ℝ) + K := by
  have hε := hP.rate_pos
  have hm := hP.m_pos
  have hB := hP.two_le_B
  have hBR : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hw0 : (0 : ℝ) ≤ peak c := by
    have h : (m : ℝ) ≤ peak c := by exact_mod_cast hP.le_peak
    linarith
  have hY : 0 ≤ (2 * (peak c : ℝ) + E) / m := by positivity
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < K ∨ n = 0
    · have hcard : |∑ d ∈ Ioc 0 n, a d| ≤ n := by
        refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun d _ => ha d).trans ?_)
        simp
      have hnK : (n : ℝ) ≤ K ∨ n = 0 := by
        rcases hn with h | h
        · exact Or.inl (by exact_mod_cast h.le)
        · exact Or.inr h
      have h0 : 0 ≤ rate c m B * n := by positivity
      have h1 : 0 ≤ 4 * ((2 * (peak c : ℝ) + E) / m) * √(n : ℝ) := by positivity
      have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      rcases hnK with h | h
      · linarith
      · subst h
        simp at hcard ⊢
    · push Not at hn
      obtain ⟨hnK, hn0⟩ := hn
      have hlt : n / B < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by omega)
      have hIH := ih _ hlt
      have hsplit := sum_Ioc_consecutive (fun d => a d) (Nat.zero_le (n / B)) (Nat.div_le_self n B)
      have hX := hP.mul_abs_sum_Ioc_le ha n
      have hL := hE n hnK
      have hqle : ((n / B : ℕ) : ℝ) ≤ (n : ℝ) / B := Nat.cast_div_le
      have hstep : (m : ℝ) * |∑ d ∈ Ioc (n / B) n, a d| ≤
          (n : ℝ) * excess c m B + ((2 * (peak c : ℝ) + E) / m) * m * √(n : ℝ) := by
        have : ((2 * (peak c : ℝ) + E) / m) * m = 2 * (peak c : ℝ) + E := by field_simp
        rw [this]
        nlinarith
      have hmain := descent_step (B := B) (K := (K : ℝ)) hε.le hm rfl hBR hqle (sqrt_div_le n hB) hY
        hP.excess_eq_rate hstep
      rw [← hsplit]
      calc _ ≤ |∑ d ∈ Ioc 0 (n / B), a d| + |∑ d ∈ Ioc (n / B) n, a d| := abs_add_le _ _
        _ ≤ _ := by linarith

/-- The ledger of a stencil, letter by letter. -/
theorem ledger_eq_sum_letters (c : ℕ →₀ ℤ) (a : ℕ → ℝ) (n : ℕ) :
    ledger c a n = ∑ k ∈ c.support, (c k : ℝ) * ∑ d ∈ Ioc 0 n, a d * (((n / k) / d : ℕ) : ℝ) := by
  rw [ledger]
  have hterm : ∀ d, a d * (stepWeight c (n / d) : ℝ) =
      ∑ k ∈ c.support, (c k : ℝ) * (a d * (((n / k) / d : ℕ) : ℝ)) := by
    intro d
    rw [stepWeight, Int.cast_sum, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    have hdiv : n / d / k = n / k / d := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
    rw [hdiv, Int.cast_mul, Int.cast_natCast]
    ring
  simp_rw [hterm, mul_sum]
  rw [sum_comm]

/-- **The ledger of `μ` is the peak.** -/
theorem IsProducer.ledger_moebius (hP : IsProducer c m B) {K : ℕ} (hK : AlphabetLE c K) {n : ℕ}
    (hn : K ≤ n) : ledger c (fun d => (ArithmeticFunction.moebius d : ℝ)) n = -(peak c : ℝ) := by
  rw [ledger_eq_sum_letters, peak]
  push_cast
  rw [neg_neg]
  refine sum_congr rfl fun k hk => ?_
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
    subst h
    exact Finsupp.mem_support_iff.mp hk hP.zero
  have hkn : k ≤ n := (hK k hk).trans hn
  have hN : 1 ≤ n / k := (Nat.one_le_div_iff hk0).mpr hkn
  have hset : Ioc 0 n = Icc 1 n := by
    ext d
    simp only [mem_Ioc, mem_Icc]
    omega
  have h := RHTower.moebius_floor_summatory_le hN (Nat.div_le_self n k)
  rw [hset, h, mul_one]

/-- **A rate bounds the Mertens function.** For all `n`, `|M(n)| ≤ ε n + 12 (w/m) √n + K`. -/
theorem IsProducer.abs_mertens_le (hP : IsProducer c m B) {K : ℕ} (hK : AlphabetLE c K) (hK1 : 1 ≤ K) (n : ℕ) :
    |mertens n| ≤ rate c m B * n + 12 * peakRatio c m * √(n : ℝ) + K := by
  have hw0 : (0 : ℝ) ≤ peak c := by
    have h : (m : ℝ) ≤ peak c := by exact_mod_cast hP.le_peak
    have := hP.m_pos
    linarith
  have h := hP.abs_sum_le_of_ledger (K := K) (a := fun d => (ArithmeticFunction.moebius d : ℝ))
    (E := peak c) (fun d => by
      have := ArithmeticFunction.abs_moebius_le_one (n := d)
      exact_mod_cast this) hw0 (fun n hn => by
      rw [hP.ledger_moebius hK hn, abs_neg, abs_of_nonneg hw0]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hK1.trans hn
      have hs : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.mpr hn1
      exact le_mul_of_one_le_right hw0 hs) n
  have hval : 4 * ((2 * (peak c : ℝ) + peak c) / m) = 12 * peakRatio c m := by
    rw [peakRatio]
    ring
  rw [hval] at h
  exact h

/-- The ledger of `λ` reads the number of squares. -/
theorem ledger_liouville (c : ℕ →₀ ℤ) (hc0 : c 0 = 0) (n : ℕ) :
    ledger c (fun d => (ArithmeticFunction.liouville d : ℝ)) n =
      ∑ k ∈ c.support, (c k : ℝ) * (Nat.sqrt (n / k) : ℝ) := by
  rw [ledger_eq_sum_letters]
  refine sum_congr rfl fun k hk => ?_
  congr 1
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
    subst h
    exact Finsupp.mem_support_iff.mp hk hc0
  obtain ⟨N, hN⟩ : ∃ N, N = n / k := ⟨_, rfl⟩
  have hNn : N ≤ n := hN ▸ Nat.div_le_self n k
  rw [← hN]
  have hsq := RigidArithmeticOfCuts.sum_Ioc_isSquare N
  have hswap := RigidArithmeticOfCuts.sum_Ioc_sum_divisors
    (fun _ e => (ArithmeticFunction.liouville e : ℝ)) N
  have hleft : ∑ m ∈ Ioc 0 N, ∑ d ∈ m.divisors, (ArithmeticFunction.liouville (m / d) : ℝ) =
      (Nat.sqrt N : ℝ) := by
    rw [← hsq]
    refine sum_congr rfl fun j hj => ?_
    have hj0 : j ≠ 0 := by
      have := (mem_Ioc.mp hj).1
      omega
    rw [Nat.sum_div_divisors j fun d => (ArithmeticFunction.liouville d : ℝ)]
    exact RigidArithmeticOfCuts.sum_divisors_liouville hj0
  have hright : ∑ e ∈ Ioc 0 N, ∑ _d ∈ Ioc 0 (N / e), (ArithmeticFunction.liouville e : ℝ) =
      ∑ d ∈ Ioc 0 n, (ArithmeticFunction.liouville d : ℝ) * ((N / d : ℕ) : ℝ) := by
    have hext : ∑ d ∈ Ioc 0 n, (ArithmeticFunction.liouville d : ℝ) * ((N / d : ℕ) : ℝ) =
        ∑ d ∈ Ioc 0 N, (ArithmeticFunction.liouville d : ℝ) * ((N / d : ℕ) : ℝ) := by
      rw [← sum_Ioc_consecutive _ (Nat.zero_le N) hNn]
      have h0 : ∑ d ∈ Ioc N n, (ArithmeticFunction.liouville d : ℝ) * ((N / d : ℕ) : ℝ) = 0 := by
        refine sum_eq_zero fun d hd => ?_
        rw [Nat.div_eq_of_lt (mem_Ioc.mp hd).1]
        simp
      rw [h0, add_zero]
    rw [hext]
    refine sum_congr rfl fun e _ => ?_
    rw [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
    ring
  rw [← hright, ← hswap, hleft]

/-- `|ledger(λ)| ≤ (Σ |c(k)|) √n`. -/
theorem abs_ledger_liouville_le (c : ℕ →₀ ℤ) (hc0 : c 0 = 0) (n : ℕ) :
    |ledger c (fun d => (ArithmeticFunction.liouville d : ℝ)) n| ≤ coeffMass c * √(n : ℝ) := by
  rw [ledger_liouville c hc0, coeffMass, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
  rw [abs_mul, Nat.abs_cast]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine Real.nat_sqrt_le_real_sqrt.trans (Real.sqrt_le_sqrt ?_)
  exact_mod_cast Nat.div_le_self n k

/-- **A rate bounds the Liouville sum.** `|L(n)| ≤ ε n + 4 ((2 w + Σ|c(k)|)/m) √n + K`. -/
theorem IsProducer.abs_liouvilleR_le (hP : IsProducer c m B) (K n : ℕ) :
    |RigidArithmeticOfCuts.liouvilleR n| ≤ rate c m B * n +
      4 * ((2 * (peak c : ℝ) + coeffMass c) / m) * √(n : ℝ) + K := by
  refine hP.abs_sum_le_of_ledger (K := K) (a := fun d => (ArithmeticFunction.liouville d : ℝ))
    (fun d => ?_) (coeffMass_nonneg c) (fun n _ => abs_ledger_liouville_le c hP.zero n) n
  by_cases hd : d = 0
  · subst hd
    simp
  have hl : ArithmeticFunction.liouville d = 1 ∨ ArithmeticFunction.liouville d = -1 := by
    rw [ArithmeticFunction.liouville_apply hd]
    exact neg_one_pow_eq_or ℤ _
  rcases hl with h | h <;> simp [h]

/-- The peak ratio against the rate: `w/m ≤ A (1 + log K)³ K ε`, the floor removing the term `1`. -/
private lemma peakRatio_le_rate {K ε x l c₁ T m : ℝ} (hK : 1 ≤ K) (hl : 0 ≤ l) (hc₁ : 0 < c₁)
    (hε : 0 < ε) (hm : 0 < m) (hT : T ≤ m * ε)
    (hw : x * m ≤ 100 * (1 + l) ^ 2 * (K * T + m)) (hfloor : c₁ / (√K * (1 + l)) ≤ ε) :
    x ≤ 100 * (1 + 1 / c₁) * (1 + l) ^ 3 * K * ε := by
  have hs0 : 0 < √K := Real.sqrt_pos.mpr (by linarith)
  have hsK : √K ≤ K := by
    have h1 : 1 ≤ √K := Real.one_le_sqrt.mpr hK
    have h2 := Real.mul_self_sqrt (by linarith : 0 ≤ K)
    nlinarith
  have hl1 : 0 < 1 + l := by linarith
  have h1 : 1 ≤ ε * (K * (1 + l) / c₁) := by
    have h2 : c₁ ≤ ε * (√K * (1 + l)) := (div_le_iff₀ (by positivity)).mp hfloor
    have h3 : ε * (√K * (1 + l)) ≤ ε * (K * (1 + l)) := by gcongr
    have h4 : c₁ ≤ ε * (K * (1 + l)) := h2.trans h3
    have : ε * (K * (1 + l) / c₁) = ε * (K * (1 + l)) / c₁ := by ring
    rw [this, le_div_iff₀ hc₁]
    linarith
  have hKT : K * T + m ≤ m * (ε * K * (1 + l) * (1 + 1 / c₁)) := by
    have h2 : K * T ≤ K * (m * ε) := mul_le_mul_of_nonneg_left hT (by linarith)
    have h3 : K * (m * ε) ≤ m * (ε * K * (1 + l)) := by
      have : K * ε * 1 ≤ K * ε * (1 + l) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith
    have h4 : m ≤ m * (ε * (K * (1 + l) / c₁)) := le_mul_of_one_le_right hm.le h1
    have e : m * (ε * K * (1 + l) * (1 + 1 / c₁)) = m * (ε * K * (1 + l)) + m * (ε * (K * (1 + l) / c₁)) := by
      field_simp
    rw [e]
    linarith
  have hfinal : x * m ≤ (100 * (1 + 1 / c₁) * (1 + l) ^ 3 * K * ε) * m := by
    refine hw.trans ?_
    calc 100 * (1 + l) ^ 2 * (K * T + m)
        ≤ 100 * (1 + l) ^ 2 * (m * (ε * K * (1 + l) * (1 + 1 / c₁))) :=
          mul_le_mul_of_nonneg_left hKT (by positivity)
      _ = _ := by ring
  exact le_of_mul_le_mul_right hfinal hm

/-- **Past `K² log⁶ K`, every producer bounds the Mertens function by its rate.** There is an absolute `D` such that a
producer of rate `ε` on `[1, K]` has `|M(n)| ≤ 3 ε n` for every `n ≥ (D (1 + log K)³ K)²`. -/
theorem exists_abs_mertens_le_three_rate :
    ∃ D : ℝ, 0 < D ∧ ∀ (K : ℕ) (c : ℕ →₀ ℤ) (m B : ℕ), 1 ≤ K → IsProducer c m B → AlphabetLE c K →
      ∀ n : ℕ, (D * (1 + Real.log K) ^ 3 * K) ^ 2 ≤ (n : ℝ) → |mertens n| ≤ 3 * rate c m B * n := by
  obtain ⟨c₁, hc₁, hfloor⟩ := exists_half_floor
  obtain ⟨A, hA⟩ : ∃ A, A = 100 * (1 + 1 / c₁) := ⟨_, rfl⟩
  have hA100 : 100 ≤ A := by
    rw [hA]
    have : 0 ≤ 1 / c₁ := by positivity
    linarith
  refine ⟨12 * A, by linarith, fun K c m B hK hP hal n hn => ?_⟩
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hl := Real.log_nonneg hKR
  have hε := hP.rate_pos
  have hm := hP.m_pos
  have hd := hP.one_sub_pos
  have hd1 : 1 - 1 / (B : ℝ) ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / B := by positivity
    linarith
  have hT : excess c m B ≤ (m : ℝ) * rate c m B := by
    rw [hP.excess_eq_rate]
    have : (m : ℝ) * (1 - 1 / (B : ℝ)) ≤ m * 1 := mul_le_mul_of_nonneg_left hd1 hm.le
    nlinarith
  have hw : IsProducer.peakRatio c m * m ≤ 100 * (1 + Real.log K) ^ 2 * ((K : ℝ) * excess c m B + m) := by
    rw [IsProducer.peakRatio, div_mul_cancel₀ _ hm.ne']
    exact hP.peak_le hal hK
  have hx := peakRatio_le_rate hKR hl hc₁ hε hm hT hw (hfloor K c m B hK hP hal)
  rw [← hA] at hx
  have hx1 := hP.one_le_peakRatio
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hR : 0 ≤ 12 * A * (1 + Real.log K) ^ 3 * K := by positivity
  have hsq : 12 * A * (1 + Real.log K) ^ 3 * K ≤ √(n : ℝ) := Real.le_sqrt_of_sq_le hn
  have hmain := hP.abs_mertens_le hal hK n
  have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0
  have h12 : 12 * IsProducer.peakRatio c m * √(n : ℝ) ≤ rate c m B * n := by
    calc 12 * IsProducer.peakRatio c m * √(n : ℝ)
        ≤ 12 * (A * (1 + Real.log K) ^ 3 * K * rate c m B) * √(n : ℝ) := by gcongr
      _ = rate c m B * (12 * A * (1 + Real.log K) ^ 3 * K) * √(n : ℝ) := by ring
      _ ≤ rate c m B * √(n : ℝ) * √(n : ℝ) := by gcongr
      _ = rate c m B * n := by rw [mul_assoc, hss]
  have hKs : (K : ℝ) ≤ √(n : ℝ) := by
    refine le_trans ?_ hsq
    have h3 : 1 ≤ (1 + Real.log K) ^ 3 := one_le_pow₀ (by linarith)
    have h4 : (K : ℝ) * 1 ≤ K * (12 * A * (1 + Real.log K) ^ 3) := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      nlinarith
    linarith
  have hsn : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
  have hK12 : (K : ℝ) ≤ 12 * IsProducer.peakRatio c m * √(n : ℝ) := by nlinarith
  linarith

/-- **A family with a rate bounds the Mertens function, for every exponent below `1/2`.** -/
theorem HasRate.eventually_abs_mertens_le {f : ℕ → ℝ} (h : HasRate f) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ : θ < 1 / 2) : ∀ᶠ n : ℕ in atTop, |mertens n| ≤ 3 * f ⌊(n : ℝ) ^ θ⌋₊ * n := by
  obtain ⟨D, hD, hall⟩ := exists_abs_mertens_le_three_rate
  have hcut : Tendsto (fun n : ℕ => ⌊(n : ℝ) ^ θ⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop hθ0).comp tendsto_natCast_atTop_atTop)
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = (1 / 2 - θ) / 3 := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; linarith
  have hδ : (0 : ℝ) < 1 / (2 * (D + 1)) := by positivity
  have hlog : ∀ᶠ x : ℝ in atTop, 1 + Real.log x ≤ 1 / (D + 1) * x ^ κ := by
    have h1 := (isLittleO_log_rpow_atTop hκ).bound hδ
    have h2 := (tendsto_rpow_atTop hκ).eventually_ge_atTop (2 * (D + 1))
    filter_upwards [h1, h2, Real.tendsto_log_atTop.eventually_ge_atTop 0] with x h3 h4 h5
    have hx : 0 ≤ x ^ κ := by linarith [show 0 < D + 1 by linarith]
    rw [Real.norm_of_nonneg h5, Real.norm_of_nonneg hx] at h3
    have h6 : 1 ≤ 1 / (2 * (D + 1)) * x ^ κ := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
      linarith
    have e : 1 / (D + 1) * x ^ κ = 1 / (2 * (D + 1)) * x ^ κ + 1 / (2 * (D + 1)) * x ^ κ := by
      field_simp
      ring
    rw [e]
    linarith
  filter_upwards [hcut.eventually h, hcut.eventually_ge_atTop 1, eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually hlog] with n hf hK1 hn1 hlogn
  obtain ⟨K, hKdef⟩ : ∃ K, K = ⌊(n : ℝ) ^ θ⌋₊ := ⟨_, rfl⟩
  rw [← hKdef] at hf hK1 ⊢
  obtain ⟨c, m, B, hP, hal, hr⟩ := hf
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  have hKle : (K : ℝ) ≤ (n : ℝ) ^ θ := hKdef ▸ Nat.floor_le (by positivity)
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hlogK : Real.log (K : ℝ) ≤ Real.log (n : ℝ) := by
    refine Real.log_le_log (by linarith) (hKle.trans ?_)
    calc (n : ℝ) ^ θ ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
      _ = n := Real.rpow_one _
  have hlK := Real.log_nonneg hKR
  have hbound : D * (1 + Real.log K) ^ 3 * K ≤ √(n : ℝ) := by
    have h1 : (1 + Real.log (K : ℝ)) ^ 3 ≤ (1 / (D + 1) * (n : ℝ) ^ κ) ^ 3 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 3
    have h2 : D * (1 / (D + 1) * (n : ℝ) ^ κ) ^ 3 ≤ ((n : ℝ) ^ κ) ^ 3 := by
      have h3 : D * (1 / (D + 1)) ^ 3 ≤ 1 := by
        have hD1 : (1 : ℝ) ≤ D + 1 := by linarith
        have h4 : (1 / (D + 1)) ^ 3 ≤ 1 / (D + 1) := by
          have h5 : 1 / (D + 1) ≤ 1 := (div_le_one (by linarith)).mpr hD1
          have h6 : 0 ≤ 1 / (D + 1) := by positivity
          calc (1 / (D + 1)) ^ 3 ≤ (1 / (D + 1)) ^ 1 :=
                pow_le_pow_of_le_one h6 h5 (by norm_num)
            _ = _ := pow_one _
        calc D * (1 / (D + 1)) ^ 3 ≤ D * (1 / (D + 1)) := mul_le_mul_of_nonneg_left h4 hD.le
          _ ≤ 1 := by
            rw [mul_one_div, div_le_one (by linarith)]
            linarith
      have h7 : 0 ≤ ((n : ℝ) ^ κ) ^ 3 := by positivity
      calc D * (1 / (D + 1) * (n : ℝ) ^ κ) ^ 3 = D * (1 / (D + 1)) ^ 3 * ((n : ℝ) ^ κ) ^ 3 := by ring
        _ ≤ 1 * ((n : ℝ) ^ κ) ^ 3 := mul_le_mul_of_nonneg_right h3 h7
        _ = _ := one_mul _
    have hpow : ((n : ℝ) ^ κ) ^ 3 * (n : ℝ) ^ θ = √(n : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le, ← Real.rpow_add hn0, Real.sqrt_eq_rpow]
      congr 1
      rw [hκdef]
      push_cast
      ring
    rw [← hpow]
    calc D * (1 + Real.log K) ^ 3 * K ≤ D * (1 / (D + 1) * (n : ℝ) ^ κ) ^ 3 * (n : ℝ) ^ θ := by
          gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (by positivity)
  have hsq : (D * (1 + Real.log K) ^ 3 * K) ^ 2 ≤ (n : ℝ) := by
    have h0 : 0 ≤ D * (1 + Real.log K) ^ 3 * K := by positivity
    calc _ ≤ √(n : ℝ) ^ 2 := pow_le_pow_left₀ h0 hbound 2
      _ = n := Real.sq_sqrt hn0.le
  refine (hall K c m B hK1 hP hal n hsq).trans ?_
  have : 3 * rate c m B * n ≤ 3 * f K * n := by gcongr
  exact this

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
