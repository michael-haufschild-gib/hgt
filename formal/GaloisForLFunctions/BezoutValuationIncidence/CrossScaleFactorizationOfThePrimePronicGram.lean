import GaloisForLFunctions.BezoutValuationIncidence.CoherentPrimeBlocksAndTheTypeIIWindowNoGo
import GaloisForLFunctions.BezoutValuationIncidence.OscillatoryPronicTailSummationByPartsAndSecondOrderVonMangoldtError
import GaloisForLFunctions.BezoutValuationIncidence.ExactVasyuninReciprocityAsResidueDifferenceEnergy

/-!
# Cross-scale factorization of the prime pronic Gram

Take a packet `a` on any primes and a packet `b` on primes `q ≥ Q`. The packet values are

`V_a(n) = m(a) + Ṽ_a(n)`,  `m(a) = L_a - Σ_p a_p (p-1)/2`,  `Ṽ_a(n) = -Σ_p a_p ((n mod p) - (p-1)/2)`,

`V_b(n) = L_b - n A_b + U_b(n)`,  `U_b(n) = Σ_q b_q q ⌊n/q⌋`.

The fluctuation `Ṽ_a` is a sum of centered periodic residues, so its sums over every interval are
at most `K_a = Σ_p |a_p| p²/2`; it is the fast factor. The slow factor `U_b` is a superposition of
the steps `n ↦ 1[jq ≤ n]`, and Abel summation of `Ṽ_a` against the pronic weight beyond `jq`
costs `K_a/(jq(jq+1))`. Summing over `j` and `q`, and using that `V_b` has pronic mean zero,

`|Σ_{p,q} a_p b_q 𝒢^{ec}(p,q) + m(a) L_b| ≤ K_a (|A_b|/2 + 2 Σ_q |b_q|/q)`,

and on the class `A_b = L_b = 0`, `|Σ a_p b_q 𝒢^{ec}(p,q)| ≤ Σ_p |a_p| p² · Σ_q |b_q|/q`.

So across scales the energy-centered Gram is, up to `O(K_a Σ |b_q|/q)`, the rank-one coupling
`-m(a) L_b` plus a term in the mass `A_b`; on the codimension-two class `A_b = L_b = 0` the whole
form is `O(Σ|a_p| p² · Σ |b_q|/q)`, for arbitrary coefficients. For `a` on `(P, 2P]` and `b` on
`[Q, 2Q]` this is `‖a‖₁‖b‖₁ P²/Q` against the Cauchy–Schwarz scale `‖a‖₁‖b‖₁ √(PQ)`: a power
saving `(P/Q)^{3/2}` with no character or modulus average. Its loss is the period `P²` of the
fast factor against the step length `Q` of the slow one.
-/

open Finset ArithmeticFunction RHTower Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Centered residues have bounded interval sums -/

/-- The centered residue `(n mod p) - (p-1)/2`. -/
def centeredResidue (p n : ℕ) : ℝ := ((n % p : ℕ) : ℝ) - ((p : ℝ) - 1) / 2

theorem sum_Ico_centeredResidue_period (p : ℕ) (hp : 0 < p) (N : ℕ) :
    ∑ n ∈ Ico N (N + p), centeredResidue p n = 0 := by
  induction N with
  | zero =>
    simp only [zero_add, centeredResidue]
    rw [← Finset.range_eq_Ico, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    rw [sum_congr rfl fun n hn => by rw [Nat.mod_eq_of_lt (mem_range.mp hn)]]
    have h := Finset.sum_range_id_mul_two p
    have hc : ((∑ i ∈ range p, i : ℕ) : ℝ) * 2 = (p : ℝ) * ((p - 1 : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [Nat.cast_sub hp, Nat.cast_one, Nat.cast_sum] at hc
    linarith
  | succ N ih =>
    rw [show N + 1 + p = N + p + 1 by ring, sum_Ico_succ_top (by omega),
      ← sum_Ico_consecutive _ (Nat.le_succ N) (by omega : N + 1 ≤ N + p)] at *
    have hN : ∑ n ∈ Ico N (N + 1), centeredResidue p n = centeredResidue p N := by simp
    have hper : centeredResidue p (N + p) = centeredResidue p N := by
      simp [centeredResidue, Nat.add_mod_right]
    linarith

theorem abs_centeredResidue_le (p n : ℕ) (hp : 0 < p) :
    |centeredResidue p n| ≤ ((p : ℝ) - 1) / 2 := by
  have h1 : ((n % p : ℕ) : ℝ) ≤ (p : ℝ) - 1 := by
    have := Nat.mod_lt n hp
    have : ((n % p : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast this
    linarith
  have h0 : (0 : ℝ) ≤ ((n % p : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [centeredResidue, abs_le]
  constructor <;> linarith

/-- Every interval sum of centered residues is at most `p²/2` in absolute value. -/
theorem abs_sum_Ico_centeredResidue_le (p : ℕ) (hp : 0 < p) (N K : ℕ) :
    |∑ n ∈ Ico N (N + K), centeredResidue p n| ≤ (p : ℝ) ^ 2 / 2 := by
  induction K using Nat.strong_induction_on generalizing N with
  | _ K ih =>
    by_cases hK : K < p
    · calc |∑ n ∈ Ico N (N + K), centeredResidue p n|
          ≤ ∑ n ∈ Ico N (N + K), |centeredResidue p n| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _n ∈ Ico N (N + K), ((p : ℝ) - 1) / 2 :=
          sum_le_sum fun n _ => abs_centeredResidue_le p n hp
        _ = K * (((p : ℝ) - 1) / 2) := by rw [sum_const, Nat.card_Ico]; simp
        _ ≤ (p : ℝ) ^ 2 / 2 := by
          have : (K : ℝ) ≤ p := by exact_mod_cast hK.le
          have : (1 : ℝ) ≤ p := by exact_mod_cast hp
          nlinarith
    · replace hK := not_lt.mp hK
      rw [show N + K = (N + p) + (K - p) by omega,
        ← sum_Ico_consecutive _ (by omega : N ≤ N + p) (by omega : N + p ≤ N + p + (K - p)),
        sum_Ico_centeredResidue_period p hp N, zero_add]
      exact ih (K - p) (by omega) (N + p)

/-! ## §2. Abel summation of a fast factor against the pronic weight -/

/-- Interval sums bounded by `K` and a nonnegative decreasing weight: `|Σ_{N ≤ n < M} w x| ≤ K w(N)`. -/
theorem abs_sum_Ico_mul_antitone_le {x w : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hw0 : ∀ n, 0 ≤ w n)
    (hanti : Antitone w) (hx : ∀ N L, |∑ n ∈ Ico N (N + L), x n| ≤ K) (N M : ℕ) :
    |∑ n ∈ Ico N M, w n * x n| ≤ K * w N := by
  rcases le_or_gt M N with h | h
  · rw [Ico_eq_empty_of_le h, sum_empty, abs_zero]
    exact mul_nonneg hK (hw0 N)
  have hshift : ∀ (f : ℕ → ℝ) (L : ℕ), ∑ n ∈ Ico N (N + L), f n = ∑ i ∈ range L, f (N + i) := by
    intro f L
    rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  have := abs_sum_range_mul_antitone_le (fun i => x (N + i)) (fun i => w (N + i)) (M - N) hK
    (fun i => hw0 _) (fun i j hij => hanti (by omega))
    (fun L _ => by rw [← hshift]; exact hx N L)
  rw [show M = N + (M - N) by omega, hshift]
  simpa using this

/-- The pronic weight `w(n) = 1/(n(n+1))` is antitone on `ℕ` (with `w 0 = 0` and `w 1 = 1/2`
excluded by starting at `1`). -/
theorem pronicWeight_antitone_shift (s : ℕ) (hs : 1 ≤ s) :
    Antitone fun n : ℕ => 1 / (((s + n : ℕ) : ℝ) * (((s + n : ℕ) : ℝ) + 1)) := by
  intro i j hij
  have hi : (1 : ℝ) ≤ ((s + i : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ s + i)
  have hij' : ((s + i : ℕ) : ℝ) ≤ ((s + j : ℕ) : ℝ) := by exact_mod_cast (by omega : s + i ≤ s + j)
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

/-- The pronic weight, made antitone on all of `ℕ` by freezing it at `n = 1`. -/
def pronicWeightAntitone (n : ℕ) : ℝ := 1 / (((max n 1 : ℕ) : ℝ) * (((max n 1 : ℕ) : ℝ) + 1))

theorem pronicWeightAntitone_antitone : Antitone pronicWeightAntitone := by
  intro i j hij
  have h1 : (1 : ℝ) ≤ ((max i 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right i 1
  have h2 : ((max i 1 : ℕ) : ℝ) ≤ ((max j 1 : ℕ) : ℝ) := by
    exact_mod_cast max_le_max hij le_rfl
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

theorem pronicWeightAntitone_of_pos {n : ℕ} (hn : 1 ≤ n) :
    pronicWeightAntitone n = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  rw [pronicWeightAntitone, max_eq_left hn]

/-! ## §3. The two factors of a cross-scale pair -/

/-- The long-run mean of a prime packet: `L - Σ a_p (p-1)/2`. -/
def primePacketMean (S : Finset Nat.Primes) (a : Nat.Primes → ℝ) : ℝ :=
  primePacketLogMoment S a - ∑ p ∈ S, a p * (((p : ℕ) : ℝ) - 1) / 2

/-- The fast fluctuation of a prime packet around its mean. -/
def primePacketFluct (S : Finset Nat.Primes) (a : Nat.Primes → ℝ) (n : ℕ) : ℝ :=
  -∑ p ∈ S, a p * centeredResidue p n

theorem primePacketValue_eq_mean_add_fluct (S : Finset Nat.Primes) (a : Nat.Primes → ℝ)
    (n : ℕ) : primePacketValue S a n = primePacketMean S a + primePacketFluct S a n := by
  rw [primePacketValue_eq_logMoment_sub]
  unfold primePacketMean primePacketFluct centeredResidue
  have h : ∑ p ∈ S, a p * (((n % (p : ℕ) : ℕ) : ℝ) - (((p : ℕ) : ℝ) - 1) / 2) =
      ∑ p ∈ S, a p * ((n % (p : ℕ) : ℕ) : ℝ) - ∑ p ∈ S, a p * (((p : ℕ) : ℝ) - 1) / 2 := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun _ _ => by ring
  rw [h]
  ring

/-- Interval sums of the fluctuation are at most `K_a = Σ |a_p| p²/2`. -/
theorem abs_sum_Ico_primePacketFluct_le (S : Finset Nat.Primes) (a : Nat.Primes → ℝ)
    (N L : ℕ) :
    |∑ n ∈ Ico N (N + L), primePacketFluct S a n| ≤
      ∑ p ∈ S, |a p| * (((p : ℕ) : ℝ) ^ 2 / 2) := by
  unfold primePacketFluct
  rw [sum_neg_distrib, abs_neg, sum_comm]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p _ => ?_)
  rw [← mul_sum, abs_mul]
  exact mul_le_mul_of_nonneg_left
    (abs_sum_Ico_centeredResidue_le p p.property.pos N L) (abs_nonneg _)

/-- The slow factor: `V_b(n) = L_b - n A_b + Σ_q b_q q ⌊n/q⌋`. -/
theorem primePacketValue_eq_ramp_add_steps (S : Finset Nat.Primes) (b : Nat.Primes → ℝ)
    (n : ℕ) : primePacketValue S b n = primePacketLogMoment S b - n * primePacketMass S b +
      ∑ q ∈ S, b q * (q : ℕ) * ((n / (q : ℕ) : ℕ) : ℝ) := by
  rw [primePacketValue_eq_logMoment_sub, primePacketMass, mul_sum]
  have h : ∑ q ∈ S, b q * ((n % (q : ℕ) : ℕ) : ℝ) =
      ∑ q ∈ S, (n : ℝ) * b q - ∑ q ∈ S, b q * (q : ℕ) * ((n / (q : ℕ) : ℕ) : ℝ) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun q _ => ?_
    have := congrArg (Nat.cast (R := ℝ)) (Nat.mod_add_div n (q : ℕ))
    push_cast at this
    linear_combination b q * this
  rw [h]
  ring

/-- Counting the steps below `n`: `⌊n/q⌋ = #{1 ≤ j ≤ H : j q ≤ n}` for `n < H`. -/
theorem cast_div_eq_sum_steps {n q H : ℕ} (hq : 0 < q) (hn : n < H) :
    ((n / q : ℕ) : ℝ) = ∑ j ∈ Icc 1 H, if j * q ≤ n then (1 : ℝ) else 0 := by
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  congr 1
  rw [show (Icc 1 H).filter (fun j => j * q ≤ n) = Icc 1 (n / q) by
    ext j
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨hj1, _⟩, hj⟩
      exact ⟨hj1, (Nat.le_div_iff_mul_le hq).mpr hj⟩
    · rintro ⟨hj1, hj⟩
      have := (Nat.le_div_iff_mul_le hq).mp hj
      exact ⟨⟨hj1, by nlinarith [Nat.div_le_self n q]⟩, this⟩, Nat.card_Icc, Nat.add_sub_cancel]

/-! ## §4. The factorization -/

/-- **Cross-scale factorization of the energy-centered prime Gram.**
`|Σ a_p b_q 𝒢^{ec}(p,q) + m(a) L_b| ≤ K_a (|A_b|/2 + 2 Σ_q |b_q|/q)`, `K_a = Σ |a_p| p²/2`. -/
theorem abs_primePacketBilinear_add_mean_mul_logMoment_le (Sa Sb : Finset Nat.Primes)
    (a b : Nat.Primes → ℝ) :
    |primePacketBilinear Sa Sb a b + primePacketMean Sa a * primePacketLogMoment Sb b| ≤
      (∑ p ∈ Sa, |a p| * (((p : ℕ) : ℝ) ^ 2 / 2)) *
        (|primePacketMass Sb b| / 2 + 2 * ∑ q ∈ Sb, |b q| / (q : ℕ)) := by
  set K := ∑ p ∈ Sa, |a p| * (((p : ℕ) : ℝ) ^ 2 / 2) with hKdef
  set m := primePacketMean Sa a
  set Lb := primePacketLogMoment Sb b
  set Ab := primePacketMass Sb b
  set Va := primePacketValue Sa a
  set Vb := primePacketValue Sb b
  set F := primePacketFluct Sa a
  set w : ℕ → ℝ := fun n => 1 / ((n : ℝ) * ((n : ℝ) + 1)) with hw
  have hK : 0 ≤ K := sum_nonneg fun p _ => by positivity
  have hF : ∀ N L, |∑ n ∈ Ico N (N + L), F n| ≤ K := abs_sum_Ico_primePacketFluct_le Sa a
  clear_value K
  -- the finite-horizon remainder
  set X : ℕ → ℝ := fun H => ∑ n ∈ range H, Va n * Vb n / ((n : ℝ) * ((n : ℝ) + 1)) -
    m * ∑ n ∈ range H, Vb n / ((n : ℝ) * ((n : ℝ) + 1)) -
    Lb * (∑ n ∈ range H, Va n / ((n : ℝ) * ((n : ℝ) + 1)) -
      m * ∑ n ∈ range H, 1 / ((n : ℝ) * ((n : ℝ) + 1))) with hX
  have hlim : Tendsto X atTop (𝓝 (primePacketBilinear Sa Sb a b + m * Lb)) := by
    have h1 := (hasSum_primePacketBilinear Sa Sb a b).tendsto_sum_nat
    have h2 := (hasSum_primePacketValue Sb b).tendsto_sum_nat
    have h3 := (hasSum_primePacketValue Sa a).tendsto_sum_nat
    have h4 := hasSum_pm_reciprocal_weight.tendsto_sum_nat
    have := (h1.sub (h2.const_mul m)).sub ((h3.sub (h4.const_mul m)).const_mul Lb)
    convert this using 2
    ring
  refine le_of_tendsto (hlim.abs) (Eventually.of_forall fun H => ?_)
  -- split `X H` into the mass term and the step term
  have hsplit : X H = -Ab * ∑ n ∈ range H, (n : ℝ) * w n * F n +
      ∑ q ∈ Sb, b q * (q : ℕ) * ∑ n ∈ range H, w n * F n * ((n / (q : ℕ) : ℕ) : ℝ) := by
    have hpt : ∀ n, Va n * Vb n / ((n : ℝ) * ((n : ℝ) + 1)) -
        m * (Vb n / ((n : ℝ) * ((n : ℝ) + 1))) -
          Lb * (Va n / ((n : ℝ) * ((n : ℝ) + 1)) - m * (1 / ((n : ℝ) * ((n : ℝ) + 1)))) =
        -Ab * ((n : ℝ) * w n * F n) +
          ∑ q ∈ Sb, b q * (q : ℕ) * (w n * F n * ((n / (q : ℕ) : ℕ) : ℝ)) := by
      intro n
      have hva : Va n = m + F n := primePacketValue_eq_mean_add_fluct Sa a n
      have hvb : Vb n - Lb = -(n : ℝ) * Ab + ∑ q ∈ Sb, b q * (q : ℕ) * ((n / (q : ℕ) : ℕ) : ℝ) := by
        have := primePacketValue_eq_ramp_add_steps Sb b n
        simp only [Vb, Lb, Ab]
        linarith
      have e1 : Va n * Vb n / ((n : ℝ) * ((n : ℝ) + 1)) -
          m * (Vb n / ((n : ℝ) * ((n : ℝ) + 1))) -
            Lb * (Va n / ((n : ℝ) * ((n : ℝ) + 1)) - m * (1 / ((n : ℝ) * ((n : ℝ) + 1)))) =
          F n * (Vb n - Lb) * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
        rw [hva]; ring
      rw [e1, hvb, hw, mul_add, add_mul, mul_sum, sum_mul]
      congr 1
      · ring
      · exact sum_congr rfl fun _ _ => by ring
    have hcomb : X H = ∑ n ∈ range H, (Va n * Vb n / ((n : ℝ) * ((n : ℝ) + 1)) -
        m * (Vb n / ((n : ℝ) * ((n : ℝ) + 1))) -
          Lb * (Va n / ((n : ℝ) * ((n : ℝ) + 1)) - m * (1 / ((n : ℝ) * ((n : ℝ) + 1))))) := by
      simp only [hX, Finset.sum_sub_distrib, Finset.mul_sum, mul_sub]
    rw [hcomb, sum_congr rfl fun n _ => hpt n, sum_add_distrib, ← mul_sum, sum_comm]
    congr 1
    exact sum_congr rfl fun q _ => by rw [mul_sum]
  rw [hsplit]
  -- the mass term: Abel summation against `1/(n+1)` from `n = 1`
  have hmass : |∑ n ∈ range H, (n : ℝ) * w n * F n| ≤ K / 2 := by
    rcases Nat.eq_zero_or_pos H with h0 | hH
    · subst h0; simp; positivity
    have hshift : ∑ n ∈ range H, (n : ℝ) * w n * F n =
        ∑ n ∈ Ico 1 H, (1 / ((n : ℝ) + 1)) * F n := by
      rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hH]
      simp only [CharP.cast_eq_zero, zero_mul, zero_add]
      refine sum_congr rfl fun n hn => ?_
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ico.mp hn).1
      rw [hw]
      field_simp
    rw [hshift]
    have := abs_sum_Ico_mul_antitone_le (x := F) (w := fun n : ℕ => 1 / ((n : ℝ) + 1)) hK
      (fun n => by positivity)
      (fun i j hij => one_div_le_one_div_of_le (by positivity)
        (by have : (i : ℝ) ≤ j := by exact_mod_cast hij
            linarith)) hF 1 H
    refine this.trans (le_of_eq ?_)
    push_cast
    ring
  -- the step term: every step `1[jq ≤ n]` costs `K w(jq)`
  have hstep : ∀ q ∈ Sb, |(q : ℕ) * ∑ n ∈ range H, w n * F n * ((n / (q : ℕ) : ℕ) : ℝ)| ≤
      2 * K / (q : ℕ) := by
    intro q _
    have hq : 0 < (q : ℕ) := q.property.pos
    have hqR : (0 : ℝ) < (q : ℕ) := by exact_mod_cast hq
    have hexp : ∑ n ∈ range H, w n * F n * ((n / (q : ℕ) : ℕ) : ℝ) =
        ∑ j ∈ Icc 1 H, ∑ n ∈ Ico (j * (q : ℕ)) H, w n * F n := by
      rw [sum_congr rfl fun n hn => by rw [cast_div_eq_sum_steps hq (mem_range.mp hn), mul_sum],
        sum_comm]
      refine sum_congr rfl fun j _ => ?_
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [← sum_filter]
      congr 1
      ext n
      simp only [mem_filter, mem_range, mem_Ico]
      tauto
    rw [hexp, abs_mul, abs_of_pos hqR]
    have hj : ∀ j ∈ Icc 1 H, |∑ n ∈ Ico (j * (q : ℕ)) H, w n * F n| ≤
        K * (2 / (((q : ℕ) : ℝ) ^ 2 * ((j : ℝ) * ((j : ℝ) + 1)))) := by
      intro j hj
      have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
      have hjq : 1 ≤ j * (q : ℕ) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have hagree : ∑ n ∈ Ico (j * (q : ℕ)) H, w n * F n =
          ∑ n ∈ Ico (j * (q : ℕ)) H, pronicWeightAntitone n * F n :=
        sum_congr rfl fun n hn => by
          rw [pronicWeightAntitone_of_pos (hjq.trans (mem_Ico.mp hn).1)]
      rw [hagree]
      refine (abs_sum_Ico_mul_antitone_le hK (fun n => by unfold pronicWeightAntitone; positivity)
        pronicWeightAntitone_antitone hF _ _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hK
      rw [pronicWeightAntitone_of_pos hjq]
      have hj1R : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      have hq1R : (1 : ℝ) ≤ (q : ℕ) := by exact_mod_cast hq
      push_cast
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hjq' : ((q : ℕ) : ℝ) ≤ j * (q : ℕ) + 2 := by nlinarith
      have hpos : (0 : ℝ) ≤ (j : ℝ) * (q : ℕ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hjq' hpos]
    calc ((q : ℕ) : ℝ) * |∑ j ∈ Icc 1 H, ∑ n ∈ Ico (j * (q : ℕ)) H, w n * F n|
        ≤ (q : ℕ) * ∑ j ∈ Icc 1 H, K * (2 / (((q : ℕ) : ℝ) ^ 2 * ((j : ℝ) * ((j : ℝ) + 1)))) :=
          mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hj)) hqR.le
      _ = 2 * K / (q : ℕ) * ∑ j ∈ Ico 1 (H + 1), 1 / ((j : ℝ) * ((j : ℝ) + 1)) := by
          rw [show Icc 1 H = Ico 1 (H + 1) from rfl, mul_sum, mul_sum]
          refine sum_congr rfl fun j hj => ?_
          have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Ico.mp hj).1
          field_simp
      _ ≤ 2 * K / (q : ℕ) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [sum_Ico_pronic_mass (by norm_num) (by omega)]
          have : (0 : ℝ) ≤ 1 / ((H + 1 : ℕ) : ℝ) := by positivity
          push_cast at this ⊢
          linarith
      _ = 2 * K / (q : ℕ) := mul_one _
  calc |-Ab * ∑ n ∈ range H, (n : ℝ) * w n * F n +
        ∑ q ∈ Sb, b q * (q : ℕ) * ∑ n ∈ range H, w n * F n * ((n / (q : ℕ) : ℕ) : ℝ)|
      ≤ |Ab| * (K / 2) + ∑ q ∈ Sb, |b q| * (2 * K / (q : ℕ)) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_neg]
          exact mul_le_mul_of_nonneg_left hmass (abs_nonneg _)
        · refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun q hq => ?_)
          rw [mul_assoc, abs_mul]
          exact mul_le_mul_of_nonneg_left (hstep q hq) (abs_nonneg _)
    _ = K * (|Ab| / 2 + 2 * ∑ q ∈ Sb, |b q| / (q : ℕ)) := by
        rw [mul_add]
        congr 1
        · ring
        · rw [mul_sum, mul_sum]
          exact sum_congr rfl fun _ _ => by ring

/-- **Type-II bound across scales on the codimension-two class.** If `b` has zero mass and zero
log moment then `|Σ a_p b_q 𝒢^{ec}(p,q)| ≤ Σ_p |a_p| p² · Σ_q |b_q|/q`, for arbitrary `a`. -/
theorem abs_primePacketBilinear_le_of_mass_logMoment_eq_zero (Sa Sb : Finset Nat.Primes)
    (a b : Nat.Primes → ℝ) (hA : primePacketMass Sb b = 0) (hL : primePacketLogMoment Sb b = 0) :
    |primePacketBilinear Sa Sb a b| ≤
      (∑ p ∈ Sa, |a p| * ((p : ℕ) : ℝ) ^ 2) * ∑ q ∈ Sb, |b q| / (q : ℕ) := by
  have h := abs_primePacketBilinear_add_mean_mul_logMoment_le Sa Sb a b
  rw [hA, hL, mul_zero, add_zero, abs_zero, zero_div, zero_add] at h
  refine h.trans (le_of_eq ?_)
  have : ∑ p ∈ Sa, |a p| * (((p : ℕ) : ℝ) ^ 2 / 2) = (∑ p ∈ Sa, |a p| * ((p : ℕ) : ℝ) ^ 2) / 2 := by
    rw [sum_div]; exact sum_congr rfl fun _ _ => by ring
  rw [this]
  ring

end

end GaloisForLFunctions.BezoutValuationIncidence
