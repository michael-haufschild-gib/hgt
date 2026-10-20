import GaloisForLFunctions.TransHorizonIncidenceMechanics.MoebiusBuchstabStepSmoothCoreLaw

/-!
# Prime pairing collapse of Möbius responses and the prime-factor step law

Let `p` be a prime dividing `k`. The divisors `d` and `pd` of `k` (with `p ∤ d`) carry opposite
Möbius signs, and divisors with `p² ∣ d` carry none, so in the truncated Möbius sum every pair
inside the horizon cancels:

`s_X(k; μ) = Σ_{d | k, p ∤ d, X/p < d ≤ X} μ(d)`.

The response at a multiple of `p` lives on the top `p`-adic window `(X/p, X]` of the `p`-free
divisors; for even `k` it is the sum of `μ` over the odd divisors in the top octave. (This is the
prime-chain renormalization `s_X(pb) - s_X(b) = s_{X/p}(μ(p·), b)` read through squarefree
saturation.)

At a squarefree horizon `m = pa` the band step therefore splits into a universal part and a window
correction:

`Δ(pa, B) = -B - 2 μ(a) Σ_{a < d < pa, p ∤ d} μ(d) ⌊B gcd(d,a)/d⌋`.

For `a = 1` this is the prime step law; for `p = 2` the window is the odd part of the top octave
`(a, 2a)`. When `a = q` is an odd prime no odd `d ∈ (q, 2q)` meets `q`, and the first such `d` is
`q + 2`, so the horizon `2q` steps by exactly `-B` in every band `B ≤ q + 1`.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

private theorem moebiusReal_prime_mul {p d : ℕ} (hp : p.Prime) :
    moebiusReal (p * d) = if p ∣ d then 0 else -moebiusReal d := by
  split_ifs with hpd
  · apply moebiusReal_eq_zero_of_not_squarefree
    intro hsq
    obtain ⟨e, rfl⟩ := hpd
    have := hsq p ⟨e, by ring⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)
  · unfold moebiusReal
    rw [isMultiplicative_moebius.map_mul_of_coprime ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd),
      moebius_apply_prime hp]
    push_cast; ring

/-- **Prime pairing collapse.** For a prime `p ∣ k` and every truncation `X`,
`s_X(k; μ) = Σ_{d ≤ X, d | k, p ∤ d, X/p < d} μ(d)`. -/
theorem sieveSeq_moebius_prime_pairing {p X k : ℕ} (hp : p.Prime) (hpk : p ∣ k) :
    sieveSeq X moebiusReal k =
      ∑ d ∈ (Icc 1 X).filter (fun d => d ∣ k ∧ ¬ p ∣ d ∧ X / p < d), moebiusReal d := by
  have hp0 : 0 < p := hp.pos
  have hIsub : Icc 1 (X / p) = (Icc 1 X).filter (· ≤ X / p) := by
    ext d; simp only [mem_Icc, mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans (Nat.div_le_self X p)⟩, h2⟩
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
  -- the `p`-divisible divisors are `p d'` with `d' ≤ X/p`
  have hdiv : ∑ d ∈ (Icc 1 X).filter (fun d => d ∣ k ∧ p ∣ d), moebiusReal d =
      ∑ d' ∈ (Icc 1 (X / p)).filter (fun d' => p * d' ∣ k), moebiusReal (p * d') := by
    refine sum_nbij' (· / p) (p * ·) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      simp only [mem_filter, mem_Icc] at hd ⊢
      obtain ⟨⟨h1, h2⟩, hdk, hpd⟩ := hd
      rw [Nat.mul_div_cancel' hpd]
      exact ⟨⟨Nat.div_pos (Nat.le_of_dvd (by omega) hpd) hp0, Nat.div_le_div_right h2⟩, hdk⟩
    · intro d hd
      simp only [mem_filter, mem_Icc] at hd ⊢
      obtain ⟨⟨h1, h2⟩, hdk⟩ := hd
      exact ⟨⟨Nat.mul_pos hp0 (by omega), by
        have := (Nat.le_div_iff_mul_le hp0).mp h2; linarith [mul_comm d p]⟩, hdk, dvd_mul_right p d⟩
    · intro d hd
      simp only [mem_filter] at hd
      exact Nat.mul_div_cancel' hd.2.2
    · intro d _
      exact Nat.mul_div_cancel_left d hp0
    · intro d hd
      simp only [mem_filter] at hd
      rw [Nat.mul_div_cancel' hd.2.2]
  -- pairing: `μ(p d') = -μ(d')` when `p ∤ d'`, and `p d' | k ↔ d' | k`
  have hpair : ∑ d' ∈ (Icc 1 (X / p)).filter (fun d' => p * d' ∣ k), moebiusReal (p * d') =
      -∑ d' ∈ (Icc 1 (X / p)).filter (fun d' => d' ∣ k ∧ ¬ p ∣ d'), moebiusReal d' := by
    rw [sum_filter, sum_filter, ← sum_neg_distrib]
    refine sum_congr rfl fun d' _ => ?_
    rw [moebiusReal_prime_mul hp]
    by_cases hpd : p ∣ d'
    · simp [hpd]
    · have hiff : p * d' ∣ k ↔ d' ∣ k :=
        ⟨fun h => (dvd_mul_left d' p).trans h,
          fun h => Nat.Coprime.mul_dvd_of_dvd_of_dvd
            ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd) hpk h⟩
      simp only [hpd, if_false, hiff, not_false_eq_true, and_true]
      split_ifs <;> simp
  unfold sieveSeq
  rw [← sum_filter_add_sum_filter_not ((Icc 1 X).filter (· ∣ k)) (fun d => p ∣ d),
    filter_filter, filter_filter, hdiv, hpair, hIsub, filter_filter]
  rw [← sum_filter_add_sum_filter_not ((Icc 1 X).filter (fun d => d ∣ k ∧ ¬ p ∣ d))
    (fun d => d ≤ X / p), filter_filter, filter_filter]
  have h1 : (Icc 1 X).filter (fun d => (d ∣ k ∧ ¬ p ∣ d) ∧ d ≤ X / p) =
      (Icc 1 X).filter (fun d => d ≤ X / p ∧ d ∣ k ∧ ¬ p ∣ d) := by
    ext d; simp only [mem_filter]; tauto
  have h2 : (Icc 1 X).filter (fun d => (d ∣ k ∧ ¬ p ∣ d) ∧ ¬ d ≤ X / p) =
      (Icc 1 X).filter (fun d => d ∣ k ∧ ¬ p ∣ d ∧ X / p < d) := by
    ext d; simp only [mem_filter, not_le]; tauto
  rw [h1, h2]
  ring

/-- **Even collapse.** For even `k`, `s_X(k; μ)` is the sum of `μ` over the odd divisors of `k`
in the top octave `(X/2, X]`. -/
theorem sieveSeq_moebius_even_collapse {X k : ℕ} (hk : 2 ∣ k) :
    sieveSeq X moebiusReal k =
      ∑ d ∈ (Icc 1 X).filter (fun d => d ∣ k ∧ ¬ 2 ∣ d ∧ X / 2 < d), moebiusReal d :=
  sieveSeq_moebius_prime_pairing Nat.prime_two hk

/-! ### The prime-factor step law -/

/-- The window correction `W_p(a, B) = Σ_{a < d < pa, p ∤ d} μ(d) ⌊B gcd(d,a)/d⌋`. -/
def primeFactorWindowCorrection (p a B : ℕ) : ℝ :=
  ∑ d ∈ (Icc (a + 1) (p * a - 1)).filter (fun d => ¬ p ∣ d),
    moebiusReal d * ((B / (d / Nat.gcd d a) : ℕ) : ℝ)

/-- At a multiple `paj` of the squarefree horizon `pa` the response is read on `[a, pa)`. -/
private theorem sieveSeq_prime_mul_horizon {p a j : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    sieveSeq (p * a - 1) moebiusReal (p * a * j) =
      ∑ d ∈ (Icc a (p * a - 1)).filter (fun d => d ∣ a * j ∧ ¬ p ∣ d), moebiusReal d := by
  have hp2 := hp.two_le
  rw [sieveSeq_moebius_prime_pairing hp (by rw [mul_assoc]; exact dvd_mul_right p _)]
  have hq : (p * a - 1) / p = a - 1 := by
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    apply Nat.div_eq_of_lt_le
    · rw [mul_add, mul_one, mul_comm b p]; omega
    · rw [mul_add, mul_one, mul_comm (b + 1) p, mul_add, mul_one]; omega
  rw [hq]
  refine sum_congr ?_ fun _ _ => rfl
  ext d
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨-, h2⟩, hdk, hpd, h3⟩
    have hc : Nat.Coprime d p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd).symm
    refine ⟨⟨by omega, h2⟩, hc.dvd_of_dvd_mul_left (by rwa [mul_assoc] at hdk), hpd⟩
  · rintro ⟨⟨h1, h2⟩, hdk, hpd⟩
    refine ⟨⟨by omega, h2⟩, by rw [mul_assoc]; exact Dvd.dvd.mul_left hdk p, hpd, by omega⟩

/-- **Prime-factor step law.** For a prime `p ∤ a` with `pa` squarefree,
`Δ(pa, B) = -B - 2 μ(a) W_p(a, B)`. -/
theorem moebiusBandStep_prime_mul {p a B : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (hsq : Squarefree (p * a)) :
    moebiusBandStep (p * a) B = -(B : ℝ) - 2 * moebiusReal a * primeFactorWindowCorrection p a B := by
  have hpa : ¬ p ∣ a := fun h => by
    obtain ⟨e, rfl⟩ := h
    have := hsq p ⟨e, by ring⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)
  have hasq : Squarefree a := hsq.of_mul_right
  have hμa : moebiusReal a ^ 2 = 1 := by
    unfold moebiusReal
    have h1 : |(μ a : ℝ)| = 1 := by exact_mod_cast abs_moebius_eq_one_of_squarefree hasq
    rw [← sq_abs, h1]; norm_num
  have hμpa : moebiusReal (p * a) = -moebiusReal a := by
    rw [moebiusReal_prime_mul hp, if_neg hpa]
  -- exchange the band sum and the window sum
  have hcount : ∀ d, 0 < d → ((Icc 1 B).filter (fun j => d ∣ a * j)).card = B / (d / Nat.gcd d a) := by
    intro d hd
    have hI : Icc 1 B = Ioc 0 B := by ext; simp only [mem_Icc, mem_Ioc]; omega
    rw [hI, ← Nat.Ioc_filter_dvd_card_eq_div]
    congr 1; ext j
    simp only [mem_filter, dvd_mul_iff_div_gcd_dvd hd]
  have hsum : ∑ j ∈ Icc 1 B, sieveSeq (p * a - 1) moebiusReal (p * a * j) =
      moebiusReal a * B + primeFactorWindowCorrection p a B := by
    simp_rw [sieveSeq_prime_mul_horizon hp ha]
    rw [sum_comm' (t' := (Icc a (p * a - 1)).filter (fun d => ¬ p ∣ d))
      (s' := fun d => (Icc 1 B).filter (fun j => d ∣ a * j))]
    · have hsplit : (Icc a (p * a - 1)).filter (fun d => ¬ p ∣ d) =
          insert a ((Icc (a + 1) (p * a - 1)).filter (fun d => ¬ p ∣ d)) := by
        ext d; simp only [mem_insert, mem_filter, mem_Icc]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          rcases eq_or_lt_of_le h1 with h | h
          · exact Or.inl h.symm
          · exact Or.inr ⟨⟨h, h2⟩, h3⟩
        · rintro (rfl | ⟨⟨h1, h2⟩, h3⟩)
          · refine ⟨⟨le_rfl, ?_⟩, hpa⟩
            have := hp.two_le; rw [Nat.le_sub_iff_add_le (by nlinarith)]; nlinarith
          · exact ⟨⟨by omega, h2⟩, h3⟩
      rw [hsplit, sum_insert (by simp), primeFactorWindowCorrection]
      simp only [sum_const, nsmul_eq_mul]
      rw [hcount a (by omega), Nat.gcd_self, Nat.div_self (by omega), Nat.div_one]
      congr 1
      · ring
      · exact sum_congr rfl fun d hd => by
          rw [hcount d (by simp only [mem_filter, mem_Icc] at hd; omega), mul_comm]
    · intro j d
      simp only [mem_filter, mem_Icc]
      tauto
  unfold moebiusBandStep
  rw [hsum, hμpa]
  linear_combination (-(B : ℝ)) * hμa

/-- **Even prime horizons.** For an odd prime `q`, the horizon `2q` steps by exactly `-B` in every
band `B ≤ q + 1`: the first odd window divisor `q + 2` is beyond the band. -/
theorem moebiusBandStep_two_mul_prime {q B : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hB : B ≤ q + 1) :
    moebiusBandStep (2 * q) B = -(B : ℝ) := by
  have hodd : ¬ 2 ∣ q := fun h => hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h).symm
  have hsq : Squarefree (2 * q) :=
    Nat.squarefree_mul_iff.mpr ⟨(Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd,
      Nat.prime_two.squarefree, hq.squarefree⟩
  rw [moebiusBandStep_prime_mul Nat.prime_two hq.one_lt.le hsq]
  have hW : primeFactorWindowCorrection 2 q B = 0 := by
    refine sum_eq_zero fun d hd => ?_
    simp only [mem_filter, mem_Icc] at hd
    obtain ⟨⟨h1, h2⟩, h3⟩ := hd
    have hqd : ¬ q ∣ d := fun h => by
      obtain ⟨e, rfl⟩ := h
      rcases e with _ | _ | e
      · omega
      · omega
      · have : 2 * q ≤ q * (e + 1 + 1) := by nlinarith
        omega
    have hg : Nat.gcd d q = 1 := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqd)
    have hd2 : q + 2 ≤ d := by
      rcases Nat.even_or_odd q with ⟨r, hr⟩ | ⟨r, hr⟩
      · exact absurd ⟨r, by omega⟩ hodd
      · rcases Nat.even_or_odd d with ⟨s, hs⟩ | ⟨s, hs⟩
        · exact absurd ⟨s, by omega⟩ h3
        · omega
    rw [hg, Nat.div_one, Nat.div_eq_of_lt (by omega)]
    simp
  rw [hW]; ring

/-- Energy form: for an odd prime `q` and `M < 2q(q+2)`, `E_{2q}(M; μ) = E_{2q-1}(M; μ) - ⌊M/(2q)⌋`. -/
theorem sieveL2PrefixEnergy_moebius_step_two_mul_prime {q M : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hM : M < 2 * q * (q + 2)) :
    sieveL2PrefixEnergy (2 * q) M moebiusReal - sieveL2PrefixEnergy (2 * q - 1) M moebiusReal =
      -((M / (2 * q) : ℕ) : ℝ) := by
  have h2q : 2 * q = (2 * q - 1) + 1 := by have := hq.two_le; omega
  have h := sieveL2PrefixEnergy_moebius_step_eq_bandStep (2 * q - 1) M
  rw [← h2q] at h
  rw [h, moebiusBandStep_two_mul_prime hq hq2]
  have := hq.two_le
  have : M / (2 * q) < q + 2 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by linarith [mul_comm (q + 2) (2 * q)])
  omega

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
