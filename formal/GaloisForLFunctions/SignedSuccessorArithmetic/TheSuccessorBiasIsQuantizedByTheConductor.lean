import GaloisForLFunctions.SignedSuccessorArithmetic.TheOneThirdSuccessorFloor
import GaloisForLFunctions.SignedSuccessorArithmetic.SquareRootCancellationIsACount
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Data.Nat.Log

/-!
# The successor bias is quantized by the conductor

For an odd prime `p` and `ε ∈ {±1}`, the **Legendre twin** `f = f_{p,ε}` is the completely
multiplicative sign equal to the quadratic symbol `χ_p` off the multiples of `p` and to `ε` at `p`.
Splitting `[1, pJ]` into periods `pj + 1, …, pj + p`, each period contributes

* `Σ_{r=1}^{p-2} χ(r) χ(r+1) = -1` from the interior steps (the finite-field law of
  `SquareRootCancellationIsACount`), and
* `χ(-1) ε f(j+1) + ε f(j+1)` from the two steps adjacent to the multiple `p(j+1)`.

This gives the **exact identity** (`succCorr_legTwin`)

  `C(pJ) = -J + (1 + χ(-1)) ε M(J)`,  `M(J) = Σ_{j ≤ J} f(j)`.

For `p ≡ 3 (mod 4)` the junction terms cancel and `C(pJ) = -J` exactly
(`succCorr_legTwin_of_three_mod_four`). In general the summatory function is self-similar,
`M(pJ) = ε M(J)`, hence `|M(N)| ≤ p (log_p N + 1)` and `|C(pJ) + J| ≤ 2p (log_p J + 1)`
(`abs_succCorr_legTwin_add_le`), and at every scale `|C(N) + N/p| ≤ 2p (log_p N + 2)`
(`abs_succCorr_legTwin_add_div_le`): the mean successor sign of a prime-conductor twin is `-1/p`.
The bias is quantized by the conductor, and the one-third floor is its value at `p = 3`.
-/

namespace GaloisForLFunctions.SignedSuccessorArithmetic

open Finset

variable (p : ℕ) [hp : Fact p.Prime]

/-- The quadratic symbol modulo `p` of a natural number, in `{-1, 0, 1}`. -/
def legSym (n : ℕ) : ℤ := quadraticChar (ZMod p) (n : ZMod p)

/-- The quadratic symbol modulo `p` as a sign (`1` on multiples of `p`). -/
def legUnit (n : ℕ) : ℤˣ := if legSym p n = -1 then -1 else 1

variable {p}

theorem legSym_add_mul (n j : ℕ) : legSym p (n + p * j) = legSym p n := by
  simp [legSym]

theorem legSym_eq_zero_iff (n : ℕ) : legSym p n = 0 ↔ p ∣ n := by
  rw [legSym, quadraticChar_eq_zero_iff, ZMod.natCast_eq_zero_iff]

theorem legSym_one : legSym p 1 = 1 := by simp [legSym]

theorem legUnit_add_mul (n j : ℕ) : legUnit p (n + p * j) = legUnit p n := by
  simp only [legUnit, legSym_add_mul]

theorem legUnit_val {n : ℕ} (hn : ¬ p ∣ n) : ((legUnit p n : ℤˣ) : ℤ) = legSym p n := by
  have h0 : (n : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  unfold legUnit legSym
  rcases quadraticChar_dichotomy h0 with h | h <;> simp [h]

theorem legUnit_mul {m n : ℕ} (hm : ¬ p ∣ m) (hn : ¬ p ∣ n) :
    legUnit p (m * n) = legUnit p m * legUnit p n := by
  have hmn : ¬ p ∣ m * n := fun h => (hp.out.dvd_mul.mp h).elim hm hn
  ext
  rw [Units.val_mul, legUnit_val hmn, legUnit_val hm, legUnit_val hn, legSym, legSym, legSym,
    Nat.cast_mul, map_mul]

variable (p) in
/-- The **Legendre twin**: equal to the quadratic symbol off `p` and to `ε` at `p`. -/
def legTwin (ε : ℤˣ) : CMSign where
  toFun n := ε ^ n.factorization p * legUnit p (n / p ^ n.factorization p)
  map_one' := by simp [legUnit, legSym_one]
  map_mul' := fun {m n} hm hn => by
    have hf : (m * n).factorization p = m.factorization p + n.factorization p := by
      rw [Nat.factorization_mul hm.ne' hn.ne']; rfl
    rw [Nat.ordCompl_mul, hf, legUnit_mul (Nat.not_dvd_ordCompl hp.out hm.ne')
      (Nat.not_dvd_ordCompl hp.out hn.ne')]
    exact (congrArg (· * _) (pow_add ε _ _)).trans (mul_mul_mul_comm _ _ _ _)

variable (ε : ℤˣ)

theorem legTwin_of_not_dvd {n : ℕ} (hn : ¬ p ∣ n) : legTwin p ε n = legUnit p n := by
  change ε ^ n.factorization p * legUnit p (n / p ^ n.factorization p) = _
  rw [Nat.factorization_eq_zero_of_not_dvd hn]
  simp

theorem legTwin_prime : legTwin p ε p = ε := by
  change ε ^ p.factorization p * legUnit p (p / p ^ p.factorization p) = _
  rw [Nat.Prime.factorization_self hp.out]
  have h1 : legUnit p (p / p ^ 1) = 1 := by
    rw [pow_one, Nat.div_self hp.out.pos]; simp [legUnit, legSym_one]
  rw [h1, mul_one]
  exact pow_one ε

theorem legTwin_prime_mul {j : ℕ} (hj : 0 < j) : legTwin p ε (p * j) = ε * legTwin p ε j := by
  rw [(legTwin p ε).map_mul hp.out.pos hj, legTwin_prime]

/-- Off the multiples of `p` the twin is the quadratic symbol, periodically. -/
theorem legTwin_val_periodic {r : ℕ} (hr : ¬ p ∣ r) (J : ℕ) :
    ((legTwin p ε (p * J + r) : ℤˣ) : ℤ) = legSym p r := by
  have h : ¬ p ∣ p * J + r := fun h => hr ((Nat.dvd_add_right (dvd_mul_right p J)).mp h)
  rw [legTwin_of_not_dvd ε h, add_comm, legUnit_add_mul, legUnit_val hr]

/-! ## Finite-field inputs -/

theorem sum_zmod_eq_sum_range (h : ZMod p → ℤ) : ∑ x : ZMod p, h x = ∑ r ∈ range p, h r := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  symm
  refine Finset.sum_nbij' (fun r => (r : ZMod p)) (fun x => x.val) (by simp)
    (fun x _ => by simpa using ZMod.val_lt x) (fun r hr => ZMod.val_cast_of_lt (by simpa using hr))
    (fun x _ => ZMod.natCast_zmod_val x) (fun _ _ => rfl)

theorem ringChar_zmod_ne_two (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rwa [ZMod.ringChar_zmod_n]

/-- The interior steps of one period: `Σ_{r=1}^{p-2} χ(r) χ(r+1) = -1`. -/
theorem sum_legSym_succ_interior (hp2 : p ≠ 2) {q : ℕ} (hq : p = q + 2) :
    ∑ r ∈ range q, legSym p (r + 1) * legSym p (r + 2) = -1 := by
  have h := quadraticChar_succCorr (ringChar_zmod_ne_two hp2)
  rw [sum_zmod_eq_sum_range (fun x => quadraticChar (ZMod p) x * quadraticChar (ZMod p) (x + 1)),
    show range p = range (q + 2) by rw [hq], sum_range_succ', sum_range_succ] at h
  have h0 : quadraticChar (ZMod p) ((0 : ℕ) : ZMod p) = 0 := by simp
  have hq2 : quadraticChar (ZMod p) (((q + 1 : ℕ) : ZMod p) + 1) = 0 := by
    rw [quadraticChar_eq_zero_iff]
    have : (((q + 1 : ℕ) : ZMod p) + 1) = ((q + 2 : ℕ) : ZMod p) := by push_cast; ring
    rw [this, ← hq, ZMod.natCast_self]
  rw [h0, zero_mul, add_zero, hq2, mul_zero, add_zero] at h
  rw [← h]
  refine sum_congr rfl fun r _ => ?_
  simp only [legSym]
  push_cast
  ring_nf

/-- `Σ_{r=1}^{p-1} χ(r) = 0`. -/
theorem sum_legSym_period (hp2 : p ≠ 2) {q : ℕ} (hq : p = q + 2) :
    ∑ r ∈ range (q + 1), legSym p (r + 1) = 0 := by
  have h := quadraticChar_sum_zero (ringChar_zmod_ne_two hp2)
  rw [sum_zmod_eq_sum_range (fun x => quadraticChar (ZMod p) x),
    show range p = range (q + 1 + 1) by rw [hq], sum_range_succ'] at h
  simp only [Nat.cast_zero, quadraticChar_zero, add_zero] at h
  rw [← h]
  refine sum_congr rfl fun r _ => ?_
  simp [legSym]

theorem legSym_pred {q : ℕ} (hq : p = q + 2) :
    legSym p (q + 1) = quadraticChar (ZMod p) (-1) := by
  rw [legSym]
  congr 1
  have : ((q + 1 : ℕ) : ZMod p) + 1 = 0 := by
    have h : (((q + 2 : ℕ) : ZMod p)) = 0 := by rw [← hq, ZMod.natCast_self]
    push_cast at h ⊢; linear_combination h
  linear_combination this

/-! ## Block sums -/

theorem sum_Icc_add_range (g : ℕ → ℤ) (N m : ℕ) :
    ∑ n ∈ Icc 1 (N + m), g n = ∑ n ∈ Icc 1 N, g n + ∑ r ∈ range m, g (N + r + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, sum_Icc_succ_top (by omega), ih, sum_range_succ, add_assoc]

/-- The successor signs of one period `pJ + 1, …, pJ + p`. -/
theorem block_succCorr_legTwin (hp2 : p ≠ 2) {q : ℕ} (hq : p = q + 2) (J : ℕ) :
    ∑ r ∈ range p, (((succSign (legTwin p ε) (p * J + r + 1)) : ℤˣ) : ℤ) =
      -1 + (1 + quadraticChar (ZMod p) (-1)) * ε * (legTwin p ε (J + 1) : ℤ) := by
  have hint : ∀ r ∈ range q, (((succSign (legTwin p ε) (p * J + r + 1)) : ℤˣ) : ℤ) =
      legSym p (r + 1) * legSym p (r + 2) := by
    intro r hr
    have hr' : r < q := by simpa using hr
    rw [succSign, Units.val_mul, show p * J + r + 1 + 1 = p * J + (r + 2) by ring,
      show p * J + r + 1 = p * J + (r + 1) by ring,
      legTwin_val_periodic ε (fun h => by have := Nat.le_of_dvd (by omega) h; omega),
      legTwin_val_periodic ε (fun h => by have := Nat.le_of_dvd (by omega) h; omega)]
  have hlast1 : (((succSign (legTwin p ε) (p * J + q + 1)) : ℤˣ) : ℤ) =
      quadraticChar (ZMod p) (-1) * (ε * (legTwin p ε (J + 1) : ℤ)) := by
    rw [succSign, Units.val_mul, show p * J + q + 1 + 1 = p * (J + 1) by rw [hq]; ring,
      legTwin_prime_mul ε (by omega : 0 < J + 1), show p * J + q + 1 = p * J + (q + 1) by ring,
      legTwin_val_periodic ε (fun h => by have := Nat.le_of_dvd (by omega) h; omega),
      legSym_pred hq, Units.val_mul]
  have hlast2 : (((succSign (legTwin p ε) (p * J + (q + 1) + 1)) : ℤˣ) : ℤ) =
      ε * (legTwin p ε (J + 1) : ℤ) := by
    rw [succSign, Units.val_mul, show p * J + (q + 1) + 1 = p * (J + 1) by rw [hq]; ring,
      legTwin_prime_mul ε (by omega : 0 < J + 1), Units.val_mul,
      show p * (J + 1) + 1 = p * (J + 1) + 1 from rfl,
      legTwin_val_periodic ε (fun h => by have := Nat.le_of_dvd one_pos h; omega), legSym_one,
      mul_one]
  rw [show range p = range (q + 2) by rw [hq], sum_range_succ, sum_range_succ,
    sum_congr rfl hint, sum_legSym_succ_interior hp2 hq,
    hlast1, hlast2]
  ring

/-! ## The exact identity and the quantized bias -/

/-- The summatory function `M(N) = Σ_{n ≤ N} f(n)`. -/
def signSum (f : ℕ → ℤˣ) (N : ℕ) : ℤ := ∑ n ∈ Icc 1 N, ((f n : ℤˣ) : ℤ)

theorem signSum_succ (f : ℕ → ℤˣ) (J : ℕ) :
    signSum f (J + 1) = signSum f J + ((f (J + 1) : ℤˣ) : ℤ) := by
  rw [signSum, sum_Icc_succ_top (by omega), ← signSum]

/-- **Exact successor identity of a Legendre twin.** `C(pJ) = -J + (1 + χ(-1)) ε M(J)`. -/
theorem succCorr_legTwin (hp2 : p ≠ 2) (J : ℕ) :
    succCorr (legTwin p ε) (p * J) =
      -J + (1 + quadraticChar (ZMod p) (-1)) * ε * signSum (legTwin p ε) J := by
  obtain ⟨q, hq⟩ : ∃ q, p = q + 2 := ⟨p - 2, by have := hp.out.two_le; omega⟩
  induction J with
  | zero => simp [succCorr, signSum]
  | succ J ih =>
    rw [show p * (J + 1) = p * J + p by ring, succCorr, sum_Icc_add_range, ← succCorr, ih,
      block_succCorr_legTwin ε hp2 hq, signSum_succ]
    push_cast
    ring

/-- **Exact law for `p ≡ 3 (mod 4)`.** The junction terms cancel: `C(pJ) = -J`. -/
theorem succCorr_legTwin_of_three_mod_four (hp4 : p % 4 = 3) (J : ℕ) :
    succCorr (legTwin p ε) (p * J) = -J := by
  have hp2 : p ≠ 2 := by omega
  have hm1 : quadraticChar (ZMod p) (-1) = -1 := by
    rw [quadraticChar_neg_one (ringChar_zmod_ne_two hp2), ZMod.card,
      ZMod.χ₄_nat_three_mod_four hp4]
  rw [succCorr_legTwin ε hp2, hm1]
  ring

/-- The twin's summatory function is self-similar: `M(pJ) = ε M(J)`. -/
theorem signSum_legTwin_prime_mul (hp2 : p ≠ 2) (J : ℕ) :
    signSum (legTwin p ε) (p * J) = ε * signSum (legTwin p ε) J := by
  obtain ⟨q, hq⟩ : ∃ q, p = q + 2 := ⟨p - 2, by have := hp.out.two_le; omega⟩
  induction J with
  | zero => simp [signSum]
  | succ J ih =>
    rw [show p * (J + 1) = p * J + p by ring, signSum, sum_Icc_add_range, ← signSum, ih,
      show range p = range (q + 1 + 1) by rw [hq], sum_range_succ]
    have hint : ∀ r ∈ range (q + 1), ((legTwin p ε (p * J + r + 1) : ℤˣ) : ℤ) = legSym p (r + 1) := by
      intro r hr
      have hr' : r < q + 1 := by simpa using hr
      rw [show p * J + r + 1 = p * J + (r + 1) by ring,
        legTwin_val_periodic ε (fun h => by have := Nat.le_of_dvd (by omega) h; omega)]
    rw [sum_congr rfl hint, sum_legSym_period hp2 hq,
      show p * J + (q + 1) + 1 = p * (J + 1) by rw [hq]; ring, legTwin_prime_mul ε (by omega : 0 < J + 1),
      signSum_succ]
    push_cast
    ring

/-- Partial periods: `M(pJ + s) = ε M(J) + Σ_{r=1}^{s} χ(r)` for `s < p`. -/
theorem signSum_legTwin_add (hp2 : p ≠ 2) (J : ℕ) {s : ℕ} (hs : s < p) :
    signSum (legTwin p ε) (p * J + s) =
      ε * signSum (legTwin p ε) J + ∑ r ∈ range s, legSym p (r + 1) := by
  rw [signSum, sum_Icc_add_range, ← signSum, signSum_legTwin_prime_mul ε hp2]
  congr 1
  refine sum_congr rfl fun r hr => ?_
  have hr' : r < s := by simpa using hr
  rw [show p * J + r + 1 = p * J + (r + 1) by ring,
    legTwin_val_periodic ε (fun h => by have := Nat.le_of_dvd (by omega) h; omega)]

theorem abs_legSym_le_one (n : ℕ) : |legSym p n| ≤ 1 := by
  unfold legSym
  by_cases h : (n : ZMod p) = 0
  · simp [h]
  · rcases quadraticChar_dichotomy h with h' | h' <;> simp [h']

/-- **Logarithmic size of the summatory function.** `|M(N)| ≤ p (log_p N + 1)`. -/
theorem abs_signSum_legTwin_le (hp2 : p ≠ 2) (N : ℕ) :
    |signSum (legTwin p ε) N| ≤ p * (Nat.log p N + 1) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    have hmod : N % p < p := Nat.mod_lt N hp.out.pos
    have hpart : |∑ r ∈ range (N % p), legSym p (r + 1)| ≤ (N % p : ℕ) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ r ∈ range (N % p), |legSym p (r + 1)| ≤ ∑ r ∈ range (N % p), (1 : ℤ) :=
            sum_le_sum fun r _ => abs_legSym_le_one _
        _ = (N % p : ℕ) := by simp
    have hε : |((ε : ℤˣ) : ℤ)| = 1 := by rcases Int.units_eq_one_or ε with h | h <;> simp [h]
    have hsplit : signSum (legTwin p ε) N =
        ε * signSum (legTwin p ε) (N / p) + ∑ r ∈ range (N % p), legSym p (r + 1) := by
      conv_lhs => rw [← Nat.div_add_mod N p]
      exact signSum_legTwin_add ε hp2 _ hmod
    rw [hsplit]
    rcases Nat.lt_or_ge N p with hNp | hNp
    · have hs0 : signSum (legTwin p ε) 0 = 0 := by simp [signSum]
      rw [Nat.div_eq_of_lt hNp, hs0, mul_zero, zero_add]
      have hle : ((N % p : ℕ) : ℤ) ≤ p := by exact_mod_cast hmod.le
      have h0 : (0 : ℤ) ≤ Nat.log p N := Nat.cast_nonneg _
      calc _ ≤ ((N % p : ℕ) : ℤ) := hpart
        _ ≤ (p : ℤ) * (Nat.log p N + 1) := by nlinarith
    · have hJ : N / p < N := Nat.div_lt_self (by omega) hp.out.one_lt
      have ih' := ih (N / p) hJ
      have hlog : Nat.log p N = Nat.log p (N / p) + 1 := by
        rw [Nat.log_div_base]
        have : 1 ≤ Nat.log p N := Nat.log_pos hp.out.one_lt hNp
        omega
      calc |ε * signSum (legTwin p ε) (N / p) + ∑ r ∈ range (N % p), legSym p (r + 1)|
          ≤ |ε * signSum (legTwin p ε) (N / p)| + |∑ r ∈ range (N % p), legSym p (r + 1)| :=
            abs_add_le _ _
        _ ≤ p * (Nat.log p (N / p) + 1) + p := by
            rw [abs_mul, hε, one_mul]
            have : ((N % p : ℕ) : ℤ) ≤ p := by exact_mod_cast hmod.le
            linarith
        _ = p * (Nat.log p N + 1) := by rw [hlog]; push_cast; ring

/-- **The successor bias of a prime-conductor twin is `-1/p`.**
`|C(pJ) + J| ≤ 2p (log_p J + 1)`. -/
theorem abs_succCorr_legTwin_add_le (hp2 : p ≠ 2) (J : ℕ) :
    |succCorr (legTwin p ε) (p * J) + J| ≤ 2 * p * (Nat.log p J + 1) := by
  rw [succCorr_legTwin ε hp2, show -(J : ℤ) + (1 + quadraticChar (ZMod p) (-1)) * ε *
    signSum (legTwin p ε) J + J = (1 + quadraticChar (ZMod p) (-1)) * ε *
    signSum (legTwin p ε) J by ring, abs_mul, abs_mul]
  have h1 : |1 + quadraticChar (ZMod p) (-1)| ≤ 2 := by
    have : (-1 : ℂ) ≠ 0 := by norm_num
    rcases quadraticChar_dichotomy (F := ZMod p) (a := -1) (neg_ne_zero.mpr one_ne_zero) with h | h <;>
      simp [h]
  have hε : |((ε : ℤˣ) : ℤ)| = 1 := by rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  have hM := abs_signSum_legTwin_le ε hp2 J
  rw [hε, mul_one]
  have hM0 : 0 ≤ |signSum (legTwin p ε) J| := abs_nonneg _
  calc |1 + quadraticChar (ZMod p) (-1)| * |signSum (legTwin p ε) J|
      ≤ 2 * (p * (Nat.log p J + 1)) := mul_le_mul h1 hM hM0 (by norm_num)
    _ = 2 * p * (Nat.log p J + 1) := by ring

/-- **The bias law at every scale.** `|C(N) + N/p| ≤ 2p (log_p N + 2)` for every `N`: the successor
correlation of a prime-conductor twin is `−N/p` up to a logarithmic error. -/
theorem abs_succCorr_legTwin_add_div_le (hp2 : p ≠ 2) (N : ℕ) :
    |(succCorr (legTwin p ε) N : ℝ) + N / p| ≤ 2 * p * (Nat.log p N + 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  set J := N / p
  set s := N % p
  have hN : N = p * J + s := (Nat.div_add_mod N p).symm
  have hs : s < p := Nat.mod_lt N hp.out.pos
  -- the partial period changes `C` by at most `s`
  have hpart : |succCorr (legTwin p ε) N - succCorr (legTwin p ε) (p * J)| ≤ s := by
    have hsplit : succCorr (legTwin p ε) (p * J + s) = succCorr (legTwin p ε) (p * J) +
        ∑ r ∈ range s, (((succSign (legTwin p ε) (p * J + r + 1)) : ℤˣ) : ℤ) := by
      rw [succCorr, sum_Icc_add_range, ← succCorr]
    rw [hN, hsplit, add_sub_cancel_left]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ r ∈ range s, |(((succSign (legTwin p ε) (p * J + r + 1)) : ℤˣ) : ℤ)|
        ≤ ∑ _r ∈ range s, (1 : ℤ) := sum_le_sum fun r _ => by
          rcases Int.units_eq_one_or (succSign (legTwin p ε) (p * J + r + 1)) with h | h <;> simp [h]
      _ = s := by simp
  have hmain := abs_succCorr_legTwin_add_le ε hp2 J
  have hlog : Nat.log p J ≤ Nat.log p N := Nat.log_mono_right (Nat.div_le_self N p)
  have hNp : (N : ℝ) / p = J + s / p := by
    rw [hN]; push_cast; field_simp
  have hs' : (s : ℝ) / p ≤ 1 := by
    rw [div_le_one hp0]; exact_mod_cast hs.le
  have hs0 : (0 : ℝ) ≤ s / p := by positivity
  have hpartR : |(succCorr (legTwin p ε) N : ℝ) - succCorr (legTwin p ε) (p * J)| ≤ s := by
    exact_mod_cast hpart
  have hmainR : |(succCorr (legTwin p ε) (p * J) : ℝ) + J| ≤ 2 * p * (Nat.log p J + 1) := by
    exact_mod_cast hmain
  have hsp : (s : ℝ) ≤ p := by exact_mod_cast hs.le
  have hlogR : (Nat.log p J : ℝ) ≤ Nat.log p N := by exact_mod_cast hlog
  rw [hNp]
  calc |(succCorr (legTwin p ε) N : ℝ) + (J + s / p)|
      = |((succCorr (legTwin p ε) N : ℝ) - succCorr (legTwin p ε) (p * J)) +
          ((succCorr (legTwin p ε) (p * J) : ℝ) + J) + s / p| := by ring_nf
    _ ≤ |(succCorr (legTwin p ε) N : ℝ) - succCorr (legTwin p ε) (p * J)| +
          |(succCorr (legTwin p ε) (p * J) : ℝ) + J| + |(s : ℝ) / p| := abs_add_three _ _ _
    _ ≤ s + 2 * p * (Nat.log p J + 1) + 1 := by
        rw [abs_of_nonneg hs0]; linarith
    _ ≤ 2 * p * (Nat.log p N + 2) := by
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
        nlinarith [mul_nonneg hp0.le (sub_nonneg.mpr hlogR)]

end GaloisForLFunctions.SignedSuccessorArithmetic
