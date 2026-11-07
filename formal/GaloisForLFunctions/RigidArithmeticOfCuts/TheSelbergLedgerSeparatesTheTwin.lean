import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheLedgerIsBlindToTheLiouvilleTwin
import GaloisForLFunctions.ArithmeticKreinLangerTheory.FinitePrimeHeckeAuxiliaryObstructions

/-!
# The Selberg ledger separates the twin

A linear ledger reads a weight through `Σ_d a(d) g(⌊N/d⌋)`, and it cannot separate `Λ` from the Liouville
twin `−λΛ` below `w √N`. The twin differs from `Λ` only on even prime powers, whose partial sum is
`2 ψ(√N)`.

Convolution changes the scale. The quadratic reading of `Λ ∗ Λ` is exact together with `Λ log`:
`(Λ log + Λ ∗ Λ) ∗ 1 = log²`, so the Selberg ledger of `Λ` is a sum of `log² m` with no prime in it. Replace
`Λ` by its twin and the cross term `Λ ∗ (Λ·1_{Ω even})` contains the main term of `Λ` read at `N/4`, of size
`N`. So **the Selberg ledger of the twin leaves the exact value at scale `N`**, not `√N`.

The reading has an exact value on `Λ` and a linear gap on the twin. It does not break sieve parity: the gap reads
the local factors at prime squares, and it gives no saving for `Λ` itself.
-/

open Finset
open ArithmeticFunction (vonMangoldt cardFactors)
open GaloisForLFunctions.ArithmeticKreinLangerTheory
open GaloisForLFunctions.ArithmeticAuxiliaryDynamics
open GaloisForLFunctions.ArithmeticOfSquareRootPrecision

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-! ### Dirichlet convolution of weights -/

/-- The Dirichlet convolution of two weights on the integers. -/
def conv (a b : ℕ → ℝ) (n : ℕ) : ℝ := ∑ d ∈ n.divisors, a d * b (n / d)

theorem conv_comm (a b : ℕ → ℝ) (n : ℕ) : conv a b n = conv b a n := by
  have h1 := Nat.sum_divisorsAntidiagonal (n := n) fun x y => a x * b y
  have h2 := Nat.sum_divisorsAntidiagonal' (n := n) fun x y => a x * b y
  rw [conv, conv, ← h1, h2]
  exact sum_congr rfl fun d _ => mul_comm _ _

theorem conv_add_left (a a' b : ℕ → ℝ) (n : ℕ) :
    conv (fun d => a d + a' d) b n = conv a b n + conv a' b n := by
  simp only [conv, add_mul, sum_add_distrib]

theorem conv_smul_left (t : ℝ) (a b : ℕ → ℝ) (n : ℕ) :
    conv (fun d => t * a d) b n = t * conv a b n := by
  simp only [conv, mul_sum, mul_assoc]

/-- **The hyperbola identity.** -/
theorem sum_Ioc_sum_divisors (F : ℕ → ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, F d (n / d) =
      ∑ e ∈ Ioc 0 N, ∑ d ∈ Ioc 0 (N / e), F d e := by
  rw [sum_sigma', sum_sigma']
  refine sum_bij' (fun x _ => ⟨x.1 / x.2, x.2⟩) (fun x _ => ⟨x.2 * x.1, x.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, d⟩ hx
    simp only [mem_sigma, mem_Ioc, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨hn0, hnN⟩, hd, -⟩ := hx
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hn0
    have hpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn0 hd) hd0
    refine ⟨⟨hpos, (Nat.div_le_self n d).trans hnN⟩, hd0, (Nat.le_div_iff_mul_le hpos).mpr ?_⟩
    rwa [Nat.mul_div_cancel' hd]
  · rintro ⟨e, d⟩ hx
    simp only [mem_sigma, mem_Ioc, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨he0, heN⟩, hd0, hdN⟩ := hx
    have hle := (Nat.le_div_iff_mul_le he0).mp hdN
    refine ⟨⟨Nat.mul_pos hd0 he0, hle⟩, dvd_mul_right d e, (Nat.mul_pos hd0 he0).ne'⟩
  · rintro ⟨n, d⟩ hx
    simp only [mem_sigma, mem_Ioc, Nat.mem_divisors] at hx
    simp only [Nat.mul_div_cancel' hx.2.1]
  · rintro ⟨e, d⟩ hx
    simp only [mem_sigma, mem_Ioc] at hx
    simp only [Nat.mul_div_cancel_left e hx.2.1]
  · rintro ⟨n, d⟩ _
    rfl

/-- Partial sums of a weight, read through a floor. -/
theorem sum_Ioc_mul_div (a : ℕ → ℝ) (M : ℕ) :
    ∑ e ∈ Ioc 0 M, a e * ((M / e : ℕ) : ℝ) = ∑ m ∈ Ioc 0 M, ∑ d ∈ m.divisors, a d := by
  have h := sum_Ioc_sum_divisors (fun _ e => a e) M
  have h2 : ∑ m ∈ Ioc 0 M, ∑ d ∈ m.divisors, a (m / d) = ∑ m ∈ Ioc 0 M, ∑ d ∈ m.divisors, a d :=
    sum_congr rfl fun m _ => Nat.sum_div_divisors m a
  rw [← h2, h]
  refine sum_congr rfl fun e _ => ?_
  simp [mul_comm]

/-! ### Ledgers of convolutions -/

theorem ledger_sub (c : ℕ →₀ ℤ) (a b : ℕ → ℝ) (N : ℕ) :
    ledger c (fun d => a d - b d) N = ledger c a N - ledger c b N := by
  simp only [ledger, sub_mul, sum_sub_distrib]

theorem ledger_add (c : ℕ →₀ ℤ) (a b : ℕ → ℝ) (N : ℕ) :
    ledger c (fun d => a d + b d) N = ledger c a N + ledger c b N := by
  simp only [ledger, add_mul, sum_add_distrib]

theorem ledger_smul (c : ℕ →₀ ℤ) (t : ℝ) (a : ℕ → ℝ) (N : ℕ) :
    ledger c (fun d => t * a d) N = t * ledger c a N := by
  simp only [ledger, mul_sum, mul_assoc]

/-- **The ledger of a convolution is a ledger of ledgers.** -/
theorem ledger_conv (c : ℕ →₀ ℤ) (a b : ℕ → ℝ) (N : ℕ) :
    ledger c (conv a b) N = ∑ e ∈ Ioc 0 N, b e * ledger c a (N / e) := by
  have h := sum_Ioc_sum_divisors (fun d e => a d * b e * (stepWeight c (N / (d * e)) : ℝ)) N
  have hL : ledger c (conv a b) N = ∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors,
      a d * b (n / d) * (stepWeight c (N / (d * (n / d))) : ℝ) := by
    simp only [ledger, conv, sum_mul]
    refine sum_congr rfl fun n _ => sum_congr rfl fun d hd => ?_
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  rw [hL, h]
  refine sum_congr rfl fun e _ => ?_
  rw [ledger, mul_sum]
  refine sum_congr rfl fun d _ => ?_
  rw [mul_comm d e, ← Nat.div_div_eq_div_mul]
  ring

/-- **A ledger is exact when the weight convolves to a known function.** -/
theorem ledger_eq_sum_coeff {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (a : ℕ → ℝ) (N : ℕ) :
    ledger c a N = ∑ k ∈ c.support, (c k : ℝ) * ∑ m ∈ Ioc 0 (N / k), ∑ d ∈ m.divisors, a d := by
  have hstep : ∀ r, (stepWeight c r : ℝ) = ∑ k ∈ c.support, (c k : ℝ) * ((r / k : ℕ) : ℝ) := by
    intro r
    rw [stepWeight]
    push_cast
    rfl
  simp only [ledger, hstep, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun k hk => ?_
  have hk0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hc0
  have hk1 : 0 < k := Nat.pos_of_ne_zero hk0
  rw [← sum_Ioc_mul_div]
  have hsub : Ioc 0 (N / k) ⊆ Ioc 0 N := Ioc_subset_Ioc_right (Nat.div_le_self N k)
  rw [← sum_subset hsub]
  · refine sum_congr rfl fun d _ => ?_
    rw [Nat.div_div_eq_div_mul, mul_comm d k, ← Nat.div_div_eq_div_mul]
    ring
  · intro d hd hd2
    have hd0 := (mem_Ioc.mp hd).1
    have hlt : N / k < d := by
      by_contra hle
      exact hd2 (mem_Ioc.mpr ⟨hd0, not_lt.mp hle⟩)
    rw [Nat.div_div_eq_div_mul, mul_comm d k, ← Nat.div_div_eq_div_mul, Nat.div_eq_of_lt hlt]
    simp

/-! ### Selberg's weight -/

/-- Selberg's weight `a log + a ∗ a`. -/
def selbergWeight (a : ℕ → ℝ) (n : ℕ) : ℝ := a n * Real.log n + conv a a n

theorem conv_vonMangoldt_eq (n : ℕ) :
    conv vonMangoldtWeight vonMangoldtWeight n =
      (ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) n := by
  rw [ArithmeticFunction.mul_apply, conv]
  exact (Nat.sum_divisorsAntidiagonal (n := n) fun x y => vonMangoldt x * vonMangoldt y).symm

/-- **Selberg's identity:** `(Λ log + Λ ∗ Λ) ∗ 1 = log²`. -/
theorem sum_divisors_selbergWeight {n : ℕ} (hn : 1 ≤ n) :
    ∑ d ∈ n.divisors, selbergWeight vonMangoldtWeight d = Real.log n ^ 2 := by
  have hn0 : n ≠ 0 := by omega
  have hconv : ∑ d ∈ n.divisors, conv vonMangoldtWeight vonMangoldtWeight d =
      ∑ d ∈ n.divisors, vonMangoldt d * Real.log ((n / d : ℕ) : ℝ) := by
    simp_rw [conv_vonMangoldt_eq]
    have h1 := ArithmeticFunction.coe_mul_zeta_apply
      (f := ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) (x := n)
    rw [← h1, mul_assoc, ArithmeticFunction.vonMangoldt_mul_zeta, ArithmeticFunction.mul_apply]
    exact Nat.sum_divisorsAntidiagonal (n := n) fun x y =>
      vonMangoldt x * ArithmeticFunction.log y
  have hlog : Real.log n ^ 2 = ∑ d ∈ n.divisors, vonMangoldt d * Real.log n := by
    rw [← sum_mul, ArithmeticFunction.vonMangoldt_sum, sq]
  have hsplit : ∑ d ∈ n.divisors, selbergWeight vonMangoldtWeight d =
      ∑ d ∈ n.divisors, vonMangoldt d * Real.log d +
        ∑ d ∈ n.divisors, conv vonMangoldtWeight vonMangoldtWeight d := by
    simp only [selbergWeight, sum_add_distrib]
  rw [hlog, hsplit, hconv, ← sum_add_distrib]
  refine sum_congr rfl fun d hd => ?_
  have hdvd := Nat.dvd_of_mem_divisors hd
  have hd0 : d ≠ 0 := fun h => hn0 (by rw [h, zero_dvd_iff] at hdvd; exact hdvd)
  have hq : ((n / d : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (Nat.pos_of_ne_zero hd0)).ne'
  have hmul : (n : ℝ) = (d : ℝ) * ((n / d : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_div_cancel' hdvd).symm
  rw [hmul, Real.log_mul (by exact_mod_cast hd0) hq]
  ring

/-- **The Selberg ledger of `Λ` is exact.** It involves no prime. -/
theorem ledger_selbergWeight {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (N : ℕ) :
    ledger c (selbergWeight vonMangoldtWeight) N =
      ∑ k ∈ c.support, (c k : ℝ) * ∑ m ∈ Ioc 0 (N / k), Real.log m ^ 2 := by
  rw [ledger_eq_sum_coeff hc0]
  refine sum_congr rfl fun k _ => ?_
  congr 1
  exact sum_congr rfl fun m hm => sum_divisors_selbergWeight (mem_Ioc.mp hm).1

/-! ### The twin -/

/-- The Liouville twin `−λΛ = Λ − 2 Λ 1_{Ω even}`. -/
def twinWeight (n : ℕ) : ℝ := -liouvilleWeight n

theorem twinWeight_eq (n : ℕ) : twinWeight n = vonMangoldtWeight n - 2 * evenVonMangoldt n := by
  rw [twinWeight, liouvilleWeight_eq]
  ring

theorem evenVonMangoldt_nonneg (n : ℕ) : 0 ≤ evenVonMangoldt n := by
  unfold evenVonMangoldt
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl

theorem evenVonMangoldt_four : evenVonMangoldt 4 = Real.log 2 := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  have heven : Even (cardFactors 4) := by
    rw [h4, ArithmeticFunction.cardFactors_apply_prime_pow Nat.prime_two]
    decide
  rw [evenVonMangoldt, if_pos heven, h4, ArithmeticFunction.vonMangoldt_apply_pow two_ne_zero,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- The quadratic ledger of the twin against that of `Λ`. -/
theorem ledger_conv_twin_sub (c : ℕ →₀ ℤ) (N : ℕ) :
    ledger c (conv twinWeight twinWeight) N -
        ledger c (conv vonMangoldtWeight vonMangoldtWeight) N =
      -4 * ledger c (conv vonMangoldtWeight evenVonMangoldt) N +
        4 * ledger c (conv evenVonMangoldt evenVonMangoldt) N := by
  have hexp : ∀ n, conv twinWeight twinWeight n = conv vonMangoldtWeight vonMangoldtWeight n +
      (-4 * conv vonMangoldtWeight evenVonMangoldt n +
        4 * conv evenVonMangoldt evenVonMangoldt n) := by
    intro n
    have htw : twinWeight = fun d => vonMangoldtWeight d + (-2) * evenVonMangoldt d := by
      funext d
      rw [twinWeight_eq]
      ring
    have hright : ∀ a : ℕ → ℝ, conv a twinWeight n = conv a vonMangoldtWeight n +
        (-2) * conv a evenVonMangoldt n := by
      intro a
      rw [conv_comm, htw, conv_add_left, conv_smul_left, conv_comm vonMangoldtWeight,
        conv_comm evenVonMangoldt]
    rw [htw, conv_add_left, conv_smul_left]
    rw [← htw, hright, hright, conv_comm evenVonMangoldt vonMangoldtWeight]
    ring
  have hL : ledger c (conv twinWeight twinWeight) N = ledger c (fun d =>
      conv vonMangoldtWeight vonMangoldtWeight d + (-4 * conv vonMangoldtWeight evenVonMangoldt d +
        4 * conv evenVonMangoldt evenVonMangoldt d)) N := by
    simp only [ledger, hexp]
  rw [hL, ledger_add, ledger_add, ledger_smul, ledger_smul]
  ring

variable {c : ℕ →₀ ℤ} {m B : ℕ}

theorem ledger_nonneg (hP : IsProducer c m B) {a : ℕ → ℝ} (ha : ∀ d, 0 ≤ a d) (N : ℕ) :
    0 ≤ ledger c a N :=
  sum_nonneg fun d _ => mul_nonneg (ha d) (by exact_mod_cast hP.nonneg _)

theorem ledger_le (hP : IsProducer c m B) {a : ℕ → ℝ} (ha : ∀ d, 0 ≤ a d) (N : ℕ) :
    ledger c a N ≤ (peak c : ℝ) * ∑ d ∈ Ioc 0 N, a d := by
  rw [mul_sum]
  refine sum_le_sum fun d _ => ?_
  have h : (stepWeight c (N / d) : ℝ) ≤ peak c := by exact_mod_cast hP.stepWeight_le_peak _
  calc a d * (stepWeight c (N / d) : ℝ) ≤ a d * (peak c : ℝ) := mul_le_mul_of_nonneg_left h (ha d)
    _ = _ := mul_comm _ _

private lemma psi_nat_le (n : ℕ) :
    Chebyshev.psi (n : ℝ) ≤ (Real.log 4 + 4) * (n : ℝ) :=
  Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)

private lemma sum_even_le (n : ℕ) :
    ∑ d ∈ Ioc 0 n, evenVonMangoldt d ≤ (Real.log 4 + 4) * (Nat.sqrt n : ℝ) := by
  rw [sum_evenVonMangoldt]
  exact psi_nat_le _

private lemma psi_sqrt_mono {a b : ℕ} (h : a ≤ b) :
    Chebyshev.psi (Nat.sqrt a : ℝ) ≤ Chebyshev.psi (Nat.sqrt b : ℝ) :=
  Chebyshev.psi_mono (by exact_mod_cast Nat.sqrt_le_sqrt h)

/-- The convolution of the even part with itself has size `N^{3/4}`. -/
theorem ledger_conv_even_le (hP : IsProducer c m B) (N : ℕ) :
    ledger c (conv evenVonMangoldt evenVonMangoldt) N ≤
      2 * (peak c : ℝ) * (Real.log 4 + 4) ^ 2 * (Nat.sqrt (Nat.sqrt N) : ℝ) * (Nat.sqrt N : ℝ) := by
  have hb := evenVonMangoldt_nonneg
  have hw : (0 : ℝ) ≤ peak c := by
    have h1 := hP.nonneg 0
    have h2 := hP.stepWeight_le_peak 0
    exact_mod_cast h1.trans h2
  have hC : (0 : ℝ) ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith
  set s := Nat.sqrt N with hs
  set S : ℕ → ℝ := fun n => ∑ d ∈ Ioc 0 n, evenVonMangoldt d with hS
  have hSnn : ∀ n, 0 ≤ S n := fun n => sum_nonneg fun d _ => hb d
  have hSpsi : ∀ n, S n = Chebyshev.psi (Nat.sqrt n : ℝ) := fun n => sum_evenVonMangoldt n
  have hSmono : ∀ {a b : ℕ}, a ≤ b → S a ≤ S b := fun {a b} h => by
    rw [hSpsi, hSpsi]
    exact psi_sqrt_mono h
  have hterm : ∀ e ∈ Ioc 0 N, evenVonMangoldt e * ledger c evenVonMangoldt (N / e) ≤
      evenVonMangoldt e * ((peak c : ℝ) * S (N / e)) := fun e _ =>
    mul_le_mul_of_nonneg_left (ledger_le hP hb _) (hb e)
  rw [ledger_conv]
  refine (sum_le_sum hterm).trans ?_
  have hsN : s ≤ N := Nat.sqrt_le_self N
  have hunion : Ioc 0 N = Ioc 0 s ∪ Ioc s N := (Ioc_union_Ioc_eq_Ioc (Nat.zero_le s) hsN).symm
  have hdisj : Disjoint (Ioc 0 s) (Ioc s N) := by
    rw [disjoint_left]
    intro x h1 h2
    have := (mem_Ioc.mp h1).2
    have := (mem_Ioc.mp h2).1
    omega
  rw [hunion, sum_union hdisj]
  have hlow : ∑ e ∈ Ioc 0 s, evenVonMangoldt e * ((peak c : ℝ) * S (N / e)) ≤
      S s * ((peak c : ℝ) * S N) := by
    rw [hS, sum_mul]
    refine sum_le_sum fun e he => ?_
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hSmono (Nat.div_le_self N e)) hw) (hb e)
  have hhigh : ∑ e ∈ Ioc s N, evenVonMangoldt e * ((peak c : ℝ) * S (N / e)) ≤
      S N * ((peak c : ℝ) * S s) := by
    have hsub : ∑ e ∈ Ioc s N, evenVonMangoldt e ≤ S N :=
      sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_left (Nat.zero_le s)) fun d _ _ => hb d
    calc _ ≤ ∑ e ∈ Ioc s N, evenVonMangoldt e * ((peak c : ℝ) * S s) := by
          refine sum_le_sum fun e he => ?_
          obtain ⟨he1, -⟩ := mem_Ioc.mp he
          have hdiv : N / e ≤ s := by
            have hlt : N / e < s + 1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr
              ((Nat.lt_succ_sqrt N).trans_le (Nat.mul_le_mul_left _ he1))
            exact Nat.lt_succ_iff.mp hlt
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hSmono hdiv) hw) (hb e)
      _ = (∑ e ∈ Ioc s N, evenVonMangoldt e) * ((peak c : ℝ) * S s) := by rw [sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hsub (mul_nonneg hw (hSnn s))
  have h1 : S s ≤ (Real.log 4 + 4) * (Nat.sqrt s : ℝ) := sum_even_le s
  have h2 : S N ≤ (Real.log 4 + 4) * (s : ℝ) := sum_even_le N
  have hprod : S s * S N ≤ ((Real.log 4 + 4) * (Nat.sqrt s : ℝ)) * ((Real.log 4 + 4) * (s : ℝ)) :=
    mul_le_mul h1 h2 (hSnn N) (by positivity)
  have hfinal : S s * ((peak c : ℝ) * S N) + S N * ((peak c : ℝ) * S s) =
      2 * (peak c : ℝ) * (S s * S N) := by ring
  calc _ ≤ S s * ((peak c : ℝ) * S N) + S N * ((peak c : ℝ) * S s) := add_le_add hlow hhigh
    _ = 2 * (peak c : ℝ) * (S s * S N) := hfinal
    _ ≤ 2 * (peak c : ℝ) * (((Real.log 4 + 4) * (Nat.sqrt s : ℝ)) * ((Real.log 4 + 4) * (s : ℝ))) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := by ring

/-- A producer has positive slope. -/
theorem stencilSlope_pos (hP : IsProducer c m B) : 0 < stencilSlope c := by
  have hm := hP.m_pos
  have h1 := hP.one_sub_pos
  have hr := hP.rate_pos
  rw [rate, normSlope, sub_pos, one_lt_div (mul_pos hm h1)] at hr
  exact (mul_pos hm h1).trans hr

/-- The cross term contains the main term of `Λ` read at `N/4`. -/
theorem le_ledger_conv_vonMangoldt_even (hP : IsProducer c m B) {N : ℕ} (hN : 4 ≤ N) :
    Real.log 2 * (stencilSlope c * ((N : ℝ) / 4 - 1) - stencilErrorConst c * (1 + Real.log N)) ≤
      ledger c (conv vonMangoldtWeight evenVonMangoldt) N := by
  have hvM : ∀ d, 0 ≤ vonMangoldtWeight d := fun d => ArithmeticFunction.vonMangoldt_nonneg
  have hb := evenVonMangoldt_nonneg
  have hmem : 4 ∈ Ioc 0 N := mem_Ioc.mpr ⟨by norm_num, hN⟩
  have hnn : ∀ e ∈ Ioc 0 N, 0 ≤ evenVonMangoldt e * ledger c vonMangoldtWeight (N / e) := fun e _ =>
    mul_nonneg (hb e) (ledger_nonneg hP hvM _)
  have hsingle := single_le_sum hnn hmem
  rw [ledger_conv]
  refine le_trans ?_ hsingle
  rw [evenVonMangoldt_four]
  refine mul_le_mul_of_nonneg_left ?_ (Real.log_nonneg (by norm_num))
  set M := N / 4 with hM
  have hM1 : 1 ≤ M := (Nat.one_le_div_iff (by norm_num)).mpr hN
  have hlog : ledger c vonMangoldtWeight M = Real.log (stencilInt c M : ℝ) := by
    rw [log_stencilInt_eq_vonMangoldt hP.zero hP.nonneg]
    rfl
  rw [hlog]
  have habs := abs_le.mp (abs_log_stencilInt_sub_slope_le hP.zero hP.balanced hP.nonneg hM1)
  have hE := stencilErrorConst_nonneg c
  have hslope := stencilSlope_pos hP
  have hMN : (N : ℝ) / 4 - 1 ≤ (M : ℝ) := by
    have h1 : N < 4 * (M + 1) := by
      rw [hM]
      omega
    have h2 : (N : ℝ) < 4 * ((M : ℝ) + 1) := by exact_mod_cast h1
    linarith
  have hlogM : Real.log (M : ℝ) ≤ Real.log (N : ℝ) := by
    refine Real.log_le_log (by exact_mod_cast hM1) ?_
    exact_mod_cast Nat.div_le_self N 4
  have h1 : stencilSlope c * ((N : ℝ) / 4 - 1) ≤ stencilSlope c * (M : ℝ) :=
    mul_le_mul_of_nonneg_left hMN hslope.le
  have h2 : stencilErrorConst c * (1 + Real.log (M : ℝ)) ≤ stencilErrorConst c * (1 + Real.log N) :=
    mul_le_mul_of_nonneg_left (by linarith) hE
  linarith [habs.1]

/-- **The quadratic reading of the twin leaves that of `Λ` at scale `N`.** -/
theorem ledger_conv_twin_sub_le (hP : IsProducer c m B) {N : ℕ} (hN : 4 ≤ N) :
    ledger c (conv twinWeight twinWeight) N -
        ledger c (conv vonMangoldtWeight vonMangoldtWeight) N ≤
      -(Real.log 2 * stencilSlope c * N) + 4 * Real.log 2 * stencilSlope c +
        4 * Real.log 2 * stencilErrorConst c * (1 + Real.log N) +
        8 * (peak c : ℝ) * (Real.log 4 + 4) ^ 2 * (Nat.sqrt (Nat.sqrt N) : ℝ) * (Nat.sqrt N : ℝ) := by
  rw [ledger_conv_twin_sub]
  have h1 := le_ledger_conv_vonMangoldt_even hP hN
  have h2 := ledger_conv_even_le hP N
  nlinarith

/-- **The twin gap.** For a producer the quadratic reading of the twin lies below that of `Λ` by at
least a fixed multiple of `N`, for all large `N`. -/
theorem exists_ledger_conv_twin_gap (hP : IsProducer c m B) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ledger c (conv twinWeight twinWeight) N ≤
      ledger c (conv vonMangoldtWeight vonMangoldtWeight) N -
        Real.log 2 / 2 * stencilSlope c * N := by
  have hslope := stencilSlope_pos hP
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hE := stencilErrorConst_nonneg c
  have hw : (0 : ℝ) ≤ peak c := by
    have h1 := hP.nonneg 0
    have h2 := hP.stepWeight_le_peak 0
    exact_mod_cast h1.trans h2
  set L : ℝ := Real.log 2 * stencilSlope c with hL
  have hLpos : 0 < L := mul_pos hlog2 hslope
  set A : ℝ := 4 * Real.log 2 * stencilSlope c with hA
  set E : ℝ := 4 * Real.log 2 * stencilErrorConst c with hEdef
  set K : ℝ := 8 * (peak c : ℝ) * (Real.log 4 + 4) ^ 2 with hK
  have hA0 : 0 ≤ A := by positivity
  have hE0 : 0 ≤ E := by positivity
  have hK0 : 0 ≤ K := by positivity
  set M : ℝ := A + 5 * E + K with hMdef
  have hM0 : 0 ≤ M := by positivity
  set X : ℝ := max 1 (2 * M / L) with hX
  have hX1 : 1 ≤ X := le_max_left _ _
  have hX2 : 2 * M / L ≤ X := le_max_right _ _
  refine ⟨⌈X ^ 4⌉₊ + 4, fun N hN => ?_⟩
  have hN4 : 4 ≤ N := by omega
  have hNR : X ^ 4 ≤ (N : ℝ) := by
    have h1 : (⌈X ^ 4⌉₊ : ℝ) ≤ N := by exact_mod_cast (by omega : ⌈X ^ 4⌉₊ ≤ N)
    exact (Nat.le_ceil _).trans h1
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set x : ℝ := Real.sqrt (Real.sqrt N) with hx
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hxsq : x ^ 2 = Real.sqrt N := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hxN : x ^ 4 = (N : ℝ) := by
    have h1 : x ^ 4 = (x ^ 2) ^ 2 := by ring
    rw [h1, hxsq, Real.sq_sqrt hN0]
  have hXx : X ≤ x := by
    have h1 : X ^ 2 ≤ Real.sqrt N := Real.le_sqrt_of_sq_le (by nlinarith [hNR, sq_nonneg X])
    exact Real.le_sqrt_of_sq_le h1
  have hx1 : 1 ≤ x := hX1.trans hXx
  have hs : (Nat.sqrt N : ℝ) ≤ x ^ 2 := by
    rw [hxsq]
    exact Real.nat_sqrt_le_real_sqrt
  have ht : (Nat.sqrt (Nat.sqrt N) : ℝ) ≤ x := by
    refine Real.nat_sqrt_le_real_sqrt.trans (Real.sqrt_le_sqrt ?_)
    exact Real.nat_sqrt_le_real_sqrt
  have hlogN : Real.log N ≤ 4 * x := by
    rw [← hxN, Real.log_pow]
    push_cast
    have := Real.log_le_self hx0
    linarith
  have hgap := ledger_conv_twin_sub_le hP hN4
  have hx3 : x ≤ x ^ 3 := by nlinarith [sq_nonneg x, mul_nonneg hx0 hx0]
  have hone3 : 1 ≤ x ^ 3 := by nlinarith [pow_pos (lt_of_lt_of_le one_pos hx1) 2]
  have herr1 : E * (1 + Real.log N) ≤ 5 * E * x ^ 3 := by
    have h1 : 1 + Real.log N ≤ 5 * x ^ 3 := by linarith
    calc E * (1 + Real.log N) ≤ E * (5 * x ^ 3) := mul_le_mul_of_nonneg_left h1 hE0
      _ = _ := by ring
  have herr2 : K * (Nat.sqrt (Nat.sqrt N) : ℝ) * (Nat.sqrt N : ℝ) ≤ K * x ^ 3 := by
    have h1 : (Nat.sqrt (Nat.sqrt N) : ℝ) * (Nat.sqrt N : ℝ) ≤ x * x ^ 2 :=
      mul_le_mul ht hs (Nat.cast_nonneg _) hx0
    calc K * (Nat.sqrt (Nat.sqrt N) : ℝ) * (Nat.sqrt N : ℝ)
        = K * ((Nat.sqrt (Nat.sqrt N) : ℝ) * (Nat.sqrt N : ℝ)) := by ring
      _ ≤ K * (x * x ^ 2) := mul_le_mul_of_nonneg_left h1 hK0
      _ = _ := by ring
  have herr3 : A ≤ A * x ^ 3 := le_mul_of_one_le_right hA0 hone3
  have hsmall : M * x ^ 3 ≤ L / 2 * x ^ 4 := by
    have h1 : 2 * M / L ≤ x := hX2.trans hXx
    rw [div_le_iff₀ hLpos] at h1
    have h3 : 0 ≤ x ^ 3 := by positivity
    have h2 : (2 * M) * x ^ 3 ≤ (x * L) * x ^ 3 := mul_le_mul_of_nonneg_right h1 h3
    have h4 : (x * L) * x ^ 3 = L * x ^ 4 := by ring
    linarith
  rw [hxN] at hsmall
  have hmain : L * (N : ℝ) = Real.log 2 * stencilSlope c * N := rfl
  have hfinal : -(Real.log 2 * stencilSlope c * N) + A + E * (1 + Real.log N) +
      K * (Nat.sqrt (Nat.sqrt N) : ℝ) * (Nat.sqrt N : ℝ) ≤ -(L / 2 * N) := by
    have h5 : M * x ^ 3 = A * x ^ 3 + 5 * E * x ^ 3 + K * x ^ 3 := by rw [hMdef]; ring
    nlinarith
  have hval : Real.log 2 / 2 * stencilSlope c * N = L / 2 * N := by rw [hL]; ring
  rw [hval]
  linarith

/-- **The Selberg ledger separates the twin.** The Selberg reading of `Λ` is exact, with value a sum of
`log² m`, and the Selberg reading of the twin leaves it by a fixed multiple of `N`. A linear ledger moves
by at most `2 w ψ(√N)`. -/
theorem exists_selberg_twin_gap (hP : IsProducer c m B) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ledger c (selbergWeight twinWeight) N ≤
      (∑ k ∈ c.support, (c k : ℝ) * ∑ j ∈ Ioc 0 (N / k), Real.log j ^ 2) -
        Real.log 2 / 2 * stencilSlope c * N := by
  obtain ⟨N₀, h⟩ := exists_ledger_conv_twin_gap hP
  refine ⟨N₀, fun N hN => ?_⟩
  rw [← ledger_selbergWeight hP.zero]
  have hgap := h N hN
  have hexp : ∀ n, selbergWeight twinWeight n = selbergWeight vonMangoldtWeight n +
      ((-2) * (evenVonMangoldt n * Real.log n) +
        (conv twinWeight twinWeight n - conv vonMangoldtWeight vonMangoldtWeight n)) := by
    intro n
    simp only [selbergWeight, twinWeight_eq]
    ring
  have hL : ledger c (selbergWeight twinWeight) N = ledger c (fun n =>
      selbergWeight vonMangoldtWeight n + ((-2) * (evenVonMangoldt n * Real.log n) +
        (conv twinWeight twinWeight n - conv vonMangoldtWeight vonMangoldtWeight n))) N := by
    simp only [ledger, hexp]
  rw [hL, ledger_add, ledger_add, ledger_smul, ledger_sub]
  have hnn : 0 ≤ ledger c (fun n => evenVonMangoldt n * Real.log n) N :=
    ledger_nonneg hP (fun n => mul_nonneg (evenVonMangoldt_nonneg n)
      (Real.log_natCast_nonneg n)) N
  linarith

end GaloisForLFunctions.RigidArithmeticOfCuts
