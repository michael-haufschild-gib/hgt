import GaloisForLFunctions.RHTower.FareyDiscrepancyLandauCriterion
import GaloisForLFunctions.RHTower.CenteredFractCorrelation

/-!
# The Farey counting function and the Mertens function

For `0 ≤ x ≤ 1` the number of Farey fractions of order `n` not exceeding `x` is
`N_n(x) = Σ_{k ≤ n} ⌊k x⌋ M(n/k)`, where `M(N) = Σ_{m ≤ N} μ(m)`.  Indeed the fractions with
denominator `q` contribute `#{a ≤ ⌊qx⌋ : (a, q) = 1} = Σ_{d ∣ q} μ(d) ⌊qx/d⌋`, a Dirichlet
convolution of `μ` with `k ↦ ⌊kx⌋`, and summing a convolution over `q ≤ n` regroups it as
`Σ_k ⌊kx⌋ M(n/k)`.  The same regrouping of `ζ * μ = 1` gives `Σ_{k ≤ n} M(n/k) = 1`.

Consequently the Farey defect `L x - N_n(x)` (`L = |F_n|`) equals
`½ + Σ_{k ≤ n} ψ(k x) M(n/k)` on `[0, 1]`, with `ψ(x) = {x} - ½`.
-/

open Finset

open RHTower.Sieve (fareySet mem_fareySet fareySet_eq_biUnion)

namespace RHTower

noncomputable section

/-- The Mertens function `M(N) = Σ_{1 ≤ m ≤ N} μ(m)`. -/
def mertensIoc (N : ℕ) : ℤ := ∑ m ∈ Ioc 0 N, ArithmeticFunction.moebius m

/-- The Farey counting function `#{a/q ∈ F_n : a/q ≤ x}`. -/
def fareyCount (n : ℕ) (x : ℝ) : ℕ := ((fareySet n).filter (fun r => fareyValue r ≤ x)).card

/-- The arithmetic function `k ↦ ⌊k x⌋`. -/
def floorMulArithmetic (x : ℝ) : ArithmeticFunction ℤ :=
  ⟨fun k => (⌊(k : ℝ) * x⌋₊ : ℤ), by simp⟩

theorem floorMulArithmetic_apply (x : ℝ) (k : ℕ) :
    floorMulArithmetic x k = (⌊(k : ℝ) * x⌋₊ : ℤ) := rfl

/-- Sums over the Farey set, fibred by denominators. -/
theorem sum_fareySet_eq_sum_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ × ℕ → M) :
    ∑ p ∈ fareySet n, g p
      = ∑ q ∈ Icc 1 n, ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q), g (a, q) := by
  rw [fareySet_eq_biUnion, sum_biUnion]
  · exact sum_congr rfl fun q _ => sum_image (fun a _ b _ hab => by simpa using hab)
  · intro q _ r _ hqr
    simp only [Function.onFun]
    rw [disjoint_left]
    intro p hp hp'
    simp only [mem_image] at hp hp'
    obtain ⟨a, _, rfl⟩ := hp
    obtain ⟨b, _, hb⟩ := hp'
    exact hqr (congrArg Prod.snd hb).symm

/-- Coprime residues in an initial segment: `#{1 ≤ a ≤ K : (a, q) = 1} = Σ_{d ∣ q} μ(d) ⌊K/d⌋`. -/
theorem card_coprime_Icc_eq_sum_moebius {q : ℕ} (hq : 1 ≤ q) (K : ℕ) :
    (((Icc 1 K).filter (fun a => Nat.Coprime a q)).card : ℤ)
      = ∑ d ∈ q.divisors, ArithmeticFunction.moebius d * ((K / d : ℕ) : ℤ) := by
  have hind : ∀ a, (if Nat.Coprime a q then (1 : ℤ) else 0)
      = ∑ d ∈ q.divisors, if d ∣ a then ArithmeticFunction.moebius d else 0 := by
    intro a
    have h1 := congrArg (fun f : ArithmeticFunction ℤ => f (Nat.gcd a q))
      ArithmeticFunction.moebius_mul_coe_zeta
    simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h1
    have h2 : (Nat.gcd a q).divisors = q.divisors.filter (fun d => d ∣ a) := by
      ext d
      simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨hda, hdq⟩, _⟩
        exact ⟨⟨hdq, by omega⟩, hda⟩
      · rintro ⟨⟨hdq, hq0⟩, hda⟩
        exact ⟨⟨hda, hdq⟩, (Nat.gcd_pos_of_pos_right a (by omega)).ne'⟩
    rw [← sum_filter, ← h2, h1]
  rw [card_filter]
  push_cast
  rw [sum_congr rfl fun a _ => hind a, sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  have hIcc : Icc 1 K = Ioc 0 K := by ext a; simp only [mem_Icc, mem_Ioc]; omega
  rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]

/-- The Farey fractions of denominator `q` below `x` are counted by a Möbius convolution. -/
theorem card_coprime_filter_le_eq {q : ℕ} (hq : 1 ≤ q) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ((((Icc 1 q).filter (fun a => Nat.Coprime a q)).filter
        (fun a => fareyValue (a, q) ≤ x)).card : ℤ)
      = (ArithmeticFunction.moebius * floorMulArithmetic x) q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hset : ((Icc 1 q).filter (fun a => Nat.Coprime a q)).filter
      (fun a => fareyValue (a, q) ≤ x)
        = (Icc 1 ⌊(q : ℝ) * x⌋₊).filter (fun a => Nat.Coprime a q) := by
    ext a
    simp only [mem_filter, mem_Icc, fareyValue]
    have hiff : (a : ℝ) / q ≤ x ↔ a ≤ ⌊(q : ℝ) * x⌋₊ := by
      rw [div_le_iff₀ hq0, Nat.le_floor_iff (by positivity), mul_comm]
    have hfl : ⌊(q : ℝ) * x⌋₊ ≤ q :=
      Nat.floor_le_of_le (by nlinarith)
    rw [hiff]
    constructor
    · rintro ⟨⟨⟨h1, _⟩, h3⟩, h4⟩
      exact ⟨⟨h1, h4⟩, h3⟩
    · rintro ⟨⟨h1, h4⟩, h3⟩
      exact ⟨⟨⟨h1, le_trans h4 hfl⟩, h3⟩, h4⟩
  rw [hset, card_coprime_Icc_eq_sum_moebius hq, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => ArithmeticFunction.moebius a * floorMulArithmetic x b)]
  refine sum_congr rfl fun d hd => ?_
  have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
  have hd0 : (d : ℝ) ≠ 0 := by
    have := Nat.pos_of_mem_divisors hd
    positivity
  rw [floorMulArithmetic_apply, Nat.cast_div hdq hd0]
  congr 2
  rw [show (q : ℝ) / d * x = (q : ℝ) * x / d by ring, Nat.floor_div_natCast]

/-- **The Farey counting identity.**  `N_n(x) = Σ_{k ≤ n} ⌊k x⌋ M(n/k)` for `0 ≤ x ≤ 1`. -/
theorem fareyCount_eq_sum (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (fareyCount n x : ℤ) = ∑ k ∈ Ioc 0 n, (⌊(k : ℝ) * x⌋₊ : ℤ) * mertensIoc (n / k) := by
  unfold fareyCount
  rw [card_filter]
  push_cast
  rw [sum_fareySet_eq_sum_sum n (fun p => if fareyValue p ≤ x then (1 : ℤ) else 0)]
  have h1 : ∀ q ∈ Icc 1 n, ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
      (if fareyValue (a, q) ≤ x then (1 : ℤ) else 0)
        = (ArithmeticFunction.moebius * floorMulArithmetic x) q := by
    intro q hq
    rw [← card_coprime_filter_le_eq (mem_Icc.mp hq).1 hx0 hx1, card_filter]
    push_cast
    rfl
  rw [sum_congr rfl h1, show Icc 1 n = Ioc 0 n by ext a; simp only [mem_Icc, mem_Ioc]; omega,
    mul_comm, ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  rfl

/-- **The Möbius regrouping.**  `Σ_{k ≤ n} M(n/k) = 1` for `n ≥ 1`. -/
theorem sum_mertensIoc_div_eq_one {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Ioc 0 n, mertensIoc (n / k) = 1 := by
  have h := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)
    ArithmeticFunction.moebius n
  rw [ArithmeticFunction.coe_zeta_mul_moebius] at h
  have h1 : ∑ q ∈ Ioc 0 n, (1 : ArithmeticFunction ℤ) q = 1 := by
    rw [sum_eq_single 1]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (mem_Ioc.mpr ⟨by omega, hn⟩) h
  rw [h1] at h
  rw [h]
  refine sum_congr rfl fun k hk => ?_
  have hk0 : k ≠ 0 := by have := (mem_Ioc.mp hk).1; omega
  simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hk0, mertensIoc]

/-- The Farey set has `L = Σ_{k ≤ n} k M(n/k)` elements. -/
theorem card_fareySet_eq_sum (n : ℕ) :
    ((fareySet n).card : ℤ) = ∑ k ∈ Ioc 0 n, (k : ℤ) * mertensIoc (n / k) := by
  have h := fareyCount_eq_sum n zero_le_one le_rfl
  have hall : fareyCount n 1 = (fareySet n).card := by
    unfold fareyCount
    congr 1
    refine filter_true_of_mem fun p hp => ?_
    obtain ⟨⟨ha1, _⟩, ⟨hq1, _⟩, hle, _⟩ := mem_fareySet.mp hp
    unfold fareyValue
    have hq0 : (0 : ℝ) < p.2 := by exact_mod_cast hq1
    rw [div_le_one hq0]
    exact_mod_cast hle
  rw [← hall, h]
  refine sum_congr rfl fun k _ => ?_
  simp


/-- The complex Mertens partial sum is the integer Mertens function. -/
theorem mobiusMertensPartialSum_eq_mertensIoc (N : ℕ) :
    mobiusMertensPartialSum N = ((mertensIoc N : ℤ) : ℂ) := by
  unfold mobiusMertensPartialSum mobiusComplexCoefficient mertensIoc
  rw [range_eq_Ico, show Ico 0 (N + 1) = insert 0 (Ioc 0 N) by
    ext k; simp only [mem_insert, mem_Ico, mem_Ioc]; omega, sum_insert (by simp)]
  push_cast
  simp

/-- **The Farey defect.**  `L x - N_n(x) = ½ + Σ_{k ≤ n} ψ(k x) M(n/k)` for `0 ≤ x ≤ 1`,
`n ≥ 1`. -/
theorem card_mul_sub_fareyCount_eq {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ((fareySet n).card : ℝ) * x - fareyCount n x
      = 1 / 2 + ∑ k ∈ Ioc 0 n, centeredFract ((k : ℝ) * x) * (mertensIoc (n / k) : ℝ) := by
  have hL : ((fareySet n).card : ℝ) = ∑ k ∈ Ioc 0 n, (k : ℝ) * (mertensIoc (n / k) : ℝ) := by
    exact_mod_cast card_fareySet_eq_sum n
  have hN : (fareyCount n x : ℝ)
      = ∑ k ∈ Ioc 0 n, (⌊(k : ℝ) * x⌋₊ : ℝ) * (mertensIoc (n / k) : ℝ) := by
    exact_mod_cast fareyCount_eq_sum n hx0 hx1
  have h1 : ∑ k ∈ Ioc 0 n, (mertensIoc (n / k) : ℝ) = 1 := by
    exact_mod_cast sum_mertensIoc_div_eq_one hn
  have hfr : ∀ k : ℕ, (k : ℝ) * x - (⌊(k : ℝ) * x⌋₊ : ℝ)
      = centeredFract ((k : ℝ) * x) + 1 / 2 := by
    intro k
    have h0 : 0 ≤ (k : ℝ) * x := by positivity
    have e : ((⌊(k : ℝ) * x⌋₊ : ℕ) : ℝ) = ((⌊(k : ℝ) * x⌋ : ℤ) : ℝ) := by
      rw [← Int.natCast_floor_eq_floor h0, Int.cast_natCast]
    rw [e]
    unfold centeredFract Int.fract
    ring
  calc ((fareySet n).card : ℝ) * x - fareyCount n x
      = ∑ k ∈ Ioc 0 n, ((k : ℝ) * x - (⌊(k : ℝ) * x⌋₊ : ℝ)) * (mertensIoc (n / k) : ℝ) := by
        rw [hL, hN, sum_mul, ← sum_sub_distrib]
        exact sum_congr rfl fun k _ => by ring
    _ = ∑ k ∈ Ioc 0 n, (centeredFract ((k : ℝ) * x) * (mertensIoc (n / k) : ℝ)
          + 1 / 2 * (mertensIoc (n / k) : ℝ)) :=
        sum_congr rfl fun k _ => by rw [hfr]; ring
    _ = _ := by rw [sum_add_distrib, ← mul_sum, h1]; ring

end

end RHTower
