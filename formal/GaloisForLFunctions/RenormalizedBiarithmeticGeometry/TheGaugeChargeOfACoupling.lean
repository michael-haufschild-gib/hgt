import GaloisForLFunctions.BiarithmeticGaugeGeometry.PrimeGaugeTorusAndVacuumIntertwiners

/-!
# The gauge charge of a coupling

A kernel built from an arithmetic source `F` couples two modes `a, b` through source values `F(n)`.
Twisting the source by a completely multiplicative sign `σ` (a real sign gauge on the prime torus)
acts on the kernel by the conjugation `K(a, b) ↦ σ(a)σ(b)K(a, b)` exactly when every coupling
`(n; a, b)` in its support satisfies `σ(n) = σ(a)σ(b)` for every `σ`. Such couplings are *blind*:
the kernel cannot tell `ζ` from Liouville's `ζ(2s)/ζ(s)`.

* **Classification** (`realSignBlind_iff_isSquare`). A coupling `(n; a, b)` is blind under every real
  sign gauge iff `n a b` is a perfect square. The proof uses the prime-flip gauges
  (`flipGauge`), with character `(−1)^{v_p}` (`gaugeChar_flipGauge`), and the square criterion
  `IsSquare N ↔ ∀ p, Even (v_p N)` (`isSquare_iff_even_factorization`).
* **Kernel form** (`sourceKernel_twist_iff`). The source twist acts on a kernel by conjugation for
  every real gauge iff every coupling in its support is of square class.
* **Diagonal, ratio and product couplings are blind** (`diagonal_coupling_blind`,
  `ratio_coupling_blind`, `product_coupling_blind`): `a·a`, `n·a·(an)` and `(ab)·a·b` are squares.
  This is the structural reason behind unitary gauge blindness of multiplicative lattice forms.
* **Successor couplings are charged** (`successor_coupling_charged`): `a(a + 1)` lies strictly
  between `a²` and `(a + 1)²`, so for every `a ≥ 1` some real sign gauge flips the link
  `a → a + 1`.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

open BiarithmeticGaugeGeometry

/-! ### The square criterion -/

/-- `N ≠ 0` is a square iff all its prime exponents are even. -/
theorem isSquare_iff_even_factorization {N : ℕ} (hN : N ≠ 0) :
    IsSquare N ↔ ∀ p, Even (N.factorization p) := by
  constructor
  · rintro ⟨k, rfl⟩ p
    have hk : k ≠ 0 := by rintro rfl; exact hN rfl
    rw [Nat.factorization_mul hk hk, Finsupp.add_apply]
    exact ⟨_, rfl⟩
  · intro h
    refine ⟨N.factorization.prod fun p e => p ^ (e / 2), ?_⟩
    rw [← Finsupp.prod_mul]
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hN]
    refine Finsupp.prod_congr fun p _ => ?_
    rw [← pow_add]
    congr 1
    obtain ⟨k, hk⟩ := h p
    omega

/-! ### Prime-flip gauges -/

/-- The prime-flip gauge: `−1` at the prime `p`, `1` elsewhere. -/
def flipGauge (p : ℕ) : PrimeGauge where
  val n := if n = p ∧ n.Prime then -1 else 1
  norm_prime _ := by split_ifs <;> simp
  nonprime_eq_one hn := by simp [hn]

theorem isRealSignGauge_flipGauge (p : ℕ) : IsRealSignGauge (flipGauge p) := by
  intro q _
  simp only [flipGauge]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The character of the flip gauge at `p` is `(−1)^{v_p(N)}`. -/
theorem gaugeChar_flipGauge {p : ℕ} (hp : p.Prime) {N : ℕ} (hN : N ≠ 0) :
    (flipGauge p).gaugeChar N = (-1) ^ (N.factorization p) := by
  rw [PrimeGauge.gaugeChar_of_ne_zero _ hN, Finsupp.prod]
  have hval : ∀ q, (flipGauge p).val q ^ N.factorization q =
      if q = p then (-1 : ℂ) ^ N.factorization q else 1 := by
    intro q
    simp only [flipGauge]
    by_cases hq : q = p
    · subst hq; simp [hp]
    · simp [hq]
  simp_rw [hval]
  rw [prod_ite_eq']
  split_ifs with hmem
  · rfl
  · rw [Finsupp.notMem_support_iff.mp hmem, pow_zero]

/-- Real sign characters square to `1` away from `0`. -/
theorem gaugeChar_sq_eq_one {ω : PrimeGauge} (hω : IsRealSignGauge ω) {n : ℕ} (hn : n ≠ 0) :
    ω.gaugeChar n ^ 2 = 1 := by
  rw [gaugeChar_eq_realSignChar hω, ← Complex.ofReal_pow, realSignChar_sq_eq_one hω hn,
    Complex.ofReal_one]

/-! ### Classification of blind couplings -/

/-- **Blind couplings are the square class.** For `n, a, b ≥ 1`, `σ(n) = σ(a)σ(b)` for every real
sign gauge iff `n a b` is a perfect square. -/
theorem realSignBlind_iff_isSquare {n a b : ℕ} (hn : n ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∀ ω : PrimeGauge, IsRealSignGauge ω → ω.gaugeChar n = ω.gaugeChar a * ω.gaugeChar b) ↔
      IsSquare (n * a * b) := by
  have hN : n * a * b ≠ 0 := mul_ne_zero (mul_ne_zero hn ha) hb
  constructor
  · intro h
    rw [isSquare_iff_even_factorization hN]
    intro p
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have hp : p.Prime := by
      by_contra hnp
      rw [Nat.factorization_eq_zero_of_not_prime _ hnp] at hodd
      exact (Nat.not_odd_zero) hodd
    have hσ := h (flipGauge p) (isRealSignGauge_flipGauge p)
    have hprod : (flipGauge p).gaugeChar (n * a * b) = 1 := by
      rw [PrimeGauge.gaugeChar_mul, PrimeGauge.gaugeChar_mul, hσ]
      have h2 := gaugeChar_sq_eq_one (isRealSignGauge_flipGauge p) ha
      have h3 := gaugeChar_sq_eq_one (isRealSignGauge_flipGauge p) hb
      linear_combination (flipGauge p).gaugeChar b ^ 2 * h2 + h3
    rw [gaugeChar_flipGauge hp hN, hodd.neg_one_pow] at hprod
    norm_num at hprod
  · rintro ⟨k, hk⟩ ω hω
    have hk0 : k ≠ 0 := by rintro rfl; rw [hk] at hN; exact hN rfl
    have hsq : ω.gaugeChar n * ω.gaugeChar a * ω.gaugeChar b = 1 := by
      rw [← PrimeGauge.gaugeChar_mul, ← PrimeGauge.gaugeChar_mul, hk, PrimeGauge.gaugeChar_mul,
        ← sq, gaugeChar_sq_eq_one hω hk0]
    have h2 := gaugeChar_sq_eq_one hω ha
    have h3 := gaugeChar_sq_eq_one hω hb
    linear_combination (ω.gaugeChar a * ω.gaugeChar b) * hsq -
      ω.gaugeChar n * ω.gaugeChar b ^ 2 * h2 - ω.gaugeChar n * h3

/-! ### Kernels built from a source -/

/-- The `(a, b)` entry of a kernel built from the source `F` with coupling coefficients `c n` over
the source indices `S`. -/
def sourceKernel (S : Finset ℕ) (c F : ℕ → ℂ) : ℂ := ∑ n ∈ S, F n * c n

/-- **Kernel form of the classification.** Twisting the source by every real sign gauge acts on the
`(a, b)` entry by `σ(a)σ(b)`, for every source, iff every coupling in its support is of square
class. -/
theorem sourceKernel_twist_iff {S : Finset ℕ} (hS : ∀ n ∈ S, n ≠ 0) {a b : ℕ} (ha : a ≠ 0)
    (hb : b ≠ 0) (c : ℕ → ℂ) :
    (∀ ω : PrimeGauge, IsRealSignGauge ω → ∀ F : ℕ → ℂ,
      sourceKernel S c (gaugeTwist ω F) = ω.gaugeChar a * ω.gaugeChar b * sourceKernel S c F) ↔
      ∀ n ∈ S, c n ≠ 0 → IsSquare (n * a * b) := by
  classical
  constructor
  · intro h n hn hc
    rw [← realSignBlind_iff_isSquare (hS n hn) ha hb]
    intro ω hω
    have h1 := h ω hω (fun k => if k = n then 1 else 0)
    simp only [sourceKernel, gaugeTwist, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      sum_ite_eq', hn, if_true, one_mul] at h1
    exact mul_right_cancel₀ hc (h1.trans (by ring))
  · intro h ω hω F
    simp only [sourceKernel, mul_sum]
    refine sum_congr rfl fun n hn => ?_
    by_cases hc : c n = 0
    · simp [hc]
    · rw [gaugeTwist, (realSignBlind_iff_isSquare (hS n hn) ha hb).mpr (h n hn hc) ω hω]
      ring

/-! ### Which couplings are blind -/

/-- Diagonal couplings `(1; a, a)` are blind. -/
theorem diagonal_coupling_blind {a : ℕ} (ha : a ≠ 0) (ω : PrimeGauge) (hω : IsRealSignGauge ω) :
    ω.gaugeChar 1 = ω.gaugeChar a * ω.gaugeChar a :=
  (realSignBlind_iff_isSquare one_ne_zero ha ha).mpr ⟨a, by ring⟩ ω hω

/-- Ratio couplings `(n; a, an)` are blind. -/
theorem ratio_coupling_blind {n a : ℕ} (hn : n ≠ 0) (ha : a ≠ 0) (ω : PrimeGauge)
    (hω : IsRealSignGauge ω) : ω.gaugeChar n = ω.gaugeChar a * ω.gaugeChar (a * n) :=
  (realSignBlind_iff_isSquare hn ha (mul_ne_zero ha hn)).mpr ⟨a * n, by ring⟩ ω hω

/-- Product couplings `(ab; a, b)` are blind. -/
theorem product_coupling_blind {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (ω : PrimeGauge)
    (hω : IsRealSignGauge ω) : ω.gaugeChar (a * b) = ω.gaugeChar a * ω.gaugeChar b :=
  (realSignBlind_iff_isSquare (mul_ne_zero ha hb) ha hb).mpr ⟨a * b, by ring⟩ ω hω

/-- `a(a + 1)` is never a square for `a ≥ 1`. -/
theorem not_isSquare_mul_succ {a : ℕ} (ha : 0 < a) : ¬ IsSquare (a * (a + 1)) := by
  rintro ⟨k, hk⟩
  have h1 : a < k := by nlinarith
  have h2 : k < a + 1 := by nlinarith
  omega

/-- **Successor couplings are charged.** For every `a ≥ 1` some real sign gauge flips the
successor link `a → a + 1`. -/
theorem successor_coupling_charged {a : ℕ} (ha : 0 < a) :
    ∃ ω : PrimeGauge, IsRealSignGauge ω ∧ ω.gaugeChar a * ω.gaugeChar (a + 1) ≠ 1 := by
  by_contra h
  push Not at h
  have hsq := (realSignBlind_iff_isSquare one_ne_zero ha.ne' (Nat.succ_ne_zero a)).mp
    fun ω hω => by rw [PrimeGauge.gaugeChar_one, h ω hω]
  rw [one_mul] at hsq
  exact not_isSquare_mul_succ ha hsq

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
