import GaloisForLFunctions.BezoutValuationIncidence.ReciprocityFormOfTheBernoulliKernel
import GaloisForLFunctions.BezoutValuationIncidence.TwoSidedSignLawOfTheSecondOrderKernel
import GaloisForLFunctions.BezoutValuationIncidence.SmoothLargeScaleRowsAndTheCancellationOfBothKernels
import GaloisForLFunctions.RHTower.EstermannKloostermanSaving

/-!
# Multiplicative Convolution of the Reciprocity Kernel, Ramanujan–Kloosterman Splitting, and Square-Root Weil Saving

In `ReciprocityFormOfTheBernoulliKernel`, the quadratic cross-scale Bernoulli kernel `𝔅(d, n)` was
expressed for `gcd(n, d) = 1` (`n n̄ ≡ 1 (mod d)`) as the nonlinear cosecant–Bernoulli sum

`𝔅(d, n) = (π² / 4) ∑_{k=1}^{d-1} B₂(k / d) / sin²(π k n̄ / d)`.

Because `n̄` enters nonlinearly inside `csc²(π k n̄ / d)`, that representation does not directly
separate the non-oscillatory coprime mean from linear additive reciprocal phases `e(m n̄ / p)`.

This module resolves that barrier by inverting `‖η − 1‖⁻² = 1 / (4 sin²(π u / d))` against the
residue potential `Φ_d` on `ℤ/dℤ` and reindexing multiplicatively on `(ℤ/pℤ)ˣ`:

1. **Finite cyclotomic inversion of `‖η − 1‖⁻²` and `csc²` at every modulus (`§1`).**
   For every `d ≥ 1` and `η₀ ∈ nontrivialRoots d`,
   `‖η₀ − 1‖⁻² = (1 / d) ∑_{M=0}^{d-1} Φ_d(M) η₀⁻ᴹ`,
   so for every `u` with `d ∤ u`,
   `1 / (4 sin²(π u / d)) = (1 / d) ∑_{M=0}^{d-1} Φ_d(M) cos(2π M u / d)`.

2. **Exact polynomial moments of the centred `B₂` sample (`§2`).**
   The shifted sample `β_d(k) := B₂(k / d) + 1 / (6 d)` has exact zero sum
   `∑_{k=1}^{d-1} β_d(k) = 0`, reflection symmetry `β_d(d − k) = β_d(k)`, and fourth-degree
   exact second moment
   `∑_{k=1}^{d-1} β_d(k)² = (d² − 1)(d − 2)(d − 3) / (180 d³)`,
   which vanishes identically at `d = 2` and `d = 3`.

3. **Multiplicative self-convolution on `(ℤ/pℤ)ˣ` and exact all-`n` Ramanujan–Kloosterman
   decomposition (`§3`).**
   For a prime `p` and `1 ≤ m < p`, define the multiplicative convolution coefficient
   `reciprocityKloostermanCoeff p m := (π² p / 2) ∑_{k=1}^{p-1} β_p(k) β_p(m k̄_p mod p)`.
   It satisfies `C_{p−m}(p) = C_m(p)`, `∑_{m=1}^{p-1} C_m(p) = 0`, and `C_m(2) = C_m(3) = 0`.
   For every prime `p` and **every** `n : ℕ` (both `p ∣ n` and `p ∤ n`),
   `𝔅(p, n) − primeKernelMean p =
     (p + 1) · primeKernelMean p · (p · 1_{p ∣ n} − 1) +
       1_{p ∤ n} ∑_{m=1}^{p-1} C_m(p) cos(2π m n̄_p / p)`,
   decomposing `𝔅(p, ·) − m_p` orthogonally into Ramanujan's sum `c_p(n) = p 1_{p ∣ n} − 1` plus a
   pure zero-mean linear Kloosterman wave on `(ℤ/pℤ)ˣ`.

4. **Dedekind–Kloosterman dual formula and `O(p^{3/2})` Weil saving with zero log loss (`§4`).**
   Expanding both `Φ_p` factors spectrally expresses `C_m(p)` for `1 ≤ m < p` as an exact
   `csc² × csc²` bilinear average of classical Kloosterman sums `S(a, b m; p)`:
   `C_m(p) = (2 π² / p³) ∑_{a=1}^{p-1} ∑_{b=1}^{p-1} Re S(a, b m; p) / (16 sin²(π a/p) sin²(π b/p))
             − π² (p − 1)(p + 1)² / (72 p³)`.
   Because `1 / (4 sin²(π a / p))` is positive and `ℓ¹`-summable with exact sum `(p² − 1) / 12`,
   applying Weil's bound `‖S(a, b m; p)‖ ≤ 2 √p` (`RHTower.norm_kloostermanSum_le_weil`) saves a
   full `√p` factor pointwise with **zero logarithmic loss**:
   `|C_m(p)| ≤ π² (p² − 1)² / (36 p² √p) + π² (p − 1)(p + 1)² / (72 p³) ≤ (π² / 24) p √p`,
   and consequently `∑_{m=1}^{p-1} C_m(p)² ≤ (π⁴ / 576) (p − 1) p³`.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Finite cyclotomic inversion of `‖η − 1‖⁻²` and `1 / (4 sin²(π u / d))` -/

/-- Orthogonality of `d`-th roots of unity on `range d`: for `η, η₀ ∈ nontrivialRoots d`,
`∑_{M < d} (η * η₀⁻¹)^M = d` if `η = η₀` and `0` otherwise. -/
theorem sum_range_mul_inv_pow_of_mem_nontrivialRoots {d : ℕ} (hd : 0 < d)
    {η η₀ : ℂ} (hη : η ∈ nontrivialRoots d) (hη₀ : η₀ ∈ nontrivialRoots d) :
    ∑ M ∈ range d, (η * η₀⁻¹) ^ M = if η = η₀ then (d : ℂ) else 0 := by
  have hdη := ((mem_nontrivialRoots hd).mp hη).2
  have hdη₀ := ((mem_nontrivialRoots hd).mp hη₀).2
  have hη₀_ne : η₀ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hd.ne'] at hdη₀
    exact zero_ne_one hdη₀
  by_cases heq : η = η₀
  · subst heq
    rw [if_pos rfl, mul_inv_cancel₀ hη₀_ne]
    simp
  · rw [if_neg heq]
    have hne1 : η * η₀⁻¹ ≠ 1 := by
      intro h1
      have := congrArg (· * η₀) h1
      rw [mul_assoc, inv_mul_cancel₀ hη₀_ne, mul_one, one_mul] at this
      exact heq this
    have hpow : (η * η₀⁻¹) ^ d = 1 := by
      rw [mul_pow, inv_pow, hdη, hdη₀, inv_one, mul_one]
    rw [geom_sum_eq hne1, hpow, sub_self, zero_div]

/-- **Finite cyclotomic inversion of `‖η₀ − 1‖⁻²`.**
For every `d ≥ 1` and `η₀ ∈ nontrivialRoots d`,
`‖η₀ − 1‖⁻² = (1 / d) ∑_{M < d} Φ_d(M) η₀⁻ᴹ`. -/
theorem inv_norm_sub_one_sq_eq_sum_residuePotential {d : ℕ} (hd : 0 < d)
    {η₀ : ℂ} (hη₀ : η₀ ∈ nontrivialRoots d) :
    (((‖η₀ - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) =
      (1 / (d : ℂ)) * ∑ M ∈ range d, (residuePotential d M : ℂ) * η₀⁻¹ ^ M := by
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hsum : ∑ M ∈ range d, (residuePotential d M : ℂ) * η₀⁻¹ ^ M =
      (d : ℂ) * (((‖η₀ - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
    simp_rw [residuePotential_eq_spectral hd, sum_mul]
    rw [sum_comm]
    have hterm : ∀ η ∈ nontrivialRoots d,
        ∑ M ∈ range d, (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * η ^ M * η₀⁻¹ ^ M =
          if η = η₀ then (d : ℂ) * (((‖η₀ - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) else 0 := by
      intro η hη
      have hrew : ∀ M ∈ range d,
          (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * η ^ M * η₀⁻¹ ^ M =
            (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * (η * η₀⁻¹) ^ M := fun M _ => by
        rw [mul_pow, mul_assoc]
      rw [sum_congr rfl hrew, ← mul_sum, sum_range_mul_inv_pow_of_mem_nontrivialRoots hd hη hη₀]
      split_ifs with heq
      · subst heq; ring
      · ring
    rw [sum_congr rfl hterm, sum_ite_eq' (nontrivialRoots d) η₀, if_pos hη₀]
  rw [hsum]
  field_simp

/-- Any power `stdRoot d ^ u` with `d ∤ u` lies in `nontrivialRoots d`. -/
theorem stdRoot_pow_mem_nontrivialRoots {d u : ℕ} (hd : 0 < d) (hu : ¬ d ∣ u) :
    stdRoot d ^ u ∈ nontrivialRoots d := by
  have hω : IsPrimitiveRoot (stdRoot d) d := Complex.isPrimitiveRoot_exp d hd.ne'
  refine (mem_nontrivialRoots hd).mpr ⟨fun h1 => hu ((hω.pow_eq_one_iff_dvd u).mp h1), ?_⟩
  rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]

/-- **Finite Fourier inversion of `1 / (4 sin²(π u / d))`.**
For every `d ≥ 1` and `u : ℕ` with `d ∤ u`,
`1 / (4 sin²(π u / d)) = (1 / d) ∑_{M < d} Φ_d(M) cos(2π M u / d)`. -/
theorem one_div_four_sin_sq_eq_sum_residuePotential_cos {d u : ℕ} (hd : 0 < d) (hu : ¬ d ∣ u) :
    1 / (4 * Real.sin (Real.pi * (u : ℝ) / d) ^ 2) =
      (1 / (d : ℝ)) *
        ∑ M ∈ range d, residuePotential d M * Real.cos (2 * Real.pi * ((M * u : ℕ) : ℝ) / d) := by
  have hmem : stdRoot d ^ u ∈ nontrivialRoots d := stdRoot_pow_mem_nontrivialRoots hd hu
  have hinv := congrArg Complex.re (inv_norm_sub_one_sq_eq_sum_residuePotential hd hmem)
  rw [Complex.ofReal_re, norm_stdRoot_pow_sub_one_sq, ← one_div] at hinv
  rw [hinv]
  have hd1 : (1 / (d : ℂ)) = ((1 / (d : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hd1, Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine sum_congr rfl fun M _ => ?_
  have hnorm : ‖stdRoot d ^ u‖ = 1 := norm_eq_one_of_mem_nontrivialRoots hd hmem
  have hconj : (stdRoot d ^ u)⁻¹ ^ M = conj (stdRoot d ^ (M * u)) := by
    rw [Complex.inv_eq_conj hnorm, ← map_pow, ← pow_mul, mul_comm u M]
  rw [hconj, Complex.re_ofReal_mul, Complex.conj_re, re_stdRoot_pow]

/-! ## §2. Exact polynomial moments of the centred `B₂` sample -/

/-- The mean-zero centred second Bernoulli sample `β_d(k) = B₂(k / d) + 1 / (6 d)` on `{1, …, d − 1}`. -/
def centredBernoulliTwoSample (d k : ℕ) : ℝ :=
  bernoulliTwo ((k : ℝ) / d) + 1 / (6 * (d : ℝ))

theorem sum_range_cast_pow_four_eq (n : ℕ) :
    ∑ i ∈ range n, (i : ℝ) ^ 4 =
      ((n : ℝ) - 1) * n * (2 * n - 1) * (3 * (n : ℝ) ^ 2 - 3 * n - 1) / 30 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- Exact first moment `∑_{k=1}^{d-1} B₂(k / d) = −(d − 1) / (6 d)` for `d ≥ 1`. -/
theorem sum_Ico_bernoulliTwo_div {d : ℕ} (hd : 0 < d) :
    ∑ k ∈ Ico 1 d, bernoulliTwo ((k : ℝ) / d) = -((d : ℝ) - 1) / (6 * (d : ℝ)) := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hsplit : (∑ k ∈ range d, bernoulliTwo ((k : ℝ) / d)) =
      bernoulliTwo 0 + ∑ k ∈ Ico 1 d, bernoulliTwo ((k : ℝ) / d) := by
    rw [← sum_range_add_sum_Ico _ (by omega : 1 ≤ d), sum_range_one]
    simp
  have hall : ∑ k ∈ range d, bernoulliTwo ((k : ℝ) / d) = 1 / (6 * (d : ℝ)) := by
    simp only [bernoulliTwo]
    have hrew : ∀ k : ℕ, ((k : ℝ) / d) ^ 2 - (k : ℝ) / d + 1 / 6 =
        (1 / (d : ℝ) ^ 2) * (k : ℝ) ^ 2 - (1 / (d : ℝ)) * (k : ℝ) + 1 / 6 := fun k => by ring
    simp_rw [hrew]
    rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, sum_const, card_range,
      nsmul_eq_mul, sum_range_cast_sq_eq, sum_range_cast_eq]
    field_simp
    ring
  have h0 : bernoulliTwo 0 = 1 / 6 := by unfold bernoulliTwo; ring
  rw [hall, h0] at hsplit
  have hsub : ∑ k ∈ Ico 1 d, bernoulliTwo ((k : ℝ) / d) = 1 / (6 * (d : ℝ)) - 1 / 6 := by
    linarith
  rw [hsub]
  field_simp
  ring

/-- **Zero mean of `centredBernoulliTwoSample` on `{1, …, d − 1}`.** -/
theorem sum_Ico_centredBernoulliTwoSample_eq_zero {d : ℕ} (hd : 0 < d) :
    ∑ k ∈ Ico 1 d, centredBernoulliTwoSample d k = 0 := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  unfold centredBernoulliTwoSample
  rw [sum_add_distrib, sum_Ico_bernoulliTwo_div hd, sum_const, Nat.card_Ico,
    nsmul_eq_mul, Nat.cast_sub hd, Nat.cast_one]
  field_simp
  ring

/-- **Reflection symmetry `β_d(d − k) = β_d(k)` for `k ≤ d`.** -/
theorem centredBernoulliTwoSample_reflect {d k : ℕ} (hd : 0 < d) (hk : k ≤ d) :
    centredBernoulliTwoSample d (d - k) = centredBernoulliTwoSample d k := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  unfold centredBernoulliTwoSample bernoulliTwo
  rw [Nat.cast_sub hk]
  field_simp
  ring

/-- Relation between `residuePotential d k` and `centredBernoulliTwoSample d k` for `k < d`:
`Φ_d(k) = (d² / 2) β_d(k) − (d + 1) / 12`. -/
theorem residuePotential_eq_centredBernoulliTwoSample {d k : ℕ} (hd : 0 < d) (hk : k < d) :
    residuePotential d k =
      (d : ℝ) ^ 2 / 2 * centredBernoulliTwoSample d k - ((d : ℝ) + 1) / 12 := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [residuePotential_eq_bernoulli hd, Nat.mod_eq_of_lt hk]
  unfold centredBernoulliTwoSample bernoulliTwo
  field_simp
  ring

/-- **Exact fourth-degree second moment of `centredBernoulliTwoSample`.**
For every `d ≥ 1`,
`∑_{k=1}^{d-1} β_d(k)² = (d² − 1)(d − 2)(d − 3) / (180 d³)`.
In particular, `β_2` and `β_3` vanish identically on `{1, …, d − 1}`. -/
theorem sum_Ico_centredBernoulliTwoSample_sq {d : ℕ} (hd : 0 < d) :
    ∑ k ∈ Ico 1 d, centredBernoulliTwoSample d k ^ 2 =
      ((d : ℝ) ^ 2 - 1) * ((d : ℝ) - 2) * ((d : ℝ) - 3) / (180 * (d : ℝ) ^ 3) := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hsplit : (∑ k ∈ range d, centredBernoulliTwoSample d k ^ 2) =
      centredBernoulliTwoSample d 0 ^ 2 + ∑ k ∈ Ico 1 d, centredBernoulliTwoSample d k ^ 2 := by
    rw [← sum_range_add_sum_Ico _ (by omega : 1 ≤ d), sum_range_one]
  set c : ℝ := 1 / 6 + 1 / (6 * (d : ℝ))
  have hall : ∑ k ∈ range d, centredBernoulliTwoSample d k ^ 2 =
      (1 / (d : ℝ) ^ 4) * (∑ k ∈ range d, (k : ℝ) ^ 4) -
        (2 / (d : ℝ) ^ 3) * (∑ k ∈ range d, (k : ℝ) ^ 3) +
        ((1 + 2 * c) / (d : ℝ) ^ 2) * (∑ k ∈ range d, (k : ℝ) ^ 2) -
        (2 * c / (d : ℝ)) * (∑ k ∈ range d, (k : ℝ)) +
        (d : ℝ) * c ^ 2 := by
    have hrew : ∀ k : ℕ, centredBernoulliTwoSample d k ^ 2 =
        (1 / (d : ℝ) ^ 4) * (k : ℝ) ^ 4 - (2 / (d : ℝ) ^ 3) * (k : ℝ) ^ 3 +
          ((1 + 2 * c) / (d : ℝ) ^ 2) * (k : ℝ) ^ 2 -
          (2 * c / (d : ℝ)) * (k : ℝ) + c ^ 2 := fun k => by
      unfold centredBernoulliTwoSample bernoulliTwo
      dsimp [c]
      ring
    simp_rw [hrew]
    rw [sum_add_distrib, sum_sub_distrib, sum_add_distrib, sum_sub_distrib,
      ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  have h0 : centredBernoulliTwoSample d 0 ^ 2 = c ^ 2 := by
    unfold centredBernoulliTwoSample bernoulliTwo
    dsimp [c]
    simp
  rw [hall, h0, sum_range_cast_pow_four_eq, sum_range_cast_cube_eq, sum_range_cast_sq_eq,
    sum_range_cast_eq] at hsplit
  have hsub : ∑ k ∈ Ico 1 d, centredBernoulliTwoSample d k ^ 2 =
      (1 / (d : ℝ) ^ 4) * (((d : ℝ) - 1) * d * (2 * d - 1) * (3 * (d : ℝ) ^ 2 - 3 * d - 1) / 30) -
        (2 / (d : ℝ) ^ 3) * ((d : ℝ) * ((d : ℝ) - 1) / 2) ^ 2 +
        ((1 + 2 * c) / (d : ℝ) ^ 2) * (((d : ℝ) - 1) * d * (2 * d - 1) / 6) -
        (2 * c / (d : ℝ)) * ((d : ℝ) * ((d : ℝ) - 1) / 2) +
        (d : ℝ) * c ^ 2 - c ^ 2 := by
    linarith
  rw [hsub]
  dsimp [c]
  field_simp
  ring

theorem centredBernoulliTwoSample_two_one : centredBernoulliTwoSample 2 1 = 0 := by
  unfold centredBernoulliTwoSample bernoulliTwo; norm_num

theorem centredBernoulliTwoSample_three {k : ℕ} (hk : k ∈ Ico 1 3) :
    centredBernoulliTwoSample 3 k = 0 := by
  obtain ⟨hk1, hk3⟩ := mem_Ico.mp hk
  interval_cases k <;> (unfold centredBernoulliTwoSample bernoulliTwo; norm_num)

/-! ## §3. Multiplicative self-convolution on `(ℤ/pℤ)ˣ` and the Ramanujan–Kloosterman splitting -/

/-- Canonical Fermat modular inverse `n^{p − 2} mod p` at a prime `p`. -/
def fermatModInv (p n : ℕ) : ℕ := n ^ (p - 2) % p

theorem mul_fermatModInv_mod_eq_one {p n : ℕ} (hp : p.Prime) (hnd : ¬ p ∣ n) :
    n * fermatModInv p n % p = 1 := by
  have hcop : Nat.Coprime n p := Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr hnd)
  have hphi : Nat.totient p = p - 1 := Nat.totient_prime hp
  have h1 : 1 ≤ p - 1 := Nat.le_sub_one_of_lt hp.one_lt
  have hpow : n * n ^ (p - 2) = n ^ Nat.totient p := by
    rw [hphi, show p - 2 = (p - 1) - 1 by omega, ← pow_succ', Nat.sub_add_cancel h1]
  have hmod := Nat.ModEq.pow_totient hcop
  rw [fermatModInv, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, hpow, hmod,
    Nat.mod_eq_of_lt hp.one_lt]

theorem fermatModInv_mem_Ico {p n : ℕ} (hp : p.Prime) (hnd : ¬ p ∣ n) :
    fermatModInv p n ∈ Ico 1 p := by
  refine mem_Ico.mpr ⟨?_, Nat.mod_lt _ hp.pos⟩
  by_contra h0
  have hz : fermatModInv p n = 0 := by omega
  have h1 := mul_fermatModInv_mod_eq_one hp hnd
  rw [hz, mul_zero, Nat.zero_mod] at h1
  exact zero_ne_one h1

theorem mul_mod_mem_Ico_of_prime {p a b : ℕ} (hp : p.Prime) (ha : a ∈ Ico 1 p) (hb : b ∈ Ico 1 p) :
    a * b % p ∈ Ico 1 p := by
  have ha' := mem_Ico.mp ha
  have hb' := mem_Ico.mp hb
  refine mem_Ico.mpr ⟨?_, Nat.mod_lt _ hp.pos⟩
  by_contra h0
  have hdvd : p ∣ a * b := Nat.dvd_of_mod_eq_zero (by omega)
  rcases hp.dvd_mul.mp hdvd with hpa | hpb
  · have := Nat.le_of_dvd (by omega) hpa; omega
  · have := Nat.le_of_dvd (by omega) hpb; omega

theorem not_dvd_of_mem_Ico {p k : ℕ} (hk : k ∈ Ico 1 p) : ¬ p ∣ k :=
  fun h => not_lt_of_ge (Nat.le_of_dvd (mem_Ico.mp hk).1 h) (mem_Ico.mp hk).2

theorem cast_fermatModInv_eq_inv {p n : ℕ} (hp : p.Prime) [Fact p.Prime] (hnd : ¬ p ∣ n) :
    (fermatModInv p n : ZMod p) = (n : ZMod p)⁻¹ := by
  have hnZ : (n : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hnd
  have hZ := congrArg (Nat.cast : ℕ → ZMod p) (mul_fermatModInv_mod_eq_one hp hnd)
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_one] at hZ
  calc (fermatModInv p n : ZMod p)
      = ((n : ZMod p) * (fermatModInv p n : ZMod p)) * (n : ZMod p)⁻¹ := by
          rw [mul_comm (n : ZMod p), mul_assoc, mul_inv_cancel₀ hnZ, mul_one]
    _ = 1 * (n : ZMod p)⁻¹ := by rw [hZ]
    _ = (n : ZMod p)⁻¹ := one_mul _

theorem eq_of_zmod_natCast_eq {p a b : ℕ} [NeZero p] (ha : a < p) (hb : b < p)
    (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  have hval := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at hval

theorem mul_fermatModInv_involutive {p m k : ℕ} (hp : p.Prime) (hm : m ∈ Ico 1 p)
    (hk : k ∈ Ico 1 p) :
    m * fermatModInv p (m * fermatModInv p k % p) % p = k := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hnd_k : ¬ p ∣ k := not_dvd_of_mem_Ico hk
  have hnd_m : ¬ p ∣ m := not_dvd_of_mem_Ico hm
  have hmZ : (m : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hnd_m
  set r := m * fermatModInv p k % p
  have hr_mem : r ∈ Ico 1 p := mul_mod_mem_Ico_of_prime hp hm (fermatModInv_mem_Ico hp hnd_k)
  have hnd_r : ¬ p ∣ r := not_dvd_of_mem_Ico hr_mem
  have hrZ : (r : ZMod p) = (m : ZMod p) * (k : ZMod p)⁻¹ := by
    dsimp [r]
    rw [ZMod.natCast_mod, Nat.cast_mul, cast_fermatModInv_eq_inv hp hnd_k]
  have hZ_eq : ((m * fermatModInv p r % p : ℕ) : ZMod p) = (k : ZMod p) := by
    rw [ZMod.natCast_mod, Nat.cast_mul, cast_fermatModInv_eq_inv hp hnd_r, hrZ, mul_inv_rev, inv_inv]
    calc (m : ZMod p) * ((k : ZMod p) * (m : ZMod p)⁻¹)
        = (k : ZMod p) * ((m : ZMod p) * (m : ZMod p)⁻¹) := by ring
      _ = (k : ZMod p) := by rw [mul_inv_cancel₀ hmZ, mul_one]
  exact eq_of_zmod_natCast_eq (Nat.mod_lt _ hp.pos) (mem_Ico.mp hk).2 hZ_eq

/-- **The multiplicative self-convolution Kloosterman coefficient `C_m(p)`.**
For a prime `p` and frequency `1 ≤ m < p`,
`C_m(p) = (π² p / 2) ∑_{k=1}^{p-1} β_p(k) β_p(m k̄_p mod p)`. -/
def reciprocityKloostermanCoeff (p m : ℕ) : ℝ :=
  (Real.pi ^ 2 * (p : ℝ) / 2) *
    ∑ k ∈ Ico 1 p, centredBernoulliTwoSample p k *
      centredBernoulliTwoSample p (m * fermatModInv p k % p)

/-- Exact vanishing at `p = 2`: `C_m(2) = 0` for all `m`. -/
theorem reciprocityKloostermanCoeff_two (m : ℕ) : reciprocityKloostermanCoeff 2 m = 0 := by
  unfold reciprocityKloostermanCoeff
  have h1 : Ico 1 2 = {1} := rfl
  rw [h1, sum_singleton, centredBernoulliTwoSample_two_one, zero_mul, mul_zero]

/-- Exact vanishing at `p = 3`: `C_m(3) = 0` for all `m`. -/
theorem reciprocityKloostermanCoeff_three (m : ℕ) : reciprocityKloostermanCoeff 3 m = 0 := by
  unfold reciprocityKloostermanCoeff
  rw [sum_eq_zero fun k hk => by rw [centredBernoulliTwoSample_three hk, zero_mul], mul_zero]

/-- **Even reflection symmetry `C_{p − m}(p) = C_m(p)` for `1 ≤ m < p`.** -/
theorem reciprocityKloostermanCoeff_reflect {p m : ℕ} (hp : p.Prime) (hm : m ∈ Ico 1 p) :
    reciprocityKloostermanCoeff p (p - m) = reciprocityKloostermanCoeff p m := by
  have hm' := mem_Ico.mp hm
  unfold reciprocityKloostermanCoeff
  congr 1
  refine sum_nbij' (fun k => p - k) (fun k => p - k) ?_ ?_ ?_ ?_ ?_
  · intro k hk; have := mem_Ico.mp hk; exact mem_Ico.mpr ⟨by omega, by omega⟩
  · intro k hk; have := mem_Ico.mp hk; exact mem_Ico.mpr ⟨by omega, by omega⟩
  · intro k hk; have := mem_Ico.mp hk; omega
  · intro k hk; have := mem_Ico.mp hk; omega
  · intro k hk
    have hk' := mem_Ico.mp hk
    have hpk_mem : p - k ∈ Ico 1 p := mem_Ico.mpr ⟨by omega, by omega⟩
    have hnd_k : ¬ p ∣ k := not_dvd_of_mem_Ico hk
    have hnd_pk : ¬ p ∣ (p - k) := not_dvd_of_mem_Ico hpk_mem
    rw [centredBernoulliTwoSample_reflect hp.pos (by omega)]
    congr 2
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : Fact p.Prime := ⟨hp⟩
    have hkZ : (k : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hnd_k
    have hpkZ : (((p - k : ℕ) : ZMod p)) = -(k : ZMod p) := by
      rw [Nat.cast_sub hk'.2.le, ZMod.natCast_self, zero_sub]
    have hinv_k : (fermatModInv p k : ZMod p) = (k : ZMod p)⁻¹ :=
      cast_fermatModInv_eq_inv hp hnd_k
    have hinv_pk : (fermatModInv p (p - k) : ZMod p) = -((k : ZMod p)⁻¹) := by
      calc (fermatModInv p (p - k) : ZMod p)
          = (-(k : ZMod p))⁻¹ := by rw [cast_fermatModInv_eq_inv hp hnd_pk, hpkZ]
        _ = (-(k : ZMod p))⁻¹ * (-(k : ZMod p) * -((k : ZMod p)⁻¹)) := by
            rw [neg_mul_neg, mul_inv_cancel₀ hkZ, mul_one]
        _ = -((k : ZMod p)⁻¹) := by
            rw [← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr hkZ), one_mul]
    have hZ_eq : (((p - m) * fermatModInv p k % p : ℕ) : ZMod p) =
        ((m * fermatModInv p (p - k) % p : ℕ) : ZMod p) := by
      rw [ZMod.natCast_mod, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_mul,
        Nat.cast_sub hm'.2.le, ZMod.natCast_self, zero_sub, hinv_k, hinv_pk]
      ring
    exact eq_of_zmod_natCast_eq (Nat.mod_lt _ hp.pos) (Nat.mod_lt _ hp.pos) hZ_eq

/-- **Exact zero sum `∑_{m=1}^{p-1} C_m(p) = 0`.** -/
theorem sum_Ico_reciprocityKloostermanCoeff_eq_zero {p : ℕ} (hp : p.Prime) :
    ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m = 0 := by
  unfold reciprocityKloostermanCoeff
  rw [← mul_sum, sum_comm]
  have hinner : ∀ k ∈ Ico 1 p,
      ∑ m ∈ Ico 1 p, centredBernoulliTwoSample p k *
        centredBernoulliTwoSample p (m * fermatModInv p k % p) = 0 := by
    intro k hk
    have hnd_k : ¬ p ∣ k := not_dvd_of_mem_Ico hk
    have hinv_mem : fermatModInv p k ∈ Ico 1 p := fermatModInv_mem_Ico hp hnd_k
    have hkbar := mul_fermatModInv_mod_eq_one hp hnd_k
    rw [← mul_sum]
    have hbij : ∑ m ∈ Ico 1 p, centredBernoulliTwoSample p (m * fermatModInv p k % p) =
        ∑ r ∈ Ico 1 p, centredBernoulliTwoSample p r := by
      refine sum_nbij' (fun m => m * fermatModInv p k % p) (fun r => r * k % p) ?_ ?_ ?_ ?_ ?_
      · intro m hm; exact mul_mod_mem_Ico_of_prime hp hm hinv_mem
      · intro r hr; exact mul_mod_mem_Ico_of_prime hp hr hk
      · intro m hm
        have hm' := mem_Ico.mp hm
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, mul_assoc, mul_comm (fermatModInv p k) k,
          Nat.mul_mod, hkbar, mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hm'.2]
      · intro r hr
        have hr' := mem_Ico.mp hr
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, mul_assoc, Nat.mul_mod, hkbar, mul_one,
          Nat.mod_mod, Nat.mod_eq_of_lt hr'.2]
      · intro _ _; rfl
    rw [hbij, sum_Ico_centredBernoulliTwoSample_eq_zero hp.pos, mul_zero]
  rw [sum_eq_zero hinner, mul_zero]

/-- Reindexing `k ↦ m k̄_p mod p` preserves the zero sum of `centredBernoulliTwoSample p` on `Ico 1 p`. -/
theorem sum_Ico_centredBernoulliTwoSample_mul_fermatModInv_eq_zero {p m : ℕ} (hp : p.Prime)
    (hm : m ∈ Ico 1 p) :
    ∑ k ∈ Ico 1 p, centredBernoulliTwoSample p (m * fermatModInv p k % p) = 0 := by
  refine (sum_nbij' (fun k => m * fermatModInv p k % p)
    (fun r => m * fermatModInv p r % p) ?_ ?_ ?_ ?_ (fun _ _ => rfl)).trans
    (sum_Ico_centredBernoulliTwoSample_eq_zero hp.pos)
  · intro k hk
    exact mul_mod_mem_Ico_of_prime hp hm (fermatModInv_mem_Ico hp (not_dvd_of_mem_Ico hk))
  · intro r hr
    exact mul_mod_mem_Ico_of_prime hp hm (fermatModInv_mem_Ico hp (not_dvd_of_mem_Ico hr))
  · intro k hk; exact mul_fermatModInv_involutive hp hm hk
  · intro r hr; exact mul_fermatModInv_involutive hp hm hr

/-- Relation between `Φ_p`-weighted convolution and `reciprocityKloostermanCoeff`:
for prime `p` and `1 ≤ m < p`,
`(π² / p) ∑_{k=1}^{p-1} B₂(k / p) Φ_p(m k̄_p mod p) = primeKernelMean p + C_m(p)`. -/
theorem sum_bernoulliTwo_mul_residuePotential_eq {p m : ℕ} (hp : p.Prime) (hm : m ∈ Ico 1 p) :
    (Real.pi ^ 2 / (p : ℝ)) *
        (∑ k ∈ Ico 1 p, bernoulliTwo ((k : ℝ) / p) *
          residuePotential p (m * fermatModInv p k % p)) =
      primeKernelMean p + reciprocityKloostermanCoeff p m := by
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hterm : ∀ k ∈ Ico 1 p,
      bernoulliTwo ((k : ℝ) / p) * residuePotential p (m * fermatModInv p k % p) =
        ((p : ℝ) ^ 2 / 2) * (centredBernoulliTwoSample p k *
            centredBernoulliTwoSample p (m * fermatModInv p k % p)) -
          ((p : ℝ) / 12) * centredBernoulliTwoSample p (m * fermatModInv p k % p) -
          (((p : ℝ) + 1) / 12) * centredBernoulliTwoSample p k +
          ((p : ℝ) + 1) / (72 * (p : ℝ)) := by
    intro k _
    rw [residuePotential_eq_centredBernoulliTwoSample hp.pos (Nat.mod_lt _ hp.pos)]
    have hB : bernoulliTwo ((k : ℝ) / p) = centredBernoulliTwoSample p k - 1 / (6 * (p : ℝ)) := by
      unfold centredBernoulliTwoSample; ring
    rw [hB]
    field_simp
    ring
  rw [sum_congr rfl hterm, sum_add_distrib, sum_sub_distrib, sum_sub_distrib,
    ← mul_sum, ← mul_sum, ← mul_sum,
    sum_Ico_centredBernoulliTwoSample_mul_fermatModInv_eq_zero hp hm,
    sum_Ico_centredBernoulliTwoSample_eq_zero hp.pos,
    sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hp.pos, Nat.cast_one]
  unfold primeKernelMean reciprocityKloostermanCoeff
  field_simp
  ring

theorem cos_two_pi_mod {d : ℕ} (hd : 0 < d) (m : ℕ) :
    Real.cos (2 * Real.pi * ((m % d : ℕ) : ℝ) / d) = Real.cos (2 * Real.pi * (m : ℝ) / d) := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hm : (m : ℝ) = (d : ℝ) * ((m / d : ℕ) : ℝ) + ((m % d : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod m d).symm
  have hphase : 2 * Real.pi * (m : ℝ) / d =
      2 * Real.pi * ((m % d : ℕ) : ℝ) / d + ((m / d : ℕ) : ℝ) * (2 * Real.pi) := by
    rw [hm]; field_simp; ring
  rw [hphase, Real.cos_add_nat_mul_two_pi]

theorem sum_Ico_cos_two_pi_of_not_dvd {p u : ℕ} (hp : p.Prime) (hu : ¬ p ∣ u) :
    ∑ m ∈ Ico 1 p, Real.cos (2 * Real.pi * ((m * u : ℕ) : ℝ) / p) = -1 := by
  have hmem : stdRoot p ^ u ∈ nontrivialRoots p := stdRoot_pow_mem_nontrivialRoots hp.pos hu
  obtain ⟨hne1, hpow⟩ := (mem_nontrivialRoots hp.pos).mp hmem
  have hgeom : ∑ m ∈ range p, (stdRoot p ^ u) ^ m = 0 := by
    rw [geom_sum_eq hne1, hpow, sub_self, zero_div]
  have hre := congrArg Complex.re hgeom
  rw [Complex.zero_re, ← sum_range_add_sum_Ico _ hp.pos, sum_range_one, pow_zero,
    Complex.add_re, Complex.one_re, Complex.re_sum] at hre
  have hcos : ∑ m ∈ Ico 1 p, ((stdRoot p ^ u) ^ m).re =
      ∑ m ∈ Ico 1 p, Real.cos (2 * Real.pi * ((m * u : ℕ) : ℝ) / p) := by
    refine sum_congr rfl fun m _ => ?_
    rw [← pow_mul, mul_comm u m, re_stdRoot_pow]
  linarith

/-- **Exact Kloosterman cosine expansion of `𝔅(p, n)` on `(ℤ/pℤ)ˣ`.**
For any prime `p` and `n` with `n * nbar % p = 1`,
`𝔅(p, n) = −π² (p² − 1) / (72 p) + ∑_{m=1}^{p-1} C_m(p) cos(2π m nbar / p)`. -/
theorem bernoulliKernel_eq_coprimeMean_add_kloosterman {p n nbar : ℕ} (hp : p.Prime)
    (hn : n * nbar % p = 1) :
    bernoulliKernel p n =
      -(Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * (p : ℝ))) +
        ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m *
          Real.cos (2 * Real.pi * ((m * nbar : ℕ) : ℝ) / p) := by
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hnd_nbar : ¬ p ∣ nbar := by
    intro hdvd
    have h0 : n * nbar % p = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hdvd n)
    omega
  rw [bernoulliKernel_eq_reciprocity hp.two_le hn]
  have hrewrite : Real.pi ^ 2 / 4 *
      (∑ k ∈ Ico 1 p,
        bernoulliTwo ((k : ℝ) / p) / Real.sin (Real.pi * ((k * nbar : ℕ) : ℝ) / p) ^ 2) =
      (Real.pi ^ 2 / (p : ℝ)) *
        ∑ k ∈ Ico 1 p, bernoulliTwo ((k : ℝ) / p) *
          ∑ M ∈ range p, residuePotential p M *
            Real.cos (2 * Real.pi * ((M * (k * nbar) : ℕ) : ℝ) / p) := by
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk' := mem_Ico.mp hk
    have hnd_kn : ¬ p ∣ k * nbar := by
      intro hdvd
      rcases hp.dvd_mul.mp hdvd with hpk | hpn
      · have := Nat.le_of_dvd hk'.1 hpk; omega
      · exact hnd_nbar hpn
    have hinv := one_div_four_sin_sq_eq_sum_residuePotential_cos hp.pos hnd_kn
    have hrew_div : Real.pi ^ 2 / 4 *
        (bernoulliTwo ((k : ℝ) / p) / Real.sin (Real.pi * ((k * nbar : ℕ) : ℝ) / p) ^ 2) =
        Real.pi ^ 2 * bernoulliTwo ((k : ℝ) / p) *
          (1 / (4 * Real.sin (Real.pi * ((k * nbar : ℕ) : ℝ) / p) ^ 2)) := by
      ring
    rw [hrew_div, hinv]
    ring
  rw [hrewrite]
  -- Split `M = 0` from `M ∈ Ico 1 p`, then reindex `M ↦ m = M * k % p` on `Ico 1 p`
  have hsplit_k : ∀ k ∈ Ico 1 p,
      bernoulliTwo ((k : ℝ) / p) *
          (∑ M ∈ range p, residuePotential p M *
            Real.cos (2 * Real.pi * ((M * (k * nbar) : ℕ) : ℝ) / p)) =
        bernoulliTwo ((k : ℝ) / p) * residuePotential p 0 +
          ∑ m ∈ Ico 1 p, bernoulliTwo ((k : ℝ) / p) *
            residuePotential p (m * fermatModInv p k % p) *
            Real.cos (2 * Real.pi * ((m * nbar : ℕ) : ℝ) / p) := by
    intro k hk
    have hk' := mem_Ico.mp hk
    have hnd_k : ¬ p ∣ k := fun h => by have := Nat.le_of_dvd hk'.1 h; omega
    have hkbar := mul_fermatModInv_mod_eq_one hp hnd_k
    have hinv_mem := fermatModInv_mem_Ico hp hnd_k
    rw [← sum_range_add_sum_Ico _ hp.pos, sum_range_one]
    simp only [zero_mul, Nat.cast_zero, mul_zero, zero_div, Real.cos_zero, mul_one, mul_add]
    congr 1
    rw [mul_sum]
    refine sum_nbij' (fun M => M * k % p) (fun m => m * fermatModInv p k % p) ?_ ?_ ?_ ?_ ?_
    · intro M hM; exact mul_mod_mem_Ico_of_prime hp hM hk
    · intro m hm; exact mul_mod_mem_Ico_of_prime hp hm hinv_mem
    · intro M hM
      have hM' := mem_Ico.mp hM
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, mul_assoc,
        Nat.mul_mod M (k * fermatModInv p k) p, hkbar, mul_one, Nat.mod_mod,
        Nat.mod_eq_of_lt hM'.2]
    · intro m hm
      have hm' := mem_Ico.mp hm
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, mul_assoc, mul_comm (fermatModInv p k) k,
        Nat.mul_mod, hkbar, mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hm'.2]
    · intro M hM
      have hM' := mem_Ico.mp hM
      have hinvM : M * k % p * fermatModInv p k % p = M := by
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, mul_assoc, Nat.mul_mod, hkbar, mul_one,
          Nat.mod_mod, Nat.mod_eq_of_lt hM'.2]
      have hcos_eq : Real.cos (2 * Real.pi * ((M * (k * nbar) : ℕ) : ℝ) / p) =
          Real.cos (2 * Real.pi * (((M * k % p) * nbar : ℕ) : ℝ) / p) := by
        have hmod : M * (k * nbar) % p = (M * k % p) * nbar % p := by
          rw [← mul_assoc M k nbar, Nat.mul_mod (M * k) nbar p,
            Nat.mul_mod (M * k % p) nbar p, Nat.mod_mod]
        rw [← cos_two_pi_mod hp.pos (M * (k * nbar)),
          ← cos_two_pi_mod hp.pos ((M * k % p) * nbar), hmod]
      rw [hinvM, hcos_eq]
      ring
  rw [sum_congr rfl hsplit_k, sum_add_distrib, ← sum_mul, sum_Ico_bernoulliTwo_div hp.pos]
  have hΦ0 : residuePotential p 0 = ((p : ℝ) ^ 2 - 1) / 12 := by simp [residuePotential]
  rw [hΦ0, sum_comm, mul_add]
  have hm_sum : (Real.pi ^ 2 / (p : ℝ)) *
      (∑ m ∈ Ico 1 p, ∑ k ∈ Ico 1 p,
        bernoulliTwo ((k : ℝ) / p) * residuePotential p (m * fermatModInv p k % p) *
          Real.cos (2 * Real.pi * ((m * nbar : ℕ) : ℝ) / p)) =
      (primeKernelMean p * ∑ m ∈ Ico 1 p, Real.cos (2 * Real.pi * ((m * nbar : ℕ) : ℝ) / p)) +
        ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m *
          Real.cos (2 * Real.pi * ((m * nbar : ℕ) : ℝ) / p) := by
    rw [mul_sum]
    have hterm : ∀ m ∈ Ico 1 p,
        (Real.pi ^ 2 / (p : ℝ)) *
            (∑ k ∈ Ico 1 p, bernoulliTwo ((k : ℝ) / p) *
              residuePotential p (m * fermatModInv p k % p) *
              Real.cos (2 * Real.pi * ((m * nbar : ℕ) : ℝ) / p)) =
          primeKernelMean p * Real.cos (2 * Real.pi * ((m * nbar : ℕ) : ℝ) / p) +
            reciprocityKloostermanCoeff p m *
              Real.cos (2 * Real.pi * ((m * nbar : ℕ) : ℝ) / p) := by
      intro m hm
      rw [← sum_mul, ← mul_assoc, sum_bernoulliTwo_mul_residuePotential_eq hp hm, add_mul]
    rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum]
  rw [hm_sum, sum_Ico_cos_two_pi_of_not_dvd hp hnd_nbar]
  unfold primeKernelMean
  field_simp
  ring

/-- **All-`n` orthogonal Ramanujan–Kloosterman decomposition of `𝔅(p, n) − primeKernelMean p`.**
For every prime `p` and every integer `n : ℕ` (whether divisible by `p` or coprime to `p`),
`𝔅(p, n) − m_p` splits into `(p + 1) m_p · c_p(n)` (Ramanujan's sum `c_p(n) = p 1_{p ∣ n} − 1`)
plus the zero-mean Kloosterman wave supported on `p ∤ n`. -/
theorem bernoulliKernel_sub_primeKernelMean_eq_ramanujan_add_kloosterman
    {p : ℕ} (hp : p.Prime) (n : ℕ) :
    bernoulliKernel p n - primeKernelMean p =
      ((p : ℝ) + 1) * primeKernelMean p * ((if p ∣ n then (p : ℝ) else 0) - 1) +
        (if p ∣ n then 0
          else ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m *
            Real.cos (2 * Real.pi * ((m * fermatModInv p n : ℕ) : ℝ) / p)) := by
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  by_cases hdvd : p ∣ n
  · rw [if_pos hdvd, if_pos hdvd, bernoulliKernel_mod, Nat.mod_eq_zero_of_dvd hdvd,
      bernoulliKernel_zero hp.pos]
    unfold primeKernelMean
    field_simp
    ring
  · rw [if_neg hdvd, if_neg hdvd,
      bernoulliKernel_eq_coprimeMean_add_kloosterman hp (mul_fermatModInv_mod_eq_one hp hdvd)]
    unfold primeKernelMean
    field_simp
    ring

/-! ## §4. Dedekind–Kloosterman dual formula and `O(p^{3/2})` Weil saving with zero log loss -/

theorem stdRoot_pow_eq_stdAddChar {p : ℕ} [NeZero p] (k : ℕ) :
    stdRoot p ^ k = ZMod.stdAddChar (k : ZMod p) := by
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  rw [stdRoot_pow, show (k : ZMod p) = ((k : ℤ) : ZMod p) by norm_cast, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  field_simp

theorem sum_Ico_one_div_four_sin_sq {d : ℕ} (hd : 0 < d) :
    ∑ a ∈ Ico 1 d, 1 / (4 * Real.sin (Real.pi * (a : ℝ) / d) ^ 2) =
      ((d : ℝ) ^ 2 - 1) / 12 := by
  have hω : IsPrimitiveRoot (stdRoot d) d := Complex.isPrimitiveRoot_exp d hd.ne'
  have hinj : Set.InjOn (fun a => stdRoot d ^ a) (Ico 1 d : Set ℕ) := fun i hi j hj h =>
    hω.pow_inj (mem_Ico.mp hi).2 (mem_Ico.mp hj).2 h
  have h := sum_nontrivialRoots_inv_norm_sq hd
  rw [nontrivialRoots_eq_image hd, sum_image hinj] at h
  rw [← h]
  refine sum_congr rfl fun a _ => ?_
  rw [norm_stdRoot_pow_sub_one_sq, one_div]

/-- **Dedekind–Kloosterman spectral representation of `reciprocityKloostermanCoeff p m`.**
For any prime `p` and `1 ≤ m < p`, `C_m(p)` is an exact `csc² × csc²` bilinear average of
classical Kloosterman sums `S(a, b m; p)`:
`(C_m(p) : ℂ) = (2 π² / p³) ∑_{a=1}^{p-1} ∑_{b=1}^{p-1}
    S(a, b m; p) / (16 sin²(π a / p) sin²(π b / p)) − π² (p − 1)(p + 1)² / (72 p³)`. -/
theorem reciprocityKloostermanCoeff_eq_kloostermanSum {p m : ℕ} (hp : p.Prime)
    [NeZero p] (hm : m ∈ Ico 1 p) :
    (reciprocityKloostermanCoeff p m : ℂ) =
      ((2 * Real.pi ^ 2 / (p : ℝ) ^ 3 : ℝ) : ℂ) *
        (∑ a ∈ Ico 1 p, ∑ b ∈ Ico 1 p,
          (((1 / (4 * Real.sin (Real.pi * (a : ℝ) / p) ^ 2)) *
              (1 / (4 * Real.sin (Real.pi * (b : ℝ) / p) ^ 2)) : ℝ) : ℂ) *
            kloostermanSum p (a : ZMod p) ((b * m : ℕ) : ZMod p)) -
        ((Real.pi ^ 2 * ((p : ℝ) - 1) * ((p : ℝ) + 1) ^ 2 / (72 * (p : ℝ) ^ 3) : ℝ) : ℂ) := by
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  haveI : Fact p.Prime := ⟨hp⟩
  -- Step 1: Relate `∑_{k=1}^{p-1} Φ_p(k) Φ_p(m k̄_p mod p)` to `C_m(p)` in `ℝ`
  have hΦ_corr : ∑ k ∈ Ico 1 p,
      residuePotential p k * residuePotential p (m * fermatModInv p k % p) =
      ((p : ℝ) ^ 3 / (2 * Real.pi ^ 2)) * reciprocityKloostermanCoeff p m +
        ((p : ℝ) - 1) * ((p : ℝ) + 1) ^ 2 / 144 := by
    have hterm : ∀ k ∈ Ico 1 p,
        residuePotential p k * residuePotential p (m * fermatModInv p k % p) =
          ((p : ℝ) ^ 4 / 4) * (centredBernoulliTwoSample p k *
              centredBernoulliTwoSample p (m * fermatModInv p k % p)) -
            ((p : ℝ) ^ 2 * ((p : ℝ) + 1) / 24) * centredBernoulliTwoSample p k -
            ((p : ℝ) ^ 2 * ((p : ℝ) + 1) / 24) *
              centredBernoulliTwoSample p (m * fermatModInv p k % p) +
            ((p : ℝ) + 1) ^ 2 / 144 := by
      intro k hk
      rw [residuePotential_eq_centredBernoulliTwoSample hp.pos (mem_Ico.mp hk).2,
        residuePotential_eq_centredBernoulliTwoSample hp.pos (Nat.mod_lt _ hp.pos)]
      ring
    rw [sum_congr rfl hterm, sum_add_distrib, sum_sub_distrib, sum_sub_distrib,
      ← mul_sum, ← mul_sum, ← mul_sum, sum_Ico_centredBernoulliTwoSample_eq_zero hp.pos,
      sum_Ico_centredBernoulliTwoSample_mul_fermatModInv_eq_zero hp hm,
      sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hp.pos, Nat.cast_one]
    have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
    unfold reciprocityKloostermanCoeff
    field_simp
    ring
  -- Step 2: Expand `∑_{k=1}^{p-1} Φ_p(k) Φ_p(m k̄_p mod p)` spectrally into Kloosterman sums
  have hω : IsPrimitiveRoot (stdRoot p) p := Complex.isPrimitiveRoot_exp p hp.ne_zero
  have hinj : Set.InjOn (fun a => stdRoot p ^ a) (Ico 1 p : Set ℕ) := fun i hi j hj h =>
    hω.pow_inj (mem_Ico.mp hi).2 (mem_Ico.mp hj).2 h
  have hspec_one : ∀ M : ℕ, (residuePotential p M : ℂ) =
      ∑ a ∈ Ico 1 p,
        (((1 / (4 * Real.sin (Real.pi * (a : ℝ) / p) ^ 2)) : ℝ) : ℂ) *
          ZMod.stdAddChar ((a : ZMod p) * (M : ZMod p)) := by
    intro M
    rw [residuePotential_eq_spectral hp.pos M, nontrivialRoots_eq_image hp.pos, sum_image hinj]
    refine sum_congr rfl fun a _ => ?_
    rw [norm_stdRoot_pow_sub_one_sq, ← one_div, ← pow_mul, stdRoot_pow_eq_stdAddChar, Nat.cast_mul]
  have hspec_prod : ((∑ k ∈ Ico 1 p,
      residuePotential p k * residuePotential p (m * fermatModInv p k % p) : ℝ) : ℂ) =
      ∑ a ∈ Ico 1 p, ∑ b ∈ Ico 1 p,
        (((1 / (4 * Real.sin (Real.pi * (a : ℝ) / p) ^ 2)) *
            (1 / (4 * Real.sin (Real.pi * (b : ℝ) / p) ^ 2)) : ℝ) : ℂ) *
          kloostermanSum p (a : ZMod p) ((b * m : ℕ) : ZMod p) := by
    rw [Complex.ofReal_sum]
    simp_rw [Complex.ofReal_mul, hspec_one, sum_mul, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun b _ => ?_
    have hkloos : ∑ k ∈ Ico 1 p,
        ZMod.stdAddChar ((a : ZMod p) * (k : ZMod p)) *
          ZMod.stdAddChar ((b : ZMod p) * ((m * fermatModInv p k % p : ℕ) : ZMod p)) =
        kloostermanSum p (a : ZMod p) ((b * m : ℕ) : ZMod p) := by
      unfold kloostermanSum kloostermanPhase
      symm
      refine sum_nbij' (fun x : (ZMod p)ˣ => (x : ZMod p).val)
        (fun k : ℕ => if h : (k : ZMod p) ≠ 0 then Units.mk0 (k : ZMod p) h else 1) ?_ ?_ ?_ ?_ ?_
      · intro x _
        refine mem_Ico.mpr ⟨?_, ZMod.val_lt (x : ZMod p)⟩
        by_contra h0
        have hz : (x : ZMod p) = 0 := (ZMod.val_eq_zero (x : ZMod p)).mp (by omega)
        exact Units.ne_zero x hz
      · intro _ _; exact mem_univ _
      · intro x _
        have hx0 : (((x : ZMod p).val : ℕ) : ZMod p) ≠ 0 := by
          rw [ZMod.natCast_zmod_val]; exact Units.ne_zero x
        rw [dif_pos hx0]
        ext
        exact ZMod.natCast_zmod_val (x : ZMod p)
      · intro k hk
        have hk0 : (k : ZMod p) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]
          exact not_dvd_of_mem_Ico hk
        rw [dif_pos hk0, Units.val_mk0]
        exact ZMod.val_natCast_of_lt (mem_Ico.mp hk).2
      · intro x _
        set k := (x : ZMod p).val
        have hk_lt : k < p := ZMod.val_lt (x : ZMod p)
        have hk_pos : 1 ≤ k := by
          by_contra h0
          exact Units.ne_zero x ((ZMod.val_eq_zero (x : ZMod p)).mp (by omega))
        have hnd_k : ¬ p ∣ k := not_dvd_of_mem_Ico (mem_Ico.mpr ⟨hk_pos, hk_lt⟩)
        have hk_cast : (k : ZMod p) = (x : ZMod p) := ZMod.natCast_zmod_val (x : ZMod p)
        have hinv_k : (fermatModInv p k : ZMod p) = ((x⁻¹ : (ZMod p)ˣ) : ZMod p) := by
          rw [Units.val_inv_eq_inv_val, ← hk_cast]
          exact cast_fermatModInv_eq_inv hp hnd_k
        rw [← AddChar.map_add_eq_mul]
        congr 1
        rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_mul, hk_cast, hinv_k]
        ring
    rw [← hkloos, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    ring
  -- Step 3: Solve for `(reciprocityKloostermanCoeff p m : ℂ)`
  set S : ℂ := ∑ a ∈ Ico 1 p, ∑ b ∈ Ico 1 p,
      (((1 / (4 * Real.sin (Real.pi * (a : ℝ) / p) ^ 2)) *
          (1 / (4 * Real.sin (Real.pi * (b : ℝ) / p) ^ 2)) : ℝ) : ℂ) *
        kloostermanSum p (a : ZMod p) ((b * m : ℕ) : ZMod p)
  have hC_corr : S =
      ((((p : ℝ) ^ 3 / (2 * Real.pi ^ 2)) * reciprocityKloostermanCoeff p m +
        ((p : ℝ) - 1) * ((p : ℝ) + 1) ^ 2 / 144 : ℝ) : ℂ) := by
    rw [← hspec_prod, hΦ_corr]
  clear_value S
  clear hspec_prod
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast at hC_corr ⊢
  linear_combination ((2 * (Real.pi : ℂ) ^ 2) / (p : ℂ) ^ 3) * hC_corr.symm +
    (by field_simp; ring :
      (reciprocityKloostermanCoeff p m : ℂ) -
        ((2 * (Real.pi : ℂ) ^ 2) / (p : ℂ) ^ 3) *
          (((p : ℂ) ^ 3 / (2 * (Real.pi : ℂ) ^ 2)) * (reciprocityKloostermanCoeff p m : ℂ) +
            ((p : ℂ) - 1) * ((p : ℂ) + 1) ^ 2 / 144) =
      -((Real.pi : ℂ) ^ 2 * ((p : ℂ) - 1) * ((p : ℂ) + 1) ^ 2 / (72 * (p : ℂ) ^ 3)))

/-- **Square-root Weil bound on `reciprocityKloostermanCoeff p m` with zero logarithmic loss.**
For every prime `p` and every `1 ≤ m < p`,
`|C_m(p)| ≤ π² (p² − 1)² / (36 p² √p) + π² (p − 1)(p + 1)² / (72 p³)`. -/
theorem abs_reciprocityKloostermanCoeff_le_weil {p m : ℕ} (hp : p.Prime) (hm : m ∈ Ico 1 p) :
    |reciprocityKloostermanCoeff p m| ≤
      Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (36 * (p : ℝ) ^ 2 * Real.sqrt p) +
        Real.pi ^ 2 * ((p : ℝ) - 1) * ((p : ℝ) + 1) ^ 2 / (72 * (p : ℝ) ^ 3) := by
  rcases eq_or_ne p 2 with rfl | hp2
  · rw [reciprocityKloostermanCoeff_two, abs_zero]
    positivity
  · haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : Fact p.Prime := ⟨hp⟩
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hsqrt_pos : 0 < Real.sqrt p := Real.sqrt_pos.mpr hpR
    rw [← Real.norm_eq_abs, ← Complex.norm_real, reciprocityKloostermanCoeff_eq_kloostermanSum hp hm]
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (by
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
      positivity)]
    refine add_le_add ?_ le_rfl
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hsum_le :
        ‖∑ a ∈ Ico 1 p, ∑ b ∈ Ico 1 p,
            (((1 / (4 * Real.sin (Real.pi * (a : ℝ) / p) ^ 2)) *
                (1 / (4 * Real.sin (Real.pi * (b : ℝ) / p) ^ 2)) : ℝ) : ℂ) *
              kloostermanSum p (a : ZMod p) ((b * m : ℕ) : ZMod p)‖ ≤
          (((p : ℝ) ^ 2 - 1) / 12) ^ 2 * (2 * Real.sqrt p) := by
      calc ‖∑ a ∈ Ico 1 p, ∑ b ∈ Ico 1 p,
              (((1 / (4 * Real.sin (Real.pi * (a : ℝ) / p) ^ 2)) *
                  (1 / (4 * Real.sin (Real.pi * (b : ℝ) / p) ^ 2)) : ℝ) : ℂ) *
                kloostermanSum p (a : ZMod p) ((b * m : ℕ) : ZMod p)‖
          ≤ ∑ a ∈ Ico 1 p, ∑ b ∈ Ico 1 p,
              (1 / (4 * Real.sin (Real.pi * (a : ℝ) / p) ^ 2)) *
                (1 / (4 * Real.sin (Real.pi * (b : ℝ) / p) ^ 2)) * (2 * Real.sqrt p) := by
            refine (norm_sum_le _ _).trans (sum_le_sum fun a _ => ?_)
            refine (norm_sum_le _ _).trans (sum_le_sum fun b hb => ?_)
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hbm_mem := mul_mod_mem_Ico_of_prime hp hb hm
            have hbm_ne : ((b * m : ℕ) : ZMod p) ≠ 0 := by
              rw [Ne, ZMod.natCast_eq_zero_iff]
              intro hdvd
              have h0 := Nat.mod_eq_zero_of_dvd hdvd
              have := (mem_Ico.mp hbm_mem).1
              omega
            exact RHTower.norm_kloostermanSum_le_weil p hp2 (a : ZMod p) hbm_ne
        _ = (∑ a ∈ Ico 1 p, 1 / (4 * Real.sin (Real.pi * (a : ℝ) / p) ^ 2)) *
              (∑ b ∈ Ico 1 p, 1 / (4 * Real.sin (Real.pi * (b : ℝ) / p) ^ 2)) *
              (2 * Real.sqrt p) := by
            rw [sum_mul_sum, sum_mul]
            refine sum_congr rfl fun a _ => ?_
            rw [sum_mul]
        _ = (((p : ℝ) ^ 2 - 1) / 12) ^ 2 * (2 * Real.sqrt p) := by
            rw [sum_Ico_one_div_four_sin_sq hp.pos]
            ring
    calc (2 * Real.pi ^ 2 / (p : ℝ) ^ 3) *
          ‖∑ a ∈ Ico 1 p, ∑ b ∈ Ico 1 p,
              (((1 / (4 * Real.sin (Real.pi * (a : ℝ) / p) ^ 2)) *
                  (1 / (4 * Real.sin (Real.pi * (b : ℝ) / p) ^ 2)) : ℝ) : ℂ) *
                kloostermanSum p (a : ZMod p) ((b * m : ℕ) : ZMod p)‖
        ≤ (2 * Real.pi ^ 2 / (p : ℝ) ^ 3) *
            ((((p : ℝ) ^ 2 - 1) / 12) ^ 2 * (2 * Real.sqrt p)) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (36 * (p : ℝ) ^ 2 * Real.sqrt p) := by
          have hsq : Real.sqrt p ^ 2 = (p : ℝ) := Real.sq_sqrt hpR.le
          field_simp
          rw [hsq]
          ring

/-- Clean `O(p^{3/2})` uniform envelope `|C_m(p)| ≤ (π² / 24) p √p` for every prime `p` and
`1 ≤ m < p`, saving `√p` over the trivial `O(p²)` bound. -/
theorem abs_reciprocityKloostermanCoeff_le_pow_three_halves {p m : ℕ} (hp : p.Prime)
    (hm : m ∈ Ico 1 p) :
    |reciprocityKloostermanCoeff p m| ≤ (Real.pi ^ 2 / 24) * (p : ℝ) * Real.sqrt p := by
  rcases eq_or_ne p 2 with rfl | hp2
  · rw [reciprocityKloostermanCoeff_two, abs_zero]
    positivity
  · rcases eq_or_ne p 3 with rfl | hp3
    · rw [reciprocityKloostermanCoeff_three, abs_zero]
      positivity
    · have hp5 : 5 ≤ p := by
        by_contra hlt
        interval_cases p
        · exact Nat.not_prime_zero hp
        · exact Nat.not_prime_one hp
        · exact hp2 rfl
        · exact hp3 rfl
        · exact absurd hp (by
            rw [show (4 : ℕ) = 2 * 2 from rfl]
            exact Nat.not_prime_mul one_lt_two.ne' one_lt_two.ne')
      have hp5R : (5 : ℝ) ≤ p := by exact_mod_cast hp5
      have hpR : (0 : ℝ) < p := by positivity
      have hsqrt_pos : 0 < Real.sqrt p := Real.sqrt_pos.mpr hpR
      have hsqrt_le : Real.sqrt p ≤ p := by
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith
      refine (abs_reciprocityKloostermanCoeff_le_weil hp hm).trans ?_
      have h1 : Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (36 * (p : ℝ) ^ 2 * Real.sqrt p) ≤
          (Real.pi ^ 2 / 36) * (p : ℝ) * Real.sqrt p := by
        rw [div_le_iff₀ (by positivity)]
        have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hpR.le
        have hnum : ((p : ℝ) ^ 2 - 1) ^ 2 ≤ (p : ℝ) ^ 4 := by nlinarith
        have hrew : (Real.pi ^ 2 / 36) * (p : ℝ) * Real.sqrt p *
            (36 * (p : ℝ) ^ 2 * Real.sqrt p) = Real.pi ^ 2 * (p : ℝ) ^ 4 := by
          calc (Real.pi ^ 2 / 36) * (p : ℝ) * Real.sqrt p * (36 * (p : ℝ) ^ 2 * Real.sqrt p)
              = Real.pi ^ 2 * (p : ℝ) ^ 3 * (Real.sqrt p * Real.sqrt p) := by ring
            _ = Real.pi ^ 2 * (p : ℝ) ^ 4 := by rw [hsq]; ring
        rw [hrew]
        exact mul_le_mul_of_nonneg_left hnum (by positivity)
      have h2 : Real.pi ^ 2 * ((p : ℝ) - 1) * ((p : ℝ) + 1) ^ 2 / (72 * (p : ℝ) ^ 3) ≤
          (Real.pi ^ 2 / 72) * (p : ℝ) * Real.sqrt p := by
        rw [div_le_iff₀ (by positivity)]
        have hsqrt1 : (1 : ℝ) ≤ Real.sqrt p := by
          rw [← Real.sqrt_one]
          exact Real.sqrt_le_sqrt (by linarith)
        have hpoly : ((p : ℝ) - 1) * ((p : ℝ) + 1) ^ 2 ≤ (p : ℝ) ^ 4 * Real.sqrt p := by
          calc ((p : ℝ) - 1) * ((p : ℝ) + 1) ^ 2
              ≤ (p : ℝ) ^ 4 * 1 := by nlinarith
            _ ≤ (p : ℝ) ^ 4 * Real.sqrt p :=
                mul_le_mul_of_nonneg_left hsqrt1 (by positivity)
        have hmul := mul_le_mul_of_nonneg_left hpoly (sq_nonneg Real.pi)
        linarith
      linarith

/-- **Sub-trivial `O(p⁴)` `ℓ²` energy bound on `C_m(p)`.**
Summing the square-root Weil bound over `1 ≤ m < p` gives
`∑_{m=1}^{p-1} C_m(p)² ≤ (π⁴ / 576) (p − 1) p³`, saving a full factor of `p` over the trivial
`O(p⁵)` bound. -/
theorem sum_Ico_reciprocityKloostermanCoeff_sq_le {p : ℕ} (hp : p.Prime) :
    ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m ^ 2 ≤
      (Real.pi ^ 4 / 576) * ((p : ℝ) - 1) * (p : ℝ) ^ 3 := by
  have hpR : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hterm : ∀ m ∈ Ico 1 p,
      reciprocityKloostermanCoeff p m ^ 2 ≤ (Real.pi ^ 4 / 576) * (p : ℝ) ^ 3 := by
    intro m hm
    have hb := abs_reciprocityKloostermanCoeff_le_pow_three_halves hp hm
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [sq_abs] at hsq
    refine hsq.trans (le_of_eq ?_)
    calc ((Real.pi ^ 2 / 24) * (p : ℝ) * Real.sqrt p) ^ 2
        = (Real.pi ^ 4 / 576) * (p : ℝ) ^ 2 * Real.sqrt p ^ 2 := by ring
      _ = (Real.pi ^ 4 / 576) * (p : ℝ) ^ 3 := by
          rw [Real.sq_sqrt hpR]
          ring
  calc ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m ^ 2
      ≤ ∑ _m ∈ Ico 1 p, (Real.pi ^ 4 / 576) * (p : ℝ) ^ 3 := sum_le_sum hterm
    _ = (Real.pi ^ 4 / 576) * ((p : ℝ) - 1) * (p : ℝ) ^ 3 := by
        rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hp.pos, Nat.cast_one]
        ring

end

end GaloisForLFunctions.BezoutValuationIncidence
