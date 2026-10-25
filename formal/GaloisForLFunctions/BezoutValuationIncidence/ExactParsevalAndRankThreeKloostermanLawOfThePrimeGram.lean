import GaloisForLFunctions.BezoutValuationIncidence.MultiplicativeConvolutionOfTheReciprocityKernel
import GaloisForLFunctions.RHTower.EulerDeletionCoprimeWordPeriodicity

/-!
# Exact Parseval Rigidity, Rank-Three Prime Gram Law, and Wiener Algebra of the Reciprocity Kernel

`MultiplicativeConvolutionOfTheReciprocityKernel` decomposed the prime-modulus Bernoulli kernel
`𝔅(p, n)` on `(ℤ/pℤ)ˣ` into its coprime mean `-π² (p² - 1) / (72 p)` plus a zero-mean Kloosterman
cosine sum `∑_{m=1}^{p-1} C_m(p) cos(2π m n̄_p / p)` whose coefficients `C_m(p)` satisfy the
log-free Weil bounds `|C_m(p)| ≤ (π² / 24) p √p` and `∑_{m=1}^{p-1} C_m(p)² ≤ (π⁴ / 576)(p - 1) p³`.

This module establishes five structural laws governing `C_m(p)`, the zero-mean reciprocity kernel
`W_K(p, n)`, and the energy-centered pronic Gram `𝒢^{ec}(p, q)` of distinct primes:

1. **Exact Unitary Parseval Identity on `(ℤ/pℤ)ˣ`
   (`mul_sum_Ico_reciprocityKloostermanCoeff_sq_eq_sum_kernel_sq`):**
   Even reflection symmetry `C_{p - m}(p) = C_m(p)` upgrades the cosine series of `W_K(p, n)` on
   `(ℤ/pℤ)ˣ` to the complex exponential series `∑_{m=1}^{p-1} C_m(p) ω_p^{m n̄_p}`, and its `u = 0`
   fibre vanishes by `∑_{m=1}^{p-1} C_m(p) = 0`. Unitary Parseval over `ℤ/pℤ` and bijectivity of
   modular inversion `n ↦ n̄_p` on `{1, …, p - 1}` give the exact identity
   `p ∑_{m=1}^{p-1} C_m(p)² = ∑_{n=1}^{p-1} (𝔅(p, n) + π²(p² - 1)/(72 p))²`.

2. **Unconditional `Θ(p⁴)` and `Θ(p^{3/2})` Order-Sharpness of `C_m(p)`
   (`sum_Ico_reciprocityKloostermanCoeff_sq_ge`, `exists_abs_reciprocityKloostermanCoeff_ge`):**
   Combining the exact Parseval identity with the negativity window `𝔅(p, n) ≤ -p² / 100` near `p / 2`
   (`bernoulliKernel_le_of_near_half`) proves that for every prime `p ≥ 67`,
   `∑_{m=1}^{p-1} C_m(p)² ≥ p⁴ / 5120000` and `max_{1 ≤ m < p} |C_m(p)| ≥ (1 / 2400) p √p`.
   Thus the `O(p⁴)` `ℓ²` bound and `O(p^{3/2})` pointwise Weil bound on `C_m(p)` are order-sharp up
   to absolute constants: no single-prime sub-Weil saving on `C_m(p)` exists.

3. **Explicit Rank-Three + Zero-Mean Kloosterman Law of the Prime Pronic Gram
   (`abs_pmRamanujanEnergyCenteredGram_sub_rankThree_kloosterman_le`):**
   For distinct primes `p ≠ q` with `p, q ≤ N`, extracting the nonzero coprime mean of `𝔅(p, q)`
   upgrades the rank-two approximation of `𝒢^{ec}(p, q)` to an explicit **rank-three** separable
   prediction `D_p log q - p β_p - (π²(p² - 1)/(72 p)) · (1 / q)` plus `W_K(p, q) / q`, accurate
   to `(3/4) p³ / q²`.

4. **Exact Two-Prime Chinese-Remainder Orthogonality and Terminal-Block Reduction
   (`sum_range_mul_reciprocityZeroMeanKernel_eq_zero`,
   `sum_range_mul_reciprocityZeroMeanKernel_eq_terminal`):**
   For any two distinct primes `p₁ ≠ p₂`, `W_K(p₁, n)` and `W_K(p₂, n)` are periodic of coprime
   periods `p₁, p₂` with zero complete-period sum, so `∑_{n < p₁ p₂} W_K(p₁, n) W_K(p₂, n) = 0`
   identically and any incomplete interval correlation `∑_{n < M} W_K(p₁, n) W_K(p₂, n)` collapses
   to its terminal residue block of length `M mod (p₁ p₂)`.

5. **Positive-Definite Linear Cosine Spectrum of `𝔅(p, ·)` and `√p`-Loss-Free Wiener Algebra Bound
   (`bernoulliLinearCoeff_nonneg`, `sum_Ico_bernoulliLinearCoeff_eq`,
   `sum_Ico_abs_reciprocityLinearCoeff_le`):**
   Every nonzero linear cosine Fourier mode `α̃_p(h)` (`1 ≤ h < p`) of `𝔅(p, n)` on `ℤ/pℤ` is
   nonnegative, so Bochner evaluation at `n = 0` gives the exact `ℓ¹` Fourier identity
   `∑_{h=1}^{p-1} |α̃_p(h)| = π² (p² - 1)² / (72 p²)`. Subtracting the `p ∣ n` point mass yields the
   exact linear-exponential representation of `W_K(p, n)` with `α_p(0) = 0` and Wiener algebra norm
   `∑_{h=1}^{p-1} |α_p(h)| ≤ π² (p² - 1)² / (36 p²) ≤ (π² / 36) p²`, avoiding any `√p` Cauchy–Schwarz
   loss over `‖W_K(p, ·)‖_∞ ≍ p²`.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The zero-mean reciprocity kernel `reciprocityZeroMeanKernel` and its exponential form -/

/-- **The zero-mean reciprocity kernel `W_K(p, n)`.**
Supported on integers coprime to `p`, where it removes the coprime mean `-π² (p² - 1) / (72 p)`
from `bernoulliKernel p n`, and set to `0` on multiples of `p`. -/
def reciprocityZeroMeanKernel (p n : ℕ) : ℝ :=
  if p ∣ n then 0 else bernoulliKernel p n + Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * (p : ℝ))

@[simp]
theorem reciprocityZeroMeanKernel_of_dvd {p n : ℕ} (h : p ∣ n) :
    reciprocityZeroMeanKernel p n = 0 := by
  rw [reciprocityZeroMeanKernel, if_pos h]

@[simp]
theorem reciprocityZeroMeanKernel_zero (p : ℕ) :
    reciprocityZeroMeanKernel p 0 = 0 :=
  reciprocityZeroMeanKernel_of_dvd (dvd_zero p)

theorem reciprocityZeroMeanKernel_of_not_dvd {p n : ℕ} (h : ¬ p ∣ n) :
    reciprocityZeroMeanKernel p n =
      bernoulliKernel p n + Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * (p : ℝ)) := by
  rw [reciprocityZeroMeanKernel, if_neg h]

theorem bernoulliKernel_periodic {d : ℕ} (_hd : 0 < d) :
    Function.Periodic (bernoulliKernel d) d := by
  intro n
  rw [bernoulliKernel_mod d (n + d), bernoulliKernel_mod d n, Nat.add_mod_right]

theorem reciprocityZeroMeanKernel_mod (p n : ℕ) :
    reciprocityZeroMeanKernel p (n % p) = reciprocityZeroMeanKernel p n := by
  unfold reciprocityZeroMeanKernel
  have hdvd : p ∣ n % p ↔ p ∣ n := Nat.dvd_mod_iff (dvd_refl p)
  by_cases h : p ∣ n
  · rw [if_pos (hdvd.mpr h), if_pos h]
  · rw [if_neg (mt hdvd.mp h), if_neg h, ← bernoulliKernel_mod]

theorem reciprocityZeroMeanKernel_periodic (p : ℕ) :
    Function.Periodic (reciprocityZeroMeanKernel p) p := by
  intro n
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · rw [← reciprocityZeroMeanKernel_mod p (n + p), ← reciprocityZeroMeanKernel_mod p n,
      Nat.add_mod_right]

/-- Exact Kloosterman cosine representation of `W_K(p, n)` on `(ℤ/pℤ)ˣ`. -/
theorem reciprocityZeroMeanKernel_eq_kloosterman {p n nbar : ℕ} (hp : p.Prime)
    (hn : n * nbar % p = 1) :
    reciprocityZeroMeanKernel p n =
      ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m *
        Real.cos (2 * Real.pi * ((m * nbar : ℕ) : ℝ) / p) := by
  have hnd : ¬ p ∣ n := by
    intro hdvd
    have h0 : n * nbar % p = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hdvd nbar)
    omega
  rw [reciprocityZeroMeanKernel_of_not_dvd hnd, bernoulliKernel_eq_coprimeMean_add_kloosterman hp hn]
  ring

theorem norm_stdRoot_eq_one (d : ℕ) : ‖stdRoot d‖ = 1 := by
  unfold stdRoot
  have hrew : (2 * (Real.pi : ℂ) * Complex.I / (d : ℂ)) =
      (((2 * Real.pi / (d : ℝ) : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hrew]
  exact Complex.norm_exp_ofReal_mul_I _

theorem stdRoot_pow_sub_mul_eq_conj {d m u : ℕ} (hd : 0 < d) (hm : m ≤ d) :
    stdRoot d ^ ((d - m) * u) = conj (stdRoot d ^ (m * u)) := by
  have hω : IsPrimitiveRoot (stdRoot d) d := Complex.isPrimitiveRoot_exp d hd.ne'
  have hnorm : ‖stdRoot d ^ (m * u)‖ = 1 := by
    rw [norm_pow, norm_stdRoot_eq_one, one_pow]
  have hne : stdRoot d ^ (m * u) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact zero_ne_one hnorm
  rw [← Complex.inv_eq_conj hnorm]
  have hprod : stdRoot d ^ ((d - m) * u) * stdRoot d ^ (m * u) = 1 := by
    rw [← pow_add, ← Nat.add_mul, Nat.sub_add_cancel hm, pow_mul, hω.pow_eq_one, one_pow]
  calc stdRoot d ^ ((d - m) * u)
      = (stdRoot d ^ ((d - m) * u) * stdRoot d ^ (m * u)) * (stdRoot d ^ (m * u))⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
    _ = (stdRoot d ^ (m * u))⁻¹ := by rw [hprod, one_mul]

/-- Because `C_{p - m}(p) = C_m(p)`, the complex exponential sum `∑_{m=1}^{p-1} C_m(p) ω_p^{m n̄_p}`
is already real and equals `reciprocityZeroMeanKernel p n` without taking real parts. -/
theorem reciprocityZeroMeanKernel_eq_exp_sum {p n nbar : ℕ} (hp : p.Prime)
    (hn : n * nbar % p = 1) :
    (reciprocityZeroMeanKernel p n : ℂ) =
      ∑ m ∈ Ico 1 p, (reciprocityKloostermanCoeff p m : ℂ) * stdRoot p ^ (m * nbar) := by
  set S : ℂ := ∑ m ∈ Ico 1 p, (reciprocityKloostermanCoeff p m : ℂ) * stdRoot p ^ (m * nbar)
  have hconj : conj S = S := by
    dsimp [S]
    rw [map_sum]
    refine sum_nbij' (fun m => p - m) (fun m => p - m) ?_ ?_ ?_ ?_ ?_
    · intro m hm; have := mem_Ico.mp hm; exact mem_Ico.mpr ⟨by omega, by omega⟩
    · intro m hm; have := mem_Ico.mp hm; exact mem_Ico.mpr ⟨by omega, by omega⟩
    · intro m hm; have := mem_Ico.mp hm; omega
    · intro m hm; have := mem_Ico.mp hm; omega
    · intro m hm
      have hm' := mem_Ico.mp hm
      rw [map_mul, Complex.conj_ofReal, reciprocityKloostermanCoeff_reflect hp hm,
        stdRoot_pow_sub_mul_eq_conj hp.pos hm'.2.le]
  have hS_real : S = (S.re : ℂ) := by
    apply Complex.ext
    · simp
    · have him := congrArg Complex.im hconj
      rw [Complex.conj_im] at him
      simp only [Complex.ofReal_im]
      linarith
  rw [hS_real, reciprocityZeroMeanKernel_eq_kloosterman hp hn]
  congr 1
  dsimp [S]
  rw [Complex.re_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [Complex.re_ofReal_mul, re_stdRoot_pow]

theorem fermatModInv_involutive {p n : ℕ} (hp : p.Prime) (hn : n ∈ Ico 1 p) :
    fermatModInv p (fermatModInv p n) = n := by
  have h1 := mul_fermatModInv_involutive hp (mem_Ico.mpr ⟨le_rfl, hp.one_lt⟩) hn
  have hlt1 : fermatModInv p n < p :=
    (mem_Ico.mp (fermatModInv_mem_Ico hp (not_dvd_of_mem_Ico hn))).2
  rw [one_mul, one_mul, Nat.mod_eq_of_lt hlt1] at h1
  have hlt2 : fermatModInv p (fermatModInv p n) < p :=
    (mem_Ico.mp (fermatModInv_mem_Ico hp (not_dvd_of_mem_Ico
      (fermatModInv_mem_Ico hp (not_dvd_of_mem_Ico hn))))).2
  rwa [Nat.mod_eq_of_lt hlt2] at h1

theorem stdRoot_pow_mul_self (d k : ℕ) (hd : 0 < d) : stdRoot d ^ (k * d) = 1 := by
  have hω : IsPrimitiveRoot (stdRoot d) d := Complex.isPrimitiveRoot_exp d hd.ne'
  rw [mul_comm, pow_mul, hω.pow_eq_one, one_pow]

/-- **Exact zero sum of `W_K(p, n)` over `(ℤ/pℤ)ˣ`.** -/
theorem sum_Ico_reciprocityZeroMeanKernel_eq_zero {p : ℕ} (hp : p.Prime) :
    ∑ n ∈ Ico 1 p, reciprocityZeroMeanKernel p n = 0 := by
  have hbij : ∑ n ∈ Ico 1 p, reciprocityZeroMeanKernel p n =
      ∑ u ∈ Ico 1 p,
        ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m *
          Real.cos (2 * Real.pi * ((m * u : ℕ) : ℝ) / p) := by
    refine sum_nbij' (fun n => fermatModInv p n) (fun u => fermatModInv p u) ?_ ?_ ?_ ?_ ?_
    · intro n hn; exact fermatModInv_mem_Ico hp (not_dvd_of_mem_Ico hn)
    · intro u hu; exact fermatModInv_mem_Ico hp (not_dvd_of_mem_Ico hu)
    · intro n hn; exact fermatModInv_involutive hp hn
    · intro u hu; exact fermatModInv_involutive hp hu
    · intro n hn
      exact reciprocityZeroMeanKernel_eq_kloosterman hp
        (mul_fermatModInv_mod_eq_one hp (not_dvd_of_mem_Ico hn))
  rw [hbij, sum_comm]
  have hinner : ∀ m ∈ Ico 1 p,
      ∑ u ∈ Ico 1 p, reciprocityKloostermanCoeff p m *
        Real.cos (2 * Real.pi * ((m * u : ℕ) : ℝ) / p) =
        -reciprocityKloostermanCoeff p m := by
    intro m hm
    rw [← mul_sum]
    have hcos : ∑ u ∈ Ico 1 p, Real.cos (2 * Real.pi * ((m * u : ℕ) : ℝ) / p) = -1 := by
      have hcomm : ∀ u ∈ Ico 1 p,
          Real.cos (2 * Real.pi * ((m * u : ℕ) : ℝ) / p) =
            Real.cos (2 * Real.pi * ((u * m : ℕ) : ℝ) / p) := fun u _ => by
        rw [mul_comm m u]
      rw [sum_congr rfl hcomm]
      exact sum_Ico_cos_two_pi_of_not_dvd hp (not_dvd_of_mem_Ico hm)
    rw [hcos]
    ring
  rw [sum_congr rfl hinner, sum_neg_distrib, sum_Ico_reciprocityKloostermanCoeff_eq_zero hp, neg_zero]

/-- **Exact zero sum of `W_K(p, n)` over a complete residue block `[0, p)`.** -/
theorem sum_range_reciprocityZeroMeanKernel_eq_zero {p : ℕ} (hp : p.Prime) :
    ∑ n ∈ range p, reciprocityZeroMeanKernel p n = 0 := by
  rw [← sum_range_add_sum_Ico _ hp.pos, sum_range_one, reciprocityZeroMeanKernel_zero,
    sum_Ico_reciprocityZeroMeanKernel_eq_zero hp, add_zero]

/-! ## §2. Exact unitary Parseval identity on `(ℤ/pℤ)ˣ` and `Θ(p⁴)` / `Θ(p^{3/2})` sharpness -/

theorem sum_range_stdRoot_mul_conj_pow {d a b : ℕ} (hd : 0 < d) (ha : a < d) (hb : b < d) :
    ∑ u ∈ range d, (stdRoot d ^ a * conj (stdRoot d ^ b)) ^ u =
      if a = b then (d : ℂ) else 0 := by
  have hω : IsPrimitiveRoot (stdRoot d) d := Complex.isPrimitiveRoot_exp d hd.ne'
  have hnorm_b : ‖stdRoot d ^ b‖ = 1 := by
    rw [norm_pow, norm_stdRoot_eq_one, one_pow]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    have h1 : stdRoot d ^ a * conj (stdRoot d ^ a) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm_b, one_pow, Complex.ofReal_one]
    rw [sum_congr rfl fun u _ => by rw [h1, one_pow], sum_const, card_range, nsmul_eq_mul, mul_one]
  · rw [if_neg hab]
    have hne1 : stdRoot d ^ a * conj (stdRoot d ^ b) ≠ 1 := by
      intro h1
      have hmul := congrArg (· * stdRoot d ^ b) h1
      rw [mul_assoc, Complex.conj_mul', hnorm_b, Complex.ofReal_one, one_pow,
        mul_one, one_mul] at hmul
      exact hab (hω.pow_inj ha hb hmul)
    have hpow : (stdRoot d ^ a * conj (stdRoot d ^ b)) ^ d = 1 := by
      rw [mul_pow, ← pow_mul, mul_comm a d, pow_mul, hω.pow_eq_one, one_pow,
        ← map_pow, ← pow_mul, mul_comm b d, pow_mul, hω.pow_eq_one, one_pow, map_one, mul_one]
    rw [geom_sum_eq hne1, hpow, sub_self, zero_div]

/-- **Exact Parseval identity for `reciprocityKloostermanCoeff p` on `(ℤ/pℤ)ˣ`.**
For every prime `p`,
`p ∑_{m=1}^{p-1} C_m(p)² = ∑_{n=1}^{p-1} (𝔅(p, n) + π² (p² - 1) / (72 p))²`. -/
theorem mul_sum_Ico_reciprocityKloostermanCoeff_sq_eq_sum_kernel_sq {p : ℕ} (hp : p.Prime) :
    (p : ℝ) * ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m ^ 2 =
      ∑ n ∈ Ico 1 p,
        (bernoulliKernel p n + Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * (p : ℝ))) ^ 2 := by
  set g : ℕ → ℂ := fun u =>
    ∑ m ∈ Ico 1 p, (reciprocityKloostermanCoeff p m : ℂ) * stdRoot p ^ (m * u)
  have hg0 : g 0 = 0 := by
    dsimp [g]
    simp only [pow_zero, mul_one]
    rw [← Complex.ofReal_sum, sum_Ico_reciprocityKloostermanCoeff_eq_zero hp, Complex.ofReal_zero]
  -- Evaluate `∑_{u < p} g(u) conj(g(u))` via orthogonality of `ω_p^m` on `range p`
  have horth : ∑ u ∈ range p, g u * conj (g u) =
      (((p : ℝ) * ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m ^ 2 : ℝ) : ℂ) := by
    have hexpand : ∀ u ∈ range p, g u * conj (g u) =
        ∑ m₁ ∈ Ico 1 p, ∑ m₂ ∈ Ico 1 p,
          (reciprocityKloostermanCoeff p m₁ : ℂ) * (reciprocityKloostermanCoeff p m₂ : ℂ) *
            (stdRoot p ^ m₁ * conj (stdRoot p ^ m₂)) ^ u := by
      intro u _
      dsimp [g]
      rw [map_sum, sum_mul]
      refine sum_congr rfl fun m₁ _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun m₂ _ => ?_
      rw [map_mul, Complex.conj_ofReal, mul_pow, ← pow_mul, ← map_pow, ← pow_mul]
      ring
    rw [sum_congr rfl hexpand, sum_comm]
    have hm1 : ∀ m₁ ∈ Ico 1 p,
        ∑ u ∈ range p, ∑ m₂ ∈ Ico 1 p,
            (reciprocityKloostermanCoeff p m₁ : ℂ) * (reciprocityKloostermanCoeff p m₂ : ℂ) *
              (stdRoot p ^ m₁ * conj (stdRoot p ^ m₂)) ^ u =
          (p : ℂ) * (reciprocityKloostermanCoeff p m₁ : ℂ) ^ 2 := by
      intro m₁ hm₁
      rw [sum_comm]
      have hm2 : ∀ m₂ ∈ Ico 1 p,
          ∑ u ∈ range p,
              (reciprocityKloostermanCoeff p m₁ : ℂ) * (reciprocityKloostermanCoeff p m₂ : ℂ) *
                (stdRoot p ^ m₁ * conj (stdRoot p ^ m₂)) ^ u =
            if m₁ = m₂ then (p : ℂ) * (reciprocityKloostermanCoeff p m₁ : ℂ) ^ 2 else 0 := by
        intro m₂ hm₂
        rw [← mul_sum, sum_range_stdRoot_mul_conj_pow hp.pos (mem_Ico.mp hm₁).2 (mem_Ico.mp hm₂).2]
        split_ifs with heq
        · subst heq; ring
        · ring
      rw [sum_congr rfl hm2, sum_ite_eq (Ico 1 p) m₁, if_pos hm₁]
    rw [sum_congr rfl hm1, ← mul_sum]
    push_cast
    rfl
  -- Evaluate `∑_{u < p} g(u) conj(g(u))` in physical coordinates via `u = fermatModInv p n`
  have hphys : ∑ u ∈ range p, g u * conj (g u) =
      ((∑ n ∈ Ico 1 p, reciprocityZeroMeanKernel p n ^ 2 : ℝ) : ℂ) := by
    rw [← sum_range_add_sum_Ico _ hp.pos, sum_range_one, hg0, zero_mul, zero_add,
      Complex.ofReal_sum]
    refine sum_nbij' (fun u => fermatModInv p u) (fun n => fermatModInv p n) ?_ ?_ ?_ ?_ ?_
    · intro u hu; exact fermatModInv_mem_Ico hp (not_dvd_of_mem_Ico hu)
    · intro n hn; exact fermatModInv_mem_Ico hp (not_dvd_of_mem_Ico hn)
    · intro u hu; exact fermatModInv_involutive hp hu
    · intro n hn; exact fermatModInv_involutive hp hn
    · intro u hu
      set n := fermatModInv p u
      have hn_mem : n ∈ Ico 1 p := fermatModInv_mem_Ico hp (not_dvd_of_mem_Ico hu)
      have hn_inv : n * u % p = 1 := by
        rw [mul_comm]
        exact mul_fermatModInv_mod_eq_one hp (not_dvd_of_mem_Ico hu)
      have hgu : g u = (reciprocityZeroMeanKernel p n : ℂ) :=
        (reciprocityZeroMeanKernel_eq_exp_sum hp hn_inv).symm
      rw [hgu, Complex.conj_ofReal]
      push_cast
      ring
  have heq : (p : ℝ) * ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m ^ 2 =
      ∑ n ∈ Ico 1 p, reciprocityZeroMeanKernel p n ^ 2 :=
    Complex.ofReal_injective (horth.symm.trans hphys)
  rw [heq]
  refine sum_congr rfl fun n hn => ?_
  rw [reciprocityZeroMeanKernel_of_not_dvd (not_dvd_of_mem_Ico hn)]

/-- **Unconditional `Ω(p⁴)` `ℓ²` lower bound on `reciprocityKloostermanCoeff p`.**
For every prime `p ≥ 67`, `∑_{m=1}^{p-1} C_m(p)² ≥ p⁴ / 5120000`, matching the upper bound
`∑_{m=1}^{p-1} C_m(p)² ≤ (π⁴ / 576)(p - 1) p³` in exact `p⁴` order. -/
theorem sum_Ico_reciprocityKloostermanCoeff_sq_ge {p : ℕ} (hp : p.Prime) (hp67 : 67 ≤ p) :
    (p : ℝ) ^ 4 / 5120000 ≤ ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m ^ 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp67R : (67 : ℝ) ≤ p := by exact_mod_cast hp67
  have hpi_sq : Real.pi ^ 2 ≤ 10 := by
    have hlt := Real.pi_lt_d2
    have hpos := Real.pi_pos
    nlinarith
  -- Near-half residue window `W = Icc (31p / 64 + 1) (33p / 64) ⊆ Ico 1 p`
  set a : ℕ := 31 * p / 64 + 1
  set b : ℕ := 33 * p / 64
  have hab_sub : Icc a b ⊆ Ico 1 p := by
    intro n hn
    obtain ⟨hna, hnb⟩ := mem_Icc.mp hn
    exact mem_Ico.mpr ⟨by omega, by omega⟩
  have hterm_ge : ∀ n ∈ Icc a b,
      (p : ℝ) ^ 4 / 40000 ≤
        (bernoulliKernel p n + Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * (p : ℝ))) ^ 2 := by
    intro n hn
    obtain ⟨hna, hnb⟩ := mem_Icc.mp hn
    have hn_lt : n < p := (mem_Ico.mp (hab_sub hn)).2
    have h64_lo : 31 * p ≤ 64 * n := by omega
    have h64_hi : 64 * n ≤ 33 * p := by omega
    have h64_loR : 31 * (p : ℝ) ≤ 64 * (n : ℝ) := by exact_mod_cast h64_lo
    have h64_hiR : 64 * (n : ℝ) ≤ 33 * (p : ℝ) := by exact_mod_cast h64_hi
    have hnear : |((n % p : ℕ) : ℝ) / (p : ℝ) - 1 / 2| ≤ 1 / 64 := by
      rw [Nat.mod_eq_of_lt hn_lt, abs_le]
      constructor
      · rw [le_sub_iff_add_le, le_div_iff₀ hpR]; linarith
      · rw [sub_le_iff_le_add, div_le_iff₀ hpR]; linarith
    have hkern := bernoulliKernel_le_of_near_half hp.pos hnear
    have hmean_le : Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * (p : ℝ)) ≤ (5 / 36) * (p : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      have hsub : (p : ℝ) ^ 2 - 1 ≤ (p : ℝ) ^ 2 := by linarith
      have h0 : 0 ≤ (p : ℝ) ^ 2 - 1 := by nlinarith
      nlinarith
    have hsum_neg :
        bernoulliKernel p n + Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * (p : ℝ)) ≤
          -((p : ℝ) ^ 2 / 200) := by
      nlinarith
    nlinarith
  have hcard_nat : p / 64 ≤ (Icc a b).card := by
    rw [Nat.card_Icc]
    omega
  have hcard_real : (p : ℝ) / 128 ≤ ((Icc a b).card : ℝ) := by
    have hdiv_nat : p ≤ 128 * (p / 64) := by omega
    have hdiv_R : (p : ℝ) ≤ 128 * ((p / 64 : ℕ) : ℝ) := by exact_mod_cast hdiv_nat
    have hcR : ((p / 64 : ℕ) : ℝ) ≤ ((Icc a b).card : ℝ) := by exact_mod_cast hcard_nat
    linarith
  have hsum_ge : (p : ℝ) ^ 5 / 5120000 ≤
      (p : ℝ) * ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m ^ 2 := by
    rw [mul_sum_Ico_reciprocityKloostermanCoeff_sq_eq_sum_kernel_sq hp]
    calc (p : ℝ) ^ 5 / 5120000
        = ((p : ℝ) / 128) * ((p : ℝ) ^ 4 / 40000) := by ring
      _ ≤ ((Icc a b).card : ℝ) * ((p : ℝ) ^ 4 / 40000) :=
          mul_le_mul_of_nonneg_right hcard_real (by positivity)
      _ = ∑ _n ∈ Icc a b, (p : ℝ) ^ 4 / 40000 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ Icc a b,
            (bernoulliKernel p n + Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * (p : ℝ))) ^ 2 :=
          sum_le_sum hterm_ge
      _ ≤ ∑ n ∈ Ico 1 p,
            (bernoulliKernel p n + Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * (p : ℝ))) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hab_sub fun _ _ _ => sq_nonneg _
  have hrew : (p : ℝ) ^ 5 / 5120000 = (p : ℝ) * ((p : ℝ) ^ 4 / 5120000) := by ring
  rw [hrew] at hsum_ge
  exact le_of_mul_le_mul_left hsum_ge hpR

/-- **Unconditional `Ω(p^{3/2})` `ℓ^∞` lower bound on `reciprocityKloostermanCoeff p`.**
For every prime `p ≥ 67`, there exists a frequency `1 ≤ m < p` with
`(1 / 2400) p √p ≤ |C_m(p)|`, proving that the square-root Weil bound
`|C_m(p)| ≤ (π² / 24) p √p` is order-sharp. -/
theorem exists_abs_reciprocityKloostermanCoeff_ge {p : ℕ} (hp : p.Prime) (hp67 : 67 ≤ p) :
    ∃ m ∈ Ico 1 p, (1 / 2400) * (p : ℝ) * Real.sqrt p ≤ |reciprocityKloostermanCoeff p m| := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  by_contra hcontra
  push Not at hcontra
  have hsq_lt : ∀ m ∈ Ico 1 p,
      reciprocityKloostermanCoeff p m ^ 2 ≤ (p : ℝ) ^ 3 / 5760000 := by
    intro m hm
    have hlt := (hcontra m hm).le
    have hpow := pow_le_pow_left₀ (abs_nonneg _) hlt 2
    rw [sq_abs] at hpow
    refine hpow.trans (le_of_eq ?_)
    calc ((1 / 2400) * (p : ℝ) * Real.sqrt p) ^ 2
        = ((p : ℝ) ^ 2 * Real.sqrt p ^ 2) / 5760000 := by ring
      _ = (p : ℝ) ^ 3 / 5760000 := by rw [Real.sq_sqrt hpR.le]; ring
  have hsum_le : ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m ^ 2 ≤ (p : ℝ) ^ 4 / 5760000 := by
    calc ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m ^ 2
        ≤ ∑ _m ∈ Ico 1 p, (p : ℝ) ^ 3 / 5760000 := sum_le_sum hsq_lt
      _ = ((p : ℝ) - 1) * ((p : ℝ) ^ 3 / 5760000) := by
          rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hp.pos, Nat.cast_one]
      _ ≤ (p : ℝ) * ((p : ℝ) ^ 3 / 5760000) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (p : ℝ) ^ 4 / 5760000 := by ring
  have hsum_ge := sum_Ico_reciprocityKloostermanCoeff_sq_ge hp hp67
  have hp4_pos : (0 : ℝ) < (p : ℝ) ^ 4 := by positivity
  linarith

/-! ## §3. Explicit rank-three + pure zero-mean Kloosterman law of the prime pronic Gram -/

/-- **Explicit rank-three + pure zero-mean Kloosterman law for `pmRamanujanEnergyCenteredGram`.**
For any two distinct primes `p ≠ q` with `p, q ≤ N`, extracting the coprime mean of `𝔅(p, q)`
yields a third explicit separable rank-one mode `- (π²(p² - 1)/(72 p)) · (1 / q)` alongside
`D_p log q` and `-p β_p`, isolating the zero-mean Kloosterman sum `W_K(p, q) / q` up to
`(3/4) p³ / q²`. -/
theorem abs_pmRamanujanEnergyCenteredGram_sub_rankThree_kloosterman_le
    {N p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpN : p ≤ N) (hqN : q ≤ N) :
    |pmRamanujanEnergyCenteredGram p q -
        ((((p : ℝ) - 1) / 2 - Real.log p) * Real.log q -
          (p : ℝ) * rowBeta N (unitRow p) -
          (Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * (p : ℝ))) * (1 / (q : ℝ))) -
        reciprocityZeroMeanKernel p q / (q : ℝ)| ≤
      3 / 4 * (p : ℝ) ^ 3 / (q : ℝ) ^ 2 := by
  have hnd : ¬ p ∣ q := fun hdvd => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd)
  have h := abs_pmRamanujanEnergyCenteredGram_sub_second_order_le hp hq hpN hqN
  have hkern : bernoulliKernel p q =
      -(Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * (p : ℝ))) + reciprocityZeroMeanKernel p q := by
    rw [reciprocityZeroMeanKernel_of_not_dvd hnd]
    ring
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  convert h using 2
  rw [hkern]
  field_simp
  ring

/-- Explicit `q̄_p`-indexed Kloosterman form of the rank-three prime pronic Gram law. -/
theorem abs_pmRamanujanEnergyCenteredGram_sub_rankThree_cos_le
    {N p q qbar : ℕ} (hp : p.Prime) (hq : q.Prime) (hpN : p ≤ N) (hqN : q ≤ N)
    (hqbar : q * qbar % p = 1) :
    |pmRamanujanEnergyCenteredGram p q -
        ((((p : ℝ) - 1) / 2 - Real.log p) * Real.log q -
          (p : ℝ) * rowBeta N (unitRow p) -
          (Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * (p : ℝ))) * (1 / (q : ℝ))) -
        (1 / (q : ℝ)) *
          ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m *
            Real.cos (2 * Real.pi * ((m * qbar : ℕ) : ℝ) / p)| ≤
      3 / 4 * (p : ℝ) ^ 3 / (q : ℝ) ^ 2 := by
  have hpq : p ≠ q := by
    intro heq
    subst heq
    have h0 : p * qbar % p = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_right p qbar)
    omega
  have h := abs_pmRamanujanEnergyCenteredGram_sub_rankThree_kloosterman_le hp hq hpq hpN hqN
  have hdiv : (∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m *
      Real.cos (2 * Real.pi * ((m * qbar : ℕ) : ℝ) / p)) / (q : ℝ) =
      (1 / (q : ℝ)) * ∑ m ∈ Ico 1 p, reciprocityKloostermanCoeff p m *
        Real.cos (2 * Real.pi * ((m * qbar : ℕ) : ℝ) / p) := by
    ring
  rw [reciprocityZeroMeanKernel_eq_kloosterman hp hqbar, hdiv] at h
  exact h

/-! ## §4. Two-prime Chinese-remainder orthogonality and terminal-block reduction -/

/-- **Exact CRT orthogonality of `W_K(p₁, n)` and `W_K(p₂, n)` over a product period.**
For any two distinct primes `p₁ ≠ p₂`,
`∑_{n < p₁ p₂} W_K(p₁, n) W_K(p₂, n) = 0`. -/
theorem sum_range_mul_reciprocityZeroMeanKernel_eq_zero
    {p₁ p₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hp₁₂ : p₁ ≠ p₂) :
    ∑ n ∈ range (p₁ * p₂),
      reciprocityZeroMeanKernel p₁ n * reciprocityZeroMeanKernel p₂ n = 0 := by
  have hcop : p₁.Coprime p₂ := (Nat.coprime_primes hp₁ hp₂).mpr hp₁₂
  rw [RHTower.DeletionCoprimeWords.coprime_period_sum_mul hp₁.pos hp₂.pos hcop
    (reciprocityZeroMeanKernel_periodic p₁) (reciprocityZeroMeanKernel_periodic p₂),
    sum_range_reciprocityZeroMeanKernel_eq_zero hp₁, zero_mul]

/-- Any multiple `K * (p₁ * p₂)` of the product period has zero cross-prime correlation. -/
theorem sum_range_mul_period_reciprocityZeroMeanKernel_eq_zero
    {p₁ p₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hp₁₂ : p₁ ≠ p₂) (K : ℕ) :
    ∑ n ∈ range (K * (p₁ * p₂)),
      reciprocityZeroMeanKernel p₁ n * reciprocityZeroMeanKernel p₂ n = 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.succ_mul, sum_range_add, ih, zero_add]
    have hper : ∀ i,
        reciprocityZeroMeanKernel p₁ (K * (p₁ * p₂) + i) *
            reciprocityZeroMeanKernel p₂ (K * (p₁ * p₂) + i) =
          reciprocityZeroMeanKernel p₁ i * reciprocityZeroMeanKernel p₂ i := by
      intro i
      rw [← reciprocityZeroMeanKernel_mod p₁ (K * (p₁ * p₂) + i),
        ← reciprocityZeroMeanKernel_mod p₂ (K * (p₁ * p₂) + i),
        show K * (p₁ * p₂) + i = i + (K * p₂) * p₁ by ring, Nat.add_mul_mod_self_right,
        show i + (K * p₂) * p₁ = i + (K * p₁) * p₂ by ring, Nat.add_mul_mod_self_right,
        reciprocityZeroMeanKernel_mod, reciprocityZeroMeanKernel_mod]
    simp_rw [hper]
    exact sum_range_mul_reciprocityZeroMeanKernel_eq_zero hp₁ hp₂ hp₁₂

/-- **Exact terminal-block collapse of incomplete two-prime correlation.**
For any two distinct primes `p₁ ≠ p₂` and any horizon `M : ℕ`, all complete blocks modulo `p₁ p₂`
cancel identically and `∑_{n < M} W_K(p₁, n) W_K(p₂, n)` equals the initial block of length
`M % (p₁ * p₂) < p₁ * p₂`. -/
theorem sum_range_mul_reciprocityZeroMeanKernel_eq_terminal
    {p₁ p₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hp₁₂ : p₁ ≠ p₂) (M : ℕ) :
    ∑ n ∈ range M,
        reciprocityZeroMeanKernel p₁ n * reciprocityZeroMeanKernel p₂ n =
      ∑ r ∈ range (M % (p₁ * p₂)),
        reciprocityZeroMeanKernel p₁ r * reciprocityZeroMeanKernel p₂ r := by
  set P := p₁ * p₂
  have hdiv : M = (M / P) * P + M % P := by
    rw [mul_comm (M / P) P]
    exact (Nat.div_add_mod M P).symm
  conv_lhs => rw [hdiv]
  rw [sum_range_add, sum_range_mul_period_reciprocityZeroMeanKernel_eq_zero hp₁ hp₂ hp₁₂ (M / P),
    zero_add]
  refine sum_congr rfl fun r _ => ?_
  rw [← reciprocityZeroMeanKernel_mod p₁ ((M / P) * P + r),
    ← reciprocityZeroMeanKernel_mod p₂ ((M / P) * P + r),
    show (M / P) * P + r = r + ((M / P) * p₂) * p₁ by dsimp [P]; ring,
    Nat.add_mul_mod_self_right,
    show r + ((M / P) * p₂) * p₁ = r + ((M / P) * p₁) * p₂ by ring,
    Nat.add_mul_mod_self_right,
    reciprocityZeroMeanKernel_mod, reciprocityZeroMeanKernel_mod]

/-! ## §5. Positive-definite linear cosine spectrum and `√p`-loss-free Wiener algebra bound -/

/-- The normalized linear cosine Fourier coefficient of `bernoulliKernel p` on `ℤ/pℤ`:
`α̃_p(h) = (1 / p) ∑_{n < p} 𝔅(p, n) cos(2π h n / p)`. -/
def bernoulliLinearCoeff (p h : ℕ) : ℝ :=
  (1 / (p : ℝ)) *
    ∑ n ∈ range p, bernoulliKernel p n * Real.cos (2 * Real.pi * ((h * n : ℕ) : ℝ) / p)

/-- The normalized linear cosine Fourier coefficient of `reciprocityZeroMeanKernel p` on `ℤ/pℤ`:
`α_p(h) = (1 / p) ∑_{n < p} W_K(p, n) cos(2π h n / p)`. -/
def reciprocityLinearCoeff (p h : ℕ) : ℝ :=
  (1 / (p : ℝ)) *
    ∑ n ∈ range p,
      reciprocityZeroMeanKernel p n * Real.cos (2 * Real.pi * ((h * n : ℕ) : ℝ) / p)

theorem bernoulliKernel_reflect {d n : ℕ} (hd : 0 < d) (hn : n ∈ Ico 1 d) :
    bernoulliKernel d (d - n) = bernoulliKernel d n := by
  haveI : NeZero d := ⟨hd.ne'⟩
  have hn' := mem_Ico.mp hn
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [bernoulliKernel_eq_finite hd, bernoulliKernel_eq_finite hd]
  congr 1
  refine sum_nbij' (fun k => d - k) (fun k => d - k) ?_ ?_ ?_ ?_ ?_
  · intro k hk; have := mem_Ico.mp hk; exact mem_Ico.mpr ⟨by omega, by omega⟩
  · intro k hk; have := mem_Ico.mp hk; exact mem_Ico.mpr ⟨by omega, by omega⟩
  · intro k hk; have := mem_Ico.mp hk; omega
  · intro k hk; have := mem_Ico.mp hk; omega
  · intro k hk
    have hk' := mem_Ico.mp hk
    have hmod_eq : k * (d - n) % d = (d - k) * n % d := by
      apply eq_of_zmod_natCast_eq (Nat.mod_lt _ hd) (Nat.mod_lt _ hd)
      rw [ZMod.natCast_mod, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_mul,
        Nat.cast_sub hk'.2.le, Nat.cast_sub hn'.2.le, ZMod.natCast_self]
      ring
    have hsin_eq : Real.sin (Real.pi * ((d - k : ℕ) : ℝ) / d) ^ 2 =
        Real.sin (Real.pi * (k : ℝ) / d) ^ 2 := by
      have harg : Real.pi * ((d - k : ℕ) : ℝ) / d = Real.pi - Real.pi * (k : ℝ) / d := by
        rw [Nat.cast_sub hk'.2.le]
        field_simp
      rw [harg, Real.sin_pi_sub]
    rw [hmod_eq, hsin_eq]

theorem reciprocityZeroMeanKernel_reflect {p n : ℕ} (hp : p.Prime) (hn : n ∈ Ico 1 p) :
    reciprocityZeroMeanKernel p (p - n) = reciprocityZeroMeanKernel p n := by
  have hn' := mem_Ico.mp hn
  have hpn_mem : p - n ∈ Ico 1 p := mem_Ico.mpr ⟨by omega, by omega⟩
  rw [reciprocityZeroMeanKernel_of_not_dvd (not_dvd_of_mem_Ico hpn_mem),
    reciprocityZeroMeanKernel_of_not_dvd (not_dvd_of_mem_Ico hn),
    bernoulliKernel_reflect hp.pos hn]

/-- Exact linear exponential Fourier inversion for any `d`-periodic even real arithmetic wave. -/
theorem even_periodic_eq_sum_linear_exp {d : ℕ} (hd : 0 < d) {F : ℕ → ℝ}
    (hper : Function.Periodic F d) (hrefl : ∀ m ∈ Ico 1 d, F (d - m) = F m) (n : ℕ) :
    (F n : ℂ) =
      ∑ h ∈ range d,
        (((1 / (d : ℝ)) *
            ∑ m ∈ range d, F m * Real.cos (2 * Real.pi * ((h * m : ℕ) : ℝ) / d) : ℝ) : ℂ) *
          stdRoot d ^ (h * n) := by
  set c : ℕ → ℝ := fun h =>
    (1 / (d : ℝ)) * ∑ m ∈ range d, F m * Real.cos (2 * Real.pi * ((h * m : ℕ) : ℝ) / d)
  set chat : ℕ → ℂ := fun h =>
    (1 / (d : ℂ)) * ∑ m ∈ range d, (F m : ℂ) * conj (stdRoot d ^ (h * m))
  -- Step 1: Even symmetry of `F` forces `chat h = (c h : ℂ)`
  have hchat_eq : ∀ h : ℕ, (c h : ℂ) = chat h := by
    intro h
    have hconj : conj (chat h) = chat h := by
      dsimp [chat]
      rw [map_mul, map_div₀, map_one, Complex.conj_natCast, map_sum,
        ← sum_range_add_sum_Ico _ hd, sum_range_one]
      have h0 : conj ((F 0 : ℂ) * conj (stdRoot d ^ (h * 0))) =
          (F 0 : ℂ) * conj (stdRoot d ^ (h * 0)) := by
        simp
      have hIco : ∑ m ∈ Ico 1 d, conj ((F m : ℂ) * conj (stdRoot d ^ (h * m))) =
          ∑ m ∈ Ico 1 d, (F m : ℂ) * conj (stdRoot d ^ (h * m)) := by
        refine sum_nbij' (fun m => d - m) (fun m => d - m) ?_ ?_ ?_ ?_ ?_
        · intro m hm; have := mem_Ico.mp hm; exact mem_Ico.mpr ⟨by omega, by omega⟩
        · intro m hm; have := mem_Ico.mp hm; exact mem_Ico.mpr ⟨by omega, by omega⟩
        · intro m hm; have := mem_Ico.mp hm; omega
        · intro m hm; have := mem_Ico.mp hm; omega
        · intro m hm
          have hm' := mem_Ico.mp hm
          rw [map_mul, Complex.conj_ofReal, Complex.conj_conj, hrefl m hm,
            mul_comm h (d - m), stdRoot_pow_sub_mul_eq_conj hd hm'.2.le, mul_comm m h,
            Complex.conj_conj]
      rw [h0, hIco, ← sum_range_one (fun m => (F m : ℂ) * conj (stdRoot d ^ (h * m))),
        sum_range_add_sum_Ico _ hd]
    have hreal : chat h = ((chat h).re : ℂ) := by
      apply Complex.ext
      · simp
      · have him := congrArg Complex.im hconj
        rw [Complex.conj_im] at him
        simp only [Complex.ofReal_im]
        linarith
    rw [hreal]
    congr 1
    dsimp [c, chat]
    have hd1 : (1 / (d : ℂ)) = ((1 / (d : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [hd1, Complex.re_ofReal_mul, Complex.re_sum]
    congr 1
    refine sum_congr rfl fun m _ => ?_
    rw [Complex.re_ofReal_mul, Complex.conj_re, re_stdRoot_pow]
  -- Step 2: Reduce `n` to `r = n % d < d` and invert the DFT on `range d`
  set r := n % d
  have hr_lt : r < d := Nat.mod_lt n hd
  have hF_mod : F n = F r := by
    have hdiv : n = r + (n / d) * d := by
      dsimp [r]
      rw [add_comm, mul_comm (n / d) d]
      exact (Nat.div_add_mod n d).symm
    conv_lhs => rw [hdiv]
    exact hper.nat_mul (n / d) r
  have hroot_mod : ∀ h : ℕ, stdRoot d ^ (h * n) = stdRoot d ^ (h * r) := by
    intro h
    have hdiv : h * n = h * r + (h * (n / d)) * d := by
      have hn_eq : n = d * (n / d) + r := (Nat.div_add_mod n d).symm
      calc h * n = h * (d * (n / d) + r) := by rw [← hn_eq]
        _ = h * r + (h * (n / d)) * d := by ring
    rw [hdiv, pow_add, stdRoot_pow_mul_self _ _ hd, mul_one]
  have hgoal_rew : ∑ h ∈ range d,
      (((1 / (d : ℝ)) *
          ∑ m ∈ range d, F m * Real.cos (2 * Real.pi * ((h * m : ℕ) : ℝ) / d) : ℝ) : ℂ) *
        stdRoot d ^ (h * n) =
      ∑ h ∈ range d, chat h * stdRoot d ^ (h * r) :=
    sum_congr rfl fun h _ => by rw [← hchat_eq h, hroot_mod h]
  rw [hF_mod, hgoal_rew]
  dsimp [chat]
  simp_rw [mul_assoc, ← mul_sum, sum_mul]
  rw [sum_comm]
  have hm_sum : ∀ m ∈ range d,
      ∑ h ∈ range d, (F m : ℂ) * conj (stdRoot d ^ (h * m)) * stdRoot d ^ (h * r) =
        if r = m then (d : ℂ) * (F r : ℂ) else 0 := by
    intro m hm
    have hrew : ∀ h ∈ range d,
        (F m : ℂ) * conj (stdRoot d ^ (h * m)) * stdRoot d ^ (h * r) =
          (F m : ℂ) * (stdRoot d ^ r * conj (stdRoot d ^ m)) ^ h := by
      intro h _
      rw [mul_pow, ← pow_mul, mul_comm r h, ← map_pow, ← pow_mul, mul_comm m h]
      ring
    rw [sum_congr rfl hrew, ← mul_sum, sum_range_stdRoot_mul_conj_pow hd hr_lt (mem_range.mp hm)]
    split_ifs with heq
    · subst heq; ring
    · ring
  rw [sum_congr rfl hm_sum, sum_ite_eq (range d) r, if_pos (mem_range.mpr hr_lt)]
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  field_simp

/-- Exact cosine Fourier inversion for any `d`-periodic even real arithmetic wave. -/
theorem even_periodic_eq_sum_linear_cos {d : ℕ} (hd : 0 < d) {F : ℕ → ℝ}
    (hper : Function.Periodic F d) (hrefl : ∀ m ∈ Ico 1 d, F (d - m) = F m) (n : ℕ) :
    F n =
      ∑ h ∈ range d,
        ((1 / (d : ℝ)) *
          ∑ m ∈ range d, F m * Real.cos (2 * Real.pi * ((h * m : ℕ) : ℝ) / d)) *
          Real.cos (2 * Real.pi * ((h * n : ℕ) : ℝ) / d) := by
  have hexp := congrArg Complex.re (even_periodic_eq_sum_linear_exp hd hper hrefl n)
  rw [Complex.ofReal_re, Complex.re_sum] at hexp
  rw [hexp]
  refine sum_congr rfl fun h _ => ?_
  rw [Complex.re_ofReal_mul, re_stdRoot_pow]

/-- Exact linear exponential Fourier expansion of `W_K(p, n)` for every `n : ℕ` (with `h = 0`
omitted since `α_p(0) = 0`). -/
theorem reciprocityZeroMeanKernel_eq_sum_linear_exp {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (reciprocityZeroMeanKernel p n : ℂ) =
      ∑ h ∈ Ico 1 p, (reciprocityLinearCoeff p h : ℂ) * stdRoot p ^ (h * n) := by
  have h0 : reciprocityLinearCoeff p 0 = 0 := by
    unfold reciprocityLinearCoeff
    simp only [zero_mul, Nat.cast_zero, mul_zero, zero_div, Real.cos_zero, mul_one]
    rw [sum_range_reciprocityZeroMeanKernel_eq_zero hp, mul_zero]
  have hall := even_periodic_eq_sum_linear_exp hp.pos
    (reciprocityZeroMeanKernel_periodic p)
    (fun m hm => reciprocityZeroMeanKernel_reflect hp hm) n
  change (reciprocityZeroMeanKernel p n : ℂ) =
      ∑ h ∈ range p, (reciprocityLinearCoeff p h : ℂ) * stdRoot p ^ (h * n) at hall
  rw [hall, ← sum_range_add_sum_Ico _ hp.pos, sum_range_one, h0, Complex.ofReal_zero,
    zero_mul, zero_add]

/-- Every linear cosine Fourier coefficient of `residuePotential d (J * ·)` is nonnegative. -/
theorem sum_range_residuePotential_mul_cos_nonneg {d : ℕ} (hd : 0 < d) (J h : ℕ) :
    0 ≤ ∑ n ∈ range d, residuePotential d (J * n) *
      Real.cos (2 * Real.pi * ((h * n : ℕ) : ℝ) / d) := by
  have hω : IsPrimitiveRoot (stdRoot d) d := Complex.isPrimitiveRoot_exp d hd.ne'
  have hinj : Set.InjOn (fun a => stdRoot d ^ a) (Ico 1 d : Set ℕ) := fun i hi j hj heq =>
    hω.pow_inj (mem_Ico.mp hi).2 (mem_Ico.mp hj).2 heq
  have hspec : ∀ n : ℕ, (residuePotential d (J * n) : ℂ) =
      ∑ a ∈ Ico 1 d,
        (((1 / (4 * Real.sin (Real.pi * (a : ℝ) / d) ^ 2)) : ℝ) : ℂ) *
          stdRoot d ^ (a * (J * n)) := by
    intro n
    rw [residuePotential_eq_spectral hd (J * n), nontrivialRoots_eq_image hd, sum_image hinj]
    refine sum_congr rfl fun a _ => ?_
    rw [norm_stdRoot_pow_sub_one_sq, ← one_div, ← pow_mul]
  have hre_eq : ∑ n ∈ range d, residuePotential d (J * n) *
        Real.cos (2 * Real.pi * ((h * n : ℕ) : ℝ) / d) =
      (∑ n ∈ range d, (residuePotential d (J * n) : ℂ) * conj (stdRoot d ^ (h * n))).re := by
    rw [Complex.re_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [Complex.re_ofReal_mul, Complex.conj_re, re_stdRoot_pow]
  rw [hre_eq]
  simp_rw [hspec, sum_mul]
  rw [sum_comm, Complex.re_sum]
  refine sum_nonneg fun a _ => ?_
  have ha_sum : ∑ n ∈ range d,
        (((1 / (4 * Real.sin (Real.pi * (a : ℝ) / d) ^ 2)) : ℝ) : ℂ) *
          stdRoot d ^ (a * (J * n)) * conj (stdRoot d ^ (h * n)) =
      (((1 / (4 * Real.sin (Real.pi * (a : ℝ) / d) ^ 2)) : ℝ) : ℂ) *
        ∑ n ∈ range d, (stdRoot d ^ ((a * J) % d) * conj (stdRoot d ^ (h % d))) ^ n := by
    rw [mul_sum]
    refine sum_congr rfl fun n _ => ?_
    have hp1 : stdRoot d ^ (a * (J * n)) = (stdRoot d ^ ((a * J) % d)) ^ n := by
      rw [← mul_assoc a J n]
      have hdiv : a * J * n = ((a * J) % d) * n + (((a * J) / d) * n) * d := by
        have hAJ : a * J = d * ((a * J) / d) + (a * J) % d := (Nat.div_add_mod (a * J) d).symm
        calc a * J * n = (d * ((a * J) / d) + (a * J) % d) * n := by rw [← hAJ]
          _ = ((a * J) % d) * n + (((a * J) / d) * n) * d := by ring
      rw [hdiv, pow_add, stdRoot_pow_mul_self _ _ hd, mul_one, pow_mul]
    have hp2 : stdRoot d ^ (h * n) = (stdRoot d ^ (h % d)) ^ n := by
      have hdiv : h * n = (h % d) * n + ((h / d) * n) * d := by
        have hh : h = d * (h / d) + h % d := (Nat.div_add_mod h d).symm
        calc h * n = (d * (h / d) + h % d) * n := by rw [← hh]
          _ = (h % d) * n + ((h / d) * n) * d := by ring
      rw [hdiv, pow_add, stdRoot_pow_mul_self _ _ hd, mul_one, pow_mul]
    rw [hp1, hp2, mul_pow, ← map_pow, mul_assoc]
  rw [ha_sum, sum_range_stdRoot_mul_conj_pow hd (Nat.mod_lt _ hd) (Nat.mod_lt _ hd),
    Complex.re_ofReal_mul]
  refine mul_nonneg (by positivity) ?_
  split_ifs
  · exact_mod_cast hd.le
  · simp

/-- **Bochner positivity of the linear cosine spectrum of `bernoulliKernel p`.**
For every `p ≥ 1` and every `h : ℕ`, `0 ≤ bernoulliLinearCoeff p h`. -/
theorem bernoulliLinearCoeff_nonneg {p : ℕ} (hp : 0 < p) (h : ℕ) :
    0 ≤ bernoulliLinearCoeff p h := by
  unfold bernoulliLinearCoeff
  refine mul_nonneg (by positivity) ?_
  have hterm : ∀ n ∈ range p, HasSum
      (fun j : ℕ => residuePotential p ((j + 1) * n) / ((j : ℝ) + 1) ^ 2 *
        Real.cos (2 * Real.pi * ((h * n : ℕ) : ℝ) / p))
      (bernoulliKernel p n * Real.cos (2 * Real.pi * ((h * n : ℕ) : ℝ) / p)) :=
    fun n _ => (hasSum_bernoulliKernel hp n).mul_right _
  have hsum := hasSum_sum hterm
  rw [← hsum.tsum_eq]
  refine tsum_nonneg fun j => ?_
  have hj_eq : ∑ n ∈ range p,
        residuePotential p ((j + 1) * n) / ((j : ℝ) + 1) ^ 2 *
          Real.cos (2 * Real.pi * ((h * n : ℕ) : ℝ) / p) =
      (1 / ((j : ℝ) + 1) ^ 2) *
        ∑ n ∈ range p, residuePotential p ((j + 1) * n) *
          Real.cos (2 * Real.pi * ((h * n : ℕ) : ℝ) / p) := by
    rw [mul_sum]
    refine sum_congr rfl fun n _ => ?_
    ring
  rw [hj_eq]
  exact mul_nonneg (by positivity) (sum_range_residuePotential_mul_cos_nonneg hp (j + 1) h)

theorem bernoulliLinearCoeff_zero_freq {p : ℕ} (hp : p.Prime) :
    bernoulliLinearCoeff p 0 = Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * (p : ℝ) ^ 2) := by
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  unfold bernoulliLinearCoeff
  simp only [zero_mul, Nat.cast_zero, mul_zero, zero_div, Real.cos_zero, mul_one]
  rw [← sum_range_add_sum_Ico _ hp.one_le, sum_range_one, bernoulliKernel_zero hp.pos]
  have hIco : ∑ n ∈ Ico 1 p, bernoulliKernel p n =
      -(((p : ℝ) - 1) * (Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * (p : ℝ)))) := by
    have hz := sum_Ico_reciprocityZeroMeanKernel_eq_zero hp
    have hrew : ∀ n ∈ Ico 1 p,
        reciprocityZeroMeanKernel p n =
          bernoulliKernel p n + Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * (p : ℝ)) :=
      fun n hn => reciprocityZeroMeanKernel_of_not_dvd (not_dvd_of_mem_Ico hn)
    rw [sum_congr rfl hrew, sum_add_distrib, sum_const, Nat.card_Ico, nsmul_eq_mul,
      Nat.cast_sub hp.pos, Nat.cast_one] at hz
    linarith
  rw [hIco]
  field_simp
  ring

/-- **Exact `ℓ¹` sum of the nonzero linear cosine modes of `bernoulliKernel p`.**
By Bochner positivity and evaluation at `n = 0`,
`∑_{h=1}^{p-1} |α̃_p(h)| = ∑_{h=1}^{p-1} α̃_p(h) = π² (p² - 1)² / (72 p²)`. -/
theorem sum_Ico_bernoulliLinearCoeff_eq {p : ℕ} (hp : p.Prime) :
    ∑ h ∈ Ico 1 p, bernoulliLinearCoeff p h =
      Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (72 * (p : ℝ) ^ 2) := by
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hinv := even_periodic_eq_sum_linear_cos hp.pos
    (bernoulliKernel_periodic hp.pos)
    (fun m hm => bernoulliKernel_reflect hp.pos hm) 0
  change bernoulliKernel p 0 =
      ∑ h ∈ range p, bernoulliLinearCoeff p h *
        Real.cos (2 * Real.pi * ((h * 0 : ℕ) : ℝ) / p) at hinv
  simp only [mul_zero, Nat.cast_zero, zero_div, Real.cos_zero, mul_one] at hinv
  rw [← sum_range_add_sum_Ico _ hp.one_le, sum_range_one, bernoulliLinearCoeff_zero_freq hp,
    bernoulliKernel_zero hp.pos] at hinv
  have hgoal : ∑ h ∈ Ico 1 p, bernoulliLinearCoeff p h =
      Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / 72 -
        Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * (p : ℝ) ^ 2) := by
    linarith
  rw [hgoal]
  field_simp

theorem reciprocityLinearCoeff_eq_sub {p h : ℕ} (hp : p.Prime) (hh : h ∈ Ico 1 p) :
    reciprocityLinearCoeff p h =
      bernoulliLinearCoeff p h -
        Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) * ((p : ℝ) + 1) / (72 * (p : ℝ) ^ 2) := by
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  unfold reciprocityLinearCoeff bernoulliLinearCoeff
  rw [← sum_range_add_sum_Ico _ hp.pos, ← sum_range_add_sum_Ico _ hp.pos,
    sum_range_one, sum_range_one, reciprocityZeroMeanKernel_zero, zero_mul, zero_add,
    bernoulliKernel_zero hp.pos]
  simp only [mul_zero, Nat.cast_zero, zero_div, Real.cos_zero, mul_one]
  have hIco : ∑ n ∈ Ico 1 p,
        reciprocityZeroMeanKernel p n * Real.cos (2 * Real.pi * ((h * n : ℕ) : ℝ) / p) =
      (∑ n ∈ Ico 1 p,
        bernoulliKernel p n * Real.cos (2 * Real.pi * ((h * n : ℕ) : ℝ) / p)) -
        Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * (p : ℝ)) := by
    have hterm : ∀ n ∈ Ico 1 p,
        reciprocityZeroMeanKernel p n * Real.cos (2 * Real.pi * ((h * n : ℕ) : ℝ) / p) =
          bernoulliKernel p n * Real.cos (2 * Real.pi * ((h * n : ℕ) : ℝ) / p) +
            (Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * (p : ℝ))) *
              Real.cos (2 * Real.pi * ((n * h : ℕ) : ℝ) / p) := by
      intro n hn
      rw [reciprocityZeroMeanKernel_of_not_dvd (not_dvd_of_mem_Ico hn), mul_comm n h]
      ring
    rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum,
      sum_Ico_cos_two_pi_of_not_dvd hp (not_dvd_of_mem_Ico hh)]
    ring
  rw [hIco]
  field_simp
  ring

/-- **`√p`-loss-free Wiener algebra bound on `reciprocityZeroMeanKernel p`.**
For every prime `p`, the linear Fourier `ℓ¹` norm satisfies
`∑_{h=1}^{p-1} |α_p(h)| ≤ π² (p² - 1)² / (36 p²) ≤ (π² / 36) p²`. -/
theorem sum_Ico_abs_reciprocityLinearCoeff_le {p : ℕ} (hp : p.Prime) :
    ∑ h ∈ Ico 1 p, |reciprocityLinearCoeff p h| ≤
      Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (36 * (p : ℝ) ^ 2) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  set B : ℝ := Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) * ((p : ℝ) + 1) / (72 * (p : ℝ) ^ 2)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    have hsub : 0 ≤ (p : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  have hterm : ∀ h ∈ Ico 1 p, |reciprocityLinearCoeff p h| ≤ bernoulliLinearCoeff p h + B := by
    intro h hh
    rw [reciprocityLinearCoeff_eq_sub hp hh]
    have ha := bernoulliLinearCoeff_nonneg hp.pos h
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg ha, abs_of_nonneg hB_nonneg])
  calc ∑ h ∈ Ico 1 p, |reciprocityLinearCoeff p h|
      ≤ ∑ h ∈ Ico 1 p, (bernoulliLinearCoeff p h + B) := sum_le_sum hterm
    _ = (∑ h ∈ Ico 1 p, bernoulliLinearCoeff p h) + ((p : ℝ) - 1) * B := by
        rw [sum_add_distrib, sum_const, Nat.card_Ico, nsmul_eq_mul,
          Nat.cast_sub hp.pos, Nat.cast_one]
    _ = Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) ^ 2 / (36 * (p : ℝ) ^ 2) := by
        rw [sum_Ico_bernoulliLinearCoeff_eq hp]
        dsimp [B]
        field_simp
        ring

end

end GaloisForLFunctions.BezoutValuationIncidence
