import GaloisForLFunctions.BezoutValuationIncidence.ExactRankTwoCrossScaleLawOfTheReceiverGram
import GaloisForLFunctions.BezoutValuationIncidence.LogFreeLargeSieveFromWindowSandwich

/-!
# Large-sieve dispersion of the cross-scale remainder

The rank-two law `ExactRankTwoCrossScaleLawOfTheReceiverGram` writes the receiver's bilinear form
of a small-scale row `c` and a large-scale row `c'` as

`B(c, c') + m(c) R(c') + β(c) H(c') = lim_H Σ_n c'(n) Σ_{j ≥ 1} Σ_{jn ≤ M < H} F_c(M)/(M(M+1))`.

For a row `c` supported on primes the fluctuation is an exponential sum over the primitive `p`-th
roots, `F_c(M) = Σ_p (c(p)/p) Σ_ζ ζ/(ζ - 1) ζ^M`. Summation by parts against the pronic weight gives
`Σ_{A ≤ M} w(M) ζ^M = w(A) ζ^A/(1 - ζ) + O(w(A)/(A |1 - ζ|²))`, so the remainder is, up to an
error `O(Σ_p |c(p)| p² · Σ_n |c'(n)|/n³)`, the dilated bilinear form

`Σ_j Σ_ζ α(ζ) Σ_n c'(n) w(jn) (ζ^j)^n`,  `α(ζ) = (c(p)/p) ζ/((ζ - 1)(1 - ζ))`.

This is an exponential sum in the large-scale variable `n` at the frequencies `ζ^j`, roots of unity
of order at most `Q₀ = max supp c`: the residue classes of `n` modulo the small primes. Each `ζ^j`
has at most `j` preimages, and the log-free large sieve over a window of length `L` containing the
support of `c'` gives

`|B(c, c') + m(c) R(c') + β(c) H(c')| ≤ ½ √(Σ_p |c(p)|² p²) √(L + 2Q₀² - 1) √(Σ_n |c'(n)|²/n⁴)
  + ½ Σ_p |c(p)| p² · Σ_n |c'(n)|/n³`,

using `Σ_ζ |1 - ζ|^{-4} ≤ p⁴/64` for the primitive `p`-th roots (Farey separation). For `c` on primes
in `(P, 2P]` and `c'` on `(Q, 2Q]` with `P ≤ Q ≤ P²`, the ratio of this bound to the diagonal
`√(D(c) D(c'))` is `P^{5/2}/Q^{3/2}`: the cross-scale Gram is rank two at diagonal quality as soon
as `Q ≥ P^{5/3}`, improving the elementary threshold `Q ≥ P²`. The input is the additive large
sieve over the small primes acting on the residues of the large moduli, with no character or
modulus average beyond the bilinear sum itself.
-/

open Finset Complex Filter Topology RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Abel summation against geometric sums -/

/-- Complex Abel summation: partial sums bounded by `B` and a nonnegative decreasing real weight. -/
theorem norm_sum_range_real_mul_le {z : ℕ → ℂ} {h : ℕ → ℝ} {K : ℕ} {B : ℝ}
    (hh : ∀ i < K, h (i + 1) ≤ h i) (hh0 : ∀ i ≤ K, 0 ≤ h i)
    (hz : ∀ m ≤ K, ‖∑ i ∈ range m, z i‖ ≤ B) :
    ‖∑ i ∈ range K, (h i : ℂ) * z i‖ ≤ B * h 0 := by
  -- `T k = Σ_{i<k} h_i z_i - h_k S_k` moves by `S_{k+1} (h_k - h_{k+1})`
  have hT : ∀ k ≤ K, ‖∑ i ∈ range k, (h i : ℂ) * z i - (h k : ℂ) * ∑ i ∈ range k, z i‖ ≤
      B * (h 0 - h k) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hstep : ∑ i ∈ range (k + 1), (h i : ℂ) * z i - (h (k + 1) : ℂ) * ∑ i ∈ range (k + 1), z i =
          (∑ i ∈ range k, (h i : ℂ) * z i - (h k : ℂ) * ∑ i ∈ range k, z i) +
            ((h k - h (k + 1) : ℝ) : ℂ) * ∑ i ∈ range (k + 1), z i := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        push_cast
        ring
      rw [hstep]
      have hd : 0 ≤ h k - h (k + 1) := sub_nonneg.mpr (hh k (by omega))
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ B * (h 0 - h k) + (h k - h (k + 1)) * B := by
          refine add_le_add (ih (by omega)) ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
          exact mul_le_mul_of_nonneg_left (hz _ hk) hd
        _ = B * (h 0 - h (k + 1)) := by ring
  have hK := hT K le_rfl
  have hlast : ‖(h K : ℂ) * ∑ i ∈ range K, z i‖ ≤ B * h K := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hh0 K le_rfl), mul_comm]
    exact mul_le_mul_of_nonneg_right (hz K le_rfl) (hh0 K le_rfl)
  calc ‖∑ i ∈ range K, (h i : ℂ) * z i‖
      = ‖(∑ i ∈ range K, (h i : ℂ) * z i - (h K : ℂ) * ∑ i ∈ range K, z i) +
          (h K : ℂ) * ∑ i ∈ range K, z i‖ := by ring_nf
    _ ≤ B * (h 0 - h K) + B * h K := (norm_add_le _ _).trans (add_le_add hK hlast)
    _ = B * h 0 := by ring

/-- The pronic weight as a real function. -/
def pw (M : ℕ) : ℝ := 1 / ((M : ℝ) * ((M : ℝ) + 1))

theorem pw_nonneg (M : ℕ) : 0 ≤ pw M := by unfold pw; positivity

theorem pw_sub_pw_succ {M : ℕ} (hM : 1 ≤ M) :
    pw M - pw (M + 1) = 2 / ((M : ℝ) * ((M : ℝ) + 1) * ((M : ℝ) + 2)) := by
  have : (0 : ℝ) < M := by exact_mod_cast hM
  unfold pw; push_cast; field_simp; ring

/-- **Summation by parts of a character against the pronic weight.** For `|ζ| = 1`, `ζ ≠ 1` and
`1 ≤ A < H`: `‖Σ_{A ≤ M < H} w(M) ζ^M - w(A) ζ^A/(1 - ζ)‖ ≤ (w(H-1) + 2(w(A) - w(A+1))/‖ζ-1‖)/‖ζ-1‖`. -/
theorem norm_sum_Ico_pw_mul_pow_sub_le {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hζ1 : ζ ≠ 1) {A H : ℕ}
    (hA : 1 ≤ A) (hAH : A < H) :
    ‖∑ M ∈ Ico A H, (pw M : ℂ) * ζ ^ M - (pw A : ℂ) * ζ ^ A / (1 - ζ)‖ ≤
      (pw (H - 1) + 2 * (pw A - pw (A + 1)) / ‖ζ - 1‖) / ‖ζ - 1‖ := by
  have hsub : (1 : ℂ) - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hζ1)
  have hnorm : ‖ζ - 1‖ = ‖1 - ζ‖ := norm_sub_rev _ _
  have hpos : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hζ1)
  -- summation by parts: `(1-ζ) Σ g ζ^M = g(A) ζ^A - g(H-1) ζ^H + Σ_{A<M<H} (g(M) - g(M-1)) ζ^M`
  have hsbp : ∀ H', A < H' → (1 - ζ) * ∑ M ∈ Ico A H', (pw M : ℂ) * ζ ^ M =
      (pw A : ℂ) * ζ ^ A - (pw (H' - 1) : ℂ) * ζ ^ H' +
        ∑ M ∈ Ico (A + 1) H', ((pw M - pw (M - 1) : ℝ) : ℂ) * ζ ^ M := by
    intro H' hH'
    induction H', hH' using Nat.le_induction with
    | base => simp; ring
    | succ H' hH' ih =>
      rw [sum_Ico_succ_top (by omega), mul_add, ih, sum_Ico_succ_top (by omega),
        show H' + 1 - 1 = H' by omega]
      push_cast
      ring
  -- the second-order sum: Abel against the decreasing weights `w(M-1) - w(M)`
  have hsecond : ‖∑ M ∈ Ico (A + 1) H, ((pw M - pw (M - 1) : ℝ) : ℂ) * ζ ^ M‖ ≤
      2 / ‖ζ - 1‖ * (pw A - pw (A + 1)) := by
    rw [sum_Ico_eq_sum_range]
    have := norm_sum_range_real_mul_le (z := fun i => ζ ^ (A + 1 + i))
      (h := fun i => pw (A + i) - pw (A + i + 1)) (K := H - (A + 1)) (B := 2 / ‖ζ - 1‖)
      (fun i _ => by
        rw [pw_sub_pw_succ (by omega), pw_sub_pw_succ (by omega)]
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        push_cast
        have : (1 : ℝ) ≤ (A : ℝ) + i := by
          have : (1 : ℝ) ≤ A := by exact_mod_cast hA
          linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
        apply mul_le_mul (mul_le_mul _ _ _ _) _ _ _ <;> nlinarith)
      (fun i _ => by
        rw [pw_sub_pw_succ (by omega)]; positivity)
      (fun m _ => by
        rw [show ∑ i ∈ range m, ζ ^ (A + 1 + i) = ∑ n ∈ Ico (A + 1) (A + 1 + m), ζ ^ n by
          rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]]
        exact norm_geom_sum_Ico_le hζ.le hζ1 _ _)
    calc ‖∑ k ∈ range (H - (A + 1)), ((pw (A + 1 + k) - pw (A + 1 + k - 1) : ℝ) : ℂ) *
          ζ ^ (A + 1 + k)‖
        = ‖∑ i ∈ range (H - (A + 1)), ((-(pw (A + i) - pw (A + i + 1)) : ℝ) : ℂ) *
            ζ ^ (A + 1 + i)‖ := by
          congr 1
          refine sum_congr rfl fun k _ => ?_
          rw [show A + 1 + k - 1 = A + k by omega, show A + 1 + k = A + k + 1 by omega]
          push_cast; ring
      _ = ‖∑ i ∈ range (H - (A + 1)), ((pw (A + i) - pw (A + i + 1) : ℝ) : ℂ) *
            ζ ^ (A + 1 + i)‖ := by
          rw [← norm_neg, ← sum_neg_distrib]
          congr 1
          exact sum_congr rfl fun _ _ => by push_cast; ring
      _ ≤ 2 / ‖ζ - 1‖ * (pw (A + 0) - pw (A + 0 + 1)) := this
      _ = 2 / ‖ζ - 1‖ * (pw A - pw (A + 1)) := by simp
  -- assemble
  have hid : ∑ M ∈ Ico A H, (pw M : ℂ) * ζ ^ M - (pw A : ℂ) * ζ ^ A / (1 - ζ) =
      (-(pw (H - 1) : ℂ) * ζ ^ H +
        ∑ M ∈ Ico (A + 1) H, ((pw M - pw (M - 1) : ℝ) : ℂ) * ζ ^ M) / (1 - ζ) := by
    rw [eq_div_iff hsub, sub_mul, div_mul_cancel₀ _ hsub, mul_comm, hsbp H hAH]
    ring
  rw [hid, norm_div, ← hnorm, div_le_div_iff_of_pos_right hpos]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pw_nonneg _),
      norm_pow, hζ, one_pow, mul_one]
  · refine hsecond.trans (le_of_eq ?_)
    ring

/-! ## §2. The fluctuation of a prime row is an exponential sum -/

theorem neg_centeredResidue_prime {p : ℕ} (hp : p.Prime) (M : ℕ) :
    -centeredResidue p M = pmRamanujanMeanCenteredPrimitive p M := by
  rw [pmRamanujanMeanCenteredPrimitive, pmRamanujanPrimitive_prime hp, Nat.totient_prime hp,
    centeredResidue]
  simp only [Complex.neg_re, Complex.natCast_re]
  rw [Nat.cast_sub hp.one_le]
  push_cast
  ring

/-- For a row supported on primes, `F_c(M) = Σ_p (c(p)/p) Σ_{ζ prim p} ζ/(ζ - 1) ζ^M`. -/
theorem rowFluct_eq_spectral {N : ℕ} {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N) {c : ℕ → ℝ}
    (hsupp : ∀ n, c n ≠ 0 → n ∈ S) (M : ℕ) :
    (rowFluct N c M : ℂ) =
      ∑ p ∈ S, ∑ ζ ∈ primitiveRoots p ℂ, ((c p / p : ℝ) : ℂ) * (ζ / (ζ - 1)) * ζ ^ M := by
  have hsub : S ⊆ Icc 1 N := fun p hp => mem_Icc.mpr ⟨(hS p hp).1.one_lt.le, (hS p hp).2⟩
  rw [rowFluct, ← sum_subset hsub fun n _ hn => by
    have : c n = 0 := by by_contra h; exact hn (hsupp n h)
    rw [this, zero_div, zero_mul]]
  push_cast
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun p hp => ?_
  have h := pmRamanujanMeanCenteredPrimitive_eq_spectral (hS p hp).1.two_le M
  rw [← neg_centeredResidue_prime (hS p hp).1] at h
  push_cast at h
  calc -((c p : ℂ) / p * (centeredResidue p M : ℂ)) = (c p : ℂ) / p * -(centeredResidue p M : ℂ) := by
        ring
    _ = (c p : ℂ) / p * ∑ ζ ∈ primitiveRoots p ℂ, ζ / (ζ - 1) * ζ ^ M := by rw [h]
    _ = _ := by rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring

/-! ## §3. Farey separation of the primitive `p`-th roots -/

theorem circleFreq_zero : circleFreq 0 = 1 := by simp [circleFreq]

theorem rootAngle_one : rootAngle 1 = 0 := by simp [rootAngle]

/-- A nontrivial `p`-th root of unity is at chordal distance `≥ 4 toIntDist` from `1`. -/
theorem four_mul_toIntDist_rootAngle_le {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    4 * toIntDist (rootAngle ζ) ≤ ‖ζ - 1‖ := by
  have h := four_mul_toIntDist_le_norm_sub 0 (rootAngle ζ)
  rwa [sub_zero, circleFreq_zero, map_one, one_mul, circleFreq_rootAngle hζ] at h

theorem one_div_le_toIntDist_rootAngle_of_pow {ζ : ℂ} {p : ℕ} (hp : 0 < p) (hζ : ‖ζ‖ = 1)
    (hpow : ζ ^ p = 1) (hne : ζ ≠ 1) : 1 / (p : ℝ) ≤ toIntDist (rootAngle ζ) :=
  one_div_le_toIntDist_of_circleFreq_pow hp (by rwa [circleFreq_rootAngle hζ])
    (by rwa [circleFreq_rootAngle hζ])

theorem four_div_le_norm_sub_one {p : ℕ} (hp : 2 ≤ p) {ζ : ℂ} (hζ : ζ ∈ primitiveRoots p ℂ) :
    4 / (p : ℝ) ≤ ‖ζ - 1‖ := by
  have hprim := (mem_primitiveRoots (by omega)).mp hζ
  have hnorm := hprim.norm'_eq_one (by omega)
  have h1 := one_div_le_toIntDist_rootAngle_of_pow (by omega) hnorm hprim.pow_eq_one
    (hprim.ne_one (by omega))
  have h2 := four_mul_toIntDist_rootAngle_le hnorm
  calc 4 / (p : ℝ) = 4 * (1 / p) := by ring
    _ ≤ 4 * toIntDist (rootAngle ζ) := by linarith
    _ ≤ _ := h2

/-- Squared reciprocal distances: `Σ_{ζ prim p} 1/‖ζ - 1‖² ≤ p²/4`. -/
theorem sum_primitiveRoots_inv_norm_sub_one_sq_le {p : ℕ} (hp : 2 ≤ p) :
    ∑ ζ ∈ primitiveRoots p ℂ, 1 / ‖ζ - 1‖ ^ 2 ≤ (p : ℝ) ^ 2 / 4 := by
  have hp0 : 0 < p := by omega
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  set s := Polynomial.nthRootsFinset p (1 : ℂ)
  have hmem : ∀ ζ ∈ s, ζ ^ p = 1 := fun ζ hζ => (Polynomial.mem_nthRootsFinset hp0 1).mp hζ
  have hnorm : ∀ ζ ∈ s, ‖ζ‖ = 1 := fun ζ hζ =>
    norm_eq_one_of_pow_eq_one (hmem ζ hζ) (by omega)
  have hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → 1 / (p : ℝ) ≤ toIntDist (rootAngle b - rootAngle a) := by
    intro a ha b hb hab
    have hcf : circleFreq (rootAngle b - rootAngle a) = conj a * b := by
      rw [← conj_circleFreq_mul, circleFreq_rootAngle (hnorm a ha),
        circleFreq_rootAngle (hnorm b hb)]
    refine one_div_le_toIntDist_of_circleFreq_pow hp0 ?_ ?_
    · rw [hcf, mul_pow, ← map_pow, hmem a ha, hmem b hb, map_one, one_mul]
    · rw [hcf]
      intro h
      apply hab
      calc a = a * (conj a * b) := by rw [h, mul_one]
        _ = (conj a * a) * b := by ring
        _ = b := by rw [conj_mul_self_of_norm_eq_one (hnorm a ha), one_mul]
  have h1s : (1 : ℂ) ∈ s := (Polynomial.mem_nthRootsFinset hp0 1).mpr (one_pow p)
  have hsum := sum_erase_one_div_toIntDist_sq_le s rootAngle (by positivity)
    (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith) hsep h1s
  rw [rootAngle_one] at hsum
  simp only [sub_zero] at hsum
  have hsubset : primitiveRoots p ℂ ⊆ s.erase 1 := fun ζ hζ => by
    have hprim := (mem_primitiveRoots hp0).mp hζ
    exact mem_erase.mpr ⟨hprim.ne_one (by omega),
      (Polynomial.mem_nthRootsFinset hp0 1).mpr hprim.pow_eq_one⟩
  have hdist : ∀ ζ ∈ s.erase 1, 0 < toIntDist (rootAngle ζ) := fun ζ hζ => by
    have h := one_div_le_toIntDist_rootAngle_of_pow hp0 (hnorm ζ (mem_of_mem_erase hζ))
      (hmem ζ (mem_of_mem_erase hζ)) (ne_of_mem_erase hζ)
    exact lt_of_lt_of_le (by positivity) h
  calc ∑ ζ ∈ primitiveRoots p ℂ, 1 / ‖ζ - 1‖ ^ 2
      ≤ ∑ ζ ∈ primitiveRoots p ℂ, 1 / 16 * (1 / toIntDist (rootAngle ζ) ^ 2) := by
        refine sum_le_sum fun ζ hζ => ?_
        have hd := hdist ζ (hsubset hζ)
        have h4 := four_mul_toIntDist_rootAngle_le (hnorm ζ (mem_of_mem_erase (hsubset hζ)))
        rw [one_div_mul_one_div, div_le_div_iff₀ (by nlinarith) (by positivity)]
        nlinarith
    _ ≤ ∑ ζ ∈ s.erase 1, 1 / 16 * (1 / toIntDist (rootAngle ζ) ^ 2) :=
        sum_le_sum_of_subset_of_nonneg hsubset fun ζ _ _ => by positivity
    _ = 1 / 16 * ∑ ζ ∈ s.erase 1, 1 / toIntDist (rootAngle ζ) ^ 2 := by rw [mul_sum]
    _ ≤ 1 / 16 * (4 / (1 / (p : ℝ)) ^ 2) := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (p : ℝ) ^ 2 / 4 := by field_simp; ring

/-- `Σ_{ζ prim p} 1/‖ζ - 1‖^k ≤ (p/4)^{k-2} p²/4` for `k = 3, 4`. -/
theorem sum_primitiveRoots_inv_norm_sub_one_pow_le {p : ℕ} (hp : 2 ≤ p) (k : ℕ) :
    ∑ ζ ∈ primitiveRoots p ℂ, 1 / ‖ζ - 1‖ ^ (k + 2) ≤ ((p : ℝ) / 4) ^ k * ((p : ℝ) ^ 2 / 4) := by
  refine le_trans (sum_le_sum fun ζ hζ => ?_) (by
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_primitiveRoots_inv_norm_sub_one_sq_le hp)
      (by positivity))
  have h := four_div_le_norm_sub_one hp hζ
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hn : 0 < ‖ζ - 1‖ := lt_of_lt_of_le (by positivity) h
  have hrw : 1 / ‖ζ - 1‖ ^ (k + 2) = (1 / ‖ζ - 1‖) ^ k * (1 / ‖ζ - 1‖ ^ 2) := by
    rw [pow_add, one_div_pow]; field_simp
  rw [hrw]
  have h' : 1 / ‖ζ - 1‖ ≤ (p : ℝ) / 4 := by
    calc 1 / ‖ζ - 1‖ ≤ 1 / (4 / (p : ℝ)) := one_div_le_one_div_of_le (by positivity) h
      _ = (p : ℝ) / 4 := by field_simp
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h' k) (by positivity)

/-! ## §4. The large sieve at dilated frequencies -/

/-- The frequencies `ζ^j` have at most `j` preimages, so the log-free large sieve costs a factor `j`. -/
theorem sum_norm_sq_dilated_le {T : Finset ℂ} {Q₀ : ℕ} (hQ₀ : 2 ≤ Q₀) (hT : T ⊆ responseRoots Q₀)
    {j : ℕ} (hj : 0 < j) (A L : ℕ) (y : ℕ → ℂ) :
    ∑ ζ ∈ T, ‖∑ k ∈ Icc (A + 1) (A + L), y k * (ζ ^ j) ^ k‖ ^ 2 ≤
      j * (((L : ℝ) + 2 * (Q₀ : ℝ) ^ 2 - 1) * ∑ k ∈ Icc (A + 1) (A + L), ‖y k‖ ^ 2) := by
  classical
  set f : ℂ → ℝ := fun ξ => ‖∑ k ∈ Icc (A + 1) (A + L), y k * ξ ^ k‖ ^ 2
  rw [show (∑ ζ ∈ T, ‖∑ k ∈ Icc (A + 1) (A + L), y k * (ζ ^ j) ^ k‖ ^ 2) =
    ∑ ζ ∈ T, f (ζ ^ j) from rfl, sum_comp]
  have himg : T.image (· ^ j) ⊆ responseRoots Q₀ := by
    intro ξ hξ
    obtain ⟨ζ, hζ, rfl⟩ := mem_image.mp hξ
    obtain ⟨d, hd, hζd⟩ := mem_biUnion.mp (hT hζ)
    have hd0 := (mem_Icc.mp hd).1
    have hpow := (Polynomial.mem_nthRootsFinset hd0 1).mp hζd
    exact mem_biUnion.mpr ⟨d, hd, (Polynomial.mem_nthRootsFinset hd0 1).mpr (by
      rw [← pow_mul, mul_comm, pow_mul, hpow, one_pow])⟩
  have hls := largeSieve_responseRoots hQ₀ himg A L y
  calc ∑ ξ ∈ T.image (· ^ j), (T.filter (· ^ j = ξ)).card • f ξ
      ≤ ∑ ξ ∈ T.image (· ^ j), (j : ℝ) * f ξ := by
        refine sum_le_sum fun ξ _ => ?_
        rw [nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        have hsub : T.filter (· ^ j = ξ) ⊆ Polynomial.nthRootsFinset j ξ := fun ζ hζ =>
          (Polynomial.mem_nthRootsFinset hj ξ).mpr (mem_filter.mp hζ).2
        have hcard : (Polynomial.nthRootsFinset j ξ).card ≤ j := by
          rw [Polynomial.nthRootsFinset_def]
          exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots j ξ)
        exact_mod_cast (card_le_card hsub).trans hcard
    _ = (j : ℝ) * ∑ ξ ∈ T.image (· ^ j), f ξ := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hls (Nat.cast_nonneg j)

/-- `Σ_{1 ≤ j ≤ H} √j/j² ≤ 4`. -/
theorem sum_Icc_sqrt_div_sq_le (H : ℕ) :
    ∑ j ∈ Icc 1 H, Real.sqrt j / (j : ℝ) ^ 2 ≤ 4 := by
  have key : ∀ j : ℕ, 1 ≤ j → Real.sqrt j / (j : ℝ) ^ 2 ≤
      4 * (1 / Real.sqrt j - 1 / Real.sqrt (j + 1)) := by
    intro j hj
    have hj0 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    set a := Real.sqrt j
    set b := Real.sqrt ((j : ℝ) + 1)
    have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
    have hb : a ≤ b := Real.sqrt_le_sqrt (by linarith)
    have ha2 : a ^ 2 = j := Real.sq_sqrt (by linarith)
    have hb2 : b ^ 2 = (j : ℝ) + 1 := Real.sq_sqrt (by linarith)
    have hb0 : 0 < b := lt_of_lt_of_le ha hb
    have hdiff : (b - a) * (b + a) = 1 := by nlinarith
    have hb2le : b ^ 2 ≤ 2 * a ^ 2 := by rw [ha2, hb2]; linarith
    have e1 : Real.sqrt j / (j : ℝ) ^ 2 = 1 / a ^ 3 := by
      rw [show (j : ℝ) = a ^ 2 from ha2.symm, Real.sqrt_sq ha.le]
      field_simp
    rw [e1, div_sub_div _ _ ha.ne' hb0.ne', one_mul, mul_one, mul_div_assoc',
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos ha hb0, sq_nonneg (a - b), mul_pos (mul_pos ha ha) hb0,
      mul_pos (mul_pos ha ha) ha]
  calc ∑ j ∈ Icc 1 H, Real.sqrt j / (j : ℝ) ^ 2
      ≤ ∑ j ∈ Icc 1 H, 4 * (1 / Real.sqrt j - 1 / Real.sqrt (j + 1)) :=
        sum_le_sum fun j hj => key j (mem_Icc.mp hj).1
    _ = 4 * (1 / Real.sqrt 1 - 1 / Real.sqrt ((H : ℝ) + 1)) := by
        rw [← mul_sum]
        congr 1
        induction H with
        | zero => simp
        | succ H ih =>
          rw [sum_Icc_succ_top (by omega), ih]
          push_cast
          ring
    _ ≤ 4 := by
        rw [Real.sqrt_one]
        have : 0 ≤ 1 / Real.sqrt ((H : ℝ) + 1) := by positivity
        linarith

/-! ## §5. The large-sieve bound for the cross-scale remainder -/

theorem pw_le_inv_sq (M : ℕ) : pw M ≤ 1 / (M : ℝ) ^ 2 := by
  unfold pw
  rcases Nat.eq_zero_or_pos M with h | h
  · subst h; simp
  have : (0 : ℝ) < M := by exact_mod_cast h
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

theorem sum_Icc_pw_sub_pw_succ_mul_le {n H : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Icc 1 H, (pw (j * n) - pw (j * n + 1)) ≤ 4 / (n : ℝ) ^ 3 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc ∑ j ∈ Icc 1 H, (pw (j * n) - pw (j * n + 1))
      ≤ ∑ j ∈ Icc 1 H, 2 / (n : ℝ) ^ 3 * (1 / (j : ℝ) ^ 2) := by
        refine sum_le_sum fun j hj => ?_
        have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
        have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
        rw [pw_sub_pw_succ (Nat.one_le_iff_ne_zero.mpr (by positivity))]
        push_cast
        have hjn : (0 : ℝ) < (j : ℝ) * n := by positivity
        calc 2 / ((j : ℝ) * n * ((j : ℝ) * n + 1) * ((j : ℝ) * n + 2))
            ≤ 2 / ((j : ℝ) * n) ^ 3 :=
              div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
          _ ≤ 2 / (n : ℝ) ^ 3 * (1 / (j : ℝ) ^ 2) := by
              rw [div_mul_div_comm, mul_one]
              refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
              have : (j : ℝ) ^ 2 * 1 ≤ (j : ℝ) ^ 2 * j := mul_le_mul_of_nonneg_left hjR (by positivity)
              nlinarith [mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 3)]
    _ = 2 / (n : ℝ) ^ 3 * ∑ j ∈ Icc 1 H, 1 / (j : ℝ) ^ 2 := by rw [mul_sum]
    _ ≤ 2 / (n : ℝ) ^ 3 * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rcases Nat.eq_zero_or_pos H with h0 | hH
        · subst h0; simp
        · have := sum_Icc_one_div_sq_le hH
          have : 0 ≤ 1 / (H : ℝ) := by positivity
          linarith
    _ = 4 / (n : ℝ) ^ 3 := by ring

/-- The step decomposition of the inner sum against the pronic weight. -/
theorem sum_range_mul_div_div_pronic_eq {n H : ℕ} (hn : 0 < n) (F : ℕ → ℝ) :
    ∑ M ∈ range H, F M * ((M / n : ℕ) : ℝ) / (pronicSeq M : ℝ) =
      ∑ j ∈ Icc 1 H, ∑ M ∈ Ico (j * n) H, F M * pw M := by
  rw [sum_congr rfl fun M hM => by
    rw [cast_div_eq_sum_steps hn (mem_range.mp hM), mul_sum, sum_div], sum_comm]
  refine sum_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
  simp_rw [mul_ite, mul_one, mul_zero, ite_div, zero_div]
  rw [← sum_filter]
  have hset : (range H).filter (fun M => j * n ≤ M) = Ico (j * n) H := by
    ext M; simp only [mem_filter, mem_range, mem_Ico]; tauto
  rw [hset]
  refine sum_congr rfl fun M hM => ?_
  rw [cast_pronicSeq_eq, pw]
  ring

/-- **Large-sieve dispersion of the cross-scale remainder.** For a row `c` on a set `S` of primes
`p ≤ Q₀` and a row `c'` on the window `[A+1, A+L]`, with `(1/2)` constants,
`|B + m R' + β H'| ≤ ½ √(Σ c(p)² p²) √(L + 2Q₀² - 1) √(Σ c'(n)²/n⁴) + ½ Σ |c(p)| p² · Σ |c'(n)|/n³`. -/
theorem abs_rowBilinear_add_mean_add_beta_le_largeSieve {N Q₀ A L : ℕ} {S : Finset ℕ}
    (hQ₀ : 2 ≤ Q₀) (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N ∧ p ≤ Q₀) {c c' : ℕ → ℝ}
    (hsupp : ∀ n, c n ≠ 0 → n ∈ S) (hsupp' : ∀ n, c' n ≠ 0 → n ∈ Icc (A + 1) (A + L))
    (hAL : A + L ≤ N) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c'| ≤
      1 / 2 * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) *
          Real.sqrt ((L : ℝ) + 2 * (Q₀ : ℝ) ^ 2 - 1) *
          Real.sqrt (∑ n ∈ Icc (A + 1) (A + L), c' n ^ 2 / (n : ℝ) ^ 4) +
        1 / 2 * (∑ p ∈ S, |c p| * (p : ℝ) ^ 2) *
          ∑ n ∈ Icc (A + 1) (A + L), |c' n| / (n : ℝ) ^ 3 := by
  classical
  set W := Icc (A + 1) (A + L) with hW
  have hWN : W ⊆ Icc 1 N := Icc_subset_Icc (by omega) hAL
  have hW1 : ∀ n ∈ W, 1 ≤ n := fun n hn => by simp only [hW, mem_Icc] at hn; omega
  have hS' : ∀ p ∈ S, p.Prime ∧ p ≤ N := fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩
  set F := rowFluct N c
  set x : ℕ → ℂ → ℂ := fun p ζ => ((c p / p : ℝ) : ℂ) * (ζ / (ζ - 1))
  set T := S.biUnion fun p => primitiveRoots p ℂ with hT
  have hdisj : (S : Set ℕ).PairwiseDisjoint fun p => primitiveRoots p ℂ := by
    intro p hp q hq hpq
    rw [Function.onFun, Finset.disjoint_left]
    intro ζ hζp hζq
    have h1 := ((mem_primitiveRoots (hS p hp).1.pos).mp hζp).eq_orderOf
    have h2 := ((mem_primitiveRoots (hS q hq).1.pos).mp hζq).eq_orderOf
    exact hpq (h1.trans h2.symm)
  have hTroots : T ⊆ responseRoots Q₀ := by
    intro ζ hζ
    obtain ⟨p, hp, hζp⟩ := mem_biUnion.mp hζ
    have hprim := (mem_primitiveRoots (hS p hp).1.pos).mp hζp
    exact mem_biUnion.mpr ⟨p, mem_Icc.mpr ⟨(hS p hp).1.one_lt.le, (hS p hp).2.2⟩,
      (Polynomial.mem_nthRootsFinset (hS p hp).1.pos 1).mpr hprim.pow_eq_one⟩
  -- the coefficient of a frequency, through its order
  set α : ℂ → ℂ := fun ζ => x (orderOf ζ) ζ / (1 - ζ) with hα
  have hαeq : ∀ p ∈ S, ∀ ζ ∈ primitiveRoots p ℂ, α ζ = x p ζ / (1 - ζ) := by
    intro p hp ζ hζ
    show x (orderOf ζ) ζ / (1 - ζ) = x p ζ / (1 - ζ)
    rw [← ((mem_primitiveRoots (hS p hp).1.pos).mp hζ).eq_orderOf]
  have hroot : ∀ p ∈ S, ∀ ζ ∈ primitiveRoots p ℂ, ‖ζ‖ = 1 ∧ ζ ≠ 1 := fun p hp ζ hζ => by
    have hprim := (mem_primitiveRoots (hS p hp).1.pos).mp hζ
    exact ⟨hprim.norm'_eq_one (hS p hp).1.ne_zero, hprim.ne_one (hS p hp).1.one_lt⟩
  -- the frequency-side sums
  set G : ℕ → ℕ → ℂ → ℂ := fun H A ζ => ∑ M ∈ Ico A H, (pw M : ℂ) * ζ ^ M
  set mainG : ℕ → ℕ → ℂ → ℂ := fun H A ζ => if A < H then (pw A : ℂ) * ζ ^ A / (1 - ζ) else 0
  set errB : ℕ → ℕ → ℂ → ℝ := fun H A ζ =>
    if A < H then (pw (H - 1) + 2 * (pw A - pw (A + 1)) / ‖ζ - 1‖) / ‖ζ - 1‖ else 0
  have hGsplit : ∀ H A ζ, 1 ≤ A → ‖ζ‖ = 1 → ζ ≠ 1 → ‖G H A ζ - mainG H A ζ‖ ≤ errB H A ζ := by
    intro H A ζ hA hζ hζ1
    simp only [G, mainG, errB]
    split_ifs with hAH
    · exact norm_sum_Ico_pw_mul_pow_sub_le hζ hζ1 hA hAH
    · rw [Ico_eq_empty_of_le (not_lt.mp hAH), sum_empty, sub_zero, norm_zero]
  -- the step sum, expanded over the window and the primitive roots
  set step : ℕ → ℝ := fun H => ∑ n ∈ Icc 1 N, c' n *
    ∑ M ∈ range H, F M * ((M / n : ℕ) : ℝ) / (pronicSeq M : ℝ)
  have hstepW : ∀ H, ((step H : ℝ) : ℂ) = ∑ n ∈ W, (c' n : ℂ) * ∑ j ∈ Icc 1 H,
      ∑ p ∈ S, ∑ ζ ∈ primitiveRoots p ℂ, x p ζ * G H (j * n) ζ := by
    intro H
    simp only [step]
    rw [← sum_subset hWN fun n _ hn => by
      have : c' n = 0 := by by_contra h; exact hn (hsupp' n h)
      rw [this, zero_mul]]
    push_cast
    refine sum_congr rfl fun n hn => ?_
    congr 1
    have hn0 : 0 < n := hW1 n hn
    have h := sum_range_mul_div_div_pronic_eq (H := H) hn0 F
    have hcast := congrArg (fun r : ℝ => (r : ℂ)) h
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_natCast] at hcast
    rw [hcast]
    refine sum_congr rfl fun j _ => ?_
    simp only [G]
    rw [sum_congr rfl fun M _ => by rw [rowFluct_eq_spectral hS' hsupp M, sum_mul],
      sum_comm]
    refine sum_congr rfl fun p _ => ?_
    rw [sum_congr rfl fun M _ => by rw [sum_mul], sum_comm]
    refine sum_congr rfl fun ζ _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun M _ => by simp only [x]; ring
  -- norms of the coefficients
  have hxnorm : ∀ p ∈ S, ∀ ζ ∈ primitiveRoots p ℂ, ‖x p ζ‖ = |c p| / p * (1 / ‖ζ - 1‖) := by
    intro p hp ζ hζ
    obtain ⟨hζn, hζ1⟩ := hroot p hp ζ hζ
    simp [x, hζn]
  have hαnorm : ∀ p ∈ S, ∀ ζ ∈ primitiveRoots p ℂ, ‖α ζ‖ ^ 2 =
      (c p / p) ^ 2 * (1 / ‖ζ - 1‖ ^ (2 + 2)) := by
    intro p hp ζ hζ
    rw [hαeq p hp ζ hζ, norm_div, hxnorm p hp ζ hζ, norm_sub_rev 1 ζ]
    have hpos : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hroot p hp ζ hζ).2)
    rw [← sq_abs (c p / p), abs_div, Nat.abs_cast]
    field_simp
  have hαsum : Real.sqrt (∑ ζ ∈ T, ‖α ζ‖ ^ 2) ≤ 1 / 8 * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) := by
    rw [show (1 : ℝ) / 8 = Real.sqrt (1 / 64) by
      rw [show (1 : ℝ) / 64 = (1 / 8) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
      ← Real.sqrt_mul (by norm_num)]
    refine Real.sqrt_le_sqrt ?_
    rw [hT, sum_biUnion hdisj, mul_sum]
    refine sum_le_sum fun p hp => ?_
    rw [sum_congr rfl fun ζ hζ => hαnorm p hp ζ hζ, ← mul_sum]
    have hp2 := (hS p hp).1.two_le
    have hpR : (0 : ℝ) < p := by exact_mod_cast (hS p hp).1.pos
    calc (c p / p) ^ 2 * ∑ ζ ∈ primitiveRoots p ℂ, 1 / ‖ζ - 1‖ ^ (2 + 2)
        ≤ (c p / p) ^ 2 * (((p : ℝ) / 4) ^ 2 * ((p : ℝ) ^ 2 / 4)) :=
          mul_le_mul_of_nonneg_left (sum_primitiveRoots_inv_norm_sub_one_pow_le hp2 2)
            (sq_nonneg _)
      _ = 1 / 64 * (c p ^ 2 * (p : ℝ) ^ 2) := by field_simp; ring
  -- the bound at a finite horizon
  set X : ℝ := (L : ℝ) + 2 * (Q₀ : ℝ) ^ 2 - 1
  set Y : ℝ := ∑ n ∈ W, c' n ^ 2 / (n : ℝ) ^ 4
  have hX : 0 ≤ X := by
    have : (2 : ℝ) ≤ Q₀ := by exact_mod_cast hQ₀
    simp only [X]; nlinarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hY : 0 ≤ Y := sum_nonneg fun n _ => by positivity
  set E₁ : ℝ := ∑ p ∈ S, |c p| * (p : ℝ) ^ 2
  set E₂ : ℝ := ∑ n ∈ W, |c' n| / (n : ℝ) ^ 3
  set δ : ℕ → ℝ := fun H => (H : ℝ) * pw (H - 1) *
    ((∑ n ∈ W, |c' n|) * ∑ p ∈ S, |c p| * p / 4)
  have hfin : ∀ H, ‖((step H : ℝ) : ℂ)‖ ≤
      1 / 2 * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) * Real.sqrt X * Real.sqrt Y +
        1 / 2 * E₁ * E₂ + δ H := by
    intro H
    rw [hstepW H]
    set y : ℕ → ℕ → ℂ := fun j n => if j * n < H then (c' n : ℂ) * (pw (j * n) : ℂ) else 0
    set Φ : ℕ → ℂ → ℂ := fun j ζ => ∑ n ∈ W, y j n * (ζ ^ j) ^ n
    have hsplit : ∑ n ∈ W, (c' n : ℂ) * ∑ j ∈ Icc 1 H, ∑ p ∈ S, ∑ ζ ∈ primitiveRoots p ℂ,
        x p ζ * G H (j * n) ζ =
        ∑ j ∈ Icc 1 H, ∑ ζ ∈ T, α ζ * Φ j ζ +
          ∑ n ∈ W, (c' n : ℂ) * ∑ j ∈ Icc 1 H, ∑ p ∈ S, ∑ ζ ∈ primitiveRoots p ℂ,
            x p ζ * (G H (j * n) ζ - mainG H (j * n) ζ) := by
      have hmain : ∑ n ∈ W, (c' n : ℂ) * ∑ j ∈ Icc 1 H, ∑ p ∈ S, ∑ ζ ∈ primitiveRoots p ℂ,
          x p ζ * mainG H (j * n) ζ = ∑ j ∈ Icc 1 H, ∑ ζ ∈ T, α ζ * Φ j ζ := by
        simp only [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun j _ => ?_
        rw [sum_comm, hT, sum_biUnion hdisj]
        refine sum_congr rfl fun p hp => ?_
        rw [sum_comm]
        refine sum_congr rfl fun ζ hζ => ?_
        simp only [Φ, mul_sum]
        refine sum_congr rfl fun n _ => ?_
        rw [hαeq p hp ζ hζ]
        simp only [mainG, y]
        split_ifs
        · rw [← pow_mul, mul_comm j n]; ring
        · simp
      rw [← hmain, ← sum_add_distrib]
      refine sum_congr rfl fun n _ => ?_
      rw [← mul_add, ← sum_add_distrib]
      congr 1
      refine sum_congr rfl fun j _ => ?_
      rw [← sum_add_distrib]
      refine sum_congr rfl fun p _ => ?_
      rw [← sum_add_distrib]
      exact sum_congr rfl fun ζ _ => by ring
    rw [hsplit]
    have hM : ‖∑ j ∈ Icc 1 H, ∑ ζ ∈ T, α ζ * Φ j ζ‖ ≤
        1 / 2 * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) * Real.sqrt X * Real.sqrt Y := by
      have hj : ∀ j ∈ Icc 1 H, ‖∑ ζ ∈ T, α ζ * Φ j ζ‖ ≤
          Real.sqrt (∑ ζ ∈ T, ‖α ζ‖ ^ 2) * (Real.sqrt X * Real.sqrt Y) *
            (Real.sqrt j / (j : ℝ) ^ 2) := by
        intro j hj
        have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
        have hjR : (0 : ℝ) < j := by exact_mod_cast hj1
        have hcs : ‖∑ ζ ∈ T, α ζ * Φ j ζ‖ ≤
            Real.sqrt (∑ ζ ∈ T, ‖α ζ‖ ^ 2) * Real.sqrt (∑ ζ ∈ T, ‖Φ j ζ‖ ^ 2) := by
          refine (norm_sum_le _ _).trans ?_
          simp only [norm_mul]
          exact Real.sum_mul_le_sqrt_mul_sqrt T _ _
        have hy : ∑ n ∈ W, ‖y j n‖ ^ 2 ≤ Y / (j : ℝ) ^ 4 := by
          rw [div_eq_mul_inv, sum_mul]
          refine sum_le_sum fun n hn => ?_
          have hn1 : 1 ≤ n := hW1 n hn
          have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
          simp only [y]
          split_ifs
          · rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs, mul_pow, sq_abs, sq_abs]
            have hpw := pw_le_inv_sq (j * n)
            have hpw0 := pw_nonneg (j * n)
            have hsq : pw (j * n) ^ 2 ≤ (1 / ((j * n : ℕ) : ℝ) ^ 2) ^ 2 :=
              pow_le_pow_left₀ hpw0 hpw 2
            calc c' n ^ 2 * pw (j * n) ^ 2 ≤ c' n ^ 2 * (1 / ((j * n : ℕ) : ℝ) ^ 2) ^ 2 :=
                  mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
              _ = c' n ^ 2 / (n : ℝ) ^ 4 * ((j : ℝ) ^ 4)⁻¹ := by push_cast; field_simp
          · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
            positivity
        have hls := sum_norm_sq_dilated_le hQ₀ hTroots (by omega : 0 < j) A L (y j)
        have hΦ : ∑ ζ ∈ T, ‖Φ j ζ‖ ^ 2 ≤ (X * Y) * (Real.sqrt j / (j : ℝ) ^ 2) ^ 2 := by
          refine hls.trans ?_
          rw [div_pow, Real.sq_sqrt hjR.le]
          calc (j : ℝ) * (X * ∑ k ∈ Icc (A + 1) (A + L), ‖y j k‖ ^ 2)
              ≤ (j : ℝ) * (X * (Y / (j : ℝ) ^ 4)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hy hX) hjR.le
            _ = X * Y * ((j : ℝ) / ((j : ℝ) ^ 2) ^ 2) := by field_simp
        have hroot' : Real.sqrt (∑ ζ ∈ T, ‖Φ j ζ‖ ^ 2) ≤
            Real.sqrt X * Real.sqrt Y * (Real.sqrt j / (j : ℝ) ^ 2) := by
          calc Real.sqrt (∑ ζ ∈ T, ‖Φ j ζ‖ ^ 2) ≤ Real.sqrt ((X * Y) *
                (Real.sqrt j / (j : ℝ) ^ 2) ^ 2) := Real.sqrt_le_sqrt hΦ
            _ = Real.sqrt X * Real.sqrt Y * (Real.sqrt j / (j : ℝ) ^ 2) := by
                rw [Real.sqrt_mul (mul_nonneg hX hY), Real.sqrt_mul hX,
                  Real.sqrt_sq (by positivity)]
        calc ‖∑ ζ ∈ T, α ζ * Φ j ζ‖ ≤ _ := hcs
          _ ≤ Real.sqrt (∑ ζ ∈ T, ‖α ζ‖ ^ 2) *
                (Real.sqrt X * Real.sqrt Y * (Real.sqrt j / (j : ℝ) ^ 2)) :=
              mul_le_mul_of_nonneg_left hroot' (Real.sqrt_nonneg _)
          _ = _ := by ring
      calc ‖∑ j ∈ Icc 1 H, ∑ ζ ∈ T, α ζ * Φ j ζ‖
          ≤ ∑ j ∈ Icc 1 H, Real.sqrt (∑ ζ ∈ T, ‖α ζ‖ ^ 2) * (Real.sqrt X * Real.sqrt Y) *
              (Real.sqrt j / (j : ℝ) ^ 2) := (norm_sum_le _ _).trans (sum_le_sum hj)
        _ = Real.sqrt (∑ ζ ∈ T, ‖α ζ‖ ^ 2) * (Real.sqrt X * Real.sqrt Y) *
              ∑ j ∈ Icc 1 H, Real.sqrt j / (j : ℝ) ^ 2 := by rw [mul_sum]
        _ ≤ 1 / 8 * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) * (Real.sqrt X * Real.sqrt Y) * 4 :=
            mul_le_mul (mul_le_mul_of_nonneg_right hαsum (by positivity))
              (sum_Icc_sqrt_div_sq_le H) (sum_nonneg fun _ _ => by positivity) (by positivity)
        _ = 1 / 2 * Real.sqrt (∑ p ∈ S, c p ^ 2 * (p : ℝ) ^ 2) * Real.sqrt X * Real.sqrt Y := by
            ring
    have hE : ‖∑ n ∈ W, (c' n : ℂ) * ∑ j ∈ Icc 1 H, ∑ p ∈ S, ∑ ζ ∈ primitiveRoots p ℂ,
        x p ζ * (G H (j * n) ζ - mainG H (j * n) ζ)‖ ≤ 1 / 2 * E₁ * E₂ + δ H := by
      -- per prime: the boundary term and the second-order term
      have hpb : ∀ n ∈ W, ∀ p ∈ S, ∑ j ∈ Icc 1 H, ∑ ζ ∈ primitiveRoots p ℂ,
          ‖x p ζ‖ * errB H (j * n) ζ ≤
            |c p| * ((H : ℝ) * pw (H - 1) * p / 4 + (p : ℝ) ^ 2 / (2 * (n : ℝ) ^ 3)) := by
        intro n hn p hp
        have hn1 := hW1 n hn
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
        have hp2 := (hS p hp).1.two_le
        have hpR : (0 : ℝ) < p := by exact_mod_cast (hS p hp).1.pos
        have hterm : ∀ j ∈ Icc 1 H, ∀ ζ ∈ primitiveRoots p ℂ, ‖x p ζ‖ * errB H (j * n) ζ ≤
            |c p| / p * ((if j * n < H then pw (H - 1) else 0) * (1 / ‖ζ - 1‖ ^ 2) +
              2 * (pw (j * n) - pw (j * n + 1)) * (1 / ‖ζ - 1‖ ^ (1 + 2))) := by
          intro j hj ζ hζ
          have hj1 := (mem_Icc.mp hj).1
          have hjn : 1 ≤ j * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
          have ha : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hroot p hp ζ hζ).2)
          have hΔ : 0 ≤ pw (j * n) - pw (j * n + 1) := by
            rw [pw_sub_pw_succ hjn]; positivity
          rw [hxnorm p hp ζ hζ]
          simp only [errB]
          split_ifs with h
          · rw [mul_assoc]
            refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by positivity)
            field_simp
            ring
          · rw [mul_zero, zero_mul, zero_add]
            positivity
        calc ∑ j ∈ Icc 1 H, ∑ ζ ∈ primitiveRoots p ℂ, ‖x p ζ‖ * errB H (j * n) ζ
            ≤ ∑ j ∈ Icc 1 H, |c p| / p * ((if j * n < H then pw (H - 1) else 0) * ((p : ℝ) ^ 2 / 4) +
                2 * (pw (j * n) - pw (j * n + 1)) * (((p : ℝ) / 4) ^ 1 * ((p : ℝ) ^ 2 / 4))) := by
              refine sum_le_sum fun j hj => ?_
              refine (sum_le_sum (hterm j hj)).trans ?_
              rw [← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum]
              have hj1 := (mem_Icc.mp hj).1
              have hΔ : 0 ≤ pw (j * n) - pw (j * n + 1) := by
                rw [pw_sub_pw_succ (Nat.one_le_iff_ne_zero.mpr (by positivity))]; positivity
              refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
              · refine mul_le_mul_of_nonneg_left (sum_primitiveRoots_inv_norm_sub_one_sq_le hp2) ?_
                split_ifs <;> [exact pw_nonneg _; exact le_rfl]
              · exact mul_le_mul_of_nonneg_left (sum_primitiveRoots_inv_norm_sub_one_pow_le hp2 1)
                  (by positivity)
          _ = |c p| / p * ((p : ℝ) ^ 2 / 4 * ∑ j ∈ Icc 1 H, (if j * n < H then pw (H - 1) else 0) +
                (p : ℝ) ^ 3 / 8 * ∑ j ∈ Icc 1 H, (pw (j * n) - pw (j * n + 1))) := by
              rw [← mul_sum, sum_add_distrib, mul_sum, mul_sum]
              congr 1
              refine congrArg₂ _ (sum_congr rfl fun _ _ => by ring) (sum_congr rfl fun _ _ => by ring)
          _ ≤ |c p| / p * ((p : ℝ) ^ 2 / 4 * ((H : ℝ) * pw (H - 1)) +
                (p : ℝ) ^ 3 / 8 * (4 / (n : ℝ) ^ 3)) := by
              refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
              · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                calc ∑ j ∈ Icc 1 H, (if j * n < H then pw (H - 1) else 0)
                    ≤ ∑ _j ∈ Icc 1 H, pw (H - 1) := sum_le_sum fun j _ => by
                      split_ifs <;> [exact le_rfl; exact pw_nonneg _]
                  _ = (H : ℝ) * pw (H - 1) := by rw [sum_const, Nat.card_Icc]; simp
              · exact mul_le_mul_of_nonneg_left (sum_Icc_pw_sub_pw_succ_mul_le hn1) (by positivity)
          _ = |c p| * ((H : ℝ) * pw (H - 1) * p / 4 + (p : ℝ) ^ 2 / (2 * (n : ℝ) ^ 3)) := by
              field_simp
              ring
      calc ‖∑ n ∈ W, (c' n : ℂ) * ∑ j ∈ Icc 1 H, ∑ p ∈ S, ∑ ζ ∈ primitiveRoots p ℂ,
            x p ζ * (G H (j * n) ζ - mainG H (j * n) ζ)‖
          ≤ ∑ n ∈ W, |c' n| * ∑ p ∈ S, ∑ j ∈ Icc 1 H, ∑ ζ ∈ primitiveRoots p ℂ,
              ‖x p ζ‖ * errB H (j * n) ζ := by
            refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, sum_comm]
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            refine (norm_sum_le _ _).trans (sum_le_sum fun p hp => ?_)
            refine (norm_sum_le _ _).trans (sum_le_sum fun j hj => ?_)
            refine (norm_sum_le _ _).trans (sum_le_sum fun ζ hζ => ?_)
            rw [norm_mul]
            have hj1 := (mem_Icc.mp hj).1
            have hn1 := hW1 n hn
            have hjn : 1 ≤ j * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
            exact mul_le_mul_of_nonneg_left (hGsplit H (j * n) ζ hjn (hroot p hp ζ hζ).1
              (hroot p hp ζ hζ).2) (norm_nonneg _)
        _ ≤ ∑ n ∈ W, |c' n| * ∑ p ∈ S,
              |c p| * ((H : ℝ) * pw (H - 1) * p / 4 + (p : ℝ) ^ 2 / (2 * (n : ℝ) ^ 3)) :=
            sum_le_sum fun n hn => mul_le_mul_of_nonneg_left
              (sum_le_sum fun p hp => hpb n hn p hp) (abs_nonneg _)
        _ = 1 / 2 * E₁ * E₂ + δ H := by
            have e1 : E₁ * E₂ = ∑ n ∈ W, ∑ p ∈ S, (|c p| * (p : ℝ) ^ 2) * (|c' n| / (n : ℝ) ^ 3) := by
              simp only [E₁, E₂]; rw [sum_mul_sum, sum_comm]
            have e2 : (∑ n ∈ W, |c' n|) * ∑ p ∈ S, |c p| * p / 4 =
                ∑ n ∈ W, ∑ p ∈ S, |c' n| * (|c p| * p / 4) := sum_mul_sum _ _ _ _
            simp only [δ]
            rw [e2, mul_assoc, e1, mul_sum, mul_sum, ← sum_add_distrib]
            refine sum_congr rfl fun n hn => ?_
            have hnR : (0 : ℝ) < n := by exact_mod_cast hW1 n hn
            rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
            refine sum_congr rfl fun p _ => ?_
            field_simp
            ring
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add hM hE
      _ = _ := by ring
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have h0 : Tendsto (fun H : ℕ => (H : ℝ) * pw (H - 1)) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun H => by
          have := pw_nonneg (H - 1); positivity)
        (eventually_atTop.mpr ⟨2, fun H hH => ?_⟩) (tendsto_const_div_atTop_nhds_zero_nat 2)
      have hH1 : ((H - 1 : ℕ) : ℝ) = (H : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have hHR : (2 : ℝ) ≤ H := by exact_mod_cast hH
      rw [pw, hH1, show (H : ℝ) - 1 + 1 = H by ring, mul_one_div,
        div_le_div_iff₀ (by nlinarith) (by linarith)]
      nlinarith
    simpa using h0.mul_const ((∑ n ∈ W, |c' n|) * ∑ p ∈ S, |c p| * p / 4)
  have hlim := (tendsto_rowStepSum N c c').abs
  have hle := le_of_tendsto_of_tendsto hlim (tendsto_const_nhds.add hδ)
    (Eventually.of_forall fun H => by
      have := hfin H
      rwa [Complex.norm_real, Real.norm_eq_abs] at this)
  simpa only [add_zero] using hle

end

end GaloisForLFunctions.BezoutValuationIncidence
