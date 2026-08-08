import GaloisForLFunctions.RHTower.Sieve.PairConvolutionPerronSum
import GaloisForLFunctions.RHTower.Sieve.GhsPerronSum
import GaloisForLFunctions.RHTower.Sieve.MultiplicativeLogRecursion

/-!
# The logarithmic weight as a single convolution, through the pair Perron law

For a completely multiplicative `f` the weight `log` is carried by *one* Dirichlet convolution,

`f(n)·log n = ∑_{ab = n} f(a)Λ(a)·f(b) = ((f·Λ) ⍟ f)(n)`,

because `f(a)f(b) = f(n)` collapses every antidiagonal term and `∑_{a ∣ n} Λ(a) = log n`.  The corpus
already owns the summed, divisor-swapped form of this identity; what the Perron passage needs is the
sequence-level one, since Perron's formula is applied to a convolution and not to a double sum.

Truncating both factors at any `L ≥ n` changes nothing, because every divisor of `n` is at most `n`.  So
the partial sum of `f` is reached by a *pair* convolution:

`‖∑_{n ≤ N} f(n)‖·log N ≤ N + ‖∑_{n ≤ N} ((f·Λ_{≤N}) ⍟ f_{≤N})(n)‖`,

the first term being the cost `∑_{n ≤ N}(log N − log n) = N log N − log N! ≤ N` of replacing `log n` by
`log N`.  Against the threefold logarithmic recursion, whose error is `O(N log log N)`, this is both
shorter and sharper; and the pair Perron law applies to it with the general affine mean square, whose
height-independent constant is the convergent `n`-weighted von Mangoldt mass `∑_{n ≤ N} Λ(n)²n^{1−2σ}`
and whose height-linear rate is the bounded `∑_{n ≤ N} Λ(n)²n^{−2σ}`.
-/

noncomputable section
namespace RHTower.Sieve
open Complex Finset ArithmeticFunction

/-- The von Mangoldt weighting of a sequence. -/
def vonMangoldtSeq (f : ℕ → ℂ) : ℕ → ℂ := fun n => f n * ((Λ n : ℝ) : ℂ)

theorem vonMangoldtSeq_support {f : ℕ → ℂ} {L n : ℕ} (h : vonMangoldtSeq (truncSeq f L) n ≠ 0) :
    n ∈ Finset.Icc 1 L := by
  refine truncSeq_support (f := f) (L := L) (n := n) ?_
  intro h0
  rw [vonMangoldtSeq, h0, zero_mul] at h
  exact h rfl

theorem norm_vonMangoldtSeq_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (L n : ℕ) :
    ‖vonMangoldtSeq (truncSeq f L) n‖ ≤ (Λ n : ℝ) := by
  rw [vonMangoldtSeq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (vonMangoldt_nonneg (n := n))]
  calc ‖truncSeq f L n‖ * (Λ n : ℝ) ≤ 1 * (Λ n : ℝ) :=
        mul_le_mul_of_nonneg_right (norm_truncSeq_le hf L n) (vonMangoldt_nonneg (n := n))
    _ = (Λ n : ℝ) := one_mul _

/-- **The logarithmic weight is one convolution.**  For a completely multiplicative `f`, truncating both
factors at any point beyond `n` leaves `((f·Λ) ⍟ f)(n) = f(n)·log n`: every divisor of `n` is at most
`n`, `f(a)f(b) = f(n)` collapses the antidiagonal, and `∑_{a ∣ n} Λ(a) = log n`. -/
theorem convolution_vonMangoldtSeq_truncSeq_eq {f : ℕ → ℂ} (hf : ∀ a b : ℕ, f (a * b) = f a * f b)
    {L n : ℕ} (hn : n ≤ L) :
    LSeries.convolution (vonMangoldtSeq (truncSeq f L)) (truncSeq f L) n
      = f n * ((Real.log (n : ℝ) : ℝ) : ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp only [LSeries.convolution_def]
    simp
  simp only [LSeries.convolution_def]
  have hterm : ∀ x ∈ n.divisorsAntidiagonal,
      vonMangoldtSeq (truncSeq f L) x.1 * truncSeq f L x.2
        = f n * ((Λ x.1 : ℝ) : ℂ) := by
    intro x hx
    rw [Nat.mem_divisorsAntidiagonal] at hx
    have h1dvd : x.1 ∣ n := ⟨x.2, hx.1.symm⟩
    have h2dvd : x.2 ∣ n := ⟨x.1, by rw [← hx.1]; ring⟩
    have h1le : x.1 ≤ L := le_trans (Nat.le_of_dvd hn0 h1dvd) hn
    have h2le : x.2 ≤ L := le_trans (Nat.le_of_dvd hn0 h2dvd) hn
    have h1pos : 1 ≤ x.1 := Nat.one_le_iff_ne_zero.2 fun h => by
      rw [h, zero_mul] at hx; exact hx.2 hx.1.symm
    have h2pos : 1 ≤ x.2 := Nat.one_le_iff_ne_zero.2 fun h => by
      rw [h, mul_zero] at hx; exact hx.2 hx.1.symm
    rw [vonMangoldtSeq, truncSeq, truncSeq, if_pos (Finset.mem_Icc.2 ⟨h1pos, h1le⟩),
      if_pos (Finset.mem_Icc.2 ⟨h2pos, h2le⟩)]
    rw [show f x.1 * ((Λ x.1 : ℝ) : ℂ) * f x.2 = f x.1 * f x.2 * ((Λ x.1 : ℝ) : ℂ) by ring,
      ← hf, hx.1]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  have hdiv : (∑ x ∈ n.divisorsAntidiagonal, ((Λ x.1 : ℝ) : ℂ))
      = ∑ i ∈ n.divisors, ((Λ i : ℝ) : ℂ) :=
    Nat.sum_divisorsAntidiagonal (fun a _ => ((Λ a : ℝ) : ℂ))
  rw [hdiv, ← Complex.ofReal_sum, vonMangoldt_sum]

/-- The logarithmically weighted partial sum is the summatory function of the pair convolution. -/
theorem sum_Icc_convolution_vonMangoldtSeq_eq {f : ℕ → ℂ}
    (hf : ∀ a b : ℕ, f (a * b) = f a * f b) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n * ((Real.log (n : ℝ) : ℝ) : ℂ)
      = ∑ n ∈ Finset.Icc 1 N,
          LSeries.convolution (vonMangoldtSeq (truncSeq f N)) (truncSeq f N) n :=
  (Finset.sum_congr rfl fun _ hn =>
    convolution_vonMangoldtSeq_truncSeq_eq hf (Finset.mem_Icc.1 hn).2).symm

/-- The coefficients of the pair convolution are bounded by `log n`. -/
theorem norm_convolution_vonMangoldtSeq_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (L n : ℕ) :
    ‖LSeries.convolution (vonMangoldtSeq (truncSeq f L)) (truncSeq f L) n‖
      ≤ Real.log (n : ℝ) := by
  simp only [LSeries.convolution_def]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ x ∈ n.divisorsAntidiagonal,
      ‖vonMangoldtSeq (truncSeq f L) x.1 * truncSeq f L x.2‖ ≤ (Λ x.1 : ℝ) := by
    intro x _
    rw [norm_mul]
    calc ‖vonMangoldtSeq (truncSeq f L) x.1‖ * ‖truncSeq f L x.2‖
        ≤ (Λ x.1 : ℝ) * 1 :=
          mul_le_mul (norm_vonMangoldtSeq_le hf L x.1) (norm_truncSeq_le hf L x.2)
            (norm_nonneg _) (vonMangoldt_nonneg (n := x.1))
      _ = (Λ x.1 : ℝ) := mul_one _
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Nat.sum_divisorsAntidiagonal (fun a _ => (Λ a : ℝ)), vonMangoldt_sum]

/-- **A uniform coefficient bound for the pair convolution.**  Beyond `L²` the convolution vanishes, so
`log(L²)` bounds it everywhere. -/
theorem norm_convolution_vonMangoldtSeq_le_uniform {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {L : ℕ}
    (hL : 1 ≤ L) (n : ℕ) :
    ‖LSeries.convolution (vonMangoldtSeq (truncSeq f L)) (truncSeq f L) n‖
      ≤ Real.log ((L * L : ℕ) : ℝ) := by
  have hLL : (1 : ℝ) ≤ ((L * L : ℕ) : ℝ) := by
    have : 1 ≤ L * L := Nat.one_le_iff_ne_zero.2 (by positivity)
    exact_mod_cast this
  by_cases hz : LSeries.convolution (vonMangoldtSeq (truncSeq f L)) (truncSeq f L) n = 0
  · rw [hz, norm_zero]
    exact Real.log_nonneg hLL
  · have hmem := convolution_mem_Icc_of_support_mul
      (fun _ hm => vonMangoldtSeq_support hm) (fun _ hm => truncSeq_support hm) hz
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hmem).1
    refine le_trans (norm_convolution_vonMangoldtSeq_le hf L n) ?_
    exact Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast (Finset.mem_Icc.1 hmem).2)

/-- **A Halász-type mean value bound through the pair convolution.**  For a bounded completely
multiplicative `f`, the partial sum obeys

`‖∑_{n ≤ N} f(n)‖·log N ≤ N + (near-diagonal truncation error) + (1/2π)·(pair analytic bound)`,

with the analytic side charging the `Λ`-weighted factor one general affine mean square and the factor
`f` a pointwise bound `V` on the range of integration.  No primality, no sieve level, no logarithmic
recursion: the whole passage from the partial sum to the Perron integral is the identity
`f·log = (f·Λ) ⍟ f` together with `∑_{n ≤ N}(log N − log n) ≤ N`. -/
theorem norm_sum_Icc_mul_log_le_pair_general {f : ℕ → ℂ} (hf : ∀ a b : ℕ, f (a * b) = f a * f b)
    (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) {N : ℕ} (hN : 1 ≤ N)
    {V σ t₀ : ℝ} (hV : 0 ≤ V) (hσ : 1 ≤ σ) (ht₀ : 1 ≤ t₀) (K : ℕ)
    (hgV : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K →
      ‖LSeries (truncSeq f N) ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V) :
    ‖∑ n ∈ Finset.Icc 1 N, f n‖ * Real.log (N : ℝ)
      ≤ (N : ℝ)
        + (Real.log ((N * N : ℕ) : ℝ) * (((N : ℝ) + 1 / 2)) ^ σ
              * (5 * (1 + Real.log ((N * N : ℕ) : ℝ)) + 4 * (1 + Real.log N))
              / (Real.pi * (t₀ * 2 ^ K))
            + (1 / (2 * Real.pi))
              * perronVerticalPairBound σ ((N : ℝ) + 1 / 2) t₀ V
                  (generalMeanSquareConst (vonMangoldtSeq (truncSeq f N)) (Finset.Icc 1 N) σ)
                  (generalMeanSquareRate (vonMangoldtSeq (truncSeq f N)) (Finset.Icc 1 N) σ) K) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg hNR
  have hNsq : N ≤ N * N := by
    calc N = N * 1 := by ring
      _ ≤ N * N := Nat.mul_le_mul_left N hN
  -- the analytic half, at the truncation `L = N`
  have hpair := norm_sum_Icc_pair_general_near_le
    (c := vonMangoldtSeq (truncSeq f N)) (g := truncSeq f N) (Mc := N) (Mg := N) (N := N)
    (fun _ hm => vonMangoldtSeq_support hm) (fun _ hm => truncSeq_support hm)
    (norm_convolution_vonMangoldtSeq_le_uniform hbdd hN) hV hσ ht₀ K hgV
  rw [min_eq_right hNsq, ← sum_Icc_convolution_vonMangoldtSeq_eq hf] at hpair
  -- the elementary half
  have hweight := norm_sum_Icc_mul_log_sub_le (f := f) hbdd N
  have hsplit : ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
            - ∑ n ∈ Finset.Icc 1 N, f n * ((Real.log (n : ℝ) : ℝ) : ℂ)‖
          + ‖∑ n ∈ Finset.Icc 1 N, f n * ((Real.log (n : ℝ) : ℝ) : ℂ)‖ := by
    have := norm_add_le ((∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
        - ∑ n ∈ Finset.Icc 1 N, f n * ((Real.log (n : ℝ) : ℝ) : ℂ))
      (∑ n ∈ Finset.Icc 1 N, f n * ((Real.log (n : ℝ) : ℝ) : ℂ))
    simpa using this
  have hnorm : ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)‖
      = ‖∑ n ∈ Finset.Icc 1 N, f n‖ * Real.log (N : ℝ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogN]
  rw [hnorm] at hsplit
  linarith [hsplit, hweight, hpair]

end RHTower.Sieve
end
