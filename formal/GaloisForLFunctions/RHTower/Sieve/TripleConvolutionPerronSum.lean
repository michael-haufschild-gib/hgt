import GaloisForLFunctions.RHTower.Sieve.PerronVerticalTripleBound
import GaloisForLFunctions.RHTower.Sieve.PerronPrimeSumBound
import GaloisForLFunctions.RHTower.Sieve.PerronNearDiagonal
import GaloisForLFunctions.RHTower.Sieve.PerronVerticalBlockTripleBound
import GaloisForLFunctions.RHTower.Sieve.ConvolutionSupport
import GaloisForLFunctions.RHTower.Sieve.ProductFirstMoment

/-!
# The partial sum of a triple convolution, through the sharp Perron formula

The Perron step of a threefold convolution needs three things, and all three are now available: the
convolution of finitely supported sequences is finitely supported, so the truncated Perron formula
applies with its half-integer error; the Dirichlet series of a convolution is the product of the series,
so the integrand is `L(A)L(B)L(g)·x^s/s`; and the vertical integral of that product is bounded by the
dyadic split against two prime-sieve mean squares and a pointwise bound on the third factor.

`‖∑_{n ≤ M_AM_BM_g} (A ⍟ (B ⍟ g))(n)‖ ≤ (Perron error) + (1/2π)·(triple analytic bound)`.

Nothing here restricts the third factor beyond finite support and a bound on its size on the line: it is
where the arithmetic of the multiplicative function under study enters, and where a distance saving would
be applied.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- A finitely supported Dirichlet series is bounded on a vertical line by the damped `ℓ¹` mass of its
coefficients. -/
theorem norm_LSeries_line_le_l1 {g : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n : ℕ, g n ≠ 0 → n ∈ s) (σ t : ℝ) :
    ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ ≤ ∑ n ∈ s, ‖g n‖ * (n : ℝ) ^ (-σ) := by
  rw [← sum_mul_cpow_neg_eq_LSeries hs0 hsupp]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n hn => ?_)
  have hn0 : n ≠ 0 := fun h => hs0 (h ▸ hn)
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hnpos]
  have hre : (-((σ : ℂ) + (t : ℝ) * I)).re = -σ := by simp
  rw [hre]

/-- The Dirichlet series of a threefold convolution of finitely supported sequences is the product of
the three series. -/
theorem LSeries_convolution_triple_of_support {A B g : ℕ → ℂ} {MA MB Mg : ℕ}
    (hAsupp : ∀ n : ℕ, A n ≠ 0 → n ∈ Finset.Icc 1 MA)
    (hBsupp : ∀ n : ℕ, B n ≠ 0 → n ∈ Finset.Icc 1 MB)
    (hgsupp : ∀ n : ℕ, g n ≠ 0 → n ∈ Finset.Icc 1 Mg) (w : ℂ) :
    LSeries (LSeries.convolution A (LSeries.convolution B g)) w
      = LSeries A w * LSeries B w * LSeries g w := by
  have hBg : ∀ k : ℕ, (LSeries.convolution B g) k ≠ 0 → k ∈ Finset.Icc 1 (MB * Mg) :=
    fun k hk => convolution_mem_Icc_of_support_mul hBsupp hgsupp hk
  rw [LSeries_convolution' (LSeriesSummable_of_support hAsupp w)
      (LSeriesSummable_of_support hBg w),
    LSeries_convolution' (LSeriesSummable_of_support hBsupp w)
      (LSeriesSummable_of_support hgsupp w), mul_assoc]

/-- **The Perron step of a triple convolution, against any truncation error and any bound on its
vertical integral.**  The identification of the Dirichlet polynomial with the product of the three
series and the triangle inequality — with both the truncation error and the vertical integral left as
parameters.  Every pair of estimates, whatever separation device the truncation uses and whatever
device the analytic bound uses on the low range or the flanks, yields a bound on the partial sum
through this one law. -/
theorem norm_sum_Icc_triple_of_error_and_analytic_le {A B g : ℕ → ℂ} {MA MB Mg N : ℕ}
    (hAsupp : ∀ n : ℕ, A n ≠ 0 → n ∈ Finset.Icc 1 MA)
    (hBsupp : ∀ n : ℕ, B n ≠ 0 → n ∈ Finset.Icc 1 MB)
    (hgsupp : ∀ n : ℕ, g n ≠ 0 → n ∈ Finset.Icc 1 Mg)
    {E P σ t₀ : ℝ} (ht₀ : 0 ≤ t₀) (K : ℕ)
    (hE : ‖(∑ n ∈ Finset.Icc 1 (min (MA * (MB * Mg)) N),
              (LSeries.convolution A (LSeries.convolution B g)) n)
            - ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-(t₀ * 2 ^ K))..(t₀ * 2 ^ K),
                (∑ n ∈ Finset.Icc 1 (MA * (MB * Mg)),
                    (LSeries.convolution A (LSeries.convolution B g)) n
                      * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
                  * (((((N : ℝ) + 1 / 2) : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
                      / ((σ : ℂ) + (t : ℝ) * I))‖ ≤ E)
    (hP : (∫ t in (-(t₀ * 2 ^ K))..(t₀ * 2 ^ K),
        ‖LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
            * LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
                / ((σ : ℂ) + (t : ℝ) * I))‖) ≤ P) :
    ‖∑ n ∈ Finset.Icc 1 (min (MA * (MB * Mg)) N),
        (LSeries.convolution A (LSeries.convolution B g)) n‖
      ≤ E + (1 / (2 * Real.pi)) * P := by
  have hTle : -(t₀ * 2 ^ K) ≤ t₀ * 2 ^ K := by
    have : (0 : ℝ) ≤ t₀ * 2 ^ K := by positivity
    linarith
  set x : ℝ := (N : ℝ) + 1 / 2 with hxdef
  set T : ℝ := t₀ * 2 ^ K with hTdef
  set c : ℕ → ℂ := LSeries.convolution A (LSeries.convolution B g) with hc
  have hBg : ∀ k : ℕ, (LSeries.convolution B g) k ≠ 0 → k ∈ Finset.Icc 1 (MB * Mg) :=
    fun k hk => convolution_mem_Icc_of_support_mul hBsupp hgsupp hk
  have hcsupp : ∀ k : ℕ, c k ≠ 0 → k ∈ Finset.Icc 1 (MA * (MB * Mg)) := by
    intro k hk
    rw [hc] at hk
    exact convolution_mem_Icc_of_support_mul hAsupp hBg hk
  have hcs0 : (0 : ℕ) ∉ Finset.Icc 1 (MA * (MB * Mg)) := by simp
  have hPerron := hE
  have hbridge : ∀ t : ℝ,
      (∑ n ∈ Finset.Icc 1 (MA * (MB * Mg)), c n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I)))
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))
        = LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
            * LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)) := by
    intro t
    rw [sum_mul_cpow_neg_eq_LSeries hcs0 hcsupp, hc,
      LSeries_convolution_triple_of_support hAsupp hBsupp hgsupp]
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
          * LSeries g ((σ : ℂ) + (t : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)))
    (fun t _ => hbridge t)] at hPerron
  have hnormint : ‖∫ t in (-T)..T,
        LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
            * LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖
      ≤ ∫ t in (-T)..T,
        ‖LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
            * LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖ :=
    intervalIntegral.norm_integral_le_integral_norm hTle
  have hscale : ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
        LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
            * LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖
      ≤ (1 / (2 * Real.pi)) * P := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
    exact mul_le_mul_of_nonneg_left (le_trans hnormint hP) (by positivity)
  have htri : ‖∑ n ∈ Finset.Icc 1 (min (MA * (MB * Mg)) N), c n‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 (min (MA * (MB * Mg)) N), c n) - ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t in (-T)..T, LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
              * LSeries g ((σ : ℂ) + (t : ℝ) * I)
              * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖
          + ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t in (-T)..T, LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
              * LSeries g ((σ : ℂ) + (t : ℝ) * I)
              * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖ := by
    have := norm_add_le ((∑ n ∈ Finset.Icc 1 (min (MA * (MB * Mg)) N), c n)
        - ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
          LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
            * LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)))
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
        LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
          * LSeries g ((σ : ℂ) + (t : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)))
    simpa using this
  linarith [hPerron, hscale, htri]

/-- **The Perron step of a triple convolution at the uniform-separation truncation error.**  The
universal law instantiated at the half-integer separation `|log(x/n)| ≥ 1/(2N+2)`. -/
theorem norm_sum_Icc_triple_of_analytic_le {A B g : ℕ → ℂ} {MA MB Mg N : ℕ}
    (hAsupp : ∀ n : ℕ, A n ≠ 0 → n ∈ Finset.Icc 1 MA)
    (hBsupp : ∀ n : ℕ, B n ≠ 0 → n ∈ Finset.Icc 1 MB)
    (hgsupp : ∀ n : ℕ, g n ≠ 0 → n ∈ Finset.Icc 1 Mg)
    (hN : 1 ≤ N) {Bc P σ t₀ : ℝ}
    (hBc : ∀ n, ‖(LSeries.convolution A (LSeries.convolution B g)) n‖ ≤ Bc)
    (hσ : 1 ≤ σ) (ht₀ : 1 ≤ t₀) (K : ℕ)
    (hP : (∫ t in (-(t₀ * 2 ^ K))..(t₀ * 2 ^ K),
        ‖LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
            * LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
                / ((σ : ℂ) + (t : ℝ) * I))‖) ≤ P) :
    ‖∑ n ∈ Finset.Icc 1 (min (MA * (MB * Mg)) N),
        (LSeries.convolution A (LSeries.convolution B g)) n‖
      ≤ 2 * ((N : ℝ) + 1) * Bc * (((N : ℝ) + 1 / 2)) ^ σ
              * (1 + Real.log ((MA * (MB * Mg) : ℕ) : ℝ)) / (Real.pi * (t₀ * 2 ^ K))
          + (1 / (2 * Real.pi)) * P := by
  have ht₀0 : (0 : ℝ) < t₀ := by linarith
  have hT : (0 : ℝ) < t₀ * 2 ^ K := by positivity
  refine norm_sum_Icc_triple_of_error_and_analytic_le hAsupp hBsupp hgsupp (by linarith) K ?_ hP
  exact norm_sum_Icc_sub_perron_integral_le
    (c := LSeries.convolution A (LSeries.convolution B g)) (M := MA * (MB * Mg)) (N := N)
    hN hBc (σ := σ) (T := t₀ * 2 ^ K) hσ hT

/-- **The Perron step of a triple convolution at the near-diagonal truncation error.**  The universal
law instantiated at the exact local behaviour of the logarithm: the factor `2(N+1)` of the
uniform-separation error is replaced by the two harmonic sums `5(1 + log M) + 4(1 + log N)`, and the
lower bound on `N` is no longer needed. -/
theorem norm_sum_Icc_triple_of_analytic_near_le {A B g : ℕ → ℂ} {MA MB Mg N : ℕ}
    (hAsupp : ∀ n : ℕ, A n ≠ 0 → n ∈ Finset.Icc 1 MA)
    (hBsupp : ∀ n : ℕ, B n ≠ 0 → n ∈ Finset.Icc 1 MB)
    (hgsupp : ∀ n : ℕ, g n ≠ 0 → n ∈ Finset.Icc 1 Mg)
    {Bc P σ t₀ : ℝ}
    (hBc : ∀ n, ‖(LSeries.convolution A (LSeries.convolution B g)) n‖ ≤ Bc)
    (hσ : 1 ≤ σ) (ht₀ : 1 ≤ t₀) (K : ℕ)
    (hP : (∫ t in (-(t₀ * 2 ^ K))..(t₀ * 2 ^ K),
        ‖LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
            * LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
                / ((σ : ℂ) + (t : ℝ) * I))‖) ≤ P) :
    ‖∑ n ∈ Finset.Icc 1 (min (MA * (MB * Mg)) N),
        (LSeries.convolution A (LSeries.convolution B g)) n‖
      ≤ Bc * (((N : ℝ) + 1 / 2)) ^ σ
              * (5 * (1 + Real.log ((MA * (MB * Mg) : ℕ) : ℝ)) + 4 * (1 + Real.log N))
              / (Real.pi * (t₀ * 2 ^ K))
          + (1 / (2 * Real.pi)) * P := by
  have ht₀0 : (0 : ℝ) < t₀ := by linarith
  have hT : (0 : ℝ) < t₀ * 2 ^ K := by positivity
  refine norm_sum_Icc_triple_of_error_and_analytic_le hAsupp hBsupp hgsupp (by linarith) K ?_ hP
  exact norm_sum_Icc_sub_perron_integral_near_le
    (c := LSeries.convolution A (LSeries.convolution B g)) (M := MA * (MB * Mg)) (N := N)
    hBc (σ := σ) (T := t₀ * 2 ^ K) hσ hT

/-- **The partial sum of a triple convolution, through the mean-square analytic bound.**  The universal
law at the symmetric mean-square estimate of the vertical integral. -/
theorem norm_sum_Icc_triple_le {A B g : ℕ → ℂ} {MA MB Mg N : ℕ}
    (hAsupp : ∀ n : ℕ, A n ≠ 0 → n ∈ Finset.Icc 1 MA)
    (hAprime : ∀ n ∈ Finset.Icc 1 MA, A n ≠ 0 → n.Prime)
    (hBsupp : ∀ n : ℕ, B n ≠ 0 → n ∈ Finset.Icc 1 MB)
    (hBprime : ∀ n ∈ Finset.Icc 1 MB, B n ≠ 0 → n.Prime)
    (hgsupp : ∀ n : ℕ, g n ≠ 0 → n ∈ Finset.Icc 1 Mg)
    (hN : 1 ≤ N)
    {Bc V σ t₀ : ℝ}
    (hBc : ∀ n, ‖(LSeries.convolution A (LSeries.convolution B g)) n‖ ≤ Bc) (hV : 0 ≤ V)
    (hσ : 1 ≤ σ) (ht₀ : 1 ≤ t₀)
    (zA YA zB YB : ℕ) (hYA : 1 ≤ YA) (hYzA : YA ≤ zA) (hzA : 2 ≤ zA) (hlogA : 0 < Real.log YA)
    (hYB : 1 ≤ YB) (hYzB : YB ≤ zB) (hzB : 2 ≤ zB) (hlogB : 0 < Real.log YB) (K : ℕ)
    (hgV : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K → ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V) :
    ‖∑ n ∈ Finset.Icc 1 (min (MA * (MB * Mg)) N),
        (LSeries.convolution A (LSeries.convolution B g)) n‖
      ≤ 2 * ((N : ℝ) + 1) * Bc * (((N : ℝ) + 1 / 2)) ^ σ
              * (1 + Real.log ((MA * (MB * Mg) : ℕ) : ℝ)) / (Real.pi * (t₀ * 2 ^ K))
          + (1 / (2 * Real.pi))
              * (2 * perronVerticalProductBound A B (Finset.Icc 1 MA) (Finset.Icc 1 MB) σ
                    ((N : ℝ) + 1 / 2) t₀ V zA YA zB YB K
                  + (V * ((N : ℝ) + 1 / 2) ^ σ / σ)
                      * (Real.sqrt (sieveMeanSquareConst A (Finset.Icc 1 MA) σ YA
                            + sieveMeanSquareRate A (Finset.Icc 1 MA) σ zA YA * t₀)
                          * Real.sqrt (sieveMeanSquareConst B (Finset.Icc 1 MB) σ YB
                            + sieveMeanSquareRate B (Finset.Icc 1 MB) σ zB YB * t₀))) := by
  have hA0 : (0 : ℕ) ∉ Finset.Icc 1 MA := by simp
  have hB0 : (0 : ℕ) ∉ Finset.Icc 1 MB := by simp
  have hg0 : (0 : ℕ) ∉ Finset.Icc 1 Mg := by simp
  have hN0 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx : (0 : ℝ) < (N : ℝ) + 1 / 2 := by linarith
  refine norm_sum_Icc_triple_of_analytic_le hAsupp hBsupp hgsupp hN hBc hσ ht₀ K ?_
  exact integral_symm_norm_perron_triple_le hA0 hAsupp hAprime hB0 hBsupp hBprime
    (by linarith) hx ht₀ hV (continuous_LSeries_line_of_support hg0 hgsupp σ)
    zA YA zB YB hYA hYzA hzA hlogA hYB hYzB hzB hlogB K hgV

/-- **The partial sum of a triple convolution at the near-diagonal truncation error.**  The same
mean-square analytic bound, with the truncation error freed of its factor `N`; the height therefore
no longer has to grow with the length of the sum. -/
theorem norm_sum_Icc_triple_near_le {A B g : ℕ → ℂ} {MA MB Mg N : ℕ}
    (hAsupp : ∀ n : ℕ, A n ≠ 0 → n ∈ Finset.Icc 1 MA)
    (hAprime : ∀ n ∈ Finset.Icc 1 MA, A n ≠ 0 → n.Prime)
    (hBsupp : ∀ n : ℕ, B n ≠ 0 → n ∈ Finset.Icc 1 MB)
    (hBprime : ∀ n ∈ Finset.Icc 1 MB, B n ≠ 0 → n.Prime)
    (hgsupp : ∀ n : ℕ, g n ≠ 0 → n ∈ Finset.Icc 1 Mg)
    {Bc V σ t₀ : ℝ}
    (hBc : ∀ n, ‖(LSeries.convolution A (LSeries.convolution B g)) n‖ ≤ Bc) (hV : 0 ≤ V)
    (hσ : 1 ≤ σ) (ht₀ : 1 ≤ t₀)
    (zA YA zB YB : ℕ) (hYA : 1 ≤ YA) (hYzA : YA ≤ zA) (hzA : 2 ≤ zA) (hlogA : 0 < Real.log YA)
    (hYB : 1 ≤ YB) (hYzB : YB ≤ zB) (hzB : 2 ≤ zB) (hlogB : 0 < Real.log YB) (K : ℕ)
    (hgV : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K → ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V) :
    ‖∑ n ∈ Finset.Icc 1 (min (MA * (MB * Mg)) N),
        (LSeries.convolution A (LSeries.convolution B g)) n‖
      ≤ Bc * (((N : ℝ) + 1 / 2)) ^ σ
              * (5 * (1 + Real.log ((MA * (MB * Mg) : ℕ) : ℝ)) + 4 * (1 + Real.log N))
              / (Real.pi * (t₀ * 2 ^ K))
          + (1 / (2 * Real.pi))
              * (2 * perronVerticalProductBound A B (Finset.Icc 1 MA) (Finset.Icc 1 MB) σ
                    ((N : ℝ) + 1 / 2) t₀ V zA YA zB YB K
                  + (V * ((N : ℝ) + 1 / 2) ^ σ / σ)
                      * (Real.sqrt (sieveMeanSquareConst A (Finset.Icc 1 MA) σ YA
                            + sieveMeanSquareRate A (Finset.Icc 1 MA) σ zA YA * t₀)
                          * Real.sqrt (sieveMeanSquareConst B (Finset.Icc 1 MB) σ YB
                            + sieveMeanSquareRate B (Finset.Icc 1 MB) σ zB YB * t₀))) := by
  have hA0 : (0 : ℕ) ∉ Finset.Icc 1 MA := by simp
  have hB0 : (0 : ℕ) ∉ Finset.Icc 1 MB := by simp
  have hg0 : (0 : ℕ) ∉ Finset.Icc 1 Mg := by simp
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hx : (0 : ℝ) < (N : ℝ) + 1 / 2 := by linarith
  refine norm_sum_Icc_triple_of_analytic_near_le hAsupp hBsupp hgsupp hBc hσ ht₀ K ?_
  exact integral_symm_norm_perron_triple_le hA0 hAsupp hAprime hB0 hBsupp hBprime
    (by linarith) hx ht₀ hV (continuous_LSeries_line_of_support hg0 hgsupp σ)
    zA YA zB YB hYA hYzA hzA hlogA hYB hYzB hzB hlogB K hgV

/-- **The partial sum of a triple convolution at per-block sieve levels and the near-diagonal
truncation error.**  Both improvements at once: the level is no longer forced to be bounded, and the
height no longer has to grow with the length of the sum. -/
theorem norm_sum_Icc_triple_block_near_le {A B g : ℕ → ℂ} {MA MB Mg N : ℕ}
    (hAsupp : ∀ n : ℕ, A n ≠ 0 → n ∈ Finset.Icc 1 MA)
    (hAprime : ∀ n ∈ Finset.Icc 1 MA, A n ≠ 0 → n.Prime)
    (hBsupp : ∀ n : ℕ, B n ≠ 0 → n ∈ Finset.Icc 1 MB)
    (hBprime : ∀ n ∈ Finset.Icc 1 MB, B n ≠ 0 → n.Prime)
    (hgsupp : ∀ n : ℕ, g n ≠ 0 → n ∈ Finset.Icc 1 Mg)
    {Bc V σ t₀ : ℝ}
    (hBc : ∀ n, ‖(LSeries.convolution A (LSeries.convolution B g)) n‖ ≤ Bc) (hV : 0 ≤ V)
    (hσ : 1 ≤ σ) (ht₀ : 1 ≤ t₀)
    (ZA YlA ZB YlB : ℕ → ℕ)
    (hYA : ∀ j, 1 ≤ YlA j) (hYzA : ∀ j, YlA j ≤ ZA j) (hzA : ∀ j, 2 ≤ ZA j)
    (hlogA : ∀ j, 0 < Real.log (YlA j))
    (hYB : ∀ j, 1 ≤ YlB j) (hYzB : ∀ j, YlB j ≤ ZB j) (hzB : ∀ j, 2 ≤ ZB j)
    (hlogB : ∀ j, 0 < Real.log (YlB j)) (K : ℕ)
    (hgV : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K → ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V) :
    ‖∑ n ∈ Finset.Icc 1 (min (MA * (MB * Mg)) N),
        (LSeries.convolution A (LSeries.convolution B g)) n‖
      ≤ Bc * (((N : ℝ) + 1 / 2)) ^ σ
              * (5 * (1 + Real.log ((MA * (MB * Mg) : ℕ) : ℝ)) + 4 * (1 + Real.log N))
              / (Real.pi * (t₀ * 2 ^ K))
          + (1 / (2 * Real.pi))
              * (2 * perronVerticalAffineProductBound σ ((N : ℝ) + 1 / 2) t₀ V
                    (blockAffineConst A MA σ ZA YlA) (blockAffineRate A MA σ ZA YlA)
                    (blockAffineConst B MB σ ZB YlB) (blockAffineRate B MB σ ZB YlB) K
                  + (V * ((N : ℝ) + 1 / 2) ^ σ / σ)
                      * (Real.sqrt (blockAffineConst A MA σ ZA YlA
                            + blockAffineRate A MA σ ZA YlA * t₀)
                          * Real.sqrt (blockAffineConst B MB σ ZB YlB
                            + blockAffineRate B MB σ ZB YlB * t₀))) := by
  have hg0 : (0 : ℕ) ∉ Finset.Icc 1 Mg := by simp
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hx : (0 : ℝ) < (N : ℝ) + 1 / 2 := by linarith
  refine norm_sum_Icc_triple_of_analytic_near_le hAsupp hBsupp hgsupp hBc hσ ht₀ K ?_
  exact integral_symm_norm_perron_triple_block_le hAsupp hAprime hBsupp hBprime
    (by linarith) hx ht₀ hV (continuous_LSeries_line_of_support hg0 hgsupp σ)
    ZA YlA ZB YlB hYA hYzA hzA hlogA hYB hYzB hzB hlogB K hgV

end RHTower.Sieve
end
