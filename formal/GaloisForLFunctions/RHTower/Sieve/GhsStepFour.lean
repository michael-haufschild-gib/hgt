import GaloisForLFunctions.RHTower.Sieve.GhsSummability
import GaloisForLFunctions.RHTower.Sieve.LorentzianLSeriesLine
import GaloisForLFunctions.RHTower.Sieve.EulerBoundLSeries
import GaloisForLFunctions.RHTower.Sieve.HalaszIntegralBound
import GaloisForLFunctions.HTGeometry.WeightedCauchySchwarz
import GaloisForLFunctions.HTGeometry.SmoothWeightInversion
/-!
# Step 4 of the Granville–Harper–Soundararajan argument, assembled

The smoothed sum of the threefold convolution the log recursion produces is a vertical integral of three
Dirichlet series against the Mellin transform of the cutoff.  One factor — the series of `f` itself — is
bounded pointwise by its Euler product; the kernel decays quadratically; the two prime weights are
Dirichlet polynomials whose Lorentzian mean squares the Selberg sieve controls.  The master inequality of
the three-factor integral then gives

`2π‖∑ₙ (a ⍟ (b ⍟ f))(n)w(n)‖ ≤ (1 + 1/(σ−1))e^{7/2} · C · 25π² · √(sieve a) · √(sieve b)`,

with `C` the quadratic-decay constant of the kernel and `sieve` the Selberg-sieve mean-square majorant of a
prime-supported polynomial on the line `Re s = σ`.

Every ingredient is unconditional and every one of them is a named theorem of the corpus: the Perron
identity for a triple convolution, absolute convergence of logarithmically bounded coefficients, the trivial
Euler bound, Cauchy–Schwarz against a decaying kernel, and the almost-diagonal mean value theorem with its
neighbour count discharged by the sieve.  What the argument still needs is a choice of the parameters
`σ, z, Y, N, H` and the arithmetic evaluation of the two sieve sums.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Finset GaloisForLFunctions.HTGeometry

/-- The Selberg-sieve majorant of the Lorentzian mean square of a prime-supported polynomial, with the
damping of the line `Re s = σ` carried inside the coefficients. -/
def sieveMeanSquare (a : ℕ → ℂ) (s : Finset ℕ) (σ : ℝ) (z Y : ℕ) : ℝ :=
  ∑ n ∈ s,
    (2 * ((n : ℝ) * (Real.exp (1 / (2 * Real.pi)) - Real.exp (-(1 / (2 * Real.pi)))) + 1)
        / Real.log Y
      + selbergFibreError z Y + (z : ℝ))
      * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2

/-- The prime-supported mean square on the Perron line, in the reciprocal form the Cauchy–Schwarz split
consumes. -/
theorem integral_lorentz_normSq_LSeries_le_sieveMeanSquare {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (hprime : ∀ n ∈ s, a n ≠ 0 → n.Prime) (σ : ℝ)
    (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y) :
    (∫ y : ℝ, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2 * (1 + y ^ 2)⁻¹)
      ≤ 25 * Real.pi ^ 2 * sieveMeanSquare a s σ z Y := by
  have h := integral_lorentz_normSq_LSeries_le_prime_sieve hs0 hsupp hprime σ z Y hY hYz hz hlog
  rw [sieveMeanSquare]
  simpa [div_eq_mul_inv] using h

/-- A finitely supported Dirichlet series is continuous on a vertical line. -/
theorem continuous_LSeries_line_of_support {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (σ : ℝ) :
    Continuous fun y : ℝ => LSeries a ((σ : ℂ) + (y : ℝ) * I) := by
  have heq : (fun y : ℝ => LSeries a ((σ : ℂ) + (y : ℝ) * I))
      = fun y : ℝ => logPoly (fun n => a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)) s
          (-y / (2 * Real.pi)) := by
    funext y
    exact LSeries_eq_logPoly_of_support hs0 hsupp σ y
  rw [heq]
  exact (continuous_logPoly _ s).comp (by fun_prop)

/-- The Dirichlet series of a bounded multiplicative function is continuous on a vertical line to the
right of `1`. -/
theorem continuous_LSeries_line_of_bounded {f : ℕ → ℂ} (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ}
    (hσ : 1 < σ) : Continuous fun y : ℝ => LSeries f ((σ : ℂ) + (y : ℝ) * I) := by
  have heq : (fun y : ℝ => LSeries f ((σ : ℂ) + (y : ℝ) * I))
      = fun y : ℝ => ∑' n : ℕ, twistedSummand f ((σ : ℂ) + (y : ℝ) * I) n := by
    funext y
    have hne : ((σ : ℂ) + (y : ℝ) * I) ≠ 0 := by
      intro h
      have hre : ((σ : ℂ) + (y : ℝ) * I).re = σ := by simp
      rw [h] at hre
      simp at hre
      linarith
    exact LSeries_eq_tsum_twistedSummand hne
  rw [heq]
  exact continuous_tsum_twistedSummand hbdd hσ

/-- **Step 4 of the Granville–Harper–Soundararajan argument, assembled.**  For a bounded multiplicative
`f`, the smoothed sum of the threefold convolution the log recursion produces obeys

`2π‖∑ₙ (a ⍟ (b ⍟ f))(n)w(n)‖ ≤ (1 + 1/(σ−1))e^{7/2} · C · 25π² · √(sieve a)·√(sieve b)`,

where `C` is the quadratic-decay constant of the smoothing kernel and the two sieve quantities are the
Selberg-sieve mean-square majorants of the two prime weights.  Every ingredient is unconditional: the
Perron identity, the Euler bound on the pointwise factor, Cauchy–Schwarz against the kernel, and GHS
Lemma 1 for the two prime-supported polynomials. -/
theorem norm_tsum_ghs_smoothWeight_le_of_kernelBound {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n) (hbdd : ∀ n, ‖f n‖ ≤ 1)
    (N₀ M : ℕ) {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {σ : ℝ} (hσ : 1 < σ)
    (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hCb : ∀ y : ℝ, ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
          ((σ : ℂ) + (y : ℝ) * I)‖ ≤ C * (1 + y ^ 2)⁻¹) :
      (2 * Real.pi) * ‖∑' n : ℕ,
            (LSeries.convolution (ghsOuter f N₀) (LSeries.convolution (ghsInner f M) f)) n
              * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)‖
        ≤ ((1 + 1 / (σ - 1)) * Real.exp (7 / 2)) * C
            * (Real.sqrt (25 * Real.pi ^ 2 * sieveMeanSquare (ghsOuter f N₀) (Finset.Icc 1 N₀) σ z Y)
              * Real.sqrt
                  (25 * Real.pi ^ 2 * sieveMeanSquare (ghsInner f M) (Finset.Icc 1 M) σ z Y)) := by
  classical
  set a : ℕ → ℂ := ghsOuter f N₀ with ha
  set b : ℕ → ℂ := ghsInner f M with hb
  set W : ℝ → ℂ := fun y =>
    mellin (fun x : ℝ => ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * I) with hW
  -- supports
  have hs0a : (0 : ℕ) ∉ Finset.Icc 1 N₀ := by simp
  have hs0b : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  have hsuppa : ∀ n : ℕ, a n ≠ 0 → n ∈ Finset.Icc 1 N₀ := fun n hn => ghsOuter_mem_Icc hn
  have hsuppb : ∀ n : ℕ, b n ≠ 0 → n ∈ Finset.Icc 1 M := fun n hn => ghsInner_mem_Icc hn
  have hprimea : ∀ n ∈ Finset.Icc 1 N₀, a n ≠ 0 → n.Prime := fun n _ hn => ghsOuter_support hn
  have hprimeb : ∀ n ∈ Finset.Icc 1 M, b n ≠ 0 → n.Prime := fun n _ hn => ghsInner_support hn
  -- the Perron identity
  have hperron := tsum_mul_smoothWeight_ghs_eq_integral hbdd N₀ M hN hH hσ
  have hnorm : (2 * Real.pi) * ‖∑' n : ℕ,
      (LSeries.convolution a (LSeries.convolution b f)) n
        * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)‖
      = ‖∫ y : ℝ, (LSeries a ((σ : ℂ) + (y : ℝ) * I) * LSeries b ((σ : ℂ) + (y : ℝ) * I)
            * LSeries f ((σ : ℂ) + (y : ℝ) * I)) * W y‖ := by
    rw [hW, ← hperron, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  rw [hnorm]
  -- the three factors and the kernel are measurable
  have hm1 : AEStronglyMeasurable (fun y : ℝ => LSeries a ((σ : ℂ) + (y : ℝ) * I)) volume :=
    (continuous_LSeries_line_of_support hs0a hsuppa σ).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun y : ℝ => LSeries b ((σ : ℂ) + (y : ℝ) * I)) volume :=
    (continuous_LSeries_line_of_support hs0b hsuppb σ).aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (fun y : ℝ => LSeries f ((σ : ℂ) + (y : ℝ) * I)) volume :=
    (continuous_LSeries_line_of_bounded hbdd hσ).aestronglyMeasurable
  have hmW : AEStronglyMeasurable W volume :=
    (verticalIntegrable_mellin_smoothWeight (σ := σ) hN hH (by linarith)).aestronglyMeasurable
  -- the master inequality
  have h1 : Integrable fun y : ℝ => ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2 * (1 + y ^ 2)⁻¹ :=
    integrable_lorentz_normSq_LSeries hs0a hsuppa σ
  have h2 : Integrable fun y : ℝ => ‖LSeries b ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2 * (1 + y ^ 2)⁻¹ :=
    integrable_lorentz_normSq_LSeries hs0b hsuppb σ
  have hmaster := norm_integral_mul_three_le_sup_mul_lorentz hm1 hm2 hm3 hmW
    (M := (1 + 1 / (σ - 1)) * Real.exp (7 / 2)) (C := C)
    (fun y => norm_LSeries_line_le_trivial hf1 hmul hbdd hσ y) (fun y => hCb y) h1 h2
  refine hmaster.trans ?_
  -- the two mean squares
  have hMnn : (0 : ℝ) ≤ (1 + 1 / (σ - 1)) * Real.exp (7 / 2) := by
    have h1' : 0 < σ - 1 := by linarith
    positivity
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hMnn hC0)
  have hb1 := integral_lorentz_normSq_LSeries_le_sieveMeanSquare hs0a hsuppa hprimea σ z Y
    hY hYz hz hlog
  have hb2 := integral_lorentz_normSq_LSeries_le_sieveMeanSquare hs0b hsuppb hprimeb σ z Y
    hY hYz hz hlog
  exact mul_le_mul (Real.sqrt_le_sqrt hb1) (Real.sqrt_le_sqrt hb2) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)

/-- **The GHS step-four bound with the kernel constant discharged.**  The instance at the Mellin kernel
bound, whose constant depends only on `N`, `H`, `σ`. -/
theorem exists_norm_tsum_ghs_smoothWeight_le {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n) (hbdd : ∀ n, ‖f n‖ ≤ 1)
    (N₀ M : ℕ) {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {σ : ℝ} (hσ : 1 < σ)
    (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y) :
    ∃ C : ℝ, 0 ≤ C ∧
      (2 * Real.pi) * ‖∑' n : ℕ,
            (LSeries.convolution (ghsOuter f N₀) (LSeries.convolution (ghsInner f M) f)) n
              * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)‖
        ≤ ((1 + 1 / (σ - 1)) * Real.exp (7 / 2)) * C
            * (Real.sqrt (25 * Real.pi ^ 2 * sieveMeanSquare (ghsOuter f N₀) (Finset.Icc 1 N₀) σ z Y)
              * Real.sqrt
                  (25 * Real.pi ^ 2 * sieveMeanSquare (ghsInner f M) (Finset.Icc 1 M) σ z Y)) := by
  obtain ⟨C, hC0, hCb⟩ :=
    exists_bound_mellin_smoothWeight_line hN hH (show (0 : ℝ) < σ by linarith)
  exact ⟨C, hC0, norm_tsum_ghs_smoothWeight_le_of_kernelBound hf1 hmul hbdd N₀ M hN hH hσ z Y hY
    hYz hz hlog hC0 hCb⟩

end RHTower.Sieve
