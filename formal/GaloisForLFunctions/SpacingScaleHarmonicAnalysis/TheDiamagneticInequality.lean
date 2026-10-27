import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheStabilityLawAtTheSpacingScale
import GaloisForLFunctions.RHTower.WeilMarkovPoleCapacity

/-!
# The diamagnetic inequality

A sign gauge twists the prime place by `ω(k)`, `|ω(k)| ≤ 1`, and leaves the archimedean place
alone. The archimedean form is a Dirichlet form — its Lévy energy decreases under the normal
contraction `f ↦ |f|` — and the prime place enters Weil's form with a positive kernel. Together:

* **Diamagnetic inequality** (`diamagnetic_inequality`): for every real `C²` compactly supported
  test `f` and every twist `|ω(k)| ≤ 1`,
  `archForm f − twistedPrimeSum ω f ≥ levyMarkovForm |f|`,
  where `levyMarkovForm h = 2θ′(0)‖h‖² + levyEnergy h − primeSum h` is the Markov form of `ζ` in
  Lévy form (`levyMarkovForm_eq_markovEnergy`), defined for every real function.
* **Atomic tests are closed under `|·|`** (`abs_atomicTest`): below the spacing, with a nonnegative
  bump, `|f_x| = f_{|x|}`.
* **`ζ` is the ground state of its gauge orbit** (`twinMarkov_atomicTest_ge_abs`,
  `twinMarkov_ge_of_markov_ge`): on atomic tests below the spacing, every twist dominates `ζ` at
  `|x|`, so every lower bound `M ≥ κ‖f‖²` for `ζ` holds for every twist.

As in gauge theory (Kato's inequality, the diamagnetic inequality for magnetic Schrödinger
operators), the zero field has the lowest ground energy. Consequently no form margin in `ζ`'s
favour can come from the archimedean-minus-prime form on a family closed under `|·|`: the margin
must come from the pole term, the one anti-Markovian term (`RHTower.WeilMarkovPole.pole_le_pole_abs`),
or from families that are not closed under `|·|` — signed bumps, or overlapping atoms.
-/

noncomputable section

open MeasureTheory Finset RHTower
open scoped Real

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics

/-! ### The Lévy form of the Markov form -/

/-- The **Lévy–Markov form** `2θ′(0)‖h‖² + levyEnergy h − primeSum h` of a real function. -/
def levyMarkovForm (h : ℝ → ℝ) : ℝ :=
  2 * gammaHardyPhaseRate 0 * (∫ u, h u ^ 2) + levyEnergy h - primeSum h

/-- On `C²` compactly supported tests the Lévy–Markov form is the Markov form. -/
theorem levyMarkovForm_eq_markovEnergy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    levyMarkovForm f = markovEnergy (fun u => (f u : ℂ)) := by
  rw [markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, archForm_eq_levyEnergy hf hfc,
    levyMarkovForm]

/-! ### The archimedean place is a Dirichlet form -/

/-- **Normal contraction lowers the Lévy energy**: `levyEnergy |f| ≤ levyEnergy f`. -/
theorem levyEnergy_abs_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    levyEnergy (fun u => |f u|) ≤ levyEnergy f := by
  have hpt : ∀ y : ℝ, ∫ u, (|f u| - |f (u + y)|) ^ 2 ≤ ∫ u, (f u - f (u + y)) ^ 2 :=
    RHTower.WeilMarkovPole.integral_abs_sub_shift_sq_le hf.continuous hfc
  unfold levyEnergy
  refine integral_mono_of_nonneg (levyIntegrand_nonneg _) (integrableOn_levyIntegrand hf hfc) ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono fun y hy => ?_
  exact mul_le_mul_of_nonneg_left (hpt y) (archLevyDensity_pos hy).le

/-! ### The prime place is a positive kernel -/

/-- A compactly supported function is moved off itself by every large shift. -/
theorem exists_shift_mul_eq_zero {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ a : ℝ, R < |a| → ∀ t, f t * f (t + a) = 0 := by
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  refine ⟨2 * max R 0, by positivity, fun a ha t => ?_⟩
  by_contra hne
  have h1 : f t ≠ 0 := left_ne_zero_of_mul hne
  have h2 : f (t + a) ≠ 0 := right_ne_zero_of_mul hne
  have ht := hR (subset_tsupport f h1)
  have hta := hR (subset_tsupport f h2)
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at ht hta
  have : |a| ≤ |t + a| + |t| := by
    calc |a| = |(t + a) - t| := by ring_nf
      _ ≤ |t + a| + |t| := abs_sub _ _
  have hm : R ≤ max R 0 := le_max_left _ _
  linarith

/-- The prime terms of a compactly supported test vanish beyond a finite range of orders. -/
theorem exists_primeTerms_eq_zero {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    ∃ K : ℕ, ∀ k, K ≤ k → ∀ t, f t * f (t - Real.log k) = 0 ∧ f t * f (t + Real.log k) = 0 := by
  obtain ⟨R, hR0, hR⟩ := exists_shift_mul_eq_zero hfc
  refine ⟨⌈Real.exp (R + 1)⌉₊, fun k hk t => ?_⟩
  have hk' : Real.exp (R + 1) ≤ k := (Nat.ceil_le).mp hk
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos _) hk'
  have hlog : R < Real.log k := by
    have := Real.log_le_log (Real.exp_pos _) hk'
    rw [Real.log_exp] at this
    linarith
  have hlog0 : 0 ≤ Real.log k := by linarith
  refine ⟨?_, hR _ (by rw [abs_of_nonneg hlog0]; exact hlog) t⟩
  have := hR (-Real.log k) (by rw [abs_neg, abs_of_nonneg hlog0]; exact hlog) t
  rwa [← sub_eq_add_neg] at this

/-- **The twisted prime sum is dominated by the prime sum of `|f|`** for every twist `|ω| ≤ 1`. -/
theorem twistedPrimeSum_le_primeSum_abs {ω : ArithmeticFunction ℝ} (hω : ∀ k, |ω k| ≤ 1)
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    twistedPrimeSum ω f ≤ primeSum (fun u => |f u|) := by
  obtain ⟨K, hK⟩ := exists_primeTerms_eq_zero hfc
  have hint : ∀ a : ℝ, Integrable fun t => f t * f (t + a) := fun a =>
    (hf.mul (hf.comp (continuous_add_const a))).integrable_of_hasCompactSupport hfc.mul_right
  have hint' : ∀ a : ℝ, Integrable fun t => |f t| * |f (t + a)| := fun a => by
    simpa [abs_mul] using (hint a).abs
  have hshift : ∀ (a : ℝ), (fun t => f t * f (t - a)) = fun t => f t * f (t + -a) := fun a => by
    funext t; rw [sub_eq_add_neg]
  -- both sums are finite
  have hvan1 : ∀ k ∉ range K, ω k * vonMangoldtAtom k *
      ((∫ t, f t * f (t - Real.log k)) + ∫ t, f t * f (t + Real.log k)) = 0 := by
    intro k hk
    have hk' : K ≤ k := by simpa using hk
    simp [fun t => (hK k hk' t).1, fun t => (hK k hk' t).2]
  have hvan2 : ∀ k ∉ range K, vonMangoldtAtom k *
      ((∫ t, |f t| * |f (t - Real.log k)|) + ∫ t, |f t| * |f (t + Real.log k)|) = 0 := by
    intro k hk
    have hk' : K ≤ k := by simpa using hk
    have e1 : ∀ t, |f t| * |f (t - Real.log k)| = 0 := fun t => by
      rw [← abs_mul, (hK k hk' t).1, abs_zero]
    have e2 : ∀ t, |f t| * |f (t + Real.log k)| = 0 := fun t => by
      rw [← abs_mul, (hK k hk' t).2, abs_zero]
    simp [e1, e2]
  rw [twistedPrimeSum, primeSum, tsum_eq_sum hvan1, tsum_eq_sum hvan2]
  refine sum_le_sum fun k _ => ?_
  have hΛ : 0 ≤ vonMangoldtAtom k := by
    unfold vonMangoldtAtom
    split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    · exact le_rfl
  have hA : |∫ t, f t * f (t - Real.log k)| ≤ ∫ t, |f t| * |f (t - Real.log k)| := by
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    simp only [abs_mul]
  have hB : |∫ t, f t * f (t + Real.log k)| ≤ ∫ t, |f t| * |f (t + Real.log k)| := by
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    simp only [abs_mul]
  set A := (∫ t, f t * f (t - Real.log k)) + ∫ t, f t * f (t + Real.log k)
  have hAB : |A| ≤ (∫ t, |f t| * |f (t - Real.log k)|) + ∫ t, |f t| * |f (t + Real.log k)| :=
    (abs_add_le _ _).trans (add_le_add hA hB)
  calc ω k * vonMangoldtAtom k * A ≤ |ω k * vonMangoldtAtom k * A| := le_abs_self _
    _ = |ω k| * vonMangoldtAtom k * |A| := by rw [abs_mul, abs_mul, abs_of_nonneg hΛ]
    _ ≤ 1 * vonMangoldtAtom k * |A| := by gcongr; exact hω k
    _ ≤ vonMangoldtAtom k *
          ((∫ t, |f t| * |f (t - Real.log k)|) + ∫ t, |f t| * |f (t + Real.log k)|) := by
        rw [one_mul]; exact mul_le_mul_of_nonneg_left hAB hΛ

/-! ### The diamagnetic inequality -/

/-- **The diamagnetic inequality**: for every real `C²` compactly supported `f` and every twist
`|ω| ≤ 1`, `archForm f − twistedPrimeSum ω f ≥ levyMarkovForm |f|`. -/
theorem diamagnetic_inequality {ω : ArithmeticFunction ℝ} (hω : ∀ k, |ω k| ≤ 1) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    levyMarkovForm (fun u => |f u|) ≤ archForm f - twistedPrimeSum ω f := by
  rw [archForm_eq_levyEnergy hf hfc, levyMarkovForm]
  have hsq : ∫ u, |f u| ^ 2 = ∫ u, f u ^ 2 := by simp only [sq_abs]
  rw [hsq]
  have h1 := levyEnergy_abs_le hf hfc
  have h2 := twistedPrimeSum_le_primeSum_abs hω hf.continuous hfc
  linarith

/-! ### Atomic tests and the ground state -/

/-- A finite sum whose terms pairwise multiply to zero has `|Σ t| = Σ |t|`. -/
theorem abs_sum_eq_sum_abs_of_mul_eq_zero {s : Finset ℕ} {t : ℕ → ℝ}
    (h : ∀ m ∈ s, ∀ n ∈ s, m ≠ n → t m * t n = 0) : |∑ n ∈ s, t n| = ∑ n ∈ s, |t n| := by
  by_cases hex : ∃ n ∈ s, t n ≠ 0
  · obtain ⟨n, hn, hne⟩ := hex
    have hzero : ∀ m ∈ s, m ≠ n → t m = 0 := fun m hm hmn =>
      (mul_eq_zero.mp (h m hm n hn hmn)).resolve_right hne
    rw [sum_eq_single n (fun m hm hmn => hzero m hm hmn) (fun h' => absurd hn h'),
      sum_eq_single n (fun m hm hmn => by rw [hzero m hm hmn, abs_zero]) (fun h' => absurd hn h')]
  · push Not at hex
    rw [sum_eq_zero hex, sum_eq_zero fun n hn => by rw [hex n hn, abs_zero], abs_zero]

/-- **Atomic tests are closed under `|·|`**: below the spacing, with a nonnegative bump,
`|f_x| = f_{|x|}`. -/
theorem abs_atomicTest {g : ℝ → ℝ} {w : ℝ} (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hg0 : ∀ u, 0 ≤ g u) {N : ℕ} (hw : w < atomSpacing N) (x : ℕ → ℝ) (u : ℝ) :
    |atomicTest N x g u| = atomicTest N (fun n => |x n|) g u := by
  unfold atomicTest
  rw [abs_sum_eq_sum_abs_of_mul_eq_zero fun m hm n hn hmn => ?_]
  · exact sum_congr rfl fun n _ => by rw [abs_mul, abs_of_nonneg (hg0 _)]
  · have := bump_mul_eq_zero hgsupp hw (mem_Icc.mp hm).1 (mem_Icc.mp hn).1
      ((min_le_left _ _).trans (mem_Icc.mp hm).2) hmn u
    rw [show x m * g (u - Real.log m) * (x n * g (u - Real.log n)) =
      x m * x n * (g (u - Real.log m) * g (u - Real.log n)) by ring, this, mul_zero]

/-- **`ζ` is the ground state of its gauge orbit on atomic tests**: below the spacing, with a
nonnegative bump, every twist `|ω| ≤ 1` satisfies `M_ω(f_x) ≥ M(f_{|x|})`, and
`‖f_{|x|}‖ = ‖f_x‖`. -/
theorem twinMarkov_atomicTest_ge_abs {ω : ArithmeticFunction ℝ} (hω : ∀ k, |ω k| ≤ 1)
    {g : ℝ → ℝ} {w : ℝ} (hg : ContDiff ℝ 2 g) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hg0 : ∀ u, 0 ≤ g u) {N : ℕ} (hw : w < atomSpacing N) (x : ℕ → ℝ) :
    markovEnergy (fun u => (atomicTest N (fun n => |x n|) g u : ℂ)) ≤
      archForm (atomicTest N x g) - twistedPrimeSum ω (atomicTest N x g) := by
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  have h := diamagnetic_inequality hω hf hfc
  have habs : (fun u => |atomicTest N x g u|) = atomicTest N (fun n => |x n|) g :=
    funext (abs_atomicTest hgsupp hg0 hw x)
  rw [habs, levyMarkovForm_eq_markovEnergy (contDiff_atomicTest hg N _)
    (hasCompactSupport_atomicTest hgsupp N _)] at h
  exact h

/-- **Lower bounds pass from `ζ` to every twist**: if `M(f) ≥ κ‖f‖²` on all atomic tests of a bump
below the spacing, then `M_ω(f) ≥ κ‖f‖²` for every twist `|ω| ≤ 1`. -/
theorem twinMarkov_ge_of_markov_ge {ω : ArithmeticFunction ℝ} (hω : ∀ k, |ω k| ≤ 1)
    {g : ℝ → ℝ} {w : ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hg0 : ∀ u, 0 ≤ g u) {N : ℕ}
    (hw : w < atomSpacing N) {κ : ℝ}
    (hζ : ∀ y : ℕ → ℝ, κ * ∫ u, atomicTest N y g u ^ 2 ≤
      markovEnergy (fun u => (atomicTest N y g u : ℂ))) (x : ℕ → ℝ) :
    κ * ∫ u, atomicTest N x g u ^ 2 ≤
      archForm (atomicTest N x g) - twistedPrimeSum ω (atomicTest N x g) := by
  have hmass : ∫ u, atomicTest N (fun n => |x n|) g u ^ 2 = ∫ u, atomicTest N x g u ^ 2 := by
    rw [integral_atomicTest_sq hg hgc hgsupp hw, integral_atomicTest_sq hg hgc hgsupp hw]
    simp only [sq_abs]
  have := hζ fun n => |x n|
  rw [hmass] at this
  exact this.trans (twinMarkov_atomicTest_ge_abs hω hg hgsupp hg0 hw x)

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
