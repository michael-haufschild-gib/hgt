import GaloisForLFunctions.ArithmeticWeightTheory.TheEdgeDivisorOfAFibre
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The edge divisor of `ζ`

The edge divisor of a fibre is read by pretentious distances (`TheJumpLocusIsThePretentiousArchimedeanLine`,
`TheEdgeDivisorOfAFibre`). At the special fibre `x = 0` the terms become classical:
`pretTerm 0 τ p = 1 − cos(τ log p)` and `antiTerm 0 τ p = 1 + cos(τ log p)`.

**Theorem** (`riemannZeta_ne_zero_iff_not_antiPretentious`). For `τ ≠ 0`,

  `ζ(1 + iτ) ≠ 0  ⟺  Σ_p (1 + cos(τ log p))/p = ∞`:

non-vanishing on the edge is exactly the failure of `1` to pretend to be `−n^{iτ}`. A zero at
`1 + iτ` makes `|ζ(1 + δ + iτ)| = O(δ)`, an edge zero; conversely an edge zero forces `ζ(1 + iτ) = 0`
by continuity.

**Theorem** (`edgeDivisor_zeta`). With the analytic continuation of `ζ` the edge divisor of the
special fibre is a single simple pole at `1`: `1` pretends to be `n^{iτ}` exactly for `τ = 0`
(`Σ_p (1 − cos(τ log p))/p = ∞` for `τ ≠ 0`), and never to `−n^{iτ}`. The coinvariant jump of the
gauge family at `ζ` is one-dimensional; its location and order are fixed by the continuation of
`ζ` across `Re s = 1` and its non-vanishing there.
-/

open MeasureTheory Filter Topology Complex Asymptotics

noncomputable section

namespace GaloisForLFunctions.ArithmeticWeightTheory

open ArithmeticCorrelationGeometry PrimeTorusTheory

/-- At the trivial fibre the pretentious term is `1 − cos(τ log p)`. -/
theorem pretTerm_trivial (τ : ℝ) {p : ℕ} (hp : 0 < p) :
    pretTerm 0 τ p = 1 - Real.cos (τ * Real.log p) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold pretTerm
  rw [twist_trivial, mul_one, Complex.cpow_def_of_ne_zero hp0, ← Complex.natCast_log]
  have hz : ((Real.log p : ℝ) : ℂ) * -((τ : ℂ) * I) = ((-(τ * Real.log p) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [hz, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- At the trivial fibre the anti-pretentious term is `1 + cos(τ log p)`. -/
theorem antiTerm_trivial (τ : ℝ) {p : ℕ} (hp : 0 < p) :
    antiTerm 0 τ p = 1 + Real.cos (τ * Real.log p) := by
  unfold antiTerm; rw [pretTerm_trivial τ hp]; ring

theorem polePoint_zero (τ : ℝ) : polePoint 0 τ = 1 + (τ : ℂ) * I := by simp [polePoint]

theorem norm_polePoint_sub (δ τ : ℝ) (hδ : 0 ≤ δ) : ‖polePoint δ τ - polePoint 0 τ‖ = δ := by
  have : polePoint δ τ - polePoint 0 τ = (δ : ℂ) := by simp [polePoint]
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ]

theorem tendsto_polePoint (τ : ℝ) :
    Tendsto (fun δ : ℝ => polePoint δ τ) (𝓝[>] 0) (𝓝 (polePoint 0 τ)) := by
  have hc : Continuous fun δ : ℝ => polePoint δ τ := by unfold polePoint; fun_prop
  exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- **Edge non-vanishing is anti-pretension.** -/
theorem riemannZeta_ne_zero_iff_not_antiPretentious {τ : ℝ} (hτ : τ ≠ 0) :
    riemannZeta (1 + (τ : ℂ) * I) ≠ 0 ↔
      ¬ Summable fun p : Nat.Primes => antiTerm 0 τ p / (p : ℕ) := by
  have hs1 : polePoint 0 τ ≠ 1 := by
    rw [polePoint_zero]
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hτ this
  have hdiff : DifferentiableAt ℂ riemannZeta (polePoint 0 τ) := differentiableAt_riemannZeta hs1
  have heq : ∀ᶠ δ in 𝓝[>] (0 : ℝ), gaugeFibre 0 (polePoint δ τ) = riemannZeta (polePoint δ τ) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ0 : (0 : ℝ) < δ := hδ
    exact gaugeFibre_trivial (by simp; linarith)
  rw [← polePoint_zero, ← edgeZero_iff_antiPretentious]
  constructor
  · -- a nonzero value at `1 + iτ` is not an edge zero
    rintro hne ⟨C, hC⟩
    have hlim : Tendsto (fun δ : ℝ => ‖riemannZeta (polePoint δ τ)‖) (𝓝[>] 0)
        (𝓝 ‖riemannZeta (polePoint 0 τ)‖) :=
      (hdiff.continuousAt.tendsto.comp (tendsto_polePoint τ)).norm
    have hlimC : Tendsto (fun δ : ℝ => C * δ) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun δ : ℝ => C * δ) (𝓝 0) (𝓝 (C * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hle : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ‖riemannZeta (polePoint δ τ)‖ ≤ C * δ := by
      filter_upwards [hC, heq] with δ h1 h2
      rwa [h2] at h1
    exact hne (norm_le_zero_iff.mp (le_of_tendsto_of_tendsto hlim hlimC hle))
  · -- a zero at `1 + iτ` is an edge zero
    intro hnz
    by_contra hz
    apply hnz
    have hO := hdiff.hasDerivAt.isBigO_sub
    rw [hz] at hO
    simp only [sub_zero] at hO
    obtain ⟨C, hC⟩ := hO.bound
    have hpath := (tendsto_polePoint τ).eventually hC
    refine ⟨C, ?_⟩
    filter_upwards [hpath, heq, self_mem_nhdsWithin] with δ h1 h2 hδ
    have hδ0 : (0 : ℝ) < δ := hδ
    rw [h2, norm_polePoint_sub δ τ hδ0.le] at *
    exact h1

/-- **`ζ` never pretends to be `−n^{iτ}`**: `Σ_p (1 + cos(τ log p))/p = ∞` for every `τ`. -/
theorem not_summable_one_add_cos (τ : ℝ) :
    ¬ Summable fun p : Nat.Primes => (1 + Real.cos (τ * Real.log (p : ℕ))) / (p : ℕ) := by
  have hcongr : (fun p : Nat.Primes => (1 + Real.cos (τ * Real.log (p : ℕ))) / (p : ℕ)) =
      fun p : Nat.Primes => antiTerm 0 τ p / (p : ℕ) := by
    funext p; rw [antiTerm_trivial τ p.2.pos]
  rw [hcongr]
  by_cases hτ : τ = 0
  · subst hτ
    intro hA
    refine not_pretentious_and_antiPretentious 0 0 ⟨?_, hA⟩
    have h0 : ∀ p : Nat.Primes, pretTerm 0 0 p = 0 := fun p => by
      rw [pretTerm_trivial 0 p.2.pos]; simp
    simp [h0]
  · exact (riemannZeta_ne_zero_iff_not_antiPretentious hτ).mp
      (riemannZeta_ne_zero_of_one_le_re (by simp))

/-- **`1` pretends to be `n^{iτ}` only at `τ = 0`**: `Σ_p (1 − cos(τ log p))/p = ∞` for `τ ≠ 0`. -/
theorem not_summable_one_sub_cos {τ : ℝ} (hτ : τ ≠ 0) :
    ¬ Summable fun p : Nat.Primes => (1 - Real.cos (τ * Real.log (p : ℕ))) / (p : ℕ) := by
  have hcongr : (fun p : Nat.Primes => (1 - Real.cos (τ * Real.log (p : ℕ))) / (p : ℕ)) =
      fun p : Nat.Primes => pretTerm 0 τ p / (p : ℕ) := by
    funext p; rw [pretTerm_trivial τ p.2.pos]
  rw [hcongr, ← pole_iff_pretentious]
  rintro ⟨c, hc, hev⟩
  have hs1 : polePoint 0 τ ≠ 1 := by
    rw [polePoint_zero]
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hτ this
  have hcont := (differentiableAt_riemannZeta hs1).continuousAt
  have hlim : Tendsto (fun δ : ℝ => δ * ‖riemannZeta (polePoint δ τ)‖) (𝓝[>] 0)
      (𝓝 (0 * ‖riemannZeta (polePoint 0 τ)‖)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).mul (hcont.tendsto.comp (tendsto_polePoint τ)).norm
  rw [zero_mul] at hlim
  have heq : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      δ * ‖gaugeFibre 0 (polePoint δ τ)‖ = δ * ‖riemannZeta (polePoint δ τ)‖ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ0 : (0 : ℝ) < δ := hδ
    rw [gaugeFibre_trivial (by simp; linarith)]
  obtain ⟨δ, h1, h2⟩ := (hev.and ((hlim.eventually (gt_mem_nhds hc)).and heq)).exists
  rw [h2.2] at h1
  linarith [h2.1]

/-- **The edge divisor of `ζ`**: a pole at `1 + iτ` exactly for `τ = 0`, never a zero. -/
theorem edgeDivisor_zeta (τ : ℝ) :
    ((Summable fun p : Nat.Primes => pretTerm 0 τ p / (p : ℕ)) ↔ τ = 0) ∧
      ¬ Summable fun p : Nat.Primes => antiTerm 0 τ p / (p : ℕ) := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · by_contra hτ
    refine not_summable_one_sub_cos hτ (h.congr fun p => ?_)
    rw [pretTerm_trivial τ p.2.pos]
  · subst h
    have h0 : ∀ p : Nat.Primes, pretTerm 0 0 p = 0 := fun p => by
      rw [pretTerm_trivial 0 p.2.pos]; simp
    simp [h0]
  · intro hA
    refine not_summable_one_add_cos τ (hA.congr fun p => ?_)
    rw [antiTerm_trivial τ p.2.pos]

end GaloisForLFunctions.ArithmeticWeightTheory
