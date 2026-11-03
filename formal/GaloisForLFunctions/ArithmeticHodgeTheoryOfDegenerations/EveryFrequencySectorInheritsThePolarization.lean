import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonLayerIsGradedByFrequency
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheTwistedSectorInheritsThePolarization

/-!
# Every frequency sector inherits the polarization

Mechanism B on a twisted sector needs only one input: that the twist has a **scalar second order**,
i.e. every window `h` twisted by `χ` has second-order term `Λ ∫ e^{−(β+1)y} H²` with the same
`Λ`. Then the Gram matrices of an independent twisted family converge to `Λ A(G)` by polarization,
and for `Λ > 0` positive definiteness passes to the nearby fibres.

* **The scalar inheritance principle** (`tendsto_twistGram_of_scalar`,
  `twisted_sector_inherits_of_scalar`).
* **Frequency sectors** (`trig_twisted_sector_inherits`): every nonzero trigonometric twist
  `Σ_k a_k cos(2πnα_k)` with distinct frequency classes has the scalar second order
  `(βA_φ/(K∫φ²)) Σ_k a_k² · ½(ζ(β+1, u_k) + ζ(β+1, 1 − u_k)) > 0`, so its sector inherits the
  polarization, for rational and irrational frequencies alike.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23 Matrix
open scoped ComplexConjugate ComplexOrder

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri HTGeometry
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ : ℝ → ℝ} {A : ℝ} {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
/-- **Gram limits of a twist with a scalar second order**: `Λ A(G)`. -/
theorem tendsto_twistGram_of_scalar (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {β Λ : ℝ} {χ : ℕ → ℝ} {c : ℕ → ℝ}
    (hc1 : ∀ N, 1 ≤ c N)
    (hlim : ∀ w : ℝ → ℝ, ContDiff ℝ 2 w → (∀ y, y ∉ Set.Icc (-A) 0 → w y = 0) →
      Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights w χ N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2)) atTop
        (𝓝 (Λ * ∫ y, Real.exp (-((β + 1) * y)) * halfWeight w y ^ 2)))
    {g : κ → ℝ → ℝ} (hg : ∀ j, ContDiff ℝ 2 (g j))
    (hgsupp : ∀ j y, y ∉ Set.Icc (-A) 0 → g j y = 0) (j j' : κ) :
    Tendsto (fun N : ℕ => ((((c N)⁻¹ / ∫ u, atomDilate φ (c N / N) u ^ 2 : ℝ) : ℂ) •
      twistGram φ g χ (c N) N) j j') atTop (𝓝 (twistLimitGram β Λ g j j')) := by
  have hp' := hlim _ ((hg j).add (hg j')) (fun y hy => by simp [hgsupp j y hy, hgsupp j' y hy])
  have hm' := hlim _ ((hg j).sub (hg j')) (fun y hy => by simp [hgsupp j y hy, hgsupp j' y hy])
  have hreal := (hp'.sub hm').div_const 4
  have hval : (Λ * (∫ y, Real.exp (-((β + 1) * y)) * halfWeight (fun y => g j y + g j' y) y ^ 2) -
      Λ * ∫ y, Real.exp (-((β + 1) * y)) * halfWeight (fun y => g j y - g j' y) y ^ 2) / 4 =
      Λ * ∫ y, Real.exp (-((β + 1) * y)) * (halfWeight (g j) y * halfWeight (g j') y) := by
    have hpol := integral_polarize_of_window (A := A)
      (w := fun y => Real.exp (-((β + 1) * y))) (by fun_prop)
      (contDiff_halfWeight (hg j)).continuous (contDiff_halfWeight (hg j')).continuous
      (halfWeight_eq_zero_of_window (hgsupp j)) (halfWeight_eq_zero_of_window (hgsupp j'))
    rw [halfWeight_add, halfWeight_sub]
    beta_reduce at hpol ⊢
    rw [← hpol]
    ring
  rw [hval] at hreal
  have hgoal : twistLimitGram β Λ g j j' =
      ((Λ * ∫ y, Real.exp (-((β + 1) * y)) * (halfWeight (g j) y * halfWeight (g j') y) : ℝ) :
        ℂ) := by
    simp only [twistLimitGram, Matrix.smul_apply, smul_eq_mul, aliasGram]
    push_cast
    ring
  rw [hgoal]
  refine ((Complex.continuous_ofReal.tendsto _).comp hreal).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hc0 : 0 < c N := by linarith [hc1 N]
  simp only [Function.comp_apply, Matrix.smul_apply, smul_eq_mul]
  rw [twistGram_apply hφ hφsupp g _ hc0 hN, ← Complex.ofReal_mul]
  congr 1
  ring

/-- **The scalar inheritance principle**: a twist with a positive scalar second order inherits the
polarization on every independent family. -/
theorem twisted_sector_inherits_of_scalar (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {β Λ : ℝ} (hΛ : 0 < Λ) {χ : ℕ → ℝ}
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    (hlim : ∀ w : ℝ → ℝ, ContDiff ℝ 2 w → (∀ y, y ∉ Set.Icc (-A) 0 → w y = 0) →
      Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights w χ N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2)) atTop
        (𝓝 (Λ * ∫ y, Real.exp (-((β + 1) * y)) * halfWeight w y ^ 2)))
    {g : κ → ℝ → ℝ} (hg : ∀ j, ContDiff ℝ 2 (g j))
    (hgsupp : ∀ j y, y ∉ Set.Icc (-A) 0 → g j y = 0) (hlin : LinearIndependent ℝ g) :
    ∀ᶠ N : ℕ in atTop, ∀ x : κ → ℂ, x ≠ 0 → 0 < hermQuad (twistGram φ g χ (c N) N) x := by
  have hpos : ∀ x : κ → ℂ, x ≠ 0 → 0 < hermQuad (twistLimitGram β Λ g) x := fun x hx => by
    unfold twistLimitGram
    rw [HTGeometry.hermQuad_smul]
    have hA' := aliasGram_posDef β hg hgsupp hlin
    have : 0 < hermQuad (aliasGram β g) x := by
      have h1 := (Matrix.posDef_iff_dotProduct_mulVec.mp hA').2 hx
      simpa [hermQuad] using (Complex.lt_def.mp h1).1
    exact mul_pos hΛ this
  have hev := eventually_hermQuad_pos_of_tendsto (twistLimitGram_isHermitian β Λ g) hpos
    (tendsto_twistGram_of_scalar hφ hφsupp hc1 hlim hg hgsupp)
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1 x hx
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw : 0 < c N / N := div_pos (by linarith [hc1 N]) hN0
  have hs : 0 < (c N)⁻¹ / ∫ u, atomDilate φ (c N / N) u ^ 2 := by
    rw [integral_atomDilate_sq φ hw]
    have : 0 < c N := by linarith [hc1 N]
    positivity
  have := hN x hx
  rw [HTGeometry.hermQuad_smul] at this
  exact pos_of_mul_pos_right this hs.le

/-- **Every frequency sector inherits the polarization**: for a nonzero trigonometric twist with
distinct frequency classes, along the critical curve the Gram matrix of the complete family on an
independent twisted family is eventually positive definite. -/
theorem trig_twisted_sector_inherits {ι : Type*} [DecidableEq ι] (s : Finset ι) (a α : ι → ℝ)
    (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β Aφ : ℝ} (hβ : 0 < β) (hAφ : 0 < Aφ)
    (hT : Tendsto (fun x => x ^ β * ArithmeticDegenerationTheory.spectralTail φ x) atTop (𝓝 Aφ))
    {g : κ → ℝ → ℝ} (hg : ∀ j, ContDiff ℝ 2 (g j)) (hA : 0 ≤ A)
    (hgsupp : ∀ j y, y ∉ Set.Icc (-A) 0 → g j y = 0) (hlin : LinearIndependent ℝ g)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    (hsum : ∀ k ∈ s, ∀ l ∈ s, Real.sin (Real.pi * (α k + α l)) ≠ 0)
    (hdiff : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → Real.sin (Real.pi * (α k - α l)) ≠ 0)
    (hne : ∃ k ∈ s, a k ≠ 0) :
    ∀ᶠ N : ℕ in atTop, ∀ x : κ → ℂ, x ≠ 0 →
      0 < hermQuad (twistGram φ g (trigTwist s a α) (c N) N) x := by
  set S := ∑ k ∈ s, a k ^ 2 * ((hurwitzSum (β + 1) (Int.fract (α k)) +
    hurwitzSum (β + 1) (1 - Int.fract (α k))) / 2) with hS
  have hsin : ∀ k ∈ s, Real.sin (Real.pi * α k) ≠ 0 := fun k hk =>
    sin_pi_ne_zero_of_two (by rw [show 2 * α k = α k + α k by ring]; exact hsum k hk k hk)
  have hS0 : 0 < S := by
    obtain ⟨k₀, hk₀, ha₀⟩ := hne
    have hterm : ∀ k ∈ s, 0 ≤ a k ^ 2 * ((hurwitzSum (β + 1) (Int.fract (α k)) +
        hurwitzSum (β + 1) (1 - Int.fract (α k))) / 2) := fun k hk => by
      have hu0 := fract_pos_of_sin (hsin k hk)
      have hu1 := Int.fract_lt_one (α k)
      have h1 := one_le_hurwitzSum (k := β + 1) (by linarith) hu0 hu1.le
      have h2 := one_le_hurwitzSum (k := β + 1) (by linarith) (by linarith : 0 < 1 - Int.fract (α k))
        (by linarith : 1 - Int.fract (α k) ≤ 1)
      positivity
    have hpos₀ : 0 < a k₀ ^ 2 * ((hurwitzSum (β + 1) (Int.fract (α k₀)) +
        hurwitzSum (β + 1) (1 - Int.fract (α k₀))) / 2) := by
      have hu0 := fract_pos_of_sin (hsin k₀ hk₀)
      have hu1 := Int.fract_lt_one (α k₀)
      have h1 := one_le_hurwitzSum (k := β + 1) (by linarith) hu0 hu1.le
      have h2 := one_le_hurwitzSum (k := β + 1) (by linarith)
        (by linarith : 0 < 1 - Int.fract (α k₀)) (by linarith : 1 - Int.fract (α k₀) ≤ 1)
      have : 0 < a k₀ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 ha₀))
      positivity
    exact lt_of_lt_of_le hpos₀ (Finset.single_le_sum hterm hk₀)
  have hΛ : 0 < β * Aφ / (K * ∫ u, φ u ^ 2) * S := by positivity
  refine twisted_sector_inherits_of_scalar (β := β) hφ hφsupp hφ2 hΛ hc1 (fun w hw hwsupp => ?_) hg
    hgsupp hlin
  exact trigTwist_layer_criticalCurve s a α hφ hφsupp hφ2 hq hCφ hdecay hβ hT hw hA hwsupp hc1 hK
    hcrit hsum hdiff

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
