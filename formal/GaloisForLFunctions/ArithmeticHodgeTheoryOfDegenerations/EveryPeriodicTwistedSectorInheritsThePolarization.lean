import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheTwistedSectorInheritsThePolarization
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheSecondOrderTermIsTheDirichletSeriesOfTheSpectrum

/-!
# Every periodic twisted sector inherits the polarization

Mechanism B on the twisted sector was proved for windows twisted by Ramanujan expansions, whose
second order is a count (`twisted_sector_inherits`). The spectral computation of the second order
(`periodicTwist_layer_criticalCurve_of_regularTail`) gives it for every mean-zero periodic twist:

* **The Gram limit of a twisted family** (`tendsto_twistGram_periodic`): for windows `g_j` twisted by
  one mean-zero `M`-periodic `χ`, the normalized Gram matrices of the complete family converge to
  `Λ_χ A(G)`, `Λ_χ = (βA_φ/(K∫φ²)) S_{β+1}(χ)`, `S` the spectral sum and `A(G)` the aliasing Gram
  matrix.
* **Inheritance** (`periodic_twisted_sector_inherits`): if `χ ≠ 0` and the family is linearly
  independent, `Λ_χ ≥ (βA_φ/(K∫φ²)) 2M⁻¹ Σ χ² > 0` (`twistSpectralSum_ge`), so the limit is positive
  definite and, positive definiteness being open, the complete family is eventually positive
  definite on the family.

This covers the character windows `Re(cψ)`, whose second order carries the `L`-value
`L(β+1, ψ̄²)`, and the cosine windows of every rational frequency: on every periodic twist the
degeneration is polarized at the critical curve and positivity passes to the nearby fibres.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23 Matrix
open scoped ComplexConjugate ComplexOrder

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri HTGeometry
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ : ℝ → ℝ} {A : ℝ} {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
/-- **The Gram limit of a periodic twisted family**: `Λ_χ A(G)`. -/
theorem tendsto_twistGram_periodic (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β Aφ : ℝ} (hβ : 0 < β)
    (hT : Tendsto (fun x => x ^ β * ArithmeticDegenerationTheory.spectralTail φ x) atTop (𝓝 Aφ))
    {g : κ → ℝ → ℝ} (hg : ∀ j, ContDiff ℝ 2 (g j)) (hA : 0 ≤ A)
    (hgsupp : ∀ j y, y ∉ Set.Icc (-A) 0 → g j y = 0) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ}
    (hK : 0 < K) (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    {χ : ℕ → ℝ} {M : ℕ} (hχ : MeanZeroTwist χ M) (j j' : κ) :
    Tendsto (fun N : ℕ => ((((c N)⁻¹ / ∫ u, atomDilate φ (c N / N) u ^ 2 : ℝ) : ℂ) •
      twistGram φ g χ (c N) N) j j') atTop
      (𝓝 (twistLimitGram β (β * Aφ / (K * ∫ u, φ u ^ 2) * twistSpectralSum (β + 1) χ M) g
        j j')) := by
  have hp' := periodicTwist_layer_criticalCurve_of_regularTail hφ hφsupp hφ2 hq hCφ hdecay hβ hT
    ((hg j).add (hg j')) hA (fun y hy => by simp [hgsupp j y hy, hgsupp j' y hy]) hc1 hK hcrit hχ
  have hm' := periodicTwist_layer_criticalCurve_of_regularTail hφ hφsupp hφ2 hq hCφ hdecay hβ hT
    ((hg j).sub (hg j')) hA (fun y hy => by simp [hgsupp j y hy, hgsupp j' y hy]) hc1 hK hcrit hχ
  have hreal := (hp'.sub hm').div_const 4
  set Λ := β * Aφ / (K * ∫ u, φ u ^ 2) * twistSpectralSum (β + 1) χ M with hΛ
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

/-- **Every periodic twisted sector inherits the polarization.** For a nonzero mean-zero periodic
twist and a linearly independent family of windows, along the critical curve the Gram matrix of the
complete family on the twisted family is eventually positive definite. -/
theorem periodic_twisted_sector_inherits (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β Aφ : ℝ} (hβ : 0 < β) (hAφ : 0 < Aφ)
    (hT : Tendsto (fun x => x ^ β * ArithmeticDegenerationTheory.spectralTail φ x) atTop (𝓝 Aφ))
    {g : κ → ℝ → ℝ} (hg : ∀ j, ContDiff ℝ 2 (g j)) (hA : 0 ≤ A)
    (hgsupp : ∀ j y, y ∉ Set.Icc (-A) 0 → g j y = 0) (hlin : LinearIndependent ℝ g)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    {χ : ℕ → ℝ} {M : ℕ} (hχ : MeanZeroTwist χ M) (hχ0 : 0 < ∑ n ∈ range M, χ n ^ 2) :
    ∀ᶠ N : ℕ in atTop, ∀ x : κ → ℂ, x ≠ 0 →
      0 < hermQuad (twistGram φ g χ (c N) N) x := by
  set Λ := β * Aφ / (K * ∫ u, φ u ^ 2) * twistSpectralSum (β + 1) χ M with hΛdef
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hχ.pos
  have hS := twistSpectralSum_ge (k' := β + 1) (by linarith) hχ
  have hΛ : 0 < Λ := by
    have h1 : 0 < 2 * ((M : ℝ)⁻¹ * ∑ n ∈ range M, χ n ^ 2) := by positivity
    have h2 : 0 < β * Aφ / (K * ∫ u, φ u ^ 2) := by positivity
    exact mul_pos h2 (lt_of_lt_of_le h1 hS)
  have hpos : ∀ x : κ → ℂ, x ≠ 0 → 0 < hermQuad (twistLimitGram β Λ g) x := fun x hx => by
    unfold twistLimitGram
    rw [HTGeometry.hermQuad_smul]
    have hA' := aliasGram_posDef β hg hgsupp hlin
    have : 0 < hermQuad (aliasGram β g) x := by
      have h1 := (Matrix.posDef_iff_dotProduct_mulVec.mp hA').2 hx
      simpa [hermQuad] using (Complex.lt_def.mp h1).1
    exact mul_pos hΛ this
  have hev := eventually_hermQuad_pos_of_tendsto (twistLimitGram_isHermitian β Λ g) hpos
    (tendsto_twistGram_periodic hφ hφsupp hφ2 hq hCφ hdecay hβ hT hg hA hgsupp hc1 hK hcrit hχ)
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

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
