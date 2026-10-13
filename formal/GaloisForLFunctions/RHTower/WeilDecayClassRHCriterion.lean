import GaloisForLFunctions.RHTower.WeilPaperRealTestSplitting
import GaloisForLFunctions.RHTower.WeilPrimeBlindZeroSideIdentity

/-!
# Weil's criterion on real tests of the decay class

**Real tests suffice** (`weilPositiveFull_of_real`).  A weight system is full-cone Weil-positive as
soon as its Weil functional is nonnegative on the autocorrelations of real-valued `C²` compactly
supported tests.  The real and imaginary parts of a complex test split both the pole and
archimedean energy and the integer logarithmic samples additively (`energy_paperSplitRealMixture`,
`defect_paperSplitRealMixture`), so `Re W(f ⋆ f̃) = W(g ⋆ g̃) + W(h ⋆ h̃)` for `f = g + ih`.

**Theorem** (`riemannHypothesis_iff_decayClass_weilPositive`).  RH holds iff for every real test
`F` with `|F|, |F'| ≤ C e^{−(1/2+δ)|x|}` (`δ > 0`)

`archPoleEnergy F ≥ Σ_n ψ(n) (P(n) − P(n+1))`,

where `ψ(n) = Σ_{m ≤ n} Λ(m)` and `P(n) = ((F ⋆ F̃)(log n) + (F ⋆ F̃)(−log n))/√n`
(`abelPrimePairing`).  The left side is the pole and archimedean energy
`2 Re(F̂(i/2)·conj F̂(−i/2)) + (1/2π) ∫ |F̂(r)|² G(r) dr`.  The test class is the natural one for
the explicit formula (transforms analytic on a strip of half-width above `½`), and the prime side is
an absolutely convergent series.

**Proof.**  (⇒) Under RH, `Λ` is Weil-positive and the decay-class spectral identity gives
`archPoleEnergy F − abelPrimePairing Λ F = ∫ |F̂|² dμ_Λ ≥ 0`.  (⇐) A real `C²` compactly supported
test is in the decay class and equals its own truncation at a large cutoff; there the inequality
is `Re W_Λ(g ⋆ g̃) ≥ 0`.  Real tests suffice, so `Λ` is full-cone Weil-positive, which is RH.
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ENNReal NNReal
open Zeta23

noncomputable section

namespace RHTower.WeilSpectral

open WeilOneSided WeilWorkPBAP

/-- **Real tests suffice for full-cone Weil positivity.** -/
theorem weilPositiveFull_of_real {lam : ℕ → ℝ}
    (h : ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      0 ≤ (weilFullFunctional lam
        (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re) :
    WeilPositiveFull lam := by
  intro f hf hfc
  set F : WeilTestFn := ⟨f, hf, hfc⟩ with hFdef
  set R := paperRealPartTestFn F with hR
  set J := paperImagPartTestFn F with hJ
  have hsplit : paperSplitRealMixture (Finsupp.single F 1) =
      Finsupp.single R 1 + Finsupp.single J 1 := by
    simp [paperSplitRealMixture, hR, hJ, Finsupp.mapDomain_single]
  have hE := energy_paperSplitRealMixture (Finsupp.single F 1)
  have hD := defect_paperSplitRealMixture (Finsupp.single F 1)
  rw [hsplit] at hE hD
  simp only [energy, defect, map_add, linearCombination_single, one_smul] at hE hD
  have hF := re_weilFullFunctional_eq lam F
  have hRe := re_weilFullFunctional_eq lam R
  have hIm := re_weilFullFunctional_eq lam J
  have hRpos := h (fun x => (f x).re) (Complex.reCLM.contDiff.comp hf)
    (hfc.comp_left (g := fun z : ℂ => z.re) (by simp))
  have hJpos := h (fun x => (f x).im) (Complex.imCLM.contDiff.comp hf)
    (hfc.comp_left (g := fun z : ℂ => z.im) (by simp))
  have hRe' : (weilFullFunctional lam (EF.weilTest R.1 R.1)).re =
      (weilFullFunctional lam
        (EF.weilTest (fun u => ((f u).re : ℂ)) (fun u => ((f u).re : ℂ)))).re := rfl
  have hIm' : (weilFullFunctional lam (EF.weilTest J.1 J.1)).re =
      (weilFullFunctional lam
        (EF.weilTest (fun u => ((f u).im : ℂ)) (fun u => ((f u).im : ℂ)))).re := rfl
  have hfF : (weilFullFunctional lam (EF.weilTest f f)).re =
      (weilFullFunctional lam (EF.weilTest F.1 F.1)).re := rfl
  rw [hfF, hF, ← hE, ← hD, map_add]
  have : (weilFullFunctional lam (EF.weilTest R.1 R.1)).re +
      (weilFullFunctional lam (EF.weilTest J.1 J.1)).re =
      weilArchRe (EF.weilTest R.1 R.1) + weilArchRe (EF.weilTest J.1 J.1) -
        ((linearCombination ℝ (fun j : LogIndex => lam j)) (logVector R) +
          (linearCombination ℝ (fun j : LogIndex => lam j)) (logVector J)) := by
    rw [hRe, hIm]; ring
  rw [← this, hRe', hIm']
  exact add_nonneg hRpos hJpos

/-- **RH from Weil positivity on real tests.** -/
theorem riemannHypothesis_iff_real_weilPositive :
    RiemannHypothesis ↔ ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      0 ≤ (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re :=
  ⟨fun hRH _g hg hgc => riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH _
      (Complex.ofRealCLM.contDiff.comp hg) (hgc.comp_left Complex.ofReal_zero),
    fun h => riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr (weilPositiveFull_of_real h)⟩

/-- A compactly supported test is its own truncation at a large cutoff. -/
theorem exists_truncTest_eq_self {g : ℝ → ℝ} (hgc : HasCompactSupport g) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → truncTest g L = g := by
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  refine ⟨|R| + 1, fun L hL => funext fun u => ?_⟩
  by_cases hu : |u| ≤ L - 1
  · exact truncTest_eq_self hu
  · have hout : u ∉ tsupport g := by
      intro hmem
      have := hR hmem
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
      linarith [le_abs_self R]
    have hg0 : g u = 0 := image_eq_zero_of_notMem_tsupport hout
    simp [truncTest, hg0]

/-- A `C²` compactly supported real test belongs to the decay class. -/
theorem expDecayTest_of_hasCompactSupport {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) : ExpDecayTest g := by
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  have hdc : HasCompactSupport (deriv g) := hgc.deriv
  obtain ⟨B₁, hB₁⟩ := hg.continuous.bounded_above_of_compact_support hgc
  obtain ⟨B₂, hB₂⟩ := (hg.continuous_deriv (by norm_num)).bounded_above_of_compact_support hdc
  set B := max (max B₁ B₂) 0 with hB
  refine ⟨hg, 1, B * Real.exp ((1 / 2 + 1) * |R|), one_pos, by positivity, fun x => ?_⟩
  by_cases hx : |x| ≤ |R|
  · have hexp : 1 ≤ Real.exp ((1 / 2 + 1) * |R|) * Real.exp (-((1 / 2 + 1) * |x|)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [abs_nonneg x])
    have hB0 : 0 ≤ B := le_max_right _ _
    constructor
    · have h1 : |g x| ≤ B := by
        have := hB₁ x; rw [Real.norm_eq_abs] at this
        exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
      calc |g x| ≤ B * 1 := by rw [mul_one]; exact h1
        _ ≤ B * (Real.exp ((1 / 2 + 1) * |R|) * Real.exp (-((1 / 2 + 1) * |x|))) :=
            mul_le_mul_of_nonneg_left hexp hB0
        _ = _ := by ring
    · have h2 : |deriv g x| ≤ B := by
        have := hB₂ x; rw [Real.norm_eq_abs] at this
        exact this.trans ((le_max_right _ _).trans (le_max_left _ _))
      calc |deriv g x| ≤ B * 1 := by rw [mul_one]; exact h2
        _ ≤ B * (Real.exp ((1 / 2 + 1) * |R|) * Real.exp (-((1 / 2 + 1) * |x|))) :=
            mul_le_mul_of_nonneg_left hexp hB0
        _ = _ := by ring
  · have hout : x ∉ tsupport g := by
      intro hmem
      have := hR hmem
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
      exact hx (this.trans (le_abs_self R))
    have hg0 : g x = 0 := image_eq_zero_of_notMem_tsupport hout
    have hd0 : deriv g x = 0 :=
      image_eq_zero_of_notMem_tsupport fun hmem => hout (tsupport_deriv_subset hmem)
    have hpos : 0 ≤ B * Real.exp ((1 / 2 + 1) * |R|) * Real.exp (-((1 / 2 + 1) * |x|)) := by
      have : 0 ≤ B := le_max_right _ _
      positivity
    exact ⟨by rw [hg0, abs_zero]; exact hpos, by rw [hd0, abs_zero]; exact hpos⟩

/-- **Weil's criterion on the decay class.**  RH holds iff the pole and archimedean energy dominates
the Abel prime pairing with `Λ` on every real test of the decay class. -/
theorem riemannHypothesis_iff_decayClass_weilPositive :
    RiemannHypothesis ↔ ∀ F : ℝ → ℝ, ExpDecayTest F →
      abelPrimePairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) F ≤ archPoleEnergy F := by
  refine ⟨fun hRH F hF => sub_nonneg.mp
      (archPoleEnergy_sub_abelPrimePairing_nonneg_of_riemannHypothesis hRH hF), fun h => ?_⟩
  refine riemannHypothesis_iff_real_weilPositive.mpr fun g hg hgc => ?_
  have hF := expDecayTest_of_hasCompactSupport hg hgc
  obtain ⟨L₀, hL₀⟩ := exists_truncTest_eq_self hgc
  have hlim := tendsto_atomPairing_truncTest_abelPrimePairing hF (A := 7)
    (w := fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (fun N => abs_primeWeightPartialSum_vonMangoldt_le N)
  have hconst : Tendsto (fun L : ℝ => atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (crossCorr (truncTest g L) (truncTest g L))) atTop
      (𝓝 (atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (crossCorr g g))) :=
    tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨L₀, fun L hL => by dsimp only; rw [hL₀ L hL]⟩)
  have habel := tendsto_nhds_unique hlim hconst
  have hre := re_weilFullFunctional_weilTest_truncTest_eq
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) hg L₀
  rw [hL₀ L₀ le_rfl] at hre
  rw [hre, ← habel]
  exact sub_nonneg.mpr (h g hF)

end RHTower.WeilSpectral
