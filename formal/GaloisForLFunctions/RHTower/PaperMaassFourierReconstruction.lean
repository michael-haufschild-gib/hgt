import GaloisForLFunctions.HTGeometry.PaperFourierLiteralConvergence
import GaloisForLFunctions.RHTower.SelbergMaassFourierPartial

/-! # Full pointwise reconstruction of the Maass source and its physical gradient

The three components are the original source, horizontal derivative, and height
derivative. Log-height parametrization pays positivity. Finite-dimensional
reconstruction chooses one null set before every continuous linear readout.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane
open scoped BigOperators ContDiff
namespace GaloisForLFunctions.RHTower
open SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage
open SelbergMaassUnipotentFourier SelbergMaassCharacterGradient
open SelbergMaassFourier SelbergMaassMean SelbergMaassFourierPartial
open GaloisForLFunctions.HTGeometry
noncomputable section

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- Actual source and both real chart derivatives at positive height `exp T`. -/
def paperMaassJetVector (T : ℝ) (i : Fin 3) (x : ℝ) : EuclideanSpace ℂ (Deck N) :=
  let z := point (x * (N + 1 : ℕ)) (Real.exp T)
  ![sourceVector N f (ofComplex z),
    fderiv ℝ (fun w => sourceVector N f (ofComplex w)) z 1,
    fderiv ℝ (fun w => sourceVector N f (ofComplex w)) z Complex.I] i

/-- Existing source, signed-frequency, and height coefficients of the physical jet. -/
def paperMaassJetCoefficient (T : ℝ) (i : Fin 3) (n : ℤ) : EuclideanSpace ℂ (Deck N) :=
  ![coefficientVector N f n (Real.exp T),
    (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) •
      coefficientVector N f n (Real.exp T),
    coefficientHeightVector N f n (Real.exp T)] i

/-- Symmetric reconstruction in the original finite-dimensional source space. -/
def paperMaassJetPartialSum (T : ℝ) (i : Fin 3) (M : ℕ) (x : ℝ) :
    EuclideanSpace ℂ (Deck N) :=
  ∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
    fourierChar n x • paperMaassJetCoefficient N f T i n

private theorem readout_directional (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    (T x : ℝ) (v : ℂ) :
    directional v (fun w => L (sourceVector N f (ofComplex w)))
        (point (x * (N + 1 : ℕ)) (Real.exp T)) =
      L (fderiv ℝ (fun w => sourceVector N f (ofComplex w))
        (point (x * (N + 1 : ℕ)) (Real.exp T)) v) := by
  let z := point (x * (N + 1 : ℕ)) (Real.exp T)
  have hz : 0 < z.im := by
    simpa only [z, point, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
      Complex.ofReal_re, zero_add] using Real.exp_pos T
  have hd := ((sourceVector_contDiffOn N f).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds hz)).differentiableAt (by simp)
  have h := ((L.restrictScalars ℝ).hasFDerivAt.comp z hd.hasFDerivAt).fderiv
  exact congrArg (fun A : ℂ →L[ℝ] ℂ => A v) h

/-- No new derivative representative: observations are exactly the existing three readouts. -/
theorem paperMaassJetVector_readout (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    (T : ℝ) (i : Fin 3) (x : ℝ) :
    L (paperMaassJetVector N f T i x) =
      ![unitRescaledSourceReadout N f L (Real.exp T),
        unitRescaledHorizontalReadout N f L (Real.exp T),
        unitRescaledVerticalReadout N f L (Real.exp T)] i x := by
  fin_cases i
  · rfl
  · exact (readout_directional N f L T x 1).symm
  · exact (readout_directional N f L T x Complex.I).symm

private theorem jet_readout_continuous (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    (T : ℝ) (i : Fin 3) : Continuous (fun x => L (paperMaassJetVector N f T i x)) := by
  simp_rw [paperMaassJetVector_readout]
  fin_cases i
  · exact continuous_unitRescaledSourceReadout N f L (Real.exp_pos T)
  · exact continuous_unitRescaledHorizontalReadout N f L (Real.exp_pos T)
  · exact continuous_unitRescaledVerticalReadout N f L (Real.exp_pos T)

/-- The vector reconstruction uses precisely the native Fourier coefficients. -/
theorem paperMaassJetCoefficient_readout (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    (T : ℝ) (i : Fin 3) (n : ℤ) :
    l2Pair (fourierChar n) (fun x => L (paperMaassJetVector N f T i x)) =
      L (paperMaassJetCoefficient N f T i n) := by
  simp_rw [paperMaassJetVector_readout]
  fin_cases i
  · exact l2Pair_fourierChar_unitRescaledSourceReadout N f L n (Real.exp_pos T)
  · simpa [paperMaassJetCoefficient, map_smul, smul_eq_mul] using
      l2Pair_fourierChar_unitRescaledHorizontalReadout N f L n (Real.exp_pos T)
  · exact l2Pair_fourierChar_unitRescaledVerticalReadout N f L n (Real.exp_pos T)

theorem paperMaassJetPartialSum_readout (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    (T : ℝ) (i : Fin 3) (M : ℕ) (x : ℝ) :
    L (paperMaassJetPartialSum N f T i M x) =
      fourierPartialSum (fun y => L (paperMaassJetVector N f T i y)) M x := by
  simp only [paperMaassJetPartialSum, map_sum, map_smul, smul_eq_mul,
    fourierPartialSum, paperMaassJetCoefficient_readout]
  apply Finset.sum_congr rfl
  intro n _
  exact mul_comm _ _

/-- A single null set reconstructs the full source and gradient at countably many heights. -/
theorem paperMaassJet_common_reconstruction {κ : Type*} [Countable κ] (T : κ → ℝ) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ x ∈ Ioc (0 : ℝ) 1, x ∉ E → ∀ j i,
        Tendsto (fun M => paperMaassJetPartialSum N f (T j) i M x)
          atTop (𝓝 (paperMaassJetVector N f (T j) i x)) := by
  let obs (j : κ × Fin 3 × Deck N) : C(ℝ, ℂ) :=
    ⟨fun x => EuclideanSpace.proj j.2.2 (paperMaassJetVector N f (T j.1) j.2.1 x),
      jet_readout_continuous N f (EuclideanSpace.proj j.2.2) (T j.1) j.2.1⟩
  obtain ⟨E, hm, hz, hc⟩ := paperUnitIntervalContinuous_common_convergence obs
  refine ⟨E, hm, hz, ?_⟩
  intro x hx he j i
  have hq : Tendsto (fun M => fun q : Deck N =>
      (paperMaassJetPartialSum N f (T j) i M x) q) atTop
      (𝓝 (fun q => (paperMaassJetVector N f (T j) i x) q)) := by
    apply tendsto_pi_nhds.mpr
    intro q
    change Tendsto (fun M => EuclideanSpace.proj q (paperMaassJetPartialSum N f (T j) i M x))
      atTop (𝓝 (EuclideanSpace.proj q (paperMaassJetVector N f (T j) i x)))
    simp only [paperMaassJetPartialSum_readout]
    exact hc x hx he (j, i, q)
  exact ((PiLp.continuous_toLp 2 (fun _ : Deck N => ℂ)).tendsto _).comp hq

/-- All complex linear observations share the same set, including observations chosen at `x`. -/
theorem paperMaassJet_all_readouts_reconstruction {κ : Type*} [Countable κ] (T : κ → ℝ) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ x ∈ Ioc (0 : ℝ) 1, x ∉ E → ∀ j i (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ),
        Tendsto (fun M => fourierPartialSum
          (fun y => L (paperMaassJetVector N f (T j) i y)) M x)
          atTop (𝓝 (L (paperMaassJetVector N f (T j) i x))) := by
  obtain ⟨E, hm, hz, hc⟩ := paperMaassJet_common_reconstruction N f T
  refine ⟨E, hm, hz, fun x hx he j i L => ?_⟩
  have h := (L.continuous.tendsto _).comp (hc x hx he j i)
  change Tendsto (fun M => L (paperMaassJetPartialSum N f (T j) i M x)) atTop _ at h
  simpa only [paperMaassJetPartialSum_readout] using h

/-- Every finite complex mixture of heights, components, and arbitrary observations converges. -/
theorem paperMaassJet_all_readouts_span_reconstruction {κ : Type*} [Countable κ]
    (T : κ → ℝ) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ x ∈ Ioc (0 : ℝ) 1, x ∉ E → ∀ (S : Finset (κ × Fin 3))
        (c : κ × Fin 3 → ℂ) (L : κ × Fin 3 → EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ),
        Tendsto (fun M => ∑ j ∈ S, c j *
          L j (paperMaassJetPartialSum N f (T j.1) j.2 M x))
          atTop (𝓝 (∑ j ∈ S, c j * L j (paperMaassJetVector N f (T j.1) j.2 x))) := by
  obtain ⟨E, hm, hz, hc⟩ := paperMaassJet_common_reconstruction N f T
  exact ⟨E, hm, hz, fun x hx he S c L => tendsto_finsetSum S
    (fun j _ => ((L j).continuous.tendsto _ |>.comp (hc x hx he j.1 j.2)).const_mul (c j))⟩

end
end GaloisForLFunctions.RHTower
