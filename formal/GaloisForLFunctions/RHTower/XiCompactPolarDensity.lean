import GaloisForLFunctions.RHTower.XiCompactPolarCardinals
import GaloisForLFunctions.RHTower.XiWeilCauchyCoreMultiplicity
import GaloisForLFunctions.RHTower.XiZeroBandFinite

/-!
# Complete compact-polar spectral density

Translation separates the two members of every cardinal pair. Thus compact
polar tests detect every multiplicity-fibre sum, and their exact Hilbert
closure is the entire folded divisor space.
-/

open Complex MeasureTheory Filter Topology Set Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower

theorem inner_fiberIndicator_eq_fiberSum (ρ : XiDivisorSupport)
    (u : lp (fun _ : XiZeroCopy => ℂ) 2) :
    inner ℂ (xiWeilFiberIndicatorLp (xiSpectralPointSupport ρ)) u = xiWeilFiberSum u ρ := by
  classical
  rw [lp.inner_eq_tsum]
  rw [tsum_eq_sum (s := xiZeroCopyFiber ρ) (fun q hq => by
    have hn : xiSpectralPoint q ≠ xiSpectralPointSupport ρ := by
      intro h
      exact hq (mem_xiZeroCopyFiber.mpr (xiSpectralPointSupport_injective h))
    simp [xiWeilFiberIndicatorLp_apply, hn])]
  apply Finset.sum_congr rfl
  intro q hq
  have h := mem_xiZeroCopyFiber.mp hq
  simp [xiWeilFiberIndicatorLp_apply, xiSpectralPoint_eq_support, h]

theorem inner_fiberIndicator_zero_of_compactPolar_orthogonal
    {u : lp (fun _ : XiZeroCopy => ℂ) 2}
    (hu : u ∈ compactXiPolarEvaluation.rangeᗮ) {a : ℂ} (hz : XiC a = 0) :
    inner ℂ (xiWeilFiberIndicatorLp a) u = 0 := by
  have hc : ∀ v ∈ compactXiPolarEvaluation.range.topologicalClosure, inner ℂ v u = 0 := by
    apply closure_minimal
    · exact hu
    · exact isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hpos {b : ℂ} (hb : 0 < b.re) (hzb : XiC b = 0) :
      inner ℂ (xiWeilFiberIndicatorLp b) u = 0 ∧
      inner ℂ (xiWeilFiberIndicatorLp (-b)) u = 0 := by
    have hn : conj b ≠ 0 := by
      intro he
      have h := congrArg Complex.re he
      simp only [Complex.conj_re, Complex.zero_re] at h
      linarith
    apply CHMDDoobGraph.exponential_pair_separation hn (r := 1) zero_lt_one
    intro t _
    have h := hc _ (translated_cardinal_mem_compactXiPolar_closure hb hzb t)
    simpa only [inner_add_left, inner_smul_left, ← Complex.exp_conj,
      map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, neg_mul, neg_neg] using h
  rcases lt_or_gt_of_ne (re_ne_zero_of_XiC_eq_zero hz) with hneg | hgt
  · have h := (hpos (b := -a) (by simpa using neg_pos.mpr hneg)
      (by rw [XiC_even, hz])).2
    simpa using h
  · exact (hpos hgt hz).1

theorem compactXiPolar_orthogonal_iff_fiberSums_zero
    (u : lp (fun _ : XiZeroCopy => ℂ) 2) :
    u ∈ compactXiPolarEvaluation.rangeᗮ ↔
      ∀ ρ : XiDivisorSupport, xiWeilFiberSum u ρ = 0 := by
  constructor
  · intro hu ρ
    rw [← inner_fiberIndicator_eq_fiberSum]
    exact inner_fiberIndicator_zero_of_compactPolar_orthogonal hu (XiC_spectralSupport_eq_zero ρ)
  · intro hu v hv
    obtain ⟨f, rfl⟩ := hv
    have hF := complexXi_squareSummable (f : compactXiTests)
      (compactXiTests.re_decay f) (compactXiTests.im_decay f)
    have he : compactXiPolarEvaluation f = xiWeilEvaluationLp (paperFT (f : compactXiTests)) hF := by
      apply Subtype.ext
      funext q
      exact compactXiPolarEvaluation_apply f q
    rw [he]
    exact inner_xiWeilEvaluationLp_eq_zero_of_xiWeilFiberSum_eq_zero _ hF u hu

/-- Every folded square-summable Xi profile is a limit of literal compact C2
tests with both polar moments exactly zero. Multiplicities are retained. -/
theorem compactXiPolarEvaluation_closure_eq_cauchyHilbertSubspace :
    compactXiPolarEvaluation.range.topologicalClosure = xiWeilCauchyHilbertSubspace := by
  have ho : compactXiPolarEvaluation.rangeᗮ = xiWeilCauchyHilbertSubspaceᗮ := by
    ext u
    rw [compactXiPolar_orthogonal_iff_fiberSums_zero,
      mem_orthogonal_xiWeilCauchyHilbertSubspace_iff]
  rw [← Submodule.orthogonal_orthogonal_eq_closure, ho,
    Submodule.orthogonal_orthogonal_eq_closure]
  exact isClosed_closure.submodule_topologicalClosure_eq

theorem exists_compactXiPolar_approximation (v : lp (fun _ : XiZeroCopy => ℂ) 2)
    (hv : v ∈ xiWeilCauchyHilbertSubspace) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : compactXiPolarTests, ‖compactXiPolarEvaluation f-v‖ < ε := by
  rw [← compactXiPolarEvaluation_closure_eq_cauchyHilbertSubspace] at hv
  obtain ⟨w, ⟨f, rfl⟩, hd⟩ := Metric.mem_closure_iff.mp hv ε hε
  exact ⟨f, by simpa [dist_eq_norm, norm_sub_rev] using hd⟩

end RHTower
