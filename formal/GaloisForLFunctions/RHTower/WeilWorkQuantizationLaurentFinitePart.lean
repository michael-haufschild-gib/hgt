import GaloisForLFunctions.RHTower.WeilWorkQuantizationHarmonicFinitePart
import GaloisForLFunctions.RHTower.ZetaResidueFactorDerivative

/-!
# The harmonic finite part is the actual source Laurent constant

The centered ordinary Dirichlet sum is continuous at one. Comparison with
the absolutely convergent source series and the regularized zeta function
identifies its finite part with the value of the source's holomorphic
pole subtraction. The same regular part retains its source-only strip bounds.
-/

open Complex Set Filter Topology
open GaloisForLFunctions.RHTower
noncomputable section
namespace RHTower.WeilSpectral
open WeilWorkSettledPhase WeilSingularArithmetic
variable {lam : ℕ → ℝ}

theorem quantization_centered_dirichlet_eq (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 < s.re) :
    dirichletSum (fun n => sourceCoeff lam (n + 1) - sourceCompletion hW 1) s =
      LSeries (sourceCoeff lam) s - sourceCompletion hW 1 * riemannZeta s := by
  let a : ℕ → ℂ := sourceCoeff lam - sourceCompletion hW 1 • (1 : ℕ → ℂ)
  have hc := (LSeriesSummable_one_iff.mpr hs).smul (sourceCompletion hW 1)
  have hl : LSeriesSummable a s := (sourceCoeff_LSeries hW hs).1.sub hc
  have hh : HasSum (fun n => LSeries.term a s (n + 1)) (LSeries a s) := by
    have := (hasSum_nat_add_iff' 1).mpr hl.LSeriesHasSum
    simpa [LSeries.term_zero] using this
  have ht : Tendsto (fun N => dirichletPartialSum (fun n => a (n + 1)) N s)
      atTop (𝓝 (LSeries a s)) := by
    refine hh.tendsto_sum_nat.congr fun N => Finset.sum_congr rfl fun n _ => ?_
    exact term_succ_eq a s n
  have he : (fun n => a (n + 1)) =
      (fun n => sourceCoeff lam (n + 1) - sourceCompletion hW 1) := by
    ext n
    simp [a]
  rw [he] at ht
  rw [tendsto_nhds_unique (tendsto_dirichletSum
    (centered_forward_dirichletConvergesAt hW (by linarith))) ht]
  change LSeries (sourceCoeff lam - sourceCompletion hW 1 • (1 : ℕ → ℂ)) s = _
  rw [LSeries_sub (sourceCoeff_LSeries hW hs).1 hc, LSeries_smul,
    LSeries_one_eq_riemannZeta hs]

private theorem source_residue_im_zero (hW : WeilPositiveFull lam) :
    (sourceCompletion hW 1).im = 0 := by
  have h := congrArg Complex.im (sourceCompletion_conj hW (s := 1) (by norm_num))
  simp only [map_one, Complex.conj_im] at h
  linarith

private theorem source_coeff_im_zero (lam : ℕ → ℝ) (n : ℕ) :
    (sourceCoeff lam n).im = 0 := by
  have h := congrArg Complex.im (forwardCoeff_ofReal_re lam n)
  rw [forwardCoeff_eq_sourceCoeff] at h
  simpa only [Complex.ofReal_im] using h.symm

theorem quantization_centered_dirichlet_one_im (hW : WeilPositiveFull lam) :
    (dirichletSum (fun n => sourceCoeff lam (n + 1) - sourceCompletion hW 1) 1).im = 0 := by
  have ht := Complex.continuous_im.tendsto _ |>.comp
    (tendsto_dirichletSum (centered_forward_dirichletConvergesAt hW (s := 1) (by norm_num)))
  simp only [Function.comp_def, dirichletPartialSum, Complex.im_sum,
    Complex.cpow_neg_one, ← div_eq_mul_inv, Complex.div_ofReal_im,
    Complex.sub_im, source_coeff_im_zero, source_residue_im_zero hW,
    sub_self, zero_div, Finset.sum_const_zero] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- The actual source regular part has exactly the harmonic finite part at its pole. -/
theorem exists_quantization_regularPart_finitePart (hW : WeilPositiveFull lam) :
    ∃ R : ℂ → ℂ, DifferentiableOn ℂ R {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → R s =
        LSeries (sourceCoeff lam) s - sourceCompletion hW 1 / (s - 1)) ∧
      R 1 = (quantizationHarmonicFinitePart hW : ℂ) ∧
      ∀ q a : ℝ, 0 < q → 0 < a → ∃ K : ℝ, 0 ≤ K ∧
        ∀ s : ℂ, 1 / 2 + q ≤ s.re → s.re ≤ 2 →
          ‖R s‖ ≤ K * (2 + |s.im|) ^ a := by
  obtain ⟨R, hRd, hRF, hRg⟩ := exists_forward_regularPart hW
  refine ⟨R, hRd, hRF, ?_, hRg⟩
  let A := dirichletSum (fun n => sourceCoeff lam (n + 1) - sourceCompletion hW 1)
  have hAc : ContinuousAt A 1 :=
    ((differentiableOn_dirichletSum
      (centered_forward_dirichletConvergesAt hW (s := (5 / 8 : ℂ)) (by norm_num))).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num))).continuousAt
  have hRc : ContinuousAt R 1 := (hRd.differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num))).continuousAt
  have hcast := tendsto_ofReal_nhdsWithin_ne_one.mono_right nhdsWithin_le_nhds
  have hcont : ContinuousAt
      (fun s : ℂ => A s + sourceCompletion hW 1 * riemannZeta₀ s) 1 :=
    hAc.add (continuousAt_const.mul (differentiable_riemannZeta₀ 1).continuousAt)
  have hlim := hcont.tendsto.comp hcast
  have hval : R 1 = A 1 + sourceCompletion hW 1 * (Real.eulerMascheroniConstant : ℂ) := by
    apply tendsto_nhds_unique (hRc.tendsto.comp hcast)
    simp only [riemannZeta₀_one] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    change A (s : ℂ) + sourceCompletion hW 1 * riemannZeta₀ (s : ℂ) = R (s : ℂ)
    rw [hRF (s : ℂ) hs, show A (s : ℂ) = _ from quantization_centered_dirichlet_eq hW hs,
      riemannZeta_eq_inv_sub_add (by exact_mod_cast (ne_of_gt hs : s ≠ 1))]
    ring
  rw [hval]
  apply Complex.ext
  · simp [quantizationHarmonicFinitePart, A]
  · simp [A, quantization_centered_dirichlet_one_im hW, source_residue_im_zero hW]

end RHTower.WeilSpectral
