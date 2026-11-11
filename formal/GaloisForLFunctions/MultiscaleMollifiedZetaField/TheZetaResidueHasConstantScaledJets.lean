import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheCorrectionJetsKeepTheSummableEnvelope
import GaloisForLFunctions.RHTower.ZetaResidueFactorDerivative

/-!
# Logarithmically scaled jets of the zeta residue

Clearing the simple pole of zeta leaves an entire function with value
one at the pole. Under logarithmic rescaling its value tends to one and
every positive-order jet tends to zero, even at convergent moving centres.
-/

open Complex Filter Set Topology
open RHTower

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The residue factor in a fixed normalized pole direction. -/
def affineZetaResidue (κ : ℝ) (z : ℂ) : ℂ := zetaResidueFactor (1 + (κ : ℂ) * z)

theorem differentiable_affineZetaResidue (κ : ℝ) : Differentiable ℂ (affineZetaResidue κ) :=
  differentiable_zetaResidueFactor.comp ((differentiable_id.const_mul (κ : ℂ)).const_add 1)

/-- Real restrictions of the actual complex jets after logarithmic rescaling. -/
def realScaledZetaResidueJet (N : ℕ) (κ : ℝ) (j : ℕ) (u : ℝ) : ℝ :=
  (iteratedDeriv j (fun z => affineZetaResidue κ (z / (Real.log N : ℂ))) (u : ℂ)).re

/-- Adjacent real residue jets are literal successive derivatives. -/
theorem hasDerivAt_realScaledZetaResidueJet (N : ℕ) (κ : ℝ) (j : ℕ) (u : ℝ) :
    HasDerivAt (realScaledZetaResidueJet N κ j) (realScaledZetaResidueJet N κ (j + 1) u) u := by
  let f : ℂ → ℂ := fun z => affineZetaResidue κ (z / (Real.log N : ℂ))
  have hf : Differentiable ℂ f :=
    (differentiable_affineZetaResidue κ).comp (differentiable_id.div_const _)
  have ha : ∀ k : ℕ, AnalyticAt ℂ (iteratedDeriv k f) (u : ℂ) := by
    intro k
    induction k with
    | zero => exact hf.differentiableOn.analyticOnNhd isOpen_univ _ (mem_univ _)
    | succ k hk => simpa only [iteratedDeriv_succ] using hk.deriv
  change HasDerivAt (fun x : ℝ => (iteratedDeriv j f (x : ℂ)).re)
    (iteratedDeriv (j + 1) f (u : ℂ)).re u
  rw [iteratedDeriv_succ]
  exact (ha j).differentiableAt.hasDerivAt.real_of_complex

/-- The rescaled residue value tends to one at every convergent moving centre. -/
theorem tendsto_realScaledZetaResidueJet_zero (κ : ℝ)
    {u : ℕ → ℝ} {u₀ : ℝ} (hu : Tendsto u atTop (𝓝 u₀)) :
    Tendsto (fun N => realScaledZetaResidueJet N κ 0 (u N)) atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have harg : Tendsto (fun N => ((u N / Real.log N : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa only [Complex.ofReal_zero, Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp (hu.div_atTop hlog)
  have hh := (differentiable_affineZetaResidue κ).continuous.continuousAt.tendsto.comp harg
  have hh' := Complex.continuous_re.continuousAt.tendsto.comp hh
  simpa only [realScaledZetaResidueJet, iteratedDeriv_zero, ← Complex.ofReal_div,
    affineZetaResidue, mul_zero, add_zero, zetaResidueFactor_one,
    Complex.one_re, Function.comp_def] using hh'

/-- Every positive-order scaled residue jet vanishes at convergent moving centres. -/
theorem tendsto_realScaledZetaResidueJet_succ (κ : ℝ)
    {u : ℕ → ℝ} {u₀ : ℝ} (hu : Tendsto u atTop (𝓝 u₀)) (j : ℕ) :
    Tendsto (fun N => realScaledZetaResidueJet N κ (j + 1) (u N)) atTop (𝓝 0) := by
  have hb : ∀ᶠ N : ℕ in atTop, ‖(u N : ℂ)‖ ≤ |u₀| + 1 := by
    have hh := hu.eventually (Metric.ball_mem_nhds u₀ zero_lt_one)
    filter_upwards [hh] with N hN
    rw [Real.dist_eq] at hN
    rw [Complex.norm_real, Real.norm_eq_abs]
    have he : u N = (u N - u₀) + u₀ := by ring
    calc
      _ = |(u N - u₀) + u₀| := by rw [he]
      _ ≤ |u N - u₀| + |u₀| := abs_add_le _ _
      _ ≤ _ := by linarith only [hN]
  have hh := tendsto_entire_normalized_jet_succ_of_bounded_centres
    (differentiable_affineZetaResidue κ) hb j
  simpa only [realScaledZetaResidueJet, Complex.zero_re, Function.comp_def] using
    Complex.continuous_re.continuousAt.tendsto.comp hh

/-- Clearing the pole identifies the zeroth scaled zeta value exactly. -/
theorem scaled_zeta_value_eq_residue {N : ℕ} (hN : 1 < N) {κ u : ℝ}
    (hκ : κ ≠ 0) (hu : u ≠ 0) :
    (riemannZeta (1 + ((κ * u / Real.log N : ℝ) : ℂ))).re / Real.log N =
      realScaledZetaResidueJet N κ 0 u / (κ * u) := by
  have hL : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  have hx : κ * u / Real.log N ≠ 0 := div_ne_zero (mul_ne_zero hκ hu) hL
  have hs : (1 : ℂ) + ((κ * u / Real.log N : ℝ) : ℂ) ≠ 1 := by
    intro he
    have hh := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re] at hh
    exact hx (by linarith only [hh])
  have he : (1 : ℂ) + (κ : ℂ) * ((u : ℂ) / (Real.log N : ℂ)) =
      1 + ((κ * u / Real.log N : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_mul]
    ring
  unfold realScaledZetaResidueJet affineZetaResidue
  rw [iteratedDeriv_zero, he, zetaResidueFactor_of_ne hs]
  simp only [add_sub_cancel_left, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  field_simp [hL, hκ, hu] <;> ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField
