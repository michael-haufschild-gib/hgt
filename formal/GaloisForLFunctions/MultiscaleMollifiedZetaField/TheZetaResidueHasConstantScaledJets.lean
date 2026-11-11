import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheCorrectionJetsKeepTheSummableEnvelope
import GaloisForLFunctions.RHTower.ZetaResidueFactorDerivative

/-!
# Logarithmically scaled jets of the zeta residue

Clearing the simple pole of zeta leaves an entire function with value
one at the pole. Under logarithmic rescaling its value tends to one and
every positive-order jet tends to zero, even at convergent moving centres.
-/

open Complex Filter Metric Set Topology
open RHTower

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The residue factor in a fixed normalized pole direction. -/
def affineZetaResidue (κ : ℝ) (z : ℂ) : ℂ := zetaResidueFactor (1 + (κ : ℂ) * z)

theorem differentiable_affineZetaResidue (κ : ℝ) : Differentiable ℂ (affineZetaResidue κ) :=
  differentiable_zetaResidueFactor.comp ((differentiable_id.const_mul (κ : ℂ)).const_add 1)

/-- Real restrictions of the actual complex jets after logarithmic rescaling. -/
def realScaledZetaResidueJet (L : ℝ) (κ : ℝ) (j : ℕ) (u : ℝ) : ℝ :=
  (iteratedDeriv j (fun z => affineZetaResidue κ (z / (L : ℂ))) (u : ℂ)).re

/-- Adjacent real residue jets are literal successive derivatives. -/
theorem hasDerivAt_realScaledZetaResidueJet (L : ℝ) (κ : ℝ) (j : ℕ) (u : ℝ) :
    HasDerivAt (realScaledZetaResidueJet L κ j) (realScaledZetaResidueJet L κ (j + 1) u) u := by
  let f : ℂ → ℂ := fun z => affineZetaResidue κ (z / (L : ℂ))
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

private theorem iteratedDeriv_succ_sub_constant (f : ℂ → ℂ) (a : ℂ) (j : ℕ) :
    iteratedDeriv (j + 1) (fun z => f z - a) = iteratedDeriv (j + 1) f := by
  induction j with
  | zero =>
      simp only [Nat.zero_add, iteratedDeriv_one]
      funext z
      exact deriv_sub_const a
  | succ j ih =>
      simpa only [iteratedDeriv_succ] using congrArg (fun g : ℂ → ℂ => deriv g) ih

/-- Every positive-order jet of an entire function under reciprocal dilation vanishes. -/
private theorem tendsto_entire_scaled_jet_succ {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {ι : Type*} {l : Filter ι}
    {L : ι → ℝ} (hL : Tendsto L l atTop) {C : ι → ℂ} {R : ℝ}
    (hR : ∀ᶠ N : ι in l, ‖C N‖ ≤ R) (j : ℕ) :
    Tendsto (fun N : ι => iteratedDeriv (j + 1)
      (fun z => f (z / (L N : ℂ))) (C N)) l (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  let η : ℝ := ε / (2 * ((j + 1).factorial : ℝ))
  have hfact : (0 : ℝ) < (j + 1).factorial := by positivity
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp (hf 0).continuousAt η hη
  filter_upwards [hL.eventually_gt_atTop 0, hL.eventually_gt_atTop ((R + 1) / δ), hR] with N hN hlarge hCN
  have hl : 0 < L N := hN
  have hd : Differentiable ℂ (fun z => f (z / (L N : ℂ)) - f 0) :=
    (hf.comp (differentiable_id.div_const _)).sub_const _
  have hb : ∀ z ∈ sphere (C N) 1, ‖f (z / (L N : ℂ)) - f 0‖ ≤ η := by
    intro z hz
    have hz1 : ‖z - C N‖ = 1 := by simpa only [mem_sphere, dist_eq_norm] using hz
    have hzn : ‖z‖ ≤ R + 1 := by
      have hh := norm_add_le (z - C N) (C N)
      rw [sub_add_cancel, hz1] at hh
      linarith only [hh, hCN]
    have hsmall : dist (z / (L N : ℂ)) 0 < δ := by
      rw [dist_zero_right, norm_div, Complex.norm_real, Real.norm_of_nonneg hl.le]
      refine (div_le_div_of_nonneg_right hzn hl.le).trans_lt ?_
      apply (div_lt_iff₀ hl).2
      simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hlarge
    have hh := hclose hsmall
    simpa only [dist_eq_norm] using hh.le
  have hCauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (j + 1) zero_lt_one hd.diffContOnCl hb
  rw [iteratedDeriv_succ_sub_constant] at hCauchy
  rw [dist_zero_right]
  refine hCauchy.trans_lt ?_
  simp only [one_pow, div_one]
  have he : ((j + 1).factorial : ℝ) * η = ε / 2 := by
    dsimp only [η]
    field_simp [hfact.ne']
  rw [he]
  exact half_lt_self hε

/-- The rescaled residue value tends to one at every convergent moving centre. -/
theorem tendsto_realScaledZetaResidueJet_zero (κ : ℝ)
    {ι : Type*} {l : Filter ι} {L : ι → ℝ} (hL : Tendsto L l atTop)
    {u : ι → ℝ} {u₀ : ℝ} (hu : Tendsto u l (𝓝 u₀)) :
    Tendsto (fun N => realScaledZetaResidueJet (L N) κ 0 (u N)) l (𝓝 1) := by
  have harg : Tendsto (fun N => ((u N / L N : ℝ) : ℂ)) l (𝓝 0) := by
    simpa only [Complex.ofReal_zero, Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp (hu.div_atTop hL)
  have hh := (differentiable_affineZetaResidue κ).continuous.continuousAt.tendsto.comp harg
  have hh' := Complex.continuous_re.continuousAt.tendsto.comp hh
  simpa only [realScaledZetaResidueJet, iteratedDeriv_zero, ← Complex.ofReal_div,
    affineZetaResidue, mul_zero, add_zero, zetaResidueFactor_one,
    Complex.one_re, Function.comp_def] using hh'

/-- Every positive-order scaled residue jet vanishes at convergent moving centres. -/
theorem tendsto_realScaledZetaResidueJet_succ (κ : ℝ)
    {ι : Type*} {l : Filter ι} {L : ι → ℝ} (hL : Tendsto L l atTop)
    {u : ι → ℝ} {u₀ : ℝ} (hu : Tendsto u l (𝓝 u₀)) (j : ℕ) :
    Tendsto (fun N => realScaledZetaResidueJet (L N) κ (j + 1) (u N)) l (𝓝 0) := by
  have hb : ∀ᶠ N : ι in l, ‖(u N : ℂ)‖ ≤ |u₀| + 1 := by
    have hh := hu.eventually (Metric.ball_mem_nhds u₀ zero_lt_one)
    filter_upwards [hh] with N hN
    rw [Real.dist_eq] at hN
    rw [Complex.norm_real, Real.norm_eq_abs]
    calc
      _ = |(u N - u₀) + u₀| := by rw [sub_add_cancel]
      _ ≤ |u N - u₀| + |u₀| := abs_add_le _ _
      _ ≤ _ := by linarith only [hN]
  have hh := tendsto_entire_scaled_jet_succ
    (differentiable_affineZetaResidue κ) hL hb j
  simpa only [realScaledZetaResidueJet, Complex.zero_re, Function.comp_def] using
    Complex.continuous_re.continuousAt.tendsto.comp hh

/-- Clearing the pole identifies the zeroth scaled zeta value exactly. -/
theorem scaled_zeta_value_eq_residue {L : ℝ} (hL : L ≠ 0) {κ u : ℝ}
    (hκ : κ ≠ 0) (hu : u ≠ 0) :
    (riemannZeta (1 + ((κ * u / L : ℝ) : ℂ))).re / L =
      realScaledZetaResidueJet L κ 0 u / (κ * u) := by
  have hx : κ * u / L ≠ 0 := div_ne_zero (mul_ne_zero hκ hu) hL
  have hs : (1 : ℂ) + ((κ * u / L : ℝ) : ℂ) ≠ 1 := by
    intro he
    have hh := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re] at hh
    exact hx (by linarith only [hh])
  have he : (1 : ℂ) + (κ : ℂ) * ((u : ℂ) / (L : ℂ)) =
      1 + ((κ * u / L : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_mul]
    ring
  unfold realScaledZetaResidueJet affineZetaResidue
  rw [iteratedDeriv_zero, he, zetaResidueFactor_of_ne hs]
  simp only [add_sub_cancel_left, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  field_simp [hL, hκ, hu] <;> ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField
