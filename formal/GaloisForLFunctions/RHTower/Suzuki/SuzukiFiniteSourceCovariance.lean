import GaloisForLFunctions.RHTower.Suzuki.SuzukiGrowingPhysicalCoercivity

open Filter
open scoped InnerProduct Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- The actual shifted-form Riesz response to an arbitrary physical source. -/
def suzukiTaSourceResponse (a : SuzukiPositiveAperture) (p : suzukiApertureHilbert a) :
    SuzukiTaHilbert a :=
  suzukiTaFromFormCLM a
    (boundedPerturbedFormRieszInv (suzukiWeilIntervalFormEmbedding a)
      (suzukiWeilIntervalBoundedRemainder a)
      (suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a)
      ((suzukiWeilIntervalFormEmbedding a).adjoint ((suzukiApertureL2Equiv a).symm p)))

/-- This response represents the existing completed covariance, without a
replacement operator or source equation premise. -/
theorem suzukiTaPhysicalEmbedding_sourceResponse (a : SuzukiPositiveAperture)
    (p : suzukiApertureHilbert a) :
    suzukiTaPhysicalEmbedding a (suzukiTaSourceResponse a p) =
      suzukiWeilIntervalCovariance a ((suzukiApertureL2Equiv a).symm p) := rfl

theorem suzukiTaSourceResponse_inner (a : SuzukiPositiveAperture)
    (p : suzukiApertureHilbert a) (z : SuzukiTaHilbert a) :
    inner ℂ (suzukiTaSourceResponse a p) z =
      inner ℂ p (ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a z)) := by
  let J := suzukiWeilIntervalFormEmbedding a
  let B := suzukiWeilIntervalBoundedRemainder a
  let hB := suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a
  let e := suzukiApertureL2Equiv a
  change inner ℂ ((boundedPerturbedFormRieszEquiv J B hB)
      ((boundedPerturbedFormRieszEquiv J B hB).symm (J.adjoint (e.symm p))))
    (suzukiTaToFormCLM a z) = _
  rw [(boundedPerturbedFormRieszEquiv J B hB).apply_symm_apply, J.adjoint_inner_left]
  exact e.symm.inner_map_map _ _

private theorem fromForm_inner (a : SuzukiPositiveAperture)
    (g : CCMArchimedeanFormDomain a) (z : SuzukiTaHilbert a) :
    inner ℂ (suzukiTaFromFormCLM a g) z =
      inner ℂ g (suzukiTaToFormCLM a z) +
        inner ℂ (ccmShiftedBoundedWeil a (ccmArchimedeanFormToAperture a g))
          (ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a z)) := by
  let u := ccmArchimedeanFormToAperture a g
  let f := ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a z)
  have hphys : inner ℂ (suzukiTaPhysicalEmbedding a (suzukiTaFromFormCLM a g))
      (suzukiTaPhysicalEmbedding a z) = inner ℂ u f :=
    (suzukiApertureL2Equiv a).symm.inner_map_map u f
  rw [inner_suzukiTa_eq, suzukiWeilIntervalForm_eq_ccmRestrictedWeilForm]
  change inner ℂ g (suzukiTaToFormCLM a z) +
      inner ℂ (ccmRestrictedWeilBoundedRemainder a u) f +
      (boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ) *
        inner ℂ (suzukiTaPhysicalEmbedding a (suzukiTaFromFormCLM a g))
          (suzukiTaPhysicalEmbedding a z) = _
  rw [hphys]
  change _ = inner ℂ g (suzukiTaToFormCLM a z) +
    inner ℂ ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ) • u +
      ccmRestrictedWeilBoundedRemainder a u) f
  rw [inner_add_left, inner_smul_left u f
    (boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ), Complex.conj_ofReal]
  ring

/-- Exact source equation controls the Ta norm of the response-minus-test
vector, retaining both the physical residual and Gamma energy. -/
theorem suzukiTaSourceResponse_form_residual_norm_le (a : SuzukiPositiveAperture)
    (p : suzukiApertureHilbert a) (g : CCMArchimedeanFormDomain a) :
    ‖suzukiTaSourceResponse a p - suzukiTaFromFormCLM a g‖ ≤
      ‖p -
        ccmShiftedBoundedWeil a (ccmArchimedeanFormToAperture a g)‖ + ‖g‖ := by
  let w := suzukiTaSourceResponse a p
  let z := w - suzukiTaFromFormCLM a g
  let f := ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a z)
  let u := ccmArchimedeanFormToAperture a g
  let r := p - ccmShiftedBoundedWeil a u
  have heq : inner ℂ z z = inner ℂ r f - inner ℂ g (suzukiTaToFormCLM a z) := by
    calc
      _ = inner ℂ w z - inner ℂ (suzukiTaFromFormCLM a g) z := inner_sub_left _ _ _
      _ = _ := by
        rw [suzukiTaSourceResponse_inner, fromForm_inner]
        dsimp only [r]
        rw [inner_sub_left]
        ring
  have hself : (inner ℂ z z).re = ‖z‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) z).symm
  have hres := congrArg Complex.re heq
  rw [hself, Complex.sub_re] at hres
  have he := suzukiTa_energy_decomposition a z
  have hc := ccmShiftedBoundedWeil_coercive a f
  change ‖z‖ ^ 2 = ‖suzukiTaToFormCLM a z‖ ^ 2 +
    (inner ℂ (ccmShiftedBoundedWeil a f) f).re at he
  have hf : ‖f‖ ≤ ‖z‖ := by
    nlinarith [sq_nonneg ‖suzukiTaToFormCLM a z‖, norm_nonneg z]
  have ht : ‖suzukiTaToFormCLM a z‖ ≤ ‖z‖ := by
    nlinarith [sq_nonneg ‖f‖, norm_nonneg z]
  have hr : (inner ℂ r f).re ≤ ‖r‖ * ‖f‖ := re_inner_le_norm (𝕜 := ℂ) r f
  have hg : -(inner ℂ g (suzukiTaToFormCLM a z)).re ≤
      ‖g‖ * ‖suzukiTaToFormCLM a z‖ := by
    have h := re_inner_le_norm (𝕜 := ℂ) (-g) (suzukiTaToFormCLM a z)
    change (inner ℂ (-g) (suzukiTaToFormCLM a z)).re ≤ _ at h
    simpa only [inner_neg_left, Complex.neg_re, norm_neg] using h
  have hrf := mul_le_mul_of_nonneg_left hf (norm_nonneg r)
  have hgt := mul_le_mul_of_nonneg_left ht (norm_nonneg g)
  have hz : ‖z‖ ≤ ‖r‖ + ‖g‖ := by
    nlinarith only [hres, hr, hg, hrf, hgt, norm_nonneg z, norm_nonneg r, norm_nonneg g]
  exact hz

/-- The actual covariance response is uniformly approximated by the finite
source construction, retaining its original amplitude at the new aperture. -/
theorem eventually_suzukiTaSourceResponse_neumann_relative_error
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a, ∀ p : suzukiApertureHilbert ⟨a, ha⟩, ∀ V : ℝ,
      ‖p‖ ≤ V → CCMFiniteExponentialBudget (p : SoninL2) V →
      Real.exp (2 * a) * ‖ccmArchimedeanFormToAperture ⟨a, ha⟩
        (suzukiTaToFormCLM ⟨a, ha⟩ (suzukiTaSourceResponse ⟨a, ha⟩ p)) -
          ccmFiniteNeumannVector ⟨a, ha⟩ p ⌈a⌉₊‖ ^ 2 ≤ ε * V ^ 2 := by
  obtain ⟨D, E, hD, hE, hform⟩ := eventually_ccmFiniteExponentialSource_form_decay
  let F := 2 * E ^ 2 + 2 * D
  let L := F / ε
  have hF : 0 < F := by dsimp [F]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  filter_upwards [hform, eventually_suzukiTa_physical_coercivity L,
    eventually_ge_atTop (1 : ℝ)] with a haForm hfloor haOne
  intro ha p V hpNorm hpBudget
  let ap : SuzukiPositiveAperture := ⟨a, ha⟩
  let w := suzukiTaSourceResponse ap p
  let u := ccmFiniteNeumannVector ap p ⌈a⌉₊
  obtain ⟨g, hg, hgNorm, hrNorm⟩ := haForm ha p V hpNorm hpBudget
  let z := w - suzukiTaFromFormCLM ap g
  let r := p - ccmShiftedBoundedWeil ap u
  have hr : ‖r‖ ≤ E * V * Real.exp (-4 * a) := by simpa only [hg] using hrNorm
  have hr2 : ‖r‖ ^ 2 ≤ E ^ 2 * a * V ^ 2 * Real.exp (-2 * a) := by
    have hs : ‖r‖ ^ 2 ≤ (E * V * Real.exp (-4 * a)) ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg r) hr
    have he : (Real.exp (-4 * a)) ^ 2 = Real.exp (-8 * a) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    calc
      _ ≤ (E * V) ^ 2 * Real.exp (-8 * a) := hs.trans_eq (by rw [mul_pow, he])
      _ ≤ (E * V) ^ 2 * Real.exp (-2 * a) := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith)) (sq_nonneg _)
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_left haOne
          (mul_nonneg (sq_nonneg (E * V)) (Real.exp_pos (-2 * a)).le)
        nlinarith only [hm]
  have hz : ‖z‖ ≤ ‖r‖ + ‖g‖ := by
    have h := suzukiTaSourceResponse_form_residual_norm_le ap p g
    rw [hg] at h
    exact h
  have hz2 : ‖z‖ ^ 2 ≤ F * a * V ^ 2 * Real.exp (-2 * a) := by
    have hs : ‖z‖ ^ 2 ≤ (‖r‖ + ‖g‖) ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg z) hz
    dsimp [F]
    nlinarith only [hs, sq_nonneg (‖r‖ - ‖g‖), hr2, hgNorm]
  have hp : L * a * ‖suzukiTaPhysicalEmbedding ap z‖ ^ 2 ≤
      F * a * V ^ 2 * Real.exp (-2 * a) := (hfloor ha z).trans hz2
  have hscaled : L * (Real.exp (2 * a) * ‖suzukiTaPhysicalEmbedding ap z‖ ^ 2) ≤
      F * V ^ 2 := by
    apply le_of_mul_le_mul_left (a := a) ?_ ha
    calc
      _ = Real.exp (2 * a) * (L * a * ‖suzukiTaPhysicalEmbedding ap z‖ ^ 2) := by ring
      _ ≤ Real.exp (2 * a) * (F * a * V ^ 2 * Real.exp (-2 * a)) :=
        mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
      _ = a * (F * V ^ 2) := by
        rw [show Real.exp (2 * a) * (F * a * V ^ 2 * Real.exp (-2 * a)) =
          (a * (F * V ^ 2)) * (Real.exp (2 * a) * Real.exp (-(2 * a))) by ring,
          ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have hsmall : Real.exp (2 * a) * ‖suzukiTaPhysicalEmbedding ap z‖ ^ 2 ≤ ε * V ^ 2 := by
    apply le_of_mul_le_mul_left (a := L) ?_ hL
    calc
      _ ≤ F * V ^ 2 := hscaled
      _ = L * (ε * V ^ 2) := by dsimp [L]; field_simp
  have hphys : ‖suzukiTaPhysicalEmbedding ap z‖ =
      ‖ccmArchimedeanFormToAperture ap (suzukiTaToFormCLM ap w) - u‖ := by
    calc
      _ = ‖ccmArchimedeanFormToAperture ap (suzukiTaToFormCLM ap z)‖ :=
        (suzukiApertureL2Equiv ap).symm.norm_map _
      _ = _ := by
        dsimp only [z]
        rw [map_sub, suzukiTaToFormCLM_fromForm, map_sub, hg]
  rw [hphys] at hsmall
  exact hsmall

end RHTower
end
