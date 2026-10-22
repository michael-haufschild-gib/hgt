import GaloisForLFunctions.RHTower.Suzuki.SuzukiGrowingPhysicalCoercivity

open Filter
open scoped Topology
noncomputable section
namespace RHTower


/-- At the actual prescribed shift, the finite source construction approximates
the matched odd response even after the natural exponential rescaling. -/
theorem eventually_suzukiTaMatchedOdd_neumann_relative_error
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a,
      Real.exp a * ‖ccmArchimedeanFormToAperture ⟨a, ha⟩
        (suzukiTaToFormCLM ⟨a, ha⟩ (suzukiTaRawCoalescingOdd ⟨a, ha⟩ (1 / 2))) -
          ccmMatchedOddNeumannVector ⟨a, ha⟩ ⌈a⌉₊‖ ^ 2 < ε := by
  obtain ⟨D, E, hD, hE, hform⟩ := eventually_ccmMatchedOddNeumannVector_form_decay
  let F := 2 * E ^ 2 + 2 * D
  let L := 2 * F / ε
  have hF : 0 < F := by dsimp [F]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  filter_upwards [hform, eventually_suzukiTa_physical_coercivity L,
    eventually_ge_atTop (1 : ℝ)] with a haForm hfloor haOne
  intro ha
  let ap : SuzukiPositiveAperture := ⟨a, ha⟩
  let w := suzukiTaRawCoalescingOdd ap (1 / 2)
  let u := ccmMatchedOddNeumannVector ap ⌈a⌉₊
  obtain ⟨g, hg, hgNorm, hrNorm⟩ := haForm ha
  let z := w - suzukiTaFromFormCLM ap g
  let r := ccmMatchedOddPoleSource ap - ccmShiftedBoundedWeil ap u
  have hr : ‖r‖ ≤ E * Real.exp (-7 * a / 2) := by
    simpa only [hg] using hrNorm
  have hr2 : ‖r‖ ^ 2 ≤ E ^ 2 * a * Real.exp (-a) := by
    have hs : ‖r‖ ^ 2 ≤ (E * Real.exp (-7 * a / 2)) ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg r) hr
    have he : (Real.exp (-7 * a / 2)) ^ 2 = Real.exp (-7 * a) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    calc
      _ ≤ E ^ 2 * Real.exp (-7 * a) := hs.trans_eq (by rw [mul_pow, he])
      _ ≤ E ^ 2 * Real.exp (-a) := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith)) (sq_nonneg E)
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_left haOne
          (mul_nonneg (sq_nonneg E) (Real.exp_pos (-a)).le)
        nlinarith only [hm]
  have hz : ‖z‖ ≤ ‖r‖ + ‖g‖ := by
    have h := suzukiTaMatchedOdd_form_residual_norm_le ⟨a, ha⟩ g
    rw [hg] at h
    simpa only [z, w, r, u, ap] using h
  have hz2 : ‖z‖ ^ 2 ≤ F * a * Real.exp (-a) := by
    have hs : ‖z‖ ^ 2 ≤ (‖r‖ + ‖g‖) ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg z) hz
    dsimp [F]
    nlinarith only [hs, sq_nonneg (‖r‖ - ‖g‖), hr2, hgNorm]
  have hp : L * a * ‖suzukiTaPhysicalEmbedding ap z‖ ^ 2 ≤ F * a * Real.exp (-a) :=
    (hfloor ha z).trans hz2
  have hscaled : L * (Real.exp a * ‖suzukiTaPhysicalEmbedding ap z‖ ^ 2) ≤ F := by
    apply le_of_mul_le_mul_left (a := a) ?_ ha
    calc
      _ = Real.exp a * (L * a * ‖suzukiTaPhysicalEmbedding ap z‖ ^ 2) := by ring
      _ ≤ Real.exp a * (F * a * Real.exp (-a)) :=
        mul_le_mul_of_nonneg_left hp (Real.exp_pos a).le
      _ = a * F := by
        rw [show Real.exp a * (F * a * Real.exp (-a)) =
          (a * F) * (Real.exp a * Real.exp (-a)) by ring,
          ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have hLF : F < L * ε := by
    dsimp [L]
    rw [div_mul_cancel₀ _ hε.ne']
    linarith
  have hsmall : Real.exp a * ‖suzukiTaPhysicalEmbedding ap z‖ ^ 2 < ε :=
    lt_of_mul_lt_mul_left (hscaled.trans_lt hLF) hL.le
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

/-- Unconditional vanishing of the naturally rescaled physical approximation
error along positive apertures tending to infinity. -/
theorem tendsto_suzukiTaMatchedOdd_neumann_relative_error :
    Tendsto (fun a : SuzukiPositiveAperture => Real.exp a.1 *
      ‖ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a (suzukiTaRawCoalescingOdd a (1 / 2))) -
        ccmMatchedOddNeumannVector a ⌈a.1⌉₊‖ ^ 2)
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro ε hε
    exact Eventually.of_forall fun a => hε.trans_le
      (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  · intro ε hε
    have hv : Tendsto (fun a : SuzukiPositiveAperture => a.1)
        (comap (fun a : SuzukiPositiveAperture => a.1) atTop) atTop := tendsto_comap
    filter_upwards [hv.eventually (eventually_suzukiTaMatchedOdd_neumann_relative_error ε hε)]
      with a ha
    exact ha a.2

end RHTower
end
