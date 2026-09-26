import GaloisForLFunctions.HTGeometry.DigammaHalfPlaneAsymptotic

/-!
# A complex Stirling difference estimate for `log |Γ|`

Along any segment `[z₀, z₁]` contained in `Re w > 0` and at distance at least `m ≥ 2` from the
origin,

  `|(log|Γ(z₁)| − log|Γ(z₀)|) − Re((z₁ log z₁ − z₁) − (z₀ log z₀ − z₀))| ≤ 3‖z₁ − z₀‖/m`.

The derivative of `l ↦ log|Γ(w(l))|` along the segment is `Re(ψ(w)·(z₁ − z₀))`, the derivative of
`Re(w log w − w)` is `Re(log w·(z₁ − z₀))`, and `‖ψ(w) − log w‖ ≤ 3/‖w‖`
(`norm_digamma_sub_log_le_of_re_pos`); the mean value theorem closes the estimate.  Only *ratios* of
`|Γ|` enter, so no absolute Stirling constant is needed.
-/

open Complex Real Filter Topology

namespace HTGeometry

noncomputable section

/-- The derivative of the logarithmic modulus of a nonvanishing curve with logarithmic
derivative `D`. -/
theorem hasDerivAt_log_norm_of_mul_self {g : ℝ → ℂ} {D : ℂ} {x : ℝ}
    (hne : g x ≠ 0) (hg : HasDerivAt g (D * g x) x) :
    HasDerivAt (fun u => Real.log ‖g u‖) D.re x := by
  let q : ℝ → ℝ := fun u => ‖g u‖ ^ (2 : ℕ)
  have hinner : inner ℝ (g x) (D * g x) = q x * D.re := by
    rw [Complex.inner]
    dsimp [q]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hq : HasDerivAt q (2 * q x * D.re) x := by
    have hraw := hg.norm_sq
    simpa [q, hinner, mul_assoc] using hraw
  have hqpos : 0 < q x := by
    dsimp [q]
    exact sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hhalf := (hq.log hqpos.ne').const_mul (1 / 2 : ℝ)
  have hfun : (fun u => Real.log ‖g u‖) = fun u => 1 / 2 * Real.log (q u) := by
    funext u
    dsimp [q]
    rw [Real.log_pow]
    push_cast
    ring
  rw [hfun]
  refine hhalf.congr_deriv ?_
  field_simp

/-- The Stirling main part `w log w − w`, whose derivative on the slit plane is `log w`. -/
def stirlingMain (w : ℂ) : ℂ := w * Complex.log w - w

theorem hasDerivAt_stirlingMain {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    HasDerivAt stirlingMain (Complex.log w) w := by
  have hw0 : w ≠ 0 := Complex.slitPlane_ne_zero hw
  have h := ((hasDerivAt_id w).mul (Complex.hasDerivAt_log hw)).sub (hasDerivAt_id w)
  refine h.congr_deriv ?_
  simp [hw0]

/-- **Complex Stirling difference.**  Along a segment in `Re > 0` staying at distance `≥ m ≥ 2`
from the origin, `log|Γ|` differs from `Re(w log w − w)` by at most `3‖z₁ − z₀‖/m`. -/
theorem abs_log_norm_Gamma_sub_stirlingMain_le {z₀ z₁ : ℂ} {m : ℝ} (hm : 2 ≤ m)
    (hseg : ∀ l ∈ Set.Icc (0 : ℝ) 1,
      0 < (z₀ + (l : ℂ) * (z₁ - z₀)).re ∧ m ≤ ‖z₀ + (l : ℂ) * (z₁ - z₀)‖) :
    |(Real.log ‖Complex.Gamma z₁‖ - Real.log ‖Complex.Gamma z₀‖)
        - (stirlingMain z₁ - stirlingMain z₀).re| ≤ 3 * ‖z₁ - z₀‖ / m := by
  set w : ℝ → ℂ := fun l => z₀ + (l : ℂ) * (z₁ - z₀) with hw
  set φ : ℝ → ℝ := fun l => Real.log ‖Complex.Gamma (w l)‖ - (stirlingMain (w l)).re with hφ
  set φ' : ℝ → ℝ := fun l => ((Complex.digamma (w l) - Complex.log (w l)) * (z₁ - z₀)).re
  have hwd : ∀ l : ℝ, HasDerivAt w (z₁ - z₀) l := by
    intro l
    have := ((hasDerivAt_id (l : ℝ)).ofReal_comp).mul_const (z₁ - z₀)
    simpa [hw] using this.const_add z₀
  have hderiv : ∀ l ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ (φ' l) l := by
    intro l hl
    obtain ⟨hre, hnorm⟩ := hseg l hl
    have hslit : w l ∈ Complex.slitPlane := Or.inl hre
    have hnotpole : ∀ n : ℕ, w l ≠ -n := by
      intro n h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hΓ : Complex.Gamma (w l) ≠ 0 := Complex.Gamma_ne_zero hnotpole
    have hΓd : HasDerivAt Complex.Gamma (Complex.digamma (w l) * Complex.Gamma (w l)) (w l) := by
      have hd := (Complex.differentiableAt_Gamma _ hnotpole).hasDerivAt
      refine hd.congr_deriv ?_
      rw [Complex.digamma_def, logDeriv_apply]
      field_simp
    have h1 := hasDerivAt_log_norm_of_mul_self (g := fun u => Complex.Gamma (w u)) (x := l)
      (D := Complex.digamma (w l) * (z₁ - z₀)) hΓ
      ((hΓd.comp l (hwd l)).congr_deriv (by ring))
    have h2 := (hasDerivAt_stirlingMain hslit).comp l (hwd l)
    have h2re := Complex.reCLM.hasFDerivAt.comp_hasDerivAt l h2
    refine (h1.sub h2re).congr_deriv ?_
    simp only [Complex.reCLM_apply, φ']
    rw [sub_mul, Complex.sub_re]
  have hbound : ∀ l ∈ Set.Ico (0 : ℝ) 1, ‖φ' l‖ ≤ 3 * ‖z₁ - z₀‖ / m := by
    intro l hl
    obtain ⟨hre, hnorm⟩ := hseg l (Set.Ico_subset_Icc_self hl)
    have hdig := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_le_of_re_pos hre (by linarith)
    have hmpos : 0 < m := by linarith
    calc ‖φ' l‖ ≤ ‖(Complex.digamma (w l) - Complex.log (w l)) * (z₁ - z₀)‖ := by
          simp only [φ', Real.norm_eq_abs]
          exact Complex.abs_re_le_norm _
      _ = ‖Complex.digamma (w l) - Complex.log (w l)‖ * ‖z₁ - z₀‖ := norm_mul _ _
      _ ≤ (3 / ‖w l‖) * ‖z₁ - z₀‖ := by gcongr
      _ ≤ (3 / m) * ‖z₁ - z₀‖ := by
          gcongr
      _ = 3 * ‖z₁ - z₀‖ / m := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun l hl => (hderiv l hl).hasDerivWithinAt) hbound 1 (Set.right_mem_Icc.mpr zero_le_one)
  have hw0 : w 0 = z₀ := by simp [hw]
  have hw1 : w 1 = z₁ := by simp [hw]
  simp only [hφ, hw0, hw1, Real.norm_eq_abs, sub_zero, mul_one] at hmv
  convert hmv using 2
  simp only [Complex.sub_re]
  ring

end

end HTGeometry
