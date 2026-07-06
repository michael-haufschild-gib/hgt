/-
The off-line decay of the χ-factor, and the unconditional off-line certificate floor.

On the critical line `‖zetaChi‖ = 1`; off it the χ-factor decays. Using the exact modulus
`‖zetaChi z‖ = π^{Re z − ½}·‖Γ((1−z)/2)‖/‖Γ(z/2)‖`, the Gamma ratio is controlled by integrating the
(now unconditional) vertical digamma bound `Re ψ(x+iy) ≈ ½ log(x²+y²)` across the real part
(FTC for `log‖Γ‖`, whose derivative is `Re ψ`). This gives `‖zetaChi(σ+it)‖ < 1` for `σ ∈ (½,1)` and
`t` large. Consequently the certificate floor reduces to a pure Dirichlet-polynomial domination: the
χ-factor is discharged, and the off-line floor `ε < ‖gN‖` holds whenever the Dirichlet part dominates
its reflection.
-/
import GaloisForLFunctions.RHTower.DigammaAsymptotic
import GaloisForLFunctions.RHTower.RouteBOfflineDomination

open Complex Set intervalIntegral MeasureTheory Real

namespace RHTower

theorem norm_zetaChi_lt_one {σ t : ℝ} (hσ1 : 1/2 < σ) (hσ2 : σ < 1) (ht : 0 < t)
    (hlarge : Real.log Real.pi + (1/(t/2)^2 + Real.pi/(2*(t/2))) < Real.log (t/2)) :
    ‖zetaChi ((σ:ℂ) + (t:ℂ) * I)‖ < 1 := by
  set z : ℂ := (σ:ℂ) + (t:ℂ) * I with hzdef
  set a : ℝ := (1 - σ) / 2 with hadef
  set b : ℝ := σ / 2 with hbdef
  set y : ℝ := t / 2 with hydef
  have hy0 : 0 < y := by rw [hydef]; linarith
  have ha0 : 0 ≤ a := by rw [hadef]; linarith
  have hab : a ≤ b := by rw [hadef, hbdef]; linarith
  have hba : b - a = σ - 1/2 := by rw [hadef, hbdef]; ring
  have hzre : z.re = σ := by rw [hzdef]; simp
  -- norm rewrites
  have h1z : (1 - z) / 2 = (a:ℂ) - (y:ℂ) * I := by rw [hzdef, hadef, hydef]; push_cast; ring
  have hnorm1 : ‖Complex.Gamma ((1 - z) / 2)‖ = ‖Complex.Gamma ((a:ℂ) + (y:ℂ) * I)‖ := by
    rw [h1z, show (a:ℂ) - (y:ℂ) * I = (starRingEnd ℂ) ((a:ℂ) + (y:ℂ) * I) by
      rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]; ring,
      Complex.Gamma_conj, RCLike.norm_conj]
  have h2z : z / 2 = (b:ℂ) + (y:ℂ) * I := by rw [hzdef, hbdef, hydef]; push_cast; ring
  have hnorm2 : ‖Complex.Gamma (z / 2)‖ = ‖Complex.Gamma ((b:ℂ) + (y:ℂ) * I)‖ := by rw [h2z]
  -- Gamma nonzero
  have hΓne : ∀ w : ℝ, Complex.Gamma ((w:ℂ) + (y:ℂ) * I) ≠ 0 := by
    intro w
    apply Complex.Gamma_ne_zero
    intro m hc
    have him := congrArg Complex.im hc
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.ofReal_re,
      Complex.I_re, mul_zero, mul_one, zero_add, add_zero, Complex.neg_im, Complex.natCast_im,
      neg_zero] at him
    linarith
  have hga : 0 < ‖Complex.Gamma ((a:ℂ) + (y:ℂ) * I)‖ := norm_pos_iff.mpr (hΓne a)
  have hgb : 0 < ‖Complex.Gamma ((b:ℂ) + (y:ℂ) * I)‖ := norm_pos_iff.mpr (hΓne b)
  set C : ℝ := 1 / y ^ 2 + Real.pi / (2 * y) with hCdef
  -- FTC + lower bound
  have hftc := ftc_log_norm_Gamma (a := a) (b := b) hy0
  have hintge : (b - a) * (Real.log y - C)
      ≤ ∫ x in a..b, (Complex.digamma ((x:ℂ) + (y:ℂ) * I)).re := by
    rw [← hCdef] at *
    have hconst : ∫ _x in a..b, (Real.log y - C) = (b - a) * (Real.log y - C) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [← hconst]
    apply intervalIntegral.integral_mono_on hab
    · exact intervalIntegral.intervalIntegrable_const
    · apply ContinuousOn.intervalIntegrable
      have hφ : ContinuousOn (fun x : ℝ => (x:ℂ) + (y:ℂ) * I) (Set.uIcc a b) := by fun_prop
      have hmaps : Set.MapsTo (fun x : ℝ => (x:ℂ) + (y:ℂ) * I) (Set.uIcc a b) {z : ℂ | 0 < z.im} := by
        intro x _
        simp only [Set.mem_setOf_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.I_im, Complex.ofReal_re, Complex.I_re, mul_zero, mul_one, zero_add, add_zero]
        exact hy0
      exact Complex.continuous_re.comp_continuousOn (digamma_continuousOn_uhp.comp hφ hmaps)
    · intro x hx
      rw [Set.mem_Icc] at hx
      exact re_digamma_ge (by linarith [hx.1]) hy0
  -- log ratio bound
  have hlogratio : (σ - 1/2) * (Real.log y - C)
      ≤ Real.log ‖Complex.Gamma ((b:ℂ) + (y:ℂ) * I)‖
        - Real.log ‖Complex.Gamma ((a:ℂ) + (y:ℂ) * I)‖ := by
    rw [← hftc, ← hba]; exact hintge
  -- assemble: ‖zetaChi‖ = π^{σ-1/2}·‖Γa‖/‖Γb‖ = exp(...)
  rw [norm_zetaChi_eq z, hnorm1, hnorm2, hzre]
  have hpi : Real.pi ^ (σ - 1/2) = Real.exp ((σ - 1/2) * Real.log Real.pi) := by
    rw [Real.rpow_def_of_pos Real.pi_pos]; ring_nf
  have hexpr : Real.pi ^ (σ - 1/2) * ‖Complex.Gamma ((a:ℂ) + (y:ℂ) * I)‖
        / ‖Complex.Gamma ((b:ℂ) + (y:ℂ) * I)‖
      = Real.exp ((σ - 1/2) * Real.log Real.pi
          + (Real.log ‖Complex.Gamma ((a:ℂ) + (y:ℂ) * I)‖
            - Real.log ‖Complex.Gamma ((b:ℂ) + (y:ℂ) * I)‖)) := by
    rw [Real.exp_add, hpi, Real.exp_sub, Real.exp_log hga, Real.exp_log hgb]
    ring
  rw [hexpr]
  apply Real.exp_lt_one_iff.mpr
  have hσpos : 0 < σ - 1/2 := by linarith
  have key : (σ - 1/2) * Real.log Real.pi
        + (Real.log ‖Complex.Gamma ((a:ℂ) + (y:ℂ) * I)‖
          - Real.log ‖Complex.Gamma ((b:ℂ) + (y:ℂ) * I)‖)
      ≤ (σ - 1/2) * (Real.log Real.pi - Real.log y + C) := by nlinarith [hlogratio]
  have hfinal : (σ - 1/2) * (Real.log Real.pi - Real.log y + C) < 0 :=
    mul_neg_of_pos_of_neg hσpos (by linarith [hlarge])
  exact lt_of_le_of_lt key hfinal


/-- With `‖zetaChi z‖ ≤ 1` (proven off the line), the certificate floor reduces to a pure
Dirichlet-polynomial domination `‖D(1−z)‖ + ε < ‖D z‖`: the χ-factor is discharged. -/
theorem norm_gN_ge_of_dirichlet_domination {N : ℕ} {z : ℂ} {ε : ℝ}
    (hχ : ‖zetaChi z‖ ≤ 1)
    (hD : ‖dirichletPoly N (1 - z)‖ + ε < ‖dirichletPoly N z‖) :
    ε < ‖gN N z‖ := by
  have hdom : ‖zetaChi z * dirichletPoly N (1 - z)‖ + ε < ‖dirichletPoly N z‖ := by
    rw [norm_mul]
    have : ‖zetaChi z‖ * ‖dirichletPoly N (1 - z)‖ ≤ ‖dirichletPoly N (1 - z)‖ := by
      nlinarith [mul_le_mul_of_nonneg_right hχ (norm_nonneg (dirichletPoly N (1 - z))), norm_nonneg (dirichletPoly N (1 - z))]
    linarith
  have hgn : gN N z = dirichletPoly N z + zetaChi z * dirichletPoly N (1 - z) := rfl
  have key : ‖dirichletPoly N z‖ ≤ ‖gN N z‖ + ‖zetaChi z * dirichletPoly N (1 - z)‖ := by
    rw [show dirichletPoly N z = gN N z - zetaChi z * dirichletPoly N (1 - z) by rw [hgn]; ring]
    exact norm_sub_le _ _
  linarith

/-- **Unconditional off-line floor.** For `σ ∈ (½,1)` and `t` large, `‖zetaChi(σ+it)‖ < 1` is a
theorem, so the certificate floor `ε < ‖gN N(σ+it)‖` holds as soon as the Dirichlet part dominates its
reflection: `‖dirichletPoly N(1−z)‖ + ε < ‖dirichletPoly N z‖`. The χ-factor is no longer an assumption. -/
theorem norm_gN_ge_offline {N : ℕ} {σ t ε : ℝ} (hσ1 : 1/2 < σ) (hσ2 : σ < 1) (ht : 0 < t)
    (hlarge : Real.log Real.pi + (1/(t/2)^2 + Real.pi/(2*(t/2))) < Real.log (t/2))
    (hD : ‖dirichletPoly N (1 - ((σ:ℂ) + (t:ℂ) * I))‖ + ε
        < ‖dirichletPoly N ((σ:ℂ) + (t:ℂ) * I)‖) :
    ε < ‖gN N ((σ:ℂ) + (t:ℂ) * I)‖ :=
  norm_gN_ge_of_dirichlet_domination (le_of_lt (norm_zetaChi_lt_one hσ1 hσ2 ht hlarge)) hD

end RHTower

namespace RHTower

/-- **Left-strip χ envelope.** For `0 < σ ≤ 1/2`, the vertical digamma bound and
FTC for `log ‖Γ‖` give an explicit upper bound for `‖χ(σ+it)‖`.  This is the
large side of the line-centered circle envelope: the worst χ-growth comes from
the left arc, while the right arc is handled by `norm_zetaChi_lt_one`. -/
theorem norm_zetaChi_le_left_line {σ t : ℝ} (hσ0 : 0 < σ) (hσ2 : σ ≤ 1 / 2) (ht : 0 < t) :
    ‖zetaChi ((σ:ℂ) + (t:ℂ) * I)‖ ≤
      Real.exp ((1 / 2 - σ) *
        ((1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + (t / 2) ^ 2)
          + (1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2))) - Real.log Real.pi)) := by
  set z : ℂ := (σ:ℂ) + (t:ℂ) * I with hzdef
  set a : ℝ := σ / 2 with hadef
  set b : ℝ := (1 - σ) / 2 with hbdef
  set y : ℝ := t / 2 with hydef
  have hy0 : 0 < y := by rw [hydef]; linarith
  have ha0 : 0 ≤ a := by rw [hadef]; linarith
  have hab : a ≤ b := by rw [hadef, hbdef]; linarith
  have hb_le : b ≤ 1 / 2 := by rw [hbdef]; linarith
  have hba : b - a = 1 / 2 - σ := by rw [hadef, hbdef]; ring
  have hzre : z.re = σ := by rw [hzdef]; simp
  have h1z : (1 - z) / 2 = (b:ℂ) - (y:ℂ) * I := by rw [hzdef, hbdef, hydef]; push_cast; ring
  have hnorm1 : ‖Complex.Gamma ((1 - z) / 2)‖ = ‖Complex.Gamma ((b:ℂ) + (y:ℂ) * I)‖ := by
    rw [h1z, show (b:ℂ) - (y:ℂ) * I = (starRingEnd ℂ) ((b:ℂ) + (y:ℂ) * I) by
      rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]; ring,
      Complex.Gamma_conj, RCLike.norm_conj]
  have h2z : z / 2 = (a:ℂ) + (y:ℂ) * I := by rw [hzdef, hadef, hydef]; push_cast; ring
  have hnorm2 : ‖Complex.Gamma (z / 2)‖ = ‖Complex.Gamma ((a:ℂ) + (y:ℂ) * I)‖ := by rw [h2z]
  have hΓne : ∀ w : ℝ, Complex.Gamma ((w:ℂ) + (y:ℂ) * I) ≠ 0 := by
    intro w
    apply Complex.Gamma_ne_zero
    intro m hc
    have him := congrArg Complex.im hc
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.ofReal_re,
      Complex.I_re, mul_zero, mul_one, zero_add, add_zero, Complex.neg_im, Complex.natCast_im,
      neg_zero] at him
    linarith
  have hga : 0 < ‖Complex.Gamma ((a:ℂ) + (y:ℂ) * I)‖ := norm_pos_iff.mpr (hΓne a)
  have hgb : 0 < ‖Complex.Gamma ((b:ℂ) + (y:ℂ) * I)‖ := norm_pos_iff.mpr (hΓne b)
  set C : ℝ := 1 / y ^ 2 + Real.pi / (2 * y) with hCdef
  set L : ℝ := (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + y ^ 2) + C with hLdef
  have hftc := ftc_log_norm_Gamma (a := a) (b := b) hy0
  have hintle : ∫ x in a..b, (Complex.digamma ((x:ℂ) + (y:ℂ) * I)).re ≤ (b - a) * L := by
    have hconst : ∫ _x in a..b, L = (b - a) * L := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [← hconst]
    apply intervalIntegral.integral_mono_on hab
    · apply ContinuousOn.intervalIntegrable
      have hφ : ContinuousOn (fun x : ℝ => (x:ℂ) + (y:ℂ) * I) (Set.uIcc a b) := by fun_prop
      have hmaps : Set.MapsTo (fun x : ℝ => (x:ℂ) + (y:ℂ) * I) (Set.uIcc a b) {z : ℂ | 0 < z.im} := by
        intro x _
        simp only [Set.mem_setOf_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.I_im, Complex.ofReal_re, Complex.I_re, mul_zero, mul_one, zero_add, add_zero]
        exact hy0
      exact Complex.continuous_re.comp_continuousOn (digamma_continuousOn_uhp.comp hφ hmaps)
    · exact intervalIntegral.intervalIntegrable_const
    · intro x hx
      rw [Set.mem_Icc] at hx
      have hx0 : 0 ≤ x := by linarith [ha0, hx.1]
      have hxle : x ≤ 1 / 2 := by linarith [hb_le, hx.2]
      have hbnd := re_digamma_vertical_bound_uncond hx0 hy0
      have habs := abs_le.mp hbnd
      have hcenter_le : (1 / 2 : ℝ) * Real.log (x ^ 2 + y ^ 2)
          ≤ (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + y ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.log_le_log (by positivity)
        have hx_sq : x ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith [hx0, hxle]
        nlinarith
      have hpsi_le : (↑x + ↑y * I).digamma.re ≤ (1 / 2 : ℝ) * Real.log (x ^ 2 + y ^ 2) + C := by
        rw [hCdef]
        linarith [habs.2]
      have hcenterC_le : (1 / 2 : ℝ) * Real.log (x ^ 2 + y ^ 2) + C ≤ L := by
        rw [hLdef]
        linarith [hcenter_le]
      exact le_trans hpsi_le hcenterC_le
  have hlogratio : Real.log ‖Complex.Gamma ((b:ℂ) + (y:ℂ) * I)‖
        - Real.log ‖Complex.Gamma ((a:ℂ) + (y:ℂ) * I)‖ ≤ (b - a) * L := by
    rw [← hftc]
    exact hintle
  rw [norm_zetaChi_eq z, hnorm1, hnorm2, hzre]
  have hpi : Real.pi ^ (σ - 1 / 2) = Real.exp ((σ - 1 / 2) * Real.log Real.pi) := by
    rw [Real.rpow_def_of_pos Real.pi_pos]; ring_nf
  have hexpr : Real.pi ^ (σ - 1 / 2) * ‖Complex.Gamma ((b:ℂ) + (y:ℂ) * I)‖
        / ‖Complex.Gamma ((a:ℂ) + (y:ℂ) * I)‖
      = Real.exp ((σ - 1 / 2) * Real.log Real.pi
          + (Real.log ‖Complex.Gamma ((b:ℂ) + (y:ℂ) * I)‖
            - Real.log ‖Complex.Gamma ((a:ℂ) + (y:ℂ) * I)‖)) := by
    rw [Real.exp_add, hpi, Real.exp_sub, Real.exp_log hgb, Real.exp_log hga]
    ring
  rw [hexpr]
  apply Real.exp_le_exp.mpr
  have htarget : (1 / 2 - σ) *
        ((1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + (t / 2) ^ 2)
          + (1 / (t / 2) ^ 2 + Real.pi / (2 * (t / 2))) - Real.log Real.pi)
      = (b - a) * (L - Real.log Real.pi) := by
    rw [hba, hLdef, hCdef, hydef]
  rw [htarget]
  have hsig : σ - 1 / 2 = -(b - a) := by linarith [hba]
  calc (σ - 1 / 2) * Real.log Real.pi
          + (Real.log ‖Complex.Gamma ((b:ℂ) + (y:ℂ) * I)‖
            - Real.log ‖Complex.Gamma ((a:ℂ) + (y:ℂ) * I)‖)
      ≤ (σ - 1 / 2) * Real.log Real.pi + (b - a) * L := by linarith [hlogratio]
    _ = (b - a) * (L - Real.log Real.pi) := by rw [hsig]; ring

end RHTower

namespace RHTower

/-- Geometry of a circle centered on the critical line: points on
`sphere(1/2+iτ,RJ)` have real and imaginary coordinates within `RJ` of the
center coordinates. -/
theorem line_sphere_re_im_bounds {τ RJ : ℝ} {z : ℂ}
    (hz : z ∈ Metric.sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ) :
    |z.re - 1 / 2| ≤ RJ ∧ |z.im - τ| ≤ RJ := by
  have hdist : ‖z - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ = RJ := by
    rw [← dist_eq_norm]
    exact Metric.mem_sphere.mp hz
  constructor
  · calc |z.re - 1 / 2|
        = |(z - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)).re| := by simp [Complex.sub_re]
      _ ≤ ‖z - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := Complex.abs_re_le_norm _
      _ = RJ := hdist
  · calc |z.im - τ|
        = |(z - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)).im| := by simp [Complex.sub_im]
      _ ≤ ‖z - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := Complex.abs_im_le_norm _
      _ = RJ := hdist

/-- **Left-arc χ circle envelope from finite scalar data.**  On the left half of
`sphere(1/2+iτ,RJ)`, the line bound `norm_zetaChi_le_left_line` is dominated by
one radius/height scalar `K`; if `exp(RJ*K) ≤ χB`, then the whole left arc has
`‖χ‖ ≤ χB`. -/
theorem norm_zetaChi_le_left_line_sphere {τ RJ χB K : ℝ}
    (hRJ12 : RJ < 1 / 2) (hheight : RJ < τ)
    (hK : K = (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + ((τ + RJ) / 2) ^ 2)
      + (1 / ((τ - RJ) / 2) ^ 2 + Real.pi / (2 * ((τ - RJ) / 2))) - Real.log Real.pi)
    (hK0 : 0 ≤ K) (hbudget : Real.exp (RJ * K) ≤ χB) :
    ∀ z ∈ Metric.sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      z.re ≤ 1 / 2 → ‖zetaChi z‖ ≤ χB := by
  intro z hz hleft
  obtain ⟨hre_abs, him_abs⟩ := line_sphere_re_im_bounds (τ := τ) (RJ := RJ) hz
  have hdist : ‖z - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ = RJ := by
    rw [← dist_eq_norm]
    exact Metric.mem_sphere.mp hz
  have hRJ0 : 0 ≤ RJ := by
    rw [← hdist]
    exact norm_nonneg _
  have hre_ge : 1 / 2 - RJ ≤ z.re := by
    have := (abs_le.mp hre_abs).1
    linarith
  have hsig0 : 0 < z.re := by linarith
  have hwidth0 : 0 ≤ 1 / 2 - z.re := by linarith
  have hwidth_le : 1 / 2 - z.re ≤ RJ := by
    have := (abs_le.mp hre_abs).1
    linarith
  have him_ge : τ - RJ ≤ z.im := by
    have := (abs_le.mp him_abs).1
    linarith
  have him_le : z.im ≤ τ + RJ := by
    have := (abs_le.mp him_abs).2
    linarith
  have him_pos : 0 < z.im := by linarith
  have hz_decomp : ((z.re : ℂ) + (z.im : ℂ) * I) = z := by
    apply Complex.ext <;> simp
  have hline := norm_zetaChi_le_left_line (σ := z.re) (t := z.im) hsig0 hleft him_pos
  rw [hz_decomp] at hline
  set Kz : ℝ := (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + (z.im / 2) ^ 2)
      + (1 / (z.im / 2) ^ 2 + Real.pi / (2 * (z.im / 2))) - Real.log Real.pi with hKzdef
  have hy0pos : 0 < (τ - RJ) / 2 := by linarith
  have hzhalf_pos : 0 < z.im / 2 := by linarith
  have hzhalf_nonneg : 0 ≤ z.im / 2 := le_of_lt hzhalf_pos
  have hy1_nonneg : 0 ≤ (τ + RJ) / 2 := by linarith
  have hy_low : (τ - RJ) / 2 ≤ z.im / 2 := by linarith
  have hy_high : z.im / 2 ≤ (τ + RJ) / 2 := by linarith
  have hsq_high : (z.im / 2) ^ 2 ≤ ((τ + RJ) / 2) ^ 2 := by
    nlinarith [hzhalf_nonneg, hy_high, hy1_nonneg]
  have hlog_le : (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + (z.im / 2) ^ 2)
      ≤ (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + ((τ + RJ) / 2) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.log_le_log (by positivity)
    nlinarith [hsq_high]
  have hsq_low : ((τ - RJ) / 2) ^ 2 ≤ (z.im / 2) ^ 2 := by
    nlinarith [hy0pos.le, hy_low, hzhalf_nonneg]
  have hden_low_pos : 0 < ((τ - RJ) / 2) ^ 2 := by positivity
  have hinv_sq : 1 / (z.im / 2) ^ 2 ≤ 1 / ((τ - RJ) / 2) ^ 2 := by
    exact one_div_le_one_div_of_le hden_low_pos hsq_low
  have hinv : 1 / (z.im / 2) ≤ 1 / ((τ - RJ) / 2) := by
    exact one_div_le_one_div_of_le hy0pos hy_low
  have hfrac : Real.pi / (2 * (z.im / 2)) ≤ Real.pi / (2 * ((τ - RJ) / 2)) := by
    have hmul := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ Real.pi / 2)
    have hleftfrac : Real.pi / (2 * (z.im / 2)) = (Real.pi / 2) * (1 / (z.im / 2)) := by
      field_simp [ne_of_gt hzhalf_pos]
    have hrightfrac : Real.pi / (2 * ((τ - RJ) / 2)) = (Real.pi / 2) * (1 / ((τ - RJ) / 2)) := by
      field_simp [ne_of_gt hy0pos]
    rw [hleftfrac, hrightfrac]
    exact hmul
  have hKz_le : Kz ≤ K := by
    rw [hK, hKzdef]
    linarith [hlog_le, hinv_sq, hfrac]
  have hexp_le : Real.exp ((1 / 2 - z.re) * Kz) ≤ Real.exp (RJ * K) := by
    apply Real.exp_le_exp.mpr
    have hprod1 : (1 / 2 - z.re) * Kz ≤ (1 / 2 - z.re) * K := by
      exact mul_le_mul_of_nonneg_left hKz_le hwidth0
    have hprod2 : (1 / 2 - z.re) * K ≤ RJ * K := by
      exact mul_le_mul_of_nonneg_right hwidth_le hK0
    exact le_trans hprod1 hprod2
  have hline' : ‖zetaChi z‖ ≤ Real.exp ((1 / 2 - z.re) * Kz) := by
    simpa [Kz] using hline
  exact le_trans hline' (le_trans hexp_le hbudget)

end RHTower

namespace RHTower

/-- **Right-arc χ circle envelope from finite scalar data.**  On the right half of
`sphere(1/2+iτ,RJ)`, the off-line decay theorem gives `‖χ‖ < 1`; the boundary
case `Re z = 1/2` is handled by critical-line unimodularity.  The pointwise
height condition is reduced to the single bottom-height scalar inequality at
`(τ-RJ)/2`. -/
theorem norm_zetaChi_le_right_line_sphere {τ RJ χB : ℝ}
    (hRJ12 : RJ < 1 / 2) (hheight : RJ < τ)
    (hlarge : Real.log Real.pi + (1 / ((τ - RJ) / 2) ^ 2
      + Real.pi / (2 * ((τ - RJ) / 2))) < Real.log ((τ - RJ) / 2))
    (hχB1 : 1 ≤ χB) :
    ∀ z ∈ Metric.sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      1 / 2 ≤ z.re → ‖zetaChi z‖ ≤ χB := by
  intro z hz hright
  obtain ⟨hre_abs, him_abs⟩ := line_sphere_re_im_bounds (τ := τ) (RJ := RJ) hz
  have hre_le : z.re ≤ 1 / 2 + RJ := by
    have := (abs_le.mp hre_abs).2
    linarith
  have hσ2 : z.re < 1 := by linarith
  have him_ge : τ - RJ ≤ z.im := by
    have := (abs_le.mp him_abs).1
    linarith
  have him_pos : 0 < z.im := by linarith
  have hy0pos : 0 < (τ - RJ) / 2 := by linarith
  have hzhalf_pos : 0 < z.im / 2 := by linarith
  have hy_low : (τ - RJ) / 2 ≤ z.im / 2 := by linarith
  have hlog_low : Real.log ((τ - RJ) / 2) ≤ Real.log (z.im / 2) :=
    Real.log_le_log hy0pos hy_low
  have hsq_low : ((τ - RJ) / 2) ^ 2 ≤ (z.im / 2) ^ 2 := by
    nlinarith [hy0pos.le, hy_low, hzhalf_pos.le]
  have hden_low_pos : 0 < ((τ - RJ) / 2) ^ 2 := by positivity
  have hinv_sq : 1 / (z.im / 2) ^ 2 ≤ 1 / ((τ - RJ) / 2) ^ 2 := by
    exact one_div_le_one_div_of_le hden_low_pos hsq_low
  have hinv : 1 / (z.im / 2) ≤ 1 / ((τ - RJ) / 2) := by
    exact one_div_le_one_div_of_le hy0pos hy_low
  have hfrac : Real.pi / (2 * (z.im / 2)) ≤ Real.pi / (2 * ((τ - RJ) / 2)) := by
    have hmul := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ Real.pi / 2)
    have hleftfrac : Real.pi / (2 * (z.im / 2)) = (Real.pi / 2) * (1 / (z.im / 2)) := by
      field_simp [ne_of_gt hzhalf_pos]
    have hrightfrac : Real.pi / (2 * ((τ - RJ) / 2)) =
        (Real.pi / 2) * (1 / ((τ - RJ) / 2)) := by
      field_simp [ne_of_gt hy0pos]
    rw [hleftfrac, hrightfrac]
    exact hmul
  have hlarge_z : Real.log Real.pi + (1 / (z.im / 2) ^ 2
      + Real.pi / (2 * (z.im / 2))) < Real.log (z.im / 2) := by
    have hleft_le : Real.log Real.pi + (1 / (z.im / 2) ^ 2
        + Real.pi / (2 * (z.im / 2))) ≤ Real.log Real.pi
        + (1 / ((τ - RJ) / 2) ^ 2 + Real.pi / (2 * ((τ - RJ) / 2))) := by
      linarith [hinv_sq, hfrac]
    exact lt_of_le_of_lt hleft_le (lt_of_lt_of_le hlarge hlog_low)
  by_cases hline : z.re = 1 / 2
  · rw [zetaChi_norm_on_line hline]
    exact hχB1
  · have hstrict : 1 / 2 < z.re := by
      by_contra hnot
      have hle : z.re ≤ 1 / 2 := le_of_not_gt hnot
      exact hline (le_antisymm hle hright)
    have hz_decomp : ((z.re : ℂ) + (z.im : ℂ) * I) = z := by
      apply Complex.ext <;> simp
    have hχlt := norm_zetaChi_lt_one (σ := z.re) (t := z.im) hstrict hσ2 him_pos hlarge_z
    rw [hz_decomp] at hχlt
    exact le_trans (le_of_lt hχlt) hχB1

/-- **Full χ circle envelope from finite scalar data.**  The left arc is controlled by
the explicit growth scalar `K`; the right arc and critical-line boundary are controlled
by the bottom-height decay inequality and `1 ≤ χB`. -/
theorem norm_zetaChi_le_line_sphere {τ RJ χB K : ℝ}
    (hRJ12 : RJ < 1 / 2) (hheight : RJ < τ)
    (hK : K = (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + ((τ + RJ) / 2) ^ 2)
      + (1 / ((τ - RJ) / 2) ^ 2 + Real.pi / (2 * ((τ - RJ) / 2))) - Real.log Real.pi)
    (hK0 : 0 ≤ K) (hleftBudget : Real.exp (RJ * K) ≤ χB)
    (hrightLarge : Real.log Real.pi + (1 / ((τ - RJ) / 2) ^ 2
      + Real.pi / (2 * ((τ - RJ) / 2))) < Real.log ((τ - RJ) / 2))
    (hχB1 : 1 ≤ χB) :
    ∀ z ∈ Metric.sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖zetaChi z‖ ≤ χB := by
  intro z hz
  by_cases hleft : z.re ≤ 1 / 2
  · exact norm_zetaChi_le_left_line_sphere
      (τ := τ) (RJ := RJ) (χB := χB) (K := K)
      hRJ12 hheight hK hK0 hleftBudget z hz hleft
  · have hright : 1 / 2 ≤ z.re := le_of_lt (lt_of_not_ge hleft)
    exact norm_zetaChi_le_right_line_sphere
      (τ := τ) (RJ := RJ) (χB := χB)
      hRJ12 hheight hrightLarge hχB1 z hz hright

end RHTower

namespace RHTower

/-- **Left-arc χ circle envelope from an external scalar upper bound.**  This is the
monotone form of `norm_zetaChi_le_left_line_sphere`: the center-height scalar may be
bounded by any nonnegative `K`, so a whole window can use one top/bottom scalar. -/
theorem norm_zetaChi_le_left_line_sphere_of_K_bound {τ RJ χB K : ℝ}
    (hRJ12 : RJ < 1 / 2) (hheight : RJ < τ)
    (hK0 : 0 ≤ K)
    (hKbound : (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + ((τ + RJ) / 2) ^ 2)
      + (1 / ((τ - RJ) / 2) ^ 2 + Real.pi / (2 * ((τ - RJ) / 2))) - Real.log Real.pi ≤ K)
    (hbudget : Real.exp (RJ * K) ≤ χB) :
    ∀ z ∈ Metric.sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      z.re ≤ 1 / 2 → ‖zetaChi z‖ ≤ χB := by
  intro z hz hleft
  obtain ⟨hre_abs, him_abs⟩ := line_sphere_re_im_bounds (τ := τ) (RJ := RJ) hz
  have hdist : ‖z - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ = RJ := by
    rw [← dist_eq_norm]
    exact Metric.mem_sphere.mp hz
  have hRJ0 : 0 ≤ RJ := by
    rw [← hdist]
    exact norm_nonneg _
  have hre_ge : 1 / 2 - RJ ≤ z.re := by
    have := (abs_le.mp hre_abs).1
    linarith
  have hsig0 : 0 < z.re := by linarith
  have hwidth0 : 0 ≤ 1 / 2 - z.re := by linarith
  have hwidth_le : 1 / 2 - z.re ≤ RJ := by
    have := (abs_le.mp hre_abs).1
    linarith
  have him_ge : τ - RJ ≤ z.im := by
    have := (abs_le.mp him_abs).1
    linarith
  have him_le : z.im ≤ τ + RJ := by
    have := (abs_le.mp him_abs).2
    linarith
  have him_pos : 0 < z.im := by linarith
  have hz_decomp : ((z.re : ℂ) + (z.im : ℂ) * I) = z := by
    apply Complex.ext <;> simp
  have hline := norm_zetaChi_le_left_line (σ := z.re) (t := z.im) hsig0 hleft him_pos
  rw [hz_decomp] at hline
  set Kz : ℝ := (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + (z.im / 2) ^ 2)
      + (1 / (z.im / 2) ^ 2 + Real.pi / (2 * (z.im / 2))) - Real.log Real.pi with hKzdef
  have hy0pos : 0 < (τ - RJ) / 2 := by linarith
  have hzhalf_pos : 0 < z.im / 2 := by linarith
  have hzhalf_nonneg : 0 ≤ z.im / 2 := le_of_lt hzhalf_pos
  have hy1_nonneg : 0 ≤ (τ + RJ) / 2 := by linarith
  have hy_low : (τ - RJ) / 2 ≤ z.im / 2 := by linarith
  have hy_high : z.im / 2 ≤ (τ + RJ) / 2 := by linarith
  have hsq_high : (z.im / 2) ^ 2 ≤ ((τ + RJ) / 2) ^ 2 := by
    nlinarith [hzhalf_nonneg, hy_high, hy1_nonneg]
  have hlog_le : (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + (z.im / 2) ^ 2)
      ≤ (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + ((τ + RJ) / 2) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.log_le_log (by positivity)
    nlinarith [hsq_high]
  have hsq_low : ((τ - RJ) / 2) ^ 2 ≤ (z.im / 2) ^ 2 := by
    nlinarith [hy0pos.le, hy_low, hzhalf_nonneg]
  have hden_low_pos : 0 < ((τ - RJ) / 2) ^ 2 := by positivity
  have hinv_sq : 1 / (z.im / 2) ^ 2 ≤ 1 / ((τ - RJ) / 2) ^ 2 := by
    exact one_div_le_one_div_of_le hden_low_pos hsq_low
  have hinv : 1 / (z.im / 2) ≤ 1 / ((τ - RJ) / 2) := by
    exact one_div_le_one_div_of_le hy0pos hy_low
  have hfrac : Real.pi / (2 * (z.im / 2)) ≤ Real.pi / (2 * ((τ - RJ) / 2)) := by
    have hmul := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ Real.pi / 2)
    have hleftfrac : Real.pi / (2 * (z.im / 2)) = (Real.pi / 2) * (1 / (z.im / 2)) := by
      field_simp [ne_of_gt hzhalf_pos]
    have hrightfrac : Real.pi / (2 * ((τ - RJ) / 2)) = (Real.pi / 2) * (1 / ((τ - RJ) / 2)) := by
      field_simp [ne_of_gt hy0pos]
    rw [hleftfrac, hrightfrac]
    exact hmul
  have hKz_le_center : Kz ≤ (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + ((τ + RJ) / 2) ^ 2)
      + (1 / ((τ - RJ) / 2) ^ 2 + Real.pi / (2 * ((τ - RJ) / 2))) - Real.log Real.pi := by
    rw [hKzdef]
    linarith [hlog_le, hinv_sq, hfrac]
  have hKz_le : Kz ≤ K := le_trans hKz_le_center hKbound
  have hexp_le : Real.exp ((1 / 2 - z.re) * Kz) ≤ Real.exp (RJ * K) := by
    apply Real.exp_le_exp.mpr
    have hprod1 : (1 / 2 - z.re) * Kz ≤ (1 / 2 - z.re) * K := by
      exact mul_le_mul_of_nonneg_left hKz_le hwidth0
    have hprod2 : (1 / 2 - z.re) * K ≤ RJ * K := by
      exact mul_le_mul_of_nonneg_right hwidth_le hK0
    exact le_trans hprod1 hprod2
  have hline' : ‖zetaChi z‖ ≤ Real.exp ((1 / 2 - z.re) * Kz) := by
    simpa [Kz] using hline
  exact le_trans hline' (le_trans hexp_le hbudget)

/-- **Window-level χ circle envelope from top/bottom scalar data.**  If
`τ ∈ [T,T+U]`, the left-arc growth scalar at height `τ` is bounded by the
window scalar using top height `T+U+RJ` and bottom height `T-RJ`, while the
right-arc decay condition is inherited from the same bottom height. -/
theorem norm_zetaChi_le_line_sphere_window {T U τ RJ χB K : ℝ}
    (hτ : τ ∈ Set.Icc T (T + U))
    (hRJ12 : RJ < 1 / 2) (hRJ0 : 0 ≤ RJ) (hheight : RJ < T)
    (hK : K = (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + ((T + U + RJ) / 2) ^ 2)
      + (1 / ((T - RJ) / 2) ^ 2 + Real.pi / (2 * ((T - RJ) / 2))) - Real.log Real.pi)
    (hK0 : 0 ≤ K) (hleftBudget : Real.exp (RJ * K) ≤ χB)
    (hrightLarge : Real.log Real.pi + (1 / ((T - RJ) / 2) ^ 2
      + Real.pi / (2 * ((T - RJ) / 2))) < Real.log ((T - RJ) / 2))
    (hχB1 : 1 ≤ χB) :
    ∀ z ∈ Metric.sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖zetaChi z‖ ≤ χB := by
  have hτlo : T ≤ τ := (Set.mem_Icc.mp hτ).1
  have hτhi : τ ≤ T + U := (Set.mem_Icc.mp hτ).2
  have hheightτ : RJ < τ := lt_of_lt_of_le hheight hτlo
  have hTbottom_pos : 0 < (T - RJ) / 2 := by linarith
  have hτbottom_pos : 0 < (τ - RJ) / 2 := by linarith
  have hbottom_le : (T - RJ) / 2 ≤ (τ - RJ) / 2 := by linarith
  have hlog_bottom : Real.log ((T - RJ) / 2) ≤ Real.log ((τ - RJ) / 2) :=
    Real.log_le_log hTbottom_pos hbottom_le
  have hsq_bottom : ((T - RJ) / 2) ^ 2 ≤ ((τ - RJ) / 2) ^ 2 := by
    nlinarith [hTbottom_pos.le, hbottom_le, hτbottom_pos.le]
  have hden_bottom_pos : 0 < ((T - RJ) / 2) ^ 2 := by positivity
  have hinv_sq : 1 / ((τ - RJ) / 2) ^ 2 ≤ 1 / ((T - RJ) / 2) ^ 2 := by
    exact one_div_le_one_div_of_le hden_bottom_pos hsq_bottom
  have hinv : 1 / ((τ - RJ) / 2) ≤ 1 / ((T - RJ) / 2) := by
    exact one_div_le_one_div_of_le hTbottom_pos hbottom_le
  have hfrac : Real.pi / (2 * ((τ - RJ) / 2)) ≤ Real.pi / (2 * ((T - RJ) / 2)) := by
    have hmul := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ Real.pi / 2)
    have hleftfrac : Real.pi / (2 * ((τ - RJ) / 2)) =
        (Real.pi / 2) * (1 / ((τ - RJ) / 2)) := by
      field_simp [ne_of_gt hτbottom_pos]
    have hrightfrac : Real.pi / (2 * ((T - RJ) / 2)) =
        (Real.pi / 2) * (1 / ((T - RJ) / 2)) := by
      field_simp [ne_of_gt hTbottom_pos]
    rw [hleftfrac, hrightfrac]
    exact hmul
  have hrightLargeτ : Real.log Real.pi + (1 / ((τ - RJ) / 2) ^ 2
      + Real.pi / (2 * ((τ - RJ) / 2))) < Real.log ((τ - RJ) / 2) := by
    have hleft_le : Real.log Real.pi + (1 / ((τ - RJ) / 2) ^ 2
        + Real.pi / (2 * ((τ - RJ) / 2))) ≤ Real.log Real.pi
        + (1 / ((T - RJ) / 2) ^ 2 + Real.pi / (2 * ((T - RJ) / 2))) := by
      linarith [hinv_sq, hfrac]
    exact lt_of_le_of_lt hleft_le (lt_of_lt_of_le hrightLarge hlog_bottom)
  have htop_nonneg : 0 ≤ (τ + RJ) / 2 := by nlinarith [hRJ0, hτlo, hheight.le]
  have htop_le : (τ + RJ) / 2 ≤ (T + U + RJ) / 2 := by linarith
  have hwin_top_nonneg : 0 ≤ (T + U + RJ) / 2 := by linarith
  have hsq_top : ((τ + RJ) / 2) ^ 2 ≤ ((T + U + RJ) / 2) ^ 2 := by
    nlinarith [htop_nonneg, htop_le, hwin_top_nonneg]
  have hlog_top : (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + ((τ + RJ) / 2) ^ 2)
      ≤ (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + ((T + U + RJ) / 2) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.log_le_log (by positivity)
    nlinarith [hsq_top]
  have hcenter_le_window : (1 / 2 : ℝ) * Real.log ((1 / 2 : ℝ) ^ 2 + ((τ + RJ) / 2) ^ 2)
      + (1 / ((τ - RJ) / 2) ^ 2 + Real.pi / (2 * ((τ - RJ) / 2))) - Real.log Real.pi ≤ K := by
    rw [hK]
    linarith [hlog_top, hinv_sq, hfrac]
  intro z hz
  by_cases hleft : z.re ≤ 1 / 2
  · exact norm_zetaChi_le_left_line_sphere_of_K_bound
      (τ := τ) (RJ := RJ) (χB := χB) (K := K)
      hRJ12 hheightτ hK0 hcenter_le_window hleftBudget z hz hleft
  · have hright : 1 / 2 ≤ z.re := le_of_lt (lt_of_not_ge hleft)
    exact norm_zetaChi_le_right_line_sphere
      (τ := τ) (RJ := RJ) (χB := χB)
      hRJ12 hheightτ hrightLargeτ hχB1 z hz hright

end RHTower
