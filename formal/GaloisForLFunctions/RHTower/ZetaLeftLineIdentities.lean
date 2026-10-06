import GaloisForLFunctions.RHTower.ZetaGaussianZeroSumContour
import GaloisForLFunctions.RHTower.LogVonMangoldtGaussianSums
import GaloisForLFunctions.RHTower.ChiLogDerivHigherDerivatives
import GaloisForLFunctions.RHTower.ZetaSquareStirlingCarrier

/-!
# `ζ` on the line `Re s = −½`

On the strip `−1 < Re s < 0` the functional equation `ζ(s) = χ(s) ζ(1 − s)` holds with all three
factors nonzero, so with `D = χ'/χ`:

* `ζ'/ζ(s) = D(s) + Σ Λ(n) n^{s−1}` (`logDeriv_riemannZeta_eq_leftStrip`);
* `(ζ'/ζ)'(s) = D'(s) + (ζ'/ζ)'(1 − s)`;
* `ζ'(s)²/ζ(s) = ζ''(s) − ζ(s) D'(s) − χ(s) Σ ℓ(n) n^{s−1}` (`sq_deriv_div_riemannZeta_eq_leftStrip`),

where `ζ(w)(ζ'/ζ)'(w) = Σ ℓ(n) n^{−w}`, `ℓ = (Λ·log) ⋆ 1`, for `Re w > 1`
(`LSeries_logVM_eq`).
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower.GaussZeroSum

noncomputable section

/-! ## The Dirichlet series of `ℓ` -/

theorem abscissa_vonMangoldt_le :
    LSeries.abscissaOfAbsConv (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy)

theorem abscissa_one_le : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact LSeriesSummable_one_iff.mpr (by simpa using hy)

theorem logMul_vonMangoldt_convolution_one :
    LSeries.convolution (LSeries.logMul fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 1 =
      fun n => (logVM n : ℂ) := by
  funext n
  rw [LSeries.convolution_def]
  unfold logVM
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [LSeries.logMul]
  ring

/-- `Σ ℓ(n) n^{−w} = ζ(w) (ζ'/ζ)'(w)` for `Re w > 1`. -/
theorem LSeries_logVM_eq {w : ℂ} (hw : 1 < w.re) :
    LSeries (fun n => (logVM n : ℂ)) w = riemannZeta w * deriv (logDeriv riemannZeta) w := by
  have hab : LSeries.abscissaOfAbsConv (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < w.re :=
    lt_of_le_of_lt abscissa_vonMangoldt_le (by exact_mod_cast hw)
  have hderiv : deriv (logDeriv riemannZeta) w =
      LSeries (LSeries.logMul fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) w := by
    have hev : logDeriv riemannZeta =ᶠ[𝓝 w]
        fun z => -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) z := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw] with z hz
      rw [logDeriv_apply, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz]
      ring
    rw [hev.deriv_eq]
    exact ((LSeries_hasDerivAt hab).neg).deriv.trans (neg_neg _)
  rw [hderiv, ← LSeries_one_eq_riemannZeta hw, mul_comm,
    ← LSeries_convolution (by rwa [LSeries.abscissaOfAbsConv_logMul])
      (lt_of_le_of_lt abscissa_one_le (by exact_mod_cast hw)),
    logMul_vonMangoldt_convolution_one]

/-! ## The functional equation on the strip `−1 < Re s < 0` -/

/-- The strip `−1 < Re s < 0`. -/
def leftStrip : Set ℂ := {z : ℂ | -1 < z.re ∧ z.re < 0}

theorem isOpen_leftStrip : IsOpen leftStrip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

theorem leftPt_mem_leftStrip (t : ℝ) : leftPt t ∈ leftStrip := by
  constructor <;> simp [leftPt] <;> norm_num

theorem gammaR_ne_zero_of_mem_leftStrip {z : ℂ} (hz : z ∈ leftStrip) : Complex.Gammaℝ z ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
  have := congrArg Complex.re hn
  simp at this
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp at this; linarith [hz.2]
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hpos
    linarith [hz.1]

theorem gammaR_one_sub_ne_zero_of_mem_leftStrip {z : ℂ} (hz : z ∈ leftStrip) :
    Complex.Gammaℝ (1 - z) ≠ 0 :=
  Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith [hz.2])

theorem zetaChi_ne_zero_of_mem_leftStrip {z : ℂ} (hz : z ∈ leftStrip) : zetaChi z ≠ 0 := by
  unfold zetaChi
  exact div_ne_zero (gammaR_one_sub_ne_zero_of_mem_leftStrip hz) (gammaR_ne_zero_of_mem_leftStrip hz)

theorem one_lt_re_one_sub_of_mem_leftStrip {z : ℂ} (hz : z ∈ leftStrip) : 1 < (1 - z).re := by
  simp; linarith [hz.2]

theorem riemannZeta_eq_of_mem_leftStrip {z : ℂ} (hz : z ∈ leftStrip) :
    riemannZeta z = zetaChi z * riemannZeta (1 - z) := by
  have h0 : z ≠ 0 := by intro h; rw [h] at hz; exact lt_irrefl _ hz.2
  have h1 : z ≠ 1 := by intro h; rw [h] at hz; have := hz.2; norm_num at this
  exact zeta_eq_zetaChi_mul h0 h1 (gammaR_one_sub_ne_zero_of_mem_leftStrip hz)

theorem riemannZeta_ne_zero_of_mem_leftStrip {z : ℂ} (hz : z ∈ leftStrip) : riemannZeta z ≠ 0 := by
  rw [riemannZeta_eq_of_mem_leftStrip hz]
  exact mul_ne_zero (zetaChi_ne_zero_of_mem_leftStrip hz)
    (riemannZeta_ne_zero_of_one_lt_re (one_lt_re_one_sub_of_mem_leftStrip hz))

theorem ne_one_of_mem_leftStrip {z : ℂ} (hz : z ∈ leftStrip) : z ≠ 1 := by
  intro h; rw [h] at hz; have := hz.2; norm_num at this

theorem one_sub_ne_one_of_mem_leftStrip {z : ℂ} (hz : z ∈ leftStrip) : 1 - z ≠ 1 := by
  intro h
  have := one_lt_re_one_sub_of_mem_leftStrip hz
  rw [h] at this; simp at this

theorem differentiableAt_zetaChi_of_mem_leftStrip {z : ℂ} (hz : z ∈ leftStrip) :
    DifferentiableAt ℂ zetaChi z :=
  (zetaChi_analyticAt (gammaR_one_sub_ne_zero_of_mem_leftStrip hz)).differentiableAt

theorem differentiableAt_riemannZeta_one_sub {z : ℂ} (hz : z ∈ leftStrip) :
    DifferentiableAt ℂ (fun w => riemannZeta (1 - w)) z :=
  (differentiableAt_riemannZeta (one_sub_ne_one_of_mem_leftStrip hz)).comp z
    ((differentiableAt_const 1).sub differentiableAt_id)

/-- `ζ'/ζ(s) = χ'/χ(s) − (ζ'/ζ)(1 − s)` on the strip. -/
theorem logDeriv_riemannZeta_eq_of_mem_leftStrip {z : ℂ} (hz : z ∈ leftStrip) :
    logDeriv riemannZeta z = logDeriv zetaChi z - logDeriv riemannZeta (1 - z) := by
  have hev : riemannZeta =ᶠ[𝓝 z] fun w => zetaChi w * riemannZeta (1 - w) := by
    filter_upwards [isOpen_leftStrip.mem_nhds hz] with w hw
    exact riemannZeta_eq_of_mem_leftStrip hw
  have hlog : logDeriv riemannZeta z = logDeriv (fun w => zetaChi w * riemannZeta (1 - w)) z := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [hlog, logDeriv_mul z (zetaChi_ne_zero_of_mem_leftStrip hz)
    (show riemannZeta (1 - z) ≠ 0 from
      riemannZeta_ne_zero_of_one_lt_re (one_lt_re_one_sub_of_mem_leftStrip hz))
    (differentiableAt_zetaChi_of_mem_leftStrip hz) (differentiableAt_riemannZeta_one_sub hz)]
  have hcomp : logDeriv (fun w => riemannZeta (1 - w)) z = -logDeriv riemannZeta (1 - z) := by
    have h := logDeriv_comp (f := riemannZeta) (g := fun w : ℂ => 1 - w) (x := z)
      (differentiableAt_riemannZeta (one_sub_ne_one_of_mem_leftStrip hz))
      ((differentiableAt_const 1).sub differentiableAt_id)
    have hd : deriv (fun w : ℂ => 1 - w) z = -1 := by
      simp
    rw [show (fun w => riemannZeta (1 - w)) = riemannZeta ∘ fun w : ℂ => 1 - w from rfl, h, hd]
    ring
  rw [hcomp]
  ring

/-- `ζ'/ζ(s) = χ'/χ(s) + Σ Λ(n) n^{s−1}` on the strip. -/
theorem logDeriv_riemannZeta_eq_leftStrip {z : ℂ} (hz : z ∈ leftStrip) :
    logDeriv riemannZeta z =
      logDeriv zetaChi z + LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 - z) := by
  rw [logDeriv_riemannZeta_eq_of_mem_leftStrip hz,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (one_lt_re_one_sub_of_mem_leftStrip hz), logDeriv_apply riemannZeta (1 - z)]
  ring

theorem analyticAt_riemannZeta_of_ne_one {z : ℂ} (hz : z ≠ 1) : AnalyticAt ℂ riemannZeta z :=
  analyticOnNhd_riemannZeta z hz

/-- `(ζ'/ζ)'(s) = D'(s) + (ζ'/ζ)'(1 − s)` on the strip. -/
theorem deriv_logDeriv_riemannZeta_eq_of_mem_leftStrip {z : ℂ} (hz : z ∈ leftStrip) :
    deriv (logDeriv riemannZeta) z =
      deriv (logDeriv zetaChi) z + deriv (logDeriv riemannZeta) (1 - z) := by
  have hev : logDeriv riemannZeta =ᶠ[𝓝 z]
      fun w => logDeriv zetaChi w - logDeriv riemannZeta (1 - w) := by
    filter_upwards [isOpen_leftStrip.mem_nhds hz] with w hw
    exact logDeriv_riemannZeta_eq_of_mem_leftStrip hw
  rw [hev.deriv_eq]
  -- differentiability of the two pieces
  have hz1 : (1 - z) ≠ 1 := one_sub_ne_one_of_mem_leftStrip hz
  have hζan : AnalyticAt ℂ riemannZeta (1 - z) := analyticAt_riemannZeta_of_ne_one hz1
  have hζ0 : riemannZeta (1 - z) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (one_lt_re_one_sub_of_mem_leftStrip hz)
  have hLan : AnalyticAt ℂ (logDeriv riemannZeta) (1 - z) := by
    have : logDeriv riemannZeta = fun w => deriv riemannZeta w / riemannZeta w := by
      funext w; exact logDeriv_apply _ _
    rw [this]
    exact hζan.deriv.div hζan hζ0
  have hχan : AnalyticAt ℂ zetaChi z := zetaChi_analyticAt (gammaR_one_sub_ne_zero_of_mem_leftStrip hz)
  have hDan : AnalyticAt ℂ (logDeriv zetaChi) z := by
    have : logDeriv zetaChi = fun w => deriv zetaChi w / zetaChi w := by
      funext w; exact logDeriv_apply _ _
    rw [this]
    exact hχan.deriv.div hχan (zetaChi_ne_zero_of_mem_leftStrip hz)
  have hcomp : HasDerivAt (fun w => logDeriv riemannZeta (1 - w))
      (deriv (logDeriv riemannZeta) (1 - z) * (-1)) z := by
    have hg : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
    exact hLan.differentiableAt.hasDerivAt.comp z hg
  have h := hDan.differentiableAt.hasDerivAt.sub hcomp
  rw [show (fun w => logDeriv zetaChi w - logDeriv riemannZeta (1 - w)) =
    (logDeriv zetaChi - fun w => logDeriv riemannZeta (1 - w)) from rfl, h.deriv]
  ring

/-- `ζ'²/ζ = ζ'' − ζ (ζ'/ζ)'` wherever `ζ ≠ 0`, `s ≠ 1`. -/
theorem sq_deriv_div_eq {z : ℂ} (hz1 : z ≠ 1) (hz : riemannZeta z ≠ 0) :
    deriv riemannZeta z ^ 2 / riemannZeta z =
      deriv (deriv riemannZeta) z - riemannZeta z * deriv (logDeriv riemannZeta) z := by
  have hζan : AnalyticAt ℂ riemannZeta z := analyticAt_riemannZeta_of_ne_one hz1
  have hfun : logDeriv riemannZeta = fun w => deriv riemannZeta w / riemannZeta w := by
    funext w; exact logDeriv_apply _ _
  have h := hζan.deriv.differentiableAt.hasDerivAt.div hζan.differentiableAt.hasDerivAt hz
  rw [hfun, show (fun w => deriv riemannZeta w / riemannZeta w) =
    deriv riemannZeta / riemannZeta from rfl, h.deriv]
  field_simp
  ring

/-- **The left-strip identity** `ζ'²/ζ = ζ'' − ζ D' − χ(s) Σ ℓ(n) n^{s−1}`. -/
theorem sq_deriv_div_riemannZeta_eq_leftStrip {z : ℂ} (hz : z ∈ leftStrip) :
    deriv riemannZeta z ^ 2 / riemannZeta z =
      deriv (deriv riemannZeta) z - riemannZeta z * deriv (logDeriv zetaChi) z -
        zetaChi z * LSeries (fun n => (logVM n : ℂ)) (1 - z) := by
  rw [sq_deriv_div_eq (ne_one_of_mem_leftStrip hz) (riemannZeta_ne_zero_of_mem_leftStrip hz),
    deriv_logDeriv_riemannZeta_eq_of_mem_leftStrip hz,
    LSeries_logVM_eq (one_lt_re_one_sub_of_mem_leftStrip hz)]
  rw [riemannZeta_eq_of_mem_leftStrip hz]
  ring

/-- `χ ζ'/ζ = χ' + χ Σ Λ(n) n^{s−1}` on the strip. -/
theorem zetaChi_mul_logDeriv_riemannZeta_eq {z : ℂ} (hz : z ∈ leftStrip) :
    zetaChi z * logDeriv riemannZeta z =
      deriv zetaChi z +
        zetaChi z * LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 - z) := by
  rw [logDeriv_riemannZeta_eq_leftStrip hz, logDeriv_apply zetaChi]
  field_simp [zetaChi_ne_zero_of_mem_leftStrip hz]

end

end RHTower.GaussZeroSum
