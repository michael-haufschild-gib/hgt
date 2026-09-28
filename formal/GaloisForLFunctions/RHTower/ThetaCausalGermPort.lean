import GaloisForLFunctions.RHTower.ThetaHalfLinePortGauge
import GaloisForLFunctions.HTGeometry.HalfLineTransformCalculus
import GaloisForLFunctions.HTGeometry.VolterraConvolutionCalculus

/-!
# Causal-germ cancellation at the theta port

For a smooth positive-ray correction `a` with an exponential moment, such that `k + a` is a causal
source, put `Q_a(w) = ∫₀^∞ a(u) sinh(wu) du` and `E_a = H + Q_a` (`H` the half-line theta
transform).  Then `E_a + E_a# = X`, `D_a = |E_a|² - |E_a#|² = 2 Re(E_a X̄) - |X|²`, and at a real
Xi zero `E_a(iγ) = i c_a(γ)`, `c_a(γ) = ∫₀^∞ (k + a) sin(γu)`, with normal derivative
`∂_α D_a(α + iγ)|₀ = -2 c_a(γ) Ξ'(γ)`.

**All-order causal-germ theorem.** If `D_a > 0` in a right collar of every sufficiently high simple
critical zero, then `(k + a)^{(2m)}(0) = 0` for all `m`: otherwise the first nonzero even jet fixes
the sign of `c_a(γ) ~ (-1)^m (k+a)^{(2m)}(0) γ^{-2m-1}`, and simple critical zeros of both slopes
occur arbitrarily high.  For analytic `k + a` the germ is odd; all even jets vanish iff `c_a` decays
faster than every power.  The sharp receiver `a_* = -k + 2uk` gives `E_{a_*} = X/2 + X'`, with
normal derivative `2Ξ'(γ)²`.
-/
open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped ContDiff ComplexConjugate

namespace RHTower

noncomputable section

/-! ## Corrected ports -/

/-- The admissible causal corrections: smooth `a` with an exponential moment such that `k + a` is
a causal source on the positive ray. -/
structure CausalCorrection (a : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ a
  moment : ∃ σ : ℝ, 0 < σ ∧ IntegrableOn (fun u => Real.exp (σ * u) * |a u|) (Ioi 0)
  source : CausalSource fun u => thetaCuspFullSource u + a u

/-- The correction transform `Q_a(w) = ∫₀^∞ a(u) sinh(wu) du`. -/
def causalCorrectionTransform (a : ℝ → ℝ) (w : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), (a u : ℂ) * Complex.sinh (w * u)

/-- The corrected port `E_a = H + Q_a`. -/
def causalPort (a : ℝ → ℝ) (w : ℂ) : ℂ := thetaHalfLaplace w + causalCorrectionTransform a w

/-- The modulus imbalance `D_a = |E_a|² - |E_a#|²`. -/
def causalPortImbalance (a : ℝ → ℝ) (w : ℂ) : ℝ :=
  ‖causalPort a w‖ ^ 2 - ‖halfPortReflect (causalPort a) w‖ ^ 2

/-- The corrected sine response `c_a(γ) = ∫₀^∞ (k + a)(u) sin(γu) du`. -/
def causalPortSine (a : ℝ → ℝ) (γ : ℝ) : ℝ :=
  halfLineSine (fun u => thetaCuspFullSource u + a u) γ

theorem halfPortReflect_causalCorrectionTransform (a : ℝ → ℝ) (w : ℂ) :
    halfPortReflect (causalCorrectionTransform a) w = -causalCorrectionTransform a w := by
  rw [halfPortReflect, causalCorrectionTransform, causalCorrectionTransform, ← integral_conj,
    ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.sinh_conj, map_mul, map_neg, Complex.conj_conj,
    Complex.conj_ofReal, neg_mul, Complex.sinh_neg]
  ring

/-- **(1).** `E_a + E_a# = X`. -/
theorem causalPort_add_reflect (a : ℝ → ℝ) (w : ℂ) :
    causalPort a w + halfPortReflect (causalPort a) w = thetaSymmetrizedPort w := by
  have h1 : halfPortReflect (causalPort a) w =
      halfPortReflect thetaHalfLaplace w + halfPortReflect (causalCorrectionTransform a) w := by
    simp only [halfPortReflect, causalPort, map_add]
  rw [h1, halfPortReflect_thetaHalfLaplace, halfPortReflect_causalCorrectionTransform, causalPort,
    thetaSymmetrizedPort]
  ring

/-- **(3).** `D_a = 2 Re(E_a conj X) - |X|²`. -/
theorem causalPortImbalance_eq (a : ℝ → ℝ) (w : ℂ) :
    causalPortImbalance a w =
      2 * (causalPort a w * conj (thetaSymmetrizedPort w)).re - ‖thetaSymmetrizedPort w‖ ^ 2 := by
  have h := causalPort_add_reflect a w
  rw [causalPortImbalance, show halfPortReflect (causalPort a) w =
    thetaSymmetrizedPort w - causalPort a w by rw [← h]; ring]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.sub_re, Complex.sub_im]
  ring

theorem CausalCorrection.integrableOn_abs {a : ℝ → ℝ} (ha : CausalCorrection a) :
    IntegrableOn (fun u => |a u|) (Ioi 0) := by
  obtain ⟨σ, hσ, h⟩ := ha.moment
  refine h.mono' (ha.contDiff.continuous.abs.aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun u hu => ?_))
  have hu : (0 : ℝ) < u := hu
  rw [Real.norm_eq_abs, abs_abs]
  exact le_mul_of_one_le_left (abs_nonneg _) (Real.one_le_exp (by positivity))

theorem CausalCorrection.integrableOn_mul_sin {a : ℝ → ℝ} (ha : CausalCorrection a) (γ : ℝ) :
    IntegrableOn (fun u => a u * Real.sin (γ * u)) (Ioi 0) := by
  refine ha.integrableOn_abs.mono' ((ha.contDiff.continuous.mul (by fun_prop)).aestronglyMeasurable)
    (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

/-- **(2).** At a real zero of Xi, `E_a(iγ) = i c_a(γ)`. -/
theorem causalPort_mul_I {a : ℝ → ℝ} (ha : CausalCorrection a) {γ : ℝ} (hγ : Xi γ = 0) :
    causalPort a (γ * I) = (causalPortSine a γ : ℂ) * I := by
  have hk : IntegrableOn (fun u => thetaCuspFullSource u * Real.sin (γ * u)) (Ioi 0) := by
    have := ha.source.integrableOn_mul_sin γ
    have h2 := ha.integrableOn_mul_sin γ
    refine (this.sub h2).congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]; ring
  rw [causalPort, thetaHalfLaplace_I_mul_of_Xi_eq_zero hγ, causalCorrectionTransform,
    causalPortSine, halfLineSine]
  have hQ : (∫ u in Ioi (0 : ℝ), (a u : ℂ) * Complex.sinh (γ * I * u)) =
      ((∫ u in Ioi (0 : ℝ), a u * Real.sin (γ * u) : ℝ) : ℂ) * I := by
    rw [← integral_complex_ofReal, ← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [show (γ : ℂ) * I * u = ((γ * u : ℝ) : ℂ) * I by push_cast; ring, Complex.sinh_mul_I]
    push_cast; ring
  rw [hQ, ← add_mul, ← Complex.ofReal_add, thetaHalfSineResponse, ← integral_add hk
    (ha.integrableOn_mul_sin γ)]
  congr 2
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  ring

/-! ## Holomorphy of the corrected port near the imaginary axis -/

theorem causalCorrectionTransform_eq {a : ℝ → ℝ} (ha : CausalCorrection a) {σ : ℝ}
    (hmom : IntegrableOn (fun u => Real.exp (σ * u) * |a u|) (Ioi 0)) {w : ℂ} (hw : |w.re| ≤ σ) :
    causalCorrectionTransform a w =
      (halfLineExpTransform (fun u => (a u : ℂ)) w -
        halfLineExpTransform (fun u => (a u : ℂ)) (-w)) / 2 := by
  have hmeas : AEStronglyMeasurable (fun u => (a u : ℂ)) (volume.restrict (Ioi 0)) :=
    (Complex.continuous_ofReal.comp ha.contDiff.continuous).aestronglyMeasurable
  have hmom' : IntegrableOn (fun u => Real.exp (σ * u) * ‖(a u : ℂ)‖) (Ioi 0) := by
    simpa [Complex.norm_real] using hmom
  have h1 := integrableOn_cexp_mul_of_moment hmeas hmom' (w := w) (by linarith [le_abs_self w.re])
  have h2 := integrableOn_cexp_mul_of_moment hmeas hmom' (w := -w)
    (by simp only [neg_re]; linarith [neg_abs_le w.re])
  rw [causalCorrectionTransform, halfLineExpTransform, halfLineExpTransform, ← integral_sub h1 h2,
    ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [Complex.sinh, neg_mul]
  ring

theorem CausalCorrection.differentiableAt {a : ℝ → ℝ} (ha : CausalCorrection a) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ w : ℂ, |w.re| < σ → DifferentiableAt ℂ (causalPort a) w := by
  obtain ⟨σ, hσ, hmom⟩ := ha.moment
  refine ⟨σ, hσ, fun w hw => ?_⟩
  have hmeas : AEStronglyMeasurable (fun u => (a u : ℂ)) (volume.restrict (Ioi 0)) :=
    (Complex.continuous_ofReal.comp ha.contDiff.continuous).aestronglyMeasurable
  have hmom' : IntegrableOn (fun u => Real.exp (σ * u) * ‖(a u : ℂ)‖) (Ioi 0) := by
    simpa [Complex.norm_real] using hmom
  have hL : ∀ z : ℂ, z.re < σ → DifferentiableAt ℂ (halfLineExpTransform fun u => (a u : ℂ)) z :=
    fun z hz => (hasDerivAt_halfLineExpTransform hmeas hmom' hz).differentiableAt
  have hopen : IsOpen {z : ℂ | |z.re| < σ} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  have heq : causalCorrectionTransform a =ᶠ[𝓝 w] fun z =>
      (halfLineExpTransform (fun u => (a u : ℂ)) z -
        halfLineExpTransform (fun u => (a u : ℂ)) (-z)) / 2 :=
    Filter.eventually_of_mem (hopen.mem_nhds hw) fun z hz =>
      causalCorrectionTransform_eq ha hmom (le_of_lt hz)
  have hQ : DifferentiableAt ℂ (causalCorrectionTransform a) w := by
    refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
    have hneg : DifferentiableAt ℂ (fun z => halfLineExpTransform (fun u => (a u : ℂ)) (-z)) w :=
      (hL (-w) (by simp only [neg_re]; linarith [neg_abs_le w.re])).comp w differentiableAt_id.neg
    exact ((hL w (by linarith [le_abs_self w.re])).sub hneg).div_const 2
  exact (differentiable_thetaHalfLaplace w).add hQ

/-- **(3).** At a real zero of Xi the normal derivative of the imbalance is `-2 c_a(γ) Ξ'(γ)`. -/
theorem hasDerivAt_causalPortImbalance {a : ℝ → ℝ} (ha : CausalCorrection a) {γ : ℝ}
    (hγ : Xi γ = 0) :
    HasDerivAt (fun α : ℝ => causalPortImbalance a (α + γ * I))
      (-2 * causalPortSine a γ * deriv Xi γ) 0 := by
  obtain ⟨σ, hσ, hdiff⟩ := ha.differentiableAt
  have hE0 : HasDerivAt (causalPort a) (deriv (causalPort a) (γ * I)) (γ * I) :=
    (hdiff (γ * I) (by simp [hσ])).hasDerivAt
  have hX0 := hasDerivAt_thetaSymmetrizedPort ((γ : ℂ) * I)
  have hE : HasDerivAt (fun α : ℝ => causalPort a (α + γ * I)) (deriv (causalPort a) (γ * I)) 0 := by
    have hE0' : HasDerivAt (causalPort a) (deriv (causalPort a) (γ * I)) (((0 : ℝ) : ℂ) + γ * I) := by
      rw [Complex.ofReal_zero, zero_add]; exact hE0
    have h := (hE0'.comp (((0 : ℝ) : ℂ)) ((hasDerivAt_id (((0 : ℝ) : ℂ))).add_const
      ((γ : ℂ) * I))).comp_ofReal
    simpa using h
  have hX : HasDerivAt (fun α : ℝ => thetaSymmetrizedPort (α + γ * I))
      (deriv thetaSymmetrizedPort (γ * I)) 0 := by
    have hX0' : HasDerivAt thetaSymmetrizedPort (deriv thetaSymmetrizedPort (γ * I))
        (((0 : ℝ) : ℂ) + γ * I) := by
      rw [Complex.ofReal_zero, zero_add]; exact hX0
    have h := (hX0'.comp (((0 : ℝ) : ℂ)) ((hasDerivAt_id (((0 : ℝ) : ℂ))).add_const
      ((γ : ℂ) * I))).comp_ofReal
    simpa using h
  have hfun : (fun α : ℝ => causalPortImbalance a (α + γ * I)) = fun α : ℝ =>
      ‖causalPort a (α + γ * I)‖ ^ 2 -
        ‖thetaSymmetrizedPort (α + γ * I) - causalPort a (α + γ * I)‖ ^ 2 := by
    funext α
    rw [causalPortImbalance, show halfPortReflect (causalPort a) (α + γ * I) =
      thetaSymmetrizedPort (α + γ * I) - causalPort a (α + γ * I) by
        rw [← causalPort_add_reflect a]; ring]
  rw [hfun]
  have h := hE.norm_sq.sub (hX.sub hE).norm_sq
  refine h.congr_deriv ?_
  have hX00 : thetaSymmetrizedPort (γ * I) = 0 := by
    rw [thetaSymmetrizedPort_mul_I, hγ, Complex.ofReal_zero]
  simp only [Pi.sub_apply, Complex.ofReal_zero, zero_add]
  rw [hX00, causalPort_mul_I ha hγ, deriv_thetaSymmetrizedPort_mul_I, Complex.inner, Complex.inner]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-! ## The all-order causal-germ theorem -/

theorem exists_neg_of_hasDerivAt {f : ℝ → ℝ} {f' : ℝ} (hf : HasDerivAt f f' 0) (h0 : f 0 = 0)
    (hneg : f' < 0) {δ : ℝ} (hδ : 0 < δ) : ∃ α, 0 < α ∧ α < δ ∧ f α < 0 := by
  have hs := (hasDerivAt_iff_tendsto_slope.mp hf).mono_left
    (nhdsWithin_mono _ (fun x (hx : x ∈ Ioi (0 : ℝ)) => ne_of_gt hx))
  have hev := (hs.eventually (gt_mem_nhds hneg)).and (Ioo_mem_nhdsGT hδ)
  obtain ⟨α, hα, hαI⟩ := hev.exists
  refine ⟨α, hαI.1, hαI.2, ?_⟩
  rw [slope_def_field, h0, sub_zero, sub_zero] at hα
  rcases div_neg_iff.mp hα with h1 | h1
  · exact absurd h1.2 (not_lt.mpr hαI.1.le)
  · exact h1.1

/-- **The all-order causal-germ theorem (4).** If the corrected port has strict right-half-plane
modulus order in some right collar of every sufficiently high simple critical zero, then every even
Taylor jet of `k + a` vanishes at the causal cut. -/
theorem causalPort_even_jets_eq_zero {a : ℝ → ℝ} (ha : CausalCorrection a)
    (horder : ∃ Γ : ℝ, ∀ γ > Γ, Xi γ = 0 → deriv Xi γ ≠ 0 →
      ∃ δ > 0, ∀ α : ℝ, 0 < α → α < δ → 0 < causalPortImbalance a (α + γ * I)) :
    ∀ m, iteratedDeriv (2 * m) (fun u => thetaCuspFullSource u + a u) 0 = 0 := by
  classical
  obtain ⟨Γ, hΓ⟩ := horder
  by_contra hne
  push Not at hne
  set f : ℝ → ℝ := fun u => thetaCuspFullSource u + a u
  let m := Nat.find hne
  have hm : iteratedDeriv (2 * m) f 0 ≠ 0 := Nat.find_spec hne
  have hlow : ∀ j < m, iteratedDeriv (2 * j) f 0 = 0 := fun j hj => by
    by_contra h'; exact Nat.find_min hne hj h'
  set L := (-1) ^ m * iteratedDeriv (2 * m) f 0
  have hL : L ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hm
  obtain ⟨Γ₁, hΓ₁⟩ := eventually_atTop.mp (ha.source.eventually_sign_halfLineSine hlow hm)
  set σ : ℝ := if 0 < L then 1 else -1
  have hσ : σ = 1 ∨ σ = -1 := by simp only [σ]; split_ifs <;> simp
  have hσL : 0 < σ * L := by
    simp only [σ]; split_ifs with h
    · linarith
    · have : L < 0 := lt_of_le_of_ne (not_lt.mp h) hL; linarith
  obtain ⟨γ, hγΓ, hXi, hσd⟩ := exists_simpleCrossing_above σ hσ (max Γ Γ₁)
  have hγ1 : Γ₁ ≤ γ := le_trans (le_max_right _ _) hγΓ.le
  have hc := hΓ₁ γ hγ1
  have hd0 : deriv Xi γ ≠ 0 := fun h => by rw [h, mul_zero] at hσd; exact lt_irrefl _ hσd
  obtain ⟨δ, hδ, hpos⟩ := hΓ γ (lt_of_le_of_lt (le_max_left _ _) hγΓ) hXi hd0
  have hprod : 0 < causalPortSine a γ * deriv Xi γ := by
    have h1 : 0 < (L * causalPortSine a γ) * (σ * deriv Xi γ) := mul_pos hc hσd
    have h2 : (L * causalPortSine a γ) * (σ * deriv Xi γ) =
        (σ * L) * (causalPortSine a γ * deriv Xi γ) := by ring
    rw [h2] at h1
    exact pos_of_mul_pos_right h1 hσL.le
  have hder := hasDerivAt_causalPortImbalance ha hXi
  have h0 : causalPortImbalance a (((0 : ℝ) : ℂ) + γ * I) = 0 := by
    rw [Complex.ofReal_zero, zero_add, causalPortImbalance_eq, thetaSymmetrizedPort_mul_I, hXi]
    simp
  obtain ⟨α, hα0, hαδ, hneg⟩ := exists_neg_of_hasDerivAt hder h0 (by linarith) hδ
  exact absurd (hpos α hα0 hαδ) (not_lt.mpr hneg.le)

/-- The collar form of (4): strict order in a fixed right collar at every height. -/
theorem causalPort_even_jets_eq_zero_of_collar {a : ℝ → ℝ} (ha : CausalCorrection a)
    (hcollar : ∃ δ > 0, ∀ w : ℂ, 0 < w.re → w.re < δ → 0 < causalPortImbalance a w) :
    ∀ m, iteratedDeriv (2 * m) (fun u => thetaCuspFullSource u + a u) 0 = 0 := by
  obtain ⟨δ, hδ, h⟩ := hcollar
  refine causalPort_even_jets_eq_zero ha ⟨0, fun γ _ _ _ => ⟨δ, hδ, fun α hα hαδ => h _ ?_ ?_⟩⟩
  · simpa using hα
  · simpa using hαδ

/-- For a real-analytic corrected source, strict order forces an odd germ at the cut: the even
germ of the correction is exactly `-k`. -/
theorem causalPort_odd_germ {a : ℝ → ℝ} (ha : CausalCorrection a)
    (horder : ∃ Γ : ℝ, ∀ γ > Γ, Xi γ = 0 → deriv Xi γ ≠ 0 →
      ∃ δ > 0, ∀ α : ℝ, 0 < α → α < δ → 0 < causalPortImbalance a (α + γ * I))
    (han : AnalyticAt ℝ (fun u => thetaCuspFullSource u + a u) 0) :
    ∀ᶠ u in 𝓝 0, thetaCuspFullSource (-u) + a (-u) = -(thetaCuspFullSource u + a u) :=
  eventually_neg_of_even_iteratedDeriv_eq_zero han (causalPort_even_jets_eq_zero ha horder)

/-- **(5a).** All even jets vanish iff `c_a` decays faster than every power. -/
theorem causalPort_even_jets_iff_rapid {a : ℝ → ℝ} (ha : CausalCorrection a) :
    (∀ m, iteratedDeriv (2 * m) (fun u => thetaCuspFullSource u + a u) 0 = 0) ↔
      ∀ N : ℕ, (causalPortSine a) =O[atTop] fun γ => (γ ^ N)⁻¹ :=
  ha.source.even_jets_eq_zero_iff_rapid

/-! ## The sharp local receiver `a_* = -k + 2uk` -/

/-- A smooth function all of whose derivatives are `O(e^{-|x|})` is a causal source. -/
theorem causalSource_of_exp_bound {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hb : ∀ n, ∃ C, ∀ x, |iteratedDeriv n g x| ≤ C * Real.exp (-|x|)) : CausalSource g := by
  refine ⟨hg, fun n => ?_, fun n => ?_⟩
  · obtain ⟨C, hC⟩ := hb n
    exact (((integrable_exp_neg_abs_line).const_mul C).mono'
      ((hg.continuous_iteratedDeriv n (by exact_mod_cast le_top)).aestronglyMeasurable)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)).integrableOn
  · obtain ⟨C, hC⟩ := hb n
    refine squeeze_zero_norm' ?_ ((Real.tendsto_exp_neg_atTop_nhds_zero).const_mul C |>.trans_eq
      (by simp))
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [Real.norm_eq_abs]
    simpa [abs_of_nonneg hx] using hC x

theorem exists_abs_mul_iteratedDeriv_thetaCuspFullSource_le (n : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x, |x * iteratedDeriv n thetaCuspFullSource x| ≤ C * Real.exp (-|x|) := by
  obtain ⟨C, hC, h⟩ := exists_abs_iteratedDeriv_thetaCuspFullSource_le 2 n
  refine ⟨C, hC, fun x => ?_⟩
  rw [abs_mul]
  calc |x| * |iteratedDeriv n thetaCuspFullSource x|
      ≤ Real.exp |x| * (C * Real.exp (-(2 * |x|))) :=
        mul_le_mul (by linarith [Real.add_one_le_exp |x|]) (h x) (abs_nonneg _) (Real.exp_pos _).le
    _ = C * Real.exp (-|x|) := by rw [mul_left_comm, ← Real.exp_add]; ring_nf

/-- The sharp local correction `a_*(u) = -k(u) + 2u k(u)`, with `k + a_* = 2uk`. -/
def causalReceiverCorrection (u : ℝ) : ℝ := -thetaCuspFullSource u + 2 * u * thetaCuspFullSource u

theorem causalReceiverCorrection_source :
    (fun u => thetaCuspFullSource u + causalReceiverCorrection u) =
      fun u => 2 * (u * thetaCuspFullSource u) := by
  funext u; simp only [causalReceiverCorrection]; ring

theorem causalCorrection_causalReceiverCorrection : CausalCorrection causalReceiverCorrection := by
  have hk := contDiff_thetaCuspFullSource
  refine ⟨by unfold causalReceiverCorrection; fun_prop, ⟨1, one_pos, ?_⟩, ?_⟩
  · obtain ⟨C, hC, h⟩ := exists_abs_thetaCuspFullSource_le 3
    refine ((integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).const_mul (3 * C)).mono'
      ((by unfold causalReceiverCorrection; fun_prop : Continuous fun u =>
        Real.exp (1 * u) * |causalReceiverCorrection u|).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun u hu => ?_))
    have hu : (0 : ℝ) ≤ u := le_of_lt hu
    have hb := h u
    rw [abs_of_nonneg hu] at hb
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_abs, causalReceiverCorrection]
    have hk0 := abs_nonneg (thetaCuspFullSource u)
    have hue : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have h1 : |-thetaCuspFullSource u + 2 * u * thetaCuspFullSource u| ≤
        (1 + 2 * Real.exp u) * (C * Real.exp (-(3 * u))) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hu, abs_two]
      nlinarith [Real.exp_pos u]
    calc Real.exp (1 * u) * |-thetaCuspFullSource u + 2 * u * thetaCuspFullSource u|
        ≤ Real.exp u * ((1 + 2 * Real.exp u) * (C * Real.exp (-(3 * u)))) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = C * (Real.exp (u + -(3 * u)) + 2 * Real.exp (u + u + -(3 * u))) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_add]; ring
      _ ≤ 3 * C * Real.exp (-1 * u) := by
          have e1 : Real.exp (u + -(3 * u)) ≤ Real.exp (-1 * u) := Real.exp_le_exp.mpr (by linarith)
          have e2 : Real.exp (u + u + -(3 * u)) = Real.exp (-1 * u) := by ring_nf
          nlinarith
  · rw [causalReceiverCorrection_source]
    have hc : ContDiff ℝ ∞ fun u => 2 * thetaCuspFullSource u := by fun_prop
    refine causalSource_of_exp_bound (by fun_prop) fun n => ?_
    rcases n with _ | n
    · obtain ⟨C, hC, h⟩ := exists_abs_mul_iteratedDeriv_thetaCuspFullSource_le 0
      refine ⟨2 * C, fun x => ?_⟩
      simp only [iteratedDeriv_zero] at h ⊢
      rw [abs_mul, abs_two]; nlinarith [h x]
    · obtain ⟨C₁, hC₁, h₁⟩ := exists_abs_mul_iteratedDeriv_thetaCuspFullSource_le (n + 1)
      obtain ⟨C₂, hC₂, h₂⟩ := exists_abs_iteratedDeriv_thetaCuspFullSource_le 1 n
      refine ⟨2 * C₁ + 2 * (n + 1) * C₂, fun x => ?_⟩
      have hfun : (fun u => 2 * (u * thetaCuspFullSource u)) =
          fun u => u * (2 * thetaCuspFullSource u) := by funext u; ring
      rw [hfun, iteratedDeriv_id_mul_real hc n]
      simp only [iteratedDeriv_const_mul_field]
      have hb2 := h₂ x
      rw [one_mul] at hb2
      have e1 : |x * (2 * iteratedDeriv (n + 1) thetaCuspFullSource x)| =
          2 * |x * iteratedDeriv (n + 1) thetaCuspFullSource x| := by
        rw [show x * (2 * iteratedDeriv (n + 1) thetaCuspFullSource x) =
          2 * (x * iteratedDeriv (n + 1) thetaCuspFullSource x) by ring, abs_mul, abs_two]
      have e2 : |((n : ℝ) + 1) * (2 * iteratedDeriv n thetaCuspFullSource x)| =
          2 * (n + 1) * |iteratedDeriv n thetaCuspFullSource x| := by
        rw [abs_mul, abs_mul, abs_two, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]; ring
      calc |x * (2 * iteratedDeriv (n + 1) thetaCuspFullSource x) +
            (↑n + 1) * (2 * iteratedDeriv n thetaCuspFullSource x)|
          ≤ 2 * |x * iteratedDeriv (n + 1) thetaCuspFullSource x| +
            2 * (n + 1) * |iteratedDeriv n thetaCuspFullSource x| := by
            rw [← e1, ← e2]; exact abs_add_le _ _
        _ ≤ 2 * (C₁ * Real.exp (-|x|)) + 2 * (n + 1) * (C₂ * Real.exp (-|x|)) := by
            gcongr
            · exact h₁ x
        _ = (2 * C₁ + 2 * (n + 1) * C₂) * Real.exp (-|x|) := by ring

theorem integrableOn_exp_mul_norm_thetaCuspFullSource (σ : ℝ) :
    IntegrableOn (fun u => Real.exp (σ * u) * ‖(thetaCuspFullSource u : ℂ)‖) (Ioi 0) := by
  have h := (integrableOn_cexp_mul_thetaCuspFullSource (σ : ℂ) (Ioi 0)).norm
  refine IntegrableOn.congr_fun h (fun u _ => ?_) measurableSet_Ioi
  rw [norm_mul, Complex.norm_exp]; simp

theorem integrableOn_exp_mul_norm_mul_thetaCuspFullSource (σ : ℝ) :
    IntegrableOn (fun u => Real.exp (σ * u) * ‖((u : ℂ) * (thetaCuspFullSource u : ℂ))‖) (Ioi 0) := by
  obtain ⟨C, hC, h⟩ := exists_abs_mul_iteratedDeriv_thetaCuspFullSource_le 0
  obtain ⟨C', hC', h'⟩ := exists_abs_thetaCuspFullSource_le (|σ| + 2)
  refine ((integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).const_mul C').mono'
    ((by fun_prop : Continuous fun u : ℝ => Real.exp (σ * u)).aestronglyMeasurable.mul
      ((by have := continuous_thetaCuspFullSource; fun_prop : Continuous fun u : ℝ =>
        ‖((u : ℂ) * (thetaCuspFullSource u : ℂ))‖).aestronglyMeasurable))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun u hu => ?_))
  have hu : (0 : ℝ) ≤ u := le_of_lt hu
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_norm, norm_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hu]
  have hb := h' u
  rw [abs_of_nonneg hu] at hb
  have hue : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  calc Real.exp (σ * u) * (u * |thetaCuspFullSource u|)
      ≤ Real.exp (|σ| * u) * (Real.exp u * (C' * Real.exp (-((|σ| + 2) * u)))) := by
        gcongr
        · exact le_abs_self σ
      _ = C' * Real.exp (-1 * u) := by
        rw [mul_left_comm, ← mul_assoc, ← Real.exp_add, mul_left_comm, ← Real.exp_add]; ring_nf

theorem deriv_thetaHalfLaplace_eq (w : ℂ) :
    deriv thetaHalfLaplace w =
      halfLineExpTransform (fun u => (u : ℂ) * (thetaCuspFullSource u : ℂ)) w := by
  have hmeas : AEStronglyMeasurable (fun u => (thetaCuspFullSource u : ℂ)) (volume.restrict (Ioi 0)) :=
    (Complex.continuous_ofReal.comp continuous_thetaCuspFullSource).aestronglyMeasurable
  have h := hasDerivAt_halfLineExpTransform hmeas
    (integrableOn_exp_mul_norm_thetaCuspFullSource (w.re + 1)) (w := w) (by linarith)
  have e : halfLineExpTransform (fun u => (thetaCuspFullSource u : ℂ)) = thetaHalfLaplace := by
    funext z; rfl
  rw [e] at h
  exact h.deriv

/-- **The sharp local receiver.** `E_{a_*} = X/2 + X'`. -/
theorem causalPort_causalReceiverCorrection (w : ℂ) :
    causalPort causalReceiverCorrection w = thetaMomentPort 1 w := by
  have hmeasu : AEStronglyMeasurable (fun u : ℝ => (u : ℂ) * (thetaCuspFullSource u : ℂ))
      (volume.restrict (Ioi 0)) :=
    ((by fun_prop : Continuous fun u : ℝ => (u : ℂ)).mul
      (Complex.continuous_ofReal.comp continuous_thetaCuspFullSource)).aestronglyMeasurable
  have hk1 := integrableOn_cexp_mul_thetaCuspFullSource w (Ioi 0)
  have hk2 := integrableOn_cexp_mul_thetaCuspFullSource (-w) (Ioi 0)
  have hu1 := integrableOn_cexp_mul_of_moment hmeasu
    (integrableOn_exp_mul_norm_mul_thetaCuspFullSource (|w.re| + 1)) (w := w)
    (by linarith [le_abs_self w.re])
  have hu2 := integrableOn_cexp_mul_of_moment hmeasu
    (integrableOn_exp_mul_norm_mul_thetaCuspFullSource (|w.re| + 1)) (w := -w)
    (by simp only [neg_re]; linarith [neg_abs_le w.re])
  have hX : deriv thetaSymmetrizedPort w = deriv thetaHalfLaplace w - deriv thetaHalfLaplace (-w) := by
    have h := (hasDerivAt_thetaHalfLaplace w).add
      ((hasDerivAt_thetaHalfLaplace (-w)).comp w (hasDerivAt_neg w))
    have e : thetaSymmetrizedPort = thetaHalfLaplace + thetaHalfLaplace ∘ Neg.neg := by
      funext z; rfl
    rw [e, h.deriv]; ring
  rw [thetaMomentPort, hX, deriv_thetaHalfLaplace_eq, deriv_thetaHalfLaplace_eq, causalPort,
    causalCorrectionTransform, thetaSymmetrizedPort, thetaHalfLaplace, thetaHalfLaplaceTail,
    thetaHalfLaplace, thetaHalfLaplaceTail, halfLineExpTransform, halfLineExpTransform]
  have hsplit : (∫ u in Ioi (0 : ℝ), (causalReceiverCorrection u : ℂ) * Complex.sinh (w * u)) =
      -((∫ u in Ioi (0 : ℝ), cexp (w * u) * (thetaCuspFullSource u : ℂ)) -
          ∫ u in Ioi (0 : ℝ), cexp (-w * u) * (thetaCuspFullSource u : ℂ)) / 2 +
        ((∫ u in Ioi (0 : ℝ), cexp (w * u) * ((u : ℂ) * (thetaCuspFullSource u : ℂ))) -
          ∫ u in Ioi (0 : ℝ), cexp (-w * u) * ((u : ℂ) * (thetaCuspFullSource u : ℂ))) := by
    have hf1 : IntegrableOn (fun u : ℝ => -(cexp (w * u) * (thetaCuspFullSource u : ℂ) -
        cexp (-w * u) * (thetaCuspFullSource u : ℂ)) / 2) (Ioi 0) := (hk1.sub hk2).neg.div_const 2
    have hf2 : IntegrableOn (fun u : ℝ => cexp (w * u) * ((u : ℂ) * (thetaCuspFullSource u : ℂ)) -
        cexp (-w * u) * ((u : ℂ) * (thetaCuspFullSource u : ℂ))) (Ioi 0) := hu1.sub hu2
    calc (∫ u in Ioi (0 : ℝ), (causalReceiverCorrection u : ℂ) * Complex.sinh (w * u))
        = ∫ u in Ioi (0 : ℝ), ((-(cexp (w * u) * (thetaCuspFullSource u : ℂ) -
            cexp (-w * u) * (thetaCuspFullSource u : ℂ)) / 2) +
            (cexp (w * u) * ((u : ℂ) * (thetaCuspFullSource u : ℂ)) -
            cexp (-w * u) * ((u : ℂ) * (thetaCuspFullSource u : ℂ)))) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
          simp only [causalReceiverCorrection, Complex.sinh, neg_mul]
          push_cast
          ring
      _ = _ := by
          rw [integral_add hf1 hf2, integral_div, integral_neg, integral_sub hk1 hk2,
            integral_sub hu1 hu2]
  rw [hsplit]
  simp only [neg_mul]
  push_cast
  ring

/-- At every simple critical zero the sharp receiver has normal derivative `2Ξ'(γ)² > 0`. -/
theorem hasDerivAt_causalPortImbalance_receiver {γ : ℝ} (hγ : Xi γ = 0) :
    HasDerivAt (fun α : ℝ => causalPortImbalance causalReceiverCorrection (α + γ * I))
      (2 * deriv Xi γ ^ 2) 0 := by
  have h := hasDerivAt_thetaMomentPort_imbalance hγ 1
  have e : (fun α : ℝ => causalPortImbalance causalReceiverCorrection (α + γ * I)) =
      fun α : ℝ => ‖thetaMomentPort 1 (α + γ * I)‖ ^ 2 -
        ‖halfPortReflect (thetaMomentPort 1) (α + γ * I)‖ ^ 2 := by
    funext α
    rw [causalPortImbalance, show causalPort causalReceiverCorrection = thetaMomentPort 1 from
      funext causalPort_causalReceiverCorrection]
  rw [e]
  simpa using h

end

end RHTower
