import GaloisForLFunctions.RHTower.ChiHyperbolicFourierTransition
import GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareMellin
import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicSharpEdges

/-!
# The actual physical-window hyperbolic transition

Every Gaussian/logarithmic Mellin slice of the actual smooth band is Schwartz,
including its moving edges. The literal physical window has an exact full-line
Mellin separation. A product L1 majorant proves the complete interchange and
absolute convergence of the resulting hyperbolic transition. The unconditional
family theorem retains the established negligible sharp/smooth cubic error.
No signed cubic cancellation or lattice Poisson transfer is asserted here.
-/

noncomputable section
open MeasureTheory Complex Set Filter
open scoped Topology ContDiff FourierTransform
open GaloisForLFunctions.RHTower
namespace RHTower.BAGTrace


/-- The actual AFE cutoff is smooth to every order on the positive axis. -/
theorem contDiffOn_smoothAFECutoff_infty_pos :
    ContDiffOn ℝ ∞ smoothAFECutoff (Ioi (0 : ℝ)) := by
  rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun x hx => (hasDerivAt_smoothAFECutoff hx).differentiableAt.differentiableWithinAt,?_⟩
  have hlog : ContDiffOn ℝ ∞ Real.log (Ioi (0 : ℝ)) :=
    contDiffOn_id.log (fun _ hx => ne_of_gt hx)
  have hnum : ContDiffOn ℝ ∞ (fun x : ℝ => Real.exp (-(Real.log x)^2/4))
      (Ioi (0 : ℝ)) := by fun_prop
  have hden : ContDiffOn ℝ ∞ (fun x : ℝ => 2*Real.sqrt Real.pi*x)
      (Ioi (0 : ℝ)) := by fun_prop
  have hnz (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) : 2*Real.sqrt Real.pi*x ≠ 0 := by
    exact ne_of_gt (mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos)) hx)
  have h := Complex.ofRealCLM.contDiff.comp_contDiffOn ((hnum.div hden hnz).neg)
  apply h.congr
  intro x hx
  exact (hasDerivAt_smoothAFECutoff hx).deriv

/-- Literal Gaussian/logarithmic slice with its complete Mellin phase. -/
def bagCubicMellinSliceValue (N : ℝ) (η : ℝ → ℝ) (τ p : ℝ) : ℂ :=
  (η p : ℂ)*smoothAFECutoff (p/N)/(Real.log p : ℂ)*
    bourgainOscillation (-τ*Real.log p)

theorem norm_bagCubicMellinSliceValue (N : ℝ) (η : ℝ → ℝ) (τ p : ℝ) :
    ‖bagCubicMellinSliceValue N η τ p‖ = ‖bagCubicMellinSliceValue N η 0 p‖ := by
  simp only [bagCubicMellinSliceValue,norm_mul,norm_bourgainOscillation,mul_one]

theorem contDiff_bagCubicMellinSliceValue {N : ℝ} (hN : 1 < N) {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hzero : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0) (τ : ℝ) :
    ContDiff ℝ ∞ (bagCubicMellinSliceValue N η τ) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : 1 < p
  · have hp0 : 0 < p := by linarith
    have hN0 : 0 < N := by linarith
    have hV : ContDiffAt ℝ ∞ (fun q : ℝ => smoothAFECutoff (q/N)) p := (contDiffOn_smoothAFECutoff_infty_pos.contDiffAt
      (Ioi_mem_nhds (div_pos hp0 hN0))).comp p (contDiffAt_id.div_const N)
    have hL : ContDiffAt ℝ ∞ (fun q : ℝ => (Real.log q : ℂ)) p := Complex.ofRealCLM.contDiff.contDiffAt.comp p
      (Real.contDiffAt_log.mpr hp0.ne')
    have hphase : ContDiffAt ℝ ∞ (fun q : ℝ => bourgainOscillation (-τ*Real.log q)) p := by
      unfold bourgainOscillation
      simp only [Complex.ofReal_mul,Complex.ofReal_neg]
      exact Complex.contDiff_exp.contDiffAt.comp p
        (contDiffAt_const.mul (contDiffAt_const.mul hL))
    have hηC : ContDiffAt ℝ ∞ (fun q : ℝ => (η q : ℂ)) p :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp p hη.contDiffAt
    change ContDiffAt ℝ ∞ (fun q : ℝ => (η q : ℂ)*smoothAFECutoff (q/N)/
      (Real.log q : ℂ)*bourgainOscillation (-τ*Real.log q)) p
    simpa only [div_eq_mul_inv,Pi.inv_apply] using
      ((hηC.mul hV).mul (hL.inv
        (Complex.ofReal_ne_zero.mpr (Real.log_pos hp).ne'))).mul hphase
  · have heq : bagCubicMellinSliceValue N η τ =ᶠ[𝓝 p] fun _ => (0 : ℂ) := by
      filter_upwards [Iio_mem_nhds (lt_of_le_of_lt (le_of_not_gt hp) hN)] with q hq
      have hz : η q=0 := hzero q (fun h => (not_lt_of_ge hq.le) h.1)
      simp [bagCubicMellinSliceValue,hz]
    exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const heq

theorem hasCompactSupport_bagCubicMellinSliceValue (N : ℝ) {η : ℝ → ℝ}
    (hη : HasCompactSupport η) (τ : ℝ) :
    HasCompactSupport (bagCubicMellinSliceValue N η τ) := by
  have hcast : HasCompactSupport (fun p : ℝ => (η p : ℂ)) := hη.comp_left (g := Complex.ofReal) rfl
  rw [show bagCubicMellinSliceValue N η τ = fun p : ℝ =>
    (η p : ℂ)*(smoothAFECutoff (p/N)/(Real.log p : ℂ)*
      bourgainOscillation (-τ*Real.log p)) by
        funext p; dsimp [bagCubicMellinSliceValue]; ring]
  exact hcast.mul_right

/-- Every admissible actual edge cutoff produces full Schwartz Mellin slices. -/
def bagCubicMellinSlice {N : ℝ} (hN : 1 < N) {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0) (τ : ℝ) : SchwartzMap ℝ ℂ :=
  (hasCompactSupport_bagCubicMellinSliceValue N hc τ).toSchwartzMap
    (contDiff_bagCubicMellinSliceValue hN hη hz τ)

@[simp] theorem bagCubicMellinSlice_apply {N : ℝ} (hN : 1 < N) {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0) (τ p : ℝ) :
    bagCubicMellinSlice hN hη hc hz τ p = bagCubicMellinSliceValue N η τ p := rfl



/-- The complete Mellin carrier of the literal physical window on the zero line. -/
def bagWindowMellinCarrier (R τ : ℝ) : ℂ :=
  (((2*Real.pi)⁻¹ : ℝ) : ℂ)*bourgainOscillation (τ*Real.log R)*
    dampedSquareWindowMellin ((τ : ℂ)*I)

theorem integrable_bagWindowMellinCarrier (R : ℝ) :
    Integrable (bagWindowMellinCarrier R) := by
  have hM : Integrable (fun τ : ℝ => dampedSquareWindowMellin ((τ : ℂ)*I)) := by
    simpa using integrable_dampedSquareWindowMellin_vertical 0
  have h := hM.bdd_mul (c := 1) (by
    unfold bourgainOscillation
    exact (by fun_prop : Continuous (fun τ : ℝ => Complex.exp (I*(τ*Real.log R : ℝ)))).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun τ : ℝ => le_of_eq (norm_bourgainOscillation (τ*Real.log R))))
  change Integrable (fun τ : ℝ => (((2*Real.pi)⁻¹ : ℝ) : ℂ)*
    bourgainOscillation (τ*Real.log R)*dampedSquareWindowMellin ((τ : ℂ)*I))
  simpa only [mul_assoc] using h.const_mul (((2*Real.pi)⁻¹ : ℝ) : ℂ)

private theorem window_inverse_phase {x : ℝ} (hx : 0 < x) :
    (bagPhysicalHeightWindow x : ℂ) = (((2*Real.pi)⁻¹ : ℝ) : ℂ)*
      ∫ τ : ℝ, bourgainOscillation (-τ*Real.log x)*dampedSquareWindowMellin ((τ : ℂ)*I) := by
  have h := (mellinInv_dampedSquareWindowMellin 0 hx).symm
  unfold mellinInv at h
  simp only [Complex.ofReal_zero,zero_add,smul_eq_mul,Complex.real_smul,one_div] at h
  rw [h]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with τ
  congr 1
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),← Complex.ofReal_log hx.le]
  unfold bourgainOscillation
  congr 1
  push_cast
  ring

/-- Exact product Mellin separation of W, retaining the entire real frequency line. -/
theorem bagPhysicalWindow_eq_mellinCarrier {p q R : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hR : 0 < R) :
    (bagPhysicalHeightWindow (p*q/R) : ℂ) =
      ∫ τ : ℝ, bagWindowMellinCarrier R τ*
        bourgainOscillation (-τ*Real.log p)*bourgainOscillation (-τ*Real.log q) := by
  rw [window_inverse_phase (div_pos (mul_pos hp hq) hR),← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with τ
  have he : bourgainOscillation (-τ*Real.log (p*q/R)) =
      bourgainOscillation (τ*Real.log R)*
        bourgainOscillation (-τ*Real.log p)*bourgainOscillation (-τ*Real.log q) := by
    rw [Real.log_div (mul_pos hp hq).ne' hR.ne',Real.log_mul hp.ne' hq.ne']
    unfold bourgainOscillation
    rw [← Complex.exp_add,← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  dsimp [bagWindowMellinCarrier]
  ring




private theorem slice_twist (N : ℝ) (η : ℝ → ℝ) (τ p : ℝ) :
    bagCubicMellinSliceValue N η τ p = bagCubicMellinSliceValue N η 0 p*
      bourgainOscillation (-τ*Real.log p) := by
  simp [bagCubicMellinSliceValue,bourgainOscillation]

/-- The full actual Gaussian/logarithmic window slice before rational atom action. -/
def bagCubicWindowKernel (N : ℝ) (η : ℝ → ℝ) (r x y : ℝ) : ℂ :=
  ∫ q : ℝ, ∫ p : ℝ, bourgainOscillation (2*Real.pi*(p*q/r+x*p+y*q))*
    (bagCubicMellinSliceValue N η 0 p*bagCubicMellinSliceValue N η 0 q)*
      (bagPhysicalHeightWindow (p*q/(r*N)) : ℂ)

/-- Full physical-window transition with absolute Mellin convergence, all
frequencies and both literal Gaussian/logarithmic amplitudes retained. -/
theorem bagCubicWindowKernel_eq_full_transition {N : ℝ} (hN : 1 < N) {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0)
    {r : ℝ} (hr : 0 < r) (x y : ℝ) :
    let F := bagCubicMellinSlice hN hη hc hz
    let B := fun τ : ℝ => bagWindowMellinCarrier (r*N) τ*
      ((r : ℂ)*bourgainOscillation (2*Real.pi*(-r*x*y))*
        bagHyperbolicTransition r (F τ) (F τ) (-r*y) (-r*x))
    Integrable B ∧ bagCubicWindowKernel N η r x y = ∫ τ : ℝ, B τ := by
  let F := bagCubicMellinSlice hN hη hc hz
  let C := bagWindowMellinCarrier (r*N)
  let D : ℝ → (ℝ × ℝ) → ℂ := fun τ z => C τ*
    (bourgainOscillation (2*Real.pi*(z.2*z.1/r+x*z.2+y*z.1))*(F τ z.2*F τ z.1))
  have htw (τ p : ℝ) : F τ p = F 0 p*bourgainOscillation (-τ*Real.log p) :=
    slice_twist N η τ p
  have hC : Integrable C := integrable_bagWindowMellinCarrier _
  have hMcont : Continuous (fun τ : ℝ => dampedSquareWindowMellin ((τ : ℂ)*I)) :=
    differentiable_dampedSquareWindowMellin.continuous.comp (by fun_prop)
  have hCcont : Continuous C := by
    change Continuous (fun τ : ℝ => (((2*Real.pi)⁻¹ : ℝ) : ℂ)*
      bourgainOscillation (τ*Real.log (r*N))*dampedSquareWindowMellin ((τ : ℂ)*I))
    unfold bourgainOscillation
    fun_prop
  have hDfun : D = fun τ z => C τ*
      (bourgainOscillation (2*Real.pi*(z.2*z.1/r+x*z.2+y*z.1))*
        ((F 0 z.2*bourgainOscillation (-τ*Real.log z.2))*
          (F 0 z.1*bourgainOscillation (-τ*Real.log z.1)))) := by
    funext τ z
    dsimp [D]
    rw [htw τ z.2,htw τ z.1]
  have hD : Integrable (Function.uncurry D) (volume.prod (volume.prod volume)) := by
    have hb := hC.norm.mul_prod
      (((F 0).integrable (μ := volume)).norm.mul_prod ((F 0).integrable (μ := volume)).norm)
    apply hb.mono'
    · change AEStronglyMeasurable (fun z : ℝ × (ℝ × ℝ) => D z.1 z.2) _
      rw [hDfun]
      apply Measurable.aestronglyMeasurable
      unfold bourgainOscillation
      have hF := (F 0).continuous.measurable
      fun_prop
    · filter_upwards [] with z
      dsimp [D,Function.uncurry]
      rw [htw z.1 z.2.2,htw z.1 z.2.1]
      simp only [norm_mul,norm_bourgainOscillation,one_mul,mul_one]
      exact le_of_eq (by ring)
  have hrow (τ : ℝ) : Integrable (D τ) (volume.prod volume) :=
    (integrable_bagHyperbolicKernel r x y (F τ) (F τ)).const_mul (C τ)
  have hroweq (τ : ℝ) :
      (∫ z : ℝ × ℝ, D τ z ∂volume.prod volume) = C τ*bagHyperbolicKernel r x y (F τ) (F τ) := by
    rw [← integral_integral (f := fun q p : ℝ => D τ (q,p)) (hrow τ)]
    dsimp [D,bagHyperbolicKernel]
    simp_rw [integral_const_mul]
  have hfreq : Integrable (fun τ : ℝ => C τ*bagHyperbolicKernel r x y (F τ) (F τ)) := by
    convert hD.integral_prod_left using 1
    funext τ
    exact (hroweq τ).symm
  have hN0 : 0 < N := by linarith
  have hpzero (p : ℝ) (hp : ¬ 0 < p) : ∀ τ : ℝ, F τ p=0 := by
    have he : η p=0 := hz p (fun h => hp (hN0.trans h.1))
    intro τ
    simp [F,bagCubicMellinSlice_apply,bagCubicMellinSliceValue,he]
  have hpoint (q p : ℝ) : (∫ τ : ℝ, D τ (q,p)) =
      bourgainOscillation (2*Real.pi*(p*q/r+x*p+y*q))*(F 0 p*F 0 q)*
        (bagPhysicalHeightWindow (p*q/(r*N)) : ℂ) := by
    by_cases hp : 0 < p
    · by_cases hq : 0 < q
      · rw [bagPhysicalWindow_eq_mellinCarrier hp hq (mul_pos hr hN0),← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with τ
        dsimp [D,C]
        rw [htw τ p,htw τ q]
        ring
      · simp [D,hpzero q hq]
    · simp [D,hpzero p hp]
  have hswap : (∫ τ : ℝ, C τ*bagHyperbolicKernel r x y (F τ) (F τ)) =
      bagCubicWindowKernel N η r x y := by
    calc
      _ = ∫ τ : ℝ, ∫ z : ℝ × ℝ, D τ z ∂volume.prod volume := by
        apply integral_congr_ae
        filter_upwards [] with τ
        exact (hroweq τ).symm
      _ = ∫ z : ℝ × ℝ, (∫ τ : ℝ, D τ z) ∂volume.prod volume := integral_integral_swap hD
      _ = ∫ q : ℝ, ∫ p : ℝ, ∫ τ : ℝ, D τ (q,p) := (integral_integral (f := fun q p : ℝ => ∫ τ : ℝ, D τ (q,p)) hD.integral_prod_right).symm
      _ = _ := by
        unfold bagCubicWindowKernel
        apply integral_congr_ae
        filter_upwards [] with q
        apply integral_congr_ae
        filter_upwards [] with p
        exact hpoint q p
  have heq (τ : ℝ) := bagHyperbolicKernel_eq_transition hr x y (F τ) (F τ)
  constructor
  · simpa only [heq] using hfreq
  · simpa only [heq] using hswap.symm


/-- The original sharp cubic admits actual smooth representatives with negligible
error and complete, absolutely convergent physical-window transitions. No
regularity, summability or arithmetic hypothesis is assumed. -/
theorem exists_bagCubicFullWindowTransitions :
    ∃ (η : ℕ → ℝ → ℝ) (F : ℕ → ℝ → SchwartzMap ℝ ℂ),
      (∀ᶠ N : ℕ in atTop,
        ContDiff ℝ ∞ (η N) ∧ HasCompactSupport (η N) ∧
        (∀ p : ℝ, η N p ∈ Icc (0 : ℝ) 1) ∧
        (∀ p : ℝ, p ∉ Ioo (N : ℝ) (2*N) → η N p=0) ∧
        (∀ p ∈ Icc ((N : ℝ)+(N : ℝ)^((1 : ℝ)/4))
          (2*N-(N : ℝ)^((1 : ℝ)/4)), η N p=1) ∧
        (∀ τ p : ℝ, F N τ p=bagCubicMellinSliceValue N (η N) τ p) ∧
        (∀ r : ℝ, 0 < r → ∀ x y : ℝ,
          let B := fun τ : ℝ => bagWindowMellinCarrier (r*N) τ*
            ((r : ℂ)*bourgainOscillation (2*Real.pi*(-r*x*y))*
              bagHyperbolicTransition r (F N τ) (F N τ) (-r*y) (-r*x))
          Integrable B ∧ bagCubicWindowKernel N (η N) r x y = ∫ τ : ℝ, B τ)) ∧
      Tendsto (fun N : ℕ => (Real.log (N : ℝ))^2/(N : ℝ)*
        ‖primeGaussianCubicOffDiagonal (N : ℝ)-
          primeGaussianCubicSmoothedOffDiagonal N (η N)‖) atTop (𝓝 0) := by
  classical
  obtain ⟨η,hη,herr⟩ := exists_primeGaussianCubic_smooth_band_negligible_error
  let Good : ℕ → Prop := fun N => 1 < (N : ℝ) ∧
    ContDiff ℝ ∞ (η N) ∧ HasCompactSupport (η N) ∧
    (∀ p : ℝ, p ∉ Ioo (N : ℝ) (2*N) → η N p=0)
  have hg : ∀ᶠ N : ℕ in atTop, Good N := by
    filter_upwards [hη,eventually_ge_atTop (2 : ℕ)] with N hreg hN
    exact ⟨by exact_mod_cast (by omega : 1 < N),hreg.1,hreg.2.1,hreg.2.2.2.1⟩
  let F : ℕ → ℝ → SchwartzMap ℝ ℂ := fun N τ =>
    if h : Good N then bagCubicMellinSlice h.1 h.2.1 h.2.2.1 h.2.2.2 τ else 0
  refine ⟨η,F,?_,herr⟩
  filter_upwards [hη,hg] with N hreg hgood
  obtain ⟨hsm,hco,hbo,hze,hpl⟩ := hreg
  refine ⟨hsm,hco,hbo,hze,hpl,?_,?_⟩
  · intro τ p
    dsimp [F]
    rw [dif_pos hgood]
    rfl
  · intro r hr x y
    simpa only [F,dif_pos hgood] using
      bagCubicWindowKernel_eq_full_transition hgood.1 hgood.2.1
        hgood.2.2.1 hgood.2.2.2 hr x y

end RHTower.BAGTrace
