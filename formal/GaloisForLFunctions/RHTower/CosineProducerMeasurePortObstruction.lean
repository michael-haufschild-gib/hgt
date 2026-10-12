import GaloisForLFunctions.RHTower.CosineProducerShiftPortObstruction
import GaloisForLFunctions.RHTower.CompactCarrierFourierBorel
import GaloisForLFunctions.RHTower.WeightedEulerPaleyWienerVanishing

/-!
# No polynomially weighted shift-average port from the cosine producer to Ξ

Let `A_h = cos(hD)Ξ` (`LocalPort.cosineProducer`) and let `L_m` be continuous linear functionals on
`C([-R, R])`, i.e. complex Radon measures `μ_m` on `[-R, R]`.

**Theorem** (`not_exists_measure_port_cosineProducer`). For `h ≠ 0` and `R ≥ 0`,
`Σ_{m<M} t^m · L_m(s ↦ A_h(t + is)) = Ξ(t)` fails for some real `t`. Polynomially weighted averages
of the cosine producer over compactly supported families of imaginary translates never give `Ξ`.
Finite combinations of point masses are special cases.

**Proof.**
* Kernel side (`apply_shiftFun`). `L(s ↦ A_h(t + is))` is the transform of `Φ(u) cosh(hu) fb_L(u)`,
  where `fb_L(u) = L(s ↦ e^{-us})` is the Fourier–Borel transform. The proof interchanges `L` with
  the Bochner integral. `t^m` acts as `(i d/du)^m`, so the port becomes `Σ_j Φ^{(j)} G_j` with
  Fourier–Borel coefficients `G_j` (`MK`).
* Separation (`MK.collect_eq_zero`). A vanishing `Σ_j Φ^{(j)} G_j` has every `G_j ≡ 0`:
  - cusp modes separate, with uniqueness for Fourier–Borel sums decaying faster than every
    exponential on a ray (`fbSum_eq_zero_of_superexp`, two-ray Paley–Wiener vanishing);
  - each mode is a polynomial in `n²` (`MK.coeffFun_eq_zero`);
  - the cusp polynomials of `Φ^{(j)}` have exact degree `j + 2`, which makes the system triangular.
* Binomial structure (`fbSum_collect_iterate_iD`). The `Φ^{(j)}`-coefficient of
  `(i d/du)^m[Φ N]` is `i^m C(m,j) N^{(m-j)}`. Descent from the top order forces `N_m ≡ 0` for
  `m ≥ 1` and `cosh(hz) fb_{L_0}(z) ≡ 1`. That fails at `z = iπ/(2h)`, where `cosh` vanishes.
-/

open Complex MeasureTheory Filter Topology Set Polynomial
open scoped Real

noncomputable section

namespace RHTower.MeasurePort

/-- The shift carrier `[-R, R]`. -/
abbrev Car (R : ℝ) : Type := Set.Icc (-R) R

/-- The coordinate on the carrier. -/
def car (R : ℝ) : C(Car R, ℂ) := ⟨fun k => ((k : ℝ) : ℂ), by fun_prop⟩

/-- Fourier–Borel transform `z ↦ L(k ↦ e^{-zk})` of a functional on `C([-R,R])`. -/
def fb {R : ℝ} (L : C(Car R, ℂ) →L[ℂ] ℂ) (z : ℂ) : ℂ := compactFourierBorel L (car R) z

theorem differentiable_fb {R : ℝ} (L : C(Car R, ℂ) →L[ℂ] ℂ) : Differentiable ℂ (fb L) :=
  fun z => ((compactFourierBorel_analyticOnNhd L (car R)) z (Set.mem_univ z)).differentiableAt

theorem norm_fb_le {R : ℝ} (L : C(Car R, ℂ) →L[ℂ] ℂ) (z : ℂ) :
    ‖fb L z‖ ≤ ‖L‖ * Real.exp (R * ‖z‖) := by
  unfold fb compactFourierBorel
  refine (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg L))
  refine (ContinuousMap.norm_le _ (Real.exp_nonneg _)).2 fun k => ?_
  rw [compactExponentialTest_apply, Complex.norm_exp]
  refine Real.exp_le_exp.2 ?_
  have hk : |(k : ℝ)| ≤ R := abs_le.mpr ⟨k.2.1, k.2.2⟩
  have h1 : (-z * car R k).re ≤ ‖z‖ * |(k : ℝ)| := by
    have := Complex.re_le_norm (-z * car R k)
    rw [norm_mul, norm_neg] at this
    simpa [car, Complex.norm_real, Real.norm_eq_abs] using this
  nlinarith [norm_nonneg z]

/-- On the negative real axis the transform grows at most like `e^{-Rx}`. -/
theorem norm_fb_real_le {R : ℝ} (L : C(Car R, ℂ) →L[ℂ] ℂ) (x : ℝ) :
    ‖fb L x‖ ≤ ‖L‖ * Real.exp (R * |x|) := by
  have := norm_fb_le L x
  rwa [Complex.norm_real, Real.norm_eq_abs] at this

/-- A finite sum `Σ a_l e^{c_l z} fb L_l(z)` of shifted Fourier–Borel transforms. -/
def fbSum {R : ℝ} (H : List (ℂ × ℝ × (C(Car R, ℂ) →L[ℂ] ℂ))) (z : ℂ) : ℂ :=
  (H.map fun p => p.1 * cexp (p.2.1 * z) * fb p.2.2 z).sum

theorem differentiable_fbSum {R : ℝ} (H : List (ℂ × ℝ × (C(Car R, ℂ) →L[ℂ] ℂ))) :
    Differentiable ℂ (fbSum H) := by
  induction H with
  | nil =>
    have h0 : fbSum ([] : List (ℂ × ℝ × (C(Car R, ℂ) →L[ℂ] ℂ))) = fun _ => (0 : ℂ) := by
      funext z; simp [fbSum]
    rw [h0]; exact differentiable_const 0
  | cons p H ih =>
    have hf : fbSum (p :: H) = fun z => p.1 * cexp (p.2.1 * z) * fb p.2.2 z + fbSum H z := by
      funext z; simp [fbSum]
    rw [hf]
    exact ((differentiable_const _).mul ((differentiable_const _).mul differentiable_id).cexp).mul
      (differentiable_fb _) |>.add ih

/-- A global exponential bound with a uniform constant. -/
theorem exists_norm_fbSum_le {R : ℝ} (H : List (ℂ × ℝ × (C(Car R, ℂ) →L[ℂ] ℂ))) :
    ∃ A c : ℝ, 0 ≤ A ∧ 0 ≤ c ∧ (∀ z : ℂ, ‖fbSum H z‖ ≤ A * Real.exp ((c + R) * ‖z‖)) ∧
      (∀ x : ℝ, x ≤ 0 → ‖fbSum H x‖ ≤ A * Real.exp (-((c + R) * x))) := by
  induction H with
  | nil => exact ⟨0, 0, le_rfl, le_rfl, fun z => by simp [fbSum], fun x _ => by simp [fbSum]⟩
  | cons p H ih =>
    obtain ⟨A, c, hA, hc, hall, hneg⟩ := ih
    set c' := max c |p.2.1| with hc'
    refine ⟨‖p.1‖ * ‖p.2.2‖ + A, c', by positivity, le_max_of_le_left hc, fun z => ?_,
      fun x hx => ?_⟩
    · have h1 : ‖p.1 * cexp (p.2.1 * z) * fb p.2.2 z‖ ≤
          ‖p.1‖ * ‖p.2.2‖ * Real.exp ((c' + R) * ‖z‖) := by
        rw [norm_mul, norm_mul, Complex.norm_exp]
        have he : (↑p.2.1 * z).re ≤ |p.2.1| * ‖z‖ := by
          have := Complex.re_le_norm (↑p.2.1 * z)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at this
          exact this
        have hfb := norm_fb_le p.2.2 z
        calc ‖p.1‖ * Real.exp (↑p.2.1 * z).re * ‖fb p.2.2 z‖
            ≤ ‖p.1‖ * Real.exp (|p.2.1| * ‖z‖) * (‖p.2.2‖ * Real.exp (R * ‖z‖)) := by
              gcongr
          _ = ‖p.1‖ * ‖p.2.2‖ * Real.exp ((|p.2.1| + R) * ‖z‖) := by
              rw [add_mul, Real.exp_add]; ring
          _ ≤ ‖p.1‖ * ‖p.2.2‖ * Real.exp ((c' + R) * ‖z‖) := by
              gcongr
              exact le_max_right _ _
      have h2 : A * Real.exp ((c + R) * ‖z‖) ≤ A * Real.exp ((c' + R) * ‖z‖) := by
        gcongr; exact le_max_left _ _
      calc ‖fbSum (p :: H) z‖ ≤ ‖p.1 * cexp (p.2.1 * z) * fb p.2.2 z‖ + ‖fbSum H z‖ := by
            simp only [fbSum, List.map_cons, List.sum_cons]; exact norm_add_le _ _
        _ ≤ _ := by nlinarith [hall z]
    · have h1 : ‖p.1 * cexp (p.2.1 * (x : ℂ)) * fb p.2.2 x‖ ≤
          ‖p.1‖ * ‖p.2.2‖ * Real.exp (-((c' + R) * x)) := by
        rw [norm_mul, norm_mul, show (p.2.1 : ℂ) * x = ((p.2.1 * x : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_exp_ofReal]
        have hfb := norm_fb_real_le p.2.2 x
        rw [abs_of_nonpos hx] at hfb
        calc ‖p.1‖ * Real.exp (p.2.1 * x) * ‖fb p.2.2 x‖
            ≤ ‖p.1‖ * Real.exp (-(|p.2.1| * x)) * (‖p.2.2‖ * Real.exp (R * -x)) := by
              gcongr
              nlinarith [neg_abs_le p.2.1]
          _ = ‖p.1‖ * ‖p.2.2‖ * Real.exp (-((|p.2.1| + R) * x)) := by
              rw [show -((|p.2.1| + R) * x) = -(|p.2.1| * x) + R * -x by ring, Real.exp_add]
              ring
          _ ≤ ‖p.1‖ * ‖p.2.2‖ * Real.exp (-((c' + R) * x)) := by
              have hm := mul_le_mul_of_nonpos_right (le_max_right c |p.2.1|) hx
              rw [← hc'] at hm
              exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
      have h2 : A * Real.exp (-((c + R) * x)) ≤ A * Real.exp (-((c' + R) * x)) := by
        have hm := mul_le_mul_of_nonpos_right (le_max_left c |p.2.1|) hx
        rw [← hc'] at hm
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hA
      calc ‖fbSum (p :: H) x‖ ≤ ‖p.1 * cexp (p.2.1 * (x : ℂ)) * fb p.2.2 x‖ + ‖fbSum H x‖ := by
            simp only [fbSum, List.map_cons, List.sum_cons]; exact norm_add_le _ _
        _ ≤ _ := by nlinarith [hneg x hx]

/-- **Uniqueness.** A finite sum of shifted Fourier–Borel transforms that decays faster than every
exponential along the positive real axis vanishes identically. -/
theorem fbSum_eq_zero_of_superexp {R : ℝ} (hR : 0 ≤ R) (H : List (ℂ × ℝ × (C(Car R, ℂ) →L[ℂ] ℂ)))
    (hdecay : ∀ M : ℝ, ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → ‖fbSum H x‖ ≤ C * Real.exp (-(M * x))) :
    fbSum H = 0 := by
  obtain ⟨A, c, hA, hc, hall, hneg⟩ := exists_norm_fbSum_le H
  set b := c + R + 1 with hb
  obtain ⟨C, hC⟩ := hdecay (b + 1)
  set g : ℂ → ℂ := fun z => fbSum H z * cexp (b * z) with hg
  have hgd : Differentiable ℂ g := (differentiable_fbSum H).mul
    ((differentiable_const _).mul differentiable_id).cexp
  have hgrow : ∀ z : ℂ, ‖g z‖ ≤ A * Real.exp ((c + R + |b|) * ‖z‖) := by
    intro z
    rw [norm_mul, Complex.norm_exp]
    have he : (↑b * z).re ≤ |b| * ‖z‖ := by
      have := Complex.re_le_norm (↑b * z)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at this
      exact this
    calc ‖fbSum H z‖ * Real.exp (↑b * z).re ≤ A * Real.exp ((c + R) * ‖z‖) *
          Real.exp (|b| * ‖z‖) := by gcongr; exact hall z
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; ring_nf
  have hC0 : 0 ≤ C := by
    have := hC 0 le_rfl
    simp at this
    exact (norm_nonneg _).trans this
  have hplus : ∀ x : ℝ, 0 ≤ x → ‖g x‖ ≤ (C + A) * Real.exp (-(1 * x)) := by
    intro x hx
    rw [norm_mul, show (b : ℂ) * x = ((b * x : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
    calc ‖fbSum H x‖ * Real.exp (b * x) ≤ C * Real.exp (-((b + 1) * x)) * Real.exp (b * x) := by
          gcongr; exact hC x hx
      _ = C * Real.exp (-(1 * x)) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ (C + A) * Real.exp (-(1 * x)) := by gcongr; linarith
  have hminus : ∀ x : ℝ, x ≤ 0 → ‖g x‖ ≤ (C + A) * Real.exp (1 * x) := by
    intro x hx
    rw [norm_mul, show (b : ℂ) * x = ((b * x : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
    calc ‖fbSum H x‖ * Real.exp (b * x) ≤ A * Real.exp (-((c + R) * x)) * Real.exp (b * x) := by
          gcongr; exact hneg x hx
      _ = A * Real.exp (1 * x) := by rw [mul_assoc, ← Real.exp_add, hb]; ring_nf
      _ ≤ (C + A) * Real.exp (1 * x) := by gcongr; linarith
  have hzero :=
    eq_zero_of_two_ray_exponential_decay hgd hA (by positivity) one_pos hgrow hplus hminus
  funext z
  have := congrFun hzero z
  simp only [hg, Pi.zero_apply, mul_eq_zero, Complex.exp_ne_zero, or_false] at this
  exact this

/-! ## The algebra of Fourier–Borel sums -/

/-- Multiplication by the negative carrier coordinate, `f ↦ -k·f`. -/
def negCar (R : ℝ) : C(Car R, ℂ) →L[ℂ] C(Car R, ℂ) :=
  ContinuousLinearMap.mul ℂ C(Car R, ℂ) (-(car R))

theorem hasDerivAt_fb {R : ℝ} (L : C(Car R, ℂ) →L[ℂ] ℂ) (z : ℂ) :
    HasDerivAt (fb L) (fb (L.comp (negCar R)) z) z := by
  -- the exponential test is entire with derivative `-k · e^{-zk}`
  have hE : HasDerivAt (compactExponentialTest (car R))
      (negCar R (compactExponentialTest (car R) z)) z := by
    have h := hasDerivAt_exp_smul_const' (𝕂 := ℂ) (-(car R)) z
    have hf : compactExponentialTest (car R) = fun u : ℂ => NormedSpace.exp (u • -(car R)) := by
      funext u; unfold compactExponentialTest; rw [smul_neg]
    rw [hf]
    refine h.congr_deriv ?_
    simp only [negCar, ContinuousLinearMap.mul_apply', smul_neg]
  exact (L.hasFDerivAt.comp_hasDerivAt z hE).congr_deriv rfl

abbrev FBList (R : ℝ) := List (ℂ × ℝ × (C(Car R, ℂ) →L[ℂ] ℂ))

/-- Termwise derivative of a Fourier–Borel sum. -/
def fbDeriv {R : ℝ} (H : FBList R) : FBList R :=
  H.flatMap fun p => [(p.1 * p.2.1, p.2.1, p.2.2), (p.1, p.2.1, p.2.2.comp (negCar R))]

theorem fbSum_nil {R : ℝ} (z : ℂ) : fbSum ([] : FBList R) z = 0 := by simp [fbSum]

theorem fbSum_cons {R : ℝ} (p : ℂ × ℝ × (C(Car R, ℂ) →L[ℂ] ℂ)) (H : FBList R) (z : ℂ) :
    fbSum (p :: H) z = p.1 * cexp (p.2.1 * z) * fb p.2.2 z + fbSum H z := by simp [fbSum]

theorem fbSum_append {R : ℝ} (H H' : FBList R) (z : ℂ) :
    fbSum (H ++ H') z = fbSum H z + fbSum H' z := by simp [fbSum, List.map_append]

theorem fbSum_flatMap {R : ℝ} {α : Type*} (L : List α) (G : α → FBList R) (z : ℂ) :
    fbSum (L.flatMap G) z = (L.map fun a => fbSum (G a) z).sum := by
  induction L with
  | nil => simp [fbSum]
  | cons a L ih => rw [List.flatMap_cons, fbSum_append, ih, List.map_cons, List.sum_cons]

theorem hasDerivAt_fbSum {R : ℝ} (H : FBList R) (z : ℂ) :
    HasDerivAt (fbSum H) (fbSum (fbDeriv H) z) z := by
  induction H with
  | nil =>
    have h0 : fbSum ([] : FBList R) = fun _ => (0 : ℂ) := funext fbSum_nil
    rw [h0]; simpa [fbDeriv, fbSum] using hasDerivAt_const z (0 : ℂ)
  | cons p H ih =>
    have hf : fbSum (p :: H) = fun w => p.1 * cexp (p.2.1 * w) * fb p.2.2 w + fbSum H w :=
      funext fun w => fbSum_cons p H w
    have he : HasDerivAt (fun w : ℂ => cexp (p.2.1 * w)) (p.2.1 * cexp (p.2.1 * z)) z := by
      have := ((hasDerivAt_id z).const_mul (p.2.1 : ℂ)).cexp
      simpa [mul_comm] using this
    have h1 := ((he.const_mul p.1).mul (hasDerivAt_fb p.2.2 z)).add ih
    rw [hf]
    refine h1.congr_deriv ?_
    simp only [fbDeriv, List.flatMap_cons, fbSum_append, fbSum_cons, fbSum_nil, add_zero]
    ring

/-- Scaling. -/
def fbScale {R : ℝ} (b : ℂ) (H : FBList R) : FBList R := H.map fun p => (b * p.1, p.2.1, p.2.2)

theorem fbSum_fbScale {R : ℝ} (b : ℂ) (H : FBList R) (z : ℂ) :
    fbSum (fbScale b H) z = b * fbSum H z := by
  induction H with
  | nil => simp [fbScale, fbSum]
  | cons p H ih =>
    simp only [fbScale, List.map_cons] at ih ⊢
    rw [fbSum_cons, fbSum_cons, ih]; ring

/-- Multiplication by `e^{γz}`. -/
def fbShift {R : ℝ} (γ : ℝ) (H : FBList R) : FBList R := H.map fun p => (p.1, p.2.1 + γ, p.2.2)

theorem fbSum_fbShift {R : ℝ} (γ : ℝ) (H : FBList R) (z : ℂ) :
    fbSum (fbShift γ H) z = cexp (γ * z) * fbSum H z := by
  induction H with
  | nil => simp [fbShift, fbSum]
  | cons p H ih =>
    simp only [fbShift, List.map_cons] at ih ⊢
    rw [fbSum_cons, fbSum_cons, ih]
    push_cast
    rw [add_mul, Complex.exp_add]
    ring

theorem fbDeriv_append {R : ℝ} (H H' : FBList R) : fbDeriv (H ++ H') = fbDeriv H ++ fbDeriv H' := by
  simp [fbDeriv, List.flatMap_append]

theorem fbSum_eq_zero_of_real {R : ℝ} {H : FBList R} (h0 : ∀ x : ℝ, fbSum H x = 0) :
    fbSum H = 0 := by
  have han : AnalyticOnNhd ℂ (fbSum H) Set.univ := fun z _ =>
    (differentiable_fbSum H).analyticAt z
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), fbSum H z = 0 := by
    have hmap : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 0) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simpa using hx
    have hne : (𝓝[≠] (0 : ℝ)).NeBot := inferInstance
    exact (hmap.frequently (Frequently.of_forall fun x => h0 x))
  funext z
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ 0) hfreq (Set.mem_univ z)

theorem fbSum_fbDeriv_eq_zero {R : ℝ} {H : FBList R} (h0 : fbSum H = 0) :
    fbSum (fbDeriv H) = 0 := by
  funext z
  have h := hasDerivAt_fbSum H z
  rw [h0] at h
  exact h.unique (hasDerivAt_const z 0)

/-! ## Kernels `Σ_j Φ^{(j)} · (Fourier–Borel sum)` -/

/-- A kernel `Σ Φ^{(j)}(u) G(u)` with Fourier–Borel coefficients `G`. -/
abbrev MK (R : ℝ) := List (ℕ × FBList R)

def MK.eval {R : ℝ} (F : MK R) (u : ℝ) : ℂ :=
  (F.map fun p => riemannKernelDeriv p.1 u * fbSum p.2 u).sum

theorem MK.eval_nil {R : ℝ} (u : ℝ) : MK.eval ([] : MK R) u = 0 := by simp [MK.eval]

theorem MK.eval_cons {R : ℝ} (p : ℕ × FBList R) (F : MK R) (u : ℝ) :
    MK.eval (p :: F) u = riemannKernelDeriv p.1 u * fbSum p.2 u + MK.eval F u := by
  simp [MK.eval]

theorem MK.eval_append {R : ℝ} (F G : MK R) (u : ℝ) :
    MK.eval (F ++ G) u = MK.eval F u + MK.eval G u := by simp [MK.eval, List.map_append]

/-- `d/du` on kernels. -/
def MK.d {R : ℝ} (F : MK R) : MK R := F.flatMap fun p => [(p.1 + 1, p.2), (p.1, fbDeriv p.2)]

theorem MK.hasDerivAt {R : ℝ} (F : MK R) (u : ℝ) :
    HasDerivAt (MK.eval F) (MK.eval (MK.d F) u) u := by
  induction F with
  | nil =>
    have h0 : MK.eval ([] : MK R) = fun _ => (0 : ℂ) := funext MK.eval_nil
    rw [h0]; simpa [MK.d, MK.eval] using hasDerivAt_const u (0 : ℂ)
  | cons p F ih =>
    have hf : MK.eval (p :: F) = fun x => riemannKernelDeriv p.1 x * fbSum p.2 x + MK.eval F x :=
      funext fun x => MK.eval_cons p F x
    have hG : HasDerivAt (fun x : ℝ => fbSum p.2 (x : ℂ)) (fbSum (fbDeriv p.2) u) u :=
      (hasDerivAt_fbSum p.2 u).comp_ofReal
    have h1 := ((hasDerivAt_riemannKernelDeriv p.1 u).mul hG).add ih
    rw [hf]
    refine h1.congr_deriv ?_
    simp only [MK.d, List.flatMap_cons, MK.eval_append, MK.eval_cons, MK.eval_nil, add_zero]

/-- `i d/du` on kernels. -/
def MK.iD {R : ℝ} (F : MK R) : MK R := (MK.d F).map fun p => (p.1, fbScale I p.2)

theorem MK.eval_iD {R : ℝ} (F : MK R) (u : ℝ) : MK.eval (MK.iD F) u = I * MK.eval (MK.d F) u := by
  unfold MK.iD
  induction MK.d F with
  | nil => simp [MK.eval]
  | cons p G ih =>
    rw [List.map_cons, MK.eval_cons, MK.eval_cons, ih, fbSum_fbScale]; ring

theorem MK.continuous_eval {R : ℝ} (F : MK R) : Continuous (MK.eval F) :=
  continuous_iff_continuousAt.mpr fun u => (MK.hasDerivAt F u).continuousAt

/-- Kernels decay faster than every exponential. -/
theorem MK.superExpDecay {R : ℝ} (F : MK R) : SuperExpDecay (MK.eval F) := by
  induction F with
  | nil => exact ⟨continuous_const, fun c => by simp [MK.eval]⟩
  | cons p F ih =>
    have hf : MK.eval (p :: F) = fun x => riemannKernelDeriv p.1 x * fbSum p.2 x + MK.eval F x :=
      funext fun x => MK.eval_cons p F x
    rw [hf]
    refine SuperExpDecay.add ?_ ih
    obtain ⟨A, c, hA, hc, hall, -⟩ := exists_norm_fbSum_le p.2
    have hcont : Continuous fun x : ℝ => riemannKernelDeriv p.1 x * fbSum p.2 x :=
      (continuous_riemannKernelDeriv p.1).mul ((differentiable_fbSum p.2).continuous.comp
        Complex.continuous_ofReal)
    refine ⟨hcont, fun c' => ?_⟩
    have hD := ((superExpDecay_riemannKernelDeriv p.1).2 (c' + c + R)).const_mul A
    refine hD.mono' (hcont.norm.mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have hx := hall x
    rw [Complex.norm_real, Real.norm_eq_abs] at hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul]
    calc ‖riemannKernelDeriv p.1 x‖ * ‖fbSum p.2 x‖ * Real.exp (c' * |x|)
        ≤ ‖riemannKernelDeriv p.1 x‖ * (A * Real.exp ((c + R) * |x|)) * Real.exp (c' * |x|) := by
          gcongr
      _ = A * (‖riemannKernelDeriv p.1 x‖ * Real.exp ((c' + c + R) * |x|)) := by
          rw [show (c' + c + R) * |x| = (c + R) * |x| + c' * |x| by ring, Real.exp_add]; ring

open Zeta23 in
theorem paperFT_MK_append {R : ℝ} (F G : MK R) (z : ℂ) :
    paperFT (MK.eval (F ++ G)) z = paperFT (MK.eval F) z + paperFT (MK.eval G) z := by
  unfold paperFT
  rw [← integral_add ((MK.superExpDecay F).integrable_mul_cexp z)
    ((MK.superExpDecay G).integrable_mul_cexp z)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [MK.eval_append]
  ring

open Zeta23 in
/-- Multiplication by `z` on the transform is `i d/du` on the kernel. -/
theorem mul_paperFT_MK {R : ℝ} (F : MK R) (z : ℂ) :
    z * paperFT (MK.eval F) z = paperFT (MK.eval (MK.iD F)) z := by
  have h := paperFT_deriv_of_superExpDecay (MK.superExpDecay F) (MK.superExpDecay (MK.d F))
    (MK.hasDerivAt F) z
  have e : MK.eval (MK.iD F) = fun u => I * MK.eval (MK.d F) u := funext (MK.eval_iD F)
  rw [e]
  unfold paperFT at h ⊢
  have : (∫ u : ℝ, I * MK.eval (MK.d F) u * cexp (I * z * u)) =
      I * ∫ u : ℝ, MK.eval (MK.d F) u * cexp (I * z * u) := by
    rw [← integral_const_mul]; congr 1; funext u; ring
  rw [this, h]
  ring_nf
  rw [I_sq]
  ring

open Zeta23 in
theorem pow_mul_paperFT_MK {R : ℝ} (m : ℕ) (F : MK R) (z : ℂ) :
    z ^ m * paperFT (MK.eval F) z = paperFT (MK.eval (MK.iD^[m] F)) z := by
  induction m generalizing F with
  | zero => simp
  | succ m ih => rw [pow_succ, mul_assoc, mul_paperFT_MK, ih, ← Function.iterate_succ_apply]

/-! ## Separation of the derivative orders -/

/-- The cusp polynomial of `Φ^{(j)}`. -/
abbrev cp (j : ℕ) : ℝ[X] := cuspDeriv^[j] riemannCuspPoly

/-- The coefficient of `Φ^{(j)}` collected from a kernel. -/
def MK.collect {R : ℝ} (j : ℕ) (F : MK R) : FBList R :=
  F.flatMap fun p => if p.1 = j then p.2 else []

/-- The `n`-th cusp head of a kernel, a Fourier–Borel sum. -/
def MK.headN {R : ℝ} (F : MK R) (n : ℕ) : FBList R :=
  F.flatMap fun p => (List.range ((cp p.1).natDegree + 1)).flatMap fun i =>
    fbScale (((cp p.1).coeff i : ℂ) * (n : ℂ) ^ (2 * i)) (fbShift (1 / 2 + 2 * i) p.2)

theorem cuspTerm_mul_fbSum {R : ℝ} (j n : ℕ) (H : FBList R) (u : ℝ) :
    (cuspTerm (cp j) n u : ℂ) * fbSum H u =
      (Real.exp (-π * ((n : ℝ) ^ 2 * Real.exp (2 * u))) : ℂ) *
        fbSum ((List.range ((cp j).natDegree + 1)).flatMap fun i =>
          fbScale (((cp j).coeff i : ℂ) * (n : ℂ) ^ (2 * i)) (fbShift (1 / 2 + 2 * i) H)) u := by
  rw [fbSum_flatMap, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  unfold cuspTerm
  rw [eval_eq_sum_range]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fbSum_fbScale, fbSum_fbShift]
  have e1 : ((n : ℂ) ^ 2 * cexp (2 * (u : ℂ))) ^ i = (n : ℂ) ^ (2 * i) * cexp (2 * i * u) := by
    rw [mul_pow, ← pow_mul, ← Complex.exp_nat_mul]; ring_nf
  have e2 : cexp (u / 2) * cexp (2 * i * u) = cexp ((1 / 2 + 2 * i : ℂ) * u) := by
    rw [← Complex.exp_add]; ring_nf
  rw [e1]
  push_cast
  rw [← e2]
  ring

theorem MK.headN_cons {R : ℝ} (p : ℕ × FBList R) (F : MK R) (n : ℕ) :
    MK.headN (p :: F) n = ((List.range ((cp p.1).natDegree + 1)).flatMap fun i =>
      fbScale (((cp p.1).coeff i : ℂ) * (n : ℂ) ^ (2 * i)) (fbShift (1 / 2 + 2 * i) p.2)) ++
      MK.headN F n := by
  simp [MK.headN, List.flatMap_cons]

/-- **Mode decomposition** for kernels with Fourier–Borel coefficients. -/
theorem MK.exists_modes_tail_le {R : ℝ} (F : MK R) (N : ℕ) : ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
    ∀ u : ℝ, 0 ≤ u → ‖MK.eval F u - ∑ k ∈ Finset.range N,
        (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) : ℂ) *
          fbSum (MK.headN F (k + 1)) u‖ ≤
      K * Real.exp (C * u) * Real.exp (-(π * ((N + 1 : ℕ) : ℝ) ^ 2) * Real.exp (2 * u)) := by
  induction F with
  | nil =>
    refine ⟨0, 0, le_rfl, le_rfl, fun u _ => ?_⟩
    simp [MK.eval, MK.headN, fbSum]
  | cons p F ih =>
    obtain ⟨K₁, C₁, hK₁, hC₁, h₁⟩ := ih
    obtain ⟨B, hB, hBle⟩ := LocalPort.exists_abs_cuspSeries_tail_from_le (cp p.1) (N + 1) (by omega)
    obtain ⟨A, c, hA, hc, hall, -⟩ := exists_norm_fbSum_le p.2
    set C₀ : ℝ := (c + R) + (1 / 2 + 2 * (cp p.1).natDegree) with hC₀
    refine ⟨A * B + K₁, max |C₀| C₁, by positivity, le_max_of_le_right hC₁, fun u hu => ?_⟩
    set Y := Real.exp (2 * u) with hY
    have hsplitR : cuspSeries (cp p.1) u = ∑ k ∈ Finset.range N, cuspTerm (cp p.1) (k + 1) u +
        ∑' n : ℕ, cuspTerm (cp p.1) (n + (N + 1)) u := by
      unfold cuspSeries
      rw [← (summable_cuspTerm (cp p.1) u).sum_add_tsum_nat_add N]
      rfl
    have hterm : ‖riemannKernelDeriv p.1 u * fbSum p.2 u - ∑ k ∈ Finset.range N,
          (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Y)) : ℂ) *
            fbSum ((List.range ((cp p.1).natDegree + 1)).flatMap fun i =>
              fbScale (((cp p.1).coeff i : ℂ) * ((k + 1 : ℕ) : ℂ) ^ (2 * i))
                (fbShift (1 / 2 + 2 * i) p.2)) u‖ ≤
        A * B * Real.exp (|C₀| * u) * Real.exp (-(π * ((N + 1 : ℕ) : ℝ) ^ 2) * Y) := by
      have hsplit : riemannKernelDeriv p.1 u * fbSum p.2 u =
          ∑ k ∈ Finset.range N, (cuspTerm (cp p.1) (k + 1) u : ℂ) * fbSum p.2 u +
            ((∑' n : ℕ, cuspTerm (cp p.1) (n + (N + 1)) u : ℝ) : ℂ) * fbSum p.2 u := by
        unfold riemannKernelDeriv
        rw [show cuspDeriv^[p.1] riemannCuspPoly = cp p.1 from rfl, hsplitR]
        push_cast
        rw [add_mul, Finset.sum_mul]
      rw [hsplit, Finset.sum_congr rfl fun k _ => cuspTerm_mul_fbSum p.1 (k + 1) p.2 u,
        add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hx := hall u
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu] at hx
      have ht := hBle u hu
      calc |∑' n : ℕ, cuspTerm (cp p.1) (n + (N + 1)) u| * ‖fbSum p.2 u‖
          ≤ (B * Real.exp ((1 / 2 + 2 * (cp p.1).natDegree) * u) *
              Real.exp (-(π * ((N + 1 : ℕ) : ℝ) ^ 2) * Y)) * (A * Real.exp ((c + R) * u)) := by
            gcongr
        _ = A * B * Real.exp (C₀ * u) * Real.exp (-(π * ((N + 1 : ℕ) : ℝ) ^ 2) * Y) := by
            rw [hC₀, show (c + R + (1 / 2 + 2 * ((cp p.1).natDegree : ℝ))) * u =
              (1 / 2 + 2 * ((cp p.1).natDegree : ℝ)) * u + (c + R) * u by ring, Real.exp_add]
            ring
        _ ≤ A * B * Real.exp (|C₀| * u) * Real.exp (-(π * ((N + 1 : ℕ) : ℝ) ^ 2) * Y) := by
            gcongr
            exact le_abs_self _
    have hrest := h₁ u hu
    have hE0 : 0 ≤ Real.exp (-(π * ((N + 1 : ℕ) : ℝ) ^ 2) * Y) := (Real.exp_pos _).le
    have hm1 : Real.exp (|C₀| * u) ≤ Real.exp (max |C₀| C₁ * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) hu)
    have hm2 : Real.exp (C₁ * u) ≤ Real.exp (max |C₀| C₁ * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hu)
    have hsum_split : ∑ k ∈ Finset.range N,
        (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Y)) : ℂ) * fbSum (MK.headN (p :: F) (k + 1)) u =
        ∑ k ∈ Finset.range N, (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Y)) : ℂ) *
            fbSum ((List.range ((cp p.1).natDegree + 1)).flatMap fun i =>
              fbScale (((cp p.1).coeff i : ℂ) * ((k + 1 : ℕ) : ℂ) ^ (2 * i))
                (fbShift (1 / 2 + 2 * i) p.2)) u +
        ∑ k ∈ Finset.range N, (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Y)) : ℂ) *
            fbSum (MK.headN F (k + 1)) u := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [MK.headN_cons, fbSum_append]; ring
    rw [MK.eval_cons, hsum_split]
    calc _ = ‖(riemannKernelDeriv p.1 u * fbSum p.2 u - ∑ k ∈ Finset.range N,
            (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Y)) : ℂ) *
              fbSum ((List.range ((cp p.1).natDegree + 1)).flatMap fun i =>
                fbScale (((cp p.1).coeff i : ℂ) * ((k + 1 : ℕ) : ℂ) ^ (2 * i))
                  (fbShift (1 / 2 + 2 * i) p.2)) u) +
          (MK.eval F u - ∑ k ∈ Finset.range N, (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Y)) : ℂ) *
            fbSum (MK.headN F (k + 1)) u)‖ := by congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hterm hrest)
      _ ≤ (A * B + K₁) * Real.exp (max |C₀| C₁ * u) *
            Real.exp (-(π * ((N + 1 : ℕ) : ℝ) ^ 2) * Y) := by
          have := mul_le_mul_of_nonneg_right hm1 (mul_nonneg (mul_nonneg hA hB) hE0)
          have := mul_le_mul_of_nonneg_right hm2 (mul_nonneg hK₁ hE0)
          nlinarith

theorem linear_sub_exp_two_mul_le {a b x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    b * x - a * Real.exp (2 * x) ≤ b ^ 2 / (8 * a) := by
  have h1 := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * x by linarith)
  have h2 : 2 * x ^ 2 ≤ Real.exp (2 * x) := by nlinarith
  have h3 : b * x - 2 * a * x ^ 2 ≤ b ^ 2 / (8 * a) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (4 * a * x - b)]
  nlinarith

/-- **Mode separation.** A vanishing kernel has vanishing cusp heads. -/
theorem MK.headN_eq_zero {R : ℝ} (hR : 0 ≤ R) (F : MK R) (hF : ∀ u : ℝ, MK.eval F u = 0)
    (n : ℕ) : fbSum (MK.headN F (n + 1)) = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨K, C, hK, hC, htail⟩ := MK.exists_modes_tail_le F (n + 1)
    refine fbSum_eq_zero_of_superexp hR _ fun M => ?_
    set a : ℝ := π * (2 * n + 3) with ha
    have ha0 : 0 < a := by positivity
    refine ⟨K * Real.exp ((C + M) ^ 2 / (8 * a)), fun x hx => ?_⟩
    have h := htail x hx
    have hprev : ∑ k ∈ Finset.range n,
        (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * x))) : ℂ) *
          fbSum (MK.headN F (k + 1)) x = 0 :=
      Finset.sum_eq_zero fun k hk => by
        rw [ih k (Finset.mem_range.mp hk)]; simp
    rw [hF x, Finset.sum_range_succ, hprev, zero_add, zero_sub, norm_neg, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h
    set Y := Real.exp (2 * x) with hY
    have hsplit : Real.exp (-(π * ((n + 1 + 1 : ℕ) : ℝ) ^ 2) * Y) =
        Real.exp (-π * (((n + 1 : ℕ) : ℝ) ^ 2 * Y)) * Real.exp (-a * Y) := by
      rw [← Real.exp_add]; congr 1; rw [ha]; push_cast; ring
    rw [hsplit] at h
    have hE := Real.exp_pos (-π * (((n + 1 : ℕ) : ℝ) ^ 2 * Y))
    have h2 : Real.exp (-π * (((n + 1 : ℕ) : ℝ) ^ 2 * Y)) * ‖fbSum (MK.headN F (n + 1)) x‖ ≤
        Real.exp (-π * (((n + 1 : ℕ) : ℝ) ^ 2 * Y)) *
          (K * Real.exp (C * x) * Real.exp (-a * Y)) := by
      have e : K * Real.exp (C * x) * (Real.exp (-π * (((n + 1 : ℕ) : ℝ) ^ 2 * Y)) *
          Real.exp (-a * Y)) = Real.exp (-π * (((n + 1 : ℕ) : ℝ) ^ 2 * Y)) *
          (K * Real.exp (C * x) * Real.exp (-a * Y)) := by ring
      linarith [h, e]
    have h' := le_of_mul_le_mul_left h2 hE
    have hq := linear_sub_exp_two_mul_le (b := C + M) ha0 hx
    calc ‖fbSum (MK.headN F (n + 1)) x‖ ≤ K * Real.exp (C * x) * Real.exp (-a * Y) := h'
      _ = K * Real.exp ((C + M) * x - a * Y) * Real.exp (-(M * x)) := by
          rw [mul_assoc K, mul_assoc K, ← Real.exp_add, ← Real.exp_add]; ring_nf
      _ ≤ K * Real.exp ((C + M) ^ 2 / (8 * a)) * Real.exp (-(M * x)) := by
          gcongr

/-- A bound on the cusp degrees occurring in a kernel. -/
def MK.degBound {R : ℝ} (F : MK R) : ℕ := (F.map fun p => (cp p.1).natDegree + 1).sum

theorem MK.natDegree_lt_degBound {R : ℝ} {F : MK R} {p : ℕ × FBList R} (hp : p ∈ F) :
    (cp p.1).natDegree < MK.degBound F := by
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun p : ℕ × FBList R =>
    (cp p.1).natDegree + 1) hp)
  unfold MK.degBound; omega

/-- The coefficient functions `W_i = Σ_p coeff_i(cp p.1) · G_p`. -/
def MK.coeffFun {R : ℝ} (F : MK R) (i : ℕ) (z : ℂ) : ℂ :=
  (F.map fun p => ((cp p.1).coeff i : ℂ) * fbSum p.2 z).sum

theorem MK.fbSum_headN {R : ℝ} (F : MK R) (n : ℕ) (z : ℂ) :
    fbSum (MK.headN F n) z = ∑ i ∈ Finset.range (MK.degBound F),
      ((n : ℂ) ^ 2) ^ i * (cexp ((1 / 2 + 2 * i : ℂ) * z) * MK.coeffFun F i z) := by
  have hper : ∀ p ∈ F, fbSum ((List.range ((cp p.1).natDegree + 1)).flatMap fun i =>
      fbScale (((cp p.1).coeff i : ℂ) * (n : ℂ) ^ (2 * i)) (fbShift (1 / 2 + 2 * i) p.2)) z =
      ∑ i ∈ Finset.range (MK.degBound F), ((n : ℂ) ^ 2) ^ i *
        (cexp ((1 / 2 + 2 * i : ℂ) * z) * (((cp p.1).coeff i : ℂ) * fbSum p.2 z)) := by
    intro p hp
    rw [fbSum_flatMap, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range,
      ← Finset.sum_subset (Finset.range_subset_range.mpr
        (show (cp p.1).natDegree + 1 ≤ MK.degBound F from MK.natDegree_lt_degBound hp))]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [fbSum_fbScale, fbSum_fbShift, ← pow_mul]
      push_cast
      ring
    · intro i _ hi
      have hc : (cp p.1).coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by
        simp only [Finset.mem_range, not_lt] at hi; omega)
      simp [hc]
  unfold MK.headN
  rw [fbSum_flatMap, List.map_congr_left hper, ← LocalPort.finset_sum_list_sum_swap]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold MK.coeffFun
  simp only [List.sum_map_mul_left]

/-- **Coefficient vanishing.** If a kernel vanishes, so does every coefficient function. -/
theorem MK.coeffFun_eq_zero {R : ℝ} (hR : 0 ≤ R) (F : MK R) (hF : ∀ u : ℝ, MK.eval F u = 0)
    (i : ℕ) (z : ℂ) : MK.coeffFun F i z = 0 := by
  by_cases hiD : MK.degBound F ≤ i
  · unfold MK.coeffFun
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have hc : (cp p.1).coeff i = 0 :=
      coeff_eq_zero_of_natDegree_lt ((MK.natDegree_lt_degBound hp).trans_le hiD)
    simp [hc]
  · have hiD' : i < MK.degBound F := not_le.mp hiD
    set Pz : ℂ[X] := ∑ k ∈ Finset.range (MK.degBound F),
      C (cexp ((1 / 2 + 2 * k : ℂ) * z) * MK.coeffFun F k z) * X ^ k with hPz
    have hroot : ∀ n : ℕ, Pz.IsRoot (((n + 1 : ℕ) : ℂ) ^ 2) := by
      intro n
      have h0 := congrFun (MK.headN_eq_zero hR F hF n) z
      rw [Pi.zero_apply, MK.fbSum_headN] at h0
      rw [Polynomial.IsRoot.def, hPz, Polynomial.eval_finsetSum]
      simpa [mul_comm] using h0
    have hPz0 : Pz = 0 := by
      refine Polynomial.eq_zero_of_infinite_isRoot Pz ?_
      refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (((n + 1 : ℕ) : ℂ) ^ 2))
        ?_ hroot
      intro a b hab
      simp only at hab
      have h1 : (a + 1) ^ 2 = (b + 1) ^ 2 := by exact_mod_cast hab
      have := Nat.pow_left_injective (by norm_num : 2 ≠ 0) h1
      omega
    have hcoeff := congrArg (fun q : ℂ[X] => q.coeff i) hPz0
    simp only [hPz, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero, Finset.sum_ite_eq, Finset.mem_range, hiD', if_true] at hcoeff
    exact (mul_eq_zero.mp hcoeff).resolve_left (Complex.exp_ne_zero _)

theorem MK.coeffFun_eq_sum_collect {R : ℝ} (F : MK R) (B : ℕ) (hB : ∀ p ∈ F, p.1 < B)
    (i : ℕ) (z : ℂ) : MK.coeffFun F i z =
      ∑ j ∈ Finset.range B, ((cp j).coeff i : ℂ) * fbSum (MK.collect j F) z := by
  induction F with
  | nil => simp [MK.coeffFun, MK.collect, fbSum]
  | cons p F ih =>
    have hpB := hB p List.mem_cons_self
    have ih' := ih fun q hq => hB q (List.mem_cons_of_mem _ hq)
    have hcol : ∀ j, fbSum (MK.collect j (p :: F)) z =
        (if p.1 = j then fbSum p.2 z else 0) + fbSum (MK.collect j F) z := by
      intro j
      simp only [MK.collect, List.flatMap_cons, fbSum_append]
      split_ifs <;> simp [fbSum]
    simp only [MK.coeffFun, List.map_cons, List.sum_cons] at ih' ⊢
    rw [ih']
    simp only [hcol, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_range, hpB, if_true]

/-- **Separation.** If `Σ Φ^{(j)} G_j` vanishes on the real line, every collected coefficient
`G_j` vanishes identically. -/
theorem MK.collect_eq_zero {R : ℝ} (hR : 0 ≤ R) (F : MK R) (hF : ∀ u : ℝ, MK.eval F u = 0)
    (j : ℕ) : fbSum (MK.collect j F) = 0 := by
  funext z
  set B := (F.map fun p => p.1 + 1).sum with hBdef
  have hB : ∀ p ∈ F, p.1 < B := by
    intro p hp
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun p : ℕ × FBList R => p.1 + 1) hp)
    omega
  have hhigh : ∀ j, B ≤ j → fbSum (MK.collect j F) z = 0 := by
    intro j hj
    have : MK.collect j F = [] := by
      unfold MK.collect
      refine List.flatMap_eq_nil_iff.mpr fun p hp => ?_
      have := hB p hp
      rw [if_neg (by omega)]
    rw [this]; simp [fbSum]
  have key : ∀ k j, B - k ≤ j → fbSum (MK.collect j F) z = 0 := by
    intro k
    induction k with
    | zero => intro j hj; exact hhigh j (by omega)
    | succ k ih =>
      intro j hj
      by_cases hj' : B - k ≤ j
      · exact ih j hj'
      · have hjB : j < B := by omega
        have hW := MK.coeffFun_eq_zero hR F hF (j + 2) z
        rw [MK.coeffFun_eq_sum_collect F B hB, Finset.sum_eq_single j] at hW
        · have hc : ((cp j).coeff (j + 2) : ℂ) ≠ 0 := by
            rw [Ne, Complex.ofReal_eq_zero]; exact LocalPort.cuspPoly_coeff_top_ne_zero j
          exact (mul_eq_zero.mp hW).resolve_left hc
        · intro j' _ hj'j
          rcases lt_or_gt_of_ne hj'j with hlt | hgt
          · have hdeg : (cp j').natDegree ≤ j' + 2 := natDegree_riemannKernelPoly_le j'
            have : (cp j').coeff (j + 2) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
            simp [this]
          · rw [ih j' (by omega), mul_zero]
        · intro h; exact absurd (Finset.mem_range.mpr hjB) h
  exact key B j (by omega)

/-! ## The derivative orders of `(i d/du)^m [Φ · G]` -/

theorem fbDeriv_flatMap {R : ℝ} {α : Type*} (L : List α) (G : α → FBList R) :
    fbDeriv (L.flatMap G) = L.flatMap fun a => fbDeriv (G a) := by
  induction L with
  | nil => simp [fbDeriv]
  | cons a L ih => rw [List.flatMap_cons, fbDeriv_append, ih, List.flatMap_cons]

theorem fbSum_fbDeriv_congr {R : ℝ} {K K' : FBList R} (c : ℂ)
    (h : fbSum K = fun z => c * fbSum K' z) :
    fbSum (fbDeriv K) = fun z => c * fbSum (fbDeriv K') z := by
  funext z
  have h1 := hasDerivAt_fbSum K z
  rw [h] at h1
  exact h1.unique ((hasDerivAt_fbSum K' z).const_mul c)

theorem fbSum_collect_d_single {R : ℝ} (p : ℕ × FBList R) (j : ℕ) (z : ℂ) :
    fbSum ([(p.1 + 1, p.2), (p.1, fbDeriv p.2)].flatMap fun q => if q.1 = j then q.2 else []) z =
      (if j = 0 then 0 else fbSum (if p.1 = j - 1 then p.2 else []) z) +
        fbSum (fbDeriv (if p.1 = j then p.2 else [])) z := by
  have hd0 : fbDeriv ([] : FBList R) = [] := by simp [fbDeriv]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, fbSum_append]
  by_cases hj : j = 0
  · subst hj
    rw [if_pos rfl, if_neg (show ¬ (p.1 + 1 = 0) by omega), fbSum_nil, zero_add, zero_add]
    by_cases h2 : p.1 = 0
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, hd0]
  · rw [if_neg hj]
    by_cases h2 : p.1 = j
    · rw [if_pos h2, if_pos h2, if_neg (show ¬ (p.1 + 1 = j) by omega),
        if_neg (show ¬ (p.1 = j - 1) by omega), fbSum_nil]
    · rw [if_neg h2, if_neg h2, hd0, fbSum_nil, add_zero, add_zero]
      by_cases h1 : p.1 + 1 = j
      · rw [if_pos h1, if_pos (show p.1 = j - 1 by omega)]
      · rw [if_neg h1, if_neg (show ¬ (p.1 = j - 1) by omega)]

theorem fbSum_collect_d {R : ℝ} (F : MK R) (j : ℕ) (z : ℂ) :
    fbSum (MK.collect j (MK.d F)) z =
      (if j = 0 then 0 else fbSum (MK.collect (j - 1) F) z) +
        fbSum (fbDeriv (MK.collect j F)) z := by
  induction F with
  | nil => simp [MK.collect, MK.d, fbDeriv, fbSum]
  | cons p F ih =>
    have hd : MK.collect j (MK.d (p :: F)) =
        ([(p.1 + 1, p.2), (p.1, fbDeriv p.2)].flatMap fun q => if q.1 = j then q.2 else []) ++
          MK.collect j (MK.d F) := by
      simp [MK.collect, MK.d, List.flatMap_cons]
    have hc : ∀ i, MK.collect i (p :: F) = (if p.1 = i then p.2 else []) ++ MK.collect i F := by
      intro i; simp [MK.collect, List.flatMap_cons]
    rw [hd, fbSum_append, ih, fbSum_collect_d_single, hc j, fbDeriv_append, fbSum_append]
    by_cases hj : j = 0
    · simp [hj]
    · rw [hc (j - 1), fbSum_append]; simp [hj]; ring

theorem fbSum_collect_iD {R : ℝ} (F : MK R) (j : ℕ) (z : ℂ) :
    fbSum (MK.collect j (MK.iD F)) z =
      I * ((if j = 0 then 0 else fbSum (MK.collect (j - 1) F) z) +
        fbSum (fbDeriv (MK.collect j F)) z) := by
  rw [← fbSum_collect_d]
  unfold MK.iD MK.collect
  rw [List.flatMap_map]
  induction MK.d F with
  | nil => simp [fbSum]
  | cons q G ih =>
    simp only [List.flatMap_cons, fbSum_append] at ih ⊢
    rw [ih, mul_add]
    congr 1
    split_ifs <;> simp [fbSum_fbScale, fbSum_nil]

/-- **Binomial structure.** `(i d/du)^m [Φ · G]` has `Φ^{(j)}`-coefficient
`i^m C(m,j) G^{(m-j)}` for `j ≤ m`, and none for `j > m`. -/
theorem fbSum_collect_iterate_iD {R : ℝ} (H : FBList R) (m j : ℕ) :
    fbSum (MK.collect j (MK.iD^[m] [(0, H)])) = fun z =>
      if j ≤ m then I ^ m * (m.choose j : ℂ) * fbSum (fbDeriv^[m - j] H) z else 0 := by
  induction m generalizing j with
  | zero =>
    funext z
    by_cases hj : j = 0
    · subst hj; simp [MK.collect]
    · have : ¬ j ≤ 0 := by omega
      have h0j : ¬ (0 = j) := fun h => hj h.symm
      simp [MK.collect, h0j, this, fbSum_nil]
  | succ m ih =>
    funext z
    rw [Function.iterate_succ_apply', fbSum_collect_iD]
    have hder : ∀ j', fbSum (fbDeriv (MK.collect j' (MK.iD^[m] [(0, H)]))) = fun z =>
        if j' ≤ m then I ^ m * (m.choose j' : ℂ) * fbSum (fbDeriv^[m - j' + 1] H) z else 0 := by
      intro j'
      by_cases hj' : j' ≤ m
      · have := fbSum_fbDeriv_congr (I ^ m * (m.choose j' : ℂ))
          (by rw [ih j']; funext w; simp [hj'])
          (K' := fbDeriv^[m - j'] H)
        rw [this]
        funext w
        simp only [hj', if_true]
        rw [← Function.iterate_succ_apply' fbDeriv]
      · have h0 : fbSum (MK.collect j' (MK.iD^[m] [(0, H)])) = fun _ => 0 := by
          rw [ih j']; funext w; simp [hj']
        have := fbSum_fbDeriv_congr 0 (K' := ([] : FBList R)) (by rw [h0]; funext w; simp)
        rw [this]
        funext w
        simp [hj']
    rw [hder j]
    by_cases hj0 : j = 0
    · subst hj0
      simp only [if_true, zero_le, Nat.choose_zero_right, Nat.cast_one, mul_one, zero_add,
        Nat.sub_zero]
      rw [pow_succ]; ring
    · rw [if_neg hj0, ih (j - 1)]
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      by_cases hle : j' + 1 ≤ m
      · have h1 : j' ≤ m := by omega
        have h2 : j' + 1 ≤ m + 1 := by omega
        simp only [h1, hle, h2, if_true]
        have hsub : m - j' = m - (j' + 1) + 1 := by omega
        have hsub' : m + 1 - (j' + 1) = m - (j' + 1) + 1 := by omega
        rw [hsub, hsub', Nat.choose_succ_succ', Nat.cast_add, pow_succ]
        ring
      · by_cases h1 : j' ≤ m
        · have hm : j' = m := by omega
          subst hm
          simp only [h1, hle, if_true, if_false, le_refl, Nat.sub_self, Nat.choose_self,
            Nat.cast_one, mul_one, add_zero, Function.iterate_zero, id]
          rw [pow_succ]; ring
        · have h2 : ¬ j' + 1 ≤ m + 1 := by omega
          simp [h1, hle, h2]

/-! ## Polynomially weighted shift averages of the cosine producer -/

theorem MK.collect_append {R : ℝ} (j : ℕ) (F G : MK R) :
    MK.collect j (F ++ G) = MK.collect j F ++ MK.collect j G := by
  simp [MK.collect, List.flatMap_append]

theorem MK.collect_flatMap {R : ℝ} {α : Type*} (j : ℕ) (L : List α) (G : α → MK R) :
    MK.collect j (L.flatMap G) = L.flatMap fun a => MK.collect j (G a) := by
  induction L with
  | nil => simp [MK.collect]
  | cons a L ih => rw [List.flatMap_cons, MK.collect_append, ih, List.flatMap_cons]

theorem MK.eval_flatMap {R : ℝ} {α : Type*} (L : List α) (G : α → MK R) (u : ℝ) :
    MK.eval (L.flatMap G) u = (L.map fun a => MK.eval (G a) u).sum := by
  induction L with
  | nil => simp [MK.eval]
  | cons a L ih => rw [List.flatMap_cons, MK.eval_append, ih, List.map_cons, List.sum_cons]

open Zeta23 in
theorem paperFT_MK_flatMap {R : ℝ} {α : Type*} (L : List α) (G : α → MK R) (z : ℂ) :
    paperFT (MK.eval (L.flatMap G)) z = (L.map fun a => paperFT (MK.eval (G a)) z).sum := by
  induction L with
  | nil =>
    simp only [List.flatMap_nil, List.map_nil, List.sum_nil]
    unfold paperFT
    simp [MK.eval]
  | cons a L ih => rw [List.flatMap_cons, paperFT_MK_append, ih, List.map_cons, List.sum_cons]

theorem fbSum_iterate_fbDeriv_eq_zero {R : ℝ} {H : FBList R} (h0 : fbSum H = 0) (r : ℕ) :
    fbSum (fbDeriv^[r] H) = 0 := by
  induction r with
  | zero => simpa using h0
  | succ r ih => rw [Function.iterate_succ_apply']; exact fbSum_fbDeriv_eq_zero ih

/-- Evaluation at the origin of the carrier. -/
def ev0 {R : ℝ} (hR : 0 ≤ R) : C(Car R, ℂ) →L[ℂ] ℂ :=
  ContinuousMap.evalCLM ℂ (⟨0, by constructor <;> linarith⟩ : Car R)

theorem fb_ev0 {R : ℝ} (hR : 0 ≤ R) (z : ℂ) : fb (ev0 hR) z = 1 := by
  simp [fb, compactFourierBorel, ev0, car]

/-- The kernel multiplier `cosh(hu) · fb L(u)` of a shift average of `A_h`. -/
def Nlist {R : ℝ} (h : ℝ) (L : C(Car R, ℂ) →L[ℂ] ℂ) : FBList R := [(1 / 2, h, L), (1 / 2, -h, L)]

theorem fbSum_Nlist {R : ℝ} (h : ℝ) (L : C(Car R, ℂ) →L[ℂ] ℂ) (z : ℂ) :
    fbSum (Nlist h L) z = Complex.cosh (h * z) * fb L z := by
  simp only [Nlist, fbSum_cons, fbSum_nil, add_zero, Complex.cosh]
  push_cast
  rw [show -(h : ℂ) * z = -(h * z) by ring]
  ring

/-- The function `s ↦ A_h(t + is)` on the carrier. -/
def shiftFun (h R t : ℝ) : C(Car R, ℂ) :=
  ⟨fun k => LocalPort.cosineProducer h ((t : ℂ) + ((k : ℝ) : ℂ) * I), by
    have hd : Differentiable ℂ (LocalPort.cosineProducer h) := by
      rw [LocalPort.cosineProducer_eq_paperFT]
      exact fun z => (LocalPort.hasDerivAt_paperFT_of_superExpDecay
        (LocalPort.KFun.superExpDecay _) z).differentiableAt
    exact hd.continuous.comp (continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const))⟩

theorem norm_compactExponentialTest_real_le {R : ℝ} (u : ℝ) :
    ‖compactExponentialTest (car R) (u : ℂ)‖ ≤ Real.exp (R * |u|) := by
  refine (ContinuousMap.norm_le _ (Real.exp_nonneg _)).2 fun k => ?_
  rw [compactExponentialTest_apply, Complex.norm_exp]
  refine Real.exp_le_exp.2 ?_
  have hk : |(k : ℝ)| ≤ R := abs_le.mpr ⟨k.2.1, k.2.2⟩
  have : (-(u : ℂ) * car R k).re = -(u * (k : ℝ)) := by simp [car]
  rw [this]
  have h1 : -(u * (k : ℝ)) ≤ |u| * |(k : ℝ)| := by rw [← abs_mul]; exact neg_le_abs _
  nlinarith [abs_nonneg u]

open Zeta23 in
/-- **Kernel of a shift average.** `L(s ↦ A_h(t + is)) = ∫ Φ(u) cosh(hu) fb L(u) e^{itu} du`. -/
theorem apply_shiftFun {R : ℝ} (h : ℝ) (L : C(Car R, ℂ) →L[ℂ] ℂ) (t : ℝ) :
    L (shiftFun h R t) = paperFT (MK.eval [(0, Nlist h L)]) t := by
  set g : ℝ → ℂ := fun u => riemannPhiKernel u * (Real.cosh (h * u) : ℂ) * cexp (I * t * u)
    with hg
  set E : ℝ → C(Car R, ℂ) := fun u => compactExponentialTest (car R) (u : ℂ) with hE
  have hEc : Continuous E :=
    (compactExponentialTest_analyticOnNhd (car R)).continuous.comp Complex.continuous_ofReal
  have hdec := LocalPort.KFun.superExpDecay (LocalPort.cosineKernel h)
  have hgc : Continuous g := by
    have := hdec.1
    simp only [hg]
    have hk : (fun u => riemannPhiKernel u * (Real.cosh (h * u) : ℂ)) =
        LocalPort.KFun.eval (LocalPort.cosineKernel h) := funext fun u =>
      (LocalPort.cosineKernel_eval h u).symm
    exact (hk ▸ this).mul (by fun_prop)
  have hint : Integrable fun u => g u • E u := by
    refine (hdec.2 R).mono' (hgc.smul hEc).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [norm_smul]
    have hgu : ‖g u‖ = ‖LocalPort.KFun.eval (LocalPort.cosineKernel h) u‖ := by
      rw [LocalPort.cosineKernel_eval, hg]
      simp only [norm_mul]
      rw [show I * (t : ℂ) * u = ((t * u : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I,
        mul_one]
    rw [hgu]
    exact mul_le_mul_of_nonneg_left (norm_compactExponentialTest_real_le u) (norm_nonneg _)
  have hfun : shiftFun h R t = ∫ u, g u • E u := by
    ext k
    have h1 := ContinuousLinearMap.integral_comp_comm (ContinuousMap.evalCLM ℂ k) hint
    rw [ContinuousMap.evalCLM_apply] at h1
    rw [← h1]
    simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, smul_eq_mul, hE,
      compactExponentialTest_apply, hg]
    simp only [shiftFun, ContinuousMap.coe_mk]
    rw [LocalPort.cosineProducer]
    unfold paperFT
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [car, ContinuousMap.coe_mk]
    rw [show I * ((t : ℂ) + ((k : ℝ) : ℂ) * I) * (u : ℂ) = I * t * u + -(u : ℂ) * ((k : ℝ) : ℂ) by
      ring_nf; rw [I_sq]; ring, Complex.exp_add]
    ring
  rw [hfun, ← ContinuousLinearMap.integral_comp_comm L hint]
  unfold paperFT
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [ContinuousLinearMap.map_smul, smul_eq_mul, hg, hE, MK.eval_cons, MK.eval_nil,
    add_zero, riemannKernelDeriv_zero, fbSum_Nlist]
  have hfb : L (compactExponentialTest (car R) (u : ℂ)) = fb L u := rfl
  rw [hfb]
  push_cast
  ring

open Zeta23 in
/-- **No polynomially weighted shift-average port from the cosine producer to `Ξ`.** For real
`h ≠ 0`, `R ≥ 0` and continuous linear functionals `L_m` on `C([-R,R])` (complex Radon measures
`μ_m`), `Σ_{m<M} t^m ∫ A_h(t + is) dμ_m(s) = Ξ(t)` fails for some real `t`. -/
theorem not_exists_measure_port_cosineProducer {h : ℝ} (hh : h ≠ 0) {R : ℝ} (hR : 0 ≤ R)
    (M : ℕ) (L : ℕ → C(Car R, ℂ) →L[ℂ] ℂ) :
    ¬ ∀ t : ℝ, ∑ m ∈ Finset.range M, (t : ℂ) ^ m * L m (shiftFun h R t) = XiC t := by
  intro H
  set Fp : MK R := (List.range M).flatMap (fun m => MK.iD^[m] [(0, Nlist h (L m))]) ++
    [(0, [(-1, 0, ev0 hR)])] with hFp
  have hPhi : ∀ w : ℂ, paperFT riemannPhiKernel w = XiC w := fun w => by
    rw [paperFT_riemannPhiKernel, riemannPhiTransform_eq_xi, XiC, mul_comm]
  have hneg : ∀ z : ℂ,
      paperFT (MK.eval [((0 : ℕ), [((-1 : ℂ), (0 : ℝ), ev0 hR)])]) z = -XiC z := by
    intro z
    rw [← hPhi]
    unfold paperFT
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp [MK.eval, fbSum, fb_ev0, riemannKernelDeriv_zero]
  have hker : ∀ t : ℝ, paperFT (MK.eval Fp) t = 0 := by
    intro t
    rw [hFp, paperFT_MK_append, paperFT_MK_flatMap, hneg, ← H t,
      ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
    rw [Finset.sum_congr rfl fun m _ => (pow_mul_paperFT_MK m [(0, Nlist h (L m))] t).symm]
    simp only [← apply_shiftFun]
    ring
  have heval : MK.eval Fp = 0 :=
    LocalPort.eq_zero_of_paperFT_real_eq_zero (MK.superExpDecay Fp) hker
  have hsep := MK.collect_eq_zero hR Fp fun u => by rw [heval]; rfl
  have hcoll : ∀ j (z : ℂ), fbSum (MK.collect j Fp) z = ∑ m ∈ Finset.range M,
      (if j ≤ m then I ^ m * (m.choose j : ℂ) * fbSum (fbDeriv^[m - j] (Nlist h (L m))) z
        else 0) + (if j = 0 then -1 else 0) := by
    intro j z
    rw [hFp, MK.collect_append, fbSum_append, MK.collect_flatMap, fbSum_flatMap,
      ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
    congr 1
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [fbSum_collect_iterate_iD]
    · by_cases hj : j = 0
      · subst hj; simp [MK.collect, fbSum_cons, fbSum_nil, fb_ev0]
      · have : ¬ ((0 : ℕ) = j) := fun h' => hj h'.symm
        simp [MK.collect, hj, this, fbSum_nil]
  -- downward descent through the derivative orders
  have key : ∀ k m, 1 ≤ m → m < M → M - k ≤ m → fbSum (Nlist h (L m)) = 0 := by
    intro k
    induction k with
    | zero => intro m _ hmM hk; omega
    | succ k ih =>
      intro m hm1 hmM hk
      by_cases hk' : M - k ≤ m
      · exact ih m hm1 hmM hk'
      · funext z
        have hz := congrFun (hsep m) z
        rw [Pi.zero_apply, hcoll, if_neg (by omega), add_zero,
          Finset.sum_eq_single m] at hz
        · rw [if_pos le_rfl, Nat.choose_self, Nat.sub_self, Function.iterate_zero, id,
            Nat.cast_one, mul_one] at hz
          exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ I_ne_zero)
        · intro m' hm' hne
          by_cases hle : m ≤ m'
          · have hgt : m < m' := lt_of_le_of_ne hle (Ne.symm hne)
            rw [if_pos hle, fbSum_iterate_fbDeriv_eq_zero
              (ih m' (by omega) (Finset.mem_range.mp hm') (by omega)), Pi.zero_apply, mul_zero]
          · rw [if_neg hle]
        · intro hm; exact absurd (Finset.mem_range.mpr hmM) hm
  -- the zeroth order: `cosh(hz) · fb L₀(z) = 1`
  have h0 : ∀ z : ℂ, M ≠ 0 → fbSum (Nlist h (L 0)) z = 1 := by
    intro z hM
    have hz := congrFun (hsep 0) z
    rw [Pi.zero_apply, hcoll, if_pos rfl, Finset.sum_eq_single 0] at hz
    · simp only [le_refl, if_true, pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
        Nat.sub_zero, Function.iterate_zero, id, one_mul] at hz
      linear_combination hz
    · intro m hm hne
      rw [if_pos (Nat.zero_le m), fbSum_iterate_fbDeriv_eq_zero
        (key M m (Nat.pos_of_ne_zero hne) (Finset.mem_range.mp hm) (by omega)), Pi.zero_apply,
        mul_zero]
    · intro h0; exact absurd (Finset.mem_range.mpr (Nat.pos_of_ne_zero hM)) h0
  by_cases hM : M = 0
  · have hz := congrFun (hsep 0) 0
    rw [Pi.zero_apply, hcoll, hM] at hz
    simp at hz
  · set z₀ : ℂ := ((π / 2 / h : ℝ) : ℂ) * I with hz₀
    have h1 := h0 z₀ hM
    rw [fbSum_Nlist] at h1
    have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh
    have hcosh : Complex.cosh (h * z₀) = 0 := by
      rw [hz₀, show (h : ℂ) * (((π / 2 / h : ℝ) : ℂ) * I) = ((π : ℂ) / 2) * I by
        push_cast; field_simp, Complex.cosh_mul_I, Complex.cos_pi_div_two]
    rw [hcosh, zero_mul] at h1
    exact zero_ne_one h1

end RHTower.MeasurePort
