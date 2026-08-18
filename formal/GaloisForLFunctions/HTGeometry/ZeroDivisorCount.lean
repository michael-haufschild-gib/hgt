import GaloisForLFunctions.HTGeometry.DiscZeroFactorization
import GaloisForLFunctions.HTGeometry.AnalyticBallFinsetFactorization
import Mathlib.Analysis.Complex.Liouville

/-!
# The zero count of a disc as a contour integral

The order of vanishing of a function presented as a finite product of powers of linear factors times
a nonvanishing analytic factor is read off the exponents, so the divisor of an analytic function on
a disc is the exponent function of any such presentation.  Combined with the weighted argument
principle at weight zero, the total multiplicity of the zeros inside a circle on which the function
does not vanish is the contour integral of its logarithmic derivative.

Being simultaneously an integer and a continuous function of the integrand, that count is locally
constant: a small uniform perturbation of the function does not change the number of its zeros.
-/

open Complex Metric Set Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

/-! ### Translating the centre of a circle integral -/

theorem circleMap_zero_add (c : ℂ) (t θ : ℝ) : circleMap 0 t θ + c = circleMap c t θ := by
  simp [circleMap]
  ring

/-- A circle integral about `c` is the circle integral about the origin of the translated
integrand. -/
theorem circleIntegral_translate (F : ℂ → ℂ) (c : ℂ) (t : ℝ) :
    (∮ ζ in C(0, t), F (ζ + c)) = ∮ w in C(c, t), F w := by
  simp only [circleIntegral, deriv_circleMap]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [circleMap_zero_add]

/-! ### The order of a factorized function -/

/-- The order of vanishing of a power of a linear factor. -/
theorem analyticOrderAt_sub_pow (u : ℂ) (k : ℕ) (a : ℂ) :
    analyticOrderAt (fun z : ℂ => (z - u) ^ k) a = (if a = u then (k : ℕ∞) else 0) := by
  classical
  by_cases h : a = u
  · subst h
    have hrw : (fun z : ℂ => (z - a) ^ k) = ((· - a) ^ k : ℂ → ℂ) := by
      funext z
      simp
    rw [if_pos rfl, hrw]
    exact analyticOrderAt_centeredMonomial
  · have hne : ((a - u) ^ k : ℂ) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr h)
    have han : AnalyticAt ℂ (fun z : ℂ => (z - u) ^ k) a :=
      (analyticAt_id.sub analyticAt_const).pow k
    rw [if_neg h, han.analyticOrderAt_eq_zero]
    exact hne

/-- The order of vanishing of a finite product of powers of linear factors is the exponent at the
base point. -/
theorem analyticOrderAt_finset_prod_pow (s : Finset ℂ) (m : ℂ → ℕ) (a : ℂ) :
    analyticOrderAt (fun z : ℂ => ∏ u ∈ s, (z - u) ^ m u) a
      = (if a ∈ s then (m a : ℕ∞) else 0) := by
  classical
  induction s using Finset.induction with
  | empty => simp [analyticOrderAt_eq_zero]
  | insert b s hb ih =>
      have hfun : (fun z : ℂ => ∏ u ∈ insert b s, (z - u) ^ m u)
          = (fun z : ℂ => (z - b) ^ m b) * fun z : ℂ => ∏ u ∈ s, (z - u) ^ m u := by
        funext z
        simp [Finset.prod_insert hb]
      have h1 : AnalyticAt ℂ (fun z : ℂ => (z - b) ^ m b) a :=
        (analyticAt_id.sub analyticAt_const).pow _
      have h2 : AnalyticAt ℂ (fun z : ℂ => ∏ u ∈ s, (z - u) ^ m u) a :=
        Finset.analyticAt_fun_prod s fun u _ => (analyticAt_id.sub analyticAt_const).pow _
      rw [hfun, analyticOrderAt_mul h1 h2, analyticOrderAt_sub_pow, ih]
      by_cases hab : a = b
      · subst hab
        simp [hb]
      · by_cases has : a ∈ s
        · simp [hab, has]
        · simp [hab, has]


/-! ### The multiplicity of a zero -/

/-- The multiplicity of a zero of an analytic function, as a natural number: the order of vanishing,
and `0` where the function vanishes identically. -/
noncomputable def zeroMult (f : ℂ → ℂ) (a : ℂ) : ℕ := (analyticOrderAt f a).toNat

/-- **The multiplicities of a factorized function are its exponents.** -/
theorem zeroMult_of_factorization {V : Set ℂ} (hV : IsOpen V) {f g : ℂ → ℂ}
    (s : Finset ℂ) (m : ℂ → ℕ)
    (hgd : DifferentiableOn ℂ g V) (hgne : ∀ z ∈ V, g z ≠ 0)
    (heq : Set.EqOn f (fun z => (∏ u ∈ s, (z - u) ^ m u) * g z) V)
    {a : ℂ} (ha : a ∈ V) :
    zeroMult f a = if a ∈ s then m a else 0 := by
  classical
  have hev : f =ᶠ[nhds a] fun z => (∏ u ∈ s, (z - u) ^ m u) * g z :=
    Filter.eventuallyEq_of_mem (hV.mem_nhds ha) heq
  have hgan : AnalyticAt ℂ g a := (hgd.analyticOnNhd hV) a ha
  have hprod : AnalyticAt ℂ (fun z : ℂ => ∏ u ∈ s, (z - u) ^ m u) a :=
    Finset.analyticAt_fun_prod s fun u _ => (analyticAt_id.sub analyticAt_const).pow _
  have hfun : (fun z : ℂ => (∏ u ∈ s, (z - u) ^ m u) * g z)
      = (fun z : ℂ => ∏ u ∈ s, (z - u) ^ m u) * g := rfl
  have horder : analyticOrderAt f a = (if a ∈ s then (m a : ℕ∞) else 0) := by
    rw [analyticOrderAt_congr hev, hfun, analyticOrderAt_mul hprod hgan,
      analyticOrderAt_finset_prod_pow, hgan.analyticOrderAt_eq_zero.mpr (hgne a ha)]
    simp
  rw [zeroMult, horder]
  by_cases h : a ∈ s <;> simp [h]

/-! ### The argument principle -/

/-- **The zero count of a disc is a contour integral.**  For a function holomorphic on a
neighbourhood of a closed disc and nonvanishing on a smaller circle, the total multiplicity of its
zeros inside that circle is the contour integral of its logarithmic derivative, divided by `2πi`. -/
theorem exists_zeroSet_circleIntegral_logDeriv {c : ℂ} {t R : ℝ} (ht : 0 < t) (htR : t < R)
    {U : Set ℂ} (hU : IsOpen U) (hsub : closedBall c R ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hne : ∀ ζ ∈ sphere c t, f ζ ≠ 0) :
    ∃ Z : Finset ℂ, (∀ ρ ∈ Z, ρ ∈ ball c t) ∧
      (∀ z ∈ ball c t, f z = 0 ↔ z ∈ Z) ∧
      (∮ ζ in C(c, t), logDeriv f ζ)
        = (2 * (Real.pi : ℂ) * Complex.I) * ∑ ρ ∈ Z, (zeroMult f ρ : ℂ) := by
  classical
  have hR : 0 < R := lt_trans ht htR
  have hfan : AnalyticOnNhd ℂ f (closedBall c R) := by
    intro z hz
    exact (hf.analyticOnNhd hU) z (hsub hz)
  -- a point of the smaller circle, where `f` does not vanish
  have hz₀ : c + (t : ℂ) ∈ ball c R := by
    rw [mem_ball, dist_eq_norm]
    simpa [abs_of_pos ht] using htR
  have hfz₀ : f (c + (t : ℂ)) ≠ 0 := by
    refine hne _ ?_
    rw [mem_sphere, dist_eq_norm]
    simp [abs_of_pos ht]
  obtain ⟨Zf, m, g, hZball, hZ1, hZzero, hgan, hgne, heq⟩ :=
    _root_.HTGeometry.exists_finset_zeroFree_factorization hfan hz₀ hfz₀
  set Z : Finset ℂ := Zf.filter (fun ρ => ρ ∈ ball c t) with hZdef
  have hballsub : ball c t ⊆ ball c R := ball_subset_ball htR.le
  have hgd : DifferentiableOn ℂ g (ball c R) := hgan.differentiableOn
  have hmult : ∀ a ∈ ball c R, zeroMult f a = if a ∈ Zf then m a else 0 := fun a ha =>
    zeroMult_of_factorization isOpen_ball Zf m hgd hgne heq ha
  refine ⟨Z, fun ρ hρ => (Finset.mem_filter.mp hρ).2, fun z hz => ?_, ?_⟩
  · rw [hZdef, Finset.mem_filter]
    constructor
    · intro h0
      exact ⟨(hZzero z (hballsub hz)).mp h0, hz⟩
    · intro h
      exact (hZzero z (hballsub hz)).mpr h.1
  -- the integrand, rewritten through the factorization
  have hsphere : ∀ ζ ∈ sphere c t, logDeriv f ζ
      = (∑ ρ ∈ Zf, (m ρ : ℂ) / (ζ - ρ)) + logDeriv g ζ := by
    intro ζ hζ
    have hζball : ζ ∈ ball c R := by
      rw [mem_ball, mem_sphere.mp hζ]
      exact htR
    have hev : f =ᶠ[nhds ζ] fun z => (∏ u ∈ Zf, (z - u) ^ m u) * g z :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hζball) heq
    have hζZ : ∀ ρ ∈ Zf, ζ ≠ ρ := by
      intro ρ hρ hcon
      exact hne ζ hζ ((hZzero ζ hζball).mpr (hcon ▸ hρ))
    have hPne : (∏ u ∈ Zf, (ζ - u) ^ m u) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun u hu => pow_ne_zero _ (sub_ne_zero.mpr (hζZ u hu))
    have hPd : DifferentiableAt ℂ (fun z : ℂ => ∏ u ∈ Zf, (z - u) ^ m u) ζ := by fun_prop
    have hgdζ : DifferentiableAt ℂ g ζ := (hgan ζ hζball).differentiableAt
    rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
    rw [← logDeriv_apply, logDeriv_mul ζ hPne (hgne ζ hζball) hPd hgdζ,
      _root_.HTGeometry.logDeriv_finset_prod_pow hζZ]
  rw [circleIntegral.integral_congr ht.le hsphere]
  -- the two pieces
  have hint1 : ∀ ρ ∈ Zf, CircleIntegrable (fun z : ℂ => (m ρ : ℂ) / (z - ρ)) c t := by
    intro ρ hρ
    have hcont : ContinuousOn (fun z : ℂ => (m ρ : ℂ) / (z - ρ)) (sphere c t) := by
      refine ContinuousOn.div continuousOn_const (by fun_prop) fun z hz => ?_
      refine sub_ne_zero.mpr ?_
      intro hcon
      have hz' : z ∈ ball c R := by
        rw [mem_ball, mem_sphere.mp hz]; exact htR
      exact hne z hz ((hZzero z hz').mpr (hcon ▸ hρ))
    exact ContinuousOn.circleIntegrable ht.le hcont
  have hintg : CircleIntegrable (logDeriv g) c t := by
    refine ContinuousOn.circleIntegrable ht.le ?_
    intro z hz
    have hz' : z ∈ ball c R := by
      rw [mem_ball, mem_sphere.mp hz]; exact htR
    have hlog : AnalyticAt ℂ (logDeriv g) z := by
      have hrw : logDeriv g = fun w => deriv g w / g w := by
        funext w
        rw [logDeriv_apply]
      rw [hrw]
      exact ((hgan.deriv) z hz').div (hgan z hz') (hgne z hz')
    exact hlog.continuousAt.continuousWithinAt
  have hintsum : CircleIntegrable (fun z : ℂ => ∑ ρ ∈ Zf, (m ρ : ℂ) / (z - ρ)) c t :=
    _root_.HTGeometry.circleIntegrable_finset_sum
      (fun ρ z => (m ρ : ℂ) / (z - ρ)) c t Zf hint1
  rw [circleIntegral.integral_add hintsum hintg,
    _root_.HTGeometry.circleIntegral_finset_sum (fun ρ z => (m ρ : ℂ) / (z - ρ)) c t Zf hint1]
  -- the nonvanishing factor contributes nothing
  have hg0 : (∮ z in C(c, t), logDeriv g z) = 0 := by
    refine DiffContOnCl.circleIntegral_eq_zero ht.le ?_
    refine DiffContOnCl.mk ?_ ?_
    · intro z hz
      have hz' : z ∈ ball c R := ball_subset_ball htR.le hz
      have hrw : logDeriv g = fun w => deriv g w / g w := by
        funext w
        rw [logDeriv_apply]
      rw [hrw]
      exact (((hgan.deriv) z hz').div (hgan z hz') (hgne z hz')).differentiableAt
        |>.differentiableWithinAt
    · rw [closure_ball c ht.ne']
      intro z hz
      have hz' : z ∈ ball c R := by
        rw [mem_ball]
        exact lt_of_le_of_lt (mem_closedBall.mp hz) htR
      have hrw : logDeriv g = fun w => deriv g w / g w := by
        funext w
        rw [logDeriv_apply]
      rw [hrw]
      exact (((hgan.deriv) z hz').div (hgan z hz') (hgne z hz')).continuousAt.continuousWithinAt
  rw [hg0, add_zero]
  -- each linear factor contributes `2πi` when its base point is inside, and nothing otherwise
  have hterm : ∀ ρ ∈ Zf, (∮ z in C(c, t), (m ρ : ℂ) / (z - ρ))
      = if ρ ∈ ball c t then (2 * (Real.pi : ℂ) * Complex.I) * (m ρ : ℂ) else 0 := by
    intro ρ hρ
    have hrw : (fun z : ℂ => (m ρ : ℂ) / (z - ρ)) = fun z : ℂ => (m ρ : ℂ) * (z - ρ)⁻¹ := by
      funext z
      rw [div_eq_mul_inv]
    rw [hrw, circleIntegral.integral_const_mul (m ρ : ℂ) (fun z : ℂ => (z - ρ)⁻¹) c t]
    by_cases hin : ρ ∈ ball c t
    · rw [if_pos hin, circleIntegral.integral_sub_inv_of_mem_ball hin]
      ring
    · rw [if_neg hin]
      -- no base point lies on the circle either, so the integrand is holomorphic on the disc
      have hsph : ρ ∉ sphere c t := by
        intro hcon
        have hρball : ρ ∈ ball c R := by
          rw [mem_ball, mem_sphere.mp hcon]
          exact htR
        exact hne ρ hcon ((hZzero ρ hρball).mpr hρ)
      have hne' : ∀ z ∈ closedBall c t, z ≠ ρ := by
        intro z hz hcon
        subst hcon
        rcases lt_or_eq_of_le (mem_closedBall.mp hz) with hlt | heqd
        · exact hin (mem_ball.mpr hlt)
        · exact hsph (mem_sphere.mpr heqd)
      have hdiff : ∀ z ∈ closedBall c t, DifferentiableAt ℂ (fun w : ℂ => (w - ρ)⁻¹) z := by
        intro z hz
        exact ((differentiable_id.sub_const ρ) z).inv (sub_ne_zero.mpr (hne' z hz))
      have hout : (∮ z in C(c, t), (z - ρ)⁻¹) = 0 := by
        refine DiffContOnCl.circleIntegral_eq_zero ht.le (DiffContOnCl.mk ?_ ?_)
        · intro z hz
          exact (hdiff z (ball_subset_closedBall hz)).differentiableWithinAt
        · rw [closure_ball c ht.ne']
          intro z hz
          exact (hdiff z hz).continuousAt.continuousWithinAt
      rw [hout]
      simp
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.mul_sum]
  rw [hZdef, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  by_cases hin : ρ ∈ ball c t
  · rw [if_pos hin, if_pos hin, hmult ρ (hballsub hin), if_pos hρ]
  · rw [if_neg hin, if_neg hin]

/-! ### The zero sum as a function of the function -/

/-- The total multiplicity of the zeros inside a circle, read off the contour integral of the
logarithmic derivative. -/
noncomputable def zeroSumBall (f : ℂ → ℂ) (c : ℂ) (t : ℝ) : ℂ :=
  (∮ ζ in C(c, t), logDeriv f ζ) / (2 * (Real.pi : ℂ) * Complex.I)

theorem twoPiI_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero

/-- **The argument principle, in normalized form.** -/
theorem exists_zeroSet_zeroSumBall {c : ℂ} {t R : ℝ} (ht : 0 < t) (htR : t < R)
    {U : Set ℂ} (hU : IsOpen U) (hsub : closedBall c R ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hne : ∀ ζ ∈ sphere c t, f ζ ≠ 0) :
    ∃ Z : Finset ℂ, (∀ ρ ∈ Z, ρ ∈ ball c t) ∧
      (∀ z ∈ ball c t, f z = 0 ↔ z ∈ Z) ∧
      zeroSumBall f c t = ∑ ρ ∈ Z, (zeroMult f ρ : ℂ) := by
  obtain ⟨Z, hZball, hZzero, hint⟩ :=
    exists_zeroSet_circleIntegral_logDeriv ht htR hU hsub hf hne
  refine ⟨Z, hZball, hZzero, ?_⟩
  rw [zeroSumBall, hint, mul_comm]
  field_simp

/-- The zero sum is a natural number. -/
theorem exists_nat_zeroSumBall {c : ℂ} {t R : ℝ} (ht : 0 < t) (htR : t < R)
    {U : Set ℂ} (hU : IsOpen U) (hsub : closedBall c R ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hne : ∀ ζ ∈ sphere c t, f ζ ≠ 0) :
    ∃ N : ℕ, zeroSumBall f c t = (N : ℂ) := by
  obtain ⟨Z, -, -, hsum⟩ := exists_zeroSet_zeroSumBall ht htR hU hsub hf hne
  refine ⟨∑ ρ ∈ Z, zeroMult f ρ, ?_⟩
  rw [hsum]
  push_cast
  rfl

/-! ### The zero sum is stable under small uniform perturbations -/

/-- Small closed discs about the points of a circle stay inside the larger disc. -/
theorem closedBall_subset_of_mem_sphere {c ζ : ℂ} {t R : ℝ} (htR : t < R)
    (hζ : ζ ∈ sphere c t) : closedBall ζ ((R - t) / 2) ⊆ closedBall c R := by
  intro w hw
  have h1 : dist w ζ ≤ (R - t) / 2 := mem_closedBall.mp hw
  have h2 : dist ζ c = t := mem_sphere.mp hζ
  have h3 : dist w c ≤ dist w ζ + dist ζ c := dist_triangle w ζ c
  rw [mem_closedBall]
  linarith

/-- **The logarithmic derivative is uniformly close on the circle.**  A function holomorphic on a
neighbourhood of a closed disc, nonvanishing on a smaller circle, has logarithmic derivative within
any prescribed tolerance of that of every sufficiently close holomorphic function. -/
theorem exists_eps_norm_logDeriv_sub_le {c : ℂ} {t R : ℝ} (ht : 0 < t) (htR : t < R)
    {U : Set ℂ} (hU : IsOpen U) (hsub : closedBall c R ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hne : ∀ ζ ∈ sphere c t, f ζ ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ h : ℂ → ℂ, DifferentiableOn ℂ h U →
      (∀ z ∈ closedBall c R, ‖h z - f z‖ ≤ ε) →
        ∀ ζ ∈ sphere c t, ‖logDeriv h ζ - logDeriv f ζ‖ ≤ η := by
  classical
  set r : ℝ := (R - t) / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  have hcompact : IsCompact (sphere c t) := isCompact_sphere c t
  have hnonempty : (sphere c t).Nonempty := ⟨c + (t : ℂ), by
    rw [mem_sphere, dist_eq_norm]
    simp [abs_of_pos ht]⟩
  have hsphsub : sphere c t ⊆ closedBall c R := fun z hz => by
    rw [mem_closedBall, mem_sphere.mp hz]
    exact htR.le
  have hfcont : ContinuousOn f (closedBall c R) :=
    (hf.mono hsub).continuousOn
  have hderivcont : ContinuousOn (deriv f) (closedBall c R) := by
    intro z hz
    have han : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hU
    exact ((han.deriv) z (hsub hz)).continuousAt.continuousWithinAt
  -- the minimum of `‖f‖` and the maxima of `‖f‖` and `‖deriv f‖` on the circle
  obtain ⟨ζ₀, hζ₀, hmin⟩ :=
    hcompact.exists_isMinOn hnonempty ((hfcont.mono hsphsub).norm)
  set δ : ℝ := ‖f ζ₀‖ with hδdef
  have hδ : 0 < δ := norm_pos_iff.mpr (hne ζ₀ hζ₀)
  obtain ⟨ζ₁, hζ₁, hmax⟩ :=
    hcompact.exists_isMaxOn hnonempty ((hfcont.mono hsphsub).norm)
  obtain ⟨ζ₂, hζ₂, hmax'⟩ :=
    hcompact.exists_isMaxOn hnonempty ((hderivcont.mono hsphsub).norm)
  set M : ℝ := ‖f ζ₁‖ with hMdef
  set M' : ℝ := ‖deriv f ζ₂‖ with hM'def
  have hM : 0 ≤ M := norm_nonneg _
  have hM' : 0 ≤ M' := norm_nonneg _
  set C : ℝ := 2 * (M / r + M') / δ ^ 2 with hCdef
  have hC : 0 ≤ C := by
    rw [hCdef]
    positivity
  refine ⟨min (δ / 2) (η / (C + 1)), lt_min (by positivity) (by positivity), ?_⟩
  intro h hhd hclose ζ hζ
  set ε : ℝ := min (δ / 2) (η / (C + 1)) with hεdef
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεδ : ε ≤ δ / 2 := min_le_left _ _
  have hεη : ε ≤ η / (C + 1) := min_le_right _ _
  have hζR : ζ ∈ closedBall c R := hsphsub hζ
  -- the value bounds on the circle
  have hfζ : δ ≤ ‖f ζ‖ := hmin hζ
  have hfζM : ‖f ζ‖ ≤ M := hmax hζ
  have hdfζ : ‖deriv f ζ‖ ≤ M' := hmax' hζ
  have hclζ : ‖h ζ - f ζ‖ ≤ ε := hclose ζ hζR
  have hhζ : δ / 2 ≤ ‖h ζ‖ := by
    have h1 : ‖f ζ‖ - ‖h ζ - f ζ‖ ≤ ‖h ζ‖ := by
      have := norm_sub_norm_le (f ζ) (f ζ - h ζ)
      have h2 : ‖f ζ - h ζ‖ = ‖h ζ - f ζ‖ := norm_sub_rev _ _
      have h3 : ‖f ζ‖ - ‖h ζ - f ζ‖ ≤ ‖f ζ - (f ζ - h ζ)‖ := by
        rw [← h2]
        exact norm_sub_norm_le _ _
      simpa using h3
    linarith
  have hhζ0 : h ζ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hhζ
    linarith
  -- the derivative bound, by Cauchy's estimate on a small disc
  have hballU : closedBall ζ r ⊆ U := subset_trans (closedBall_subset_of_mem_sphere htR hζ) hsub
  have hGd : ∀ w ∈ closedBall ζ r, DifferentiableAt ℂ (fun u => h u - f u) w := by
    intro w hw
    exact (hhd.differentiableAt (hU.mem_nhds (hballU hw))).sub
      (hf.differentiableAt (hU.mem_nhds (hballU hw)))
  have hdd : ‖deriv h ζ - deriv f ζ‖ ≤ ε / r := by
    have hderiv : deriv (fun u => h u - f u) ζ = deriv h ζ - deriv f ζ :=
      deriv_sub (hhd.differentiableAt (hU.mem_nhds (hballU (mem_closedBall_self hr.le))))
        (hf.differentiableAt (hU.mem_nhds (hballU (mem_closedBall_self hr.le))))
    rw [← hderiv]
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr ?_ ?_
    · refine DiffContOnCl.mk ?_ ?_
      · intro w hw
        exact (hGd w (ball_subset_closedBall hw)).differentiableWithinAt
      · rw [closure_ball ζ hr.ne']
        intro w hw
        exact (hGd w hw).continuousAt.continuousWithinAt
    · intro w hw
      exact hclose w (closedBall_subset_of_mem_sphere htR hζ (sphere_subset_closedBall hw))
  -- assembling the estimate
  have hfζ0 : f ζ ≠ 0 := hne ζ hζ
  have hkey : logDeriv h ζ - logDeriv f ζ
      = ((deriv h ζ - deriv f ζ) * f ζ + deriv f ζ * (f ζ - h ζ)) / (h ζ * f ζ) := by
    rw [logDeriv_apply, logDeriv_apply]
    field_simp
    ring
  rw [hkey, norm_div, norm_mul]
  have hnum : ‖(deriv h ζ - deriv f ζ) * f ζ + deriv f ζ * (f ζ - h ζ)‖
      ≤ (M / r + M') * ε := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖deriv h ζ - deriv f ζ‖ * ‖f ζ‖ ≤ (ε / r) * M :=
      mul_le_mul hdd hfζM (norm_nonneg _) (by positivity)
    have h2 : ‖deriv f ζ‖ * ‖f ζ - h ζ‖ ≤ M' * ε := by
      refine mul_le_mul hdfζ ?_ (norm_nonneg _) hM'
      rw [norm_sub_rev]
      exact hclζ
    have h3 : (ε / r) * M = (M / r) * ε := by ring
    linarith
  have hden : δ ^ 2 / 2 ≤ ‖h ζ‖ * ‖f ζ‖ := by
    have : (δ / 2) * δ ≤ ‖h ζ‖ * ‖f ζ‖ :=
      mul_le_mul hhζ hfζ (le_of_lt hδ) (le_trans (by positivity) hhζ)
    nlinarith
  have hdenpos : 0 < ‖h ζ‖ * ‖f ζ‖ := by nlinarith
  rw [div_le_iff₀ hdenpos]
  have hstep : (M / r + M') * ε ≤ η * (δ ^ 2 / 2) := by
    have hCε : C * ε ≤ η := by
      have h1 : ε * (C + 1) ≤ η := by
        rw [hεdef]
        calc min (δ / 2) (η / (C + 1)) * (C + 1) ≤ (η / (C + 1)) * (C + 1) :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
          _ = η := by field_simp
      nlinarith
    have h2 : (M / r + M') = C * (δ ^ 2 / 2) := by
      rw [hCdef]
      field_simp
    rw [h2]
    calc C * (δ ^ 2 / 2) * ε = (C * ε) * (δ ^ 2 / 2) := by ring
      _ ≤ η * (δ ^ 2 / 2) := mul_le_mul_of_nonneg_right hCε (by positivity)
  calc ‖(deriv h ζ - deriv f ζ) * f ζ + deriv f ζ * (f ζ - h ζ)‖ ≤ (M / r + M') * ε := hnum
    _ ≤ η * (δ ^ 2 / 2) := hstep
    _ ≤ η * (‖h ζ‖ * ‖f ζ‖) := mul_le_mul_of_nonneg_left hden hη.le

/-- **The zero count is locally constant.**  A function holomorphic on a neighbourhood of a closed
disc and nonvanishing on a smaller circle keeps both properties, and the same total zero
multiplicity inside that circle, under every sufficiently small uniform perturbation. -/
theorem exists_eps_zeroSumBall_eq {c : ℂ} {t R : ℝ} (ht : 0 < t) (htR : t < R)
    {U : Set ℂ} (hU : IsOpen U) (hsub : closedBall c R ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hne : ∀ ζ ∈ sphere c t, f ζ ≠ 0) :
    ∃ ε > 0, ∀ h : ℂ → ℂ, DifferentiableOn ℂ h U →
      (∀ z ∈ closedBall c R, ‖h z - f z‖ ≤ ε) →
        (∀ ζ ∈ sphere c t, h ζ ≠ 0) ∧ zeroSumBall h c t = zeroSumBall f c t := by
  classical
  have hcompact : IsCompact (sphere c t) := isCompact_sphere c t
  have hnonempty : (sphere c t).Nonempty := ⟨c + (t : ℂ), by
    rw [mem_sphere, dist_eq_norm]
    simp [abs_of_pos ht]⟩
  have hsphsub : sphere c t ⊆ closedBall c R := fun z hz => by
    rw [mem_closedBall, mem_sphere.mp hz]
    exact htR.le
  have hfcont : ContinuousOn f (closedBall c R) := (hf.mono hsub).continuousOn
  obtain ⟨ζ₀, hζ₀, hmin⟩ :=
    hcompact.exists_isMinOn hnonempty ((hfcont.mono hsphsub).norm)
  set δ : ℝ := ‖f ζ₀‖ with hδdef
  have hδ : 0 < δ := norm_pos_iff.mpr (hne ζ₀ hζ₀)
  obtain ⟨ε₁, hε₁, hlog⟩ :=
    exists_eps_norm_logDeriv_sub_le ht htR hU hsub hf hne (η := 1 / (2 * t)) (by positivity)
  refine ⟨min ε₁ (δ / 2), lt_min hε₁ (by positivity), ?_⟩
  intro h hhd hclose
  have hclose₁ : ∀ z ∈ closedBall c R, ‖h z - f z‖ ≤ ε₁ := fun z hz =>
    le_trans (hclose z hz) (min_le_left _ _)
  have hcloseδ : ∀ z ∈ closedBall c R, ‖h z - f z‖ ≤ δ / 2 := fun z hz =>
    le_trans (hclose z hz) (min_le_right _ _)
  -- the perturbation does not vanish on the circle either
  have hhne : ∀ ζ ∈ sphere c t, h ζ ≠ 0 := by
    intro ζ hζ h0
    have hfζ : δ ≤ ‖f ζ‖ := hmin hζ
    have hc : ‖h ζ - f ζ‖ ≤ δ / 2 := hcloseδ ζ (hsphsub hζ)
    rw [h0, zero_sub, norm_neg] at hc
    linarith
  refine ⟨hhne, ?_⟩
  -- the two logarithmic derivatives are circle integrable
  have hintf : CircleIntegrable (logDeriv f) c t := by
    refine ContinuousOn.circleIntegrable ht.le fun z hz => ?_
    have hz' : z ∈ U := hsub (hsphsub hz)
    have hrw : logDeriv f = fun w => deriv f w / f w := by
      funext w
      rw [logDeriv_apply]
    rw [hrw]
    have han : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hU
    exact (((han.deriv) z hz').div (han z hz') (hne z hz)).continuousAt.continuousWithinAt
  have hinth : CircleIntegrable (logDeriv h) c t := by
    refine ContinuousOn.circleIntegrable ht.le fun z hz => ?_
    have hz' : z ∈ U := hsub (hsphsub hz)
    have hrw : logDeriv h = fun w => deriv h w / h w := by
      funext w
      rw [logDeriv_apply]
    rw [hrw]
    have han : AnalyticOnNhd ℂ h U := hhd.analyticOnNhd hU
    exact (((han.deriv) z hz').div (han z hz') (hhne z hz)).continuousAt.continuousWithinAt
  -- the two contour integrals are within `2π` of each other
  have hbound : ‖(∮ ζ in C(c, t), logDeriv h ζ) - ∮ ζ in C(c, t), logDeriv f ζ‖
      ≤ 2 * Real.pi * t * (1 / (2 * t)) := by
    rw [← circleIntegral.integral_sub hinth hintf]
    refine circleIntegral.norm_integral_le_of_norm_le_const ht.le fun z hz => ?_
    exact hlog h hhd hclose₁ z hz
  have hnormI : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    simp
  have hlt : ‖zeroSumBall h c t - zeroSumBall f c t‖ < 1 := by
    rw [zeroSumBall, zeroSumBall, div_sub_div_same, norm_div, hnormI]
    rw [div_lt_one (by positivity)]
    have hval : 2 * Real.pi * t * (1 / (2 * t)) = Real.pi := by
      field_simp
    rw [hval] at hbound
    have : Real.pi < 2 * Real.pi := by
      have := Real.pi_pos
      linarith
    exact lt_of_le_of_lt hbound this
  -- both counts are natural numbers
  obtain ⟨Nf, hNf⟩ := exists_nat_zeroSumBall ht htR hU hsub hf hne
  obtain ⟨Nh, hNh⟩ := exists_nat_zeroSumBall ht htR hU hsub hhd hhne
  rw [hNf, hNh] at hlt ⊢
  have hcast : ((Nh : ℂ) - (Nf : ℂ)) = (((Nh : ℤ) - (Nf : ℤ) : ℤ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.norm_intCast] at hlt
  have hz : ((Nh : ℤ) - (Nf : ℤ)) = 0 := by
    have h1 : |((Nh : ℤ) - (Nf : ℤ))| < 1 := by exact_mod_cast hlt
    have h2 := abs_nonneg ((Nh : ℤ) - (Nf : ℤ))
    have h3 : |((Nh : ℤ) - (Nf : ℤ))| = 0 := by omega
    exact abs_eq_zero.mp h3
  have : (Nh : ℤ) = (Nf : ℤ) := by omega
  exact_mod_cast congrArg (fun n : ℤ => (n : ℂ)) this

end GaloisForLFunctions.HTGeometry
