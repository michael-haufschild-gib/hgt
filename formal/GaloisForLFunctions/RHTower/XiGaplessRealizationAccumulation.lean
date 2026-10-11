import GaloisForLFunctions.RHTower.XiGaplessRealizationLaw

/-!
# Resonances of lossless realizations of Ξ accumulate at the real axis

**Theorem** (`not_exists_shallow_lowerPolyaClass_realization`). For no `h > 0`, no nonzero
polynomial `Q` with all roots in `Im < 0` and no lower Pólya function `G₀` is

  `Ξ(t) = Re (Q(t) · G₀(t + ih))`   for all real `t`.

The function `E(z) = Q(z) G₀(z + ih)` is Hermite–Biehler. All its zeros lie in `Im ≤ −h` except
the finitely many zeros of `Q`. So no lossless realization of Ξ can confine its resonances to
finitely many inside a strip `−h < Im z < 0`: the resonances accumulate at the real axis.

**Proof.**
* *RH.* The polynomials `e_m = Q · p_m(· + ih)` have all roots in `Im < 0`, so
  `(e_m + ē_m)/2` is real-rooted (`roots_eq_zero_of_norm_eval_eq_conj`). Hurwitz transfer gives RH.
* *Phase.* The phase speed of `E` is that of `Q` plus that of `G₀`. Far to the right of the roots
  of `Q` both parts are log-Lipschitz (`poissonTerm_le_exp_mul_of_far`,
  `LowerPolyaClass.phaseSpeed_le_exp_mul`).
* `false_of_phase_rigid_realization` concludes.
-/

open Complex Filter Topology Set Polynomial
open GaloisForLFunctions.HTGeometry (LowerPolyaClass phaseSpeed poissonTerm)

namespace RHTower

noncomputable section

/-- The factor identity `‖z − r‖² − ‖z̄ − r‖² = −4 Im z Im r`. -/
theorem norm_sq_sub_norm_sq_conj_zero (z r : ℂ) :
    ‖z - r‖ ^ 2 - ‖(starRingEnd ℂ) z - r‖ ^ 2 = -4 * z.im * r.im := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.conj_re, Complex.sub_im, Complex.conj_im]
  ring

/-- **Strict Hermite–Biehler for polynomials with roots in `Im < 0`.** If `Im z ≠ 0` and
`‖e(z)‖ = ‖e(z̄)‖`, then `e` has no roots. -/
theorem roots_eq_zero_of_norm_eval_eq_conj {e : ℂ[X]} (hroots : ∀ r ∈ e.roots, r.im < 0)
    {z : ℂ} (hz : z.im ≠ 0) (heq : ‖e.eval z‖ = ‖e.eval ((starRingEnd ℂ) z)‖) : e.roots = 0 := by
  by_contra hne
  have hp : e ≠ 0 := fun h0 => hne (by rw [h0, Polynomial.roots_zero])
  have hlead : e.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  rw [(IsAlgClosed.splits e).eval_eq_prod_roots, (IsAlgClosed.splits e).eval_eq_prod_roots,
    norm_mul, norm_mul, norm_multiset_prod_map, norm_multiset_prod_map] at heq
  have hln : 0 < ‖e.leadingCoeff‖ := norm_pos_iff.mpr hlead
  rcases lt_or_gt_of_ne hz with hneg | hposz
  · have hlt := multiset_prod_map_lt hne (f := fun r => ‖z - r‖)
      (g := fun r => ‖(starRingEnd ℂ) z - r‖) (fun r _ => norm_nonneg _)
      (fun r hr => by
        have h1 := norm_sq_sub_norm_sq_conj_zero z r
        have h3 : ‖z - r‖ ^ 2 < ‖(starRingEnd ℂ) z - r‖ ^ 2 := by
          have := hroots r hr; nlinarith
        exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h3)
    have := mul_lt_mul_of_pos_left hlt hln
    linarith
  · have hlt := multiset_prod_map_lt hne (f := fun r => ‖(starRingEnd ℂ) z - r‖)
      (g := fun r => ‖z - r‖) (fun r _ => norm_nonneg _)
      (fun r hr => by
        have h1 := norm_sq_sub_norm_sq_conj_zero z r
        have h3 : ‖(starRingEnd ℂ) z - r‖ ^ 2 < ‖z - r‖ ^ 2 := by
          have := hroots r hr; nlinarith
        exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h3)
    have := mul_lt_mul_of_pos_left hlt hln
    linarith

/-- Multiplying a locally uniformly convergent sequence by a fixed continuous function. -/
theorem tendstoLocallyUniformly_mul_left {g : ℂ → ℂ} (hg : Continuous g) {F : ℕ → ℂ → ℂ}
    {f : ℂ → ℂ} (hF : TendstoLocallyUniformly F f atTop) :
    TendstoLocallyUniformly (fun n z => g z * F n z) (fun z => g z * f z) atTop := by
  rw [Metric.tendstoLocallyUniformly_iff] at hF ⊢
  intro ε hε x
  set M := ‖g x‖ + 1 with hM
  have hM0 : 0 < M := by positivity
  have hnear : ∀ᶠ y in 𝓝 x, ‖g y‖ < M := by
    have := (hg.norm.tendsto x).eventually (gt_mem_nhds (show ‖g x‖ < M by linarith))
    exact this
  obtain ⟨t, ht, hev⟩ := hF (ε / M) (by positivity) x
  refine ⟨t ∩ {y | ‖g y‖ < M}, inter_mem ht hnear, ?_⟩
  filter_upwards [hev] with n hn y hy
  have h1 := hn y hy.1
  rw [dist_eq_norm] at h1 ⊢
  have e : g y * f y - g y * F n y = g y * (f y - F n y) := by ring
  rw [e, norm_mul]
  calc ‖g y‖ * ‖f y - F n y‖ ≤ M * ‖f y - F n y‖ :=
        mul_le_mul_of_nonneg_right hy.2.le (norm_nonneg _)
    _ < M * (ε / M) := mul_lt_mul_of_pos_left h1 hM0
    _ = ε := by field_simp


/-- **RH from a realization with finitely many shallow resonances.** -/
theorem riemannHypothesis_of_shallow_realization {h : ℝ} (hh : 0 < h) {Q : ℂ[X]}
    (hQ : Q ≠ 0) (hQroots : ∀ r ∈ Q.roots, r.im < 0) {G₀ : ℂ → ℂ} (hG₀ : LowerPolyaClass G₀)
    (hrep : ∀ t : ℝ, Xi t = (Q.eval (t : ℂ) * G₀ ((t : ℂ) + h * I)).re) : RiemannHypothesis := by
  obtain ⟨p, hroots, hconv⟩ := hG₀
  set e : ℕ → ℂ[X] := fun m => Q * (p m).comp (X + C ((h : ℂ) * I)) with he
  have heval : ∀ m z, (e m).eval z = Q.eval z * (p m).eval (z + h * I) := by
    intro m z; simp [he, Polynomial.eval_mul, Polynomial.eval_comp]
  set E : ℂ → ℂ := fun z => Q.eval z * G₀ (z + h * I) with hE
  have hconvE : TendstoLocallyUniformly (fun m z => (e m).eval z) E atTop := by
    have h1 : TendstoLocallyUniformly (fun m z => (p m).eval (z + h * I))
        (fun z => G₀ (z + h * I)) atTop := hconv.comp (fun z => z + h * I) (by fun_prop)
    have h2 := tendstoLocallyUniformly_mul_left (Polynomial.continuous Q) h1
    have e1 : (fun m z => (e m).eval z) = fun m z => Q.eval z * (p m).eval (z + h * I) := by
      funext m z; exact heval m z
    rw [e1]; exact h2
  set P : ℕ → ℂ → ℂ := fun m z => ((e m).eval z + ((e m).map (starRingEnd ℂ)).eval z) / 2
    with hP
  set Gs : ℂ → ℂ := fun z => (E z + (starRingEnd ℂ) (E ((starRingEnd ℂ) z))) / 2 with hGs
  have hconvP : TendstoLocallyUniformly P Gs atTop := by
    have hB : TendstoLocallyUniformly (fun m z => (starRingEnd ℂ) ((e m).eval ((starRingEnd ℂ) z)))
        (fun z => (starRingEnd ℂ) (E ((starRingEnd ℂ) z))) atTop := by
      have h1 := hconvE.comp (fun z => (starRingEnd ℂ) z) Complex.continuous_conj
      exact Complex.isometry_conj.uniformContinuous.comp_tendstoLocallyUniformly h1
    have h2 := uniformContinuous_half.comp_tendstoLocallyUniformly (hconvE.add hB)
    have e2 : (fun m => (fun w : ℂ => w / 2) ∘ ((fun m z => (e m).eval z) +
        fun m z => (starRingEnd ℂ) ((e m).eval ((starRingEnd ℂ) z))) m) = P := by
      funext m z
      simp only [hP, Function.comp_apply, Pi.add_apply, eval_map_conj]
    rw [e2] at h2
    exact h2
  have hPd : ∀ m, Differentiable ℂ (P m) := fun m =>
    ((Polynomial.differentiable (e m)).add (Polynomial.differentiable _)).div_const 2
  have hGsd : Differentiable ℂ Gs := by
    have := (tendstoLocallyUniformlyOn_univ.mpr hconvP).differentiableOn
      (Eventually.of_forall fun m => (hPd m).differentiableOn) isOpen_univ
    exact differentiableOn_univ.mp this
  have hXiCd : Differentiable ℂ XiC := fun z =>
    (xi_differentiable.comp ((differentiable_const _).add
      (differentiable_id.mul (differentiable_const _)))) z
  have hGsXi : Gs = XiC := by
    refine eq_of_eq_on_real hGsd hXiCd fun t => ?_
    rw [XiC_ofReal, hrep t]
    simp only [hGs, hE, Complex.conj_ofReal]
    rw [Complex.add_conj]
    push_cast
    ring
  rw [hGsXi] at hconvP
  refine riemannHypothesis_of_XiC_locally_uniform_real_zero_approximants hconvP
    (Eventually.of_forall hPd) ?_
  have hX0 : XiC 0 ≠ 0 := by
    rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, XiC_ofReal]
    exact_mod_cast Xi_zero_pos.ne'
  have hev0 : ∀ᶠ m in atTop, P m 0 ≠ 0 :=
    ((tendstoLocallyUniformlyOn_univ.mpr hconvP).tendsto_at (mem_univ 0)).eventually_ne hX0
  filter_upwards [hev0] with m hm0
  intro z hz
  by_contra hzim
  -- `e_m ≠ 0`, and its roots lie in `Im < 0`
  have hem : e m ≠ 0 := by
    intro h0; apply hm0; simp only [hP, h0, Polynomial.map_zero, Polynomial.eval_zero]; ring
  have hpm : p m ≠ 0 := by
    intro h0; apply hem; simp [he, h0]
  have hroots_e : ∀ r ∈ (e m).roots, r.im < 0 := by
    intro r hr
    have h0 := (Polynomial.mem_roots hem).mp hr
    rw [Polynomial.IsRoot, heval] at h0
    rcases mul_eq_zero.mp h0 with hq | hp
    · exact hQroots r ((Polynomial.mem_roots hQ).mpr hq)
    · have := hroots m (r + h * I) ((Polynomial.mem_roots hpm).mpr hp)
      simp at this; linarith
  have hsum : (e m).eval z = -((starRingEnd ℂ) ((e m).eval ((starRingEnd ℂ) z))) := by
    have : P m z = 0 := hz
    simp only [hP, eval_map_conj] at this
    linear_combination (2 : ℂ) * this
  have hnorm : ‖(e m).eval z‖ = ‖(e m).eval ((starRingEnd ℂ) z)‖ := by
    rw [hsum, norm_neg, Complex.norm_conj]
  have hr := roots_eq_zero_of_norm_eval_eq_conj hroots_e hzim hnorm
  have hdeg : (e m).natDegree = 0 := by
    rw [(IsAlgClosed.splits (e m)).natDegree_eq_card_roots, hr, Multiset.card_zero]
  have hC := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hconst : ∀ w, P m w = ((e m).coeff 0 + (starRingEnd ℂ) ((e m).coeff 0)) / 2 := by
    intro w
    simp only [hP]
    rw [hC]
    simp [Polynomial.eval_C, Polynomial.map_C]
  apply hm0
  rw [hconst 0, ← hconst z]
  exact hz


/-- The phase speed of `w ↦ Q(w − ih) G₀(w)` on the line `Im w = h` splits into the phase speed of
`Q` on the real axis plus that of `G₀`. -/
theorem phaseSpeed_mul_shift_eq {h : ℝ} {Q : ℂ[X]} {G₀ : ℂ → ℂ} (hG₀d : Differentiable ℂ G₀)
    (t : ℝ) (hQt : Q.eval (t : ℂ) ≠ 0) (hGt : G₀ ((t : ℂ) + h * I) ≠ 0) :
    phaseSpeed (fun w => Q.eval (w - h * I) * G₀ w) h t =
      -((Q.derivative.eval (t : ℂ)) / Q.eval (t : ℂ)).im + phaseSpeed G₀ h t := by
  have hwt : (t : ℂ) + h * I - h * I = (t : ℂ) := by ring
  have h1 : HasDerivAt (fun w : ℂ => Q.eval (w - h * I))
      (Q.derivative.eval ((t : ℂ) + h * I - h * I)) ((t : ℂ) + h * I) :=
    (Polynomial.hasDerivAt Q _).comp_sub_const _ _
  have hd : HasDerivAt (fun w => Q.eval (w - h * I) * G₀ w)
      (Q.derivative.eval ((t : ℂ) + h * I - h * I) * G₀ ((t : ℂ) + h * I) +
        Q.eval ((t : ℂ) + h * I - h * I) * deriv G₀ ((t : ℂ) + h * I)) ((t : ℂ) + h * I) :=
    h1.mul (hG₀d ((t : ℂ) + h * I)).hasDerivAt
  unfold phaseSpeed
  rw [hd.deriv]
  simp only [hwt]
  have e : (Q.derivative.eval (t : ℂ) * G₀ ((t : ℂ) + h * I) +
      Q.eval (t : ℂ) * deriv G₀ ((t : ℂ) + h * I)) / (Q.eval (t : ℂ) * G₀ ((t : ℂ) + h * I)) =
      Q.derivative.eval (t : ℂ) / Q.eval (t : ℂ) +
        deriv G₀ ((t : ℂ) + h * I) / G₀ ((t : ℂ) + h * I) := by
    field_simp
  rw [e, Complex.add_im]
  ring

/-- The phase speed of `Q` on the real axis is a Poisson sum over its roots. -/
theorem neg_im_logDeriv_eval_real_eq_sum {Q : ℂ[X]} (t : ℝ) (hQt : Q.eval (t : ℂ) ≠ 0) :
    -((Q.derivative.eval (t : ℂ)) / Q.eval (t : ℂ)).im =
      (Q.roots.map (fun r => poissonTerm r.re (0 - r.im) t)).sum := by
  have e : ((t : ℂ) + ((0 : ℝ) : ℂ) * I) = (t : ℂ) := by simp
  have := GaloisForLFunctions.HTGeometry.neg_im_logDeriv_eval_eq_sum (p := Q) (h := 0) (t := t)
    (by rw [e]; exact hQt)
  rw [e] at this
  exact this

/-- **Resonances accumulate at the real axis.** No lossless realization `E(z) = Q(z) G₀(z + ih)` of
`Ξ = Re E` has only finitely many resonances in the strip `−h < Im z < 0`. -/
theorem not_exists_shallow_lowerPolyaClass_realization {h : ℝ} (hh : 0 < h) :
    ¬ ∃ (Q : ℂ[X]) (G₀ : ℂ → ℂ), Q ≠ 0 ∧ (∀ r ∈ Q.roots, r.im < 0) ∧ LowerPolyaClass G₀ ∧
      ∀ t : ℝ, Xi t = (Q.eval (t : ℂ) * G₀ ((t : ℂ) + h * I)).re := by
  rintro ⟨Q, G₀, hQ, hQroots, hG₀, hrep⟩
  have hG₀d := hG₀.differentiable
  have hRH := riemannHypothesis_of_shallow_realization hh hQ hQroots hG₀ hrep
  -- nonvanishing
  have hQreal : ∀ t : ℝ, Q.eval (t : ℂ) ≠ 0 := by
    intro t h0
    have := hQroots t ((Polynomial.mem_roots hQ).mpr h0)
    simp at this
  have hG₀a : G₀ ((0 : ℝ) + h * I) ≠ 0 := by
    intro h0
    have := hrep 0
    rw [h0, mul_zero, Complex.zero_re] at this
    exact Xi_zero_pos.ne' this
  have hG₀ne : ∀ t : ℝ, G₀ ((t : ℂ) + h * I) ≠ 0 := by
    intro t h0
    have := lowerPolyaClass_im_nonpos_of_eq_zero hG₀ hG₀a h0
    simp at this; linarith
  set G : ℂ → ℂ := fun w => Q.eval (w - h * I) * G₀ w with hGdef
  have hGd : Differentiable ℂ G :=
    ((Polynomial.differentiable Q).comp (differentiable_id.sub (differentiable_const _))).mul hG₀d
  have hGline : ∀ t : ℝ, G ((t : ℂ) + h * I) = Q.eval (t : ℂ) * G₀ ((t : ℂ) + h * I) := by
    intro t; simp only [hGdef]; congr 2; ring
  have hne : ∀ t : ℝ, G ((t : ℂ) + h * I) ≠ 0 := fun t => by
    rw [hGline]; exact mul_ne_zero (hQreal t) (hG₀ne t)
  have hrepG : ∀ t : ℝ, Xi t = (G ((t : ℂ) + h * I)).re := fun t => by rw [hGline]; exact hrep t
  -- the phase speed splits
  set qs : ℝ → ℝ := fun t => (Q.roots.map (fun r => poissonTerm r.re (0 - r.im) t)).sum with hqs
  have hsplit : ∀ t : ℝ, phaseSpeed G h t = qs t + phaseSpeed G₀ h t := by
    intro t
    rw [hGdef, phaseSpeed_mul_shift_eq hG₀d t (hQreal t) (hG₀ne t),
      neg_im_logDeriv_eval_real_eq_sum t (hQreal t)]
  have hLL₀ := fun s t => hG₀.phaseSpeed_le_exp_mul hh hG₀ne s t
  have hqs0 : ∀ t, 0 ≤ qs t := by
    intro t
    refine Multiset.sum_nonneg fun x hx => ?_
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
    have := hQroots r hr
    unfold poissonTerm
    have : 0 < 0 - r.im := by linarith
    positivity
  -- far to the right, the root part of the phase speed is log-Lipschitz
  set T₀ : ℝ := 1 + (Q.roots.map (fun r => |r.re|)).sum with hT₀
  have hfar : ∀ r ∈ Q.roots, r.re + 1 ≤ T₀ := by
    intro r hr
    have h1 : |r.re| ≤ (Q.roots.map (fun r => |r.re|)).sum :=
      Multiset.single_le_sum (fun x hx => by
        obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hx; exact abs_nonneg _) _
        (Multiset.mem_map_of_mem _ hr)
    have := le_abs_self r.re
    linarith
  set h' : ℝ := min 1 h with hh'def
  have hh' : 0 < h' := lt_min one_pos hh
  have hexp1 : ∀ s t : ℝ, Real.exp (2 * |s - t| / 1) ≤ Real.exp (2 * |s - t| / h') := fun s t =>
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (by positivity) hh' (min_le_left _ _))
  have hexph : ∀ s t : ℝ, Real.exp (2 * |s - t| / h) ≤ Real.exp (2 * |s - t| / h') := fun s t =>
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (by positivity) hh' (min_le_right _ _))
  have hLLq : ∀ s t, T₀ ≤ s → T₀ ≤ t → qs s ≤ Real.exp (2 * |s - t| / h') * qs t := by
    intro s t hs ht
    have h1 : qs s ≤ Real.exp (2 * |s - t| / 1) * qs t := by
      simp only [hqs]
      rw [← Multiset.sum_map_mul_left]
      refine Multiset.sum_map_le_sum_map _ _ fun r hr => ?_
      have hb : 0 < 0 - r.im := by linarith [hQroots r hr]
      exact GaloisForLFunctions.HTGeometry.poissonTerm_le_exp_mul_of_far hb one_pos
        (by linarith [hfar r hr]) (by linarith [hfar r hr])
    exact h1.trans (mul_le_mul_of_nonneg_right (hexp1 s t) (hqs0 t))
  have hLL : ∀ s t, T₀ ≤ s → T₀ ≤ t →
      phaseSpeed G h s ≤ Real.exp (2 * |s - t| / h') * phaseSpeed G h t := by
    intro s t hs ht
    rw [hsplit s, hsplit t, mul_add]
    have h1 := hLLq s t hs ht
    have h2 := (hLL₀ s t).2.trans (mul_le_mul_of_nonneg_right (hexph s t) (hLL₀ t t).1)
    linarith
  -- the phase speed is positive
  have hωpos : ∀ t, 0 < phaseSpeed G h t := by
    intro t₀
    rw [hsplit t₀]
    by_contra hle
    push Not at hle
    have hq0 : qs t₀ = 0 := le_antisymm (by linarith [(hLL₀ t₀ t₀).1]) (hqs0 t₀)
    have hg0 : phaseSpeed G₀ h t₀ = 0 := le_antisymm (by linarith [hqs0 t₀]) (hLL₀ t₀ t₀).1
    -- `Q` has no roots
    have hQr : Q.roots = 0 := by
      by_contra hne
      obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hne
      have hpos : 0 < poissonTerm r.re (0 - r.im) t₀ := by
        have := hQroots r hr
        unfold poissonTerm
        have : 0 < 0 - r.im := by linarith
        positivity
      have hle : poissonTerm r.re (0 - r.im) t₀ ≤ qs t₀ :=
        Multiset.single_le_sum (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
          have := hQroots y hy
          unfold poissonTerm
          have : 0 < 0 - y.im := by linarith
          positivity) _ (Multiset.mem_map_of_mem _ hr)
      linarith
    have hqz : ∀ t, qs t = 0 := fun t => by simp [hqs, hQr]
    have hgz : ∀ s, phaseSpeed G₀ h s = 0 := fun s => by
      have h1 := (hLL₀ s t₀).2
      rw [hg0, mul_zero] at h1
      linarith [(hLL₀ s s).1]
    obtain ⟨A, φ, hA, hφ, hAφ⟩ := GaloisForLFunctions.HTGeometry.exists_phase_rep hGd hne
    have hconst : ∀ x y : ℝ, φ x = φ y := by
      refine is_const_of_deriv_eq_zero (fun x => (hφ x).differentiableAt) fun x => ?_
      rw [(hφ x).deriv, hsplit x, hqz x, hgz x, add_zero, neg_zero]
    obtain ⟨t, -, ht⟩ := exists_Xi_zero_gt 0
    have h0 := Xi_zero_pos
    rw [hrepG, hAφ] at ht h0
    rw [hconst t 0] at ht
    have hc : Real.cos (φ 0) = 0 := (mul_eq_zero.mp ht).resolve_left (hA t).ne'
    rw [hc, mul_zero] at h0
    exact lt_irrefl _ h0
  exact false_of_phase_rigid_realization hh' hGd hne hrepG hRH hωpos hLL

end

end RHTower
