import GaloisForLFunctions.RHTower.ZetaZeroAntiCrystalWindow
import GaloisForLFunctions.RHTower.XiGaplessRealizationAccumulation

/-!
# Lossless realizations of Ξ are critical at every scale

`StrictLowerPolyaClass E` means `E` is a locally uniform limit of polynomials whose roots all lie in
the open lower half-plane. Such an `E` is Hermite–Biehler, and its zeros are the resonances of the
realization `Ξ = Re E`.

**Theorem** (`eventually_exists_shallow_resonance`). Let `E` be in the class, with `Re E = Ξ` on
`ℝ` and no real zero. For every `h > 0`, eventually in `T`, `E` has a zero `z` with
`T^{1/2} − 1 ≤ Re z ≤ T³ + K` and `Im z > −h`, where `K` is a fixed constant.

So every lossless realization of Ξ without bound states has resonances within any fixed depth of the
real axis at every large scale.

**Proof.**
* RH follows from the real-rooted approximants `(p_m + p̄_m)/2`
  (`riemannHypothesis_of_strictLowerPolya_realization`).
* If a window has no shallow resonance, then for large `m` every root of `p_m` is deep or far from
  the window. Every Poisson term of the phase speed is then log-Lipschitz on the window
  (`poissonTerm_le_exp_mul`, `poissonTerm_le_exp_mul_of_far`, `poissonTerm_le_exp_mul_of_far_left`),
  and so is the phase speed of `E` (`StrictLowerPolyaClass.phaseSpeed_window`). The zeros of Ξ in
  the window are then simple and rigid (`gap_rigidity_of_phase_window`), which contradicts
  `eventually_not_rigidWindow`.
-/

open Complex Filter Topology Set Polynomial
open GaloisForLFunctions.HTGeometry (phaseSpeed poissonTerm poissonTerm_le_exp_mul
  poissonTerm_le_exp_mul_of_far poissonTerm_le_exp_mul_of_far_left neg_im_logDeriv_eval_eq_sum
  exists_phase_rep gap_rigidity_of_phase_window)

namespace RHTower

noncomputable section

/-- The strict lower Pólya class: locally uniform limits of polynomials with roots in `Im < 0`. -/
def StrictLowerPolyaClass (E : ℂ → ℂ) : Prop :=
  ∃ p : ℕ → ℂ[X], (∀ m, ∀ r ∈ (p m).roots, r.im < 0) ∧
    TendstoLocallyUniformly (fun m z => (p m).eval z) E atTop

theorem StrictLowerPolyaClass.differentiable {E : ℂ → ℂ} (hE : StrictLowerPolyaClass E) :
    Differentiable ℂ E := by
  obtain ⟨p, -, hconv⟩ := hE
  have := (tendstoLocallyUniformlyOn_univ.mpr hconv).differentiableOn
    (Eventually.of_forall fun m => (Polynomial.differentiable (p m)).differentiableOn) isOpen_univ
  exact differentiableOn_univ.mp this

/-- **RH from a strict lower Pólya realization.** -/
theorem riemannHypothesis_of_strictLowerPolya_realization {E : ℂ → ℂ}
    (hE : StrictLowerPolyaClass E) (hrep : ∀ t : ℝ, Xi t = (E t).re) : RiemannHypothesis := by
  obtain ⟨p, hroots, hconv⟩ := hE
  set P : ℕ → ℂ → ℂ := fun m z => ((p m).eval z + ((p m).map (starRingEnd ℂ)).eval z) / 2
    with hP
  set Gs : ℂ → ℂ := fun z => (E z + (starRingEnd ℂ) (E ((starRingEnd ℂ) z))) / 2 with hGs
  have hconvP : TendstoLocallyUniformly P Gs atTop := by
    have hB : TendstoLocallyUniformly (fun m z => (starRingEnd ℂ) ((p m).eval ((starRingEnd ℂ) z)))
        (fun z => (starRingEnd ℂ) (E ((starRingEnd ℂ) z))) atTop := by
      have h1 := hconv.comp (fun z => (starRingEnd ℂ) z) Complex.continuous_conj
      exact Complex.isometry_conj.uniformContinuous.comp_tendstoLocallyUniformly h1
    have h2 := uniformContinuous_half.comp_tendstoLocallyUniformly (hconv.add hB)
    have e2 : (fun m => (fun w : ℂ => w / 2) ∘ ((fun m z => (p m).eval z) +
        fun m z => (starRingEnd ℂ) ((p m).eval ((starRingEnd ℂ) z))) m) = P := by
      funext m z
      simp only [hP, Function.comp_apply, Pi.add_apply, eval_map_conj]
    rw [e2] at h2
    exact h2
  have hPd : ∀ m, Differentiable ℂ (P m) := fun m =>
    ((Polynomial.differentiable (p m)).add (Polynomial.differentiable _)).div_const 2
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
    simp only [hGs, Complex.conj_ofReal]
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
  have hsum : (p m).eval z = -((starRingEnd ℂ) ((p m).eval ((starRingEnd ℂ) z))) := by
    have : P m z = 0 := hz
    simp only [hP, eval_map_conj] at this
    linear_combination (2 : ℂ) * this
  have hnorm : ‖(p m).eval z‖ = ‖(p m).eval ((starRingEnd ℂ) z)‖ := by
    rw [hsum, norm_neg, Complex.norm_conj]
  have hr := roots_eq_zero_of_norm_eval_eq_conj (hroots m) hzim hnorm
  have hdeg : (p m).natDegree = 0 := by
    rw [(IsAlgClosed.splits (p m)).natDegree_eq_card_roots, hr, Multiset.card_zero]
  have hC := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hconst : ∀ w, P m w = ((p m).coeff 0 + (starRingEnd ℂ) ((p m).coeff 0)) / 2 := by
    intro w
    simp only [hP]
    rw [hC]
    simp [Polynomial.eval_C, Polynomial.map_C]
  apply hm0
  rw [hconst 0, ← hconst z]
  exact hz


/-- **Windowed phase rigidity with margin `m`.** Let `E` be strict lower Pólya and nonzero on `ℝ`,
with no zero in the box `[X − m, Y + m] × [−h, 0]`. Its phase speed on `ℝ` is nonnegative, and on
`[X, Y]` it is log-Lipschitz with constant `2 / min h m`. -/
theorem StrictLowerPolyaClass.phaseSpeed_window_margin {E : ℂ → ℂ} (hE : StrictLowerPolyaClass E)
    {h m X Y : ℝ} (hh : 0 < h) (hm : 0 < m) (hXY : X ≤ Y)
    (hne : ∀ t : ℝ, E ((t : ℂ) + ((0 : ℝ) : ℂ) * I) ≠ 0)
    (hfree : ∀ z : ℂ, X - m ≤ z.re → z.re ≤ Y + m → -h ≤ z.im → z.im ≤ 0 → E z ≠ 0) :
    (∀ t : ℝ, 0 ≤ phaseSpeed E 0 t) ∧ ∀ s ∈ Icc X Y, ∀ t ∈ Icc X Y,
      phaseSpeed E 0 s ≤ Real.exp (2 * |s - t| / min h m) * phaseSpeed E 0 t := by
  have hEd := hE.differentiable
  obtain ⟨p, hroots, hconv⟩ := hE
  have hU := tendstoLocallyUniformlyOn_univ.mpr hconv
  have hD := hU.deriv (Eventually.of_forall fun m =>
    (Polynomial.differentiable (p m)).differentiableOn) isOpen_univ
  have hval : ∀ z : ℂ, Tendsto (fun m => (p m).eval z) atTop (𝓝 (E z)) := fun z =>
    hU.tendsto_at (mem_univ z)
  have hder : ∀ z : ℂ, Tendsto (fun m => (p m).derivative.eval z) atTop (𝓝 (deriv E z)) := by
    intro z
    have := hD.tendsto_at (mem_univ z)
    simp only [Function.comp_def, Polynomial.deriv] at this
    exact this
  have hω : ∀ u : ℝ, Tendsto (fun m => -(((p m).derivative.eval ((u : ℂ) + ((0 : ℝ) : ℂ) * I)) /
      ((p m).eval ((u : ℂ) + ((0 : ℝ) : ℂ) * I))).im) atTop (𝓝 (phaseSpeed E 0 u)) := by
    intro u
    have := (hder ((u : ℂ) + ((0 : ℝ) : ℂ) * I)).div (hval ((u : ℂ) + ((0 : ℝ) : ℂ) * I)) (hne u)
    exact (Complex.continuous_im.tendsto _).comp this |>.neg
  have hev : ∀ u : ℝ, ∀ᶠ m in atTop, (p m).eval ((u : ℂ) + ((0 : ℝ) : ℂ) * I) ≠ 0 := fun u =>
    (hval _).eventually_ne (hne u)
  have hpos : ∀ m, ∀ r ∈ (p m).roots, ∀ u, 0 ≤ poissonTerm r.re (0 - r.im) u := by
    intro m r hr u
    have : 0 < 0 - r.im := by linarith [hroots m r hr]
    unfold poissonTerm; positivity
  -- eventually the approximants have no root in the box
  set R : Set ℂ := Icc (X - m) (Y + m) ×ℂ Icc (-h) 0 with hRdef
  have hRc : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  have hRne : R.Nonempty := ⟨(X : ℂ), Complex.mem_reProdIm.mpr
    ⟨by simp only [Complex.ofReal_re, mem_Icc]; constructor <;> linarith,
      by simp only [Complex.ofReal_im, mem_Icc]; constructor <;> linarith⟩⟩
  obtain ⟨z₀, hz₀, hmin⟩ := hRc.exists_isMinOn hRne hEd.continuous.norm.continuousOn
  have hER : ∀ z ∈ R, E z ≠ 0 := fun z hz => by
    rw [hRdef, Complex.mem_reProdIm] at hz
    exact hfree z hz.1.1 hz.1.2 hz.2.1 hz.2.2
  have hμ : 0 < ‖E z₀‖ := norm_pos_iff.mpr (hER z₀ hz₀)
  have hunif := Metric.tendstoUniformlyOn_iff.mp
    (tendstoLocallyUniformly_iff_forall_isCompact.mp hconv R hRc) _ hμ
  have hroot : ∀ᶠ m in atTop, ∀ r ∈ (p m).roots, r ∉ R := by
    filter_upwards [hunif] with m hm r hr hrR
    have h0 : (p m).eval r = 0 := (Polynomial.isRoot_of_mem_roots hr).eq_zero
    have h1 := hm r hrR
    rw [h0, dist_zero_right] at h1
    exact lt_irrefl _ (h1.trans_le (isMinOn_iff.mp hmin r hrR))
  -- termwise log-Lipschitz bounds
  have hm1 : 0 < min h m := lt_min hh hm
  have hterm : ∀ n, (∀ r ∈ (p n).roots, r ∉ R) → ∀ r ∈ (p n).roots, ∀ s ∈ Icc X Y,
      ∀ t ∈ Icc X Y, poissonTerm r.re (0 - r.im) s ≤
        Real.exp (2 * |s - t| / min h m) * poissonTerm r.re (0 - r.im) t := by
    intro n hn r hr s hs t ht
    have hb : 0 < 0 - r.im := by linarith [hroots n r hr]
    have hmono : Real.exp (2 * |s - t| / m) ≤ Real.exp (2 * |s - t| / min h m) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (by positivity) hm1 (min_le_right _ _))
    have hpt := hpos n r hr t
    by_cases hdeep : h ≤ 0 - r.im
    · exact poissonTerm_le_exp_mul hm1 ((min_le_left _ _).trans hdeep) s t
    · have hrR := hn r hr
      rw [hRdef, Complex.mem_reProdIm] at hrR
      have him : r.im ∈ Icc (-h) 0 := ⟨by linarith, (hroots n r hr).le⟩
      have hre : r.re ∉ Icc (X - m) (Y + m) := fun h1 => hrR ⟨h1, him⟩
      rw [mem_Icc, not_and_or, not_le, not_le] at hre
      rcases hre with hre | hre
      · exact (poissonTerm_le_exp_mul_of_far hb hm (by linarith [hs.1])
          (by linarith [ht.1])).trans (mul_le_mul_of_nonneg_right hmono hpt)
      · exact (poissonTerm_le_exp_mul_of_far_left hb hm (by linarith [hs.2])
          (by linarith [ht.2])).trans (mul_le_mul_of_nonneg_right hmono hpt)
  refine ⟨fun t => ?_, fun s hs t ht => ?_⟩
  · refine ge_of_tendsto (hω t) ?_
    filter_upwards [hev t] with m hm
    rw [neg_im_logDeriv_eval_eq_sum hm]
    exact Multiset.sum_nonneg fun x hx => by
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
      exact hpos m r hr t
  · refine le_of_tendsto_of_tendsto (hω s) ((hω t).const_mul _) ?_
    filter_upwards [hev s, hev t, hroot] with m hms hmt hmR
    rw [neg_im_logDeriv_eval_eq_sum hms, neg_im_logDeriv_eval_eq_sum hmt,
      ← Multiset.sum_map_mul_left]
    exact Multiset.sum_map_le_sum_map _ _ fun r hr => hterm m hmR r hr s hs t ht

/-- **Windowed phase rigidity.** Let `E` be strict lower Pólya and nonzero on `ℝ`, with no zero in
the box `[X − 1, Y + 1] × [−h, 0]`. Its phase speed on `ℝ` is nonnegative, and on `[X, Y]` it is
log-Lipschitz with constant `2 / min h 1`. -/
theorem StrictLowerPolyaClass.phaseSpeed_window {E : ℂ → ℂ} (hE : StrictLowerPolyaClass E)
    {h X Y : ℝ} (hh : 0 < h) (hXY : X ≤ Y)
    (hne : ∀ t : ℝ, E ((t : ℂ) + ((0 : ℝ) : ℂ) * I) ≠ 0)
    (hfree : ∀ z : ℂ, X - 1 ≤ z.re → z.re ≤ Y + 1 → -h ≤ z.im → z.im ≤ 0 → E z ≠ 0) :
    (∀ t : ℝ, 0 ≤ phaseSpeed E 0 t) ∧ ∀ s ∈ Icc X Y, ∀ t ∈ Icc X Y,
      phaseSpeed E 0 s ≤ Real.exp (2 * |s - t| / min h 1) * phaseSpeed E 0 t :=
  hE.phaseSpeed_window_margin hh one_pos hXY hne hfree

/-- Under RH every ordered ordinate is a real zero of `Ξ`. -/
theorem Xi_orderedPositiveOrdinate_eq_zero (hRH : RiemannHypothesis) (n : ℕ) :
    Xi (xiOrderedPositiveOrdinate n) = 0 := by
  have h1 := xi_half_add_orderedPositiveOrdinate_mul_I_eq_zero hRH n
  have h2 : XiC (xiOrderedPositiveOrdinate n) = 0 := by
    rw [XiC]; convert h1 using 2; push_cast; ring
  rw [XiC_ofReal] at h2
  exact_mod_cast h2

/-- Every positive real zero of `Ξ` is an ordered ordinate. -/
theorem exists_orderedPositiveOrdinate_eq_of_Xi_eq_zero {y : ℝ} (hy : 0 < y) (hy0 : Xi y = 0) :
    ∃ m, xiOrderedPositiveOrdinate m = y := by
  have hxi : xi (1 / 2 + (y : ℂ) * I) = 0 := by
    have h1 := XiC_ofReal y
    rw [hy0, Complex.ofReal_zero] at h1
    rw [XiC] at h1; convert h1 using 2
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
  have hqpos : 0 < (q.1 : ℂ).im := by rw [hq]; simpa using hy
  obtain ⟨m, hm⟩ := exists_xiOrderedPositiveZeroCopy_eq hqpos
  refine ⟨m, ?_⟩
  rw [← xiOrderedPositiveZeroCopy_im_eq, hm, hq]
  simp

/-- `Ξ` has no zero strictly between consecutive ordered ordinates. -/
theorem Xi_ne_zero_of_mem_Ioo_ordinates {n : ℕ} {x : ℝ}
    (hx : x ∈ Ioo (xiOrderedPositiveOrdinate n) (xiOrderedPositiveOrdinate (n + 1))) :
    Xi x ≠ 0 := by
  intro h0
  have hx0 : 0 < x := lt_of_le_of_lt (xiOrderedPositiveOrdinate_nonneg n) hx.1
  obtain ⟨m, hm⟩ := exists_orderedPositiveOrdinate_eq_of_Xi_eq_zero hx0 h0
  rcases le_or_gt m n with hmn | hmn
  · have := xiOrderedPositiveOrdinate_monotone hmn; linarith [hx.1]
  · have := xiOrderedPositiveOrdinate_monotone (show n + 1 ≤ m by omega); linarith [hx.2]

/-- **Simple zeros from positive phase speed.** Under RH, if a realization `Ξ(t) = Re G(t + ih)`
has positive phase speed at `γ_n`, then `γ_n < γ_{n+1}`. -/
theorem ordinate_lt_succ_of_phaseSpeed_pos {G : ℂ → ℂ} {h : ℝ} (hGd : Differentiable ℂ G)
    (hrep : ∀ t : ℝ, Xi t = (G ((t : ℂ) + h * I)).re) (hRH : RiemannHypothesis) {n : ℕ}
    (hne : G ((xiOrderedPositiveOrdinate n : ℂ) + h * I) ≠ 0)
    (hω : 0 < phaseSpeed G h (xiOrderedPositiveOrdinate n)) :
    xiOrderedPositiveOrdinate n < xiOrderedPositiveOrdinate (n + 1) := by
  set γ := xiOrderedPositiveOrdinate with hγ
  have hRHxi := riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH
  rcases lt_or_eq_of_le (xiOrderedPositiveOrdinate_monotone (Nat.le_succ n)) with hlt | heq
  · exact hlt
  · exfalso
    set q₁ := xiOrderedPositiveZeroCopy n with hq₁
    set q₂ := xiOrderedPositiveZeroCopy (n + 1) with hq₂
    have hq12 : q₁ ≠ q₂ := fun h12 => by
      have := xiOrderedPositiveZeroCopy_injective h12; omega
    have hpt : ∀ k, ((xiOrderedPositiveZeroCopy k).1 : ℂ) = 1 / 2 + (γ k : ℂ) * I := by
      intro k
      apply Complex.ext
      · rw [hRHxi _ (xi_xiZeroCopy_eq_zero _)]; simp
      · rw [xiOrderedPositiveZeroCopy_im_eq]; simp [hγ]
    have heqC : (q₁.1 : ℂ) = (q₂.1 : ℂ) := by
      have hγeq : γ n = γ (n + 1) := heq
      rw [hq₁, hq₂, hpt n, hpt (n + 1), hγeq]
    have hcrit := deriv_xi_eq_zero_of_copies hq12 heqC
    rw [hq₁, hpt n] at hcrit
    have hd1 := hasDerivAt_Xi_xi (γ n)
    rw [hcrit, zero_mul, Complex.zero_re] at hd1
    have hd2 := hasDerivAt_Xi_of_realization hGd hrep (γ n)
    have hzero : (G ((γ n : ℂ) + h * I)).re = 0 := by
      rw [← hrep]; exact Xi_orderedPositiveOrdinate_eq_zero hRH n
    exact re_deriv_ne_zero_of_realization hne hω hzero (hd2.unique hd1)

/-- **Bounded double gaps and occupied windows.** For some `w > 0` and `T₁ > 0`:
`γ_{k+2} ≤ γ_k + 2w` whenever `γ_k ≥ T₁`, and every `(X, X + 2w]` with `X ≥ T₁` contains an
ordinate. -/
theorem exists_ordinate_window_facts :
    ∃ w : ℝ, 0 < w ∧ ∃ T₁ : ℝ, 0 < T₁ ∧
      (∀ k, T₁ ≤ xiOrderedPositiveOrdinate k →
        xiOrderedPositiveOrdinate (k + 2) ≤ xiOrderedPositiveOrdinate k + 2 * w) ∧
      ∀ X, T₁ ≤ X → ∃ n, X < xiOrderedPositiveOrdinate n ∧
        xiOrderedPositiveOrdinate n ≤ X + 2 * w := by
  obtain ⟨w, hw, T₁, hT₁4, hwin⟩ := exists_xiZeroCount_window_ge_log
  have hmax1 := le_max_left T₁ (Real.exp 2)
  have hmax2 := le_max_right T₁ (Real.exp 2)
  have hlog2 : ∀ x, max T₁ (Real.exp 2) ≤ x → 2 ≤ Real.log (x + w) := fun x hx => by
    have h1 : Real.exp 2 ≤ x + w := by linarith
    have := Real.log_le_log (Real.exp_pos _) h1; rwa [Real.log_exp] at this
  refine ⟨w, hw, max T₁ (Real.exp 2), lt_max_of_lt_right (Real.exp_pos 2), fun k hk => ?_,
    fun X hX => ?_⟩
  · set γ := xiOrderedPositiveOrdinate
    have hwk := hwin (γ k + w) (by linarith)
    rw [show γ k + w - w = γ k by ring, show γ k + w + w = γ k + 2 * w by ring] at hwk
    have hlog := hlog2 (γ k) hk
    have hc : ((k + 1 : ℕ) : ℤ) ≤ xiZeroCount (γ k) := xiOrderedPositiveOrdinate_le_iff.mp le_rfl
    apply xiOrderedPositiveOrdinate_le_iff.mpr
    have h2 : (2 : ℤ) ≤ xiZeroCount (γ k + 2 * w) - xiZeroCount (γ k) := by
      have : (2 : ℝ) ≤ (xiZeroCount (γ k + 2 * w) : ℝ) - (xiZeroCount (γ k) : ℝ) := by linarith
      exact_mod_cast this
    push_cast at hc ⊢; omega
  · have hwX := hwin (X + w) (by linarith)
    rw [show X + w - w = X by ring, show X + w + w = X + 2 * w by ring] at hwX
    have hlog := hlog2 X hX
    have h2 : (2 : ℤ) ≤ xiZeroCount (X + 2 * w) - xiZeroCount X := by
      have : (2 : ℝ) ≤ (xiZeroCount (X + 2 * w) : ℝ) - (xiZeroCount X : ℝ) := by linarith
      exact_mod_cast this
    have h0 := xiZeroCount_nonneg X
    have hnX : ((xiZeroCount X).toNat : ℤ) = xiZeroCount X := Int.toNat_of_nonneg h0
    refine ⟨(xiZeroCount X).toNat, ?_, ?_⟩
    · by_contra hle
      push Not at hle
      have := lt_toNat_xiZeroCount_iff.mpr hle
      omega
    · apply xiOrderedPositiveOrdinate_le_iff.mpr
      push_cast; omega

/-- **A resonance-free box makes the window rigid.** Let `E` be strict lower Pólya, nonzero on
`ℝ`, with `Re E = Ξ`. If `E` has no zero `z` with `T^{1/2} − 1 ≤ Re z ≤ T³ + 2w + 1` and
`Im z ≥ −h`, then the window `[T^{1/2}, T³]` is `(min h 1 / 2)`-rigid. Here `w`, `T₁` are the
constants of `exists_ordinate_window_facts` and `T^{1/2} ≥ T₁`. -/
theorem rigidWindow_of_resonance_free {E : ℂ → ℂ} (hE : StrictLowerPolyaClass E)
    (hrep : ∀ t : ℝ, Xi t = (E t).re) (hne : ∀ t : ℝ, E t ≠ 0) {w T₁ : ℝ}
    (hgap2 : ∀ k, T₁ ≤ xiOrderedPositiveOrdinate k →
      xiOrderedPositiveOrdinate (k + 2) ≤ xiOrderedPositiveOrdinate k + 2 * w)
    (hzwin : ∀ X, T₁ ≤ X → ∃ n, X < xiOrderedPositiveOrdinate n ∧
      xiOrderedPositiveOrdinate n ≤ X + 2 * w)
    (hw : 0 < w) {h T : ℝ} (hh : 0 < h) (hXT : T₁ ≤ T ^ (1 / 2 : ℝ)) (hT1 : 1 ≤ T)
    (hcon : ∀ z : ℂ, E z = 0 → T ^ (1 / 2 : ℝ) - 1 ≤ z.re → z.re ≤ T ^ 3 + (2 * w + 1) →
      z.im < -h) :
    RigidWindow (min h 1 / 2) T := by
  have hRH := riemannHypothesis_of_strictLowerPolya_realization hE hrep
  have hEd := hE.differentiable
  have hne' : ∀ t : ℝ, E ((t : ℂ) + ((0 : ℝ) : ℂ) * I) ≠ 0 := fun t => by simpa using hne t
  have hrep' : ∀ t : ℝ, Xi t = (E ((t : ℂ) + ((0 : ℝ) : ℂ) * I)).re := fun t => by
    simpa using hrep t
  obtain ⟨A, φ, hA, hφ, hAφ⟩ := exists_phase_rep hEd hne'
  have hXi : ∀ t, Xi t = A t * Real.cos (φ t) := fun t => by rw [hrep' t, hAφ t]
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hφ x).continuousAt
  have hm1 : 0 < min h 1 := lt_min hh one_pos
  set γ := xiOrderedPositiveOrdinate with hγ
  set X := T ^ (1 / 2 : ℝ) with hX
  set Y := T ^ 3 + 2 * w with hY
  have hXT3 : X ≤ T ^ 3 :=
    (Real.rpow_le_self_of_one_le hT1 (by norm_num)).trans (le_self_pow₀ hT1 (by norm_num))
  have hXY : X < Y := by linarith
  have hfree : ∀ z : ℂ, X - 1 ≤ z.re → z.re ≤ Y + 1 → -h ≤ z.im → z.im ≤ 0 → E z ≠ 0 := by
    intro z h1 h2 h3 _ hz
    have := hcon z hz h1 (by linarith)
    linarith
  obtain ⟨hω0, hLL⟩ := hE.phaseSpeed_window hh hXY.le hne' hfree
  -- the phase speed is positive on the window
  have hωpos : ∀ t ∈ Icc X Y, 0 < phaseSpeed E 0 t := by
    intro t₀ ht₀
    by_contra hle
    push Not at hle
    have h0 : phaseSpeed E 0 t₀ = 0 := le_antisymm hle (hω0 t₀)
    have hz : ∀ s ∈ Icc X Y, phaseSpeed E 0 s = 0 := fun s hs => by
      have := hLL s hs t₀ ht₀
      rw [h0, mul_zero] at this
      exact le_antisymm this (hω0 s)
    have hconst : ∀ y ∈ Icc X Y, φ y = φ X := by
      intro y hy
      rcases eq_or_lt_of_le hy.1 with hXy | hXy
      · rw [hXy]
      obtain ⟨ξ, hξ, hm⟩ := exists_hasDerivAt_eq_slope φ (fun t => -phaseSpeed E 0 t) hXy
        hφc.continuousOn fun x _ => hφ x
      have hyX : y - X ≠ 0 := by linarith
      rw [hz ξ ⟨hξ.1.le, hξ.2.le.trans hy.2⟩, eq_div_iff hyX] at hm
      linarith
    obtain ⟨n, hn1, hn2⟩ := hzwin X hXT
    have hcos0 : Real.cos (φ X) = 0 := by
      have := Xi_orderedPositiveOrdinate_eq_zero hRH n
      rw [hXi, hconst _ ⟨hn1.le, by linarith⟩] at this
      exact (mul_eq_zero.mp this).resolve_left (hA _).ne'
    have hsub : Ioo X Y ⊆ γ '' Iio (xiZeroCount Y).toNat := by
      intro y hy
      have hy0 : 0 < y := lt_of_le_of_lt (Real.rpow_nonneg (by linarith) _) hy.1
      have hXiy : Xi y = 0 := by rw [hXi, hconst y ⟨hy.1.le, hy.2.le⟩, hcos0, mul_zero]
      obtain ⟨m, hm⟩ := exists_orderedPositiveOrdinate_eq_of_Xi_eq_zero hy0 hXiy
      exact ⟨m, lt_toNat_xiZeroCount_iff.mpr (by rw [hm]; exact hy.2.le), hm⟩
    exact Set.Ioo_infinite hXY (((Set.finite_Iio _).image γ).subset hsub)
  have hstrict : ∀ k, X ≤ γ k → γ k ≤ Y → γ k < γ (k + 1) := fun k h1 h2 =>
    ordinate_lt_succ_of_phaseSpeed_pos hEd hrep' hRH (hne' _) (hωpos _ ⟨h1, h2⟩)
  have hz : ∀ j, A (γ j) * Real.cos (φ (γ j)) = 0 := fun j => by
    rw [← hXi]; exact Xi_orderedPositiveOrdinate_eq_zero hRH j
  have hno : ∀ j, ∀ x ∈ Ioo (γ j) (γ (j + 1)), A x * Real.cos (φ x) ≠ 0 := fun j x hx => by
    rw [← hXi]; exact Xi_ne_zero_of_mem_Ioo_ordinates hx
  intro k hk1 hk2
  have hk2' : γ (k + 2) ≤ Y := by have := hgap2 k (le_trans hXT hk1); linarith
  have hk1' : γ (k + 1) ≤ Y := (xiOrderedPositiveOrdinate_monotone (Nat.le_succ _)).trans hk2'
  have hs0 := hstrict k hk1 (by linarith)
  have hs1 := hstrict (k + 1) (hk1.trans hs0.le) hk1'
  have hgr := gap_rigidity_of_phase_window hm1 hA hφ hωpos hLL hk1 hk2' hs0 hs1 (hz k)
    (hz (k + 1)) (hz (k + 2)) (hno k) (hno (k + 1))
  have he : 2 * (γ (k + 2) - γ k) / min h 1 =
      (ordinateGap k + ordinateGap (k + 1)) / (min h 1 / 2) := by
    simp only [ordinateGap, hγ]
    field_simp
    ring
  rw [he] at hgr
  have e1 : γ (k + 2) - γ (k + 1) = ordinateGap (k + 1) := by simp only [ordinateGap, hγ]
  have e2 : γ (k + 1) - γ k = ordinateGap k := by simp only [ordinateGap, hγ]
  rw [e1, e2] at hgr
  exact ⟨hs0, hgr.1, hgr.2⟩

/-- **Shallow resonances at every scale.** Let `E` be strict lower Pólya, nonzero on `ℝ`, with
`Re E = Ξ` on `ℝ`. There is `K` such that for every `h > 0`, eventually in `T`, `E` has a zero `z`
with `T^{1/2} − 1 ≤ Re z ≤ T³ + K` and `Im z ≥ −h`. -/
theorem eventually_exists_shallow_resonance {E : ℂ → ℂ} (hE : StrictLowerPolyaClass E)
    (hrep : ∀ t : ℝ, Xi t = (E t).re) (hne : ∀ t : ℝ, E t ≠ 0) :
    ∃ K : ℝ, ∀ h : ℝ, 0 < h → ∀ᶠ T : ℝ in atTop, ∃ z : ℂ, E z = 0 ∧
      T ^ (1 / 2 : ℝ) - 1 ≤ z.re ∧ z.re ≤ T ^ 3 + K ∧ -h ≤ z.im := by
  obtain ⟨w, hw, T₁, hT₁, hgap2, hzwin⟩ := exists_ordinate_window_facts
  refine ⟨2 * w + 1, fun h hh => ?_⟩
  have hm1 : 0 < min h 1 := lt_min hh one_pos
  have eX := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).eventually_ge_atTop T₁
  filter_upwards [eventually_not_rigidWindow (half_pos hm1), eX, eventually_ge_atTop (1 : ℝ)]
    with T hnot hXT hT1
  by_contra hcon
  push Not at hcon
  exact hnot (rigidWindow_of_resonance_free hE hrep hne hgap2 hzwin hw hh hXT hT1 hcon)

end

end RHTower
