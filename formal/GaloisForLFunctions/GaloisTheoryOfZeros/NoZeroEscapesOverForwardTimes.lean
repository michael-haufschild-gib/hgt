import GaloisForLFunctions.GaloisTheoryOfZeros.FarZerosAtForwardTimesAreSimple
import GaloisForLFunctions.GaloisTheoryOfZeros.AZeroContinuesAlongAPathOfTimesUntilItEscapes

/-!
# No zero escapes over forward times

Over the open half-plane of forward times `Re τ > 0` the heat cover is tame.

* **A far zero is trapped** (`exists_forall_norm_sub_le_of_zero_path`). Let `τ` move by at most
  `1/12` inside a box `{t₀ ≤ Re τ, ‖τ‖ ≤ T₀}` and let `w` be a continuous family of zeros that
  starts at a far zero. Then `w` moves by at most `1/2`. The phase `Φ` between the two
  exponentials of the model satisfies `‖e^Φ − 1‖ ≤ 1/8` at every zero within distance one, and a
  phase with `‖Φ‖ ≤ 1/2` and `‖e^Φ − 1‖ ≤ 1/8` has `‖Φ‖ ≤ 1/4`: the modulus of the phase cannot
  cross the gap `(1/4, 1/2]`, and the displacement of the zero is at most `‖Φ‖` plus the drift.
* **No escape** (`not_escapesAlong_of_re_pos`). A zero does not escape along a path of forward
  times: close to the escape parameter the zero would be far and the path nearly constant.
* **Lifting** (`exists_isZeroLift_of_re_pos`, `exists_transport_equiv`). Along a path of forward
  times that avoids the branch times every zero lifts, and the transport of zeros is a bijection
  between the fibres over the two endpoints. Along a loop it is a permutation of the fibre: the
  monodromy of the heat cover over the forward times is defined.
* **The branch times are discrete** (`finite_branchTimes_box`, `exists_ball_branchTimes_subset`).
  A box of forward times contains finitely many branch times: the multiple zeros form a closed
  discrete set, and over the box they are bounded because far zeros are simple.
-/

open Complex Filter Topology Set Metric
open RHTower

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## The trap -/

/-- A small phase whose exponential is near one is smaller still. -/
theorem norm_le_two_mul_of_norm_exp_sub_one_le {E : ℂ} {r : ℝ} (hE : ‖E‖ ≤ 1 / 2)
    (h : ‖cexp E - 1‖ ≤ r) : ‖E‖ ≤ 2 * r := by
  have h1 := Complex.norm_exp_sub_one_sub_id_le (x := E) (by linarith)
  have h2 : ‖E‖ ≤ ‖cexp E - 1‖ + ‖cexp E - 1 - E‖ := by
    have := norm_sub_le (cexp E - 1) (cexp E - 1 - E)
    rwa [sub_sub_cancel] at this
  have h3 : ‖E‖ ^ 2 ≤ 1 / 2 * ‖E‖ := by
    rw [sq]
    exact mul_le_mul_of_nonneg_right hE (norm_nonneg _)
  linarith

/-- **A far zero is trapped.** Let `γ` be a path of times in the box `{t₀ ≤ Re τ, ‖τ‖ ≤ T₀}`
that stays within `1/12` of `γ(s₁)`, and `w` a continuous family of zeros of `H_{γ(s)}` with
`‖w(s₁)‖ ≥ R`. Then `w` stays within `1/2` of `w(s₁)`. -/
theorem exists_forall_norm_sub_le_of_zero_path {t₀ : ℝ} (T₀ : ℝ) (ht₀ : 0 < t₀) :
    ∃ R : ℝ, ∀ (γ w : ℝ → ℂ) (s₁ s₂ : ℝ), ContinuousOn γ (Icc s₁ s₂) →
      ContinuousOn w (Icc s₁ s₂) →
      (∀ s ∈ Icc s₁ s₂, t₀ ≤ (γ s).re ∧ ‖γ s‖ ≤ T₀ ∧ ‖γ s - γ s₁‖ ≤ 1 / 12 ∧
        complexHeat (γ s) (w s) = 0) →
      R ≤ ‖w s₁‖ → ∀ s ∈ Icc s₁ s₂, ‖w s - w s₁‖ ≤ 1 / 2 := by
  by_cases hT : 0 ≤ T₀
  swap
  · exact ⟨0, fun γ w s₁ s₂ _ _ h _ s hs => absurd ((norm_nonneg _).trans (h s hs).2.1) hT⟩
  obtain ⟨R₁, hR₁⟩ := exists_norm_exp_zeroPhase_sub_one_le (ε := 1 / 8) T₀ ht₀ (by norm_num)
  obtain ⟨R₂, hR₂⟩ := exists_complexHeat_ne_zero_of_le_abs_im T₀ ht₀
  refine ⟨max (max R₁ R₂)
    (max (2 * Real.pi * Real.exp (2 * (1 / 2)) + (37 / 2 + 21 * T₀)) (37 + 42 * T₀)),
    fun γ w s₁ s₂ hγ hw h hR s hs => ?_⟩
  have hRa := (le_max_left _ _).trans hR
  have hRb := (le_max_right _ _).trans hR
  have hR1 := (le_max_left _ _).trans hRa
  have hR2 := (le_max_right _ _).trans hRa
  have hR3 := (le_max_left _ _).trans hRb
  have hR4 := (le_max_right _ _).trans hRb
  have hs₁ : s₁ ∈ Icc s₁ s₂ := ⟨le_rfl, hs.1.trans hs.2⟩
  obtain ⟨hτ₁t, hτ₁T, -, hH₁⟩ := h s₁ hs₁
  have him : |(w s₁).im| ≤ 12 + 21 * T₀ := by
    by_contra hcon
    exact hR₂ (γ s₁) (w s₁) hτ₁t hτ₁T (not_le.1 hcon).le hR2 hH₁
  have hΛ : 1 ≤ ‖zeroFrequency T₀ (w s₁)‖ := by
    have := le_norm_zeroFrequency (A := 1 / 2) hT hR3
    linarith
  have hdrift := norm_zeroDrift_le hT (him.trans (by linarith)) hR4
  -- the modulus of the phase along the path
  have hφc : ContinuousOn (fun x => ‖zeroPhase T₀ (γ s₁) (w s₁) (γ x) (w x)‖) (Icc s₁ s₂) := by
    unfold zeroPhase
    exact (continuousOn_const.mul ((continuousOn_const.mul (hw.sub continuousOn_const)).add
      (continuousOn_const.mul (hγ.sub continuousOn_const)))).norm
  have hdisp : ∀ x ∈ Icc s₁ s₂,
      ‖w x - w s₁‖ ≤ ‖zeroPhase T₀ (γ s₁) (w s₁) (γ x) (w x)‖ + 1 / 4 := by
    intro x hx
    have h1 := norm_sub_le_of_zeroPhase (τ₀ := γ s₁) (γ x) (w x) hΛ
    have h2 := mul_le_mul hdrift (h x hx).2.2.1 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
    linarith
  -- the phase does not enter the gap `(1/4, 1/2]`
  have hgap : ∀ x ∈ Icc s₁ s₂, ‖zeroPhase T₀ (γ s₁) (w s₁) (γ x) (w x)‖ ≤ 1 / 2 →
      ‖zeroPhase T₀ (γ s₁) (w s₁) (γ x) (w x)‖ ≤ 1 / 4 := by
    intro x hx hx2
    obtain ⟨hτt, hτT, -, hH⟩ := h x hx
    have h1 := hdisp x hx
    have h2 := hR₁ (γ s₁) (γ x) (w s₁) (w x) hτ₁t hτ₁T hτt hτT hR1 (by linarith) hH₁ hH
    have h3 := norm_le_two_mul_of_norm_exp_sub_one_le hx2 h2
    linarith
  have hall : ∀ x ∈ Icc s₁ s₂, ‖zeroPhase T₀ (γ s₁) (w s₁) (γ x) (w x)‖ ≤ 1 / 4 := by
    intro x hx
    by_contra hcon
    rw [not_le] at hcon
    have hmem : min ‖zeroPhase T₀ (γ s₁) (w s₁) (γ x) (w x)‖ (1 / 2) ∈
        Icc ‖zeroPhase T₀ (γ s₁) (w s₁) (γ s₁) (w s₁)‖
          ‖zeroPhase T₀ (γ s₁) (w s₁) (γ x) (w x)‖ := by
      rw [zeroPhase_self, norm_zero]
      exact ⟨le_min (norm_nonneg _) (by norm_num), min_le_left _ _⟩
    obtain ⟨y, hy, hyeq⟩ := intermediate_value_Icc hx.1
      (hφc.mono (Icc_subset_Icc_right hx.2)) hmem
    have hyeq' : ‖zeroPhase T₀ (γ s₁) (w s₁) (γ y) (w y)‖ =
        min ‖zeroPhase T₀ (γ s₁) (w s₁) (γ x) (w x)‖ (1 / 2) := hyeq
    have h1 := hgap y ⟨hy.1, hy.2.trans hx.2⟩ (hyeq'.le.trans (min_le_right _ _))
    rw [hyeq'] at h1
    have h2 : 1 / 4 < min ‖zeroPhase T₀ (γ s₁) (w s₁) (γ x) (w x)‖ (1 / 2) :=
      lt_min hcon (by norm_num)
    linarith
  have h1 := hdisp s hs
  have h2 := hall s hs
  linarith

/-! ## No escape -/

/-- **No zero escapes over forward times.** Along a path of times in the open right half-plane
no zero of the heat family escapes to infinity. -/
theorem not_escapesAlong_of_re_pos {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1))
    (hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < (γ s).re) (z₀ : ℂ) : ¬ EscapesAlong γ z₀ := by
  rintro ⟨b, hb, z, hzc, -, hzero, htend⟩
  -- the path lies in a box
  obtain ⟨sm, hsm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one)
    (Complex.continuous_re.comp_continuousOn hγ)
  obtain ⟨T₀, hT₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hγ
  obtain ⟨R, hR⟩ := exists_forall_norm_sub_le_of_zero_path T₀ (hpos sm hsm)
  -- near the escape parameter the path is nearly constant
  have hbI : b ∈ Icc (0 : ℝ) 1 := ⟨hb.1.le, hb.2⟩
  obtain ⟨δ, hδ, hδγ⟩ := Metric.continuousOn_iff.1 hγ b hbI (1 / 24) (by norm_num)
  have hev1 : ∀ᶠ s in 𝓝[<] b, R ≤ ‖z s‖ := htend.eventually_ge_atTop R
  have hev2 : ∀ᶠ s in 𝓝[<] b, s ∈ Ioo (max 0 (b - δ)) b :=
    Ioo_mem_nhdsLT (max_lt hb.1 (by linarith))
  obtain ⟨s₁, hs₁R, hs₁⟩ := (hev1.and hev2).exists
  have hs₁0 : 0 < s₁ := (le_max_left _ _).trans_lt hs₁.1
  have hs₁δ : b - δ < s₁ := (le_max_right _ _).trans_lt hs₁.1
  have hnear : ∀ x ∈ Ico s₁ b, ‖γ x - γ b‖ < 1 / 24 := by
    intro x hx
    have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨hs₁0.le.trans hx.1, hx.2.le.trans hb.2⟩
    have := hδγ x hxI (by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    rwa [dist_eq_norm] at this
  -- after `s₁` the zero is trapped
  have hbound : ∀ s ∈ Ico s₁ b, ‖z s‖ ≤ ‖z s₁‖ + 1 / 2 := by
    intro s hs
    have hsub : Icc s₁ s ⊆ Ico 0 b := fun x hx => ⟨hs₁0.le.trans hx.1, hx.2.trans_lt hs.2⟩
    have hsubI : Icc s₁ s ⊆ Icc 0 1 := fun x hx => ⟨(hsub hx).1, (hsub hx).2.le.trans hb.2⟩
    have h := hR γ z s₁ s (hγ.mono hsubI) (hzc.mono hsub) (fun x hx => by
      refine ⟨isMinOn_iff.1 hmin x (hsubI hx), hT₀ x (hsubI hx), ?_, hzero x (hsub hx)⟩
      have h1 := hnear x ⟨hx.1, (hsub hx).2⟩
      have h2 := hnear s₁ ⟨le_rfl, hs₁.2⟩
      have h3 := norm_sub_le (γ x - γ b) (γ s₁ - γ b)
      rw [sub_sub_sub_cancel_right] at h3
      linarith) hs₁R s ⟨hs.1, le_rfl⟩
    have := norm_sub_norm_le (z s) (z s₁)
    linarith
  -- but its modulus tends to infinity
  have hev3 : ∀ᶠ s in 𝓝[<] b, ‖z s₁‖ + 1 ≤ ‖z s‖ := htend.eventually_ge_atTop _
  have hev4 : ∀ᶠ s in 𝓝[<] b, s ∈ Ioo s₁ b := Ioo_mem_nhdsLT hs₁.2
  obtain ⟨s, hs3, hs4⟩ := (hev3.and hev4).exists
  have := hbound s ⟨hs4.1.le, hs4.2⟩
  linarith

/-! ## Lifting and transport -/

/-- **Every zero lifts along a path of forward times.** Along a path in the open right half-plane
that avoids the branch times, a zero of `H_{γ(0)}` continues to a zero of `H_{γ(1)}`. -/
theorem exists_isZeroLift_of_re_pos {γ : ℝ → ℂ} {z₀ : ℂ} (hγ : ContinuousOn γ (Icc 0 1))
    (hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < (γ s).re)
    (hsimple : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∉ branchTimes) (h0 : complexHeat (γ 0) z₀ = 0) :
    ∃ z, IsZeroLift γ 1 z ∧ z 0 = z₀ :=
  (exists_isZeroLift_or_escape hγ hsimple h0).resolve_right
    (not_escapesAlong_of_re_pos hγ hpos z₀)

/-- Every zero of `H_{γ(1)}` is the end of a lift: lift along the reversed path. -/
theorem exists_isZeroLift_ending_at {γ : ℝ → ℂ} {z₁ : ℂ} (hγ : ContinuousOn γ (Icc 0 1))
    (hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < (γ s).re)
    (hsimple : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∉ branchTimes) (h1 : complexHeat (γ 1) z₁ = 0) :
    ∃ z, IsZeroLift γ 1 z ∧ z 1 = z₁ := by
  have hmaps : MapsTo (fun s : ℝ => 1 - s) (Icc 0 1) (Icc 0 1) := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hrev : ContinuousOn (fun s : ℝ => 1 - s) (Icc 0 1) :=
    (continuous_const.sub continuous_id).continuousOn
  have hγr : ContinuousOn (fun s => γ (1 - s)) (Icc 0 1) := hγ.comp hrev hmaps
  obtain ⟨w, hw, hw0⟩ := exists_isZeroLift_of_re_pos (γ := fun s => γ (1 - s)) hγr
    (fun s hs => hpos _ (hmaps hs)) (fun s hs => hsimple _ (hmaps hs)) (by simpa using h1)
  refine ⟨fun s => w (1 - s), ⟨hw.continuousOn.comp hrev hmaps, fun s hs => ?_⟩,
    by simpa using hw0⟩
  have := hw.zero (1 - s) (hmaps hs)
  simpa using this

/-- The transport of zeros along a path: `z₀` over `γ(0)` continues to `z₁` over `γ(1)`. -/
def Transports (γ : ℝ → ℂ) (z₀ z₁ : ℂ) : Prop :=
  ∃ z, IsZeroLift γ 1 z ∧ z 0 = z₀ ∧ z 1 = z₁

/-- **Transport over forward times is a bijection of fibres.** Along a path in the open right
half-plane that avoids the branch times, the continuation of zeros is a bijection from the zeros
of `H_{γ(0)}` onto the zeros of `H_{γ(1)}`. For a loop it is a permutation of the fibre. -/
theorem exists_transport_equiv {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1))
    (hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < (γ s).re)
    (hsimple : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∉ branchTimes) :
    ∃ e : {z : ℂ // complexHeat (γ 0) z = 0} ≃ {z : ℂ // complexHeat (γ 1) z = 0},
      ∀ p, Transports γ p.1 (e p).1 := by
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hex : ∀ p : {z : ℂ // complexHeat (γ 0) z = 0},
      ∃ q : {z : ℂ // complexHeat (γ 1) z = 0}, Transports γ p.1 q.1 := fun p => by
    obtain ⟨z, hz, hz0⟩ := exists_isZeroLift_of_re_pos hγ hpos hsimple p.2
    exact ⟨⟨z 1, hz.zero 1 h11⟩, z, hz, hz0, rfl⟩
  choose f hf using hex
  refine ⟨Equiv.ofBijective f ⟨fun p p' hpp => ?_, fun q => ?_⟩, hf⟩
  · obtain ⟨z, hz, hz0, hz1⟩ := hf p
    obtain ⟨z', hz', hz0', hz1'⟩ := hf p'
    have h := hz.eq_zero_of_eq_one hγ hsimple hz' (by rw [hz1, hz1', hpp])
    exact Subtype.ext (hz0.symm.trans (h.trans hz0'))
  · obtain ⟨z, hz, hz1⟩ := exists_isZeroLift_ending_at hγ hpos hsimple q.2
    refine ⟨⟨z 0, hz.zero 0 h01⟩, ?_⟩
    obtain ⟨z', hz', hz0', hz1'⟩ := hf ⟨z 0, hz.zero 0 h01⟩
    have he := IsZeroLift.eqOn hγ hz' hz hz0' (fun s hs =>
      deriv_complexHeat_ne_zero_of_not_mem_branchTimes (hsimple s hs) (hz'.zero s hs)) h11
    exact Subtype.ext (hz1'.symm.trans (he.trans hz1))

/-! ## The branch times are discrete -/

/-- The derivative in the place is the partial derivative of the family of two variables. -/
theorem deriv_complexHeat_eq_fderiv (τ z : ℂ) :
    deriv (complexHeat τ) z =
      fderiv ℂ (fun p : ℂ × ℂ => complexHeat p.1 p.2) (τ, z) (0, 1) := by
  have hd := (analyticAt_complexHeat (τ, z)).differentiableAt.hasFDerivAt
  have hline : HasDerivAt (fun w : ℂ => (τ, w)) ((0 : ℂ), (1 : ℂ)) z :=
    (hasDerivAt_const z τ).prodMk (hasDerivAt_id z)
  exact (hd.comp_hasDerivAt z hline).deriv

theorem continuous_deriv_complexHeat :
    Continuous fun p : ℂ × ℂ => deriv (complexHeat p.1) p.2 := by
  have h : Continuous fun p : ℂ × ℂ =>
      fderiv ℂ (fun q : ℂ × ℂ => complexHeat q.1 q.2) p (0, 1) :=
    (continuous_iff_continuousAt.2 fun p =>
      (analyticAt_complexHeat p).fderiv.continuousAt).clm_apply continuous_const
  exact h.congr fun p => (deriv_complexHeat_eq_fderiv p.1 p.2).symm

/-- The multiple zeros of the family form a closed subset of `ℂ²`. -/
theorem isClosed_multipleZeros : IsClosed multipleZeros :=
  (isClosed_eq continuous_complexHeat continuous_const).and
    (isClosed_eq continuous_deriv_complexHeat continuous_const)

/-- **Finitely many multiple zeros over a box of forward times.** -/
theorem finite_multipleZeros_box {t₀ : ℝ} (T₀ : ℝ) (ht₀ : 0 < t₀) :
    {p : ℂ × ℂ | p ∈ multipleZeros ∧ t₀ ≤ p.1.re ∧ ‖p.1‖ ≤ T₀}.Finite := by
  obtain ⟨R, hR⟩ := exists_deriv_complexHeat_ne_zero T₀ ht₀
  have hsub : {p : ℂ × ℂ | p ∈ multipleZeros ∧ t₀ ≤ p.1.re ∧ ‖p.1‖ ≤ T₀} ⊆
      multipleZeros ∩ closedBall (0 : ℂ × ℂ) (max T₀ R) := by
    rintro p ⟨hp, hτt, hτT⟩
    refine ⟨hp, ?_⟩
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    refine max_le (hτT.trans (le_max_left _ _)) ?_
    by_contra hcon
    exact hR p.1 p.2 hτt hτT ((le_max_right _ _).trans (not_le.1 hcon).le) hp.1 hp.2
  have hcompact : IsCompact (multipleZeros ∩ closedBall (0 : ℂ × ℂ) (max T₀ R)) :=
    (isCompact_closedBall _ _).inter_left isClosed_multipleZeros
  have hdisc : IsDiscrete (multipleZeros ∩ closedBall (0 : ℂ × ℂ) (max T₀ R)) :=
    (isDiscrete_iff_discreteTopology.2 discreteTopology_multipleZeros).mono inter_subset_left
  exact (hcompact.finite hdisc).subset hsub

/-- **Finitely many branch times in a box of forward times.** -/
theorem finite_branchTimes_box {t₀ : ℝ} (T₀ : ℝ) (ht₀ : 0 < t₀) :
    {τ : ℂ | τ ∈ branchTimes ∧ t₀ ≤ τ.re ∧ ‖τ‖ ≤ T₀}.Finite := by
  refine ((finite_multipleZeros_box T₀ ht₀).image Prod.fst).subset ?_
  rintro τ ⟨⟨p, hp, rfl⟩, h1, h2⟩
  exact ⟨p, ⟨hp, h1, h2⟩, rfl⟩

/-- **The branch times are isolated in the forward half-plane.** Every forward time has a
neighbourhood that contains no other branch time. -/
theorem exists_ball_branchTimes_subset {τ₀ : ℂ} (hτ₀ : 0 < τ₀.re) :
    ∃ r > 0, ∀ τ ∈ ball τ₀ r, τ ∈ branchTimes → τ = τ₀ := by
  have hfin := finite_branchTimes_box (t₀ := τ₀.re / 2) (‖τ₀‖ + 1) (half_pos hτ₀)
  have hclosed : IsClosed
      ({τ : ℂ | τ ∈ branchTimes ∧ τ₀.re / 2 ≤ τ.re ∧ ‖τ‖ ≤ ‖τ₀‖ + 1} \ {τ₀}) :=
    (hfin.subset sdiff_subset).isClosed
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hclosed.isOpen_compl τ₀ (fun h => h.2 rfl)
  refine ⟨min ε (min (τ₀.re / 2) 1), lt_min hε (lt_min (half_pos hτ₀) one_pos),
    fun τ hτ hb => ?_⟩
  rw [mem_ball, dist_eq_norm] at hτ
  have h1 : ‖τ - τ₀‖ < ε := hτ.trans_le (min_le_left _ _)
  have h2 : ‖τ - τ₀‖ < τ₀.re / 2 := hτ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : ‖τ - τ₀‖ < 1 := hτ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  by_contra hne
  refine hball (by rw [mem_ball, dist_eq_norm]; exact h1) ⟨⟨hb, ?_, ?_⟩, hne⟩
  · have := (abs_le.1 (Complex.abs_re_le_norm (τ - τ₀))).1
    rw [Complex.sub_re] at this
    linarith
  · have := norm_le_insert' τ τ₀
    linarith

end

end GaloisForLFunctions.GaloisTheoryOfZeros
