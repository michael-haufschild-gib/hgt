import GaloisForLFunctions.RHTower.ModularLambdaHeightBound
import GaloisForLFunctions.Bottcher.ModularLambdaProperness

/-!
# The modular `λ` separates `Γ(2)`-orbits

For `η₁, η₂ ∈ ℍ`, `λ(η₁) = λ(η₂)` forces `η₁ ∈ Γ(2)·η₂`
(`exists_gamma2_smul_eq_of_modularLambda_eq`). Equivalently, the descended covering
`λ̄ : Γ(2)\ℍ → ℂ∖{0,1}` is injective (`lambdaBar_injective`): it has degree one. Consequences:

* `λ` is injective on the open `Γ(2)` fundamental domain `⋃_p h_p⁻¹ • 𝒟ᵒ`
  (`injOn_modularLambda_gamma2Fdo`), where `h_p` runs over coset representatives;
* the kernel of the anharmonic representation `SL(2,ℤ) → S₃` is exactly `Γ(2)`
  (`anharmHom_ker_eq_gamma2`).

The proof has four steps.

* A covering map over a preconnected base is injective once one fibre is a subsingleton, because
  every fibre over an evenly covered neighbourhood is homeomorphic to the fibre over its centre.
* Reduction mod 2 shows that every `g ∈ SL(2,ℤ)` lies in `Γ(2)·r` for one of the six words
  `r ∈ {1, S, T, ST, TS, STS}`.
* Near the cusp, `λ(τ) = e^{iπτ} u(τ)` with `|u − 16| < 8`. Cauchy's estimate gives `|u'/u| ≤ 1 < π`,
  so `iπτ + log u(τ)` is injective modulo `2πiℤ`, and `λ(τ₁) = λ(τ₂)` forces `τ₁ − τ₂ ∈ 2ℤ`.
* The height bound `|log |λ(g•z)|| ≤ π Im z + C` on `𝒟` puts every preimage of a tiny value high
  in the cusp, and the six anharmonic values of a small `λ` force the word `r` to be `1` or `T`.
-/

open Filter Topology Set UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups Pointwise

namespace GaloisForLFunctions.RHTower.ModularLambdaWinding

open Bottcher ModularGroup

noncomputable section

/-- A covering map over a preconnected base is injective as soon as one fibre is a subsingleton:
along an evenly covered neighbourhood every fibre is homeomorphic to the fibre over the centre, so
"the fibre is a subsingleton" is a locally constant proposition. -/
theorem injective_of_isCoveringMap_of_subsingleton_fiber {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [PreconnectedSpace X] {f : E → X} (hf : IsCoveringMap f) {x₀ : X}
    (h₀ : (f ⁻¹' {x₀}).Subsingleton) : Function.Injective f := by
  have hloc : IsLocallyConstant (fun x : X => (f ⁻¹' {x}).Subsingleton) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    obtain ⟨hd, U, hxU, hU, hfU, H, hH⟩ := hf x
    refine ⟨U, hU, hxU, fun x' hx' => ?_⟩
    have hcov : IsEvenlyCovered f x' (f ⁻¹' {x}) := ⟨hd, U, hx', hU, hfU, H, hH⟩
    rw [← Set.subsingleton_coe, ← Set.subsingleton_coe]
    exact propext hcov.fiberHomeomorph.toEquiv.subsingleton_congr.symm
  intro a b hab
  have h : (f ⁻¹' {x₀}).Subsingleton = (f ⁻¹' {f a}).Subsingleton :=
    hloc.apply_eq_of_preconnectedSpace x₀ (f a)
  exact (h ▸ h₀) (show a ∈ f ⁻¹' {f a} from rfl) (show b ∈ f ⁻¹' {f a} from hab.symm)

/-- `T² ∈ Γ(2)`. -/
theorem T_sq_mem_gamma2 : T ^ 2 ∈ Gamma 2 := by
  rw [Gamma_mem]; simp [sq, ModularGroup.T, Matrix.mul_apply, Fin.sum_univ_two]; rfl

/-- **Coset words mod 2.** Every `g ∈ SL(2,ℤ)` lies in `Γ(2)·r` for one of the six words
`1, S, T, ST, TS, STS`: they reduce to the six elements of `SL(2, ℤ/2)`. -/
theorem exists_word_mul_mem_gamma2 (g : SL(2, ℤ)) :
    ∃ r ∈ ({1, S, T, S * T, T * S, S * T * S} : Set SL(2, ℤ)), g * r⁻¹ ∈ Gamma 2 := by
  set φ : SL(2, ℤ) →* SL(2, ZMod 2) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 2))
    with hφ
  have key : ∀ x : SL(2, ZMod 2), x = φ 1 ∨ x = φ S ∨ x = φ T ∨ x = φ (S * T) ∨ x = φ (T * S) ∨
      x = φ (S * T * S) := by
    rw [hφ]; decide
  have hmem : ∀ r, g * r⁻¹ ∈ Gamma 2 ↔ φ g = φ r := fun r => by
    show g * r⁻¹ ∈ φ.ker ↔ _
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
  rcases key (φ g) with h | h | h | h | h | h
  · exact ⟨1, by simp, (hmem 1).2 h⟩
  · exact ⟨S, by simp, (hmem S).2 h⟩
  · exact ⟨T, by simp, (hmem T).2 h⟩
  · exact ⟨S * T, by simp, (hmem _).2 h⟩
  · exact ⟨T * S, by simp, (hmem _).2 h⟩
  · exact ⟨S * T * S, by simp, (hmem _).2 h⟩

/-- `λ(Sτ) = 1 − λ(τ)`. -/
theorem modularLambda_coe_S_smul (τ : ℍ) :
    modularLambda ((S • τ : ℍ) : ℂ) = 1 - modularLambda τ :=
  congrArg Subtype.val (lambdaPunct_smul_S τ)

/-- `λ(Tτ) = λ(τ)/(λ(τ) − 1)`. -/
theorem modularLambda_coe_T_smul (τ : ℍ) :
    modularLambda ((T • τ : ℍ) : ℂ) = modularLambda τ / (modularLambda τ - 1) :=
  congrArg Subtype.val (lambdaPunct_smul_T τ)

/-- **Small values pin the word.** If `|λ(z)| ≤ 1/2` and `|λ(r z)| < 1/2` for one of the six words,
then `r ∈ {1, T}`: the other four anharmonic images `1 − w`, `1/(1 − w)`, `(w − 1)/w`, `1/w` of a
`w` with `|w| ≤ 1/2` have modulus at least `1/2`. -/
theorem word_eq_one_or_T_of_norm_lt {z : ℍ} (hz : ‖modularLambda z‖ ≤ 1 / 2) {r : SL(2, ℤ)}
    (hr : r ∈ ({1, S, T, S * T, T * S, S * T * S} : Set SL(2, ℤ)))
    (hrz : ‖modularLambda ((r • z : ℍ) : ℂ)‖ < 1 / 2) : r = 1 ∨ r = T := by
  set w := modularLambda z with hw
  have hw0 : w ≠ 0 := modularLambda_ne_zero_of_im_pos z.im_pos
  have hw1 : w - 1 ≠ 0 := sub_ne_zero.2 (modularLambda_ne_one z.im_pos)
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have h1w : 1 / 2 ≤ ‖1 - w‖ := by
    have := norm_sub_norm_le (1 : ℂ) w; rw [norm_one] at this; linarith
  have hw1le : ‖w - 1‖ ≤ 3 / 2 := by
    have := norm_sub_le w 1; rw [norm_one] at this; linarith
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · rw [modularLambda_coe_S_smul] at hrz; linarith
  · exact Or.inr rfl
  · exfalso
    rw [mul_smul, modularLambda_coe_S_smul, modularLambda_coe_T_smul, ← hw,
      show 1 - w / (w - 1) = -1 / (w - 1) by field_simp; ring, norm_div, norm_neg, norm_one] at hrz
    rw [div_lt_iff₀ (norm_pos_iff.2 hw1)] at hrz
    linarith
  · exfalso
    rw [mul_smul, modularLambda_coe_T_smul, modularLambda_coe_S_smul, ← hw,
      show (1 - w) / (1 - w - 1) = (1 - w) / (-w) by ring, norm_div, norm_neg] at hrz
    rw [div_lt_iff₀ hwpos] at hrz
    nlinarith
  · exfalso
    rw [mul_smul, mul_smul, modularLambda_coe_S_smul, modularLambda_coe_T_smul,
      modularLambda_coe_S_smul, ← hw,
      show 1 - (1 - w) / (1 - w - 1) = 1 / w by
        rw [show (1 : ℂ) - w - 1 = -w by ring]; field_simp; ring, norm_div, norm_one] at hrz
    rw [div_lt_iff₀ hwpos] at hrz
    linarith

/-- `T^{2k} ∈ Γ(2)`. -/
theorem T_zpow_two_mul_mem_gamma2 (k : ℤ) : T ^ (2 * k) ∈ Gamma 2 := by
  rw [zpow_mul]; exact zpow_mem (by exact_mod_cast T_sq_mem_gamma2) k

/-- `λ(τ + 2k) = λ(τ)` for every integer `k`. -/
theorem modularLambda_add_two_mul_int {τ : ℂ} (hτ : 0 < τ.im) (k : ℤ) :
    modularLambda (τ + 2 * k) = modularLambda τ := by
  have h := modularLambda_smul (T_zpow_two_mul_mem_gamma2 k) ⟨τ, hτ⟩
  rw [ModularGroup.coe_T_zpow_smul_eq] at h
  push_cast at h
  exact h

/-- **Cusp injectivity.** High in the cusp, `λ(τ₁) = λ(τ₂)` forces `τ₁ − τ₂ ∈ 2ℤ`. Writing
`λ(τ) = e^{iπτ} u(τ)` with `|u − 16| < 8`, Cauchy's estimate on unit discs gives `|u'| ≤ 8 < |u|`,
so `G = log u` is `1`-Lipschitz on the half-plane, `2`-periodic, and
`iπ(τ₁ − τ₂ − 2k) = G(τ₂ + 2k) − G(τ₁)` has only the trivial solution since `π > 1`. -/
theorem exists_cusp_injective : ∃ Y : ℝ, 1 ≤ Y ∧ ∀ τ₁ τ₂ : ℂ, Y ≤ τ₁.im → Y ≤ τ₂.im →
    modularLambda τ₁ = modularLambda τ₂ → ∃ k : ℤ, τ₁ = τ₂ + 2 * k := by
  obtain ⟨Y₀, hY₀, hb⟩ := exists_cusp_bounds
  set u : ℂ → ℂ := fun z => modularLambda z * Complex.exp (-(Real.pi * Complex.I * z)) with hu
  have hu_diff : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ u z := fun z hz =>
    (differentiableAt_modularLambda_of_im_pos hz).mul (by fun_prop)
  have hu_per : ∀ z : ℂ, 0 < z.im → ∀ k : ℤ, u (z + 2 * k) = u z := fun z hz k => by
    simp only [hu]
    rw [modularLambda_add_two_mul_int hz,
      show -(Real.pi * Complex.I * (z + 2 * k)) =
        -(Real.pi * Complex.I * z) + (-k : ℤ) * (2 * Real.pi * Complex.I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hlow : ∀ z : ℂ, Y₀ ≤ z.im → 8 < ‖u z‖ := fun z hz => by
    have h := (hb z hz).1
    have := norm_sub_norm_le (16 : ℂ) (u z)
    rw [norm_sub_rev] at this
    norm_num at this
    linarith
  have hslit : ∀ z : ℂ, Y₀ ≤ z.im → u z ∈ Complex.slitPlane := fun z hz => by
    have h := (hb z hz).1
    have hre : |(u z - 16).re| ≤ ‖u z - 16‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re] at hre
    refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
    norm_num at hre
    linarith [(abs_le.1 hre).1]
  set Y := Y₀ + 1 with hY
  have hderiv : ∀ z : ℂ, Y ≤ z.im → ‖deriv u z‖ ≤ 8 := fun z hz => by
    have hcl : ∀ w ∈ Metric.closedBall z 1, Y₀ ≤ w.im := fun w hw => by
      have h1 : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
      rw [Complex.sub_im] at h1
      have h2 : ‖w - z‖ ≤ 1 := by rwa [Metric.mem_closedBall, dist_eq_norm] at hw
      linarith [(abs_le.1 h1).1]
    have hD : DiffContOnCl ℂ (fun w => u w - 16) (Metric.ball z 1) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball z one_ne_zero]
      intro w hw
      exact ((hu_diff w (by linarith [hcl w hw])).sub_const 16).differentiableWithinAt
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (C := 8) one_pos hD
      (fun w hw => (hb w (hcl w (Metric.sphere_subset_closedBall hw))).1.le)
    rwa [deriv_sub_const, div_one] at h
  set G : ℂ → ℂ := fun z => Complex.log (u z) with hG
  have hGd : ∀ z ∈ {z : ℂ | Y ≤ z.im}, HasDerivAt G (deriv u z / u z) z := fun z hz =>
    ((hu_diff z (by simp only [mem_setOf_eq] at hz; linarith)).hasDerivAt).clog
      (hslit z (by simp only [mem_setOf_eq] at hz; linarith))
  have hGlip : ∀ z ∈ {z : ℂ | Y ≤ z.im}, ‖deriv G z‖ ≤ 1 := fun z hz => by
    rw [(hGd z hz).deriv, norm_div]
    have hz' : Y ≤ z.im := hz
    exact div_le_one_of_le₀ ((hderiv z hz').trans (hlow z (by linarith)).le) (norm_nonneg _)
  refine ⟨Y, by linarith, fun τ₁ τ₂ h₁ h₂ heq => ?_⟩
  have hexp : ∀ τ : ℂ, Y ≤ τ.im →
      Complex.exp (Real.pi * Complex.I * τ + G τ) = modularLambda τ := fun τ hτ => by
    rw [Complex.exp_add, Complex.exp_log (fun h0 => by
      have := hlow τ (by linarith); rw [h0, norm_zero] at this; linarith)]
    simp only [hu]
    rw [mul_left_comm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 ((hexp τ₁ h₁).trans (heq.trans (hexp τ₂ h₂).symm))
  refine ⟨n, ?_⟩
  set τ₃ := τ₂ + 2 * (n : ℂ) with hτ₃
  have h₃ : Y ≤ τ₃.im := by simpa [hτ₃] using h₂
  have hG3 : G τ₃ = G τ₂ := by
    show Complex.log (u (τ₂ + 2 * (n : ℂ))) = Complex.log (u τ₂)
    rw [hu_per τ₂ (by linarith) n]
  have key : (Real.pi * Complex.I) * (τ₁ - τ₃) = G τ₃ - G τ₁ := by
    rw [hG3, hτ₃]; linear_combination hn
  have hL := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hGd z hz).differentiableAt) hGlip (convex_halfSpace_im_ge Y) h₁ h₃
  rw [← key, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, norm_sub_rev τ₃ τ₁, one_mul] at hL
  have hz : ‖τ₁ - τ₃‖ = 0 := by
    have := Real.pi_gt_three
    nlinarith [norm_nonneg (τ₁ - τ₃)]
  exact sub_eq_zero.1 (norm_eq_zero.1 hz)

/-- **A one-orbit fibre.** There is a point `τ₀` high on the imaginary axis whose `λ`-fibre is a
single `Γ(2)`-orbit. A preimage `η` of the tiny value `λ(τ₀)` is `g⁻¹ z` with `z ∈ 𝒟`; the height
bound forces `z` high in the cusp, the anharmonic values force `η ∈ Γ(2)·{z, Tz}`, and cusp
injectivity identifies `z` or `Tz` with `τ₀` modulo `2ℤ`. -/
theorem exists_point_fiber_orbit : ∃ τ₀ : ℍ, ∀ η : ℍ, modularLambda η = modularLambda τ₀ →
    ∃ γ ∈ Gamma 2, γ • τ₀ = η := by
  obtain ⟨Y₁, hY₁, hinj⟩ := exists_cusp_injective
  obtain ⟨Y₀, hY₀, hb⟩ := exists_cusp_bounds
  obtain ⟨C, hC⟩ := exists_abs_log_norm_modularLambda_smul_le
  set Y := max Y₁ Y₀ with hY
  set ε := min (1 / 2) (Real.exp (-(Real.pi * Y + C))) with hε
  have hεpos : 0 < ε := lt_min (by norm_num) (Real.exp_pos _)
  have hev := tendsto_modularLambda_atImInfty.eventually (Metric.ball_mem_nhds 0 hεpos)
  rw [Filter.eventually_comap, Filter.eventually_atTop] at hev
  obtain ⟨A, hA⟩ := hev
  set t := max A Y + 1 with ht
  have htY : Y < t := by rw [ht]; linarith [le_max_right A Y]
  have hY1 : 1 ≤ Y := le_trans hY₁ (le_max_left _ _)
  have htpos : 0 < t := by linarith
  refine ⟨⟨Complex.I * t, by simpa using htpos⟩, fun η hη => ?_⟩
  set τ₀ : ℍ := ⟨Complex.I * t, by simpa using htpos⟩ with hτ₀
  have hτ₀im : (τ₀ : ℂ).im = t := by simp [hτ₀]
  set w := modularLambda (τ₀ : ℂ) with hw
  have hwε : ‖w‖ < ε := by
    have := hA t (by rw [ht]; linarith [le_max_left A Y]) (τ₀ : ℂ) hτ₀im
    simpa [Metric.mem_ball, dist_zero_right] using this
  have hw0 : 0 < ‖w‖ := norm_pos_iff.2 (modularLambda_ne_zero_of_im_pos (by rw [hτ₀im]; exact htpos))
  have hlogw : Real.log ‖w‖ < -(Real.pi * Y + C) := by
    rw [← Real.log_exp (-(Real.pi * Y + C))]
    exact Real.log_lt_log hw0 (hwε.trans_le (min_le_right _ _))
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd η
  set z := g • η with hz
  have hηz : g⁻¹ • z = η := inv_smul_smul g η
  have hzY : Y < z.im := by
    have h := hC z hg g⁻¹
    rw [hηz, hη] at h
    have := neg_abs_le (Real.log ‖w‖)
    have hπ := Real.pi_pos
    by_contra hcon
    push Not at hcon
    nlinarith
  have hzY₀ : Y₀ ≤ (z : ℂ).im := by
    rw [UpperHalfPlane.coe_im]; linarith [le_max_right Y₁ Y₀]
  obtain ⟨r, hr, hγ⟩ := exists_word_mul_mem_gamma2 g⁻¹
  have hηr : (g⁻¹ * r⁻¹) • (r • z) = η := by rw [← mul_smul, inv_mul_cancel_right, hηz]
  have hlr : modularLambda ((r • z : ℍ) : ℂ) = w := by
    rw [← modularLambda_smul hγ (r • z), hηr, hη]
  have hrz : ‖modularLambda ((r • z : ℍ) : ℂ)‖ < 1 / 2 := by
    rw [hlr]; exact hwε.trans_le (min_le_left _ _)
  have hrim : (r • z).im = z.im := by
    rcases word_eq_one_or_T_of_norm_lt (hb _ hzY₀).2 hr hrz with rfl | rfl
    · rw [one_smul]
    · exact ModularGroup.im_T_smul z
  obtain ⟨k, hk⟩ := hinj ((r • z : ℍ) : ℂ) (τ₀ : ℂ)
    (by rw [UpperHalfPlane.coe_im, hrim]; linarith [le_max_left Y₁ Y₀])
    (by rw [hτ₀im]; linarith [le_max_left Y₁ Y₀]) (hlr.trans hw)
  have hTk : T ^ (2 * k) • τ₀ = r • z := by
    apply UpperHalfPlane.ext
    rw [ModularGroup.coe_T_zpow_smul_eq, hk]; push_cast; ring
  refine ⟨(g⁻¹ * r⁻¹) * T ^ (2 * k), mul_mem hγ (T_zpow_two_mul_mem_gamma2 k), ?_⟩
  rw [mul_smul, hTk, hηr]

/-- **Degree one.** The descended covering `λ̄ : Γ(2)\ℍ → ℂ∖{0,1}` is injective. -/
theorem lambdaBar_injective : Function.Injective lambdaBar := by
  haveI : ConnectedSpace Punctured := isConnected_iff_connectedSpace.1 isConnected_compl_zero_one
  obtain ⟨τ₀, hτ₀⟩ := exists_point_fiber_orbit
  have hfib : ∀ a ∈ lambdaBar ⁻¹' {lambdaPunct τ₀},
      a = Quotient.mk (MulAction.orbitRel (Gamma 2 ⧸ projKer) ℍ) τ₀ := by
    intro a ha
    induction a using Quotient.inductionOn with
    | h η =>
      have hη : modularLambda η = modularLambda τ₀ := congrArg Subtype.val ha
      obtain ⟨γ, hγ, hγη⟩ := hτ₀ η hη
      refine Quotient.sound ((MulAction.orbitRel_apply).2 ⟨(QuotientGroup.mk ⟨γ, hγ⟩ :
        Gamma 2 ⧸ projKer), ?_⟩)
      show (QuotientGroup.mk ⟨γ, hγ⟩ : Gamma 2 ⧸ projKer) • τ₀ = η
      rw [mk_smul]; exact hγη
  exact injective_of_isCoveringMap_of_subsingleton_fiber isCoveringMap_lambdaBar'
    (x₀ := lambdaPunct τ₀) (fun a ha b hb => (hfib a ha).trans (hfib b hb).symm)

/-- **`λ` separates `Γ(2)`-orbits.** `λ(η₁) = λ(η₂)` iff `η₁ = γ η₂` for some `γ ∈ Γ(2)`. -/
theorem exists_gamma2_smul_eq_of_modularLambda_eq {η₁ η₂ : ℍ}
    (h : modularLambda η₁ = modularLambda η₂) : ∃ γ ∈ Gamma 2, γ • η₂ = η₁ := by
  have hq := lambdaBar_injective (a₁ := Quotient.mk (MulAction.orbitRel (Gamma 2 ⧸ projKer) ℍ) η₁)
    (a₂ := Quotient.mk _ η₂) (Subtype.ext h)
  obtain ⟨q, hq⟩ := (MulAction.orbitRel_apply).1 (Quotient.exact hq)
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨γ, γ.2, ?_⟩
  simp only at hq
  rw [mk_smul] at hq
  exact hq

/-- The open `Γ(2)` fundamental domain: the union over the cosets `p ∈ SL(2,ℤ)/Γ(2)` of the
translates `h_p⁻¹ • 𝒟ᵒ` of the open modular fundamental domain, `h_p = Quotient.out p`. -/
def gamma2Fdo : Set ℍ := ⋃ p : SL(2, ℤ) ⧸ Gamma 2, (Quotient.out p)⁻¹ • ModularGroup.fdo

/-- **`λ` is injective on the open `Γ(2)` fundamental domain.** Two points `h₁⁻¹ z₁`, `h₂⁻¹ z₂`
(`zᵢ ∈ 𝒟ᵒ`) with equal `λ` differ by `γ ∈ Γ(2)`; then `h₁ γ h₂⁻¹` maps `z₂ ∈ 𝒟ᵒ` into `𝒟ᵒ`, so it
is `±1`. Since `−1 ∈ Γ(2)` the cosets agree, `h₁ = h₂`, and `z₁ = z₂`. -/
theorem injOn_modularLambda_gamma2Fdo :
    InjOn (fun η : ℍ => modularLambda (η : ℂ)) gamma2Fdo := by
  intro x hx y hy hxy
  simp only [gamma2Fdo, mem_iUnion, Set.mem_smul_set] at hx hy
  obtain ⟨p₁, z₁, hz₁, rfl⟩ := hx
  obtain ⟨p₂, z₂, hz₂, rfl⟩ := hy
  obtain ⟨γ, hγ, hγeq⟩ := exists_gamma2_smul_eq_of_modularLambda_eq hxy
  set h₁ := Quotient.out p₁
  set h₂ := Quotient.out p₂
  have hz : (h₁ * γ * h₂⁻¹) • z₂ = z₁ := by
    rw [mul_smul, mul_smul, hγeq, smul_inv_smul]
  have hpm := ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo hz₂ (hz ▸ hz₁)
  have hcos : h₁⁻¹ * h₂ ∈ Gamma 2 := by
    rcases hpm with h | h
    · rw [show h₁⁻¹ * h₂ = γ by rw [mul_inv_eq_one] at h; rw [← h]; group]
      exact hγ
    · rw [show h₁⁻¹ * h₂ = -1 * γ by
        rw [mul_inv_eq_iff_eq_mul] at h
        rw [show h₂ = -(h₁ * γ) by rw [h]; simp]
        simp [mul_neg]]
      exact mul_mem negI_mem_gamma2 hγ
  have hp : p₁ = p₂ := by
    rw [← QuotientGroup.out_eq' p₁, ← QuotientGroup.out_eq' p₂]
    exact QuotientGroup.eq.2 hcos
  subst hp
  have hzz : z₁ = z₂ := by
    rw [← hz]
    rcases hpm with h | h
    · rw [h, one_smul]
    · rw [h, ModularGroup.SL_neg_smul, one_smul]
  rw [hzz]

/-- `λ` is injective on the image of the open `Γ(2)` fundamental domain in `ℂ`. -/
theorem injOn_modularLambda_coe_gamma2Fdo :
    InjOn modularLambda (UpperHalfPlane.coe '' gamma2Fdo) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
  rw [injOn_modularLambda_gamma2Fdo hx hy hxy]

/-- **The anharmonic representation has kernel exactly `Γ(2)`**: `SL(2,ℤ)/Γ(2) ≅ S₃` acts
faithfully on the values of `λ`. -/
theorem anharmHom_ker_eq_gamma2 : anharmHom.ker = Gamma 2 := by
  refine le_antisymm (fun g hg => ?_) gamma2_le_ker_anharmHom
  have hfix : ∀ τ : ℍ, modularLambda ((g • τ : ℍ) : ℂ) = modularLambda τ := fun τ => by
    have h := anharmElem_eq g τ
    rw [show anharmElem g = 1 from MonoidHom.mem_ker.1 hg] at h
    exact congrArg Subtype.val h
  obtain ⟨r, hr, hγ⟩ := exists_word_mul_mem_gamma2 g
  have hev := tendsto_modularLambda_atImInfty.eventually
    (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
  rw [Filter.eventually_comap, Filter.eventually_atTop] at hev
  obtain ⟨A, hA⟩ := hev
  set t := max A 1 with ht
  have htpos : 0 < t := lt_of_lt_of_le one_pos (le_max_right _ _)
  set z : ℍ := ⟨Complex.I * t, by simpa using htpos⟩ with hzdef
  have hsmall : ‖modularLambda z‖ < 1 / 2 := by
    have := hA t (le_max_left _ _) (z : ℂ) (by simp [hzdef])
    simpa [Metric.mem_ball, dist_zero_right] using this
  have hrz : modularLambda ((r • z : ℍ) : ℂ) = modularLambda z := by
    rw [← hfix z, show g = g * r⁻¹ * r by group, mul_smul, modularLambda_smul hγ]
  rcases word_eq_one_or_T_of_norm_lt hsmall.le hr (by rw [hrz]; exact hsmall) with rfl | rfl
  · simpa using hγ
  · exfalso
    rw [modularLambda_coe_T_smul] at hrz
    have hw1 : modularLambda z - 1 ≠ 0 := sub_ne_zero.2 (modularLambda_ne_one z.im_pos)
    have hw0 : modularLambda z ≠ 0 := modularLambda_ne_zero_of_im_pos z.im_pos
    rw [div_eq_iff hw1] at hrz
    have h2 : modularLambda z = 2 := by
      have := mul_left_cancel₀ hw0 (show modularLambda z * 1 = modularLambda z * (modularLambda z - 1)
        by rw [mul_one]; exact hrz)
      linear_combination -this
    rw [h2] at hsmall; norm_num at hsmall

end

end GaloisForLFunctions.RHTower.ModularLambdaWinding
