import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheSquareOfAQuadraticRingPairsWithItsConductor
import GaloisForLFunctions.RHTower.WeilDecayClassRHCriterion
import GaloisForLFunctions.RHTower.WeilMarginSuperexponentialLaw
import GaloisForLFunctions.SquareRootThreshold.TheIncidenceLedgerGradedByTheZeroWidth

/-!
# Bézout determines the constant of the counterterm

The self-intersection of a degree point is the logarithm of the density of its comb over a
constant: `log(n/2π)` on the integers, `log(q n²/(2π)²)` on the norms of a quadratic ring of
conductor `q`. The constant is not a normalization. With any larger density in the counterterm
the inequality of Castelnuovo and Severi fails on a packet with both degrees zero, without
hypothesis; with any smaller one it is the same statement as with the constant itself.

* **Real and imaginary parts** (`re_weilFullFunctional_split`, `placeEnergy_split`,
  `re_zeta_W_split`, `zeroSums_split`): the sums over the zeros of `ζ` and of `L(s, χ)` of a
  complex test whose transform vanishes at `±i/2` are the sums of the values on its real and
  imaginary parts, and both parts have both degrees zero (`degrees_eq_zero_of_polar`).
* **No gap on the packets of degree zero** (`exists_primitive_packet_zeroSum_lt`,
  `exists_primitive_packet_zeroSums_lt`): for every `c > 0` there is a packet with
  `d₁ = d₂ = 0` and `Z(g) < c ∫g²`, for `ζ` and for the zeta function of a quadratic ring. The
  packets are truncations of functions in the radical of the forms: Riemann's kernel and the
  theta kernel of the character.
* **The integers** (`combBezoutShift_iff`): Bézout with the counterterm `log(n/2π) − c` holds iff
  `c ≤ 0` and the Riemann hypothesis holds. So `2π` is the largest constant for which the
  inequality is not refuted, and every smaller constant gives the Riemann hypothesis again:
  the inequality has no slack in either direction.
* **A quadratic ring** (`exists_packet_quadraticForm_pos`): with the conductor `q e^{−c}` in
  place of `q`, `c > 0`, some packet with both degrees zero has a positive pairing. The
  discriminant is forced from below by the inequality.

So the pairing on packets of degree zero is negative, if it is, without a gap: no multiple of the
mass can be added to the inequality, and the counterterm is read off from it.
-/

open Finset Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt Real

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Real and imaginary parts of a test -/

section Split

open _root_.RHTower _root_.RHTower.WeilOneSided _root_.RHTower.WeilWorkPBAP Finsupp

/-- The functional of a weight on a test is the sum of its values on the real and on the
imaginary part of the test. -/
theorem re_weilFullFunctional_split (lam : ℕ → ℝ) {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) :
    (_root_.RHTower.weilFullFunctional lam (EF.weilTest F F)).re =
      (_root_.RHTower.weilFullFunctional lam
        (EF.weilTest (fun u => ((F u).re : ℂ)) (fun u => ((F u).re : ℂ)))).re +
      (_root_.RHTower.weilFullFunctional lam
        (EF.weilTest (fun u => ((F u).im : ℂ)) (fun u => ((F u).im : ℂ)))).re := by
  classical
  set T : WeilTestFn := ⟨F, hF, hFc⟩ with hT
  set R := paperRealPartTestFn T with hR
  set J := paperImagPartTestFn T with hJ
  have hsplit : paperSplitRealMixture (Finsupp.single T 1) =
      Finsupp.single R 1 + Finsupp.single J 1 := by
    simp [paperSplitRealMixture, hR, hJ, Finsupp.mapDomain_single]
  have hE := energy_paperSplitRealMixture (Finsupp.single T 1)
  have hD := defect_paperSplitRealMixture (Finsupp.single T 1)
  rw [hsplit] at hE hD
  simp only [energy, defect, map_add, linearCombination_single, one_smul] at hE hD
  have h1 := re_weilFullFunctional_eq lam T
  have h2 := re_weilFullFunctional_eq lam R
  have h3 := re_weilFullFunctional_eq lam J
  show (_root_.RHTower.weilFullFunctional lam (EF.weilTest T.1 T.1)).re =
    (_root_.RHTower.weilFullFunctional lam (EF.weilTest R.1 R.1)).re +
      (_root_.RHTower.weilFullFunctional lam (EF.weilTest J.1 J.1)).re
  rw [h1, h2, h3, ← hE, ← hD, map_add]
  ring

end Split

variable {q : ℕ}

/-- The mass of a test is the sum of the masses of its real and imaginary parts. -/
theorem integral_norm_sq_split {F : ℝ → ℂ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    ∫ x, ‖F x‖ ^ 2 = (∫ x, (F x).re ^ 2) + ∫ x, (F x).im ^ 2 := by
  have hre : Continuous fun x => (F x).re := Complex.continuous_re.comp hF
  have him : Continuous fun x => (F x).im := Complex.continuous_im.comp hF
  have hrc : HasCompactSupport fun x => (F x).re ^ 2 :=
    hFc.comp_left (g := fun z : ℂ => z.re ^ 2) (by simp)
  have hic : HasCompactSupport fun x => (F x).im ^ 2 :=
    hFc.comp_left (g := fun z : ℂ => z.im ^ 2) (by simp)
  have i1 : Integrable fun x => (F x).re ^ 2 := (hre.pow 2).integrable_of_hasCompactSupport hrc
  have i2 : Integrable fun x => (F x).im ^ 2 := (him.pow 2).integrable_of_hasCompactSupport hic
  rw [← integral_add i1 i2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show ‖F x‖ ^ 2 = (F x).re ^ 2 + (F x).im ^ 2
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- **A test whose transform vanishes at `±i/2` has real and imaginary parts of degree zero.** -/
theorem degrees_eq_zero_of_polar {F : ℝ → ℂ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hp : paperFT F (Complex.I / 2) = 0) (hm : paperFT F (-(Complex.I / 2)) = 0) :
    (∫ u, (F u).re * Real.exp (-u / 2)) = 0 ∧ (∫ u, (F u).re * Real.exp (u / 2)) = 0 ∧
      (∫ u, (F u).im * Real.exp (-u / 2)) = 0 ∧ (∫ u, (F u).im * Real.exp (u / 2)) = 0 := by
  rw [_root_.RHTower.LebesgueAtomWeil.paperFT_I_div_two] at hp
  rw [← neg_div, _root_.RHTower.LebesgueAtomWeil.paperFT_neg_I_div_two] at hm
  have hi1 : Integrable fun u : ℝ => F u * (Real.exp (-u / 2) : ℂ) :=
    (hF.mul (by fun_prop)).integrable_of_hasCompactSupport hFc.mul_right
  have hi2 : Integrable fun u : ℝ => F u * (Real.exp (u / 2) : ℂ) :=
    (hF.mul (by fun_prop)).integrable_of_hasCompactSupport hFc.mul_right
  have r1 : ∫ u, (F u * (Real.exp (-u / 2) : ℂ)).re = (∫ u, F u * (Real.exp (-u / 2) : ℂ)).re :=
    Complex.reCLM.integral_comp_comm hi1
  have i1 : ∫ u, (F u * (Real.exp (-u / 2) : ℂ)).im = (∫ u, F u * (Real.exp (-u / 2) : ℂ)).im :=
    Complex.imCLM.integral_comp_comm hi1
  have r2 : ∫ u, (F u * (Real.exp (u / 2) : ℂ)).re = (∫ u, F u * (Real.exp (u / 2) : ℂ)).re :=
    Complex.reCLM.integral_comp_comm hi2
  have i2 : ∫ u, (F u * (Real.exp (u / 2) : ℂ)).im = (∫ u, F u * (Real.exp (u / 2) : ℂ)).im :=
    Complex.imCLM.integral_comp_comm hi2
  rw [hp, Complex.zero_re] at r1
  rw [hp, Complex.zero_im] at i1
  rw [hm, Complex.zero_re] at r2
  rw [hm, Complex.zero_im] at i2
  have hre : ∀ (z : ℂ) (r : ℝ), (z * (r : ℂ)).re = z.re * r := fun z r => by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have him : ∀ (z : ℂ) (r : ℝ), (z * (r : ℂ)).im = z.im * r := fun z r => by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← r1]
    exact integral_congr_ae (Eventually.of_forall fun u => (hre _ _).symm)
  · rw [← r2]
    exact integral_congr_ae (Eventually.of_forall fun u => (hre _ _).symm)
  · rw [← i1]
    exact integral_congr_ae (Eventually.of_forall fun u => (him _ _).symm)
  · rw [← i2]
    exact integral_congr_ae (Eventually.of_forall fun u => (him _ _).symm)

/-- The energy of the second archimedean factor is the sum of its values on the real and on the
imaginary part of a test: the autocorrelations add. -/
theorem placeEnergy_split (χ : DirichletCharacter ℂ q) {a : ℝ} {F : ℝ → ℂ}
    (hF : ContDiff ℝ 2 F) (hFs : tsupport F ⊆ Set.Icc (-a) a) :
    placeEnergy χ F =
      placeEnergy χ (fun u => ((F u).re : ℂ)) + placeEnergy χ (fun u => ((F u).im : ℂ)) := by
  rcases χ.even_or_odd with heven | hodd
  · rw [placeEnergy_of_even heven, placeEnergy_of_even heven, placeEnergy_of_even heven, add_zero]
  · obtain ⟨hFc, -, -, -, -⟩ := _root_.RHTower.weilTest_self_data hF hFs
    have hU : ContDiff ℝ 2 fun u => ((F u).re : ℂ) :=
      Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp hF)
    have hV : ContDiff ℝ 2 fun u => ((F u).im : ℂ) :=
      Complex.ofRealCLM.contDiff.comp (Complex.imCLM.contDiff.comp hF)
    have hUc : HasCompactSupport fun u => ((F u).re : ℂ) :=
      hFc.comp_left (g := fun z : ℂ => (z.re : ℂ)) (by simp)
    have hVc : HasCompactSupport fun u => ((F u).im : ℂ) :=
      hFc.comp_left (g := fun z : ℂ => (z.im : ℂ)) (by simp)
    have hUs : tsupport (fun u => ((F u).re : ℂ)) ⊆ Set.Icc (-a) a :=
      (tsupport_comp_subset (g := fun z : ℂ => (z.re : ℂ)) (by simp) F).trans hFs
    have hVs : tsupport (fun u => ((F u).im : ℂ)) ⊆ Set.Icc (-a) a :=
      (tsupport_comp_subset (g := fun z : ℂ => (z.im : ℂ)) (by simp) F).trans hFs
    have hκc := _root_.RHTower.CHMDHalfTime.continuous_inv_cosh_half
    have hint : ∀ {G : ℝ → ℂ}, ContDiff ℝ 2 G → HasCompactSupport G →
        Integrable fun r : ℝ => (Real.cosh (r / 2))⁻¹ *
          (EF.weilTest G G r + EF.weilTest G G (-r)).re := by
      intro G hG hGc
      have hkc := EF.weilTest_hasCompactSupport hGc hGc
      have hkcont : Continuous (EF.weilTest G G) :=
        (EF.weilTest_contDiff hG hG.continuous hGc).continuous
      have hsum : HasCompactSupport fun r : ℝ =>
          (EF.weilTest G G r + EF.weilTest G G (-r)).re :=
        (hkc.add (hkc.comp_homeomorph (Homeomorph.neg ℝ))).comp_left (g := Complex.re)
          Complex.zero_re
      exact (hκc.mul (Complex.continuous_re.comp
        (hkcont.add (hkcont.comp continuous_neg)))).integrable_of_hasCompactSupport
          (hsum.mul_left (f := fun r : ℝ => (Real.cosh (r / 2))⁻¹))
    have hs : ∀ y : ℝ,
        (EF.weilTest (fun u => ((F u).re : ℂ)) (fun u => ((F u).re : ℂ)) y).re +
          (EF.weilTest (fun u => ((F u).im : ℂ)) (fun u => ((F u).im : ℂ)) y).re =
        (EF.weilTest F F y).re := fun y => by
      have h := congrArg Complex.re
        (_root_.RHTower.WeilWorkPBAP.weilTest_real_imag_split ⟨F, hF, hFc⟩ y)
      rw [Complex.add_re, Complex.ofReal_re] at h
      exact h
    rw [placeEnergy_of_odd hodd, placeEnergy_of_odd hodd, placeEnergy_of_odd hodd,
      integral_normSq_paperFT_mul_sech hF hFs, integral_normSq_paperFT_mul_sech hU hUs,
      integral_normSq_paperFT_mul_sech hV hVs, ← mul_add, ← integral_add (hint hU hUc)
        (hint hV hVc)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    show (Real.cosh (r / 2))⁻¹ * (EF.weilTest F F r + EF.weilTest F F (-r)).re =
      (Real.cosh (r / 2))⁻¹ *
          (EF.weilTest (fun u => ((F u).re : ℂ)) (fun u => ((F u).re : ℂ)) r +
            EF.weilTest (fun u => ((F u).re : ℂ)) (fun u => ((F u).re : ℂ)) (-r)).re +
        (Real.cosh (r / 2))⁻¹ *
          (EF.weilTest (fun u => ((F u).im : ℂ)) (fun u => ((F u).im : ℂ)) r +
            EF.weilTest (fun u => ((F u).im : ℂ)) (fun u => ((F u).im : ℂ)) (-r)).re
    rw [Complex.add_re, Complex.add_re, Complex.add_re, ← hs r, ← hs (-r)]
    ring

/-- The sum over the zeros of `ζ` of a test is the sum of its values on the real and on the
imaginary part. -/
theorem re_zeta_W_split {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) :
    (zetaZeroConfig.W F F).re = zeroSum (fun x => (F x).re) + zeroSum (fun x => (F x).im) := by
  have hu : ContDiff ℝ 2 fun x => (F x).re := Complex.reCLM.contDiff.comp hF
  have hv : ContDiff ℝ 2 fun x => (F x).im := Complex.imCLM.contDiff.comp hF
  have huc : HasCompactSupport fun x => (F x).re :=
    hFc.comp_left (g := fun z : ℂ => z.re) (by simp)
  have hvc : HasCompactSupport fun x => (F x).im :=
    hFc.comp_left (g := fun z : ℂ => z.im) (by simp)
  have e1 : zeroSum (fun x => (F x).re) = (_root_.RHTower.weilFullFunctional
      (fun n => (Λ n : ℝ))
      (EF.weilTest (fun u => ((F u).re : ℂ)) (fun u => ((F u).re : ℂ)))).re :=
    zeroSum_eq_weilFullFunctional hu huc
  have e2 : zeroSum (fun x => (F x).im) = (_root_.RHTower.weilFullFunctional
      (fun n => (Λ n : ℝ))
      (EF.weilTest (fun u => ((F u).im : ℂ)) (fun u => ((F u).im : ℂ)))).re :=
    zeroSum_eq_weilFullFunctional hv hvc
  rw [_root_.RHTower.zeta_W_eq_weilFullFunctional hF hFc, re_weilFullFunctional_split _ hF hFc,
    e1, e2]

/-- **The zero sums of a quadratic ring on a test whose transform vanishes at `±i/2`** are the
sums of the zero sums of its real and imaginary parts. -/
theorem zeroSums_split [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0) {a : ℝ} (ha : 0 ≤ a)
    {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) (hFs : tsupport F ⊆ Set.Icc (-a) a)
    (hp : paperFT F (Complex.I / 2) = 0) (hm : paperFT F (-(Complex.I / 2)) = 0) :
    (zetaZeroConfig.W F F).re + ((_root_.RHTower.dirichletZeros hq hprim).W F F).re =
      (zeroSum (fun x => (F x).re) + twistedZeroSum hq hprim (fun x => (F x).re)) +
        (zeroSum (fun x => (F x).im) + twistedZeroSum hq hprim (fun x => (F x).im)) := by
  obtain ⟨hFc, -, -, -, -⟩ := _root_.RHTower.weilTest_self_data hF hFs
  obtain ⟨hd1, hd2, hd3, hd4⟩ := degrees_eq_zero_of_polar hF.continuous hFc hp hm
  have hu : ContDiff ℝ 2 fun x => (F x).re := Complex.reCLM.contDiff.comp hF
  have hv : ContDiff ℝ 2 fun x => (F x).im := Complex.imCLM.contDiff.comp hF
  have huc : HasCompactSupport fun x => (F x).re :=
    hFc.comp_left (g := fun z : ℂ => z.re) (by simp)
  have hvc : HasCompactSupport fun x => (F x).im :=
    hFc.comp_left (g := fun z : ℂ => z.im) (by simp)
  have hχF := re_weilFullFunctional_twist hq hprim hreal ha hF hFs
  rw [_root_.RHTower.weilPoleTerm_eq_zero_of_paperFT_I_div_two_eq_zero hF.continuous hFc hp,
    Complex.zero_re, zero_add, integral_norm_sq_split hF.continuous hFc, mul_add,
    placeEnergy_split χ hF hFs, re_weilFullFunctional_split _ hF hFc] at hχF
  have hχu : (_root_.RHTower.weilFullFunctional (twistWeight χ)
        (EF.weilTest (fun u => ((F u).re : ℂ)) (fun u => ((F u).re : ℂ)))).re =
      2 * ((∫ u, (F u).re * Real.exp (-u / 2)) * ∫ u, (F u).re * Real.exp (u / 2)) +
        twistedZeroSum hq hprim (fun x => (F x).re) - Real.log q * (∫ u, (F u).re ^ 2) -
        placeEnergy χ (fun u => ((F u).re : ℂ)) :=
    re_weilFullFunctional_twist_packet hq hprim hu huc
  have hχv : (_root_.RHTower.weilFullFunctional (twistWeight χ)
        (EF.weilTest (fun u => ((F u).im : ℂ)) (fun u => ((F u).im : ℂ)))).re =
      2 * ((∫ u, (F u).im * Real.exp (-u / 2)) * ∫ u, (F u).im * Real.exp (u / 2)) +
        twistedZeroSum hq hprim (fun x => (F x).im) - Real.log q * (∫ u, (F u).im ^ 2) -
        placeEnergy χ (fun u => ((F u).im : ℂ)) :=
    re_weilFullFunctional_twist_packet hq hprim hv hvc
  rw [hd1, hd2] at hχu
  rw [hd3, hd4] at hχv
  have hζ := re_zeta_W_split hF hFc
  linarith

/-! ### No gap on the packets of degree zero -/

/-- The tails of `R e^{−R/2}` are small. -/
theorem exists_radius_small (R₀ M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, R₀ ≤ R ∧ 1 ≤ R ∧ M * (R * Real.exp (-(R / 2))) < ε := by
  have hlim : Tendsto (fun R : ℝ => M * (R * Real.exp (-(R / 2)))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    have h2 := (h.const_mul 2).const_mul M
    simp only [mul_zero] at h2
    refine h2.congr fun R => ?_
    simp only [Function.comp_apply, id, pow_one]
    ring
  obtain ⟨R, hR1, hR2, hR3⟩ := ((hlim.eventually (gt_mem_nhds hε)).and
    ((eventually_ge_atTop R₀).and (eventually_ge_atTop 1))).exists
  exact ⟨R, hR2, hR3, hR1⟩

/-- **A test in the radical of both forms, truncated.** For a real primitive character of
conductor `q > 1` and every `c > 0` there is a test whose transform vanishes at `±i/2` and whose
zero sums for `ζ` and `L(s, χ)` add up to less than `c` times its mass. -/
theorem exists_test_zeroSums_lt [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) {c : ℝ} (hc : 0 < c) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ F : ℝ → ℂ, ContDiff ℝ 2 F ∧ tsupport F ⊆ Set.Icc (-a) a ∧
      paperFT F (Complex.I / 2) = 0 ∧ paperFT F (-(Complex.I / 2)) = 0 ∧
      (zetaZeroConfig.W F F).re + ((_root_.RHTower.dirichletZeros hq hprim).W F F).re <
        c * ∫ x, ‖F x‖ ^ 2 := by
  have hχ := _root_.RHTower.ne_one_of_isPrimitive hq hprim
  have hπ : 0 < π := Real.pi_pos
  have key : ∀ {F : ℝ → ℂ} {a KW KL R c₁ : ℝ}, ContDiff ℝ 2 F → tsupport F ⊆ Set.Icc (-a) a →
      ‖zetaZeroConfig.W F F‖ ≤ KW * (R * Real.exp (-(R / 2))) →
      ‖(_root_.RHTower.dirichletZeros hq hprim).W F F‖ ≤ KL * (R * Real.exp (-(R / 2))) →
      (KW + KL) * (R * Real.exp (-(R / 2))) < c * c₁ / (2 * π) →
      c₁ ≤ ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 →
      (zetaZeroConfig.W F F).re + ((_root_.RHTower.dirichletZeros hq hprim).W F F).re <
        c * ∫ x, ‖F x‖ ^ 2 := by
    intro F a KW KL R c₁ hF hFs h1 h2 h3 h4
    rw [_root_.RHTower.integral_norm_paperFT_sq hF hFs] at h4
    have e1 := (Complex.re_le_norm (zetaZeroConfig.W F F)).trans h1
    have e2 := (Complex.re_le_norm ((_root_.RHTower.dirichletZeros hq hprim).W F F)).trans h2
    have e3 : c * c₁ / (2 * π) ≤ c * ∫ x, ‖F x‖ ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    rw [add_mul] at h3
    linarith
  rcases χ.even_or_odd with heven | hodd
  · obtain ⟨c₁, R₀, hc₁, -, hmass⟩ :=
      _root_.RHTower.exists_integral_normSq_dirichletTest_ge hq hχ heven
    obtain ⟨KW, -, hKW⟩ := _root_.RHTower.exists_norm_W_zeta_dirichletTest_le hq hχ
    obtain ⟨KL, -, hKL⟩ :=
      _root_.RHTower.exists_norm_W_dirichlet_dirichletTest_le hq hχ heven hprim
    obtain ⟨R, hR₀, hR1, hRs⟩ := exists_radius_small R₀ (KW + KL)
      (show 0 < c * c₁ / (2 * π) by positivity)
    exact ⟨5 * R, by linarith, _root_.RHTower.dirichletTest χ R,
      _root_.RHTower.contDiff_dirichletTest χ R, _root_.RHTower.tsupport_dirichletTest χ R,
      _root_.RHTower.paperFT_dirichletTest_half_I χ R,
      _root_.RHTower.paperFT_dirichletTest_neg_half_I χ R,
      key (_root_.RHTower.contDiff_dirichletTest χ R) (_root_.RHTower.tsupport_dirichletTest χ R)
        (hKW R hR1) (hKL R hR1) hRs (hmass R hR₀)⟩
  · obtain ⟨CΨ, hCΨ, hΨd⟩ :=
      _root_.RHTower.exists_norm_dirichletOddAxisKernel_le χ (B := 1) (by norm_num)
    have hΨd' : ∀ u, ‖_root_.RHTower.dirichletOddAxisKernel χ u‖ ≤ CΨ * Real.exp (-|u|) :=
      fun u => by simpa using hΨd u
    have hΨc := _root_.RHTower.continuous_dirichletOddAxisKernel χ
    obtain ⟨c₁, R₀, hc₁, -, hmass⟩ := _root_.RHTower.exists_integral_normSq_jointRadicalTest_ge
      (_root_.RHTower.superExpDecay_dirichletOddAxisKernel χ)
      (_root_.RHTower.paperFT_dirichletOddAxisKernel_ne_zero hq hodd) hCΨ hΨd'
    obtain ⟨KW, -, hKW⟩ := _root_.RHTower.exists_norm_W_zeta_jointRadicalTest_le hΨc hΨd'
    obtain ⟨KL, -, hKL⟩ := _root_.RHTower.exists_norm_W_jointRadicalTest_le
      (_root_.RHTower.dirichletZeros hq hprim) (_root_.RHTower.summable_dirichletZeros hq hprim)
      (fun ρ => by
        have h : Zeta23.ThmE.IsNontrivialZeroL χ (ρ : ℂ) := ρ.2
        exact ⟨h.2.1, h.2.2⟩)
      hΨc hCΨ hΨd'
      (fun ρ => _root_.RHTower.paperFT_dirichletOddAxisKernel_gammaOf_eq_zero hq hodd ρ.2)
    obtain ⟨R, hR₀, hR1, hRs⟩ := exists_radius_small R₀ (KW + KL)
      (show 0 < c * c₁ / (2 * π) by positivity)
    exact ⟨5 * R, by linarith,
      _root_.RHTower.jointRadicalTest (_root_.RHTower.dirichletOddAxisKernel χ) R,
      _root_.RHTower.contDiff_jointRadicalTest hΨc R, _root_.RHTower.tsupport_jointRadicalTest _ R,
      _root_.RHTower.paperFT_jointRadicalTest_half_I hΨc R,
      _root_.RHTower.paperFT_jointRadicalTest_neg_half_I hΨc R,
      key (_root_.RHTower.contDiff_jointRadicalTest hΨc R)
        (_root_.RHTower.tsupport_jointRadicalTest _ R) (hKW R hR1) (hKL R hR1) hRs
        (hmass R hR₀)⟩

/-- **No gap for a quadratic ring.** For every `c > 0` there is a packet with both degrees zero
whose zero sums for `ζ` and `L(s, χ)` add up to less than `c` times its mass. -/
theorem exists_primitive_packet_zeroSums_lt [NeZero q] (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0)
    {c : ℝ} (hc : 0 < c) :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      (∫ u, g u * Real.exp (-u / 2)) = 0 ∧ (∫ u, g u * Real.exp (u / 2)) = 0 ∧
      zeroSum g + twistedZeroSum hq hprim g < c * ∫ u, g u ^ 2 := by
  obtain ⟨a, ha, F, hF, hFs, hp, hm, hlt⟩ := exists_test_zeroSums_lt hq hprim hc
  obtain ⟨hFc, -, -, -, -⟩ := _root_.RHTower.weilTest_self_data hF hFs
  obtain ⟨hd1, hd2, hd3, hd4⟩ := degrees_eq_zero_of_polar hF.continuous hFc hp hm
  rw [zeroSums_split hq hprim hreal ha hF hFs hp hm, integral_norm_sq_split hF.continuous hFc,
    mul_add] at hlt
  have hu : ContDiff ℝ 2 fun x => (F x).re := Complex.reCLM.contDiff.comp hF
  have hv : ContDiff ℝ 2 fun x => (F x).im := Complex.imCLM.contDiff.comp hF
  have huc : HasCompactSupport fun x => (F x).re :=
    hFc.comp_left (g := fun z : ℂ => z.re) (by simp)
  have hvc : HasCompactSupport fun x => (F x).im :=
    hFc.comp_left (g := fun z : ℂ => z.im) (by simp)
  by_cases h : zeroSum (fun x => (F x).re) + twistedZeroSum hq hprim (fun x => (F x).re) <
      c * ∫ x, (F x).re ^ 2
  · exact ⟨fun x => (F x).re, hu, huc, hd1, hd2, h⟩
  · exact ⟨fun x => (F x).im, hv, hvc, hd3, hd4, by linarith [not_lt.mp h]⟩

/-- **A truncation of Riemann's kernel.** For every `c > 0` there is a test whose transform
vanishes at `±i/2` and whose zero sum is less than `c` times its mass. -/
theorem exists_test_zeroSum_lt {c : ℝ} (hc : 0 < c) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ F : ℝ → ℂ, ContDiff ℝ 2 F ∧ tsupport F ⊆ Set.Icc (-a) a ∧
      paperFT F (Complex.I / 2) = 0 ∧ paperFT F (-(Complex.I / 2)) = 0 ∧
      (zetaZeroConfig.W F F).re < c * ∫ x, ‖F x‖ ^ 2 := by
  obtain ⟨C, L₀, hC, -, h⟩ := _root_.RHTower.zeta_weil_margin_superexponential
  obtain ⟨L, hL1, hL3, hLlog⟩ : ∃ L : ℝ, L₀ ≤ L ∧ 3 ≤ L ∧ Real.log (C / c) + 1 ≤ L :=
    ⟨max L₀ (max 3 (Real.log (C / c) + 1)), le_max_left _ _,
      (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
  obtain ⟨F, hF, hFs, hp, hm, hpos, hW⟩ := h L hL1
  refine ⟨L, by linarith, F, hF, hFs, hp, hm, ?_⟩
  -- the constant of the margin is at most `C e^{−L}`
  have hexp : Real.exp (12 * L) * Real.exp (-π * Real.exp (2 * L - 1 / 2)) ≤ Real.exp (-L) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hq := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 * L - 1 / 2 by linarith)
    have hE : 13 * L ≤ 3 * Real.exp (2 * L - 1 / 2) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hL3) (sub_nonneg.mpr hL3)]
    have hπE : 3 * Real.exp (2 * L - 1 / 2) ≤ π * Real.exp (2 * L - 1 / 2) :=
      mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.exp_pos _).le
    linarith
  have hsmall : C * Real.exp (-L) < c := by
    have hlog : Real.exp (Real.log (C / c)) = C / c := Real.exp_log (div_pos hC hc)
    have h1 : Real.exp (-L) < c / C := by
      rw [show c / C = (C / c)⁻¹ by rw [inv_div], ← hlog, ← Real.exp_neg]
      exact Real.exp_lt_exp.mpr (by linarith)
    calc C * Real.exp (-L) < C * (c / C) := mul_lt_mul_of_pos_left h1 hC
      _ = c := by field_simp
  calc (zetaZeroConfig.W F F).re ≤ ‖zetaZeroConfig.W F F‖ := Complex.re_le_norm _
    _ ≤ C * Real.exp (12 * L) * Real.exp (-π * Real.exp (2 * L - 1 / 2)) *
          ∫ x, ‖F x‖ ^ 2 := hW
    _ ≤ C * Real.exp (-L) * ∫ x, ‖F x‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ hpos.le
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hexp hC.le
    _ < c * ∫ x, ‖F x‖ ^ 2 := mul_lt_mul_of_pos_right hsmall hpos

/-- **No gap for the integers.** For every `c > 0` there is a packet with both degrees zero
whose zero sum is less than `c` times its mass. -/
theorem exists_primitive_packet_zeroSum_lt {c : ℝ} (hc : 0 < c) :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      (∫ u, g u * Real.exp (-u / 2)) = 0 ∧ (∫ u, g u * Real.exp (u / 2)) = 0 ∧
      zeroSum g < c * ∫ u, g u ^ 2 := by
  obtain ⟨a, -, F, hF, hFs, hp, hm, hlt⟩ := exists_test_zeroSum_lt hc
  obtain ⟨hFc, -, -, -, -⟩ := _root_.RHTower.weilTest_self_data hF hFs
  obtain ⟨hd1, hd2, hd3, hd4⟩ := degrees_eq_zero_of_polar hF.continuous hFc hp hm
  rw [re_zeta_W_split hF hFc, integral_norm_sq_split hF.continuous hFc, mul_add] at hlt
  have hu : ContDiff ℝ 2 fun x => (F x).re := Complex.reCLM.contDiff.comp hF
  have hv : ContDiff ℝ 2 fun x => (F x).im := Complex.imCLM.contDiff.comp hF
  have huc : HasCompactSupport fun x => (F x).re :=
    hFc.comp_left (g := fun z : ℂ => z.re) (by simp)
  have hvc : HasCompactSupport fun x => (F x).im :=
    hFc.comp_left (g := fun z : ℂ => z.im) (by simp)
  by_cases h : zeroSum (fun x => (F x).re) < c * ∫ x, (F x).re ^ 2
  · exact ⟨fun x => (F x).re, hu, huc, hd1, hd2, h⟩
  · exact ⟨fun x => (F x).im, hv, hvc, hd3, hd4, by linarith [not_lt.mp h]⟩

/-! ### Packets in a window -/

/-- A degree of a packet vanishes with that of its translates. -/
theorem integral_translate_mul_eq_zero {g e : ℝ → ℝ} (he : ∀ u s, e (u + s) = e s * e u)
    (h : ∫ u, g u * e u = 0) (s : ℝ) : ∫ u, g (u - s) * e u = 0 := by
  have h0 : ∫ u, g (u - s) * e (u - s + s) = ∫ u, g u * e (u + s) :=
    integral_sub_right_eq_self (fun u => g u * e (u + s)) s
  have h1 : ∫ u, g (u - s) * e u = ∫ u, g (u - s) * e (u - s + s) :=
    integral_congr_ae (Eventually.of_forall fun u => by
      show g (u - s) * e u = g (u - s) * e (u - s + s)
      rw [sub_add_cancel])
  have h2 : ∫ u, g u * e (u + s) = e s * ∫ u, g u * e u := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun u => by
      show g u * e (u + s) = e s * (g u * e u)
      rw [he]
      ring)
  rw [h1, h0, h2, h, mul_zero]

/-- A packet with both degrees zero has a translate in a window with both degrees zero. -/
theorem exists_translate_window_primitive {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (h1 : (∫ u, g u * Real.exp (-u / 2)) = 0)
    (h2 : (∫ u, g u * Real.exp (u / 2)) = 0) :
    ∃ (s : ℝ) (K : ℕ), 1 ≤ K ∧ (∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → g (u - s) = 0) ∧
      ContDiff ℝ 2 (fun u => g (u - s)) ∧ HasCompactSupport (fun u => g (u - s)) ∧
      (∫ u, g (u - s) * Real.exp (-u / 2)) = 0 ∧ (∫ u, g (u - s) * Real.exp (u / 2)) = 0 ∧
      (∫ u, g (u - s) ^ 2) = ∫ u, g u ^ 2 := by
  obtain ⟨s, K, hK, hsupp⟩ := exists_translate_window hgc
  refine ⟨s, K, hK, hsupp, hg.comp (contDiff_id.sub contDiff_const),
    hgc.comp_homeomorph (Homeomorph.subRight s), ?_, ?_,
    integral_sub_right_eq_self (fun u => g u ^ 2) s⟩
  · exact integral_translate_mul_eq_zero (e := fun u => Real.exp (-u / 2)) (fun u s => by
      rw [← Real.exp_add]
      congr 1
      ring) h1 s
  · exact integral_translate_mul_eq_zero (e := fun u => Real.exp (u / 2)) (fun u s => by
      rw [← Real.exp_add]
      congr 1
      ring) h2 s

/-! ### The integers -/

variable {f : ℝ → ℝ}

/-- The pairing of the degree points with the counterterm `log(n/2π) − c` on a packet. -/
theorem tendsto_shiftedPairing (c : ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {K : ℕ} (hK : 1 ≤ K) (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => degreeForm f (3 * K) N +
        c * ∑ n ∈ Ioc N (N + 3 * K * N), degreeSample f N n ^ 2 / n +
        2 * degreeContact f (3 * K) N) atTop
      (𝓝 (2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) - zeroSum f +
        c * ∫ u, f u ^ 2)) :=
  ((tendsto_degreePairing_degrees_sub_zeroSum hf hfc hK hsupp).add
    ((tendsto_degreeMass hf.continuous hK hsupp).const_mul c)).congr fun N => by ring

/-- Bézout on the comb of the integers with the counterterm `log(n/2π) − c`: the density of the
comb over `2π e^{c}`. -/
def CombBezoutShift (c : ℝ) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f → ∀ K : ℕ, 1 ≤ K →
    (∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) →
    ∀ l : ℝ, Tendsto (fun N : ℕ => degreeForm f (3 * K) N +
        c * ∑ n ∈ Ioc N (N + 3 * K * N), degreeSample f N n ^ 2 / n +
        2 * degreeContact f (3 * K) N) atTop (𝓝 l) →
      l ≤ 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2))

/-- **With a constant above `2π` the inequality fails.** For `c > 0` some packet with both
degrees zero has a positive pairing with the counterterm `log(n/2π) − c`. -/
theorem exists_packet_shiftedPairing_pos {c : ℝ} (hc : 0 < c) :
    ∃ (f : ℝ → ℝ) (K : ℕ), ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ 1 ≤ K ∧
      (∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) ∧
      (∫ u, f u * Real.exp (-u / 2)) = 0 ∧ (∫ u, f u * Real.exp (u / 2)) = 0 ∧
      ∃ l : ℝ, Tendsto (fun N : ℕ => degreeForm f (3 * K) N +
            c * ∑ n ∈ Ioc N (N + 3 * K * N), degreeSample f N n ^ 2 / n +
            2 * degreeContact f (3 * K) N) atTop (𝓝 l) ∧ 0 < l := by
  obtain ⟨g, hg, hgc, hg1, hg2, hlt⟩ := exists_primitive_packet_zeroSum_lt hc
  obtain ⟨s, K, hK, hsupp, hf, hfc, hd1, hd2, hmass⟩ :=
    exists_translate_window_primitive hg hgc hg1 hg2
  refine ⟨fun u => g (u - s), K, hf, hfc, hK, hsupp, hd1, hd2, _,
    tendsto_shiftedPairing c hf hfc hK hsupp, ?_⟩
  have hpos : 0 < 2 * ((∫ u, g (u - s) * Real.exp (-u / 2)) *
        ∫ u, g (u - s) * Real.exp (u / 2)) - zeroSum (fun u => g (u - s)) +
      c * ∫ u, g (u - s) ^ 2 := by
    rw [hd1, zeroSum_translate hg hgc s, hmass]
    linarith
  exact hpos

section Floor

open GaloisForLFunctions.ArithmeticCriticalityTheory GaloisForLFunctions.ArithmeticPositivityTheory

/-- **Bézout on the integers has no slack in either direction.** With the counterterm
`log(n/2π) − c` the inequality holds for all packets iff `c ≤ 0` and the Riemann hypothesis
holds. -/
theorem combBezoutShift_iff (c : ℝ) : CombBezoutShift c ↔ c ≤ 0 ∧ RiemannHypothesis := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hc
      obtain ⟨f, K, hf, hfc, hK, hsupp, hd1, hd2, l, hl, hpos⟩ :=
        exists_packet_shiftedPairing_pos (not_le.mp hc)
      have := h f hf hfc K hK hsupp l hl
      rw [hd1, zero_mul, mul_zero] at this
      linarith
    · refine SquareRootThreshold.riemannHypothesis_of_odd_fullZeroForm_bddBelow (C := -c)
        fun F hF hFc _ => ?_
      obtain ⟨s, K, hK, hsupp⟩ := exists_translate_window hFc
      have hg : ContDiff ℝ 2 fun u => F (u - s) := hF.comp (contDiff_id.sub contDiff_const)
      have hgc : HasCompactSupport fun u => F (u - s) :=
        hFc.comp_homeomorph (Homeomorph.subRight s)
      have hle : 2 * ((∫ u, F (u - s) * Real.exp (-u / 2)) *
            ∫ u, F (u - s) * Real.exp (u / 2)) - zeroSum (fun u => F (u - s)) +
          c * ∫ u, F (u - s) ^ 2 ≤
          2 * ((∫ u, F (u - s) * Real.exp (-u / 2)) * ∫ u, F (u - s) * Real.exp (u / 2)) :=
        h _ hg hgc K hK hsupp _ (tendsto_shiftedPairing c hg hgc hK hsupp)
      have hmass : ∫ u, F (u - s) ^ 2 = ∫ u, F u ^ 2 :=
        integral_sub_right_eq_self (fun u => F u ^ 2) s
      rw [zeroSum_translate hF hFc s, hmass] at hle
      rw [fullZeroForm_eq_re_weilFullFunctional hF.continuous hFc,
        ← zeroSum_eq_weilFullFunctional hF hFc]
      linarith
  · rintro ⟨hc, hRH⟩ f hf hfc K hK hsupp l hl
    rw [tendsto_nhds_unique hl (tendsto_shiftedPairing c hf hfc hK hsupp)]
    have hZ : 0 ≤ zeroSum f := by
      have h1 := neg_offLineDefect_le_zeroSum hf hfc
      rw [riemannHypothesis_iff_offLineDefect_eq_zero.mp hRH f hf hfc] at h1
      linarith
    have hm : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun u => sq_nonneg _
    nlinarith

end Floor

/-! ### A quadratic ring -/

/-- **Bézout forces the conductor into the counterterm.** For a real primitive character of
conductor `q > 1` and every `c > 0` there is a packet in a window, with both degrees zero, whose
pairing on the square of the quadratic ring with the counterterm `log(q e^{−c} n²/(2π)²)` has a
positive limit. -/
theorem exists_packet_quadraticForm_pos [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0) {c : ℝ} (hc : 0 < c) :
    ∃ (f : ℝ → ℝ) (K : ℕ), ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ 1 ≤ K ∧
      (∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) ∧
      (∫ u, f u * Real.exp (-u / 2)) = 0 ∧ (∫ u, f u * Real.exp (u / 2)) = 0 ∧
      ∃ l : ℝ, Tendsto (fun N : ℕ => quadraticForm χ f (3 * K) N +
            c * ∑ n ∈ Ioc N (N + 3 * K * N), degreeSample f N n ^ 2 / n +
            2 * weightedContact (idealWeight χ) f (3 * K) N) atTop (𝓝 l) ∧ 0 < l := by
  obtain ⟨g, hg, hgc, hg1, hg2, hlt⟩ := exists_primitive_packet_zeroSums_lt hq hprim hreal hc
  obtain ⟨s, K, hK, hsupp, hf, hfc, hd1, hd2, hmass⟩ :=
    exists_translate_window_primitive hg hgc hg1 hg2
  have hlim := (tendsto_quadraticForm_add_idealContact hq hprim hf hfc hK hsupp).add
    ((tendsto_degreeMass hf.continuous hK hsupp).const_mul c)
  refine ⟨fun u => g (u - s), K, hf, hfc, hK, hsupp, hd1, hd2, _,
    hlim.congr fun N => by ring, ?_⟩
  have hpos : 0 < 2 * ((∫ u, g (u - s) * Real.exp (-u / 2)) *
        ∫ u, g (u - s) * Real.exp (u / 2)) -
      (zeroSum (fun u => g (u - s)) + twistedZeroSum hq hprim (fun u => g (u - s))) +
      c * ∫ u, g (u - s) ^ 2 := by
    rw [hd1, zeroSum_translate hg hgc s, twistedZeroSum_translate hq hprim hg hgc s, hmass]
    linarith
  exact hpos

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
