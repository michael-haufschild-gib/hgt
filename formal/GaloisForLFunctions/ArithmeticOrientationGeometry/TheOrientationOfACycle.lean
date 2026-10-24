import GaloisForLFunctions.ArithmeticOrientationGeometry.TheScalingDatumOfAConfiguration
import GaloisForLFunctions.SquareRootThreshold.WeilPositivityForcesTheCriticalLine
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectIsCyclic

/-!
# The orientation of a cycle

On the scaling datum of a tempered configuration, which cycles are oriented, i.e. satisfy the
Hasse–Weil bound `|c_x(t)| ≤ c_x(0)` at every scale? The answer is spectral and exact.

A real test `f` is **blind to the off-line zeros** (`BlindOffLine`) when its transform vanishes at
one of the two points `γ_ρ, γ̄_ρ` of every off-line reflection pair.

* **Blindness orients** (`orbitHodgeIndex_of_blindOffLine`). On every tempered configuration, a
  cycle whose test is blind to the off-line zeros has the orbit Hodge index. Every orbit
  combination has transform `P(z) h_f(z)` with an exponential polynomial `P`
  (`paperFT_orbitTest`), so it is blind as well; its Weil form is then a sum of on-line terms
  `m |h(γ)|² ≥ 0`.
* **Self-upgrade** (`blindOffLine_of_hasseWeil`). On a configuration symmetric under the functional
  equation, the Hasse–Weil bound at every scale forces blindness. Otherwise a rightmost zero at
  some height carries a nonzero weight and the orbit correlation, an exponential sum over the
  zeros, has a pole beyond the imaginary axis; a bounded exponential sum has no such pole
  (Square-Root Threshold, `exists_minor_fails_of_top`). The orbit correlation of a real test is
  real there (`W_real_of_fes`), so the two-bump minor of Square-Root Threshold is the Weil plane.
* **The orientation theorem** (`orientation_tfae`). For such configurations the following are
  equivalent: Hasse–Weil at every scale; the orbit Hodge index; blindness to the off-line zeros.
  Positivity on the orbit is a growth statement about one function.
* **The oriented locus** (`blindOffLine_orbitTest`). Blindness is inherited by every orbit
  combination, so the oriented cycles are a union of correspondence-stable subspaces, one for each
  choice of a point in every off-line pair.
* **One generic orbit decides** (`onLine_iff_hasseWeil_of_generic`). A spectrally generic test is
  blind only if there are no off-line zeros, so its single orbit decides whether the configuration
  lies on the critical line.
* **For `ζ`** (`zeta_orientation_tfae`, `riemannHypothesis_iff_hasseWeil_of_generic`). A cycle of
  the scaling surface of `ℤ` satisfies the Hasse–Weil bound along its whole orbit iff its transform
  vanishes at one point of each off-line pair of zeros of `ζ`; RH holds iff the orbit of one
  spectrally generic real test satisfies `|W(f, f(· − t))| ≤ W(f, f)` for every `t`.
-/

noncomputable section

open Complex Finset
open scoped ComplexConjugate
open Zeta23

namespace GaloisForLFunctions.ArithmeticOrientationGeometry

open ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig
  rightZeros lagStructure lagTerm offLineWeight pairWeight exists_top_at_height
  exists_minor_fails_of_top exists_radius_of_hasCompactSupport)

/-! ### Blindness to the off-line zeros -/

/-- A real test is **blind to the off-line zeros** of `Z` when its transform vanishes at one of
the two points `γ_ρ, γ̄_ρ` of every zero off the critical line. -/
def BlindOffLine (Z : ZeroConfig) (f : ℝ → ℝ) : Prop :=
  ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 →
    paperFT (cx f) (gammaOf ρ) = 0 ∨ paperFT (cx f) (conj (gammaOf ρ)) = 0

/-- Translation multiplies the transform by an exponential at every point. -/
theorem paperFT_cx_scaleShift_apply (t : ℝ) (f : ℝ → ℝ) (z : ℂ) :
    paperFT (cx (scaleShift t f)) z = cexp (t * (I * z)) * paperFT (cx f) z := by
  have hg : gammaOf (I * z + 1 / 2) = z := by
    rw [gammaOf, add_sub_cancel_right, mul_div_cancel_left₀ _ I_ne_zero]
  have h := paperFT_cx_scaleShift t f (I * z + 1 / 2)
  rwa [hg, add_sub_cancel_right] at h

/-- **Orbit combinations have transform `P(z) h_f(z)`** with the exponential polynomial
`P(z) = Σ c_g e^{i g z}`. -/
theorem paperFT_orbitTest {f : ℝ → ℝ} (hf : f ∈ realTests) (S : Finset ℝ) (c : ℝ → ℝ) (z : ℂ) :
    paperFT (cx (∑ g ∈ S, c g • scaleShift g f)) z =
      (∑ g ∈ S, (c g : ℂ) * cexp (g * (I * z))) * paperFT (cx f) z := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [cx, paperFT]
  | insert a S ha ih =>
    have hmem : ∀ T : Finset ℝ, (∑ g ∈ T, c g • scaleShift g f) ∈ realTests := fun T =>
      Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (scaleShift_mem g hf)
    have ha' : (c a • scaleShift a f) ∈ realTests := Submodule.smul_mem _ _ (scaleShift_mem a hf)
    rw [sum_insert ha, cx_add, paperFT_add (cx_contDiff ha'.1).continuous
      (cx_hasCompactSupport ha'.2) (cx_contDiff (hmem S).1).continuous
      (cx_hasCompactSupport (hmem S).2), ih, cx_smul, paperFT_smul, paperFT_cx_scaleShift_apply,
      sum_insert ha]
    ring

/-- The test component of an orbit combination on a configuration datum. -/
theorem orbitComb_test (Z : ZeroConfig) (hZ : TemperedConfig Z) (x : ScalingCycle) (S : Finset ℝ)
    (c : ℝ → ℝ) :
    (((configScalingDatum Z hZ).orbitComb x S c).2.2 : ℝ → ℝ) =
      ∑ g ∈ S, c g • scaleShift g x.2.2 := by
  simp only [ScalingDatum.orbitComb, Prod.snd_sum, Submodule.coe_sum, Prod.smul_snd,
    Submodule.coe_smul]
  rfl

/-- **The oriented locus is correspondence-stable.** Every orbit combination of a blind test is
blind. -/
theorem blindOffLine_orbitTest {Z : ZeroConfig} {f : ℝ → ℝ} (hf : f ∈ realTests)
    (hb : BlindOffLine Z f) (S : Finset ℝ) (c : ℝ → ℝ) :
    BlindOffLine Z (∑ g ∈ S, c g • scaleShift g f) := fun ρ hρ hre => by
  rcases hb ρ hρ hre with h | h
  · left; rw [paperFT_orbitTest hf, h, mul_zero]
  · right; rw [paperFT_orbitTest hf, h, mul_zero]

/-- **Blindness orients.** On every tempered configuration a cycle whose test is blind to the
off-line zeros has the orbit Hodge index. -/
theorem orbitHodgeIndex_of_blindOffLine (Z : ZeroConfig) (hZ : TemperedConfig Z) (x : ScalingCycle)
    (hb : BlindOffLine Z x.2.2) : (configScalingDatum Z hZ).OrbitHodgeIndex x := by
  rw [ScalingDatum.orbitHodgeIndex_iff_defect_nonneg]
  intro S c
  change 0 ≤ (configSurface Z hZ).defect _ _
  rw [configSurface_defect, configWeil, orbitComb_test]
  have hbF := blindOffLine_orbitTest x.2.2.2 hb S c
  refine SquareRootThreshold.re_W_nonneg_of_summand_nonneg Z fun ρ hρ => ?_
  by_cases hre : ρ.re = 1 / 2
  · exact SquareRootThreshold.re_Wsummand_nonneg_of_onLine Z _ hre
  · rcases hbF ρ hρ hre with h | h
    · rw [ZeroConfig.Wsummand, h, mul_zero, zero_mul, Complex.zero_re]
    · rw [ZeroConfig.Wsummand, h, map_zero, mul_zero, Complex.zero_re]

/-! ### Reality of the Weil form on symmetric configurations -/

theorem gammaOf_conj (ρ : ℂ) : gammaOf (conj ρ) = -conj (gammaOf ρ) := by
  simp only [gammaOf, map_div₀, map_sub, Complex.conj_I, map_one, map_div₀, map_ofNat]
  rw [div_neg, neg_neg]

/-- On a functional-equation-symmetric configuration, complex conjugation permutes the carrier. -/
def conjEquiv {Z : ZeroConfig} (hFE : FESymmetric Z) : Z.carrier ≃ Z.carrier :=
  (fesEquiv hFE).trans (reflectEquiv Z)

theorem conjEquiv_apply {Z : ZeroConfig} (hFE : FESymmetric Z) (τ : Z.carrier) :
    (conjEquiv hFE τ : ℂ) = conj (τ : ℂ) := by
  simp [conjEquiv, fesEquiv_apply, reflectEquiv_apply, fesCarrier, reflectCarrier, reflect]

theorem mult_conj {Z : ZeroConfig} (hFE : FESymmetric Z) {ρ : ℂ} (hρ : ρ ∈ Z.carrier) :
    Z.mult (conj ρ) = Z.mult ρ := by
  have h1 := Z.mult_reflect _ (hFE ρ hρ).1
  have e : reflect (1 - ρ) = conj ρ := by simp [reflect]
  rw [e] at h1
  rw [h1, (hFE ρ hρ).2]

/-- The transform of a real test is conjugation-symmetric: `conj h_f(z) = h_f(−z̄)`. -/
theorem conj_paperFT_cx (f : ℝ → ℝ) (z : ℂ) : conj (paperFT (cx f) z) = paperFT (cx f) (-conj z) := by
  unfold paperFT
  rw [← integral_conj]
  congr 1
  funext u
  rw [map_mul, cx, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- Conjugating a summand of real tests moves it to the conjugate zero. -/
theorem conj_Wsummand_ofReal (Z : ZeroConfig) (hFE : FESymmetric Z) (f g : ℝ → ℝ) {ρ : ℂ}
    (hρ : ρ ∈ Z.carrier) :
    conj (Z.Wsummand (cx f) (cx g) ρ) = Z.Wsummand (cx f) (cx g) (conj ρ) := by
  have hcf : ∀ z, conj (paperFT (cx f) z) = paperFT (cx f) (-conj z) := conj_paperFT_cx f
  have hcg : ∀ z, paperFT (cx g) z = conj (paperFT (cx g) (-conj z)) := fun z => by
    rw [conj_paperFT_cx g, map_neg, conj_conj, neg_neg]
  simp only [ZeroConfig.Wsummand, map_mul, conj_conj, Complex.conj_natCast, mult_conj hFE hρ,
    gammaOf_conj, hcf]
  rw [hcg (conj (gammaOf ρ)), conj_conj, map_neg, conj_conj]

/-- **The Weil form of real tests is real on a symmetric configuration.** -/
theorem W_real_of_fes (Z : ZeroConfig) (hFE : FESymmetric Z) (f g : ℝ → ℝ) :
    conj (Z.W (cx f) (cx g)) = Z.W (cx f) (cx g) := by
  rw [ZeroConfig.W, Complex.conj_tsum, ← (conjEquiv hFE).tsum_eq]
  refine tsum_congr fun τ => ?_
  rw [conjEquiv_apply, conj_Wsummand_ofReal Z hFE f g (hFE.conj_mem τ.2), conj_conj]

/-! ### The self-upgrade: Hasse–Weil at every scale forces blindness -/

/-- The weight of a zero in Square-Root Threshold is the Weil summand. -/
theorem offLineWeight_eq_Wsummand (Z : ZeroConfig) (b : ℝ → ℂ) (t : ℂ) :
    offLineWeight b (Z.mult t) t = Z.Wsummand b b t := by
  have hγ : gammaOf t = (t.im : ℂ) - I * ((t.re - 1 / 2 : ℝ) : ℂ) := gammaOf_eq t
  have hγc : conj (gammaOf t) = (t.im : ℂ) + I * ((t.re - 1 / 2 : ℝ) : ℂ) := by
    rw [hγ, map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]; ring
  rw [offLineWeight, pairWeight, ZeroConfig.Wsummand, hγ, ← hγc, hγ]
  ring

/-- The lag structure of a real test is the exponential sum of its Weil summands. -/
theorem lagStructure_eq (Z : ZeroConfig) {f : ℝ → ℝ} (hf : f ∈ realTests) (v : ℝ) :
    lagStructure Z (cx f) v =
      ∑' ρ : Z.carrier, cexp (v * ((ρ : ℂ) - 1 / 2)) * Z.Wsummand (cx f) (cx f) ρ := by
  rw [lagStructure]
  refine tsum_congr fun ρ => ?_
  rw [EF.paperFT_weilTest (cx_contDiff hf.1).continuous (cx_contDiff hf.1).continuous
    (cx_hasCompactSupport hf.2) (cx_hasCompactSupport hf.2), ZeroConfig.Wsummand]
  have : I * gammaOf ρ * v = v * ((ρ : ℂ) - 1 / 2) := by
    rw [gammaOf, mul_div_cancel₀ _ I_ne_zero]; ring
  rw [this]
  ring

/-- The exponential sum of the summands of a real test at lag `v` is the Weil pairing of its
translate by `v` with itself. -/
theorem tsum_exp_Wsummand_eq_W (Z : ZeroConfig) (f : ℝ → ℝ) (v : ℝ) :
    ∑' ρ : Z.carrier, cexp (v * ((ρ : ℂ) - 1 / 2)) * Z.Wsummand (cx f) (cx f) ρ =
      Z.W (cx (scaleShift v f)) (cx f) := by
  rw [ZeroConfig.W]
  refine tsum_congr fun ρ => ?_
  have h := Wsummand_scaleShift Z v 0 f f ρ
  rw [scaleShift_zero, Complex.ofReal_zero, sub_zero] at h
  exact h.symm

theorem W_scaleShift_neg_eq (Z : ZeroConfig) (f : ℝ → ℝ) (v : ℝ) :
    Z.W (cx (scaleShift (-v) f)) (cx f) = Z.W (cx f) (cx (scaleShift v f)) := by
  rw [ZeroConfig.W, ZeroConfig.W]
  refine tsum_congr fun ρ => ?_
  have h1 := Wsummand_scaleShift Z (-v) 0 f f ρ
  have h2 := Wsummand_scaleShift Z 0 v f f ρ
  rw [scaleShift_zero] at h1 h2
  rw [h1, h2]
  congr 2
  push_cast
  ring

/-- **The self-upgrade.** On a functional-equation-symmetric tempered configuration, a cycle whose
orbit satisfies the Hasse–Weil bound at every scale is blind to the off-line zeros. -/
theorem blindOffLine_of_hasseWeil (Z : ZeroConfig) (hZ : TemperedConfig Z) (hFE : FESymmetric Z)
    (x : ScalingCycle) (hHW : ∀ v : ℝ, (configScalingDatum Z hZ).HasseWeilAt x v) :
    BlindOffLine Z x.2.2 := by
  set f : ℝ → ℝ := (x.2.2 : ℝ → ℝ) with hfdef
  have hf : f ∈ realTests := x.2.2.2
  set b : ℝ → ℂ := cx f with hbdef
  intro ρ hρ hre
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  -- a zero right of the line with nonzero weight
  have hw : ∀ t ∈ Z.carrier, paperFT b (gammaOf t) ≠ 0 → paperFT b (conj (gammaOf t)) ≠ 0 →
      offLineWeight b (Z.mult t) t ≠ 0 := fun t ht ha hb' => by
    rw [offLineWeight_eq_Wsummand, ZeroConfig.Wsummand]
    have hm : (Z.mult t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := Z.one_le_mult t ht; omega)
    exact mul_ne_zero (mul_ne_zero hm ha) ((map_ne_zero _).mpr hb')
  obtain ⟨t, ht, hqt⟩ : ∃ t ∈ SquareRootThreshold.rightZeros Z, offLineWeight b (Z.mult t) t ≠ 0 := by
    rcases lt_or_gt_of_ne hre with hlt | hgt
    · refine ⟨reflect ρ, ⟨Z.reflect_mem _ hρ, by simp [reflect]; linarith⟩, ?_⟩
      refine hw _ (Z.reflect_mem _ hρ) ?_ ?_
      · rwa [gammaOf_reflect]
      · rwa [gammaOf_reflect, conj_conj]
    · exact ⟨ρ, ⟨hρ, hgt⟩, hw ρ hρ h1 h2⟩
  obtain ⟨t₀, ht₀, him₀, hq₀, htop⟩ := exists_top_at_height Z ht
    (fun z => offLineWeight b (Z.mult z) z ≠ 0) hqt
  obtain ⟨A, -, hA⟩ := exists_radius_of_hasCompactSupport (cx_hasCompactSupport hf.2)
  have hbs : ∀ u, b u ≠ 0 → |u| ≤ A := fun u hu => by
    by_contra h
    exact hu (hA u (not_le.mp h))
  obtain ⟨v, -, hv⟩ := exists_minor_fails_of_top Z hZ (cx_contDiff hf.1) hbs ht₀ hq₀
    fun t' ht' him' hq' => htop t' ht' (him'.trans him₀) hq'
  -- the lag structure is the real orbit correlation
  set S : ℝ → ℂ := fun w => Z.W (cx (scaleShift w f)) (cx f) with hS
  have hlag : ∀ w, lagStructure Z b w = S w := fun w => by
    rw [hbdef, lagStructure_eq Z hf, tsum_exp_Wsummand_eq_W]
  have hreal : ∀ w, conj (S w) = S w := fun w => W_real_of_fes Z hFE _ _
  have hneg : S (-v) = S v := by
    rw [hS]
    dsimp only
    rw [W_scaleShift_neg_eq, ← W_conj_symm Z (cx f) (cx (scaleShift v f)), W_real_of_fes Z hFE]
  have hcorr : ∀ w, (configScalingDatum Z hZ).orbitCorr x w = (S w).re := fun w => by
    rw [configScalingDatum_orbitCorr_eq, tsum_exp_Wsummand_eq_W]
  rw [hlag, hlag, hlag, hneg, hreal] at hv
  have hSv : S v = ((S v).re : ℂ) := by
    conv_lhs => rw [← Complex.re_add_im (S v)]
    have him : (S v).im = 0 := by
      have := congrArg Complex.im (hreal v)
      rw [Complex.conj_im] at this
      linarith
    rw [him]; simp
  rw [← two_mul, norm_mul, hSv, Complex.norm_real, Real.norm_eq_abs] at hv
  have hHWv := hHW v
  rw [ScalingDatum.HasseWeilAt, hcorr, hcorr] at hHWv
  norm_num at hv
  linarith

/-- **The orientation theorem.** On a functional-equation-symmetric tempered configuration, for
every cycle: Hasse–Weil at every scale ⟺ orbit Hodge index ⟺ blindness to the off-line zeros. -/
theorem orientation_tfae (Z : ZeroConfig) (hZ : TemperedConfig Z) (hFE : FESymmetric Z)
    (x : ScalingCycle) :
    List.TFAE [∀ v : ℝ, (configScalingDatum Z hZ).HasseWeilAt x v,
      (configScalingDatum Z hZ).OrbitHodgeIndex x, BlindOffLine Z x.2.2] := by
  tfae_have 1 → 3 := blindOffLine_of_hasseWeil Z hZ hFE x
  tfae_have 3 → 2 := orbitHodgeIndex_of_blindOffLine Z hZ x
  tfae_have 2 → 1 := fun h v => (configScalingDatum Z hZ).hasseWeilAt_of_orbitHodgeIndex h v
  tfae_finish

/-! ### One generic orbit decides -/

/-- A real test whose transform vanishes at no zero of `Z`. -/
def RealSpectrallyGeneric (Z : ZeroConfig) (f : ℝ → ℝ) : Prop :=
  ∀ ρ ∈ Z.carrier, paperFT (cx f) (gammaOf ρ) ≠ 0

/-- A spectrally generic test is blind only when there are no off-line zeros. -/
theorem onLine_iff_blindOffLine_of_generic (Z : ZeroConfig) {f : ℝ → ℝ}
    (hgen : RealSpectrallyGeneric Z f) :
    BlindOffLine Z f ↔ ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  constructor
  · intro hb ρ hρ
    by_contra hre
    rcases hb ρ hρ hre with h | h
    · exact hgen ρ hρ h
    · rw [← gammaOf_reflect] at h
      exact hgen _ (Z.reflect_mem _ hρ) h
  · intro hon ρ hρ hre
    exact absurd (hon ρ hρ) hre

/-- **One generic orbit decides the critical line.** -/
theorem onLine_iff_hasseWeil_of_generic (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hFE : FESymmetric Z) (x : ScalingCycle) (hgen : RealSpectrallyGeneric Z x.2.2) :
    (∀ v : ℝ, (configScalingDatum Z hZ).HasseWeilAt x v) ↔ ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  exact ((orientation_tfae Z hZ hFE x).out 0 2).trans (onLine_iff_blindOffLine_of_generic Z hgen)

/-! ### Real generic tests exist -/

/-- A real smooth bump of positive mass. -/
def realBump : ℝ → ℝ :=
  fun u => ({ rIn := 1, rOut := 2, rIn_pos := one_pos, rIn_lt_rOut := one_lt_two } :
    ContDiffBump (0 : ℝ)) u

theorem realBump_mem : realBump ∈ realTests :=
  ⟨ContDiffBump.contDiff _, ContDiffBump.hasCompactSupport _⟩

theorem paperFT_realBump_zero : paperFT (cx realBump) 0 ≠ 0 := by
  have hpos : 0 < ∫ u, realBump u := ContDiffBump.integral_pos _
  simp only [paperFT, mul_zero, zero_mul, Complex.exp_zero, mul_one, cx]
  rw [integral_complex_ofReal]
  exact_mod_cast hpos.ne'

/-- The dilation `u ↦ f(u/λ)`. -/
def dilateTest (l : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun u => f (l⁻¹ * u)

theorem dilateTest_mem {l : ℝ} (hl : l ≠ 0) {f : ℝ → ℝ} (hf : f ∈ realTests) :
    dilateTest l f ∈ realTests :=
  ⟨hf.1.comp (contDiff_const.mul contDiff_id),
    hf.2.comp_homeomorph (Homeomorph.mulLeft₀ l⁻¹ (inv_ne_zero hl))⟩

/-- **Dilation rescales the transform**: `h_{f(·/λ)}(z) = |λ| h_f(λz)`. -/
theorem paperFT_dilateTest {l : ℝ} (hl : l ≠ 0) (f : ℝ → ℝ) (z : ℂ) :
    paperFT (cx (dilateTest l f)) z = |l| * paperFT (cx f) (l * z) := by
  set G : ℝ → ℂ := fun w => (f w : ℂ) * Complex.exp (Complex.I * ((l : ℂ) * z) * (w : ℂ))
  have h1 : (fun u : ℝ => cx (dilateTest l f) u * Complex.exp (Complex.I * z * (u : ℂ))) =
      fun u => G (l⁻¹ * u) := by
    funext u
    have hlc : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl
    simp only [G, cx, dilateTest]
    congr 2
    push_cast
    field_simp
  rw [paperFT, h1, MeasureTheory.Measure.integral_comp_mul_left, inv_inv, paperFT]
  simp only [G, Complex.real_smul, cx]

/-- **Real generic tests exist.** A suitable dilation of the real bump has transform vanishing at no
point of `Z`: the dilations killing it at some zero form a countable set. -/
theorem exists_realSpectrallyGeneric (Z : ZeroConfig) :
    ∃ f ∈ realTests, RealSpectrallyGeneric Z f := by
  have hd : Differentiable ℂ (paperFT (cx realBump)) :=
    RHTower.EvenSector.differentiable_paperFT_of_compact (cx_contDiff realBump_mem.1).continuous
      (cx_hasCompactSupport realBump_mem.2)
  have hcount := HTGeometry.countable_zeros_of_entire_nonzero hd paperFT_realBump_zero
  set B : Set ℝ := {0} ∪ ⋃ ρ ∈ Z.carrier,
    (fun l : ℝ => (l : ℂ) * gammaOf ρ) ⁻¹' {t | paperFT (cx realBump) t = 0} with hB
  have hBc : B.Countable := by
    refine (Set.countable_singleton 0).union
      ((SquareRootThreshold.carrier_countable Z).biUnion fun ρ _ => ?_)
    by_cases hγ : gammaOf ρ = 0
    · refine Set.Countable.mono (fun l hl => ?_) (Set.countable_empty : (∅ : Set ℝ).Countable)
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hγ, mul_zero] at hl
      exact paperFT_realBump_zero hl
    · exact hcount.preimage fun a b h => by
        simpa [mul_left_inj' hγ] using h
  obtain ⟨l, hl⟩ : ∃ l, l ∉ B := by
    by_contra h
    push Not at h
    exact Cardinal.not_countable_real (hBc.mono fun l _ => h l)
  have hl0 : l ≠ 0 := fun h => hl (Or.inl h)
  refine ⟨dilateTest l realBump, dilateTest_mem hl0 realBump_mem, fun ρ hρ h0 => hl (Or.inr ?_)⟩
  rw [paperFT_dilateTest hl0] at h0
  have habs : ((|l| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr hl0
  exact Set.mem_biUnion hρ ((mul_eq_zero.mp h0).resolve_left habs)

/-! ### `ζ` -/

theorem configScalingDatum_zeta_orbitCorr (x : ScalingCycle) (t : ℝ) :
    (configScalingDatum zetaZeroConfig temperedConfig_zetaZeroConfig).orbitCorr x t =
      zetaScalingDatum.orbitCorr x t := by
  simp only [ScalingDatum.orbitCorr]
  change (configSurface zetaZeroConfig temperedConfig_zetaZeroConfig).defect _ _ =
    scalingSurface.defect _ _
  rw [configSurface_zeta_eq]
  rfl

theorem zeta_hasseWeilAt_iff (x : ScalingCycle) (t : ℝ) :
    zetaScalingDatum.HasseWeilAt x t ↔
      (configScalingDatum zetaZeroConfig temperedConfig_zetaZeroConfig).HasseWeilAt x t := by
  simp only [ScalingDatum.HasseWeilAt, configScalingDatum_zeta_orbitCorr]

/-- **The oriented cycles of `ℤ`.** A cycle of the scaling surface satisfies the Hasse–Weil bound
along its whole orbit iff its transform vanishes at one point of every off-line pair of zeros of
`ζ`. -/
theorem zeta_orientation_iff (x : ScalingCycle) :
    (∀ t : ℝ, zetaScalingDatum.HasseWeilAt x t) ↔ BlindOffLine zetaZeroConfig x.2.2 := by
  simp only [zeta_hasseWeilAt_iff]
  exact (orientation_tfae zetaZeroConfig temperedConfig_zetaZeroConfig fesSymmetric_zetaZeroConfig
    x).out 0 2

/-- **RH from one generic orbit.** For a spectrally generic real test, RH holds iff its orbit
satisfies the Hasse–Weil bound at every scale. -/
theorem riemannHypothesis_iff_hasseWeil_of_generic (x : ScalingCycle)
    (hgen : RealSpectrallyGeneric zetaZeroConfig x.2.2) :
    RiemannHypothesis ↔ ∀ t : ℝ, zetaScalingDatum.HasseWeilAt x t := by
  rw [zeta_orientation_iff, onLine_iff_blindOffLine_of_generic _ hgen]
  constructor
  · intro hRH
    have hall := (zetaScalingDatum.hodgeIndex_tfae.out 0 2).mp
      (zetaScalingDatum_hodgeIndex_iff.mpr hRH)
    have hb := blindOffLine_of_hasseWeil zetaZeroConfig temperedConfig_zetaZeroConfig
      fesSymmetric_zetaZeroConfig x fun v => (zeta_hasseWeilAt_iff x v).mp (hall x v)
    exact (onLine_iff_blindOffLine_of_generic _ hgen).mp hb
  · intro hon
    apply zetaScalingDatum_hodgeIndex_iff.mp
    have h := configSurface_hodgeIndex_of_onLine zetaZeroConfig temperedConfig_zetaZeroConfig hon
    rw [configSurface_zeta_eq] at h
    exact h


/-- **One orbit decides RH.** There is a real test whose orbit satisfies the Hasse–Weil bound at
every scale iff RH holds. -/
theorem exists_orbit_deciding_riemannHypothesis :
    ∃ x : ScalingCycle, RiemannHypothesis ↔ ∀ t : ℝ, zetaScalingDatum.HasseWeilAt x t := by
  obtain ⟨f, hf, hgen⟩ := exists_realSpectrallyGeneric zetaZeroConfig
  exact ⟨(0, 0, ⟨f, hf⟩), riemannHypothesis_iff_hasseWeil_of_generic _ hgen⟩

end GaloisForLFunctions.ArithmeticOrientationGeometry
