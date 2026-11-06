import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheNearLineZerosCannotBlockTheCamera
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheBlaschkeFactorBoundsTheCauchyForm

/-!
# The hyperbolic camera sees isolated zeros

At a fixed height `t` the deep part of the zero field is an exponential sum in the centre:

`Σ_{ρ∈D} m_ρ K̂_{δ,y}(γ_ρ − t − i b_ρ) = Σ_{ρ∈D} C_ρ e^{λ_ρ y}`, `λ_ρ = ρ − ½ − it`, `C_ρ = m_ρ v̂(δ(γ_ρ − t − i b_ρ))`

(`term_eq_cameraWeight_mul_exp`). Its energy over the centres `y ∈ [2δ, (1−2c)L]` is therefore a difference of Cauchy forms,
bounded below by the Blaschke factor of `ρ` in `D`:

`|C_ρ|² e^{2bY} Π_{ρ'≠ρ} ϱ(ρ, ρ')² / (2b)`, `ϱ(ρ, ρ') = |ρ − ρ'|/|ρ + ρ̄' − 1|`,

and `ϱ` is the pseudo-hyperbolic distance of the half plane `Re s > ½`; the height `t` cancels (`norm_blaschke_cameraNode`).

Integrating the camera equation over the centres and the mean value theorem over the heights bounds the same energy by
`≪ L T/c²` on average (`integral_cameraEnergy_le`). So zeros of depth `≈ α/L` with Blaschke factor at least `B₀` obey

`#S ≪_c (α + 1) T L e^{−2(1−3c)α} / B₀²`, up to an exceptional set of heights (`exists_card_hyperbolic_zeros_le`).

**What this removes.** The Turán camera needs a bounded number of competitors in a sector and small mass outside it. Here the
coefficients and positions of the zeros of `D` are arbitrary, and neither sector nor count enters. A competitor costs only its
factor `ϱ`, which is close to `1` for far zeros, much deeper zeros and much shallower zeros. Only zeros at hyperbolic distance
`O(1)` from `ρ`, that is comparably deep and within `≍ b_ρ` in ordinate, cost anything.

The remaining conditions of `HyperbolicAtHeight` bound the noise of the zeros outside `D` and the coefficient mass of `D` at the low centre.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped ComplexConjugate
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

variable {v : ℝ → ℝ}

/-! ### Nodes, weights and the hyperbolic ratio -/

/-- The pseudo-hyperbolic ratio `|ρ − ρ'|/|ρ + ρ̄' − 1|` of the half plane `Re s > ½`. -/
def hyperbolicRatio (ρ ρ' : ℂ) : ℝ := ‖ρ - ρ'‖ / ‖ρ + conj ρ' - 1‖

/-- The node `λ_ρ = ρ − ½ − it` of a zero at the height `t`. -/
def cameraNode (t : ℝ) (ρ : zetaZeroConfig.carrier) : ℂ := (ρ : ℂ) - 1 / 2 - t * I

/-- The coefficient `C_ρ = m_ρ v̂(δ(γ_ρ − t − i b_ρ))` of a zero. -/
def cameraWeight (v : ℝ → ℝ) (δ t : ℝ) (ρ : zetaZeroConfig.carrier) : ℂ :=
  (zetaZeroConfig.mult ρ : ℂ) * paperFT (cplx v) ((gammaOf (ρ : ℂ) - t) * δ)

theorem cameraNode_re (t : ℝ) (ρ : zetaZeroConfig.carrier) :
    (cameraNode t ρ).re = (ρ : ℂ).re - 1 / 2 := by
  simp [cameraNode]

/-- The height cancels: the Blaschke factor at the camera nodes is the pseudo-hyperbolic ratio. -/
theorem norm_blaschke_cameraNode (t : ℝ) (j i : zetaZeroConfig.carrier) :
    ‖blaschke (cameraNode t) j i‖ = hyperbolicRatio (i : ℂ) (j : ℂ) := by
  unfold blaschke hyperbolicRatio cameraNode
  rw [norm_div]
  congr 2
  · ring
  · simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, map_div₀, map_one, map_ofNat]
    ring

/-- The camera is an exponential in its centre. -/
theorem term_eq_cameraWeight_mul_exp {δ : ℝ} (hδ : 0 < δ) (t y : ℝ) (ρ : zetaZeroConfig.carrier) :
    (zetaZeroConfig.mult ρ : ℂ) * paperFT (cameraTest v δ y) (gammaOf (ρ : ℂ) - t) =
      cameraWeight v δ t ρ * cexp (cameraNode t ρ * y) := by
  have e : I * (gammaOf (ρ : ℂ) - t) * y = cameraNode t ρ * y := by
    unfold gammaOf cameraNode
    field_simp
  rw [paperFT_cameraTest hδ, e, cameraWeight]
  ring

/-- `|C_ρ| e^{b y}` is the size of the term at the centre `y`. -/
theorem norm_cameraWeight_mul_exp_le (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) (t y : ℝ) (ρ : zetaZeroConfig.carrier) :
    ‖cameraWeight v δ t ρ‖ * Real.exp ((cameraNode t ρ).re * y) ≤
      (zetaZeroConfig.mult ρ : ℝ) * (profileMass v * companionWeight δ y t (ρ : ℂ)) := by
  have h := congrArg norm (term_eq_cameraWeight_mul_exp (v := v) hδ t y ρ)
  rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_exp] at h
  have e : (cameraNode t ρ * (y : ℂ)).re = (cameraNode t ρ).re * y := by simp
  rw [e] at h
  rw [← h]
  exact mul_le_mul_of_nonneg_left (norm_paperFT_companion_le hv hsupp hδ y t (ρ : ℂ))
    (Nat.cast_nonneg _)

/-- In the sector a zero's coefficient is at least `½ e^{−bδ} ∫v`. -/
theorem norm_cameraWeight_ge (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    (hv0 : ∀ u, 0 ≤ v u) {δ : ℝ} (hδ : 0 < δ) {t : ℝ} {ρ : zetaZeroConfig.carrier}
    (hb : 1 / 2 ≤ (ρ : ℂ).re) (ht : |t - (ρ : ℂ).im| ≤ 1 / (10 * δ)) :
    1 / 2 * Real.exp (-(((ρ : ℂ).re - 1 / 2) * δ)) * (∫ u, v u) ≤ ‖cameraWeight v δ t ρ‖ := by
  have hre : |(gammaOf (ρ : ℂ) - t).re| * δ ≤ 1 / 10 := by
    rw [gammaOf_sub_re, abs_sub_comm]
    have h1 := mul_le_mul_of_nonneg_right ht hδ.le
    have e : 1 / (10 * δ) * δ = 1 / 10 := by field_simp
    linarith
  have h := re_paperFT_profile_ge hv hsupp hv0 hδ hre
  have him : |(gammaOf (ρ : ℂ) - t).im| = (ρ : ℂ).re - 1 / 2 := by
    rw [gammaOf_sub_im, abs_neg, abs_of_nonneg (by linarith)]
  rw [him] at h
  have hm1 : (1 : ℝ) ≤ zetaZeroConfig.mult ρ := by
    exact_mod_cast zetaZeroConfig.one_le_mult ρ ρ.2
  have hn : (paperFT (cplx v) ((gammaOf (ρ : ℂ) - t) * δ)).re ≤
      ‖paperFT (cplx v) ((gammaOf (ρ : ℂ) - t) * δ)‖ :=
    (le_abs_self _).trans (Complex.abs_re_le_norm _)
  rw [cameraWeight, norm_mul, Complex.norm_natCast]
  exact (h.trans hn).trans (le_mul_of_one_le_left (norm_nonneg _) hm1)

/-! ### The polynomial at a fixed length -/

/-- The camera polynomial at a fixed length, jointly continuous in the centre and the height. -/
def cameraPolyAt (v : ℝ → ℝ) (δ y : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  edPoly (cameraCoeff v δ y) (Finset.Icc 1 N) (displacedLinePt 0 t)

theorem cameraPoly_eq_cameraPolyAt (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) {δ y : ℝ} (hδ : 0 < δ) {N : ℕ}
    (hN : cameraLength δ y ≤ N) (t : ℝ) : cameraPoly v δ y t = cameraPolyAt v δ y N t := by
  unfold cameraPoly cameraPolyAt edPoly
  refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hN) fun n hn hnot => ?_
  obtain ⟨hn1, -⟩ := Finset.mem_Icc.mp hn
  have hlt : cameraLength δ y < n := by
    by_contra h
    exact hnot (Finset.mem_Icc.mpr ⟨hn1, not_lt.mp h⟩)
  have h0 : cameraTest v δ y (Real.log n) = 0 := by
    apply cameraTest_eq_zero hsupp hδ
    have h1 : Real.exp (y + δ) < n := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hlt)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have h2 : y + δ < Real.log n := (Real.lt_log_iff_exp_lt hnpos).2 h1
    rw [abs_of_pos (by linarith)]
    linarith
  simp [cameraCoeff, h0]

theorem continuous_cameraPolyAt (hv : Continuous v) (δ : ℝ) (N : ℕ) :
    Continuous fun p : ℝ × ℝ => cameraPolyAt v δ p.1 N p.2 := by
  unfold cameraPolyAt edPoly
  refine continuous_finsetSum _ fun n hn => ?_
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hne : ((n : ℝ) : ℂ) ≠ 0 := by
    have : (n : ℝ) ≠ 0 := by
      have : 0 < n := hn1
      positivity
    exact_mod_cast this
  have h1 : Continuous fun p : ℝ × ℝ => cameraCoeff v δ p.1 n := by
    unfold cameraCoeff cameraTest
    refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
    exact (hv.comp ((continuous_const.sub continuous_fst).div_const δ)).div_const δ
  have h2 : Continuous fun p : ℝ × ℝ => ((n : ℝ) : ℂ) ^ (-displacedLinePt 0 p.2) := by
    refine Continuous.const_cpow ?_ (Or.inl hne)
    unfold displacedLinePt
    fun_prop
  exact h1.mul h2

/-- The energy `∫_{y₀}^{Y} |C_y(t)|² dy` of the camera polynomial over the centres. -/
def cameraEnergy (v : ℝ → ℝ) (δ y₀ Y : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∫ y in y₀..Y, ‖cameraPolyAt v δ y N t‖ ^ 2

theorem cameraEnergy_nonneg {y₀ Y : ℝ} (hy : y₀ ≤ Y) (δ : ℝ) (N : ℕ) (t : ℝ) :
    0 ≤ cameraEnergy v δ y₀ Y N t :=
  intervalIntegral.integral_nonneg hy fun _ _ => by positivity

theorem continuous_cameraEnergy (hv : Continuous v) (δ y₀ Y : ℝ) (N : ℕ) :
    Continuous (cameraEnergy v δ y₀ Y N) := by
  have h : Continuous (Function.uncurry fun (t y : ℝ) => ‖cameraPolyAt v δ y N t‖ ^ 2) := by
    have h1 := continuous_cameraPolyAt hv δ N
    exact ((h1.comp (continuous_snd.prodMk continuous_fst)).norm.pow 2)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h _ _

/-- **The mean of the energy.** Fubini and the mean value theorem at every centre. -/
theorem integral_cameraEnergy_le (hv : Continuous v) {δ y₀ Y T B : ℝ} (hy : y₀ ≤ Y) {N : ℕ}
    (hB : ∀ y ∈ Icc y₀ Y, ∫ t in T..(2 * T), ‖cameraPolyAt v δ y N t‖ ^ 2 ≤ B) :
    ∫ t in T..(2 * T), cameraEnergy v δ y₀ Y N t ≤ (Y - y₀) * B := by
  have hcont : Continuous (Function.uncurry fun (y t : ℝ) => ‖cameraPolyAt v δ y N t‖ ^ 2) :=
    (continuous_cameraPolyAt hv δ N).norm.pow 2
  have hswap : (∫ t in T..(2 * T), ∫ y in y₀..Y, ‖cameraPolyAt v δ y N t‖ ^ 2) =
      ∫ y in y₀..Y, ∫ t in T..(2 * T), ‖cameraPolyAt v δ y N t‖ ^ 2 := by
    symm
    apply intervalIntegral_intervalIntegral_swap
    refine (hcont.continuousOn.integrableOn_compact (μ := volume)
      ((isCompact_uIcc (a := y₀) (b := Y)).prod
        (isCompact_uIcc (a := T) (b := 2 * T)))).mono_set ?_
    exact Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc
  unfold cameraEnergy
  rw [hswap]
  have hc2 : Continuous fun y : ℝ => ∫ t in T..(2 * T), ‖cameraPolyAt v δ y N t‖ ^ 2 :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcont _ _
  have h := intervalIntegral.integral_mono_on (μ := volume) hy (hc2.intervalIntegrable _ _)
    (intervalIntegrable_const (c := B)) hB
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  exact h

/-! ### One height -/

/-- The field minus the part on `D` is bounded by the finite masses outside `D`. -/
theorem norm_zeroField_sub_expField_le (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    {δ y t Ξ : ℝ} (hδ : 0 < δ) (hyδ : δ < y) (D : Finset zetaZeroConfig.carrier)
    (h : ∀ F : Finset zetaZeroConfig.carrier, Disjoint F D →
      profileMass v * ∑ ρ' ∈ F, (zetaZeroConfig.mult ρ' : ℝ) * companionWeight δ y t ρ' ≤ Ξ) :
    ‖zeroField v δ y t - expField D (cameraNode t) (cameraWeight v δ t) y‖ ≤ Ξ := by
  classical
  obtain ⟨hsum, -⟩ := camera_explicit_formula hv hsupp hδ hyδ t
  have htail := norm_tsum_sub_sum_le hsum D (c := Ξ) (fun F hF => by
    refine le_trans ?_ (h F hF)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ρ' _ => ?_
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ' := Nat.cast_nonneg _
    have hk := norm_paperFT_companion_le hv hsupp hδ y t (ρ' : ℂ)
    rw [norm_mul, Complex.norm_natCast]
    calc (zetaZeroConfig.mult ρ' : ℝ) * ‖paperFT (cameraTest v δ y) (gammaOf (ρ' : ℂ) - t)‖
        ≤ (zetaZeroConfig.mult ρ' : ℝ) * (profileMass v * companionWeight δ y t (ρ' : ℂ)) :=
          mul_le_mul_of_nonneg_left hk hm
      _ = _ := by ring)
  have hfinite : ∑ ρ' ∈ D, (zetaZeroConfig.mult ρ' : ℂ) *
      paperFT (cameraTest v δ y) (gammaOf (ρ' : ℂ) - t) =
      expField D (cameraNode t) (cameraWeight v δ t) y :=
    Finset.sum_congr rfl fun ρ' _ => term_eq_cameraWeight_mul_exp hδ t y ρ'
  rw [hfinite] at htail
  exact htail

/-- **The energy chain at one height.** The Blaschke lower bound for the deep part of the field against the camera energy. -/
theorem energy_chain (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) (hv0 : ∀ u, 0 ≤ v u)
    {δ y₀ Y t b₀ B₀ Ξ E₀ : ℝ} {N : ℕ} (hδ : 0 < δ) (hy₀δ : δ < y₀) (hy : y₀ ≤ Y) (hb₀ : 0 < b₀)
    (hB₀ : 0 ≤ B₀) (hsupp' : ∀ y ∈ Icc y₀ Y, cameraLength δ y ≤ N)
    (hclose : ∀ y ∈ Icc y₀ Y, ‖zeroField v δ y t + cameraPoly v δ y t‖ ≤ E₀)
    {D : Finset zetaZeroConfig.carrier} {ρ : zetaZeroConfig.carrier} (hρ : ρ ∈ D)
    (hdeep : ∀ ρ' ∈ D, b₀ ≤ (ρ' : ℂ).re - 1 / 2)
    (hprod : B₀ ≤ ∏ ρ' ∈ D.erase ρ, hyperbolicRatio (ρ : ℂ) (ρ' : ℂ))
    (hsec : |t - (ρ : ℂ).im| ≤ 1 / (10 * δ))
    (hlow : profileMass v * ∑ ρ' ∈ D, (zetaZeroConfig.mult ρ' : ℝ) * companionWeight δ y₀ t ρ' ≤ Ξ)
    (hnoise : ∀ y ∈ Icc y₀ Y, ∀ F : Finset zetaZeroConfig.carrier, Disjoint F D →
      profileMass v * ∑ ρ' ∈ F, (zetaZeroConfig.mult ρ' : ℝ) * companionWeight δ y t ρ' ≤ Ξ) :
    (∫ u, v u) ^ 2 * Real.exp (2 * ((ρ : ℂ).re - 1 / 2) * (Y - δ)) * B₀ ^ 2 /
          (8 * ((ρ : ℂ).re - 1 / 2)) - Ξ ^ 2 / (2 * b₀) ≤
      3 * cameraEnergy v δ y₀ Y N t + 3 * (Y - y₀) * (E₀ ^ 2 + Ξ ^ 2) := by
  classical
  have hI0 : 0 ≤ ∫ u, v u := integral_nonneg hv0
  have hbρ : b₀ ≤ (ρ : ℂ).re - 1 / 2 := hdeep ρ hρ
  have hb : 0 < (ρ : ℂ).re - 1 / 2 := by linarith
  have hlam : ∀ k ∈ D, b₀ ≤ (cameraNode t k).re := fun k hk => by
    rw [cameraNode_re]
    exact hdeep k hk
  have hen := energy_ge_blaschke D hb₀ hlam hρ (cameraWeight v δ t) y₀ Y
  simp only [norm_blaschke_cameraNode, cameraNode_re] at hen
  -- the coefficient of `ρ`
  have hw := norm_cameraWeight_ge hv hsupp hv0 hδ (by linarith : 1 / 2 ≤ (ρ : ℂ).re) hsec
  have hprod0 : 0 ≤ ∏ ρ' ∈ D.erase ρ, hyperbolicRatio (ρ : ℂ) (ρ' : ℂ) := hB₀.trans hprod
  have hmain : (∫ u, v u) ^ 2 * Real.exp (2 * ((ρ : ℂ).re - 1 / 2) * (Y - δ)) * B₀ ^ 2 /
        (8 * ((ρ : ℂ).re - 1 / 2)) ≤
      ‖cameraWeight v δ t ρ‖ ^ 2 * Real.exp (2 * ((ρ : ℂ).re - 1 / 2) * Y) *
        (∏ ρ' ∈ D.erase ρ, hyperbolicRatio (ρ : ℂ) (ρ' : ℂ)) ^ 2 / (2 * ((ρ : ℂ).re - 1 / 2)) := by
    have h1 : (1 / 2 * Real.exp (-(((ρ : ℂ).re - 1 / 2) * δ)) * (∫ u, v u)) ^ 2 ≤
        ‖cameraWeight v δ t ρ‖ ^ 2 := pow_le_pow_left₀ (by positivity) hw 2
    have h2 : B₀ ^ 2 ≤ (∏ ρ' ∈ D.erase ρ, hyperbolicRatio (ρ : ℂ) (ρ' : ℂ)) ^ 2 :=
      pow_le_pow_left₀ hB₀ hprod 2
    have h3 : (1 / 2 * Real.exp (-(((ρ : ℂ).re - 1 / 2) * δ)) * (∫ u, v u)) ^ 2 *
        Real.exp (2 * ((ρ : ℂ).re - 1 / 2) * Y) =
        (∫ u, v u) ^ 2 / 4 * Real.exp (2 * ((ρ : ℂ).re - 1 / 2) * (Y - δ)) := by
      rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
      have e : 2 * ((ρ : ℂ).re - 1 / 2) * (Y - δ) =
          ((2 : ℕ) : ℝ) * -(((ρ : ℂ).re - 1 / 2) * δ) + 2 * ((ρ : ℂ).re - 1 / 2) * Y := by
        push_cast
        ring
      rw [e, Real.exp_add]
      ring
    have h4 : (∫ u, v u) ^ 2 * Real.exp (2 * ((ρ : ℂ).re - 1 / 2) * (Y - δ)) * B₀ ^ 2 /
        (8 * ((ρ : ℂ).re - 1 / 2)) =
        (1 / 2 * Real.exp (-(((ρ : ℂ).re - 1 / 2) * δ)) * (∫ u, v u)) ^ 2 *
          Real.exp (2 * ((ρ : ℂ).re - 1 / 2) * Y) * B₀ ^ 2 / (2 * ((ρ : ℂ).re - 1 / 2)) := by
      rw [h3]
      field_simp
      ring
    rw [h4]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le) h2 (sq_nonneg _)
      (by positivity)
  -- the coefficient mass at the low centre
  have hmass : ∑ k ∈ D, ‖cameraWeight v δ t k‖ * Real.exp (((k : ℂ).re - 1 / 2) * y₀) ≤ Ξ := by
    refine le_trans ?_ hlow
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have h := norm_cameraWeight_mul_exp_le hv hsupp hδ t y₀ k
    rw [cameraNode_re] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  have hmass0 : 0 ≤ ∑ k ∈ D, ‖cameraWeight v δ t k‖ * Real.exp (((k : ℂ).re - 1 / 2) * y₀) :=
    Finset.sum_nonneg fun k _ => by positivity
  have hmass2 : (∑ k ∈ D, ‖cameraWeight v δ t k‖ * Real.exp (((k : ℂ).re - 1 / 2) * y₀)) ^ 2 /
      (2 * b₀) ≤ Ξ ^ 2 / (2 * b₀) :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hmass0 hmass 2) (by positivity)
  -- the upper bound through the camera equation
  have hF := continuous_expField D (cameraNode t) (cameraWeight v δ t)
  have hP : Continuous fun y : ℝ => ‖cameraPolyAt v δ y N t‖ ^ 2 :=
    ((continuous_cameraPolyAt hv.continuous δ N).comp
      (continuous_id.prodMk continuous_const)).norm.pow 2
  have hupper : ∫ y in y₀..Y, ‖expField D (cameraNode t) (cameraWeight v δ t) y‖ ^ 2 ≤
      ∫ y in y₀..Y, (3 * ‖cameraPolyAt v δ y N t‖ ^ 2 + 3 * (E₀ ^ 2 + Ξ ^ 2)) := by
    refine intervalIntegral.integral_mono_on hy ((hF.norm.pow 2).intervalIntegrable _ _)
      (((continuous_const.mul hP).add continuous_const).intervalIntegrable _ _) fun y hy' => ?_
    have hyδ : δ < y := lt_of_lt_of_le hy₀δ hy'.1
    have h1 := norm_zeroField_sub_expField_le hv hsupp hδ hyδ D (hnoise y hy')
    have h2 := hclose y hy'
    rw [cameraPoly_eq_cameraPolyAt hsupp hδ (hsupp' y hy')] at h2
    set a := ‖cameraPolyAt v δ y N t‖ with ha
    have ha0 : 0 ≤ a := norm_nonneg _
    have h3 : ‖zeroField v δ y t‖ ≤ E₀ + a := by
      have := norm_sub_le (zeroField v δ y t + cameraPolyAt v δ y N t) (cameraPolyAt v δ y N t)
      rw [add_sub_cancel_right] at this
      linarith
    have h4 : ‖expField D (cameraNode t) (cameraWeight v δ t) y‖ ≤ a + E₀ + Ξ := by
      have := norm_sub_norm_le (expField D (cameraNode t) (cameraWeight v δ t) y) (zeroField v δ y t)
      rw [norm_sub_rev] at this
      linarith
    have h5 := pow_le_pow_left₀ (norm_nonneg _) h4 2
    refine h5.trans ?_
    nlinarith [sq_nonneg (a - E₀), sq_nonneg (a - Ξ), sq_nonneg (E₀ - Ξ)]
  have hint : (∫ y in y₀..Y, (3 * ‖cameraPolyAt v δ y N t‖ ^ 2 + 3 * (E₀ ^ 2 + Ξ ^ 2))) =
      3 * cameraEnergy v δ y₀ Y N t + 3 * (Y - y₀) * (E₀ ^ 2 + Ξ ^ 2) := by
    have hi1 : IntervalIntegrable (fun y : ℝ => 3 * ‖cameraPolyAt v δ y N t‖ ^ 2) volume y₀ Y :=
      (continuous_const.mul hP).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun _ : ℝ => 3 * (E₀ ^ 2 + Ξ ^ 2)) volume y₀ Y :=
      intervalIntegrable_const
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    unfold cameraEnergy
    ring
  rw [← hint]
  refine le_trans ?_ hupper
  refine le_trans ?_ hen
  exact sub_le_sub hmain hmass2

/-! ### The count -/

/-- `ρ` is hyperbolically isolated at the height `t`: there is a family `D ∋ ρ` of zeros of depth `≥ b₀` in which `ρ` has Blaschke
factor at least `B₀`, with coefficient mass at most `Ξ` at the low centre and with the zeros outside `D` carrying mass at
most `Ξ` at every centre. The zeros of `D` are otherwise unconstrained. -/
def HyperbolicAtHeight (v : ℝ → ℝ) (δ y₀ Y b₀ B₀ Ξ : ℝ) (ρ : zetaZeroConfig.carrier) (t : ℝ) : Prop :=
  ∃ D : Finset zetaZeroConfig.carrier, ρ ∈ D ∧
    (∀ ρ' ∈ D, b₀ ≤ (ρ' : ℂ).re - 1 / 2) ∧
    B₀ ≤ ∏ ρ' ∈ D.erase ρ, hyperbolicRatio (ρ : ℂ) (ρ' : ℂ) ∧
    profileMass v * ∑ ρ' ∈ D, (zetaZeroConfig.mult ρ' : ℝ) * companionWeight δ y₀ t ρ' ≤ Ξ ∧
    ∀ y ∈ Icc y₀ Y, ∀ F : Finset zetaZeroConfig.carrier, Disjoint F D →
      profileMass v * ∑ ρ' ∈ F, (zetaZeroConfig.mult ρ' : ℝ) * companionWeight δ y t ρ' ≤ Ξ

/-- The main term of the chain at depth `≈ α/L`. -/
theorem main_term_ge {I₀ B₀ b L α c Y δ : ℝ} (hL : 0 < L) (hα : 0 ≤ α) (hc : c < 1 / 3)
    (hb1 : α / L ≤ b) (hb2 : b ≤ (α + 1) / L) (hb0 : 0 < b) (hY : Y - δ = (1 - 3 * c) * L) :
    L * (I₀ ^ 2 * Real.exp (2 * ((1 - 3 * c) * α)) * B₀ ^ 2 / (α + 1)) / 8 ≤
      I₀ ^ 2 * Real.exp (2 * b * (Y - δ)) * B₀ ^ 2 / (8 * b) := by
  have h13 : 0 < 1 - 3 * c := by linarith
  have hα1 : 0 < α + 1 := by linarith
  have hexp : Real.exp (2 * ((1 - 3 * c) * α)) ≤ Real.exp (2 * b * (Y - δ)) := by
    refine Real.exp_le_exp.2 ?_
    rw [hY]
    have h1 : α ≤ b * L := by
      rwa [div_le_iff₀ hL] at hb1
    nlinarith
  have hbL : b * L ≤ α + 1 := by
    rwa [le_div_iff₀ hL] at hb2
  have hdiv : L / (α + 1) ≤ 1 / b := by
    rw [div_le_div_iff₀ hα1 hb0]
    linarith
  have hnn : 0 ≤ I₀ ^ 2 * B₀ ^ 2 := by positivity
  calc L * (I₀ ^ 2 * Real.exp (2 * ((1 - 3 * c) * α)) * B₀ ^ 2 / (α + 1)) / 8
      = I₀ ^ 2 * B₀ ^ 2 * Real.exp (2 * ((1 - 3 * c) * α)) * (L / (α + 1)) / 8 := by ring
    _ ≤ I₀ ^ 2 * B₀ ^ 2 * Real.exp (2 * b * (Y - δ)) * (1 / b) / 8 := by
        gcongr
    _ = _ := by
        field_simp

/-- The closing arithmetic of the chain. -/
theorem energy_threshold {L Θ Ξ E₀ G b₀ A 𝓔 ℓ : ℝ} (hL : 0 < L) (hΞ : Ξ = Θ / 14)
    (hb₀ : b₀ = A / L) (hA : 1 ≤ A) (hE₀0 : 0 ≤ E₀) (hE₀ : 14 * E₀ ≤ Θ) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ L)
    (hG : L * Θ ^ 2 / 8 ≤ G) (hchain : G - Ξ ^ 2 / (2 * b₀) ≤ 3 * 𝓔 + 3 * ℓ * (E₀ ^ 2 + Ξ ^ 2)) :
    L * Θ ^ 2 / 40 ≤ 𝓔 := by
  have hA0 : 0 < A := by linarith
  have h1 : Ξ ^ 2 / (2 * b₀) ≤ L * Θ ^ 2 / 392 := by
    rw [hΞ, hb₀]
    have e : (Θ / 14) ^ 2 / (2 * (A / L)) = L * Θ ^ 2 / 392 / A := by
      field_simp
      ring
    rw [e]
    exact div_le_self (by positivity) hA
  have hE2 : E₀ ^ 2 ≤ Θ ^ 2 / 196 := by
    have : E₀ ≤ Θ / 14 := by linarith
    calc E₀ ^ 2 ≤ (Θ / 14) ^ 2 := pow_le_pow_left₀ hE₀0 this 2
      _ = _ := by ring
  have hΞ2 : Ξ ^ 2 = Θ ^ 2 / 196 := by
    rw [hΞ]
    ring
  have h2 : 3 * ℓ * (E₀ ^ 2 + Ξ ^ 2) ≤ 3 * L * (Θ ^ 2 / 98) := by
    have h3 : E₀ ^ 2 + Ξ ^ 2 ≤ Θ ^ 2 / 98 := by
      rw [hΞ2]
      linarith
    have h4 : 0 ≤ Θ ^ 2 / 98 := by positivity
    calc 3 * ℓ * (E₀ ^ 2 + Ξ ^ 2) ≤ 3 * ℓ * (Θ ^ 2 / 98) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ 3 * L * (Θ ^ 2 / 98) := by
          gcongr
  have hLΘ : 0 ≤ L * Θ ^ 2 := by positivity
  nlinarith

/-- The camera equation on the dyadic range, with a constant depending only on `c`. -/
theorem close_of_scale {C₁ c T L y t : ℝ} (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ δ y t : ℝ, 1 ≤ δ → δ < y → 1 ≤ t → Real.exp (y + δ) ≤ t →
      ‖zeroField v δ y t + cameraPoly v δ y t‖ ≤ C₁ * (1 + Real.log (2 + t) / δ))
    (hc0 : 0 < c) (hc : c < 1) (hT3 : 3 ≤ T) (hL : L = Real.log T) (hδ1 : 1 ≤ c * L)
    (hyδ : c * L < y) (hy : y + c * L ≤ (1 - c) * L) (ht : t ∈ Ioc T (2 * T)) :
    ‖zeroField v (c * L) y t + cameraPoly v (c * L) y t‖ ≤ C₁ * (1 + 2 / c) := by
  have hT0 : 0 < T := by linarith
  have ht1 : 1 ≤ t := by linarith [ht.1]
  have hδ0 : 0 < c * L := by linarith
  have hexpL : Real.exp L = T := by
    rw [hL]
    exact Real.exp_log hT0
  have hNt : Real.exp (y + c * L) ≤ t := by
    have h1 : Real.exp (y + c * L) ≤ Real.exp L := Real.exp_le_exp.2 (by nlinarith)
    linarith [ht.1]
  refine (hC₁ _ _ t hδ1 hyδ ht1 hNt).trans (mul_le_mul_of_nonneg_left ?_ hC₁0)
  have hlog : Real.log (2 + t) ≤ 2 * L := by
    have h1 : 2 + t ≤ T ^ 2 := by nlinarith [ht.2]
    calc Real.log (2 + t) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) h1
      _ = 2 * L := by rw [Real.log_pow, ← hL]; norm_num
  have hq : Real.log (2 + t) / (c * L) ≤ 2 / c := by
    rw [div_le_div_iff₀ hδ0 hc0]
    nlinarith
  linarith

/-- The count from the energy: separated windows lie in the set of large energy or in an exceptional set, or the bound is trivial. -/
theorem card_le_of_energy {ι : Type*} (Z : Finset ι) (g : ι → ℝ) {𝓔 : ℝ → ℝ} (h𝓔 : Continuous 𝓔)
    (h𝓔0 : ∀ t, 0 ≤ 𝓔 t) {r T L c Sv E₀ Θ Bbad : ℝ} {Bad : Set ℝ} (hr0 : 0 < r)
    (h2r : (2 * r)⁻¹ = 5 * (c * L)) (hT : 0 < T) (hL : 0 < L) (hc : 0 < c) (hE₀ : 0 ≤ E₀) (hΘ : 0 < Θ)
    (hBbad : 0 ≤ Bbad) (hBad : volume Bad ≤ ENNReal.ofReal Bbad)
    (hmean : ∫ t in T..(2 * T), 𝓔 t ≤ L * (8 * Sv ^ 2 / c ^ 2 * T))
    (hsep : ∀ ρ ∈ Z, ∀ ρ' ∈ Z, ρ ≠ ρ' → 2 * r ≤ |g ρ - g ρ'|)
    (hmem : ∀ ρ ∈ Z, Ioo (g ρ - r) (g ρ + r) ⊆ Ioc T (2 * T))
    (hbig : 14 * E₀ ≤ Θ → ∀ ρ ∈ Z, Ioo (g ρ - r) (g ρ + r) ⊆
      {t | t ∈ Ioc T (2 * T) ∧ L * Θ ^ 2 / 40 ≤ 𝓔 t} ∪ Bad) :
    (Z.card : ℝ) ≤ (1600 * Sv ^ 2 / c + 980 * c * E₀ ^ 2) * T * L / Θ ^ 2 + Bbad * (5 * (c * L)) := by
  have hunion := volume_biUnion_windows_eq Z g hsep
  have hcard_of : ∀ B : ℝ, (Z.card : ℝ) * (2 * r) ≤ B → (Z.card : ℝ) ≤ B * (5 * (c * L)) := by
    intro B h
    rw [← h2r]
    have h2 : 0 < 2 * r := by positivity
    calc (Z.card : ℝ) = (Z.card : ℝ) * (2 * r) * (2 * r)⁻¹ := by field_simp
      _ ≤ B * (2 * r)⁻¹ := mul_le_mul_of_nonneg_right h (by positivity)
  have hΘ2 : 0 < Θ ^ 2 := by positivity
  have hBnn : 0 ≤ Bbad * (5 * (c * L)) := by positivity
  rcases le_or_gt (14 * E₀) Θ with h14 | hsmall
  · have hthr : 0 < L * Θ ^ 2 / 40 := by positivity
    have hvol := volume_ge_le_of_integral h𝓔 h𝓔0 hT hthr hmean
    have hle : volume (⋃ ρ ∈ Z, Ioo (g ρ - r) (g ρ + r)) ≤
        ENNReal.ofReal (L * (8 * Sv ^ 2 / c ^ 2 * T) / (L * Θ ^ 2 / 40) + Bbad) := by
      refine (measure_mono (Set.iUnion₂_subset (hbig h14))).trans ?_
      refine (measure_union_le _ _).trans ?_
      rw [ENNReal.ofReal_add (by positivity) hBbad]
      exact add_le_add hvol hBad
    rw [hunion] at hle
    have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle
    refine (hcard_of _ hreal).trans ?_
    have e : (L * (8 * Sv ^ 2 / c ^ 2 * T) / (L * Θ ^ 2 / 40) + Bbad) * (5 * (c * L)) =
        1600 * Sv ^ 2 / c * T * L / Θ ^ 2 + Bbad * (5 * (c * L)) := by
      field_simp
      ring
    rw [e]
    refine add_le_add ?_ le_rfl
    refine div_le_div_of_nonneg_right ?_ hΘ2.le
    have h0 : 0 ≤ 980 * c * E₀ ^ 2 * T * L := by positivity
    nlinarith
  · have hle : volume (⋃ ρ ∈ Z, Ioo (g ρ - r) (g ρ + r)) ≤ ENNReal.ofReal T := by
      refine (measure_mono (Set.iUnion₂_subset hmem)).trans ?_
      rw [Real.volume_Ioc, show 2 * T - T = T by ring]
    rw [hunion] at hle
    have hreal := (ENNReal.ofReal_le_ofReal_iff hT.le).1 hle
    refine (hcard_of _ hreal).trans ?_
    have hΘE : Θ ^ 2 ≤ 196 * E₀ ^ 2 := by nlinarith
    have hmain : T * (5 * (c * L)) ≤ (1600 * Sv ^ 2 / c + 980 * c * E₀ ^ 2) * T * L / Θ ^ 2 := by
      rw [le_div_iff₀ hΘ2]
      have h1 : T * (5 * (c * L)) * Θ ^ 2 ≤ T * (5 * (c * L)) * (196 * E₀ ^ 2) :=
        mul_le_mul_of_nonneg_left hΘE (by positivity)
      have h2 : 0 ≤ 1600 * Sv ^ 2 / c * T * L := by positivity
      have e : (1600 * Sv ^ 2 / c + 980 * c * E₀ ^ 2) * T * L =
          1600 * Sv ^ 2 / c * T * L + T * (5 * (c * L)) * (196 * E₀ ^ 2) := by ring
      rw [e]
      linarith
    linarith

/-- The window of a hyperbolically isolated zero lies in the set of large energy. -/
theorem window_subset_energy (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    (hv0 : ∀ u, 0 ≤ v u) {c L y₀ Y α A B₀ E₀ Θ x r : ℝ} {N : ℕ} (hc : c < 1 / 3)
    (hδ0 : 0 < c * L) (hL0 : 0 < L) (hy₀δ : c * L < y₀) (hyy : y₀ ≤ Y) (hYδ : Y - c * L = (1 - 3 * c) * L)
    (hℓ : Y - y₀ ≤ L) (hα : 0 ≤ α) (hA : 1 ≤ A) (hB₀ : 0 < B₀) (hE₀0 : 0 ≤ E₀) (hbig : 14 * E₀ ≤ Θ)
    (hx : x = (1 - 3 * c) * α)
    (hΘsq : Θ ^ 2 = (∫ u, v u) ^ 2 * Real.exp (2 * x) * B₀ ^ 2 / (α + 1)) (hr : r = 1 / (10 * (c * L)))
    (hsupp' : ∀ y ∈ Icc y₀ Y, cameraLength (c * L) y ≤ N)
    {t : ℝ} (hclose : ∀ y ∈ Icc y₀ Y, ‖zeroField v (c * L) y t + cameraPoly v (c * L) y t‖ ≤ E₀)
    {ρ : zetaZeroConfig.carrier} (hd1 : α / L ≤ (ρ : ℂ).re - 1 / 2)
    (hd2 : (ρ : ℂ).re - 1 / 2 ≤ (α + 1) / L) (habs : |t - (ρ : ℂ).im| ≤ r)
    (hhyp : HyperbolicAtHeight v (c * L) y₀ Y (A / L) B₀ (Θ / 14) ρ t) :
    L * Θ ^ 2 / 40 ≤ cameraEnergy v (c * L) y₀ Y N t := by
  rw [hr] at habs
  obtain ⟨D, hρD, hdeep, hprod, hlow, hnoise⟩ := hhyp
  have hb₀ : 0 < A / L := by
    have : 0 < A := by linarith
    positivity
  have hchain := energy_chain hv hsupp hv0 hδ0 hy₀δ hyy hb₀ hB₀.le hsupp'
    hclose hρD hdeep hprod habs hlow hnoise
  have hbρ : 0 < (ρ : ℂ).re - 1 / 2 := lt_of_lt_of_le hb₀ (hdeep ρ hρD)
  have hG := main_term_ge (I₀ := ∫ u, v u) (B₀ := B₀) hL0 hα hc hd1 hd2 hbρ hYδ
  rw [← hx, ← hΘsq] at hG
  exact energy_threshold hL0 rfl rfl hA hE₀0 hbig (by linarith) hℓ hG hchain

/-- **The hyperbolic camera bounds isolated zeros.** Separated zeros of depth in `[α/L, (α+1)/L]` in `[T+1, 2T−1]` that are hyperbolically
isolated at every height of their window off an exceptional set `Bad` number `≪_c (α+1) T L e^{−2(1−3c)α}/B₀²`, up to
`5cL |Bad|`. -/
theorem exists_card_hyperbolic_zeros_le (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u) {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ α A B₀ Bbad : ℝ, 0 ≤ α → 1 ≤ A → 0 < B₀ → 0 ≤ Bbad →
      ∀ Bad : Set ℝ, volume Bad ≤ ENNReal.ofReal Bbad → ∀ S : Finset zetaZeroConfig.carrier,
      (∀ ρ ∈ S, α / Real.log T ≤ (ρ : ℂ).re - 1 / 2 ∧ (ρ : ℂ).re - 1 / 2 ≤ (α + 1) / Real.log T ∧
        T + 1 ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T - 1 ∧
        ∀ t : ℝ, |t - (ρ : ℂ).im| ≤ 1 / (10 * (c * Real.log T)) → t ∉ Bad →
        HyperbolicAtHeight v (c * Real.log T) (2 * (c * Real.log T)) ((1 - 2 * c) * Real.log T)
          (A / Real.log T) B₀
          ((∫ u, v u) * Real.exp ((1 - 3 * c) * α) * B₀ / Real.sqrt (α + 1) / 14) ρ t) →
      (∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' → 1 / (5 * (c * Real.log T)) ≤ |(ρ : ℂ).im - (ρ' : ℂ).im|) →
      (S.card : ℝ) ≤ C * (α + 1) * T * Real.log T * Real.exp (-(2 * (1 - 3 * c) * α)) / B₀ ^ 2 +
        Bbad * (5 * (c * Real.log T)) := by
  classical
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_zeroField_add_cameraPoly_le hv hsupp
  obtain ⟨Sv, hS0, hS⟩ := exists_abs_profile_le hv hsupp
  obtain ⟨CΛ, hCΛ⟩ := exists_sum_vonMangoldt_sq_div_le
  obtain ⟨E₀, hE₀def⟩ : ∃ E₀, E₀ = C₁ * (1 + 2 / c) := ⟨_, rfl⟩
  have hE₀0 : 0 ≤ E₀ := by
    rw [hE₀def]
    positivity
  refine ⟨(1600 * Sv ^ 2 / c + 980 * c * E₀ ^ 2) / (∫ u, v u) ^ 2, by positivity, ?_⟩
  have hL : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop 3, hL.eventually_ge_atTop (1 / c), hL.eventually_ge_atTop 2,
    hL.eventually_ge_atTop (64 / c ^ 2), hL.eventually_ge_atTop (1 + |CΛ|)]
    with T hT3 hLc hL2 hLd hLC α A B₀ Bbad hα hA hB₀ hBbad Bad hBadvol Z hZ hsep
  have hT0 : 0 < T := by linarith
  have hsq : ∀ y : ℝ, 0 ≤ y + c * Real.log T → y + c * Real.log T ≤ (1 - c) * Real.log T →
      ∫ t in T..(2 * T), ‖cameraPoly v (c * Real.log T) y t‖ ^ 2 ≤ 8 * Sv ^ 2 / c ^ 2 * T :=
    fun y h1 h2 => integral_cameraPoly_sq_le (v := v) hS hCΛ hc0 (by linarith) hT3 hL2 hLd hLC h1 h2
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log T := ⟨_, rfl⟩
  rw [← hLdef] at hLc hL2 hLd hLC hsq hZ hsep ⊢
  have hL0 : 0 < L := by linarith
  have hδ1 : 1 ≤ c * L := by
    rw [div_le_iff₀ hc0] at hLc
    linarith
  have hδ0 : 0 < c * L := by linarith
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, y₀ = 2 * (c * L) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (1 - 2 * c) * L := ⟨_, rfl⟩
  rw [← hy₀, ← hY] at hZ
  have hy₀δ : c * L < y₀ := by
    rw [hy₀]
    linarith
  have hyy : y₀ ≤ Y := by
    rw [hy₀, hY]
    nlinarith
  obtain ⟨N, hN⟩ : ∃ N, N = cameraLength (c * L) Y := ⟨_, rfl⟩
  have hsupp' : ∀ y ∈ Icc y₀ Y, cameraLength (c * L) y ≤ N := by
    intro y hy
    rw [hN]
    exact Nat.ceil_mono (Real.exp_le_exp.2 (by linarith [hy.2]))
  have hyrange : ∀ y ∈ Icc y₀ Y, y + c * L ≤ (1 - c) * L := by
    intro y hy
    have := hy.2
    rw [hY] at this
    nlinarith
  have hclose : ∀ t ∈ Ioc T (2 * T), ∀ y ∈ Icc y₀ Y,
      ‖zeroField v (c * L) y t + cameraPoly v (c * L) y t‖ ≤ E₀ := fun t ht y hy => by
    rw [hE₀def]
    exact close_of_scale hC₁0 hC₁ hc0 (by linarith) hT3 hLdef hδ1
      (lt_of_lt_of_le hy₀δ hy.1) (hyrange y hy) ht
  have hmv : ∀ y ∈ Icc y₀ Y, ∫ t in T..(2 * T), ‖cameraPolyAt v (c * L) y N t‖ ^ 2 ≤
      8 * Sv ^ 2 / c ^ 2 * T := by
    intro y hy
    refine le_trans (le_of_eq ?_) (hsq y (by linarith [hy.1]) (hyrange y hy))
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [cameraPoly_eq_cameraPolyAt hsupp hδ0 (hsupp' y hy)]
  have hmean := integral_cameraEnergy_le (v := v) hv.continuous (T := T) hyy hmv
  have hℓ : Y - y₀ ≤ L := by
    rw [hy₀, hY]
    nlinarith
  have hmean2 : ∫ t in T..(2 * T), cameraEnergy v (c * L) y₀ Y N t ≤ L * (8 * Sv ^ 2 / c ^ 2 * T) :=
    hmean.trans (mul_le_mul_of_nonneg_right hℓ (by positivity))
  obtain ⟨x, hx⟩ : ∃ x, x = (1 - 3 * c) * α := ⟨_, rfl⟩
  rw [← hx] at hZ
  have hexp2 : Real.exp (-(2 * (1 - 3 * c) * α)) = (Real.exp (2 * x))⁻¹ := by
    rw [← Real.exp_neg, hx]
    congr 1
    ring
  rw [hexp2]
  have hα1 : 0 < α + 1 := by linarith
  obtain ⟨Θ, hΘdef⟩ : ∃ Θ, Θ = (∫ u, v u) * Real.exp x * B₀ / Real.sqrt (α + 1) := ⟨_, rfl⟩
  have hΘ0 : 0 < Θ := by
    rw [hΘdef]
    positivity
  have hΘsq : Θ ^ 2 = (∫ u, v u) ^ 2 * Real.exp (2 * x) * B₀ ^ 2 / (α + 1) := by
    rw [hΘdef, div_pow, Real.sq_sqrt hα1.le, mul_pow, mul_pow, ← Real.exp_nat_mul]
    push_cast
    rfl
  rw [← hΘdef] at hZ
  obtain ⟨r, hr⟩ : ∃ r, r = 1 / (10 * (c * L)) := ⟨_, rfl⟩
  have hr0 : 0 < r := by
    rw [hr]
    positivity
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one (by positivity)]
    linarith
  have h2r : (2 * r)⁻¹ = 5 * (c * L) := by
    rw [hr]
    field_simp
    norm_num
  have hsep' : ∀ ρ ∈ Z, ∀ ρ' ∈ Z, ρ ≠ ρ' → 2 * r ≤ |(ρ : ℂ).im - (ρ' : ℂ).im| := by
    intro ρ hρ ρ' hρ' hne
    have e : 2 * r = 1 / (5 * (c * L)) := by
      rw [hr]
      field_simp
      norm_num
    rw [e]
    exact hsep ρ hρ ρ' hρ' hne
  have hmem : ∀ ρ ∈ Z, Ioo ((ρ : ℂ).im - r) ((ρ : ℂ).im + r) ⊆ Ioc T (2 * T) := by
    intro ρ hρ t ht
    obtain ⟨-, -, hlow, hhigh, -⟩ := hZ ρ hρ
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hYδ : Y - c * L = (1 - 3 * c) * L := by
    rw [hY]
    ring
  have hwindow : 14 * E₀ ≤ Θ → ∀ ρ ∈ Z, Ioo ((ρ : ℂ).im - r) ((ρ : ℂ).im + r) ⊆
      {t | t ∈ Ioc T (2 * T) ∧ L * Θ ^ 2 / 40 ≤ cameraEnergy v (c * L) y₀ Y N t} ∪ Bad := by
    intro hbig ρ hρ t ht
    by_cases htBad : t ∈ Bad
    · exact Or.inr htBad
    refine Or.inl ?_
    obtain ⟨hd1, hd2, -, -, hhyp⟩ := hZ ρ hρ
    have htI := hmem ρ hρ ht
    have habs : |t - (ρ : ℂ).im| ≤ r := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hc3 : c < 1 / 3 := by linarith
    have hhyp' : HyperbolicAtHeight v (c * L) y₀ Y (A / L) B₀ (Θ / 14) ρ t :=
      hhyp t (by rw [← hr]; exact habs) htBad
    refine ⟨htI, ?_⟩
    exact window_subset_energy hv hsupp hv0 hc3 hδ0 hL0 hy₀δ hyy hYδ hℓ hα hA hB₀
      hE₀0 hbig hx hΘsq hr hsupp' (hclose t htI) hd1 hd2 habs hhyp'
  have hkey := card_le_of_energy Z (fun ρ : zetaZeroConfig.carrier => (ρ : ℂ).im)
    (continuous_cameraEnergy hv.continuous (c * L) y₀ Y N) (cameraEnergy_nonneg hyy (c * L) N)
    (Sv := Sv) hr0 h2r hT0 hL0 hc0 hE₀0 hΘ0 hBbad hBadvol hmean2 hsep' hmem hwindow
  refine hkey.trans (le_of_eq ?_)
  rw [hΘsq]
  congr 1
  field_simp

end GaloisForLFunctions.MultiscaleMollifiedZetaField
