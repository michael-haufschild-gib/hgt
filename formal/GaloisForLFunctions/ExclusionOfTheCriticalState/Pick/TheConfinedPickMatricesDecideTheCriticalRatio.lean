import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.TheRealProbeKernelCountsTheZerosRightOfTheLine
import GaloisForLFunctions.ExclusionOfTheCriticalState.Collar.TheCollarIsCoerciveAndPrimeBlind
import GaloisForLFunctions.RHTower.WeilPhiDoobPrimeAtoms
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheCriticalStatesFormAnOrthogonalLadder

/-!
# The confined Pick matrices decide the critical ratio

On probes `e_p(u) = e^{pu}` (`u < 0`) the confined form is the real Pick kernel
`Q_R(e_p, e_q) = (D(p) + D(q))/(p + q) + a(R)/(p + q − 8)` (`criticalHalfLineMixedEnergy_probe`).

* **Probe sums approximate window tests.** For a `C²` test `G` supported in `[−A, 0]`, write
  `G(u) = e^{6u} g(eᵘ)` with `g` of class `C²` (`windowProfile`). Weierstrass approximation of `g'`
  gives a polynomial `h` with `|g − h|, |g' − h'| ≤ ε` on `[0, 1]`, and `P(u) = e^{6u} h(eᵘ)` is a
  combination of the probes `e_7, e_8, …`. The error `D = G − P = e^{6u} φ(eᵘ)` has zero transform
  `|∫ D e^{zu}| ≤ 2ε/|6 + z|` on the critical strip (integration by parts on `(−∞, 0]`), so the zero
  coordinates of `P` converge to those of `G` in `ℓ²` (temperedness of the zeros).
* **Krein form on both sides** (`re_inner_reflect_probeSumVec`, `weilQuad_eq_re_inner_windowVec`).
  The bare form of a probe sum and Weil's form of a window test are `Re⟨R y, y⟩` for their zero
  coordinates `y(ρ) = √m_ρ ∫ F(u) e^{(ρ−½)u} du`, so they converge together.
* **The Pick form decides the confined form** (`confinedPick_nonneg_iff`). Every real Pick matrix of
  `Q_R` on the integer nodes `7, 8, …` is positive semidefinite iff `R` is at most every window
  threshold: one direction by the approximation, the other because the confined energy of a probe
  sum is its Pick form (`criticalHalfLineFullEnergy_probeSum`, bilinearity of the mixed energy).
* **The critical ratio in Pick form** (`isGreatest_confinedPick_criticalRatio`,
  `riemannHypothesis_or_isGreatest_confinedPick`). Off RH, `W₀` is the largest ratio at which all
  the integer Pick matrices `((D(m) + D(n))/(m + n) + a(R)/(m + n − 8))_{m,n ≥ 7}` are positive
  semidefinite; finite node blocks approximate it from above
  (`confinedPick_blocks_approximate_criticalRatio`).
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped ComplexConjugate lp

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry Zeta23
  _root_.RHTower CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis
open GaloisForLFunctions.SquareRootThreshold (temperedConfig_zetaZeroConfig)

/-! ### Zero coordinates in Weil's convention -/

theorem I_mul_gammaOf (ρ : ℂ) : I * gammaOf ρ = ρ - 1 / 2 := by
  rw [gammaOf, mul_comm]
  exact div_mul_cancel₀ _ I_ne_zero

/-- The zero coordinate of a real profile: `√m_ρ ∫ F(u) e^{(ρ−½)u} du`. -/
theorem zeroCoord_cx_eq (F : ℝ → ℝ) (τ : zetaZeroConfig.carrier) :
    zeroCoord zetaZeroConfig (ArithmeticCastelnuovoSeveri.cx F) τ =
      ((Real.sqrt (zetaZeroConfig.mult τ) : ℝ) : ℂ) *
        ∫ u : ℝ, (F u : ℂ) * cexp (((τ : ℂ) - 1 / 2) * u) := by
  rw [zeroCoord, paperFT, I_mul_gammaOf]
  rfl

theorem re_carrier_sub_half_ge (τ : zetaZeroConfig.carrier) : -(1 / 2) ≤ ((τ : ℂ) - 1 / 2).re :=
  (abs_le.mp (abs_re_carrier_sub_half τ)).1

theorem re_carrier_sub_half_le (τ : zetaZeroConfig.carrier) : ((τ : ℂ) - 1 / 2).re ≤ 1 / 2 :=
  (abs_le.mp (abs_re_carrier_sub_half τ)).2

/-- Probe coordinates in Weil's convention, `w_p(ρ) = √m_ρ/(p + ρ − ½)`. -/
def probeCoordW (p : ℝ) (τ : zetaZeroConfig.carrier) : ℂ :=
  ((Real.sqrt (zetaZeroConfig.mult τ) : ℝ) : ℂ) / ((p : ℂ) + ((τ : ℂ) - 1 / 2))

theorem zeroCoord_probe_eq {p : ℝ} (hp : 1 ≤ p) (τ : zetaZeroConfig.carrier) :
    zeroCoord zetaZeroConfig (ArithmeticCastelnuovoSeveri.cx (probe p)) τ = probeCoordW p τ := by
  have hre : 0 < p + ((τ : ℂ) - 1 / 2).re := by linarith [re_carrier_sub_half_ge τ]
  rw [zeroCoord_cx_eq, integral_probe_mul_cexp hre, mul_one_div]
  rfl

theorem norm_probeCoordW_sq_le {p : ℝ} (hp : 1 ≤ p) (τ : zetaZeroConfig.carrier) :
    ‖probeCoordW p τ‖ ^ 2 ≤
      5 * ((zetaZeroConfig.mult τ : ℝ) / (1 + Complex.normSq ((τ : ℂ) - 1 / 2))) := by
  have h := (one_add_normSq_le_five_mul hp (abs_re_carrier_sub_half τ)).2
  have hN : 0 < 1 + Complex.normSq ((τ : ℂ) - 1 / 2) := by
    have := Complex.normSq_nonneg ((τ : ℂ) - 1 / 2)
    linarith
  have hD : 0 < Complex.normSq ((p : ℂ) + ((τ : ℂ) - 1 / 2)) := by linarith
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult τ := Nat.cast_nonneg _
  rw [probeCoordW, norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt hm, Complex.sq_norm, div_le_iff₀ hD]
  rw [mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hN]
  nlinarith

theorem memℓp_probeCoordW {p : ℝ} (hp : 1 ≤ p) : Memℓp (probeCoordW p) 2 := by
  refine (memℓp_gen_iff (by norm_num)).mpr ?_
  refine Summable.of_nonneg_of_le (fun τ => by positivity) (fun τ => ?_)
    (summable_mult_div_normSq.mul_left 5)
  rw [ENNReal.toReal_ofNat, Real.rpow_two]
  exact norm_probeCoordW_sq_le hp τ

/-- The probe vector `w_p ∈ ℓ²` in Weil's convention. -/
def probeVecW {p : ℝ} (hp : 1 ≤ p) : ℓ²(zetaZeroConfig.carrier, ℂ) :=
  ⟨probeCoordW p, memℓp_probeCoordW hp⟩

theorem probeVecW_apply {p : ℝ} (hp : 1 ≤ p) (τ : zetaZeroConfig.carrier) :
    probeVecW hp τ = probeCoordW p τ := rfl

theorem mult_div_eq_conj_mul_W (p q : ℝ) (τ : zetaZeroConfig.carrier) :
    (zetaZeroConfig.mult τ : ℂ) *
        ((((q : ℂ) - ((τ : ℂ) - 1 / 2)) * ((p : ℂ) + ((τ : ℂ) - 1 / 2)))⁻¹) =
      conj (probeCoordW q (reflectCarrier zetaZeroConfig τ)) * probeCoordW p τ := by
  have hm : zetaZeroConfig.mult (reflect (τ : ℂ)) = zetaZeroConfig.mult τ :=
    zetaZeroConfig.mult_reflect _ τ.2
  have hsq : ((Real.sqrt (zetaZeroConfig.mult τ) : ℝ) : ℂ) * (Real.sqrt (zetaZeroConfig.mult τ) : ℝ) =
      (zetaZeroConfig.mult τ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have hconj : conj ((q : ℂ) + (reflect (τ : ℂ) - 1 / 2)) = (q : ℂ) - ((τ : ℂ) - 1 / 2) := by
    simp only [reflect, map_add, map_sub, map_one, Complex.conj_ofReal, Complex.conj_conj, map_div₀,
      map_ofNat]
    ring
  simp only [probeCoordW, reflectCarrier, hm, map_div₀, Complex.conj_ofReal, hconj]
  rw [mul_inv, ← hsq]
  ring

/-- **The probe kernel in Weil's coordinates**: `K(q, p) = ⟨R w_q, w_p⟩`. -/
theorem bareMixedEnergy_probe_eq_inner_W {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    (bareMixedEnergy (probe q) (probe p) : ℂ) =
      inner ℂ (reflectVec zetaZeroConfig (probeVecW hq)) (probeVecW hp) := by
  rw [bareMixedEnergy_probe_eq_tsum_carrier hq hp, lp.inner_eq_tsum]
  refine tsum_congr fun τ => ?_
  rw [mult_div_eq_conj_mul_W p q, RCLike.inner_apply', reflectVec_apply, probeVecW_apply,
    probeVecW_apply]

/-! ### Probe sums and window tests in Krein form -/

/-- The probe sum `Σ_k c_k e_{p_k}`. -/
def probeSum {N : ℕ} (p c : Fin N → ℝ) (u : ℝ) : ℝ := ∑ k, c k * probe (p k) u

/-- Its zero vector `Σ_k c_k w_{p_k}`. -/
def probeSumVec {N : ℕ} {p : Fin N → ℝ} (hp : ∀ k, 1 ≤ p k) (c : Fin N → ℝ) :
    ℓ²(zetaZeroConfig.carrier, ℂ) :=
  ∑ k, (c k : ℂ) • probeVecW (hp k)

theorem re_inner_reflect_probeSumVec {N : ℕ} {p : Fin N → ℝ} (hp : ∀ k, 1 ≤ p k)
    (c : Fin N → ℝ) :
    (inner ℂ (reflectVec zetaZeroConfig (probeSumVec hp c)) (probeSumVec hp c)).re =
      ∑ j, ∑ k, c j * c k * bareMixedEnergy (probe (p j)) (probe (p k)) := by
  unfold probeSumVec
  rw [reflectVec_sum_smul, sum_inner]
  simp only [inner_smul_left, inner_sum, inner_smul_right, Complex.conj_ofReal]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← bareMixedEnergy_probe_eq_inner_W (hp k) (hp j), ← Complex.ofReal_mul,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

theorem probeSumVec_apply {N : ℕ} {p : Fin N → ℝ} (hp : ∀ k, 1 ≤ p k) (c : Fin N → ℝ)
    (τ : zetaZeroConfig.carrier) :
    probeSumVec hp c τ = ∑ k, (c k : ℂ) * probeCoordW (p k) τ := by
  simp only [probeSumVec, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, probeVecW_apply]

/-- A window test as an element of the space of `C²` compactly supported tests. -/
def windowTestElt {A : ℝ} {G : ℝ → ℝ} (hG : IsWindowTest A G) : testSpace :=
  ⟨ArithmeticCastelnuovoSeveri.cx G, cx_contDiff hG.contDiff,
    hG.hasCompactSupport.comp_left Complex.ofReal_zero⟩

/-- The zero coordinates of a window test. -/
def windowVec {A : ℝ} {G : ℝ → ℝ} (hG : IsWindowTest A G) : ℓ²(zetaZeroConfig.carrier, ℂ) :=
  zeroMap zetaZeroConfig temperedConfig_zetaZeroConfig (windowTestElt hG)

theorem windowVec_apply {A : ℝ} {G : ℝ → ℝ} (hG : IsWindowTest A G) (τ : zetaZeroConfig.carrier) :
    windowVec hG τ = zeroCoord zetaZeroConfig (ArithmeticCastelnuovoSeveri.cx G) τ := rfl

/-- **Weil's form of a window test is the Krein form of its zero coordinates.** -/
theorem weilQuad_eq_re_inner_windowVec {A : ℝ} {G : ℝ → ℝ} (hG : IsWindowTest A G) :
    weilQuad G = (inner ℂ (reflectVec zetaZeroConfig (windowVec hG)) (windowVec hG)).re := by
  have hcx := cx_contDiff hG.contDiff
  have hcc : HasCompactSupport (ArithmeticCastelnuovoSeveri.cx G) :=
    hG.hasCompactSupport.comp_left Complex.ofReal_zero
  have hW : zetaZeroConfig.W (ArithmeticCastelnuovoSeveri.cx G) (ArithmeticCastelnuovoSeveri.cx G) =
      inner ℂ (reflectVec zetaZeroConfig (windowVec hG)) (windowVec hG) :=
    W_eq_inner zetaZeroConfig temperedConfig_zetaZeroConfig (windowTestElt hG) (windowTestElt hG)
  rw [← hW, zeta_W_eq_weilFullFunctional_mixed hcx hcc hcx hcc]
  rfl

/-- The Krein form moves by at most `‖b − a‖(2‖a‖ + ‖b − a‖)`. -/
theorem re_inner_reflect_le (a b : ℓ²(zetaZeroConfig.carrier, ℂ)) :
    (inner ℂ (reflectVec zetaZeroConfig b) b).re ≤
      (inner ℂ (reflectVec zetaZeroConfig a) a).re + ‖b - a‖ * (2 * ‖a‖ + ‖b - a‖) := by
  set d := b - a
  have hb : b = a + d := by simp only [d]; abel
  rw [hb, reflectVec_add, inner_add_left, inner_add_right, inner_add_right]
  have h1 := (norm_inner_le_norm (𝕜 := ℂ) (reflectVec zetaZeroConfig a) d).trans_eq
    (by rw [norm_reflectVec])
  have h2 := (norm_inner_le_norm (𝕜 := ℂ) (reflectVec zetaZeroConfig d) a).trans_eq
    (by rw [norm_reflectVec])
  have h3 := (norm_inner_le_norm (𝕜 := ℂ) (reflectVec zetaZeroConfig d) d).trans_eq
    (by rw [norm_reflectVec])
  have r1 := Complex.re_le_norm (inner ℂ (reflectVec zetaZeroConfig a) d)
  have r2 := Complex.re_le_norm (inner ℂ (reflectVec zetaZeroConfig d) a)
  have r3 := Complex.re_le_norm (inner ℂ (reflectVec zetaZeroConfig d) d)
  simp only [Complex.add_re]
  nlinarith [norm_nonneg a, norm_nonneg d]

/-! ### The profile `g` of a window test -/

/-- `g(x) = G(log x)/x⁶` for `x > 0`, extended by `0`: `G(u) = e^{6u} g(eᵘ)`. -/
def windowProfile (G : ℝ → ℝ) (x : ℝ) : ℝ := if 0 < x then G (Real.log x) / x ^ 6 else 0

theorem windowProfile_exp (G : ℝ → ℝ) (u : ℝ) :
    Real.exp (6 * u) * windowProfile G (Real.exp u) = G u := by
  have h6 : Real.exp u ^ 6 = Real.exp (6 * u) := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [windowProfile, if_pos (Real.exp_pos u), Real.log_exp, h6]
  field_simp

theorem windowProfile_eq_zero_of_lt {A : ℝ} {G : ℝ → ℝ} (hG : IsWindowTest A G) {x : ℝ}
    (hx : x < Real.exp (-A)) : windowProfile G x = 0 := by
  unfold windowProfile
  split_ifs with h0
  · rw [hG.vanish _ fun hm => ?_, zero_div]
    have := Real.log_lt_log h0 hx
    rw [Real.log_exp] at this
    linarith [hm.1]
  · rfl

theorem windowProfile_zero (G : ℝ → ℝ) : windowProfile G 0 = 0 := by
  simp [windowProfile]

theorem contDiff_windowProfile {A : ℝ} {G : ℝ → ℝ} (hG : IsWindowTest A G) :
    ContDiff ℝ 2 (windowProfile G) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_or_ge x (Real.exp (-A)) with hx | hx
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact windowProfile_eq_zero_of_lt hG hy
  · have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
    refine ContDiffAt.congr_of_eventuallyEq (f := fun y => G (Real.log y) / y ^ 6) ?_ ?_
    · exact (hG.contDiff.contDiffAt.comp x (Real.contDiffAt_log.mpr hx0.ne')).div
        (contDiffAt_id.pow 6) (pow_ne_zero 6 hx0.ne')
    · filter_upwards [Ioi_mem_nhds hx0] with y hy
      simp only [windowProfile, if_pos (show 0 < y from hy)]

/-! ### Polynomial antiderivatives -/

/-- `h(x) = Σ_{k ≤ d} π_k x^{k+1}/(k + 1)`, an antiderivative of `π` vanishing at `0`. -/
def antiderivPoly (π : Polynomial ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (π.natDegree + 1), π.coeff k / (k + 1) * x ^ (k + 1)

theorem hasDerivAt_antiderivPoly (π : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (antiderivPoly π) (π.eval x) x := by
  have hk : ∀ k ∈ Finset.range (π.natDegree + 1), HasDerivAt
      (fun y : ℝ => π.coeff k / (k + 1) * y ^ (k + 1)) (π.coeff k * x ^ k) x := by
    intro k _
    refine ((hasDerivAt_pow (k + 1) x).const_mul (π.coeff k / (k + 1))).congr_deriv ?_
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    rw [Nat.add_sub_cancel]
    push_cast
    field_simp
  have hf : antiderivPoly π =
      ∑ k ∈ Finset.range (π.natDegree + 1), fun y : ℝ => π.coeff k / (k + 1) * y ^ (k + 1) := by
    funext y
    rw [Finset.sum_apply]
    rfl
  rw [hf, Polynomial.eval_eq_sum_range]
  exact HasDerivAt.sum hk

theorem antiderivPoly_zero (π : Polynomial ℝ) : antiderivPoly π 0 = 0 := by
  simp [antiderivPoly]

/-- On `u < 0` the polynomial is a probe sum: `e^{6u} h(eᵘ) = Σ_k c_k e^{(k+7)u}`. -/
theorem exp_mul_antiderivPoly_eq_probeSum (π : Polynomial ℝ) {u : ℝ} (hu : u < 0) :
    Real.exp (6 * u) * antiderivPoly π (Real.exp u) =
      probeSum (fun k : Fin (π.natDegree + 1) => (k : ℝ) + 7)
        (fun k => π.coeff k / ((k : ℝ) + 1)) u := by
  unfold antiderivPoly probeSum
  rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [probe_of_neg hu, ← Real.exp_nat_mul]
  have : Real.exp (6 * u) * Real.exp ((((k : ℕ) + 1 : ℕ) : ℝ) * u) =
      Real.exp (((k : ℝ) + 7) * u) := by
    rw [← Real.exp_add]; push_cast; ring_nf
  rw [mul_left_comm, this]

/-! ### Probe sums approximate window tests -/

/-- **Weierstrass approximation of the profile**: a polynomial antiderivative `h` with
`|g' − h'| ≤ ε` and `|g − h| ≤ ε` on `[0, 1]`. -/
theorem exists_antiderivPoly_near {A : ℝ} {G : ℝ → ℝ} (hG : IsWindowTest A G) {ε : ℝ}
    (hε : 0 < ε) : ∃ π : Polynomial ℝ,
      (∀ x ∈ Icc (0 : ℝ) 1, |deriv (windowProfile G) x - π.eval x| ≤ ε) ∧
      ∀ x ∈ Icc (0 : ℝ) 1, |windowProfile G x - antiderivPoly π x| ≤ ε := by
  have hg := contDiff_windowProfile hG
  obtain ⟨π, hπ⟩ := exists_polynomial_near_of_continuousOn 0 1 (deriv (windowProfile G))
    (hg.continuous_deriv one_le_two).continuousOn ε hε
  have hd : ∀ x ∈ Icc (0 : ℝ) 1, |deriv (windowProfile G) x - π.eval x| ≤ ε := fun x hx => by
    rw [abs_sub_comm]; exact (hπ x hx).le
  refine ⟨π, hd, fun x hx => ?_⟩
  have hφ : ∀ y ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun y => windowProfile G y - antiderivPoly π y)
      (deriv (windowProfile G) y - π.eval y) (Icc 0 1) y := fun y _ =>
    (((hg.differentiable two_ne_zero) y).hasDerivAt.sub
      (hasDerivAt_antiderivPoly π y)).hasDerivWithinAt
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hφ (fun y hy => by
    rw [Real.norm_eq_abs]; exact hd y (Ico_subset_Icc_self hy)) x hx
  rw [windowProfile_zero, antiderivPoly_zero, sub_zero, sub_zero, sub_zero, Real.norm_eq_abs] at h
  calc |windowProfile G x - antiderivPoly π x| ≤ ε * x := h
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hx.2 hε.le
    _ = ε := mul_one ε

theorem norm_cexp_mul_ofReal_le {w : ℂ} (hw : 1 ≤ w.re) {u : ℝ} (hu : u ≤ 0) :
    ‖cexp (w * u)‖ ≤ Real.exp u := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  nlinarith

/-- **The zero transform of the error.** If `D(u) = e^{6u} φ(eᵘ)` on `u < 0` with `|φ|, |φ'| ≤ ε`
on `[0, 1]` and `D = 0` on `u ≥ 0`, then `|∫ D e^{zu}| ≤ 2ε/|6 + z|` for `Re z ≥ −½`: integrate
`(e^{(6+z)u} φ(eᵘ))'` over `(−∞, 0]`. -/
theorem norm_integral_error_le {φ φ' : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ'c : Continuous φ') {ε : ℝ} (hε : 0 ≤ ε) (hb : ∀ x ∈ Icc (0 : ℝ) 1, |φ x| ≤ ε)
    (hb' : ∀ x ∈ Icc (0 : ℝ) 1, |φ' x| ≤ ε) {D : ℝ → ℝ}
    (hD : ∀ u, u < 0 → D u = Real.exp (6 * u) * φ (Real.exp u)) (hD0 : ∀ u, 0 ≤ u → D u = 0)
    {z : ℂ} (hz : -(1 / 2) ≤ z.re) :
    ‖∫ u : ℝ, (D u : ℂ) * cexp (z * u)‖ ≤ 2 * ε / ‖(6 : ℂ) + z‖ := by
  set w : ℂ := 6 + z with hwdef
  have hwre : 11 / 2 ≤ w.re := by simp only [w, Complex.add_re]; norm_num; linarith
  have hw1 : 1 ≤ w.re := by linarith
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at hwre; linarith
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun x => (hφ x).continuousAt
  have hexp01 : ∀ u : ℝ, u ≤ 0 → Real.exp u ∈ Icc (0 : ℝ) 1 := fun u hu =>
    ⟨(Real.exp_pos u).le, Real.exp_le_one_iff.mpr hu⟩
  set I1 : ℝ → ℂ := fun u => cexp (w * u) * (φ (Real.exp u) : ℂ) with hI1
  set I2 : ℝ → ℂ := fun u => cexp (w * u) * ((φ' (Real.exp u) * Real.exp u : ℝ) : ℂ) with hI2
  -- the derivative of `e^{wu} φ(eᵘ)`
  have hderiv : ∀ u : ℝ, HasDerivAt I1 (w * I1 u + I2 u) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => cexp (w * u)) (cexp (w * u) * w) u := by
      have := (((hasDerivAt_id u).ofReal_comp).const_mul w).cexp
      simpa using this
    have h2 : HasDerivAt (fun u : ℝ => (φ (Real.exp u) : ℂ))
        ((φ' (Real.exp u) * Real.exp u : ℝ) : ℂ) u :=
      ((hφ (Real.exp u)).comp u (Real.hasDerivAt_exp u)).ofReal_comp
    refine (h1.mul h2).congr_deriv ?_
    show _ = w * (cexp (w * u) * (φ (Real.exp u) : ℂ)) +
      cexp (w * u) * ((φ' (Real.exp u) * Real.exp u : ℝ) : ℂ)
    ring
  have hcI1 : Continuous I1 := by
    show Continuous fun u : ℝ => cexp (w * u) * (φ (Real.exp u) : ℂ)
    fun_prop
  have hcI2 : Continuous I2 := by
    show Continuous fun u : ℝ => cexp (w * u) * ((φ' (Real.exp u) * Real.exp u : ℝ) : ℂ)
    fun_prop
  have hbI1 : ∀ u : ℝ, u ≤ 0 → ‖I1 u‖ ≤ ε * Real.exp u := fun u hu => by
    show ‖cexp (w * u) * (φ (Real.exp u) : ℂ)‖ ≤ ε * Real.exp u
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [mul_comm ε]
    exact mul_le_mul (norm_cexp_mul_ofReal_le hw1 hu) (hb _ (hexp01 u hu)) (abs_nonneg _)
      (Real.exp_pos u).le
  have hbI2 : ∀ u : ℝ, u ≤ 0 → ‖I2 u‖ ≤ ε * Real.exp u := fun u hu => by
    show ‖cexp (w * u) * ((φ' (Real.exp u) * Real.exp u : ℝ) : ℂ)‖ ≤ ε * Real.exp u
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos u)]
    have h1 := norm_cexp_mul_ofReal_le hw1 hu
    have h2 := hb' _ (hexp01 u hu)
    have h3 := Real.exp_le_one_iff.mpr hu
    have h4 := (Real.exp_pos u).le
    calc ‖cexp (w * u)‖ * (|φ' (Real.exp u)| * Real.exp u) ≤ Real.exp u * (ε * 1) := by
          gcongr
      _ = ε * Real.exp u := by ring
  have hgi : IntegrableOn (fun u : ℝ => ε * Real.exp u) (Iic 0) :=
    IntegrableOn.congr_fun ((integrableOn_exp_mul_Iic one_pos 0).const_mul ε)
      (fun u _ => by simp) measurableSet_Iic
  have hI1i : IntegrableOn I1 (Iic 0) :=
    Integrable.mono' hgi hcI1.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun u hu => hbI1 u hu))
  have hI2i : IntegrableOn I2 (Iic 0) :=
    Integrable.mono' hgi hcI2.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun u hu => hbI2 u hu))
  -- FTC on `(−∞, 0]`
  have htend : Tendsto I1 atBot (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using (Real.tendsto_exp_atBot.const_mul ε))
    filter_upwards [eventually_le_atBot 0] with u hu
    exact hbI1 u hu
  have hFTC := integral_Iic_of_hasDerivAt_of_tendsto (hcI1.continuousWithinAt)
    (fun u _ => hderiv u) ((hI1i.const_mul w).add hI2i) htend
  rw [sub_zero, integral_add (hI1i.const_mul w) hI2i, integral_const_mul] at hFTC
  have hI10 : I1 0 = (φ 1 : ℂ) := by simp [I1]
  rw [hI10] at hFTC
  -- the transform of `D` is the integral of `I1`
  have hDint : ∫ u : ℝ, (D u : ℂ) * cexp (z * u) = ∫ u in Iic 0, I1 u := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Iic (0 : ℝ)) fun u hu => by
      rw [hD0 u (le_of_lt (not_le.mp hu)), Complex.ofReal_zero, zero_mul],
      integral_Iic_eq_integral_Iio, integral_Iic_eq_integral_Iio]
    refine setIntegral_congr_fun measurableSet_Iio fun u hu => ?_
    have he : cexp ((6 + z) * u) = cexp (6 * u) * cexp (z * u) := by
      rw [← Complex.exp_add]; congr 1; ring
    simp only [I1, w]
    rw [hD u hu]
    push_cast
    rw [he]
    ring
  have hnI2 : ‖∫ u in Iic 0, I2 u‖ ≤ ε := by
    have h := norm_integral_le_of_norm_le hgi
      ((ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun u hu => hbI2 u hu))
    rw [integral_const_mul, integral_exp_Iic, Real.exp_zero, mul_one] at h
    exact h
  have hφ1 : ‖(φ 1 : ℂ)‖ ≤ ε := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hb 1 ⟨zero_le_one, le_rfl⟩
  have hw : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  rw [hDint, le_div_iff₀ hw, mul_comm]
  have hEq : w * ∫ u in Iic 0, I1 u = (φ 1 : ℂ) - ∫ u in Iic 0, I2 u := by
    rw [← hFTC]; ring
  calc ‖w‖ * ‖∫ u in Iic 0, I1 u‖ = ‖w * ∫ u in Iic 0, I1 u‖ := (norm_mul _ _).symm
    _ = ‖(φ 1 : ℂ) - ∫ u in Iic 0, I2 u‖ := by rw [hEq]
    _ ≤ ‖(φ 1 : ℂ)‖ + ‖∫ u in Iic 0, I2 u‖ := norm_sub_le _ _
    _ ≤ 2 * ε := by linarith

/-! ### The zero coordinates of the error -/

theorem integrable_ofReal_probe_mul_cexp {p : ℝ} {z : ℂ} (h : 0 < p + z.re) :
    Integrable (fun u : ℝ => (probe p u : ℂ) * cexp (z * u)) := by
  refine (integrable_probe_mul_exp h).mono'
    ((Complex.measurable_ofReal.comp (measurable_probe p)).mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (probe_nonneg p u), Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, le_refl]

/-- The zero coordinates of `G − P` are the zero transforms of the error. -/
theorem windowVec_sub_probeSumVec_apply {A : ℝ} {G : ℝ → ℝ} (hG : IsWindowTest A G) {N : ℕ}
    {p : Fin N → ℝ} (hp : ∀ k, 1 ≤ p k) (c : Fin N → ℝ) (τ : zetaZeroConfig.carrier) :
    (windowVec hG - probeSumVec hp c) τ = ((Real.sqrt (zetaZeroConfig.mult τ) : ℝ) : ℂ) *
      ∫ u : ℝ, ((G u - probeSum p c u : ℝ) : ℂ) * cexp (((τ : ℂ) - 1 / 2) * u) := by
  have hre : ∀ k, 0 < p k + ((τ : ℂ) - 1 / 2).re := fun k => by
    linarith [hp k, re_carrier_sub_half_ge τ]
  have hGi : Integrable (fun u : ℝ => (G u : ℂ) * cexp (((τ : ℂ) - 1 / 2) * u)) :=
    ((Complex.continuous_ofReal.comp hG.continuous).mul (by fun_prop)).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_right (f' := fun u : ℝ => cexp (((τ : ℂ) - 1 / 2) * u))
        (hG.hasCompactSupport.comp_left Complex.ofReal_zero))
  have hPi : ∀ k, Integrable (fun u : ℝ =>
      (c k : ℂ) * ((probe (p k) u : ℂ) * cexp (((τ : ℂ) - 1 / 2) * u))) :=
    fun k => (integrable_ofReal_probe_mul_cexp (hre k)).const_mul _
  have hfun : (fun u : ℝ => ((G u - probeSum p c u : ℝ) : ℂ) * cexp (((τ : ℂ) - 1 / 2) * u)) =
      fun u => (G u : ℂ) * cexp (((τ : ℂ) - 1 / 2) * u) -
        ∑ k, (c k : ℂ) * ((probe (p k) u : ℂ) * cexp (((τ : ℂ) - 1 / 2) * u)) := by
    funext u
    simp only [probeSum]
    push_cast
    rw [sub_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  have hk : ∀ k, probeCoordW (p k) τ = ((Real.sqrt (zetaZeroConfig.mult τ) : ℝ) : ℂ) *
      ∫ u : ℝ, (probe (p k) u : ℂ) * cexp (((τ : ℂ) - 1 / 2) * u) := fun k => by
    rw [← zeroCoord_probe_eq (hp k), zeroCoord_cx_eq]
  rw [hfun, integral_sub hGi (integrable_finsetSum _ fun k _ => hPi k),
    integral_finsetSum _ fun k _ => hPi k]
  simp only [integral_const_mul]
  rw [lp.coeFn_sub, Pi.sub_apply, windowVec_apply, probeSumVec_apply, zeroCoord_cx_eq]
  simp only [hk]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **The error is small in `ℓ²`.** If the zero transforms of `G − P` are `≤ 2ε/|6 + z|`, the zero
coordinates differ by at most `2ε √(5 Σ_ρ m_ρ/(1 + |ρ − ½|²))`. -/
theorem norm_windowVec_sub_probeSumVec_le {A : ℝ} {G : ℝ → ℝ} (hG : IsWindowTest A G) {N : ℕ}
    {p : Fin N → ℝ} (hp : ∀ k, 1 ≤ p k) (c : Fin N → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ τ : zetaZeroConfig.carrier,
      ‖∫ u : ℝ, ((G u - probeSum p c u : ℝ) : ℂ) * cexp (((τ : ℂ) - 1 / 2) * u)‖ ≤
        2 * ε / ‖(6 : ℂ) + ((τ : ℂ) - 1 / 2)‖) :
    ‖windowVec hG - probeSumVec hp c‖ ≤
      2 * ε * Real.sqrt (5 * ∑' τ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult τ : ℝ) / (1 + Complex.normSq ((τ : ℂ) - 1 / 2))) := by
  have hM : 0 ≤ ∑' τ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult τ : ℝ) / (1 + Complex.normSq ((τ : ℂ) - 1 / 2)) :=
    tsum_nonneg fun τ => by have := Complex.normSq_nonneg ((τ : ℂ) - 1 / 2); positivity
  have hpt : ∀ τ : zetaZeroConfig.carrier, ‖(windowVec hG - probeSumVec hp c) τ‖ ^ 2 ≤
      20 * ε ^ 2 * ((zetaZeroConfig.mult τ : ℝ) / (1 + Complex.normSq ((τ : ℂ) - 1 / 2))) := by
    intro τ
    have hz := (one_add_normSq_le_five_mul (by norm_num : (1 : ℝ) ≤ 6)
      (abs_re_carrier_sub_half τ)).2
    push_cast at hz
    have hz' : 1 + Complex.normSq ((τ : ℂ) - 1 / 2) ≤ 5 * ‖(6 : ℂ) + ((τ : ℂ) - 1 / 2)‖ ^ 2 := by
      rw [Complex.sq_norm]; exact hz
    have hN : 0 < 1 + Complex.normSq ((τ : ℂ) - 1 / 2) := by
      have := Complex.normSq_nonneg ((τ : ℂ) - 1 / 2); linarith
    have hn : 0 < ‖(6 : ℂ) + ((τ : ℂ) - 1 / 2)‖ := by
      by_contra hc
      have h0 : ‖(6 : ℂ) + ((τ : ℂ) - 1 / 2)‖ = 0 := le_antisymm (not_lt.mp hc) (norm_nonneg _)
      rw [h0] at hz'
      linarith
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult τ := Nat.cast_nonneg _
    rw [windowVec_sub_probeSumVec_apply, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hm]
    set I := ‖∫ u : ℝ, ((G u - probeSum p c u : ℝ) : ℂ) * cexp (((τ : ℂ) - 1 / 2) * u)‖
    set n := ‖(6 : ℂ) + ((τ : ℂ) - 1 / 2)‖
    have hI : I * n ≤ 2 * ε := (le_div_iff₀ hn).mp (h τ)
    have hI0 : 0 ≤ I := norm_nonneg _
    have hI2' : (I * n) ^ 2 ≤ (2 * ε) ^ 2 := pow_le_pow_left₀ (by positivity) hI 2
    have hI2 : I ^ 2 * n ^ 2 ≤ 4 * ε ^ 2 := by rw [mul_pow, mul_pow] at hI2'; linarith
    have hI3 : I ^ 2 * (1 + Complex.normSq ((τ : ℂ) - 1 / 2)) ≤ 20 * ε ^ 2 := by
      have := mul_le_mul_of_nonneg_left hz' (sq_nonneg I)
      linarith
    rw [mul_div_assoc', le_div_iff₀ hN]
    have := mul_le_mul_of_nonneg_left hI3 hm
    linarith
  have hs := (lp.memℓp (windowVec hG - probeSumVec hp c)).summable
    (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
  refine lp.norm_le_of_tsum_le (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) (by positivity) ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  calc ∑' τ, ‖(windowVec hG - probeSumVec hp c) τ‖ ^ 2
      ≤ ∑' τ : zetaZeroConfig.carrier, 20 * ε ^ 2 *
          ((zetaZeroConfig.mult τ : ℝ) / (1 + Complex.normSq ((τ : ℂ) - 1 / 2))) :=
        Summable.tsum_le_tsum hpt hs (summable_mult_div_normSq.mul_left _)
    _ = (2 * ε * Real.sqrt (5 * ∑' τ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult τ : ℝ) / (1 + Complex.normSq ((τ : ℂ) - 1 / 2)))) ^ 2 := by
        rw [tsum_mul_left, mul_pow, Real.sq_sqrt (by positivity)]
        ring

/-! ### The confinement of a probe sum -/

theorem integrable_probe_mul_probe_mul_exp {p q : ℝ} (h : 8 < p + q) :
    Integrable (fun u => probe p u * probe q u * Real.exp (-(8 * u))) :=
  (integrable_probe_mul_exp (p := p + q) (c := -8) (by linarith)).congr
    (Eventually.of_forall fun u => by simp only [probe_mul_probe, neg_mul])

theorem probeSum_sq_mul_exp {N : ℕ} (p c : Fin N → ℝ) (u : ℝ) :
    probeSum p c u ^ 2 * Real.exp (-(8 * u)) =
      ∑ j, ∑ k, c j * c k * (probe (p j) u * probe (p k) u * Real.exp (-(8 * u))) := by
  rw [probeSum, sq, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem integrable_probeSum_sq_mul_exp {N : ℕ} {p : Fin N → ℝ} (hp : ∀ k, 4 < p k)
    (c : Fin N → ℝ) : Integrable (fun u => probeSum p c u ^ 2 * Real.exp (-(8 * u))) := by
  simp only [probeSum_sq_mul_exp]
  exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
    (integrable_probe_mul_probe_mul_exp (by linarith [hp j, hp k])).const_mul _

/-- The confinement of a probe sum: `Σ_{j,k} c_j c_k/(p_j + p_k − 8) = ∫_{u<0} P² e^{−8u}`. -/
theorem sum_div_eq_integral_probeSum_sq {N : ℕ} {p : Fin N → ℝ} (hp : ∀ k, 4 < p k)
    (c : Fin N → ℝ) :
    ∑ j, ∑ k, c j * c k / (p j + p k - 8) =
      ∫ u in Iio 0, probeSum p c u ^ 2 * Real.exp (-(8 * u)) := by
  have hI : ∀ j k, Integrable (fun u =>
      c j * c k * (probe (p j) u * probe (p k) u * Real.exp (-(8 * u)))) := fun j k =>
    (integrable_probe_mul_probe_mul_exp (by linarith [hp j, hp k])).const_mul _
  simp only [probeSum_sq_mul_exp]
  rw [integral_finsetSum _ fun j _ => (integrable_finsetSum _ fun k _ => hI j k).integrableOn]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => (hI j k).integrableOn]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, confinement_probe_probe (by linarith [hp j, hp k])]
  ring

/-- **The confinement of a nearby probe sum.** If `|G − P| ≤ ε e^{6u}` on `u < 0`, then
`∫_{u<0} P² e^{−8u} ≤ ∫ G² e^{−8u} + 2ε ∫ |G| e^{−2u} + ε²`. -/
theorem integral_probeSum_sq_le {A : ℝ} {G : ℝ → ℝ} (hG : IsWindowTest A G) {N : ℕ}
    {p : Fin N → ℝ} (hp : ∀ k, 4 < p k) (c : Fin N → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hD : ∀ u, u < 0 → |G u - probeSum p c u| ≤ ε * Real.exp (6 * u)) :
    ∫ u in Iio 0, probeSum p c u ^ 2 * Real.exp (-(8 * u)) ≤
      (∫ u, G u ^ 2 * Real.exp (-(8 * u))) + 2 * ε * (∫ u, |G u| * Real.exp (-(2 * u))) +
        ε ^ 2 := by
  have hc : Continuous G := hG.continuous
  have hcs : HasCompactSupport G := hG.hasCompactSupport
  have hG2 : Integrable (fun u => G u ^ 2 * Real.exp (-(8 * u))) :=
    (show Continuous (fun u => G u ^ 2 * Real.exp (-(8 * u))) by fun_prop).integrable_of_hasCompactSupport
      (hcs.mono fun u hu h0 => hu (by simp only [h0]; ring))
  have hG1 : Integrable (fun u => |G u| * Real.exp (-(2 * u))) :=
    (show Continuous (fun u => |G u| * Real.exp (-(2 * u))) by fun_prop).integrable_of_hasCompactSupport
      (hcs.mono fun u hu h0 => hu (by simp only [h0, abs_zero, zero_mul]))
  have hE : IntegrableOn (fun u : ℝ => Real.exp u) (Iio 0) :=
    ((integrableOn_exp_mul_Iic one_pos 0).congr_fun (fun u _ => by simp) measurableSet_Iic).mono_set
      Iio_subset_Iic_self
  have hR : IntegrableOn (fun u => G u ^ 2 * Real.exp (-(8 * u)) +
      2 * ε * (|G u| * Real.exp (-(2 * u))) + ε ^ 2 * Real.exp u) (Iio 0) :=
    ((hG2.integrableOn.add (hG1.integrableOn.const_mul _)).add (hE.const_mul _))
  have hpt : ∀ u ∈ Iio (0 : ℝ), probeSum p c u ^ 2 * Real.exp (-(8 * u)) ≤
      G u ^ 2 * Real.exp (-(8 * u)) + 2 * ε * (|G u| * Real.exp (-(2 * u))) +
        ε ^ 2 * Real.exp u := by
    intro u hu
    have hu' : u < 0 := hu
    set d := G u - probeSum p c u
    have hd := hD u hu'
    have hP : probeSum p c u = G u - d := by simp only [d]; ring
    have hw : 0 < Real.exp (-(8 * u)) := Real.exp_pos _
    have e1 : Real.exp (6 * u) * Real.exp (-(8 * u)) = Real.exp (-(2 * u)) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (6 * u) ^ 2 * Real.exp (-(8 * u)) ≤ Real.exp u := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    have hd0 : 0 ≤ |d| := abs_nonneg d
    have hGd : -(2 * G u * d) ≤ 2 * |G u| * |d| := by
      have := neg_abs_le (G u * d)
      rw [abs_mul] at this
      nlinarith
    have hdd : d ^ 2 ≤ (ε * Real.exp (6 * u)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ hd0 hd 2
    rw [hP]
    have hexp : (G u - d) ^ 2 * Real.exp (-(8 * u)) =
        G u ^ 2 * Real.exp (-(8 * u)) - 2 * G u * d * Real.exp (-(8 * u)) +
          d ^ 2 * Real.exp (-(8 * u)) := by ring
    rw [hexp]
    have t1 : -(2 * G u * d * Real.exp (-(8 * u))) ≤
        2 * ε * (|G u| * Real.exp (-(2 * u))) := by
      have := mul_le_mul_of_nonneg_right hGd hw.le
      have h2 : 2 * |G u| * |d| * Real.exp (-(8 * u)) ≤
          2 * |G u| * (ε * Real.exp (6 * u)) * Real.exp (-(8 * u)) := by
        have := abs_nonneg (G u)
        gcongr
      have h3 : 2 * |G u| * (ε * Real.exp (6 * u)) * Real.exp (-(8 * u)) =
          2 * ε * (|G u| * Real.exp (-(2 * u))) := by
        rw [← e1]; ring
      linarith
    have t2 : d ^ 2 * Real.exp (-(8 * u)) ≤ ε ^ 2 * Real.exp u := by
      have := mul_le_mul_of_nonneg_right hdd hw.le
      have h4 : (ε * Real.exp (6 * u)) ^ 2 * Real.exp (-(8 * u)) =
          ε ^ 2 * (Real.exp (6 * u) ^ 2 * Real.exp (-(8 * u))) := by ring
      have h5 := mul_le_mul_of_nonneg_left e2 (sq_nonneg ε)
      linarith
    linarith
  have hmono := setIntegral_mono_on (integrable_probeSum_sq_mul_exp hp c).integrableOn hR
    measurableSet_Iio hpt
  have hA1 : IntegrableOn (fun u => G u ^ 2 * Real.exp (-(8 * u)) +
      2 * ε * (|G u| * Real.exp (-(2 * u)))) (Iio 0) :=
    hG2.integrableOn.add (hG1.integrableOn.const_mul _)
  have hA2 : IntegrableOn (fun u => 2 * ε * (|G u| * Real.exp (-(2 * u)))) (Iio 0) :=
    hG1.integrableOn.const_mul _
  have hA3 : IntegrableOn (fun u : ℝ => ε ^ 2 * Real.exp u) (Iio 0) := hE.const_mul _
  rw [integral_add hA1 hA3, integral_add hG2.integrableOn hA2, integral_const_mul,
    integral_const_mul] at hmono
  have hEint : ∫ u in Iio (0 : ℝ), Real.exp u = 1 := by
    rw [← integral_Iic_eq_integral_Iio, integral_exp_Iic, Real.exp_zero]
  rw [hEint, mul_one] at hmono
  have hs1 : ∫ u in Iio (0 : ℝ), G u ^ 2 * Real.exp (-(8 * u)) ≤
      ∫ u, G u ^ 2 * Real.exp (-(8 * u)) :=
    setIntegral_le_integral hG2 (Eventually.of_forall fun u => by positivity)
  have hs2 : ∫ u in Iio (0 : ℝ), |G u| * Real.exp (-(2 * u)) ≤
      ∫ u, |G u| * Real.exp (-(2 * u)) :=
    setIntegral_le_integral hG1 (Eventually.of_forall fun u => by positivity)
  have hs2' := mul_le_mul_of_nonneg_left hs2 (by positivity : (0 : ℝ) ≤ 2 * ε)
  linarith

/-! ### The Pick form decides the confined form on window tests -/

/-- The real Pick form of the confined form on the integer nodes `7, …, N + 6`. -/
def confinedPickForm (R : ℝ) {N : ℕ} (c : Fin N → ℝ) : ℝ :=
  ∑ j, ∑ k, c j * c k *
    criticalHalfLineMixedEnergy R (probe ((j : ℝ) + 7)) (probe ((k : ℝ) + 7))

theorem confinedPickForm_eq (R : ℝ) {N : ℕ} (c : Fin N → ℝ)
    (hp : ∀ k : Fin N, 1 ≤ (k : ℝ) + 7) :
    confinedPickForm R c =
      (inner ℂ (reflectVec zetaZeroConfig (probeSumVec hp c)) (probeSumVec hp c)).re +
        criticalAliasCoefficient R *
          ∑ j : Fin N, ∑ k : Fin N, c j * c k / (((j : ℝ) + 7) + ((k : ℝ) + 7) - 8) := by
  have h4 : ∀ i : Fin N, (4 : ℝ) < (i : ℝ) + 7 := fun i => by
    linarith [Nat.cast_nonneg (α := ℝ) (i : ℕ)]
  have hh : ∀ i : Fin N, (1 / 2 : ℝ) < (i : ℝ) + 7 := fun i => by linarith [h4 i]
  rw [re_inner_reflect_probeSumVec hp c, Finset.mul_sum, ← Finset.sum_add_distrib]
  unfold confinedPickForm
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [criticalHalfLineMixedEnergy_probe R (h4 j) (h4 k), bareMixedEnergy_probe (hh j) (hh k)]
  ring

/-- **Pick positivity gives positivity on window tests.** If every real Pick matrix of the confined
form `Q_R` on the integer nodes `7, 8, …` is positive semidefinite, `Q_R ≥ 0` on every window
test. -/
theorem fullEnergy_window_nonneg_of_confinedPick_nonneg {R : ℝ} (hR : 0 < R)
    (h : ∀ (N : ℕ) (c : Fin N → ℝ), 0 ≤ confinedPickForm R c) {A : ℝ} {G : ℝ → ℝ}
    (hG : IsWindowTest A G) : 0 ≤ criticalHalfLineFullEnergy R G := by
  set a := criticalAliasCoefficient R with ha_def
  have ha : 0 ≤ a := (criticalAliasCoefficient_positive hR).le
  set y := windowVec hG
  set M := ∑' τ : zetaZeroConfig.carrier,
    (zetaZeroConfig.mult τ : ℝ) / (1 + Complex.normSq ((τ : ℂ) - 1 / 2))
  have hM : 0 ≤ M := tsum_nonneg fun τ => by
    have := Complex.normSq_nonneg ((τ : ℂ) - 1 / 2); positivity
  set B := 2 * Real.sqrt (5 * M)
  have hB : 0 ≤ B := by positivity
  set J := ∫ u, |G u| * Real.exp (-(2 * u))
  have hJ : 0 ≤ J := integral_nonneg fun u => by positivity
  set K := B * (2 * ‖y‖ + B) + a * (2 * J + 1)
  have hK : 0 ≤ K := by positivity
  have hQ : criticalHalfLineFullEnergy R G = (inner ℂ (reflectVec zetaZeroConfig y) y).re +
      a * ∫ u, G u ^ 2 * Real.exp (-(8 * u)) := by
    rw [fullEnergy_eq_weilQuad_add hG.contDiff hG.hasCompactSupport
      (windowTest_vanish_nonneg hG), weilQuad_eq_re_inner_windowVec hG]
  -- at every scale `ε ≤ 1` some Pick form is within `Kε` of `Q_R(G)`
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → -(K * ε) ≤ criticalHalfLineFullEnergy R G := by
    intro ε hε hε1
    obtain ⟨π, hd, hφ⟩ := exists_antiderivPoly_near hG hε
    have hp1 : ∀ k : Fin (π.natDegree + 1), 1 ≤ (k : ℝ) + 7 := fun k => by
      linarith [Nat.cast_nonneg (α := ℝ) (k : ℕ)]
    have hp4 : ∀ k : Fin (π.natDegree + 1), 4 < (k : ℝ) + 7 := fun k => by
      linarith [Nat.cast_nonneg (α := ℝ) (k : ℕ)]
    set c : Fin (π.natDegree + 1) → ℝ := fun k => π.coeff k / ((k : ℝ) + 1) with hc
    have hDneg : ∀ u, u < 0 →
        G u - probeSum (fun k : Fin (π.natDegree + 1) => (k : ℝ) + 7) c u =
          Real.exp (6 * u) * (windowProfile G (Real.exp u) - antiderivPoly π (Real.exp u)) := by
      intro u hu
      rw [← exp_mul_antiderivPoly_eq_probeSum π hu, mul_sub, windowProfile_exp]
    have hD0 : ∀ u, 0 ≤ u →
        G u - probeSum (fun k : Fin (π.natDegree + 1) => (k : ℝ) + 7) c u = 0 := by
      intro u hu
      simp only [probeSum, probe_of_nonneg hu, mul_zero, Finset.sum_const_zero, sub_zero]
      exact windowTest_vanish_nonneg hG u hu
    have hφd : ∀ x, HasDerivAt (fun x => windowProfile G x - antiderivPoly π x)
        (deriv (windowProfile G) x - π.eval x) x := fun x =>
      (((contDiff_windowProfile hG).differentiable two_ne_zero) x).hasDerivAt.sub
        (hasDerivAt_antiderivPoly π x)
    have hφ'c : Continuous fun x => deriv (windowProfile G) x - π.eval x :=
      ((contDiff_windowProfile hG).continuous_deriv one_le_two).sub (Polynomial.continuous π)
    have hdn := norm_windowVec_sub_probeSumVec_le hG hp1 c hε.le fun τ =>
      norm_integral_error_le hφd hφ'c hε.le hφ hd hDneg hD0 (re_carrier_sub_half_ge τ)
    have hdn' : ‖probeSumVec hp1 c - y‖ ≤ ε * B := by
      rw [norm_sub_rev]; simp only [B]; linarith
    have hK1 := re_inner_reflect_le y (probeSumVec hp1 c)
    have hDabs : ∀ u, u < 0 →
        |G u - probeSum (fun k : Fin (π.natDegree + 1) => (k : ℝ) + 7) c u| ≤
          ε * Real.exp (6 * u) := fun u hu => by
      rw [hDneg u hu, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm ε]
      exact mul_le_mul_of_nonneg_left
        (hφ _ ⟨(Real.exp_pos u).le, Real.exp_le_one_iff.mpr hu.le⟩) (Real.exp_pos _).le
    have hW := integral_probeSum_sq_le hG hp4 c hε.le hDabs
    rw [← sum_div_eq_integral_probeSum_sq hp4 c] at hW
    have hPick := confinedPickForm_eq R c hp1
    have h0 := h _ c
    have e1 : ‖probeSumVec hp1 c - y‖ * (2 * ‖y‖ + ‖probeSumVec hp1 c - y‖) ≤
        ε * B * (2 * ‖y‖ + B) := by
      have hεB : ε * B ≤ B := by nlinarith
      exact mul_le_mul hdn' (by linarith) (by positivity) (by positivity)
    have hε2 : ε ^ 2 ≤ ε := by nlinarith
    have e2 : a * ∑ j : Fin (π.natDegree + 1), ∑ k : Fin (π.natDegree + 1),
        c j * c k / (((j : ℝ) + 7) + ((k : ℝ) + 7) - 8) ≤
          a * (∫ u, G u ^ 2 * Real.exp (-(8 * u))) + a * (ε * (2 * J + 1)) := by
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ ha
      have := mul_le_mul_of_nonneg_left (le_refl J) hε.le
      nlinarith
    have eK : K * ε = ε * B * (2 * ‖y‖ + B) + a * (ε * (2 * J + 1)) := by
      simp only [K]; ring
    linarith
  -- conclude
  by_contra hneg
  have hlt : criticalHalfLineFullEnergy R G < 0 := not_le.mp hneg
  set Q := criticalHalfLineFullEnergy R G
  set ε := min 1 (-Q / (2 * (K + 1)))
  have hε : 0 < ε := lt_min one_pos (by apply div_pos <;> linarith)
  have hk := key ε hε (min_le_left _ _)
  have hε2 : ε ≤ -Q / (2 * (K + 1)) := min_le_right _ _
  have h1 : K * ε ≤ K * (-Q / (2 * (K + 1))) := mul_le_mul_of_nonneg_left hε2 hK
  have h3 : K * (-Q / (2 * (K + 1))) < -Q := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

/-- `Q_R ≥ 0` on the window tests of `[−A, 0]` puts `R` below the window threshold. -/
theorem le_windowThreshold_of_fullEnergy_nonneg {R : ℝ} (hR : 0 < R) {A : ℝ}
    (h : ∀ H : ℝ → ℝ, IsWindowTest A H → 0 ≤ criticalHalfLineFullEnergy R H) :
    (R : EReal) ≤ windowThreshold A := by
  unfold windowThreshold
  refine le_iInf fun H => le_iInf fun hH => le_iInf fun hQ => ?_
  rw [EReal.coe_le_coe_iff]
  have h1 := h H hH
  rw [fullEnergy_eq_weilQuad_add hH.contDiff hH.hasCompactSupport
    (windowTest_vanish_nonneg hH)] at h1
  have hs := splineAtom_pos
  have hS1 : (∫ u, tiltedUnitSpline u) ^ 2 ≠ 0 := fun h0 => by
    rw [splineAtom, h0, zero_div] at hs; exact lt_irrefl 0 hs
  have hS2 : (∫ u, tiltedUnitSpline u ^ 2) ≠ 0 := fun h0 => by
    rw [splineAtom, h0, div_zero] at hs; exact lt_irrefl 0 hs
  have hS0 : (∫ u, tiltedUnitSpline u) ≠ 0 := fun h0 => hS1 (by rw [h0]; ring)
  have ha : criticalAliasCoefficient R * splineAtom * R = 7 * tiltedJordanOne := by
    unfold criticalAliasCoefficient splineAtom
    field_simp
  have hM : WindowTowerOfSpecZ.exponentialMass 8 H = ∫ u, H u ^ 2 * Real.exp (-(8 * u)) := by
    unfold WindowTowerOfSpecZ.exponentialMass
    congr 1
    funext u
    ring
  unfold testCriticalMultiple
  rw [hM, le_div_iff₀ (mul_pos hs (by linarith))]
  calc R * (splineAtom * -weilQuad H) = (R * splineAtom) * (-weilQuad H) := by ring
    _ ≤ (R * splineAtom) * (criticalAliasCoefficient R * ∫ u, H u ^ 2 * Real.exp (-(8 * u))) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (criticalAliasCoefficient R * splineAtom * R) * ∫ u, H u ^ 2 * Real.exp (-(8 * u)) := by
        ring
    _ = 7 * tiltedJordanOne * ∫ u, H u ^ 2 * Real.exp (-(8 * u)) := by rw [ha]

/-- **The integer Pick matrices bound the critical ratio.** If every real Pick matrix of `Q_R` on
the integer nodes `7, 8, …` is positive semidefinite, `R` is at most every window threshold, so
at most the critical ratio `W₀`. -/
theorem le_iInf_windowThreshold_of_confinedPick_nonneg {R : ℝ} (hR : 0 < R)
    (h : ∀ (N : ℕ) (c : Fin N → ℝ), 0 ≤ confinedPickForm R c) :
    (R : EReal) ≤ ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A :=
  le_iInf fun _ => le_iInf fun _ => le_windowThreshold_of_fullEnergy_nonneg hR fun _ hH =>
    fullEnergy_window_nonneg_of_confinedPick_nonneg hR h hH

/-! ### Bilinearity of the mixed energy -/

section Bilinear
open CriticalArithmeticCorrelationTheory

theorem integrable_cx_mul_cexp_I {H : ℝ → ℝ} (hH : Integrable H) (r : ℝ) :
    Integrable (fun u : ℝ => (H u : ℂ) * cexp (I * r * u)) := by
  refine hH.norm.mono' (hH.ofReal.aestronglyMeasurable.mul
    (by fun_prop : Continuous fun u : ℝ => cexp (I * r * u)).aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul, Complex.norm_real, Complex.norm_exp]
  simp

theorem paperFT_cx_add_const_mul {F G : ℝ → ℝ} (hF : Integrable F) (hG : Integrable G) (c r : ℝ) :
    paperFT (ArithmeticCastelnuovoSeveri.cx fun u => F u + c * G u) r =
      paperFT (ArithmeticCastelnuovoSeveri.cx F) r + c * paperFT (ArithmeticCastelnuovoSeveri.cx G) r := by
  simp only [paperFT, ArithmeticCastelnuovoSeveri.cx]
  have h : (fun u : ℝ => ((F u + c * G u : ℝ) : ℂ) * cexp (I * r * u)) =
      fun u => (F u : ℂ) * cexp (I * r * u) + (c : ℂ) * ((G u : ℂ) * cexp (I * r * u)) := by
    funext u; push_cast; ring
  rw [h, integral_add (integrable_cx_mul_cexp_I hF r)
    ((integrable_cx_mul_cexp_I hG r).const_mul _), integral_const_mul]

theorem gammaMixedForm_add_const_mul_left {F G H : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) (hH : CriticalHalfLineEnergyDomain H) (c : ℝ) :
    gammaMixedForm (fun u => F u + c * G u) H = gammaMixedForm F H + c * gammaMixedForm G H := by
  have hpair : ∀ r : ℝ, gammaFourierPair (fun u => F u + c * G u) H r =
      gammaFourierPair F H r + c * gammaFourierPair G H r := fun r => by
    simp only [gammaFourierPair, paperFT_cx_add_const_mul hF.integrable hG.integrable c r,
      Complex.add_re, Complex.add_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    ring
  have hi1 := integrable_gammaFourierPair hF.integrable hH.integrable hF.gamma hH.gamma
  have hi2 := (integrable_gammaFourierPair hG.integrable hH.integrable hG.gamma hH.gamma).const_mul c
  simp only [gammaMixedForm, hpair, add_mul, mul_assoc]
  rw [integral_add hi1 hi2, integral_const_mul]
  ring

theorem coshHalfMoment_add_const_mul_of_weighted {F G : ℝ → ℝ} (hF : WeightedTwo F)
    (hG : WeightedTwo G) (c : ℝ) :
    coshHalfMoment (fun u => F u + c * G u) = coshHalfMoment F + c * coshHalfMoment G := by
  have hc : Continuous fun u : ℝ => Real.cosh (u / 2) :=
    Real.continuous_cosh.comp (continuous_id.div_const 2)
  have hiF := (abs_integral_mul_kernel_le hF hc abs_cosh_half_le_exp).1
  have hiG := (abs_integral_mul_kernel_le hG hc abs_cosh_half_le_exp).1
  unfold coshHalfMoment
  simp_rw [add_mul, mul_assoc]
  rw [integral_add hiF (hiG.const_mul c), integral_const_mul]

theorem sinhHalfMoment_add_const_mul_of_weighted {F G : ℝ → ℝ} (hF : WeightedTwo F)
    (hG : WeightedTwo G) (c : ℝ) :
    sinhHalfMoment (fun u => F u + c * G u) = sinhHalfMoment F + c * sinhHalfMoment G := by
  have hc : Continuous fun u : ℝ => Real.sinh (u / 2) :=
    Real.continuous_sinh.comp (continuous_id.div_const 2)
  have hiF := (abs_integral_mul_kernel_le hF hc abs_sinh_half_le_exp).1
  have hiG := (abs_integral_mul_kernel_le hG hc abs_sinh_half_le_exp).1
  unfold sinhHalfMoment
  simp_rw [add_mul, mul_assoc]
  rw [integral_add hiF (hiG.const_mul c), integral_const_mul]

theorem primeMixedForm_const_mul_right_of (f g : ℝ → ℝ) (c : ℝ) :
    primeMixedForm f (fun t => c * g t) = c * primeMixedForm f g := by
  have hterm (n : ℕ) : primePairTerm f (fun t => c * g t) n = c * primePairTerm f g n := by
    unfold primePairTerm
    simp_rw [mul_left_comm _ c, integral_const_mul]
    ring
  unfold primeMixedForm
  simp_rw [hterm]
  exact tsum_mul_left

theorem integrable_mul_mul_exp {F H : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hH : CriticalHalfLineEnergyDomain H) :
    Integrable (fun u => F u * H u * Real.exp (-(8 * u))) := by
  refine ((hF.exponential.add hH.exponential).div_const 2).mono'
    ((hF.meas.mul hH.meas).mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  have hw := Real.exp_pos (-(8 * u))
  have h1 : |F u| * |H u| ≤ (F u ^ 2 + H u ^ 2) / 2 := by
    nlinarith [sq_nonneg (|F u| - |H u|), sq_abs (F u), sq_abs (H u)]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hw]
  calc |F u| * |H u| * Real.exp (-(8 * u)) ≤ (F u ^ 2 + H u ^ 2) / 2 * Real.exp (-(8 * u)) :=
        mul_le_mul_of_nonneg_right h1 hw.le
    _ = (F u ^ 2 * Real.exp (-(8 * u)) + H u ^ 2 * Real.exp (-(8 * u))) / 2 := by ring

/-- **The mixed energy is linear in its first argument** on the energy domain. -/
theorem criticalHalfLineMixedEnergy_add_const_mul_left (R : ℝ) {F G H : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G)
    (hH : CriticalHalfLineEnergyDomain H) (c : ℝ) :
    criticalHalfLineMixedEnergy R (fun u => F u + c * G u) H =
      criticalHalfLineMixedEnergy R F H + c * criticalHalfLineMixedEnergy R G H := by
  have hconf : (∫ u in Iio 0, (F u + c * G u) * H u * Real.exp (-(8 * u))) =
      (∫ u in Iio 0, F u * H u * Real.exp (-(8 * u))) +
        c * ∫ u in Iio 0, G u * H u * Real.exp (-(8 * u)) := by
    have h : (fun u => (F u + c * G u) * H u * Real.exp (-(8 * u))) =
        fun u => F u * H u * Real.exp (-(8 * u)) + c * (G u * H u * Real.exp (-(8 * u))) := by
      funext u; ring
    rw [h, integral_add (integrable_mul_mul_exp hF hH).integrableOn
      ((integrable_mul_mul_exp hG hH).integrableOn.const_mul c), integral_const_mul]
  simp only [criticalHalfLineMixedEnergy]
  rw [gammaMixedForm_add_const_mul_left hF hG hH c,
    primeMixedForm_add_left hF.weighted (hG.weighted.const_mul c) hH.weighted,
    primeMixedForm_const_mul_left, primeMixedForm_add_right hH.weighted hF.weighted
      (hG.weighted.const_mul c), primeMixedForm_const_mul_right_of,
    coshHalfMoment_add_const_mul_of_weighted hF.weighted hG.weighted,
    sinhHalfMoment_add_const_mul_of_weighted hF.weighted hG.weighted, hconf]
  ring

end Bilinear

theorem criticalHalfLineMixedEnergy_comm (R : ℝ) (F G : ℝ → ℝ) :
    criticalHalfLineMixedEnergy R F G = criticalHalfLineMixedEnergy R G F := by
  rw [criticalHalfLineMixedEnergy_eq_bare_add, criticalHalfLineMixedEnergy_eq_bare_add,
    bareMixedEnergy_comm]
  congr 2
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  ring

theorem criticalHalfLineEnergyDomain_finsetSum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ}
    (hF : ∀ i, CriticalHalfLineEnergyDomain (F i)) (c : ι → ℝ) :
    CriticalHalfLineEnergyDomain (fun u => ∑ i ∈ s, c i * F i u) := by
  have hZ : CriticalHalfLineEnergyDomain (fun _ : ℝ => (0 : ℝ)) :=
    criticalHalfLineEnergyDomain_of_compact_negative contDiff_const HasCompactSupport.zero
      fun _ _ => rfl
  simpa only [zero_add] using criticalHalfLineEnergyDomain_add_sum hZ hF c s

theorem criticalHalfLineMixedEnergy_finsetSum_left (R : ℝ) {ι : Type*} (s : Finset ι)
    {F : ι → ℝ → ℝ} (hF : ∀ i, CriticalHalfLineEnergyDomain (F i)) (c : ι → ℝ) {H : ℝ → ℝ}
    (hH : CriticalHalfLineEnergyDomain H) :
    criticalHalfLineMixedEnergy R (fun u => ∑ i ∈ s, c i * F i u) H =
      ∑ i ∈ s, c i * criticalHalfLineMixedEnergy R (F i) H := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hZ : CriticalHalfLineEnergyDomain (fun _ : ℝ => (0 : ℝ)) :=
      criticalHalfLineEnergyDomain_of_compact_negative contDiff_const HasCompactSupport.zero
        fun _ _ => rfl
    have h0 := criticalHalfLineMixedEnergy_add_const_mul_left R hZ hZ hH 1
    simp only [mul_zero, add_zero, one_mul] at h0
    simp only [Finset.sum_empty]
    linarith
  | insert a s ha ih =>
    have hS := criticalHalfLineEnergyDomain_finsetSum s hF c
    have e : (fun u => ∑ i ∈ insert a s, c i * F i u) =
        fun u => (∑ i ∈ s, c i * F i u) + c a * F a u := by
      funext u; rw [Finset.sum_insert ha, add_comm]
    rw [e, criticalHalfLineMixedEnergy_add_const_mul_left R hS (hF a) hH, ih, Finset.sum_insert ha]
    ring

/-- **The confined energy of a probe sum is its Pick form.** -/
theorem criticalHalfLineFullEnergy_probeSum (R : ℝ) {N : ℕ} {p : Fin N → ℝ} (hp : ∀ k, 4 < p k)
    (c : Fin N → ℝ) :
    criticalHalfLineFullEnergy R (probeSum p c) =
      ∑ j, ∑ k, c j * c k * criticalHalfLineMixedEnergy R (probe (p j)) (probe (p k)) := by
  have hD : ∀ k, CriticalHalfLineEnergyDomain (probe (p k)) := fun k =>
    criticalHalfLineEnergyDomain_probe (hp k)
  have hP : CriticalHalfLineEnergyDomain (probeSum p c) :=
    criticalHalfLineEnergyDomain_finsetSum _ hD c
  rw [← criticalHalfLineMixedEnergy_self R hP]
  unfold probeSum
  rw [criticalHalfLineMixedEnergy_finsetSum_left R _ hD c
    (H := fun u => ∑ k, c k * probe (p k) u) hP]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [criticalHalfLineMixedEnergy_comm, criticalHalfLineMixedEnergy_finsetSum_left R _ hD c (hD j),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [criticalHalfLineMixedEnergy_comm]
  ring

theorem confinedPickForm_eq_fullEnergy (R : ℝ) {N : ℕ} (c : Fin N → ℝ) :
    confinedPickForm R c =
      criticalHalfLineFullEnergy R (probeSum (fun k : Fin N => (k : ℝ) + 7) c) := by
  rw [criticalHalfLineFullEnergy_probeSum R
    (fun k => by linarith [Nat.cast_nonneg (α := ℝ) (k : ℕ)]) c]
  rfl

/-! ### The critical ratio in Pick form -/

/-- Below every window threshold the confined form is nonnegative on the whole domain. -/
theorem fullEnergy_nonneg_of_le_iInf {R : ℝ} (hR : 0 < R)
    (hle : (R : EReal) ≤ ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) : 0 ≤ criticalHalfLineFullEnergy R F := by
  rcases hle.lt_or_eq with hlt | heq
  · set m := ∫ u, F u ^ 2
    have hm : 0 ≤ m := integral_nonneg fun u => sq_nonneg _
    set s := 1 / (Real.sqrt m + 1)
    have hs : 0 < s := by positivity
    have hint : (∫ u, (s * F u) ^ 2) = s ^ 2 * m := by
      simp_rw [mul_pow]; exact integral_const_mul _ _
    have hnorm : (∫ u, (s * F u) ^ 2) ≤ 1 := by
      rw [hint]
      have hsq := Real.sq_sqrt hm
      have hr := Real.sqrt_nonneg m
      simp only [s]
      rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      nlinarith
    have h := criticalHalfLineFullEnergy_nonneg_normalized_below_windowThreshold hR hlt
      (hF.const_mul s) hnorm
    rw [criticalHalfLineFullEnergy_const_mul] at h
    exact (mul_nonneg_iff_of_pos_left (by positivity)).mp h
  · exact criticalHalfLineFullEnergy_nonneg_at_windowThreshold hR heq.symm hF

/-- **The integer Pick matrices decide the confined form.** For `R > 0` every real Pick matrix
`(Q_R(e_m, e_n))_{m,n ≥ 7}` is positive semidefinite iff `R` is at most every window threshold. -/
theorem confinedPick_nonneg_iff {R : ℝ} (hR : 0 < R) :
    (∀ (N : ℕ) (c : Fin N → ℝ), 0 ≤ confinedPickForm R c) ↔
      (R : EReal) ≤ ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A := by
  refine ⟨le_iInf_windowThreshold_of_confinedPick_nonneg hR, fun hle N c => ?_⟩
  rw [confinedPickForm_eq_fullEnergy]
  exact fullEnergy_nonneg_of_le_iInf hR hle (criticalHalfLineEnergyDomain_finsetSum _
    (fun k => criticalHalfLineEnergyDomain_probe (by linarith [Nat.cast_nonneg (α := ℝ) (k : ℕ)])) c)

/-- **The critical ratio is the last ratio of positive integer Pick matrices.** Off RH, with
`W₀ = inf_A windowThreshold A`, `W₀` is the largest ratio at which every real Pick matrix
`((D(m) + D(n))/(m + n) + a(R)/(m + n − 8))_{m,n ≥ 7}` is positive semidefinite. -/
theorem isGreatest_confinedPick_criticalRatio {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) :
    IsGreatest {R : ℝ | 0 < R ∧ ∀ (N : ℕ) (c : Fin N → ℝ), 0 ≤ confinedPickForm R c} W₀ := by
  refine ⟨⟨hW, (confinedPick_nonneg_iff hW).mpr hthreshold.ge⟩, fun R hR => ?_⟩
  have h := (confinedPick_nonneg_iff hR.1).mp hR.2
  rw [hthreshold] at h
  exact EReal.coe_le_coe_iff.mp h

/-- Off RH the critical ratio is attained by the integer Pick matrices: some ratio `W₀ > 0` is the
largest at which all of them are positive semidefinite. -/
theorem riemannHypothesis_or_isGreatest_confinedPick :
    RiemannHypothesis ∨ ∃ W₀ : ℝ,
      IsGreatest {R : ℝ | 0 < R ∧ ∀ (N : ℕ) (c : Fin N → ℝ), 0 ≤ confinedPickForm R c} W₀ := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀, _, hW, ht, _⟩
  · exact Or.inl h
  · exact Or.inr ⟨W₀, isGreatest_confinedPick_criticalRatio hW ht⟩

/-! ### Finite node blocks approximate the critical ratio -/

/-- Pick positivity descends in the ratio: the confinement `a(R)/(m + n − 8)` grows as `R` falls. -/
theorem confinedPickForm_mono {R S : ℝ} (hR : 0 < R) (hRS : R ≤ S) {N : ℕ} (c : Fin N → ℝ) :
    confinedPickForm S c ≤ confinedPickForm R c := by
  have hp : ∀ k : Fin N, 1 ≤ (k : ℝ) + 7 := fun k => by
    linarith [Nat.cast_nonneg (α := ℝ) (k : ℕ)]
  have hp4 : ∀ k : Fin N, 4 < (k : ℝ) + 7 := fun k => by
    linarith [Nat.cast_nonneg (α := ℝ) (k : ℕ)]
  rw [confinedPickForm_eq S c hp, confinedPickForm_eq R c hp,
    sum_div_eq_integral_probeSum_sq hp4 c]
  have hI : 0 ≤ ∫ u in Iio (0 : ℝ),
      probeSum (fun k : Fin N => (k : ℝ) + 7) c u ^ 2 * Real.exp (-(8 * u)) :=
    setIntegral_nonneg measurableSet_Iio fun u _ => by positivity
  have ha := criticalAliasCoefficient_antitone hR hRS
  nlinarith

/-- Padding by zeros: the Pick form of a coefficient vector on the first `N` nodes is a Pick form on
any larger block. -/
theorem confinedPickForm_extend (R : ℝ) {N M : ℕ} (hNM : N ≤ M) (c : Fin N → ℝ) :
    ∃ d : Fin M → ℝ, confinedPickForm R d = confinedPickForm R c := by
  classical
  refine ⟨fun k => if h : (k : ℕ) < N then c ⟨k, h⟩ else 0, ?_⟩
  set f : ℕ → ℕ → ℝ := fun j k =>
    (if h : j < N then c ⟨j, h⟩ else 0) * (if h : k < N then c ⟨k, h⟩ else 0) *
      criticalHalfLineMixedEnergy R (probe ((j : ℝ) + 7)) (probe ((k : ℝ) + 7)) with hf
  have hM : confinedPickForm R (fun k : Fin M => if h : (k : ℕ) < N then c ⟨k, h⟩ else 0) =
      ∑ j ∈ Finset.range M, ∑ k ∈ Finset.range M, f j k := by
    unfold confinedPickForm
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Fin.sum_univ_eq_sum_range]
  have hN : confinedPickForm R c = ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, f j k := by
    unfold confinedPickForm
    rw [← Fin.sum_univ_eq_sum_range (fun j => ∑ k ∈ Finset.range N, f j k)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun k => f j k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [f, dif_pos j.2, dif_pos k.2]
  have hzero : ∀ j k, (N ≤ j ∨ N ≤ k) → f j k = 0 := by
    intro j k h
    rcases h with h | h
    · simp only [f, dif_neg (not_lt.mpr h), zero_mul]
    · simp only [f, dif_neg (not_lt.mpr h), mul_zero, zero_mul]
  rw [hM, hN]
  have hsub : Finset.range N ⊆ Finset.range M := Finset.range_subset_range.mpr hNM
  rw [← Finset.sum_subset hsub fun j _ hj => Finset.sum_eq_zero fun k _ =>
    hzero j k (Or.inl (by simpa using hj))]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (Finset.sum_subset hsub fun k _ hk => hzero j k (Or.inr (by simpa using hk))).symm

/-- **Finite node blocks approximate `W₀`.** Off RH, below the critical ratio every block of integer
Pick matrices is positive semidefinite, and above it all sufficiently large blocks
`(Q_R(e_m, e_n))_{7 ≤ m,n < N + 7}` fail: the finite-block critical ratios decrease to `W₀`. -/
theorem confinedPick_blocks_approximate_criticalRatio {W₀ : ℝ}
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) {R : ℝ}
    (hR : 0 < R) :
    (R ≤ W₀ → ∀ (N : ℕ) (c : Fin N → ℝ), 0 ≤ confinedPickForm R c) ∧
      (W₀ < R → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ c : Fin N → ℝ, confinedPickForm R c < 0) := by
  refine ⟨fun hle => (confinedPick_nonneg_iff hR).mpr (by rw [hthreshold]; exact_mod_cast hle),
    fun hlt => ?_⟩
  have hnot : ¬ ∀ (N : ℕ) (c : Fin N → ℝ), 0 ≤ confinedPickForm R c := fun h => by
    have := (confinedPick_nonneg_iff hR).mp h
    rw [hthreshold, EReal.coe_le_coe_iff] at this
    linarith
  push Not at hnot
  obtain ⟨N₀, c₀, hc₀⟩ := hnot
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨d, hd⟩ := confinedPickForm_extend R hN c₀
  exact ⟨d, hd ▸ hc₀⟩

#print axioms confinedPick_blocks_approximate_criticalRatio

#print axioms confinedPick_nonneg_iff
#print axioms isGreatest_confinedPick_criticalRatio
#print axioms riemannHypothesis_or_isGreatest_confinedPick

end GaloisForLFunctions.ExclusionOfTheCriticalState
