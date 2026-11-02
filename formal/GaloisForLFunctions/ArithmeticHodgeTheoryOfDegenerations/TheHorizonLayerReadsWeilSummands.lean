import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheZeroLedgerOfTheBulk
import GaloisForLFunctions.RHTower.CausalMobiusThetaSmoothGaugeProfile

/-!
# The horizon layer reads Weil summands

A horizon block is a vector supported near the top of the range: `x_n = h(log(n/N))/√n` with a
continuous `h` supported in `[−A, 0]`. Its atoms fill the window `[log N − A, log N]` and
synthesize the test `H(y) = e^{y/2} h(y)` translated to the horizon. On the zero side its Dirichlet
polynomial is a Riemann sum: `N^{−s} D_x(γ_s) = N⁻¹ Σ_{r≤N} F_s(r/N)` with
`F_s(x) = h(log x) x^{s−1}`, and `∫_0^1 F_s = ∫ h(y) e^{sy} dy = ĥ(s)`.

* **Riemann sum** (`tendsto_horizonDirichlet`): `N^{−s} D_x(γ_s) → ĥ(s)` for every `s`.
* **Weil summand of the synthesized test** (`Wsummand_halfWeight`): `W_ρ(H, H) = m_ρ ĥ(ρ) ĥ(1−ρ)`.
* **Horizon ledger** (`tendsto_horizonLedger`): along every schedule with `c_N/N → 0` the
  contribution of `ρ` to the normalized complete form of the block satisfies
  `c_N⁻¹ · W_ρ / ∫g² → ((∫φ)²/∫φ²) W_ρ(H, H)`.

Fixed conductor packets see a point of the strip only through a positive pole weight
(`TheZeroLedgerOfTheBulk`); a horizon block sees it through Weil's summand of the test it
synthesizes, which is a square on the line and indefinite for an off-line quadruple. The horizon
layer, not the bulk, is where the complete family can see an individual zero.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23 Set
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri

/-- Atomic weights of a horizon block, `x_n = h(log n − log N)/√n`. -/
def horizonWeights (h : ℝ → ℝ) (N n : ℕ) : ℝ := h (Real.log n - Real.log N) / Real.sqrt n

/-- The Riemann-sum profile `F_s(x) = h(log x) x^{s−1}` on `x > 0`, extended by `0`. -/
def horizonProfile (h : ℝ → ℝ) (s : ℂ) (x : ℝ) : ℂ :=
  if 0 < x then (h (Real.log x) : ℂ) * ((x : ℝ) : ℂ) ^ (s - 1) else 0

/-- The horizon transform `ĥ(s) = ∫ h(y) e^{sy} dy`. -/
def horizonTransform (h : ℝ → ℝ) (s : ℂ) : ℂ := ∫ y, (h y : ℂ) * Complex.exp (s * y)

/-- The synthesized test `H(y) = e^{y/2} h(y)`. -/
def halfWeight (h : ℝ → ℝ) (y : ℝ) : ℝ := Real.exp (y / 2) * h y

variable {h : ℝ → ℝ} {A : ℝ}

theorem horizonProfile_eq_zero_of_lt (hsupp : ∀ y, y ∉ Icc (-A) 0 → h y = 0) (s : ℂ) {x : ℝ}
    (hx : x < Real.exp (-A)) : horizonProfile h s x = 0 := by
  unfold horizonProfile
  split_ifs with h0
  · have : Real.log x < -A := by
      rw [Real.log_lt_iff_lt_exp h0]; exact hx
    rw [hsupp _ (fun hm => by linarith [hm.1]), Complex.ofReal_zero, zero_mul]
  · rfl

theorem continuous_horizonProfile (hh : Continuous h) (hsupp : ∀ y, y ∉ Icc (-A) 0 → h y = 0)
    (s : ℂ) : Continuous (horizonProfile h s) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_or_ge (0 : ℝ) x with hx | hx
  · have hev : horizonProfile h s =ᶠ[𝓝 x] fun t => (h (Real.log t) : ℂ) * ((t : ℝ) : ℂ) ^ (s - 1) :=
      (lt_mem_nhds hx).mono fun t ht => by simp only [horizonProfile, if_pos ht]
    refine ContinuousAt.congr ?_ hev.symm
    refine ContinuousAt.mul ?_ ?_
    · exact Complex.continuous_ofReal.continuousAt.comp
        (hh.continuousAt.comp (Real.continuousAt_log hx.ne'))
    · exact (Complex.continuousAt_ofReal_cpow_const x (s - 1) (Or.inr hx.ne'))
  · have hev : horizonProfile h s =ᶠ[𝓝 x] fun _ => 0 :=
      (gt_mem_nhds (lt_of_le_of_lt hx (Real.exp_pos (-A)))).mono fun t ht =>
        horizonProfile_eq_zero_of_lt hsupp s ht
    exact ContinuousAt.congr continuousAt_const hev.symm

theorem horizonProfile_eq_zero_of_notMem (hsupp : ∀ y, y ∉ Icc (-A) 0 → h y = 0) (s : ℂ) {x : ℝ}
    (hx : x ∉ Icc (0 : ℝ) 1) : horizonProfile h s x = 0 := by
  unfold horizonProfile
  split_ifs with h0
  · have h1 : 1 < x := by
      by_contra hc; exact hx ⟨h0.le, not_lt.mp hc⟩
    rw [hsupp _ (fun hm => by linarith [hm.2, Real.log_pos h1]), Complex.ofReal_zero, zero_mul]
  · rfl

/-- Riemann sums of a continuous complex function vanishing off `[0,1]`. -/
theorem tendsto_riemannSum_Icc_complex {F : ℝ → ℂ} (hF : Continuous F)
    (hsupp : ∀ x, x ∉ Icc (0 : ℝ) 1 → F x = 0) :
    Tendsto (fun N : ℕ => ((N : ℝ) : ℂ)⁻¹ * ∑ r ∈ Finset.Icc 1 N, F (r / N)) atTop
      (𝓝 (∫ x, F x)) := by
  have hre := RHTower.tendsto_riemannSum_Icc (Complex.continuous_re.comp hF)
    fun x hx => by simp [hsupp x hx]
  have him := RHTower.tendsto_riemannSum_Icc (Complex.continuous_im.comp hF)
    fun x hx => by simp [hsupp x hx]
  have hint : Integrable F := hF.integrable_of_hasCompactSupport
    (HasCompactSupport.intro isCompact_Icc fun x hx => hsupp x hx)
  have hre' : ∫ x, (F x).re = (∫ x, F x).re := by
    simpa only [RCLike.re_to_complex] using integral_re hint
  have him' : ∫ x, (F x).im = (∫ x, F x).im := by
    simpa only [RCLike.im_to_complex] using integral_im hint
  have hlim := ((Complex.continuous_ofReal.tendsto _).comp hre).add
    (((Complex.continuous_ofReal.tendsto _).comp him).mul_const Complex.I)
  simp only [Function.comp_def] at hlim
  rw [hre', him', Complex.re_add_im] at hlim
  refine hlim.congr fun N => ?_
  push_cast
  rw [← Complex.re_add_im (∑ r ∈ Finset.Icc 1 N, F (r / N))]
  simp only [Complex.re_sum, Complex.im_sum]
  push_cast
  ring

/-- The Dirichlet polynomial of a horizon block is a Riemann sum:
`N⁻¹ Σ_{r≤N} F_s(r/N) = N^{−s} D_x(γ_s)`. -/
theorem riemannSum_horizonProfile (h : ℝ → ℝ) (s : ℂ) {N : ℕ} (hN : 1 ≤ N) :
    ((N : ℝ) : ℂ)⁻¹ * ∑ r ∈ Finset.Icc 1 N, horizonProfile h s (r / N) =
      ((N : ℝ) : ℂ) ^ (-s) * dirichletPoly N (horizonWeights h N) (gammaOf s) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [dirichletPoly_gammaOf, mul_sum, mul_sum]
  refine sum_congr rfl fun r hr => ?_
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  have hq : (0 : ℝ) < r / N := div_pos hr0 hN0
  have e1 : horizonProfile h s (r / N) = (h (Real.log r - Real.log N) : ℂ) *
      Complex.exp (((Real.log r - Real.log N : ℝ) : ℂ) * (s - 1)) := by
    rw [horizonProfile, if_pos hq, RHTower.cpow_ofReal_eq_exp hq, Real.log_div hr0.ne' hN0.ne']
  have e2 : ((horizonWeights h N r : ℝ) : ℂ) * Complex.exp ((s - 1 / 2) * (Real.log r : ℂ)) =
      (h (Real.log r - Real.log N) : ℂ) * Complex.exp (((Real.log r : ℝ) : ℂ) * (s - 1)) := by
    rw [horizonWeights, Complex.ofReal_div, div_eq_mul_inv, mul_assoc, inv_sqrt_mul_exp hr1,
      RHTower.cpow_ofReal_eq_exp hr0]
  have e3 : ((N : ℝ) : ℂ)⁻¹ = Complex.exp (-((Real.log N : ℝ) : ℂ)) := by
    rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hN0]
  rw [e1, e3, RHTower.cpow_ofReal_eq_exp hN0, e2]
  have key : Complex.exp (-((Real.log N : ℝ) : ℂ)) *
      Complex.exp (((Real.log r - Real.log N : ℝ) : ℂ) * (s - 1)) =
      Complex.exp (((Real.log N : ℝ) : ℂ) * -s) * Complex.exp (((Real.log r : ℝ) : ℂ) * (s - 1)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (h (Real.log r - Real.log N) : ℂ) * key

/-- `∫ F_s = ĥ(s)`: the substitution `x = e^y`. -/
theorem integral_horizonProfile (hh : Continuous h) (hsupp : ∀ y, y ∉ Icc (-A) 0 → h y = 0)
    (hA : 0 ≤ A) (s : ℂ) : ∫ x, horizonProfile h s x = horizonTransform h s := by
  have hcont := continuous_horizonProfile hh hsupp s
  -- both integrals live on compact intervals
  have hL : ∫ x, horizonProfile h s x = ∫ x in Real.exp (-A)..Real.exp 0, horizonProfile h s x := by
    rw [intervalIntegral.integral_of_le (Real.exp_le_exp.mpr (by linarith)),
      ← integral_Icc_eq_integral_Ioc, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rcases lt_or_ge x (Real.exp (-A)) with h1 | h1
    · exact horizonProfile_eq_zero_of_lt hsupp s h1
    · refine horizonProfile_eq_zero_of_notMem hsupp s fun hm => hx ⟨h1, ?_⟩
      rw [Real.exp_zero]; exact hm.2
  have hR : horizonTransform h s = ∫ y in (-A)..0, (h y : ℂ) * Complex.exp (s * y) := by
    rw [horizonTransform, intervalIntegral.integral_of_le (by linarith),
      ← integral_Icc_eq_integral_Ioc, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro y hy
    rw [hsupp y hy, Complex.ofReal_zero, zero_mul]
  have hsub := intervalIntegral.integral_deriv_smul_comp (a := -A) (b := 0) (f := Real.exp)
    (f' := Real.exp) (g := horizonProfile h s) (fun y _ => Real.hasDerivAt_exp y)
    Real.continuous_exp.continuousOn hcont
  rw [hL, hR, ← hsub]
  refine intervalIntegral.integral_congr fun y _ => ?_
  simp only [Function.comp_apply, horizonProfile, if_pos (Real.exp_pos y), Real.log_exp,
    Complex.real_smul]
  rw [RHTower.cpow_ofReal_eq_exp (Real.exp_pos y), Real.log_exp, Complex.ofReal_exp,
    mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

/-- **Riemann sum of a horizon block**: `N^{−s} D_x(γ_s) → ĥ(s)`. -/
theorem tendsto_horizonDirichlet (hh : Continuous h) (hsupp : ∀ y, y ∉ Icc (-A) 0 → h y = 0)
    (hA : 0 ≤ A) (s : ℂ) :
    Tendsto (fun N : ℕ => ((N : ℝ) : ℂ) ^ (-s) * dirichletPoly N (horizonWeights h N) (gammaOf s))
      atTop (𝓝 (horizonTransform h s)) := by
  rw [← integral_horizonProfile hh hsupp hA s]
  refine (tendsto_riemannSum_Icc_complex (continuous_horizonProfile hh hsupp s)
    fun x hx => horizonProfile_eq_zero_of_notMem hsupp s hx).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact riemannSum_horizonProfile h s hN

/-- **Weil summand of the synthesized test**: `W_ρ(H, H) = m_ρ ĥ(ρ) ĥ(1 − ρ)`, `H = e^{y/2} h`. -/
theorem Wsummand_halfWeight (Z : ZeroConfig) (h : ℝ → ℝ) (ρ : ℂ) :
    Z.Wsummand (cx (halfWeight h)) (cx (halfWeight h)) ρ =
      (Z.mult ρ : ℂ) * (horizonTransform h ρ * horizonTransform h (1 - ρ)) := by
  have h1 : paperFT (cx (halfWeight h)) (gammaOf ρ) = horizonTransform h ρ := by
    unfold paperFT horizonTransform
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [cx, halfWeight, gammaOf]
    push_cast
    rw [mul_comm (Complex.exp _) (h y : ℂ), mul_assoc, ← Complex.exp_add]
    congr 2
    field_simp
    ring
  have h2 : conj (paperFT (cx (halfWeight h)) (conj (gammaOf ρ))) = horizonTransform h (1 - ρ) := by
    unfold paperFT horizonTransform
    rw [← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [cx, halfWeight, gammaOf, map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
      map_div₀, map_sub, map_neg, Complex.conj_I, Complex.conj_conj, map_one, map_ofNat, neg_neg]
    push_cast
    rw [mul_comm (Complex.exp _) (h y : ℂ), mul_assoc, ← Complex.exp_add]
    congr 2
    field_simp
    ring
  rw [ZeroConfig.Wsummand, h1, h2]
  ring

/-- The contribution of `ρ` to the normalized complete form of a horizon block. -/
def horizonLedger (Z : ZeroConfig) (φ h : ℝ → ℝ) (c : ℝ) (N : ℕ) (ρ : ℂ) : ℂ :=
  Z.Wsummand (cx (atomicTest N (horizonWeights h N) (atomDilate φ (c / N))))
      (cx (atomicTest N (horizonWeights h N) (atomDilate φ (c / N)))) ρ /
    ((∫ u, atomDilate φ (c / N) u ^ 2 : ℝ) : ℂ)

theorem inv_mul_horizonLedger (Z : ZeroConfig) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφ2 : 0 < ∫ u, φ u ^ 2) (h : ℝ → ℝ) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) (ρ : ℂ) :
    ((c⁻¹ : ℝ) : ℂ) * horizonLedger Z φ h c N ρ =
      (Z.mult ρ : ℂ) * (paperFT (cx φ) (((c / N : ℝ) : ℂ) * gammaOf ρ) *
        conj (paperFT (cx φ) (((c / N : ℝ) : ℂ) * conj (gammaOf ρ)))) /
        ((∫ u, φ u ^ 2 : ℝ) : ℂ) *
      ((((N : ℝ) : ℂ) ^ (-ρ) * dirichletPoly N (horizonWeights h N) (gammaOf ρ)) *
        (((N : ℝ) : ℂ) ^ (-(1 - ρ)) * dirichletPoly N (horizonWeights h N) (gammaOf (1 - ρ)))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hg : Continuous (atomDilate φ (c / N)) := by unfold atomDilate; fun_prop
  have hgc : HasCompactSupport (atomDilate φ (c / N)) := hasCompactSupport_atomDilate hw.ne' hφc
  have hNc : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have hpow : ((N : ℝ) : ℂ) ^ (-ρ) * ((N : ℝ) : ℂ) ^ (-(1 - ρ)) = ((N : ℝ) : ℂ)⁻¹ := by
    rw [← Complex.cpow_add _ _ hNc, show -ρ + -(1 - ρ) = (-1 : ℂ) by ring, Complex.cpow_neg_one]
  unfold horizonLedger
  rw [Wsummand_atomicTest Z hg hgc, paperFT_atomDilate hw, paperFT_atomDilate hw,
    conj_dirichletPoly_conj_gammaOf, integral_atomDilate_sq φ hw]
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hI : ((∫ u, φ u ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hφ2.ne'
  rw [show ((N : ℝ) : ℂ) ^ (-ρ) * dirichletPoly N (horizonWeights h N) (gammaOf ρ) *
      (((N : ℝ) : ℂ) ^ (-(1 - ρ)) * dirichletPoly N (horizonWeights h N) (gammaOf (1 - ρ))) =
      (((N : ℝ) : ℂ) ^ (-ρ) * ((N : ℝ) : ℂ) ^ (-(1 - ρ))) *
        (dirichletPoly N (horizonWeights h N) (gammaOf ρ) *
          dirichletPoly N (horizonWeights h N) (gammaOf (1 - ρ))) by ring, hpow]
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  field_simp

/-- **Horizon ledger.** Along every schedule with `c_N/N → 0`, a point `ρ` contributes
`c_N ((∫φ)²/∫φ²) W_ρ(H, H) + o(c_N)` to the normalized complete form of the horizon block of `h`,
`H(y) = e^{y/2} h(y)`. -/
theorem tendsto_horizonLedger (Z : ZeroConfig) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφ2 : 0 < ∫ u, φ u ^ 2) (hh : Continuous h)
    (hsupp : ∀ y, y ∉ Icc (-A) 0 → h y = 0) (hA : 0 ≤ A) (ρ : ℂ) {c : ℕ → ℝ}
    (hc : ∀ N, 0 < c N) (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ((c N)⁻¹ : ℂ) * horizonLedger Z φ h (c N) N ρ) atTop
      (𝓝 ((((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) *
        Z.Wsummand (cx (halfWeight h)) (cx (halfWeight h)) ρ)) := by
  have hF : Continuous (paperFT (cx φ)) :=
    (RHTower.EvenSector.differentiable_paperFT_of_compact (Complex.continuous_ofReal.comp hφ)
      (hφc.comp_left Complex.ofReal_zero)).continuous
  have hw : Tendsto (fun N : ℕ => ((c N / N : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa using hcN.ofReal
  have h1 : Tendsto (fun N : ℕ => paperFT (cx φ) (((c N / N : ℝ) : ℂ) * gammaOf ρ)) atTop
      (𝓝 (paperFT (cx φ) 0)) := by
    have := hw.mul_const (gammaOf ρ)
    rw [zero_mul] at this
    exact (hF.tendsto 0).comp this
  have h2 : Tendsto (fun N : ℕ => conj (paperFT (cx φ) (((c N / N : ℝ) : ℂ) * conj (gammaOf ρ))))
      atTop (𝓝 (conj (paperFT (cx φ) 0))) := by
    have := hw.mul_const (conj (gammaOf ρ))
    rw [zero_mul] at this
    exact (Complex.continuous_conj.tendsto _).comp ((hF.tendsto 0).comp this)
  have hlim := (((h1.mul h2).const_mul (Z.mult ρ : ℂ)).div_const ((∫ u, φ u ^ 2 : ℝ) : ℂ)).mul
    ((tendsto_horizonDirichlet hh hsupp hA ρ).mul (tendsto_horizonDirichlet hh hsupp hA (1 - ρ)))
  rw [paperFT_cx_zero, Complex.conj_ofReal] at hlim
  have hval : (Z.mult ρ : ℂ) * (((∫ u, φ u : ℝ) : ℂ) * ((∫ u, φ u : ℝ) : ℂ)) /
        ((∫ u, φ u ^ 2 : ℝ) : ℂ) * (horizonTransform h ρ * horizonTransform h (1 - ρ)) =
      (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) *
        Z.Wsummand (cx (halfWeight h)) (cx (halfWeight h)) ρ := by
    rw [Wsummand_halfWeight]; push_cast; ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [← inv_mul_horizonLedger Z hφ hφc hφ2 h (hc N) hN ρ]
  push_cast
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
