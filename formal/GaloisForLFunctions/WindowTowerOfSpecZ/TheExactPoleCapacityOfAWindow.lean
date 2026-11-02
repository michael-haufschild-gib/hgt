import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.TheCanonicalDegreeBoundsTheWindowForm

/-!
# The exact pole capacity of a window

The pole term of Weil's form is `2Ĥ(0)Ĥ(1) = 2(∫He^{u/2})(∫He^{−u/2})`, which is invariant under
translation. Centring it at the midpoint of the window `[−A, 0]` gives

`½⟨2 cosh(u/2), H⟩² − ½⟨2 sinh(u/2), H⟩² = ½⟨c_A, H⟩² − ½⟨s_A, H⟩²`,
`c_A(u) = 2 cosh((u + A/2)/2)`, `s_A(u) = 2 sinh((u + A/2)/2)` (`pole_eq_centred`).

On the window `‖s_A‖² = 4 sinh(A/2) − 2A` (`integral_centredSinh_sq`), so

* **Exact pole capacity** (`centredSinhPairing_sq_le`, `pole_ge`): `½⟨s_A,H⟩² ≤ (2 sinh(A/2) − A)‖H‖²` and
  the pole term is at least `−(2 sinh(A/2) − A)‖H‖²`; the constant is `‖s_A‖²/2`, attained by the
  centred sinh itself (Cauchy–Schwarz).
* **The sharp window floor** (`weilQuad_ge_neg_sharpWindowFloor`):
  `Q(H) ≥ −(deg K_A + 2 sinh(A/2) − A)‖H‖²`; and the pencil `κQ + c∫e^{−py}H²` is nonnegative as soon
  as `c ≥ κ(deg K_A + 2 sinh(A/2) − A)` (`pencil_nonneg_sharp`).
* **The floor has exponent one half** (`halfChebyshev_le`, `sharpWindowFloor_le`):
  `ψ_{1/2}(x) ≤ 2√x log x`, hence `deg K_A + 2 sinh(A/2) − A ≤ −Ω(0) + (4A + 1)e^{A/2}`. Window
  negativity grows at most like `A e^{A/2}`: the trivial strip, with explicit constants. The rate
  theory of the restricted Weil ground energy (ACCE `UnconditionalEqualityOfPolarAndFullGroundEnergyRates`:
  `zero width ≤ rate ≤ ½`, RH iff rate `0`) is the exponent form of this floor.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis RHTower.WeilMarkovPole

variable {A : ℝ} {H : ℝ → ℝ}

/-- The centred cosh `c_A(u) = 2 cosh((u + A/2)/2)`. -/
def centredCosh (A u : ℝ) : ℝ := 2 * Real.cosh ((u + A / 2) / 2)

/-- The centred sinh `s_A(u) = 2 sinh((u + A/2)/2)`. -/
def centredSinh (A u : ℝ) : ℝ := 2 * Real.sinh ((u + A / 2) / 2)

theorem continuous_centredSinh (A : ℝ) : Continuous (centredSinh A) := by
  unfold centredSinh; fun_prop

theorem centredCosh_eq (A u : ℝ) :
    centredCosh A u = Real.exp (A / 4) * Real.exp (u / 2) + Real.exp (-(A / 4)) * Real.exp (-u / 2) := by
  rw [centredCosh, Real.cosh_eq, ← Real.exp_add, ← Real.exp_add]
  ring_nf

theorem centredSinh_eq (A u : ℝ) :
    centredSinh A u = Real.exp (A / 4) * Real.exp (u / 2) - Real.exp (-(A / 4)) * Real.exp (-u / 2) := by
  rw [centredSinh, Real.sinh_eq, ← Real.exp_add, ← Real.exp_add]
  ring_nf

/-- **The pole plane centred at the window**: `½⟨c,H⟩² − ½⟨s,H⟩² = ½⟨c_A,H⟩² − ½⟨s_A,H⟩²`. -/
theorem pole_eq_centred (hc : Continuous H) (hcs : HasCompactSupport H) (A : ℝ) :
    coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2 =
      (∫ u, H u * centredCosh A u) ^ 2 / 2 - (∫ u, H u * centredSinh A u) ^ 2 / 2 := by
  have hp : Integrable fun u => H u * Real.exp (u / 2) :=
    (hc.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
  have hm : Integrable fun u => H u * Real.exp (-u / 2) :=
    (hc.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
  set a := ∫ u, H u * Real.exp (u / 2)
  set b := ∫ u, H u * Real.exp (-u / 2)
  have hC : ∫ u, H u * centredCosh A u = Real.exp (A / 4) * a + Real.exp (-(A / 4)) * b := by
    simp_rw [centredCosh_eq, mul_add]
    rw [integral_add (by simpa [mul_left_comm] using hp.const_mul (Real.exp (A / 4)))
      (by simpa [mul_left_comm] using hm.const_mul (Real.exp (-(A / 4))))]
    simp_rw [mul_left_comm (H _)]
    rw [integral_const_mul, integral_const_mul]
  have hS : ∫ u, H u * centredSinh A u = Real.exp (A / 4) * a - Real.exp (-(A / 4)) * b := by
    simp_rw [centredSinh_eq, mul_sub]
    rw [integral_sub (by simpa [mul_left_comm] using hp.const_mul (Real.exp (A / 4)))
      (by simpa [mul_left_comm] using hm.const_mul (Real.exp (-(A / 4))))]
    simp_rw [mul_left_comm (H _)]
    rw [integral_const_mul, integral_const_mul]
  have he : Real.exp (A / 4) * Real.exp (-(A / 4)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [← pole_eq_pairings H hc hcs, hC, hS]
  linear_combination (-2 * a * b) * he

/-! ### The norm of the centred sinh on the window -/

/-- `(2 sinh(x/2))² = 2 cosh x − 2`. -/
theorem two_sinh_half_sq (x : ℝ) : (2 * Real.sinh (x / 2)) ^ 2 = 2 * Real.cosh x - 2 := by
  have h := Real.cosh_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  rw [h, Real.cosh_sq]
  ring

/-- **The centred sinh has squared norm `4 sinh(A/2) − 2A` on the window.** -/
theorem integral_centredSinh_sq (hA : 0 ≤ A) :
    ∫ u in Icc (-A) 0, centredSinh A u ^ 2 = 4 * Real.sinh (A / 2) - 2 * A := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have hderiv : ∀ u ∈ uIcc (-A) 0, HasDerivAt (fun u => 2 * Real.sinh (u + A / 2) - 2 * u)
      (centredSinh A u ^ 2) u := fun u _ => by
    have h1 : HasDerivAt (fun u => u + A / 2) 1 u := (hasDerivAt_id u).add_const _
    have h2 : HasDerivAt (fun y => Real.sinh (y + A / 2)) (Real.cosh (u + A / 2) * 1) u :=
      h1.sinh
    have h3 : HasDerivAt (fun u => 2 * Real.sinh (u + A / 2) - 2 * u)
        (2 * (Real.cosh (u + A / 2) * 1) - 2 * 1) u :=
      (h2.const_mul 2).fun_sub ((hasDerivAt_id' u).const_mul 2)
    refine h3.congr_deriv ?_
    rw [centredSinh, two_sinh_half_sq]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (((continuous_centredSinh A).pow 2).intervalIntegrable _ _)]
  simp only [zero_add, mul_zero, sub_zero, show -A + A / 2 = -(A / 2) by ring, Real.sinh_neg]
  ring

/-- **Exact pole capacity**: `⟨s_A, H⟩² ≤ (4 sinh(A/2) − 2A)‖H‖²` on window tests. -/
theorem centredSinhPairing_sq_le (hH : IsWindowTest A H) (hA : 0 ≤ A) :
    (∫ u, H u * centredSinh A u) ^ 2 ≤ (4 * Real.sinh (A / 2) - 2 * A) * ∫ u, H u ^ 2 := by
  set S : ℝ → ℝ := (Icc (-A) 0).indicator (centredSinh A) with hSdef
  have hcS : Continuous (centredSinh A) := continuous_centredSinh A
  have iH := integrable_sq hH.continuous hH.hasCompactSupport
  have iS2 : Integrable fun u => S u ^ 2 := by
    have : (fun u => S u ^ 2) = (Icc (-A) 0).indicator fun u => centredSinh A u ^ 2 := by
      funext u; by_cases hu : u ∈ Icc (-A) 0 <;> simp [hSdef, hu]
    rw [this]
    exact (integrable_indicator_iff measurableSet_Icc).mpr
      ((hcS.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
  have hHS : (fun u => H u * centredSinh A u) = fun u => H u * S u := funext fun u => by
    by_cases hu : u ∈ Icc (-A) 0
    · simp [hSdef, hu]
    · simp [hSdef, hu, hH.vanish u hu]
  have iHS : Integrable fun u => H u * S u := by
    rw [← hHS]
    exact (hH.continuous.mul hcS).integrable_of_hasCompactSupport hH.hasCompactSupport.mul_right
  have hS2 : ∫ u, S u ^ 2 = 4 * Real.sinh (A / 2) - 2 * A := by
    have : (fun u => S u ^ 2) = (Icc (-A) 0).indicator fun u => centredSinh A u ^ 2 := by
      funext u; by_cases hu : u ∈ Icc (-A) 0 <;> simp [hSdef, hu]
    rw [this, integral_indicator measurableSet_Icc, integral_centredSinh_sq hA]
  have hcs := abs_integral_mul_le iH iS2 iHS
  rw [hHS]
  have h2 := pow_le_pow_left₀ (abs_nonneg _) hcs 2
  rw [sq_abs, mul_pow, Real.sq_sqrt (integral_nonneg fun u => sq_nonneg _),
    Real.sq_sqrt (integral_nonneg fun u => sq_nonneg _), hS2] at h2
  linarith

/-- **The pole term on a window is at least `−(2 sinh(A/2) − A)‖H‖²`.** -/
theorem pole_ge (hH : IsWindowTest A H) (hA : 0 ≤ A) :
    -((2 * Real.sinh (A / 2) - A) * ∫ u, H u ^ 2) ≤
      coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2 := by
  rw [pole_eq_centred hH.continuous hH.hasCompactSupport A]
  have h := centredSinhPairing_sq_le hH hA
  nlinarith [sq_nonneg (∫ u, H u * centredCosh A u)]

/-! ### The sharp window floor -/

/-- The **sharp window floor** `deg K_A + 2 sinh(A/2) − A`. -/
def sharpWindowFloor (A : ℝ) : ℝ := canonicalDegree A + (2 * Real.sinh (A / 2) - A)

theorem sinh_sub_self_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.sinh x - x := by
  have := Real.self_le_sinh_iff.mpr hx
  linarith

theorem sharpWindowFloor_nonneg (hA : 0 ≤ A) : 0 ≤ sharpWindowFloor A := by
  have h := sinh_sub_self_nonneg (x := A / 2) (by linarith)
  have := canonicalDegree_pos A
  rw [sharpWindowFloor]
  linarith

/-- **The sharp window floor**: `Q(H) ≥ −(deg K_A + 2 sinh(A/2) − A)‖H‖²` on window tests. -/
theorem weilQuad_ge_neg_sharpWindowFloor (hH : IsWindowTest A H) (hA : 0 ≤ A) :
    -(sharpWindowFloor A * ∫ u, H u ^ 2) ≤ weilQuad H := by
  rw [weilQuad_eq_fold_sub_canonical hH]
  have hJ := levyJump_nonneg H
  have hF : 0 ≤ ∑ n ∈ Finset.Icc 2 (windowLevel A),
      primeJumpWeight n * foldEnergy A (Real.log n) H :=
    Finset.sum_nonneg fun n _ => mul_nonneg (primeJumpWeight_nonneg n) (foldEnergy_nonneg _ _ _)
  have hk := integral_canonicalDensity_mul_le hH
  have hp := pole_ge hH hA
  rw [sharpWindowFloor, canonicalDegree_eq_halfChebyshev]
  nlinarith

/-- **The sharp pencil**: `κQ(H) + c∫e^{−py}H² ≥ 0` for `c ≥ κ(deg K_A + 2 sinh(A/2) − A)`. -/
theorem pencil_nonneg_sharp (hH : IsWindowTest A H) (hA : 0 ≤ A) {κ c p : ℝ} (hκ : 0 < κ)
    (hp : 0 ≤ p) (hc : κ * sharpWindowFloor A ≤ c) :
    0 ≤ κ * weilQuad H + c * ∫ y, Real.exp (-(p * y)) * H y ^ 2 := by
  have iH := integrable_sq hH.continuous hH.hasCompactSupport
  have hHc := hH.continuous
  have hcont : Continuous fun y => Real.exp (-(p * y)) * H y ^ 2 := by fun_prop
  have hcs : HasCompactSupport fun y => Real.exp (-(p * y)) * H y ^ 2 :=
    HasCompactSupport.intro (isCompact_Icc (a := -A) (b := 0)) fun y hy => by
      rw [hH.vanish y hy]; ring
  have iE : Integrable fun y => Real.exp (-(p * y)) * H y ^ 2 :=
    hcont.integrable_of_hasCompactSupport hcs
  have hmono : ∫ y, H y ^ 2 ≤ ∫ y, Real.exp (-(p * y)) * H y ^ 2 :=
    integral_mono iH iE fun y => by
      by_cases hy : y ∈ Icc (-A) 0
      · have : 1 ≤ Real.exp (-(p * y)) := Real.one_le_exp (by nlinarith [hy.2])
        nlinarith [sq_nonneg (H y)]
      · simp [hH.vanish y hy]
  have hQ := mul_le_mul_of_nonneg_left (weilQuad_ge_neg_sharpWindowFloor hH hA) hκ.le
  have hW := sharpWindowFloor_nonneg hA
  have hM : 0 ≤ ∫ y, H y ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hc0 : 0 ≤ c := (mul_nonneg hκ.le hW).trans hc
  have h1 := mul_le_mul_of_nonneg_left hmono hc0
  have h2 := mul_le_mul_of_nonneg_right hc hM
  linarith

/-! ### The floor has exponent one half -/

/-- `1/√n ≤ 2(√n − √(n−1))` for `n ≥ 1`. -/
theorem inv_sqrt_le_two_mul_sub (n : ℕ) :
    1 / Real.sqrt (n + 1) ≤ 2 * (Real.sqrt (n + 1) - Real.sqrt n) := by
  have h1 : 0 < Real.sqrt (n + 1) := Real.sqrt_pos.mpr (by positivity)
  have h0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hs1 : Real.sqrt (n + 1) ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
  have hs0 : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by positivity)
  rw [div_le_iff₀ h1]
  nlinarith [sq_nonneg (Real.sqrt (n + 1) - Real.sqrt n)]

/-- `Σ_{1 ≤ n ≤ N} 1/√n ≤ 2√N`. -/
theorem sum_inv_sqrt_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, 1 / Real.sqrt n ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_succ]
    have := inv_sqrt_le_two_mul_sub N
    linarith

/-- **`ψ_{1/2}(x) ≤ 2√x log x`** for `x ≥ 1`. -/
theorem halfChebyshev_le {x : ℝ} (hx : 1 ≤ x) :
    halfChebyshev x ≤ 2 * Real.sqrt x * Real.log x := by
  rw [halfChebyshev]
  have hterm : ∀ n ∈ Finset.Icc 2 ⌊x⌋₊, primeJumpWeight n ≤ Real.log x * (1 / Real.sqrt n) :=
    fun n hn => by
      have hn2 := (Finset.mem_Icc.mp hn).1
      have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff (by linarith)).mp (Finset.mem_Icc.mp hn).2
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      rw [primeJumpWeight, mul_one_div]
      refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
      exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn0 hnx)
  have hsub : ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, 1 / Real.sqrt n ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 1 / Real.sqrt n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by norm_num) le_rfl)
      fun _ _ _ => by positivity
  have hfl : Real.sqrt ⌊x⌋₊ ≤ Real.sqrt x := Real.sqrt_le_sqrt (Nat.floor_le (by linarith))
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  calc ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, primeJumpWeight n
      ≤ ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, Real.log x * (1 / Real.sqrt n) := Finset.sum_le_sum hterm
    _ = Real.log x * ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, 1 / Real.sqrt n := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.log x * (2 * Real.sqrt x) := by
        refine mul_le_mul_of_nonneg_left ?_ hlog
        linarith [sum_inv_sqrt_le ⌊x⌋₊]
    _ = 2 * Real.sqrt x * Real.log x := by ring

/-- **The floor grows at most like `A e^{A/2}`**: `deg K_A + 2 sinh(A/2) − A ≤ −Ω(0) + (4A + 1)e^{A/2}`. -/
theorem sharpWindowFloor_le (hA : 0 ≤ A) :
    sharpWindowFloor A ≤ -EF.gammaBracket 0 + (4 * A + 1) * Real.exp (A / 2) := by
  have hψ := halfChebyshev_le (Real.one_le_exp hA)
  rw [Real.log_exp, show Real.sqrt (Real.exp A) = Real.exp (A / 2) by
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf] at hψ
  have hsinh : 2 * Real.sinh (A / 2) - A ≤ Real.exp (A / 2) := by
    rw [Real.sinh_eq]
    have := Real.exp_pos (-(A / 2))
    linarith
  rw [sharpWindowFloor, canonicalDegree_eq_halfChebyshev]
  nlinarith [Real.exp_pos (A / 2)]

end GaloisForLFunctions.WindowTowerOfSpecZ
