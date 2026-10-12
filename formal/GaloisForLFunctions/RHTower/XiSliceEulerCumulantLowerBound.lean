import GaloisForLFunctions.RHTower.XiSliceSaddleArcBoundsEulerRegion
import GaloisForLFunctions.RHTower.XiSliceStripGrowthBounds

/-!
# Low-order derivatives of the slice at Euler points

Let `S(t, z) = ξ(½+z+it) ξ(½−z+it)`, `L(z) = S'(z)/S(z)` (`xiSliceLogDeriv`), and let `x` be a real
point with `½ + 2η ≤ x ≤ t/2`.  On the disc `|w| ≤ η` around `x` the slice has no zeros and `L`
varies by at most `M' = log 4 + π + 4C_η` (`xiSliceLogDeriv_disc_bounds_euler`), while
`h₁ = L(x)` is real and close to `log t`.

**Theorem** (`iteratedDeriv_xiSliceProduct_ge_cumulant`).  For `0 < ρ < η` and every order
`n ≤ h₁ρ/(2e^{ρM'/2})`,

  `Re S^{(n)}(x) ≥ S(x) h₁ⁿ/2`.

Proof.  `S(x + w) = S(x) e^{h₁w} E(w)` with `E' = E·(L(x+w) − h₁)`, `E(0) = 1`, `E'(0) = 0`.  Along
the segment `s ↦ sw` this gives `E(w) = exp ∫₀¹ w(L(x+sw) − h₁) ds`, so `|E| ≤ e^{ρM'}` on `|w| ≤ ρ`
(`norm_cumulantFactor_le`), and Cauchy gives `|E^{(k)}(0)| ≤ k! e^{ρM'} ρ^{−k}`.  By Leibniz,
`S^{(n)}(x) = S(x) Σ_k C(n,k) h₁^{n−k} E^{(k)}(0)`, and with `C(n,k) k! ≤ nᵏ` the terms `k ≥ 2` cost at
most `S(x) h₁ⁿ e^{ρM'} Σ_{k≥2} (n/(h₁ρ))ᵏ ≤ S(x) h₁ⁿ/2`.
-/

open Complex Real Metric
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- `S' = S·L` right of the critical strip. -/
theorem hasDerivAt_xiSliceProduct_logDeriv {t : ℝ} {w : ℂ} (hw : 1 / 2 < w.re) :
    HasDerivAt (xiSliceProduct t) (xiSliceProduct t w * xiSliceLogDeriv t w) w := by
  have hS := scaledLogDeriv_xiSliceProduct (t := t) hw
  have hne : xiSliceProduct t w ≠ 0 := xiSliceProduct_ne_zero_of_re hw
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw; linarith
  have hd := (differentiable_xiSliceProduct t w).hasDerivAt
  unfold HTGeometry.scaledLogDeriv at hS
  have heq : deriv (xiSliceProduct t) w = xiSliceProduct t w * xiSliceLogDeriv t w := by
    field_simp at hS
    linear_combination hS
  rw [← heq]
  exact hd

/-- The cumulant factor `E(w) = S(x+w) e^{−h₁w}/S(x)`. -/
def cumulantFactor (t x h₁ : ℝ) (w : ℂ) : ℂ :=
  xiSliceProduct t ((x : ℂ) + w) * Complex.exp (-(h₁ : ℂ) * w) / xiSliceProduct t (x : ℂ)

theorem differentiable_cumulantFactor (t x h₁ : ℝ) : Differentiable ℂ (cumulantFactor t x h₁) := by
  unfold cumulantFactor
  have hg := differentiable_xiSliceProduct t
  intro w
  exact (((hg ((x : ℂ) + w)).comp w ((differentiable_const _).add differentiable_id w)).mul
    (by fun_prop)).div_const _

theorem cumulantFactor_zero {t x h₁ : ℝ} (hx : 1 / 2 < x) : cumulantFactor t x h₁ 0 = 1 := by
  unfold cumulantFactor
  have hne : xiSliceProduct t (x : ℂ) ≠ 0 := xiSliceProduct_ne_zero_of_re (by simpa using hx)
  simp [hne]

/-- `E' = E·(L(x+w) − h₁)` on `x + Re w > ½`. -/
theorem hasDerivAt_cumulantFactor {t x h₁ : ℝ} {w : ℂ}
    (hw : 1 / 2 < x + w.re) :
    HasDerivAt (cumulantFactor t x h₁)
      (cumulantFactor t x h₁ w * (xiSliceLogDeriv t ((x : ℂ) + w) - h₁)) w := by
  have hz : 1 / 2 < ((x : ℂ) + w).re := by simpa using hw
  have hS : HasDerivAt (fun w : ℂ => xiSliceProduct t ((x : ℂ) + w))
      (xiSliceProduct t ((x : ℂ) + w) * xiSliceLogDeriv t ((x : ℂ) + w)) w := by
    have := (hasDerivAt_xiSliceProduct_logDeriv (t := t) hz).comp w
      ((hasDerivAt_id w).const_add (x : ℂ))
    simpa [Function.comp_def] using this
  have hE : HasDerivAt (fun w : ℂ => Complex.exp (-(h₁ : ℂ) * w))
      (Complex.exp (-(h₁ : ℂ) * w) * (-(h₁ : ℂ))) w := by
    have := ((hasDerivAt_id w).const_mul (-(h₁ : ℂ))).cexp
    simpa [mul_comm] using this
  have h := (hS.mul hE).div_const (xiSliceProduct t (x : ℂ))
  unfold cumulantFactor
  exact h.congr_deriv (by ring)

/-- **The cumulant factor is bounded on the disc.**  `|E(w)| ≤ e^{ρM'}` for `|w| ≤ ρ < η`, with
`M' = log 4 + π + 4C_η` and `h₁ = Re L(x)`. -/
theorem norm_cumulantFactor_le {t η x ρ : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2) (ht : 8 ≤ t)
    (hx : 1 / 2 + 2 * η ≤ x) (hxt : x ≤ t / 2) (hρ : 0 < ρ) (hρη : ρ < η) {w : ℂ}
    (hw : ‖w‖ ≤ ρ) :
    ‖cumulantFactor t x (xiSliceLogDeriv t x).re w‖
      ≤ Real.exp (ρ * (Real.log 4 + Real.pi + 4 * xiEulerConstant η)) := by
  set h₁ : ℝ := (xiSliceLogDeriv t x).re with hh₁
  set M' : ℝ := Real.log 4 + Real.pi + 4 * xiEulerConstant η with hM'
  have hx' : 1 / 2 < x := by linarith
  obtain ⟨him, -, -⟩ := xiSliceLogDeriv_real_bounds_euler (t := t) (R := x) hη ht (by linarith)
    hxt
  have hLx : xiSliceLogDeriv t (x : ℂ) = (h₁ : ℂ) := by
    apply Complex.ext
    · simp [hh₁]
    · simp [him]
  -- the ODE along the segment `s ↦ s w`
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℂ, G = fun s : ℝ => cumulantFactor t x h₁ ((s : ℂ) * w) :=
    ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ → ℂ,
      Q = fun s : ℝ => w * (xiSliceLogDeriv t ((x : ℂ) + (s : ℂ) * w) - h₁) := ⟨_, rfl⟩
  have hb : (0 : ℝ) < η / ρ := by positivity
  have hsw : ∀ s ∈ Set.Ioo (-(η / ρ)) (η / ρ), ‖(s : ℂ) * w‖ < η := by
    intro s hs
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hs' : |s| < η / ρ := abs_lt.mpr ⟨hs.1, hs.2⟩
    calc |s| * ‖w‖ ≤ |s| * ρ := mul_le_mul_of_nonneg_left hw (abs_nonneg s)
      _ < η / ρ * ρ := mul_lt_mul_of_pos_right hs' hρ
      _ = η := by field_simp
  have hre : ∀ s ∈ Set.Ioo (-(η / ρ)) (η / ρ), 1 / 2 < x + ((s : ℂ) * w).re := by
    intro s hs
    have h1 := (abs_le.mp ((Complex.abs_re_le_norm ((s : ℂ) * w)).trans (hsw s hs).le)).1
    linarith
  have hGd : ∀ s ∈ Set.Ioo (-(η / ρ)) (η / ρ), HasDerivAt G (G s * Q s) s := by
    intro s hs
    have hin : HasDerivAt (fun y : ℝ => (y : ℂ) * w) (1 * w) s :=
      ((hasDerivAt_id s).ofReal_comp).mul_const w
    have h1 := (hasDerivAt_cumulantFactor (t := t) (h₁ := h₁) (hre s hs)).comp s hin
    rw [hG, hQ]
    exact h1.congr_deriv (by ring)
  have hQc : ContinuousOn Q (Set.Ioo (-(η / ρ)) (η / ρ)) := by
    have hL := differentiableOn_xiSliceLogDeriv t
    rw [hQ]
    refine continuousOn_const.mul (ContinuousOn.sub ?_ continuousOn_const)
    refine hL.continuousOn.comp (by fun_prop) fun s hs => ?_
    show 1 / 2 < ((x : ℂ) + (s : ℂ) * w).re
    simpa using hre s hs
  have hG0 : G 0 = 1 := by
    rw [hG]
    simp only [Complex.ofReal_zero, zero_mul]
    exact cumulantFactor_zero hx'
  have h1mem : (1 : ℝ) ∈ Set.Ioo (-(η / ρ)) (η / ρ) := by
    constructor
    · have : (0 : ℝ) < η / ρ := hb
      linarith
    · rw [lt_div_iff₀ hρ]; linarith
  have hexp := HTGeometry.eq_exp_integral_of_hasDerivAt_mul_Ioo (by linarith) hb hQc hGd hG0 h1mem
  have hG1 : G 1 = cumulantFactor t x h₁ w := by rw [hG]; simp
  rw [hG1] at hexp
  rw [hexp, Complex.norm_exp]
  refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)
  have hQb : ∀ s ∈ Set.uIoc (0 : ℝ) 1, ‖Q s‖ ≤ ρ * M' := by
    intro s hs
    rw [Set.uIoc_of_le zero_le_one] at hs
    have hsw : ‖(s : ℂ) * w‖ ≤ ρ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs.1]
      calc s * ‖w‖ ≤ 1 * ρ := mul_le_mul hs.2 hw (norm_nonneg _) zero_le_one
        _ = ρ := one_mul ρ
    have hball : (x : ℂ) + (s : ℂ) * w ∈ closedBall (x : ℂ) η := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      linarith
    have hd := (xiSliceLogDeriv_disc_bounds_euler hη hη1 ht hx hxt hball).2
    rw [hLx] at hd
    rw [hQ, norm_mul]
    exact mul_le_mul hw hd (norm_nonneg _) hρ.le
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hQb
  simp only [sub_zero, abs_one, mul_one] at hint
  exact hint

/-- **Low-order lower bound at an Euler point.**  For `½ + 2η ≤ x ≤ t/2`, `0 < ρ < η`, `h₁ = Re L(x) > 0`
and `n ≤ h₁ρ/(2e^{ρM'/2})`: `Re S^{(n)}(x) ≥ S(x) h₁ⁿ/2`. -/
theorem iteratedDeriv_xiSliceProduct_ge_cumulant {t η x ρ : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2)
    (ht : 8 ≤ t) (hx : 1 / 2 + 2 * η ≤ x) (hxt : x ≤ t / 2) (hρ : 0 < ρ) (hρη : ρ < η)
    (hh : 0 < (xiSliceLogDeriv t x).re) (n : ℕ)
    (hn : (n : ℝ) ≤ (xiSliceLogDeriv t x).re * ρ
      / (2 * Real.exp (ρ * (Real.log 4 + Real.pi + 4 * xiEulerConstant η) / 2))) :
    xiSliceReal t x * (xiSliceLogDeriv t x).re ^ n / 2
      ≤ (iteratedDeriv n (xiSliceProduct t) (x : ℂ)).re := by
  set h₁ : ℝ := (xiSliceLogDeriv t x).re with hh₁
  set M' : ℝ := Real.log 4 + Real.pi + 4 * xiEulerConstant η with hM'
  set E := cumulantFactor t x h₁ with hEdef
  have hx' : 1 / 2 < x := by linarith
  have hSx : xiSliceProduct t (x : ℂ) = ((xiSliceReal t x : ℝ) : ℂ) :=
    xiSliceProduct_ofReal_eq_xiSliceReal t x
  have hSxpos : 0 < xiSliceReal t x := xiSliceReal_pos t hx'
  have hSne : xiSliceProduct t (x : ℂ) ≠ 0 := xiSliceProduct_ne_zero_of_re (by simpa using hx')
  have hEd := differentiable_cumulantFactor t x h₁
  -- the factorisation `S(x + w) = S(x) e^{h₁ w} E(w)`
  have hfac : (fun w : ℂ => xiSliceProduct t ((x : ℂ) + w))
      = fun w => xiSliceProduct t (x : ℂ) * (Complex.exp ((h₁ : ℂ) * w) * E w) := by
    funext w
    simp only [hEdef, cumulantFactor]
    have he : Complex.exp ((h₁ : ℂ) * w) * Complex.exp (-(h₁ : ℂ) * w) = 1 := by
      rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
    field_simp
    rw [mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  have hshift : iteratedDeriv n (xiSliceProduct t) (x : ℂ)
      = iteratedDeriv n (fun w : ℂ => xiSliceProduct t ((x : ℂ) + w)) 0 := by
    have h := congrFun (iteratedDeriv_comp_const_add n (xiSliceProduct t) (x : ℂ)) 0
    simpa using h.symm
  have hLeib : iteratedDeriv n (fun w : ℂ => Complex.exp ((h₁ : ℂ) * w) * E w) 0
      = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * (h₁ : ℂ) ^ i
        * iteratedDeriv (n - i) E 0 := by
    rw [iteratedDeriv_fun_mul (by fun_prop) (hEd.contDiff.contDiffAt)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iteratedDeriv_cexp_const_mul]
    simp only [mul_zero, Complex.exp_zero, mul_one]
    rfl
  have hS : iteratedDeriv n (xiSliceProduct t) (x : ℂ)
      = xiSliceProduct t (x : ℂ) * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * (h₁ : ℂ) ^ i
        * iteratedDeriv (n - i) E 0 := by
    rw [hshift, hfac, iteratedDeriv_const_mul_field, hLeib]
  -- Cauchy bounds for the cumulant factor
  have hρ' : ρ < η := hρη
  have hEb : ∀ z ∈ sphere (0 : ℂ) ρ, ‖E z‖ ≤ Real.exp (ρ * M') := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    exact norm_cumulantFactor_le hη hη1 ht hx hxt hρ hρη hz.le
  have hcauchy : ∀ k : ℕ, ‖iteratedDeriv k E 0‖ ≤ k.factorial * Real.exp (ρ * M') / ρ ^ k :=
    fun k => Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hρ hEd.diffContOnCl hEb
  have hE0 : iteratedDeriv 0 E 0 = 1 := by
    rw [iteratedDeriv_zero]; exact cumulantFactor_zero hx'
  have hE1 : iteratedDeriv 1 E 0 = 0 := by
    rw [iteratedDeriv_one]
    have hd := hasDerivAt_cumulantFactor (t := t) (h₁ := h₁) (w := 0) (by simpa using hx')
    rw [hd.deriv, add_zero]
    obtain ⟨him, -, -⟩ := xiSliceLogDeriv_real_bounds_euler (t := t) (R := x) hη ht (by linarith)
      hxt
    have hLx : xiSliceLogDeriv t (x : ℂ) = (h₁ : ℂ) := by
      apply Complex.ext
      · simp [hh₁]
      · simp [him]
    rw [hLx, sub_self, mul_zero]
  -- reflect the Leibniz sum: `Σ_k C(n,k) h₁^{n−k} E^{(k)}(0)`
  set T : ℕ → ℂ := fun k => (n.choose k : ℂ) * (h₁ : ℂ) ^ (n - k) * iteratedDeriv k E 0 with hTdef
  have hrefl : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * (h₁ : ℂ) ^ i
      * iteratedDeriv (n - i) E 0 = ∑ k ∈ Finset.range (n + 1), T k := by
    rw [← Finset.sum_range_reflect T (n + 1)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simp only [hTdef, Nat.add_sub_cancel]
    rw [Nat.sub_sub_self hin, Nat.choose_symm hin]
  rw [hrefl] at hS
  set q : ℝ := n / (h₁ * ρ) with hq
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hexpM : 0 < Real.exp (ρ * M') := Real.exp_pos _
  have hsq : Real.exp (ρ * M') = Real.exp (ρ * M' / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have hqle : q ≤ 1 / (2 * Real.exp (ρ * M' / 2)) := by
    rw [hq, div_le_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at hn
    calc (n : ℝ) ≤ h₁ * ρ / (2 * Real.exp (ρ * M' / 2)) := by
          rw [le_div_iff₀ (by positivity)]; linarith
      _ = 1 / (2 * Real.exp (ρ * M' / 2)) * (h₁ * ρ) := by ring
  have hexp1 : 1 ≤ Real.exp (ρ * M' / 2) := Real.one_le_exp (by
    have : 0 ≤ M' := by
      rw [hM']
      have := xiEulerConstant_pos hη
      have : 0 < Real.log 4 := Real.log_pos (by norm_num)
      linarith [Real.pi_pos]
    positivity)
  have hqhalf : q ≤ 1 / 2 := hqle.trans (one_div_le_one_div_of_le (by norm_num) (by linarith))
  have hq2 : Real.exp (ρ * M') * (2 * q ^ 2) ≤ 1 / 2 := by
    have h1 : q ^ 2 ≤ (1 / (2 * Real.exp (ρ * M' / 2))) ^ 2 := pow_le_pow_left₀ hq0 hqle 2
    rw [hsq]
    have hE2 : 0 < Real.exp (ρ * M' / 2) := Real.exp_pos _
    calc Real.exp (ρ * M' / 2) ^ 2 * (2 * q ^ 2)
        ≤ Real.exp (ρ * M' / 2) ^ 2 * (2 * (1 / (2 * Real.exp (ρ * M' / 2))) ^ 2) := by gcongr
      _ = 1 / 2 := by field_simp
  -- bound of the terms `k ≥ 2`
  have hTb : ∀ k : ℕ, 2 ≤ k → k ≤ n → ‖T k‖ ≤ h₁ ^ n * Real.exp (ρ * M') * q ^ k := by
    intro k hk2 hkn
    simp only [hTdef]
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh,
      Complex.norm_natCast]
    have hc := hcauchy k
    have hdesc : (n.choose k : ℝ) * k.factorial ≤ (n : ℝ) ^ k := by
      have h1 := Nat.descFactorial_le_pow n k
      rw [Nat.descFactorial_eq_factorial_mul_choose] at h1
      have : ((k.factorial * n.choose k : ℕ) : ℝ) ≤ ((n ^ k : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at this
      linarith
    have hpowsplit : h₁ ^ n = h₁ ^ (n - k) * h₁ ^ k := by
      rw [← pow_add]; congr 1; omega
    have hρk : 0 < ρ ^ k := pow_pos hρ k
    calc (n.choose k : ℝ) * h₁ ^ (n - k) * ‖iteratedDeriv k E 0‖
        ≤ (n.choose k : ℝ) * h₁ ^ (n - k) * (k.factorial * Real.exp (ρ * M') / ρ ^ k) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ = ((n.choose k : ℝ) * k.factorial) * h₁ ^ (n - k) * Real.exp (ρ * M') / ρ ^ k := by ring
      _ ≤ (n : ℝ) ^ k * h₁ ^ (n - k) * Real.exp (ρ * M') / ρ ^ k := by gcongr
      _ = h₁ ^ n * Real.exp (ρ * M') * q ^ k := by
          rw [hq, hpowsplit, div_pow, mul_pow]
          field_simp
  -- the main terms and the tail
  have hT0 : T 0 = (h₁ : ℂ) ^ n := by simp [hTdef, hE0]
  have hT1 : T 1 = 0 := by simp [hTdef, hE1]
  have hSre : (iteratedDeriv n (xiSliceProduct t) (x : ℂ)).re
      = xiSliceReal t x * (∑ k ∈ Finset.range (n + 1), T k).re := by
    rw [hS, hSx, Complex.re_ofReal_mul]
  rw [hSre]
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · simp only [zero_add, Finset.range_one, Finset.sum_singleton, hT0, pow_zero, Complex.one_re]
    nlinarith [hSxpos]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ', hT0, hT1, add_zero]
  have htail : ‖∑ k ∈ Finset.range m, T (k + 1 + 1)‖
      ≤ h₁ ^ (m + 1) * Real.exp (ρ * M') * (2 * q ^ 2) := by
    calc ‖∑ k ∈ Finset.range m, T (k + 1 + 1)‖ ≤ ∑ k ∈ Finset.range m, ‖T (k + 1 + 1)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range m, h₁ ^ (m + 1) * Real.exp (ρ * M') * q ^ (k + 2) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkm := Finset.mem_range.mp hk
          exact hTb (k + 1 + 1) (by omega) (by omega)
      _ = h₁ ^ (m + 1) * Real.exp (ρ * M') * q ^ 2 * ∑ k ∈ Finset.range m, q ^ k := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ ≤ h₁ ^ (m + 1) * Real.exp (ρ * M') * q ^ 2 * 2 := by
          have hgeom : ∑ k ∈ Finset.range m, q ^ k ≤ 2 := by
            have h1 := geom_sum_Ico_le_of_lt_one (m := 0) (n := m) hq0 (by linarith)
            rw [Finset.range_eq_Ico]
            calc ∑ i ∈ Finset.Ico 0 m, q ^ i ≤ q ^ 0 / (1 - q) := h1
              _ ≤ 2 := by
                  rw [pow_zero, div_le_iff₀ (by linarith)]
                  linarith
          exact mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = h₁ ^ (m + 1) * Real.exp (ρ * M') * (2 * q ^ 2) := by ring
  have hre_tail := (Complex.re_le_norm (∑ k ∈ Finset.range m, T (k + 1 + 1))).trans htail
  have hre_tail' := neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans htail)
  rw [Complex.add_re]
  have hpowre : ((h₁ : ℂ) ^ (m + 1)).re = h₁ ^ (m + 1) := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [hpowre]
  have hh1 : 0 < h₁ ^ (m + 1) := pow_pos hh _
  have key : h₁ ^ (m + 1) * Real.exp (ρ * M') * (2 * q ^ 2) ≤ h₁ ^ (m + 1) / 2 := by
    have := mul_le_mul_of_nonneg_left hq2 hh1.le
    linarith
  have hsum : h₁ ^ (m + 1) / 2 ≤ (∑ k ∈ Finset.range m, T (k + 1 + 1)).re + h₁ ^ (m + 1) := by
    linarith
  have := mul_le_mul_of_nonneg_left hsum hSxpos.le
  linarith

end

end RHTower
