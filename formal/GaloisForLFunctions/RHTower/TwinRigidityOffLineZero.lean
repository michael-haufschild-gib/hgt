import GaloisForLFunctions.RHTower.TwinRigidityZetaPower
import GaloisForLFunctions.RHTower.CompletedZetaGrowth

/-!
# Every real twin `ζ^d + E` has a zero off the critical line

Let `E(s) = Σ e(n) n^{−s}` be a nonzero Dirichlet series with real coefficients, `e(1) = 0`,
absolutely convergent on `Re s > σ₀`, such that `Γ_ℝ(s)^d E(s)` extends to an entire function
`E₀` of finite order with `E₀(1 − s) = E₀(s)`.  Then the completion of the twin `T = ζ^d + E`,

`Λ(s) = (2ξ(s))^d + (s(s − 1))^d E₀(s)`,

has a zero off the critical line (`exists_zero_offLine`).  This is unconditional: if every zero of
`Λ` were critical, twin rigidity would give `T = ζ^d`, hence `E = 0`.  In degree `3` such twins `E`
exist in infinite-dimensional families (`DegreeThreeHankel.gammaRCube_functional_equation_abundance`).
-/

open Complex Filter Topology Set LSeries

noncomputable section

namespace RHTower.TwinRigidity

/-- The coefficients of `ζ^d`, the `d`-fold divisor function. -/
def zetaPowCoeff (d : ℕ) : ℕ → ℝ := fun n => ((ArithmeticFunction.zeta ^ d : ArithmeticFunction ℕ) n : ℝ)

theorem zetaPowCoeff_one (d : ℕ) : zetaPowCoeff d 1 = 1 := by
  induction d with
  | zero => simp [zetaPowCoeff]
  | succ d ih =>
    simp only [zetaPowCoeff] at ih ⊢
    rw [pow_succ, ArithmeticFunction.mul_apply_one]
    push_cast
    rw [ih]
    simp

/-- `L(ζ^d) = ζ^d`, absolutely convergent on `Re s > 1`. -/
theorem lseries_zetaPowCoeff (d : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (cplx (zetaPowCoeff d)) s ∧
      LSeries (cplx (zetaPowCoeff d)) s = riemannZeta s ^ d := by
  induction d with
  | zero =>
    have e : cplx (zetaPowCoeff 0) = LSeries.delta := by
      funext n
      simp only [cplx, zetaPowCoeff, pow_zero, LSeries.delta, ArithmeticFunction.one_apply]
      split_ifs <;> simp
    rw [e, LSeries_delta, pow_zero]
    exact ⟨by
      refine (summable_of_ne_finset_zero (s := {1}) fun n hn => ?_)
      simp only [Finset.mem_singleton] at hn
      simp [LSeries.term, LSeries.delta, hn], rfl⟩
  | succ d ih =>
    have hz : LSeriesSummable (fun n => ((ArithmeticFunction.zeta n : ℕ) : ℂ)) s :=
      ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
    have e : cplx (zetaPowCoeff (d + 1)) =
        LSeries.convolution (cplx (zetaPowCoeff d))
          (fun n => ((ArithmeticFunction.zeta n : ℕ) : ℂ)) := by
      funext n
      rw [LSeries.convolution_def]
      simp only [cplx, zetaPowCoeff, pow_succ, ArithmeticFunction.mul_apply]
      push_cast
      rfl
    rw [e]
    refine ⟨ih.1.convolution hz, ?_⟩
    rw [LSeries_convolution' ih.1 hz, ih.2, ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs,
      pow_succ]

/-- Absorbing the order-one envelope and a polynomial into a finite-order bound. -/
theorem rpow_le_one_add_rpow {x a b : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hab : a ≤ b) :
    x ^ a ≤ 1 + x ^ b := by
  rcases le_or_gt x 1 with h1 | h1
  · have := Real.rpow_le_one hx h1 ha
    linarith [Real.rpow_nonneg hx b]
  · have := Real.rpow_le_rpow_of_exponent_le h1.le hab
    linarith

/-- **Every real twin `ζ^d + E` with `E ≠ 0` has a zero off the critical line.** -/
theorem exists_zero_offLine {d : ℕ} (hd : 0 < d) {e : ℕ → ℝ} (he1 : e 1 = 0)
    (hne : ∃ n, n ≠ 0 ∧ e n ≠ 0) {σ₀ : ℝ} (hsum : ∀ s : ℂ, σ₀ < s.re → LSeriesSummable (cplx e) s)
    {E₀ : ℂ → ℂ} (hE : Differentiable ℂ E₀)
    (hcomp : ∀ s : ℂ, σ₀ < s.re → E₀ s = Complex.Gammaℝ s ^ d * LSeries (cplx e) s)
    (hfe : ∀ s, E₀ (1 - s) = E₀ s) (hfin : ∃ ρ C : ℝ, ∀ s, ‖E₀ s‖ ≤ C * Real.exp (‖s‖ ^ ρ)) :
    ∃ s : ℂ, (2 * xi s) ^ d + (s * (s - 1)) ^ d * E₀ s = 0 ∧ s.re ≠ 1 / 2 := by
  by_contra hcon
  push Not at hcon
  set Λ : ℂ → ℂ := fun s => (2 * xi s) ^ d + (s * (s - 1)) ^ d * E₀ s with hΛ
  set a : ℕ → ℝ := fun n => zetaPowCoeff d n + e n with ha
  set σ₁ : ℝ := max σ₀ 1 with hσ₁
  have hσ₁0 : σ₀ ≤ σ₁ := le_max_left _ _
  have hσ₁1 : 1 ≤ σ₁ := le_max_right _ _
  have hcplx : ∀ n, cplx a n = cplx (zetaPowCoeff d) n + cplx e n := fun n => by
    simp [cplx, ha]
  have hsumA : ∀ s : ℂ, σ₁ < s.re → LSeriesSummable (cplx a) s := fun s hs => by
    have h1 := (lseries_zetaPowCoeff d (s := s) (by linarith)).1
    have h2 := hsum s (by linarith)
    have : cplx a = cplx (zetaPowCoeff d) + cplx e := funext hcplx
    rw [this]
    exact h1.add h2
  have hLA : ∀ s : ℂ, σ₁ < s.re →
      LSeries (cplx a) s = riemannZeta s ^ d + LSeries (cplx e) s := fun s hs => by
    have h1 := lseries_zetaPowCoeff d (s := s) (by linarith)
    have h2 := hsum s (by linarith)
    have : cplx a = cplx (zetaPowCoeff d) + cplx e := funext hcplx
    rw [this, LSeries_add h1.1 h2, h1.2]
  -- the twin datum
  obtain ⟨Cξ, hCξ0, hCξ⟩ := xi_growth_order_le_one
  obtain ⟨ρ, C₀, hfin⟩ := hfin
  have hD : TwinDatum d a σ₁ Λ := by
    refine ⟨by simp [ha, zetaPowCoeff_one, he1], hsumA, ?_, ?_, ?_, ?_⟩
    · exact ((xi_differentiable.const_mul 2).pow d).add
        (((differentiable_id.mul (differentiable_id.sub_const 1)).pow d).mul hE)
    · intro s hs
      have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
      have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs; linarith
      have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
      have hξ : 2 * xi s = s * (s - 1) * Complex.Gammaℝ s * riemannZeta s := by
        rw [xi_eq_half_mul hs0 hs1, riemannZeta_def_of_ne_zero hs0]
        field_simp
      simp only [hΛ]
      rw [hξ, hcomp s (by linarith), hLA s hs]
      simp only [mul_pow]
      ring
    · intro s
      simp only [hΛ]
      rw [xi_one_sub, hfe]
      ring
    · -- finite order
      obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
        hE.continuous.continuousOn
      set ρ' : ℝ := max ρ 3 with hρ'
      have hρ3 : (3 : ℝ) ≤ ρ' := le_max_right _ _
      have hρρ : ρ ≤ ρ' := le_max_left _ _
      set K : ℝ := 2 * d * Cξ with hK
      have hK0 : 0 ≤ K := by positivity
      set P : ℝ := ((2 * d).factorial : ℝ) with hP
      have hP0 : 0 < P := by positivity
      refine ⟨ρ' + 1, (2 ^ d * Real.exp (K + K ^ 3 + 1) + P * Real.exp 2 * (|M| + |C₀|)) *
        Real.exp (2 ^ (ρ' + 1)), fun s => ?_⟩
      set x : ℝ := ‖s‖ with hx
      have hx0 : 0 ≤ x := norm_nonneg s
      have hxρ : x ≤ 1 + x ^ ρ' := by
        have := rpow_le_one_add_rpow hx0 zero_le_one (by linarith : (1 : ℝ) ≤ ρ')
        rwa [Real.rpow_one] at this
      have hx3 : x ^ (3 : ℝ) ≤ 1 + x ^ ρ' := rpow_le_one_add_rpow hx0 (by norm_num) hρ3
      have hexp1 : Real.exp (x ^ ρ') ≥ 1 := Real.one_le_exp (Real.rpow_nonneg hx0 _)
      -- the `ξ` part
      have hξb : ‖(2 * xi s) ^ d‖ ≤ 2 ^ d * Real.exp (K + K ^ 3 + 1) * Real.exp (x ^ ρ') := by
        rw [norm_pow, norm_mul, Complex.norm_ofNat, mul_pow]
        have h1 : ‖xi s‖ ^ d ≤ Real.exp (Cξ * (1 + x) * Real.log (2 + x)) ^ d :=
          pow_le_pow_left₀ (norm_nonneg _) (hCξ s) d
        rw [← Real.exp_nat_mul] at h1
        have hlog : Real.log (2 + x) ≤ 1 + x := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 + x by linarith); linarith
        have hl0 : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith)
        have hq : (d : ℝ) * (Cξ * (1 + x) * Real.log (2 + x)) ≤ K + K * x ^ 2 := by
          have : (1 + x) * Real.log (2 + x) ≤ (1 + x) * (1 + x) :=
            mul_le_mul_of_nonneg_left hlog (by linarith)
          have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          calc (d : ℝ) * (Cξ * (1 + x) * Real.log (2 + x))
              = d * Cξ * ((1 + x) * Real.log (2 + x)) := by ring
            _ ≤ d * Cξ * ((1 + x) * (1 + x)) := mul_le_mul_of_nonneg_left this (by positivity)
            _ ≤ K + K * x ^ 2 := by rw [hK]; nlinarith [sq_nonneg (x - 1)]
        have hKx : K * x ^ 2 ≤ K ^ 3 + x ^ (3 : ℝ) := by
          rw [show x ^ (3 : ℝ) = x ^ (3 : ℕ) by norm_cast]
          rcases le_total x K with h | h
          · nlinarith [mul_le_mul h h hx0 hK0]
          · nlinarith [mul_le_mul h h hK0 hx0]
        calc 2 ^ d * ‖xi s‖ ^ d ≤ 2 ^ d * Real.exp (d * (Cξ * (1 + x) * Real.log (2 + x))) := by
              gcongr
          _ ≤ 2 ^ d * Real.exp (K + K ^ 3 + 1 + x ^ ρ') := by
              gcongr; linarith
          _ = 2 ^ d * Real.exp (K + K ^ 3 + 1) * Real.exp (x ^ ρ') := by
              rw [Real.exp_add]; ring
      -- the `E₀` part
      have hEb : ‖E₀ s‖ ≤ (|M| + |C₀|) * Real.exp (x ^ ρ') := by
        rcases le_or_gt x 1 with h1 | h1
        · have := hM s (by simpa [Metric.mem_closedBall] using h1)
          calc ‖E₀ s‖ ≤ M := this
            _ ≤ |M| + |C₀| := by linarith [le_abs_self M, abs_nonneg C₀]
            _ ≤ (|M| + |C₀|) * Real.exp (x ^ ρ') := le_mul_of_one_le_right (by positivity) hexp1
        · have h2 : x ^ ρ ≤ x ^ ρ' := Real.rpow_le_rpow_of_exponent_le h1.le hρρ
          have hC0 : 0 ≤ C₀ :=
            nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hfin s)) (Real.exp_pos _)
          calc ‖E₀ s‖ ≤ C₀ * Real.exp (x ^ ρ) := hfin s
            _ ≤ C₀ * Real.exp (x ^ ρ') := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h2) hC0
            _ ≤ (|M| + |C₀|) * Real.exp (x ^ ρ') :=
                mul_le_mul_of_nonneg_right (by linarith [le_abs_self C₀, abs_nonneg M])
                  (Real.exp_pos _).le
      have hpoly : ‖(s * (s - 1)) ^ d‖ ≤ P * Real.exp 2 * Real.exp (x ^ ρ') := by
        rw [norm_pow, norm_mul]
        have h1 : ‖s - 1‖ ≤ 1 + x := by
          calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = 1 + x := by simp [hx]; ring
        have h2 : (x * ‖s - 1‖) ^ d ≤ (1 + x) ^ (2 * d) := by
          rw [pow_mul, sq]
          exact pow_le_pow_left₀ (by positivity)
            (mul_le_mul (by linarith) h1 (norm_nonneg _) (by linarith)) d
        have h3 : (1 + x) ^ (2 * d) ≤ P * Real.exp (1 + x) := by
          have := Real.pow_div_factorial_le_exp (1 + x) (by linarith) (2 * d)
          rw [div_le_iff₀ hP0] at this
          linarith [mul_comm (Real.exp (1 + x)) P]
        calc (x * ‖s - 1‖) ^ d ≤ P * Real.exp (1 + x) := h2.trans h3
          _ ≤ P * Real.exp (2 + x ^ ρ') :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hxρ])) hP0.le
          _ = P * Real.exp 2 * Real.exp (x ^ ρ') := by rw [Real.exp_add]; ring
      simp only [hΛ]
      calc ‖(2 * xi s) ^ d + (s * (s - 1)) ^ d * E₀ s‖
          ≤ ‖(2 * xi s) ^ d‖ + ‖(s * (s - 1)) ^ d‖ * ‖E₀ s‖ := by
            rw [← norm_mul]; exact norm_add_le _ _
        _ ≤ 2 ^ d * Real.exp (K + K ^ 3 + 1) * Real.exp (x ^ ρ') +
              (P * Real.exp 2 * Real.exp (x ^ ρ')) * ((|M| + |C₀|) * Real.exp (x ^ ρ')) := by
            gcongr
        _ ≤ (2 ^ d * Real.exp (K + K ^ 3 + 1) + P * Real.exp 2 * (|M| + |C₀|)) *
              Real.exp (2 * x ^ ρ') := by
            have he2 : Real.exp (2 * x ^ ρ') = Real.exp (x ^ ρ') * Real.exp (x ^ ρ') := by
              rw [← Real.exp_add]; ring_nf
            rw [he2]
            have hA0 : 0 ≤ 2 ^ d * Real.exp (K + K ^ 3 + 1) := by positivity
            nlinarith [mul_le_mul_of_nonneg_left hexp1 hA0, Real.exp_pos (x ^ ρ')]
        _ ≤ (2 ^ d * Real.exp (K + K ^ 3 + 1) + P * Real.exp 2 * (|M| + |C₀|)) *
              Real.exp (2 ^ (ρ' + 1) + x ^ (ρ' + 1)) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
            have hρ0 : 0 ≤ ρ' := by linarith
            rcases le_or_gt x 2 with h2 | h2
            · have h3 : x ^ ρ' ≤ 2 ^ ρ' := Real.rpow_le_rpow hx0 h2 hρ0
              rw [Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
              linarith [Real.rpow_nonneg hx0 (ρ' + 1)]
            · rw [Real.rpow_add_one (by linarith : x ≠ 0)]
              nlinarith [Real.rpow_nonneg hx0 ρ', Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (ρ' + 1)]
        _ = (2 ^ d * Real.exp (K + K ^ 3 + 1) + P * Real.exp 2 * (|M| + |C₀|)) *
              Real.exp (2 ^ (ρ' + 1)) * Real.exp (x ^ (ρ' + 1)) := by
            rw [Real.exp_add (2 ^ (ρ' + 1)) (x ^ (ρ' + 1))]; ring
  have hRH := twin_rigidity hd hD hcon
  -- `L(E) = 0` far to the right, hence `E = 0`
  have hE0 : ∀ s : ℂ, σ₁ < s.re → LSeries (cplx e) s = 0 := fun s hs => by
    have h := hRH.2 s (by simpa [max_eq_left hσ₁1] using hs)
    rw [hLA s hs] at h
    linear_combination h
  have hev : (fun x : ℝ => LSeries (cplx e) x) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop σ₁] with x hx
    exact hE0 x (by simpa using hx)
  rcases LSeries_eventually_eq_zero_iff'.mp hev with h | h
  · obtain ⟨n, hn, hen⟩ := hne
    have := h n hn
    simp only [cplx, Complex.ofReal_eq_zero] at this
    exact hen this
  · have : LSeries.abscissaOfAbsConv (cplx e) ≤ σ₀ :=
      LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
        hsum y (by simpa using hy)
    rw [h] at this
    exact absurd this (by simp)

end RHTower.TwinRigidity

end
