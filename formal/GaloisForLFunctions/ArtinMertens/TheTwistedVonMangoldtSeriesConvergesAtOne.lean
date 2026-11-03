import GaloisForLFunctions.ArtinMertens.NewmansAnalyticTheorem
import GaloisForLFunctions.PNTPlus.Wiener

/-!
# The twisted von Mangoldt series converges at `s = 1`

For a nontrivial Dirichlet character `χ` mod `q`,

  `Σ_{n ≤ x} χ(n) Λ(n)/n → −L'(1, χ)/L(1, χ)`   (`tendsto_sum_twist_vonMangoldt_div`).

* **The Laplace transform** (`integral_twistLaplace_eq`): `f(u) = ψ(e^u, χ) e^{−u}`,
  `ψ(x, χ) = Σ_{n ≤ x} χ(n)Λ(n)`, is bounded by `log 4 + 4` (Chebyshev), and for `Re z > 0`
  `∫_0^∞ f(u) e^{−zu} du = L(z + 1, χΛ)/(z + 1)` (`LSeries_eq_mul_integral` and `x = e^u`).
* **Its continuation** (`analyticAt_twistNewmanG`): `L(χΛ, s) = −L'(s, χ)/L(s, χ)` is analytic on
  `Re s ≥ 1`, since `L(s, χ)` is entire and has no zero there.
* **Newman's theorem** gives `∫_1^x ψ(t, χ)/t² dt → −L'(1, χ)/L(1, χ)`; Abel summation
  `Σ_{n ≤ x} χ(n)Λ(n)/n = ψ(x, χ)/x + ∫_1^x ψ(t, χ)/t² dt`; and `ψ(x, χ) = o(x)` by the prime number
  theorem in progressions and the orthogonality `Σ_a χ(a) = 0` (`tendsto_twistPsi_div`).
-/

noncomputable section

open Complex Filter Topology MeasureTheory Set intervalIntegral Finset

namespace GaloisForLFunctions.ArtinMertens

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- The twisted Chebyshev function `ψ(x, χ) = Σ_{1 ≤ n ≤ x} χ(n)Λ(n)`. -/
def twistPsi (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n * (ArithmeticFunction.vonMangoldt n : ℂ)

/-- Chebyshev's bound for the twisted Chebyshev function: `‖ψ(x, χ)‖ ≤ (log 4 + 4) x`. -/
theorem norm_twistPsi_le {x : ℝ} (hx : 0 ≤ x) :
    ‖twistPsi χ x‖ ≤ (Real.log 4 + 4) * x := by
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖χ n * (ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n := by
    refine (sum_le_sum fun n _ => ?_).trans (sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_left (Nat.zero_le 1)) fun n _ _ =>
        ArithmeticFunction.vonMangoldt_nonneg)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (DirichletCharacter.norm_le_one χ _)
  refine h1.trans ?_
  rw [← Chebyshev.psi_eq_sum_Icc]
  exact Chebyshev.psi_le_const_mul_self hx

/-- The Newman function `f(u) = ψ(e^u, χ) e^{−u}`. -/
def twistNewmanF (u : ℝ) : ℂ := twistPsi χ (Real.exp u) * ((Real.exp (-u) : ℝ) : ℂ)

theorem norm_twistNewmanF_le (u : ℝ) : ‖twistNewmanF χ u‖ ≤ Real.log 4 + 4 := by
  unfold twistNewmanF
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h := norm_twistPsi_le χ (Real.exp_pos u).le
  calc ‖twistPsi χ (Real.exp u)‖ * Real.exp (-u) ≤ (Real.log 4 + 4) * Real.exp u * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = Real.log 4 + 4 := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

theorem measurable_twistNewmanF : Measurable (twistNewmanF χ) := by
  have h1 : Measurable fun u : ℝ => twistPsi χ (Real.exp u) := by
    have : (fun u : ℝ => twistPsi χ (Real.exp u)) = (fun m : ℕ =>
        ∑ n ∈ Finset.Icc 1 m, χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) ∘
          (fun u : ℝ => ⌊Real.exp u⌋₊) := rfl
    rw [this]
    exact measurable_from_nat.comp (Nat.measurable_floor.comp Real.measurable_exp)
  exact h1.mul (Complex.measurable_ofReal.comp (Real.measurable_exp.comp measurable_neg))

/-- The image of `(0, ∞)` under `exp` is `(1, ∞)`. -/
theorem exp_image_Ioi_zero : Real.exp '' Ioi (0 : ℝ) = Ioi 1 := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩; exact Real.one_lt_exp.mpr hu
  · intro ht
    exact ⟨Real.log t, Real.log_pos ht, Real.exp_log (lt_trans one_pos ht)⟩

/-- `(e^u)^w = e^{uw}` for real `u`. -/
theorem ofReal_exp_cpow (u : ℝ) (w : ℂ) : ((Real.exp u : ℝ) : ℂ) ^ w = cexp ((u : ℂ) * w) := by
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]

/-- **The Laplace transform**: for `Re z > 0`, `∫_0^∞ f(u) e^{−zu} du = L(χΛ, z + 1)/(z + 1)`. -/
theorem integral_twistLaplace_eq {z : ℂ} (hz : 0 < z.re) :
    ∫ u in Ioi (0 : ℝ), twistNewmanF χ u * cexp (-(z * u)) =
      LSeries (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (z + 1) / (z + 1) := by
  have hs : (1 : ℝ) < (z + 1).re := by simp; linarith
  have hz1 : z + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ k * (ArithmeticFunction.vonMangoldt k : ℂ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound (Real.log 4 + 4) (Eventually.of_forall fun n => ?_)
    have h := norm_twistPsi_le χ (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    unfold twistPsi at h
    rw [Nat.floor_natCast] at h
    rw [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
    exact h
  have h1 := LSeries_eq_mul_integral (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ))
    zero_le_one hs (LSeriesSummable_twist_vonMangoldt χ hs) hO
  rw [h1, mul_div_cancel_left₀ _ hz1]
  -- the substitution `t = e^u`
  have hsub := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ)) (f := Real.exp)
    (f' := Real.exp) measurableSet_Ioi (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    Real.exp_injective.injOn
    (fun t : ℝ => (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k * (ArithmeticFunction.vonMangoldt k : ℂ)) *
      (t : ℂ) ^ (-(z + 1 + 1)))
  rw [exp_image_Ioi_zero] at hsub
  rw [hsub]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  simp only [twistNewmanF, twistPsi]
  rw [abs_of_pos (Real.exp_pos u), ofReal_exp_cpow, Complex.real_smul, Complex.ofReal_exp,
    Complex.ofReal_exp]
  have e : cexp (u : ℂ) * cexp ((u : ℂ) * -(z + 1 + 1)) = cexp ((-u : ℝ) : ℂ) * cexp (-(z * u)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [← mul_assoc, mul_comm (cexp (u : ℂ)), mul_assoc, e]
  ring

/-- The continuation `g(z) = (−L'(z + 1, χ)/L(z + 1, χ))/(z + 1)`. -/
def twistNewmanG (z : ℂ) : ℂ :=
  (-deriv (DirichletCharacter.LFunction χ) (z + 1) / DirichletCharacter.LFunction χ (z + 1)) /
    (z + 1)

/-- For `Re s > 1`: `L(χΛ, s) = −L'(s, χ)/L(s, χ)` with the entire `L`-function. -/
theorem LSeries_twist_vonMangoldt_eq_LFunction {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s := by
  have h := LSeries_twist_vonMangoldt_eq χ hs
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 s] LSeries (fun n => χ n) :=
    Filter.eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
      fun w hw => DirichletCharacter.LFunction_eq_LSeries χ hw
  rw [hev.deriv_eq, DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact h

/-- `g` is analytic at every point of the closed half-plane `Re z ≥ 0`. -/
theorem analyticAt_twistNewmanG (hχ : χ ≠ 1) {z : ℂ} (hz : 0 ≤ z.re) :
    AnalyticAt ℂ (twistNewmanG χ) z := by
  have hdiff := DirichletCharacter.differentiable_LFunction hχ
  have hA : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) univ := fun w _ => hdiff.analyticAt w
  have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1) z := analyticAt_id.add analyticAt_const
  have hL : AnalyticAt ℂ (fun w : ℂ => DirichletCharacter.LFunction χ (w + 1)) z :=
    (hA (z + 1) trivial).comp hshift
  have hD : AnalyticAt ℂ (fun w : ℂ => deriv (DirichletCharacter.LFunction χ) (w + 1)) z :=
    ((hA.deriv) (z + 1) trivial).comp hshift
  have hne : DirichletCharacter.LFunction χ (z + 1) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp; linarith)
  have hz1 : z + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  exact (hD.neg.div hL hne).div hshift hz1

/-- **Newman's theorem for `χ`**: `∫_0^T ψ(e^u, χ) e^{−u} du → −L'(1, χ)/L(1, χ)`. -/
theorem tendsto_integral_twistNewmanF (hχ : χ ≠ 1) :
    Tendsto (fun T : ℝ => ∫ u in (0 : ℝ)..T, twistNewmanF χ u) atTop
      (𝓝 (-deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)) := by
  have h := newman_analytic_theorem (f := twistNewmanF χ) (B := Real.log 4 + 4)
    (measurable_twistNewmanF χ).aestronglyMeasurable (fun u _ => norm_twistNewmanF_le χ u)
    (g := twistNewmanG χ) (fun z hz => analyticAt_twistNewmanG χ hχ hz)
    (fun z hz => by
      rw [integral_twistLaplace_eq χ hz, twistNewmanG,
        LSeries_twist_vonMangoldt_eq_LFunction χ (by simp; linarith)])
  simpa [twistNewmanG] using h
