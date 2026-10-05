import GaloisForLFunctions.RHTower.LiClockThetaReciprocalPoleCancellation
import GaloisForLFunctions.HTGeometry.CanonicalEulerLog
import GaloisForLFunctions.RHTower.PrimePowerCountLaplace
import GaloisForLFunctions.HTGeometry.InverseArgumentLahFormula

/-!
# The Euler coefficients of the reciprocal logarithm

For `1 < p < 2`, `s(u) = 1/2 + 1/(p-u)` and `s₀ = s(0)`, the Taylor coefficients
`ζ_n = (log ζ ∘ s)^{(n)}(0)/n!` of the Euler logarithm are, for every `n ≥ 1`,

  `ζ_n = p^{-n} Σ_m (Λ(m)/log m) m^{-s₀} P_n(log m/p)
       = p^{-n} Σ_{ℓ prime} Σ_{k ≥ 1} ℓ^{-k s₀}/k · P_n(k log ℓ/p)`   (A13)

with the signed polynomial `P_n(x) = Σ_{m=1}^n C(n-1, m-1)(-x)^m/m!`.  The interchange is the
termwise differentiation of the canonical Euler logarithm on a disk where it converges uniformly,
and each prime-power term is differentiated by the Lah formula for `exp(-a/(p-u))`.
-/

open Set Filter Topology Complex GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

local notation "σ" => liClockReciprocalPoleArgument
local notation "S" => liClockReciprocalPoleArgumentC

/-- The signed Euler polynomial `P_n(x) = Σ_{m=1}^n C(n-1, m-1)(-x)^m/m!`. -/
def liClockReciprocalEulerPolynomial (n : ℕ) (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 n, ((n - 1).choose (m - 1) : ℝ) * (-x) ^ m / m.factorial

/-- The complex prime-power term `(Λ(m)/log m) m^{-S(w)}`. -/
def liClockReciprocalEulerTerm (p : ℝ) (m : ℕ) (w : ℂ) : ℂ :=
  eulerLogDirichletCoeff m * cexp (-(Real.log m : ℂ) * S p w)

/-- The real prime-power term `(Λ(m)/log m) m^{-s(u)}`. -/
def liClockReciprocalEulerTermReal (p : ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  eulerLogCoeffReal m * Real.exp (-Real.log m * σ p u)

local notation "Fe" => liClockReciprocalEulerTerm
local notation "fe" => liClockReciprocalEulerTermReal

theorem liClockReciprocalEulerTerm_ofReal (p : ℝ) (m : ℕ) (u : ℝ) :
    Fe p m (u : ℂ) = (fe p m u : ℂ) := by
  unfold liClockReciprocalEulerTerm liClockReciprocalEulerTermReal
  rw [eulerLogDirichletCoeff_eq_ofReal_eulerLogCoeffReal, liClockReciprocalPoleArgumentC_ofReal]
  push_cast
  rfl

/-- On `Re s > 1`, the terms are the canonical Euler-log Dirichlet terms. -/
theorem liClockReciprocalEulerTerm_eq_term (p : ℝ) (m : ℕ) (w : ℂ) :
    Fe p m w = LSeries.term eulerLogDirichletCoeff (S p w) m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [liClockReciprocalEulerTerm, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hm, liClockReciprocalEulerTerm,
      Complex.cpow_def_of_ne_zero (by exact_mod_cast hm),
      show Complex.log (m : ℂ) = ((Real.log m : ℝ) : ℂ) by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_log m.cast_nonneg],
      div_eq_mul_inv, ← Complex.exp_neg]
    ring_nf

/-- The canonical Euler logarithm along the moving argument. -/
theorem hasSum_liClockReciprocalEulerTerm {p : ℝ} {w : ℂ} (hw : 1 < (S p w).re) :
    HasSum (fun m => Fe p m w) (canonicalEulerLogZeta (S p w)) := by
  have e : (fun m => Fe p m w) = LSeries.term eulerLogDirichletCoeff (S p w) :=
    funext fun m => liClockReciprocalEulerTerm_eq_term p m w
  rw [e]
  exact (canonicalEulerLogZeta_summable hw).hasSum

/-! ## Uniform convergence on a disk -/

private def radius (p : ℝ) : ℝ := (2 - p) / 2

private def expo (p : ℝ) : ℝ := 1 / 2 + 1 / (p + radius p)

private theorem one_lt_expo {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) : 1 < expo p := by
  unfold expo radius
  have : 1 / 2 < 1 / (p + (2 - p) / 2) := by
    rw [div_lt_div_iff₀ (by norm_num) (by linarith)]; linarith
  linarith

private theorem norm_liClockReciprocalEulerTerm_le {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (m : ℕ)
    {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) (radius p)) :
    ‖Fe p m w‖ ≤ ((m : ℝ) ^ expo p)⁻¹ := by
  rw [Metric.mem_ball, dist_zero_right] at hw
  have hρ : 0 < radius p := by unfold radius; linarith
  have hre : expo p ≤ (S p w).re := by
    have h := re_one_div_sub_ge (p := p) (ρ := radius p) hρ.le
      (by unfold radius; linarith) hw.le
    unfold liClockReciprocalPoleArgumentC expo
    simp only [Complex.add_re, show ((1 : ℂ) / 2).re = 1 / 2 by norm_num]
    linarith
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [liClockReciprocalEulerTerm, eulerLogDirichletCoeff_zero, zero_mul, norm_zero,
      Nat.cast_zero]
    positivity
  · have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
    unfold liClockReciprocalEulerTerm
    rw [norm_mul, Complex.norm_exp]
    have hc := norm_eulerLogDirichletCoeff_le_one m
    have he : (-(Real.log m : ℂ) * S p w).re = -Real.log m * (S p w).re := by
      rw [neg_mul, Complex.neg_re, Complex.re_ofReal_mul]; ring
    rw [he]
    have hmono : Real.exp (-Real.log m * (S p w).re) ≤ Real.exp (-Real.log m * expo p) :=
      Real.exp_le_exp.2 (by nlinarith)
    have hval : Real.exp (-Real.log m * expo p) = ((m : ℝ) ^ expo p)⁻¹ := by
      rw [Real.rpow_def_of_pos (by exact_mod_cast hm), ← Real.exp_neg]; ring_nf
    calc ‖eulerLogDirichletCoeff m‖ * Real.exp (-Real.log m * (S p w).re) ≤
        1 * Real.exp (-Real.log m * expo p) := by gcongr
      _ = _ := by rw [one_mul, hval]

private theorem differentiable_liClockReciprocalEulerTerm (p : ℝ) (m : ℕ) {w : ℂ}
    (hw : (p : ℂ) - w ≠ 0) : DifferentiableAt ℂ (Fe p m) w := by
  unfold liClockReciprocalEulerTerm
  exact (differentiableAt_const _).mul
    (((differentiableAt_const _).mul
      (hasDerivAt_liClockReciprocalPoleArgumentC p hw).differentiableAt).cexp)

private theorem differentiableOn_liClockReciprocalEulerTerm {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (m : ℕ) : DifferentiableOn ℂ (Fe p m) (Metric.ball 0 (radius p)) := by
  intro w hw
  rw [Metric.mem_ball, dist_zero_right] at hw
  have hne : (p : ℂ) - w ≠ 0 := by
    intro h
    have : ‖w‖ = p := by
      rw [show w = (p : ℂ) by linear_combination -h, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
    unfold radius at hw
    linarith
  exact (differentiable_liClockReciprocalEulerTerm p m hne).differentiableWithinAt

/-! ## The Euler logarithm as the real part of the termwise series -/

theorem liClockReciprocalEulerLog_eq_re_tsum {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) {u : ℝ}
    (hu : u ∈ Ioo (-radius p) (radius p)) :
    liClockReciprocalEulerLog p u = (∑' m, Fe p m (u : ℂ)).re := by
  have hρ : radius p < 2 - p := by unfold radius; linarith
  have hσ : 1 < σ p u := liClockReciprocalPoleArgument_gt_one (by linarith [hu.1])
    (by linarith [hu.2])
  have hS : 1 < (S p (u : ℂ)).re := by
    rw [liClockReciprocalPoleArgumentC_ofReal, Complex.ofReal_re]; exact hσ
  rw [(hasSum_liClockReciprocalEulerTerm hS).tsum_eq]
  have hexp := exp_canonicalEulerLogZeta_eq_riemannZeta hS
  rw [liClockReciprocalPoleArgumentC_ofReal] at hexp ⊢
  have hnorm := congrArg (‖·‖) hexp
  simp only [Complex.norm_exp] at hnorm
  have hz := riemannZeta_ofReal_eq hσ
  have hpos := re_riemannZeta_ofReal_pos hσ
  rw [hz, Complex.norm_real, Real.norm_eq_abs] at hnorm
  rw [hz, Complex.ofReal_re] at hpos
  unfold liClockReciprocalEulerLog
  rw [hz, Complex.ofReal_re, ← abs_of_pos hpos, ← hnorm, Real.log_exp]

/-- **(A13 setup)** `log ζ(s) = Σ_m (Λ(m)/log m) m^{-s}` for real `s > 1`. -/
theorem log_riemannZeta_ofReal_hasSum {s : ℝ} (hs : 1 < s) :
    HasSum (fun m : ℕ => eulerLogCoeffReal m * ((m : ℝ) ^ s)⁻¹)
      (Real.log (riemannZeta (s : ℂ)).re) := by
  have hS : 1 < ((s : ℂ)).re := by simpa using hs
  have h := (canonicalEulerLogZeta_summable hS).hasSum
  have hexp := exp_canonicalEulerLogZeta_eq_riemannZeta hS
  have hnorm := congrArg (‖·‖) hexp
  simp only [Complex.norm_exp] at hnorm
  have hz := riemannZeta_ofReal_eq hs
  have hpos := re_riemannZeta_ofReal_pos hs
  rw [hz, Complex.norm_real, Real.norm_eq_abs] at hnorm
  rw [hz, Complex.ofReal_re] at hpos
  rw [hz, Complex.ofReal_re, ← abs_of_pos hpos, ← hnorm, Real.log_exp]
  have hre := Complex.hasSum_re h
  refine hre.congr_fun fun m => ?_
  rcases eq_or_ne m 0 with rfl | hm
  · simp [LSeries.term_zero, eulerLogCoeffReal]
  · rw [LSeries.term_of_ne_zero hm, eulerLogDirichletCoeff_eq_ofReal_eulerLogCoeffReal,
      show ((m : ℂ) ^ (s : ℂ)) = (((m : ℝ) ^ s : ℝ) : ℂ) by
        rw [Complex.ofReal_cpow m.cast_nonneg]; norm_cast, ← Complex.ofReal_div,
      Complex.ofReal_re, div_eq_mul_inv]

/-! ## Termwise differentiation -/

private theorem weierstrass_euler {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    DifferentiableOn ℂ (fun w => ∑' m, Fe p m w) (Metric.ball (0 : ℂ) (radius p)) ∧
      ∀ k : ℕ, ∀ w ∈ Metric.ball (0 : ℂ) (radius p), HasSum (fun m => iteratedDeriv k (Fe p m) w)
        (iteratedDeriv k (fun w => ∑' m, Fe p m w) w) :=
  hasSum_iteratedDeriv_of_summable_bound Metric.isOpen_ball
    (differentiableOn_liClockReciprocalEulerTerm hp1 hp2)
    (Real.summable_nat_rpow_inv.2 (one_lt_expo hp1 hp2))
    (fun m _ hw => norm_liClockReciprocalEulerTerm_le hp1 hp2 m hw)

/-- `ζ_n = Re (Σ_m F_m)^{(n)}(0)/n!`. -/
theorem liClockReciprocalEulerCoeff_eq_re {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (n : ℕ) :
    liClockReciprocalEulerCoeff p n =
      (iteratedDeriv n (fun w => ∑' m, Fe p m w) 0).re / n.factorial := by
  have hρ : 0 < radius p := by unfold radius; linarith
  have h := iteratedDeriv_eq_re_of_differentiableOn (f := liClockReciprocalEulerLog p)
    (h := fun w => ∑' m, Fe p m w) Metric.isOpen_ball (weierstrass_euler hp1 hp2).1 isOpen_Ioo
    (fun y hy => by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_lt]
      exact hy)
    (fun y hy => liClockReciprocalEulerLog_eq_re_tsum hp1 hp2 hy) n (x := 0) ⟨by linarith, hρ⟩
  unfold liClockReciprocalEulerCoeff
  rw [h, Complex.ofReal_zero]

/-- Each complex term restricts to the real term: `Re F_m^{(n)}(0) = f_m^{(n)}(0)`. -/
theorem iteratedDeriv_liClockReciprocalEulerTerm_re {p : ℝ} (hp : 0 < p) (m n : ℕ) :
    (iteratedDeriv n (Fe p m) 0).re = iteratedDeriv n (fe p m) 0 := by
  have hU : IsOpen {w : ℂ | (p : ℂ) - w ≠ 0} :=
    isOpen_ne_fun (by fun_prop : Continuous fun w : ℂ => (p : ℂ) - w) continuous_const
  have hd : DifferentiableOn ℂ (Fe p m) {w : ℂ | (p : ℂ) - w ≠ 0} := fun w hw =>
    (differentiable_liClockReciprocalEulerTerm p m hw).differentiableWithinAt
  have h := iteratedDeriv_eq_re_of_differentiableOn (f := fe p m) hU hd isOpen_Iio
    (fun y hy => by
      show (p : ℂ) - y ≠ 0
      rw [← Complex.ofReal_sub]; exact_mod_cast (show p - y ≠ 0 by linarith [mem_Iio.1 hy]))
    (fun y _ => by rw [liClockReciprocalEulerTerm_ofReal, Complex.ofReal_re]) n (x := 0) hp
  rw [h, Complex.ofReal_zero]

/-! ## The Lah coefficients of `exp(-a/(p-u))` -/

theorem liClockReciprocalEulerPolynomial_succ (N : ℕ) (x : ℝ) :
    liClockReciprocalEulerPolynomial (N + 1) x =
      ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * (-x) ^ (k + 1) / (k + 1).factorial := by
  unfold liClockReciprocalEulerPolynomial
  have e : ∀ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * (-x) ^ (k + 1) / (k + 1).factorial =
      (fun m => (((N + 1 - 1).choose (m - 1) : ℕ) : ℝ) * (-x) ^ m / m.factorial) (k + 1) := by
    intro k _; simp
  rw [Finset.sum_congr rfl e, Finset.range_eq_Ico, Finset.sum_Ico_add'
    (fun m => (((N + 1 - 1).choose (m - 1) : ℕ) : ℝ) * (-x) ^ m / m.factorial) 0 (N + 1) 1]
  rfl

/-- `(d/du)^{N+1} exp(-a/(p-u))|_{u=0} = (N+1)! e^{-a/p} p^{-(N+1)} P_{N+1}(a/p)`. -/
theorem iteratedDeriv_exp_neg_div_sub (a : ℝ) {p : ℝ} (hp : 0 < p) (N : ℕ) :
    iteratedDeriv (N + 1) (fun u => Real.exp (-a / (p - u))) 0 =
      (N + 1).factorial * Real.exp (-a / p) * (p ^ (N + 1))⁻¹ *
        liClockReciprocalEulerPolynomial (N + 1) (a / p) := by
  set L : ℝ → ℝ := fun x => Real.exp (-a * x) with hLdef
  have hLk : ∀ k, iteratedDeriv k L = fun x => (-a) ^ k * Real.exp (-a * x) := fun k =>
    iteratedDeriv_exp_const_mul k (-a)
  have hL : ∀ k, Differentiable ℝ (iteratedDeriv k L) := fun k => by
    rw [hLk]; fun_prop
  have hfun : (fun u => Real.exp (-a / (p - u))) = fun u => (fun q => L q⁻¹) (p - u) := by
    funext u; simp only [hLdef, div_eq_mul_inv]
  have hlah := GaloisForLFunctions.HTGeometry.neg_one_pow_mul_iteratedDeriv_comp_inv_eq_choose
    hL N hp
  rw [hfun, iteratedDeriv_comp_const_sub (N + 1) (fun q => L q⁻¹) p]
  beta_reduce
  rw [sub_zero, smul_eq_mul, hlah,
    liClockReciprocalEulerPolynomial_succ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hLk]
  simp only
  have hf : ((k + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [show -(a / p) = -a / p by ring, div_pow, inv_pow]
  have hp' : p ≠ 0 := hp.ne'
  field_simp
  ring

/-- `f_m^{(n)}(0) = n! (Λ(m)/log m) m^{-s₀} p^{-n} P_n(log m/p)` for `n ≥ 1`. -/
theorem iteratedDeriv_liClockReciprocalEulerTermReal {p : ℝ} (hp : 0 < p) (m : ℕ) {n : ℕ}
    (hn : 1 ≤ n) : iteratedDeriv n (fe p m) 0 = n.factorial * ((p ^ n)⁻¹ *
      (eulerLogCoeffReal m * ((m : ℝ) ^ σ p 0)⁻¹ *
        liClockReciprocalEulerPolynomial n (Real.log m / p))) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hfun : fe p m = fun u => (eulerLogCoeffReal m * Real.exp (-Real.log m / 2)) *
      Real.exp (-Real.log m / (p - u)) := by
    funext u
    unfold liClockReciprocalEulerTermReal liClockReciprocalPoleArgument
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hfun, iteratedDeriv_const_mul_field, iteratedDeriv_exp_neg_div_sub _ hp]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [eulerLogCoeffReal]
  · have hσ : ((m : ℝ) ^ σ p 0)⁻¹ = Real.exp (-Real.log m / 2) * Real.exp (-Real.log m / p) := by
      rw [Real.rpow_def_of_pos (by exact_mod_cast hm), ← Real.exp_neg, ← Real.exp_add]
      unfold liClockReciprocalPoleArgument
      congr 1
      ring
    rw [hσ]
    ring

/-! ## (A13) The Euler coefficients -/

/-- **(A13)** `ζ_n = p^{-n} Σ_m (Λ(m)/log m) m^{-s₀} P_n(log m/p)` for every `n ≥ 1`. -/
theorem hasSum_liClockReciprocalEulerCoeff {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) {n : ℕ}
    (hn : 1 ≤ n) :
    HasSum (fun m : ℕ => (p ^ n)⁻¹ * (eulerLogCoeffReal m * ((m : ℝ) ^ σ p 0)⁻¹ *
      liClockReciprocalEulerPolynomial n (Real.log m / p))) (liClockReciprocalEulerCoeff p n) := by
  have hp0 : 0 < p := by linarith
  have hρ : 0 < radius p := by unfold radius; linarith
  have h := Complex.hasSum_re ((weierstrass_euler hp1 hp2).2 n 0 (Metric.mem_ball_self hρ))
  have h' := h.div_const (n.factorial : ℝ)
  rw [← liClockReciprocalEulerCoeff_eq_re hp1 hp2] at h'
  refine h'.congr_fun fun m => ?_
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [iteratedDeriv_liClockReciprocalEulerTerm_re hp0, iteratedDeriv_liClockReciprocalEulerTermReal
    hp0 m hn]
  field_simp

private theorem liClockEulerLogCoeffReal_prime_pow (ℓ : Nat.Primes) (k : ℕ) :
    eulerLogCoeffReal ((ℓ : ℕ) ^ (k + 1)) = 1 / (k + 1) := by
  have hℓ := ℓ.prop
  have hlog : 0 < Real.log (ℓ : ℕ) := Real.log_pos (by exact_mod_cast hℓ.one_lt)
  unfold eulerLogCoeffReal
  rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k),
    ArithmeticFunction.vonMangoldt_apply_prime hℓ, Nat.cast_pow, Real.log_pow]
  push_cast
  field_simp

/-- **(A13)** `ζ_n = p^{-n} Σ_{ℓ prime} Σ_{k ≥ 1} ℓ^{-k s₀}/k · P_n(k log ℓ/p)` for every `n ≥ 1`. -/
theorem hasSum_liClockReciprocalEulerCoeff_primePow {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) {n : ℕ}
    (hn : 1 ≤ n) :
    HasSum (fun ℓk : Nat.Primes × ℕ => (p ^ n)⁻¹ *
      (((ℓk.1 : ℕ) : ℝ) ^ ((ℓk.2 + 1 : ℕ) * σ p 0))⁻¹ / (ℓk.2 + 1 : ℕ) *
        liClockReciprocalEulerPolynomial n ((ℓk.2 + 1 : ℕ) * Real.log (ℓk.1 : ℕ) / p))
      (liClockReciprocalEulerCoeff p n) := by
  set f : ℕ → ℝ := fun m => (p ^ n)⁻¹ * (eulerLogCoeffReal m * ((m : ℝ) ^ σ p 0)⁻¹ *
    liClockReciprocalEulerPolynomial n (Real.log m / p)) with hfdef
  set g : Nat.Primes × ℕ → ℕ := fun ℓk => (ℓk.1 : ℕ) ^ (ℓk.2 + 1) with hgdef
  have hg : Function.Injective g := by
    rintro ⟨ℓ, k⟩ ⟨ℓ', k'⟩ h
    obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj ℓ.prop ℓ'.prop h
    simp only [Prod.mk.injEq]
    exact ⟨Subtype.ext h1, h2⟩
  have hzero : ∀ m ∉ Set.range g, f m = 0 := by
    intro m hm
    have hnot : ¬IsPrimePow m := by
      rw [isPrimePow_nat_iff]
      rintro ⟨ℓ, k, hℓ, hk, rfl⟩
      exact hm ⟨(⟨ℓ, hℓ⟩, k - 1), by simp only [hgdef]; rw [Nat.sub_add_cancel hk]⟩
    simp [hfdef, eulerLogCoeffReal, ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hnot]
  have h := (hg.hasSum_iff hzero).2 (hasSum_liClockReciprocalEulerCoeff hp1 hp2 hn)
  refine h.congr_fun fun ℓk => ?_
  obtain ⟨ℓ, k⟩ := ℓk
  have hℓ0 : (0 : ℝ) ≤ ((ℓ : ℕ) : ℝ) := Nat.cast_nonneg _
  simp only [Function.comp_apply, hfdef, hgdef, liClockEulerLogCoeffReal_prime_pow, Nat.cast_pow,
    Real.log_pow]
  rw [← Real.rpow_natCast ((ℓ : ℕ) : ℝ) (k + 1), ← Real.rpow_mul hℓ0]
  push_cast
  ring

end RHTower
