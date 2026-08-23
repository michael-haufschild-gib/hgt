import GaloisForLFunctions.RHTower.FriableMomentDensity
import GaloisForLFunctions.RHTower.LocalizedHalfDensityGerm

/-!
# The Mellin transform of the friable density

The friable density has rapid decay at both ends of the positive half-line, and its Mellin
transform is `Γ(s) ζ_S(s)` on the half-plane `0 < Re s`.
-/

open Filter MeasureTheory Set Asymptotics GaloisForLFunctions

open scoped Topology

namespace RHTower

noncomputable section

variable {k : ℕ}

theorem mellinRapid_friableDensity {p : Fin k → ℕ} (hp : ∀ i, 2 ≤ p i) :
    MellinRapid (friableDensity p) := by
  refine ⟨locallyIntegrableOn_friableDensity hp, ?_, ?_⟩
  · intro a
    set σ : ℝ := max a 1 with hσdef
    have hσ : 0 < σ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    obtain ⟨C, hC0, hC⟩ := exp_neg_le_rpow_neg hσ
    refine IsBigO.of_bound (C * friableDirichlet p σ) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hbound := norm_friableDensity_le hp hσ hC hx0
    have hmono : x ^ (-σ) ≤ x ^ (-a) :=
      Real.rpow_le_rpow_of_exponent_le hx (by simp only [neg_le_neg_iff]; exact le_max_left _ _)
    have hK : (0 : ℝ) ≤ C * friableDirichlet p σ :=
      mul_nonneg hC0.le (friableDirichlet_nonneg p σ)
    have hxa : (0 : ℝ) ≤ x ^ (-a) := Real.rpow_nonneg hx0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg hxa]
    calc ‖friableDensity p x‖ ≤ C * friableDirichlet p σ * x ^ (-σ) := hbound
      _ ≤ C * friableDirichlet p σ * x ^ (-a) := by
          exact mul_le_mul_of_nonneg_left hmono hK
  · intro b hb
    obtain ⟨C, hC0, hC⟩ := exp_neg_le_rpow_neg hb
    refine IsBigO.of_bound (C * friableDirichlet p b) ?_
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    have hx0 : (0 : ℝ) < x := hx
    have hxa : (0 : ℝ) ≤ x ^ (-b) := Real.rpow_nonneg hx0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg hxa]
    exact norm_friableDensity_le hp hb hC hx0

/-! ## The scaled exponential term -/

theorem mellinRapid_expScaled {n : ℕ} (hn : 1 ≤ n) :
    MellinRapid (fun x : ℝ => ((Real.exp (-((n : ℝ) * x)) : ℝ) : ℂ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  refine ⟨?_, ?_, ?_⟩
  · exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)).continuousOn.locallyIntegrableOn
        measurableSet_Ioi
  · intro a
    have hbase := isBigO_gammaLogIntegrandReal_atTop 0 a
    refine IsBigO.trans (IsBigO.of_bound 1 ?_) hbase
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, one_mul,
      abs_of_nonneg (Real.exp_pos _).le, gammaLogIntegrandReal, pow_zero, one_mul,
      abs_of_nonneg (Real.exp_pos _).le]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  · intro b hb
    obtain ⟨C, hC0, hC⟩ := exp_neg_le_rpow_neg hb
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    have hx0 : (0 : ℝ) < x := hx
    have hxb : (0 : ℝ) ≤ x ^ (-b) := Real.rpow_nonneg hx0.le _
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos _).le, abs_of_nonneg hxb]
    have h := hC _ (mul_pos hn0 hx0)
    refine h.trans ?_
    have hmul : ((n : ℝ) * x) ^ (-b) ≤ x ^ (-b) := by
      rw [Real.mul_rpow hn0.le hx0.le]
      have hnb : (n : ℝ) ^ (-b) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
      nlinarith [Real.rpow_nonneg hn0.le (-b)]
    exact mul_le_mul_of_nonneg_left hmul hC0.le

theorem MellinRapid.mellinConvergent {f : ℝ → ℂ} (hf : MellinRapid f) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent f s :=
  mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := s.re / 2) hf.loc
    (hf.top (s.re + 1)) (by linarith) (hf.bot (s.re / 2) (by linarith)) (by linarith)

theorem mellin_expScaled {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x : ℝ => ((Real.exp (-((n : ℝ) * x)) : ℝ) : ℂ)) s
      = ((n : ℝ) : ℂ) ^ (-s) * Complex.Gamma s := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h := mellin_comp_mul_left (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) s hn0
  have hfun : (fun t : ℝ => ((Real.exp (-((n : ℝ) * t)) : ℝ) : ℂ))
      = fun t : ℝ => (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) ((n : ℝ) * t) := rfl
  rw [hfun, h, ← Complex.GammaIntegral_eq_mellin, ← Complex.Gamma_eq_integral hs, smul_eq_mul]

theorem norm_mellinExpScaled_integrand {n : ℕ} {s : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (s - 1) • ((Real.exp (-((n : ℝ) * x)) : ℝ) : ℂ)‖
      = x ^ (s.re - 1) * Real.exp (-((n : ℝ) * x)) := by
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_pos _).le]
  congr 1

theorem integral_norm_mellinExpScaled {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (0 : ℝ), ‖(x : ℂ) ^ (s - 1) • ((Real.exp (-((n : ℝ) * x)) : ℝ) : ℂ)‖)
      = Real.Gamma s.re * ((n : ℝ)) ^ (-s.re) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcplx := mellin_expScaled hn (s := ((s.re : ℝ) : ℂ)) (by simpa using hs)
  have hleft : mellin (fun x : ℝ => ((Real.exp (-((n : ℝ) * x)) : ℝ) : ℂ)) ((s.re : ℝ) : ℂ)
      = ((∫ x in Ioi (0 : ℝ), x ^ (s.re - 1) * Real.exp (-((n : ℝ) * x)) : ℝ) : ℂ) := by
    rw [mellin, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    rw [smul_eq_mul, Complex.ofReal_mul]
    congr 1
    rw [Complex.ofReal_cpow hx0.le]
    congr 1
    push_cast
    ring
  have hright : ((n : ℝ) : ℂ) ^ (-((s.re : ℝ) : ℂ)) * Complex.Gamma ((s.re : ℝ) : ℂ)
      = ((Real.Gamma s.re * ((n : ℝ)) ^ (-s.re) : ℝ) : ℂ) := by
    rw [Complex.Gamma_ofReal, ← Complex.ofReal_neg, ← Complex.ofReal_cpow hn0.le]
    push_cast
    ring
  rw [hleft, hright] at hcplx
  have hcast := Complex.ofReal_inj.mp hcplx
  rw [← hcast]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  exact norm_mellinExpScaled_integrand hx

/-- **The Mellin transform of the friable density is `Γ(s) ζ_S(s)`.** -/
theorem mellin_friableDensity {p : Fin k → ℕ} (hp : ∀ i, 2 ≤ p i) {s : ℂ} (hs : 0 < s.re) :
    mellin (friableDensity p) s = Complex.Gamma s * eulerProductL p 1 s := by
  have hp1 : ∀ i, 1 ≤ p i := fun i => by have := hp i; omega
  have hn1 : ∀ ν : Fin k →₀ ℕ, 1 ≤ smoothNat p ν := fun ν => one_le_smoothNat hp1 ν
  set F : (Fin k →₀ ℕ) → ℝ → ℂ := fun ν x =>
    (x : ℂ) ^ (s - 1) • ((Real.exp (-((smoothNat p ν : ℝ) * x)) : ℝ) : ℂ) with hF
  have hint : ∀ ν, IntegrableOn (F ν) (Ioi (0 : ℝ)) volume := fun ν =>
    (mellinRapid_expScaled (hn1 ν)).mellinConvergent hs
  have hsummableInt : Summable fun ν : Fin k →₀ ℕ =>
      ∫ x in Ioi (0 : ℝ), ‖F ν x‖ := by
    have hval : ∀ ν : Fin k →₀ ℕ, (∫ x in Ioi (0 : ℝ), ‖F ν x‖)
        = Real.Gamma s.re * ((smoothNat p ν : ℝ)) ^ (-s.re) :=
      fun ν => integral_norm_mellinExpScaled (hn1 ν) hs
    refine Summable.congr ((summable_smoothNat_rpow hp hs).mul_left (Real.Gamma s.re)) ?_
    intro ν
    exact (hval ν).symm
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Ioi (0 : ℝ))) hint hsummableInt
  have hdens : mellin (friableDensity p) s = ∫ x in Ioi (0 : ℝ), ∑' ν, F ν x := by
    rw [mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    have hsum : Summable fun ν : Fin k →₀ ℕ =>
        ((Real.exp (-((smoothNat p ν : ℝ) * x)) : ℝ) : ℂ) := by
      refine Summable.of_norm ?_
      refine (summable_friableTerm hp hx0).congr fun ν => ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    rw [friableDensity]
    exact (Summable.tsum_const_smul ((x : ℂ) ^ (s - 1)) hsum).symm
  have hterm : ∀ ν : Fin k →₀ ℕ, (∫ x in Ioi (0 : ℝ), F ν x)
      = ((smoothNat p ν : ℝ) : ℂ) ^ (-s) * Complex.Gamma s := fun ν => by
    rw [← mellin_expScaled (hn1 ν) hs, mellin]
  have hnome : ∀ ν : Fin k →₀ ℕ, ((smoothNat p ν : ℝ) : ℂ) ^ (-s)
      = HTGeometry.nomeMonomial (fun i => ((p i : ℂ)) ^ (-s)) ν := by
    intro ν
    have hn0 : ((smoothNat p ν : ℕ) : ℝ) ≠ 0 := by
      have := hn1 ν
      positivity
    have hlog : Real.log ((smoothNat p ν : ℕ) : ℝ)
        = ∑ i, (ν i : ℝ) * Real.log (p i) := by
      rw [smoothNat]
      push_cast
      rw [Real.log_prod (fun i _ => by
        have := hp1 i
        positivity)]
      exact Finset.sum_congr rfl fun i _ => Real.log_pow _ _
    rw [HTGeometry.nomeMonomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    have hexp : ∀ i : Fin k, (((p i : ℕ) : ℂ)) ^ (-s)
        = Complex.exp ((Real.log (p i) : ℂ) * (-s)) := by
      intro i
      have hpi : (p i : ℕ) ≠ 0 := by have := hp1 i; omega
      exact natCast_cpow_eq_cexp hpi (-s)
    have hlhs : ((smoothNat p ν : ℝ) : ℂ) ^ (-s)
        = Complex.exp ((Real.log ((smoothNat p ν : ℕ) : ℝ) : ℂ) * (-s)) := by
      have hnn : (smoothNat p ν : ℕ) ≠ 0 := by have := hn1 ν; omega
      have h := natCast_cpow_eq_cexp hnn (-s)
      rw [← h]
      norm_cast
    rw [hlhs, hlog, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hexp i, ← Complex.exp_nat_mul]
    congr 1
    rw [Complex.ofReal_mul]
    push_cast
    ring
  rw [hdens, ← hswap]
  have hsum2 : Summable fun ν : Fin k →₀ ℕ =>
      HTGeometry.nomeMonomial (fun i => ((p i : ℂ)) ^ (-s)) ν := by
    have hulty : ∀ i : Fin k, ‖((p i : ℂ)) ^ (-s)‖ < 1 := by
      intro i
      have hpi : (1 : ℝ) < (p i : ℝ) := by
        have := hp i
        exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two this
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
      simp only [Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg hpi (by linarith)
    have h := (HTGeometry.summable_nomeMonomial_pow_iff 0
      (fun i : Fin k => ((p i : ℂ)) ^ (-s)) hulty).2 (Summable.of_finite)
    refine Summable.of_norm ?_
    simpa using h
  calc (∑' ν : Fin k →₀ ℕ, ∫ x in Ioi (0 : ℝ), F ν x)
      = ∑' ν : Fin k →₀ ℕ,
          HTGeometry.nomeMonomial (fun i => ((p i : ℂ)) ^ (-s)) ν * Complex.Gamma s := by
        refine tsum_congr fun ν => ?_
        rw [hterm ν, hnome ν]
    _ = (∑' ν : Fin k →₀ ℕ, HTGeometry.nomeMonomial (fun i => ((p i : ℂ)) ^ (-s)) ν)
          * Complex.Gamma s := by
        rw [tsum_mul_right]
    _ = Complex.Gamma s * eulerProductL p 1 s := by
        rw [tsum_nomeMonomial_eq_fintype_eulerProduct _ (fun i => by
          have hpi : (1 : ℝ) < (p i : ℝ) := by
            have := hp i
            exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two this
          rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
          simp only [Complex.neg_re]
          exact Real.rpow_lt_one_of_one_lt_of_neg hpi (by linarith))]
        rw [eulerProductL]
        simp only [Pi.one_apply, one_mul]
        ring

end

end RHTower
