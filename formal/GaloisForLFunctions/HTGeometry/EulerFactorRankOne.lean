import GaloisForLFunctions.HTGeometry.BohrProductUniformLimit
import GaloisForLFunctions.HTGeometry.BohrFejerConcentration

/-!
# Infinite spectrum, rank-one frequency module

The Euler factor at `2`, restricted to a vertical line `Re s = σ > 0`,

`E(t) = (1 − 2^{-σ-it})⁻¹`,

is a uniform limit of the partial sums of its Dirichlet expansion, whose frequencies are the
integer multiples of `log 2`.  Its Bohr coefficient at `−m log 2` is `2^{-σm} ≠ 0`, so its spectrum
is infinite; but every frequency is a rational multiple of `log 2`, so its frequency module has rank
at most one.

Infinite Dirichlet support is therefore compatible with finite rational frequency rank: the
finite-phase law concludes finite rank, and that is the sharp conclusion.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- `2^{-s}` on the vertical line `Re s = σ`. -/
noncomputable def twoPowerLine (σ t : ℝ) : ℂ :=
  Complex.exp (-(((σ : ℂ) + (t : ℂ) * Complex.I) * (Real.log 2 : ℂ)))

/-- The frequencies of the Dirichlet expansion of the Euler factor at `2`. -/
noncomputable def twoFrequency (n : ℕ) : ℝ := -((n : ℝ) * Real.log 2)

/-- The Euler factor at `2` on a vertical line. -/
noncomputable def eulerFactorLine (σ t : ℝ) : ℂ := (1 - twoPowerLine σ t)⁻¹

theorem twoFrequency_injective : Function.Injective twoFrequency := by
  intro m n h
  rw [twoFrequency, twoFrequency, neg_inj] at h
  have hlog : Real.log 2 ≠ 0 := by
    have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    exact ne_of_gt this
  have := mul_right_cancel₀ hlog h
  exact_mod_cast this

/-- The line restriction of `2^{-s}` is a constant modulus times a character. -/
theorem twoPowerLine_eq (σ t : ℝ) :
    twoPowerLine σ t = (((2 : ℝ) ^ (-σ) : ℝ) : ℂ) * expChar (-Real.log 2) t := by
  rw [twoPowerLine, expChar,
    show -(((σ : ℂ) + (t : ℂ) * Complex.I) * (Real.log 2 : ℂ))
      = ((-σ * Real.log 2 : ℝ) : ℂ) + ((-Real.log 2 * t : ℝ) : ℂ) * Complex.I from by
        push_cast; ring,
    Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_exp]
  congr 1
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  ring_nf

theorem two_rpow_pow (σ : ℝ) (n : ℕ) : ((2 : ℝ) ^ (-σ)) ^ n = (2 : ℝ) ^ (-σ * n) := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (-σ)) n, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- The `n`-th power is the `n`-th Dirichlet term. -/
theorem twoPowerLine_pow (σ t : ℝ) (n : ℕ) :
    twoPowerLine σ t ^ n = (((2 : ℝ) ^ (-σ * n) : ℝ) : ℂ) * expChar (twoFrequency n) t := by
  rw [twoPowerLine_eq, mul_pow, ← Complex.ofReal_pow, two_rpow_pow]
  congr 1
  rw [twoFrequency, show -((n : ℝ) * Real.log 2) = (n : ℝ) * (-Real.log 2) from by ring,
    expChar_nat_mul]

theorem norm_twoPowerLine (σ t : ℝ) : ‖twoPowerLine σ t‖ = (2 : ℝ) ^ (-σ) := by
  rw [twoPowerLine_eq, norm_mul, norm_expChar, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]

theorem two_rpow_neg_lt_one (hσ : 0 < σ) : (2 : ℝ) ^ (-σ) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_iff_pos.mpr hσ)

theorem one_sub_twoPowerLine_ne_zero (hσ : 0 < σ) (t : ℝ) : (1 : ℂ) - twoPowerLine σ t ≠ 0 := by
  intro h
  have hone : twoPowerLine σ t = 1 := by
    have := sub_eq_zero.mp h
    exact this.symm
  have hnorm : ‖twoPowerLine σ t‖ = 1 := by rw [hone, norm_one]
  rw [norm_twoPowerLine] at hnorm
  exact absurd hnorm (ne_of_lt (two_rpow_neg_lt_one hσ))

/-- The geometric error of the Dirichlet partial sum. -/
theorem eulerFactorLine_sub_partialSum (hσ : 0 < σ) (t : ℝ) (N : ℕ) :
    eulerFactorLine σ t - ∑ n ∈ Finset.range N, twoPowerLine σ t ^ n
      = twoPowerLine σ t ^ N * eulerFactorLine σ t := by
  have hz : (1 : ℂ) - twoPowerLine σ t ≠ 0 := one_sub_twoPowerLine_ne_zero hσ t
  have hz1 : twoPowerLine σ t ≠ 1 := by
    intro h
    rw [h] at hz
    simp at hz
  have hz1' : twoPowerLine σ t - 1 ≠ 0 := sub_ne_zero.mpr hz1
  rw [eulerFactorLine, geom_sum_eq hz1]
  field_simp
  ring

theorem norm_eulerFactorLine_le (hσ : 0 < σ) (t : ℝ) :
    ‖eulerFactorLine σ t‖ ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ := by
  have hlt : (2 : ℝ) ^ (-σ) < 1 := two_rpow_neg_lt_one hσ
  have hpos : (0 : ℝ) < 1 - (2 : ℝ) ^ (-σ) := by linarith
  have hge : 1 - (2 : ℝ) ^ (-σ) ≤ ‖(1 : ℂ) - twoPowerLine σ t‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (twoPowerLine σ t)
    rw [norm_one, norm_twoPowerLine] at h
    exact h
  rw [eulerFactorLine, norm_inv]
  rw [inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le hpos hge

/-- **The uniform Dirichlet approximation.**  The partial sums of the Dirichlet expansion converge
to the Euler factor uniformly on the line, with geometric error. -/
theorem norm_eulerFactorLine_sub_dirichletSum_le (hσ : 0 < σ) (t : ℝ) (N : ℕ) :
    ‖eulerFactorLine σ t
        - ∑ n ∈ Finset.range N, (((2 : ℝ) ^ (-σ * n) : ℝ) : ℂ) * expChar (twoFrequency n) t‖
      ≤ ((2 : ℝ) ^ (-σ)) ^ N * (1 - (2 : ℝ) ^ (-σ))⁻¹ := by
  have hsum : ∑ n ∈ Finset.range N, (((2 : ℝ) ^ (-σ * n) : ℝ) : ℂ) * expChar (twoFrequency n) t
      = ∑ n ∈ Finset.range N, twoPowerLine σ t ^ n :=
    Finset.sum_congr rfl fun n _ => (twoPowerLine_pow σ t n).symm
  rw [hsum, eulerFactorLine_sub_partialSum hσ, norm_mul, norm_pow, norm_twoPowerLine]
  exact mul_le_mul_of_nonneg_left (norm_eulerFactorLine_le hσ t) (by positivity)

theorem tendsto_dirichlet_error (hσ : 0 < σ) :
    Tendsto (fun N : ℕ => ((2 : ℝ) ^ (-σ)) ^ N * (1 - (2 : ℝ) ^ (-σ))⁻¹) atTop (nhds 0) := by
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one
    (le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-σ))) (two_rpow_neg_lt_one hσ)
  simpa using hlim.mul_const ((1 - (2 : ℝ) ^ (-σ))⁻¹)

theorem continuous_twoPowerLine (σ : ℝ) : Continuous (twoPowerLine σ) := by
  unfold twoPowerLine
  fun_prop

theorem continuous_eulerFactorLine (hσ : 0 < σ) : Continuous (eulerFactorLine σ) := by
  unfold eulerFactorLine
  exact (continuous_const.sub (continuous_twoPowerLine σ)).inv₀
    (one_sub_twoPowerLine_ne_zero hσ)

theorem isBohrAlmostPeriodic_eulerFactorLine (hσ : 0 < σ) :
    HTGeometry.IsBohrAlmostPeriodic (eulerFactorLine σ) := by
  refine HTGeometry.isBohrAlmostPeriodic_of_uniform_approx fun ε hε => ?_
  obtain ⟨N, hN⟩ := ((tendsto_dirichlet_error hσ).eventually (gt_mem_nhds hε)).exists
  refine ⟨fun t => ∑ n ∈ Finset.range N,
    (((2 : ℝ) ^ (-σ * n) : ℝ) : ℂ) * expChar (twoFrequency n) t, ?_, fun t => ?_⟩
  · exact isBohrAlmostPeriodic_sum (Finset.range N)
      (fun n _ => continuous_const.mul (continuous_expChar (twoFrequency n)))
      (fun n _ => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_expChar (twoFrequency n)))
  · exact le_trans (norm_eulerFactorLine_sub_dirichletSum_le hσ t N) hN.le

/-- **The Bohr coefficients of the Euler factor are its Dirichlet coefficients.** -/
theorem bohrCoefficient_eulerFactorLine (hσ : 0 < σ) (m : ℕ) :
    bohrCoefficient (eulerFactorLine σ) (twoFrequency m) = (((2 : ℝ) ^ (-σ * m) : ℝ) : ℂ) := by
  classical
  have hkey : ∀ N : ℕ, m < N →
      ‖bohrCoefficient (eulerFactorLine σ) (twoFrequency m)
        - (((2 : ℝ) ^ (-σ * m) : ℝ) : ℂ)‖
        ≤ ((2 : ℝ) ^ (-σ)) ^ N * (1 - (2 : ℝ) ^ (-σ))⁻¹ := by
    intro N hN
    have hGc : Continuous (fun t : ℝ => ∑ n ∈ Finset.range N,
        (((2 : ℝ) ^ (-σ * n) : ℝ) : ℂ) * expChar (twoFrequency n) t) :=
      continuous_finsetSum _ (fun n _ => continuous_const.mul (continuous_expChar _))
    have hGa : HTGeometry.IsBohrAlmostPeriodic (fun t : ℝ => ∑ n ∈ Finset.range N,
        (((2 : ℝ) ^ (-σ * n) : ℝ) : ℂ) * expChar (twoFrequency n) t) :=
      isBohrAlmostPeriodic_sum (Finset.range N)
        (fun n _ => continuous_const.mul (continuous_expChar _))
        (fun n _ => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_expChar _))
    have hcoeff : bohrCoefficient (fun t : ℝ => ∑ n ∈ Finset.range N,
        (((2 : ℝ) ^ (-σ * n) : ℝ) : ℂ) * expChar (twoFrequency n) t) (twoFrequency m)
        = (((2 : ℝ) ^ (-σ * m) : ℝ) : ℂ) := by
      have hfun : (fun t : ℝ => ∑ n ∈ Finset.range N,
          (((2 : ℝ) ^ (-σ * n) : ℝ) : ℂ) * expChar (twoFrequency n) t)
          = fun t : ℝ => ∑ n ∈ Finset.range N,
            (((2 : ℝ) ^ (-σ * n) : ℝ) : ℂ) * bohrExp (twoFrequency n) t := by
        funext t
        exact Finset.sum_congr rfl fun n _ => by rw [expChar_eq_bohrExp]
      rw [hfun, bohrCoefficient_trigPoly]
      have hterm : ∀ n ∈ Finset.range N,
          (if twoFrequency n = twoFrequency m then (((2 : ℝ) ^ (-σ * n) : ℝ) : ℂ) else 0)
            = if n = m then (((2 : ℝ) ^ (-σ * n) : ℝ) : ℂ) else 0 := by
        intro n _
        by_cases hnm : n = m
        · simp [hnm]
        · have : twoFrequency n ≠ twoFrequency m := fun h => hnm (twoFrequency_injective h)
          simp [this, hnm]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range N) m
        (fun n => (((2 : ℝ) ^ (-σ * n) : ℝ) : ℂ)), if_pos (Finset.mem_range.mpr hN)]
    have hlip := norm_bohrCoefficient_sub_le (continuous_eulerFactorLine hσ)
      (isBohrAlmostPeriodic_eulerFactorLine hσ) hGc hGa
      (fun t => norm_eulerFactorLine_sub_dirichletSum_le hσ t N) (twoFrequency m)
    rwa [hcoeff] at hlip
  have hle : ‖bohrCoefficient (eulerFactorLine σ) (twoFrequency m)
      - (((2 : ℝ) ^ (-σ * m) : ℝ) : ℂ)‖ ≤ 0 :=
    ge_of_tendsto (tendsto_dirichlet_error hσ)
      (eventually_atTop.mpr ⟨m + 1, fun N hN => hkey N (by omega)⟩)
  have := norm_le_zero_iff.mp hle
  exact sub_eq_zero.mp this

/-- **The spectrum is infinite.**  Every integer multiple of `−log 2` is a frequency. -/
theorem infinite_bohrSpectrum_eulerFactorLine (hσ : 0 < σ) :
    (bohrSpectrum (eulerFactorLine σ)).Infinite := by
  refine Set.infinite_of_injective_forall_mem twoFrequency_injective ?_
  intro m
  show bohrCoefficient (eulerFactorLine σ) (twoFrequency m) ≠ 0
  rw [bohrCoefficient_eulerFactorLine hσ m]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  exact ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)

/-- **The frequency module has rank at most one.**  Every frequency is a rational multiple of
`log 2`. -/
theorem bohrFrequencyModule_eulerFactorLine_le (hσ : 0 < σ) :
    bohrFrequencyModule (eulerFactorLine σ) ≤ Submodule.span ℚ {Real.log 2} := by
  have hmem : ∀ n : ℕ, twoFrequency n ∈ (Submodule.span ℚ {Real.log 2} : Submodule ℚ ℝ) := by
    intro n
    have hbase : Real.log 2 ∈ (Submodule.span ℚ {Real.log 2} : Submodule ℚ ℝ) :=
      Submodule.mem_span_singleton_self _
    have := Submodule.smul_mem (Submodule.span ℚ {Real.log 2}) (-(n : ℚ)) hbase
    have heq : (-(n : ℚ)) • Real.log 2 = twoFrequency n := by
      rw [twoFrequency, Rat.smul_def]
      push_cast
      ring
    rwa [heq] at this
  have hbound := bohrFrequencyModule_le_of_uniform_approx_nat
    (continuous_eulerFactorLine hσ) (isBohrAlmostPeriodic_eulerFactorLine hσ)
    ((Submodule.span ℚ {Real.log 2} : Submodule ℚ ℝ) : Set ℝ) twoFrequency hmem ?_
  · rwa [Submodule.span_eq] at hbound
  · intro ε hε
    obtain ⟨N, hN⟩ := ((tendsto_dirichlet_error hσ).eventually (gt_mem_nhds hε)).exists
    exact ⟨N, fun n => (((2 : ℝ) ^ (-σ * n) : ℝ) : ℂ),
      fun t => le_trans (norm_eulerFactorLine_sub_dirichletSum_le hσ t N) hN.le⟩

/-- Infinite Dirichlet support with rank-one frequency module: the finite-rank conclusion of the
phase law is sharp, and does not imply finite support. -/
theorem rank_bohrFrequencyModule_eulerFactorLine_le_one (hσ : 0 < σ) :
    Module.rank ℚ (bohrFrequencyModule (eulerFactorLine σ)) ≤ 1 := by
  refine le_trans (Submodule.rank_mono (bohrFrequencyModule_eulerFactorLine_le hσ)) ?_
  refine le_trans (rank_span_le _) ?_
  rw [Cardinal.mk_singleton]

/-- `2^{-s}` as a function of the complex variable. -/
noncomputable def twoPower (s : ℂ) : ℂ := Complex.exp (-(s * (Real.log 2 : ℂ)))

/-- The Euler factor at `2` as a function of the complex variable. -/
noncomputable def eulerFactorTwo (s : ℂ) : ℂ := (1 - twoPower s)⁻¹

theorem twoPowerLine_eq_twoPower (σ t : ℝ) :
    twoPowerLine σ t = twoPower ((σ : ℂ) + (t : ℂ) * Complex.I) := rfl

theorem eulerFactorLine_eq_eulerFactorTwo (σ t : ℝ) :
    eulerFactorLine σ t = eulerFactorTwo ((σ : ℂ) + (t : ℂ) * Complex.I) := rfl

theorem norm_twoPower (s : ℂ) : ‖twoPower s‖ = Real.exp (-(s.re * Real.log 2)) := by
  rw [twoPower, Complex.norm_exp]
  congr 1
  rw [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem one_sub_twoPower_ne_zero {s : ℂ} (hs : 0 < s.re) : (1 : ℂ) - twoPower s ≠ 0 := by
  intro h
  have hone : twoPower s = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖twoPower s‖ = 1 := by rw [hone, norm_one]
  rw [norm_twoPower] at hnorm
  have hneg : -(s.re * Real.log 2) < 0 := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  have := Real.exp_lt_one_iff.mpr hneg
  rw [hnorm] at this
  exact absurd this (lt_irrefl 1)

theorem hasDerivAt_twoPower (s : ℂ) :
    HasDerivAt twoPower (twoPower s * (-(Real.log 2 : ℂ))) s := by
  have hbase : HasDerivAt (fun z : ℂ => z * (Real.log 2 : ℂ)) (1 * (Real.log 2 : ℂ)) s :=
    (hasDerivAt_id s).mul_const ((Real.log 2 : ℂ))
  refine (hbase.neg).cexp.congr_deriv ?_
  simp only [Pi.neg_apply]
  rw [twoPower]
  ring

/-- **The Euler factor satisfies a constant-coefficient first-order algebraic differential
equation.**  It is differentially algebraic over `ℂ` — the relation carries no coefficient in `s`
at all. -/
theorem hasDerivAt_eulerFactorTwo {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt eulerFactorTwo
      (-(Real.log 2 : ℂ) * (eulerFactorTwo s ^ 2 - eulerFactorTwo s)) s := by
  have hne : (1 : ℂ) - twoPower s ≠ 0 := one_sub_twoPower_ne_zero hs
  have hden : HasDerivAt (fun z : ℂ => 1 - twoPower z) (twoPower s * (Real.log 2 : ℂ)) s := by
    refine ((hasDerivAt_twoPower s).const_sub (1 : ℂ)).congr_deriv ?_
    ring
  have hinv := hden.inv hne
  refine hinv.congr_deriv ?_
  rw [eulerFactorTwo]
  field_simp
  ring

/-- The autonomous relation in the form of eq. (8): a nonzero polynomial in the jet, with constant
coefficients, vanishes identically on the half-plane. -/
theorem eulerFactorTwo_autonomous {s : ℂ} (hs : 0 < s.re) :
    deriv eulerFactorTwo s + (Real.log 2 : ℂ) * (eulerFactorTwo s ^ 2 - eulerFactorTwo s) = 0 := by
  rw [(hasDerivAt_eulerFactorTwo hs).deriv]
  ring

end GaloisForLFunctions
