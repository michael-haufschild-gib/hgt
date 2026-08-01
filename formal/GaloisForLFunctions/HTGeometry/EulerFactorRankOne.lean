import GaloisForLFunctions.HTGeometry.BohrProductUniformLimit
import GaloisForLFunctions.HTGeometry.BohrFejerConcentration

/-!
# Infinite spectrum, rank-one frequency module

For a base `b > 1` the Euler factor

`E(s) = (1 − b^{-s})⁻¹`,

restricted to a vertical line `Re s = σ > 0`, is a uniform limit of the partial sums of its
geometric Dirichlet expansion, whose frequencies are the integer multiples of `log b`.  Its Bohr
coefficient at `−m log b` is `b^{-σm} ≠ 0`, so its spectrum is infinite; but every frequency is a
rational multiple of `log b`, so its frequency module has rank at most one.

Infinite Dirichlet support is therefore compatible with finite rational frequency rank: the
finite-phase law concludes finite rank, and that is the sharp conclusion.  The factor is moreover
*autonomous* differentially algebraic: `E′ + (log b)(E² − E) = 0`, a first-order polynomial relation
with constant coefficients.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {b σ : ℝ}

/-- `b^{-s}` on the vertical line `Re s = σ`. -/
noncomputable def basePowerLine (b σ t : ℝ) : ℂ :=
  Complex.exp (-(((σ : ℂ) + (t : ℂ) * Complex.I) * (Real.log b : ℂ)))

/-- The frequencies of the Dirichlet expansion of the Euler factor at base `b`. -/
noncomputable def baseFrequency (b : ℝ) (n : ℕ) : ℝ := -((n : ℝ) * Real.log b)

/-- The Euler factor at base `b` on a vertical line. -/
noncomputable def eulerFactorLine (b σ t : ℝ) : ℂ := (1 - basePowerLine b σ t)⁻¹

theorem log_pos_of_one_lt (hb : 1 < b) : 0 < Real.log b := Real.log_pos hb

theorem baseFrequency_injective (hb : 1 < b) : Function.Injective (baseFrequency b) := by
  intro m n h
  rw [baseFrequency, baseFrequency, neg_inj] at h
  have := mul_right_cancel₀ (ne_of_gt (log_pos_of_one_lt hb)) h
  exact_mod_cast this

/-- The line restriction of `b^{-s}` is a constant modulus times a character. -/
theorem basePowerLine_eq (b σ t : ℝ) (hb : 0 < b) :
    basePowerLine b σ t = ((b ^ (-σ) : ℝ) : ℂ) * expChar (-Real.log b) t := by
  rw [basePowerLine, expChar,
    show -(((σ : ℂ) + (t : ℂ) * Complex.I) * (Real.log b : ℂ))
      = ((-σ * Real.log b : ℝ) : ℂ) + ((-Real.log b * t : ℝ) : ℂ) * Complex.I from by
        push_cast; ring,
    Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_exp]
  congr 1
  rw [Real.rpow_def_of_pos hb]
  ring_nf

theorem base_rpow_pow (hb : 0 < b) (σ : ℝ) (n : ℕ) : (b ^ (-σ)) ^ n = b ^ (-σ * n) := by
  rw [← Real.rpow_natCast (b ^ (-σ)) n, ← Real.rpow_mul hb.le]

/-- The `n`-th power is the `n`-th Dirichlet term. -/
theorem basePowerLine_pow (hb : 0 < b) (σ t : ℝ) (n : ℕ) :
    basePowerLine b σ t ^ n = ((b ^ (-σ * n) : ℝ) : ℂ) * expChar (baseFrequency b n) t := by
  rw [basePowerLine_eq b σ t hb, mul_pow, ← Complex.ofReal_pow, base_rpow_pow hb]
  congr 1
  rw [baseFrequency, show -((n : ℝ) * Real.log b) = (n : ℝ) * (-Real.log b) from by ring,
    expChar_nat_mul]

theorem norm_basePowerLine (hb : 0 < b) (σ t : ℝ) : ‖basePowerLine b σ t‖ = b ^ (-σ) := by
  rw [basePowerLine_eq b σ t hb, norm_mul, norm_expChar, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hb _)]

theorem base_rpow_neg_lt_one (hb : 1 < b) (hσ : 0 < σ) : b ^ (-σ) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hb (neg_neg_iff_pos.mpr hσ)

theorem one_sub_basePowerLine_ne_zero (hb : 1 < b) (hσ : 0 < σ) (t : ℝ) :
    (1 : ℂ) - basePowerLine b σ t ≠ 0 := by
  intro h
  have hone : basePowerLine b σ t = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖basePowerLine b σ t‖ = 1 := by rw [hone, norm_one]
  rw [norm_basePowerLine (lt_trans zero_lt_one hb)] at hnorm
  exact absurd hnorm (ne_of_lt (base_rpow_neg_lt_one hb hσ))

/-- The geometric error of the Dirichlet partial sum. -/
theorem eulerFactorLine_sub_partialSum (hb : 1 < b) (hσ : 0 < σ) (t : ℝ) (N : ℕ) :
    eulerFactorLine b σ t - ∑ n ∈ Finset.range N, basePowerLine b σ t ^ n
      = basePowerLine b σ t ^ N * eulerFactorLine b σ t := by
  have hz : (1 : ℂ) - basePowerLine b σ t ≠ 0 := one_sub_basePowerLine_ne_zero hb hσ t
  have hz1 : basePowerLine b σ t ≠ 1 := by
    intro h
    rw [h] at hz
    simp at hz
  have hz1' : basePowerLine b σ t - 1 ≠ 0 := sub_ne_zero.mpr hz1
  rw [eulerFactorLine, geom_sum_eq hz1]
  field_simp
  ring

theorem norm_eulerFactorLine_le (hb : 1 < b) (hσ : 0 < σ) (t : ℝ) :
    ‖eulerFactorLine b σ t‖ ≤ (1 - b ^ (-σ))⁻¹ := by
  have hlt : b ^ (-σ) < 1 := base_rpow_neg_lt_one hb hσ
  have hpos : (0 : ℝ) < 1 - b ^ (-σ) := by linarith
  have hge : 1 - b ^ (-σ) ≤ ‖(1 : ℂ) - basePowerLine b σ t‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (basePowerLine b σ t)
    rw [norm_one, norm_basePowerLine (lt_trans zero_lt_one hb)] at h
    exact h
  rw [eulerFactorLine, norm_inv, inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le hpos hge

/-- **The uniform Dirichlet approximation.**  The partial sums of the Dirichlet expansion converge
to the Euler factor uniformly on the line, with geometric error. -/
theorem norm_eulerFactorLine_sub_dirichletSum_le (hb : 1 < b) (hσ : 0 < σ) (t : ℝ) (N : ℕ) :
    ‖eulerFactorLine b σ t
        - ∑ n ∈ Finset.range N, ((b ^ (-σ * n) : ℝ) : ℂ) * expChar (baseFrequency b n) t‖
      ≤ (b ^ (-σ)) ^ N * (1 - b ^ (-σ))⁻¹ := by
  have hb0 : (0 : ℝ) < b := lt_trans zero_lt_one hb
  have hsum : ∑ n ∈ Finset.range N, ((b ^ (-σ * n) : ℝ) : ℂ) * expChar (baseFrequency b n) t
      = ∑ n ∈ Finset.range N, basePowerLine b σ t ^ n :=
    Finset.sum_congr rfl fun n _ => (basePowerLine_pow hb0 σ t n).symm
  rw [hsum, eulerFactorLine_sub_partialSum hb hσ, norm_mul, norm_pow, norm_basePowerLine hb0]
  exact mul_le_mul_of_nonneg_left (norm_eulerFactorLine_le hb hσ t) (by positivity)

theorem tendsto_dirichlet_error (hb : 1 < b) (hσ : 0 < σ) :
    Tendsto (fun N : ℕ => (b ^ (-σ)) ^ N * (1 - b ^ (-σ))⁻¹) atTop (nhds 0) := by
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one
    (le_of_lt (Real.rpow_pos_of_pos (lt_trans zero_lt_one hb) (-σ))) (base_rpow_neg_lt_one hb hσ)
  simpa using hlim.mul_const ((1 - b ^ (-σ))⁻¹)

theorem continuous_basePowerLine (b σ : ℝ) : Continuous (basePowerLine b σ) := by
  unfold basePowerLine
  fun_prop

theorem continuous_eulerFactorLine (hb : 1 < b) (hσ : 0 < σ) :
    Continuous (eulerFactorLine b σ) := by
  unfold eulerFactorLine
  exact (continuous_const.sub (continuous_basePowerLine b σ)).inv₀
    (one_sub_basePowerLine_ne_zero hb hσ)

theorem isBohrAlmostPeriodic_eulerFactorLine (hb : 1 < b) (hσ : 0 < σ) :
    HTGeometry.IsBohrAlmostPeriodic (eulerFactorLine b σ) := by
  refine HTGeometry.isBohrAlmostPeriodic_of_uniform_approx fun ε hε => ?_
  obtain ⟨N, hN⟩ := ((tendsto_dirichlet_error hb hσ).eventually (gt_mem_nhds hε)).exists
  refine ⟨fun t => ∑ n ∈ Finset.range N,
    ((b ^ (-σ * n) : ℝ) : ℂ) * expChar (baseFrequency b n) t, ?_, fun t => ?_⟩
  · exact isBohrAlmostPeriodic_sum (Finset.range N)
      (fun n _ => continuous_const.mul (continuous_expChar (baseFrequency b n)))
      (fun n _ => isBohrAlmostPeriodic_const_mul _
        (isBohrAlmostPeriodic_expChar (baseFrequency b n)))
  · exact le_trans (norm_eulerFactorLine_sub_dirichletSum_le hb hσ t N) hN.le

/-- **The Bohr coefficients of the Euler factor are its Dirichlet coefficients.** -/
theorem bohrCoefficient_eulerFactorLine (hb : 1 < b) (hσ : 0 < σ) (m : ℕ) :
    bohrCoefficient (eulerFactorLine b σ) (baseFrequency b m) = ((b ^ (-σ * m) : ℝ) : ℂ) := by
  classical
  have hkey : ∀ N : ℕ, m < N →
      ‖bohrCoefficient (eulerFactorLine b σ) (baseFrequency b m) - ((b ^ (-σ * m) : ℝ) : ℂ)‖
        ≤ (b ^ (-σ)) ^ N * (1 - b ^ (-σ))⁻¹ := by
    intro N hN
    have hGc : Continuous (fun t : ℝ => ∑ n ∈ Finset.range N,
        ((b ^ (-σ * n) : ℝ) : ℂ) * expChar (baseFrequency b n) t) :=
      continuous_finsetSum _ (fun n _ => continuous_const.mul (continuous_expChar _))
    have hGa : HTGeometry.IsBohrAlmostPeriodic (fun t : ℝ => ∑ n ∈ Finset.range N,
        ((b ^ (-σ * n) : ℝ) : ℂ) * expChar (baseFrequency b n) t) :=
      isBohrAlmostPeriodic_sum (Finset.range N)
        (fun n _ => continuous_const.mul (continuous_expChar _))
        (fun n _ => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_expChar _))
    have hcoeff : bohrCoefficient (fun t : ℝ => ∑ n ∈ Finset.range N,
        ((b ^ (-σ * n) : ℝ) : ℂ) * expChar (baseFrequency b n) t) (baseFrequency b m)
        = ((b ^ (-σ * m) : ℝ) : ℂ) := by
      have hfun : (fun t : ℝ => ∑ n ∈ Finset.range N,
          ((b ^ (-σ * n) : ℝ) : ℂ) * expChar (baseFrequency b n) t)
          = fun t : ℝ => ∑ n ∈ Finset.range N,
            ((b ^ (-σ * n) : ℝ) : ℂ) * bohrExp (baseFrequency b n) t := by
        funext t
        exact Finset.sum_congr rfl fun n _ => by rw [expChar_eq_bohrExp]
      rw [hfun, bohrCoefficient_trigPoly]
      have hterm : ∀ n ∈ Finset.range N,
          (if baseFrequency b n = baseFrequency b m then ((b ^ (-σ * n) : ℝ) : ℂ) else 0)
            = if n = m then ((b ^ (-σ * n) : ℝ) : ℂ) else 0 := by
        intro n _
        by_cases hnm : n = m
        · simp [hnm]
        · have : baseFrequency b n ≠ baseFrequency b m :=
            fun h => hnm (baseFrequency_injective hb h)
          simp [this, hnm]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range N) m
        (fun n => ((b ^ (-σ * n) : ℝ) : ℂ)), if_pos (Finset.mem_range.mpr hN)]
    have hlip := norm_bohrCoefficient_sub_le (continuous_eulerFactorLine hb hσ)
      (isBohrAlmostPeriodic_eulerFactorLine hb hσ) hGc hGa
      (fun t => norm_eulerFactorLine_sub_dirichletSum_le hb hσ t N) (baseFrequency b m)
    rwa [hcoeff] at hlip
  have hle : ‖bohrCoefficient (eulerFactorLine b σ) (baseFrequency b m)
      - ((b ^ (-σ * m) : ℝ) : ℂ)‖ ≤ 0 :=
    ge_of_tendsto (tendsto_dirichlet_error hb hσ)
      (eventually_atTop.mpr ⟨m + 1, fun N hN => hkey N (by omega)⟩)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hle)

/-- **The spectrum is infinite.**  Every integer multiple of `−log b` is a frequency. -/
theorem infinite_bohrSpectrum_eulerFactorLine (hb : 1 < b) (hσ : 0 < σ) :
    (bohrSpectrum (eulerFactorLine b σ)).Infinite := by
  refine Set.infinite_of_injective_forall_mem (baseFrequency_injective hb) ?_
  intro m
  show bohrCoefficient (eulerFactorLine b σ) (baseFrequency b m) ≠ 0
  rw [bohrCoefficient_eulerFactorLine hb hσ m]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  exact ne_of_gt (Real.rpow_pos_of_pos (lt_trans zero_lt_one hb) _)

/-- Every frequency of the Euler factor is a rational multiple of `log b`. -/
theorem bohrFrequencyModule_eulerFactorLine_le (hb : 1 < b) (hσ : 0 < σ) :
    bohrFrequencyModule (eulerFactorLine b σ) ≤ Submodule.span ℚ {Real.log b} := by
  have hmem : ∀ n : ℕ, baseFrequency b n ∈ (Submodule.span ℚ {Real.log b} : Submodule ℚ ℝ) := by
    intro n
    have hbase : Real.log b ∈ (Submodule.span ℚ {Real.log b} : Submodule ℚ ℝ) :=
      Submodule.mem_span_singleton_self _
    have hsmul := Submodule.smul_mem (Submodule.span ℚ {Real.log b}) (-(n : ℚ)) hbase
    have heq : (-(n : ℚ)) • Real.log b = baseFrequency b n := by
      rw [baseFrequency, Rat.smul_def]
      push_cast
      ring
    rwa [heq] at hsmul
  have hbound := bohrFrequencyModule_le_of_uniform_approx_nat
    (continuous_eulerFactorLine hb hσ) (isBohrAlmostPeriodic_eulerFactorLine hb hσ)
    ((Submodule.span ℚ {Real.log b} : Submodule ℚ ℝ) : Set ℝ) (baseFrequency b) hmem ?_
  · rwa [Submodule.span_eq] at hbound
  · intro ε hε
    obtain ⟨N, hN⟩ := ((tendsto_dirichlet_error hb hσ).eventually (gt_mem_nhds hε)).exists
    exact ⟨N, fun n => ((b ^ (-σ * n) : ℝ) : ℂ),
      fun t => le_trans (norm_eulerFactorLine_sub_dirichletSum_le hb hσ t N) hN.le⟩

/-- Infinite Dirichlet support with rank-one frequency module: the finite-rank conclusion of the
phase law is sharp, and does not imply finite support. -/
theorem rank_bohrFrequencyModule_eulerFactorLine_le_one (hb : 1 < b) (hσ : 0 < σ) :
    Module.rank ℚ (bohrFrequencyModule (eulerFactorLine b σ)) ≤ 1 := by
  refine le_trans (Submodule.rank_mono (bohrFrequencyModule_eulerFactorLine_le hb hσ)) ?_
  refine le_trans (rank_span_le _) ?_
  rw [Cardinal.mk_singleton]

/-- `b^{-s}` as a function of the complex variable. -/
noncomputable def basePower (b : ℝ) (s : ℂ) : ℂ := Complex.exp (-(s * (Real.log b : ℂ)))

/-- The Euler factor at base `b` as a function of the complex variable. -/
noncomputable def eulerFactor (b : ℝ) (s : ℂ) : ℂ := (1 - basePower b s)⁻¹

theorem basePowerLine_eq_basePower (b σ t : ℝ) :
    basePowerLine b σ t = basePower b ((σ : ℂ) + (t : ℂ) * Complex.I) := rfl

theorem eulerFactorLine_eq_eulerFactor (b σ t : ℝ) :
    eulerFactorLine b σ t = eulerFactor b ((σ : ℂ) + (t : ℂ) * Complex.I) := rfl

theorem norm_basePower (b : ℝ) (s : ℂ) : ‖basePower b s‖ = Real.exp (-(s.re * Real.log b)) := by
  rw [basePower, Complex.norm_exp]
  congr 1
  rw [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem one_sub_basePower_ne_zero (hb : 1 < b) {s : ℂ} (hs : 0 < s.re) :
    (1 : ℂ) - basePower b s ≠ 0 := by
  intro h
  have hone : basePower b s = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖basePower b s‖ = 1 := by rw [hone, norm_one]
  rw [norm_basePower] at hnorm
  have hneg : -(s.re * Real.log b) < 0 := by
    have hlog : 0 < Real.log b := log_pos_of_one_lt hb
    nlinarith
  have hlt := Real.exp_lt_one_iff.mpr hneg
  rw [hnorm] at hlt
  exact absurd hlt (lt_irrefl 1)

theorem hasDerivAt_basePower (b : ℝ) (s : ℂ) :
    HasDerivAt (basePower b) (basePower b s * (-(Real.log b : ℂ))) s := by
  have hbase : HasDerivAt (fun z : ℂ => z * (Real.log b : ℂ)) (1 * (Real.log b : ℂ)) s :=
    (hasDerivAt_id s).mul_const ((Real.log b : ℂ))
  refine (hbase.neg).cexp.congr_deriv ?_
  simp only [Pi.neg_apply]
  rw [basePower]
  ring

/-- **The Euler factor satisfies a constant-coefficient first-order algebraic differential
equation.**  It is differentially algebraic over `ℂ` — the relation carries no coefficient in `s`
at all. -/
theorem hasDerivAt_eulerFactor (hb : 1 < b) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (eulerFactor b)
      (-(Real.log b : ℂ) * (eulerFactor b s ^ 2 - eulerFactor b s)) s := by
  have hne : (1 : ℂ) - basePower b s ≠ 0 := one_sub_basePower_ne_zero hb hs
  have hden : HasDerivAt (fun z : ℂ => 1 - basePower b z)
      (basePower b s * (Real.log b : ℂ)) s := by
    refine ((hasDerivAt_basePower b s).const_sub (1 : ℂ)).congr_deriv ?_
    ring
  refine (hden.inv hne).congr_deriv ?_
  rw [eulerFactor]
  field_simp
  ring

/-- The autonomous relation in the form of eq. (8): a nonzero polynomial in the jet, with constant
coefficients, vanishes identically on the half-plane. -/
theorem eulerFactor_autonomous (hb : 1 < b) {s : ℂ} (hs : 0 < s.re) :
    deriv (eulerFactor b) s + (Real.log b : ℂ) * (eulerFactor b s ^ 2 - eulerFactor b s) = 0 := by
  rw [(hasDerivAt_eulerFactor hb hs).deriv]
  ring

end GaloisForLFunctions
