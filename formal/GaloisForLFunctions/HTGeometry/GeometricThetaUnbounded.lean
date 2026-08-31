import GaloisForLFunctions.HTGeometry.ShiftLatticeExpansion
import GaloisForLFunctions.HTGeometry.ShiftSpectrumSpacing

/-!
# The geometric theta series is unbounded at the cusp

For the constant coefficient family in degree one and spectral parameter zero the
theta series is the geometric series `∑_{n ≥ 1} e^{2πi z n}`.  On the imaginary
axis every term is a positive real, so the sum dominates any partial sum, and
taking `N` terms at height `1/N` gives a lower bound `N e^{-2π}` which diverges.

The series is therefore unbounded on every disk touching the real axis, which is
exactly the singularity certificate the radius law consumes.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

section GeometricTheta

/-- The constant coefficient family. -/
def oneCoeff : ℕ → ℂ := fun _ => 1

theorem oneCoeff_bound : ∀ n : ℕ, ‖oneCoeff n‖ ≤ 1 * (n : ℝ) ^ (0 : ℝ) := by
  intro n
  rw [oneCoeff, norm_one, Real.rpow_zero, mul_one]

/-- On the imaginary axis the terms are positive reals. -/
theorem thetaTerm_geometric {y : ℝ} {n : ℕ} (hn : 0 < n) :
    thetaTerm oneCoeff 1 0 ((y : ℂ) * Complex.I) n
      = ((Real.exp (-(2 * Real.pi * y * (n : ℝ))) : ℝ) : ℂ) := by
  rw [thetaTerm, if_neg hn.ne', oneCoeff, neg_zero, Complex.cpow_zero, one_mul,
    one_mul, Complex.ofReal_exp]
  congr 1
  have hd : ((n : ℝ)) ^ (1 / (1 : ℝ)) = (n : ℝ) := by
    rw [one_div_one, Real.rpow_one]
  rw [hd]
  push_cast
  rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((y : ℂ) * Complex.I) * (n : ℂ)
      = (2 * (Real.pi : ℂ) * (y : ℂ) * (n : ℂ)) * (Complex.I * Complex.I) by ring,
    Complex.I_mul_I]
  ring

/-- The real geometric term. -/
noncomputable def geomTerm (y : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else Real.exp (-(2 * Real.pi * y * (n : ℝ)))

theorem geomTerm_nonneg (y : ℝ) (n : ℕ) : 0 ≤ geomTerm y n := by
  rw [geomTerm]
  split
  · exact le_rfl
  · exact (Real.exp_pos _).le

theorem geomTerm_le_pow (y : ℝ) (n : ℕ) :
    geomTerm y n ≤ (Real.exp (-(2 * Real.pi * y))) ^ n := by
  rw [geomTerm]
  split
  · positivity
  · rw [← Real.exp_nat_mul]
    apply le_of_eq
    congr 1
    ring

theorem summable_geomTerm {y : ℝ} (hy : 0 < y) : Summable (geomTerm y) := by
  have hr : Real.exp (-(2 * Real.pi * y)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have := Real.pi_pos
    nlinarith
  refine Summable.of_nonneg_of_le (geomTerm_nonneg y) (geomTerm_le_pow y) ?_
  exact summable_geometric_of_lt_one (Real.exp_pos _).le hr

theorem thetaSeries_geometric (y : ℝ) :
    thetaSeries oneCoeff 1 0 ((y : ℂ) * Complex.I)
      = ((∑' n : ℕ, geomTerm y n : ℝ) : ℂ) := by
  rw [thetaSeries, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [thetaTerm_zero, geomTerm, if_pos rfl, Complex.ofReal_zero]
  · rw [thetaTerm_geometric hn, geomTerm, if_neg hn.ne']

/-- **Lower bound by a truncation.**  Taking `N` terms on the imaginary axis
gives `N e^{-2πyN}`. -/
theorem le_norm_thetaSeries_geometric {y : ℝ} (hy : 0 < y) (N : ℕ) :
    (N : ℝ) * Real.exp (-(2 * Real.pi * y * (N : ℝ)))
      ≤ ‖thetaSeries oneCoeff 1 0 ((y : ℂ) * Complex.I)‖ := by
  have hsum := summable_geomTerm hy
  have hpart : (N : ℝ) * Real.exp (-(2 * Real.pi * y * (N : ℝ)))
      ≤ ∑ n ∈ Finset.Icc 1 N, geomTerm y n := by
    have hcard : (Finset.Icc 1 N).card = N := by
      rw [Nat.card_Icc]
      omega
    calc (N : ℝ) * Real.exp (-(2 * Real.pi * y * (N : ℝ)))
        = ∑ _n ∈ Finset.Icc 1 N, Real.exp (-(2 * Real.pi * y * (N : ℝ))) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
      _ ≤ ∑ n ∈ Finset.Icc 1 N, geomTerm y n := by
          refine Finset.sum_le_sum fun n hn => ?_
          obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
          rw [geomTerm, if_neg (by omega : ¬ n = 0)]
          refine Real.exp_le_exp.mpr ?_
          have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn2
          have hmul := mul_le_mul_of_nonneg_left hnN
            (by positivity : (0 : ℝ) ≤ 2 * Real.pi * y)
          linarith
  have hle : ∑ n ∈ Finset.Icc 1 N, geomTerm y n ≤ ∑' n : ℕ, geomTerm y n :=
    Summable.sum_le_tsum _ (fun n _ => geomTerm_nonneg y n) hsum
  rw [thetaSeries_geometric, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg (geomTerm_nonneg y))]
  linarith

/-- **The geometric theta series is unbounded on every disk touching the real
axis.** -/
theorem unbounded_thetaSeries_geometric {y₀ : ℝ} (hy₀ : 0 < y₀) (M : ℝ) :
    ∃ z ∈ Metric.ball ((y₀ : ℂ) * Complex.I) y₀,
      M < ‖thetaSeries oneCoeff 1 0 z‖ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (M * Real.exp (2 * Real.pi)) (1 / y₀))
  have hN1 : (1 : ℝ) / y₀ < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hNM : M * Real.exp (2 * Real.pi) < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_trans (by positivity) hN1
  set y : ℝ := 1 / (N : ℝ) with hy
  have hypos : 0 < y := by rw [hy]; positivity
  have hylt : y < y₀ := by
    rw [hy, div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hy₀] at hN1
    linarith
  refine ⟨(y : ℂ) * Complex.I, ?_, ?_⟩
  · rw [Metric.mem_ball, Complex.dist_eq, ← sub_mul, Complex.norm_mul, Complex.norm_I,
      mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  · refine lt_of_lt_of_le ?_ (le_norm_thetaSeries_geometric hypos N)
    have hexp : -(2 * Real.pi * y * (N : ℝ)) = -(2 * Real.pi) := by
      rw [hy]
      field_simp
    rw [hexp, Real.exp_neg, ← div_eq_mul_inv,
      lt_div_iff₀ (Real.exp_pos (2 * Real.pi))]
    exact hNM

theorem im_mul_I (y : ℝ) : ((y : ℂ) * Complex.I).im = y := by
  simp

/-- **The boxed radius law, unconditionally, for the geometric family.**  For the
constant coefficient family in degree one at spectral parameter zero the
shift-lattice expansion at `i y₀` has growth functional exactly
`1/(2π y₀)`, with no hypotheses: the singularity is proved, not assumed. -/
theorem hadamardLimsup_geometricShiftLattice {y₀ : ℝ} (hy₀ : 0 < y₀) :
    hadamardLimsup (shiftLatticeCoeff oneCoeff 1 0 ((y₀ : ℂ) * Complex.I))
      = ENNReal.ofReal (1 / (2 * Real.pi * y₀)) := by
  have him : ((y₀ : ℂ) * Complex.I).im = y₀ := im_mul_I y₀
  have hz : 0 < ((y₀ : ℂ) * Complex.I).im := by rw [him]; exact hy₀
  have hsing : ∀ R' : ℝ, ((y₀ : ℂ) * Complex.I).im < R' →
      ¬ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball ((y₀ : ℂ) * Complex.I) R')
        ∧ ∀ z ∈ Metric.ball ((y₀ : ℂ) * Complex.I) ((y₀ : ℂ) * Complex.I).im,
            g z = thetaSeries oneCoeff 1 0 z := by
    rw [him]
    exact no_analytic_extension_of_unbounded (unbounded_thetaSeries_geometric hy₀)
  have h := hadamardLimsup_shiftLatticeCoeff_eq oneCoeff_bound (by norm_num : (0:ℝ) < 1)
    0 ((y₀ : ℂ) * Complex.I) hz hsing
  rwa [him] at h

/-- **The radius is exactly the height, unconditionally, for the geometric
family.**  This is the card's primary phrasing — "with radius of convergence
exactly `Δ(α₀)`" — with no hypotheses. -/
theorem radius_geometricShiftLattice {y₀ : ℝ} (hy₀ : 0 < y₀) :
    (FormalMultilinearSeries.ofScalars ℂ
        (fun k => shiftFactor ^ k
          * shiftLatticeCoeff oneCoeff 1 0 ((y₀ : ℂ) * Complex.I) k)).radius
      = ENNReal.ofReal y₀ := by
  have him : ((y₀ : ℂ) * Complex.I).im = y₀ := im_mul_I y₀
  have hz : 0 < ((y₀ : ℂ) * Complex.I).im := by rw [him]; exact hy₀
  have hsing : ∀ R' : ℝ, ((y₀ : ℂ) * Complex.I).im < R' →
      ¬ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball ((y₀ : ℂ) * Complex.I) R')
        ∧ ∀ z ∈ Metric.ball ((y₀ : ℂ) * Complex.I) ((y₀ : ℂ) * Complex.I).im,
            g z = thetaSeries oneCoeff 1 0 z := by
    rw [him]
    exact no_analytic_extension_of_unbounded (unbounded_thetaSeries_geometric hy₀)
  have h := radius_shiftLattice_eq oneCoeff_bound (by norm_num : (0:ℝ) < 1)
    0 ((y₀ : ℂ) * Complex.I) hz hsing
  rwa [him] at h

end GeometricTheta

section PowerTheta

/-- The real term of the constant family at a real spectral parameter. -/
noncomputable def powTerm (σ y : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else ((n : ℝ) ^ (-σ)) * Real.exp (-(2 * Real.pi * y * (n : ℝ)))

theorem powTerm_nonneg (σ y : ℝ) (n : ℕ) : 0 ≤ powTerm σ y n := by
  rw [powTerm]
  split
  · exact le_rfl
  · positivity

/-- On the imaginary axis the terms at a real spectral parameter are positive
reals. -/
theorem thetaTerm_pow {σ y : ℝ} {n : ℕ} (hn : 0 < n) :
    thetaTerm oneCoeff 1 (σ : ℂ) ((y : ℂ) * Complex.I) n
      = ((powTerm σ y n : ℝ) : ℂ) := by
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [thetaTerm, if_neg hn.ne', oneCoeff, one_mul, powTerm, if_neg hn.ne']
  have hcpow : ((n : ℂ)) ^ (-(σ : ℂ)) = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hnR]
    push_cast
    rfl
  have hd : ((n : ℝ)) ^ (1 / (1 : ℝ)) = (n : ℝ) := by
    rw [one_div_one, Real.rpow_one]
  rw [hcpow, hd, Complex.ofReal_mul, Complex.ofReal_exp]
  congr 1
  push_cast
  rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((y : ℂ) * Complex.I) * (n : ℂ)
      = (2 * (Real.pi : ℂ) * (y : ℂ) * (n : ℂ)) * (Complex.I * Complex.I) by ring,
    Complex.I_mul_I]
  ring

theorem summable_powTerm {σ y : ℝ} (hy : 0 < y) : Summable (powTerm σ y) := by
  have hbase : Summable fun n : ℕ => ‖thetaTerm oneCoeff 1 (σ : ℂ)
      ((y : ℂ) * Complex.I) n‖ := by
    refine summable_norm_thetaTerm_of_im_pos oneCoeff_bound (by norm_num) _ _ ?_
    rw [im_mul_I]
    exact hy
  refine hbase.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [thetaTerm_zero, norm_zero, powTerm, if_pos rfl]
  · rw [thetaTerm_pow hn, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (powTerm_nonneg σ y n)]

theorem thetaSeries_pow (σ y : ℝ) :
    thetaSeries oneCoeff 1 (σ : ℂ) ((y : ℂ) * Complex.I)
      = ((∑' n : ℕ, powTerm σ y n : ℝ) : ℂ) := by
  rw [thetaSeries, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [thetaTerm_zero, powTerm, if_pos rfl, Complex.ofReal_zero]
  · rw [thetaTerm_pow hn]

/-- The partial sums of the `p`-series. -/
noncomputable def pSum (σ : ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ)

/-- **Truncation bound at a real spectral parameter.** -/
theorem le_norm_thetaSeries_pow {σ y : ℝ} (hy : 0 < y) (N : ℕ) :
    pSum σ N * Real.exp (-(2 * Real.pi * y * (N : ℝ)))
      ≤ ‖thetaSeries oneCoeff 1 (σ : ℂ) ((y : ℂ) * Complex.I)‖ := by
  have hsum := summable_powTerm (σ := σ) hy
  have hpart : pSum σ N * Real.exp (-(2 * Real.pi * y * (N : ℝ)))
      ≤ ∑ n ∈ Finset.Icc 1 N, powTerm σ y n := by
    rw [pSum, Finset.sum_mul]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    rw [powTerm, if_neg (by omega : ¬ n = 0)]
    have hnR : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    refine mul_le_mul_of_nonneg_left ?_ hnR
    refine Real.exp_le_exp.mpr ?_
    have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn2
    have hmul := mul_le_mul_of_nonneg_left hnN
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi * y)
    linarith
  have hle : ∑ n ∈ Finset.Icc 1 N, powTerm σ y n ≤ ∑' n : ℕ, powTerm σ y n :=
    Summable.sum_le_tsum _ (fun n _ => powTerm_nonneg σ y n) hsum
  rw [thetaSeries_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg (powTerm_nonneg σ y))]
  linarith

/-- **The `p`-series partial sums diverge at and below the abscissa.** -/
theorem tendsto_pSum_atTop {σ : ℝ} (hσ : σ ≤ 1) :
    Tendsto (pSum σ) atTop atTop := by
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := fun n =>
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hns : ¬ Summable fun n : ℕ => (n : ℝ) ^ (-σ) := by
    intro hsum
    have hps : Summable fun n : ℕ => 1 / ((n : ℝ)) ^ σ := by
      refine hsum.congr fun n => ?_
      rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
    rw [Real.summable_one_div_nat_rpow] at hps
    linarith
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).mp hns
  have hshift : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), (n : ℝ) ^ (-σ))
      atTop atTop := hdiv.comp (tendsto_add_atTop_nat 1)
  have hsplit : ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1), (n : ℝ) ^ (-σ)
      = ((0 : ℕ) : ℝ) ^ (-σ) + pSum σ N := by
    intro N
    have hins : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
      ext n
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hins, Finset.sum_insert (by simp), pSum]
  have hsum : Tendsto (fun N : ℕ => ((0 : ℕ) : ℝ) ^ (-σ) + pSum σ N) atTop atTop :=
    hshift.congr hsplit
  have := hsum.atTop_add (tendsto_const_nhds (x := -(((0 : ℕ) : ℝ) ^ (-σ)))
    (f := atTop (α := ℕ)))
  refine this.congr fun N => ?_
  ring

/-- **The theta series at a real spectral parameter at or below one is unbounded
on every disk touching the real axis.** -/
theorem unbounded_thetaSeries_pow {σ : ℝ} (hσ : σ ≤ 1) {y₀ : ℝ} (hy₀ : 0 < y₀)
    (M : ℝ) :
    ∃ z ∈ Metric.ball ((y₀ : ℂ) * Complex.I) y₀,
      M < ‖thetaSeries oneCoeff 1 (σ : ℂ) z‖ := by
  have hdiv := tendsto_pSum_atTop hσ
  have hbig : ∀ᶠ N : ℕ in atTop, M * Real.exp (2 * Real.pi) < pSum σ N :=
    hdiv.eventually_gt_atTop _
  have hsmall : ∀ᶠ N : ℕ in atTop, (1 : ℝ) / y₀ < (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  obtain ⟨N, hNM, hN1⟩ := (hbig.and hsmall).exists
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_trans (by positivity) hN1
  set y : ℝ := 1 / (N : ℝ) with hy
  have hypos : 0 < y := by rw [hy]; positivity
  have hylt : y < y₀ := by
    rw [hy, div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hy₀] at hN1
    linarith
  refine ⟨(y : ℂ) * Complex.I, ?_, ?_⟩
  · rw [Metric.mem_ball, Complex.dist_eq, ← sub_mul, Complex.norm_mul, Complex.norm_I,
      mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  · refine lt_of_lt_of_le ?_ (le_norm_thetaSeries_pow hypos N)
    have hexp : -(2 * Real.pi * y * (N : ℝ)) = -(2 * Real.pi) := by
      rw [hy]
      field_simp
    rw [hexp, Real.exp_neg, ← div_eq_mul_inv,
      lt_div_iff₀ (Real.exp_pos (2 * Real.pi))]
    exact hNM

/-- **The boxed radius law, unconditionally, at every real spectral parameter at
or below one.**  For the constant coefficient family in degree one the
shift-lattice expansion at `i y₀` has growth functional exactly `1/(2π y₀)`. -/
theorem hadamardLimsup_powShiftLattice {σ : ℝ} (hσ : σ ≤ 1) {y₀ : ℝ}
    (hy₀ : 0 < y₀) :
    hadamardLimsup (shiftLatticeCoeff oneCoeff 1 (σ : ℂ) ((y₀ : ℂ) * Complex.I))
      = ENNReal.ofReal (1 / (2 * Real.pi * y₀)) := by
  have him : ((y₀ : ℂ) * Complex.I).im = y₀ := im_mul_I y₀
  have hz : 0 < ((y₀ : ℂ) * Complex.I).im := by rw [him]; exact hy₀
  have hsing : ∀ R' : ℝ, ((y₀ : ℂ) * Complex.I).im < R' →
      ¬ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball ((y₀ : ℂ) * Complex.I) R')
        ∧ ∀ z ∈ Metric.ball ((y₀ : ℂ) * Complex.I) ((y₀ : ℂ) * Complex.I).im,
            g z = thetaSeries oneCoeff 1 (σ : ℂ) z := by
    rw [him]
    exact no_analytic_extension_of_unbounded (unbounded_thetaSeries_pow hσ hy₀)
  have h := hadamardLimsup_shiftLatticeCoeff_eq oneCoeff_bound
    (by norm_num : (0:ℝ) < 1) (σ : ℂ) ((y₀ : ℂ) * Complex.I) hz hsing
  rwa [him] at h

end PowerTheta

section DegreeTheta

/-- On the imaginary axis the shift character is a real decaying exponential. -/
theorem shiftExp_imag (y t : ℝ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((y : ℂ) * Complex.I) * (t : ℂ))
      = ((Real.exp (-(2 * Real.pi * y * t)) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((y : ℂ) * Complex.I) * (t : ℂ)
      = (2 * (Real.pi : ℂ) * (y : ℂ) * (t : ℂ)) * (Complex.I * Complex.I) by ring,
    Complex.I_mul_I]
  ring

/-- The real theta term of the constant family at a real spectral parameter in
degree `d`. -/
noncomputable def degTerm (σ d y : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0
  else ((n : ℝ) ^ (-σ)) * Real.exp (-(2 * Real.pi * y * ((n : ℝ) ^ (1 / d))))

theorem degTerm_nonneg (σ d y : ℝ) (n : ℕ) : 0 ≤ degTerm σ d y n := by
  rw [degTerm]
  split
  · exact le_rfl
  · positivity

/-- On the imaginary axis every term of the degree-`d` theta series at a real
spectral parameter is a positive real. -/
theorem thetaTerm_deg {σ d y : ℝ} {n : ℕ} (hn : 0 < n) :
    thetaTerm oneCoeff d (σ : ℂ) ((y : ℂ) * Complex.I) n
      = ((degTerm σ d y n : ℝ) : ℂ) := by
  rw [thetaTerm, if_neg hn.ne', oneCoeff, one_mul, degTerm, if_neg hn.ne',
    Complex.ofReal_mul, shiftExp_imag]
  congr 1
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  rfl

theorem summable_degTerm {σ d y : ℝ} (hd : 0 < d) (hy : 0 < y) :
    Summable (degTerm σ d y) := by
  have hbase : Summable fun n : ℕ => ‖thetaTerm oneCoeff d (σ : ℂ)
      ((y : ℂ) * Complex.I) n‖ := by
    refine summable_norm_thetaTerm_of_im_pos oneCoeff_bound hd _ _ ?_
    rw [im_mul_I]
    exact hy
  refine hbase.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [thetaTerm_zero, norm_zero, degTerm, if_pos rfl]
  · rw [thetaTerm_deg hn, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (degTerm_nonneg σ d y n)]

theorem thetaSeries_deg (σ d y : ℝ) :
    thetaSeries oneCoeff d (σ : ℂ) ((y : ℂ) * Complex.I)
      = ((∑' n : ℕ, degTerm σ d y n : ℝ) : ℂ) := by
  rw [thetaSeries, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [thetaTerm_zero, degTerm, if_pos rfl, Complex.ofReal_zero]
  · rw [thetaTerm_deg hn]

/-- **Truncation bound in degree `d`.**  The first `N` terms are all at least the
`N`-th exponential, so the whole sum dominates `(∑_{n ≤ N} n^{-σ}) e^{-2π y N^{1/d}}`. -/
theorem le_norm_thetaSeries_deg {σ d y : ℝ} (hd : 0 < d) (hy : 0 < y) (N : ℕ) :
    pSum σ N * Real.exp (-(2 * Real.pi * y * ((N : ℝ) ^ (1 / d))))
      ≤ ‖thetaSeries oneCoeff d (σ : ℂ) ((y : ℂ) * Complex.I)‖ := by
  have hsum := summable_degTerm (σ := σ) hd hy
  have hpart : pSum σ N * Real.exp (-(2 * Real.pi * y * ((N : ℝ) ^ (1 / d))))
      ≤ ∑ n ∈ Finset.Icc 1 N, degTerm σ d y n := by
    rw [pSum, Finset.sum_mul]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    rw [degTerm, if_neg (by omega : ¬ n = 0)]
    have hnR : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    refine mul_le_mul_of_nonneg_left ?_ hnR
    refine Real.exp_le_exp.mpr ?_
    have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn2
    have hrp : ((n : ℝ)) ^ (1 / d) ≤ ((N : ℝ)) ^ (1 / d) :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) hnN (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hrp
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi * y)
    linarith
  have hle : ∑ n ∈ Finset.Icc 1 N, degTerm σ d y n ≤ ∑' n : ℕ, degTerm σ d y n :=
    Summable.sum_le_tsum _ (fun n _ => degTerm_nonneg σ d y n) hsum
  rw [thetaSeries_deg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg (degTerm_nonneg σ d y))]
  linarith

/-- Every positive inverse real power of the natural index tends to zero. -/
theorem tendsto_natCast_rpow_neg_atTop {u : ℝ} (hu : 0 < u) :
    Tendsto (fun N : ℕ => ((N : ℝ)) ^ (-u)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun x : ℝ => x ^ u) atTop atTop :=
    tendsto_rpow_atTop hu
  have hinv : Tendsto (fun x : ℝ => (x ^ u)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hpow
  have hzeroReal : Tendsto (fun x : ℝ => x ^ (-u)) atTop (𝓝 0) := by
    refine hinv.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_neg hx.le]
  exact hzeroReal.comp tendsto_natCast_atTop_atTop

/-- **The degree-`d` theta series of the constant family at a real spectral
parameter at or below one is unbounded on every disk touching the real axis.**
At height `N^{-1/d}` the exponential is the constant `e^{-2π}` and the prefactor
is the `p`-series partial sum, which diverges. -/
theorem unbounded_thetaSeries_deg {σ d : ℝ} (hσ : σ ≤ 1) (hd : 0 < d)
    {y₀ : ℝ} (hy₀ : 0 < y₀) (M : ℝ) :
    ∃ z ∈ Metric.ball ((y₀ : ℂ) * Complex.I) y₀,
      M < ‖thetaSeries oneCoeff d (σ : ℂ) z‖ := by
  have hdinv : (0 : ℝ) < 1 / d := by positivity
  have hbig : ∀ᶠ N : ℕ in atTop, M * Real.exp (2 * Real.pi) < pSum σ N :=
    (tendsto_pSum_atTop hσ).eventually_gt_atTop _
  have hzero : Tendsto (fun N : ℕ => ((N : ℝ)) ^ (-(1 / d))) atTop (𝓝 0) :=
    tendsto_natCast_rpow_neg_atTop hdinv
  have hsmall : ∀ᶠ N : ℕ in atTop, ((N : ℝ)) ^ (-(1 / d)) < y₀ :=
    hzero.eventually_lt_const hy₀
  obtain ⟨N, ⟨hNM, hNy⟩, hN1⟩ :=
    ((hbig.and hsmall).and (eventually_ge_atTop 1)).exists
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hrpos : (0 : ℝ) < ((N : ℝ)) ^ (1 / d) := Real.rpow_pos_of_pos hNpos _
  set y : ℝ := ((N : ℝ)) ^ (-(1 / d)) with hy
  have hyeq : y = (((N : ℝ)) ^ (1 / d))⁻¹ := by
    rw [hy, Real.rpow_neg hNpos.le]
  have hypos : 0 < y := by rw [hyeq]; positivity
  refine ⟨(y : ℂ) * Complex.I, ?_, ?_⟩
  · rw [Metric.mem_ball, Complex.dist_eq, ← sub_mul, Complex.norm_mul, Complex.norm_I,
      mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  · refine lt_of_lt_of_le ?_ (le_norm_thetaSeries_deg hd hypos N)
    have hexp : -(2 * Real.pi * y * ((N : ℝ) ^ (1 / d))) = -(2 * Real.pi) := by
      rw [hyeq]
      field_simp
    rw [hexp, Real.exp_neg, ← div_eq_mul_inv,
      lt_div_iff₀ (Real.exp_pos (2 * Real.pi))]
    exact hNM

/-- **The boxed radius law, unconditionally, in every degree and at every real
spectral parameter at or below one.**  For the constant coefficient family the
shift-lattice expansion at `i y₀` has growth functional exactly `1/(2π y₀)`. -/
theorem hadamardLimsup_degShiftLattice {σ d : ℝ} (hσ : σ ≤ 1) (hd : 0 < d)
    {y₀ : ℝ} (hy₀ : 0 < y₀) :
    hadamardLimsup (shiftLatticeCoeff oneCoeff d (σ : ℂ) ((y₀ : ℂ) * Complex.I))
      = ENNReal.ofReal (1 / (2 * Real.pi * y₀)) := by
  have him : ((y₀ : ℂ) * Complex.I).im = y₀ := im_mul_I y₀
  have hz : 0 < ((y₀ : ℂ) * Complex.I).im := by rw [him]; exact hy₀
  have hsing : ∀ R' : ℝ, ((y₀ : ℂ) * Complex.I).im < R' →
      ¬ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball ((y₀ : ℂ) * Complex.I) R')
        ∧ ∀ z ∈ Metric.ball ((y₀ : ℂ) * Complex.I) ((y₀ : ℂ) * Complex.I).im,
            g z = thetaSeries oneCoeff d (σ : ℂ) z := by
    rw [him]
    exact no_analytic_extension_of_unbounded (unbounded_thetaSeries_deg hσ hd hy₀)
  have h := hadamardLimsup_shiftLatticeCoeff_eq oneCoeff_bound hd (σ : ℂ)
    ((y₀ : ℂ) * Complex.I) hz hsing
  rwa [him] at h

/-- **Radius of convergence exactly the gap, unconditionally, in every degree and
at every real spectral parameter at or below one.** -/
theorem radius_degShiftLattice {σ d : ℝ} (hσ : σ ≤ 1) (hd : 0 < d)
    {y₀ : ℝ} (hy₀ : 0 < y₀) :
    (FormalMultilinearSeries.ofScalars ℂ (fun k =>
        shiftFactor ^ k
          * shiftLatticeCoeff oneCoeff d (σ : ℂ) ((y₀ : ℂ) * Complex.I) k)).radius
      = ENNReal.ofReal y₀ := by
  have him : ((y₀ : ℂ) * Complex.I).im = y₀ := im_mul_I y₀
  have hz : 0 < ((y₀ : ℂ) * Complex.I).im := by rw [him]; exact hy₀
  have hsing : ∀ R' : ℝ, ((y₀ : ℂ) * Complex.I).im < R' →
      ¬ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball ((y₀ : ℂ) * Complex.I) R')
        ∧ ∀ z ∈ Metric.ball ((y₀ : ℂ) * Complex.I) ((y₀ : ℂ) * Complex.I).im,
            g z = thetaSeries oneCoeff d (σ : ℂ) z := by
    rw [him]
    exact no_analytic_extension_of_unbounded (unbounded_thetaSeries_deg hσ hd hy₀)
  have h := radius_shiftLattice_eq oneCoeff_bound hd (σ : ℂ)
    ((y₀ : ℂ) * Complex.I) hz hsing
  rwa [him] at h

end DegreeTheta

end GaloisForLFunctions.HTGeometry
