import GaloisForLFunctions.HTGeometry.GeometricThetaUnbounded

/-!
# Non-negative coefficients force a cusp singularity

For a coefficient family with non-negative real values, every term of the theta
series is a positive real on the imaginary axis, so the sum dominates each of its
truncations.  Taking `N` terms at height `N^{-1/d}` turns the exponential into
the constant `e^{-2π}` and leaves the Dirichlet partial sum
`∑_{n ≤ N} a(n) n^{-σ}`, which diverges exactly when the Dirichlet series fails
to converge at `σ`.

The theta series is therefore unbounded on every disk touching the real axis,
and the shift-lattice radius law holds with no hypotheses beyond non-negativity,
a polynomial coefficient bound, and non-convergence at `σ`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

section NonnegTheta

variable {r : ℕ → ℝ}

/-- A real coefficient family, viewed as a complex one. -/
def realCoeff (r : ℕ → ℝ) : ℕ → ℂ := fun n => ((r n : ℝ) : ℂ)

@[simp] theorem realCoeff_apply (r : ℕ → ℝ) (n : ℕ) :
    realCoeff r n = ((r n : ℝ) : ℂ) := rfl

/-- The real theta term on the imaginary axis. -/
noncomputable def nonnegTerm (r : ℕ → ℝ) (σ d y : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0
  else r n * ((n : ℝ) ^ (-σ)) * Real.exp (-(2 * Real.pi * y * ((n : ℝ) ^ (1 / d))))

theorem nonnegTerm_nonneg (hr : ∀ n, 0 ≤ r n) (σ d y : ℝ) (n : ℕ) :
    0 ≤ nonnegTerm r σ d y n := by
  rw [nonnegTerm]
  split
  · exact le_rfl
  · have h1 : (0 : ℝ) ≤ r n := hr n
    have h2 : (0 : ℝ) ≤ ((n : ℝ) ^ (-σ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    positivity

/-- On the imaginary axis the terms of a real family at a real spectral parameter
are real. -/
theorem thetaTerm_realCoeff {σ d y : ℝ} {n : ℕ} (hn : 0 < n) :
    thetaTerm (realCoeff r) d (σ : ℂ) ((y : ℂ) * Complex.I) n
      = ((nonnegTerm r σ d y n : ℝ) : ℂ) := by
  rw [thetaTerm, if_neg hn.ne', nonnegTerm, if_neg hn.ne',
    Complex.ofReal_mul, Complex.ofReal_mul, shiftExp_imag]
  simp only [realCoeff_apply]
  congr 2
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  rfl

theorem summable_nonnegTerm (hr : ∀ n, 0 ≤ r n) {C B : ℝ}
    (hb : ∀ n, ‖realCoeff r n‖ ≤ C * (n : ℝ) ^ B) {σ d y : ℝ}
    (hd : 0 < d) (hy : 0 < y) : Summable (nonnegTerm r σ d y) := by
  have hbase : Summable fun n : ℕ => ‖thetaTerm (realCoeff r) d (σ : ℂ)
      ((y : ℂ) * Complex.I) n‖ := by
    refine summable_norm_thetaTerm_of_im_pos hb hd _ _ ?_
    rw [im_mul_I]
    exact hy
  refine hbase.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [thetaTerm_zero, norm_zero, nonnegTerm, if_pos rfl]
  · rw [thetaTerm_realCoeff hn, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (nonnegTerm_nonneg hr σ d y n)]

theorem thetaSeries_realCoeff (σ d y : ℝ) :
    thetaSeries (realCoeff r) d (σ : ℂ) ((y : ℂ) * Complex.I)
      = ((∑' n : ℕ, nonnegTerm r σ d y n : ℝ) : ℂ) := by
  rw [thetaSeries, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [thetaTerm_zero, nonnegTerm, if_pos rfl, Complex.ofReal_zero]
  · rw [thetaTerm_realCoeff hn]

/-- The Dirichlet partial sums of a real family. -/
noncomputable def dirichletPartial (r : ℕ → ℝ) (σ : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, r n * (n : ℝ) ^ (-σ)

theorem dirichletPartial_one (σ : ℝ) (N : ℕ) :
    dirichletPartial (fun _ => 1) σ N = pSum σ N := by
  rw [dirichletPartial, pSum]
  exact Finset.sum_congr rfl fun n _ => one_mul _

/-- **The Dirichlet partial sums diverge at and below the abscissa of
convergence.** -/
theorem tendsto_dirichletPartial_atTop (hr : ∀ n, 0 ≤ r n) {σ : ℝ}
    (hns : ¬ Summable fun n : ℕ => r n * (n : ℝ) ^ (-σ)) :
    Tendsto (dirichletPartial r σ) atTop atTop := by
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ r n * (n : ℝ) ^ (-σ) := fun n =>
    mul_nonneg (hr n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).mp hns
  have hshift : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), r n * (n : ℝ) ^ (-σ)) atTop atTop :=
    hdiv.comp (tendsto_add_atTop_nat 1)
  have hsplit : ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1), r n * (n : ℝ) ^ (-σ)
      = r 0 * ((0 : ℕ) : ℝ) ^ (-σ) + dirichletPartial r σ N := by
    intro N
    have hins : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
      ext n
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hins, Finset.sum_insert (by simp), dirichletPartial]
  have hsum : Tendsto
      (fun N : ℕ => r 0 * ((0 : ℕ) : ℝ) ^ (-σ) + dirichletPartial r σ N)
      atTop atTop := hshift.congr hsplit
  have := hsum.atTop_add (tendsto_const_nhds
    (x := -(r 0 * ((0 : ℕ) : ℝ) ^ (-σ))) (f := atTop (α := ℕ)))
  refine this.congr fun N => ?_
  ring

/-- **Truncation bound for a non-negative family.** -/
theorem le_norm_thetaSeries_nonneg (hr : ∀ n, 0 ≤ r n) {C B : ℝ}
    (hb : ∀ n, ‖realCoeff r n‖ ≤ C * (n : ℝ) ^ B) {σ d y : ℝ}
    (hd : 0 < d) (hy : 0 < y) (N : ℕ) :
    dirichletPartial r σ N * Real.exp (-(2 * Real.pi * y * ((N : ℝ) ^ (1 / d))))
      ≤ ‖thetaSeries (realCoeff r) d (σ : ℂ) ((y : ℂ) * Complex.I)‖ := by
  have hsum := summable_nonnegTerm (σ := σ) hr hb hd hy
  have hpart : dirichletPartial r σ N
        * Real.exp (-(2 * Real.pi * y * ((N : ℝ) ^ (1 / d))))
      ≤ ∑ n ∈ Finset.Icc 1 N, nonnegTerm r σ d y n := by
    rw [dirichletPartial, Finset.sum_mul]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    rw [nonnegTerm, if_neg (by omega : ¬ n = 0)]
    have hnR : (0 : ℝ) ≤ r n * ((n : ℝ) ^ (-σ)) :=
      mul_nonneg (hr n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    refine mul_le_mul_of_nonneg_left ?_ hnR
    refine Real.exp_le_exp.mpr ?_
    have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn2
    have hrp : ((n : ℝ)) ^ (1 / d) ≤ ((N : ℝ)) ^ (1 / d) :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) hnN (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hrp
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi * y)
    linarith
  have hle : ∑ n ∈ Finset.Icc 1 N, nonnegTerm r σ d y n
      ≤ ∑' n : ℕ, nonnegTerm r σ d y n :=
    Summable.sum_le_tsum _ (fun n _ => nonnegTerm_nonneg hr σ d y n) hsum
  rw [thetaSeries_realCoeff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg (nonnegTerm_nonneg hr σ d y))]
  linarith

/-- **A non-negative family whose Dirichlet series diverges at `σ` has a theta
series unbounded on every disk touching the real axis.** -/
theorem unbounded_thetaSeries_nonneg (hr : ∀ n, 0 ≤ r n) {C B : ℝ}
    (hb : ∀ n, ‖realCoeff r n‖ ≤ C * (n : ℝ) ^ B) {σ d : ℝ} (hd : 0 < d)
    (hns : ¬ Summable fun n : ℕ => r n * (n : ℝ) ^ (-σ))
    {y₀ : ℝ} (hy₀ : 0 < y₀) (M : ℝ) :
    ∃ z ∈ Metric.ball ((y₀ : ℂ) * Complex.I) y₀,
      M < ‖thetaSeries (realCoeff r) d (σ : ℂ) z‖ := by
  have hdinv : (0 : ℝ) < 1 / d := by positivity
  have hbig : ∀ᶠ N : ℕ in atTop,
      M * Real.exp (2 * Real.pi) < dirichletPartial r σ N :=
    (tendsto_dirichletPartial_atTop hr hns).eventually_gt_atTop _
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
  · refine lt_of_lt_of_le ?_ (le_norm_thetaSeries_nonneg hr hb hd hypos N)
    have hexp : -(2 * Real.pi * y * ((N : ℝ) ^ (1 / d))) = -(2 * Real.pi) := by
      rw [hyeq]
      field_simp
    rw [hexp, Real.exp_neg, ← div_eq_mul_inv,
      lt_div_iff₀ (Real.exp_pos (2 * Real.pi))]
    exact hNM

/-- **The boxed radius law, unconditionally, for every non-negative coefficient
family below its abscissa of convergence.** -/
theorem hadamardLimsup_nonnegShiftLattice (hr : ∀ n, 0 ≤ r n) {C B : ℝ}
    (hb : ∀ n, ‖realCoeff r n‖ ≤ C * (n : ℝ) ^ B) {σ d : ℝ} (hd : 0 < d)
    (hns : ¬ Summable fun n : ℕ => r n * (n : ℝ) ^ (-σ))
    {y₀ : ℝ} (hy₀ : 0 < y₀) :
    hadamardLimsup (shiftLatticeCoeff (realCoeff r) d (σ : ℂ)
        ((y₀ : ℂ) * Complex.I))
      = ENNReal.ofReal (1 / (2 * Real.pi * y₀)) := by
  have him : ((y₀ : ℂ) * Complex.I).im = y₀ := im_mul_I y₀
  have hz : 0 < ((y₀ : ℂ) * Complex.I).im := by rw [him]; exact hy₀
  have hsing : ∀ R' : ℝ, ((y₀ : ℂ) * Complex.I).im < R' →
      ¬ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball ((y₀ : ℂ) * Complex.I) R')
        ∧ ∀ z ∈ Metric.ball ((y₀ : ℂ) * Complex.I) ((y₀ : ℂ) * Complex.I).im,
            g z = thetaSeries (realCoeff r) d (σ : ℂ) z := by
    rw [him]
    exact no_analytic_extension_of_unbounded
      (unbounded_thetaSeries_nonneg hr hb hd hns hy₀)
  have h := hadamardLimsup_shiftLatticeCoeff_eq hb hd (σ : ℂ)
    ((y₀ : ℂ) * Complex.I) hz hsing
  rwa [him] at h

/-- **Radius of convergence exactly the gap, unconditionally, for every
non-negative coefficient family below its abscissa of convergence.** -/
theorem radius_nonnegShiftLattice (hr : ∀ n, 0 ≤ r n) {C B : ℝ}
    (hb : ∀ n, ‖realCoeff r n‖ ≤ C * (n : ℝ) ^ B) {σ d : ℝ} (hd : 0 < d)
    (hns : ¬ Summable fun n : ℕ => r n * (n : ℝ) ^ (-σ))
    {y₀ : ℝ} (hy₀ : 0 < y₀) :
    (FormalMultilinearSeries.ofScalars ℂ (fun k =>
        shiftFactor ^ k
          * shiftLatticeCoeff (realCoeff r) d (σ : ℂ)
              ((y₀ : ℂ) * Complex.I) k)).radius
      = ENNReal.ofReal y₀ := by
  have him : ((y₀ : ℂ) * Complex.I).im = y₀ := im_mul_I y₀
  have hz : 0 < ((y₀ : ℂ) * Complex.I).im := by rw [him]; exact hy₀
  have hsing : ∀ R' : ℝ, ((y₀ : ℂ) * Complex.I).im < R' →
      ¬ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball ((y₀ : ℂ) * Complex.I) R')
        ∧ ∀ z ∈ Metric.ball ((y₀ : ℂ) * Complex.I) ((y₀ : ℂ) * Complex.I).im,
            g z = thetaSeries (realCoeff r) d (σ : ℂ) z := by
    rw [him]
    exact no_analytic_extension_of_unbounded
      (unbounded_thetaSeries_nonneg hr hb hd hns hy₀)
  have h := radius_shiftLattice_eq hb hd (σ : ℂ) ((y₀ : ℂ) * Complex.I) hz hsing
  rwa [him] at h

end NonnegTheta

end GaloisForLFunctions.HTGeometry
