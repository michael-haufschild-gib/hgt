import GaloisForLFunctions.RHTower.Sieve.GeneralAffineMeanSquare
import GaloisForLFunctions.RHTower.Sieve.PerronPrimeSumBound
import GaloisForLFunctions.RHTower.Sieve.TwistedSeriesAsDirichletPoly
import GaloisForLFunctions.RHTower.Sieve.DirichletIntegralMeanValue
import GaloisForLFunctions.RHTower.Sieve.HalaszMeanSquare
import GaloisForLFunctions.HTGeometry.IntervalMeanSquareMoment

/-!
# The mean square of a Dirichlet polynomial is affine in the height

`DirichletDiagonal.lean` reduces the mean square of `dirPoly` to its off-diagonal sum and states that
what remains is a Hilbert inequality for the frequencies `log n`; `DirichletIntegralMeanValue.lean`
supplies the absolute-values bound `4N(1 + log N)∑|aₙ|²`, which charges the largest frequency gap to
every coefficient.

The affine mean square of `GeneralAffineMeanSquare.lean` already closes that gap for an arbitrary
finitely supported Dirichlet series, and a Dirichlet polynomial is one: reading `a` as the coefficient
sequence of the series with abscissa `0`,

`dirPoly N a t = L(a, i(-t))`,

so

`∫_{|t| ≤ T} ‖dirPoly N a t‖² dt ≤ 5πe·∑_{m < N} (m+1)‖a_m‖² + (5π/2)·T·∑_{m < N} ‖a_m‖²`.

The `n`-weighted mass replaces `N(1 + log N)` times the plain mass: never worse, since
`∑(m+1)‖a_m‖² ≤ N∑‖a_m‖²`, and better by the whole logarithm — and by a factor `N/k` whenever the mass
sits below `k`.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- The coefficient sequence of a Dirichlet polynomial, indexed from `1`. -/
noncomputable def dirSeq {N : ℕ} (a : Fin N → ℂ) : ℕ → ℂ :=
  fun n => if h : 1 ≤ n ∧ n - 1 < N then a ⟨n - 1, h.2⟩ else 0

theorem dirSeq_zero {N : ℕ} (a : Fin N → ℂ) : dirSeq a 0 = 0 := by
  rw [dirSeq]
  refine dif_neg ?_
  intro h
  omega

theorem dirSeq_succ {N : ℕ} (a : Fin N → ℂ) (m : Fin N) : dirSeq a ((m : ℕ) + 1) = a m := by
  rw [dirSeq]
  have h : 1 ≤ (m : ℕ) + 1 ∧ (m : ℕ) + 1 - 1 < N := ⟨by omega, by have := m.isLt; omega⟩
  rw [dif_pos h]
  congr 1

theorem dirSeq_support {N : ℕ} (a : Fin N → ℂ) {n : ℕ} (h : dirSeq a n ≠ 0) :
    n ∈ Finset.Icc 1 N := by
  rw [Finset.mem_Icc]
  by_contra hcon
  rw [dirSeq] at h
  refine h (dif_neg ?_)
  intro hmem
  exact hcon ⟨hmem.1, by omega⟩

/-- The polynomial coefficients are the truncated twisted coefficients at abscissa `0`. -/
theorem twistedTruncCoeff_dirSeq {N : ℕ} (a : Fin N → ℂ) :
    twistedTruncCoeff (dirSeq a) 0 N = a := by
  funext k
  rw [twistedTruncCoeff, dirSeq_succ, neg_zero, Real.rpow_zero]
  simp

/-- **A Dirichlet polynomial is a Dirichlet series with abscissa `0`.** -/
theorem LSeries_dirSeq_eq_dirPoly {N : ℕ} (a : Fin N → ℂ) (t : ℝ) :
    LSeries (dirSeq a) (((0 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I) = dirPoly N a (-t) := by
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 N := by simp
  have hsupp : ∀ n : ℕ, dirSeq a n ≠ 0 → n ∈ Finset.Icc 1 N := fun _ h => dirSeq_support a h
  have hbridge := sum_range_twistedSummand_eq_dirPoly (f := dirSeq a) (dirSeq_zero a) 0 t N
  rw [twistedTruncCoeff_dirSeq] at hbridge
  rw [← hbridge]
  have hzero : twistedSummand (dirSeq a) (((0 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I) 0 = 0 := by
    rw [twistedSummand, dirSeq_zero, zero_mul]
  have hsub : Finset.Icc 1 N ⊆ Finset.range (N + 1) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_range]
    omega
  have hout : ∀ k ∈ Finset.range (N + 1), k ∉ Finset.Icc 1 N →
      twistedSummand (dirSeq a) (((0 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I) k = 0 := by
    intro k hk hkn
    rw [Finset.mem_range] at hk
    rw [Finset.mem_Icc] at hkn
    have hk0 : k = 0 := by omega
    rw [hk0]
    exact hzero
  rw [← Finset.sum_subset hsub hout]
  refine (sum_mul_cpow_neg_eq_LSeries hs0 hsupp _).symm.trans ?_
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [twistedSummand]

/-- The `n`-weighted mass of the coefficient sequence. -/
theorem sum_Icc_mul_norm_sq_dirSeq {N : ℕ} (a : Fin N → ℂ) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) * ‖dirSeq a n * ((((n : ℝ) ^ (-(0 : ℝ)) : ℝ)) : ℂ)‖ ^ 2
      = ∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a m‖ ^ 2 := by
  rw [← sum_fin_eq_sum_Icc N
    (fun n => (n : ℝ) * ‖dirSeq a n * ((((n : ℝ) ^ (-(0 : ℝ)) : ℝ)) : ℂ)‖ ^ 2)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [dirSeq_succ, neg_zero, Real.rpow_zero]
  push_cast
  simp

/-- The plain mass of the coefficient sequence. -/
theorem sum_Icc_norm_sq_dirSeq {N : ℕ} (a : Fin N → ℂ) :
    ∑ n ∈ Finset.Icc 1 N, ‖dirSeq a n * ((((n : ℝ) ^ (-(0 : ℝ)) : ℝ)) : ℂ)‖ ^ 2
      = ∑ m : Fin N, ‖a m‖ ^ 2 := by
  rw [← sum_fin_eq_sum_Icc N
    (fun n => ‖dirSeq a n * ((((n : ℝ) ^ (-(0 : ℝ)) : ℝ)) : ℂ)‖ ^ 2)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [dirSeq_succ, neg_zero, Real.rpow_zero]
  simp

/-- **The affine mean square of a Dirichlet polynomial.**  The `n`-weighted mass replaces
`N(1 + log N)` times the plain mass. -/
theorem integral_Icc_normSq_dirPoly_le_affine {N : ℕ} (a : Fin N → ℂ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t in Set.Icc (-T) T, ‖dirPoly N a t‖ ^ 2)
      ≤ 5 * Real.pi * Real.exp 1 * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a m‖ ^ 2)
        + (5 * Real.pi / 2) * (∑ m : Fin N, ‖a m‖ ^ 2) * T := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 N := by simp
  have hsupp : ∀ n : ℕ, dirSeq a n ≠ 0 → n ∈ Finset.Icc 1 N := fun _ h => dirSeq_support a h
  have hms := integral_Icc_normSq_LSeries_le_general_affine hs0 hsupp (0 : ℝ) hT
  rw [generalMeanSquareConst, generalMeanSquareRate, sum_Icc_mul_norm_sq_dirSeq,
    sum_Icc_norm_sq_dirSeq] at hms
  have hrefl : (∫ t in Set.Icc (-T) T, ‖dirPoly N a t‖ ^ 2)
      = ∫ t in Set.Icc (-T) T, ‖LSeries (dirSeq a) (((0 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I)‖ ^ 2 := by
    have hcongr : (∫ t in Set.Icc (-T) T,
          ‖LSeries (dirSeq a) (((0 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I)‖ ^ 2)
        = ∫ t in Set.Icc (-T) T, ‖dirPoly N a (-t)‖ ^ 2 := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
      rw [LSeries_dirSeq_eq_dirPoly]
    rw [hcongr]
    exact (GaloisForLFunctions.HTGeometry.integral_Icc_normSq_comp_neg
      (fun t : ℝ => dirPoly N a t) hT0).symm
  rw [hrefl]
  exact hms

/-- **The level set of a Dirichlet polynomial, with the affine mean square.**  Chebyshev against
`integral_Icc_normSq_dirPoly_le_affine`: no factor `log N`, and the mass is `n`-weighted. -/
theorem volume_largeValues_le_affine (N : ℕ) (a : Fin N → ℂ) {T V : ℝ} (hT : 1 ≤ T) (hV : 0 ≤ V) :
    V ^ 2 * volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖}
      ≤ 5 * Real.pi * Real.exp 1 * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a m‖ ^ 2)
        + (5 * Real.pi / 2) * (∑ m : Fin N, ‖a m‖ ^ 2) * T := by
  classical
  have hT0 : (0 : ℝ) ≤ T := by linarith
  set g : ℝ → ℝ := fun t => ‖dirPoly N a t‖ ^ 2 with hg
  have hgc : Continuous g := ((continuous_dirPoly N a).norm).pow 2
  have hint : IntegrableOn g (Set.Ioc (0 : ℝ) T) := hgc.integrableOn_Ioc
  have hintIcc : IntegrableOn g (Set.Icc (-T) T) := hgc.integrableOn_Icc
  have hA : (∫ t in Set.Ioc (0 : ℝ) T, g t)
      ≤ 5 * Real.pi * Real.exp 1 * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a m‖ ^ 2)
        + (5 * Real.pi / 2) * (∑ m : Fin N, ‖a m‖ ^ 2) * T := by
    have hset : (∫ t in Set.Ioc (0 : ℝ) T, g t) ≤ ∫ t in Set.Icc (-T) T, g t := by
      refine MeasureTheory.setIntegral_mono_set hintIcc
        (Filter.Eventually.of_forall fun t => by positivity) ?_
      refine Filter.Eventually.of_forall fun t ht => ?_
      exact ⟨by linarith [ht.1], ht.2⟩
    exact le_trans hset (integral_Icc_normSq_dirPoly_le_affine a hT)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) T)] g :=
    Filter.Eventually.of_forall fun t => by positivity
  have hmark := MeasureTheory.mul_meas_ge_le_integral_of_nonneg hnn hint (V ^ 2)
  have hmeas : MeasurableSet {x : ℝ | V ^ 2 ≤ g x} :=
    measurableSet_le measurable_const hgc.measurable
  have hsub : {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖}
      ⊆ {x : ℝ | V ^ 2 ≤ g x} ∩ Set.Ioc (0 : ℝ) T := by
    rintro t ⟨ht, hle⟩
    exact ⟨by simpa [hg] using pow_le_pow_left₀ hV hle 2, ht⟩
  have hfin : volume ({x : ℝ | V ^ 2 ≤ g x} ∩ Set.Ioc (0 : ℝ) T) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Ioc]) (measure_mono Set.inter_subset_right)
  have hmono : volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖}
      ≤ (volume.restrict (Set.Ioc (0 : ℝ) T)).real {x : ℝ | V ^ 2 ≤ g x} := by
    rw [measureReal_restrict_apply hmeas]
    exact measureReal_mono hsub hfin
  have hVsq : (0 : ℝ) ≤ V ^ 2 := by positivity
  calc V ^ 2 * volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖}
      ≤ V ^ 2 * (volume.restrict (Set.Ioc (0 : ℝ) T)).real {x : ℝ | V ^ 2 ≤ g x} :=
        mul_le_mul_of_nonneg_left hmono hVsq
    _ ≤ ∫ t in Set.Ioc (0 : ℝ) T, g t := hmark
    _ ≤ _ := hA

/-- **The Halász mean-value bound with the affine mean square.**  The `N(1 + log N)` of
`integral_norm_dirPoly_halasz_on` is replaced by the `n`-weighted mass. -/
theorem integral_norm_dirPoly_halasz_affine (N : ℕ) (a : Fin N → ℂ) {T V M : ℝ} (hT : 1 ≤ T)
    (hV : 0 < V) (hM0 : 0 ≤ M) (hM : ∀ t ∈ Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖ ≤ M) :
    ∫ t in Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖
      ≤ V * T
        + M * (5 * Real.pi * Real.exp 1 * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a m‖ ^ 2)
            + (5 * Real.pi / 2) * (∑ m : Fin N, ‖a m‖ ^ 2) * T) / V ^ 2 := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hV2 : (0 : ℝ) < V ^ 2 := by positivity
  have hlev := volume_largeValues_le_affine N a hT hV.le
  have hmeas : volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖}
      ≤ (5 * Real.pi * Real.exp 1 * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a m‖ ^ 2)
          + (5 * Real.pi / 2) * (∑ m : Fin N, ‖a m‖ ^ 2) * T) / V ^ 2 := by
    rw [le_div_iff₀ hV2]
    linarith [hlev]
  refine le_trans (integral_norm_dirPoly_le_of_sup_on N a hT0 hV.le hM) ?_
  have hstep := mul_le_mul_of_nonneg_left hmeas hM0
  have hdiv : M * ((5 * Real.pi * Real.exp 1 * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a m‖ ^ 2)
        + (5 * Real.pi / 2) * (∑ m : Fin N, ‖a m‖ ^ 2) * T) / V ^ 2)
      = M * (5 * Real.pi * Real.exp 1 * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a m‖ ^ 2)
          + (5 * Real.pi / 2) * (∑ m : Fin N, ‖a m‖ ^ 2) * T) / V ^ 2 := by
    ring
  linarith [hdiv ▸ hstep]

end RHTower.Sieve
end
