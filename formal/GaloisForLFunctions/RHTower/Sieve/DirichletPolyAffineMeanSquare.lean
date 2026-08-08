import GaloisForLFunctions.RHTower.Sieve.GeneralAffineMeanSquare
import GaloisForLFunctions.RHTower.Sieve.PerronPrimeSumBound
import GaloisForLFunctions.RHTower.Sieve.TwistedSeriesAsDirichletPoly
import GaloisForLFunctions.RHTower.Sieve.DirichletIntegralMeanValue
import GaloisForLFunctions.RHTower.Sieve.HalaszMeanSquare
import GaloisForLFunctions.RHTower.Sieve.MoebiusSmoothCancellation
import GaloisForLFunctions.RHTower.Sieve.PerronNearDiagonal
import GaloisForLFunctions.HTGeometry.IntervalMeanSquareMoment
import GaloisForLFunctions.RHTower.Sieve.CesaroDyadicMeanSquare
import GaloisForLFunctions.RHTower.Sieve.AffineMeanSquareL1

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

/-- **The affine mean square with no lower bound on the height.**  For `T ≤ 1` the range sits inside
`[-1, 1]`, where the estimate at `T = 1` applies. -/
theorem integral_Icc_normSq_dirPoly_le_affine_max {N : ℕ} (a : Fin N → ℂ) (T : ℝ) :
    (∫ t in Set.Icc (-T) T, ‖dirPoly N a t‖ ^ 2)
      ≤ 5 * Real.pi * Real.exp 1 * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a m‖ ^ 2)
        + (5 * Real.pi / 2) * (∑ m : Fin N, ‖a m‖ ^ 2) * max T 1 := by
  rcases le_total 1 T with h | h
  · rw [max_eq_left h]
    exact integral_Icc_normSq_dirPoly_le_affine a h
  · rw [max_eq_right h]
    have hsub : (∫ t in Set.Icc (-T) T, ‖dirPoly N a t‖ ^ 2)
        ≤ ∫ t in Set.Icc (-1 : ℝ) 1, ‖dirPoly N a t‖ ^ 2 := by
      refine MeasureTheory.setIntegral_mono_set
        (((continuous_dirPoly N a).norm.pow 2).integrableOn_Icc)
        (Filter.Eventually.of_forall fun t => by positivity)
        (Filter.Eventually.of_forall fun t ht => ?_)
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h1 := integral_Icc_normSq_dirPoly_le_affine a (le_refl (1 : ℝ))
    linarith


/-- **The first moment of a Dirichlet polynomial against the second-order kernel.**  The affine mean
square feeds the dyadic block law, so the bound is uniform in the height. -/
theorem integral_symm_norm_dirPoly_mul_cesaroKernel_le {N : ℕ} (a : Fin N → ℂ) {σ x T : ℝ}
    (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (hx : 0 < x) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖dirPoly N a t‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2))
      ≤ 8 * x ^ σ * Real.sqrt (5 * Real.pi * Real.exp 1
            * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a m‖ ^ 2))
        + 12 * x ^ σ * Real.sqrt ((5 * Real.pi / 2) * (∑ m : Fin N, ‖a m‖ ^ 2)) := by
  have hQ0 : (0 : ℝ) ≤ 5 * Real.pi * Real.exp 1
      * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a m‖ ^ 2) := by
    have : (0 : ℝ) ≤ ∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a m‖ ^ 2 :=
      Finset.sum_nonneg fun m _ => by positivity
    positivity
  have hκ0 : (0 : ℝ) ≤ (5 * Real.pi / 2) * (∑ m : Fin N, ‖a m‖ ^ 2) := by
    have : (0 : ℝ) ≤ ∑ m : Fin N, ‖a m‖ ^ 2 := Finset.sum_nonneg fun m _ => by positivity
    positivity
  refine integral_symm_norm_mul_cesaroKernel_le_of_meanSquare (continuous_dirPoly N a) hQ0 hκ0
    hσ1 hσ2 hx hT ?_
  intro U hU
  have h := integral_Icc_normSq_dirPoly_le_affine a (by linarith : (1 : ℝ) ≤ U)
  linarith


/-- **The first moment of a Dirichlet polynomial on a symmetric range.**  Cauchy–Schwarz against `1`
and the affine mean square.  Against
`DirichletFirstMomentLargeValues.integral_norm_dirPoly_le_largeValues`, which discretises by cell
maxima and pays the harmonic cost `(1/Δ + 2 log N)` of the discrete mean value, this has the same shape
with no logarithm and with the `n`-weighted mass in place of `N` times the plain mass. -/
theorem integral_Icc_norm_dirPoly_le_sqrt_affine {N : ℕ} (a : Fin N → ℂ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t in Set.Icc (-T) T, ‖dirPoly N a t‖)
      ≤ Real.sqrt (2 * T
          * (5 * Real.pi * Real.exp 1 * (∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖a m‖ ^ 2)
            + (5 * Real.pi / 2) * (∑ m : Fin N, ‖a m‖ ^ 2) * T)) := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 N := by simp
  have hsupp : ∀ n : ℕ, dirSeq a n ≠ 0 → n ∈ Finset.Icc 1 N := fun _ h => dirSeq_support a h
  have hcongr : (∫ t in Set.Icc (-T) T, ‖dirPoly N a t‖)
      = ∫ t in Set.Icc (-T) T, ‖LSeries (dirSeq a) (((0 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I)‖ := by
    have hstep : (∫ t in Set.Icc (-T) T,
          ‖LSeries (dirSeq a) (((0 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I)‖)
        = ∫ t in Set.Icc (-T) T, ‖dirPoly N a (-t)‖ := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
      rw [LSeries_dirSeq_eq_dirPoly]
    rw [hstep]
    exact (GaloisForLFunctions.HTGeometry.integral_Icc_comp_neg
      (fun t : ℝ => ‖dirPoly N a t‖) hT0).symm
  rw [hcongr]
  refine le_trans (integral_Icc_norm_LSeries_le_sqrt_general_affine hs0 hsupp (0 : ℝ) hT)
    (Real.sqrt_le_sqrt ?_)
  rw [generalMeanSquareConst, generalMeanSquareRate, sum_Icc_mul_norm_sq_dirSeq,
    sum_Icc_norm_sq_dirSeq]


section
variable {f : ℕ → ℂ}

/-- Each twisted coefficient square is at most `1/n²`. -/
theorem norm_sq_twistedTruncCoeff_le (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 ≤ σ) (L : ℕ)
    (m : Fin L) :
    ‖twistedTruncCoeff f σ L m‖ ^ 2 ≤ 1 / (((m : ℕ) : ℝ) + 1) ^ 2 := by
  have hb : (1 : ℝ) ≤ ((m : ℕ) : ℝ) + 1 := by
    have : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have h1 := norm_twistedTruncCoeff_le hbdd σ L m
  have hstep : (((m : ℕ) : ℝ) + 1) ^ (-σ) ≤ 1 / (((m : ℕ) : ℝ) + 1) := by
    have hmono : (((m : ℕ) : ℝ) + 1) ^ (-σ) ≤ (((m : ℕ) : ℝ) + 1) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hb (by linarith)
    have hval : (((m : ℕ) : ℝ) + 1) ^ (-1 : ℝ) = 1 / (((m : ℕ) : ℝ) + 1) := by
      rw [Real.rpow_neg (by linarith), Real.rpow_one, one_div]
    rwa [hval] at hmono
  have hle : ‖twistedTruncCoeff f σ L m‖ ≤ 1 / (((m : ℕ) : ℝ) + 1) := le_trans h1 hstep
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hle 2
  calc ‖twistedTruncCoeff f σ L m‖ ^ 2 ≤ (1 / (((m : ℕ) : ℝ) + 1)) ^ 2 := hsq
    _ = 1 / (((m : ℕ) : ℝ) + 1) ^ 2 := by rw [div_pow, one_pow]

/-- The plain mass of the twisted coefficients is at most `2`. -/
theorem sum_norm_sq_twistedTruncCoeff_le_two (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 ≤ σ)
    (L : ℕ) :
    ∑ m : Fin L, ‖twistedTruncCoeff f σ L m‖ ^ 2 ≤ 2 := by
  have hstep : ∑ m : Fin L, ‖twistedTruncCoeff f σ L m‖ ^ 2
      ≤ ∑ m : Fin L, 1 / (((m : ℕ) : ℝ) + 1) ^ 2 :=
    Finset.sum_le_sum fun m _ => norm_sq_twistedTruncCoeff_le hbdd hσ L m
  have hcast : ∑ m : Fin L, 1 / (((m : ℕ) : ℝ) + 1) ^ 2
      = ∑ k ∈ Finset.Icc 1 L, 1 / (k : ℝ) ^ 2 := by
    rw [← sum_fin_eq_sum_Icc L (fun k => 1 / (k : ℝ) ^ 2)]
    refine Finset.sum_congr rfl fun m _ => ?_
    push_cast
    ring
  have htwo := sum_inv_sq_le_two_of_pos (P := Finset.Icc 1 L)
    (fun n hn => (Finset.mem_Icc.1 hn).1)
  rw [hcast] at hstep
  linarith

/-- The `n`-weighted mass of the twisted coefficients costs one logarithm. -/
theorem sum_mul_norm_sq_twistedTruncCoeff_le (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 ≤ σ)
    (L : ℕ) :
    ∑ m : Fin L, (((m : ℕ) : ℝ) + 1) * ‖twistedTruncCoeff f σ L m‖ ^ 2 ≤ 1 + Real.log L := by
  have hstep : ∑ m : Fin L, (((m : ℕ) : ℝ) + 1) * ‖twistedTruncCoeff f σ L m‖ ^ 2
      ≤ ∑ m : Fin L, 1 / (((m : ℕ) : ℝ) + 1) := by
    refine Finset.sum_le_sum fun m _ => ?_
    have hb : (1 : ℝ) ≤ ((m : ℕ) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have h := norm_sq_twistedTruncCoeff_le hbdd hσ L m
    calc (((m : ℕ) : ℝ) + 1) * ‖twistedTruncCoeff f σ L m‖ ^ 2
        ≤ (((m : ℕ) : ℝ) + 1) * (1 / (((m : ℕ) : ℝ) + 1) ^ 2) :=
          mul_le_mul_of_nonneg_left h (by linarith)
      _ = 1 / (((m : ℕ) : ℝ) + 1) := by
          field_simp
  have hcast : ∑ m : Fin L, 1 / (((m : ℕ) : ℝ) + 1) = ∑ k ∈ Finset.Icc 1 L, 1 / (k : ℝ) := by
    rw [← sum_fin_eq_sum_Icc L (fun k => 1 / (k : ℝ))]
    refine Finset.sum_congr rfl fun m _ => ?_
    push_cast
    ring
  have hlog : ∑ k ∈ Finset.Icc 1 L, 1 / (k : ℝ) ≤ 1 + Real.log L :=
    sum_inv_comp_le_one_add_log (φ := id) (fun _ _ _ _ h => h) (fun a ha => ha)
  rw [hcast] at hstep
  linarith

/-- **The Halász mean-value bound for the truncated twisted series, with the affine mean square.**
The `L(1 + log L)` of `integral_norm_dirPoly_twisted_halasz` becomes `1 + log L`: the mass of the
twisted coefficients is `n`-weighted, and `∑_n n·n^{-2σ} ≍ log L` where `∑_n n^{-2σ} ≍ 1`. -/
theorem integral_norm_dirPoly_twisted_halasz_affine
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) (hf0 : f 0 = 0)
    {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz : 1 ≤ z) {δ : ℝ} (hδ : 0 ≤ δ)
    {L : ℕ} (hL : 1 ≤ L) {T V : ℝ} (hT : 1 ≤ T) (hV : 0 < V)
    (hunif : ∀ t : ℝ, |t| ≤ T →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z))) :
    ∫ u in Set.Ioc (0 : ℝ) T, ‖dirPoly L (twistedTruncCoeff f σ L) u‖
      ≤ V * T
        + ((1 + 1 / (σ - 1)) *
              Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2)
            + ((L : ℝ)) ^ (1 - σ) / (σ - 1))
          * (5 * Real.pi * Real.exp 1 * (1 + Real.log L) + 5 * Real.pi * T) / V ^ 2 := by
  set damped : ℝ := (1 + 1 / (σ - 1)) *
    Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) with hdamped
  set trunc : ℝ := ((L : ℝ)) ^ (1 - σ) / (σ - 1) with htrunc
  have hσ1 : (0 : ℝ) < σ - 1 := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hdamped0 : 0 ≤ damped := by
    rw [hdamped]
    positivity
  have htrunc0 : 0 ≤ trunc := by
    rw [htrunc]
    have hL0 : (0 : ℝ) ≤ ((L : ℕ) : ℝ) := Nat.cast_nonneg L
    positivity
  have hsup : ∀ u ∈ Set.Ioc (0 : ℝ) T,
      ‖dirPoly L (twistedTruncCoeff f σ L) u‖ ≤ damped + trunc := by
    intro u hu
    have hid : ∑ n ∈ Finset.range (L + 1),
        twistedSummand f (((σ : ℝ) : ℂ) + (((-u : ℝ)) : ℂ) * Complex.I) n
        = dirPoly L (twistedTruncCoeff f σ L) u := by
      rw [sum_range_twistedSummand_eq_dirPoly hf0 σ (-u) L, neg_neg]
    have hsre : (1 : ℝ) < (((σ : ℝ) : ℂ) + (((-u : ℝ)) : ℂ) * Complex.I).re := by
      rw [re_ofReal_add_mul_I]
      exact hσ
    have habs : |(-u : ℝ)| ≤ T := by
      rw [abs_neg, abs_of_pos hu.1]
      exact hu.2
    have hfull : ‖∑' n : ℕ,
        twistedSummand f (((σ : ℝ) : ℂ) + (((-u : ℝ)) : ℂ) * Complex.I) n‖ ≤ damped :=
      norm_tsum_twistedSummand_le_damped_of_uniform hf1 hmul hbdd hσ hz hδ hunif habs
    have htail : ‖(∑' n : ℕ,
          twistedSummand f (((σ : ℝ) : ℂ) + (((-u : ℝ)) : ℂ) * Complex.I) n) -
        ∑ n ∈ Finset.range (L + 1),
          twistedSummand f (((σ : ℝ) : ℂ) + (((-u : ℝ)) : ℂ) * Complex.I) n‖ ≤ trunc := by
      have h := norm_tsum_sub_sum_range_le_pow hbdd hsre hL
      rwa [re_ofReal_add_mul_I] at h
    rw [← hid]
    have hsplit := norm_sub_le
      (∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + (((-u : ℝ)) : ℂ) * Complex.I) n)
      ((∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + (((-u : ℝ)) : ℂ) * Complex.I) n) -
        ∑ n ∈ Finset.range (L + 1),
          twistedSummand f (((σ : ℝ) : ℂ) + (((-u : ℝ)) : ℂ) * Complex.I) n)
    rw [sub_sub_cancel] at hsplit
    linarith
  have hbase := integral_norm_dirPoly_halasz_affine L (twistedTruncCoeff f σ L) hT hV
    (by linarith : (0 : ℝ) ≤ damped + trunc) hsup
  have hmass1 := sum_mul_norm_sq_twistedTruncCoeff_le hbdd hσ.le L
  have hmass2 := sum_norm_sq_twistedTruncCoeff_le_two hbdd hσ.le L
  have hV2 : (0 : ℝ) < V ^ 2 := by positivity
  have hnum : 5 * Real.pi * Real.exp 1
        * (∑ m : Fin L, (((m : ℕ) : ℝ) + 1) * ‖twistedTruncCoeff f σ L m‖ ^ 2)
      + (5 * Real.pi / 2) * (∑ m : Fin L, ‖twistedTruncCoeff f σ L m‖ ^ 2) * T
      ≤ 5 * Real.pi * Real.exp 1 * (1 + Real.log L) + 5 * Real.pi * T := by
    have h1 : 5 * Real.pi * Real.exp 1
          * (∑ m : Fin L, (((m : ℕ) : ℝ) + 1) * ‖twistedTruncCoeff f σ L m‖ ^ 2)
        ≤ 5 * Real.pi * Real.exp 1 * (1 + Real.log L) :=
      mul_le_mul_of_nonneg_left hmass1 (by positivity)
    have h2 : (5 * Real.pi / 2) * (∑ m : Fin L, ‖twistedTruncCoeff f σ L m‖ ^ 2) * T
        ≤ (5 * Real.pi / 2) * 2 * T := by
      have hstep : (5 * Real.pi / 2) * (∑ m : Fin L, ‖twistedTruncCoeff f σ L m‖ ^ 2)
          ≤ (5 * Real.pi / 2) * 2 := mul_le_mul_of_nonneg_left hmass2 (by positivity)
      exact mul_le_mul_of_nonneg_right hstep hT0.le
    have hval : (5 * Real.pi / 2) * 2 * T = 5 * Real.pi * T := by ring
    linarith
  have hfrac : (damped + trunc)
        * (5 * Real.pi * Real.exp 1
            * (∑ m : Fin L, (((m : ℕ) : ℝ) + 1) * ‖twistedTruncCoeff f σ L m‖ ^ 2)
          + (5 * Real.pi / 2) * (∑ m : Fin L, ‖twistedTruncCoeff f σ L m‖ ^ 2) * T) / V ^ 2
      ≤ (damped + trunc) * (5 * Real.pi * Real.exp 1 * (1 + Real.log L) + 5 * Real.pi * T)
          / V ^ 2 := by
    refine div_le_div_of_nonneg_right ?_ hV2.le
    exact mul_le_mul_of_nonneg_left hnum (by linarith)
  linarith [hbase, hfrac]

end

end RHTower.Sieve
end
