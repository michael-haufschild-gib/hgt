import GaloisForLFunctions.HTGeometry.EntireCoeffsPartialSumSource
import GaloisForLFunctions.HTGeometry.GapSeriesEntireCarrier
import GaloisForLFunctions.HTGeometry.GaussianEntireCarrier

/-!
# The Gaussian series splits into its polynomial head and a tail of the shifted coordinates

Beyond any index the Gaussian series is again an entire coefficient series whose coefficients depend
only on the shifted coordinates, and the polynomial-growth event is a tail event.  This is the
decomposition the finite-jet law needs.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The coefficients of the Gaussian series beyond index `N`, as a function of the shifted
coordinates. -/
def gaussianTailCoeff (N : ℕ) (y : ℕ → ℂ) (m : ℕ) : ℂ :=
  if m < N then 0 else y (m - N) / ((Real.sqrt ((Nat.factorial m : ℕ) : ℝ) : ℝ) : ℂ)

/-- The polynomial-growth event read on the shifted coordinates. -/
def GoodGaussianTail (N : ℕ) (y : ℕ → ℂ) : Prop :=
  ∀ᶠ k : ℕ in atTop, ‖y k‖ < (k : ℝ) + (N : ℝ)

theorem measurableSet_goodGaussianTail (N : ℕ) :
    MeasurableSet {y : ℕ → ℂ | GoodGaussianTail N y} := by
  have hset : {y : ℕ → ℂ | GoodGaussianTail N y}
      = ⋃ K : ℕ, ⋂ k : {m : ℕ // K ≤ m},
        {y : ℕ → ℂ | ‖y (k : ℕ)‖ < ((k : ℕ) : ℝ) + (N : ℝ)} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, GoodGaussianTail,
      eventually_atTop]
    constructor
    · rintro ⟨K, hK⟩
      exact ⟨K, fun k => hK (k : ℕ) k.2⟩
    · rintro ⟨K, hK⟩
      exact ⟨K, fun k hk => hK ⟨k, hk⟩⟩
  rw [hset]
  refine MeasurableSet.iUnion fun K => MeasurableSet.iInter fun k => ?_
  exact measurableSet_lt ((measurable_pi_apply (X := fun _ : ℕ => ℂ) (k : ℕ)).norm)
    measurable_const

theorem goodGaussianCoefficients_iff (N : ℕ) (x : ℕ → ℂ) :
    GoodGaussianCoefficients x ↔ GoodGaussianTail N (fun k => x (k + N)) := by
  constructor
  · intro hx
    have h := (tendsto_add_atTop_nat N).eventually hx
    filter_upwards [h] with k hk
    push_cast at hk
    exact hk
  · intro hy
    rw [GoodGaussianTail, eventually_atTop] at hy
    obtain ⟨K, hK⟩ := hy
    rw [GoodGaussianCoefficients, eventually_atTop]
    refine ⟨K + N, fun n hn => ?_⟩
    have hval := hK (n - N) (by omega)
    rw [show n - N + N = n by omega] at hval
    have hcast : ((n - N : ℕ) : ℝ) = (n : ℝ) - (N : ℝ) := by
      have : N ≤ n := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [hcast] at hval
    linarith

theorem entireCoeffs_gaussianTailCoeff {N : ℕ} {y : ℕ → ℂ} (hy : GoodGaussianTail N y) :
    EntireCoeffs (gaussianTailCoeff N y) := by
  refine entireCoeffs_of_eventually_norm_le_index ?_
  have h := (tendsto_sub_atTop_nat N).eventually hy
  filter_upwards [h, eventually_ge_atTop N] with m hm hmN
  have hfac : (0 : ℝ) < Real.sqrt ((Nat.factorial m : ℕ) : ℝ) := by
    refine Real.sqrt_pos.2 ?_
    exact_mod_cast Nat.factorial_pos m
  rw [gaussianTailCoeff, if_neg (by omega), norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hcast : ((m - N : ℕ) : ℝ) = (m : ℝ) - (N : ℝ) := by
    push_cast [Nat.cast_sub hmN]
    ring
  rw [hcast] at hm
  gcongr
  linarith

open Classical in
/-- The tail source of the Gaussian series beyond index `N`. -/
def gaussianTailSource (N : ℕ) (y : ℕ → ℂ) : MultivariateEntire 1 :=
  if h : GoodGaussianTail N y then coeffFunSource (entireCoeffs_gaussianTailCoeff h) else 0

/-- **The coefficient split.** -/
theorem coeffFun_gafCoeff_split {x : ℕ → ℂ} (hx : GoodGaussianCoefficients x) (N : ℕ) (z : ℂ) :
    coeffFun (gafCoeff x) z
      = (∑ n ∈ Finset.range N, gafCoeff x n * z ^ n)
        + coeffFun (gaussianTailCoeff N (fun k => x (k + N))) z := by
  classical
  have hEC := entireCoeffs_gafCoeff hx
  have hECt : EntireCoeffs (gaussianTailCoeff N (fun k => x (k + N))) :=
    entireCoeffs_gaussianTailCoeff ((goodGaussianCoefficients_iff N x).1 hx)
  have hsum := summable_coeffFun_term hEC z
  have hsumt := summable_coeffFun_term hECt z
  have hagree : ∀ k : ℕ, gaussianTailCoeff N (fun j => x (j + N)) (k + N) = gafCoeff x (k + N) := by
    intro k
    rw [gaussianTailCoeff, if_neg (by omega), gafCoeff]
    congr 2
    omega
  have hzeroHead : ∀ m : ℕ, m < N → gaussianTailCoeff N (fun j => x (j + N)) m = 0 := by
    intro m hm
    rw [gaussianTailCoeff, if_pos hm]
  rw [coeffFun_eq_tsum, coeffFun_eq_tsum, ← hsum.sum_add_tsum_nat_add N,
    ← hsumt.sum_add_tsum_nat_add N]
  have hhead : ∑ m ∈ Finset.range N,
      gaussianTailCoeff N (fun j => x (j + N)) m * z ^ m = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [hzeroHead m (Finset.mem_range.1 hm), zero_mul]
  have htail : ∑' k : ℕ, gaussianTailCoeff N (fun j => x (j + N)) (k + N) * z ^ (k + N)
      = ∑' k : ℕ, gafCoeff x (k + N) * z ^ (k + N) :=
    tsum_congr fun k => by rw [hagree k]
  rw [hhead, htail, zero_add]

end

end GaloisForLFunctions.HTGeometry
