import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimeScreenJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullDerivativeExponentialMoments
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimeWeightedConvergence

/-!
# All-jet weighted convergence of finite-prime theta screens

Every actual derivative of each selected even screen converges to the corresponding completed
theta-source derivative in every exponentially weighted `L¹` norm.
-/

open Filter Topology Set MeasureTheory

noncomputable section

namespace RHTower

/-- Fixed global bound for one derivative of the smooth transition cutoff. -/
noncomputable def thetaCuspScreenCutoffDerivativeBound (r : ℕ) : ℝ :=
  Classical.choose (exists_bound_iteratedDeriv_ccmSmoothHalflineCutoff r)

theorem thetaCuspScreenCutoffDerivativeBound_nonneg (r : ℕ) :
    0 ≤ thetaCuspScreenCutoffDerivativeBound r :=
  (Classical.choose_spec
    (exists_bound_iteratedDeriv_ccmSmoothHalflineCutoff r)).1

theorem abs_iteratedDeriv_finitePrimeThetaCuspScreenCutoff_le
    (r j : ℕ) (x : ℝ) :
    |iteratedDeriv r (finitePrimeThetaCuspScreenCutoff j) x| ≤
      thetaCuspScreenCutoffDerivativeBound r := by
  have hshift := congrFun
    (iteratedDeriv_comp_add_const r ccmSmoothHalflineCutoff (j : ℝ)) x
  have hbound := (Classical.choose_spec
    (exists_bound_iteratedDeriv_ccmSmoothHalflineCutoff r)).2 (x + j)
  simpa only [finitePrimeThetaCuspScreenCutoff] using hshift ▸ hbound

/-- Nonnegative Leibniz coefficient carrying the cutoff-derivative bound. -/
def thetaCuspScreenJetCoefficient (m r : ℕ) : ℝ :=
  (m.choose r : ℝ) * thetaCuspScreenCutoffDerivativeBound r

theorem thetaCuspScreenJetCoefficient_nonneg (m r : ℕ) :
    0 ≤ thetaCuspScreenJetCoefficient m r :=
  mul_nonneg (Nat.cast_nonneg _) (thetaCuspScreenCutoffDerivativeBound_nonneg r)

theorem iteratedDeriv_finitePrimeThetaCuspEvenScreen_neg
    (m j : ℕ) (x : ℝ) :
    iteratedDeriv m (finitePrimeThetaCuspEvenScreen j) (-x) =
      (-1 : ℝ) ^ m * iteratedDeriv m (finitePrimeThetaCuspEvenScreen j) x := by
  have hfun : (fun y : ℝ ↦ finitePrimeThetaCuspEvenScreen j (-y)) =
      finitePrimeThetaCuspEvenScreen j := by
    funext y
    exact finitePrimeThetaCuspEvenScreen_neg j y
  have hder := congrArg (iteratedDeriv m) hfun
  have hx := congrFun hder (-x)
  rw [iteratedDeriv_comp_neg] at hx
  simpa [smul_eq_mul] using hx.symm

theorem abs_iteratedDeriv_finitePrimeThetaCuspEvenScreen_neg
    (m j : ℕ) (x : ℝ) :
    |iteratedDeriv m (finitePrimeThetaCuspEvenScreen j) (-x)| =
      |iteratedDeriv m (finitePrimeThetaCuspEvenScreen j) x| := by
  rw [iteratedDeriv_finitePrimeThetaCuspEvenScreen_neg, abs_mul, abs_pow]
  simp

/-- On the positive ray, the reflected one-sided jet is controlled by finitely many completed
source jets plus the diagonal Gaussian accuracy error. -/
theorem abs_iteratedDeriv_finitePrimeThetaCuspRightScreen_neg_le
    (m j : ℕ) {x : ℝ} (hx : 0 < x) (hm : m ≤ j) :
    |iteratedDeriv m (finitePrimeThetaCuspRightScreen j) (-x)| ≤
      ∑ r ∈ Finset.range (m + 1), thetaCuspScreenJetCoefficient m r *
        (|iteratedDeriv (m - r) thetaCuspFullSource x| +
          Real.exp (-((j : ℝ) ^ (2 : ℕ)))) := by
  let N := finitePrimeThetaCuspPositiveScreenIndex j
  by_cases hxj : ((j + 1 : ℕ) : ℝ) < x
  · have hlocal : finitePrimeThetaCuspRightScreen j =ᶠ[𝓝 (-x)]
        (fun _ : ℝ ↦ 0) := by
      have hneg : -x < -((j + 1 : ℕ) : ℝ) := by linarith
      filter_upwards [Iio_mem_nhds hneg] with y hy
      rw [finitePrimeThetaCuspRightScreen,
        finitePrimeThetaCuspScreenCutoff_eq_zero j hy.le, zero_mul]
    have hzero : |iteratedDeriv m (fun _ : ℝ ↦ (0 : ℝ)) (-x)| = (0 : ℝ) := by simp
    rw [hlocal.iteratedDeriv_eq m, hzero]
    exact Finset.sum_nonneg fun r _ ↦
      mul_nonneg (thetaCuspScreenJetCoefficient_nonneg m r)
        (add_nonneg (abs_nonneg _) (Real.exp_pos _).le)
  · have hxj' : x ≤ ((j + 1 : ℕ) : ℝ) := le_of_not_gt hxj
    rw [congrFun (iteratedDeriv_finitePrimeThetaCuspRightScreen m j) (-x)]
    unfold finitePrimeThetaCuspRightScreenDerivative
    calc
      |∑ r ∈ Finset.range (m + 1),
          (m.choose r : ℝ) *
            iteratedDeriv r (finitePrimeThetaCuspScreenCutoff j) (-x) *
            finitePrimeThetaCuspDerivative (m - r) N (-x)| ≤
        ∑ r ∈ Finset.range (m + 1),
          |(m.choose r : ℝ) *
            iteratedDeriv r (finitePrimeThetaCuspScreenCutoff j) (-x) *
            finitePrimeThetaCuspDerivative (m - r) N (-x)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ Finset.range (m + 1), thetaCuspScreenJetCoefficient m r *
          (|iteratedDeriv (m - r) thetaCuspFullSource x| +
            Real.exp (-((j : ℝ) ^ (2 : ℕ)))) := by
        apply Finset.sum_le_sum
        intro r hr
        have hrm : r ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
        have horder : m - r ≤ j := (Nat.sub_le m r).trans hm
        have hmem : -x ∈ Icc (-((j + 1 : ℕ) : ℝ)) ((j + 1 : ℕ) : ℝ) := by
          constructor <;> linarith
        have hacc := finitePrimeThetaCuspPositiveScreenIndex_accuracy j
          (m - r) horder (-x) hmem
        rw [congrFun (iteratedDeriv_finitePrimeThetaCuspSource (m - r) N) (-x)] at hacc
        have hfinite : |finitePrimeThetaCuspDerivative (m - r) N (-x)| <
            |iteratedDeriv (m - r) thetaCuspFullSource x| +
              Real.exp (-((j : ℝ) ^ (2 : ℕ))) := by
          have htri : |finitePrimeThetaCuspDerivative (m - r) N (-x)| ≤
              |finitePrimeThetaCuspDerivative (m - r) N (-x) -
                iteratedDeriv (m - r) thetaCuspFullSource (-x)| +
              |iteratedDeriv (m - r) thetaCuspFullSource (-x)| := by
            calc
              |finitePrimeThetaCuspDerivative (m - r) N (-x)| =
                  |(finitePrimeThetaCuspDerivative (m - r) N (-x) -
                    iteratedDeriv (m - r) thetaCuspFullSource (-x)) +
                    iteratedDeriv (m - r) thetaCuspFullSource (-x)| := by ring
              _ ≤ _ := abs_add_le _ _
          rw [abs_iteratedDeriv_thetaCuspFullSource_neg] at htri
          linarith
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (m.choose r))]
        calc
          (m.choose r : ℝ) *
              |iteratedDeriv r (finitePrimeThetaCuspScreenCutoff j) (-x)| *
              |finitePrimeThetaCuspDerivative (m - r) N (-x)| ≤
            (m.choose r : ℝ) * thetaCuspScreenCutoffDerivativeBound r *
              |finitePrimeThetaCuspDerivative (m - r) N (-x)| := by
            gcongr
            exact abs_iteratedDeriv_finitePrimeThetaCuspScreenCutoff_le r j (-x)
          _ ≤ (m.choose r : ℝ) * thetaCuspScreenCutoffDerivativeBound r *
              (|iteratedDeriv (m - r) thetaCuspFullSource x| +
                Real.exp (-((j : ℝ) ^ (2 : ℕ)))) := by
            exact mul_le_mul_of_nonneg_left hfinite.le
              (mul_nonneg (Nat.cast_nonneg _)
                (thetaCuspScreenCutoffDerivativeBound_nonneg r))
          _ = thetaCuspScreenJetCoefficient m r *
              (|iteratedDeriv (m - r) thetaCuspFullSource x| +
                Real.exp (-((j : ℝ) ^ (2 : ℕ)))) := rfl

/-- Exponentially weighted pointwise error of the actual `m`-th screen derivative. -/
def finitePrimeThetaCuspWeightedScreenJetError
    (m : ℕ) (A : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  Real.exp (A * |x|) *
    |iteratedDeriv m (finitePrimeThetaCuspEvenScreen j) x -
      iteratedDeriv m thetaCuspFullSource x|

/-- Integrable majorant, independent of screen index, for one weighted derivative error. -/
def finitePrimeThetaCuspWeightedScreenJetMajor
    (m : ℕ) (A : ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  finitePrimeThetaCuspWeightedDerivativeConstant m q *
      Real.exp (-(((q + 1 : ℕ) : ℝ) - |A|) * |x|) +
    Real.exp (|A| * |x|) * |iteratedDeriv m thetaCuspFullSource x| +
    ∑ r ∈ Finset.range (m + 1), thetaCuspScreenJetCoefficient m r *
      (Real.exp (|A| * |x|) *
          |iteratedDeriv (m - r) thetaCuspFullSource x| +
        Real.exp (|A| ^ (2 : ℕ) + 1) * Real.exp (-(1 / 4 : ℝ) * x ^ (2 : ℕ)))

theorem integrable_finitePrimeThetaCuspWeightedScreenJetMajor
    (m : ℕ) (A : ℝ) (q : ℕ) (hA : |A| < (q + 1 : ℕ)) :
    Integrable (finitePrimeThetaCuspWeightedScreenJetMajor m A q) := by
  have hc : 0 < ((q + 1 : ℕ) : ℝ) - |A| := sub_pos.mpr hA
  have htail : Integrable (fun x : ℝ ↦
      finitePrimeThetaCuspWeightedDerivativeConstant m q *
        Real.exp (-(((q + 1 : ℕ) : ℝ) - |A|) * |x|)) := by
    have h := (HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hc).const_mul
      (finitePrimeThetaCuspWeightedDerivativeConstant m q)
    simpa only [pow_zero, one_mul] using h
  have htarget := integrable_exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource m |A|
  have hgauss : Integrable (fun x : ℝ ↦
      Real.exp (|A| ^ (2 : ℕ) + 1) * Real.exp (-(1 / 4 : ℝ) * x ^ (2 : ℕ))) := by
    simpa only [pow_zero, one_mul] using
      (integrable_abs_pow_mul_exp_neg_mul_sq
        (by norm_num : (0 : ℝ) < 1 / 4) 0).const_mul (Real.exp (|A| ^ (2 : ℕ) + 1))
  have hsum : Integrable (fun x : ℝ ↦
      ∑ r ∈ Finset.range (m + 1), thetaCuspScreenJetCoefficient m r *
        (Real.exp (|A| * |x|) *
            |iteratedDeriv (m - r) thetaCuspFullSource x| +
          Real.exp (|A| ^ (2 : ℕ) + 1) * Real.exp (-(1 / 4 : ℝ) * x ^ (2 : ℕ)))) := by
    let term : ℕ → ℝ → ℝ := fun r x ↦ thetaCuspScreenJetCoefficient m r *
      (Real.exp (|A| * |x|) *
          |iteratedDeriv (m - r) thetaCuspFullSource x| +
        Real.exp (|A| ^ (2 : ℕ) + 1) * Real.exp (-(1 / 4 : ℝ) * x ^ (2 : ℕ)))
    have hterm (r : ℕ) : Integrable (term r) :=
      ((integrable_exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource
        (m - r) |A|).add hgauss).const_mul _
    have hall : ∀ s : Finset ℕ, Integrable (fun x : ℝ ↦ ∑ r ∈ s, term r x) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert r s hrs ih =>
          refine ((hterm r).add ih).congr ?_
          filter_upwards with x
          rw [Finset.sum_insert hrs]
          rfl
    simpa only [term] using hall (Finset.range (m + 1))
  change Integrable (fun x : ℝ ↦
    finitePrimeThetaCuspWeightedDerivativeConstant m q *
        Real.exp (-(((q + 1 : ℕ) : ℝ) - |A|) * |x|) +
      Real.exp (|A| * |x|) * |iteratedDeriv m thetaCuspFullSource x| +
      ∑ r ∈ Finset.range (m + 1), thetaCuspScreenJetCoefficient m r *
        (Real.exp (|A| * |x|) *
            |iteratedDeriv (m - r) thetaCuspFullSource x| +
          Real.exp (|A| ^ (2 : ℕ) + 1) * Real.exp (-(1 / 4 : ℝ) * x ^ (2 : ℕ))))
  exact (htail.add htarget).add hsum

theorem finitePrimeThetaCuspWeightedScreenJetError_le_major_of_pos
    (m : ℕ) (A : ℝ) (q j : ℕ) {x : ℝ} (hx : 0 < x) (hm : m ≤ j) :
    finitePrimeThetaCuspWeightedScreenJetError m A j x ≤
      finitePrimeThetaCuspWeightedScreenJetMajor m A q x := by
  let N := finitePrimeThetaCuspPositiveScreenIndex j
  let B := |A|
  let C := finitePrimeThetaCuspWeightedDerivativeConstant m q
  let c := ((q + 1 : ℕ) : ℝ) - B
  have hx0 : 0 ≤ x := hx.le
  have hweight : Real.exp (A * x) ≤ Real.exp (B * x) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self A) hx0)
  have hlocal : finitePrimeThetaCuspRightScreen j =ᶠ[𝓝 x]
      finitePrimeThetaCuspSource N := by
    have hnegj : -((j : ℕ) : ℝ) < x := by
      have hj : (0 : ℝ) ≤ (j : ℕ) := by positivity
      linarith
    filter_upwards [Ioi_mem_nhds hnegj] with y hy
    rw [finitePrimeThetaCuspRightScreen,
      finitePrimeThetaCuspScreenCutoff_eq_one j hy.le, one_mul]
  have hrightEq : iteratedDeriv m (finitePrimeThetaCuspRightScreen j) x =
      finitePrimeThetaCuspDerivative m N x := by
    rw [hlocal.iteratedDeriv_eq m,
      congrFun (iteratedDeriv_finitePrimeThetaCuspSource m N) x]
  have hright : Real.exp (B * x) *
      |iteratedDeriv m (finitePrimeThetaCuspRightScreen j) x| ≤
      C * Real.exp (-(c * x)) := by
    rw [hrightEq]
    simpa only [C, c, neg_mul] using
      exp_mul_abs_finitePrimeThetaCuspDerivative_le m q N B hx0
  have hrefRaw := abs_iteratedDeriv_finitePrimeThetaCuspRightScreen_neg_le m j hx hm
  have href : Real.exp (B * x) *
      |iteratedDeriv m (finitePrimeThetaCuspRightScreen j) (-x)| ≤
      ∑ r ∈ Finset.range (m + 1), thetaCuspScreenJetCoefficient m r *
        (Real.exp (B * x) * |iteratedDeriv (m - r) thetaCuspFullSource x| +
          Real.exp (B ^ (2 : ℕ) + 1) * Real.exp (-(1 / 4 : ℝ) * x ^ (2 : ℕ))) := by
    by_cases hxj : x ≤ ((j + 1 : ℕ) : ℝ)
    · calc
        Real.exp (B * x) *
            |iteratedDeriv m (finitePrimeThetaCuspRightScreen j) (-x)| ≤
          Real.exp (B * x) *
            (∑ r ∈ Finset.range (m + 1), thetaCuspScreenJetCoefficient m r *
              (|iteratedDeriv (m - r) thetaCuspFullSource x| +
                Real.exp (-((j : ℝ) ^ (2 : ℕ))))) :=
          mul_le_mul_of_nonneg_left hrefRaw (Real.exp_pos _).le
        _ = ∑ r ∈ Finset.range (m + 1), Real.exp (B * x) *
            (thetaCuspScreenJetCoefficient m r *
              (|iteratedDeriv (m - r) thetaCuspFullSource x| +
                Real.exp (-((j : ℝ) ^ (2 : ℕ))))) := by rw [Finset.mul_sum]
        _ ≤ ∑ r ∈ Finset.range (m + 1), thetaCuspScreenJetCoefficient m r *
            (Real.exp (B * x) * |iteratedDeriv (m - r) thetaCuspFullSource x| +
              Real.exp (B ^ (2 : ℕ) + 1) * Real.exp (-(1 / 4 : ℝ) * x ^ (2 : ℕ))) := by
          apply Finset.sum_le_sum
          intro r hr
          have hgauss := exp_screenAccuracy_le_gaussianMajor A j hx0 hxj
          calc
            Real.exp (B * x) *
                (thetaCuspScreenJetCoefficient m r *
                  (|iteratedDeriv (m - r) thetaCuspFullSource x| +
                    Real.exp (-((j : ℝ) ^ (2 : ℕ))))) =
              thetaCuspScreenJetCoefficient m r *
                (Real.exp (B * x) * |iteratedDeriv (m - r) thetaCuspFullSource x| +
                  Real.exp (B * x) * Real.exp (-((j : ℝ) ^ (2 : ℕ)))) := by ring
            _ ≤ thetaCuspScreenJetCoefficient m r *
                (Real.exp (B * x) * |iteratedDeriv (m - r) thetaCuspFullSource x| +
                  Real.exp (B ^ (2 : ℕ) + 1) * Real.exp (-(1 / 4 : ℝ) * x ^ (2 : ℕ))) := by
              exact mul_le_mul_of_nonneg_left (add_le_add_right hgauss _)
                (thetaCuspScreenJetCoefficient_nonneg m r)
    · have hfar : ((j + 1 : ℕ) : ℝ) < x := lt_of_not_ge hxj
      have hlocalZero : finitePrimeThetaCuspRightScreen j =ᶠ[𝓝 (-x)]
          (fun _ : ℝ ↦ 0) := by
        have hneg : -x < -((j + 1 : ℕ) : ℝ) := by linarith
        filter_upwards [Iio_mem_nhds hneg] with y hy
        rw [finitePrimeThetaCuspRightScreen,
          finitePrimeThetaCuspScreenCutoff_eq_zero j hy.le, zero_mul]
      have hzero : |iteratedDeriv m
          (finitePrimeThetaCuspRightScreen j) (-x)| = 0 := by
        rw [hlocalZero.iteratedDeriv_eq m]
        simp
      rw [hzero, mul_zero]
      exact Finset.sum_nonneg fun r _ ↦
        mul_nonneg (thetaCuspScreenJetCoefficient_nonneg m r)
          (add_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
            (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
  have hscreen : |iteratedDeriv m (finitePrimeThetaCuspEvenScreen j) x| ≤
      |iteratedDeriv m (finitePrimeThetaCuspRightScreen j) x| +
        |iteratedDeriv m (finitePrimeThetaCuspRightScreen j) (-x)| := by
    rw [congrFun (iteratedDeriv_finitePrimeThetaCuspEvenScreen m j) x]
    unfold finitePrimeThetaCuspEvenScreenDerivative
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      |finitePrimeThetaCuspRightScreenDerivative m j x +
          (-1 : ℝ) ^ m * finitePrimeThetaCuspRightScreenDerivative m j (-x)| / 2 ≤
        (|finitePrimeThetaCuspRightScreenDerivative m j x| +
          |(-1 : ℝ) ^ m * finitePrimeThetaCuspRightScreenDerivative m j (-x)|) / 2 := by
        gcongr
        exact abs_add_le _ _
      _ ≤ |finitePrimeThetaCuspRightScreenDerivative m j x| +
          |finitePrimeThetaCuspRightScreenDerivative m j (-x)| := by
        rw [abs_mul, abs_pow]
        simp only [abs_neg, abs_one, one_pow, one_mul]
        have h1 := abs_nonneg (finitePrimeThetaCuspRightScreenDerivative m j x)
        have h2 := abs_nonneg (finitePrimeThetaCuspRightScreenDerivative m j (-x))
        linarith
      _ = |iteratedDeriv m (finitePrimeThetaCuspRightScreen j) x| +
          |iteratedDeriv m (finitePrimeThetaCuspRightScreen j) (-x)| := by
        rw [congrFun (iteratedDeriv_finitePrimeThetaCuspRightScreen m j) x,
          congrFun (iteratedDeriv_finitePrimeThetaCuspRightScreen m j) (-x)]
  have herr : |iteratedDeriv m (finitePrimeThetaCuspEvenScreen j) x -
      iteratedDeriv m thetaCuspFullSource x| ≤
      |iteratedDeriv m (finitePrimeThetaCuspRightScreen j) x| +
        |iteratedDeriv m (finitePrimeThetaCuspRightScreen j) (-x)| +
        |iteratedDeriv m thetaCuspFullSource x| := by
    calc
      |iteratedDeriv m (finitePrimeThetaCuspEvenScreen j) x -
          iteratedDeriv m thetaCuspFullSource x| ≤
        |iteratedDeriv m (finitePrimeThetaCuspEvenScreen j) x| +
          |iteratedDeriv m thetaCuspFullSource x| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (iteratedDeriv m (finitePrimeThetaCuspEvenScreen j) x)
            (-iteratedDeriv m thetaCuspFullSource x)
      _ ≤ _ := by linarith
  rw [finitePrimeThetaCuspWeightedScreenJetError, abs_of_pos hx]
  calc
    Real.exp (A * x) *
        |iteratedDeriv m (finitePrimeThetaCuspEvenScreen j) x -
          iteratedDeriv m thetaCuspFullSource x| ≤
      Real.exp (B * x) *
        |iteratedDeriv m (finitePrimeThetaCuspEvenScreen j) x -
          iteratedDeriv m thetaCuspFullSource x| :=
      mul_le_mul_of_nonneg_right hweight (abs_nonneg _)
    _ ≤ Real.exp (B * x) *
        (|iteratedDeriv m (finitePrimeThetaCuspRightScreen j) x| +
          |iteratedDeriv m (finitePrimeThetaCuspRightScreen j) (-x)| +
          |iteratedDeriv m thetaCuspFullSource x|) :=
      mul_le_mul_of_nonneg_left herr (Real.exp_pos _).le
    _ = Real.exp (B * x) *
          |iteratedDeriv m (finitePrimeThetaCuspRightScreen j) x| +
        Real.exp (B * x) *
          |iteratedDeriv m (finitePrimeThetaCuspRightScreen j) (-x)| +
        Real.exp (B * x) * |iteratedDeriv m thetaCuspFullSource x| := by ring
    _ ≤ C * Real.exp (-(c * x)) +
        (∑ r ∈ Finset.range (m + 1), thetaCuspScreenJetCoefficient m r *
          (Real.exp (B * x) * |iteratedDeriv (m - r) thetaCuspFullSource x| +
            Real.exp (B ^ (2 : ℕ) + 1) * Real.exp (-(1 / 4 : ℝ) * x ^ (2 : ℕ)))) +
        Real.exp (B * x) * |iteratedDeriv m thetaCuspFullSource x| := by
      gcongr
    _ = finitePrimeThetaCuspWeightedScreenJetMajor m A q x := by
      simp only [finitePrimeThetaCuspWeightedScreenJetMajor, abs_of_pos hx, B, C, c]
      simp only [mul_comm, add_comm, add_assoc, Nat.cast_add, Nat.cast_one, mul_neg]

theorem finitePrimeThetaCuspWeightedScreenJetError_neg
    (m : ℕ) (A : ℝ) (j : ℕ) (x : ℝ) :
    finitePrimeThetaCuspWeightedScreenJetError m A j (-x) =
      finitePrimeThetaCuspWeightedScreenJetError m A j x := by
  unfold finitePrimeThetaCuspWeightedScreenJetError
  rw [abs_neg, iteratedDeriv_finitePrimeThetaCuspEvenScreen_neg,
    iteratedDeriv_thetaCuspFullSource_neg]
  rw [← mul_sub, abs_mul, abs_pow]
  simp

theorem finitePrimeThetaCuspWeightedScreenJetMajor_neg
    (m : ℕ) (A : ℝ) (q : ℕ) (x : ℝ) :
    finitePrimeThetaCuspWeightedScreenJetMajor m A q (-x) =
      finitePrimeThetaCuspWeightedScreenJetMajor m A q x := by
  unfold finitePrimeThetaCuspWeightedScreenJetMajor
  simp only [abs_neg, neg_sq, abs_iteratedDeriv_thetaCuspFullSource_neg]

theorem finitePrimeThetaCuspWeightedScreenJetError_le_major_of_ne_zero
    (m : ℕ) (A : ℝ) (q j : ℕ) (hm : m ≤ j) {x : ℝ} (hx : x ≠ 0) :
    finitePrimeThetaCuspWeightedScreenJetError m A j x ≤
      finitePrimeThetaCuspWeightedScreenJetMajor m A q x := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have h := finitePrimeThetaCuspWeightedScreenJetError_le_major_of_pos
      m A q j (neg_pos.mpr hxneg) hm
    rwa [finitePrimeThetaCuspWeightedScreenJetError_neg,
      finitePrimeThetaCuspWeightedScreenJetMajor_neg] at h
  · exact finitePrimeThetaCuspWeightedScreenJetError_le_major_of_pos
      m A q j hxpos hm

/-- Quantitative central-window accuracy for every actual screen derivative. -/
theorem finitePrimeThetaCuspEvenScreenJet_sub_full_abs_lt_accuracy
    (m j : ℕ) (hm : m ≤ j) {x : ℝ} (hx : |x| < (j : ℝ)) :
    |iteratedDeriv m (finitePrimeThetaCuspEvenScreen j) x -
        iteratedDeriv m thetaCuspFullSource x| <
      Real.exp (-((j : ℝ) ^ (2 : ℕ))) := by
  let N := finitePrimeThetaCuspPositiveScreenIndex j
  let s : ℝ := (-1 : ℝ) ^ m
  have hmemx : x ∈ Icc (-((j + 1 : ℕ) : ℝ)) ((j + 1 : ℕ) : ℝ) := by
    constructor <;> push_cast <;> linarith [neg_abs_le x, le_abs_self x]
  have hmemneg : -x ∈ Icc (-((j + 1 : ℕ) : ℝ)) ((j + 1 : ℕ) : ℝ) := by
    constructor <;> push_cast <;> linarith [neg_abs_le x, le_abs_self x]
  have haccx := finitePrimeThetaCuspPositiveScreenIndex_accuracy j m hm x hmemx
  have haccneg := finitePrimeThetaCuspPositiveScreenIndex_accuracy j m hm (-x) hmemneg
  rw [congrFun (iteratedDeriv_finitePrimeThetaCuspSource m N) x] at haccx
  rw [congrFun (iteratedDeriv_finitePrimeThetaCuspSource m N) (-x)] at haccneg
  have hpar := iteratedDeriv_thetaCuspFullSource_neg m x
  have hsq : s * s = 1 := by
    rw [show s * s = s ^ (2 : ℕ) by ring]
    dsimp only [s]
    rw [← pow_mul]
    norm_num
  have hcentral := iteratedDeriv_finitePrimeThetaCuspEvenScreen_eq_source_average
    m j hx
  have hid : iteratedDeriv m (finitePrimeThetaCuspEvenScreen j) x -
      iteratedDeriv m thetaCuspFullSource x =
      ((finitePrimeThetaCuspDerivative m N x -
          iteratedDeriv m thetaCuspFullSource x) +
        s * (finitePrimeThetaCuspDerivative m N (-x) -
          iteratedDeriv m thetaCuspFullSource (-x))) / 2 := by
    change iteratedDeriv m (finitePrimeThetaCuspEvenScreen j) x =
      (finitePrimeThetaCuspDerivative m N x +
        s * finitePrimeThetaCuspDerivative m N (-x)) / 2 at hcentral
    change iteratedDeriv m thetaCuspFullSource (-x) =
      s * iteratedDeriv m thetaCuspFullSource x at hpar
    rw [hcentral, hpar]
    rw [mul_sub, ← mul_assoc, hsq, one_mul]
    ring
  rw [hid]
  calc
    |((finitePrimeThetaCuspDerivative m N x -
          iteratedDeriv m thetaCuspFullSource x) +
        s * (finitePrimeThetaCuspDerivative m N (-x) -
          iteratedDeriv m thetaCuspFullSource (-x))) / 2| ≤
      (|finitePrimeThetaCuspDerivative m N x -
          iteratedDeriv m thetaCuspFullSource x| +
        |finitePrimeThetaCuspDerivative m N (-x) -
          iteratedDeriv m thetaCuspFullSource (-x)|) / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have htri := abs_add_le
        (finitePrimeThetaCuspDerivative m N x -
          iteratedDeriv m thetaCuspFullSource x)
        (s * (finitePrimeThetaCuspDerivative m N (-x) -
          iteratedDeriv m thetaCuspFullSource (-x)))
      have hsabs : |s| = 1 := by simp [s]
      have htri' :
          |finitePrimeThetaCuspDerivative m N x -
              iteratedDeriv m thetaCuspFullSource x +
            s * (finitePrimeThetaCuspDerivative m N (-x) -
              iteratedDeriv m thetaCuspFullSource (-x))| ≤
            |finitePrimeThetaCuspDerivative m N x -
              iteratedDeriv m thetaCuspFullSource x| +
            |finitePrimeThetaCuspDerivative m N (-x) -
              iteratedDeriv m thetaCuspFullSource (-x)| := by
        calc
          _ ≤ |finitePrimeThetaCuspDerivative m N x -
                iteratedDeriv m thetaCuspFullSource x| +
              |s * (finitePrimeThetaCuspDerivative m N (-x) -
                iteratedDeriv m thetaCuspFullSource (-x))| := htri
          _ = _ := by rw [abs_mul, hsabs, one_mul]
      exact div_le_div_of_nonneg_right htri' (by norm_num)
    _ < Real.exp (-((j : ℝ) ^ (2 : ℕ))) := by linarith

theorem tendsto_finitePrimeThetaCuspWeightedScreenJetError_pointwise
    (m : ℕ) (A x : ℝ) :
    Tendsto (fun j : ℕ ↦ finitePrimeThetaCuspWeightedScreenJetError m A j x)
      atTop (𝓝 0) := by
  have hm : ∀ᶠ j : ℕ in atTop, m ≤ j := eventually_ge_atTop m
  have hxj : ∀ᶠ j : ℕ in atTop, |x| < (j : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)) (eventually_gt_atTop |x|)
  have hnonneg : ∀ j : ℕ, 0 ≤ finitePrimeThetaCuspWeightedScreenJetError m A j x :=
    fun j ↦ mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  have hupper : ∀ᶠ j : ℕ in atTop,
      finitePrimeThetaCuspWeightedScreenJetError m A j x ≤
        Real.exp (A * |x|) * Real.exp (-((j : ℝ) ^ (2 : ℕ))) := by
    filter_upwards [hm, hxj] with j hmj hxj'
    unfold finitePrimeThetaCuspWeightedScreenJetError
    exact mul_le_mul_of_nonneg_left
      (finitePrimeThetaCuspEvenScreenJet_sub_full_abs_lt_accuracy m j hmj hxj').le
      (Real.exp_pos _).le
  have henv : Tendsto
      (fun j : ℕ ↦ Real.exp (A * |x|) * Real.exp (-((j : ℝ) ^ (2 : ℕ))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_exp_neg_natCast_sq_zero.const_mul
      (Real.exp (A * |x|))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds henv (Eventually.of_forall hnonneg) hupper

/-- All actual screen derivatives converge in every exponentially weighted `L¹` norm. -/
theorem tendsto_integral_finitePrimeThetaCuspWeightedScreenJetError
    (m : ℕ) (A : ℝ) :
    Tendsto (fun j : ℕ ↦ ∫ x : ℝ,
      finitePrimeThetaCuspWeightedScreenJetError m A j x) atTop (𝓝 0) := by
  obtain ⟨q : ℕ, hq⟩ := exists_nat_gt |A|
  have hq' : |A| < (q + 1 : ℕ) :=
    lt_trans hq (by exact_mod_cast Nat.lt_succ_self q)
  have hmeas : ∀ᶠ j : ℕ in atTop,
      AEStronglyMeasurable (finitePrimeThetaCuspWeightedScreenJetError m A j) := by
    filter_upwards with j
    have hmTop : (m : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞)) := by
      exact_mod_cast (ENat.coe_lt_top m).le
    exact (((Real.continuous_exp.comp
      (continuous_const.mul continuous_abs))).mul
        (((contDiff_finitePrimeThetaCuspEvenScreen j).continuous_iteratedDeriv m hmTop).sub
          (contDiff_thetaCuspFullSource.continuous_iteratedDeriv m hmTop)).abs).aestronglyMeasurable
  have hbound : ∀ᶠ j : ℕ in atTop, ∀ᵐ x : ℝ,
      ‖finitePrimeThetaCuspWeightedScreenJetError m A j x‖ ≤
        finitePrimeThetaCuspWeightedScreenJetMajor m A q x := by
    filter_upwards [eventually_ge_atTop m] with j hmj
    have hne : ∀ᵐ x : ℝ, x ≠ 0 := ae_iff.mpr (by simp)
    filter_upwards [hne] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      exact mul_nonneg (Real.exp_pos _).le (abs_nonneg _))]
    exact finitePrimeThetaCuspWeightedScreenJetError_le_major_of_ne_zero
      m A q j hmj hx
  have hlim : ∀ᵐ x : ℝ,
      Tendsto (fun j : ℕ ↦ finitePrimeThetaCuspWeightedScreenJetError m A j x)
        atTop (𝓝 (0 : ℝ)) :=
    Eventually.of_forall (tendsto_finitePrimeThetaCuspWeightedScreenJetError_pointwise m A)
  have h := tendsto_integral_filter_of_dominated_convergence
    (finitePrimeThetaCuspWeightedScreenJetMajor m A q) hmeas hbound
    (integrable_finitePrimeThetaCuspWeightedScreenJetMajor m A q hq') hlim
  simpa using h

end RHTower
