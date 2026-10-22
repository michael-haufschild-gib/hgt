import GaloisForLFunctions.HTGeometry.SmoothDerivativeChain
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimePositiveScreen

/-!
# Actual derivatives of finite-prime theta screens

Finite-prime theta sources form a complete derivative chain and hence are smooth. Leibniz and
reflection then identify every actual derivative of the one-sided and even screens.
-/

open Filter Topology Set

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

theorem contDiff_finitePrimeThetaCuspDerivative (m N : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (finitePrimeThetaCuspDerivative m N) := by
  exact contDiff_top_of_hasDerivAt_chain
    (f := fun r ↦ finitePrimeThetaCuspDerivative r N)
    (fun r x ↦ hasDerivAt_finitePrimeThetaCuspDerivative r N x) m

theorem contDiff_finitePrimeThetaCuspSource (N : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (finitePrimeThetaCuspSource N) := by
  have hzero : finitePrimeThetaCuspSource N = finitePrimeThetaCuspDerivative 0 N := by
    simpa only [iteratedDeriv_zero] using iteratedDeriv_finitePrimeThetaCuspSource 0 N
  rw [hzero]
  exact contDiff_finitePrimeThetaCuspDerivative 0 N

theorem contDiff_finitePrimeThetaCuspScreenCutoff (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (finitePrimeThetaCuspScreenCutoff j) := by
  unfold finitePrimeThetaCuspScreenCutoff
  exact ccmSmoothHalflineCutoff_contDiff.comp (contDiff_id.add contDiff_const)

theorem contDiff_finitePrimeThetaCuspRightScreen (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (finitePrimeThetaCuspRightScreen j) := by
  unfold finitePrimeThetaCuspRightScreen
  exact (contDiff_finitePrimeThetaCuspScreenCutoff j).mul
    (contDiff_finitePrimeThetaCuspSource _)

theorem contDiff_finitePrimeThetaCuspEvenScreen (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (finitePrimeThetaCuspEvenScreen j) := by
  unfold finitePrimeThetaCuspEvenScreen
  have hr := contDiff_finitePrimeThetaCuspRightScreen j
  have hneg : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ℝ ↦ finitePrimeThetaCuspRightScreen j (-x)) :=
    hr.comp (by fun_prop)
  exact (hr.add hneg).div_const 2

/-- Explicit Leibniz jet of the one-sided screened source. -/
def finitePrimeThetaCuspRightScreenDerivative (m j : ℕ) (x : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (m + 1),
    (m.choose r : ℝ) *
      iteratedDeriv r (finitePrimeThetaCuspScreenCutoff j) x *
      finitePrimeThetaCuspDerivative (m - r)
        (finitePrimeThetaCuspPositiveScreenIndex j) x

theorem iteratedDeriv_finitePrimeThetaCuspRightScreen (m j : ℕ) :
    iteratedDeriv m (finitePrimeThetaCuspRightScreen j) =
      finitePrimeThetaCuspRightScreenDerivative m j := by
  funext x
  have hm : (m : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞)) := by
    exact_mod_cast (ENat.coe_lt_top m).le
  change iteratedDeriv m
      (finitePrimeThetaCuspScreenCutoff j *
        finitePrimeThetaCuspSource (finitePrimeThetaCuspPositiveScreenIndex j)) x = _
  rw [iteratedDeriv_mul
    ((contDiff_finitePrimeThetaCuspScreenCutoff j).contDiffAt.of_le hm)
    ((contDiff_finitePrimeThetaCuspSource
      (finitePrimeThetaCuspPositiveScreenIndex j)).contDiffAt.of_le hm)]
  unfold finitePrimeThetaCuspRightScreenDerivative
  apply Finset.sum_congr rfl
  intro r hr
  rw [congrFun (iteratedDeriv_finitePrimeThetaCuspSource (m - r)
    (finitePrimeThetaCuspPositiveScreenIndex j)) x]

/-- Explicit reflected jet of the positive even screen. -/
def finitePrimeThetaCuspEvenScreenDerivative (m j : ℕ) (x : ℝ) : ℝ :=
  (finitePrimeThetaCuspRightScreenDerivative m j x +
    (-1 : ℝ) ^ m * finitePrimeThetaCuspRightScreenDerivative m j (-x)) / 2

theorem iteratedDeriv_finitePrimeThetaCuspEvenScreen (m j : ℕ) :
    iteratedDeriv m (finitePrimeThetaCuspEvenScreen j) =
      finitePrimeThetaCuspEvenScreenDerivative m j := by
  funext x
  have hr := contDiff_finitePrimeThetaCuspRightScreen j
  have hm : (m : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞)) := by
    exact_mod_cast (ENat.coe_lt_top m).le
  have hsum : iteratedDeriv m (fun y : ℝ ↦
      finitePrimeThetaCuspRightScreen j y +
        finitePrimeThetaCuspRightScreen j (-y)) x =
      iteratedDeriv m (finitePrimeThetaCuspRightScreen j) x +
        (-1 : ℝ) ^ m * iteratedDeriv m
          (finitePrimeThetaCuspRightScreen j) (-x) := by
    change iteratedDeriv m
      (finitePrimeThetaCuspRightScreen j +
        fun y : ℝ ↦ finitePrimeThetaCuspRightScreen j (-y)) x = _
    rw [iteratedDeriv_add (hr.contDiffAt.of_le hm)
      ((by fun_prop : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : ℝ ↦ finitePrimeThetaCuspRightScreen j (-y))).contDiffAt.of_le hm)]
    rw [iteratedDeriv_comp_neg]
    simp only [smul_eq_mul]
  change iteratedDeriv m (fun y : ℝ ↦
    (finitePrimeThetaCuspRightScreen j y +
      finitePrimeThetaCuspRightScreen j (-y)) / 2) x = _
  rw [iteratedDeriv_div_const]
  rw [hsum]
  rw [congrFun (iteratedDeriv_finitePrimeThetaCuspRightScreen m j) x,
    congrFun (iteratedDeriv_finitePrimeThetaCuspRightScreen m j) (-x)]
  rfl

/-- Inside the fully open screen window, every actual jet is the parity average of the selected
finite-prime source jets. -/
theorem iteratedDeriv_finitePrimeThetaCuspEvenScreen_eq_source_average
    (m j : ℕ) {x : ℝ} (hx : |x| < (j : ℝ)) :
    iteratedDeriv m (finitePrimeThetaCuspEvenScreen j) x =
      (finitePrimeThetaCuspDerivative m
          (finitePrimeThetaCuspPositiveScreenIndex j) x +
        (-1 : ℝ) ^ m * finitePrimeThetaCuspDerivative m
          (finitePrimeThetaCuspPositiveScreenIndex j) (-x)) / 2 := by
  let N := finitePrimeThetaCuspPositiveScreenIndex j
  have hxlo : -((j : ℕ) : ℝ) < x := by linarith [neg_abs_le x]
  have hxhi : x < ((j : ℕ) : ℝ) := (le_abs_self x).trans_lt hx
  let f : ℝ → ℝ := fun y ↦
    (finitePrimeThetaCuspSource N y + finitePrimeThetaCuspSource N (-y)) / 2
  have heq : finitePrimeThetaCuspEvenScreen j =ᶠ[𝓝 x] f := by
    filter_upwards [Ioi_mem_nhds hxlo, Iio_mem_nhds hxhi] with y hylo hyhi
    unfold finitePrimeThetaCuspEvenScreen finitePrimeThetaCuspRightScreen f
    rw [finitePrimeThetaCuspScreenCutoff_eq_one j hylo.le,
      finitePrimeThetaCuspScreenCutoff_eq_one j (by
        change y < ((j : ℕ) : ℝ) at hyhi
        linarith)]
    ring
  rw [heq.iteratedDeriv_eq m]
  have hs := contDiff_finitePrimeThetaCuspSource N
  have hm : (m : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞)) := by
    exact_mod_cast (ENat.coe_lt_top m).le
  dsimp only [f]
  have hsum : iteratedDeriv m (fun y : ℝ ↦
      finitePrimeThetaCuspSource N y + finitePrimeThetaCuspSource N (-y)) x =
      iteratedDeriv m (finitePrimeThetaCuspSource N) x +
        (-1 : ℝ) ^ m * iteratedDeriv m (finitePrimeThetaCuspSource N) (-x) := by
    change iteratedDeriv m
      (finitePrimeThetaCuspSource N +
        fun y : ℝ ↦ finitePrimeThetaCuspSource N (-y)) x = _
    rw [iteratedDeriv_add (hs.contDiffAt.of_le hm)
      ((by fun_prop : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : ℝ ↦ finitePrimeThetaCuspSource N (-y))).contDiffAt.of_le hm)]
    rw [iteratedDeriv_comp_neg]
    simp only [smul_eq_mul]
  rw [iteratedDeriv_div_const]
  rw [hsum]
  rw [congrFun (iteratedDeriv_finitePrimeThetaCuspSource m N) x,
    congrFun (iteratedDeriv_finitePrimeThetaCuspSource m N) (-x)]

end RHTower
