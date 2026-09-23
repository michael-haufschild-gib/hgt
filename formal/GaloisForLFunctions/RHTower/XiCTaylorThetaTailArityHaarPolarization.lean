import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSquareIndexPolarization

open Complex Real MeasureTheory Set Filter Topology Polynomial
namespace RHTower
noncomputable section

/-- Critical translate row at an arbitrary positive logarithmic scale. -/
def thetaSquareIndexScaleDensity (L : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-((k : ℝ) * L) / 2) *
    thetaCuspTailSecondDensity (x + (k : ℝ) * L)

/-- Exact-valuation layer between two adjacent scale rows. -/
def thetaSquareIndexScaleExactLayer (L : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  thetaSquareIndexScaleDensity L k x -
    thetaSquareIndexScaleDensity L (k + 1) x

/-- Mean-zero arity-Haar layer. -/
def thetaSquareIndexScaleHaarLayer (L : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  Real.exp L * thetaSquareIndexScaleDensity L (k + 1) x -
    thetaSquareIndexScaleDensity L k x

@[simp] theorem thetaSquareIndexScaleDensity_zero (L x : ℝ) :
    thetaSquareIndexScaleDensity L 0 x = thetaCuspTailSecondDensity x := by
  simp [thetaSquareIndexScaleDensity]

/-- Universal arity-Haar one-step polarization. -/
theorem thetaSquareIndexScale_oneStep
    {L : ℝ} (hL : L ≠ 0) (k : ℕ) (x y : ℝ) :
    thetaSquareIndexScaleDensity L k x * thetaSquareIndexScaleDensity L k y =
      (Real.exp L / (Real.exp L - 1)) *
          thetaSquareIndexScaleExactLayer L k x *
            thetaSquareIndexScaleExactLayer L k y -
        (1 / (Real.exp L - 1)) *
          thetaSquareIndexScaleHaarLayer L k x *
            thetaSquareIndexScaleHaarLayer L k y +
        Real.exp L *
          thetaSquareIndexScaleDensity L (k + 1) x *
            thetaSquareIndexScaleDensity L (k + 1) y := by
  have hden : Real.exp L - 1 ≠ 0 := by
    intro h
    have : Real.exp L = 1 := sub_eq_zero.mp h
    apply hL
    apply Real.exp_injective
    simpa using this
  unfold thetaSquareIndexScaleExactLayer thetaSquareIndexScaleHaarLayer
  field_simp
  ring

/-- Cofinal polarization at every logarithmic arity. -/
theorem thetaCuspTailSecondDensity_mul_scaleHaarPolarization
    {L : ℝ} (hL : L ≠ 0) (N : ℕ) (x y : ℝ) :
    thetaCuspTailSecondDensity x * thetaCuspTailSecondDensity y =
      (∑ k ∈ Finset.range N, Real.exp ((k : ℝ) * L) *
        ((Real.exp L / (Real.exp L - 1)) *
            thetaSquareIndexScaleExactLayer L k x *
              thetaSquareIndexScaleExactLayer L k y -
          (1 / (Real.exp L - 1)) *
            thetaSquareIndexScaleHaarLayer L k x *
              thetaSquareIndexScaleHaarLayer L k y)) +
      Real.exp ((N : ℝ) * L) *
        thetaSquareIndexScaleDensity L N x *
          thetaSquareIndexScaleDensity L N y := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hexp : Real.exp (((N + 1 : ℕ) : ℝ) * L) =
          Real.exp ((N : ℝ) * L) * Real.exp L := by
        rw [show (((N + 1 : ℕ) : ℝ) * L) = (N : ℝ) * L + L by
          push_cast
          ring,
          Real.exp_add]
      have hstep := thetaSquareIndexScale_oneStep hL N x y
      have htop :
          Real.exp ((N : ℝ) * L) *
              thetaSquareIndexScaleDensity L N x *
                thetaSquareIndexScaleDensity L N y =
            Real.exp ((N : ℝ) * L) *
                ((Real.exp L / (Real.exp L - 1)) *
                    thetaSquareIndexScaleExactLayer L N x *
                      thetaSquareIndexScaleExactLayer L N y -
                  (1 / (Real.exp L - 1)) *
                    thetaSquareIndexScaleHaarLayer L N x *
                      thetaSquareIndexScaleHaarLayer L N y) +
              Real.exp (((N + 1 : ℕ) : ℝ) * L) *
                thetaSquareIndexScaleDensity L (N + 1) x *
                  thetaSquareIndexScaleDensity L (N + 1) y := by
        rw [show Real.exp ((N : ℝ) * L) *
              thetaSquareIndexScaleDensity L N x *
                thetaSquareIndexScaleDensity L N y =
            Real.exp ((N : ℝ) * L) *
              (thetaSquareIndexScaleDensity L N x *
                thetaSquareIndexScaleDensity L N y) by ring,
          hstep, hexp]
        ring
      rw [Finset.sum_range_succ, ih, htop]
      ring

/-- The completion character cancellation is universal in the logarithmic scale. -/
theorem thetaSquareIndexScaleCompletionCharacter_cancel (L x : ℝ) :
    Real.exp (L / 2) * thetaCuspReflectionMode (x - L) -
        thetaCuspReflectionMode x =
      -((Real.exp L - 1) / 2) * Real.exp (-x / 2) := by
  unfold thetaCuspReflectionMode
  have hpos : Real.exp ((x - L) / 2) =
      Real.exp (x / 2) * Real.exp (-L / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hneg : Real.exp (-(x - L) / 2) =
      Real.exp (-x / 2) * Real.exp (L / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcancel : Real.exp (L / 2) * Real.exp (-L / 2) = 1 := by
    rw [← Real.exp_add]
    rw [show L / 2 + -L / 2 = 0 by ring, Real.exp_zero]
  have hsquare : Real.exp (L / 2) * Real.exp (L / 2) = Real.exp L := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hpos, hneg]
  linear_combination
    (Real.exp (x / 2) / 2) * hcancel +
      (-Real.exp (-x / 2) / 2) * hsquare

/-- Reflection sends the mean-zero Haar row to the translated exact-valuation row.  The only
defect is the universal decaying half-exponential. -/
theorem thetaSquareIndexScaleHaarLayer_neg_reflection
    (L : ℝ) (k : ℕ) (x : ℝ) :
    thetaSquareIndexScaleHaarLayer L k (-x) =
      Real.exp (L / 2) *
          thetaSquareIndexScaleExactLayer L k
            (x - (2 * k + 1 : ℕ) * L) -
        ((Real.exp L - 1) / 2) * Real.exp (-x / 2) := by
  let t : ℝ := x - (k : ℝ) * L
  have harg0 : -x + (k : ℝ) * L = -t := by
    dsimp [t]
    ring
  have harg1 : -x + ((k + 1 : ℕ) : ℝ) * L = -(t - L) := by
    dsimp [t]
    push_cast
    ring
  have hshift0 : x - ((2 * k + 1 : ℕ) : ℝ) * L + (k : ℝ) * L = t - L := by
    dsimp [t]
    push_cast
    ring
  have hshift1 : x - ((2 * k + 1 : ℕ) : ℝ) * L +
      ((k + 1 : ℕ) : ℝ) * L = t := by
    dsimp [t]
    push_cast
    ring
  have hw1 : Real.exp L * Real.exp (-(((k + 1 : ℕ) : ℝ) * L) / 2) =
      Real.exp (-((k : ℝ) * L) / 2) * Real.exp (L / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hw0 : Real.exp (-((k : ℝ) * L) / 2) =
      Real.exp (L / 2) * Real.exp (-(((k + 1 : ℕ) : ℝ) * L) / 2) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hdef := thetaSquareIndexScaleCompletionCharacter_cancel L t
  have hscale : Real.exp (-((k : ℝ) * L) / 2) * Real.exp (-t / 2) =
      Real.exp (-x / 2) := by
    rw [← Real.exp_add]
    dsimp [t]
    congr 1
    ring
  have hdens :
      Real.exp L *
            (Real.exp (-(((k + 1 : ℕ) : ℝ) * L) / 2) *
              thetaCuspTailSecondDensity (t - L)) -
          Real.exp (-((k : ℝ) * L) / 2) * thetaCuspTailSecondDensity t =
        Real.exp (L / 2) *
          (Real.exp (-((k : ℝ) * L) / 2) *
              thetaCuspTailSecondDensity (t - L) -
            Real.exp (-(((k + 1 : ℕ) : ℝ) * L) / 2) *
              thetaCuspTailSecondDensity t) := by
    rw [show Real.exp L *
          (Real.exp (-(((k + 1 : ℕ) : ℝ) * L) / 2) *
            thetaCuspTailSecondDensity (t - L)) =
        (Real.exp L * Real.exp (-(((k + 1 : ℕ) : ℝ) * L) / 2)) *
          thetaCuspTailSecondDensity (t - L) by ring,
      hw1, hw0]
    ring
  have hcomp :
      Real.exp L *
            (Real.exp (-(((k + 1 : ℕ) : ℝ) * L) / 2) *
              thetaCuspReflectionMode (t - L)) -
          Real.exp (-((k : ℝ) * L) / 2) * thetaCuspReflectionMode t =
        -((Real.exp L - 1) / 2) * Real.exp (-x / 2) := by
    calc
      _ = Real.exp (-((k : ℝ) * L) / 2) *
          (Real.exp (L / 2) * thetaCuspReflectionMode (t - L) -
            thetaCuspReflectionMode t) := by
              rw [show Real.exp L *
                    (Real.exp (-(((k + 1 : ℕ) : ℝ) * L) / 2) *
                      thetaCuspReflectionMode (t - L)) =
                  (Real.exp L *
                    Real.exp (-(((k + 1 : ℕ) : ℝ) * L) / 2)) *
                      thetaCuspReflectionMode (t - L) by ring,
                hw1]
              ring
      _ = Real.exp (-((k : ℝ) * L) / 2) *
          (-((Real.exp L - 1) / 2) * Real.exp (-t / 2)) := by rw [hdef]
      _ = _ := by
        rw [show Real.exp (-((k : ℝ) * L) / 2) *
            (-((Real.exp L - 1) / 2) * Real.exp (-t / 2)) =
          -((Real.exp L - 1) / 2) *
            (Real.exp (-((k : ℝ) * L) / 2) * Real.exp (-t / 2)) by ring,
          hscale]
  unfold thetaSquareIndexScaleHaarLayer thetaSquareIndexScaleExactLayer
    thetaSquareIndexScaleDensity
  rw [harg0, harg1, thetaCuspTailSecondDensity_neg,
    thetaCuspTailSecondDensity_neg, hshift0, hshift1]
  linear_combination hdens + hcomp

/-- Reflection cancels the two square channels at every arity. -/
theorem thetaSquareIndexScaleHaarLayer_reflected_polarization
    {L : ℝ} (hL : L ≠ 0) (k : ℕ) (x y : ℝ) :
    (Real.exp L / (Real.exp L - 1)) *
          thetaSquareIndexScaleExactLayer L k
              (x - (2 * k + 1 : ℕ) * L) *
            thetaSquareIndexScaleExactLayer L k
              (y - (2 * k + 1 : ℕ) * L) -
        (1 / (Real.exp L - 1)) *
          thetaSquareIndexScaleHaarLayer L k (-x) *
            thetaSquareIndexScaleHaarLayer L k (-y) =
      (Real.exp (L / 2) / 2) *
          (thetaSquareIndexScaleExactLayer L k
                (x - (2 * k + 1 : ℕ) * L) * Real.exp (-y / 2) +
            Real.exp (-x / 2) *
              thetaSquareIndexScaleExactLayer L k
                (y - (2 * k + 1 : ℕ) * L)) -
        ((Real.exp L - 1) / 4) *
          Real.exp (-x / 2) * Real.exp (-y / 2) := by
  rw [thetaSquareIndexScaleHaarLayer_neg_reflection,
    thetaSquareIndexScaleHaarLayer_neg_reflection]
  have hden : Real.exp L - 1 ≠ 0 := by
    intro h
    apply hL
    apply Real.exp_injective
    simpa using sub_eq_zero.mp h
  have hsquare : Real.exp (L / 2) * Real.exp (L / 2) = Real.exp L := by
    rw [← Real.exp_add]
    congr 1
    ring
  field_simp
  ring_nf
  have hsquare' : Real.exp (L * (1 / 2)) ^ (2 : ℕ) = Real.exp L := by
    rw [pow_two]
    convert hsquare using 1 ; congr 1 <;> ring
  rw [hsquare']
  ring

/-- One exact-valuation translate is a discrete coboundary after critical weighting. -/
theorem thetaSquareIndexScaleExactLayer_shifted_coboundary
    (L : ℝ) (k : ℕ) (x : ℝ) :
    Real.exp ((k : ℝ) * L) * Real.exp (L / 2) *
        thetaSquareIndexScaleExactLayer L k
          (x - (2 * k + 1 : ℕ) * L) =
      Real.exp (((k + 1 : ℕ) : ℝ) * L) *
          thetaSquareIndexScaleDensity L (k + 1)
            (x - 2 * ((k + 1 : ℕ) : ℝ) * L) -
        Real.exp ((k : ℝ) * L) *
          thetaSquareIndexScaleDensity L k
            (x - 2 * (k : ℝ) * L) := by
  unfold thetaSquareIndexScaleExactLayer thetaSquareIndexScaleDensity
  have harg0 :
      x - ((2 * k + 1 : ℕ) : ℝ) * L + (k : ℝ) * L =
        x - ((k + 1 : ℕ) : ℝ) * L := by
    push_cast
    ring
  have harg1 :
      x - ((2 * k + 1 : ℕ) : ℝ) * L + ((k + 1 : ℕ) : ℝ) * L =
        x - (k : ℝ) * L := by
    push_cast
    ring
  have htoparg :
      x - 2 * ((k + 1 : ℕ) : ℝ) * L + ((k + 1 : ℕ) : ℝ) * L =
        x - ((k + 1 : ℕ) : ℝ) * L := by ring
  have hbotarg : x - 2 * (k : ℝ) * L + (k : ℝ) * L =
      x - (k : ℝ) * L := by ring
  rw [harg0, harg1, htoparg, hbotarg]
  have hcoef0 :
      Real.exp ((k : ℝ) * L) * Real.exp (L / 2) *
          Real.exp (-((k : ℝ) * L) / 2) =
        Real.exp (((k + 1 : ℕ) : ℝ) * L) *
          Real.exp (-(((k + 1 : ℕ) : ℝ) * L) / 2) := by
    repeat rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hcoef1 :
      Real.exp ((k : ℝ) * L) * Real.exp (L / 2) *
          Real.exp (-(((k + 1 : ℕ) : ℝ) * L) / 2) =
        Real.exp ((k : ℝ) * L) * Real.exp (-((k : ℝ) * L) / 2) := by
    repeat rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [show Real.exp ((k : ℝ) * L) * Real.exp (L / 2) *
        (Real.exp (-((k : ℝ) * L) / 2) *
            thetaCuspTailSecondDensity (x - ((k + 1 : ℕ) : ℝ) * L) -
          Real.exp (-(((k + 1 : ℕ) : ℝ) * L) / 2) *
            thetaCuspTailSecondDensity (x - (k : ℝ) * L)) =
      (Real.exp ((k : ℝ) * L) * Real.exp (L / 2) *
          Real.exp (-((k : ℝ) * L) / 2)) *
            thetaCuspTailSecondDensity (x - ((k + 1 : ℕ) : ℝ) * L) -
        (Real.exp ((k : ℝ) * L) * Real.exp (L / 2) *
          Real.exp (-(((k + 1 : ℕ) : ℝ) * L) / 2)) *
            thetaCuspTailSecondDensity (x - (k : ℝ) * L) by ring,
    hcoef0, hcoef1]
  ring

/-- All intermediate translated exact-valuation rows telescope. -/
theorem thetaSquareIndexScaleExactLayer_shifted_weightedSum
    (L : ℝ) (N : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range N,
      Real.exp ((k : ℝ) * L) * Real.exp (L / 2) *
        thetaSquareIndexScaleExactLayer L k
          (x - (2 * k + 1 : ℕ) * L)) =
      Real.exp ((N : ℝ) * L) *
          thetaSquareIndexScaleDensity L N
            (x - 2 * (N : ℝ) * L) -
        thetaCuspTailSecondDensity x := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih,
        thetaSquareIndexScaleExactLayer_shifted_coboundary]
      push_cast
      ring

theorem sum_exp_mul_exp_sub_one (L : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N,
      Real.exp ((k : ℝ) * L) * (Real.exp L - 1)) =
      Real.exp ((N : ℝ) * L) - 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hexp : Real.exp (((N + 1 : ℕ) : ℝ) * L) =
          Real.exp ((N : ℝ) * L) * Real.exp L := by
        rw [show (((N + 1 : ℕ) : ℝ) * L) = (N : ℝ) * L + L by
          push_cast
          ring,
          Real.exp_add]
      rw [hexp]
      ring

/-- Every logarithmic arity has the same terminal reflected source: one remote row, the original
density cross, and the elementary exponential square. -/
theorem thetaSquareIndexScaleHaarLayer_reflected_sum_eq_topDifference
    {L : ℝ} (hL : L ≠ 0) (N : ℕ) (x y : ℝ) :
    (∑ k ∈ Finset.range N,
      Real.exp ((k : ℝ) * L) *
        ((Real.exp L / (Real.exp L - 1)) *
              thetaSquareIndexScaleExactLayer L k
                  (x - (2 * k + 1 : ℕ) * L) *
                thetaSquareIndexScaleExactLayer L k
                  (y - (2 * k + 1 : ℕ) * L) -
          (1 / (Real.exp L - 1)) *
            thetaSquareIndexScaleHaarLayer L k (-x) *
              thetaSquareIndexScaleHaarLayer L k (-y))) =
      (1 / 2 : ℝ) * Real.exp ((N : ℝ) * L) *
          (thetaSquareIndexScaleDensity L N
                (x - 2 * (N : ℝ) * L) * Real.exp (-y / 2) +
            Real.exp (-x / 2) *
              thetaSquareIndexScaleDensity L N
                (y - 2 * (N : ℝ) * L)) -
        (1 / 2 : ℝ) *
          (thetaCuspTailSecondDensity x * Real.exp (-y / 2) +
            Real.exp (-x / 2) * thetaCuspTailSecondDensity y) -
        ((Real.exp ((N : ℝ) * L) - 1) / 4) *
          Real.exp (-x / 2) * Real.exp (-y / 2) := by
  rw [show (∑ k ∈ Finset.range N,
      Real.exp ((k : ℝ) * L) *
        ((Real.exp L / (Real.exp L - 1)) *
              thetaSquareIndexScaleExactLayer L k
                  (x - (2 * k + 1 : ℕ) * L) *
                thetaSquareIndexScaleExactLayer L k
                  (y - (2 * k + 1 : ℕ) * L) -
          (1 / (Real.exp L - 1)) *
            thetaSquareIndexScaleHaarLayer L k (-x) *
              thetaSquareIndexScaleHaarLayer L k (-y))) =
      ∑ k ∈ Finset.range N, Real.exp ((k : ℝ) * L) *
        ((Real.exp (L / 2) / 2) *
            (thetaSquareIndexScaleExactLayer L k
                  (x - (2 * k + 1 : ℕ) * L) * Real.exp (-y / 2) +
              Real.exp (-x / 2) *
                thetaSquareIndexScaleExactLayer L k
                  (y - (2 * k + 1 : ℕ) * L)) -
          ((Real.exp L - 1) / 4) *
            Real.exp (-x / 2) * Real.exp (-y / 2)) by
    apply Finset.sum_congr rfl
    intro k _hk
    rw [thetaSquareIndexScaleHaarLayer_reflected_polarization hL]
  ]
  rw [show (∑ k ∈ Finset.range N, Real.exp ((k : ℝ) * L) *
      ((Real.exp (L / 2) / 2) *
          (thetaSquareIndexScaleExactLayer L k
                (x - (2 * k + 1 : ℕ) * L) * Real.exp (-y / 2) +
            Real.exp (-x / 2) *
              thetaSquareIndexScaleExactLayer L k
                (y - (2 * k + 1 : ℕ) * L)) -
        ((Real.exp L - 1) / 4) *
          Real.exp (-x / 2) * Real.exp (-y / 2))) =
      (1 / 2 : ℝ) *
          (∑ k ∈ Finset.range N,
            Real.exp ((k : ℝ) * L) * Real.exp (L / 2) *
              thetaSquareIndexScaleExactLayer L k
                (x - (2 * k + 1 : ℕ) * L)) * Real.exp (-y / 2) +
        (1 / 2 : ℝ) * Real.exp (-x / 2) *
          (∑ k ∈ Finset.range N,
            Real.exp ((k : ℝ) * L) * Real.exp (L / 2) *
              thetaSquareIndexScaleExactLayer L k
                (y - (2 * k + 1 : ℕ) * L)) -
        (1 / 4 : ℝ) *
          (∑ k ∈ Finset.range N,
            Real.exp ((k : ℝ) * L) * (Real.exp L - 1)) *
              Real.exp (-x / 2) * Real.exp (-y / 2) by
    rw [show (fun k : ℕ => Real.exp ((k : ℝ) * L) *
        ((Real.exp (L / 2) / 2) *
            (thetaSquareIndexScaleExactLayer L k
                  (x - (2 * k + 1 : ℕ) * L) * Real.exp (-y / 2) +
              Real.exp (-x / 2) *
                thetaSquareIndexScaleExactLayer L k
                  (y - (2 * k + 1 : ℕ) * L)) -
          ((Real.exp L - 1) / 4) *
            Real.exp (-x / 2) * Real.exp (-y / 2))) =
      fun k : ℕ =>
        (1 / 2 : ℝ) *
            (Real.exp ((k : ℝ) * L) * Real.exp (L / 2) *
              thetaSquareIndexScaleExactLayer L k
                (x - (2 * k + 1 : ℕ) * L)) * Real.exp (-y / 2) +
          (1 / 2 : ℝ) * Real.exp (-x / 2) *
            (Real.exp ((k : ℝ) * L) * Real.exp (L / 2) *
              thetaSquareIndexScaleExactLayer L k
                (y - (2 * k + 1 : ℕ) * L)) -
          (1 / 4 : ℝ) *
            (Real.exp ((k : ℝ) * L) * (Real.exp L - 1)) *
              Real.exp (-x / 2) * Real.exp (-y / 2) by
        funext k
        ring]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_mul, Finset.mul_sum]
  ]
  rw [thetaSquareIndexScaleExactLayer_shifted_weightedSum,
    thetaSquareIndexScaleExactLayer_shifted_weightedSum,
    sum_exp_mul_exp_sub_one]
  ring

end
end RHTower
