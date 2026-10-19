import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateInfinityFailure
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateSuperposition
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStatePlateauPositivity

/-!
# Finite signed superpositions of shifted ground states fail at infinity

Let `ω = Σ_j c_j ω_{a_j}` be a finite superposition of shifted ground states with arbitrary real
coefficients, all `a_j > 0`, and test coordinate `M = Φ ω = Σ_j c_j m_{a_j}`. Its folded defect is
linear (`𝓛_N` is linear on the span):

    𝓛_N ω − Φ cosh(x/2) ω = 2Φ(x) [ σ sinh(x/2) − Σ_j c_j C_{a_j}(x) ],    σ = Σ_j c_j sinh(a_j/2).

With mixed signs the per-shift collar lower bounds cannot be combined. On the cone `M ≥ 0` on the
half line they need not be: every `m_{a_j}` is positive on `(0, ∞)` and negative on `(−∞, 0)`, so
positive parts are additive there,

    Σ_j c_j max(m_{a_j}(y), 0) = max(M(y), 0)     for all y,

and the combined collar is the collar of `M`. It dominates the signed prime shift sum of `M`, which
the theta harmonic identity evaluates two-sidedly, shift by shift, to `2 sinh(a_j/2) sinh(x/2)` up
to the universal constant `K`. Hence for `x ≥ max a_j`

    𝓛_N ω − Φ cosh(x/2) ω ≤ −2Φ(x) [ σ sinh(x/2) − K Σ_j |c_j| ].

The decisive coefficient is the pole moment: `σ = 2 ∫_{x>0} M(x) sinh(x/2) dx`, which is positive
for every nonzero `M ≥ 0`. So every finite signed superposition that is nonnegative on the half line
and not identically zero is a strict folded subsolution on a half line `[X, ∞)`. The same pole
moment that makes wide plateaus positive directions of the odd form forbids folded supersolutions in
the span at infinity.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

variable {ι : Type*}

/-- Doob coordinate of the superposition `Σ_j c_j ω_{a_j}`. -/
def spanGroundState (s : Finset ι) (c a : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ s, c j * shiftedGroundState (a j) x

/-- Test coordinate of the superposition, `M = Σ_j c_j m_{a_j}`. -/
def spanShiftDifference (s : Finset ι) (c a : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ s, c j * shiftDifference (a j) x

/-- Source coefficient `σ = Σ_j c_j sinh(a_j/2)` of the superposition. -/
def spanSourceCoefficient (s : Finset ι) (c a : ι → ℝ) : ℝ :=
  ∑ j ∈ s, c j * Real.sinh (a j / 2)

theorem riemannKernelReal_mul_spanGroundState (s : Finset ι) (c a : ι → ℝ) (x : ℝ) :
    riemannKernelReal x * spanGroundState s c a x = spanShiftDifference s c a x := by
  unfold spanGroundState spanShiftDifference
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← riemannKernelReal_mul_shiftedGroundState]
  ring

theorem spanShiftDifference_neg (s : Finset ι) (c a : ι → ℝ) (x : ℝ) :
    spanShiftDifference s c a (-x) = -spanShiftDifference s c a x := by
  unfold spanShiftDifference
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [shiftDifference_neg]
  ring

theorem continuous_spanShiftDifference (s : Finset ι) (c a : ι → ℝ) :
    Continuous (spanShiftDifference s c a) := by
  unfold spanShiftDifference
  exact continuous_finsetSum s fun j _ => continuous_const.mul (continuous_shiftDifference (a j))

/-! ### Linearity of the folded generator on the span -/

theorem foldedShiftGenerator_finsetSum (s : Finset ι) (c : ι → ℝ) (ω : ι → ℝ → ℝ) (t x : ℝ) :
    foldedShiftGenerator (fun y => ∑ j ∈ s, c j * ω j y) t x =
      ∑ j ∈ s, c j * foldedShiftGenerator (ω j) t x := by
  unfold foldedShiftGenerator
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The folded generator of a finite superposition is the superposition of the folded generators. -/
theorem foldedGenerator_spanGroundState {s : Finset ι} {c a : ι → ℝ} (ha : ∀ j ∈ s, 0 < a j)
    {x : ℝ} (hx : 0 < x) :
    foldedGenerator (spanGroundState s c a) x =
      ∑ j ∈ s, c j * foldedGenerator (shiftedGroundState (a j)) x := by
  have hpt : ∀ t, foldedShiftGenerator (spanGroundState s c a) t x =
      ∑ j ∈ s, c j * foldedShiftGenerator (shiftedGroundState (a j)) t x := fun t =>
    foldedShiftGenerator_finsetSum s c (fun j => shiftedGroundState (a j)) t x
  have harch : (∫ t in Ioi (0 : ℝ), archLevyDensity t *
      foldedShiftGenerator (spanGroundState s c a) t x) =
      ∑ j ∈ s, c j * ∫ t in Ioi (0 : ℝ), archLevyDensity t *
        foldedShiftGenerator (shiftedGroundState (a j)) t x := by
    have e : (fun t => archLevyDensity t * foldedShiftGenerator (spanGroundState s c a) t x) =
        fun t => ∑ j ∈ s, c j * (archLevyDensity t *
          foldedShiftGenerator (shiftedGroundState (a j)) t x) := by
      funext t
      rw [hpt, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, integral_finsetSum s fun j hj =>
      (integrableOn_archLevy_foldedShiftGenerator_shiftedGroundState (ha j hj) hx).const_mul _]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have hprime : (∑' n : ℕ, vonMangoldtAtom n *
      foldedShiftGenerator (spanGroundState s c a) (Real.log n) x) =
      ∑ j ∈ s, c j * ∑' n : ℕ, vonMangoldtAtom n *
        foldedShiftGenerator (shiftedGroundState (a j)) (Real.log n) x := by
    have e : (fun n : ℕ => vonMangoldtAtom n *
        foldedShiftGenerator (spanGroundState s c a) (Real.log n) x) =
        fun n => ∑ j ∈ s, c j * (vonMangoldtAtom n *
          foldedShiftGenerator (shiftedGroundState (a j)) (Real.log n) x) := by
      funext n
      rw [hpt, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, Summable.tsum_finsetSum fun j hj =>
      (summable_atom_foldedShiftGenerator_shiftedGroundState (ha j hj) x).mul_left _]
    exact Finset.sum_congr rfl fun j _ => tsum_mul_left
  unfold foldedGenerator
  rw [harch, hprime, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Folded defect of a finite superposition.**
`𝓛_N ω − Φ cosh(x/2) ω = 2Φ(x) [σ sinh(x/2) − Σ_j c_j C_{a_j}(x)]`. -/
theorem foldedDefect_spanGroundState {s : Finset ι} {c a : ι → ℝ} (ha : ∀ j ∈ s, 0 < a j)
    {x : ℝ} (hx : 0 < x) :
    foldedGenerator (spanGroundState s c a) x -
        riemannKernelReal x * Real.cosh (x / 2) * spanGroundState s c a x =
      2 * riemannKernelReal x * (spanSourceCoefficient s c a * Real.sinh (x / 2) -
        ∑ j ∈ s, c j * shiftedCollarMass (a j) x) := by
  rw [foldedGenerator_spanGroundState ha hx]
  unfold spanGroundState spanSourceCoefficient
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_mul, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have h := foldedGenerator_shiftedGroundState_sub_potential (ha j hj) hx
  linear_combination c j * h

/-! ### The collar of the superposition -/

/-- On the cone `M ≥ 0` on the half line, positive parts are additive:
`Σ_j c_j max(m_{a_j}(y), 0) = max(M(y), 0)`. -/
theorem sum_mul_max_shiftDifference_eq {s : Finset ι} {c a : ι → ℝ} (ha : ∀ j ∈ s, 0 < a j)
    (hnn : ∀ y, 0 < y → 0 ≤ spanShiftDifference s c a y) (y : ℝ) :
    ∑ j ∈ s, c j * max (shiftDifference (a j) y) 0 = max (spanShiftDifference s c a y) 0 := by
  rcases le_or_gt y 0 with hy | hy
  · rw [Finset.sum_eq_zero fun j hj => by
      rw [max_shiftDifference_eq_zero_of_nonpos (ha j hj) hy, mul_zero]]
    have hodd := spanShiftDifference_neg s c a y
    have hM : spanShiftDifference s c a y ≤ 0 := by
      rcases hy.lt_or_eq with h | h
      · linarith [hnn (-y) (by linarith)]
      · rw [h, neg_zero] at hodd
        rw [h]
        linarith
    exact (max_eq_right hM).symm
  · rw [max_eq_left (hnn y hy)]
    unfold spanShiftDifference
    exact Finset.sum_congr rfl fun j hj => by
      rw [max_eq_left (shiftDifference_pos (ha j hj) hy).le]

/-- The prime atoms of the superposition's test coordinate are summable. -/
theorem summable_atom_spanShiftDifference_log_sub (s : Finset ι) (c a : ι → ℝ) (x : ℝ) :
    Summable fun n : ℕ => vonMangoldtAtom n * spanShiftDifference s c a (Real.log n - x) := by
  have h := summable_sum (s := s) fun j _ =>
    (summable_atom_shiftDifference_log_sub (a j) x).mul_left (c j)
  refine h.congr fun n => ?_
  unfold spanShiftDifference
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The signed prime shift sum of the superposition is the superposition of the signed sums. -/
theorem tsum_atom_spanShiftDifference_log_sub (s : Finset ι) (c a : ι → ℝ) (x : ℝ) :
    (∑' n : ℕ, vonMangoldtAtom n * spanShiftDifference s c a (Real.log n - x)) =
      ∑ j ∈ s, c j * signedPrimeShift (a j) x := by
  have e : (fun n : ℕ => vonMangoldtAtom n * spanShiftDifference s c a (Real.log n - x)) =
      fun n => ∑ j ∈ s, c j * (vonMangoldtAtom n * shiftDifference (a j) (Real.log n - x)) := by
    funext n
    unfold spanShiftDifference
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, Summable.tsum_finsetSum fun j _ =>
    (summable_atom_shiftDifference_log_sub (a j) x).mul_left _]
  exact Finset.sum_congr rfl fun j _ => tsum_mul_left

/-- **The combined collar dominates the combined signed prime shift sum** on the cone `M ≥ 0`. -/
theorem sum_mul_signedPrimeShift_le_sum_mul_shiftedCollarMass {s : Finset ι} {c a : ι → ℝ}
    (ha : ∀ j ∈ s, 0 < a j) (hnn : ∀ y, 0 < y → 0 ≤ spanShiftDifference s c a y) {x : ℝ}
    (hx : 0 < x) :
    ∑ j ∈ s, c j * signedPrimeShift (a j) x ≤ ∑ j ∈ s, c j * shiftedCollarMass (a j) x := by
  have hadd := sum_mul_max_shiftDifference_eq ha hnn
  have harch : (∑ j ∈ s, c j * ∫ t in Ioi (0 : ℝ),
      archLevyDensity t * max (shiftDifference (a j) (t - x)) 0) =
      ∫ t in Ioi (0 : ℝ), archLevyDensity t * max (spanShiftDifference s c a (t - x)) 0 := by
    have e : (fun t => archLevyDensity t * max (spanShiftDifference s c a (t - x)) 0) =
        fun t => ∑ j ∈ s, c j * (archLevyDensity t * max (shiftDifference (a j) (t - x)) 0) := by
      funext t
      rw [← hadd, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, integral_finsetSum s fun j hj =>
      (integrableOn_archLevy_max_shiftDifference (ha j hj) hx).const_mul _]
    exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm
  have hprime : (∑ j ∈ s, c j * ∑' n : ℕ,
      vonMangoldtAtom n * max (shiftDifference (a j) (Real.log n - x)) 0) =
      ∑' n : ℕ, vonMangoldtAtom n * max (spanShiftDifference s c a (Real.log n - x)) 0 := by
    have e : (fun n : ℕ => vonMangoldtAtom n * max (spanShiftDifference s c a (Real.log n - x)) 0) =
        fun n => ∑ j ∈ s, c j *
          (vonMangoldtAtom n * max (shiftDifference (a j) (Real.log n - x)) 0) := by
      funext n
      rw [← hadd, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, Summable.tsum_finsetSum fun j _ => (summable_atom_max_shiftDifference (a j) x).mul_left _]
    exact Finset.sum_congr rfl fun j _ => tsum_mul_left.symm
  have hsplit : (∑ j ∈ s, c j * shiftedCollarMass (a j) x) =
      (∫ t in Ioi (0 : ℝ), archLevyDensity t * max (spanShiftDifference s c a (t - x)) 0) +
        ∑' n : ℕ, vonMangoldtAtom n * max (spanShiftDifference s c a (Real.log n - x)) 0 := by
    rw [← harch, ← hprime, ← Finset.sum_add_distrib]
    unfold shiftedCollarMass
    exact Finset.sum_congr rfl fun j _ => by ring
  have h1 : 0 ≤ ∫ t in Ioi (0 : ℝ), archLevyDensity t * max (spanShiftDifference s c a (t - x)) 0 :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (archLevyDensity_pos (mem_Ioi.mp ht)).le (le_max_right _ _)
  have hsum : Summable fun n : ℕ =>
      vonMangoldtAtom n * max (spanShiftDifference s c a (Real.log n - x)) 0 := by
    have h := summable_sum (s := s) fun j _ => (summable_atom_max_shiftDifference (a j) x).mul_left (c j)
    refine h.congr fun n => ?_
    rw [← hadd, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : (∑' n : ℕ, vonMangoldtAtom n * spanShiftDifference s c a (Real.log n - x)) ≤
      ∑' n : ℕ, vonMangoldtAtom n * max (spanShiftDifference s c a (Real.log n - x)) 0 :=
    Summable.tsum_le_tsum
      (fun n => mul_le_mul_of_nonneg_left (le_max_left _ _) (vonMangoldtAtom_nonneg n))
      (summable_atom_spanShiftDifference_log_sub s c a x) hsum
  rw [hsplit, ← tsum_atom_spanShiftDifference_log_sub]
  linarith

/-! ### Two-sided evaluation of the signed prime shift sum -/

/-- The theta harmonic identity evaluates the signed prime shift sum two-sidedly:
`|Σ Λ(n) n^{−1/2} m_a(log n − x) − 2 sinh(a/2) sinh(x/2)| ≤ K` for `0 ≤ a ≤ x`. -/
theorem abs_signedPrimeShift_sub_le {a x : ℝ} (ha : 0 ≤ a) (hx : a ≤ x) :
    |signedPrimeShift a x - 2 * Real.sinh (a / 2) * Real.sinh (x / 2)| ≤ collarExcessConstant := by
  have hP : ∀ y, leftPrimeShift y = primeKernelSum y - rightPrimeShift y := fun y => by
    rw [primeKernelSum_eq_add]
    ring
  rw [signedPrimeShift_eq, hP, hP, theta_harmonic_identity, theta_harmonic_identity]
  have hQ1 := rightPrimeShift_le_zero_point (show 0 ≤ x + a by linarith)
  have hQ2 := rightPrimeShift_le_zero_point (show 0 ≤ x - a by linarith)
  have hQ1' := rightPrimeShift_nonneg (x + a)
  have hQ2' := rightPrimeShift_nonneg (x - a)
  have hA1 := abs_le.mp (abs_integral_symArchTerm_le (x + a))
  have hA2 := abs_le.mp (abs_integral_symArchTerm_le (x - a))
  have hcosh : Real.cosh ((x + a) / 2) - Real.cosh ((x - a) / 2) =
      2 * Real.sinh (a / 2) * Real.sinh (x / 2) := by
    rw [show (x + a) / 2 = x / 2 + a / 2 by ring, show (x - a) / 2 = x / 2 - a / 2 by ring,
      Real.cosh_add, Real.cosh_sub]
    ring
  have hc : |2 * archConstantReal * (riemannKernelReal (x + a) - riemannKernelReal (x - a))| ≤
      2 * |archConstantReal| * riemannKernelReal 0 := by
    rw [abs_mul, abs_mul, abs_two]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 := riemannKernelReal_pos (x + a)
    have h2 := riemannKernelReal_pos (x - a)
    have h1' := riemannKernelReal_le_zero_point (x + a)
    have h2' := riemannKernelReal_le_zero_point (x - a)
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hc' := abs_le.mp hc
  unfold collarExcessConstant
  rw [abs_le]
  constructor <;> nlinarith [hA1.1, hA1.2, hA2.1, hA2.2, hc'.1, hc'.2]

/-- The combined signed prime shift sum is at least `2σ sinh(x/2) − K Σ_j |c_j|` once `x ≥ a_j`
for all `j`. -/
theorem sum_mul_signedPrimeShift_ge {s : Finset ι} {c a : ι → ℝ} (ha : ∀ j ∈ s, 0 ≤ a j) {x : ℝ}
    (hx : ∀ j ∈ s, a j ≤ x) :
    2 * spanSourceCoefficient s c a * Real.sinh (x / 2) -
        collarExcessConstant * ∑ j ∈ s, |c j| ≤
      ∑ j ∈ s, c j * signedPrimeShift (a j) x := by
  unfold spanSourceCoefficient
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun j hj => ?_
  have h := abs_signedPrimeShift_sub_le (ha j hj) (hx j hj)
  have hmul : |c j * (signedPrimeShift (a j) x - 2 * Real.sinh (a j / 2) * Real.sinh (x / 2))| ≤
      |c j| * collarExcessConstant := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
  have := (abs_le.mp hmul).1
  nlinarith

/-! ### Infinity failure -/

/-- **Quantitative infinity failure of the span.** On the cone `M ≥ 0` on the half line, for
`x ≥ a_j` for all `j`,
`𝓛_N ω − Φ cosh(x/2) ω ≤ −2Φ(x) [σ sinh(x/2) − K Σ_j |c_j|]`. -/
theorem foldedDefect_spanGroundState_le {s : Finset ι} {c a : ι → ℝ} (ha : ∀ j ∈ s, 0 < a j)
    (hnn : ∀ y, 0 < y → 0 ≤ spanShiftDifference s c a y) {x : ℝ} (hx0 : 0 < x)
    (hx : ∀ j ∈ s, a j ≤ x) :
    foldedGenerator (spanGroundState s c a) x -
        riemannKernelReal x * Real.cosh (x / 2) * spanGroundState s c a x ≤
      -(2 * riemannKernelReal x * (spanSourceCoefficient s c a * Real.sinh (x / 2) -
        collarExcessConstant * ∑ j ∈ s, |c j|)) := by
  rw [foldedDefect_spanGroundState ha hx0]
  have h1 := sum_mul_signedPrimeShift_le_sum_mul_shiftedCollarMass ha hnn hx0
  have h2 := sum_mul_signedPrimeShift_ge (c := c) (fun j hj => (ha j hj).le) hx
  have h3 := mul_le_mul_of_nonneg_left (le_trans h2 h1)
    (mul_nonneg zero_le_two (riemannKernelReal_pos x).le)
  nlinarith [h3]

/-! ### The source coefficient is the pole moment -/

/-- `∫_{x>0} M(x) sinh(x/2) dx = σ/2`: the source coefficient of the superposition is twice the
half-line pole moment of its test coordinate. -/
theorem integral_Ioi_spanShiftDifference_mul_sinh_half (s : Finset ι) (c a : ι → ℝ) :
    (∫ x in Ioi (0 : ℝ), spanShiftDifference s c a x * Real.sinh (x / 2)) =
      spanSourceCoefficient s c a / 2 := by
  have e : (fun x => spanShiftDifference s c a x * Real.sinh (x / 2)) =
      fun x => ∑ j ∈ s, c j * (shiftDifference (a j) x * Real.sinh (x / 2)) := by
    funext x
    unfold spanShiftDifference
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, integral_finsetSum s fun j _ =>
    ((integrable_shiftDifference_mul_sinh_half (a j)).integrableOn).const_mul _]
  unfold spanSourceCoefficient
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_Ioi_shiftDifference_mul_sinh_half]
  ring

/-- The pole moment is positive on the nonzero cone: if `M ≥ 0` on the half line and `M(x₀) > 0`
for some `x₀ > 0`, then `σ > 0`. -/
theorem spanSourceCoefficient_pos {s : Finset ι} {c a : ι → ℝ}
    (hnn : ∀ y, 0 < y → 0 ≤ spanShiftDifference s c a y) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hM : 0 < spanShiftDifference s c a x₀) :
    0 < spanSourceCoefficient s c a := by
  set f : ℝ → ℝ := fun x => spanShiftDifference s c a x * Real.sinh (x / 2) with hf
  have hcont : Continuous f :=
    (continuous_spanShiftDifference s c a).mul (Real.continuous_sinh.comp (continuous_id.div_const 2))
  have hint : IntegrableOn f (Ioi 0) := by
    have e : f = fun x => ∑ j ∈ s, c j * (shiftDifference (a j) x * Real.sinh (x / 2)) := by
      funext x
      simp only [hf, spanShiftDifference, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact integrable_finsetSum s fun j _ =>
      ((integrable_shiftDifference_mul_sinh_half (a j)).integrableOn).const_mul _
  have hnn' : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun y hy =>
      mul_nonneg (hnn y hy) (Real.sinh_nonneg_iff.mpr (by linarith [mem_Ioi.mp hy]))
  have hpos : 0 < ∫ x in Ioi (0 : ℝ), f x := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae hnn' hint]
    have hopen : IsOpen ({y | 0 < f y} ∩ Ioi 0) :=
      (isOpen_lt continuous_const hcont).inter isOpen_Ioi
    have hmem : x₀ ∈ {y | 0 < f y} ∩ Ioi 0 :=
      ⟨mul_pos hM (Real.sinh_pos_iff.mpr (by linarith)), hx₀⟩
    refine lt_of_lt_of_le (hopen.measure_pos volume ⟨x₀, hmem⟩) (measure_mono ?_)
    exact fun y hy => ⟨ne_of_gt hy.1, hy.2⟩
  have h := integral_Ioi_spanShiftDifference_mul_sinh_half s c a
  rw [← hf] at h
  linarith

/-- **Infinity failure of the span.** Every finite signed superposition of shifted ground states
that is nonnegative on the half line and not identically zero there is a strict folded subsolution
on a half line `[X, ∞)`. -/
theorem exists_infinity_window_spanGroundState_foldedGenerator_lt_potential {s : Finset ι}
    {c a : ι → ℝ} (ha : ∀ j ∈ s, 0 < a j)
    (hnn : ∀ y, 0 < y → 0 ≤ spanShiftDifference s c a y) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hM : 0 < spanShiftDifference s c a x₀) :
    ∃ X : ℝ, 0 < X ∧ ∀ x, X ≤ x →
      foldedGenerator (spanGroundState s c a) x <
        riemannKernelReal x * Real.cosh (x / 2) * spanGroundState s c a x := by
  have hσ := spanSourceCoefficient_pos hnn hx₀ hM
  set σ := spanSourceCoefficient s c a
  set B := |collarExcessConstant| * ∑ j ∈ s, |c j|
  have hB : collarExcessConstant * ∑ j ∈ s, |c j| ≤ B :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (Finset.sum_nonneg fun j _ => abs_nonneg _)
  set A := ∑ j ∈ s, a j
  have hA : ∀ j ∈ s, a j ≤ A := fun j hj =>
    Finset.single_le_sum (fun i hi => (ha i hi).le) hj
  refine ⟨max (|A| + 1) (2 * (B + 1) / σ), lt_of_lt_of_le (by positivity) (le_max_left _ _),
    fun x hX => ?_⟩
  have hx1 : |A| + 1 ≤ x := le_trans (le_max_left _ _) hX
  have hx0 : 0 < x := by linarith [abs_nonneg A]
  have hxa : ∀ j ∈ s, a j ≤ x := fun j hj => by linarith [hA j hj, le_abs_self A]
  have hx2 : 2 * (B + 1) / σ ≤ x := le_trans (le_max_right _ _) hX
  have h1 : 2 * (B + 1) ≤ x * σ := by rwa [div_le_iff₀ hσ] at hx2
  have hsinh : x / 2 ≤ Real.sinh (x / 2) := Real.self_le_sinh_iff.mpr (by linarith)
  have h2 := mul_le_mul_of_nonneg_left hsinh hσ.le
  have hgap : 0 < σ * Real.sinh (x / 2) - collarExcessConstant * ∑ j ∈ s, |c j| := by
    nlinarith
  have hd := foldedDefect_spanGroundState_le ha hnn hx0 hxa
  have hΦ := riemannKernelReal_pos x
  have : 0 < 2 * riemannKernelReal x *
      (σ * Real.sinh (x / 2) - collarExcessConstant * ∑ j ∈ s, |c j|) := by positivity
  linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
