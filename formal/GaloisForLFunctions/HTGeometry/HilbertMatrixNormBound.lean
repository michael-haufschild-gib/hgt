import GaloisForLFunctions.HTGeometry.ConvexAntitoneComposition
import GaloisForLFunctions.HTGeometry.MidpointConvexIntegralInterior
import GaloisForLFunctions.HTGeometry.ArctanSqrtAntiderivative
import GaloisForLFunctions.HTGeometry.WeightedSchurTest

/-!
# The Hilbert matrix has norm at most `π`

The quadratic form of the Hilbert–Hankel kernel `1/(m+n+1)` is bounded by `π` times the energy:

```text
|∑_{m,n} b m · b n / (m+n+1)| ≤ π ∑_m (b m)²
```

for every finitely supported real vector `b`.  Together with the positivity of the same form this is
the operator-norm statement for the Hilbert matrix.

The proof is the weighted Schur test with the weight `w n = (n + ½)^{-1/2}`, whose weighted row sums
are exactly midpoint values:

```text
∑_n 1/((m+n+1) √(n+½)) = ∑_n f(n+½),      f(t) = 1/((m+½+t)√t),
```

`f` is convex on the open interval `(n, n+1)`, so each midpoint value is at most the integral of `f`
over that interval; the intervals telescope and the improper integral over `(0,∞)` equals
`π/√(m+½) = π · w m`.  The singularity of `f` at the origin is integrable, which is why the midpoint
comparison is used in its open-interval form.
-/

open MeasureTheory Set

namespace GaloisForLFunctions

noncomputable section

/-! ## Integrability of the comparison kernel -/

/-- The comparison kernel is integrable on the positive half-line: its arctangent antiderivative is
continuous at the origin, has it as derivative, and converges at infinity. -/
theorem integrableOn_one_div_add_mul_sqrt {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => 1 / ((a + t) * Real.sqrt t)) (Ioi 0) volume := by
  have hcont : ContinuousWithinAt
      (fun t : ℝ => 2 / Real.sqrt a * Real.arctan (Real.sqrt t / Real.sqrt a))
      (Ici (0:ℝ)) 0 := by
    have hc : Continuous fun t : ℝ =>
        2 / Real.sqrt a * Real.arctan (Real.sqrt t / Real.sqrt a) := by fun_prop
    exact hc.continuousWithinAt
  exact integrableOn_Ioi_deriv_of_nonneg hcont
    (fun t ht => hasDerivAt_arctan_sqrt_div ha ht)
    (fun t ht => one_div_add_mul_sqrt_nonneg ha.le ht)
    (tendsto_arctan_sqrt_div_atTop ha)

/-- The comparison kernel is interval integrable on every interval inside `[0,∞)`. -/
theorem intervalIntegrable_one_div_add_mul_sqrt {a : ℝ} (ha : 0 < a) {c d : ℝ}
    (hc : 0 ≤ c) (hcd : c ≤ d) :
    IntervalIntegrable (fun t : ℝ => 1 / ((a + t) * Real.sqrt t)) volume c d := by
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hcd).mpr ?_
  refine (integrableOn_one_div_add_mul_sqrt ha).mono_set ?_
  intro t ht
  exact mem_Ioi.mpr (lt_of_le_of_lt hc ht.1)

/-! ## One unit interval -/

/-- **The midpoint value is at most the integral over a unit interval.**  The kernel is convex on the
open interval, which is all the midpoint rule needs. -/
theorem midpoint_le_integral_one_div_add_mul_sqrt {a : ℝ} (ha : 0 < a) {c : ℝ} (hc : 0 ≤ c) :
    1 / ((a + (c + 1 / 2)) * Real.sqrt (c + 1 / 2))
      ≤ ∫ t in c..(c + 1), 1 / ((a + t) * Real.sqrt t) := by
  have hconv : ConvexOn ℝ (Ioo c (c + 1)) (fun t : ℝ => 1 / ((a + t) * Real.sqrt t)) := by
    refine (convexOn_one_div_add_mul_sqrt ha.le).subset ?_ (convex_Ioo _ _)
    intro t ht
    exact mem_Ioi.mpr (lt_of_le_of_lt hc ht.1)
  have h := ConvexOn.midpoint_mul_le_integral_of_Ioo (by linarith : c ≤ c + 1) hconv
    (intervalIntegrable_one_div_add_mul_sqrt ha hc (by linarith))
  have hmid : (c + (c + 1)) / 2 = c + 1 / 2 := by ring
  have hlen : c + 1 - c = 1 := by ring
  rw [hmid, hlen, mul_one] at h
  exact h

/-! ## Telescoping the unit intervals -/

/-- The midpoint sum over the first `k` unit intervals is at most the integral over `(0,k)`. -/
theorem sum_midpoint_le_integral_one_div_add_mul_sqrt {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ∑ n ∈ Finset.range k, 1 / ((a + ((n : ℝ) + 1 / 2)) * Real.sqrt ((n : ℝ) + 1 / 2))
      ≤ ∫ t in (0:ℝ)..(k : ℝ), 1 / ((a + t) * Real.sqrt t) := by
  have hadj : ∀ i < k, IntervalIntegrable (fun t : ℝ => 1 / ((a + t) * Real.sqrt t)) volume
      ((i : ℕ) : ℝ) (((i + 1 : ℕ) : ℝ)) := by
    intro i _
    exact intervalIntegrable_one_div_add_mul_sqrt ha (by positivity) (by push_cast; linarith)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => (n : ℝ)) (f := fun t : ℝ => 1 / ((a + t) * Real.sqrt t)) hadj
  have hstep : ∀ n ∈ Finset.range k,
      1 / ((a + ((n : ℝ) + 1 / 2)) * Real.sqrt ((n : ℝ) + 1 / 2))
        ≤ ∫ t in ((n : ℕ) : ℝ)..(((n + 1 : ℕ) : ℝ)), 1 / ((a + t) * Real.sqrt t) := by
    intro n _
    have h := midpoint_le_integral_one_div_add_mul_sqrt ha
      (c := (n : ℝ)) (by positivity)
    have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    exact h
  calc ∑ n ∈ Finset.range k, 1 / ((a + ((n : ℝ) + 1 / 2)) * Real.sqrt ((n : ℝ) + 1 / 2))
      ≤ ∑ n ∈ Finset.range k,
          ∫ t in ((n : ℕ) : ℝ)..(((n + 1 : ℕ) : ℝ)), 1 / ((a + t) * Real.sqrt t) :=
        Finset.sum_le_sum hstep
    _ = ∫ t in ((0 : ℕ) : ℝ)..((k : ℕ) : ℝ), 1 / ((a + t) * Real.sqrt t) := hsum
    _ = ∫ t in (0:ℝ)..(k : ℝ), 1 / ((a + t) * Real.sqrt t) := by norm_num

/-- The integral over `(0,k)` is at most the improper integral `π/√a`. -/
theorem integral_le_pi_div_sqrt {a : ℝ} (ha : 0 < a) (k : ℕ) :
    (∫ t in (0:ℝ)..(k : ℝ), 1 / ((a + t) * Real.sqrt t)) ≤ Real.pi / Real.sqrt a := by
  have hle : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [intervalIntegral.integral_of_le hle]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] fun t : ℝ => 1 / ((a + t) * Real.sqrt t) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    filter_upwards with t ht using one_div_add_mul_sqrt_nonneg ha.le ht
  have hsub : (Ioc (0:ℝ) (k : ℝ)) ≤ᵐ[volume] (Ioi (0:ℝ)) :=
    Filter.Eventually.of_forall fun t ht => mem_Ioi.mpr ht.1
  have h := setIntegral_mono_set (integrableOn_one_div_add_mul_sqrt ha) hnn hsub
  rwa [integral_Ioi_one_div_add_mul_sqrt ha] at h

/-! ## The weighted row bound -/

/-- **The weighted row bound for the Hilbert–Hankel kernel over an initial segment.**  Each summand
is the midpoint value of the comparison kernel with `a = m + ½`. -/
theorem hilbert_weighted_row_range_bound (m k : ℕ) :
    ∑ n ∈ Finset.range k, 1 / (((m + n + 1 : ℕ) : ℝ) * Real.sqrt ((n : ℝ) + 1 / 2))
      ≤ Real.pi / Real.sqrt ((m : ℝ) + 1 / 2) := by
  have ha : (0:ℝ) < (m : ℝ) + 1 / 2 := by positivity
  have hterm : ∀ n ∈ Finset.range k,
      1 / (((m + n + 1 : ℕ) : ℝ) * Real.sqrt ((n : ℝ) + 1 / 2))
        = 1 / (((m : ℝ) + 1 / 2 + ((n : ℝ) + 1 / 2)) * Real.sqrt ((n : ℝ) + 1 / 2)) := by
    intro n _
    have hc : (((m + n + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 / 2 + ((n : ℝ) + 1 / 2) := by
      push_cast
      ring
    rw [hc]
  calc ∑ n ∈ Finset.range k, 1 / (((m + n + 1 : ℕ) : ℝ) * Real.sqrt ((n : ℝ) + 1 / 2))
      = ∑ n ∈ Finset.range k,
          1 / (((m : ℝ) + 1 / 2 + ((n : ℝ) + 1 / 2)) * Real.sqrt ((n : ℝ) + 1 / 2)) :=
        Finset.sum_congr rfl hterm
    _ ≤ ∫ t in (0:ℝ)..(k : ℝ), 1 / (((m : ℝ) + 1 / 2 + t) * Real.sqrt t) :=
        sum_midpoint_le_integral_one_div_add_mul_sqrt ha k
    _ ≤ Real.pi / Real.sqrt ((m : ℝ) + 1 / 2) := integral_le_pi_div_sqrt ha k

/-- **The weighted row bound over an arbitrary finite index set.**  All summands are nonnegative, so
the bound over an initial segment containing the set suffices. -/
theorem hilbert_weighted_row_bound (m : ℕ) (s : Finset ℕ) :
    ∑ n ∈ s, 1 / (((m + n + 1 : ℕ) : ℝ) * Real.sqrt ((n : ℝ) + 1 / 2))
      ≤ Real.pi / Real.sqrt ((m : ℝ) + 1 / 2) := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_range_sup_succ s) ?_)
    (hilbert_weighted_row_range_bound m _)
  intro i _ _
  positivity

/-! ## The norm bound -/

/-- **The Hilbert matrix has norm at most `π`.**  The absolute quadratic form of `1/(m+n+1)` on any
finitely supported real vector is at most `π` times its energy. -/
theorem hilbertAbsQuadraticForm_le_pi (b : ℕ →₀ ℝ) :
    ∑ m ∈ b.support, ∑ n ∈ b.support,
        |b m| * |b n| * (1 / (((m + n : ℕ) : ℝ) + 1))
      ≤ Real.pi * ∑ m ∈ b.support, (b m) ^ 2 := by
  classical
  set K : ℕ → ℕ → ℝ := fun r s => 1 / (((r + s : ℕ) : ℝ) + 1) with hK
  set w : ℕ → ℝ := fun r => (Real.sqrt ((r : ℝ) + 1 / 2))⁻¹ with hw
  have hwpos : ∀ r : ℕ, 0 < w r := by
    intro r
    have : (0:ℝ) < Real.sqrt ((r : ℝ) + 1 / 2) := Real.sqrt_pos.mpr (by positivity)
    simpa [hw] using inv_pos.mpr this
  have hKsymm : ∀ r s : ℕ, K r s = K s r := by
    intro r s
    rw [hK]
    simp only []
    rw [Nat.add_comm]
  have hKnn : ∀ r s : ℕ, 0 ≤ K r s := by
    intro r s
    have : (0:ℝ) ≤ ((r + s : ℕ) : ℝ) + 1 := by positivity
    simpa [hK] using div_nonneg zero_le_one this
  -- the weighted row sums, rewritten as the midpoint sums of the comparison kernel
  have hrowfinset : ∀ r : ℕ, ∑ n ∈ b.support, K r n * w n ≤ Real.pi * w r := by
    intro r
    have hterm : ∀ n ∈ b.support,
        K r n * w n = 1 / (((r + n + 1 : ℕ) : ℝ) * Real.sqrt ((n : ℝ) + 1 / 2)) := by
      intro n _
      have hs : (0:ℝ) < Real.sqrt ((n : ℝ) + 1 / 2) := Real.sqrt_pos.mpr (by positivity)
      have hc : (((r + n + 1 : ℕ) : ℝ)) = ((r + n : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hK, hw, hc]
      field_simp
    have hsum := hilbert_weighted_row_bound r b.support
    have hpi : Real.pi * w r = Real.pi / Real.sqrt ((r : ℝ) + 1 / 2) := by
      rw [hw]
      field_simp
    rw [Finset.sum_congr rfl hterm, hpi]
    exact hsum
  -- transport the Schur test from the support subtype to the support finset
  have hschur := weighted_double_sum_le_weightedRowBound
    (ι := ↥(b.support)) (b := fun r : ↥(b.support) => b r)
    (w := fun r : ↥(b.support) => w r) (H := Real.pi)
    (K := fun r s : ↥(b.support) => K r s)
    (fun r => hwpos r) (fun r s => hKsymm r s) (fun r s => hKnn r s) ?_
  · have hdouble : ∑ r : ↥(b.support), ∑ s : ↥(b.support), |b (r : ℕ)| * |b (s : ℕ)| * K r s
        = ∑ m ∈ b.support, ∑ n ∈ b.support, |b m| * |b n| * K m n := by
      rw [Finset.sum_coe_sort b.support
        (fun m => ∑ s : ↥(b.support), |b m| * |b (s : ℕ)| * K m s)]
      refine Finset.sum_congr rfl fun m _ => ?_
      exact Finset.sum_coe_sort b.support (fun n => |b m| * |b n| * K m n)
    calc ∑ m ∈ b.support, ∑ n ∈ b.support, |b m| * |b n| * (1 / (((m + n : ℕ) : ℝ) + 1))
        = ∑ r : ↥(b.support), ∑ s : ↥(b.support), |b (r : ℕ)| * |b (s : ℕ)| * K r s := hdouble.symm
      _ ≤ Real.pi * ∑ r : ↥(b.support), (b (r : ℕ)) ^ 2 := hschur
      _ = Real.pi * ∑ m ∈ b.support, (b m) ^ 2 := by
          rw [Finset.sum_coe_sort b.support (fun m => (b m) ^ 2)]
  · intro r
    have hle : ∑ s : ↥(b.support), K r s * w s ≤ ∑ n ∈ b.support, K r n * w n := by
      rw [Finset.sum_coe_sort b.support (fun n => K r n * w n)]
    exact hle.trans (hrowfinset r)

/-- The signed quadratic form obeys the same bound: the Hilbert matrix is bounded with norm at most
`π`. -/
theorem hilbertQuadraticForm_abs_le_pi (b : ℕ →₀ ℝ) :
    |∑ m ∈ b.support, ∑ n ∈ b.support, b m * b n * (1 / (((m + n : ℕ) : ℝ) + 1))|
      ≤ Real.pi * ∑ m ∈ b.support, (b m) ^ 2 := by
  refine le_trans (le_trans (Finset.abs_sum_le_sum_abs _ _) ?_) (hilbertAbsQuadraticForm_le_pi b)
  refine Finset.sum_le_sum fun m _ => ?_
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum fun n _ => ?_
  have hnn : (0:ℝ) ≤ 1 / (((m + n : ℕ) : ℝ) + 1) := by positivity
  rw [abs_mul, abs_mul, abs_of_nonneg hnn]

end

end GaloisForLFunctions
