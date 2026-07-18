import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Group.InfiniteSum
import GaloisForLFunctions.RHTower.ArcsineZetaDerivativeSpectrum

/-!
# The arithmetic dilation matrix has a projective diagonal limit

The finite-aperture von Mangoldt dilation matrix of the constrained prolate source is the
symmetrization

```text
A(j,k) = (a j + a k) · G(j,k)
```

of a radial Gram matrix `G` by the truncated divisor weights `a`.  Suppose that, after
normalization by the leakage scale, `G` converges to a diagonal `w` in the *weighted* projective
norm with logarithmic weights `Ω`, and that the divisor weights are trapped between `0` and their
limit `L` while stabilizing at every fixed index.  Then `A` converges to the diagonal
`κ k = 2 · L k · w k` in the plain projective norm.

The mechanism is a two-term split: the weighted hypothesis absorbs the factor `a j + a k ≤ Ω j +
Ω k` off the diagonal, and the remaining diagonal discrepancy `2 |L k − a k| w k` is dominated by
the summable `2 L k w k` and vanishes at every fixed index, so a tail-truncation argument sends it
to zero.

Because the projective norm dominates the trace norm and permits pairing with the all-ones matrix,
the total mass converges as well: the raw prime charge `−∑_{j,k} A(j,k)` converges to the negative
trace `−∑_k κ k`.  Specialized to the constrained prolate radial source, `κ` is exactly
`constrainedProlateArithmeticEigenvalue`.
-/

open Filter

noncomputable section

namespace RHTower

/-! ## Diagonal matrices on `ℕ × ℕ` -/

/-- The matrix on `ℕ × ℕ` supported on the diagonal with entries `g`. -/
def diagMatrix (g : ℕ → ℝ) (p : ℕ × ℕ) : ℝ := if p.1 = p.2 then g p.2 else 0

theorem injective_diagEmbed : Function.Injective (fun k : ℕ => (k, k)) := by
  intro m n h
  simpa using congrArg Prod.fst h

theorem diagMatrix_support (g : ℕ → ℝ) :
    Function.support (diagMatrix g) ⊆ Set.range (fun k : ℕ => (k, k)) := by
  intro p hp
  by_cases h : p.1 = p.2
  · refine ⟨p.2, ?_⟩
    exact Prod.ext h.symm rfl
  · exact absurd (if_neg h) hp

theorem diagMatrix_comp (g : ℕ → ℝ) (k : ℕ) : diagMatrix g (k, k) = g k := by
  simp [diagMatrix]

theorem summable_diagMatrix {g : ℕ → ℝ} (hg : Summable g) : Summable (diagMatrix g) := by
  refine (Function.Injective.summable_iff injective_diagEmbed ?_).1 ?_
  · intro p hp
    by_cases h : p.1 = p.2
    · exact absurd ⟨p.2, Prod.ext h.symm rfl⟩ hp
    · simp [diagMatrix, h]
  · simpa [Function.comp_def, diagMatrix] using hg

theorem tsum_diagMatrix (g : ℕ → ℝ) : ∑' p : ℕ × ℕ, diagMatrix g p = ∑' k : ℕ, g k := by
  rw [← Function.Injective.tsum_eq injective_diagEmbed (diagMatrix_support g)]
  simp [diagMatrix]

/-- The triangle inequality for an absolutely convergent real series. -/
theorem abs_tsum_le_tsum_abs {ι : Type*} (f : ι → ℝ) (hf : Summable fun i => |f i|) :
    |∑' i, f i| ≤ ∑' i, |f i| := by
  have hn : Summable fun i => ‖f i‖ := by simpa [Real.norm_eq_abs] using hf
  simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hn

/-! ## A tail-truncation limit -/

/-- A nonnegative family dominated by a fixed summable sequence, and eventually zero at every
fixed index, has total mass tending to zero.  Splitting the series at a tail cut chosen from the
dominating sequence reduces the statement to finitely many indices, each of which vanishes
eventually. -/
theorem tendsto_tsum_of_eventually_pointwise_zero
    {α : Type*} {l : Filter α} {f : α → ℕ → ℝ} {h : ℕ → ℝ}
    (hf0 : ∀ x k, 0 ≤ f x k) (hfh : ∀ x k, f x k ≤ h k)
    (hh : Summable h) (hev : ∀ k, ∀ᶠ x in l, f x k = 0) :
    Tendsto (fun x => ∑' k : ℕ, f x k) l (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∑' i : ℕ, h (i + N) < ε := by
    have hlim := tendsto_sum_nat_add h
    exact ((hlim.eventually (eventually_lt_nhds hε)).exists)
  have hzero : ∀ᶠ x in l, ∀ k ∈ Finset.range N, f x k = 0 :=
    (eventually_all_finset (Finset.range N)).2 (fun k _ => hev k)
  filter_upwards [hzero] with x hx
  have hsum : Summable (f x) := hh.of_nonneg_of_le (hf0 x) (hfh x)
  have hfin : ∑ i ∈ Finset.range N, f x i = 0 := Finset.sum_eq_zero hx
  have hsplit := hsum.sum_add_tsum_nat_add N
  have heq : ∑' i : ℕ, f x i = ∑' i : ℕ, f x (i + N) := by
    rw [← hsplit, hfin, zero_add]
  have hle : ∑' i : ℕ, f x (i + N) ≤ ∑' i : ℕ, h (i + N) :=
    Summable.tsum_le_tsum (fun i => hfh x (i + N))
      ((summable_nat_add_iff N).2 hsum) ((summable_nat_add_iff N).2 hh)
  have hnn : 0 ≤ ∑' i : ℕ, f x i := tsum_nonneg (fun i => hf0 x i)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn, heq]
  linarith

/-! ## The projective arithmetic limit -/

section Projective

variable {α : Type*} {l : Filter α} {E : α → ℕ → ℕ → ℝ} {w L Ω : ℕ → ℝ} {a : α → ℕ → ℝ}

/-- The pointwise projective bound: the discrepancy of the symmetrized arithmetic matrix from its
limiting diagonal is bounded by the weighted Gram discrepancy plus the diagonal divisor defect. -/
theorem arithmeticDilation_abs_le
    (hw : ∀ k, 0 ≤ w k) (hΩ : ∀ k, L k ≤ Ω k)
    (ha0 : ∀ x k, 0 ≤ a x k) (haL : ∀ x k, a x k ≤ L k)
    (x : α) (p : ℕ × ℕ) :
    |(a x p.1 + a x p.2) * (E x p.1 p.2 + diagMatrix w p)
        - diagMatrix (fun k => 2 * L k * w k) p|
      ≤ (Ω p.1 + Ω p.2) * |E x p.1 p.2|
        + diagMatrix (fun k => 2 * (L k - a x k) * w k) p := by
  have haΩ : ∀ k, a x k ≤ Ω k := fun k => le_trans (haL x k) (hΩ k)
  by_cases h : p.1 = p.2
  · simp only [diagMatrix, if_pos h]
    rw [h]
    set k := p.2 with hk
    have hLa : 0 ≤ L k - a x k := sub_nonneg.2 (haL x k)
    have hY : 0 ≤ 2 * (L k - a x k) * w k :=
      mul_nonneg (by linarith) (hw k)
    have h2a : (0 : ℝ) ≤ 2 * a x k := by linarith [ha0 x k]
    have heq : (a x k + a x k) * (E x k k + w k) - 2 * L k * w k
        = 2 * a x k * E x k k + -(2 * (L k - a x k) * w k) := by ring
    rw [heq]
    calc |2 * a x k * E x k k + -(2 * (L k - a x k) * w k)|
        ≤ |2 * a x k * E x k k| + |-(2 * (L k - a x k) * w k)| := abs_add_le _ _
      _ = 2 * a x k * |E x k k| + 2 * (L k - a x k) * w k := by
            rw [abs_neg, abs_mul, abs_of_nonneg h2a, abs_of_nonneg hY]
      _ ≤ (Ω k + Ω k) * |E x k k| + 2 * (L k - a x k) * w k := by
            have hle : 2 * a x k ≤ Ω k + Ω k := by linarith [haΩ k]
            nlinarith [abs_nonneg (E x k k)]
  · simp only [diagMatrix, if_neg h, add_zero, sub_zero]
    have hnn : (0 : ℝ) ≤ a x p.1 + a x p.2 := by linarith [ha0 x p.1, ha0 x p.2]
    rw [abs_mul, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_right (add_le_add (haΩ p.1) (haΩ p.2)) (abs_nonneg _)

/-- **The arithmetic projective limit.**  Weighted projective convergence of the normalized Gram
matrix to a diagonal, together with divisor weights trapped below their pointwise-stabilizing
limit, forces the symmetrized arithmetic dilation matrix to converge to the diagonal
`κ k = 2 L k w k` in the plain projective norm. -/
theorem arithmeticDilation_projective_tendsto
    (hw : ∀ k, 0 ≤ w k) (hΩ : ∀ k, L k ≤ Ω k)
    (ha0 : ∀ x k, 0 ≤ a x k) (haL : ∀ x k, a x k ≤ L k)
    (haev : ∀ k, ∀ᶠ x in l, a x k = L k)
    (hLw : Summable fun k => L k * w k)
    (hEsum : ∀ x, Summable fun p : ℕ × ℕ => (Ω p.1 + Ω p.2) * |E x p.1 p.2|)
    (hE : Tendsto (fun x => ∑' p : ℕ × ℕ, (Ω p.1 + Ω p.2) * |E x p.1 p.2|) l (nhds 0)) :
    Tendsto (fun x => ∑' p : ℕ × ℕ,
        |(a x p.1 + a x p.2) * (E x p.1 p.2 + diagMatrix w p)
          - diagMatrix (fun k => 2 * L k * w k) p|) l (nhds 0) := by
  have hbound := arithmeticDilation_abs_le (E := E) hw hΩ ha0 haL
  -- the diagonal defect series
  have hdef0 : ∀ x k, 0 ≤ 2 * (L k - a x k) * w k := fun x k =>
    mul_nonneg (by linarith [haL x k]) (hw k)
  have hdefle : ∀ x k, 2 * (L k - a x k) * w k ≤ 2 * (L k * w k) := fun x k => by
    have := mul_nonneg (ha0 x k) (hw k)
    nlinarith [hw k, ha0 x k]
  have hdefsum : Summable fun k => 2 * (L k * w k) := hLw.mul_left 2
  have hdeftend : Tendsto (fun x => ∑' k : ℕ, 2 * (L k - a x k) * w k) l (nhds 0) := by
    refine tendsto_tsum_of_eventually_pointwise_zero hdef0 hdefle hdefsum ?_
    intro k
    filter_upwards [haev k] with x hx
    rw [hx]
    ring
  -- summability of the bounding family
  have hBsum : ∀ x, Summable (fun p : ℕ × ℕ =>
      (Ω p.1 + Ω p.2) * |E x p.1 p.2|
        + diagMatrix (fun k => 2 * (L k - a x k) * w k) p) := fun x =>
    (hEsum x).add (summable_diagMatrix
      (hdefsum.of_nonneg_of_le (fun k => hdef0 x k) (fun k => hdefle x k)))
  have hDsum : ∀ x, Summable (fun p : ℕ × ℕ =>
      |(a x p.1 + a x p.2) * (E x p.1 p.2 + diagMatrix w p)
        - diagMatrix (fun k => 2 * L k * w k) p|) := fun x =>
    (hBsum x).of_nonneg_of_le (fun p => abs_nonneg _) (fun p => hbound x p)
  -- the bounding total mass tends to zero
  have hBtend : Tendsto (fun x => ∑' p : ℕ × ℕ,
      ((Ω p.1 + Ω p.2) * |E x p.1 p.2|
        + diagMatrix (fun k => 2 * (L k - a x k) * w k) p)) l (nhds 0) := by
    have hsplit : ∀ x, (∑' p : ℕ × ℕ,
        ((Ω p.1 + Ω p.2) * |E x p.1 p.2|
          + diagMatrix (fun k => 2 * (L k - a x k) * w k) p))
        = (∑' p : ℕ × ℕ, (Ω p.1 + Ω p.2) * |E x p.1 p.2|)
          + ∑' k : ℕ, 2 * (L k - a x k) * w k := by
      intro x
      rw [Summable.tsum_add (hEsum x) (summable_diagMatrix
        (hdefsum.of_nonneg_of_le (fun k => hdef0 x k) (fun k => hdefle x k))),
        tsum_diagMatrix]
    simp only [hsplit]
    simpa using hE.add hdeftend
  refine squeeze_zero (fun x => tsum_nonneg (fun p => abs_nonneg _)) (fun x => ?_) hBtend
  exact Summable.tsum_le_tsum (fun p => hbound x p) (hDsum x) (hBsum x)

/-- **Recovery of the total charge as a trace.**  Projective convergence permits pairing with the
all-ones matrix, so the total mass of the arithmetic dilation matrix converges to the trace of
its limiting diagonal. -/
theorem arithmeticDilation_total_tendsto
    (hw : ∀ k, 0 ≤ w k) (hΩ : ∀ k, L k ≤ Ω k)
    (ha0 : ∀ x k, 0 ≤ a x k) (haL : ∀ x k, a x k ≤ L k)
    (haev : ∀ k, ∀ᶠ x in l, a x k = L k)
    (hLw : Summable fun k => L k * w k)
    (hEsum : ∀ x, Summable fun p : ℕ × ℕ => (Ω p.1 + Ω p.2) * |E x p.1 p.2|)
    (hE : Tendsto (fun x => ∑' p : ℕ × ℕ, (Ω p.1 + Ω p.2) * |E x p.1 p.2|) l (nhds 0)) :
    Tendsto (fun x => ∑' p : ℕ × ℕ,
        (a x p.1 + a x p.2) * (E x p.1 p.2 + diagMatrix w p)) l
      (nhds (∑' k : ℕ, 2 * L k * w k)) := by
  have hproj := arithmeticDilation_projective_tendsto hw hΩ ha0 haL haev hLw hEsum hE
  have hbound := arithmeticDilation_abs_le (E := E) hw hΩ ha0 haL
  have hdef0 : ∀ x k, 0 ≤ 2 * (L k - a x k) * w k := fun x k =>
    mul_nonneg (by linarith [haL x k]) (hw k)
  have hdefle : ∀ x k, 2 * (L k - a x k) * w k ≤ 2 * (L k * w k) := fun x k => by
    nlinarith [hw k, ha0 x k, mul_nonneg (ha0 x k) (hw k)]
  have hdefsum : Summable fun k => 2 * (L k * w k) := hLw.mul_left 2
  have hBsum : ∀ x, Summable (fun p : ℕ × ℕ =>
      (Ω p.1 + Ω p.2) * |E x p.1 p.2|
        + diagMatrix (fun k => 2 * (L k - a x k) * w k) p) := fun x =>
    (hEsum x).add (summable_diagMatrix
      (hdefsum.of_nonneg_of_le (fun k => hdef0 x k) (fun k => hdefle x k)))
  have hDabs : ∀ x, Summable (fun p : ℕ × ℕ =>
      |(a x p.1 + a x p.2) * (E x p.1 p.2 + diagMatrix w p)
        - diagMatrix (fun k => 2 * L k * w k) p|) := fun x =>
    (hBsum x).of_nonneg_of_le (fun p => abs_nonneg _) (fun p => hbound x p)
  have hDiff : ∀ x, Summable (fun p : ℕ × ℕ =>
      (a x p.1 + a x p.2) * (E x p.1 p.2 + diagMatrix w p)
        - diagMatrix (fun k => 2 * L k * w k) p) := fun x => (hDabs x).of_abs
  have hκsum : Summable (diagMatrix fun k => 2 * L k * w k) :=
    summable_diagMatrix (by simpa [mul_assoc] using hLw.mul_left 2)
  -- the difference tends to zero because its absolute total mass does
  have hdiffzero : Tendsto (fun x => ∑' p : ℕ × ℕ,
      ((a x p.1 + a x p.2) * (E x p.1 p.2 + diagMatrix w p)
        - diagMatrix (fun k => 2 * L k * w k) p)) l (nhds 0) := by
    refine squeeze_zero_norm (fun x => ?_) hproj
    rw [Real.norm_eq_abs]
    exact abs_tsum_le_tsum_abs _ (hDabs x)
  have hrewrite : ∀ x, (∑' p : ℕ × ℕ, (a x p.1 + a x p.2) * (E x p.1 p.2 + diagMatrix w p))
      = (∑' p : ℕ × ℕ, ((a x p.1 + a x p.2) * (E x p.1 p.2 + diagMatrix w p)
          - diagMatrix (fun k => 2 * L k * w k) p)) + ∑' k : ℕ, 2 * L k * w k := by
    intro x
    rw [← tsum_diagMatrix (fun k => 2 * L k * w k), ← Summable.tsum_add (hDiff x) hκsum]
    exact tsum_congr (fun p => by ring)
  simp only [hrewrite]
  simpa using hdiffzero.add_const (∑' k : ℕ, 2 * L k * w k)

end Projective

/-! ## The constrained prolate specialization -/

/-- The limiting arithmetic eigenvalue is `2 · log k · w k` for the radial leakage diagonal
`w k = (8/(11π)) · arcsin(1/k)/k`, with paper index `k = n + 2`. -/
theorem constrainedProlateArithmeticEigenvalue_eq_two_mul_log_mul (n : ℕ) :
    GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n
      = 2 * Real.log ((n + 2 : ℕ) : ℝ)
        * ((8 / (11 * Real.pi))
            * (Real.arcsin (1 / ((n + 2 : ℕ) : ℝ)) / ((n + 2 : ℕ) : ℝ))) := by
  show (16 / (11 * Real.pi))
      * (Real.log ((n + 2 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)
          * Real.arcsin (1 / ((n + 2 : ℕ) : ℝ))) = _
  ring

end RHTower
