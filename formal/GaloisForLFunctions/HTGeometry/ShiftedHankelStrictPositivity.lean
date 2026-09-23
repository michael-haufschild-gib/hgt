import GaloisForLFunctions.HTGeometry.StieltjesMomentProblem

/-!
# Strict positivity of shifted Hankel blocks from infinite support

For a positive measure on the nonnegative half line with all polynomial moments, the shifted
Hankel quadratic form is the weighted square integral

`∑ᵢⱼ cᵢ cⱼ m_{i+j}^{(r)} = ∫ xʳ p(x)² dμ`,   `p = ∑ᵢ cᵢ Xⁱ`.

A nonzero `p` of degree at most `d` has at most `d` roots, so if the measure charges every
neighbourhood of `d+1` distinct positive points, the integrand is strictly positive on a
neighbourhood of one of them and the block is positive definite.  Contrapositively, a singular
shifted block forces the measure to miss one of any `d+1` prescribed positive points: singular
finite Schur branches are finite-support artifacts.
-/

open scoped BigOperators
open MeasureTheory Polynomial Matrix

noncomputable section

namespace HTGeometry

/-- The shifted moment `∫ x^{n+r} dμ`. -/
def shiftedMomentOf (μ : Measure ℝ) (r n : ℕ) : ℝ := ∫ x, x ^ (n + r) ∂μ

/-- The coefficient polynomial of a coefficient vector. -/
def coeffPolyOf {d : ℕ} (c : Fin (d + 1) → ℝ) : Polynomial ℝ :=
  ∑ i : Fin (d + 1), Polynomial.C (c i) * X ^ (i : ℕ)

theorem coeffPolyOf_eval {d : ℕ} (c : Fin (d + 1) → ℝ) (x : ℝ) :
    (coeffPolyOf c).eval x = ∑ i : Fin (d + 1), c i * x ^ (i : ℕ) := by
  rw [coeffPolyOf, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl (fun i _ => by simp)

theorem coeffPolyOf_coeff {d : ℕ} (c : Fin (d + 1) → ℝ) (j : Fin (d + 1)) :
    (coeffPolyOf c).coeff (j : ℕ) = c j := by
  classical
  rw [coeffPolyOf, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have hne : (j : ℕ) ≠ (i : ℕ) := fun h => hij (Fin.ext h.symm)
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem coeffPolyOf_ne_zero {d : ℕ} {c : Fin (d + 1) → ℝ} (hc : c ≠ 0) :
    coeffPolyOf c ≠ 0 := by
  intro h0
  refine hc (funext fun j => ?_)
  have := coeffPolyOf_coeff c j
  rw [h0] at this
  simpa using this.symm

theorem coeffPolyOf_natDegree_le {d : ℕ} (c : Fin (d + 1) → ℝ) :
    (coeffPolyOf c).natDegree ≤ d := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ => ?_)
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  simp only [Polynomial.natDegree_X_pow]
  exact Nat.lt_succ_iff.mp i.2

/-- Expanding the weighted square. -/
theorem shiftedSquare_expand {d : ℕ} (c : Fin (d + 1) → ℝ) (r : ℕ) (x : ℝ) :
    x ^ r * ((coeffPolyOf c).eval x) ^ (2 : ℕ) =
      ∑ i : Fin (d + 1), ∑ j : Fin (d + 1), c i * c j * x ^ ((i : ℕ) + (j : ℕ) + r) := by
  rw [coeffPolyOf_eval, pow_two, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [pow_add, pow_add]
  ring

theorem integrable_shiftedSquare {μ : Measure ℝ} {d : ℕ} (c : Fin (d + 1) → ℝ) (r : ℕ)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ) :
    Integrable (fun x : ℝ => x ^ r * ((coeffPolyOf c).eval x) ^ (2 : ℕ)) μ := by
  have hEq : (fun x : ℝ => x ^ r * ((coeffPolyOf c).eval x) ^ (2 : ℕ)) =
      fun x : ℝ => ∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
        c i * c j * x ^ ((i : ℕ) + (j : ℕ) + r) :=
    funext (fun x => shiftedSquare_expand c r x)
  rw [hEq]
  exact MeasureTheory.integrable_finsetSum _ (fun i _ =>
    MeasureTheory.integrable_finsetSum _ (fun j _ => (hint _).const_mul _))

/-- The shifted Hankel quadratic form is the weighted square integral. -/
theorem quadForm_shiftedMomentOf (μ : Measure ℝ) (r d : ℕ) (c : Fin (d + 1) → ℝ)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ) :
    ∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
        c i * c j * shiftedMomentOf μ r ((i : ℕ) + (j : ℕ)) =
      ∫ x, x ^ r * ((coeffPolyOf c).eval x) ^ (2 : ℕ) ∂μ := by
  have hIij : ∀ i j : Fin (d + 1),
      Integrable (fun x : ℝ => c i * c j * x ^ ((i : ℕ) + (j : ℕ) + r)) μ :=
    fun i j => (hint _).const_mul _
  calc ∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
        c i * c j * shiftedMomentOf μ r ((i : ℕ) + (j : ℕ))
      = ∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
          ∫ x, c i * c j * x ^ ((i : ℕ) + (j : ℕ) + r) ∂μ := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [MeasureTheory.integral_const_mul, shiftedMomentOf]
    _ = ∑ i : Fin (d + 1),
          ∫ x, (∑ j : Fin (d + 1), c i * c j * x ^ ((i : ℕ) + (j : ℕ) + r)) ∂μ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [MeasureTheory.integral_finsetSum _ (fun j _ => hIij i j)]
    _ = ∫ x, (∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
          c i * c j * x ^ ((i : ℕ) + (j : ℕ) + r)) ∂μ := by
        rw [MeasureTheory.integral_finsetSum _ (fun i _ =>
          MeasureTheory.integrable_finsetSum _ (fun j _ => hIij i j))]
    _ = ∫ x, x ^ r * ((coeffPolyOf c).eval x) ^ (2 : ℕ) ∂μ := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        exact (shiftedSquare_expand c r x).symm

/-- **Strict positivity of the shifted Hankel block.**  If the measure charges every neighbourhood
of `d+1` distinct positive points, its shifted Hankel block of size `d+1` is positive definite. -/
theorem shiftedHankel_quadForm_pos {μ : Measure ℝ} {r d : ℕ} {c : Fin (d + 1) → ℝ} (hc : c ≠ 0)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ)
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x)
    (x : Fin (d + 1) → ℝ) (hxpos : ∀ k, 0 < x k) (hxinj : Function.Injective x)
    (hsupp : ∀ k, ∀ ε > 0, 0 < μ (Metric.ball (x k) ε)) :
    0 < ∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
      c i * c j * shiftedMomentOf μ r ((i : ℕ) + (j : ℕ)) := by
  classical
  have hpne : coeffPolyOf c ≠ 0 := coeffPolyOf_ne_zero hc
  have hpdeg : (coeffPolyOf c).natDegree ≤ d := coeffPolyOf_natDegree_le c
  obtain ⟨k, hk⟩ : ∃ k, (coeffPolyOf c).eval (x k) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ.image x) ⊆ (coeffPolyOf c).roots.toFinset := by
      intro y hy
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hy
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hpne).mpr (hall k))
    have hcard : (Finset.univ.image x).card = d + 1 := by
      rw [Finset.card_image_of_injective _ hxinj, Finset.card_univ, Fintype.card_fin]
    have hle : (d + 1 : ℕ) ≤ (coeffPolyOf c).roots.toFinset.card := by
      rw [← hcard]
      exact Finset.card_le_card hsub
    have hroots : (coeffPolyOf c).roots.toFinset.card ≤ (coeffPolyOf c).natDegree :=
      le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' _)
    omega
  have hfint : Integrable (fun y : ℝ => y ^ r * ((coeffPolyOf c).eval y) ^ (2 : ℕ)) μ :=
    integrable_shiftedSquare c r hint
  have hfnonneg : 0 ≤ᵐ[μ] fun y : ℝ => y ^ r * ((coeffPolyOf c).eval y) ^ (2 : ℕ) := by
    filter_upwards [hμ] with y hy
    exact mul_nonneg (pow_nonneg hy r) (sq_nonneg _)
  have hfcont : Continuous fun y : ℝ => y ^ r * ((coeffPolyOf c).eval y) ^ (2 : ℕ) :=
    (continuous_pow r).mul ((coeffPolyOf c).continuous.pow 2)
  have hfk : 0 < (x k) ^ r * ((coeffPolyOf c).eval (x k)) ^ (2 : ℕ) :=
    mul_pos (pow_pos (hxpos k) r) (sq_pos_of_ne_zero hk)
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ y ∈ Metric.ball (x k) δ,
      0 < y ^ r * ((coeffPolyOf c).eval y) ^ (2 : ℕ) := by
    have hopen : IsOpen {y : ℝ | 0 < y ^ r * ((coeffPolyOf c).eval y) ^ (2 : ℕ)} :=
      isOpen_lt continuous_const hfcont
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hopen (x k) hfk
    exact ⟨δ, hδ, fun y hy => hsub hy⟩
  have hsuppsub : Metric.ball (x k) δ ⊆
      Function.support fun y : ℝ => y ^ r * ((coeffPolyOf c).eval y) ^ (2 : ℕ) :=
    fun y hy => ne_of_gt (hball y hy)
  have hmpos : 0 < μ (Function.support fun y : ℝ => y ^ r * ((coeffPolyOf c).eval y) ^ (2 : ℕ)) :=
    lt_of_lt_of_le (hsupp k δ hδ) (measure_mono hsuppsub)
  rw [quadForm_shiftedMomentOf μ r d c hint]
  exact (integral_pos_iff_support_of_nonneg_ae hfnonneg hfint).mpr hmpos

/-! ### Matrix form -/

/-- The shifted Hankel block `H_r(d) = [m_{i+j}^{(r)}]`. -/
def shiftedHankelMatrixOf (μ : Measure ℝ) (r d : ℕ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => shiftedMomentOf μ r ((i : ℕ) + (j : ℕ))

theorem shiftedHankelMatrixOf_isHermitian (μ : Measure ℝ) (r d : ℕ) :
    (shiftedHankelMatrixOf μ r d).IsHermitian := by
  refine Matrix.IsHermitian.ext (fun i j => ?_)
  simp only [shiftedHankelMatrixOf, star_trivial]
  rw [Nat.add_comm]

theorem dotProduct_mulVec_shiftedHankelMatrixOf (μ : Measure ℝ) (r d : ℕ)
    (c : Fin (d + 1) → ℝ) :
    c ⬝ᵥ ((shiftedHankelMatrixOf μ r d) *ᵥ c) =
      ∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
        c i * c j * shiftedMomentOf μ r ((i : ℕ) + (j : ℕ)) := by
  simp only [dotProduct, Matrix.mulVec, shiftedHankelMatrixOf, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

/-- **Infinite support gives strict shifted Hankel blocks.**  If the measure charges every
neighbourhood of `d+1` distinct positive points, the shifted Hankel block of size `d+1` is
positive definite. -/
theorem shiftedHankelMatrixOf_posDef {μ : Measure ℝ} {r d : ℕ}
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ)
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x)
    (x : Fin (d + 1) → ℝ) (hxpos : ∀ k, 0 < x k) (hxinj : Function.Injective x)
    (hsupp : ∀ k, ∀ ε > 0, 0 < μ (Metric.ball (x k) ε)) :
    (shiftedHankelMatrixOf μ r d).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (shiftedHankelMatrixOf_isHermitian μ r d) (fun c hc => ?_)
  rw [star_trivial, dotProduct_mulVec_shiftedHankelMatrixOf]
  exact shiftedHankel_quadForm_pos hc hint hμ x hxpos hxinj hsupp

/-- **Contrapositive: a singular block forces a thin support.**  If the shifted Hankel block of
size `d+1` fails to be positive definite, then no `d+1` distinct positive points are all charged
by the measure. -/
theorem not_forall_charged_of_not_posDef {μ : Measure ℝ} {r d : ℕ}
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ)
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x)
    (hns : ¬ (shiftedHankelMatrixOf μ r d).PosDef)
    (x : Fin (d + 1) → ℝ) (hxpos : ∀ k, 0 < x k) (hxinj : Function.Injective x) :
    ∃ k, ∃ ε > 0, μ (Metric.ball (x k) ε) = 0 := by
  by_contra hall
  push Not at hall
  refine hns (shiftedHankelMatrixOf_posDef hint hμ x hxpos hxinj (fun k ε hε => ?_))
  exact pos_iff_ne_zero.mpr (hall k ε hε)

end HTGeometry
