import GaloisForLFunctions.HTGeometry.PaperRotationClosedAlgebra
import GaloisForLFunctions.HTGeometry.PhaseResonanceProjection
import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# Canonical trace on the concrete rotation algebra

A fixed ultrafilter limit of bounded diagonal means defines a continuous
positive linear functional on the ambient operators. Its restriction to the
norm-closed rotation algebra is normalized and cyclic. Its Weyl-word values
are determined by ordinary Cesaro limits and determine the restriction
uniquely, independently of the ultrafilter. For an infinite-order clock they
are the Laurent constant coefficient.

Finite Weyl spans are proved to be star algebras with exactly the existing
rotation algebra as norm closure. This supplies the density argument for
cyclicity; no trace-existence or trace-range premise is introduced. No Xi
projective source or Riemann-hypothesis conclusion is asserted here.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter Topology
local notation "RotOp" => PaperRotationHilbert →L[ℂ] PaperRotationHilbert

/-- Mean of diagonal coefficients on the first `N` nonnegative basis vectors. -/
def paperRotationDiagonalMean (N : ℕ) : RotOp →ₗ[ℂ] ℂ where
  toFun A := (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
    (A (lp.single (E := fun _ : ℤ => ℂ) 2 (n : ℤ) (1 : ℂ))) (n : ℤ)
  map_add' A B := by simp [Finset.sum_add_distrib, mul_add]
  map_smul' c A := by simp [Finset.mul_sum, mul_left_comm]

private theorem diagonal_bound (A : RotOp) (n : ℤ) :
    ‖(A (lp.single (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ))) n‖ ≤ ‖A‖ := by
  calc
    _ ≤ ‖A (lp.single (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ))‖ := lp.norm_apply_le_norm (by norm_num) _ _
    _ ≤ ‖A‖ * ‖lp.single (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ)‖ := A.le_opNorm _
    _ = ‖A‖ := by rw [lp.norm_single (E := fun _ : ℤ => ℂ) (p := 2) (by norm_num), norm_one, mul_one]

theorem paperRotationDiagonalMean_bound (N : ℕ) (A : RotOp) :
    ‖paperRotationDiagonalMean N A‖ ≤ ‖A‖ := by
  by_cases hN : N = 0
  · subst N; simp [paperRotationDiagonalMean]
  change ‖(N : ℂ)⁻¹ * _‖ ≤ _
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hp : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  rw [inv_mul_le_iff₀ hp]
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖(A (lp.single (E := fun _ : ℤ => ℂ) 2 (n : ℤ) (1 : ℂ))) (n : ℤ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range N, ‖A‖ := Finset.sum_le_sum fun n _ => diagonal_bound A n
    _ = (N : ℝ) * ‖A‖ := by simp

private def traceFilter : Ultrafilter ℕ := Ultrafilter.of atTop

private theorem trace_limit_exists (A : RotOp) :
    ∃ z : ℂ, Tendsto (fun N => paperRotationDiagonalMean N A)
      (traceFilter : Filter ℕ) (𝓝 z) := by
  have hm : ((Ultrafilter.map (fun N => paperRotationDiagonalMean N A) traceFilter) : Filter ℂ)
      ≤ 𝓟 (Metric.closedBall 0 ‖A‖) := by
    rw [le_principal_iff]
    change ∀ᶠ N : ℕ in (traceFilter : Filter ℕ), paperRotationDiagonalMean N A ∈ Metric.closedBall 0 ‖A‖
    exact Eventually.of_forall fun N => by
      simpa only [Metric.mem_closedBall, dist_zero_right] using paperRotationDiagonalMean_bound N A
  obtain ⟨z, _, hz⟩ := (isCompact_closedBall (0 : ℂ) ‖A‖).ultrafilter_le_nhds _ hm
  exact ⟨z, hz⟩

private def traceValue (A : RotOp) : ℂ :=
  limUnder (traceFilter : Filter ℕ) (fun N => paperRotationDiagonalMean N A)

private theorem traceValue_tendsto (A : RotOp) :
    Tendsto (fun N => paperRotationDiagonalMean N A) (traceFilter : Filter ℕ)
      (𝓝 (traceValue A)) := tendsto_nhds_limUnder (trace_limit_exists A)

private theorem traceValue_bound (A : RotOp) : ‖traceValue A‖ ≤ ‖A‖ :=
  le_of_tendsto (traceValue_tendsto A).norm (Eventually.of_forall fun N =>
    paperRotationDiagonalMean_bound N A)

private def traceLinear : RotOp →ₗ[ℂ] ℂ where
  toFun := traceValue
  map_add' A B := by
    apply tendsto_nhds_unique (traceValue_tendsto (A + B))
    simpa only [map_add] using (traceValue_tendsto A).add (traceValue_tendsto B)
  map_smul' c A := by
    apply tendsto_nhds_unique (traceValue_tendsto (c • A))
    simpa only [map_smul, RingHom.id_apply] using (traceValue_tendsto A).const_smul c

/-- A bounded diagonal-mean functional on the full operator algebra. Its restriction to the
rotation algebra is the canonical trace. Cyclicity is asserted only on that subalgebra. -/
def paperRotationTrace : RotOp →L[ℂ] ℂ :=
  traceLinear.mkContinuous 1 (fun A => by simpa only [traceLinear, LinearMap.coe_mk, AddHom.coe_mk, one_mul] using traceValue_bound A)

theorem paperRotationTrace_bound (A : RotOp) : ‖paperRotationTrace A‖ ≤ ‖A‖ :=
  traceValue_bound A

private theorem trace_eq_of_tendsto (A : RotOp) (z : ℂ)
    (h : Tendsto (fun N => paperRotationDiagonalMean N A) atTop (𝓝 z)) :
    paperRotationTrace A = z :=
  tendsto_nhds_unique (traceValue_tendsto A) (h.mono_left (Ultrafilter.of_le atTop))

theorem paperRotationTrace_word (a : ℤ) (b : ℝ) :
    paperRotationTrace (paperRotationWord a b) =
      if a = 0 ∧ paperRotationPhase b = 1 then 1 else 0 := by
  apply trace_eq_of_tendsto
  by_cases ha : a = 0
  · subst a
    have he (N : ℕ) : paperRotationDiagonalMean N (paperRotationWord 0 b) =
        cesaroCoeff (paperRotationPhase b) N := by
      simp only [paperRotationDiagonalMean, LinearMap.coe_mk, AddHom.coe_mk,
        paperRotationWord_apply, sub_zero, lp.single_apply_self, mul_one, cesaroCoeff]
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      simp only [paperRotationPhase, Int.cast_natCast, mul_comm b, Circle.exp_natCast_mul, Circle.coe_pow]
    simp_rw [he]
    simpa only [true_and, eq_self] using tendsto_cesaroCoeff (paperRotationPhase_norm b)
  · have he (N : ℕ) : paperRotationDiagonalMean N (paperRotationWord a b) = 0 := by
      have hn (n : ℕ) : (n : ℤ) - a ≠ n := by omega
      simp [paperRotationDiagonalMean, paperRotationWord_apply, lp.single_apply,
        Pi.single_eq_of_ne (hn _)]
    simp only [he, ha, false_and, ↓reduceIte]
    exact tendsto_const_nhds

@[simp] theorem paperRotationTrace_one : paperRotationTrace 1 = 1 := by
  have h : paperRotationWord 0 0 = (1 : RotOp) := by
    simp only [paperRotationWord, paperRotationModulation_zero, paperRotationShift_zero, ContinuousLinearMap.id_comp]
    rfl
  simpa only [h, paperRotationPhase_zero, eq_self, and_self, ↓reduceIte] using
    paperRotationTrace_word 0 0


private theorem positive_diagonal (A : RotOp) (n : ℤ) :
    ((star A * A) (lp.single (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ))) n =
      (‖A (lp.single (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ))‖ ^ 2 : ℝ) := by
  have he (v : PaperRotationHilbert) :
      inner ℂ (lp.single (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ)) v = v n := by
    rw [lp.inner_single_left]
    simp
  rw [← he, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  norm_cast

private theorem diagonalMean_positive (N : ℕ) (A : RotOp) :
    0 ≤ (paperRotationDiagonalMean N (star A * A)).re := by
  change 0 ≤ ((N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
    ((star A * A) (lp.single (E := fun _ : ℤ => ℂ) 2 (n : ℤ) (1 : ℂ))) (n : ℤ)).re
  simp_rw [positive_diagonal]
  rw [← Complex.ofReal_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  positivity

/-- Positivity holds for every square in the ambient operator algebra. -/
theorem paperRotationTrace_positive (A : RotOp) :
    0 ≤ (paperRotationTrace (star A * A)).re := by
  exact ge_of_tendsto ((Complex.continuous_re.tendsto _).comp
    (traceValue_tendsto (star A * A)))
    (Eventually.of_forall fun N => diagonalMean_positive N A)

/-- The canonical word values are precisely the Laurent constant coefficient for an
infinite-order clock. -/
theorem paperRotationTrace_integer_word (t : ℝ)
    (ht : ∀ b : ℤ, paperRotationPhase ((b : ℝ) * t) = 1 ↔ b = 0) (a b : ℤ) :
    paperRotationTrace (paperRotationWord a ((b : ℝ) * t)) =
      if a = 0 ∧ b = 0 then 1 else 0 := by
  simp only [paperRotationTrace_word, ht]

/-- Every Weyl word is a unitary operator with the already constructed exact inverse. -/
def paperRotationWordEquiv (a : ℤ) (b : ℝ) :
    PaperRotationHilbert ≃ₗᵢ[ℂ] PaperRotationHilbert where
  toLinearEquiv :=
    { (paperRotationWord a b).toLinearMap with
      invFun := paperRotationWordUndo a b
      left_inv := fun v => by
        change (paperRotationWordUndo a b ∘L paperRotationWord a b) v = v
        rw [paperRotationWordUndo_left]; rfl
      right_inv := fun v => by
        change (paperRotationWord a b ∘L paperRotationWordUndo a b) v = v
        rw [paperRotationWordUndo_right]; rfl }
  norm_map' := paperRotationWord_norm a b

theorem paperRotationWord_star (a : ℤ) (b : ℝ) :
    star (paperRotationWord a b) =
      paperRotationPhase (-(a : ℝ) * b) • paperRotationWord (-a) (-b) := by
  have h : star (paperRotationWord a b) = paperRotationWordUndo a b :=
    (paperRotationWordEquiv a b).adjoint_eq_symm
  rw [h]
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext n
  simp only [paperRotationWordUndo, ContinuousLinearMap.comp_apply,
    paperRotationShift_apply, paperRotationModulation_apply, paperRotationWord_apply,
    smul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc,
    ← paperRotationPhase_add]
  congr 2
  push_cast
  ring

/-- Finite complex linear combinations of the integer Weyl words. -/
def paperRotationWordSpan (t : ℝ) : Submodule ℂ RotOp :=
  Submodule.span ℂ (Set.range fun ab : ℤ × ℤ => paperRotationWord ab.1 ((ab.2 : ℝ) * t))

theorem paperRotationWord_mem_span (t : ℝ) (a b : ℤ) :
    paperRotationWord a ((b : ℝ) * t) ∈ paperRotationWordSpan t :=
  Submodule.subset_span ⟨(a, b), rfl⟩

private theorem wordSpan_one (t : ℝ) : (1 : RotOp) ∈ paperRotationWordSpan t := by
  change ContinuousLinearMap.id ℂ PaperRotationHilbert ∈ paperRotationWordSpan t
  simpa [paperRotationWord, paperRotationModulation_zero, paperRotationShift_zero] using
    paperRotationWord_mem_span t 0 0

private theorem wordSpan_mul (t : ℝ) {A B : RotOp}
    (hA : A ∈ paperRotationWordSpan t) (hB : B ∈ paperRotationWordSpan t) :
    A * B ∈ paperRotationWordSpan t := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hA
    induction hB using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨⟨c, d⟩, rfl⟩ := hB
      rw [ContinuousLinearMap.mul_def, paperRotationWord_comp]
      convert (paperRotationWordSpan t).smul_mem
        (paperRotationPhase (-(a : ℝ) * ((d : ℝ) * t)))
        (paperRotationWord_mem_span t (a + c) (b + d)) using 1
      simp [Int.cast_add, add_mul]
    | zero => simp
    | add B C _ _ ihB ihC =>
      rw [mul_add]; exact (paperRotationWordSpan t).add_mem ihB ihC
    | smul z B _ ih => rw [mul_smul_comm]; exact (paperRotationWordSpan t).smul_mem z ih
  | zero => simp
  | add A C _ _ ihA ihC =>
    rw [add_mul]; exact (paperRotationWordSpan t).add_mem ihA ihC
  | smul z A _ ih => rw [smul_mul_assoc]; exact (paperRotationWordSpan t).smul_mem z ih

private theorem wordSpan_star (t : ℝ) {A : RotOp}
    (hA : A ∈ paperRotationWordSpan t) : star A ∈ paperRotationWordSpan t := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hA
    rw [paperRotationWord_star]
    convert (paperRotationWordSpan t).smul_mem
      (paperRotationPhase (-(a : ℝ) * ((b : ℝ) * t)))
      (paperRotationWord_mem_span t (-a) (-b)) using 1
    simp
  | zero => simp
  | add A B _ _ ihA ihB =>
    rw [star_add]; exact (paperRotationWordSpan t).add_mem ihA ihB
  | smul z A _ ih => rw [star_smul]; exact (paperRotationWordSpan t).smul_mem (star z) ih

/-- The finite Weyl algebra, before taking the operator norm closure. -/
def paperRotationPolynomialAlgebra (t : ℝ) : StarSubalgebra ℂ RotOp where
  carrier := paperRotationWordSpan t
  algebraMap_mem' z := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (paperRotationWordSpan t).smul_mem z (wordSpan_one t)
  add_mem' := (paperRotationWordSpan t).add_mem
  mul_mem' := wordSpan_mul t
  star_mem' := wordSpan_star t

private theorem span_eq_adjoin (t : ℝ) :
    (paperRotationWordSpan t : Set RotOp) =
      (StarAlgebra.adjoin ℂ (Set.range fun ab : ℤ × ℤ =>
        paperRotationWord ab.1 ((ab.2 : ℝ) * t)) : Set RotOp) := by
  apply Set.Subset.antisymm
  · change paperRotationWordSpan t ≤ (StarAlgebra.adjoin ℂ
      (Set.range fun ab : ℤ × ℤ => paperRotationWord ab.1 ((ab.2 : ℝ) * t))).toSubalgebra.toSubmodule
    exact Submodule.span_le.mpr (StarAlgebra.subset_adjoin ℂ _)
  · change StarAlgebra.adjoin ℂ _ ≤ paperRotationPolynomialAlgebra t
    exact StarAlgebra.adjoin_le fun _ h => Submodule.subset_span h

theorem paperRotationAlgebra_eq_closure_span (t : ℝ) :
    (paperRotationAlgebra t : Set RotOp) = closure (paperRotationWordSpan t : Set RotOp) := by
  rw [span_eq_adjoin]
  rfl

/-- A closed linear property can be checked on the generating Weyl words. -/
theorem paperRotationAlgebra_induction (t : ℝ) (P : RotOp → Prop)
    (hclosed : IsClosed {A | P A})
    (hword : ∀ a b : ℤ, P (paperRotationWord a ((b : ℝ) * t)))
    (hzero : P 0) (hadd : ∀ A B, P A → P B → P (A + B))
    (hsmul : ∀ z : ℂ, ∀ A, P A → P (z • A))
    {A : RotOp} (hA : A ∈ paperRotationAlgebra t) : P A := by
  change A ∈ (paperRotationAlgebra t : Set RotOp) at hA
  rw [paperRotationAlgebra_eq_closure_span] at hA
  apply closure_minimal (t := {A | P A}) ?_ hclosed hA
  intro B hB
  induction hB using Submodule.span_induction with
  | mem B hB => obtain ⟨⟨a, b⟩, rfl⟩ := hB; exact hword a b
  | zero => exact hzero
  | add B C _ _ ihB ihC => exact hadd B C ihB ihC
  | smul z B _ ih => exact hsmul z B ih

private theorem phase_int_mul (a : ℤ) (b : ℝ) :
    paperRotationPhase ((a : ℝ) * b) = paperRotationPhase b ^ a := by
  simp only [paperRotationPhase, Circle.exp_intCast_mul, Circle.coe_zpow]

private theorem trace_words_cyclic (a c : ℤ) (b d : ℝ) :
    paperRotationTrace (paperRotationWord a b * paperRotationWord c d) =
      paperRotationTrace (paperRotationWord c d * paperRotationWord a b) := by
  simp only [ContinuousLinearMap.mul_def, paperRotationWord_comp, map_smul,
    paperRotationTrace_word, smul_eq_mul]
  rw [add_comm c a, add_comm d b]
  split_ifs with h
  · have hc : c = -a := by omega
    subst c
    simp only [mul_one, Int.cast_neg, neg_neg]
    calc
      paperRotationPhase (-(a : ℝ) * d) =
          paperRotationPhase ((-a : ℤ) * (b + d) + (a : ℝ) * b) := by
        congr 1
        push_cast
        ring
      _ = paperRotationPhase ((-a : ℤ) * (b + d)) *
          paperRotationPhase ((a : ℝ) * b) := paperRotationPhase_add _ _
      _ = paperRotationPhase ((a : ℝ) * b) := by
        rw [phase_int_mul, h.2, one_zpow, one_mul]
  · simp

/-- Cyclicity on the actual norm-closed rotation algebra. -/
theorem paperRotationTrace_cyclic (t : ℝ) (A B : paperRotationAlgebra t) :
    paperRotationTrace (A.val * B.val) = paperRotationTrace (B.val * A.val) := by
  have hleft (W : RotOp) (hW : ∀ c d : ℤ,
      paperRotationTrace (W * paperRotationWord c ((d : ℝ) * t)) =
        paperRotationTrace (paperRotationWord c ((d : ℝ) * t) * W)) :
      ∀ B : paperRotationAlgebra t,
        paperRotationTrace (W * B.val) = paperRotationTrace (B.val * W) := by
    intro B
    apply paperRotationAlgebra_induction t
      (fun X => paperRotationTrace (W * X) = paperRotationTrace (X * W))
      (isClosed_eq (paperRotationTrace.continuous.comp (continuous_const.mul continuous_id))
        (paperRotationTrace.continuous.comp (continuous_id.mul continuous_const))) hW
      (by simp) (fun X Y hX hY => by simp [mul_add, add_mul, hX, hY])
      (fun z X hX => by simp [hX]) B.property
  apply paperRotationAlgebra_induction t
    (fun X => paperRotationTrace (X * B.val) = paperRotationTrace (B.val * X))
    (isClosed_eq (paperRotationTrace.continuous.comp (continuous_id.mul continuous_const))
      (paperRotationTrace.continuous.comp (continuous_const.mul continuous_id)))
    (fun a b => hleft _ (fun c d => trace_words_cyclic a c _ _) B)
    (by simp) (fun X Y hX hY => by simp [mul_add, add_mul, hX, hY])
    (fun z X hX => by simp [hX]) A.property

/-- The restriction is fixed by the Weyl-word values: the ultrafilter choice cannot affect it. -/
theorem paperRotationTrace_unique (t : ℝ) (τ : RotOp →L[ℂ] ℂ)
    (hτ : ∀ a b : ℤ, τ (paperRotationWord a ((b : ℝ) * t)) =
      if a = 0 ∧ paperRotationPhase ((b : ℝ) * t) = 1 then 1 else 0)
    (A : paperRotationAlgebra t) : τ A.val = paperRotationTrace A.val := by
  apply paperRotationAlgebra_induction t (fun X => τ X = paperRotationTrace X)
    (isClosed_eq τ.continuous paperRotationTrace.continuous)
    (fun a b => (hτ a b).trans (paperRotationTrace_word a _).symm)
    (by simp) (fun X Y hX hY => by simp [hX, hY])
    (fun z X hX => by simp [hX]) A.property

theorem paperRotationTrace_word_pair (t : ℝ)
    (ht : ∀ b : ℤ, paperRotationPhase ((b : ℝ) * t) = 1 ↔ b = 0)
    (a b c d : ℤ) :
    paperRotationTrace (star (paperRotationWord a ((b : ℝ) * t)) *
      paperRotationWord c ((d : ℝ) * t)) = if a = c ∧ b = d then 1 else 0 := by
  rw [paperRotationWord_star, smul_mul_assoc, map_smul,
    ContinuousLinearMap.mul_def, paperRotationWord_comp, map_smul]
  have he : -((b : ℝ) * t) + (d : ℝ) * t = ((-b + d : ℤ) : ℝ) * t := by
    push_cast; ring
  rw [he, paperRotationTrace_integer_word t ht]
  by_cases h : a = c ∧ b = d
  · obtain ⟨rfl, rfl⟩ := h
    simp only [neg_add_cancel, eq_self, and_self, ↓reduceIte, smul_eq_mul, mul_one,
      Int.cast_neg, neg_neg, ← paperRotationPhase_add]
    convert paperRotationPhase_zero using 1
    congr 1
    ring
  · have hab : ¬ (-a + c = 0 ∧ -b + d = 0) := by omega
    simp [h, hab]

/-- Irrational Weyl words are linearly independent in the actual operator representation. -/
theorem paperRotationWords_linearIndependent (t : ℝ)
    (ht : ∀ b : ℤ, paperRotationPhase ((b : ℝ) * t) = 1 ↔ b = 0) :
    LinearIndependent ℂ
      (fun ab : ℤ × ℤ => paperRotationWord ab.1 ((ab.2 : ℝ) * t)) := by
  apply linearIndependent_iff'.mpr
  intro S z hz k hk
  have h := congrArg
    (fun A : RotOp => paperRotationTrace (star (paperRotationWord k.1 ((k.2 : ℝ) * t)) * A)) hz
  simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul,
    paperRotationTrace_word_pair t ht, mul_zero, map_zero] at h
  have hi (j : ℤ × ℤ) : (k.1 = j.1 ∧ k.2 = j.2) ↔ k = j := Prod.ext_iff.symm
  simpa only [hi, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    if_pos hk] using h

end
end GaloisForLFunctions.HTGeometry
