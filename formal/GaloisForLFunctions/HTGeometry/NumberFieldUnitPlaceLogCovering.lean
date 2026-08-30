import GaloisForLFunctions.HTGeometry.NumberFieldBoundedPrincipalIdeals

/-!
# Unconditional covering for the number-field unit log lattice

Minkowski reduction produces a nonzero algebraic integer with uniformly controlled shifted
archimedean values.  Its principal ideal belongs to a finite bounded set; division by the chosen
generator of that ideal produces a unit.  Integral norm nonvanishing supplies the missing lower
coordinate bounds.  Thus one radius covers the entire weighted-zero place-log hyperplane by unit
logarithms, with no rank, chosen-unit, condition-number, or fundamental-domain premise.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField NumberField.InfinitePlace
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- The unit log lattice has a finite covering radius in the weighted-zero place hyperplane. -/
theorem exists_numberFieldUnitPlaceLog_coveringRadius :
    ∃ R : ℝ, 0 < R ∧ ∀ y ∈ numberFieldUnitPlaceLogHyperplane (K := K),
      ∃ u : (𝓞 K)ˣ, ‖numberFieldUnitPlaceLogEmbeddings u - y‖ ≤ R := by
  obtain ⟨C, hC, hCall⟩ := exists_numberFieldInteger_placeValue_le (K := K)
  let N : ℕ := ⌈C ^ Fintype.card (K →+* ℂ)⌉₊
  let B : ℝ := ∑ I : boundedNonzeroPrincipalIdeals K N,
    ‖fun w : InfinitePlace K =>
      Real.log (w ((boundedPrincipalIdealGenerator I : 𝓞 K) : K))‖
  let D : ℝ := ∑ w : InfinitePlace K, (mult w : ℝ)
  let M : ℝ := |Real.log C|
  let R : ℝ := D * M + B + 1
  have hD : 0 ≤ D := Finset.sum_nonneg fun w _ => by
    exact_mod_cast (Nat.zero_le (mult w))
  have hM : 0 ≤ M := abs_nonneg _
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hR : 0 < R := by
    dsimp [R]
    positivity
  refine ⟨R, hR, ?_⟩
  intro y hy
  have hySum : ∑ w : InfinitePlace K, (mult w : ℝ) * y w = 0 := hy
  obtain ⟨α, hα, hαPlace⟩ := hCall y hySum
  have hαNorm : Ideal.absNorm (Ideal.span {α}) ≤ N := by
    dsimp [N]
    exact absNorm_span_singleton_le_ceil_of_placeValue_le α y hySum hαPlace
  have hαIdeal_ne : Ideal.span {α} ≠ (⊥ : Ideal (𝓞 K)) := by
    intro hbot
    exact hα (Ideal.span_singleton_eq_bot.mp hbot)
  let I : boundedNonzeroPrincipalIdeals K N :=
    ⟨Ideal.span {α}, hαNorm, hαIdeal_ne, α, hα, rfl⟩
  let β : 𝓞 K := boundedPrincipalIdealGenerator I
  have hβ : β ≠ 0 := boundedPrincipalIdealGenerator_ne_zero I
  have hβB : ‖fun w : InfinitePlace K => Real.log (w (β : K))‖ ≤ B := by
    dsimp [B, β]
    exact Finset.single_le_sum (fun J _ => norm_nonneg
      (fun w : InfinitePlace K =>
        Real.log (w ((boundedPrincipalIdealGenerator J : 𝓞 K) : K))))
      (Finset.mem_univ I)
  have hassoc : Associated α β := by
    apply Ideal.span_singleton_eq_span_singleton.mp
    exact (span_boundedPrincipalIdealGenerator I).symm
  rcases hassoc with ⟨u, hu⟩
  let d : InfinitePlace K → ℝ := fun w => Real.log (w (α : K)) - y w
  have hdUpper (w : InfinitePlace K) : d w ≤ M := by
    have hαPos : 0 < w (α : K) := by
      rw [InfinitePlace.pos_iff]
      exact_mod_cast hα
    have hbound := Real.log_le_log hαPos (hαPlace w)
    calc
      d w ≤ Real.log (C * Real.exp (y w)) - y w := sub_le_sub_right hbound _
      _ = Real.log C := by
        rw [Real.log_mul (ne_of_gt hC) (Real.exp_ne_zero _), Real.log_exp]
        ring
      _ ≤ M := le_abs_self _
  have hdSum : 0 ≤ ∑ w : InfinitePlace K, (mult w : ℝ) * d w := by
    simp_rw [d, mul_sub]
    rw [Finset.sum_sub_distrib, hySum, sub_zero]
    exact weightedSum_numberFieldIntegerPlaceLog_nonneg α hα
  have hm (w : InfinitePlace K) : 1 ≤ (mult w : ℝ) := by
    by_cases hw : w.IsReal <;> simp [InfinitePlace.mult, hw]
  have hdNorm : ‖d‖ ≤ D * M := by
    dsimp [D]
    exact norm_le_weightedSum_mul_of_weightedSum_nonneg_of_le
      (fun w : InfinitePlace K => (mult w : ℝ)) hm d hM hdSum hdUpper
  have hlogMul :
      (fun w : InfinitePlace K => Real.log (w (β : K))) =
        (fun w => Real.log (w (α : K))) + numberFieldUnitPlaceLogEmbeddings u := by
    funext w
    rw [Pi.add_apply]
    have hcast : (β : K) = (α : K) * ((u : 𝓞 K) : K) := by
      exact_mod_cast hu.symm
    rw [hcast, map_mul, Real.log_mul]
    · rfl
    · apply ne_of_gt
      rw [InfinitePlace.pos_iff]
      exact_mod_cast hα
    · apply ne_of_gt
      rw [InfinitePlace.pos_iff]
      norm_cast
      exact u.ne_zero
  have hlogInv : numberFieldUnitPlaceLogEmbeddings (u⁻¹) =
      -numberFieldUnitPlaceLogEmbeddings u := by
    have hmul := numberFieldUnitPlaceLogEmbeddings_mul (u⁻¹) u
    have hsum : numberFieldUnitPlaceLogEmbeddings (u⁻¹) +
        numberFieldUnitPlaceLogEmbeddings u = 0 := by
      rw [← hmul]
      funext w
      simp [numberFieldUnitPlaceLogEmbeddings]
    calc
      numberFieldUnitPlaceLogEmbeddings (u⁻¹) =
          (numberFieldUnitPlaceLogEmbeddings (u⁻¹) +
            numberFieldUnitPlaceLogEmbeddings u) -
              numberFieldUnitPlaceLogEmbeddings u := by abel
      _ = -numberFieldUnitPlaceLogEmbeddings u := by rw [hsum, zero_sub]
  have hdiff : numberFieldUnitPlaceLogEmbeddings (u⁻¹) - y =
      d - (fun w : InfinitePlace K => Real.log (w (β : K))) := by
    rw [hlogInv, hlogMul]
    funext w
    simp only [Pi.sub_apply, Pi.neg_apply, Pi.add_apply]
    dsimp [d]
    ring
  refine ⟨u⁻¹, ?_⟩
  rw [hdiff]
  calc
    ‖d - (fun w : InfinitePlace K => Real.log (w (β : K)))‖ ≤
        ‖d‖ + ‖fun w : InfinitePlace K => Real.log (w (β : K))‖ := norm_sub_le _ _
    _ ≤ D * M + B := add_le_add hdNorm hβB
    _ ≤ R := by dsimp [R]; linarith

end

end GaloisForLFunctions.HTGeometry
