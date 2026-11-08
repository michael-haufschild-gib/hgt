import GaloisForLFunctions.SelbergClass.Primon.KestenTailCyclicity
import GaloisForLFunctions.SelbergClass.Primon.SpectralCharacterAlgebra
import GaloisForLFunctions.SelbergClass.Primon.SemicircleObservableLinear
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier

/-!
# The bounded square-coordinate operator

Compact semicircle support makes multiplication by `x²` a bounded positive
self-adjoint operator. Its even-character recurrence preserves the closed
likelihood space, where it defines the square-coordinate Jacobi operator.
-/

open MeasureTheory Set
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

private def squareSymbol (x : ℝ) : ℝ := min (x ^ 2) 4

private theorem measurable_squareSymbol : Measurable squareSymbol := by
  unfold squareSymbol
  fun_prop

private theorem squareSymbol_bound (x : ℝ) : ‖squareSymbol x‖ ≤ 4 := by
  rw [squareSymbol, Real.norm_eq_abs,
    abs_of_nonneg (le_min (sq_nonneg x) (by norm_num))]
  exact min_le_right _ _

private theorem squareSymbol_eq (x : ℝ) (hx : x ∈ Icc (-2 : ℝ) 2) :
    squareSymbol x = x ^ 2 := by
  apply min_eq_left
  have hm := mul_nonneg (sub_nonneg.mpr hx.2)
    (show 0 ≤ x + 2 by linarith only [hx.1])
  nlinarith only [hm]

/-- Actual multiplication by the squared spectral coordinate on semicircle `L²`. -/
def semicircleSquareMul : SemicircleL2 →L[ℝ] SemicircleL2 :=
  lpBoundedMulCLM measurable_squareSymbol (by norm_num : (0 : ℝ) ≤ 4) squareSymbol_bound

/-- The bounded operator acts as literal square-coordinate multiplication almost everywhere. -/
theorem semicircleSquareMul_ae (f : SemicircleL2) :
    semicircleSquareMul f =ᵐ[(semicircleSpectralLaw : Measure ℝ)] fun x => x ^ 2 * f x := by
  have ha : ∀ᵐ x ∂(semicircleSpectralLaw : Measure ℝ), x ∈ Icc (-2 : ℝ) 2 := by
    rw [ae_iff]
    exact semicircleSpectralLaw_carried
  filter_upwards [lpBoundedMulCLM_coeFn measurable_squareSymbol
    (by norm_num : (0 : ℝ) ≤ 4) squareSymbol_bound f, ha] with x hm hx
  calc
    _ = squareSymbol x * f x := hm
    _ = _ := by rw [squareSymbol_eq x hx]

/-- The square-coordinate operator has norm at most the upper spectral edge `4`. -/
theorem norm_semicircleSquareMul_le : ‖semicircleSquareMul‖ ≤ 4 :=
  norm_lpBoundedMulCLM_le measurable_squareSymbol (by norm_num) squareSymbol_bound

/-- Square-coordinate multiplication is self-adjoint on the actual semicircle Hilbert space. -/
theorem inner_semicircleSquareMul (f g : SemicircleL2) :
    inner ℝ (semicircleSquareMul f) g = inner ℝ f (semicircleSquareMul g) :=
  lpBoundedMulCLM_inner_real measurable_squareSymbol (by norm_num) squareSymbol_bound
    (fun _ => rfl) f g

/-- Its quadratic form is nonnegative for every square-integrable observable. -/
theorem inner_semicircleSquareMul_nonneg (f : SemicircleL2) :
    0 ≤ inner ℝ f (semicircleSquareMul f) := by
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [semicircleSquareMul_ae f] with x hx
  rw [hx, RCLike.inner_apply]
  simp only [conj_trivial]
  have he : x ^ 2 * f x * f x = x ^ 2 * (f x) ^ 2 := by ring
  rw [he]
  exact mul_nonneg (sq_nonneg x) (sq_nonneg (f x))

/-- On continuous observables, the square multiplier agrees with pointwise polynomial multiplication. -/
theorem semicircleSquareMul_observable (f : C(ℝ, ℝ)) :
    semicircleSquareMul (semicircleL2Observable f) =
      semicircleL2Observable ⟨fun x => x ^ 2 * f x, by fun_prop⟩ := by
  apply Lp.ext
  filter_upwards [semicircleSquareMul_ae (semicircleL2Observable f),
    coeFn_semicircleL2Observable f,
    coeFn_semicircleL2Observable ⟨fun x => x ^ 2 * f x, by fun_prop⟩] with x hm hf hg
  rw [hm, hf, hg]
  rfl

/-- The constant character has diagonal coefficient `1` at the lower Jacobi boundary. -/
theorem semicircleSquareMul_character_zero :
    semicircleSquareMul (spectralCharacterVector 0) =
      spectralCharacterVector 2 + spectralCharacterVector 0 := by
  change semicircleSquareMul (semicircleL2Observable (spectralCharacter 0)) = _
  rw [semicircleSquareMul_observable]
  change semicircleObservableMap _ =
    semicircleObservableMap (spectralCharacter 2) + semicircleObservableMap (spectralCharacter 0)
  rw [← map_add]
  congr 1
  ext x
  change x ^ 2 * spectralCharacter 0 x = spectralCharacter 2 x + spectralCharacter 0 x
  have h := spectralCharacter_add_two 0 x
  simp only [Nat.zero_add, spectralCharacter_zero, spectralCharacter_one] at h ⊢
  nlinarith only [h]

/-- Away from the boundary, the even-character Jacobi coefficients are `1,2,1`. -/
theorem semicircleSquareMul_character_succ (n : ℕ) :
    semicircleSquareMul (spectralCharacterVector (2 * (n + 1))) =
      spectralCharacterVector (2 * (n + 2)) +
        (2 : ℝ) • spectralCharacterVector (2 * (n + 1)) + spectralCharacterVector (2 * n) := by
  change semicircleSquareMul (semicircleL2Observable (spectralCharacter (2 * (n + 1)))) = _
  rw [semicircleSquareMul_observable]
  change semicircleObservableMap _ = semicircleObservableMap (spectralCharacter (2 * (n + 2))) +
    (2 : ℝ) • semicircleObservableMap (spectralCharacter (2 * (n + 1))) +
      semicircleObservableMap (spectralCharacter (2 * n))
  rw [← map_smul, ← map_add, ← map_add]
  congr 1
  ext x
  change x ^ 2 * spectralCharacter (2 * (n + 1)) x =
    spectralCharacter (2 * (n + 2)) x + 2 * spectralCharacter (2 * (n + 1)) x +
      spectralCharacter (2 * n) x
  have h := spectralCharacter_add_four (2 * n) x
  rw [show 2 * n + 4 = 2 * (n + 2) by omega,
    show 2 * n + 2 = 2 * (n + 1) by omega] at h
  linear_combination -h

/-- Square-coordinate multiplication preserves the full closed likelihood space. -/
theorem semicircleSquareMul_mem_likelihoodHilbert (f : KestenLikelihoodHilbert) :
    semicircleSquareMul (f : SemicircleL2) ∈ KestenLikelihoodHilbert := by
  have hle : evenCharacterSpan ≤ KestenLikelihoodHilbert.comap semicircleSquareMul.toLinearMap := by
    apply Submodule.span_le.2
    rintro _ ⟨n, rfl⟩
    change semicircleSquareMul (spectralCharacterVector (2 * n)) ∈ KestenLikelihoodHilbert
    cases n with
    | zero =>
        rw [Nat.mul_zero, semicircleSquareMul_character_zero]
        exact KestenLikelihoodHilbert.add_mem (evenCharacter_mem_likelihoodHilbert 1)
          (evenCharacter_mem_likelihoodHilbert 0)
    | succ n =>
        rw [semicircleSquareMul_character_succ]
        exact KestenLikelihoodHilbert.add_mem
          (KestenLikelihoodHilbert.add_mem (evenCharacter_mem_likelihoodHilbert (n + 2))
            (KestenLikelihoodHilbert.smul_mem 2 (evenCharacter_mem_likelihoodHilbert (n + 1))))
          (evenCharacter_mem_likelihoodHilbert n)
  have hc : IsClosed (KestenLikelihoodHilbert.comap semicircleSquareMul.toLinearMap : Set SemicircleL2) :=
    isClosed_closure.preimage semicircleSquareMul.continuous
  have hf : (f : SemicircleL2) ∈ evenCharacterSpan.topologicalClosure := by
    rw [evenCharacterSpan_closure]
    exact f.property
  exact closure_minimal hle hc hf

/-- The actual square-coordinate Jacobi operator on the likelihood Hilbert space. -/
def kestenSquareJacobi : KestenLikelihoodHilbert →L[ℝ] KestenLikelihoodHilbert :=
  semicircleSquareMul.restrict (fun f hf => semicircleSquareMul_mem_likelihoodHilbert ⟨f, hf⟩)

@[simp] theorem coe_kestenSquareJacobi (f : KestenLikelihoodHilbert) :
    (kestenSquareJacobi f : SemicircleL2) = semicircleSquareMul (f : SemicircleL2) := rfl

/-- The restricted Jacobi operator retains the spectral norm bound `4`. -/
theorem norm_kestenSquareJacobi_le : ‖kestenSquareJacobi‖ ≤ 4 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  exact (semicircleSquareMul.le_opNorm (f : SemicircleL2)).trans
    (mul_le_mul_of_nonneg_right norm_semicircleSquareMul_le (norm_nonneg _))

/-- The square-coordinate Jacobi operator is self-adjoint in the likelihood metric. -/
theorem inner_kestenSquareJacobi (f g : KestenLikelihoodHilbert) :
    inner ℝ (kestenSquareJacobi f) g = inner ℝ f (kestenSquareJacobi g) :=
  inner_semicircleSquareMul f g

/-- The square-coordinate Jacobi operator is positive in the likelihood metric. -/
theorem inner_kestenSquareJacobi_nonneg (f : KestenLikelihoodHilbert) :
    0 ≤ inner ℝ f (kestenSquareJacobi f) :=
  inner_semicircleSquareMul_nonneg f

end
end GaloisForLFunctions.SelbergClass.Primon

