import GaloisForLFunctions.RHTower.WeilLagFunctionGram
import GaloisForLFunctions.RHTower.WeilLagFunctionOmega

/-!
# The reflection partner of the lag kernel is never positive

`lagGramKernel x y = Φ(log x − log y)` is the *translation* (Toeplitz) kernel of the lag function on
the multiplicative group of positive reals; `riemannHypothesis_iff_lagGramKernel_posSemidef` says RH
is exactly its positive semidefiniteness.  Its *reflection* (Hankel) partner is

  `lagReflectionKernel x y = Φ(log x + log y) = Φ(log (x·y))`,

the kernel a criterion of Hankel shape — one whose entries depend on the product rather than on the
ratio — would ask to be positive.

The two are related by the inversion of the group, `K♯(x,y) = K(x, y⁻¹)`, so they agree along a
column exactly at a fixed point of the inversion, i.e. at a `2`-torsion element.  The multiplicative
group of positive reals (like the group `ℚ^×_{>0}` of principal divisors of `Spec ℤ`) is
torsion free: its only fixed point is `1`.

Consequently reflection positivity is not merely unproved here — it is false.  The diagonal of the
reflection kernel is the lag function restricted to the squares, `x ↦ Φ(log (x²))`, and the lag
function is unconditionally `Ω₋`; so the reflection kernel has a strictly negative diagonal entry
with no hypothesis.  Worse, under RH the antipodal two-point form on `{x, x⁻¹}` equals
`2(Φ(log x²) − Φ(0))`, which is `≤ 0` for every `x` because `Φ(0)` is then the supremum of `Φ`:
RH makes the reflection form negative semidefinite in exactly the directions the inversion creates.
-/

open Real Filter Topology

namespace RHTower

noncomputable section

/-- The reflection (Hankel) partner of the lag kernel: `K♯(x,y) = Φ(log x + log y)`. -/
def lagReflectionKernel (x y : ℝ) : ℝ := weilLagFunctionReal (Real.log x + Real.log y)

theorem lagReflectionKernel_symm (x y : ℝ) :
    lagReflectionKernel x y = lagReflectionKernel y x := by
  unfold lagReflectionKernel; rw [add_comm]

/-- **The reflection kernel is the translation kernel composed with the group inversion.** -/
theorem lagReflectionKernel_eq_lagGramKernel_inv (x y : ℝ) :
    lagReflectionKernel x y = lagGramKernel x y⁻¹ := by
  unfold lagReflectionKernel lagGramKernel
  rw [Real.log_inv, sub_neg_eq_add]

/-- The two kernels agree along a column exactly at a fixed point of the inversion. -/
theorem lagReflectionKernel_eq_lagGramKernel_of_inv_eq_self
    {y : ℝ} (h : y⁻¹ = y) (x : ℝ) :
    lagReflectionKernel x y = lagGramKernel x y := by
  rw [lagReflectionKernel_eq_lagGramKernel_inv x y, h]

/-- The inversion of the multiplicative group of positive reals has trivial fixed set: its
`2`-torsion is `{1}`.  This is the structural reason the reflection kernel cannot inherit the
translation kernel's positivity. -/
theorem inv_eq_self_iff_one {y : ℝ} (hy : 0 < y) : y⁻¹ = y ↔ y = 1 := by
  constructor
  · intro h
    have h1 : y * y = 1 := by
      field_simp at h
      nlinarith [h]
    nlinarith [hy]
  · intro h; rw [h, inv_one]

/-- **The reflection kernel's diagonal is the lag function restricted to the squares.** -/
theorem lagReflectionKernel_self (x : ℝ) :
    lagReflectionKernel x x = weilLagFunctionReal (Real.log (x ^ 2)) := by
  unfold lagReflectionKernel
  rw [Real.log_pow]
  push_cast
  ring_nf

/-- The antipodal two-point form of the reflection kernel on `{x, x⁻¹}` with weights `(1, −1)`
is `2(Φ(log x²) − Φ(0))`. -/
theorem lagReflection_antipodal_form (x : ℝ) :
    lagReflectionKernel x x - 2 * lagReflectionKernel x x⁻¹
        + lagReflectionKernel x⁻¹ x⁻¹
      = 2 * (weilLagFunctionReal (Real.log (x ^ 2)) - poleSharpConstant) := by
  have hmid : lagReflectionKernel x x⁻¹ = poleSharpConstant := by
    unfold lagReflectionKernel
    rw [Real.log_inv, add_neg_cancel]
    have := integerLag_one
    unfold integerLag at this
    rwa [Nat.cast_one, Real.log_one] at this
  have hinv : lagReflectionKernel x⁻¹ x⁻¹ = weilLagFunctionReal (Real.log (x ^ 2)) := by
    rw [lagReflectionKernel_self, inv_pow, Real.log_inv, weilLagFunctionReal_neg]
  rw [lagReflectionKernel_self, hmid, hinv]; ring

/-- **The reflection kernel has a strictly negative diagonal entry, unconditionally.**  The witness
is `x = √n` for any `n` realising the unconditional `Ω₋` law of the integer lags. -/
theorem exists_lagReflectionKernel_self_neg :
    ∃ x : ℝ, 0 < x ∧ lagReflectionKernel x x < 0 := by
  obtain ⟨η, hη, hfreq⟩ := frequently_integerLag_le_neg
  obtain ⟨n, hn1, hn⟩ := (Filter.frequently_atTop.mp hfreq) 1
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  refine ⟨Real.sqrt n, Real.sqrt_pos.mpr hn0, ?_⟩
  rw [lagReflectionKernel_self, Real.sq_sqrt hn0.le]
  have hre : integerLag n = weilLagFunctionReal (Real.log n) := rfl
  rw [← hre]
  linarith

/-- **The reflection kernel is not positive semidefinite**, unconditionally: not even its diagonal
is nonnegative. -/
theorem not_forall_lagReflectionKernel_self_nonneg :
    ¬ ∀ x : ℝ, 0 < x → 0 ≤ lagReflectionKernel x x := by
  obtain ⟨x, hx, hneg⟩ := exists_lagReflectionKernel_self_neg
  exact fun h => absurd (h x hx) (not_le.mpr hneg)

/-- By contrast the *translation* kernel's diagonal is the positive archimedean genus
`2 + γ − log 4π`. -/
theorem lagGramKernel_self_pos (x : ℝ) : 0 < lagGramKernel x x := by
  rw [lagGramKernel_self]; exact poleSharpConstant_pos

theorem weilLagFunctionReal_le_of_riemannHypothesis (hRH : RiemannHypothesis) (L : ℝ) :
    weilLagFunctionReal L ≤ poleSharpConstant := by
  have h := norm_weilLagFunction_le_of_riemannHypothesis hRH L
  rw [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

/-- **Under RH the antipodal reflection form is nonpositive at every point.**  The functional
equation's reflection therefore acts on the lag kernel with the wrong sign: RH does not supply
reflection positivity, it refutes it. -/
theorem lagReflection_antipodal_form_nonpos_of_riemannHypothesis
    (hRH : RiemannHypothesis) (x : ℝ) :
    lagReflectionKernel x x - 2 * lagReflectionKernel x x⁻¹
        + lagReflectionKernel x⁻¹ x⁻¹ ≤ 0 := by
  rw [lagReflection_antipodal_form x]
  have := weilLagFunctionReal_le_of_riemannHypothesis hRH (Real.log (x ^ 2))
  linarith

end

end RHTower
