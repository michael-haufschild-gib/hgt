import GaloisForLFunctions.RHTower.DeningerSechMultiplier
import GaloisForLFunctions.RHTower.DeningerMeyerOscillator

/-!
# The two-sided weight is an automorphism of the source

The weight `w_K(t) = e^{Kt} + e^{-Kt} = 2\cosh(Kt)` acts on the source as the sum of two
exponential multiplications, and its inverse is the bounded multiplier `1/(2\cosh(Kt))`.  So the
oscillator family pulled back along it is again nuclear, and — unlike the one-sided family — it is
monotone in `K`, which is what the comparison with the Meyer seminorms needs.

* `deningerTwoSidedMul` : `w_K` as a linear map of the source.
* `deningerTwoSidedMul_surjective` : **it is surjective.**
* `deningerTwoSidedOsc_isNuclearSpaceC` : **the two-sided oscillator family is nuclear.**
-/

namespace RHTower

open SchwartzMap Function

noncomputable section

/-- Multiplication by the two-sided weight `w_K(t) = e^{Kt} + e^{-Kt}`. -/
def deningerTwoSidedMul (K : ℝ) : DeningerExpSchwartz →ₗ[ℂ] DeningerExpSchwartz :=
  deningerExpMulLM K + deningerExpMulLM (-K)

theorem deningerTwoSidedMul_apply (K : ℝ) (h : DeningerExpSchwartz) (t : ℝ) :
    ((deningerTwoSidedMul K h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
      = (((Real.exp (K * t) + Real.exp (-(K * t)) : ℝ)) : ℂ)
        * ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t := by
  show ((deningerExpMulLM K h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
      + ((deningerExpMulLM (-K) h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t = _
  rw [deningerExpMulLM_apply, deningerExpMulLM_apply]
  push_cast
  rw [show (-(K : ℂ)) * (t : ℂ) = -((K : ℂ) * (t : ℂ)) from by ring]
  ring

/-- **The two-sided weight acts surjectively on the source**, with inverse the bounded multiplier
`1/(2\cosh(Kt))`. -/
theorem deningerTwoSidedMul_surjective (K : ℝ) : Surjective (deningerTwoSidedMul K) := by
  intro h
  refine ⟨deningerBddMul (deningerSechMultiplier K) h, ?_⟩
  refine Subtype.ext (SchwartzMap.ext fun t => ?_)
  rw [deningerTwoSidedMul_apply, deningerBddMul_apply, deningerSechMultiplier_apply,
    ← mul_assoc, ← Complex.ofReal_mul]
  have hcosh : Real.exp (K * t) + Real.exp (-(K * t)) = 2 * Real.cosh (K * t) := by
    rw [Real.cosh_eq]
    ring
  have hpos : (0 : ℝ) < 2 * Real.cosh (K * t) := by
    have := Real.cosh_pos (K * t); positivity
  have hone : (Real.exp (K * t) + Real.exp (-(K * t))) * deningerSechWeight K t = 1 := by
    rw [hcosh, deningerSechWeight]
    field_simp
  rw [hone, Complex.ofReal_one, one_mul]

/-- The two-sided oscillator family `N(K,m)(h) = Q_m(w_K h)`. -/
def deningerTwoSidedOscFamily : SeminormFamily ℂ DeningerExpSchwartz (ℕ × ℕ) :=
  fun Km => (deningerSourceOscSeminorm Km.2).comp (deningerTwoSidedMul (Km.1 : ℝ))

theorem deningerTwoSidedOscFamily_apply (K m : ℕ) (h : DeningerExpSchwartz) :
    deningerTwoSidedOscFamily (K, m) h
      = deningerSourceOscSeminorm m (deningerTwoSidedMul (K : ℝ) h) := rfl

/-- **The two-sided oscillator family is nuclear.** -/
theorem deningerTwoSidedOsc_isNuclearSpaceC :
    DeningerIsNuclearSpaceC deningerTwoSidedOscFamily := by
  rintro ⟨K, m⟩
  obtain ⟨m', C, hle, hnuc⟩ :=
    deningerIsNuclearSpaceC_comp_surjective deningerSourceOscSeminorm
      (deningerTwoSidedMul (K : ℝ)) (deningerTwoSidedMul_surjective (K : ℝ))
      deningerSourceOsc_isNuclearSpaceC m
  exact ⟨(K, m'), C, hle, hnuc⟩

/-- **The two-sided weight dominates the Meyer weight**, so the family is comparable to the Meyer
seminorms pointwise. -/
theorem deningerTwoSidedWeight_ge (K t : ℝ) (hK : 0 ≤ K) :
    Real.exp (K * |t|) ≤ Real.exp (K * t) + Real.exp (-(K * t)) := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    have : (0 : ℝ) < Real.exp (-(K * t)) := Real.exp_pos _
    linarith
  · rw [abs_of_nonpos ht]
    have heq : K * -t = -(K * t) := by ring
    rw [heq]
    have : (0 : ℝ) < Real.exp (K * t) := Real.exp_pos _
    linarith

theorem deningerTwoSidedWeight_le (K t : ℝ) (hK : 0 ≤ K) :
    Real.exp (K * t) + Real.exp (-(K * t)) ≤ 2 * Real.exp (K * |t|) := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    have h1 : Real.exp (-(K * t)) ≤ Real.exp (K * t) := by
      refine Real.exp_le_exp.2 ?_
      nlinarith
    linarith
  · rw [abs_of_nonpos ht]
    have heq : K * -t = -(K * t) := by ring
    rw [heq]
    have h1 : Real.exp (K * t) ≤ Real.exp (-(K * t)) := by
      refine Real.exp_le_exp.2 ?_
      nlinarith
    linarith

end

end RHTower
