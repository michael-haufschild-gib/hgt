import GaloisForLFunctions.RHTower.WeldClassTable
import GaloisForLFunctions.RHTower.SeamWeldCommutator
import GaloisForLFunctions.RHTower.SignedReflectionParity

/-!
# The scalar weld class collapses in its natural affine coefficient module

The weld table places the conversion cocycle `θ m_g n_h` in scalar cohomology with trivial
coefficients, where it is nonzero for `θ ≠ 0`.  The concrete derivative--Euler-multiplier relation
forces a larger coefficient module: the affine span of the archimedean derivation `D` and the scalar
identity `I`, with difference conjugation `D ↦ D - nθ I`.

In that minimal two-dimensional module the scalar cocycle has an explicit primitive

`b_θ(m,n) = mD - θmn I`.

Hence the scalar weld is nonzero before coefficient extension but exact afterward.  Moreover the
primitive is covariant for the genuine functional-equation involution, which acts simultaneously
on coefficients and generator labels.  Functional-equation symmetry therefore does not rescue the
class.  Any surviving obstruction must restrict the admissible gauge category for an independent,
structural reason such as differential order.
-/

open GaloisForLFunctions Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Minimal coefficient module spanned by the derivation and scalar identity.  The first coordinate
is the `D` coefficient and the second is the `I` coefficient. -/
def WeldAffineCoeff (_θ : ℝ) := ℝ × ℝ

instance weldAffineCoeffAddCommGroup (θ : ℝ) : AddCommGroup (WeldAffineCoeff θ) :=
  inferInstanceAs (AddCommGroup (ℝ × ℝ))

/-- Conjugation by the difference generator fixes the derivation coefficient and shifts its scalar
part by the conversion rate: `(a,b) ↦ (a,b-a n θ)`. -/
instance (θ : ℝ) : DistribMulAction WeldGroup (WeldAffineCoeff θ) where
  smul g v := (v.1, v.2 - v.1 * ((Multiplicative.toAdd g).2 : ℝ) * θ)
  one_smul v := by
    change (v.1, v.2 - v.1 * (((Multiplicative.toAdd (1 : WeldGroup)).2 : ℤ) : ℝ) * θ) = v
    simp
  mul_smul g h v := by
    change (v.1, v.2 - v.1 * ((Multiplicative.toAdd (g * h)).2 : ℝ) * θ) =
      (v.1,
        v.2 - v.1 * ((Multiplicative.toAdd h).2 : ℝ) * θ -
          v.1 * ((Multiplicative.toAdd g).2 : ℝ) * θ)
    rw [toAdd_mul]
    simp only [Prod.snd_add]
    push_cast
    congr 1
    ring
  smul_zero g := by
    change ((0 : ℝ), 0 - 0 * ((Multiplicative.toAdd g).2 : ℝ) * θ) = (0, 0)
    simp
  smul_add g v w := by
    change (v.1 + w.1,
        v.2 + w.2 - (v.1 + w.1) * ((Multiplicative.toAdd g).2 : ℝ) * θ) =
      (v.1, v.2 - v.1 * ((Multiplicative.toAdd g).2 : ℝ) * θ) +
        (w.1, w.2 - w.1 * ((Multiplicative.toAdd g).2 : ℝ) * θ)
    ext <;> simp
    ring

/-- Equivariant inclusion of scalar coefficients as multiples of the identity. -/
def weldAffineScalar (θ r : ℝ) : WeldAffineCoeff θ := (0, r)

/-- Scalar inclusion as an additive homomorphism into the affine coefficient module. -/
def weldAffineScalarHom (θ : ℝ) : ℝ →+ WeldAffineCoeff θ where
  toFun := weldAffineScalar θ
  map_zero' := by
    change ((0 : ℝ), 0) = (0, 0)
    rfl
  map_add' x y := by
    change ((0 : ℝ), x + y) = (0, x) + (0, y)
    change ((0 : ℝ), x + y) = (0 + 0, x + y)
    simp

/-- The derivation-valued normal-ordering primitive for the scalar weld cocycle. -/
def weldAffinePrimitive (θ : ℝ) (g : WeldGroup) : WeldAffineCoeff θ :=
  let m : ℝ := (Multiplicative.toAdd g).1
  let n : ℝ := (Multiplicative.toAdd g).2
  (m, -θ * m * n)

/-- The scalar weld cocycle after inclusion in the affine coefficient module. -/
def weldAffineCocycle (θ : ℝ) (g h : WeldGroup) : WeldAffineCoeff θ :=
  weldAffineScalar θ (weldCocycle θ g h)

/-- The scalar inclusion is fixed by the affine coefficient action, so it is an equivariant
coefficient inclusion. -/
theorem smul_weldAffineScalar (θ r : ℝ) (g : WeldGroup) :
    g • weldAffineScalar θ r = weldAffineScalar θ r := by
  change ((0 : ℝ), r - 0 * ((Multiplicative.toAdd g).2 : ℝ) * θ) = (0, r)
  simp

/-- The scalar additive homomorphism is equivariant for the trivial scalar action and affine
conjugation action.  Thus the collapse below is a genuine change-of-coefficients phenomenon. -/
theorem weldAffineScalarHom_smul (θ r : ℝ) (g : WeldGroup) :
    weldAffineScalarHom θ (g • r) = g • weldAffineScalarHom θ r := by
  change weldAffineScalar θ (g • r) = g • weldAffineScalar θ r
  rw [weldGroup_smul_trivial, smul_weldAffineScalar]

/-- **Affine trivialization.**  The included scalar weld cocycle is the two-coboundary of the
explicit derivation-valued primitive `b_θ(m,n)=mD-θmnI`. -/
theorem twoCoboundary_weldAffinePrimitive (θ : ℝ) :
    twoCoboundary (weldAffinePrimitive θ) = weldAffineCocycle θ := by
  funext g h
  change
    (((Multiplicative.toAdd h).1 : ℝ),
        -θ * ((Multiplicative.toAdd h).1 : ℝ) * ((Multiplicative.toAdd h).2 : ℝ) -
          ((Multiplicative.toAdd h).1 : ℝ) * ((Multiplicative.toAdd g).2 : ℝ) * θ) -
      (((Multiplicative.toAdd (g * h)).1 : ℝ),
        -θ * ((Multiplicative.toAdd (g * h)).1 : ℝ) *
          ((Multiplicative.toAdd (g * h)).2 : ℝ)) +
      (((Multiplicative.toAdd g).1 : ℝ),
        -θ * ((Multiplicative.toAdd g).1 : ℝ) * ((Multiplicative.toAdd g).2 : ℝ)) =
      (0, weldCocycle θ g h)
  rw [toAdd_mul]
  simp only [Prod.fst_add, Prod.snd_add, weldCocycle]
  push_cast
  ext <;> simp
  ring

/-- The affine lift is a closed cocycle because it is an exact coboundary. -/
theorem weldAffineCocycle_isTwoCocycle (θ : ℝ) : IsTwoCocycle (weldAffineCocycle θ) := by
  rw [← twoCoboundary_weldAffinePrimitive]
  exact twoCoboundary_isTwoCocycle _

/-- The scalar weld obstruction collapses after the forced affine coefficient extension. -/
theorem weldAffine_obstruction_eq_zero (θ : ℝ) :
    obstructionClassOf (weldAffineCocycle θ) (weldAffineCocycle_isTwoCocycle θ) = 0 := by
  rw [obstructionClassOf_eq_zero_iff_exists_cochain]
  exact ⟨weldAffinePrimitive θ, (twoCoboundary_weldAffinePrimitive θ).symm⟩

/-- **Coefficient-category dichotomy.**  For `θ ≠ 0`, the weld obstruction is nonzero in trivial
scalar coefficients and zero in the natural affine coefficients generated by `D` and `I`. -/
theorem weld_scalar_nonzero_affine_zero {θ : ℝ} (hθ : θ ≠ 0) :
    obstructionClassOf (weldCocycle θ) (weldCocycle_isTwoCocycle θ) ≠ 0 ∧
      obstructionClassOf (weldAffineCocycle θ) (weldAffineCocycle_isTwoCocycle θ) = 0 := by
  exact ⟨(weld_obstruction_ne_zero_iff θ).2 hθ, weldAffine_obstruction_eq_zero θ⟩

/-- At every prime rate, the scalar weld is nonzero but its natural affine lift is exact. -/
theorem prime_weld_scalar_nonzero_affine_zero {p : ℕ} (hp : p.Prime) :
    obstructionClassOf (weldCocycle (Real.log p))
        (weldCocycle_isTwoCocycle (Real.log p)) ≠ 0 ∧
      obstructionClassOf (weldAffineCocycle (Real.log p))
        (weldAffineCocycle_isTwoCocycle (Real.log p)) = 0 := by
  exact ⟨prime_weld_obstruction_ne_zero hp, weldAffine_obstruction_eq_zero (Real.log p)⟩

/-! ### Genuine functional-equation covariance -/

/-- FE reflection reverses the derivation coordinate and fixes the scalar identity coordinate. -/
def weldAffineReflection (θ : ℝ) (v : WeldAffineCoeff θ) : WeldAffineCoeff θ := (-v.1, v.2)

/-- The coefficient reflection is the one forced by the completed functional equation: `xi` is
reflection-even about `1/2`, while its derivative is reflection-odd. -/
theorem xi_deriv_one_sub_eq_neg (s : ℂ) :
    deriv _root_.RHTower.xi (1 - s) = -deriv _root_.RHTower.xi s := by
  have h := _root_.RHTower.deriv_signed_reflection
    (f := _root_.RHTower.xi) (c := (1 : ℂ) / 2) (ε := 1)
    _root_.RHTower.xi_differentiable
    (fun z => by simpa only [one_mul, show 2 * ((1 : ℂ) / 2) - z = 1 - z by ring] using
      _root_.RHTower.xi_one_sub z) s
  simpa only [one_mul, neg_one_mul,
    show 2 * ((1 : ℂ) / 2) - s = 1 - s by ring] using h

/-- On weld labels, the functional equation reverses both the derivation and Euler-multiplier
directions.  The scalar factor in `R M_p R = p⁻¹ M_p⁻¹` is central, so the label action is inversion. -/
def weldFEGroupReflection (g : WeldGroup) : WeldGroup := g⁻¹

/-- The coefficient reflection is semilinear for inversion of the weld labels. -/
theorem weldAffineReflection_smul (θ : ℝ) (g : WeldGroup) (v : WeldAffineCoeff θ) :
    weldAffineReflection θ (g • v) =
      weldFEGroupReflection g • weldAffineReflection θ v := by
  change
    (-v.1, v.2 - v.1 * ((Multiplicative.toAdd g).2 : ℝ) * θ) =
      (-v.1, v.2 - (-v.1) *
        ((Multiplicative.toAdd (g⁻¹ : WeldGroup)).2 : ℝ) * θ)
  rw [toAdd_inv]
  simp only [Prod.snd_neg]
  push_cast
  congr 1
  ring

/-- Genuine FE covariance acts on both the cochain value and its weld-group argument. -/
def IsFECovariantAffineCochain (θ : ℝ) (b : WeldGroup → WeldAffineCoeff θ) : Prop :=
  ∀ g, weldAffineReflection θ (b g) = b (weldFEGroupReflection g)

/-- The explicit affine primitive is covariant for the genuine functional-equation action. -/
theorem weldAffinePrimitive_isFECovariant (θ : ℝ) :
    IsFECovariantAffineCochain θ (weldAffinePrimitive θ) := by
  intro g
  change
    (-((Multiplicative.toAdd g).1 : ℝ),
      -θ * ((Multiplicative.toAdd g).1 : ℝ) * ((Multiplicative.toAdd g).2 : ℝ)) =
      (((Multiplicative.toAdd (g⁻¹ : WeldGroup)).1 : ℝ),
        -θ * ((Multiplicative.toAdd (g⁻¹ : WeldGroup)).1 : ℝ) *
          ((Multiplicative.toAdd (g⁻¹ : WeldGroup)).2 : ℝ))
  rw [toAdd_inv]
  simp only [Prod.fst_neg, Prod.snd_neg]
  push_cast
  congr 1
  ring

@[simp] private theorem weldAffine_smul_snd {θ : ℝ} (g : WeldGroup) (v : WeldAffineCoeff θ) :
    (g • v).2 = v.2 - v.1 * ((Multiplicative.toAdd g).2 : ℝ) * θ := rfl

@[simp] private theorem weldAffine_add_snd {θ : ℝ} (v w : WeldAffineCoeff θ) :
    (v + w).2 = v.2 + w.2 := by
  change v.2 + w.2 = v.2 + w.2
  rfl

@[simp] private theorem weldAffine_sub_snd {θ : ℝ} (v w : WeldAffineCoeff θ) :
    (v - w).2 = v.2 - w.2 := by
  change v.2 - w.2 = v.2 - w.2
  rfl

/-- **Primitive rigidity.**  Every affine primitive of a nonzero weld cocycle contains the
archimedean derivation with coefficient exactly one at the derivation generator.  Thus the explicit
primitive above is not an artifact of a convenient gauge: its reflection-odd component is forced. -/
theorem weldAffinePrimitive_derivCoeff_eq_one {θ : ℝ} (hθ : θ ≠ 0)
    {b : WeldGroup → WeldAffineCoeff θ}
    (hb : twoCoboundary b = weldAffineCocycle θ) :
    (b weldGenD).1 = 1 := by
  have hds := congrArg Prod.snd (congrFun (congrFun hb weldGenD) weldGenS)
  have hsd := congrArg Prod.snd (congrFun (congrFun hb weldGenS) weldGenD)
  simp [twoCoboundary, weldAffineCocycle, weldAffineScalar, weldCocycle,
    weldGenD, weldGenS] at hds hsd
  change (b weldGenS).2 - (b (weldGenD * weldGenS)).2 + (b weldGenD).2 = θ at hds
  change (b weldGenD).2 - (b weldGenD).1 * θ -
      (b (weldGenS * weldGenD)).2 + (b weldGenS).2 = 0 at hsd
  have hsame : b (weldGenD * weldGenS) = b (weldGenS * weldGenD) :=
    congrArg b weldGen_comm
  have hsnd := congrArg Prod.snd hsame
  have hmul : θ * (b weldGenD).1 = θ := by
    linear_combination hds - hsd + hsnd
  apply mul_left_cancel₀ hθ
  simpa using hmul

/-- **FE-covariant collapse.**  Functional-equation covariance does not exclude the affine
primitive: the same cochain is both FE-covariant and an exact trivialization. -/
theorem exists_FECovariantAffinePrimitive (θ : ℝ) :
    ∃ b : WeldGroup → WeldAffineCoeff θ,
      IsFECovariantAffineCochain θ b ∧ twoCoboundary b = weldAffineCocycle θ :=
  ⟨weldAffinePrimitive θ, weldAffinePrimitive_isFECovariant θ,
    twoCoboundary_weldAffinePrimitive θ⟩

/-- Prime specialization: even the completed FE symmetry leaves an admissible affine primitive. -/
theorem prime_exists_FECovariantAffinePrimitive {p : ℕ} (_hp : p.Prime) :
    ∃ b : WeldGroup → WeldAffineCoeff (Real.log p),
      IsFECovariantAffineCochain (Real.log p) b ∧
        twoCoboundary b = weldAffineCocycle (Real.log p) :=
  exists_FECovariantAffinePrimitive (Real.log p)

/-- The concrete fixed-operator form of the affine action: conjugating the archimedean derivative
by the prime Euler multiplier shifts it by `-log p` times the identity. -/
theorem weld_conjugation_defect_prime (p : ℕ) (hp : 0 < p) (f : ℂ → ℂ) (s : ℂ)
    (hf : DifferentiableAt ℂ f s) :
    (p : ℂ) ^ s * deriv (fun z => (p : ℂ) ^ (-z) * f z) s - deriv f s =
      (-(Real.log p) : ℂ) * f s := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpow : (p : ℂ) ^ s * (p : ℂ) ^ (-s) = 1 := by
    rw [← Complex.cpow_add _ _ hp0, show s + -s = 0 by ring, Complex.cpow_zero]
  have h := weld_commutator_prime p hp f s hf
  rw [Complex.real_smul] at h
  calc
    (p : ℂ) ^ s * deriv (fun z => (p : ℂ) ^ (-z) * f z) s - deriv f s =
        (p : ℂ) ^ s *
          (deriv (fun z => (p : ℂ) ^ (-z) * f z) s -
            (p : ℂ) ^ (-s) * deriv f s) := by
      rw [mul_sub, ← mul_assoc, hpow, one_mul]
    _ = (p : ℂ) ^ s *
        (((-(Real.log p) : ℝ) : ℂ) * ((p : ℂ) ^ (-s) * f s)) := by rw [h]
    _ = (-(Real.log p) : ℂ) * f s := by
      calc
        (p : ℂ) ^ s * (((-(Real.log p) : ℝ) : ℂ) * ((p : ℂ) ^ (-s) * f s)) =
            (((-(Real.log p) : ℝ) : ℂ)) *
              (((p : ℂ) ^ s * (p : ℂ) ^ (-s)) * f s) := by ring
        _ = (((-(Real.log p) : ℝ) : ℂ)) * f s := by rw [hpow, one_mul]
        _ = (-(Real.log p) : ℂ) * f s := by norm_cast

end GaloisForLFunctions.RHTower
