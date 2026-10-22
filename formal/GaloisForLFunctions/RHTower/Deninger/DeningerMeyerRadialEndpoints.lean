import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Meyer's radial space and its two endpoint functionals

Evaluation at a point and evaluation of the Fourier transform at zero are continuous functionals on
the Schwartz space.  Meyer's space is cut out by them together with evenness: it is the even
Schwartz functions vanishing at the origin together with their Fourier transform.  Being an
intersection of kernels of continuous functionals it is a closed subspace, and normalizing the
second endpoint map by a nonzero constant does not change the subspace it cuts out — so no extra
boundary point survives beyond the two endpoint maps.

Two further ingredients of the comparison are recorded.  An intersection of a family of subspaces
indexed by the reals reduces to the integer-indexed intersection as soon as consecutive integer
members are contained in the intermediate ones, which is why the weights of the radial space need
only be intersected over the integers.  And multiplying a vector by a positive scalar does not
move its normalization, which is why the positive rational flow acts trivially on the unit sphere.

* `deningerSchwartzEval`, `deningerFourierEval` : the two endpoint functionals.
* `DeningerMeyerCap`, `deningerMeyerCap_mem_iff`, `_isClosed` : Meyer's space and its closedness.
* `deningerMeyerCap_eq_endpoints` : the normalized endpoint maps cut out the same space.
* `deningerIInf_real_eq_int` : intersecting over the integers suffices.
* `deningerNormalize_smul` : positive scalars fix the normalization.
-/

namespace RHTower

open SchwartzMap

section SchwartzEndpoints

/-- **Evaluation of a Schwartz function**, as a continuous functional. -/
noncomputable def deningerSchwartzEval (x : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ x).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)

@[simp]
theorem deningerSchwartzEval_apply (x : ℝ) (f : 𝓢(ℝ, ℂ)) :
    deningerSchwartzEval x f = f x :=
  SchwartzMap.toBoundedContinuousFunctionCLM_apply ℂ ℝ ℂ f x

/-- **Evaluation of the Fourier transform at the origin**, as a continuous functional. -/
noncomputable def deningerFourierEval : 𝓢(ℝ, ℂ) →L[ℂ] ℂ :=
  (deningerSchwartzEval 0).comp
    ((FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ) : 𝓢(ℝ, ℂ) ≃L[ℂ] 𝓢(ℝ, ℂ)) :
      𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ))

@[simp]
theorem deningerFourierEval_apply (f : 𝓢(ℝ, ℂ)) :
    deningerFourierEval f = (FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ) f) 0 := by
  show deningerSchwartzEval 0 (FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ) f) = _
  exact deningerSchwartzEval_apply 0 _

/-- **The second endpoint map of `(10)`**, normalized by `π/2`. -/
noncomputable def deningerFourierEndpoint : 𝓢(ℝ, ℂ) →L[ℂ] ℂ :=
  (((Real.pi / 2 : ℝ) : ℂ)) • deningerFourierEval

theorem deningerFourierEndpoint_apply (f : 𝓢(ℝ, ℂ)) :
    deningerFourierEndpoint f = ((Real.pi / 2 : ℝ) : ℂ) * deningerFourierEval f := rfl

/-- **The normalization does not change the kernel.**  The two endpoint maps cut out the same
subspace, so no extra boundary point is created by the factor `π/2`. -/
theorem deningerFourierEndpoint_ker :
    LinearMap.ker (deningerFourierEndpoint : 𝓢(ℝ, ℂ) →ₗ[ℂ] ℂ)
      = LinearMap.ker (deningerFourierEval : 𝓢(ℝ, ℂ) →ₗ[ℂ] ℂ) := by
  have hpi : ((Real.pi / 2 : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact div_ne_zero Real.pi_ne_zero two_ne_zero
  refine Submodule.ext fun f => ?_
  simp only [LinearMap.mem_ker]
  constructor
  · intro h
    have h' : ((Real.pi / 2 : ℝ) : ℂ) * deningerFourierEval f = 0 := h
    exact (mul_eq_zero.mp h').resolve_left hpi
  · intro h
    have h' : deningerFourierEval f = 0 := h
    show ((Real.pi / 2 : ℝ) : ℂ) * deningerFourierEval f = 0
    rw [h', mul_zero]

end SchwartzEndpoints

section EvenSchwartz

/-- The even Schwartz functions, cut out by the differences of evaluation functionals. -/
noncomputable def deningerEvenSchwartz : Submodule ℂ 𝓢(ℝ, ℂ) :=
  ⨅ x : ℝ, LinearMap.ker
    ((deningerSchwartzEval (-x) - deningerSchwartzEval x : 𝓢(ℝ, ℂ) →L[ℂ] ℂ) :
      𝓢(ℝ, ℂ) →ₗ[ℂ] ℂ)

theorem deningerEvenSchwartz_mem_iff (f : 𝓢(ℝ, ℂ)) :
    f ∈ deningerEvenSchwartz ↔ ∀ x : ℝ, f (-x) = f x := by
  rw [deningerEvenSchwartz, Submodule.mem_iInf]
  refine forall_congr' fun x => ?_
  rw [LinearMap.mem_ker]
  show f (-x) - f x = 0 ↔ f (-x) = f x
  exact sub_eq_zero

theorem deningerEvenSchwartz_isClosed :
    IsClosed (deningerEvenSchwartz : Set 𝓢(ℝ, ℂ)) := by
  rw [deningerEvenSchwartz, Submodule.coe_iInf]
  exact isClosed_iInter fun x =>
    ContinuousLinearMap.isClosed_ker
      (deningerSchwartzEval (-x) - deningerSchwartzEval x : 𝓢(ℝ, ℂ) →L[ℂ] ℂ)

end EvenSchwartz

section MeyerCap

/-- **Meyer's space `(2)`**: the even Schwartz functions vanishing at the origin together with
their Fourier transform. -/
noncomputable def DeningerMeyerCap : Submodule ℂ 𝓢(ℝ, ℂ) :=
  deningerEvenSchwartz
    ⊓ LinearMap.ker (deningerSchwartzEval 0 : 𝓢(ℝ, ℂ) →ₗ[ℂ] ℂ)
    ⊓ LinearMap.ker (deningerFourierEval : 𝓢(ℝ, ℂ) →ₗ[ℂ] ℂ)

theorem deningerMeyerCap_mem_iff (f : 𝓢(ℝ, ℂ)) :
    f ∈ DeningerMeyerCap ↔
      (∀ x : ℝ, f (-x) = f x) ∧ f 0 = 0
        ∧ (FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ) f) 0 = 0 := by
  rw [DeningerMeyerCap, Submodule.mem_inf, Submodule.mem_inf, deningerEvenSchwartz_mem_iff,
    LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨he, h0⟩, hF⟩
    exact ⟨he, h0, hF⟩
  · rintro ⟨he, h0, hF⟩
    exact ⟨⟨he, h0⟩, hF⟩

/-- **Meyer's space is a closed subspace**, being the common kernel of continuous functionals. -/
theorem deningerMeyerCap_isClosed : IsClosed (DeningerMeyerCap : Set 𝓢(ℝ, ℂ)) := by
  rw [DeningerMeyerCap]
  refine IsClosed.inter (IsClosed.inter deningerEvenSchwartz_isClosed ?_) ?_
  · exact ContinuousLinearMap.isClosed_ker (deningerSchwartzEval 0)
  · exact ContinuousLinearMap.isClosed_ker deningerFourierEval

/-- **The relative common kernel of the two endpoint maps of `(10)` is exactly Meyer's space.**
Normalizing the Fourier endpoint by `π/2` does not change the subspace it cuts out. -/
theorem deningerMeyerCap_eq_endpoints :
    DeningerMeyerCap
      = deningerEvenSchwartz
        ⊓ LinearMap.ker (deningerSchwartzEval 0 : 𝓢(ℝ, ℂ) →ₗ[ℂ] ℂ)
        ⊓ LinearMap.ker (deningerFourierEndpoint : 𝓢(ℝ, ℂ) →ₗ[ℂ] ℂ) := by
  rw [DeningerMeyerCap, deningerFourierEndpoint_ker]

end MeyerCap

section IntegerWeights

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **Intersecting over the integers suffices.**  If every real weight is dominated by the two
neighbouring integer weights, the real-indexed intersection equals the integer-indexed one. -/
theorem deningerIInf_real_eq_int (W : ℝ → Submodule R M)
    (h : ∀ s : ℝ, W ((⌊s⌋ : ℤ) : ℝ) ⊓ W (((⌊s⌋ + 1 : ℤ) : ℝ)) ≤ W s) :
    (⨅ s : ℝ, W s) = ⨅ n : ℤ, W ((n : ℤ) : ℝ) := by
  refine le_antisymm ?_ ?_
  · exact le_iInf fun n => iInf_le W ((n : ℤ) : ℝ)
  · intro x hx
    rw [Submodule.mem_iInf] at hx ⊢
    intro s
    exact h s ⟨hx ⌊s⌋, hx (⌊s⌋ + 1)⟩

end IntegerWeights

section Normalization

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **A positive scalar does not move the normalization.**  This is why the positive rational flow
acts trivially on the unit sphere, and hence why the angular contraction commutes with it. -/
theorem deningerNormalize_smul {r : ℝ} (hr : 0 < r) (h : H) :
    ‖r • h‖⁻¹ • (r • h) = ‖h‖⁻¹ • h := by
  rcases eq_or_ne h 0 with rfl | hne
  · simp
  · have hn : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hne
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_inv, smul_smul]
    congr 1
    field_simp

end Normalization

end RHTower

