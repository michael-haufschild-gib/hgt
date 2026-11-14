import GaloisForLFunctions.HTGeometry.FramePurificationPartialTrace

/-!
# Finite frames and unitary orbits

A finite frame detects exactly its linear span: its nullspace is the orthogonal
complement of that span. For a unitary group orbit, the frame commutes with the
group action and its trace is the group order times the squared seed norm.
These are the finite-frame identities underlying Lemma 3.4 of Du,
*Arithmetic theta products and doubling at arbitrary level*.
-/

noncomputable section
open scoped InnerProductSpace
open Finset ContinuousLinearMap InnerProductSpace
open GaloisForLFunctions.HTGeometry
open _root_.RHTower

namespace HilbertMetric

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The frame quadratic form is the sum of the squared readings of its vectors. -/
theorem finite_frame_energy (v : ι → E) (x : E) :
    (inner ℂ x (frameOperator v x)).re = ∑ i, ‖inner ℂ (v i) x‖ ^ 2 := by
  rw [frameOperator_apply Summable.of_finite, tsum_fintype, inner_sum, Complex.re_sum]
  apply sum_congr rfl
  intro i _
  rw [inner_smul_right, ← inner_conj_symm x (v i), Complex.mul_conj,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- Zero frame output is equivalent to every individual reading vanishing. -/
theorem finite_frame_eq_zero_iff (v : ι → E) (x : E) :
    frameOperator v x = 0 ↔ ∀ i, inner ℂ (v i) x = 0 := by
  constructor
  · intro hx
    have hs : (∑ i, ‖inner ℂ (v i) x‖ ^ 2) = 0 := by
      rw [← finite_frame_energy, hx, inner_zero_right, Complex.zero_re]
    have hz := (sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖inner ℂ (v i) x‖)).mp hs
    intro i
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (hz i (mem_univ i)))
  · intro hx
    rw [frameOperator_apply Summable.of_finite]
    simp only [hx, zero_smul, tsum_zero]

/-- The frame kernel is precisely the orthogonal complement of its cyclic span. -/
theorem finite_frame_ker (v : ι → E) :
    (frameOperator v).ker = (Submodule.span ℂ (Set.range v))ᗮ := by
  ext x
  change frameOperator v x = 0 ↔ x ∈ (Submodule.span ℂ (Set.range v))ᗮ
  rw [finite_frame_eq_zero_iff, Submodule.mem_orthogonal]
  constructor
  · intro h u hu
    induction hu using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact h i
    | zero => exact inner_zero_left _
    | add y z hy hz ihy ihz => rw [inner_add_left, ihy, ihz, add_zero]
    | smul a y hy ih => rw [inner_smul_left, ih, mul_zero]
  · intro h i
    exact h (v i) (Submodule.subset_span ⟨i, rfl⟩)

/-- The frame trace counts seed mass, retaining multiplicities in the family. -/
theorem finite_frame_trace (v : ι → E) :
    opTrace (frameOperator v) = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  calc
    opTrace (frameOperator v) =
        opTrace (frameOperator v ∘L ContinuousLinearMap.id ℂ E) := by rw [comp_id]
    _ = ∑' i, inner ℂ (v i) (ContinuousLinearMap.id ℂ E (v i)) :=
      opTrace_frameOperator_comp Summable.of_finite _
    _ = ∑ i, ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
      rw [tsum_fintype]
      apply sum_congr rfl
      intro i _
      rw [id_apply, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
      rfl
    _ = _ := by push_cast; rfl

section Orbit
variable {G : Type*} [Group G] [Fintype G]

/-- The frame of a complete finite unitary orbit, with one term per group element. -/
def orbitFrame (ρ : G →* (E ≃ₗᵢ[ℂ] E)) (e : E) : E →L[ℂ] E :=
  frameOperator (fun g => ρ g e)

theorem orbitFrame_apply (ρ : G →* (E ≃ₗᵢ[ℂ] E)) (e x : E) :
    orbitFrame ρ e x = ∑ g, inner ℂ (ρ g e) x • ρ g e := by
  rw [orbitFrame, frameOperator_apply Summable.of_finite, tsum_fintype]

/-- Orbit-frame normalization commutes with every symmetry of the representation. -/
theorem orbitFrame_equivariant (ρ : G →* (E ≃ₗᵢ[ℂ] E)) (e x : E) (h : G) :
    orbitFrame ρ e (ρ h x) = ρ h (orbitFrame ρ e x) := by
  rw [orbitFrame_apply, orbitFrame_apply, map_sum]
  have hreindex := Equiv.sum_comp (Equiv.mulLeft h)
    (fun g : G => inner ℂ (ρ g e) (ρ h x) • ρ g e)
  rw [← hreindex]
  apply sum_congr rfl
  intro g _
  change inner ℂ (ρ (h * g) e) (ρ h x) • ρ (h * g) e =
    ρ h (inner ℂ (ρ g e) x • ρ g e)
  simp only [map_mul]
  change inner ℂ (ρ h (ρ g e)) (ρ h x) • ρ h (ρ g e) =
    ρ h (inner ℂ (ρ g e) x • ρ g e)
  rw [LinearIsometryEquiv.inner_map_map, map_smul]

/-- Every group element contributes the same squared seed norm to the trace. -/
theorem orbitFrame_trace (ρ : G →* (E ≃ₗᵢ[ℂ] E)) (e : E) :
    opTrace (orbitFrame ρ e) =
      (Fintype.card G : ℂ) * (‖e‖ : ℂ) ^ 2 := by
  rw [orbitFrame, finite_frame_trace]
  simp only [LinearIsometryEquiv.norm_map, sum_const, card_univ, nsmul_eq_mul]
  push_cast
  rfl

/-- An orbit is invisible exactly in the orthogonal complement of its cyclic span. -/
theorem orbitFrame_ker (ρ : G →* (E ≃ₗᵢ[ℂ] E)) (e : E) :
    (orbitFrame ρ e).ker = (Submodule.span ℂ (Set.range fun g => ρ g e))ᗮ :=
  finite_frame_ker _

end Orbit

#print axioms finite_frame_energy
#print axioms finite_frame_eq_zero_iff
#print axioms finite_frame_ker
#print axioms orbitFrame_equivariant
#print axioms orbitFrame_trace
#print axioms orbitFrame_ker

end HilbertMetric
