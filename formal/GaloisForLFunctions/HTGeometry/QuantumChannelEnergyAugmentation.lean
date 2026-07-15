/-
# Positive-channel augmentation of a Hilbert--Schmidt master effect

If two Hilbert--Schmidt channels `C : E → F` and `B : E → G` share a source, stacking the
channels replaces the positive source effect `C†C` by `C†C + B†B`.  This is the operator-valued
version of adding one Kraus/measurement channel.  The zeroth trace gains the channel energy
`‖B‖²_HS`; the second trace gains both the self-energy `‖B†B‖²_HS` and the nonnegative
interference energy `2‖CB†‖²_HS`.

The final scalar lemma records the exact obstruction to using this positive augmentation while
claiming that a normalized second moment is unchanged: an additional balance equation is
necessary and sufficient.
-/
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace HTGeometry

noncomputable section

open ContinuousLinearMap

variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Orthogonal-instrument Bessel bound.**  If the outcome channels `A k` have
operator-norm bounds `b k` with square-summable squared bounds, then the total outcome energy
is controlled by the same scalar budget.  This is the countable-outcome form of the
Kraus/measurement identity used after outcome labels have been made orthogonal. -/
theorem orthogonalInstrumentEnergy_le
    {κ : Type*} (A : κ → E →L[ℂ] F) (b : κ → ℝ)
    (hb : ∀ k, 0 ≤ b k)
    (hA : ∀ k, ‖A k‖ ≤ b k)
    (hsum : Summable (fun k => b k ^ 2)) (x : E) :
    ∑' k, ‖A k x‖ ^ 2 ≤ (∑' k, b k ^ 2) * ‖x‖ ^ 2 := by
  have hpoint (k : κ) : ‖A k x‖ ^ 2 ≤ b k ^ 2 * ‖x‖ ^ 2 := by
    have hnorm : ‖A k x‖ ≤ b k * ‖x‖ :=
      (A k).le_opNorm x |>.trans
        (mul_le_mul_of_nonneg_right (hA k) (norm_nonneg x))
    have hsquare : ‖A k x‖ ^ 2 ≤ (b k * ‖x‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg (A k x))
        (mul_nonneg (hb k) (norm_nonneg x))).2 hnorm
    calc
      ‖A k x‖ ^ 2 ≤ (b k * ‖x‖) ^ 2 := hsquare
      _ = b k ^ 2 * ‖x‖ ^ 2 := by ring
  have hleft : Summable (fun k => ‖A k x‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hpoint
      (hsum.mul_right (‖x‖ ^ 2))
  calc
    ∑' k, ‖A k x‖ ^ 2 ≤ ∑' k, b k ^ 2 * ‖x‖ ^ 2 :=
      hleft.tsum_le_tsum hpoint (hsum.mul_right (‖x‖ ^ 2))
    _ = (∑' k, b k ^ 2) * ‖x‖ ^ 2 := tsum_mul_right

/-- The positive source effect of a Hilbert-space channel. -/
def quantumChannelEffect (C : E →L[ℂ] F) : E →L[ℂ] E :=
  ContinuousLinearMap.adjoint C ∘L C

/-- The source effect obtained by retaining both channels with their output labels distinct. -/
def augmentedQuantumChannelEffect (C : E →L[ℂ] F) (B : E →L[ℂ] G) : E →L[ℂ] E :=
  quantumChannelEffect C + quantumChannelEffect B

theorem adjoint_quantumChannelEffect (C : E →L[ℂ] F) :
    ContinuousLinearMap.adjoint (quantumChannelEffect C) = quantumChannelEffect C := by
  rw [quantumChannelEffect, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

theorem adjoint_augmentedQuantumChannelEffect (C : E →L[ℂ] F) (B : E →L[ℂ] G) :
    ContinuousLinearMap.adjoint (augmentedQuantumChannelEffect C B) =
      augmentedQuantumChannelEffect C B := by
  let adj : (E →L[ℂ] E) ≃ₗᵢ⋆[ℂ] (E →L[ℂ] E) := ContinuousLinearMap.adjoint
  rw [augmentedQuantumChannelEffect, adj.map_add,
    adjoint_quantumChannelEffect, adjoint_quantumChannelEffect]

theorem quantumChannelEffect_isHilbertSchmidt
    {C : E →L[ℂ] F} (hC : IsHilbertSchmidt C) :
    IsHilbertSchmidt (quantumChannelEffect C) := by
  exact hC.comp_left (ContinuousLinearMap.adjoint C)

theorem augmentedQuantumChannelEffect_isHilbertSchmidt
    {C : E →L[ℂ] F} {B : E →L[ℂ] G}
    (hC : IsHilbertSchmidt C) (hB : IsHilbertSchmidt B) :
    IsHilbertSchmidt (augmentedQuantumChannelEffect C B) :=
  (quantumChannelEffect_isHilbertSchmidt hC).add
    (quantumChannelEffect_isHilbertSchmidt hB)

private theorem hsInner_self_eq_ofReal
    {K L : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    {T : K →L[ℂ] L} (hT : IsHilbertSchmidt T) :
    hsInner T T = (hsNormSq T : ℂ) := by
  apply Complex.ext
  · exact hsInner_self_re hT
  · rw [Complex.ofReal_im]
    change (∑' i, inner ℂ (T (hsBasis ℂ K i)) (T (hsBasis ℂ K i))).im = 0
    rw [Complex.im_tsum (hT.summable_inner hT (hsBasis ℂ K))]
    have hzero : (fun i => (inner ℂ
        (T (hsBasis ℂ K i)) (T (hsBasis ℂ K i))).im) = fun _ => 0 := by
      funext i
      simpa using inner_self_im (𝕜 := ℂ) (T (hsBasis ℂ K i))
    rw [hzero, tsum_zero]

/-- Adding a positive channel is additive at trace degree zero.  The trace is used only on the
two displayed products of Hilbert--Schmidt operators. -/
theorem opTrace_augmentedQuantumChannelEffect
    {C : E →L[ℂ] F} {B : E →L[ℂ] G}
    (hC : IsHilbertSchmidt C) (hB : IsHilbertSchmidt B) :
    opTrace (augmentedQuantumChannelEffect C B) =
      opTrace (quantumChannelEffect C) + opTrace (quantumChannelEffect B) := by
  let b := hsBasis ℂ E
  have hCdiag := summable_inner_diag_comp hC.adjoint hC b
  have hBdiag := summable_inner_diag_comp hB.adjoint hB b
  have hCdiag' : Summable (fun i =>
      inner ℂ (b i) (quantumChannelEffect C (b i))) := by
    simpa only [quantumChannelEffect] using hCdiag
  have hBdiag' : Summable (fun i =>
      inner ℂ (b i) (quantumChannelEffect B (b i))) := by
    simpa only [quantumChannelEffect] using hBdiag
  change (∑' i, inner ℂ (b i)
      ((quantumChannelEffect C + quantumChannelEffect B) (b i))) =
    (∑' i, inner ℂ (b i) (quantumChannelEffect C (b i))) +
      ∑' i, inner ℂ (b i) (quantumChannelEffect B (b i))
  rw [← hCdiag'.tsum_add hBdiag']
  exact tsum_congr fun i => by rw [ContinuousLinearMap.add_apply, inner_add_right]

/-- Exact zeroth value relation for positive-channel augmentation. -/
theorem re_opTrace_augmentedQuantumChannelEffect
    {C : E →L[ℂ] F} {B : E →L[ℂ] G}
    (hC : IsHilbertSchmidt C) (hB : IsHilbertSchmidt B) :
    (opTrace (augmentedQuantumChannelEffect C B)).re = hsNormSq C + hsNormSq B := by
  rw [opTrace_augmentedQuantumChannelEffect hC hB, Complex.add_re]
  change RCLike.re
      (opTrace (ContinuousLinearMap.adjoint C ∘L C)) +
    RCLike.re (opTrace (ContinuousLinearMap.adjoint B ∘L B)) = _
  rw [re_opTrace_adjoint_comp_self hC, re_opTrace_adjoint_comp_self hB]

/-- The mixed effect pairing is itself a squared Hilbert--Schmidt norm.  In particular, the
interference contribution created by adding a channel is nonnegative, not an uncontrolled
complex cross term. -/
theorem hsInner_quantumChannelEffect_eq_cross_hsNormSq
    {C : E →L[ℂ] F} {B : E →L[ℂ] G}
    (hC : IsHilbertSchmidt C) (hB : IsHilbertSchmidt B) :
    hsInner (quantumChannelEffect C) (quantumChannelEffect B) =
      (hsNormSq (C ∘L ContinuousLinearMap.adjoint B) : ℂ) := by
  let T := quantumChannelEffect C
  let S := quantumChannelEffect B
  let X := C ∘L ContinuousLinearMap.adjoint B
  have hT : IsHilbertSchmidt T := quantumChannelEffect_isHilbertSchmidt hC
  have hX : IsHilbertSchmidt X := hB.adjoint.comp_left C
  have hXB : IsHilbertSchmidt (X ∘L B) := hB.comp_left X
  have hTadj : ContinuousLinearMap.adjoint T = T := by
    simpa only [T] using adjoint_quantumChannelEffect C
  have hXadj : ContinuousLinearMap.adjoint X =
      B ∘L ContinuousLinearMap.adjoint C := by
    change ContinuousLinearMap.adjoint
      (C ∘L ContinuousLinearMap.adjoint B) = _
    rw [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  change hsInner T S = (hsNormSq X : ℂ)
  calc
    hsInner T S = opTrace (ContinuousLinearMap.adjoint T ∘L S) := by
      rw [opTrace_comp_eq_hsInner, ContinuousLinearMap.adjoint_adjoint]
    _ = opTrace (T ∘L S) := by rw [hTadj]
    _ = opTrace (ContinuousLinearMap.adjoint C ∘L (X ∘L B)) := by
      apply congrArg opTrace
      apply ContinuousLinearMap.ext
      intro x
      rfl
    _ = opTrace ((X ∘L B) ∘L ContinuousLinearMap.adjoint C) :=
      opTrace_comp_comm hC.adjoint hXB
    _ = opTrace (X ∘L ContinuousLinearMap.adjoint X) := by
      apply congrArg opTrace
      apply ContinuousLinearMap.ext
      intro x
      rw [hXadj]
      rfl
    _ = opTrace (ContinuousLinearMap.adjoint X ∘L X) :=
      opTrace_comp_comm hX hX.adjoint
    _ = hsInner X X := opTrace_adjoint_comp_self X
    _ = (hsNormSq X : ℂ) := hsInner_self_eq_ofReal hX

/-- Exact second-energy value relation for channel augmentation:
`||C†C + B†B||²_HS = ||C†C||²_HS + 2||CB†||²_HS + ||B†B||²_HS`. -/
theorem hsNormSq_augmentedQuantumChannelEffect
    {C : E →L[ℂ] F} {B : E →L[ℂ] G}
    (hC : IsHilbertSchmidt C) (hB : IsHilbertSchmidt B) :
    hsNormSq (augmentedQuantumChannelEffect C B) =
      hsNormSq (quantumChannelEffect C) +
        2 * hsNormSq (C ∘L ContinuousLinearMap.adjoint B) +
          hsNormSq (quantumChannelEffect B) := by
  let T := quantumChannelEffect C
  let S := quantumChannelEffect B
  let X := C ∘L ContinuousLinearMap.adjoint B
  have hT : IsHilbertSchmidt T := quantumChannelEffect_isHilbertSchmidt hC
  have hS : IsHilbertSchmidt S := quantumChannelEffect_isHilbertSchmidt hB
  have hTS : IsHilbertSchmidt (T + S) := hT.add hS
  have hTself : (hsInner T T).re = hsNormSq T := hsInner_self_re hT
  have hSself : (hsInner S S).re = hsNormSq S := hsInner_self_re hS
  have hcross : hsInner T S = (hsNormSq X : ℂ) := by
    simpa only [T, S, X] using
      hsInner_quantumChannelEffect_eq_cross_hsNormSq hC hB
  have hcross' : hsInner S T = (hsNormSq X : ℂ) := by
    calc
      hsInner S T = star (hsInner T S) := hsInner_conj_symm S T
      _ = (hsNormSq X : ℂ) := by rw [hcross]; simp
  have hpair :
      hsInner (T + S) (T + S) =
        (hsInner T T + hsInner T S) + (hsInner S T + hsInner S S) := by
    calc
      hsInner (T + S) (T + S) =
          hsInner T (T + S) + hsInner S (T + S) :=
        hsInner_add_left hT hS hTS
      _ = (hsInner T T + hsInner T S) +
          (hsInner S T + hsInner S S) := by
        rw [hsInner_add_right hT hT hS, hsInner_add_right hS hT hS]
  change hsNormSq (T + S) =
    hsNormSq T + 2 * hsNormSq X + hsNormSq S
  calc
    hsNormSq (T + S) = Complex.re (hsInner (T + S) (T + S)) :=
      (hsInner_self_re hTS).symm
    _ = hsNormSq T + 2 * hsNormSq X + hsNormSq S := by
      rw [hpair]
      rw [hcross, hcross']
      simp only [Complex.add_re, Complex.ofReal_re]
      rw [hTself, hSself]
      ring

/-- Exact real second-trace relation for the augmented positive effect. -/
theorem re_opTrace_augmentedQuantumChannelEffect_sq
    {C : E →L[ℂ] F} {B : E →L[ℂ] G}
    (hC : IsHilbertSchmidt C) (hB : IsHilbertSchmidt B) :
    (opTrace (augmentedQuantumChannelEffect C B ∘L
      augmentedQuantumChannelEffect C B)).re =
        hsNormSq (quantumChannelEffect C) +
          2 * hsNormSq (C ∘L ContinuousLinearMap.adjoint B) +
            hsNormSq (quantumChannelEffect B) := by
  let A := augmentedQuantumChannelEffect C B
  have hA : IsHilbertSchmidt A := augmentedQuantumChannelEffect_isHilbertSchmidt hC hB
  calc
    (opTrace (A ∘L A)).re =
        (opTrace (ContinuousLinearMap.adjoint A ∘L A)).re := by
      rw [adjoint_augmentedQuantumChannelEffect]
    _ = hsNormSq A := re_opTrace_adjoint_comp_self hA
    _ = hsNormSq (quantumChannelEffect C) +
          2 * hsNormSq (C ∘L ContinuousLinearMap.adjoint B) +
            hsNormSq (quantumChannelEffect B) :=
      hsNormSq_augmentedQuantumChannelEffect hC hB

/-- A nonzero added channel supplies a strictly positive zeroth trace even if the original
channel vanishes. -/
theorem re_opTrace_augmentedQuantumChannelEffect_pos_of_right_ne
    {C : E →L[ℂ] F} {B : E →L[ℂ] G}
    (hC : IsHilbertSchmidt C) (hB : IsHilbertSchmidt B) (hBne : B ≠ 0) :
    0 < (opTrace (augmentedQuantumChannelEffect C B)).re := by
  rw [re_opTrace_augmentedQuantumChannelEffect hC hB]
  have hBn : hsNormSq B ≠ 0 := by
    intro hzero
    exact hBne ((hsNormSq_eq_zero_iff hB).mp hzero)
  exact add_pos_of_nonneg_of_pos (hsNormSq_nonneg C)
    (lt_of_le_of_ne (hsNormSq_nonneg B) (Ne.symm hBn))

/-- Projective normalization does not erase an added positive channel automatically.  If the
old zeroth value is `e`, the added zeroth value is `b`, the old second value is `q`, and the
added second increment is `d`, equality of the normalized second values is equivalent to the
single balance equation `e*d = b*q`. -/
theorem augmentedNormalizedSecondValue_eq_iff
    (e b q d : ℝ) (he : e ≠ 0) (heb : e + b ≠ 0) :
    (q + d) / (e + b) = q / e ↔ e * d = b * q := by
  constructor
  · intro h
    field_simp [he, heb] at h
    nlinarith
  · intro h
    field_simp [he, heb]
    nlinarith

end

end HTGeometry
