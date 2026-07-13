/-
# The trace on products of Hilbert–Schmidt operators

A product `A ∘L B` of two Hilbert–Schmidt operators is trace class in the factorization sense, and
its trace is computable without any spectral theory: the diagonal `⟨eᵢ, (A∘B) eᵢ⟩` rewrites as the
Hilbert–Schmidt-pairing integrand `⟨A† eᵢ, B eᵢ⟩`, so the diagonal sum converges absolutely, equals
`⟨A†, B⟩_HS`, and is independent of the Hilbert basis by the polarization basis-independence of the
Hilbert–Schmidt inner product.  Cyclicity `tr(A∘B) = tr(B∘A)` is the adjoint-reversal law of that
pairing — for maps between two different spaces it identifies a trace over `E` with a trace
over `F`.

Proved here:
* `opTrace` — the diagonal sum `∑ᵢ ⟨eᵢ, T eᵢ⟩` on the canonical Hilbert basis.
* `summable_inner_diag_comp` — the diagonal of a Hilbert–Schmidt product is absolutely summable
  over every Hilbert basis.
* `opTrace_comp_eq_hsInner` — `tr(A ∘L B) = ⟨A†, B⟩_HS`.
* `opTrace_comp_eq_tsum_basis` — the trace of a Hilbert–Schmidt product is the same diagonal sum
  over every Hilbert basis.
* `opTrace_comp_comm` — **cyclicity**: `tr(A ∘L B) = tr(B ∘L A)`, across a pair of spaces.
* `norm_opTrace_comp_le` — the trace bound `‖tr(A∘B)‖ ≤ ‖A‖_HS·‖B‖_HS`.
* `opTrace_adjoint_comp_self`, `re_opTrace_adjoint_comp_self` — the positive energy:
  `tr(T† ∘L T) = ⟨T, T⟩_HS`, with real part `‖T‖²_HS`.
* `HilbertSchmidt.matrixOf_adjoint`, `HilbertSchmidt.adjoint_toOperator` — the matrix of the
  adjoint is the conjugate-transpose kernel: the bridge intertwines the two adjoints.
* `HilbertSchmidt.opTrace_toOperator_comp` — **the trace weld**: the operator trace of
  `toOperator K ∘L toOperator L` is the kernel trace `∑ᵢ (K∘L)(i,i)`, the quantity that drives the
  kernel-side power traces, resolvent trace, and Fredholm determinants.
-/
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The **operator trace**: the diagonal sum `∑ᵢ ⟨eᵢ, T eᵢ⟩` on the canonical Hilbert basis.
Convergent and basis-independent on products of Hilbert–Schmidt operators
(`opTrace_comp_eq_tsum_basis`); junk value otherwise. -/
noncomputable def opTrace (T : E →L[𝕜] E) : 𝕜 :=
  ∑' i, inner 𝕜 (hsBasis 𝕜 E i) (T (hsBasis 𝕜 E i))

/-- The diagonal entry of a composition is the Hilbert–Schmidt pairing integrand of the
adjointed pair: `⟨x, (A∘B) x⟩ = ⟨A† x, B x⟩`. -/
theorem inner_comp_apply (A : F →L[𝕜] E) (B : E →L[𝕜] F) (x : E) :
    inner 𝕜 x ((A ∘L B) x) = inner 𝕜 ((ContinuousLinearMap.adjoint A) x) (B x) := by
  rw [comp_apply, adjoint_inner_left]

/-- The diagonal of a product of two Hilbert–Schmidt operators is summable over every Hilbert
basis. -/
theorem summable_inner_diag_comp {A : F →L[𝕜] E} {B : E →L[𝕜] F}
    (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    Summable (fun i => inner 𝕜 (b i) ((A ∘L B) (b i))) := by
  refine (hA.adjoint.summable_inner hB b).congr fun i => ?_
  exact (inner_comp_apply A B (b i)).symm

/-- **The trace of a product is the Hilbert–Schmidt pairing.**  `tr(A ∘L B) = ⟨A†, B⟩_HS` — an
unconditional identity of diagonal sums, meaningful when both operators are Hilbert–Schmidt. -/
theorem opTrace_comp_eq_hsInner (A : F →L[𝕜] E) (B : E →L[𝕜] F) :
    opTrace (A ∘L B) = hsInner (ContinuousLinearMap.adjoint A) B := by
  rw [opTrace, hsInner]
  exact tsum_congr fun i => inner_comp_apply A B _

/-- **Basis independence of the trace** on Hilbert–Schmidt products: the diagonal sum is the same
over every Hilbert basis of `E`. -/
theorem opTrace_comp_eq_tsum_basis {A : F →L[𝕜] E} {B : E →L[𝕜] F}
    (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    opTrace (A ∘L B) = ∑' i, inner 𝕜 (b i) ((A ∘L B) (b i)) := by
  rw [opTrace_comp_eq_hsInner A B, hsInner_eq_tsum_basis hA.adjoint hB b]
  exact tsum_congr fun i => (inner_comp_apply A B _).symm

/-- **Cyclicity of the trace on Hilbert–Schmidt pairs.**  `tr_E(A ∘L B) = tr_F(B ∘L A)`: the
adjoint-reversal law of the Hilbert–Schmidt inner product, read through
`tr(A∘B) = ⟨A†, B⟩_HS`. -/
theorem opTrace_comp_comm {A : F →L[𝕜] E} {B : E →L[𝕜] F}
    (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) :
    opTrace (A ∘L B) = opTrace (B ∘L A) := by
  rw [opTrace_comp_eq_hsInner A B, opTrace_comp_eq_hsInner B A]
  have h := hsInner_adjoint_adjoint hB hA.adjoint
  rw [adjoint_adjoint] at h
  exact h.symm

/-- **The trace bound.**  `‖tr(A∘B)‖ ≤ ‖A‖_HS·‖B‖_HS` — Cauchy–Schwarz for the Hilbert–Schmidt
pairing together with the adjoint isometry. -/
theorem norm_opTrace_comp_le {A : F →L[𝕜] E} {B : E →L[𝕜] F}
    (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) :
    ‖opTrace (A ∘L B)‖ ≤ hsNorm A * hsNorm B := by
  rw [opTrace_comp_eq_hsInner A B]
  have h := norm_hsInner_le hA.adjoint hB
  rwa [show hsNorm (ContinuousLinearMap.adjoint A) = hsNorm A by
    rw [hsNorm, hsNorm, hA.hsNormSq_adjoint]] at h

/-- The positive energy of an operator has trace the Hilbert–Schmidt self-pairing:
`tr(T† ∘L T) = ⟨T, T⟩_HS`. -/
theorem opTrace_adjoint_comp_self (T : E →L[𝕜] F) :
    opTrace (ContinuousLinearMap.adjoint T ∘L T) = hsInner T T := by
  rw [opTrace_comp_eq_hsInner (ContinuousLinearMap.adjoint T) T, adjoint_adjoint]

/-- `Re tr(T† ∘L T) = ‖T‖²_HS`: the trace of the positive energy is the squared Hilbert–Schmidt
norm. -/
theorem re_opTrace_adjoint_comp_self {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) :
    RCLike.re (opTrace (ContinuousLinearMap.adjoint T ∘L T)) = hsNormSq T := by
  rw [opTrace_adjoint_comp_self T]
  exact hsInner_self_re hT

end ContinuousLinearMap

namespace HilbertSchmidt

variable {ι : Type*}

/-- `toOperator` respects kernel equality: the operator depends only on the kernel. -/
theorem toOperator_congr {K K' : ι × ι → ℂ} (hK : IsHS K) (hK' : IsHS K') (h : K = K') :
    toOperator hK = toOperator hK' := by subst h; rfl

/-- **The matrix of the adjoint is the conjugate-transpose kernel.**
`matrixOf T† = (matrixOf T)ᴴ`. -/
theorem matrixOf_adjoint [DecidableEq ι]
    (T : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :
    matrixOf (ContinuousLinearMap.adjoint T) = hsAdjoint (matrixOf T) := by
  funext p
  show ContinuousLinearMap.adjoint T (lp.single 2 p.2 (1 : ℂ)) p.1
    = (starRingEnd ℂ) (T (lp.single 2 p.1 (1 : ℂ)) p.2)
  have h1 : ContinuousLinearMap.adjoint T (lp.single 2 p.2 (1 : ℂ)) p.1
      = inner ℂ (lp.single 2 p.1 (1 : ℂ)) (ContinuousLinearMap.adjoint T (lp.single 2 p.2 1)) := by
    rw [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
  have h2 : T (lp.single 2 p.1 (1 : ℂ)) p.2
      = inner ℂ (lp.single 2 p.2 (1 : ℂ)) (T (lp.single 2 p.1 1)) := by
    rw [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
  rw [h1, h2, ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm]

/-- **The bridge intertwines the adjoints**: the adjoint of the represented operator is the
operator represented by the conjugate-transpose kernel. -/
theorem adjoint_toOperator [DecidableEq ι] {K : ι × ι → ℂ} (hK : IsHS K) :
    ContinuousLinearMap.adjoint (toOperator hK) = toOperator (isHS_hsAdjoint hK) := by
  have h1 : matrixOf (ContinuousLinearMap.adjoint (toOperator hK)) = hsAdjoint K := by
    rw [matrixOf_adjoint, matrixOf_toOperator]
  have h2 := toOperator_matrixOf (isHilbertSchmidt_toOperator hK).adjoint
  rw [← h2]
  exact toOperator_congr _ _ h1

/-- **The trace weld.**  The operator trace of a represented Hilbert–Schmidt product is the kernel
trace: `tr(K· ∘L L·) = ∑ᵢ (K∘L)(i,i)` — the coordinate-free trace lands exactly on the diagonal
sums that drive the kernel-side power traces, the resolvent trace, and the Fredholm
determinants. -/
theorem opTrace_toOperator_comp [DecidableEq ι] {K L : ι × ι → ℂ} (hK : IsHS K) (hL : IsHS L) :
    ContinuousLinearMap.opTrace (toOperator hK ∘L toOperator hL)
      = ∑' i, hsComp K L (i, i) := by
  rw [ContinuousLinearMap.opTrace_comp_eq_hsInner (toOperator hK) (toOperator hL),
    adjoint_toOperator hK, hsInner_toOperator (isHS_hsAdjoint hK) hL, ← hsTrace_hsComp hK hL]

end HilbertSchmidt
