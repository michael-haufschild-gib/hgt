import GaloisForLFunctions.RHTower.MertensClockRelativeDeterminant
import GaloisForLFunctions.HTGeometry.HermitianDilationSecondJetObstruction
import GaloisForLFunctions.RHTower.TraceNormBound
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantScaling

/-!
# Fredholm determinants are determined by the traces of powers

For a Hilbert–Schmidt operator `T` on a Hilbert space with Hilbert basis `b`, write

`det(1 - zT) = det₂(1 - zT) e^{-z tr T}`

for the ordinary Fredholm determinant `fredholmDetOp b (-(z • T))`.  It is an entire function of
`z`, and near the origin

`det(1 - zT) = exp(-z tr T - ∑_{n ≥ 2} zⁿ tr(Tⁿ)/n)`,

because the coordinate matrix of `T` multiplies like `T` (Parseval) and the traces of its powers
are the operator traces `tr(Tⁿ)`.  Hence two operators, possibly on different Hilbert spaces, whose
powers have equal traces have equal Fredholm determinants everywhere (identity theorem).

For a Hilbert–Schmidt `V : E → F` the powers of `V*V` and `VV*` have equal traces
(`(V*V)^{n+1} = V* (VV*)^n V` and cyclicity), so

`det(1 - z V*V) = det(1 - z VV*)`,

and `V` restricts to an isomorphism between the `λ`-eigenspaces of `V*V` and `VV*` for `λ ≠ 0`.
The second Taylor coefficient of `det(1 - zT)` is `((tr T)² - tr(T²))/2`, and `det(1 - zT) ≠ 0`
whenever `|z| ‖T‖ < 1`.
-/

open Filter Metric Topology
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open HilbertSchmidt _root_.RHTower ContinuousLinearMap

/-! ## Coordinate matrices multiply like operators -/

section Coordinates

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ H)

omit [CompleteSpace H] in
theorem coordMatrix_smul (c : ℂ) (T : H →L[ℂ] H) :
    coordMatrix b (c • T) = c • coordMatrix b T := by
  funext p
  simp [coordMatrix_apply]

omit [CompleteSpace H] in
theorem coordMatrix_neg (T : H →L[ℂ] H) : coordMatrix b (-T) = -coordMatrix b T := by
  funext p
  simp [coordMatrix_apply, inner_neg_right]

theorem hsComp_coordMatrix (S T : H →L[ℂ] H) :
    hsComp (coordMatrix b S) (coordMatrix b T) = coordMatrix b (S ∘L T) := by
  funext p
  simp only [hsComp, coordMatrix_apply, ContinuousLinearMap.comp_apply]
  have h := b.tsum_inner_mul_inner (ContinuousLinearMap.adjoint S (b p.1)) (T (b p.2))
  rw [ContinuousLinearMap.adjoint_inner_left] at h
  rw [← h]
  refine tsum_congr fun k => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]

theorem hsPow_coordMatrix (T : H →L[ℂ] H) :
    ∀ n : ℕ, hsPow (coordMatrix b T) n = coordMatrix b (T ^ (n + 1))
  | 0 => by simp [hsPow]
  | (n + 1) => by
      rw [hsPow, hsPow_coordMatrix T n, hsComp_coordMatrix, pow_succ' T (n + 1)]
      rfl

theorem tsum_diag_coordMatrix_comp {A B : H →L[ℂ] H} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) :
    ∑' i, coordMatrix b (A ∘L B) (i, i) = opTrace (A ∘L B) := by
  rw [opTrace_comp_eq_tsum_basis hA hB b]
  exact tsum_congr fun i => coordMatrix_apply b _ _

/-- The traces of the powers of the coordinate matrix are the operator traces. -/
theorem tsum_diag_hsPow_coordMatrix {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (n : ℕ) :
    ∑' i, hsPow (coordMatrix b T) (n + 1) (i, i) = opTrace (T ^ (n + 2)) := by
  have hP : IsHilbertSchmidt (T ^ (n + 1)) := by
    rw [pow_succ]
    exact hT.comp_left (T ^ n)
  rw [hsPow_coordMatrix, show T ^ (n + 1 + 1) = T ∘L T ^ (n + 1) from pow_succ' T (n + 1)]
  exact tsum_diag_coordMatrix_comp b hT hP

end Coordinates

/-! ## The determinant `det(1 - zT)` -/

section Determinant

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ H)

/-- The Fredholm determinant `det(1 - zT) = det₂(1 - zT) e^{-z tr T}`. -/
def detOneSub (T : H →L[ℂ] H) (z : ℂ) : ℂ := fredholmDetOp b (-(z • T))

theorem detOneSub_eq {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (z : ℂ) :
    detOneSub b T z = entireDet2 (coordMatrix b T) z * Complex.exp (-z * opTrace T) := by
  rw [detOneSub, fredholmDetOp, det2Op, coordMatrix_neg, coordMatrix_smul, ← neg_smul,
    entireDet2_smul (isHS_coordMatrix b hT), ← neg_smul,
    GaloisForLFunctions.HTGeometry.opTrace_smul]
  simp only [neg_mul_neg, mul_one]

theorem differentiable_detOneSub {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    Differentiable ℂ (detOneSub b T) := by
  have h : detOneSub b T = fun z =>
      entireDet2 (coordMatrix b T) z * Complex.exp (-z * opTrace T) :=
    funext (detOneSub_eq b hT)
  rw [h]
  exact (differentiable_entireDet2 (isHS_coordMatrix b hT)).mul
    ((differentiable_id.neg.mul_const _).cexp)

/-- The determinant exponent in operator traces: `∑_{n ≥ 2} zⁿ tr(Tⁿ)/n`. -/
def traceExponent (T : H →L[ℂ] H) (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ (n + 2) / ((n + 2 : ℕ) : ℂ) * opTrace (T ^ (n + 2))

theorem fredholmExp_coordMatrix {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (z : ℂ) :
    fredholmExp (coordMatrix b T) z = traceExponent T z := by
  unfold fredholmExp traceExponent
  exact tsum_congr fun n => by rw [tsum_diag_hsPow_coordMatrix b hT n]

/-- Near the origin, `det(1 - zT) = exp(-z tr T - ∑_{n ≥ 2} zⁿ tr(Tⁿ)/n)`. -/
theorem exists_detOneSub_eq_exp {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    ∃ r > 0, ∀ z ∈ ball (0 : ℂ) r,
      detOneSub b T z = Complex.exp (-(traceExponent T z) - z * opTrace T) := by
  obtain ⟨-, r, hr, -, he⟩ := isRegularizedDet_entireDet2 (isHS_coordMatrix b hT)
  refine ⟨r, hr, fun z hz => ?_⟩
  rw [detOneSub_eq b hT, he z hz, fredholmDet, fredholmExp_coordMatrix b hT, ← Complex.exp_add]
  ring_nf

end Determinant

/-! ## Equal trace powers force equal determinants -/

section Comparison

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  {ι₁ ι₂ : Type*} [DecidableEq ι₁] [DecidableEq ι₂]

/-- **Operators whose powers have equal traces have equal Fredholm determinants.** -/
theorem detOneSub_eq_of_opTrace_pow_eq (b₁ : HilbertBasis ι₁ ℂ H₁) (b₂ : HilbertBasis ι₂ ℂ H₂)
    {T : H₁ →L[ℂ] H₁} {U : H₂ →L[ℂ] H₂} (hT : IsHilbertSchmidt T) (hU : IsHilbertSchmidt U)
    (h : ∀ n : ℕ, opTrace (T ^ (n + 1)) = opTrace (U ^ (n + 1))) :
    detOneSub b₁ T = detOneSub b₂ U := by
  obtain ⟨r₁, hr₁, he₁⟩ := exists_detOneSub_eq_exp b₁ hT
  obtain ⟨r₂, hr₂, he₂⟩ := exists_detOneSub_eq_exp b₂ hU
  have hexp : traceExponent T = traceExponent U := by
    funext z
    unfold traceExponent
    exact tsum_congr fun n => by rw [h (n + 1)]
  have htr : opTrace T = opTrace U := by simpa using h 0
  have hev : detOneSub b₁ T =ᶠ[𝓝 0] detOneSub b₂ U := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (lt_min hr₁ hr₂))] with z hz
    rw [he₁ z (ball_subset_ball (min_le_left _ _) hz),
      he₂ z (ball_subset_ball (min_le_right _ _) hz),
      hexp, htr]
  exact AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => (differentiable_detOneSub b₁ hT).analyticAt z)
    (fun z _ => (differentiable_detOneSub b₂ hU).analyticAt z) hev

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem adjoint_comp_self_pow_succ (V : E →L[ℂ] F) (n : ℕ) :
    (adjoint V ∘L V) ^ (n + 1) = adjoint V ∘L (((V ∘L adjoint V) ^ n) ∘L V) := by
  induction n with
  | zero => ext x; simp
  | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      ext x
      simp

/-- **`tr((V*V)ⁿ) = tr((VV*)ⁿ)`** for Hilbert–Schmidt `V` and `n ≥ 1`. -/
theorem opTrace_adjoint_comp_self_pow {V : E →L[ℂ] F} (hV : IsHilbertSchmidt V) (n : ℕ) :
    opTrace ((adjoint V ∘L V) ^ (n + 1)) = opTrace ((V ∘L adjoint V) ^ (n + 1)) := by
  rw [adjoint_comp_self_pow_succ, opTrace_comp_comm hV.adjoint (hV.comp_left _), pow_succ]
  rfl

/-- **`det(1 - z V*V) = det(1 - z VV*)`** for Hilbert–Schmidt `V`. -/
theorem detOneSub_adjoint_comp_self_eq (b₁ : HilbertBasis ι₁ ℂ E) (b₂ : HilbertBasis ι₂ ℂ F)
    {V : E →L[ℂ] F} (hV : IsHilbertSchmidt V) :
    detOneSub b₁ (adjoint V ∘L V) = detOneSub b₂ (V ∘L adjoint V) :=
  detOneSub_eq_of_opTrace_pow_eq b₁ b₂ (hV.comp_left _) (hV.comp_right _)
    (opTrace_adjoint_comp_self_pow hV)

/-- For `λ ≠ 0`, `V` maps the `λ`-eigenspace of `V*V` isomorphically onto that of `VV*`. -/
def eigenspaceEquiv (V : E →L[ℂ] F) {c : ℂ} (hc : c ≠ 0) :
    Module.End.eigenspace ((adjoint V ∘L V : E →L[ℂ] E) : E →ₗ[ℂ] E) c
      ≃ₗ[ℂ] Module.End.eigenspace ((V ∘L adjoint V : F →L[ℂ] F) : F →ₗ[ℂ] F) c where
  toFun x := ⟨V (x : E), by
    have hx := Module.End.mem_eigenspace_iff.mp x.2
    rw [Module.End.mem_eigenspace_iff]
    change V (adjoint V (V (x : E))) = c • V (x : E)
    have : adjoint V (V (x : E)) = c • (x : E) := hx
    rw [this, map_smul]⟩
  invFun y := ⟨c⁻¹ • adjoint V (y : F), by
    have hy := Module.End.mem_eigenspace_iff.mp y.2
    rw [Module.End.mem_eigenspace_iff]
    change adjoint V (V (c⁻¹ • adjoint V (y : F))) = c • (c⁻¹ • adjoint V (y : F))
    have : V (adjoint V (y : F)) = c • (y : F) := hy
    rw [map_smul, map_smul, this, map_smul, smul_smul, smul_smul, inv_mul_cancel₀ hc,
      mul_inv_cancel₀ hc]⟩
  left_inv x := by
    have hx := Module.End.mem_eigenspace_iff.mp x.2
    have : adjoint V (V (x : E)) = c • (x : E) := hx
    ext1
    change c⁻¹ • adjoint V (V (x : E)) = x
    rw [this, smul_smul, inv_mul_cancel₀ hc, one_smul]
  right_inv y := by
    have hy := Module.End.mem_eigenspace_iff.mp y.2
    have : V (adjoint V (y : F)) = c • (y : F) := hy
    ext1
    change V (c⁻¹ • adjoint V (y : F)) = y
    rw [map_smul, this, smul_smul, inv_mul_cancel₀ hc, one_smul]
  map_add' x y := by ext1; exact map_add V (x : E) (y : E)
  map_smul' a x := by ext1; exact map_smul V a (x : E)

/-- `V*V` and `VV*` have the same nonzero eigenvalues with the same multiplicities. -/
theorem finrank_eigenspace_adjoint_comp_self_eq (V : E →L[ℂ] F) {c : ℂ} (hc : c ≠ 0) :
    Module.finrank ℂ (Module.End.eigenspace ((adjoint V ∘L V : E →L[ℂ] E) : E →ₗ[ℂ] E) c)
      = Module.finrank ℂ
          (Module.End.eigenspace ((V ∘L adjoint V : F →L[ℂ] F) : F →ₗ[ℂ] F) c) :=
  (eigenspaceEquiv V hc).finrank_eq

end Comparison

/-! ## Second coefficient and the zero-free disc -/

section Coefficients

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ H)

/-- **The second Fredholm coefficient.**  The `z²`-coefficient of `det(1 - zT)` is
`((tr T)² - tr(T²))/2`. -/
theorem taylorCoeff_detOneSub_two {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    taylorCoeff (detOneSub b T) 2 = (opTrace T ^ 2 - opTrace (T ^ 2)) / 2 := by
  set K := coordMatrix b T
  have hK := isHS_coordMatrix b hT
  set D := entireDet2 K
  set τ := opTrace T
  set Ex : ℂ → ℂ := fun z => Complex.exp (-z * τ)
  have hD : Differentiable ℂ D := differentiable_entireDet2 hK
  have hEx : ∀ z, HasDerivAt Ex (-τ * Ex z) z := by
    intro z
    have h := ((hasDerivAt_id z).neg.mul_const τ).cexp
    simpa [Ex, mul_comm] using h
  have hf : detOneSub b T = fun z => D z * Ex z := funext (detOneSub_eq b hT)
  have hderiv : deriv (detOneSub b T) = fun z => deriv D z * Ex z + D z * (-τ * Ex z) := by
    funext z
    rw [hf]
    exact ((hD z).hasDerivAt.mul (hEx z)).deriv
  have hDD : HasDerivAt (deriv D) (deriv (deriv D) 0) 0 :=
    ((hD.analyticAt 0).deriv.differentiableAt).hasDerivAt
  have hsecond : HasDerivAt (deriv (detOneSub b T))
      (deriv (deriv D) 0 * Ex 0 + deriv D 0 * (-τ * Ex 0)
        + (deriv D 0 * (-τ * Ex 0) + D 0 * (-τ * (-τ * Ex 0)))) 0 := by
    rw [hderiv]
    exact (hDD.mul (hEx 0)).add ((hD 0).hasDerivAt.mul ((hEx 0).const_mul (-τ)))
  have hD0 : D 0 = 1 := by
    obtain ⟨-, r, hr, -, he⟩ := isRegularizedDet_entireDet2 hK
    show entireDet2 (coordMatrix b T) 0 = 1
    rw [he 0 (mem_ball_self hr), fredholmDet, fredholmExp]
    simp
  have hD1 : deriv D 0 = 0 := deriv_entireDet2_zero hK
  have hD2 : deriv (deriv D) 0 = -opTrace (T ^ 2) := by
    have h := taylorCoeff_entireDet2_two hK
    rw [taylorCoeff, iteratedDeriv_succ, iteratedDeriv_one] at h
    have htr := tsum_diag_hsPow_coordMatrix b hT 0
    rw [htr] at h
    norm_num at h
    linear_combination 2 * h
  have hE0 : Ex 0 = 1 := by simp [Ex]
  rw [taylorCoeff, iteratedDeriv_succ, iteratedDeriv_one, hsecond.deriv, hD0, hD1, hD2, hE0]
  norm_num
  ring

/-- **The zero-free disc.**  `det(1 - zT) ≠ 0` whenever `|z| ‖T‖ < 1`. -/
theorem detOneSub_ne_zero {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) {z : ℂ}
    (hz : ‖z‖ * ‖T‖ < 1) : detOneSub b T z ≠ 0 := by
  rw [detOneSub, Ne, fredholmDetOp_eq_zero_iff b (hT.smul z).neg]
  rintro ⟨v, hv0, hv⟩
  have hv' : z • T v = v := by
    have := congrArg Neg.neg hv
    simpa using this
  have hlt : ‖z • T v‖ < ‖v‖ := by
    calc ‖z • T v‖ = ‖z‖ * ‖T v‖ := norm_smul _ _
      _ ≤ ‖z‖ * (‖T‖ * ‖v‖) := mul_le_mul_of_nonneg_left (T.le_opNorm v) (norm_nonneg _)
      _ = (‖z‖ * ‖T‖) * ‖v‖ := by ring
      _ < 1 * ‖v‖ := mul_lt_mul_of_pos_right hz (norm_pos_iff.mpr hv0)
      _ = ‖v‖ := one_mul _
  rw [hv'] at hlt
  exact lt_irrefl _ hlt

end Coefficients

end GaloisForLFunctions.HTGeometry
