import GaloisForLFunctions.RHTower.SoninCoherentApertureCurvature

/-!
# Cubic survivor of balanced Sonin Ward completion

The actual Sonin relative ideal supports the three-block normal form
`M=ZZ†-Z†Z-2(Z†W+W†Z)`. Under its source orthogonality relations,
`Tr M=0`, while `Re Tr M³=-12 ||ZZ†W||²_HS`.

The cubic character vanishes exactly when the retained/lost Gram cross channel
`Z†W` vanishes. Both `M` and `-M` can be positive only when `Z=0`.
This identifies the operator and cubic information left by scalar Ward balancing;
it asserts neither a prime--Gamma completion nor a Hardy-index comparison.
-/

noncomputable section
namespace RHTower
open ContinuousLinearMap

private theorem tr_add {A B : evenSubspace →L[ℂ] evenSubspace}
    (hA : IsSoninPrincipalRelativeIdeal A) (hB : IsSoninPrincipalRelativeIdeal B) :
    opTrace (A + B) = opTrace A + opTrace B :=
  opTrace_add_of_memSchattenClass_one hA.memSchattenClass_one hB.memSchattenClass_one

private theorem tr_sub {A B : evenSubspace →L[ℂ] evenSubspace}
    (hA : IsSoninPrincipalRelativeIdeal A) (hB : IsSoninPrincipalRelativeIdeal B) :
    opTrace (A - B) = opTrace A - opTrace B :=
  opTrace_sub_of_memSchattenClass_one hA.memSchattenClass_one hB.memSchattenClass_one

private theorem tr_cyc {A : evenSubspace →L[ℂ] evenSubspace}
    (hA : IsSoninPrincipalRelativeIdeal A) (B : evenSubspace →L[ℂ] evenSubspace) :
    opTrace (A * B) = opTrace (B * A) :=
  (hA.memSchattenClass_one.one_opTrace_comp_comm B).symm

private theorem tr_cube_add {A B : evenSubspace →L[ℂ] evenSubspace}
    (hA : IsSoninPrincipalRelativeIdeal A) (hB : IsSoninPrincipalRelativeIdeal B) :
    opTrace ((A + B) ^ 3) = opTrace (A ^ 3) + opTrace (B ^ 3) +
      3 * opTrace (A * A * B) + 3 * opTrace (A * B * B) := by
  have hAA := hA.rightMul A
  have hAB := hA.rightMul B
  have hBA := hB.rightMul A
  have hBB := hB.rightMul B
  have hABA : opTrace (A * B * A) = opTrace (A * A * B) := by
    rw [tr_cyc hAB A, ← mul_assoc]
  have hBAA : opTrace (B * A * A) = opTrace (A * A * B) := by
    rw [mul_assoc, tr_cyc hB (A * A)]
  have hBAB : opTrace (B * A * B) = opTrace (A * B * B) := by
    rw [tr_cyc hBA B, ← mul_assoc, tr_cyc hBB A]
    rw [mul_assoc]
  have hBBA : opTrace (B * B * A) = opTrace (A * B * B) := by
    rw [tr_cyc hBB A, ← mul_assoc]
  have hexp : (A + B) ^ 3 =
      ((A * A * A + A * A * B) + (A * B * A + A * B * B)) +
        ((B * A * A + B * A * B) + (B * B * A + B * B * B)) := by noncomm_ring
  rw [hexp, tr_add
    (((hAA.rightMul A).add (hAA.rightMul B)).add
      ((hAB.rightMul A).add (hAB.rightMul B)))
    (((hBA.rightMul A).add (hBA.rightMul B)).add
      ((hBB.rightMul A).add (hBB.rightMul B))),
    tr_add ((hAA.rightMul A).add (hAA.rightMul B))
      ((hAB.rightMul A).add (hAB.rightMul B)),
    tr_add ((hBA.rightMul A).add (hBA.rightMul B))
      ((hBB.rightMul A).add (hBB.rightMul B)),
    tr_add (hAA.rightMul A) (hAA.rightMul B),
    tr_add (hAB.rightMul A) (hAB.rightMul B),
    tr_add (hBA.rightMul A) (hBA.rightMul B),
    tr_add (hBB.rightMul A) (hBB.rightMul B), hABA, hBAA, hBAB, hBBA]
  simp only [pow_succ, pow_zero, one_mul]
  ring

/-- Scalar powers factor out of the ordinary operator trace. -/
theorem opTrace_even_smul_pow (z : ℂ) (T : evenSubspace →L[ℂ] evenSubspace) (n : ℕ) :
    opTrace ((z • T) ^ n) = z ^ n * opTrace (T ^ n) := by
  have h : (z • T) ^ n = z ^ n • T ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, pow_succ, pow_succ, ih, smul_mul_even, mul_smul_even, smul_smul]
  rw [h, opTrace_smul]

private theorem orthogonal_sub_cube {R : Type*} [Ring R] (P S : R)
    (hPS : P * S = 0) (hSP : S * P = 0) :
    (P - S) ^ 3 = P ^ 3 - S ^ 3 := by
  noncomm_ring [hPS, hSP]

private theorem tr_ward_triangle
    (P A V U : evenSubspace →L[ℂ] evenSubspace)
    (hP : IsSoninPrincipalRelativeIdeal P) (hA : IsSoninPrincipalRelativeIdeal A)
    (hV : IsSoninPrincipalRelativeIdeal V) (hU : IsSoninPrincipalRelativeIdeal U)
    (hPA : P * A = 0) (hAP : A * P = 0)
    (hPV : P * V = 0) (hVP : V * P = 0)
    (hPU : P * U = 0) (hUP : U * P = 0)
    (hVA : V * A = 0) (hAU : A * U = 0)
    (hVV : V * V = 0) (hUU : U * U = 0)
    (hdiag : opTrace (P ^ 3) = opTrace (A ^ 3)) :
    opTrace ((P - (A + (2 : ℂ) • (V + U))) ^ 3) =
      -12 * opTrace (A * V * U) := by
  let C := V + U
  have hC : IsSoninPrincipalRelativeIdeal C := hV.add hU
  have hC3 : opTrace (C ^ 3) = 0 := by
    rw [tr_cube_add hV hU]
    have hV3 : V ^ 3 = 0 := by simp only [pow_succ, pow_zero, one_mul, hVV, zero_mul]
    have hU3 : U ^ 3 = 0 := by simp only [pow_succ, pow_zero, one_mul, hUU, zero_mul]
    rw [hV3, hU3, hVV, zero_mul, mul_assoc V U U, hUU, mul_zero, opTrace_zero]
    ring
  have hAAC : opTrace (A * A * C) = 0 := by
    have hAAV : opTrace (A * A * V) = 0 := by
      rw [tr_cyc (hA.rightMul A) V, ← mul_assoc, hVA, zero_mul, opTrace_zero]
    have hAAU : A * A * U = 0 := by rw [mul_assoc, hAU, mul_zero]
    rw [show A * A * C = A * A * V + A * A * U by dsimp only [C]; rw [mul_add],
      tr_add ((hA.rightMul A).rightMul V) ((hA.rightMul A).rightMul U),
      hAAV, hAAU, opTrace_zero, add_zero]
  have hACC : A * C * C = A * V * U := by
    dsimp only [C]
    noncomm_ring [hAU, hVV, hUU]
  let S := A + (2 : ℂ) • C
  have hS : IsSoninPrincipalRelativeIdeal S := hA.add (hC.smul _)
  have hS3 : opTrace (S ^ 3) = opTrace (A ^ 3) + 12 * opTrace (A * V * U) := by
    rw [tr_cube_add hA (hC.smul _), opTrace_even_smul_pow, hC3]
    simp only [mul_smul_even, smul_mul_even, smul_smul, opTrace_smul, hAAC, hACC]
    ring
  have hPS : P * S = 0 := by
    dsimp only [S, C]
    simp only [mul_add, mul_smul_even, hPA, hPV, hPU, add_zero]
    module
  have hSP : S * P = 0 := by
    dsimp only [S, C]
    simp only [add_mul, smul_mul_even, hAP, hVP, hUP, add_zero]
    module
  have hexp := orthogonal_sub_cube P S hPS hSP
  change opTrace ((P - S) ^ 3) = _
  have hP3 : IsSoninPrincipalRelativeIdeal (P ^ 3) := by
    simpa only [pow_succ, pow_zero, one_mul] using (hP.rightMul P).rightMul P
  have hScube : IsSoninPrincipalRelativeIdeal (S ^ 3) := by
    simpa only [pow_succ, pow_zero, one_mul] using (hS.rightMul S).rightMul S
  rw [hexp, tr_sub hP3 hScube, hS3, hdiag]
  ring

private theorem four_word_zero {R : Type*} [Ring R] (a b c d : R)
    (h : b * c = 0) : (a * b) * (c * d) = 0 := by
  rw [mul_assoc, ← mul_assoc b c d, h, zero_mul, mul_zero]

/-- Twice the balanced Ward completion, in its three-block source normal form. -/
def doubledRelativeWard (Z W : evenSubspace →L[ℂ] evenSubspace) :
    evenSubspace →L[ℂ] evenSubspace :=
  Z * adjoint Z - (adjoint Z * Z +
    (2 : ℂ) • (adjoint Z * W + adjoint W * Z))

/-- The exact returning-word survivor of scalar Ward cancellation. -/
theorem re_opTrace_doubledRelativeWard_cube
    (Z W : evenSubspace →L[ℂ] evenSubspace)
    (hZ : IsSoninPrincipalRelativeIdeal Z)
    (hZZ : Z * Z = 0) (hWZ : W * Z = 0) (hWZa : W * adjoint Z = 0) :
    (opTrace (doubledRelativeWard Z W ^ 3)).re =
      -12 * hsNormSq (Z * adjoint Z * W) := by
  have hZaZa : adjoint Z * adjoint Z = 0 := by
    simpa only [adjoint_mul_clm, ContinuousLinearMap.adjoint.map_zero] using
      congrArg adjoint hZZ
  have hZaWa : adjoint Z * adjoint W = 0 := by
    simpa only [adjoint_mul_clm, ContinuousLinearMap.adjoint.map_zero] using
      congrArg adjoint hWZ
  have hZWa : Z * adjoint W = 0 := by
    simpa only [adjoint_mul_clm, adjoint_adjoint,
      ContinuousLinearMap.adjoint.map_zero] using congrArg adjoint hWZa
  have hdiag : opTrace ((Z * adjoint Z) ^ 3) =
      opTrace ((adjoint Z * Z) ^ 3) := by
    calc
      _ = opTrace (Z * (adjoint Z * Z * adjoint Z * Z * adjoint Z)) := by
        congr 1
      _ = opTrace ((adjoint Z * Z * adjoint Z * Z * adjoint Z) * Z) := tr_cyc hZ _
      _ = _ := by congr 1
  have hcubic := tr_ward_triangle (Z * adjoint Z) (adjoint Z * Z)
    (adjoint Z * W) (adjoint W * Z)
    (hZ.rightMul _) (hZ.leftMul _) (hZ.adjoint.rightMul _) (hZ.leftMul _)
    (four_word_zero _ _ _ _ hZaZa) (four_word_zero _ _ _ _ hZZ)
    (four_word_zero _ _ _ _ hZaZa) (four_word_zero _ _ _ _ hWZ)
    (four_word_zero _ _ _ _ hZaWa) (four_word_zero _ _ _ _ hZZ)
    (four_word_zero _ _ _ _ hWZa) (four_word_zero _ _ _ _ hZWa)
    (four_word_zero _ _ _ _ hWZa) (four_word_zero _ _ _ _ hZWa) hdiag
  have hreturn : opTrace ((adjoint Z * Z) * (adjoint Z * W) * (adjoint W * Z)) =
      opTrace (adjoint (Z * adjoint Z * W) * (Z * adjoint Z * W)) := by
    rw [tr_cyc ((hZ.leftMul (adjoint Z)).rightMul (adjoint Z * W)) (adjoint W * Z)]
    simp only [adjoint_mul_clm, adjoint_adjoint]
    congr 1
  have hTHS : (Z * adjoint Z * W).IsHilbertSchmidt :=
    isHilbertSchmidt_of_adjoint_mul_self_memSchattenClass_one _
      (((hZ.rightMul (adjoint Z)).rightMul W).leftMul _).memSchattenClass_one
  change opTrace (doubledRelativeWard Z W ^ 3) = _ at hcubic
  rw [hreturn] at hcubic
  have hre := congrArg Complex.re hcubic
  have henergy := re_opTrace_adjoint_comp_self hTHS
  change (opTrace (adjoint (Z * adjoint Z * W) * (Z * adjoint Z * W))).re = _ at henergy
  simpa [Complex.mul_re, henergy] using hre

/-- The cubic return vanishes precisely when the retained and lost Gram channels decouple. -/
theorem relativeWard_return_eq_zero_iff (Z W : evenSubspace →L[ℂ] evenSubspace) :
    Z * adjoint Z * W = 0 ↔ adjoint Z * W = 0 := by
  constructor
  · intro h
    apply adjoint_comp_self_eq_zero_iff.mp
    change adjoint (adjoint Z * W) * (adjoint Z * W) = 0
    rw [adjoint_mul_clm, adjoint_adjoint]
    calc
      _ = adjoint W * (Z * adjoint Z * W) := by simp only [mul_assoc]
      _ = 0 := by rw [h, mul_zero]
  · intro h
    rw [mul_assoc, h, mul_zero]

/-- The doubled balanced completion has zero cubic trace exactly on the decoupled Gram locus. -/
theorem re_opTrace_doubledRelativeWard_cube_eq_zero_iff
    (Z W : evenSubspace →L[ℂ] evenSubspace)
    (hZ : IsSoninPrincipalRelativeIdeal Z)
    (hZZ : Z * Z = 0) (hWZ : W * Z = 0) (hWZa : W * adjoint Z = 0) :
    (opTrace (doubledRelativeWard Z W ^ 3)).re = 0 ↔ adjoint Z * W = 0 := by
  have hT : (Z * adjoint Z * W).IsHilbertSchmidt :=
    isHilbertSchmidt_of_adjoint_mul_self_memSchattenClass_one _
      (((hZ.rightMul (adjoint Z)).rightMul W).leftMul _).memSchattenClass_one
  rw [re_opTrace_doubledRelativeWard_cube Z W hZ hZZ hWZ hWZa,
    mul_eq_zero, hsNormSq_eq_zero_iff hT, relativeWard_return_eq_zero_iff]
  simp

/-- The normal form retains the concrete Sonin relative ideal. -/
theorem doubledRelativeWard_mem_principalRelativeIdeal
    (Z W : evenSubspace →L[ℂ] evenSubspace) (hZ : IsSoninPrincipalRelativeIdeal Z) :
    IsSoninPrincipalRelativeIdeal (doubledRelativeWard Z W) :=
  (hZ.rightMul (adjoint Z)).sub ((hZ.leftMul (adjoint Z)).add
    (((hZ.adjoint.rightMul W).add (hZ.leftMul (adjoint W))).smul _))

/-- Scalar balancing cancels the complete complex trace. -/
theorem opTrace_doubledRelativeWard_eq_zero
    (Z W : evenSubspace →L[ℂ] evenSubspace) (hZ : IsSoninPrincipalRelativeIdeal Z)
    (hWZa : W * adjoint Z = 0) : opTrace (doubledRelativeWard Z W) = 0 := by
  have hZWa : Z * adjoint W = 0 := by
    simpa only [adjoint_mul_clm, adjoint_adjoint,
      ContinuousLinearMap.adjoint.map_zero] using congrArg adjoint hWZa
  have hV : opTrace (adjoint Z * W) = 0 := by
    rw [tr_cyc hZ.adjoint W, hWZa, opTrace_zero]
  have hU : opTrace (adjoint W * Z) = 0 := by
    rw [← tr_cyc hZ (adjoint W), hZWa, opTrace_zero]
  rw [doubledRelativeWard,
    tr_sub (hZ.rightMul _) ((hZ.leftMul _).add
      (((hZ.adjoint.rightMul _).add (hZ.leftMul _)).smul _)),
    tr_add (hZ.leftMul _) (((hZ.adjoint.rightMul _).add (hZ.leftMul _)).smul _),
    opTrace_smul, tr_add (hZ.adjoint.rightMul _) (hZ.leftMul _),
    hV, hU, tr_cyc hZ (adjoint Z)]
  ring

private theorem doubledRelativeWard_conjugate_left
    (Z W : evenSubspace →L[ℂ] evenSubspace)
    (hZZ : Z * Z = 0) (hWZa : W * adjoint Z = 0) :
    Z * doubledRelativeWard Z W * adjoint Z = -(Z * adjoint Z) ^ 2 := by
  have hZWa : Z * adjoint W = 0 := by
    simpa only [adjoint_mul_clm, adjoint_adjoint,
      ContinuousLinearMap.adjoint.map_zero] using congrArg adjoint hWZa
  unfold doubledRelativeWard
  simp only [mul_sub, sub_mul, mul_add, add_mul, mul_smul_even, smul_mul_even]
  have h₁ : Z * (Z * adjoint Z) * adjoint Z = 0 := by
    rw [← mul_assoc, hZZ, zero_mul, zero_mul]
  have h₂ : Z * (adjoint Z * W) * adjoint Z = 0 := by
    rw [mul_assoc, mul_assoc, hWZa, mul_zero, mul_zero]
  have h₃ : Z * (adjoint W * Z) * adjoint Z = 0 := by
    rw [← mul_assoc, hZWa, zero_mul, zero_mul]
  simp only [h₁, h₂, h₃]
  have hm : Z * (adjoint Z * Z) * adjoint Z = (Z * adjoint Z) ^ 2 := by
    simp only [pow_two, mul_assoc]
  simp only [hm]
  module

private theorem re_inner_selfadjoint_square
    (T : evenSubspace →L[ℂ] evenSubspace) (hT : adjoint T = T) (x : evenSubspace) :
    (inner ℂ x ((T ^ 2) x)).re = ‖T x‖ ^ 2 := by
  have h := adjoint_inner_right T x (T x)
  rw [hT] at h
  change (inner ℂ x (T (T x))).re = _
  rw [h]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (T x)

private theorem positive_negative_square_conjugate
    (T S A : evenSubspace →L[ℂ] evenSubspace) (hT : T.IsPositive)
    (hA : adjoint A = A) (hconj : adjoint S * T * S = -A ^ 2) : A = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have h := hT.re_inner_nonneg_right (S x)
  change 0 ≤ (inner ℂ (S x) (T (S x))).re at h
  have he : (inner ℂ (S x) (T (S x))).re = -‖A x‖ ^ 2 := by
    rw [← adjoint_inner_right S x (T (S x))]
    change (inner ℂ x ((adjoint S * T * S) x)).re = _
    rw [hconj, _root_.neg_apply, inner_neg_right, Complex.neg_re,
      re_inner_selfadjoint_square A hA x]
  rw [he] at h
  have hn : ‖A x‖ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

/-- A nonzero lost transition prevents positivity even after scalar Ward balancing. -/
theorem doubledRelativeWard_isPositive_iff
    (Z W : evenSubspace →L[ℂ] evenSubspace)
    (hZZ : Z * Z = 0) (hWZa : W * adjoint Z = 0) :
    (doubledRelativeWard Z W).IsPositive ↔ Z = 0 := by
  constructor
  · intro hpos
    have hP : Z * adjoint Z = 0 := positive_negative_square_conjugate
      _ (adjoint Z) _ hpos (by rw [adjoint_mul_clm, adjoint_adjoint])
      (by simpa only [adjoint_adjoint] using doubledRelativeWard_conjugate_left Z W hZZ hWZa)
    have hz : adjoint Z = 0 := by
      apply adjoint_comp_self_eq_zero_iff.mp
      change adjoint (adjoint Z) * adjoint Z = 0
      rw [adjoint_adjoint]
      exact hP
    have := congrArg adjoint hz
    simpa using this
  · rintro rfl
    simp [doubledRelativeWard]

private theorem doubledRelativeWard_conjugate_right
    (Z W : evenSubspace →L[ℂ] evenSubspace)
    (hZZ : Z * Z = 0) (hWZ : W * Z = 0) :
    adjoint Z * doubledRelativeWard Z W * Z = (adjoint Z * Z) ^ 2 := by
  unfold doubledRelativeWard
  simp only [mul_sub, sub_mul, mul_add, add_mul, mul_smul_even, smul_mul_even]
  have h₁ : adjoint Z * (adjoint Z * Z) * Z = 0 := by
    simp only [mul_assoc, hZZ, mul_zero]
  have h₂ : adjoint Z * (adjoint Z * W) * Z = 0 := by
    simp only [mul_assoc, hWZ, mul_zero]
  have h₃ : adjoint Z * (adjoint W * Z) * Z = 0 := by
    simp only [mul_assoc, hZZ, mul_zero]
  have hm : adjoint Z * (Z * adjoint Z) * Z = (adjoint Z * Z) ^ 2 := by
    simp only [pow_two, mul_assoc]
  simp only [h₁, h₂, h₃, hm]
  module

/-- A nonzero transition also rules out negative semidefiniteness: balancing leaves both signs. -/
theorem neg_doubledRelativeWard_isPositive_iff
    (Z W : evenSubspace →L[ℂ] evenSubspace)
    (hZZ : Z * Z = 0) (hWZ : W * Z = 0) :
    (-doubledRelativeWard Z W).IsPositive ↔ Z = 0 := by
  constructor
  · intro hpos
    have hA : adjoint Z * Z = 0 := positive_negative_square_conjugate
      _ Z _ hpos (by rw [adjoint_mul_clm, adjoint_adjoint])
      (by simp only [mul_neg, neg_mul,
        doubledRelativeWard_conjugate_right Z W hZZ hWZ])
    exact adjoint_comp_self_eq_zero_iff.mp hA
  · rintro rfl
    simp [doubledRelativeWard]

end RHTower

end
