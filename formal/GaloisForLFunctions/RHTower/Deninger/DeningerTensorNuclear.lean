import GaloisForLFunctions.RHTower.Deninger.DeningerTensorBilinear

/-!
# A projective tensor product of nuclear comparison maps is nuclear

Two absolutely convergent series pass through a bounded bilinear map into a complete space: the
double family is absolutely summable and its sum is computed by iterating, giving the product of
the two sums.

Applied to the rank one representations of two nuclear comparison maps, this makes the products of
their functionals and of their vectors a nuclear representation of the comparison map of the
projective tensor seminorms, on the completed quotients: the products of functionals are
functionals of the tensor quotient, the products of vectors are its elementary tensors, and their
norms multiply to a summable family.  Hence the projective tensor product of two nuclear spaces is
nuclear.

* `deningerHasSum_bilinear` : two sums multiply through a bounded bilinear map.
* `deningerIsNuclear_tensorC` : **a tensor product of nuclear comparison maps is nuclear.**
* `deningerIsNuclearSpaceC_tensor` : **the projective tensor product of two nuclear spaces is
  nuclear.**
-/

namespace RHTower

open scoped TensorProduct

open UniformSpace ContinuousLinearMap

section BilinearHasSum

variable {𝕜 X Y Z : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]

/-- **Two absolutely convergent series multiply through a bounded bilinear map.** -/
theorem deningerHasSum_bilinear (B : X →L[𝕜] Y →L[𝕜] Z) {ι κ : Type*} {f : ι → X} {g : κ → Y}
    {a : X} {b : Y} (hf : HasSum f a) (hg : HasSum g b) (hfn : Summable fun i => ‖f i‖)
    (hgn : Summable fun j => ‖g j‖) :
    HasSum (fun ij : ι × κ => B (f ij.1) (g ij.2)) (B a b) := by
  have hbound : ∀ ij : ι × κ, ‖B (f ij.1) (g ij.2)‖ ≤ ‖B‖ * ‖f ij.1‖ * ‖g ij.2‖ :=
    fun ij => B.le_opNorm₂ (f ij.1) (g ij.2)
  have hprod : Summable fun ij : ι × κ => ‖f ij.1‖ * ‖g ij.2‖ :=
    hfn.mul_of_nonneg hgn (fun i => norm_nonneg _) fun j => norm_nonneg _
  have hnormsummable : Summable fun ij : ι × κ => ‖B‖ * ‖f ij.1‖ * ‖g ij.2‖ := by
    simpa [mul_assoc] using hprod.mul_left ‖B‖
  have hsummable : Summable fun ij : ι × κ => B (f ij.1) (g ij.2) :=
    Summable.of_norm_bounded hnormsummable hbound
  have hfiber : ∀ i : ι, Summable fun j : κ => B (f i) (g j) :=
    fun i => ((B (f i)).hasSum hg).summable
  have htsum : ∑' ij : ι × κ, B (f ij.1) (g ij.2) = B a b := by
    rw [hsummable.tsum_prod' hfiber]
    have hinner : ∀ i : ι, ∑' j : κ, B (f i) (g j) = B (f i) b :=
      fun i => ((B (f i)).hasSum hg).tsum_eq
    simp_rw [hinner]
    simpa using ((B.flip b).hasSum hf).tsum_eq
  rw [← htsum]
  exact hsummable.hasSum

end BilinearHasSum

section TensorNuclear

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- The elementary tensor map of the quotients, into the completion, as a bounded bilinear map. -/
noncomputable def deningerTensorBilinCLC (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) :
    DeningerSeminormSpace p →L[𝕜] DeningerSeminormSpace q →L[𝕜]
      Completion (DeningerSeminormSpace (deningerTensorSeminorm p q)) :=
  LinearMap.mkContinuous₂
    ((deningerTensorBilin p q).compr₂
      (Completion.toComplL (𝕜 := 𝕜)
        (E := DeningerSeminormSpace (deningerTensorSeminorm p q))).toLinearMap)
    1
    (by
      intro a b
      show ‖Completion.toComplL (𝕜 := 𝕜)
        (E := DeningerSeminormSpace (deningerTensorSeminorm p q))
          (deningerTensorBilin p q a b)‖ ≤ 1 * ‖a‖ * ‖b‖
      rw [Completion.coe_toComplL, Completion.norm_coe, one_mul]
      exact deningerTensorBilin_norm_le p q a b)

omit [CompleteSpace 𝕜] in
theorem deningerTensorBilinCLC_apply (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F)
    (a : DeningerSeminormSpace p) (b : DeningerSeminormSpace q) :
    deningerTensorBilinCLC p q a b
      = Completion.toComplL (𝕜 := 𝕜)
        (E := DeningerSeminormSpace (deningerTensorSeminorm p q))
        (deningerTensorBilin p q a b) := rfl

set_option maxHeartbeats 1000000 in
/-- **A projective tensor product of nuclear comparison maps is nuclear**, on the completed
quotients. -/
theorem deningerIsNuclear_tensorC {p₁ p₂ : Seminorm 𝕜 E} {q₁ q₂ : Seminorm 𝕜 F} {C D : ℝ}
    {hp : ∀ x, p₁ x ≤ C * p₂ x} {hq : ∀ y, q₁ y ≤ D * q₂ y}
    (hpq : ∀ u, deningerTensorSeminorm p₁ q₁ u ≤ C * D * deningerTensorSeminorm p₂ q₂ u)
    (h₁ : DeningerIsNuclear (deningerSeminormComparison hp))
    (h₂ : DeningerIsNuclear (deningerSeminormComparison hq)) :
    DeningerIsNuclear (deningerSeminormComparisonC hpq) := by
  obtain ⟨ι, φ, y, hsum₁, happ₁⟩ := h₁
  obtain ⟨κ, ψ, z, hsum₂, happ₂⟩ := h₂
  set Φ : ι × κ →
      (Completion (DeningerSeminormSpace (deningerTensorSeminorm p₂ q₂)) →L[𝕜] 𝕜) :=
    fun ij => deningerCompletionFunctional (deningerTensorDual p₂ q₂ (φ ij.1) (ψ ij.2))
    with hΦdef
  set V : ι × κ → Completion (DeningerSeminormSpace (deningerTensorSeminorm p₁ q₁)) :=
    fun ij => deningerTensorBilinCLC p₁ q₁ (y ij.1) (z ij.2) with hVdef
  have hVnorm : ∀ ij, ‖V ij‖ ≤ ‖y ij.1‖ * ‖z ij.2‖ := by
    intro ij
    show ‖deningerTensorBilinCLC p₁ q₁ (y ij.1) (z ij.2)‖ ≤ ‖y ij.1‖ * ‖z ij.2‖
    rw [deningerTensorBilinCLC_apply, Completion.coe_toComplL, Completion.norm_coe]
    exact deningerTensorBilin_norm_le p₁ q₁ (y ij.1) (z ij.2)
  have hΦnorm : ∀ ij, ‖Φ ij‖ ≤ ‖φ ij.1‖ * ‖ψ ij.2‖ := fun ij =>
    le_trans (deningerCompletionFunctional_norm_le _)
      (deningerTensorDual_norm_le p₂ q₂ (φ ij.1) (ψ ij.2))
  have hsum : Summable fun ij : ι × κ => ‖Φ ij‖ * ‖V ij‖ := by
    have hprod : Summable fun ij : ι × κ =>
        (‖φ ij.1‖ * ‖y ij.1‖) * (‖ψ ij.2‖ * ‖z ij.2‖) :=
      hsum₁.mul_of_nonneg hsum₂ (fun i => by positivity) fun j => by positivity
    refine Summable.of_nonneg_of_le (fun ij => by positivity) (fun ij => ?_) hprod
    calc ‖Φ ij‖ * ‖V ij‖ ≤ (‖φ ij.1‖ * ‖ψ ij.2‖) * (‖y ij.1‖ * ‖z ij.2‖) :=
          mul_le_mul (hΦnorm ij) (hVnorm ij) (norm_nonneg _) (by positivity)
      _ = (‖φ ij.1‖ * ‖y ij.1‖) * (‖ψ ij.2‖ * ‖z ij.2‖) := by ring
  have hnormeq : (fun ij => ‖(Φ ij).smulRight (V ij)‖) = fun ij => ‖Φ ij‖ * ‖V ij‖ := by
    funext ij
    exact ContinuousLinearMap.norm_smulRight_apply (Φ ij) (V ij)
  have hsummable : Summable fun ij => (Φ ij).smulRight (V ij) := by
    refine Summable.of_norm ?_
    rw [hnormeq]
    exact hsum
  obtain ⟨S, hS⟩ := hsummable
  have hpoint : ∀ w, HasSum (fun ij => Φ ij w • V ij) (S w) := by
    intro w
    have h1 := (ContinuousLinearMap.apply 𝕜 _ w).hasSum hS
    have heq : (fun ij => (ContinuousLinearMap.apply 𝕜 _ w) ((Φ ij).smulRight (V ij)))
        = fun ij => Φ ij w • V ij := by
      funext ij
      show ((Φ ij).smulRight (V ij)) w = Φ ij w • V ij
      exact ContinuousLinearMap.smulRight_apply
    rwa [heq] at h1
  have hmk : ∀ u : E ⊗[𝕜] F,
      HasSum (fun ij => Φ ij (deningerSeminormMkC (deningerTensorSeminorm p₂ q₂) u) • V ij)
        (deningerSeminormMkC (deningerTensorSeminorm p₁ q₁) u) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero =>
        simp only [map_zero, zero_smul]
        exact hasSum_zero
    | tmul x w =>
        have hx : HasSum (fun i => φ i (deningerSeminormMk p₂ x) • y i)
            (deningerSeminormMk p₁ x) := happ₁ (deningerSeminormMk p₂ x)
        have hw : HasSum (fun j => ψ j (deningerSeminormMk q₂ w) • z j)
            (deningerSeminormMk q₁ w) := happ₂ (deningerSeminormMk q₂ w)
        have hxn : Summable fun i => ‖φ i (deningerSeminormMk p₂ x) • y i‖ := by
          refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_)
            (hsum₁.mul_right ‖deningerSeminormMk p₂ x‖)
          rw [norm_smul]
          calc ‖φ i (deningerSeminormMk p₂ x)‖ * ‖y i‖
              ≤ (‖φ i‖ * ‖deningerSeminormMk p₂ x‖) * ‖y i‖ :=
                mul_le_mul_of_nonneg_right ((φ i).le_opNorm _) (norm_nonneg _)
            _ = ‖φ i‖ * ‖y i‖ * ‖deningerSeminormMk p₂ x‖ := by ring
        have hwn : Summable fun j => ‖ψ j (deningerSeminormMk q₂ w) • z j‖ := by
          refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
            (hsum₂.mul_right ‖deningerSeminormMk q₂ w‖)
          rw [norm_smul]
          calc ‖ψ j (deningerSeminormMk q₂ w)‖ * ‖z j‖
              ≤ (‖ψ j‖ * ‖deningerSeminormMk q₂ w‖) * ‖z j‖ :=
                mul_le_mul_of_nonneg_right ((ψ j).le_opNorm _) (norm_nonneg _)
            _ = ‖ψ j‖ * ‖z j‖ * ‖deningerSeminormMk q₂ w‖ := by ring
        have hbil := deningerHasSum_bilinear (deningerTensorBilinCLC p₁ q₁) hx hw hxn hwn
        have htarget : deningerSeminormMkC (deningerTensorSeminorm p₁ q₁) (x ⊗ₜ[𝕜] w)
            = deningerTensorBilinCLC p₁ q₁ (deningerSeminormMk p₁ x)
              (deningerSeminormMk q₁ w) := by
          rw [deningerTensorBilinCLC_apply, deningerTensorBilin_mk]
          rfl
        have hfun : ∀ ij : ι × κ,
            Φ ij (deningerSeminormMkC (deningerTensorSeminorm p₂ q₂) (x ⊗ₜ[𝕜] w)) • V ij
              = deningerTensorBilinCLC p₁ q₁ (φ ij.1 (deningerSeminormMk p₂ x) • y ij.1)
                (ψ ij.2 (deningerSeminormMk q₂ w) • z ij.2) := by
          intro ij
          have hB : deningerTensorBilinCLC p₁ q₁ (φ ij.1 (deningerSeminormMk p₂ x) • y ij.1)
                (ψ ij.2 (deningerSeminormMk q₂ w) • z ij.2)
              = (φ ij.1 (deningerSeminormMk p₂ x) * ψ ij.2 (deningerSeminormMk q₂ w)) • V ij := by
            simp only [map_smul, smul_apply, smul_smul, hVdef]
            rw [mul_comm]
          rw [hB]
          congr 1
          show deningerCompletionFunctional (deningerTensorDual p₂ q₂ (φ ij.1) (ψ ij.2))
              (Completion.toComplL (𝕜 := 𝕜)
                (E := DeningerSeminormSpace (deningerTensorSeminorm p₂ q₂))
                (deningerSeminormMk (deningerTensorSeminorm p₂ q₂) (x ⊗ₜ[𝕜] w)))
            = φ ij.1 (deningerSeminormMk p₂ x) * ψ ij.2 (deningerSeminormMk q₂ w)
          rw [deningerCompletionFunctional_coe]
          rfl
        simp only [hfun]
        rw [htarget]
        exact hbil
    | add u v hu hv =>
        have hfun : (fun ij : ι × κ =>
              Φ ij (deningerSeminormMkC (deningerTensorSeminorm p₂ q₂) (u + v)) • V ij)
            = fun ij : ι × κ =>
              Φ ij (deningerSeminormMkC (deningerTensorSeminorm p₂ q₂) u) • V ij
                + Φ ij (deningerSeminormMkC (deningerTensorSeminorm p₂ q₂) v) • V ij := by
          funext ij
          rw [map_add, map_add, add_smul]
        rw [hfun, map_add]
        exact hu.add hv
  have hSeq : S = deningerSeminormComparisonC hpq := by
    refine deningerSeminormComparisonC_ext S (deningerSeminormComparisonC hpq) fun u => ?_
    have h3 : S (deningerSeminormMkC (deningerTensorSeminorm p₂ q₂) u)
        = deningerSeminormMkC (deningerTensorSeminorm p₁ q₁) u :=
      (hpoint (deningerSeminormMkC (deningerTensorSeminorm p₂ q₂) u)).unique (hmk u)
    rw [h3]
    show deningerSeminormMkC (deningerTensorSeminorm p₁ q₁) u
      = deningerSeminormComparisonC hpq (Completion.toComplL (𝕜 := 𝕜)
        (E := DeningerSeminormSpace (deningerTensorSeminorm p₂ q₂))
        (deningerSeminormMk (deningerTensorSeminorm p₂ q₂) u))
    rw [deningerSeminormComparisonC_coe]
    rfl
  rw [← hSeq]
  exact ⟨ι × κ, Φ, V, hsum, hpoint⟩

/-- **The projective tensor product of two nuclear spaces is nuclear.**  Each pair of seminorms is
dominated by the tensor product of dominating seminorms, whose comparison map is the tensor product
of two nuclear comparison maps. -/
theorem deningerIsNuclearSpaceC_tensor {ι κ : Type*} (P : SeminormFamily 𝕜 E ι)
    (Q : SeminormFamily 𝕜 F κ) (hP : DeningerIsNuclearSpace P) (hQ : DeningerIsNuclearSpace Q) :
    DeningerIsNuclearSpaceC fun ij : ι × κ => deningerTensorSeminorm (P ij.1) (Q ij.2) := by
  rintro ⟨i, j⟩
  obtain ⟨i', C, hC, hnuc₁⟩ := hP i
  obtain ⟨j', D, hD, hnuc₂⟩ := hQ j
  have hC' : ∀ x, P i x ≤ |C| * P i' x := deningerSeminorm_le_abs hC
  have hD' : ∀ y, Q j y ≤ |D| * Q j' y := deningerSeminorm_le_abs hD
  have hnuc₁' : DeningerIsNuclear (deningerSeminormComparison hC') :=
    hnuc₁.of_eq (deningerSeminormComparison_congr hC' hC)
  have hnuc₂' : DeningerIsNuclear (deningerSeminormComparison hD') :=
    hnuc₂.of_eq (deningerSeminormComparison_congr hD' hD)
  have hpq : ∀ u, deningerTensorSeminorm (P i) (Q j) u
      ≤ |C| * |D| * deningerTensorSeminorm (P i') (Q j') u :=
    deningerTensorSeminorm_mono (abs_nonneg C) (abs_nonneg D) hC' hD'
  exact ⟨(i', j'), |C| * |D|, hpq, deningerIsNuclear_tensorC hpq hnuc₁' hnuc₂'⟩

end TensorNuclear

end RHTower
