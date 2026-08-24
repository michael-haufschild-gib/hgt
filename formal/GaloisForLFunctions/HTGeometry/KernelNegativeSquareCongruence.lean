import GaloisForLFunctions.HTGeometry.PSDKernelOperations
import GaloisForLFunctions.RHTower.AnalyticKernelUniquenessRegion

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X Y : Type*}

/-- Pointwise diagonal scaling of a finitely supported coefficient packet by nonzero weights. -/
def finsuppDiagonal (a : X → ℂ) (ha : ∀ x, a x ≠ 0) (f : X →₀ ℂ) : X →₀ ℂ where
  support := f.support
  toFun := fun x => a x * f x
  mem_support_toFun := by
    intro x
    simp [ha x]

@[simp]
theorem finsuppDiagonal_apply (a : X → ℂ) (ha : ∀ x, a x ≠ 0)
    (f : X →₀ ℂ) (x : X) :
    finsuppDiagonal a ha f x = a x * f x := rfl

theorem finsuppDiagonal_add (a : X → ℂ) (ha : ∀ x, a x ≠ 0)
    (f g : X →₀ ℂ) :
    finsuppDiagonal a ha (f + g) =
      finsuppDiagonal a ha f + finsuppDiagonal a ha g := by
  ext x
  simp [mul_add]

theorem finsuppDiagonal_smul (a : X → ℂ) (ha : ∀ x, a x ≠ 0)
    (c : ℂ) (f : X →₀ ℂ) :
    finsuppDiagonal a ha (c • f) = c • finsuppDiagonal a ha f := by
  ext x
  simp
  ring_nf

theorem finsuppDiagonal_sum_smul {r : ℕ} (a : X → ℂ) (ha : ∀ x, a x ≠ 0)
    (c : Fin r → ℂ) (d : Fin r → X →₀ ℂ) :
    finsuppDiagonal a ha (∑ i, c i • d i) =
      ∑ i, c i • finsuppDiagonal a ha (d i) := by
  ext x
  simp [Finset.mul_sum]
  ring_nf

theorem finsuppDiagonal_ne_zero (a : X → ℂ) (ha : ∀ x, a x ≠ 0)
    {f : X →₀ ℂ} (hf : f ≠ 0) :
    finsuppDiagonal a ha f ≠ 0 := by
  intro hzero
  apply hf
  ext x
  have hx := congrArg (fun g : X →₀ ℂ => g x) hzero
  simp at hx
  exact hx.resolve_left (ha x)

/-- Literal finite negative dimension of a scalar kernel. -/
def HasFiniteKernelNegativeDimension (K : X → X → ℂ) (r : ℕ) : Prop :=
  ∃ d : Fin r → (X →₀ ℂ), ∀ c : Fin r → ℂ, c ≠ 0 →
    (kernelForm K (∑ i, c i • d i) (∑ i, c i • d i)).re < 0

theorem finiteKernelGramQuadratic_eq_kernelForm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : RHTower.AnalyticHermitianKernelRealization H)
    (S : Set ℂ) (d : S →₀ ℂ) :
    R.finiteKernelGramQuadratic S d =
      (kernelForm (fun z w : S => R.kernel z w) d d).re := by
  unfold RHTower.AnalyticHermitianKernelRealization.finiteKernelGramQuadratic
  unfold kernelForm
  apply congrArg Complex.re
  rw [Finsupp.sum_comm]
  apply Finsupp.sum_congr
  intro y _
  apply Finsupp.sum_congr
  intro x _
  rfl

theorem hasFiniteGramNegativeDimensionOn_iff_kernel
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : RHTower.AnalyticHermitianKernelRealization H)
    (S : Set ℂ) (r : ℕ) :
    R.HasFiniteGramNegativeDimensionOn S r ↔
      HasFiniteKernelNegativeDimension (fun z w : S => R.kernel z w) r := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ :=
      R.hasFiniteGramNegativeDimensionOn_literal_negative h
    refine ⟨d, fun c hc => ?_⟩
    rw [← finiteKernelGramQuadratic_eq_kernelForm R S]
    exact hd c hc
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    intro c hcunit
    have hc0 : c ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hcunit
      norm_num at hcunit
    have hneg := hd c hc0
    rw [RHTower.AnalyticHermitianKernelRealization.sectionQuadratic,
      ← R.finiteKernelCombination_sum_smul S d c,
      ← R.finiteKernelGramQuadratic_eq S,
      finiteKernelGramQuadratic_eq_kernelForm] 
    exact hneg

/-- Diagonal congruence transports kernel forms exactly. -/
theorem kernelForm_diagonal_congruence
    (K : Y → Y → ℂ) (e : X → Y) (a : X → ℂ)
    (ha : ∀ x, a x ≠ 0)
    (f g : X →₀ ℂ) :
    kernelForm (fun x y => a x * K (e x) (e y) * (starRingEnd ℂ) (a y)) f g =
      kernelForm (fun x y => K (e x) (e y))
        (finsuppDiagonal a ha f) (finsuppDiagonal a ha g) := by
  classical
  rw [kernelForm, kernelForm]
  change
    f.sum (fun y dy => g.sum fun x dx =>
      (starRingEnd ℂ) dy * dx *
        (a x * K (e x) (e y) * (starRingEnd ℂ) (a y))) =
    f.sum (fun y dy => g.sum fun x dx =>
      (starRingEnd ℂ) (a y * dy) * (a x * dx) * K (e x) (e y))
  apply Finsupp.sum_congr
  intro y _
  apply Finsupp.sum_congr
  intro x _
  rw [map_mul]
  ring_nf

/-- A diagonal pullback of a kernel cannot lose any finite negative dimension when every diagonal
weight is nonzero. The coefficient pushforward automatically combines any repeated image nodes. -/
theorem hasFiniteKernelNegativeDimension_of_diagonal_pullback
    (KX : X → X → ℂ) (KY : Y → Y → ℂ)
    (e : X → Y) (a : X → ℂ) (ha : ∀ x, a x ≠ 0)
    (hK : ∀ x y, KX x y =
      a x * KY (e x) (e y) * (starRingEnd ℂ) (a y))
    {r : ℕ} (hneg : HasFiniteKernelNegativeDimension KX r) :
    HasFiniteKernelNegativeDimension KY r := by
  classical
  obtain ⟨d, hd⟩ := hneg
  let dY : Fin r → (Y →₀ ℂ) := fun i =>
    Finsupp.mapDomain e (finsuppDiagonal a ha (d i))
  refine ⟨dY, ?_⟩
  intro c hc
  have hdiag := kernelForm_diagonal_congruence KY e a ha
    (∑ i, c i • d i) (∑ i, c i • d i)
  have hpull := kernelForm_mapDomain KY e
    (finsuppDiagonal a ha (∑ i, c i • d i))
    (finsuppDiagonal a ha (∑ i, c i • d i))
  have hsum : ∑ i, c i • dY i =
      Finsupp.mapDomain e (finsuppDiagonal a ha (∑ i, c i • d i)) := by
    simp only [dY]
    simp_rw [← Finsupp.mapDomain_smul]
    calc
      ∑ i, Finsupp.mapDomain e (c i • finsuppDiagonal a ha (d i)) =
          Finsupp.mapDomain e (∑ i, c i • finsuppDiagonal a ha (d i)) := by
        exact (map_sum (Finsupp.mapDomain.addMonoidHom e)
          (fun i => c i • finsuppDiagonal a ha (d i)) Finset.univ).symm
      _ = Finsupp.mapDomain e (finsuppDiagonal a ha (∑ i, c i • d i)) := by
        exact congrArg (Finsupp.mapDomain e)
          (finsuppDiagonal_sum_smul a ha c d).symm
  rw [hsum, hpull, ← hdiag]
  have hpoint : (fun x y =>
      a x * KY (e x) (e y) * (starRingEnd ℂ) (a y)) = KX := by
    funext x y
    exact (hK x y).symm
  rw [hpoint]
  exact hd c hc

/-- Exact invariance of every finite negative dimension under an invertible diagonal congruence
and an equivalence of node types. -/
theorem hasFiniteKernelNegativeDimension_diagonal_equiv_iff
    (KX : X → X → ℂ) (KY : Y → Y → ℂ)
    (e : X ≃ Y) (a : X → ℂ) (ha : ∀ x, a x ≠ 0)
    (hK : ∀ x y, KX x y =
      a x * KY (e x) (e y) * (starRingEnd ℂ) (a y))
    (r : ℕ) :
    HasFiniteKernelNegativeDimension KX r ↔
      HasFiniteKernelNegativeDimension KY r := by
  constructor
  · exact hasFiniteKernelNegativeDimension_of_diagonal_pullback
      KX KY e a ha hK
  · intro hneg
    let b : Y → ℂ := fun y => (a (e.symm y))⁻¹
    have hb : ∀ y, b y ≠ 0 := fun y => inv_ne_zero (ha (e.symm y))
    have hrev : ∀ y y', KY y y' =
        b y * KX (e.symm y) (e.symm y') * (starRingEnd ℂ) (b y') := by
      intro y y'
      rw [hK (e.symm y) (e.symm y'), e.apply_symm_apply, e.apply_symm_apply]
      simp only [b, map_inv₀]
      field_simp [ha (e.symm y), ha (e.symm y'),
        (map_ne_zero (starRingEnd ℂ)).mpr (ha (e.symm y'))]
    exact hasFiniteKernelNegativeDimension_of_diagonal_pullback
      KY KX e.symm b hb hrev hneg

end

end GaloisForLFunctions.HTGeometry
