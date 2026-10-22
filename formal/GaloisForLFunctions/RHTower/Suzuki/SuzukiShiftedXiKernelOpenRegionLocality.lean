import GaloisForLFunctions.RHTower.Suzuki.SuzukiShiftedXiAnalyticKernelRealization

open Complex Set
open scoped InnerProductSpace ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Regular upper-half-plane locus of the literal shifted-Xi quotient. -/
def xiShiftRegularUpperSet (omega : ℝ) : Set ℂ :=
  {z | 0 < z.im ∧ suzukiCanonicalE omega z ≠ 0}

theorem isOpen_xiShiftRegularUpperSet (omega : ℝ) :
    IsOpen (xiShiftRegularUpperSet omega) := by
  have hE : Continuous (suzukiCanonicalE omega) :=
    (differentiable_suzukiCanonicalE omega).continuous
  change IsOpen (upperHalfPlaneSet ∩
    suzukiCanonicalE omega ⁻¹' ({0} : Set ℂ)ᶜ)
  exact isOpen_upperHalfPlaneSet.inter
    ((isClosed_singleton.preimage hE).isOpen_compl)

theorem I_mem_xiShiftRegularUpperSet (omega : ℝ) :
    I ∈ xiShiftRegularUpperSet omega := by
  constructor
  · norm_num
  · rw [suzukiCanonicalE]
    simpa [I_mul_I] using xi_ne_zero_of_real (1 / 2 + omega + 1)

theorem xiShiftRegularUpperSet_nonempty (omega : ℝ) :
    (xiShiftRegularUpperSet omega).Nonempty :=
  ⟨I, I_mem_xiShiftRegularUpperSet omega⟩

/-- Every nonempty open upper-half-plane node region preserves every finite
negative dimension of the denominator-cleared shifted-Xi kernel. -/
theorem xiShiftClearedUpperKernel_openRegion_negativeDimension_iff
    (omega : ℝ) (V : Set ℂ) (hopen : IsOpen V)
    (hsub : V ⊆ upperHalfPlaneSet) (hne : V.Nonempty) (r : ℕ) :
    HasFiniteKernelNegativeDimension
        (fun z w : V => xiShiftClearedUpperKernel omega z.1 w.1) r ↔
      HasFiniteKernelNegativeDimension
        (fun z w : upperHalfPlaneSet =>
          xiShiftClearedUpperKernel omega z.1 w.1) r := by
  let R := xiShiftClearedUpperRealization omega
  let O : R.toAnalyticTotalSectionFamily.OpenRegion := {
    region := V
    isOpen_region := hopen
    region_subset := hsub
    region_nonempty := hne }
  have hloc := R.hasFiniteGramNegativeDimensionOn_openRegion_iff O r
  rw [hasFiniteGramNegativeDimensionOn_iff_kernel,
    hasFiniteGramNegativeDimensionOn_iff_kernel] at hloc
  have hV : (fun z w : V => R.kernel z.1 w.1) =
      (fun z w : V => xiShiftClearedUpperKernel omega z.1 w.1) := by
    funext z w
    exact xiShiftClearedUpperRealization_kernel_eq omega (hsub z.2) (hsub w.2)
  have hU : (fun z w : upperHalfPlaneSet => R.kernel z.1 w.1) =
      (fun z w : upperHalfPlaneSet =>
        xiShiftClearedUpperKernel omega z.1 w.1) := by
    funext z w
    exact xiShiftClearedUpperRealization_kernel_eq omega z.2 w.2
  rw [← hV, ← hU]
  exact hloc

theorem xiShiftClearedUpperKernel_regularSet_negativeDimension_iff
    (omega : ℝ) (r : ℕ) :
    HasFiniteKernelNegativeDimension
        (fun z w : xiShiftRegularUpperSet omega =>
          xiShiftClearedUpperKernel omega z.1 w.1) r ↔
      HasFiniteKernelNegativeDimension
        (fun z w : upperHalfPlaneSet =>
          xiShiftClearedUpperKernel omega z.1 w.1) r := by
  apply xiShiftClearedUpperKernel_openRegion_negativeDimension_iff
    omega (xiShiftRegularUpperSet omega)
    (isOpen_xiShiftRegularUpperSet omega)
  · intro z hz
    exact hz.1
  · exact xiShiftRegularUpperSet_nonempty omega

theorem xiShiftClearedUpperKernel_regular_congruence_iff
    (omega : ℝ) (r : ℕ) :
    HasFiniteKernelNegativeDimension
        (fun z w : xiShiftRegularUpperSet omega =>
          xiShiftClearedUpperKernel omega z.1 w.1) r ↔
      HasFiniteKernelNegativeDimension (xiShiftRegularUpperKernel omega) r := by
  let e : xiShiftRegularUpperSet omega ≃ XiShiftRegularUpperNode omega :=
    Equiv.refl _
  apply hasFiniteKernelNegativeDimension_diagonal_equiv_iff
    (fun z w : xiShiftRegularUpperSet omega =>
      xiShiftClearedUpperKernel omega z.1 w.1)
    (xiShiftRegularUpperKernel omega) e
    (fun z => suzukiCanonicalE omega z.1)
    (fun z => z.2.2)
  intro z w
  exact xiShiftClearedUpperKernel_eq_regular_congruence omega z w

/-- Literal shifted-Xi locality: restriction to any nonempty open regular node
window preserves every finite negative dimension of the full regular kernel. -/
theorem xiShiftRegularUpperKernel_openRegion_negativeDimension_iff
    (omega : ℝ) (V : Set ℂ) (hopen : IsOpen V)
    (hsub : V ⊆ upperHalfPlaneSet)
    (hregular : ∀ z ∈ V, suzukiCanonicalE omega z ≠ 0)
    (hne : V.Nonempty) (r : ℕ) :
    HasFiniteKernelNegativeDimension
        (fun z w : V =>
          upperHalfPlaneSchurKernel (suzukiCanonicalTheta omega) z.1 w.1) r ↔
      HasFiniteKernelNegativeDimension (xiShiftRegularUpperKernel omega) r := by
  have hcongV :
      HasFiniteKernelNegativeDimension
          (fun z w : V => xiShiftClearedUpperKernel omega z.1 w.1) r ↔
        HasFiniteKernelNegativeDimension
          (fun z w : V =>
            upperHalfPlaneSchurKernel (suzukiCanonicalTheta omega) z.1 w.1) r := by
    apply hasFiniteKernelNegativeDimension_diagonal_equiv_iff
      (fun z w : V => xiShiftClearedUpperKernel omega z.1 w.1)
      (fun z w : V =>
        upperHalfPlaneSchurKernel (suzukiCanonicalTheta omega) z.1 w.1)
      (Equiv.refl V) (fun z => suzukiCanonicalE omega z.1)
      (fun z => hregular z.1 z.2)
    intro z w
    let zr : XiShiftRegularUpperNode omega :=
      ⟨z.1, hsub z.2, hregular z.1 z.2⟩
    let wr : XiShiftRegularUpperNode omega :=
      ⟨w.1, hsub w.2, hregular w.1 w.2⟩
    simpa [zr, wr, xiShiftRegularUpperKernel] using
      xiShiftClearedUpperKernel_eq_regular_congruence omega zr wr
  rw [← hcongV,
    xiShiftClearedUpperKernel_openRegion_negativeDimension_iff
      omega V hopen hsub hne r,
    ← xiShiftClearedUpperKernel_regularSet_negativeDimension_iff omega r,
    xiShiftClearedUpperKernel_regular_congruence_iff omega r]

/-- Every node set accumulating inside the upper half-plane preserves every
finite negative dimension of the denominator-cleared shifted-Xi kernel. -/
theorem xiShiftClearedUpperKernel_accumulationSet_negativeDimension_iff
    (omega : ℝ) (D : Set ℂ) (hsub : D ⊆ upperHalfPlaneSet)
    (p : ℂ) (hp : p ∈ upperHalfPlaneSet)
    (hfreq : ∃ᶠ z in nhdsWithin p ({p}ᶜ), z ∈ D) (r : ℕ) :
    HasFiniteKernelNegativeDimension
        (fun z w : D => xiShiftClearedUpperKernel omega z.1 w.1) r ↔
      HasFiniteKernelNegativeDimension
        (fun z w : upperHalfPlaneSet =>
          xiShiftClearedUpperKernel omega z.1 w.1) r := by
  let R := xiShiftClearedUpperRealization omega
  let A : R.toAnalyticTotalSectionFamily.AccumulationSet := {
    nodes := D
    nodes_subset := hsub
    point := p
    point_mem_domain := hp
    frequently_nodes := hfreq }
  have hloc := R.hasFiniteGramNegativeDimensionOn_accumulationSet_iff A r
  rw [hasFiniteGramNegativeDimensionOn_iff_kernel,
    hasFiniteGramNegativeDimensionOn_iff_kernel] at hloc
  have hD : (fun z w : D => R.kernel z.1 w.1) =
      (fun z w : D => xiShiftClearedUpperKernel omega z.1 w.1) := by
    funext z w
    exact xiShiftClearedUpperRealization_kernel_eq omega (hsub z.2) (hsub w.2)
  have hU : (fun z w : upperHalfPlaneSet => R.kernel z.1 w.1) =
      (fun z w : upperHalfPlaneSet =>
        xiShiftClearedUpperKernel omega z.1 w.1) := by
    funext z w
    exact xiShiftClearedUpperRealization_kernel_eq omega z.2 w.2
  rw [← hD, ← hU]
  exact hloc

/-- Literal shifted-Xi accumulation locality: sampling on any regular node set
with an interior accumulation point preserves the full finite negative-dimension profile. -/
theorem xiShiftRegularUpperKernel_accumulationSet_negativeDimension_iff
    (omega : ℝ) (D : Set ℂ) (hsub : D ⊆ upperHalfPlaneSet)
    (hregular : ∀ z ∈ D, suzukiCanonicalE omega z ≠ 0)
    (p : ℂ) (hp : p ∈ upperHalfPlaneSet)
    (hfreq : ∃ᶠ z in nhdsWithin p ({p}ᶜ), z ∈ D) (r : ℕ) :
    HasFiniteKernelNegativeDimension
        (fun z w : D =>
          upperHalfPlaneSchurKernel (suzukiCanonicalTheta omega) z.1 w.1) r ↔
      HasFiniteKernelNegativeDimension (xiShiftRegularUpperKernel omega) r := by
  have hcongD :
      HasFiniteKernelNegativeDimension
          (fun z w : D => xiShiftClearedUpperKernel omega z.1 w.1) r ↔
        HasFiniteKernelNegativeDimension
          (fun z w : D =>
            upperHalfPlaneSchurKernel (suzukiCanonicalTheta omega) z.1 w.1) r := by
    apply hasFiniteKernelNegativeDimension_diagonal_equiv_iff
      (fun z w : D => xiShiftClearedUpperKernel omega z.1 w.1)
      (fun z w : D =>
        upperHalfPlaneSchurKernel (suzukiCanonicalTheta omega) z.1 w.1)
      (Equiv.refl D) (fun z => suzukiCanonicalE omega z.1)
      (fun z => hregular z.1 z.2)
    intro z w
    let zr : XiShiftRegularUpperNode omega :=
      ⟨z.1, hsub z.2, hregular z.1 z.2⟩
    let wr : XiShiftRegularUpperNode omega :=
      ⟨w.1, hsub w.2, hregular w.1 w.2⟩
    simpa [zr, wr, xiShiftRegularUpperKernel] using
      xiShiftClearedUpperKernel_eq_regular_congruence omega zr wr
  rw [← hcongD,
    xiShiftClearedUpperKernel_accumulationSet_negativeDimension_iff
      omega D hsub p hp hfreq r,
    ← xiShiftClearedUpperKernel_regularSet_negativeDimension_iff omega r,
    xiShiftClearedUpperKernel_regular_congruence_iff omega r]

/-- Exact finite-or-infinite shifted-divisor count on every nonempty open
regular node window. -/
theorem xiShiftRegularUpperKernel_openRegion_negativeIndex_classification
    {omega : ℝ} (homega : 0 < omega) (hnon : SuzukiShiftNonexceptional omega)
    (V : Set ℂ) (hopen : IsOpen V) (hsub : V ⊆ upperHalfPlaneSet)
    (hregular : ∀ z ∈ V, suzukiCanonicalE omega z ≠ 0)
    (hne : V.Nonempty) :
    (Finite (XiShiftRightZeroCopy omega) ∧
      HasFiniteKernelNegativeDimension
        (fun z w : V =>
          upperHalfPlaneSchurKernel (suzukiCanonicalTheta omega) z.1 w.1)
        (Nat.card (XiShiftRightZeroCopy omega)) ∧
      ∀ r : ℕ, HasFiniteKernelNegativeDimension
          (fun z w : V =>
            upperHalfPlaneSchurKernel (suzukiCanonicalTheta omega) z.1 w.1) r →
        r ≤ Nat.card (XiShiftRightZeroCopy omega)) ∨
    (Infinite (XiShiftRightZeroCopy omega) ∧
      ∀ r : ℕ, HasFiniteKernelNegativeDimension
        (fun z w : V =>
          upperHalfPlaneSchurKernel (suzukiCanonicalTheta omega) z.1 w.1) r) := by
  have hlocal := xiShiftRegularUpperKernel_openRegion_negativeDimension_iff
    omega V hopen hsub hregular hne
  simpa only [hlocal] using
    xiShiftRegularUpperKernel_negativeIndex_classification homega hnon

/-- Exact finite-or-infinite shifted-divisor count on every regular node set
with an interior accumulation point. -/
theorem xiShiftRegularUpperKernel_accumulationSet_negativeIndex_classification
    {omega : ℝ} (homega : 0 < omega) (hnon : SuzukiShiftNonexceptional omega)
    (D : Set ℂ) (hsub : D ⊆ upperHalfPlaneSet)
    (hregular : ∀ z ∈ D, suzukiCanonicalE omega z ≠ 0)
    (p : ℂ) (hp : p ∈ upperHalfPlaneSet)
    (hfreq : ∃ᶠ z in nhdsWithin p ({p}ᶜ), z ∈ D) :
    (Finite (XiShiftRightZeroCopy omega) ∧
      HasFiniteKernelNegativeDimension
        (fun z w : D =>
          upperHalfPlaneSchurKernel (suzukiCanonicalTheta omega) z.1 w.1)
        (Nat.card (XiShiftRightZeroCopy omega)) ∧
      ∀ r : ℕ, HasFiniteKernelNegativeDimension
          (fun z w : D =>
            upperHalfPlaneSchurKernel (suzukiCanonicalTheta omega) z.1 w.1) r →
        r ≤ Nat.card (XiShiftRightZeroCopy omega)) ∨
    (Infinite (XiShiftRightZeroCopy omega) ∧
      ∀ r : ℕ, HasFiniteKernelNegativeDimension
        (fun z w : D =>
          upperHalfPlaneSchurKernel (suzukiCanonicalTheta omega) z.1 w.1) r) := by
  have hlocal := xiShiftRegularUpperKernel_accumulationSet_negativeDimension_iff
    omega D hsub hregular p hp hfreq
  simpa only [hlocal] using
    xiShiftRegularUpperKernel_negativeIndex_classification homega hnon

end
end RHTower
