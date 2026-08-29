import GaloisForLFunctions.HTGeometry.SelfAdjointResolvent
import GaloisForLFunctions.HTGeometry.LinearPMapBoundedUnitaryTransport
import Mathlib.MeasureTheory.Function.L2Space
import GaloisForLFunctions.HTGeometry.MaximalRealL2Multiplication

/-!
# Multiplication symbols with no eigenvectors, and unitary transport

A multiplication operator has an eigenvector at `lam` only if the level set of its symbol at `lam`
carries mass.  For a symbol whose level sets are singletons — the dilation symbol `2t` after the
logarithmic and Fourier unitaries — no level set carries Lebesgue mass, so there is no eigenvector
at any complex number.

Absence of eigenvectors is invariant under unitary conjugation, so it transports along the two
unitaries of the dilation generator.
-/

open MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Multiplication operators -/

/-- **A multiplication operator has no eigenfunctions when no level set of its symbol carries
mass.** -/
theorem ae_eq_zero_of_mul_ae_eq_smul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℂ} {lam : ℂ} (hlevel : μ {x | g x = lam} = 0) {f : α → ℂ}
    (hf : ∀ᵐ x ∂μ, g x * f x = lam * f x) : ∀ᵐ x ∂μ, f x = 0 := by
  have hnull : ∀ᵐ x ∂μ, g x ≠ lam := by
    rw [ae_iff]
    simpa using hlevel
  filter_upwards [hf, hnull] with x hx hne
  have hzero : (g x - lam) * f x = 0 := by
    rw [sub_mul, hx, sub_self]
  rcases mul_eq_zero.1 hzero with h | h
  · exact absurd (sub_eq_zero.1 h) hne
  · exact h

/-- Every level set of a nondegenerate linear symbol on the line is at most a point. -/
theorem subsingleton_linearSymbol_level {c : ℂ} (hc : c ≠ 0) (lam : ℂ) :
    Set.Subsingleton {t : ℝ | c * (t : ℂ) = lam} := by
  intro s hs t ht
  simp only [Set.mem_setOf_eq] at hs ht
  have : (s : ℂ) = (t : ℂ) := by
    have := hs.trans ht.symm
    exact mul_left_cancel₀ hc this
  exact_mod_cast this

/-- **No level set of a nondegenerate linear symbol carries Lebesgue mass.**  This is the exact
input to the eigenvector-free law for the dilation generator, whose symbol is `2t`. -/
theorem volume_linearSymbol_level_eq_zero {c : ℂ} (hc : c ≠ 0) (lam : ℂ) :
    volume {t : ℝ | c * (t : ℂ) = lam} = 0 :=
  (subsingleton_linearSymbol_level hc lam).measure_zero _

/-- The dilation symbol `2t` has no level set of positive measure. -/
theorem volume_dilationSymbol_level_eq_zero (lam : ℂ) :
    volume {t : ℝ | (2 : ℂ) * (t : ℂ) = lam} = 0 :=
  volume_linearSymbol_level_eq_zero two_ne_zero lam

/-! ## Unitary transport of the eigenvector-free property -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Absence of eigenvectors is a unitary invariant.** -/
theorem hasNoEigenvector_unitaryConjugate {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] (U : H ≃ₗᵢ[ℂ] K) {T : K →ₗ.[ℂ] K} (hT : HasNoEigenvector T) :
    HasNoEigenvector (unitaryConjugateLinearPMap U T) := by
  intro lam x hx
  have hUx : T ⟨U (x : H), x.property⟩ = lam • (U (x : H)) := by
    have h := congrArg U hx
    rw [unitaryConjugateLinearPMap_apply] at h
    simpa [unitaryConjugateDomainMap] using h
  have hz := hT lam ⟨U (x : H), x.property⟩ hUx
  have := congrArg U.symm hz
  simpa using this

/-! ## Multiplication operators on `L²` have no eigenvectors -/

/-- **A partially defined operator acting as multiplication by a symbol with null level sets has
no eigenvectors.**  This is the spectral input `(12)` of the dilation generator: after the
logarithmic and Fourier unitaries its symbol is `2t`, whose level sets are points. -/
theorem hasNoEigenvector_of_multiplication {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {T : (Lp ℂ 2 μ) →ₗ.[ℂ] (Lp ℂ 2 μ)} {g : α → ℂ}
    (hT : ∀ f : T.domain, (T f : α → ℂ) =ᵐ[μ] fun x => g x * ((f : Lp ℂ 2 μ) : α → ℂ) x)
    (hlevel : ∀ lam : ℂ, μ {x | g x = lam} = 0) :
    HasNoEigenvector T := by
  intro lam f hf
  have hsmul : ((lam • (f : Lp ℂ 2 μ) : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ]
      fun x => lam * ((f : Lp ℂ 2 μ) : α → ℂ) x := Lp.coeFn_smul lam _
  have h1 : (T f : α → ℂ) =ᵐ[μ] fun x => lam * ((f : Lp ℂ 2 μ) : α → ℂ) x := by
    rw [hf]
    exact hsmul
  have h2 : ∀ᵐ x ∂μ, g x * ((f : Lp ℂ 2 μ) : α → ℂ) x =
      lam * ((f : Lp ℂ 2 μ) : α → ℂ) x := (hT f).symm.trans h1
  have h3 := ae_eq_zero_of_mul_ae_eq_smul (hlevel lam) h2
  exact (Lp.eq_zero_iff_ae_eq_zero).2 h3

/-- Every level set of a nondegenerate real linear symbol on the line is at most a point. -/
theorem subsingleton_realLinearSymbol_level {c : ℝ} (hc : c ≠ 0) (lam : ℂ) :
    Set.Subsingleton {t : ℝ | ((c * t : ℝ) : ℂ) = lam} := by
  intro s hs t ht
  simp only [Set.mem_setOf_eq] at hs ht
  have hst : ((c * s : ℝ) : ℂ) = ((c * t : ℝ) : ℂ) := hs.trans ht.symm
  have : c * s = c * t := by exact_mod_cast hst
  exact mul_left_cancel₀ hc this

/-- **No level set of a nondegenerate real linear symbol carries Lebesgue mass.** -/
theorem volume_realLinearSymbol_level_eq_zero {c : ℝ} (hc : c ≠ 0) (lam : ℂ) :
    volume {t : ℝ | ((c * t : ℝ) : ℂ) = lam} = 0 :=
  (subsingleton_realLinearSymbol_level hc lam).measure_zero _

/-- **The maximal real multiplication operator has no eigenvectors when its symbol has null level
sets.** -/
theorem hasNoEigenvector_maximalRealL2Mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {energy : α → ℝ} (hlevel : ∀ lam : ℂ, μ {x | ((energy x : ℝ) : ℂ) = lam} = 0) :
    HasNoEigenvector (maximalRealL2Mul μ energy) :=
  hasNoEigenvector_of_multiplication (fun f => maximalRealL2Mul_apply_ae μ energy f) hlevel

end GaloisForLFunctions.HTGeometry
