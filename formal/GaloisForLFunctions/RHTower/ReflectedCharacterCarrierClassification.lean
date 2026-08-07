import GaloisForLFunctions.RHTower.ReflectedCharacterBocksteinRH
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# What the reflected-character carrier hypothesis actually says

The relative-character carrier class is completely classified: the zero vector always lies in it,
and a nonzero vector lies in it exactly when the two characters coincide.  So a nonzero carrier is
not extra structure — it is the equality of the two characters, restated.

Downstream, the reflected-character RH consumer needs neither a module nor a carrier.  Its whole
content is one scalar equation at each Xi zero, `‖α q‖ = ‖β q‖`; and under the two norm
calibrations that equation is *equivalent* to the spectral point lying on the critical line.  The
consumer is therefore an exact re-encoding of the Riemann hypothesis, not a reduction of it, and
this file proves that rather than asserting it.
-/

open Complex Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The carrier class, classified -/

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- The zero vector is a carrier for every pair of characters. -/
theorem isRelativeCharacterCarrier_zero
    {V : Type*} [AddCommGroup V] [Module K V] (α β : A →ₐ[K] K) :
    IsRelativeCharacterCarrier α β (0 : V) := by
  intro a
  simp

/-- If the characters coincide, every vector is a carrier. -/
theorem isRelativeCharacterCarrier_of_eq
    {V : Type*} [AddCommGroup V] [Module K V] {α β : A →ₐ[K] K} (h : α = β) (x : V) :
    IsRelativeCharacterCarrier α β x := by
  intro a
  rw [h]

/-- **Classification.**  A nonzero vector is a relative-character carrier exactly when the two
characters coincide. -/
theorem isRelativeCharacterCarrier_iff_of_ne_zero
    {V : Type*} [AddCommGroup V] [Module K V] {α β : A →ₐ[K] K} {x : V} (hx : x ≠ 0) :
    IsRelativeCharacterCarrier α β x ↔ α = β :=
  ⟨fun hcarrier => relativeCharacters_eq_of_nonzero_carrier hx hcarrier,
    fun h => isRelativeCharacterCarrier_of_eq h x⟩

/-- Hence a nonzero carrier exists in a nontrivial module exactly when the characters coincide. -/
theorem exists_ne_zero_isRelativeCharacterCarrier_iff
    {V : Type*} [AddCommGroup V] [Module K V] [Nontrivial V] {α β : A →ₐ[K] K} :
    (∃ x : V, x ≠ 0 ∧ IsRelativeCharacterCarrier α β x) ↔ α = β := by
  constructor
  · rintro ⟨x, hx, hcarrier⟩
    exact (isRelativeCharacterCarrier_iff_of_ne_zero hx).mp hcarrier
  · intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    exact ⟨x, hx, isRelativeCharacterCarrier_of_eq h x⟩

/-! ## The consumer needs only a scalar equation -/

variable {B : Type*} [CommRing B] [Algebra ℂ B]

/-- **The calibrated norm equation is the critical line.**  With the source-inverse and
analytic-adjoint calibrations, the two character norms at `q` agree exactly when the spectral point
is on the critical line. -/
theorem reflectedCharacterNorm_eq_iff_re_eq_half
    {rho : ℂ} {q : B} {α β : B →ₐ[ℂ] ℂ}
    (hsourceInverse : ‖α q‖ = Real.exp (1 / 2 - rho.re))
    (hanalyticAdjoint : ‖β q‖ = Real.exp (rho.re - 1 / 2)) :
    ‖α q‖ = ‖β q‖ ↔ rho.re = 1 / 2 := by
  rw [hsourceInverse, hanalyticAdjoint, Real.exp_eq_exp]
  constructor <;> intro h <;> linarith

/-- The critical-line consumer, with the carrier replaced by the scalar equation. -/
theorem criticalLine_of_reflectedCharacterNorm_eq
    {rho : ℂ} {q : B} {α β : B →ₐ[ℂ] ℂ}
    (hsourceInverse : ‖α q‖ = Real.exp (1 / 2 - rho.re))
    (hanalyticAdjoint : ‖β q‖ = Real.exp (rho.re - 1 / 2))
    (hnorm : ‖α q‖ = ‖β q‖) :
    rho.re = 1 / 2 :=
  (reflectedCharacterNorm_eq_iff_re_eq_half hsourceInverse hanalyticAdjoint).mp hnorm

/-- **The RH consumer, stripped.**  No module, no carrier, no cohomology class: the calibrated
norm equation at every Xi zero already gives the Riemann hypothesis. -/
theorem riemannHypothesis_of_reflectedCharacterNorm_eq
    (q : B) (α β : ℂ → B →ₐ[ℂ] ℂ)
    (hnorm : ∀ rho, xi rho = 0 → ‖α rho q‖ = ‖β rho q‖)
    (hsourceInverse : ∀ rho, ‖α rho q‖ = Real.exp (1 / 2 - rho.re))
    (hanalyticAdjoint : ∀ rho, ‖β rho q‖ = Real.exp (rho.re - 1 / 2)) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  have hline : rho.re = 1 / 2 :=
    criticalLine_of_reflectedCharacterNorm_eq (hsourceInverse rho)
      (hanalyticAdjoint rho) (hnorm rho hzero)
  have hright : 1 / 2 < rho.re := mem_rightHalf.mp hrho
  linarith

/-- The carrier consumer is the special case in which the scalar equation is supplied by a nonzero
carrier. -/
theorem riemannHypothesis_of_nonzero_reflectedCharacterCarrier_via_norm
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (q : B) (α β : ℂ → B →ₐ[ℂ] ℂ) (x : ℂ → V)
    (hnonzero : ∀ rho, xi rho = 0 → x rho ≠ 0)
    (hcarrier : ∀ rho, xi rho = 0 →
      IsRelativeCharacterCarrier (α rho) (β rho) (x rho))
    (hsourceInverse : ∀ rho, ‖α rho q‖ = Real.exp (1 / 2 - rho.re))
    (hanalyticAdjoint : ∀ rho, ‖β rho q‖ = Real.exp (rho.re - 1 / 2)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_reflectedCharacterNorm_eq q α β (fun rho hzero => ?_)
    hsourceInverse hanalyticAdjoint
  have hαβ : α rho = β rho :=
    (isRelativeCharacterCarrier_iff_of_ne_zero (hnonzero rho hzero)).mp (hcarrier rho hzero)
  rw [hαβ]

/-- **Re-encoding verdict.**  Under the two calibrations, the scalar hypothesis of the consumer is
*equivalent* to the Riemann hypothesis itself: the critical-line conclusion at every `xi` zero is
`RiemannHypothesis` (`riemannHypothesis_iff_xi_zero_re_eq_half`).  The reflected-character programme
therefore restates RH at this point; it does not reduce it to anything weaker. -/
theorem reflectedCharacterNorm_eq_iff_criticalLine
    (q : B) (α β : ℂ → B →ₐ[ℂ] ℂ)
    (hsourceInverse : ∀ rho, ‖α rho q‖ = Real.exp (1 / 2 - rho.re))
    (hanalyticAdjoint : ∀ rho, ‖β rho q‖ = Real.exp (rho.re - 1 / 2)) :
    (∀ rho, xi rho = 0 → ‖α rho q‖ = ‖β rho q‖) ↔ RiemannHypothesis := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half]
  constructor
  · intro h rho hzero
    exact criticalLine_of_reflectedCharacterNorm_eq (hsourceInverse rho)
      (hanalyticAdjoint rho) (h rho hzero)
  · intro h rho hzero
    exact (reflectedCharacterNorm_eq_iff_re_eq_half (hsourceInverse rho)
      (hanalyticAdjoint rho)).mpr (h rho hzero)

end

end RHTower
