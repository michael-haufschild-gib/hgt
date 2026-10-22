import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalAngularWeakResponse
import GaloisForLFunctions.HTGeometry.CoerciveOperatorInverse

set_option autoImplicit false
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMModularCore
noncomputable section

/-- The modular form of `2-Delta`, on the original value-plus-gradient domain. -/
def reconstructionOperator : energyDomain →L[ℂ] energyDomain :=
  ContinuousLinearMap.id ℂ energyDomain + embedding.adjoint.comp embedding

/-- The full form retains both frame derivatives and doubles the scalar mass. -/
theorem reconstructionOperator_inner (v h : energyDomain) :
    inner ℂ v (reconstructionOperator h) =
      (∑ i : Fin 2, inner ℂ ((v : EnergySpace) i.succ) ((h : EnergySpace) i.succ)) +
        2*inner ℂ (embedding v) (embedding h) := by
  change inner ℂ v (h+embedding.adjoint (embedding h)) = _
  rw [inner_add_right, embedding.adjoint_inner_right, energy_inner_decomposition]
  ring

/-- A unit coercivity floor is supplied by the constructed energy norm itself. -/
theorem reconstructionOperator_coercive (h : energyDomain) :
    ‖h‖^(2 : ℕ) ≤ (inner ℂ (reconstructionOperator h) h).re := by
  change ‖h‖^(2 : ℕ) ≤ (inner ℂ (h+embedding.adjoint (embedding h)) h).re
  rw [inner_add_left, embedding.adjoint_inner_left,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp only [Complex.add_re, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow, Complex.ofReal_re]
  nlinarith [sq_nonneg ‖embedding h‖]

/-- The angular reconstruction denominator has a bounded inverse on the actual
modular energy domain, with no spectral-parameter or domain premise. -/
theorem reconstructionOperator_inverse :
    ∃ S : energyDomain →L[ℂ] energyDomain,
      (∀ v, reconstructionOperator (S v) = v) ∧
      (∀ u, S (reconstructionOperator u) = u) ∧ ∀ v, ‖S v‖ ≤ ‖v‖ := by
  simpa only [one_mul, inv_one] using
    (exists_inverse_of_coercive (A := reconstructionOperator) (c := 1)
      (by norm_num) (fun v => by simpa only [one_mul] using reconstructionOperator_coercive v))

/-- Every modular L² forcing admits exactly one finite-energy weak reconstruction
for `2-Delta`, retaining the full original angular field. -/
theorem exists_unique_angular_reconstruction (F : Space) :
    ∃! h : energyDomain, ∀ v : energyDomain,
      (∑ i : Fin 2, inner ℂ ((v : EnergySpace) i.succ) ((h : EnergySpace) i.succ)) +
        2*inner ℂ (embedding v) (embedding h) = inner ℂ (embedding v) F := by
  obtain ⟨S, hS, hSinv, _⟩ := reconstructionOperator_inverse
  let h := S (embedding.adjoint F)
  have hh : reconstructionOperator h = embedding.adjoint F := hS _
  refine ⟨h, ?_, ?_⟩
  · intro v
    rw [← reconstructionOperator_inner, hh, embedding.adjoint_inner_right]
  · intro k hk
    have he : reconstructionOperator k = embedding.adjoint F := by
      apply ext_inner_left ℂ
      intro v
      rw [reconstructionOperator_inner, embedding.adjoint_inner_right]
      exact hk v
    calc
      k = S (reconstructionOperator k) := (hSinv k).symm
      _ = h := by rw [he]

/-- The reconstruction controls the complete energy norm by half the original
forcing norm; both gradient channels are included in that norm. -/
theorem angular_reconstruction_norm_le (F : Space) (h : energyDomain)
    (hh : ∀ v : energyDomain,
      (∑ i : Fin 2, inner ℂ ((v : EnergySpace) i.succ) ((h : EnergySpace) i.succ)) +
        2*inner ℂ (embedding v) (embedding h) = inner ℂ (embedding v) F) :
    ‖h‖ ≤ ‖F‖/2 := by
  have he := hh h
  rw [← reconstructionOperator_inner] at he
  change inner ℂ h (h+embedding.adjoint (embedding h)) = _ at he
  rw [inner_add_right, embedding.adjoint_inner_right] at he
  have hre := congrArg Complex.re he
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hre
  simp only [Complex.add_re, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow, Complex.ofReal_re] at hre
  have hb : (inner ℂ (embedding h) F).re ≤ ‖embedding h‖*‖F‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) _ _)
  have hs : (2*‖h‖)^(2 : ℕ) ≤ ‖F‖^(2 : ℕ) := by
    nlinarith [sq_nonneg (2*‖embedding h‖-‖F‖)]
  nlinarith [norm_nonneg h, norm_nonneg F]

end
end RHTower.D4BMModularCore
