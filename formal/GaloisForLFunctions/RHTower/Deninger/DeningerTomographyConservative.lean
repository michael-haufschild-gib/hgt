import GaloisForLFunctions.RHTower.Deninger.DeningerDepletedQuotient
import GaloisForLFunctions.RHTower.Deninger.DeningerTomographyInjective

/-!
# The cofinal trace is algebraically conservative

The Meyer quotient is exactly the admitted sector of the depleted quotient, and because the cofinal
prime traces separate points, two cochains with the same traces are equal — so the induced map on
any quotient is injective.

* `deningerIotaEquiv` : **`M_ζ ≃ ker Per̄_p`.**
* `deningerCofinalTrace_mod_mem` : **traces conservative modulo any subspace.**
-/

namespace RHTower

open SchwartzMap

noncomputable section

/-- **The Meyer quotient is the admitted sector of the depleted quotient.**  This is the
identification behind `(9)`: `ι_p` is injective with image exactly `ker Per̄_p`. -/
def deningerIotaEquiv {L : ℝ} (hL : 0 < L) :
    DeningerMeyerQuotient ≃ₗ[ℂ] LinearMap.ker (deningerPerBar hL) :=
  (LinearEquiv.ofInjective (deningerIota L) (deningerIota_injective hL)).trans
    (LinearEquiv.ofEq _ _ (deningerIota_range_eq_perBar_ker hL))

theorem deningerIotaEquiv_apply {L : ℝ} (hL : 0 < L) (x : DeningerMeyerQuotient) :
    ((deningerIotaEquiv hL x : LinearMap.ker (deningerPerBar hL)) : DeningerDepletedQuotient L)
      = deningerIota L x := rfl

/-- **The cofinal prime traces are conservative modulo any subspace.**  This is the argument the
card gives for `(10)`: if `𝒫_Q h = 𝒫_Q b` for some `b` in the subspace, then `h = b`, so `h` is in
the subspace too. -/
theorem deningerCofinalTrace_mod_mem {Q : Set ℕ} (hQinf : Q.Infinite)
    (hQp : ∀ q ∈ Q, Nat.Prime q) (N : Submodule ℂ DeningerExpSchwartz)
    {h b : DeningerExpSchwartz} (hb : b ∈ N)
    (heq : ∀ q ∈ Q, ∀ t : ℝ,
      deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log q) t
        = deningerPeriodizationSum ((b : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log q) t) :
    h ∈ N := by
  have heqhb : h = b :=
    Subtype.ext (deningerCofinalPrimeTomography_eq h.2 b.2 hQinf hQp heq)
  rw [heqhb]
  exact hb

/-- **The induced map on any quotient is injective.**  Two classes with the same cofinal prime
traces coincide. -/
theorem deningerCofinalTrace_quotient_injective {Q : Set ℕ} (hQinf : Q.Infinite)
    (hQp : ∀ q ∈ Q, Nat.Prime q) (N : Submodule ℂ DeningerExpSchwartz)
    {h b : DeningerExpSchwartz} (hb : b ∈ N)
    (heq : ∀ q ∈ Q, ∀ t : ℝ,
      deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log q) t
        = deningerPeriodizationSum ((b : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log q) t) :
    (Submodule.Quotient.mk h : DeningerExpSchwartz ⧸ N) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact deningerCofinalTrace_mod_mem hQinf hQp N hb heq

end

end RHTower
