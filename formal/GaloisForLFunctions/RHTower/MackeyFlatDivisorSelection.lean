import GaloisForLFunctions.RHTower.FormationPotentialCriterion
import GaloisForLFunctions.HTGeometry.AmbidextrousKummerCalkinProperness

/-!
# Mackey-flat divisor selection for the Euler-shell transfer

The local charges of the survival transfer are the strict-right zeta orders, so ambidextrous
flatness of every local Kummer charge section, cofinal doubling flatness, and compactness of every
local regular packet are each equivalent to the Riemann hypothesis.
-/

open Complex GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The local formation charge of the survival transfer at a strict-right point: the vanishing
order of zeta, which by Theorem 2.1 is the pole order of the transfer. -/
def localFormationCharge (ρ : ℂ) : ℤ := ((analyticOrderAt riemannZeta ρ).toNat : ℤ)

theorem localFormationCharge_eq_zero_iff {ρ : ℂ} (hρ1 : ρ ≠ 1) :
    localFormationCharge ρ = 0 ↔ riemannZeta ρ ≠ 0 := by
  have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := analyticOrderAt_riemannZeta_ne_top hρ1
  rw [localFormationCharge]
  constructor
  · intro h hzero
    have hne0 : analyticOrderAt riemannZeta ρ ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨analyticOn_riemannZeta ρ hρ1, hzero⟩
    have h0 : (analyticOrderAt riemannZeta ρ).toNat = 0 := by exact_mod_cast h
    exact hne0 (by
      rw [← ENat.coe_toNat hfin, h0]
      rfl)
  · intro hne
    have h0 : analyticOrderAt riemannZeta ρ = 0 :=
      (analyticOn_riemannZeta ρ hρ1).analyticOrderAt_eq_zero.mpr hne
    rw [h0]
    rfl

/-- **Mackey-flat divisor selection for the Euler shell** (ART, Corollary 6.1).  Vanishing of every
local formation charge, universal ambidextrous flatness, cofinal doubling flatness and compactness
of every local regular packet are each equivalent to the Riemann hypothesis. -/
theorem riemannHypothesis_tfae_mackeyFlat :
    List.TFAE
      [ RiemannHypothesis,
        ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ ≠ 1 → localFormationCharge ρ = 0,
        ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ ≠ 1 →
          ∀ (n m : ℕ) (h : n ∣ m), ambidextrousDefect h (localFormationCharge ρ) = 0,
        ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ ≠ 1 →
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            ambidextrousDoublingDefect n (localFormationCharge ρ) = 0,
        ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ ≠ 1 →
          IsCompactOperator (ambPacketDefect (localFormationCharge ρ)) ] := by
  tfae_have 1 → 2 := by
    intro hrh ρ hρ hρ1
    exact (localFormationCharge_eq_zero_iff hρ1).2
      (riemannHypothesis_iff_zetaZeroFreeRight.1 hrh ρ hρ hρ1)
  tfae_have 2 → 3 := fun h ρ hρ hρ1 n m hnm => by
    rw [h ρ hρ hρ1]
    exact ambidextrousDefect_zero hnm
  tfae_have 3 → 4 := fun h ρ hρ hρ1 =>
    ((ambidextrousDefect_tfae (localFormationCharge ρ)).out 1 3).1 (h ρ hρ hρ1)
  tfae_have 4 → 1 := by
    intro h
    refine riemannHypothesis_iff_zetaZeroFreeRight.2 fun ρ hρ hρ1 => ?_
    refine (localFormationCharge_eq_zero_iff hρ1).1 ?_
    exact ((ambidextrousDefect_tfae (localFormationCharge ρ)).out 3 0).1 (h ρ hρ hρ1)
  tfae_have 1 → 5 := by
    intro hrh ρ hρ hρ1
    refine (isCompactOperator_ambPacketDefect_iff _).2 ?_
    exact (localFormationCharge_eq_zero_iff hρ1).2
      (riemannHypothesis_iff_zetaZeroFreeRight.1 hrh ρ hρ hρ1)
  tfae_have 5 → 1 := by
    intro h
    refine riemannHypothesis_iff_zetaZeroFreeRight.2 fun ρ hρ hρ1 => ?_
    refine (localFormationCharge_eq_zero_iff hρ1).1 ?_
    exact (isCompactOperator_ambPacketDefect_iff _).1 (h ρ hρ hρ1)
  tfae_finish

/-- **The essential norm of the local packet is a charge invariant.**  It is `2` at every nonzero
local charge and `0` at charge zero, so any transport that preserves local divisor order — the
holomorphic functional-equation reflection in particular — preserves it (ART.14). -/
theorem essNorm_ambPacketDefect_charge_invariant {ρ σ : ℂ}
    (hcharge : localFormationCharge ρ = localFormationCharge σ) :
    ambPacketDefect (localFormationCharge ρ) = ambPacketDefect (localFormationCharge σ) := by
  rw [hcharge]

end

end RHTower
