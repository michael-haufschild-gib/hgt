import GaloisForLFunctions.RHTower.DeningerOscMeyerDomination
import GaloisForLFunctions.RHTower.DeningerQuotientNuclearCompleted
import GaloisForLFunctions.RHTower.DeningerDepletedQuotient

/-!
# Meyer's source is a nuclear space

The two-sided oscillator family is nuclear, and it is equivalent to the family of finite suprema of
the Meyer seminorms, so the latter is nuclear too.  Nuclearity of the Euler-depleted quotients
follows by permanence.

* `deningerMeyerSupFamily` : the finite suprema of the Meyer seminorms.
* `deningerMeyerSup_isNuclearSpaceC` : **`H_-` is a nuclear space.**
* `deningerMeyerQuotient_isNuclearSpaceC` : **every quotient of `H_-` is nuclear.**
-/

namespace RHTower

open SchwartzMap GaloisForLFunctions

noncomputable section

/-- The finite suprema of the Meyer seminorms — the directed presentation of the source topology. -/
def deningerMeyerSupFamily : SeminormFamily ℂ DeningerExpSchwartz (Finset (ℕ × ℕ)) :=
  fun s => s.sup (fun i : ℕ × ℕ => deningerMeyerSeminorm ((i.1 : ℕ) : ℝ) i.2)

/-- **Meyer's source is a nuclear space.** -/
theorem deningerMeyerSup_isNuclearSpaceC :
    DeningerIsNuclearSpaceC deningerMeyerSupFamily := by
  refine deningerIsNuclearSpaceC_of_dominating deningerTwoSidedOscFamily deningerMeyerSupFamily
    ?_ ?_ deningerTwoSidedOsc_isNuclearSpaceC
  · intro s
    obtain ⟨A, M, C, _, hb⟩ := deningerMeyerSup_le_twoSidedShifted s
    exact ⟨(A, M), C, fun x => hb x⟩
  · rintro ⟨K, m⟩
    obtain ⟨s, C, _, hb⟩ := deningerTwoSidedOsc_le_meyerSup K m
    exact ⟨s, C, fun x => hb x⟩

/-- **Every quotient of Meyer's source is nuclear.**  In particular `M_ζ = H_- / Z(H_∩)` and the
Euler-depleted quotient `M_ζ^{(p)} = H_- / Δ_p Z(H_∩)`. -/
theorem deningerMeyerQuotient_isNuclearSpaceC (N : Submodule ℂ DeningerExpSchwartz) :
    DeningerIsNuclearSpaceC (fun s : Finset (ℕ × ℕ) =>
      deningerQuotientSeminorm N (deningerMeyerSupFamily s)) :=
  deningerIsNuclearSpaceC_quotient_of_C deningerMeyerSupFamily N deningerMeyerSup_isNuclearSpaceC

/-- **The Meyer quotient `M_ζ` is nuclear.** -/
theorem deningerMeyerQuotient_nuclear :
    DeningerIsNuclearSpaceC (fun s : Finset (ℕ × ℕ) =>
      deningerQuotientSeminorm deningerPoissonRangeSubmodule (deningerMeyerSupFamily s)) :=
  deningerMeyerQuotient_isNuclearSpaceC _

/-- **The Euler-depleted quotient `M_ζ^{(p)}` is nuclear.** -/
theorem deningerDepletedQuotient_nuclear (L : ℝ) :
    DeningerIsNuclearSpaceC (fun s : Finset (ℕ × ℕ) =>
      deningerQuotientSeminorm (deningerDepletedPoissonRange L) (deningerMeyerSupFamily s)) :=
  deningerMeyerQuotient_isNuclearSpaceC _

end

end RHTower
