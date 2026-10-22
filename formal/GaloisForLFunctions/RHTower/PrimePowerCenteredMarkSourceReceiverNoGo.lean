import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittCenteredPrimeMarkXiFiberComparison

/-!
# Prime-power centered-mark source/receiver no-go

The centered prime mark has exact source Adams law, but that law never creates
finite monodromy in the strict right half-plane. Its complete natural-power
orbit is injective there. Consequently any quotient that identifies two orbit
levels necessarily loses faithfulness to the actual scalar marks and cannot
supply the equality required by the PPM endpoint.

The canonical Big-Witt Frobenius reporter is already injective on every
hypothetical right completed-Xi fibre. Restricting a collision assertion to
those fibres does not repair the source problem: the resulting predicate is
exactly RH. Thus source-first monodromy is impossible, while receiver-first
monodromy imports the theorem it was meant to prove.

The positive survivor is a global rigidity law: any genuine collision of two
distinct centered-prime powers forces the spectral label onto the critical
line.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Finite monodromy of the actual centered-prime power orbit at every
right-half spectral label, before any Xi divisor is selected. -/
def RightHalfPrimePowerMarkFiniteMonodromy (p : ℕ) : Prop :=
  ∀ s : ℂ, s ∈ rightHalf →
    ∃ a b : ℕ, a < b ∧
      centeredPrimeMark p s ^ a = centeredPrimeMark p s ^ b

/-- **Positive survivor.** A genuine collision of centered-prime powers can
occur only on the critical line. -/
theorem centeredPrimeMark_re_eq_half_of_pow_eq
    {p : ℕ} (hp : 1 < p) {s : ℂ} {a b : ℕ} (hab : a < b)
    (hpowers : centeredPrimeMark p s ^ a = centeredPrimeMark p s ^ b) :
    s.re = 1 / 2 := by
  have hmark0 : centeredPrimeMark p s ≠ 0 := Complex.exp_ne_zero _
  have hnorm : ‖centeredPrimeMark p s‖ ^ a = ‖centeredPrimeMark p s‖ ^ b := by
    simpa only [norm_pow] using congrArg norm hpowers
  have hnormOne : ‖centeredPrimeMark p s‖ = 1 := by
    by_contra hne
    have hab' : a = b :=
      pow_right_injective₀ (norm_pos_iff.mpr hmark0) hne hnorm
    exact (ne_of_lt hab) hab'
  exact (centeredPrimeMark_norm_eq_one_iff hp s).mp hnormOne

/-- Every centered-prime power orbit is injective throughout the strict right
half-plane. -/
theorem centeredPrimeMark_pow_injective_of_mem_rightHalf
    {p : ℕ} (hp : 1 < p) {s : ℂ} (hs : s ∈ rightHalf) :
    Function.Injective (fun a : ℕ => centeredPrimeMark p s ^ a) := by
  intro a b hpowers
  have hcontract : ‖centeredPrimeMark p s‖ < 1 :=
    (centeredPrimeMark_norm_lt_one_iff hp s).mpr (Set.mem_setOf.mp hs)
  have hmark0 : centeredPrimeMark p s ≠ 0 := Complex.exp_ne_zero _
  have hnorm : ‖centeredPrimeMark p s‖ ^ a = ‖centeredPrimeMark p s‖ ^ b := by
    simpa only [norm_pow] using congrArg norm hpowers
  exact pow_right_injective₀
    (norm_pos_iff.mpr hmark0) (ne_of_lt hcontract) hnorm

/-- A divisor-independent finite-monodromy law on all right-half spectral
labels is impossible. -/
theorem not_rightHalfPrimePowerMarkFiniteMonodromy
    {p : ℕ} (hp : 1 < p) :
    ¬ RightHalfPrimePowerMarkFiniteMonodromy p := by
  intro hmono
  let s : ℂ := 1
  have hs : s ∈ rightHalf := by
    change (1 / 2 : ℝ) < (s : ℂ).re
    norm_num [s]
  obtain ⟨a, b, hab, hpowers⟩ := hmono s hs
  exact (ne_of_lt hab)
    (centeredPrimeMark_pow_injective_of_mem_rightHalf hp hs hpowers)

/-- Any quotient collision in the strict right half-plane forces the quotient
map to lose faithfulness to actual centered-mark powers. -/
theorem centeredPrimeMark_quotientCollision_not_injective
    {p : ℕ} (hp : 1 < p) {s : ℂ} (hs : s ∈ rightHalf)
    {Q : Type*} (q : ℂ → Q) {a b : ℕ} (hab : a < b)
    (hcollision : q (centeredPrimeMark p s ^ a) =
      q (centeredPrimeMark p s ^ b)) :
    ¬ Function.Injective q := by
  intro hq
  exact (ne_of_lt hab)
    (centeredPrimeMark_pow_injective_of_mem_rightHalf hp hs
      (hq hcollision))

/-- **Closed PPM terminal certificate.** Source-side monodromy is impossible,
faithful quotients cannot create it, canonical Big-Witt Frobenius is free on
right Xi fibres, and the remaining zero-indexed condition is exactly RH. -/
theorem primePowerCenteredMark_source_receiver_terminal :
    (∀ s : ℂ, s ∈ rightHalf →
      Function.Injective (fun a : ℕ => centeredPrimeMark 2 s ^ a)) ∧
    (¬ RightHalfPrimePowerMarkFiniteMonodromy 2) ∧
    (∀ (Q : Type) (q : ℂ → Q), Function.Injective q →
      ∀ s : ℂ, s ∈ rightHalf →
        ¬ ∃ a b : ℕ, a < b ∧
          q (centeredPrimeMark 2 s ^ a) =
            q (centeredPrimeMark 2 s ^ b)) ∧
    (∀ e : CompletedXiThetaRightSpectralFiber,
      Function.Injective
        (fun k => completedXiBigWittPrimeMarkOrbit 2 e.1.1 k)) ∧
    (XiRightPrimePowerMarkCollision 2 ↔ RiemannHypothesis) := by
  refine ⟨?_,
    not_rightHalfPrimePowerMarkFiniteMonodromy (p := 2) (by omega), ?_,
    completedXiRightSpectralFiber_bigWittPrimeMarkOrbit_injective,
    xiRightPrimePowerMarkCollision_iff_riemannHypothesis (p := 2) (by omega)⟩
  · intro s hs
    exact centeredPrimeMark_pow_injective_of_mem_rightHalf (p := 2) (by omega) hs
  intro Q q hq s hs
  rintro ⟨a, b, hab, hcollision⟩
  exact centeredPrimeMark_quotientCollision_not_injective
    (p := 2) (by omega) hs q hab hcollision hq

end

end RHTower
