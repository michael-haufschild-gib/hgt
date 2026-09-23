import GaloisForLFunctions.RHTower.ThetaCuspHawkingSchwarzschildRecoilCompletionEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekBorelPartnerEndpoint

/-!
# Literal two-emission scalar recoil coherence cannot be a PW CTP seam

The exact normalized Schwarzschild two-emission factor is

`C(M; E, F) = exp (-4*pi*(E-F)^(2 : ℕ))`.

It is positive, independent of the black-hole mass, and symmetric under exchange of the two
emissions.  This leaf tests the literal scalar multi-event repair left by the one-endpoint no-go:
using `C` itself to dress the oriented Parikh--Wilczek Borel recoil phase and asking that entire
quantity to supply the CTP-ordered contact.

That repair fails off the critical wall.  The dressed phase has exactly the same zero locus as the
undressed recoil holonomy, while event exchange leaves it fixed.  A nonzero off-wall phase is
therefore not CTP-skew.  Scalar entropy coherence can dress a separately supplied ordered contact,
but cannot be that contact or force its partner balance.

Proof-chain role:
`literal Hawking CTP seam -> reciprocal completion with finite-energy contact -> fixed-grade
partner balance -> Xi occurrence -> RH`.  This retires the subroute where normalized two-emission
Schwarzschild coherence is the entire ordered seam.  The survivor must add an exchange-odd,
channel-relative contact to the literal two-scale multi-event source.

`[NEW] [PW-B ROUTE-CLASS NO-GO] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- The source-exact normalized two-emission coherence dressing of one oriented PW recoil phase. -/
def schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase
    (M E F : ℝ) (s : ℂ) (k : ℕ) : ℝ :=
  schwarzschildNormalizedTwoEmissionRecoilCoherence M E F *
    (schwarzschildParikhWilczekBorelRecoilHolonomy s k).im

/-- Literal normalized two-emission entropy coherence is strictly positive. -/
theorem schwarzschildNormalizedTwoEmissionRecoilCoherence_pos
    (M E F : ℝ) : 0 < schwarzschildNormalizedTwoEmissionRecoilCoherence M E F := by
  rw [schwarzschildNormalizedTwoEmissionRecoilCoherence_eq]
  exact Real.exp_pos _

/-- Coupling the literal two-emission factor to the PW phase cannot recover a mass coordinate:
the normalized source factor has already canceled it exactly. -/
theorem schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase_mass_invariant
    (M N E F : ℝ) (s : ℂ) (k : ℕ) :
    schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase M E F s k =
      schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase N E F s k := by
  rw [schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase,
    schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase,
    schwarzschildNormalizedTwoEmissionRecoilCoherence_eq,
    schwarzschildNormalizedTwoEmissionRecoilCoherence_eq]

/-- The literal scalar two-emission factor is insensitive to the order of its source legs. -/
theorem schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase_event_swap
    (M E F : ℝ) (s : ℂ) (k : ℕ) :
    schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase M F E s k =
      schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase M E F s k := by
  rw [schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase,
    schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase,
    schwarzschildNormalizedTwoEmissionRecoilCoherence_eq,
    schwarzschildNormalizedTwoEmissionRecoilCoherence_eq]
  congr 2
  ring

/-- Exact wall classification: literal two-emission scalar coherence neither creates nor erases
the PW recoil-phase zero locus. -/
theorem schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase_eq_zero_iff
    (M E F : ℝ) (s : ℂ) (k : ℕ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hsim : s.im ≠ 0) :
    schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase M E F s k = 0 ↔
      s.re = 1 / 2 := by
  rw [schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase, mul_eq_zero]
  have hcoherence : schwarzschildNormalizedTwoEmissionRecoilCoherence M E F ≠ 0 :=
    (schwarzschildNormalizedTwoEmissionRecoilCoherence_pos M E F).ne'
  simp only [hcoherence, false_or]
  exact schwarzschildParikhWilczekBorelRecoilHolonomy_im_eq_zero_iff
    s k hs0 hs1 hsim

/-- In every off-critical nonreal strip mode the literal scalar two-emission dressing survives. -/
theorem schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase_ne_zero_of_offCritical
    (M E F : ℝ) (s : ℂ) (k : ℕ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hsim : s.im ≠ 0)
    (hoff : s.re ≠ 1 / 2) :
    schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase M E F s k ≠ 0 := by
  intro hzero
  exact hoff ((schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase_eq_zero_iff
    M E F s k hs0 hs1 hsim).mp hzero)

/-- **Literal two-emission scalar CTP no-go.** Since source-leg exchange fixes the scalar
two-emission dressing, it cannot itself equal its CTP reverse off the PW critical wall. -/
theorem not_schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase_ctp_skew_of_offCritical
    (M E F : ℝ) (s : ℂ) (k : ℕ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hsim : s.im ≠ 0)
    (hoff : s.re ≠ 1 / 2) :
    ¬ schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase M E F s k =
      -schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase M F E s k := by
  intro hskew
  rw [schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase_event_swap] at hskew
  have hzero_swapped :
      schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase M F E s k = 0 := by
    linarith
  have hzero : schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase M E F s k = 0 := by
    rw [← schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase_event_swap M E F s k]
    exact hzero_swapped
  exact (schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase_ne_zero_of_offCritical
    M E F s k hs0 hs1 hsim hoff) hzero

end

end RHTower
