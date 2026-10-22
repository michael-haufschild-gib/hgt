import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingModularSuperselectionEndpoint
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangleExhaustion
import GaloisForLFunctions.HTGeometry.PrimeValuationKakutaniSector

/-!
# Occupation-aligned double-KMS diagnostic for theta-cusp backreaction

For a bifurcate Killing horizon, Higuchi--Lima (`arXiv:2107.10271`) identify the
Hartle--Hawking state with a pure, wedge-reflection-invariant double KMS state whose restrictions
to both static regions are thermal at the same Hawking temperature.  The mathematical diagnostic
below asks for more: it places the two arithmetic geometric laws in the two marginals of the
*same occupation-aligned oscillator pair*.

The source-built theta horizon gives geometric occupation ratios

`q_visible(p,c) = p^{-(1-2c)}` and `q_partner(p,c) = p^{-(1+2c)}`,

where `c` is physical port dissipation divided by twice source mass and closed-state energy.
Both ratios lie in `(0,1)` at every two-ended resonance.  Under the extra same-pair alignment, a
common Schmidt list forces equality already at vacuum occupation; strict injectivity of
`x ↦ p^x` then forces `c = 0`.

**[FALSIFIED]** Purity or double-KMS thermality alone does not supply this alignment.  A charged
thermofield double of a complex scalar factorizes into independent positive- and negative-charge
sectors with shifted geometric ratios while remaining pure (Chapman--Chen,
`arXiv:1910.07508`).  Thus the valid theorem is an aligned-pair diagnostic, not a general
Hartle--Hawking obstruction.  A physical producer would have to prove from the real theta mirror
that no independent charge-conjugate sector exists and that the two arithmetic laws are the
marginals of one self-conjugate oscillator pair.  Neither wedge reflection nor purity proves it.
-/

open Complex
open GaloisForLFunctions

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Visible-wedge geometric KMS ratio at one prime channel. -/
def thetaCuspHawkingPrimeVisibleKMSRatio
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (p : Nat.Primes) : ℝ :=
  primeTwistRatio (thetaCuspHawkingBackreactionHorizonCharge r) p

/-- Wedge-reflected partner geometric KMS ratio at one prime channel. -/
def thetaCuspHawkingPrimePartnerKMSRatio
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (p : Nat.Primes) : ℝ :=
  primeTwistRatio (-thetaCuspHawkingBackreactionHorizonCharge r) p

/-- Real geometric occupation mass `(1-q)q^k`. -/
def thetaCuspHawkingPrimeGeometricKMSMass (q : ℝ) (k : ℕ) : ℝ :=
  (1 - q) * q ^ k

/-- Every backreaction resonance charge lies in the centered Xi half-strip. -/
theorem thetaCuspHawkingBackreactionHorizonCharge_mem_openHalf
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    (-1 / 2 : ℝ) < thetaCuspHawkingBackreactionHorizonCharge r ∧
      thetaCuspHawkingBackreactionHorizonCharge r < 1 / 2 := by
  rw [thetaCuspHawkingBackreactionHorizonCharge_eq_im]
  exact xiC_zero_im_mem_openHalf
    (thetaCuspHawkingBackreactionResonantMode_XiC_eq_zero r)

/-- Visible arithmetic KMS ratio is strictly positive. -/
theorem thetaCuspHawkingPrimeVisibleKMSRatio_pos
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (p : Nat.Primes) :
    0 < thetaCuspHawkingPrimeVisibleKMSRatio r p :=
  primeTwistRatio_pos _ _

/-- Visible arithmetic KMS ratio is normalizable. -/
theorem thetaCuspHawkingPrimeVisibleKMSRatio_lt_one
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (p : Nat.Primes) :
    thetaCuspHawkingPrimeVisibleKMSRatio r p < 1 := by
  apply primeTwistRatio_lt_one
  exact (thetaCuspHawkingBackreactionHorizonCharge_mem_openHalf r).2

/-- Reflected arithmetic KMS ratio is strictly positive. -/
theorem thetaCuspHawkingPrimePartnerKMSRatio_pos
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (p : Nat.Primes) :
    0 < thetaCuspHawkingPrimePartnerKMSRatio r p :=
  primeTwistRatio_pos _ _

/-- Reflected arithmetic KMS ratio is normalizable. -/
theorem thetaCuspHawkingPrimePartnerKMSRatio_lt_one
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (p : Nat.Primes) :
    thetaCuspHawkingPrimePartnerKMSRatio r p < 1 := by
  apply primeTwistRatio_lt_one
  have hstrip := thetaCuspHawkingBackreactionHorizonCharge_mem_openHalf r
  linarith

/-- Primewise type-I occupation-aligned completion.  `schmidtMass k` is the common squared Schmidt
coefficient of occupation `k`; its two equations say that the visible and reflected geometric
KMS states are the reduced states of one occupation-aligned pure double.  This is strictly stronger
than abstract pure double-KMS existence: charged conjugate sectors need not share this list.

For geometric spectra with ratio in `(0,1)`, occupation order is spectral order, so this is the
ordered Schmidt-spectrum condition supplied by a pure double KMS state. -/
structure ThetaCuspHawkingPrimeDoubleKMSPurification
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (p : Nat.Primes) where
  schmidtMass : ℕ → ℝ
  visible_marginal : ∀ k,
    schmidtMass k =
      thetaCuspHawkingPrimeGeometricKMSMass
        (thetaCuspHawkingPrimeVisibleKMSRatio r p) k
  partner_marginal : ∀ k,
    schmidtMass k =
      thetaCuspHawkingPrimeGeometricKMSMass
        (thetaCuspHawkingPrimePartnerKMSRatio r p) k

/-- **[PAPER-PROVED] Local Hawking-temperature rigidity.**  Visible and reflected geometric KMS
ratios agree at one prime exactly when physical backreaction charge vanishes. -/
theorem thetaCuspHawkingPrimeKMSRatio_eq_iff_horizonCharge_zero
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (p : Nat.Primes) :
    thetaCuspHawkingPrimeVisibleKMSRatio r p =
        thetaCuspHawkingPrimePartnerKMSRatio r p ↔
      thetaCuspHawkingBackreactionHorizonCharge r = 0 := by
  constructor
  · intro h
    unfold thetaCuspHawkingPrimeVisibleKMSRatio
      thetaCuspHawkingPrimePartnerKMSRatio primeTwistRatio at h
    have hp1 : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
    have hexp := (Real.strictMono_rpow_of_base_gt_one hp1).injective h
    rw [twistExponent, twistExponent] at hexp
    linarith
  · intro h
    simp [thetaCuspHawkingPrimeVisibleKMSRatio,
      thetaCuspHawkingPrimePartnerKMSRatio, h]

/-- **[LEAN-PROVED] Prime aligned-purification law.**  One prime channel admits a common
ordered Schmidt spectrum for its two arithmetic KMS marginals exactly at neutral physical
horizon charge. -/
theorem thetaCuspHawkingPrimeDoubleKMSPurification_iff_horizonCharge_zero
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (p : Nat.Primes) :
    Nonempty (ThetaCuspHawkingPrimeDoubleKMSPurification r p) ↔
      thetaCuspHawkingBackreactionHorizonCharge r = 0 := by
  constructor
  · rintro ⟨w⟩
    have hmass := (w.visible_marginal 0).symm.trans (w.partner_marginal 0)
    simp only [thetaCuspHawkingPrimeGeometricKMSMass, pow_zero, mul_one] at hmass
    apply (thetaCuspHawkingPrimeKMSRatio_eq_iff_horizonCharge_zero r p).mp
    linarith
  · intro hzero
    have hratio :=
      (thetaCuspHawkingPrimeKMSRatio_eq_iff_horizonCharge_zero r p).mpr hzero
    refine ⟨{
      schmidtMass := fun k =>
        thetaCuspHawkingPrimeGeometricKMSMass
          (thetaCuspHawkingPrimeVisibleKMSRatio r p) k
      visible_marginal := fun _ => rfl
      partner_marginal := ?_
    }⟩
    intro k
    rw [hratio]

/-- **[LEAN-PROVED] Positive-charge aligned-pair obstruction.**  No positive physical horizon
charge can be completed to the source-prescribed occupation-aligned pure double, already at one
prime.  This does not exclude a charged thermofield double with independent conjugate sectors. -/
theorem no_thetaCuspHawkingPrimeDoubleKMSPurification_of_horizonCharge_pos
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (p : Nat.Primes)
    (hpos : 0 < thetaCuspHawkingBackreactionHorizonCharge r) :
    ¬ Nonempty (ThetaCuspHawkingPrimeDoubleKMSPurification r p) := by
  intro hpure
  have hzero :=
    (thetaCuspHawkingPrimeDoubleKMSPurification_iff_horizonCharge_zero r p).mp hpure
  linarith

/-- **[OPEN CORE] Source-faithful neutral-sector localization.**  Every theta backreaction
resonance and every prime oscillator channel admits one occupation-aligned pure double KMS
completion with the source-prescribed visible and reflected marginals.

Required producer: quantize the existing real anomaly/backreaction system, exclude an independent
charge-conjugate factorization, and prove that its two wedge restrictions are exactly these
prime-valuation laws in the same oscillator sector.  General Hawking thermality and purity do not
identify arbitrary arithmetic measures with those wedge reductions. -/
def ThetaCuspHawkingHartleHawkingDoubleKMSCompletable : Prop :=
  ∀ (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes),
    Nonempty (ThetaCuspHawkingPrimeDoubleKMSPurification r p)

/-- **[BRIDGE] Occupation-aligned double-KMS endpoint.**  Source-faithful same-sector completion
of every physical theta resonance is equivalent to RH.  One prime vacuum Schmidt weight kills
positive or negative charge; under RH every pair of geometric marginals is identical.  The
equivalence is not a claim that a general Hartle--Hawking state supplies the alignment. -/
theorem thetaCuspHawkingHartleHawkingDoubleKMSCompletable_iff_riemannHypothesis :
    ThetaCuspHawkingHartleHawkingDoubleKMSCompletable ↔ RiemannHypothesis := by
  rw [riemannHypothesis_iff_thetaCuspHawkingBackreactionResonances_real]
  constructor
  · intro hcomplete alpha hres
    let r : ThetaCuspHawkingBackreactionResonantMode := ⟨alpha, hres⟩
    have hzero :=
      (thetaCuspHawkingPrimeDoubleKMSPurification_iff_horizonCharge_zero
        r ⟨2, Nat.prime_two⟩).mp
        (hcomplete r ⟨2, Nat.prime_two⟩)
    rw [thetaCuspHawkingBackreactionHorizonCharge_eq_im] at hzero
    exact hzero
  · intro hreal r p
    apply
      (thetaCuspHawkingPrimeDoubleKMSPurification_iff_horizonCharge_zero r p).mpr
    rw [thetaCuspHawkingBackreactionHorizonCharge_eq_im]
    exact hreal r.1 r.2

end RHTower
