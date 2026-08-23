import GaloisForLFunctions.RHTower.ThetaCuspHawkingModularSuperselectionEndpoint
import GaloisForLFunctions.RHTower.AcceleratedWoldType
import GaloisForLFunctions.RHTower.ReesGradeFiltrationPrimeWoldWitness

/-!
# Theta-cusp Hawking J-only partner no-go

**[FALSIFIED]** Earlier interpretation treated Tomita modular conjugation `J` as state-to-state
transport between the two arithmetic density vectors.  This is not standard modular theory.
Natural-cone state vectors are fixed by `J`; relative state transport uses the relative Tomita
operator and its generally unbounded factor `Δ_{ψ|φ}^{1/2}`.  Thus ordinary horizon modularity
does not supply the bounded sewing hypothesis below.

The theta arithmetic horizon has an exact obstruction to such a shadow.  If a positive physical
horizon charge is `c`, any operator family which carries its prime-valuation Hellinger sector to
the reflected sector has accelerated Wold type at least

`2 * exp (-EulerGamma) * c`.

In particular, no uniformly bounded family can perform the sewing.  The endpoint below says that
every positive-charge theta resonance admits a uniformly bounded scalar shadow of one Tomita
partner conjugation.  This condition is equivalent to RH.

The mathematical accelerated-type obstruction remains valid.  The predicate below is now kept as
a deliberately stronger `J`-only localization diagnostic, not as a consequence of the
Tomita--Takesaki or Bisognano--Wichmann theorems.  The physically faithful successor is the
Hartle--Hawking double-KMS/Schmidt endpoint.
-/

open Complex Filter Asymptotics
open GaloisForLFunctions

noncomputable section

namespace RHTower

/-- Exact accelerated-type floor forced by one positive physical Hawking horizon charge. -/
def thetaCuspHawkingTomitaAcceleratedTypeFloor
    (r : ThetaCuspHawkingBackreactionResonantMode) : ℝ :=
  2 * Real.exp (-Real.eulerMascheroniConstant) *
    thetaCuspHawkingBackreactionHorizonCharge r

/-- The accelerated Tomita sewing floor is strictly positive at positive horizon charge. -/
theorem thetaCuspHawkingTomitaAcceleratedTypeFloor_pos
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hpos : 0 < thetaCuspHawkingBackreactionHorizonCharge r) :
    0 < thetaCuspHawkingTomitaAcceleratedTypeFloor r := by
  unfold thetaCuspHawkingTomitaAcceleratedTypeFloor
  positivity

/-- **[PAPER-PROVED] Hawking--Tomita accelerated-type obstruction.**  In arbitrary cutoff-wise
real normed spaces, every exact operator sewing of the visible and reflected theta horizon
vectors has accelerated Wold type bounded below by the normalized physical port charge.  No
dimension, basis, or scalar realization is assumed. -/
theorem thetaCuspHawkingTomitaSewing_eventually_acceleratedTypeFloor
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hpos : 0 < thetaCuspHawkingBackreactionHorizonCharge r)
    {E F : ℕ → Type*}
    [∀ N, NormedAddCommGroup (E N)] [∀ N, NormedSpace ℝ (E N)]
    [∀ N, NormedAddCommGroup (F N)] [∀ N, NormedSpace ℝ (F N)]
    (J : ∀ N, E N →L[ℝ] F N) (visible : ∀ N, E N) (partner : ∀ N, F N)
    (hJ : ∀ N, J N (visible N) = partner N)
    (hvisible : ∀ N, ‖visible N‖ =
      primeValuationSquaredHellingerBelow
        (thetaCuspHawkingBackreactionHorizonCharge r) N)
    (hpartner : ∀ N, ‖partner N‖ =
      primeValuationSquaredHellingerBelow
        (-thetaCuspHawkingBackreactionHorizonCharge r) N)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop,
      thetaCuspHawkingTomitaAcceleratedTypeFloor r - ε <
        mertensPrimeProductBelow N * ell2 ‖J N‖ := by
  obtain ⟨q, _, hcharge⟩ :=
    exists_xiRightZeroCopy_of_thetaCuspHawkingBackreactionHorizonCharge_pos r hpos
  have hbase := eventually_lt_mertensProduct_mul_ell2_opNorm
    (c := xiRightSourceModularCharge q)
    (xiRightSourceModularCharge_pos q)
    (xiRightSourceModularCharge_lt_half q)
    J visible partner hJ (fun N ↦ by simpa only [hcharge] using hvisible N)
      (fun N ↦ by simpa only [hcharge] using hpartner N) hε
  simpa only [thetaCuspHawkingTomitaAcceleratedTypeFloor, hcharge] using hbase

/-- **[LEAN-PROVED] Bounded Tomita-shadow no-go.**  A positive-charge theta Hawking resonance
cannot have its two reflected squared-Hellinger sectors sewn by a uniformly bounded family.  A
norm-one antiunitary shadow is a fortiori excluded. -/
theorem no_bounded_thetaCuspHawkingTomitaPartnerShadow
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hpos : 0 < thetaCuspHawkingBackreactionHorizonCharge r)
    (J : ℕ → (ℝ →L[ℝ] ℝ))
    (hbounded : (fun N ↦ ‖J N‖) =O[atTop] fun _ ↦ (1 : ℝ)) :
    (fun N ↦ J N
      (primeValuationSquaredHellingerBelow
        (thetaCuspHawkingBackreactionHorizonCharge r) N)) ≠
      primeValuationSquaredHellingerBelow
        (-thetaCuspHawkingBackreactionHorizonCharge r) := by
  obtain ⟨q, _, hcharge⟩ :=
    exists_xiRightZeroCopy_of_thetaCuspHawkingBackreactionHorizonCharge_pos r hpos
  have hhalf : thetaCuspHawkingBackreactionHorizonCharge r < 1 / 2 := by
    rw [← hcharge]
    exact xiRightSourceModularCharge_lt_half q
  exact no_boundedOperator_sews_reflected_Hellinger_sectors
    hpos hhalf J hbounded

/-- **[FALSIFIED] J-only localization hypothesis.**  Every positive-charge theta resonance has a
uniformly bounded scalar map from visible prime-valuation Hellinger data to reflected data.  This
is mathematically well-defined but is not supplied by actual Tomita conjugation: state transport
contains the relative modular factor. -/
def ThetaCuspHawkingTomitaPartnerShadowLocalized : Prop :=
  ∀ r : ThetaCuspHawkingBackreactionResonantMode,
    0 < thetaCuspHawkingBackreactionHorizonCharge r →
      ∃ J : ℕ → (ℝ →L[ℝ] ℝ),
        ((fun N ↦ ‖J N‖) =O[atTop] fun _ ↦ (1 : ℝ)) ∧
        (fun N ↦ J N
          (primeValuationSquaredHellingerBelow
            (thetaCuspHawkingBackreactionHorizonCharge r) N)) =
          primeValuationSquaredHellingerBelow
            (-thetaCuspHawkingBackreactionHorizonCharge r)

/-- **[BRIDGE] J-only diagnostic endpoint.**  Bounded reflected-data sewing is equivalent to RH.
Positive charge contradicts the accelerated-type obstruction; applying the same argument to the
functional-equation partner excludes negative charge.  This equivalence does not make bounded
sewing a theorem of Hawking or Tomita physics. -/
theorem thetaCuspHawkingTomitaPartnerShadowLocalized_iff_riemannHypothesis :
    ThetaCuspHawkingTomitaPartnerShadowLocalized ↔ RiemannHypothesis := by
  rw [riemannHypothesis_iff_thetaCuspHawkingBackreactionResonances_real]
  constructor
  · intro hlocalized alpha hres
    let r : ThetaCuspHawkingBackreactionResonantMode := ⟨alpha, hres⟩
    have hnonpos :
        ¬ 0 < thetaCuspHawkingBackreactionHorizonCharge r := by
      intro hpos
      obtain ⟨J, hbounded, hsew⟩ := hlocalized r hpos
      exact (no_bounded_thetaCuspHawkingTomitaPartnerShadow
        r hpos J hbounded) hsew
    have him_le : r.1.im ≤ 0 := by
      rw [thetaCuspHawkingBackreactionHorizonCharge_eq_im] at hnonpos
      exact le_of_not_gt hnonpos
    let rr := thetaCuspHawkingBackreactionReflectedResonantMode r
    have href_nonpos :
        ¬ 0 < thetaCuspHawkingBackreactionHorizonCharge rr := by
      intro hpos
      obtain ⟨J, hbounded, hsew⟩ := hlocalized rr hpos
      exact (no_bounded_thetaCuspHawkingTomitaPartnerShadow
        rr hpos J hbounded) hsew
    have href_im_le : rr.1.im ≤ 0 := by
      rw [thetaCuspHawkingBackreactionHorizonCharge_eq_im] at href_nonpos
      exact le_of_not_gt href_nonpos
    rw [thetaCuspHawkingBackreactionReflectedResonantMode_im] at href_im_le
    change alpha.im = 0
    dsimp only [r] at him_le
    linarith
  · intro hreal r hpos
    have him : r.1.im = 0 := hreal r.1 r.2
    rw [thetaCuspHawkingBackreactionHorizonCharge_eq_im, him] at hpos
    linarith

end RHTower
