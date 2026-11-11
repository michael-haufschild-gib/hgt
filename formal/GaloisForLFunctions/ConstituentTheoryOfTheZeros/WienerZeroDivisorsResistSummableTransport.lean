import GaloisForLFunctions.ConstituentTheoryOfTheZeros.SummableResidueErrorsDoNotPermitZeros
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.VanishingZeroDisplacementsForcePurity
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.WienerZeroDivisorsHaveBoundedLocalMass
import GaloisForLFunctions.HTGeometry.LocalMassHolderSummability
import GaloisForLFunctions.HTGeometry.LocalMassSampling
import GaloisForLFunctions.RHTower.ZetaCellDisplacementEnvelope

/-!
# Wiener zero divisors resist summable transport

The zeros of a nonzero Wiener expansion cannot be moved cofinitely to zeta zeros
by an `ℓᵖ` family of displacements for any finite `p > 0`. Vanishing
displacements first force purity. Zeta's vertical mean square, bounded
local multiplicity and Hölder make the residues summable, contradicting
the jump law.
-/

open Complex Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.InfiniteRankPurityTheory

private theorem summable_on_subset {α : Type*} {S T : Set α} {f : α → ℝ}
    (hST : S ⊆ T) (hf : Summable (fun p : T => f p)) :
    Summable (fun p : S => f p) := by
  let incl : S → T := fun p => ⟨p, hST p.2⟩
  have hinj : Function.Injective incl := by
    intro p q h
    exact Subtype.ext (congrArg (fun z : T => (z : α)) h)
  exact hf.comp_injective hinj

/-- A nonzero Wiener expansion with an interior zero admits no cofinite
transport of its strip divisor to zeta zeros with summable `p`th-power
displacements, for any finite `p > 0`. -/
theorem not_cofinite_zeta_zero_of_summable_displacements
    {c : Scale → ℂ} {ω p : ℝ} (hω0 : 0 < ω) (hω : ω ≤ 1 / 2)
    (hc : WSummable (1 / 2 - ω) (1 / 2 + ω) c) (hne : c ≠ 0)
    {s : ℂ} (hs : |s.re - 1 / 2| < ω) (hs0 : expansion c s = 0)
    (hp : 0 < p)
    {η : {z ∈ {z : ℂ | 1 / 2 - ω < z.re ∧ z.re < 1 / 2 + ω} |
      expansion c z = 0} → ℂ}
    (hηsum : Summable (fun z => ‖η z‖ ^ p)) :
    ¬ (∀ᶠ z : {z ∈ {z : ℂ | 1 / 2 - ω < z.re ∧ z.re < 1 / 2 + ω} |
      expansion c z = 0} in cofinite, riemannZeta ((z : ℂ) + η z) = 0) := by
  classical
  intro hzero
  let U : Set ℂ := {z | 1 / 2 - ω < z.re ∧ z.re < 1 / 2 + ω}
  let Z : Set ℂ := {z ∈ U | expansion c z = 0}
  have hη := HTGeometry.tendsto_zero_of_summable_norm_rpow hp hηsum
  have hFne : ∃ z : ℂ, z ∈ U ∧ expansion c z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hne
    refine eq_zero_of_expansion_eq_zero (le_refl (1 / 2 : ℝ))
      (hc.mono (by linarith only [hω0]) le_rfl (by linarith only [hω0])) ?_
    intro z hz1 hz2
    have hz : z.re = 1 / 2 := le_antisymm hz2 hz1
    exact hcon z ⟨by rw [hz]; linarith only [hω0], by rw [hz]; linarith only [hω0]⟩
  have hpure : ∀ z : Z, (z : ℂ).re = 1 / 2 := by
    intro z
    have hz1 := z.2.1.1
    have hz2 := z.2.1.2
    have hzabs : |(z : ℂ).re - 1 / 2| < ω :=
      abs_lt.mpr ⟨by linarith only [hz1], by linarith only [hz2]⟩
    let R := (ω - |(z : ℂ).re - 1 / 2|) / 2
    have hR : 0 < R := by dsimp [R]; linarith only [hzabs]
    have hAP : IsStripAlmostPeriodicOn (expansion c) (z : ℂ).re R :=
      isStripAlmostPeriodicOn_expansion (hc.mono
        (by dsimp [R]; linarith only [neg_le_abs ((z : ℂ).re - 1 / 2), hzabs])
        (by linarith only [hR])
        (by dsimp [R]; linarith only [le_abs_self ((z : ℂ).re - 1 / 2), hzabs]))
    exact re_eq_half_of_zero_displacements_tendsto_zero (differentiableOn_expansion hc)
      hFne hz1 hz2 (by linarith only [hz1, hω]) (by linarith only [hz2, hω])
      z.2.2 hR hAP hη hzero
  obtain ⟨L, hL, N, _, hmass⟩ := exists_local_expansion_divisor_bound
    (σ := 1 / 2) (a := 0) hc hne le_rfl hω0
  let m : Z → ℝ := fun z => analyticOrderNatAt (expansion c) z
  have hm : ∀ z, 0 ≤ m z := fun z => Nat.cast_nonneg _
  have hlocal : ∀ t : ℝ, ∀ v : Finset Z,
      (∀ z ∈ v, t ≤ (z : ℂ).im ∧ (z : ℂ).im ≤ t + L) → ∑ z ∈ v, m z ≤ N := by
    intro t v hv
    let incl : Z ↪ ℂ := ⟨Subtype.val, Subtype.val_injective⟩
    have hb := hmass t (v.map incl) (by
      intro z hz
      obtain ⟨z, hmem, rfl⟩ := Finset.mem_map.mp hz
      exact ⟨by change |(z : ℂ).re - 1 / 2| ≤ 0; rw [hpure z, sub_self, abs_zero],
        hv z hmem⟩)
    rw [Finset.sum_map] at hb
    exact hb
  -- Raising small exponents to three puts the conjugate strictly between one and two.
  let P := max p 3
  have hP1 : 1 < P := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hP2 : 2 < P := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  let q := Real.conjExponent P
  have hPq : P.HolderConjugate q := Real.HolderConjugate.conjExponent hP1
  have hq1 : 1 < q := by
    have h := hPq.symm.sub_one_pos
    linarith only [h]
  have hq2 : q < 2 := by
    rw [hPq.conjugate_eq, div_lt_iff₀ hPq.sub_one_pos]
    linarith only [hP2]
  have hηP : Summable (fun z => ‖η z‖ ^ P) :=
    HTGeometry.summable_norm_rpow_of_le hp (le_max_left _ _) hηsum
  obtain ⟨r, hr, v, hv, hvs, hbound⟩ := exists_summable_zeta_displacement_cell_envelope hq1 hq2
  have htail := HTGeometry.summable_mass_mul_of_lp_cell_bound
    (fun z : Z => (z : ℂ).im) hm (fun z => norm_nonneg (η z)) hL hlocal hPq hηP hv hvs
  have hsmall : ∀ᶠ z in cofinite, ‖η z‖ < r := by
    have ht := hη.norm
    rw [norm_zero] at ht
    exact ht.eventually (gt_mem_nhds hr)
  have hres : ∀ z : ℂ, ‖expansionZetaResidue c z‖ =
      (analyticOrderNatAt (expansion c) z : ℝ) * ‖riemannZeta z / z‖ := by
    intro z
    simp only [expansionZetaResidue, HTGeometry.weightedLogResidue, norm_mul,
      norm_neg, Complex.norm_natCast]
  have hsum : Summable (fun z : Z => ‖expansionZetaResidue c z‖) := by
    refine htail.of_norm_bounded_eventually ?_
    filter_upwards [hsmall.and hzero] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hres]
    calc (analyticOrderNatAt (expansion c) z : ℝ) * ‖riemannZeta z / z‖ ≤
          m z * (v ⌊(z : ℂ).im⌋ * ‖η z‖) :=
        mul_le_mul_of_nonneg_left (hbound z (η z) (hpure z) hz.1 hz.2) (hm z)
      _ = m z * ‖η z‖ * v ⌊(z : ℂ).im⌋ := by ring
  rcases expansion_zero_forces_offLine_or_nonsummable_residues hω0 hω hc hne hs hs0 with
    ⟨z, hz, hz0, hzoff⟩ | hcrit
  · have hz' := abs_lt.mp hz
    exact hzoff (hpure ⟨z, ⟨by linarith only [hz'.1], by linarith only [hz'.2]⟩, hz0⟩)
  · apply hcrit
    refine summable_on_subset (f := fun z : ℂ => ‖expansionZetaResidue c z‖) ?_ hsum
    intro z hz
    exact ⟨⟨by rw [hz.1]; linarith only [hω0], by rw [hz.1]; linarith only [hω0]⟩, hz.2⟩

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
