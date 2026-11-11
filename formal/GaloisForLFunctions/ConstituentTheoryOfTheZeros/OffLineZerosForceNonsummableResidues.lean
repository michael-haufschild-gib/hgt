import GaloisForLFunctions.ConstituentTheoryOfTheZeros.SummableResidueErrorsDoNotPermitZeros
import GaloisForLFunctions.RHTower.ZetaDiscLowerBoundsOnBothSides
import GaloisForLFunctions.HTGeometry.SummableMassHasSparseShadows

/-!
# Off-line zeros force nonsummable zeta residues

Zeros of a nonzero holomorphic almost-periodic function recur in thick sets of
vertical shifts. Off the critical line, zeta has a uniform positive floor
outside an arbitrarily small proportion of shifts. Summable residue weights
would give those recurrent zeros only a density-zero set of vertical shadows.
-/

open Complex Filter Topology Set Metric MeasureTheory

noncomputable section

namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.InfiniteRankPurityTheory

/-- A recurrent off-line zero forces divergent unweighted
zeta residue mass on the full zero divisor of the strip. -/
theorem not_summable_zeta_weights_of_offLine_zero {F : ℂ → ℂ} {τ₁ τ₂ : ℝ}
    (hF : DifferentiableOn ℂ F {z : ℂ | τ₁ < z.re ∧ z.re < τ₂})
    (hFne : ∃ z₁ : ℂ, (τ₁ < z₁.re ∧ z₁.re < τ₂) ∧ F z₁ ≠ 0)
    {ρ₀ : ℂ} (hρ1 : τ₁ < ρ₀.re) (hρ2 : ρ₀.re < τ₂)
    (hpos : 0 < ρ₀.re) (hone : ρ₀.re < 1) (hne : ρ₀.re ≠ 1 / 2) (hFρ : F ρ₀ = 0)
    {R : ℝ} (hR : 0 < R) (hAP : IsStripAlmostPeriodicOn F ρ₀.re R) :
    ¬ Summable (fun p : {z ∈ {z : ℂ | τ₁ < z.re ∧ z.re < τ₂} | F z = 0} =>
      ‖riemannZeta p / (p : ℂ)‖) := by
  intro hsum
  let U : Set ℂ := {z | τ₁ < z.re ∧ z.re < τ₂}
  let E : Set ℂ := {z ∈ U | F z = 0}
  obtain ⟨z₁, hz₁, hz₁ne⟩ := hFne
  have hcount : E.Countable := Bottcher.analyticOnNhd_zeros_countable
    (hF.analyticOnNhd (isOpen_openStrip _ _)) (isPreconnected_openStrip _ _) hz₁ hz₁ne
  letI : Countable E := hcount.to_subtype
  obtain ⟨r₀, hr₀, hfloor₀⟩ := exists_zeta_offLine_disc_floor hpos hone hne
  let r := min r₀ (min (ρ₀.re / 2)
    (min ((ρ₀.re - τ₁) / 2) ((τ₂ - ρ₀.re) / 2)))
  have hr : 0 < r := lt_min hr₀ (lt_min (by linarith)
    (lt_min (by linarith) (by linarith)))
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrpos : r ≤ ρ₀.re / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrτ₁ : r ≤ (ρ₀.re - τ₁) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrτ₂ : r ≤ (τ₂ - ρ₀.re) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨L, hL, d, hd, hthick⟩ := exists_thick_zero_shifts_on_strip hF
    ⟨z₁, hz₁, hz₁ne⟩ hρ1 hρ2 hFρ hR hAP hr
  have hlow := eventually_le_volume_of_relativelyDense hL hd hthick
  let κ := d / (L + 2 * d)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  obtain ⟨b, hb, hfloorLarge⟩ := hfloor₀ (κ / 4) (by positivity)
  have hfloor : ∀ᶠ T : ℝ in atTop,
      volume ({t : ℝ | ∃ z ∈ closedBall ρ₀ r, ‖riemannZeta (z + t * I)‖ < b} ∩ Icc 0 T) ≤
        ENNReal.ofReal (κ / 4 * T) := by
    filter_upwards [hfloorLarge] with T hT
    refine le_trans (measure_mono ?_) hT
    rintro t ⟨⟨z, hz, hsmall⟩, ht⟩
    exact ⟨⟨z, closedBall_subset_closedBall hrr₀ hz, hsmall⟩, ht⟩
  let w : E → ℝ := fun p => ‖riemannZeta p / (p : ℂ)‖
  have hsparse := HTGeometry.eventually_volume_weighted_vertical_shadows_le
    (w := w) (fun p : E => (p : ℂ)) (fun p => norm_nonneg _) hsum ρ₀ hr hb
    (show 0 < κ / 4 by positivity)
  have hcover : {t : ℝ | ∃ z ∈ ball ρ₀ r, F (z + t * I) = 0} ⊆
      {t : ℝ | ∃ z ∈ closedBall ρ₀ r, ‖riemannZeta (z + t * I)‖ < b} ∪
      {t : ℝ | ∃ p : E, ‖(p : ℂ) - (ρ₀ + t * I)‖ < r ∧ b ≤ ‖(p : ℂ)‖ * w p} := by
    rintro t ⟨z, hz, hFz⟩
    by_cases hsmall : ‖riemannZeta (z + t * I)‖ < b
    · exact Or.inl ⟨z, ball_subset_closedBall hz, hsmall⟩
    · right
      have hdist := mem_ball_iff_norm.mp hz
      have hre := abs_lt.mp ((Complex.abs_re_le_norm (z - ρ₀)).trans_lt hdist)
      simp only [Complex.sub_re] at hre
      have hzU : z + t * I ∈ U := by
        change τ₁ < (z + t * I).re ∧ (z + t * I).re < τ₂
        simp only [Complex.add_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero, add_zero]
        constructor <;> linarith [hre.1, hre.2]
      let p : E := ⟨z + t * I, hzU, hFz⟩
      have hp0 : (p : ℂ) ≠ 0 := by
        intro hp
        have hpre : (p : ℂ).re = z.re := by simp only [p, Complex.add_re,
          Complex.mul_I_re, Complex.ofReal_im, neg_zero, add_zero]
        rw [hp, Complex.zero_re] at hpre
        linarith [hre.1]
      refine ⟨p, ?_, ?_⟩
      · simpa only [p, add_sub_add_right_eq_sub] using hdist
      · change b ≤ ‖z + t * I‖ * ‖riemannZeta (z + t * I) / (z + t * I)‖
        rw [norm_div, mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hp0)]
        exact le_of_not_gt hsmall
  obtain ⟨T, hTlow, hTfloor, hTsparse, hT0⟩ :=
    (hlow.and (hfloor.and (hsparse.and (eventually_gt_atTop (0 : ℝ))))).exists
  have hup : volume ({t : ℝ | ∃ z ∈ ball ρ₀ r, F (z + t * I) = 0} ∩ Icc 0 T) ≤
      ENNReal.ofReal (κ / 2 * T) := by
    calc volume _ ≤ volume (({t : ℝ | ∃ z ∈ closedBall ρ₀ r, ‖riemannZeta (z + t * I)‖ < b} ∩ Icc 0 T) ∪
        ({t : ℝ | ∃ p : E, ‖(p : ℂ) - (ρ₀ + t * I)‖ < r ∧ b ≤ ‖(p : ℂ)‖ * w p} ∩ Icc 0 T)) := by
          apply measure_mono
          intro t ht
          rcases hcover ht.1 with hsmall | hshadow
          · exact Or.inl ⟨hsmall, ht.2⟩
          · exact Or.inr ⟨hshadow, ht.2⟩
      _ ≤ _ := (measure_union_le _ _).trans ((add_le_add hTfloor hTsparse).trans (by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply le_of_eq
        congr 1
        ring))
  have h := hTlow.trans hup
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  change κ * T ≤ κ / 2 * T at h
  nlinarith [mul_pos hκ hT0]

/-- The full zero divisor of an expansion in the open critical strip of width `2ω`. -/
def expansionStripZeros (c : Scale → ℂ) (ω : ℝ) : Set ℂ :=
  {z ∈ {z : ℂ | 1 / 2 - ω < z.re ∧ z.re < 1 / 2 + ω} | expansion c z = 0}

/-- At a zero of finite analytic order, multiplicity only increases residue mass. -/
private theorem norm_zeta_weight_le_residue {F : ℂ → ℂ} {τ₁ τ₂ : ℝ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | τ₁ < z.re ∧ z.re < τ₂})
    (hne : ∃ z, (τ₁ < z.re ∧ z.re < τ₂) ∧ F z ≠ 0)
    {p : ℂ} (hp : τ₁ < p.re ∧ p.re < τ₂) (hp0 : F p = 0) :
    ‖riemannZeta p / p‖ ≤
      ‖HTGeometry.weightedLogResidue F (fun z => -(riemannZeta z / z)) p‖ := by
  have hfin : analyticOrderAt F p ≠ ⊤ := by
    intro htop
    obtain ⟨z₁, hz₁, hz₁ne⟩ := hne
    exact hz₁ne (hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (isPreconnected_openStrip _ _) hp (analyticOrderAt_eq_top.mp htop) hz₁)
  have hord : 0 < analyticOrderNatAt F p := by
    apply Nat.pos_of_ne_zero
    intro horder
    obtain ⟨g, _, hg0, hfg⟩ := ((hF p hp).analyticOrderNatAt_eq_iff hfin).mp rfl
    have hvalue := hfg.self_of_nhds
    rw [horder, pow_zero, one_smul] at hvalue
    exact hg0 (hvalue.symm.trans hp0)
  simp only [HTGeometry.weightedLogResidue, norm_mul, norm_neg, Complex.norm_natCast]
  exact le_mul_of_one_le_left (norm_nonneg _) (by exact_mod_cast (Nat.succ_le_iff.mpr hord))

private theorem summable_restrict_subset {α : Type*} {S T : Set α} {f : α → ℝ}
    (hST : S ⊆ T) (hf : Summable (fun p : T => f p)) :
    Summable (fun p : S => f p) := by
  let incl : S → T := fun p => ⟨p, hST p.2⟩
  have hinj : Function.Injective incl := by
    intro p q h
    exact Subtype.ext (congrArg (fun z : T => (z : α)) h)
  exact hf.comp_injective hinj

/-- Every zero of a nonzero Wiener expansion forces infinite total residue mass
`Σ mρ |ζ(ρ)/ρ|` on its strip. No purity assumption is needed. -/
theorem expansion_zero_forces_nonsummable_residues {c : Scale → ℂ} {ω : ℝ}
    (hω0 : 0 < ω) (hω : ω ≤ 1 / 2)
    (hc : WSummable (1 / 2 - ω) (1 / 2 + ω) c) (hne : c ≠ 0)
    {s : ℂ} (hs : |s.re - 1 / 2| < ω) (hs0 : expansion c s = 0) :
    ¬ Summable (fun p : expansionStripZeros c ω => ‖expansionZetaResidue c p‖) := by
  classical
  intro hr
  let U : Set ℂ := {z | 1 / 2 - ω < z.re ∧ z.re < 1 / 2 + ω}
  have hFne : ∃ z₁ : ℂ, z₁ ∈ U ∧ expansion c z₁ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hne (eq_zero_of_expansion_eq_zero (le_refl (1 / 2 : ℝ))
      (hc.mono (by linarith) le_rfl (by linarith)) fun z h1 h2 => ?_)
    have hre : z.re = 1 / 2 := le_antisymm h2 h1
    exact hcon z ⟨by rw [hre]; linarith, by rw [hre]; linarith⟩
  rcases expansion_zero_forces_offLine_or_nonsummable_residues hω0 hω hc hne hs hs0 with
    ⟨ρ₀, hρ, hρzero, hρoff⟩ | hcrit
  · have hρbounds := abs_lt.mp hρ
    let R := (ω - |ρ₀.re - 1 / 2|) / 2
    have hR : 0 < R := by dsimp [R]; linarith
    have hAP : IsStripAlmostPeriodicOn (expansion c) ρ₀.re R :=
      isStripAlmostPeriodicOn_expansion (hc.mono
        (by dsimp [R]; linarith only [neg_le_abs (ρ₀.re - 1 / 2), hρ])
        (by linarith only [hR])
        (by dsimp [R]; linarith only [le_abs_self (ρ₀.re - 1 / 2), hρ]))
    have hnot := not_summable_zeta_weights_of_offLine_zero (differentiableOn_expansion hc)
      hFne (by linarith [hρbounds.1]) (by linarith [hρbounds.2])
      (by linarith [hρbounds.1]) (by linarith [hρbounds.2]) hρoff hρzero hR hAP
    apply hnot
    refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) ?_ hr
    intro p
    exact norm_zeta_weight_le_residue
      ((differentiableOn_expansion hc).analyticOnNhd (isOpen_openStrip _ _)) hFne p.2.1 p.2.2
  · apply hcrit
    refine summable_restrict_subset (f := fun p : ℂ => ‖expansionZetaResidue c p‖) ?_ hr
    intro p hp
    exact ⟨⟨by rw [hp.1]; linarith only [hω0], by rw [hp.1]; linarith only [hω0]⟩, hp.2⟩

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
