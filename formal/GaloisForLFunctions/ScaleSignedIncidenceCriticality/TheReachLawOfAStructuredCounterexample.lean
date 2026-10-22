import GaloisForLFunctions.ScaleSignedIncidenceCriticality.AliasingIsFreeInsideAnyBackground

/-!
# The reach law of a structured counterexample

The two hiding mechanisms have now been separated and each made sharp. This module puts them
together into a single two-sided law for how far a structured off-line set can hide, with both
bounds explicit.

Let the configuration be an off-line sub-lattice of spacing parameter `ℓ` and depth `δ` inside an
on-line background of mass `2L`, and consider apertures `a ≤ L/2`. Then

* **lower reach** (`reach_lower`): positivity holds for every `a ≤ min (ℓ/2) (L/2)`, free of charge
  and at every depth — the aliasing regime of `AliasingIsFreeInsideAnyBackground`, sharp by
  `TheFreeRegimeEndsExactlyAtNyquist`;
* **upper reach** (`reach_upper`): positivity at `a` forces

  `a ≤ log ((3L + ℓ)/ℓ) / (2δ) + ℓ/2`,

  from the exchange law of `TheMassApertureExchangeLaw` together with `2a ≤ L`.

`theReachLaw` states the pair. In words: **the reach is the aliasing scale plus a logarithm of the
mass-to-dilution ratio, divided by twice the depth.** The first term is free and comes from the
arithmetic structure of the off-line set; the second is bought with mass and is only logarithmic in
it; and the depth divides, so deeper zeros hide less far.

This is the quantitative form of the field's central wall, with every ingredient named. It also says
exactly which parameter a mechanism should attack: not the mass, whose contribution is a logarithm,
but the dilution `ℓ` — the arithmetic structure of the hypothetical off-line set, whose contribution
is linear.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The lower reach: aliasing, free -/

/-- **Lower reach.** Below the sub-lattice's own Nyquist aperture positivity is free. -/
theorem reach_lower {ℓ L δ a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (ha : 0 < a) (haℓ : a ≤ ℓ / 2) (haL : a ≤ L / 2) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re :=
  dilutedLattice_hides_below_own_nyquist hℓ hL hδ hδ' ha haℓ haL hf hfs

/-! ### 2. The upper reach: a logarithm of the mass -/

/-- **Upper reach.** Positivity at aperture `a` forces `a` below the aliasing scale plus a
logarithm of the mass-to-dilution ratio, divided by twice the depth. -/
theorem reach_upper {ℓ L δ a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (ha : 0 < a) (haL : a ≤ L / 2)
    (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) :
    a ≤ Real.log ((3 * L + ℓ) / ℓ) / (2 * δ) + ℓ / 2 := by
  have hmass := mass_ge_of_dilutedLattice_positive hℓ hL hδ hδ' ha haL hpos
  have hcap : ℓ * Real.exp (δ * (2 * a - ℓ)) ≤ 3 * L + ℓ := by
    have h2a : 2 * a ≤ L := by linarith
    linarith
  have hquot : Real.exp (δ * (2 * a - ℓ)) ≤ (3 * L + ℓ) / ℓ := by
    rw [le_div_iff₀ hℓ]; linarith
  have hposq : (0 : ℝ) < (3 * L + ℓ) / ℓ := by positivity
  have hlog : δ * (2 * a - ℓ) ≤ Real.log ((3 * L + ℓ) / ℓ) :=
    (Real.le_log_iff_exp_le hposq).mpr hquot
  rw [← sub_le_iff_le_add, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * δ)]
  nlinarith [hlog]

/-! ### 3. The law -/

/-- **The reach law.** The hiding reach of a structured off-line set lies between its own aliasing
scale, which is free, and that scale plus a logarithm of the mass-to-dilution ratio divided by twice
the depth, which must be bought. -/
theorem theReachLaw {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    (∀ a : ℝ, 0 < a → a ≤ ℓ / 2 → a ≤ L / 2 → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f →
        tsupport f ⊆ Icc (-a) a → 0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) ∧
      ∀ a : ℝ, 0 < a → a ≤ L / 2 →
        (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
          0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) →
        a ≤ Real.log ((3 * L + ℓ) / ℓ) / (2 * δ) + ℓ / 2 :=
  ⟨fun _ ha haℓ haL _ hf hfs => reach_lower hℓ hL hδ hδ' ha haℓ haL hf hfs,
    fun _ ha haL hpos => reach_upper hℓ hL hδ hδ' ha haL hpos⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
