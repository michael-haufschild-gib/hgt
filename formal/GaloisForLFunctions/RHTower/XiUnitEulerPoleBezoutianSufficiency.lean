/-
# The translated Bezoutian classifier: sufficiency

If the value fibre `xi = c` lies entirely on the critical line, then the translated Bezoutian of
`X_c(w) = xi (1/2 + w) - c` is positive semidefinite on the open right half plane.

`X_c` is even by the functional equation, entire of order one, and its zeros are exactly the
critical-line preimages of `c` recentred at the origin, hence purely imaginary.  The imaginary
divisor Bezoutian theorem then applies verbatim, and combining it with the necessity half gives the
exact classification of the value fibre.
-/
import GaloisForLFunctions.RHTower.XiUnitEulerPoleAffineSection
import GaloisForLFunctions.RHTower.ImaginaryZeroBezoutianPositivity
import GaloisForLFunctions.RHTower.EntireWeightedLittlewoodRectangle
import GaloisForLFunctions.RHTower.CompletedZetaGrowth
import GaloisForLFunctions.HTGeometry.OrderOneEnvelope

noncomputable section

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped ComplexOrder

namespace RHTower

/-- The centred value fibre is even: the functional equation reflects `1/2 + w` to `1/2 - w`. -/
theorem xiTranslatedCentered_even (c : ℂ) (w : ℂ) :
    xiTranslatedCentered c (-w) = xiTranslatedCentered c w := by
  rw [xiTranslatedCentered, xiTranslatedCentered]
  congr 1
  rw [show (1 : ℂ) / 2 + -w = 1 - (1 / 2 + w) by ring, xi_one_sub]

/-- The centred value fibre has an order-one growth envelope. -/
theorem orderOneEnvelope_xiTranslatedCentered (c : ℂ) :
    OrderOneEnvelope (xiTranslatedCentered c) := by
  have hxi : OrderOneEnvelope xi := xi_growth_order_le_one
  have hshift : OrderOneEnvelope (fun w : ℂ => xi (1 * w + 1 / 2)) := hxi.comp_affine 1 (1 / 2)
  have hshift' : OrderOneEnvelope (fun w : ℂ => xi (1 / 2 + w)) :=
    hshift.congr (fun s => congrArg xi (by ring))
  exact (hshift'.add (orderOneEnvelope_const (-c))).congr (fun s => by
    rw [xiTranslatedCentered]; ring)

/-- The centred value fibre is nowhere locally zero. -/
theorem analyticOrderAt_xiTranslatedCentered_ne_top (c : ℂ) (z : ℂ) :
    analyticOrderAt (xiTranslatedCentered c) z ≠ ⊤ :=
  analyticOrderAt_ne_top_of_entire_exists_ne_zero (analyticOnNhd_xiTranslatedCentered c)
    (xiTranslatedCentered_ne_zero_somewhere c) z

/-- **The Bezoutian classifier, sufficiency.**  If the selected value fibre lies on the critical
line, every finite Gram matrix of the translated Bezoutian over the open right half plane is
positive semidefinite. -/
theorem posSemidef_xiTranslatedBezoutian_of_critical {c : ℂ}
    (hcrit : ∀ s : ℂ, xi s = c → s.re = 1 / 2)
    {n : ℕ} (w : Fin n → ℂ) (hw : ∀ j, 0 < (w j).re) :
    (Matrix.of fun j k => xiTranslatedBezoutian c (w j) (w k)).PosSemidef := by
  obtain ⟨C, hC, hbound⟩ := orderOneEnvelope_xiTranslatedCentered c
  have himag : ∀ z : ℂ, xiTranslatedCentered c z = 0 → z.re = 0 := by
    intro z hz
    have hval : xi (1 / 2 + z) = c := by
      rw [xiTranslatedCentered, sub_eq_zero] at hz
      exact hz
    have := hcrit _ hval
    rw [Complex.add_re] at this
    simp only [Complex.div_re, Complex.one_re, Complex.one_im] at this
    norm_num at this
    linarith
  exact OrderOneHadamard.posSemidef_bezoutian_of_imaginary_zeros hC.le
    (analyticOnNhd_xiTranslatedCentered c)
    (analyticOrderAt_xiTranslatedCentered_ne_top c)
    (xiTranslatedCentered_even c) hbound himag w hw

/-- **The exact value-fibre classification.**  Positive semidefiniteness of the translated
Bezoutian on the open right half plane is equivalent to the selected value fibre lying on the
critical line. -/
theorem posSemidef_xiTranslatedBezoutian_iff (c : ℂ) :
    (∀ (n : ℕ) (w : Fin n → ℂ), (∀ j, 0 < (w j).re) →
        (Matrix.of fun j k => xiTranslatedBezoutian c (w j) (w k)).PosSemidef)
      ↔ ∀ s : ℂ, xi s = c → s.re = 1 / 2 := by
  constructor
  · intro hpsd s hs
    refine re_eq_half_of_xiTranslatedBezoutian_nonneg (c := c) (fun v hv => ?_) hs
    have hM := hpsd 1 (fun _ => v) (fun _ => hv)
    have hquad : (0 : ℂ) ≤ (Matrix.of fun j k : Fin 1 => xiTranslatedBezoutian c v v) 0 0 :=
      Matrix.PosSemidef.diag_nonneg hM
    rw [Matrix.of_apply] at hquad
    exact (Complex.le_def.mp hquad).1
  · intro hcrit n w hw
    exact posSemidef_xiTranslatedBezoutian_of_critical hcrit w hw

/-- **The marked top-down chain.**  The Riemann hypothesis is equivalent to the existence of a real
translation whose decompleted residue at the zeta pole is the unit and whose translated Bezoutian is
positive semidefinite on the open right half plane.  The residue condition marks the affine origin,
the Bezoutian condition orients the selected fibre. -/
theorem riemannHypothesis_iff_unitResidue_and_posSemidef_bezoutian :
    RiemannHypothesis ↔ ∃ c : ℝ,
      Tendsto (fun s => (s - 1) * zetaTranslatedDecompletion (c : ℂ) s) (𝓝[≠] (1 : ℂ)) (𝓝 1) ∧
      ∀ (n : ℕ) (w : Fin n → ℂ), (∀ j, 0 < (w j).re) →
        (Matrix.of fun j k => xiTranslatedBezoutian (c : ℂ) (w j) (w k)).PosSemidef := by
  constructor
  · intro hRH
    refine ⟨0, ?_, ?_⟩
    · have h := tendsto_translatedDecompletion_residue ((0 : ℝ) : ℂ)
      simpa using h
    · intro n w hw
      refine posSemidef_xiTranslatedBezoutian_of_critical (fun s hs => ?_) w hw
      exact riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH s (by simpa using hs)
  · rintro ⟨c, hres, hpsd⟩
    have hlim := tendsto_translatedDecompletion_residue ((c : ℝ) : ℂ)
    have huniq : (1 : ℂ) - 2 * ((c : ℝ) : ℂ) = 1 := tendsto_nhds_unique hlim hres
    have hc0 : ((c : ℝ) : ℂ) = 0 := (translatedDecompletion_residue_eq_one_iff _).mp huniq
    refine riemannHypothesis_iff_xi_zero_re_eq_half.mpr (fun ρ hρ => ?_)
    refine (posSemidef_xiTranslatedBezoutian_iff ((c : ℝ) : ℂ)).mp hpsd ρ ?_
    rw [hc0]
    exact hρ

end RHTower
