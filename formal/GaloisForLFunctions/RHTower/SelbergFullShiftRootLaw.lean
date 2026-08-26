import GaloisForLFunctions.RHTower.SelbergShiftLatticeRegularity
import GaloisForLFunctions.RHTower.SelbergClass.Full

/-!
# Shift-lattice root law for the full Selberg class

The extended carrier's cusp root law asks separately that the first Dirichlet coefficient be
nonzero.  For the full Selberg class this is automatic from the normalization `a_F(1) = 1`.
These wrappers state the resulting law directly on `SelbergClass`.
-/

open Filter Topology Complex

namespace RHTower

noncomputable section

/-- The shift-lattice cusp root law for a full Selberg-class member.  Normalization discharges the
nonzero first-coefficient premise. -/
theorem SelbergClass.limsup_norm_shift_rpow_inv_of_height
    (F : SelbergClass) (hd : 0 < F.gammaData.degree) {s₀ : ℂ}
    (hheight : F.gammaData.gammaTailHeight < |s₀.im|)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hfreq : ∃ᶠ k : ℕ in atTop,
      c₀ ≤ ‖F.gammaData.asymmetricS
        (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖) :
    limsup (fun k : ℕ =>
        (‖F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ / (k.factorial : ℝ)) ^
          (1 / (k : ℝ))) atTop
      = F.gammaData.conductor ^ (1 / F.gammaData.degree)
        / (2 * Real.pi * F.gammaData.degree) := by
  have ha1 : (F.toExtendedSelbergClass.coeff 1 : ℂ) ≠ 0 := by
    rw [F.coeff_one]
    exact one_ne_zero
  exact F.toExtendedSelbergClass.limsup_norm_shift_rpow_inv_of_height
    hd ha1 hheight hc₀ hfreq

/-- The full-class shift-lattice root law with sine nondegeneracy discharged by a rank-one gamma
presentation. -/
theorem SelbergClass.limsup_norm_shift_rpow_inv_of_halfRate_of_height
    (F : SelbergClass) (hd : 0 < F.gammaData.degree) {s₀ : ℂ}
    (hrate : ∀ j, F.gammaData.lambda j = F.gammaData.degree / 2)
    (hheight : F.gammaData.gammaTailHeight < |s₀.im|) :
    limsup (fun k : ℕ =>
        (‖F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ / (k.factorial : ℝ)) ^
          (1 / (k : ℝ))) atTop
      = F.gammaData.conductor ^ (1 / F.gammaData.degree)
        / (2 * Real.pi * F.gammaData.degree) := by
  have ha1 : (F.toExtendedSelbergClass.coeff 1 : ℂ) ≠ 0 := by
    rw [F.coeff_one]
    exact one_ne_zero
  exact F.toExtendedSelbergClass.limsup_norm_shift_rpow_inv_of_halfRate_of_height
    hd ha1 hrate hheight

end


end RHTower
