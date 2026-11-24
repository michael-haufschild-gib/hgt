import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.Readout

/-! # Measuring cancellation when two arithmetic energy gaps compose -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

theorem gapFrequency_product (a b c d : ℕ+) :
    gapFrequency (a,b) + gapFrequency (c,d) = gapFrequency (a*c,b*d) := by
  simp only [gapFrequency,energy_mul]
  ring

/-- Reducing an unreduced gap erases twice the common factor's energy from its loss before damping. -/
theorem lineLoss_unreduced {x : ℝ} (hx : 1/2 < x) (q : ℕ+ × ℕ+) :
    lineLoss x (gapFrequency q) = (x+x)*(energy q.1+energy q.2)-(4*x)*energy (q.1.gcd q.2) := by
  obtain ⟨⟨⟨⟨a,b⟩,hc⟩,k⟩,he⟩ := _root_.RHTower.thetaCuspPrimitiveRayIndexEquivPositivePair.surjective q
  change (a*k,b*k) = q at he
  subst q
  have hg : (a*k).gcd (b*k) = k := by
    apply PNat.coe_injective
    rw [PNat.gcd_coe,PNat.mul_coe,PNat.mul_coe,Nat.gcd_mul_right,(PNat.coprime_coe.mpr hc).gcd_eq_one,one_mul]
  dsimp only
  rw [gapFrequency_scale,lineLoss_reduced hx hc,hg,energy_mul,energy_mul]
  ring

/-- The triangle defect is exactly the energy erased by cancellation of common prime occupations. -/
theorem lineLoss_composition_defect {x : ℝ} (hx : 1/2 < x) {a b c d : ℕ+}
    (hab : a.Coprime b) (hcd : c.Coprime d) :
    lineLoss x (gapFrequency (a,b)) + lineLoss x (gapFrequency (c,d)) -
      lineLoss x (gapFrequency (a,b)+gapFrequency (c,d)) = (4*x)*energy ((a*c).gcd (b*d)) := by
  rw [gapFrequency_product,lineLoss_reduced hx hab,lineLoss_reduced hx hcd,lineLoss_unreduced hx]
  simp only [energy_mul]
  ring

/-- Three observed intensities and the damping recover the cancelled integer itself. -/
theorem read_cancelled_factor {x : ℝ} (hx : 1/2 < x) {a b c d : ℕ+} (hab : a.Coprime b) (hcd : c.Coprime d) :
    Real.exp ((lineLoss x (gapFrequency (a,b)) + lineLoss x (gapFrequency (c,d)) -
      lineLoss x (gapFrequency (a,b)+gapFrequency (c,d)))/(4*x)) = (((a*c).gcd (b*d) : ℕ):ℝ) := by
  rw [lineLoss_composition_defect hx hab hcd,mul_div_cancel_left₀ _ (by linarith : 4*x ≠ 0)]
  exact Real.exp_log (Nat.cast_pos.mpr ((a*c).gcd (b*d)).pos)

/-- Every two observed lines obey the triangle inequality, including opposite frequencies. -/
theorem observed_lineLoss_subadditive {x u v : ℝ} (hx : 1/2 < x)
    (hu : overlapCoefficient x u ≠ 0) (hv : overlapCoefficient x v ≠ 0) :
    lineLoss x (u+v) ≤ lineLoss x u + lineLoss x v := by
  obtain ⟨a,b,hc,rfl⟩ := (overlapCoefficient_support hx u).mp hu
  obtain ⟨c,d,hd,rfl⟩ := (overlapCoefficient_support hx v).mp hv
  apply sub_nonneg.mp
  rw [lineLoss_composition_defect hx hc hd]
  exact mul_nonneg (by linarith) (Real.log_natCast_nonneg _)

/-- Intensities multiply under composition exactly when the composed pair needs no reduction. -/
theorem lineLoss_additive_iff_coprime {x : ℝ} (hx : 1/2 < x) {a b c d : ℕ+}
    (hab : a.Coprime b) (hcd : c.Coprime d) :
    lineLoss x (gapFrequency (a,b)) + lineLoss x (gapFrequency (c,d)) =
      lineLoss x (gapFrequency (a,b)+gapFrequency (c,d)) ↔ (a*c).Coprime (b*d) := by
  rw [← sub_eq_zero,lineLoss_composition_defect hx hab hcd]
  constructor
  · intro h
    have he := (mul_eq_zero.mp h).resolve_left (by linarith)
    exact label_of_energy_eq (he.trans (by simp [energy]))
  · intro h
    change (a*c).gcd (b*d) = 1 at h
    simp [h,energy]

#print axioms gapFrequency_product
#print axioms lineLoss_unreduced
#print axioms lineLoss_composition_defect
#print axioms read_cancelled_factor
#print axioms observed_lineLoss_subadditive
#print axioms lineLoss_additive_iff_coprime

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
