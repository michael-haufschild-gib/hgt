import GaloisForLFunctions.RHTower.XiCTaylorSignedFourAtomLiteralReflectionEscape

/-!
# A literal four-atom profile encodes one transverse reflection orbit

The four-atom equal-charge construction is not only minimal: its projective coefficient ray
determines the reciprocal damping radius up to inversion.  This file classifies every four-atom
literal equal-charge profile as a scalar multiple of the explicit ray and proves that one nonzero
profile cannot work at two distinct transverse reflection orbits.

Thus the local four-atom survivor is target-informative.  A divisor-independent source lift must
derive its one permitted transverse orbit from source data; it cannot use the same ray uniformly
at another orbit.
-/

open Complex Real Polynomial Function

namespace RHTower

noncomputable section

/-! ## Closed coefficient formulas for the canonical ray -/

/-- The third canonical weight depends only on the reciprocal-orbit coordinate `r + r⁻¹`. -/
theorem signedFourAtomLiteralRayThree_eq_radiusOrbitFormula
    {r : ℝ} (hr : 0 < r) :
    signedFourAtomLiteralRayThree r =
      (r + r⁻¹) * (2 * (r + r⁻¹) + 3) / (1 + (r + r⁻¹)) := by
  have hr0 := hr.ne'
  have hden : 1 + (r + r⁻¹) ≠ 0 := by positivity
  have hsource : r * (1 + r + r ^ (2 : ℕ)) ≠ 0 := by positivity
  unfold signedFourAtomLiteralRayThree signedFourAtomLiteralRootSum
    signedFourAtomLiteralAuxRoot
  field_simp [hr0, hden, hsource]
  ring

/-- Closed first-weight formula in the reciprocal-orbit coordinate. -/
theorem signedFourAtomLiteralRayOne_eq_radiusOrbitFormula
    {r : ℝ} (hr : 0 < r) :
    signedFourAtomLiteralRayOne r =
      (r + r⁻¹) * (1 + (r + r⁻¹)) := by
  have hr0 := hr.ne'
  unfold signedFourAtomLiteralRayOne signedFourAtomLiteralRootSum
    signedFourAtomLiteralAuxRoot
  field_simp [hr0]
  ring

/-- Closed second-weight formula in the reciprocal-orbit coordinate. -/
theorem signedFourAtomLiteralRayTwo_eq_radiusOrbitFormula
    {r : ℝ} (hr : 0 < r) :
    signedFourAtomLiteralRayTwo r =
      -(r + r⁻¹) * ((r + r⁻¹) + 2) := by
  have hr0 := hr.ne'
  unfold signedFourAtomLiteralRayTwo signedFourAtomLiteralRootSum
    signedFourAtomLiteralAuxRoot
  field_simp [hr0]
  ring

/-- **Orbit reconstruction from one projective coordinate.** Equality of the third weights of
two positive canonical rays already forces their radii to belong to the same reciprocal orbit. -/
theorem signedFourAtomLiteralRayThree_orbit_injective
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (h :
      signedFourAtomLiteralRayThree r =
        signedFourAtomLiteralRayThree t) :
    t = r ∨ t = r⁻¹ := by
  have hr0 := hr.ne'
  have ht0 := ht.ne'
  have hrden : 1 + (r + r⁻¹) ≠ 0 := by positivity
  have htden : 1 + (t + t⁻¹) ≠ 0 := by positivity
  let x : ℝ := r + r⁻¹
  let y : ℝ := t + t⁻¹
  rw [signedFourAtomLiteralRayThree_eq_radiusOrbitFormula hr,
    signedFourAtomLiteralRayThree_eq_radiusOrbitFormula ht] at h
  change x * (2 * x + 3) / (1 + x) =
    y * (2 * y + 3) / (1 + y) at h
  have hxden : 1 + x ≠ 0 := by dsimp [x]; positivity
  have hyden : 1 + y ≠ 0 := by dsimp [y]; positivity
  have hsum : r + r⁻¹ = t + t⁻¹ := by
    have hfac :
        (x - y) * (2 * (1 + x) * (1 + y) + 1) = 0 := by
      field_simp [hxden, hyden] at h
      linear_combination h
    have hpos :
        0 < 2 * (1 + x) * (1 + y) + 1 := by
      dsimp [x, y]
      positivity
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp hfac).resolve_right hpos.ne')
  have horbit : (r - t) * (r * t - 1) = 0 := by
    have hmul := congrArg (fun x : ℝ => x * (r * t)) hsum
    field_simp [hr0, ht0] at hmul
    nlinarith
  rcases mul_eq_zero.mp horbit with hrt | hprod
  · exact Or.inl (sub_eq_zero.mp hrt).symm
  · exact Or.inr (eq_inv_of_mul_eq_one_right (sub_eq_zero.mp hprod))

/-! ## Complete four-atom equal-charge classification -/

/-- **Complete arity-four classification.** At one positive off-center reciprocal pair, the two
value-kernel equations and equality of the reflected derivative charges force every coefficient
vector onto the explicit canonical ray.  The statement includes the zero profile; no nonzero
charge premise is needed for classification. -/
theorem signedFourAtom_literalReflection_equalCharge_profile_classification
    {T r a₁ a₂ a₃ a₄ : ℝ}
    (hT : T ≠ 0) (hr : 0 < r) (hr1 : r ≠ 1)
    (hvaluePlus :
      signedFourAtomFullTurnValueCoefficient r a₁ a₂ a₃ a₄ = 0)
    (hvalueMinus :
      signedFourAtomFullTurnValueCoefficient r⁻¹ a₁ a₂ a₃ a₄ = 0)
    (hcharge :
      signedFourAtomFullTurnDerivativeCoefficient T r a₁ a₂ a₃ a₄ =
        signedFourAtomFullTurnDerivativeCoefficient T r⁻¹ a₁ a₂ a₃ a₄) :
    a₁ = -a₄ * signedFourAtomLiteralRayOne r ∧
      a₂ = -a₄ * signedFourAtomLiteralRayTwo r ∧
      a₃ = -a₄ * signedFourAtomLiteralRayThree r := by
  have hr0 := hr.ne'
  have hrInv1 : r⁻¹ ≠ 1 := inv_ne_one.mpr hr1
  have hrNeInv : r ≠ r⁻¹ := by
    intro hri
    have hmul := congrArg (fun x : ℝ => x * r) hri
    simp only [inv_mul_cancel₀ hr0] at hmul
    have hfac : (r - 1) * (r + 1) = 0 := by
      calc
        _ = r * r - 1 := by ring
        _ = 0 := by rw [hmul]; ring
    rcases mul_eq_zero.mp hfac with hminus | hplus
    · exact hr1 (sub_eq_zero.mp hminus)
    · nlinarith
  let x : ℝ := r + r⁻¹
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hxgt : 2 < x := by
    have hsq : 0 < (r - 1) ^ (2 : ℕ) := sq_pos_of_ne_zero (sub_ne_zero.mpr hr1)
    have hquot : 0 < (r - 1) ^ (2 : ℕ) / r := div_pos hsq hr
    have hid : (r - 1) ^ (2 : ℕ) / r = r + r⁻¹ - 2 := by
      field_simp [hr0]
      ring
    rw [hid] at hquot
    dsimp [x]
    linarith
  have hplus :
      a₁ + (1 + r) * a₂ + (1 + r + r ^ (2 : ℕ)) * a₃ +
        (1 + r + r ^ (2 : ℕ) + r ^ (3 : ℕ)) * a₄ = 0 := by
    have hfac :
        (1 - r) *
          (a₁ + (1 + r) * a₂ + (1 + r + r ^ (2 : ℕ)) * a₃ +
            (1 + r + r ^ (2 : ℕ) + r ^ (3 : ℕ)) * a₄) = 0 := by
      calc
        _ = signedFourAtomFullTurnValueCoefficient r a₁ a₂ a₃ a₄ := by
          unfold signedFourAtomFullTurnValueCoefficient
          ring
        _ = 0 := hvaluePlus
    exact (mul_eq_zero.mp hfac).resolve_left
      (sub_ne_zero.mpr hr1.symm)
  have hminus :
      a₁ + (1 + r⁻¹) * a₂ +
        (1 + r⁻¹ + (r⁻¹) ^ (2 : ℕ)) * a₃ +
        (1 + r⁻¹ + (r⁻¹) ^ (2 : ℕ) + (r⁻¹) ^ (3 : ℕ)) * a₄ = 0 := by
    have hfac :
        (1 - r⁻¹) *
          (a₁ + (1 + r⁻¹) * a₂ +
            (1 + r⁻¹ + (r⁻¹) ^ (2 : ℕ)) * a₃ +
            (1 + r⁻¹ + (r⁻¹) ^ (2 : ℕ) + (r⁻¹) ^ (3 : ℕ)) * a₄) = 0 := by
      calc
        _ = signedFourAtomFullTurnValueCoefficient r⁻¹ a₁ a₂ a₃ a₄ := by
          unfold signedFourAtomFullTurnValueCoefficient
          ring
        _ = 0 := hvalueMinus
    exact (mul_eq_zero.mp hfac).resolve_left
      (sub_ne_zero.mpr hrInv1.symm)
  have hchargeRaw :
      r * a₁ + 2 * r ^ (2 : ℕ) * a₂ + 3 * r ^ (3 : ℕ) * a₃ + 4 * r ^ (4 : ℕ) * a₄ =
        r⁻¹ * a₁ + 2 * (r⁻¹) ^ (2 : ℕ) * a₂ +
          3 * (r⁻¹) ^ (3 : ℕ) * a₃ + 4 * (r⁻¹) ^ (4 : ℕ) * a₄ := by
    have hnegT : -T ≠ 0 := neg_ne_zero.mpr hT
    apply mul_left_cancel₀ hnegT
    simpa only [signedFourAtomFullTurnDerivativeCoefficient] using hcharge
  have hdelta :
      a₂ + (1 + x) * a₃ + x * (1 + x) * a₄ = 0 := by
    have hfac :
        (r - r⁻¹) *
          (a₂ + (1 + x) * a₃ + x * (1 + x) * a₄) = 0 := by
      calc
        _ =
            (a₁ + (1 + r) * a₂ + (1 + r + r ^ (2 : ℕ)) * a₃ +
              (1 + r + r ^ (2 : ℕ) + r ^ (3 : ℕ)) * a₄) -
            (a₁ + (1 + r⁻¹) * a₂ +
              (1 + r⁻¹ + (r⁻¹) ^ (2 : ℕ)) * a₃ +
              (1 + r⁻¹ + (r⁻¹) ^ (2 : ℕ) + (r⁻¹) ^ (3 : ℕ)) * a₄) := by
                dsimp [x]
                field_simp [hr0]
                ring
        _ = 0 := by rw [hplus, hminus, sub_zero]
    exact (mul_eq_zero.mp hfac).resolve_left
      (sub_ne_zero.mpr hrNeInv)
  have hder :
      a₁ + 2 * x * a₂ + 3 * (x ^ (2 : ℕ) - 1) * a₃ +
        4 * (x ^ (3 : ℕ) - 2 * x) * a₄ = 0 := by
    have hfac :
        (r - r⁻¹) *
          (a₁ + 2 * x * a₂ + 3 * (x ^ (2 : ℕ) - 1) * a₃ +
            4 * (x ^ (3 : ℕ) - 2 * x) * a₄) = 0 := by
      calc
        _ =
            (r * a₁ + 2 * r ^ (2 : ℕ) * a₂ + 3 * r ^ (3 : ℕ) * a₃ + 4 * r ^ (4 : ℕ) * a₄) -
            (r⁻¹ * a₁ + 2 * (r⁻¹) ^ (2 : ℕ) * a₂ +
              3 * (r⁻¹) ^ (3 : ℕ) * a₃ + 4 * (r⁻¹) ^ (4 : ℕ) * a₄) := by
                dsimp [x]
                field_simp [hr0]
                ring
        _ = 0 := sub_eq_zero.mpr hchargeRaw
    exact (mul_eq_zero.mp hfac).resolve_left
      (sub_ne_zero.mpr hrNeInv)
  have hsum :
      2 * a₁ + (2 + x) * a₂ + x * (1 + x) * a₃ +
        (x ^ (3 : ℕ) + x ^ (2 : ℕ) - 2 * x) * a₄ = 0 := by
    calc
      _ =
          (a₁ + (1 + r) * a₂ + (1 + r + r ^ (2 : ℕ)) * a₃ +
            (1 + r + r ^ (2 : ℕ) + r ^ (3 : ℕ)) * a₄) +
          (a₁ + (1 + r⁻¹) * a₂ +
            (1 + r⁻¹ + (r⁻¹) ^ (2 : ℕ)) * a₃ +
            (1 + r⁻¹ + (r⁻¹) ^ (2 : ℕ) + (r⁻¹) ^ (3 : ℕ)) * a₄) := by
              dsimp [x]
              field_simp [hr0]
              ring
      _ = 0 := by rw [hplus, hminus, add_zero]
  have hmaster :
      -2 * (x - 2) *
        ((1 + x) * a₃ + x * (2 * x + 3) * a₄) = 0 := by
    linear_combination hsum - 2 * hder - (2 - 3 * x) * hdelta
  have hthird :
      (1 + x) * a₃ + x * (2 * x + 3) * a₄ = 0 := by
    exact (mul_eq_zero.mp hmaster).resolve_left
      (mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0)
        (sub_ne_zero.mpr (ne_of_gt hxgt)))
  have hRay₁ :
      signedFourAtomLiteralRayOne r = x * (1 + x) := by
    simpa only [x] using signedFourAtomLiteralRayOne_eq_radiusOrbitFormula hr
  have hRay₂ :
      signedFourAtomLiteralRayTwo r = -x * (x + 2) := by
    simpa only [x] using signedFourAtomLiteralRayTwo_eq_radiusOrbitFormula hr
  have hRay₃ :
      signedFourAtomLiteralRayThree r =
        x * (2 * x + 3) / (1 + x) := by
    simpa only [x] using signedFourAtomLiteralRayThree_eq_radiusOrbitFormula hr
  have ha₃ :
      a₃ = -a₄ * signedFourAtomLiteralRayThree r := by
    rw [hRay₃]
    have hxden : 1 + x ≠ 0 := by positivity
    rw [← mul_div_assoc]
    apply (eq_div_iff hxden).2
    linear_combination hthird
  have ha₂ :
      a₂ = -a₄ * signedFourAtomLiteralRayTwo r := by
    rw [hRay₂]
    have hxden : 1 + x ≠ 0 := by positivity
    have ha₃' : a₃ = (-a₄ * (x * (2 * x + 3))) / (1 + x) := by
      rw [ha₃, hRay₃]
      ring
    rw [show a₂ = -(1 + x) * a₃ - x * (1 + x) * a₄ by
      linarith [hdelta], ha₃']
    field_simp [hxden]
    ring
  have ha₁ :
      a₁ = -a₄ * signedFourAtomLiteralRayOne r := by
    rw [hRay₁]
    have hxden : 1 + x ≠ 0 := by positivity
    have ha₃' : a₃ = (-a₄ * (x * (2 * x + 3))) / (1 + x) := by
      rw [ha₃, hRay₃]
      ring
    have ha₂' : a₂ = a₄ * x * (x + 2) := by
      rw [ha₂, hRay₂]
      ring
    rw [show a₁ = -2 * x * a₂ - 3 * (x ^ (2 : ℕ) - 1) * a₃ -
        4 * (x ^ (3 : ℕ) - 2 * x) * a₄ by linarith [hder],
      ha₂', ha₃']
    field_simp [hxden]
    ring
  exact ⟨ha₁, ha₂, ha₃⟩

/-! ## Transverse information-capacity one -/

/-- **Four-atom transverse-orbit rigidity.** One literal coefficient vector which carries
nonzero equal reflected charge at `r` cannot also carry equal reflected charge at a distinct
positive reciprocal orbit.  The charge at the second orbit need not be assumed nonzero. -/
theorem signedFourAtom_literalReflection_twoOrbit_rigidity
    {T r t a₁ a₂ a₃ a₄ mr mt : ℝ}
    (hT : T ≠ 0)
    (hr : 0 < r) (hr1 : r ≠ 1)
    (ht : 0 < t) (ht1 : t ≠ 1)
    (hvalueRPlus :
      signedFourAtomFullTurnValueCoefficient r a₁ a₂ a₃ a₄ = 0)
    (hvalueRMinus :
      signedFourAtomFullTurnValueCoefficient r⁻¹ a₁ a₂ a₃ a₄ = 0)
    (hchargeRPlus :
      signedFourAtomFullTurnDerivativeCoefficient T r a₁ a₂ a₃ a₄ = mr)
    (hchargeRMinus :
      signedFourAtomFullTurnDerivativeCoefficient T r⁻¹ a₁ a₂ a₃ a₄ = mr)
    (hmr : mr ≠ 0)
    (hvalueTPlus :
      signedFourAtomFullTurnValueCoefficient t a₁ a₂ a₃ a₄ = 0)
    (hvalueTMinus :
      signedFourAtomFullTurnValueCoefficient t⁻¹ a₁ a₂ a₃ a₄ = 0)
    (hchargeTPlus :
      signedFourAtomFullTurnDerivativeCoefficient T t a₁ a₂ a₃ a₄ = mt)
    (hchargeTMinus :
      signedFourAtomFullTurnDerivativeCoefficient T t⁻¹ a₁ a₂ a₃ a₄ = mt) :
    t = r ∨ t = r⁻¹ := by
  have hclassR :=
    signedFourAtom_literalReflection_equalCharge_profile_classification
      hT hr hr1 hvalueRPlus hvalueRMinus
        (hchargeRPlus.trans hchargeRMinus.symm)
  have hclassT :=
    signedFourAtom_literalReflection_equalCharge_profile_classification
      hT ht ht1 hvalueTPlus hvalueTMinus
        (hchargeTPlus.trans hchargeTMinus.symm)
  have ha₄ : a₄ ≠ 0 := by
    intro ha₄
    have ha₁ : a₁ = 0 := by
      rw [hclassR.1, ha₄]
      ring
    have ha₂ : a₂ = 0 := by
      rw [hclassR.2.1, ha₄]
      ring
    have ha₃ : a₃ = 0 := by
      rw [hclassR.2.2, ha₄]
      ring
    rw [ha₁, ha₂, ha₃, ha₄] at hchargeRPlus
    simp [signedFourAtomFullTurnDerivativeCoefficient] at hchargeRPlus
    exact hmr hchargeRPlus.symm
  have hthird :
      signedFourAtomLiteralRayThree r =
        signedFourAtomLiteralRayThree t := by
    apply mul_left_cancel₀ (neg_ne_zero.mpr ha₄)
    calc
      -a₄ * signedFourAtomLiteralRayThree r = a₃ := hclassR.2.2.symm
      _ = -a₄ * signedFourAtomLiteralRayThree t := hclassT.2.2
  exact signedFourAtomLiteralRayThree_orbit_injective hr ht hthird

end

end RHTower
