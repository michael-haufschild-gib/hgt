import GaloisForLFunctions.RHTower.Sieve.TotientMoebiusNormalisation
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import GaloisForLFunctions.RHTower.SelbergThetaCommonForcingPairing
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinActualFourierCoefficient
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinCoprimeRowSum

/-!
# Arithmetic coordinates for the native theta horizontal weight

The complete primitive-row mean of the fixed positive theta source becomes a totient-weighted
lattice sum of its inverse-square radial projection. The actual projection is uniformly bounded,
has an inverse-cube tail, and is absolutely integrable on the positive half-line. These bounds
admit the full divisor-pair sum, so Möbius inversion retains every row and every sign.

With `a = sqrt y`, `B = radialMass`, `L = moebiusDensity`, and `Q = quadratureError`, the final
identity is `J(y) - L*B = f(y) + sum_d mu(d)/d^2 * Q(d*a)`. Its remainder converges absolutely.
The native mean identification and the stronger signed cancellation estimate are separate inputs.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
set_option autoImplicit false
namespace RHTower.SelbergThetaHorizontalArithmetic
open D4BMModularCore D4BMJointSource D4BMGlobalAngularResponse SelbergThetaNativeSource
noncomputable section

private def heightProfile (y : ℝ) : ℂ := (positiveProfile y:ℂ)
private def source (z : UpperHalfPlane) : ℂ := (positiveSource z:ℂ)

private theorem heightProfile_power_bound (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → ‖heightProfile y‖ ≤ C*y^r := by
  obtain ⟨C,hC,hb⟩ := positiveProfile_power_bound r
  refine ⟨C,hC,fun y hy => ?_⟩
  have hp : 0 < positiveProfile y :=
    mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all _)
  simpa [heightProfile,abs_of_pos hp] using hb y hy

private theorem heightProfile_measurable : Measurable heightProfile := by
  unfold heightProfile positiveProfile
  exact Complex.continuous_ofReal.measurable.comp
    (((Real.measurable_log.div_const 2).exp).mul
      (contDiff_thetaCuspFullSource.continuous.measurable.comp (Real.measurable_log.div_const 2)))

private theorem rows_summable (z : UpperHalfPlane) :
    Summable (fun v : gammaSetHalf => heightProfile (gammaSetMatrix v.1 • z).im) := by
  obtain ⟨C,_,hb⟩ := heightProfile_power_bound 2
  apply Summable.of_norm_bounded ((positiveCuspRows_summable 2 (by norm_num) z).mul_left C)
  intro v
  exact hb _ (gammaSetMatrix v.1 • z).im_pos

private theorem source_eq_rows (z : UpperHalfPlane) :
    source z = ∑' v : gammaSetHalf, heightProfile (gammaSetMatrix v.1 • z).im := by
  unfold source positiveSource heightProfile
  exact Complex.ofReal_tsum _

private theorem point_im (x y : ℝ) (hy : 0 < y) :
    (ofComplex (⟨x,y⟩:ℂ)).im = y := by
  rw [ofComplex_apply_of_im_pos hy]
  rfl

private def positiveHalfRow (p : D4BMPositivePrimitivePair) : gammaSetHalf :=
  ⟨primitiveRowEquiv p.1, Or.inl p.2⟩

private theorem positiveHalfRow_injective : Function.Injective positiveHalfRow := by
  intro p q h
  exact Subtype.ext (primitiveRowEquiv.injective (congrArg Subtype.val h))

private theorem positiveHalfRow_ne_identity (p : D4BMPositivePrimitivePair) :
    positiveHalfRow p ≠ cuspIdentityRow := by
  intro h
  have he := congrArg (fun v : gammaSetHalf => v.1.1 0) h
  change p.1.pair.1 = 0 at he
  exact (ne_of_gt p.2) he

private def halfRowMap : Unit ⊕ D4BMPositivePrimitivePair → gammaSetHalf
  | Sum.inl _ => cuspIdentityRow
  | Sum.inr p => positiveHalfRow p

private theorem halfRowMap_bijective : Function.Bijective halfRowMap := by
  constructor
  · rintro (a | p) (b | q) h
    · cases a; cases b; rfl
    · exact False.elim (positiveHalfRow_ne_identity q h.symm)
    · exact False.elim (positiveHalfRow_ne_identity p h)
    · exact congrArg Sum.inr (positiveHalfRow_injective h)
  · intro v
    by_cases hv : v = cuspIdentityRow
    · exact ⟨Sum.inl (), hv.symm⟩
    · let p : D4BMPositivePrimitivePair :=
        ⟨primitiveRowEquiv.symm v.1, by
          change 0 < v.1.1 0
          exact cuspRow_c_pos hv⟩
      refine ⟨Sum.inr p, ?_⟩
      exact Subtype.ext (primitiveRowEquiv.apply_symm_apply v.1)

private def halfRowEquiv : Unit ⊕ D4BMPositivePrimitivePair ≃ gammaSetHalf :=
  Equiv.ofBijective halfRowMap halfRowMap_bijective

private theorem primitive_height (z : UpperHalfPlane) (p : D4BMPrimitiveIntegerPair) :
    (gammaSetMatrix (primitiveRowEquiv p) • z).im =
      z.im / d4BMPoincareQuadratic ⟨z.re,z.im,z.im_pos⟩ p.pair := by
  have he := poincareSeed_eq_row_height z (1:ℂ) p
  simp only [d4BMPoincareSeed, Complex.cpow_one] at he
  exact (Complex.ofReal_injective he).symm

private theorem source_positive_rows (z : UpperHalfPlane) :
    source z = heightProfile z.im +
      ∑' p : D4BMPositivePrimitivePair,
        heightProfile (gammaSetMatrix (primitiveRowEquiv p.1) • z).im := by
  have hs := (rows_summable z).comp_injective halfRowEquiv.injective
  have ha := hs.comp_injective Sum.inl_injective
  have hb := hs.comp_injective Sum.inr_injective
  rw [source_eq_rows, ← halfRowEquiv.tsum_eq
    (fun v : gammaSetHalf => heightProfile (gammaSetMatrix v.1 • z).im)]
  have he := ha.tsum_sum hb
  simp only [Function.comp_apply] at he
  rw [he]
  change (∑' u : Unit, heightProfile (gammaSetMatrix cuspIdentityRow.1 • z).im) + _ = _
  simp only [tsum_fintype, Finset.univ_unique, Finset.sum_singleton, cuspIdentityRow_height]
  rfl

private theorem source_denominator_rows (z : UpperHalfPlane) :
    source z = heightProfile z.im + ∑' c : ℕ+,
      ∑' d : D4BMCoprimeInteger (d4BMPositiveModulusOfPNat c),
        heightProfile (gammaSetMatrix (primitiveRowEquiv
          (d4BMCoprimeIntegerToPrimitivePair (d4BMPositiveModulusOfPNat c) d)) • z).im := by
  have hs := (rows_summable z).comp_injective positiveHalfRow_injective
  have hi := hs.comp_injective d4BMPositiveCuspIndexEquivPrimitivePair.injective
  rw [source_positive_rows, ← d4BMPositiveCuspIndexEquivPrimitivePair.tsum_eq
    (fun p : D4BMPositivePrimitivePair =>
      heightProfile (gammaSetMatrix (primitiveRowEquiv p.1) • z).im)]
  have he := hi.tsum_sigma
  simp only [Function.comp_apply, positiveHalfRow] at he
  rw [he]
  rfl

private abbrev UnitResidue (c : ℕ+) :=
  {a : ZMod (d4BMPositiveModulusOfPNat c).value // IsUnit a}

/-- The complete real-translation profile for one positive denominator. -/
def archProfile (y : ℝ) (c : ℕ+) (x : ℝ) : ℂ :=
  heightProfile (y / (((c:ℕ):ℝ)^2*(y^2+x^2)))

/-- The sum of every reduced-residue periodization for one positive denominator. -/
private def denominatorSlice (y : ℝ) (c : ℕ+) (x : ℝ) : ℂ :=
  ∑' a : UnitResidue c, l1Periodization (archProfile y c) (x+(a.1.val:ℝ)/(c:ℕ))

private theorem unitTranslate_height (z : UpperHalfPlane) (c : ℕ+)
    (p : D4BMUnitResidueTranslateIndex (d4BMPositiveModulusOfPNat c)) :
    (gammaSetMatrix (primitiveRowEquiv (d4BMUnitResidueTranslateToPrimitivePair
      (d4BMPositiveModulusOfPNat c) p)) • z).im =
      z.im / (((c:ℕ):ℝ)^2*(z.im^2+(z.re+(p.1.1.val:ℝ)/(c:ℕ)+(p.2:ℝ))^2)) := by
  rw [primitive_height]
  congr 1
  have hc : (((c:ℕ):ℝ)) ≠ 0 := by exact_mod_cast c.ne_zero
  dsimp [d4BMUnitResidueTranslateToPrimitivePair, d4BMCoprimeIntegerToPrimitivePair,
    d4BMUnitResidueTranslateEquivCoprimeInteger, d4BMUnitResidueTranslateToCoprimeInteger,
    d4BMPositiveModulusOfPNat, d4BMPoincareQuadratic]
  push_cast
  field_simp [hc]
  ring!

private theorem denominator_rows_eq_slice (z : UpperHalfPlane) (c : ℕ+) :
    (∑' d : D4BMCoprimeInteger (d4BMPositiveModulusOfPNat c),
      heightProfile (gammaSetMatrix (primitiveRowEquiv
        (d4BMCoprimeIntegerToPrimitivePair (d4BMPositiveModulusOfPNat c) d)) • z).im) =
      denominatorSlice z.im c z.re := by
  have hs := (rows_summable z).comp_injective positiveHalfRow_injective
  have hi := hs.comp_injective d4BMPositiveCuspIndexEquivPrimitivePair.injective
  have hinj : Function.Injective
      (fun d : D4BMCoprimeInteger (d4BMPositiveModulusOfPNat c) => (⟨c,d⟩:D4BMPositiveCuspIndex)) := by
    intro d e h
    simpa using h
  have hq := hi.comp_injective hinj
  have hp := hq.comp_injective
    (d4BMUnitResidueTranslateEquivCoprimeInteger (d4BMPositiveModulusOfPNat c)).injective
  have hp' : Summable (fun p : D4BMUnitResidueTranslateIndex (d4BMPositiveModulusOfPNat c) =>
      heightProfile (gammaSetMatrix (primitiveRowEquiv
        (d4BMUnitResidueTranslateToPrimitivePair (d4BMPositiveModulusOfPNat c) p)) • z).im) := hp
  rw [← (d4BMUnitResidueTranslateEquivCoprimeInteger (d4BMPositiveModulusOfPNat c)).tsum_eq
    (fun d => heightProfile (gammaSetMatrix (primitiveRowEquiv
      (d4BMCoprimeIntegerToPrimitivePair (d4BMPositiveModulusOfPNat c) d)) • z).im)]
  change (∑' p : D4BMUnitResidueTranslateIndex (d4BMPositiveModulusOfPNat c),
      heightProfile (gammaSetMatrix (primitiveRowEquiv
        (d4BMUnitResidueTranslateToPrimitivePair (d4BMPositiveModulusOfPNat c) p)) • z).im) = _
  rw [hp'.tsum_prod]
  unfold denominatorSlice l1Periodization archProfile
  apply tsum_congr
  intro a
  apply tsum_congr
  intro k
  rw [unitTranslate_height]

/-- Exact decomposition of the complete source into its parabolic row and every reduced-residue
periodization at every positive denominator. -/
private theorem source_eq_denominator_slices (z : UpperHalfPlane) :
    source z = heightProfile z.im +
      ∑' c : ℕ+, denominatorSlice z.im c z.re := by
  rw [source_denominator_rows]
  congr 1
  apply tsum_congr
  intro c
  exact denominator_rows_eq_slice z c


private def cauchyMajorant (y x : ℝ) : ℝ := (y^2+x^2)^(-(2:ℝ))

private theorem cauchyMajorant_integrable (y : ℝ) (hy : 0 < y) :
    Integrable (cauchyMajorant y) := by
  have h := (integrable_d4BMCauchyPowerKernel ⟨0,y,hy⟩ ⟨2,by norm_num⟩).norm
  change Integrable (fun x => (y^2+x^2)^(-(2:ℝ)))
  simpa [norm_d4BMCauchyPowerKernel] using h

private theorem archProfile_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : ℝ), 0 < y → ∀ (c : ℕ+) (x : ℝ),
      ‖archProfile y c x‖ ≤
        (C*y^2*((c:ℕ):ℝ)^(-(4:ℝ)))*cauchyMajorant y x := by
  obtain ⟨C,hC,hb⟩ := heightProfile_power_bound 2
  refine ⟨C,hC,fun y hy c x => ?_⟩
  have hc : 0 < ((c:ℕ):ℝ) := by exact_mod_cast c.pos
  have hq : 0 < y^2+x^2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hy) (sq_nonneg x)
  have h := hb (y/(((c:ℕ):ℝ)^2*(y^2+x^2))) (by positivity)
  change ‖archProfile y c x‖ ≤ _ at h
  convert h using 1
  unfold cauchyMajorant
  rw [Real.rpow_neg hc.le, Real.rpow_neg hq.le]
  norm_num
  field_simp [hc.ne', hq.ne']

private theorem archProfile_measurable (y : ℝ) (c : ℕ+) :
    Measurable (archProfile y c) := by
  exact (heightProfile_measurable).comp (by fun_prop)

/-- Every complete translation profile is absolutely integrable. -/
theorem archProfile_integrable (y : ℝ) (hy : 0 < y) (c : ℕ+) :
    Integrable (archProfile y c) := by
  obtain ⟨C,_,hb⟩ := archProfile_bound
  exact ((cauchyMajorant_integrable y hy).const_mul
    (C*y^2*((c:ℕ):ℝ)^(-(4:ℝ)))).mono'
      (archProfile_measurable y c).aestronglyMeasurable (ae_of_all _ (hb y hy c))

private theorem shiftedPeriodization_integrable {f : ℝ → ℂ} (hf : Integrable f) (a : ℝ) :
    IntegrableOn (fun x => l1Periodization f (x+a)) (Ioc 0 1) := by
  have h := integrableOn_Ioc_l1Periodization (hf.comp_add_right a)
  exact h.congr (ae_of_all _ (fun x => (d4BM_l1Periodization_add_eq_translated f x a).symm))

private theorem shiftedPeriodization_norm_le {f : ℝ → ℂ} (hf : Integrable f) (a : ℝ) :
    (∫ x in Ioc (0:ℝ) 1, ‖l1Periodization f (x+a)‖) ≤ ∫ t, ‖f t‖ := by
  have h := integral_unit_norm_l1Periodization_le_integral_norm (hf.comp_add_right a)
  have ht := (measurePreserving_add_right volume a).integral_comp
    (MeasurableEquiv.addRight a).measurableEmbedding (fun t => ‖f t‖)
  simpa only [← d4BM_l1Periodization_add_eq_translated] using h.trans_eq ht

private theorem shiftedPeriodization_mean {f : ℝ → ℂ} (hf : Integrable f) (a : ℝ) :
    (∫ x in Ioc (0:ℝ) 1, l1Periodization f (x+a)) = ∫ t, f t := by
  have h := integral_unit_l1Periodization_mul_fourier_eq (hf.comp_add_right a) 0
  have ht := (measurePreserving_add_right volume a).integral_comp
    (MeasurableEquiv.addRight a).measurableEmbedding f
  have h' : (∫ x in Ioc (0:ℝ) 1, l1Periodization f (x+a)) = ∫ t, f (t+a) := by
    simpa [← d4BM_l1Periodization_add_eq_translated, Real.fourier_eq] using h
  exact h'.trans ht

private theorem unitResidue_card (c : ℕ+) :
    Fintype.card (UnitResidue c) = (c:ℕ).totient := by
  let e : (ZMod (d4BMPositiveModulusOfPNat c).value)ˣ ≃ UnitResidue c :=
    { toFun := fun u => ⟨u,u.isUnit⟩
      invFun := fun x => x.prop.unit
      left_inv := fun u => IsUnit.unit_of_val_units u.isUnit
      right_inv := fun x => Subtype.ext (IsUnit.unit_spec x.prop) }
  rw [← Fintype.card_congr e, ZMod.card_units_eq_totient]
  rfl

private theorem denominatorSlice_integrable (y : ℝ) (hy : 0 < y) (c : ℕ+) :
    IntegrableOn (denominatorSlice y c) (Ioc 0 1) := by
  exact GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    (fun a : UnitResidue c => shiftedPeriodization_integrable
      (archProfile_integrable y hy c) ((a.1.val:ℝ)/(c:ℕ))) Summable.of_finite

private theorem denominatorSlice_mean (y : ℝ) (hy : 0 < y) (c : ℕ+) :
    (∫ x in Ioc (0:ℝ) 1, denominatorSlice y c x) =
      ((c:ℕ).totient:ℂ)*(∫ t, archProfile y c t) := by
  unfold denominatorSlice
  rw [GaloisForLFunctions.HTGeometry.integral_tsum_eq_tsum_integral_of_summable_integral_norm
    (fun a : UnitResidue c => shiftedPeriodization_integrable
      (archProfile_integrable y hy c) ((a.1.val:ℝ)/(c:ℕ))) Summable.of_finite]
  simp only [shiftedPeriodization_mean (archProfile_integrable y hy c)]
  simp [tsum_fintype, unitResidue_card, nsmul_eq_mul]

private theorem denominatorSlice_norm_le (y : ℝ) (hy : 0 < y) (c : ℕ+) :
    (∫ x in Ioc (0:ℝ) 1, ‖denominatorSlice y c x‖) ≤
      (c:ℕ)*(∫ t, ‖archProfile y c t‖) := by
  have hi := fun a : UnitResidue c => shiftedPeriodization_integrable
    (archProfile_integrable y hy c) ((a.1.val:ℝ)/(c:ℕ))
  have h := GaloisForLFunctions.HTGeometry.integral_norm_tsum_le_tsum_integral_norm
    hi Summable.of_finite
  change (∫ x in Ioc (0:ℝ) 1, ‖denominatorSlice y c x‖) ≤ _ at h
  refine h.trans ?_
  calc
    _ ≤ ∑' _a : UnitResidue c, ∫ t, ‖archProfile y c t‖ := by
      rw [tsum_fintype, tsum_fintype]
      exact Finset.sum_le_sum fun a _ => shiftedPeriodization_norm_le
        (archProfile_integrable y hy c) _
    _ = ((c:ℕ).totient:ℝ)*(∫ t, ‖archProfile y c t‖) := by
      simp [tsum_fintype, unitResidue_card, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le (c:ℕ))
      (integral_nonneg fun _ => norm_nonneg _)


private theorem denominatorSlice_norm_summable (y : ℝ) (hy : 0 < y) :
    Summable (fun c : ℕ+ => ∫ x in Ioc (0:ℝ) 1, ‖denominatorSlice y c x‖) := by
  obtain ⟨C,hC,hb⟩ := archProfile_bound
  have hm := cauchyMajorant_integrable y hy
  have hn := Real.summable_nat_rpow_inv.mpr (by norm_num : 1 < (3:ℝ))
  have hn' : Summable (fun n : ℕ => (n:ℝ)^(-(3:ℝ))) :=
    hn.congr (fun n => by rw [Real.rpow_neg (by positivity)])
  have hc : Summable (fun c : ℕ+ => ((c:ℕ):ℝ)^(-(3:ℝ))) :=
    hn'.comp_injective (fun _ _ h => PNat.coe_injective h)
  have hmaj := hc.mul_left (C*y^2*(∫ t, cauchyMajorant y t))
  refine Summable.of_nonneg_of_le (fun c => integral_nonneg (fun _ => norm_nonneg _)) ?_ hmaj
  intro c
  have hcpos : 0 < ((c:ℕ):ℝ) := by exact_mod_cast c.pos
  have hbint : (∫ t, ‖archProfile y c t‖) ≤
      (C*y^2*((c:ℕ):ℝ)^(-(4:ℝ)))*(∫ t, cauchyMajorant y t) := by
    rw [← integral_const_mul]
    exact integral_mono (archProfile_integrable y hy c).norm
      (hm.const_mul _) (hb y hy c)
  calc
    _ ≤ (c:ℕ)*(∫ t, ‖archProfile y c t‖) := denominatorSlice_norm_le y hy c
    _ ≤ ((c:ℕ):ℝ)*((C*y^2*((c:ℕ):ℝ)^(-(4:ℝ)))*(∫ t, cauchyMajorant y t)) := by
      gcongr
    _ = _ := by
      rw [Real.rpow_neg hcpos.le, Real.rpow_neg hcpos.le]
      norm_num
      field_simp

/-- The complete theta source has its exact primitive-denominator mean, with every totient
multiplicity retained and the infinite sum interchanged by absolute integrability. -/
private theorem source_horizontal_mean (y : ℝ) (hy : 0 < y) :
    (∫ x in Ioc (0:ℝ) 1, source (ofComplex (⟨x,y⟩:ℂ))) =
      heightProfile y + ∑' c : ℕ+,
        ((c:ℕ).totient:ℂ)*(∫ t, archProfile y c t) := by
  have hi := denominatorSlice_integrable y hy
  have hs := denominatorSlice_norm_summable y hy
  have hint := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm hi hs
  have he (x : ℝ) : source (ofComplex (⟨x,y⟩:ℂ)) =
      heightProfile y + ∑' c : ℕ+, denominatorSlice y c x := by
    rw [source_eq_denominator_slices, point_im x y hy]
    congr 1
    apply tsum_congr
    intro c
    congr 1
    simp [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < (⟨x,y⟩:ℂ).im from hy)]
  simp_rw [he]
  rw [integral_add (integrable_const _) hint,
    GaloisForLFunctions.HTGeometry.integral_tsum_eq_tsum_integral_of_summable_integral_norm hi hs]
  simp only [denominatorSlice_mean y hy]
  simp


/-- Exact arithmetic expansion of the fixed positive weight in the native scalar pairing. -/
theorem horizontalWeight_eq_totient (y : ℝ) (hy : 0 < y) :
    (SelbergThetaCommonForcingPairing.horizontalWeight y:ℂ) =
      (positiveProfile y:ℂ) + ∑' c : ℕ+,
        ((c:ℕ).totient:ℂ) * ∫ t, archProfile y c t := by
  rw [SelbergThetaCommonForcingPairing.horizontalWeight,← integral_complex_ofReal,
    integral_Ico_eq_integral_Ioc]
  exact source_horizontal_mean y hy

/-- The inverse-square radial profile of the actual positive theta source. -/
def radialProfile (u v : ℝ) : ℂ :=
  (positiveProfile (1 / (u^2+v^2)):ℂ)

/-- Projection of the actual radial theta field onto one coordinate. -/
def radialProjection (u : ℝ) : ℂ := ∫ v, radialProfile u v

private theorem radialProfile_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 < u → ∀ v : ℝ,
      ‖radialProfile u v‖ ≤ C*cauchyMajorant u v := by
  obtain ⟨C,hC,hb⟩ := heightProfile_power_bound 2
  refine ⟨C,hC,fun u hu v => ?_⟩
  have hq : 0 < u^2+v^2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hu) (sq_nonneg v)
  have h := hb (1/(u^2+v^2)) (by positivity)
  change ‖radialProfile u v‖ ≤ _ at h
  convert h using 1
  unfold cauchyMajorant
  rw [Real.rpow_neg hq.le]
  norm_num

/-- Absolute admission for every positive projection coordinate. -/
theorem radialProfile_integrable (u : ℝ) (hu : 0 < u) :
    Integrable (radialProfile u) := by
  obtain ⟨C,_,hb⟩ := radialProfile_bound
  refine ((cauchyMajorant_integrable u hu).const_mul C).mono' ?_ (ae_of_all _ (hb u hu))
  exact (heightProfile_measurable.comp (by fun_prop)).aestronglyMeasurable

/-- Exact rescaling of a complete primitive-row integral to the fixed radial projection. -/
theorem archProfile_integral_eq_radial (y : ℝ) (hy : 0 < y) (c : ℕ+) :
    (∫ x, archProfile y c x) = (Real.sqrt y / (c:ℕ)) •
      radialProjection ((c:ℕ)*Real.sqrt y) := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hc : 0 < ((c:ℕ):ℝ) := by exact_mod_cast c.pos
  have hs2 := Real.sq_sqrt hy.le
  have hp (x : ℝ) : archProfile y c x =
      radialProfile ((c:ℕ)*Real.sqrt y) (((c:ℕ):ℝ)/Real.sqrt y*x) := by
    unfold archProfile radialProfile heightProfile
    congr 2
    field_simp
    rw [show Real.sqrt y^4 = (Real.sqrt y^2)^2 by ring, hs2]
    ring
  simp_rw [hp]
  rw [Measure.integral_comp_mul_left]
  congr 1
  rw [abs_of_pos (by positivity), inv_div]

/-- The full native horizontal weight in radial arithmetic coordinates. -/
theorem horizontalWeight_eq_radial (y : ℝ) (hy : 0 < y) :
    (SelbergThetaCommonForcingPairing.horizontalWeight y:ℂ) =
      (positiveProfile y:ℂ) + (Real.sqrt y:ℂ) *
        ∑' c : ℕ+, (((c:ℕ).totient:ℂ)/(c:ℕ))*radialProjection ((c:ℕ)*Real.sqrt y) := by
  rw [horizontalWeight_eq_totient y hy, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro c
  rw [archProfile_integral_eq_radial y hy c, Complex.real_smul, Complex.ofReal_div]
  push_cast
  ring

private theorem cauchyMajorant_integral_scale (u : ℝ) (hu : 0 < u) :
    (∫ v, cauchyMajorant u v) = (∫ v, cauchyMajorant 1 v) / u^3 := by
  have hp (v : ℝ) : cauchyMajorant u (u*v) = u⁻¹^4*cauchyMajorant 1 v := by
    unfold cauchyMajorant
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
    norm_num
    field_simp
  have hi := Measure.integral_comp_mul_left (cauchyMajorant u) u
  simp only [hp, integral_const_mul, abs_of_pos (inv_pos.mpr hu), smul_eq_mul] at hi
  field_simp at hi ⊢
  nlinarith [hi]

/-- An unconditional inverse-cube bound for the literal theta projection. -/
theorem radialProjection_inverse_cube_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 < u → ‖radialProjection u‖ ≤ C/u^3 := by
  obtain ⟨C,hC,hb⟩ := radialProfile_bound
  let K := ∫ v, cauchyMajorant 1 v
  have hK : 0 ≤ K := integral_nonneg fun v => Real.rpow_nonneg (by positivity) _
  refine ⟨C*(K+1),by positivity,fun u hu => ?_⟩
  calc
    ‖radialProjection u‖ ≤ ∫ v, ‖radialProfile u v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v, C*cauchyMajorant u v := integral_mono
      (radialProfile_integrable u hu).norm ((cauchyMajorant_integrable u hu).const_mul C)
      (hb u hu)
    _ = C*K/u^3 := by rw [integral_const_mul,cauchyMajorant_integral_scale u hu]; dsimp [K]; ring
    _ ≤ C*(K+1)/u^3 := by gcongr; linarith


private theorem pnat_inv_pow_summable (k : ℕ) (hk : 1 < k) :
    Summable (fun n : ℕ+ => (((n:ℕ):ℝ)^k)⁻¹) := by
  have h := Real.summable_nat_rpow_inv.mpr (show 1 < (k:ℝ) by exact_mod_cast hk)
  have h' : Summable (fun n : ℕ => ((n:ℝ)^k)⁻¹) := by
    simpa only [Real.rpow_natCast] using h
  exact h'.comp_injective (fun _ _ h => PNat.coe_injective h)

/-- Every full positive lattice sum of the actual theta projection converges absolutely. -/
theorem radialProjection_lattice_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ+ => radialProjection ((n:ℕ)*a)) := by
  obtain ⟨C,hC,hb⟩ := radialProjection_inverse_cube_bound
  refine Summable.of_norm_bounded ((pnat_inv_pow_summable 3 (by omega)).mul_left (C/a^3)) ?_
  intro n
  have hn : 0 < ((n:ℕ):ℝ) := by exact_mod_cast n.pos
  convert hb ((n:ℕ)*a) (by positivity) using 1
  field_simp

/-- The signed divisor-pair source, before either infinite sum is taken. -/
def moebiusPair (a : ℝ) (p : ℕ+ × ℕ+) : ℂ :=
  ((ArithmeticFunction.moebius (p.1:ℕ):ℂ)/(p.1:ℕ)) *
    radialProjection (((p.1:ℕ):ℝ)*(p.2:ℕ)*a)

private theorem moebius_norm_le_one (n : ℕ) :
    ‖(ArithmeticFunction.moebius n:ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

/-- Absolute convergence of the complete two-index signed source. -/
theorem moebiusPair_summable (a : ℝ) (ha : 0 < a) : Summable (moebiusPair a) := by
  obtain ⟨C,hC,hb⟩ := radialProjection_inverse_cube_bound
  have h4 := pnat_inv_pow_summable 4 (by omega)
  have h3 := pnat_inv_pow_summable 3 (by omega)
  have hp : Summable (fun p : ℕ+ × ℕ+ =>
      ((((p.1:ℕ):ℝ)^4)⁻¹)*((((p.2:ℕ):ℝ)^3)⁻¹)) :=
    h4.mul_of_nonneg h3 (fun _ => by positivity) (fun _ => by positivity)
  refine Summable.of_norm_bounded (hp.mul_left (C/a^3)) ?_
  intro p
  have hd : 0 < ((p.1:ℕ):ℝ) := by exact_mod_cast p.1.pos
  have hk : 0 < ((p.2:ℕ):ℝ) := by exact_mod_cast p.2.pos
  calc
    ‖moebiusPair a p‖ =
        ‖(ArithmeticFunction.moebius (p.1:ℕ):ℂ)‖ / (p.1:ℕ) *
          ‖radialProjection (((p.1:ℕ):ℝ)*(p.2:ℕ)*a)‖ := by
      simp [moebiusPair]
    _ ≤ (1/((p.1:ℕ):ℝ)) * (C/((((p.1:ℕ):ℝ)*(p.2:ℕ)*a)^3)) := by
      gcongr
      · exact moebius_norm_le_one _
      · exact hb _ (by positivity)
    _ = _ := by field_simp

private theorem moebius_divisor_coefficient (n : ℕ+) :
    (∑ x ∈ (n:ℕ).divisorsAntidiagonal,
      ((ArithmeticFunction.moebius x.1:ℂ)/(x.1:ℂ))) =
        ((n:ℕ).totient:ℂ)/(n:ℕ) := by
  rw [Nat.sum_divisorsAntidiagonal (f := fun x _ =>
    ((ArithmeticFunction.moebius x:ℂ)/(x:ℂ)))]
  have h := Sieve.sum_moebius_div_divisors_eq_totient_div n.pos
  have hc := congrArg (fun x : ℝ => (x:ℂ)) h
  push_cast at hc
  exact hc

private theorem moebiusPair_divisor_sum (a : ℝ) (n : ℕ+) :
    (∑' x : (n:ℕ).divisorsAntidiagonal,
      moebiusPair a (divisorsAntidiagonalFactors n x)) =
        (((n:ℕ).totient:ℂ)/(n:ℕ))*radialProjection ((n:ℕ)*a) := by
  have hp (x : (n:ℕ).divisorsAntidiagonal) :
      moebiusPair a (divisorsAntidiagonalFactors n x) =
        ((ArithmeticFunction.moebius x.1.1:ℂ)/(x.1.1:ℂ)) *
          radialProjection ((n:ℕ)*a) := by
    change ((ArithmeticFunction.moebius x.1.1:ℂ)/(x.1.1:ℂ)) *
      radialProjection ((x.1.1:ℝ)*x.1.2*a) = _
    congr 2
    rw [← Nat.cast_mul, (Nat.mem_divisorsAntidiagonal.mp x.2).1]
  simp_rw [hp]
  rw [tsum_fintype]
  simp only [Finset.univ_eq_attach]
  rw [(n:ℕ).divisorsAntidiagonal.sum_attach (fun x : ℕ × ℕ =>
    ((ArithmeticFunction.moebius x.1:ℂ)/(x.1:ℂ))*radialProjection ((n:ℕ)*a)),
    ← Finset.sum_mul, moebius_divisor_coefficient]

/-- Möbius inversion for the actual radial theta weight, with full sums and absolute admission. -/
theorem totient_radial_eq_moebius (a : ℝ) (ha : 0 < a) :
    (∑' n : ℕ+, (((n:ℕ).totient:ℂ)/(n:ℕ))*radialProjection ((n:ℕ)*a)) =
      ∑' d : ℕ+, ((ArithmeticFunction.moebius (d:ℕ):ℂ)/(d:ℕ)) *
        ∑' k : ℕ+, radialProjection ((k:ℕ)*((d:ℕ)*a)) := by
  have hs := moebiusPair_summable a ha
  have hsig : Summable (fun p : (Σ n : ℕ+, (n:ℕ).divisorsAntidiagonal) =>
      moebiusPair a (sigmaAntidiagonalEquivProd p)) :=
    hs.comp_injective sigmaAntidiagonalEquivProd.injective
  have he := sigmaAntidiagonalEquivProd.tsum_eq (moebiusPair a)
  rw [hsig.tsum_sigma] at he
  have he' : (∑' n : ℕ+, (((n:ℕ).totient:ℂ)/(n:ℕ))*radialProjection ((n:ℕ)*a)) =
      ∑' p : ℕ+ × ℕ+, moebiusPair a p := by
    convert he using 1
    apply tsum_congr
    intro n
    exact (moebiusPair_divisor_sum a n).symm
  rw [he',hs.tsum_prod]
  apply tsum_congr
  intro d
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  unfold moebiusPair
  congr 2
  push_cast
  ring

/-- Exact signed arithmetic formula for the horizontal weight entering the native Gram. -/
theorem horizontalWeight_eq_moebius (y : ℝ) (hy : 0 < y) :
    (SelbergThetaCommonForcingPairing.horizontalWeight y:ℂ) =
      (positiveProfile y:ℂ) + (Real.sqrt y:ℂ) *
        ∑' d : ℕ+, ((ArithmeticFunction.moebius (d:ℕ):ℂ)/(d:ℕ)) *
          ∑' k : ℕ+, radialProjection ((k:ℕ)*((d:ℕ)*Real.sqrt y)) := by
  rw [horizontalWeight_eq_radial y hy,
    totient_radial_eq_moebius (Real.sqrt y) (Real.sqrt_pos.mpr hy)]


private theorem radialProfile_uniform_majorant :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 < u → ∀ v : ℝ,
      ‖radialProfile u v‖ ≤ C*cauchyMajorant 1 v := by
  obtain ⟨C0,hC0,h0⟩ := heightProfile_power_bound 0
  obtain ⟨C2,hC2,h2⟩ := heightProfile_power_bound 2
  refine ⟨4*(C0+C2),by positivity,fun u hu v => ?_⟩
  have hq : 0 < u^2+v^2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hu) (sq_nonneg v)
  have hden : 0 < (1+v^2)^2 := by positivity
  have hmaj : 4*(C0+C2)*cauchyMajorant 1 v = 4*(C0+C2)/(1+v^2)^2 := by
    unfold cauchyMajorant
    rw [Real.rpow_neg (by positivity)]
    norm_num
    rfl
  rw [hmaj]
  by_cases hv : v^2 ≤ 1
  · have hh : ‖radialProfile u v‖ ≤ C0 := by
      have h := h0 (1/(u^2+v^2)) (by positivity)
      change ‖radialProfile u v‖ ≤ C0*(1/(u^2+v^2))^(0:ℝ) at h
      simpa only [Real.rpow_zero,mul_one] using h
    have hd : (1+v^2)^2 ≤ 4 := by
      calc (1+v^2)^2 ≤ (2:ℝ)^2 := by gcongr; linarith
           _ = 4 := by norm_num
    refine hh.trans ((le_div_iff₀ hden).mpr ?_)
    nlinarith [mul_le_mul_of_nonneg_left hd hC0.le]
  · have hh : ‖radialProfile u v‖ ≤ C2/(u^2+v^2)^2 := by
      have h := h2 (1/(u^2+v^2)) (by positivity)
      simpa [Real.rpow_two,radialProfile,heightProfile,div_pow,div_eq_mul_inv] using h
    have hd : (1+v^2)^2 ≤ 4*(u^2+v^2)^2 := by
      calc (1+v^2)^2 ≤ (2*(u^2+v^2))^2 := by gcongr; nlinarith [sq_nonneg u]
           _ = _ := by ring
    refine hh.trans ((div_le_div_iff₀ (pow_pos hq 2) hden).mpr ?_)
    nlinarith [mul_le_mul_of_nonneg_left hd hC2.le]

/-- A uniform bound, including arbitrarily small positive projection coordinates. -/
theorem radialProjection_uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 < u → ‖radialProjection u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := radialProfile_uniform_majorant
  let K := ∫ v, cauchyMajorant 1 v
  have hK : 0 ≤ K := integral_nonneg fun _ => Real.rpow_nonneg (by positivity) _
  refine ⟨C*(K+1),by positivity,fun u hu => ?_⟩
  calc
    ‖radialProjection u‖ ≤ ∫ v, ‖radialProfile u v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v, C*cauchyMajorant 1 v := integral_mono
      (radialProfile_integrable u hu).norm ((cauchyMajorant_integrable 1 (by norm_num)).const_mul C)
      (hb u hu)
    _ = C*K := integral_const_mul _ _
    _ ≤ C*(K+1) := by nlinarith

/-- Measurability of the full radial projection. -/
theorem radialProjection_stronglyMeasurable : StronglyMeasurable radialProjection := by
  have hm : StronglyMeasurable (fun p : ℝ × ℝ => radialProfile p.1 p.2) :=
    (heightProfile_measurable.comp (by fun_prop)).stronglyMeasurable
  exact hm.integral_prod_right'

/-- The actual radial projection has finite absolute mass on the positive half-line. -/
theorem radialProjection_integrableOn : IntegrableOn radialProjection (Ioi 0) := by
  obtain ⟨C0,_,h0⟩ := radialProjection_uniform_bound
  obtain ⟨C3,_,h3⟩ := radialProjection_inverse_cube_bound
  have hm : AEStronglyMeasurable radialProjection volume :=
    radialProjection_stronglyMeasurable.aestronglyMeasurable
  have hi : IntegrableOn radialProjection (Ioc 0 1) := by
    have hc : IntegrableOn (fun _ : ℝ => C0) (Ioc 0 1) := integrable_const C0
    exact hc.mono' hm.restrict ((ae_restrict_mem measurableSet_Ioc).mono (fun u hu => h0 u hu.1))
  have ht : IntegrableOn radialProjection (Ioi 1) := by
    have hc := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3:ℝ)< -1)
      (by norm_num : (0:ℝ)<1)).const_mul C3
    refine hc.mono' hm.restrict ((ae_restrict_mem measurableSet_Ioi).mono (fun u hu => ?_))
    have hu0 : 0 < u := lt_trans (by norm_num : (0:ℝ)<1) hu
    convert h3 u hu0 using 1
    rw [Real.rpow_neg hu0.le]
    norm_num [div_eq_mul_inv]
  have he : Ioi (0:ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext u
    simp only [mem_Ioi,mem_union,mem_Ioc]
    constructor
    · intro hu
      by_cases h1 : u ≤ 1
      · exact Or.inl ⟨hu,h1⟩
      · exact Or.inr (lt_of_not_ge h1)
    · rintro (⟨hu,_⟩ | hu)
      · exact hu
      · linarith
  rw [he]
  exact hi.union ht

/-- The source-defined main-term mass of the radial quadrature. -/
def radialMass : ℂ := ∫ u in Ioi (0:ℝ), radialProjection u

/-- The exact full-lattice quadrature error at positive mesh size. -/
def quadratureError (t : ℝ) : ℂ :=
  (t:ℂ)*(∑' k : ℕ+, radialProjection ((k:ℕ)*t))-radialMass

/-- The absolutely convergent Möbius density coefficient. -/
def moebiusDensity : ℂ := ∑' d : ℕ+, (ArithmeticFunction.moebius (d:ℕ):ℂ)/(d:ℕ)^2

private theorem moebius_density_summable :
    Summable (fun d : ℕ+ => (ArithmeticFunction.moebius (d:ℕ):ℂ)/(d:ℕ)^2) := by
  refine Summable.of_norm_bounded (pnat_inv_pow_summable 2 (by omega)) (fun d => ?_)
  simpa only [norm_div,norm_pow,Complex.norm_natCast,one_div] using
    div_le_div_of_nonneg_right (moebius_norm_le_one (d:ℕ)) (by positivity : 0 ≤ ((d:ℕ):ℝ)^2)

private theorem moebius_lattice_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun d : ℕ+ => ((ArithmeticFunction.moebius (d:ℕ):ℂ)/(d:ℕ)) *
      ∑' k : ℕ+, radialProjection ((k:ℕ)*((d:ℕ)*a))) := by
  have hs := (moebiusPair_summable a ha).prod
  refine hs.congr (fun d => ?_)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  unfold moebiusPair
  congr 2
  push_cast
  ring

/-- Absolute convergence of the signed, centered full-lattice remainder. -/
theorem quadratureError_moebius_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun d : ℕ+ => ((ArithmeticFunction.moebius (d:ℕ):ℂ)/(d:ℕ)^2) *
      quadratureError ((d:ℕ)*a)) := by
  have h := ((moebius_lattice_summable a ha).mul_left (a:ℂ)).sub
    (moebius_density_summable.mul_right radialMass)
  refine h.congr (fun d => ?_)
  have hd : ((d:ℕ):ℂ) ≠ 0 := by exact_mod_cast d.ne_zero
  unfold quadratureError
  push_cast
  field_simp
  simp only [mul_assoc,mul_comm]

/-- Exact main-term subtraction, expressed as a convergent signed quadrature remainder.
Identifying this arithmetic main term with the native mean requires the separate volume/mass law. -/
theorem horizontalWeight_sub_main_eq_quadrature (y : ℝ) (hy : 0 < y) :
    (SelbergThetaCommonForcingPairing.horizontalWeight y:ℂ)-moebiusDensity*radialMass =
      (positiveProfile y:ℂ) + ∑' d : ℕ+,
        ((ArithmeticFunction.moebius (d:ℕ):ℂ)/(d:ℕ)^2) * quadratureError ((d:ℕ)*Real.sqrt y) := by
  have ha := Real.sqrt_pos.mpr hy
  have hp (d : ℕ+) : ((ArithmeticFunction.moebius (d:ℕ):ℂ)/(d:ℕ)^2) *
      quadratureError ((d:ℕ)*Real.sqrt y) =
      (Real.sqrt y:ℂ)*(((ArithmeticFunction.moebius (d:ℕ):ℂ)/(d:ℕ)) *
        ∑' k : ℕ+, radialProjection ((k:ℕ)*((d:ℕ)*Real.sqrt y))) -
      ((ArithmeticFunction.moebius (d:ℕ):ℂ)/(d:ℕ)^2)*radialMass := by
    have hd : ((d:ℕ):ℂ) ≠ 0 := by exact_mod_cast d.ne_zero
    unfold quadratureError
    push_cast
    field_simp
    simp only [mul_assoc,mul_left_comm,mul_comm]
  simp_rw [hp]
  rw [(((moebius_lattice_summable (Real.sqrt y) ha).mul_left (Real.sqrt y:ℂ)).tsum_sub
    (moebius_density_summable.mul_right radialMass)),tsum_mul_left,tsum_mul_right,
    horizontalWeight_eq_moebius y hy,moebiusDensity]
  ring


end
end RHTower.SelbergThetaHorizontalArithmetic
