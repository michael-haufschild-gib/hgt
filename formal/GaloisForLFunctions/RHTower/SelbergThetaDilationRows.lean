import GaloisForLFunctions.RHTower.SelbergThetaDilationTransform
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualFourierCoefficient
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinCoprimeRowSum
import GaloisForLFunctions.RHTower.SelbergThetaNativeSource
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMStripMeanAdmission
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMHalfRowIntegralInterchange
/-!
# Complete theta dilation rows and native pairing

The literal dyadic theta profile has arbitrary power decay in the positive-height chart.
Its complete modular periodization belongs to the native Hilbert space, and its native pairing
unfolds absolutely. Reindexing every primitive row by positive denominator, reduced residue,
and integer translate gives the exact totient-weighted horizontal mean and native height integral.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
namespace RHTower.SelbergThetaDilationRows
open D4BMModularCore D4BMJointSource D4BMGlobalAngularResponse
open SelbergThetaDilationTransform
noncomputable section

private theorem base_norm (rho : ℂ) (t : ℝ) :
    ‖baseProfile rho t‖ = (1/2:ℝ) *
      SelbergThetaNativeSource.positiveProfile (Real.exp t) *
        Real.exp ((rho.re-1/2)*t/2) := by
  unfold baseProfile SelbergThetaNativeSource.positiveProfile
  rw [Real.log_exp]
  simp only [norm_mul, norm_div, norm_one, norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (thetaCuspFullSource_pos_all _), Complex.norm_exp]
  have he : ((rho+1/2)*((t/2:ℝ):ℂ)).re = (rho.re+1/2)*t/2 := by
    simp [Complex.mul_re]
    ring
  rw [he]
  rw [show (1/2:ℝ)*(Real.exp (t/2)*thetaCuspFullSource (t/2))*
      Real.exp ((rho.re-1/2)*t/2) =
      (1/2:ℝ)*thetaCuspFullSource (t/2)*
        (Real.exp (t/2)*Real.exp ((rho.re-1/2)*t/2)) by ring]
  rw [← Real.exp_add]
  congr 2
  ring

private theorem base_exp_bound (rho : ℂ) (a : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖baseProfile rho t‖ ≤ C*Real.exp (a*t) := by
  obtain ⟨C,hC,hb⟩ := SelbergThetaNativeSource.positiveProfile_power_bound
    (a-(rho.re-1/2)/2)
  refine ⟨C/2, by positivity, fun t => ?_⟩
  have hb' := hb (Real.exp t) (Real.exp_pos t)
  rw [base_norm]
  calc
    _ ≤ (1/2:ℝ)*(C*(Real.exp t)^(a-(rho.re-1/2)/2))*
        Real.exp ((rho.re-1/2)*t/2) := by gcongr
    _ = C/2*Real.exp (a*t) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]
      have he : t*(a-(rho.re-1/2)/2)+(rho.re-1/2)*t/2 = a*t := by ring
      rw [show (1/2:ℝ)*(C*Real.exp (t*(a-(rho.re-1/2)/2)))*
          Real.exp ((rho.re-1/2)*t/2) =
          C/2*(Real.exp (t*(a-(rho.re-1/2)/2))*Real.exp ((rho.re-1/2)*t/2)) by ring,
        ← Real.exp_add, he]

/-- Every real exponential dominates the literal dyadic theta profile with a finite constant. -/
theorem profile_exp_bound (rho : ℂ) (a : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖profile rho t‖ ≤ C*Real.exp (a*t) := by
  obtain ⟨C,hC,hb⟩ := base_exp_bound rho a
  have hd := dyadicWeight_pos
  refine ⟨(2+dyadicWeight*Real.exp (a*Real.log 2))*C, by positivity, fun t => ?_⟩
  calc
    _ ≤ 2*‖baseProfile rho t‖+dyadicWeight*‖baseProfile rho (t+Real.log 2)‖ := by
      simpa only [profile, norm_mul, norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos dyadicWeight_pos] using norm_sub_le
          (2*baseProfile rho t) ((dyadicWeight:ℂ)*baseProfile rho (t+Real.log 2))
    _ ≤ 2*(C*Real.exp (a*t))+dyadicWeight*(C*Real.exp (a*(t+Real.log 2))) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (hb t) (by norm_num))
        (mul_le_mul_of_nonneg_left (hb (t+Real.log 2)) hd.le)
    _ = _ := by rw [mul_add, Real.exp_add]; ring

/-- The original logarithmic dilation family expressed in the positive-height chart. -/
def heightProfile (rho : ℂ) (L y : ℝ) : ℂ :=
  (Real.exp (Real.log y/2):ℂ)*profile rho (Real.log y+L)

/-- The literal dilation seed retains arbitrary decay powers at both cusp ends. -/
theorem heightProfile_power_bound (rho : ℂ) (L r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → ‖heightProfile rho L y‖ ≤ C*y^r := by
  obtain ⟨C,hC,hb⟩ := profile_exp_bound rho (r-1/2)
  refine ⟨C*Real.exp ((r-1/2)*L), by positivity, fun y hy => ?_⟩
  rw [heightProfile, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (Real.log y/2)*(C*Real.exp ((r-1/2)*(Real.log y+L))) := by gcongr; exact hb _
    _ = C*Real.exp ((r-1/2)*L)*y^r := by
      rw [Real.rpow_def_of_pos hy]
      have he : Real.log y/2+(r-1/2)*(Real.log y+L) = (r-1/2)*L+Real.log y*r := by ring
      rw [show Real.exp (Real.log y/2)*(C*Real.exp ((r-1/2)*(Real.log y+L))) =
          C*(Real.exp (Real.log y/2)*Real.exp ((r-1/2)*(Real.log y+L))) by ring,
        ← Real.exp_add, he, Real.exp_add]
      ring

/-- The literal height profile is measurable on the real chart. -/
theorem heightProfile_measurable (rho : ℂ) (L : ℝ) : Measurable (heightProfile rho L) := by
  have hg : Continuous (profile rho) := by
    have ht := contDiff_thetaCuspFullSource.continuous
    unfold profile baseProfile
    fun_prop
  unfold heightProfile
  fun_prop

private theorem rows_summable (rho : ℂ) (L : ℝ) (z : UpperHalfPlane) :
    Summable (fun v : gammaSetHalf => heightProfile rho L (gammaSetMatrix v.1 • z).im) := by
  obtain ⟨C,_,hb⟩ := heightProfile_power_bound rho L 2
  apply Summable.of_norm_bounded ((positiveCuspRows_summable 2 (by norm_num) z).mul_left C)
  intro v
  exact hb _ (gammaSetMatrix v.1 • z).im_pos

/-- Complete modular periodization of the literal theta dilation seed. -/
def source (rho : ℂ) (L : ℝ) (z : UpperHalfPlane) : ℂ :=
  periodize (cuspHeightSeed (heightProfile rho L)) z

/-- Every primitive projective row is retained in the original source. -/
theorem source_eq_rows (rho : ℂ) (L : ℝ) (z : UpperHalfPlane) :
    source rho L z = ∑' v : gammaSetHalf, heightProfile rho L (gammaSetMatrix v.1 • z).im :=
  periodize_cuspHeightSeed_eq_rows_of_rows_summable _ z (rows_summable rho L z)

/-- The complete modular dilation source is measurable. -/
theorem source_measurable (rho : ℂ) (L : ℝ) : Measurable (source rho L) :=
  periodize_measurable _ (cuspHeightSeed_measurable _ (heightProfile_measurable rho L))

private theorem source_bound_rows (rho : ℂ) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, ‖source rho L z‖ ≤ C*positiveCuspRows 2 z := by
  obtain ⟨C,hC,hb⟩ := heightProfile_power_bound rho L 2
  refine ⟨C,hC,fun z => ?_⟩
  rw [source_eq_rows]
  calc
    _ ≤ ∑' v : gammaSetHalf, ‖heightProfile rho L (gammaSetMatrix v.1 • z).im‖ :=
      norm_tsum_le_tsum_norm (rows_summable rho L z).norm
    _ ≤ ∑' v : gammaSetHalf, C*(gammaSetMatrix v.1 • z).im^(2:ℝ) :=
      (rows_summable rho L z).norm.tsum_le_tsum
        (fun v => hb _ (gammaSetMatrix v.1 • z).im_pos)
        ((positiveCuspRows_summable 2 (by norm_num) z).mul_left C)
    _ = _ := tsum_mul_left

/-- Every real power-weighted absolute moment of the height profile is finite. -/
theorem weighted_profile_integrable (rho : ℂ) (L r : ℝ) :
    IntegrableOn (fun y : ℝ => ‖heightProfile rho L y‖*y^r) (Ioi (0:ℝ)) := by
  have hm := heightProfile_measurable rho L
  have hmeas : Measurable (fun y : ℝ => ‖heightProfile rho L y‖*y^r) := by fun_prop
  obtain ⟨C,_,hC⟩ := heightProfile_power_bound rho L (-r)
  obtain ⟨D,_,hD⟩ := heightProfile_power_bound rho L (-2-r)
  have hsmall : IntegrableOn (fun y : ℝ => ‖heightProfile rho L y‖*y^r) (Ioc (0:ℝ) 1) := by
    apply (integrable_const C).mono' hmeas.aestronglyMeasurable
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hy.1.le _))]
    calc
      _ ≤ (C*y^(-r))*y^r := mul_le_mul_of_nonneg_right (hC y hy.1) (Real.rpow_nonneg hy.1.le _)
      _ = C := by rw [mul_assoc, ← Real.rpow_add hy.1]; simp
  have hlarge : IntegrableOn (fun y : ℝ => ‖heightProfile rho L y‖*y^r) (Ioi (1:ℝ)) := by
    apply ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1)
      (by norm_num : (0:ℝ)<1)).const_mul D).mono' hmeas.aestronglyMeasurable
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro y hy
    have hy0 : 0 < y := lt_trans zero_lt_one hy
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hy0.le _))]
    calc
      _ ≤ (D*y^(-2-r))*y^r := mul_le_mul_of_nonneg_right (hD y hy0) (Real.rpow_nonneg hy0.le _)
      _ = D*y^(-2:ℝ) := by rw [mul_assoc, ← Real.rpow_add hy0]; congr 2; ring
  apply (hsmall.union hlarge).mono_set
  intro y hy
  rcases le_or_gt y 1 with h | h
  · exact Or.inl ⟨hy,h⟩
  · exact Or.inr h

private def seedProduct (rho : ℂ) (L M : ℝ) (z : UpperHalfPlane) : ℂ :=
  conj (heightProfile rho L z.im)*source rho M z

private theorem seedProduct_measurable (rho : ℂ) (L M : ℝ) :
    Measurable (seedProduct rho L M) := by
  have hm := heightProfile_measurable rho L
  have hn := source_measurable rho M
  unfold seedProduct
  fun_prop

private theorem point_im (x y : ℝ) (hy : 0 < y) :
    (ofComplex (⟨x,y⟩:ℂ)).im = y := by
  rw [ofComplex_apply_of_im_pos hy]
  rfl

private theorem seedProduct_strip_integrable (rho : ℂ) (L M : ℝ) :
    IntegrableOn (seedProduct rho L M) modularStrip volume := by
  obtain ⟨C,hC,hb⟩ := source_bound_rows rho M
  have hm := seedProduct_measurable rho L M
  have hp := heightProfile_measurable rho L
  have hx : Measurable (fun p : ℝ × ℝ => seedProduct rho L M (ofComplex (⟨p.2,p.1⟩:ℂ))) :=
    hm.comp cuspStripPoint_measurable
  have hline (y : ℝ) (hy : 0 < y) :
      IntegrableOn (fun x : ℝ => seedProduct rho L M (ofComplex (⟨x,y⟩:ℂ))) (Ico (0:ℝ) 1) := by
    apply ((positiveCuspRows_horizontal_integrable 2 (by norm_num) hy).const_mul
      (‖heightProfile rho L y‖*C)).mono' (hx.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    apply ae_restrict_of_forall_mem measurableSet_Ico
    intro x _
    change ‖conj (heightProfile rho L (ofComplex (⟨x,y⟩:ℂ)).im)*
      source rho M (ofComplex (⟨x,y⟩:ℂ))‖ ≤ _
    rw [norm_mul, norm_conj, point_im x y hy]
    calc
      _ ≤ ‖heightProfile rho L y‖*(C*positiveCuspRows 2 (ofComplex (⟨x,y⟩:ℂ))) :=
        mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)
      _ = _ := by ring
  apply modularStrip_integrable_of_norm_mean _ hm hline
  have hi := ((weighted_profile_integrable rho L 0).add
    ((weighted_profile_integrable rho L (-3)).const_mul (cuspReflectionNorm 2))).const_mul C
  apply hi.mono' ?_ ?_
  · exact ((measurable_id.pow_const 2).inv.mul (cuspHorizontalNormMean_measurable _ hm)).aestronglyMeasurable
  · apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro y hy
    have hy0 : 0 < y := hy
    have hmean : (∫ x in Ico (0:ℝ) 1, ‖seedProduct rho L M (ofComplex (⟨x,y⟩:ℂ))‖) ≤
        (‖heightProfile rho L y‖*C)*(y^2+cuspReflectionNorm 2*y^(-1:ℝ)) := by
      calc
        _ ≤ ∫ x in Ico (0:ℝ) 1,
            (‖heightProfile rho L y‖*C)*positiveCuspRows 2 (ofComplex (⟨x,y⟩:ℂ)) := by
          apply integral_mono (hline y hy).norm
            ((positiveCuspRows_horizontal_integrable 2 (by norm_num) hy).const_mul _)
          intro x
          change ‖conj (heightProfile rho L (ofComplex (⟨x,y⟩:ℂ)).im)*
            source rho M (ofComplex (⟨x,y⟩:ℂ))‖ ≤ _
          rw [norm_mul, norm_conj, point_im x y hy]
          nlinarith [hb (ofComplex (⟨x,y⟩:ℂ)), norm_nonneg (heightProfile rho L y)]
        _ ≤ _ := by
          rw [integral_const_mul]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa only [Real.rpow_two, show (1-2:ℝ)=(-1:ℝ) by norm_num] using
            positiveCuspRows_mean_le 2 (by norm_num) hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ (y^2)⁻¹*((‖heightProfile rho L y‖*C)*(y^2+cuspReflectionNorm 2*y^(-1:ℝ))) :=
        mul_le_mul_of_nonneg_left hmean (by positivity)
      _ = _ := by
        simp only [Pi.add_apply, Real.rpow_zero, mul_one, Real.rpow_neg_one]
        rw [show y^(-3:ℝ)=(y^3)⁻¹ by rw [Real.rpow_neg hy0.le]; norm_num]
        field_simp [hy0.ne']

private theorem seedProduct_periodic (rho : ℂ) (L M : ℝ) (n : ℤ) (z : UpperHalfPlane) :
    seedProduct rho L M (ModularGroup.T^n • z) = seedProduct rho L M z := by
  unfold seedProduct
  rw [im_T_zpow_smul]
  congr 1
  exact periodize_invariant _ (QuotientGroup.mk (ModularGroup.T^n)) z

private theorem seedProduct_rows (rho : ℂ) (L M : ℝ) (z : UpperHalfPlane) :
    (∑' v : gammaSetHalf, seedProduct rho L M (gammaSetMatrix v.1 • z)) =
      conj (source rho L z)*source rho M z := by
  have he (v : gammaSetHalf) : source rho M (gammaSetMatrix v.1 • z) = source rho M z :=
    periodize_invariant _ (QuotientGroup.mk (gammaSetMatrix v.1)) z
  unfold seedProduct
  simp_rw [he]
  rw [tsum_mul_right, ← Complex.conj_tsum, ← source_eq_rows]

/-- Absolute admission of the full source product in the native modular measure. -/
theorem source_pairing_integrable (rho : ℂ) (L M : ℝ) :
    Integrable (fun z => conj (source rho L z)*source rho M z) angularMeasure := by
  have hi := seedProduct_strip_integrable rho L M
  have hp := seedProduct_periodic rho L M
  have hr (v : gammaSetHalf) : IntegrableOn
      (fun z : UpperHalfPlane => seedProduct rho L M (gammaSetMatrix v.1 • z)) fd volume :=
    (integrableOn_smul_set_iff _ _ _).mp (integrableOn_smul_fd_of_periodic hp hi _)
  have ha := integrable_tsum_of_summable_integral_norm hr
    (modularStrip_halfRow_norm_integrals_summable _ hp hi)
  simpa only [seedProduct_rows] using! ha

private theorem source_pairing_unfold (rho : ℂ) (L M : ℝ) :
    (∫ z, conj (source rho L z)*source rho M z ∂angularMeasure) =
      ∫ z in modularStrip, seedProduct rho L M z := by
  have he := modularStrip_integral_halfRow_sum _ (seedProduct_periodic rho L M)
    (seedProduct_strip_integrable rho L M)
  simpa only [seedProduct_rows] using! he

/-- Every member of the literal theta dilation family belongs to the original native Hilbert space. -/
theorem source_memLp (rho : ℂ) (L : ℝ) : MemLp (source rho L) 2 angularMeasure := by
  apply (memLp_two_iff_integrable_sq_norm (source_measurable rho L).aestronglyMeasurable).2
  simpa only [norm_mul, norm_conj, pow_two] using! (source_pairing_integrable rho L L).norm

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

private theorem source_positive_rows (rho : ℂ) (L : ℝ) (z : UpperHalfPlane) :
    source rho L z = heightProfile rho L z.im +
      ∑' p : D4BMPositivePrimitivePair,
        heightProfile rho L (gammaSetMatrix (primitiveRowEquiv p.1) • z).im := by
  have hs := (rows_summable rho L z).comp_injective halfRowEquiv.injective
  have ha := hs.comp_injective Sum.inl_injective
  have hb := hs.comp_injective Sum.inr_injective
  rw [source_eq_rows, ← halfRowEquiv.tsum_eq
    (fun v : gammaSetHalf => heightProfile rho L (gammaSetMatrix v.1 • z).im)]
  have he := ha.tsum_sum hb
  simp only [Function.comp_apply] at he
  rw [he]
  change (∑' u : Unit, heightProfile rho L (gammaSetMatrix cuspIdentityRow.1 • z).im) + _ = _
  simp only [tsum_fintype, Finset.univ_unique, Finset.sum_singleton, cuspIdentityRow_height]
  rfl

private theorem source_denominator_rows (rho : ℂ) (L : ℝ) (z : UpperHalfPlane) :
    source rho L z = heightProfile rho L z.im + ∑' c : ℕ+,
      ∑' d : D4BMCoprimeInteger (d4BMPositiveModulusOfPNat c),
        heightProfile rho L (gammaSetMatrix (primitiveRowEquiv
          (d4BMCoprimeIntegerToPrimitivePair (d4BMPositiveModulusOfPNat c) d)) • z).im := by
  have hs := (rows_summable rho L z).comp_injective positiveHalfRow_injective
  have hi := hs.comp_injective d4BMPositiveCuspIndexEquivPrimitivePair.injective
  rw [source_positive_rows, ← d4BMPositiveCuspIndexEquivPrimitivePair.tsum_eq
    (fun p : D4BMPositivePrimitivePair =>
      heightProfile rho L (gammaSetMatrix (primitiveRowEquiv p.1) • z).im)]
  have he := hi.tsum_sigma
  simp only [Function.comp_apply, positiveHalfRow] at he
  rw [he]
  rfl

private abbrev UnitResidue (c : ℕ+) :=
  {a : ZMod (d4BMPositiveModulusOfPNat c).value // IsUnit a}

/-- The complete real-translation profile for one positive denominator. -/
def archProfile (rho : ℂ) (L y : ℝ) (c : ℕ+) (x : ℝ) : ℂ :=
  heightProfile rho L (y / (((c:ℕ):ℝ)^2*(y^2+x^2)))

/-- The sum of every reduced-residue periodization for one positive denominator. -/
def denominatorSlice (rho : ℂ) (L y : ℝ) (c : ℕ+) (x : ℝ) : ℂ :=
  ∑' a : UnitResidue c, l1Periodization (archProfile rho L y c) (x+(a.1.val:ℝ)/(c:ℕ))

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

private theorem denominator_rows_eq_slice (rho : ℂ) (L : ℝ) (z : UpperHalfPlane) (c : ℕ+) :
    (∑' d : D4BMCoprimeInteger (d4BMPositiveModulusOfPNat c),
      heightProfile rho L (gammaSetMatrix (primitiveRowEquiv
        (d4BMCoprimeIntegerToPrimitivePair (d4BMPositiveModulusOfPNat c) d)) • z).im) =
      denominatorSlice rho L z.im c z.re := by
  have hs := (rows_summable rho L z).comp_injective positiveHalfRow_injective
  have hi := hs.comp_injective d4BMPositiveCuspIndexEquivPrimitivePair.injective
  have hinj : Function.Injective
      (fun d : D4BMCoprimeInteger (d4BMPositiveModulusOfPNat c) => (⟨c,d⟩:D4BMPositiveCuspIndex)) := by
    intro d e h
    simpa using h
  have hq := hi.comp_injective hinj
  have hp := hq.comp_injective
    (d4BMUnitResidueTranslateEquivCoprimeInteger (d4BMPositiveModulusOfPNat c)).injective
  have hp' : Summable (fun p : D4BMUnitResidueTranslateIndex (d4BMPositiveModulusOfPNat c) =>
      heightProfile rho L (gammaSetMatrix (primitiveRowEquiv
        (d4BMUnitResidueTranslateToPrimitivePair (d4BMPositiveModulusOfPNat c) p)) • z).im) := hp
  rw [← (d4BMUnitResidueTranslateEquivCoprimeInteger (d4BMPositiveModulusOfPNat c)).tsum_eq
    (fun d => heightProfile rho L (gammaSetMatrix (primitiveRowEquiv
      (d4BMCoprimeIntegerToPrimitivePair (d4BMPositiveModulusOfPNat c) d)) • z).im)]
  change (∑' p : D4BMUnitResidueTranslateIndex (d4BMPositiveModulusOfPNat c),
      heightProfile rho L (gammaSetMatrix (primitiveRowEquiv
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
theorem source_eq_denominator_slices (rho : ℂ) (L : ℝ) (z : UpperHalfPlane) :
    source rho L z = heightProfile rho L z.im +
      ∑' c : ℕ+, denominatorSlice rho L z.im c z.re := by
  rw [source_denominator_rows]
  congr 1
  apply tsum_congr
  intro c
  exact denominator_rows_eq_slice rho L z c


private def cauchyMajorant (y x : ℝ) : ℝ := (y^2+x^2)^(-(2:ℝ))

private theorem cauchyMajorant_integrable (y : ℝ) (hy : 0 < y) :
    Integrable (cauchyMajorant y) := by
  have h := (integrable_d4BMCauchyPowerKernel ⟨0,y,hy⟩ ⟨2,by norm_num⟩).norm
  change Integrable (fun x => (y^2+x^2)^(-(2:ℝ)))
  simpa [norm_d4BMCauchyPowerKernel] using h

private theorem archProfile_bound (rho : ℂ) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : ℝ), 0 < y → ∀ (c : ℕ+) (x : ℝ),
      ‖archProfile rho L y c x‖ ≤
        (C*y^2*((c:ℕ):ℝ)^(-(4:ℝ)))*cauchyMajorant y x := by
  obtain ⟨C,hC,hb⟩ := heightProfile_power_bound rho L 2
  refine ⟨C,hC,fun y hy c x => ?_⟩
  have hc : 0 < ((c:ℕ):ℝ) := by exact_mod_cast c.pos
  have hq : 0 < y^2+x^2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hy) (sq_nonneg x)
  have h := hb (y/(((c:ℕ):ℝ)^2*(y^2+x^2))) (by positivity)
  change ‖archProfile rho L y c x‖ ≤ _ at h
  convert h using 1
  unfold cauchyMajorant
  rw [Real.rpow_neg hc.le, Real.rpow_neg hq.le]
  norm_num
  field_simp [hc.ne', hq.ne']

private theorem archProfile_measurable (rho : ℂ) (L y : ℝ) (c : ℕ+) :
    Measurable (archProfile rho L y c) := by
  exact (heightProfile_measurable rho L).comp (by fun_prop)

/-- Every complete translation profile is absolutely integrable. -/
theorem archProfile_integrable (rho : ℂ) (L y : ℝ) (hy : 0 < y) (c : ℕ+) :
    Integrable (archProfile rho L y c) := by
  obtain ⟨C,_,hb⟩ := archProfile_bound rho L
  exact ((cauchyMajorant_integrable y hy).const_mul
    (C*y^2*((c:ℕ):ℝ)^(-(4:ℝ)))).mono'
      (archProfile_measurable rho L y c).aestronglyMeasurable (ae_of_all _ (hb y hy c))

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

private theorem denominatorSlice_integrable (rho : ℂ) (L y : ℝ) (hy : 0 < y) (c : ℕ+) :
    IntegrableOn (denominatorSlice rho L y c) (Ioc 0 1) := by
  exact GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    (fun a : UnitResidue c => shiftedPeriodization_integrable
      (archProfile_integrable rho L y hy c) ((a.1.val:ℝ)/(c:ℕ))) Summable.of_finite

private theorem denominatorSlice_mean (rho : ℂ) (L y : ℝ) (hy : 0 < y) (c : ℕ+) :
    (∫ x in Ioc (0:ℝ) 1, denominatorSlice rho L y c x) =
      ((c:ℕ).totient:ℂ)*(∫ t, archProfile rho L y c t) := by
  unfold denominatorSlice
  rw [GaloisForLFunctions.HTGeometry.integral_tsum_eq_tsum_integral_of_summable_integral_norm
    (fun a : UnitResidue c => shiftedPeriodization_integrable
      (archProfile_integrable rho L y hy c) ((a.1.val:ℝ)/(c:ℕ))) Summable.of_finite]
  simp only [shiftedPeriodization_mean (archProfile_integrable rho L y hy c)]
  simp [tsum_fintype, unitResidue_card, nsmul_eq_mul]

private theorem denominatorSlice_norm_le (rho : ℂ) (L y : ℝ) (hy : 0 < y) (c : ℕ+) :
    (∫ x in Ioc (0:ℝ) 1, ‖denominatorSlice rho L y c x‖) ≤
      (c:ℕ)*(∫ t, ‖archProfile rho L y c t‖) := by
  have hi := fun a : UnitResidue c => shiftedPeriodization_integrable
    (archProfile_integrable rho L y hy c) ((a.1.val:ℝ)/(c:ℕ))
  have h := GaloisForLFunctions.HTGeometry.integral_norm_tsum_le_tsum_integral_norm
    hi Summable.of_finite
  change (∫ x in Ioc (0:ℝ) 1, ‖denominatorSlice rho L y c x‖) ≤ _ at h
  refine h.trans ?_
  calc
    _ ≤ ∑' _a : UnitResidue c, ∫ t, ‖archProfile rho L y c t‖ := by
      rw [tsum_fintype, tsum_fintype]
      exact Finset.sum_le_sum fun a _ => shiftedPeriodization_norm_le
        (archProfile_integrable rho L y hy c) _
    _ = ((c:ℕ).totient:ℝ)*(∫ t, ‖archProfile rho L y c t‖) := by
      simp [tsum_fintype, unitResidue_card, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le (c:ℕ))
      (integral_nonneg fun _ => norm_nonneg _)


private theorem denominatorSlice_norm_summable (rho : ℂ) (L y : ℝ) (hy : 0 < y) :
    Summable (fun c : ℕ+ => ∫ x in Ioc (0:ℝ) 1, ‖denominatorSlice rho L y c x‖) := by
  obtain ⟨C,hC,hb⟩ := archProfile_bound rho L
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
  have hbint : (∫ t, ‖archProfile rho L y c t‖) ≤
      (C*y^2*((c:ℕ):ℝ)^(-(4:ℝ)))*(∫ t, cauchyMajorant y t) := by
    rw [← integral_const_mul]
    exact integral_mono (archProfile_integrable rho L y hy c).norm
      (hm.const_mul _) (hb y hy c)
  calc
    _ ≤ (c:ℕ)*(∫ t, ‖archProfile rho L y c t‖) := denominatorSlice_norm_le rho L y hy c
    _ ≤ ((c:ℕ):ℝ)*((C*y^2*((c:ℕ):ℝ)^(-(4:ℝ)))*(∫ t, cauchyMajorant y t)) := by
      gcongr
    _ = _ := by
      rw [Real.rpow_neg hcpos.le, Real.rpow_neg hcpos.le]
      norm_num
      field_simp

/-- The complete theta source has its exact primitive-denominator mean, with every totient
multiplicity retained and the infinite sum interchanged by absolute integrability. -/
theorem source_horizontal_mean (rho : ℂ) (L y : ℝ) (hy : 0 < y) :
    (∫ x in Ioc (0:ℝ) 1, source rho L (ofComplex (⟨x,y⟩:ℂ))) =
      heightProfile rho L y + ∑' c : ℕ+,
        ((c:ℕ).totient:ℂ)*(∫ t, archProfile rho L y c t) := by
  have hi := denominatorSlice_integrable rho L y hy
  have hs := denominatorSlice_norm_summable rho L y hy
  have hint := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm hi hs
  have he (x : ℝ) : source rho L (ofComplex (⟨x,y⟩:ℂ)) =
      heightProfile rho L y + ∑' c : ℕ+, denominatorSlice rho L y c x := by
    rw [source_eq_denominator_slices, point_im x y hy]
    congr 1
    apply tsum_congr
    intro c
    congr 1
    simp [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < (⟨x,y⟩:ℂ).im from hy)]
  simp_rw [he]
  rw [integral_add (integrable_const _) hint,
    GaloisForLFunctions.HTGeometry.integral_tsum_eq_tsum_integral_of_summable_integral_norm hi hs]
  simp only [denominatorSlice_mean rho L y hy]
  simp


/-- Exact native pairing against the complete primitive-denominator mean. -/
theorem source_pairing_height (rho : ℂ) (L M : ℝ) :
    (∫ z, conj (source rho L z)*source rho M z ∂angularMeasure) =
      ∫ y in Ioi (0:ℝ), ((y^2)⁻¹:ℝ) •
        (conj (heightProfile rho L y) * (heightProfile rho M y + ∑' c : ℕ+,
          ((c:ℕ).totient:ℂ)*(∫ t, archProfile rho M y c t))) := by
  rw [source_pairing_unfold, setIntegral_modularStrip_eq_iterated _
    (seedProduct_strip_integrable rho L M)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have he (x : ℝ) : seedProduct rho L M (ofComplex (⟨x,y⟩:ℂ)) =
      conj (heightProfile rho L y)*source rho M (ofComplex (⟨x,y⟩:ℂ)) := by
    unfold seedProduct
    rw [point_im x y hy]
  simp_rw [he]
  rw [integral_const_mul, integral_Ico_eq_integral_Ioc, source_horizontal_mean rho M y hy]

end
end RHTower.SelbergThetaDilationRows
