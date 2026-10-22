import GaloisForLFunctions.RHTower.SelbergScatteringHeightConjugation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinActualFirstStokesDefect
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalAngularCutoffCalibration

/-!
# The original Xi field after an outgoing quarter shift

The full retained forcing has an exact Weyl–Fourier decomposition. At every
actual Xi parameter its Weyl term vanishes and its Fourier tail has rapid cusp
decay. The shifted source has an exact modular inversion multiplier and fails
scalar inversion invariance. Among power-weighted squared norms, inversion
invariance holds exactly for the compensating half-power, whose density is
identically the original source density.
-/

open Complex Real Set Filter Topology
open scoped ContDiff
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open RHTower.D4BMAngularSeries RHTower.D4BMJointSource
namespace RHTower.SelbergScatteringHeightConjugation
noncomputable section

/-- The actual coordinate derivative equals the complete canonical vertical jet on the exterior cusp. -/
theorem scalarSource_vertical_eq (u : ℂ) (x : ℝ) (Y : {y : ℝ // 1 ≤ y}) :
    coordDeriv 1 (scalarSource u) ![x,(Y:ℝ)] =
      d4BMCanonicalCuspConstantVerticalFirstJet u Y +
        d4BMCompletedEisensteinCuspVerticalFirstJetTail u x Y := by
  have hc : HasDerivAt (fun y : ℝ => ![x,y]) (Pi.single 1 1) (Y:ℝ) := by
    convert! ((hasDerivAt_id (Y:ℝ)).smul_const
      (Pi.single 1 1 : Fin 2 → ℝ)).const_add ![x,0] using 1
    · funext y i
      fin_cases i <;> simp
    · simp
  have hd := ((cuspLeg_contDiffAt .scalar u 2 ![x,(Y:ℝ)]
    (zero_lt_one.trans_le Y.2)).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt (Y:ℝ) hc
  have he := hd.unique (hasDerivAt_d4BMCompletedEisensteinCanonicalCuspLeg_vertical u x Y)
  rw [d4BM_canonicalCuspFullSecondJet_sigma_eq_constant_add_tail] at he
  exact he

/-- The full nonconstant Fourier contribution to the outgoing derivative defect. -/
def outgoingTailDefect (u : ℂ) (x y : ℝ) : ℂ :=
  (y:ℂ)*d4BMCompletedEisensteinCuspVerticalFirstJetTail u x y -
    (1/2-u)*d4BMCompletedEisensteinCuspTailPart .scalar u x y

/-- Exact separation of the incoming Weyl contribution and the complete outgoing Fourier defect. -/
theorem outgoingDefect_eq_constant_add_tail (u : ℂ) (x : ℝ)
    (Y : {y : ℝ // 1 ≤ y}) :
    outgoingDefect u ![x,(Y:ℝ)] =
      2*u*reflectedCompletedLambda (1+2*u)*(Y:ℂ)^(1/2+u) +
        outgoingTailDefect u x Y := by
  have hY : 0 < (Y:ℝ) := zero_lt_one.trans_le Y.2
  rw [outgoingDefect, scalarSource_vertical_eq,
    d4BM_canonicalCuspConstantVerticalFirstJet_eq_termSum u hY]
  simp only [scalarSource, d4BMCompletedEisensteinCuspLeg,
    d4BMCompletedEisensteinCuspConstantPart, d4BMCompletedEisensteinCuspConstantTerm,
    d4BMCompletedEisensteinCuspConstantMaassFactor, mul_one,
    d4BMCompletedEisensteinCuspConstantCoefficient, d4BMCompletedEisensteinCuspWeylExponent,
    d4BMCuspSign, Bool.false_eq_true, ite_false, ite_true, Int.cast_neg, Int.cast_one,
    neg_one_mul, one_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hm := d4BM_zeroFrequency_cpow_mul_deriv (1/2-u) hY
  have hp := d4BM_zeroFrequency_cpow_mul_deriv (1/2+u) hY
  simp only [sub_eq_add_neg] at hm
  unfold outgoingTailDefect
  linear_combination reflectedCompletedLambda (2*u)*hm +
    reflectedCompletedLambda (1+2*u)*hp

/-- At each fixed horizontal position, the full outgoing Fourier defect beats every complex height power. -/
theorem outgoingTailDefect_rapid (u w : ℂ) (x : ℝ) :
    Tendsto (fun y : ℝ => (y:ℂ)^w*outgoingTailDefect u x y) atTop (𝓝 0) := by
  have h1 := tendsto_d4BMCompletedEisensteinComplexPowerCuspVerticalFirstJetTail_atTop_zero u (w+1) x
  have h0 := (d4BM_tendsto_cpow_cuspTailPart .scalar u w x).const_mul (1/2-u)
  have h := h1.sub h0
  simp only [mul_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne'), Complex.cpow_one]
  unfold outgoingTailDefect
  ring

private theorem lambda_xi (q : XiZeroCopy) : reflectedCompletedLambda (q.1:ℂ) = 0 := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hne1 : (q.1:ℂ) ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    norm_num at he
    linarith [hstrip.2]
  have hz := (xi_eq_zero_iff hstrip.1 hne1).mp (xi_eq_zero_of_mem_divisor_support q.1)
  rw [reflectedCompletedLambda,hz,mul_zero]

/-- At every physical Xi parameter the incoming Weyl coefficient vanishes, leaving exactly the Fourier defect. -/
theorem outgoingDefect_xi_eq_tail (q : XiZeroCopy) (x : ℝ)
    (Y : {y : ℝ // 1 ≤ y}) :
    outgoingDefect (physicalAngularParameter q) ![x,(Y:ℝ)] =
      outgoingTailDefect (physicalAngularParameter q) x Y := by
  rw [outgoingDefect_eq_constant_add_tail]
  have hp : 1+2*physicalAngularParameter q = (q.1:ℂ) := by
    rw [physicalAngularParameter_eq]; ring
  rw [hp, lambda_xi, mul_zero, zero_mul, zero_add]

/-- The actual Xi outgoing derivative defect has rapid decay at each fixed horizontal position. -/
theorem outgoingDefect_xi_rapid (q : XiZeroCopy) (w : ℂ) (x : ℝ) :
    Tendsto (fun y : ℝ => (y:ℂ)^w*outgoingDefect (physicalAngularParameter q) ![x,y])
      atTop (𝓝 0) := by
  apply (outgoingTailDefect_rapid (physicalAngularParameter q) w x).congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
  rw [outgoingDefect_xi_eq_tail q x ⟨y,hy⟩]


/-- The shifted full Xi source obeys its literal Casimir equation with the complete first-order forcing retained. -/
theorem quarterShiftSource_xi_equation (q : XiZeroCopy) (z : Fin 2 → ℝ)
    (hz : 0 < z 1) :
    -hyperbolicLaplacian (quarterShiftSource (physicalAngularParameter q)) z -
        ((q.1:ℂ)/2+1/4)*(1-(q.1:ℂ)/2-1/4)*
          quarterShiftSource (physicalAngularParameter q) z =
      (1/2:ℂ)*(z 1:ℂ)^(-1/4:ℂ)*outgoingDefect (physicalAngularParameter q) z := by
  have h := quarterShiftSource_equation (physicalAngularParameter q) z hz
  convert h using 1
  rw [physicalAngularParameter_eq]
  ring

/-- Every fixed complex height weight of the actual shifted Xi residual tends to zero along each vertical ray. -/
theorem quarterShiftSource_xi_residual_rapid (q : XiZeroCopy) (w : ℂ) (x : ℝ) :
    Tendsto (fun y : ℝ => (y:ℂ)^w *
      (-hyperbolicLaplacian (quarterShiftSource (physicalAngularParameter q)) ![x,y] -
        ((q.1:ℂ)/2+1/4)*(1-(q.1:ℂ)/2-1/4)*
          quarterShiftSource (physicalAngularParameter q) ![x,y])) atTop (𝓝 0) := by
  have h := (outgoingDefect_xi_rapid q (w+(-1/4)) x).const_mul (1/2:ℂ)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  rw [quarterShiftSource_xi_equation q ![x,y] hy,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne')]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  ring

/-- The original modular inversion transports the shifted Xi field with an exact nonunitary height multiplier. -/
theorem quarterShiftSource_xi_invert (q : XiZeroCopy) (z : D4BMUpperHalfPlaneCoordinate) :
    ((z.x^2+z.y^2:ℝ):ℂ)^(-1/4:ℂ)*
        quarterShiftSource (physicalAngularParameter q)
          ![(d4BMEisensteinInvertCoordinate z).x,(d4BMEisensteinInvertCoordinate z).y] =
      quarterShiftSource (physicalAngularParameter q) ![z.x,z.y] := by
  have hQ : 0 < z.x^2+z.y^2 := by nlinarith [sq_nonneg z.x, sq_pos_of_pos z.y_pos]
  have hi : scalarSource (physicalAngularParameter q)
      ![(d4BMEisensteinInvertCoordinate z).x,(d4BMEisensteinInvertCoordinate z).y] =
      scalarSource (physicalAngularParameter q) ![z.x,z.y] := physicalScalar_invert q z
  have hp := Complex.mul_cpow_ofReal_nonneg hQ.le
    (d4BMEisensteinInvertCoordinate z).y_pos.le (-1/4:ℂ)
  have he : (z.x^2+z.y^2)*(d4BMEisensteinInvertCoordinate z).y = z.y := by
    dsimp [d4BMEisensteinInvertCoordinate]
    field_simp
  rw [← Complex.ofReal_mul, he] at hp
  simp only [quarterShiftSource, Matrix.cons_val_one, Matrix.cons_val_zero, hi]
  rw [← mul_assoc, ← hp]

private theorem lambda_before_xi_ne (q : XiZeroCopy) :
    reflectedCompletedLambda ((q.1:ℂ)-1) ≠ 0 := by
  have h := (physicalScalar_cutoff_calibration q).2.1
  rw [(physicalScalar_cutoff_calibration q).1] at h
  exact (mul_ne_zero_iff.mp h).2

/-- The original full Xi source is nonzero somewhere on every positive horizontal line, by its nonzero Weyl mean. -/
theorem scalarSource_xi_nonzero_on_every_height (q : XiZeroCopy) (y : ℝ) (hy : 0 < y) :
    ∃ x : ℝ, scalarSource (physicalAngularParameter q) ![x,y] ≠ 0 := by
  by_contra hn
  push Not at hn
  have he := mean_scalar (physicalAngularParameter q) hy
  have hz : (fun x : ℝ => D4BMGlobalAngularResponse.scalar (physicalAngularParameter q) ![x,y]) =
      fun _ => 0 := by funext x; exact hn x
  rw [hz] at he
  have hp := physicalScalar_principal q ![0,y]
  have hh : D4BMGlobalAngularResponse.principal (physicalAngularParameter q) ![0,y] = 0 := by
    simpa [D4BMCuspProjection.mean] using he.symm
  rw [hp] at hh
  exact (mul_ne_zero (lambda_before_xi_ne q)
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne')))) hh

/-- At every actual Xi parameter, the literal quarter-height multiplier destroys scalar inversion invariance. -/
theorem quarterShiftSource_xi_not_inversion_invariant (q : XiZeroCopy) :
    ¬ ∀ z : D4BMUpperHalfPlaneCoordinate,
      quarterShiftSource (physicalAngularParameter q)
          ![(d4BMEisensteinInvertCoordinate z).x,(d4BMEisensteinInvertCoordinate z).y] =
        quarterShiftSource (physicalAngularParameter q) ![z.x,z.y] := by
  intro hi
  obtain ⟨x,hx⟩ := scalarSource_xi_nonzero_on_every_height q 2 (by norm_num)
  let z : D4BMUpperHalfPlaneCoordinate := ⟨x,2,by norm_num⟩
  have hnon : quarterShiftSource (physicalAngularParameter q) ![z.x,z.y] ≠ 0 := by
    exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num : (2:ℂ) ≠ 0))) hx
  have he := quarterShiftSource_xi_invert q z
  rw [hi z] at he
  have hfac : ((z.x^2+z.y^2:ℝ):ℂ)^(-1/4:ℂ) = 1 :=
    (mul_left_inj' hnon).mp (he.trans (one_mul _).symm)
  have hQ : 1 < z.x^2+z.y^2 := by dsimp [z]; nlinarith [sq_nonneg x]
  have hh := congrArg norm hfac
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans zero_lt_one hQ), norm_one] at hh
  have hlt := Real.rpow_lt_one_of_one_lt_of_neg hQ (by norm_num : (-1/4:ℝ) < 0)
  have hh' : (z.x^2+z.y^2)^(-1/4:ℝ) = 1 := by
    convert hh using 1
    norm_num
  exact (ne_of_lt hlt) hh'


/-- The compensating half-power density equals the original full source density pointwise. -/
theorem quarterShiftSource_compensated_norm (u : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    (z 1 : ℝ)^(1/2:ℝ)*‖quarterShiftSource u z‖^2 = ‖scalarSource u z‖^2 := by
  rw [quarterShiftSource, norm_mul, mul_pow, Complex.norm_cpow_eq_rpow_re_of_pos hz]
  have he : ((-1/4:ℂ).re) = (-1/4:ℝ) := by norm_num
  rw [he, ← Real.rpow_mul_natCast hz.le]
  rw [← mul_assoc, ← Real.rpow_add hz]
  norm_num

/-- The compensated squared norm of the actual shifted Xi source retains modular inversion invariance. -/
theorem quarterShiftSource_xi_compensated_density_invert (q : XiZeroCopy)
    (z : D4BMUpperHalfPlaneCoordinate) :
    (d4BMEisensteinInvertCoordinate z).y^(1/2:ℝ)*
        ‖quarterShiftSource (physicalAngularParameter q)
          ![(d4BMEisensteinInvertCoordinate z).x,(d4BMEisensteinInvertCoordinate z).y]‖^2 =
      z.y^(1/2:ℝ)*‖quarterShiftSource (physicalAngularParameter q) ![z.x,z.y]‖^2 := by
  have hL := quarterShiftSource_compensated_norm (physicalAngularParameter q)
    ![(d4BMEisensteinInvertCoordinate z).x,(d4BMEisensteinInvertCoordinate z).y]
    (d4BMEisensteinInvertCoordinate z).y_pos
  have hR := quarterShiftSource_compensated_norm (physicalAngularParameter q) ![z.x,z.y] z.y_pos
  exact hL.trans ((congrArg (fun a : ℂ => ‖a‖^2) (physicalScalar_invert q z)).trans hR.symm)


/-- Every power-weighted shifted density is exactly a height power times the original density. -/
theorem quarterShiftSource_weighted_norm (u : ℂ) (b : ℝ) (z : Fin 2 → ℝ)
    (hz : 0 < z 1) :
    (z 1 : ℝ)^b*‖quarterShiftSource u z‖^2 =
      (z 1 : ℝ)^(b-1/2)*‖scalarSource u z‖^2 := by
  rw [quarterShiftSource, norm_mul, mul_pow, Complex.norm_cpow_eq_rpow_re_of_pos hz]
  have he : ((-1/4:ℂ).re) = (-1/4:ℝ) := by norm_num
  rw [he, ← Real.rpow_mul_natCast hz.le, ← mul_assoc, ← Real.rpow_add hz]
  congr 2
  norm_num
  ring

/-- Among all real height powers, precisely the compensating half-power makes the actual Xi density inversion invariant. -/
theorem quarterShiftSource_xi_power_density_invariant_iff (q : XiZeroCopy) (b : ℝ) :
    (∀ z : D4BMUpperHalfPlaneCoordinate,
      (d4BMEisensteinInvertCoordinate z).y^b*
          ‖quarterShiftSource (physicalAngularParameter q)
            ![(d4BMEisensteinInvertCoordinate z).x,(d4BMEisensteinInvertCoordinate z).y]‖^2 =
        z.y^b*‖quarterShiftSource (physicalAngularParameter q) ![z.x,z.y]‖^2) ↔ b = 1/2 := by
  constructor
  · intro hi
    by_contra hb
    obtain ⟨x,hx⟩ := scalarSource_xi_nonzero_on_every_height q 2 (by norm_num)
    let z : D4BMUpperHalfPlaneCoordinate := ⟨x,2,by norm_num⟩
    have hL := quarterShiftSource_weighted_norm (physicalAngularParameter q) b
      ![(d4BMEisensteinInvertCoordinate z).x,(d4BMEisensteinInvertCoordinate z).y]
      (d4BMEisensteinInvertCoordinate z).y_pos
    have hR := quarterShiftSource_weighted_norm (physicalAngularParameter q) b ![z.x,z.y] z.y_pos
    have hfield : scalarSource (physicalAngularParameter q)
        ![(d4BMEisensteinInvertCoordinate z).x,(d4BMEisensteinInvertCoordinate z).y] =
        scalarSource (physicalAngularParameter q) ![z.x,z.y] := physicalScalar_invert q z
    rw [hfield] at hL
    have he := hL.symm.trans ((hi z).trans hR)
    have hnorm : ‖scalarSource (physicalAngularParameter q) ![z.x,z.y]‖^2 ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
    have hp := (mul_left_inj' hnorm).mp he
    have hy := (Real.rpow_left_inj (d4BMEisensteinInvertCoordinate z).y_pos.le
      z.y_pos.le (sub_ne_zero.mpr hb)).mp hp
    change 2/(x^2+2^2)=2 at hy
    have hQ : (x^2+2^2:ℝ) ≠ 0 := by nlinarith [sq_nonneg x]
    have hm := congrArg (fun t : ℝ => t*(x^2+2^2)) hy
    rw [div_mul_cancel₀ _ hQ] at hm
    nlinarith [sq_nonneg x]
  · rintro rfl
    exact quarterShiftSource_xi_compensated_density_invert q

end
end RHTower.SelbergScatteringHeightConjugation
