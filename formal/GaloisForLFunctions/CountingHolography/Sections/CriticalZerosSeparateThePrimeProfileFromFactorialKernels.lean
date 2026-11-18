import GaloisForLFunctions.CountingHolography.Sections.TheDyadicPrimeWeightOfSquareConductors
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import GaloisForLFunctions.RHTower.NymanMellinGaugeCollapse
import GaloisForLFunctions.RHTower.MobiusLaplaceMellinPlancherelBridge
import GaloisForLFunctions.RHTower.EvenSectorWeightGrowth
import GaloisForLFunctions.CountingHolography.TheIntegerProbesAreNotIntegerValued

/-!
# Critical zeros separate the square prime profile from factorial kernels

The logarithmic profile is twice the spline autocorrelation minus its
log-four translate. Its Mellin transform is nonzero at each critical zero
seen by the spline. Finite fractional-part combinations vanish there.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Complex MeasureTheory Filter Finset Topology Zeta23 ArithmeticCastelnuovoSeveri
open BiScaleUncertainty.ChebyshevGauge ArithmeticWeightTheory ArithmeticOrientationGeometry
open RenormalizedIntersectionTheory

private theorem lift_autocorr : cx splineAutoCorr = EF.weilTest (cx cubicSpline) (cx cubicSpline) := by
  funext t
  simp only [cx,splineAutoCorr,weilTest_ofReal,Complex.ofReal_re]

private theorem transform_profile (t : ℂ) :
    paperFT (cx squareLogProfile) t =
      (2-cexp (I*t*(Real.log 4:ℝ)))*
        (paperFT (cx cubicSpline) t*starRingEnd ℂ (paperFT (cx cubicSpline) (starRingEnd ℂ t))) := by
  let H := EF.weilTest (cx cubicSpline) (cx cubicSpline)
  let c : Fin 2 → ℂ := ![2,-1]
  let x : Fin 2 → ℝ := ![0,Real.log 4]
  have hH (v : ℝ) : H v = (splineAutoCorr v:ℂ) := congrFun lift_autocorr.symm v
  have he : cx squareLogProfile = fun u => ∑ i : Fin 2, c i*H (u-x i) := by
    funext u
    simp only [c,x,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,sub_zero,
      hH,cx,squareLogProfile,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_ofNat,neg_one_mul,sub_eq_add_neg]
  have hc := (cx_contDiff contDiff_cubicSpline).continuous
  have hs := cx_hasCompactSupport hasCompactSupport_cubicSpline
  rw [he,_root_.RHTower.EvenSector.paperFT_sum_translate univ c x
    (EF.weilTest_contDiff (cx_contDiff contDiff_cubicSpline) hc hs).continuous (EF.weilTest_hasCompactSupport hs hs)]
  rw [show H = EF.weilTest (cx cubicSpline) (cx cubicSpline) from rfl,EF.paperFT_weilTest hc hc hs hs]
  simp only [c,x,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Complex.ofReal_zero,
    mul_zero,Complex.exp_zero,mul_one,neg_one_mul,Complex.conj_ofReal,sub_eq_add_neg]

private theorem mellin_prime_weight (t : ℂ) :
    mellin squarePrimeWeight (1/2+t*I) = paperFT (cx squareLogProfile) t := by
  rw [_root_.RHTower.mellin_eq_integral_exp_neg_mul_log,paperFT]
  rw [← integral_neg_eq_self (fun u : ℝ => cx squareLogProfile u * cexp (I*t*u)) volume]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  change cexp (-(1/2+t*I)*u)*squarePrimeWeight (Real.exp (-u)) =
    (squareLogProfile (-u):ℂ)*cexp (I*t*(-u:ℝ))
  rw [squarePrimeWeight,Real.log_exp,neg_neg,Complex.ofReal_mul,Complex.ofReal_exp]
  rw [← mul_assoc,← Complex.exp_add]
  have he : -(1/2+t*I)*u+((u/2:ℝ):ℂ) = I*t*(-u:ℝ) := by push_cast; ring
  rw [he,mul_comm]

/-- The pole at one cancels exactly in the dyadic profile. -/
theorem squarePrimeWeight_mean_zero :
    (∫ v in Set.Ioi 0, squarePrimeWeight v) = 0 := by
  have hl : Real.log 4=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  have hi : I*(-I/2)=1/2 := by
    calc I*(-I/2) = -(I*I)/2 := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  have hs : 1/2+(-I/2)*I=1 := by rw [mul_comm _ I,hi]; norm_num
  have hphase : cexp (I*(-I/2)*(Real.log 4:ℝ))=2 := by
    rw [hi,hl,Complex.ofReal_mul,Complex.ofReal_ofNat,
      show (1/2:ℂ)*(2*(Real.log 2:ℝ))=(Real.log 2:ℝ) by ring,← Complex.ofReal_exp,
      Real.exp_log (by norm_num : (0:ℝ)<2),Complex.ofReal_ofNat]
  have h := mellin_prime_weight (-I/2)
  rw [hs,transform_profile,hphase,sub_self,zero_mul] at h
  simpa only [mellin,sub_self,Complex.cpow_zero,one_smul] using h

/-- Every critical zero seen by the cubic spline survives the subtraction
of the second conductor. -/
theorem mellin_squarePrimeWeight_ne_zero {ρ : ℂ} (hρ : ρ ∈ criticalSeen) :
    mellin squarePrimeWeight ρ ≠ 0 := by
  obtain ⟨_,hre,hseen⟩ := hρ
  have he : 1/2+(ρ.im:ℂ)*I = ρ := Complex.ext (by simp [hre]) (by simp)
  rw [← he,mellin_prime_weight,transform_profile,Complex.conj_ofReal]
  have hu : ‖cexp (I*(ρ.im:ℂ)*(Real.log 4:ℝ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re,Complex.mul_im]
  have hphase : (2:ℂ)-cexp (I*(ρ.im:ℂ)*(Real.log 4:ℝ)) ≠ 0 := by
    intro hh
    rw [← sub_eq_zero.mp hh] at hu
    norm_num at hu
  exact mul_ne_zero hphase (mul_ne_zero hseen (map_ne_zero (starRingEnd ℂ) hseen))

/-- Away from the critical line the four-box transform and its conjugate
are nonzero. The phase can only have modulus two on the boundary Re s = 1. -/
theorem mellin_squarePrimeWeight_off_line {ρ : ℂ} (h₁ : ρ.re < 1) (hhalf : ρ.re ≠ 1/2) :
    mellin squarePrimeWeight ρ ≠ 0 := by
  let z : ℂ := ⟨ρ.im,1/2-ρ.re⟩
  have he : 1/2+z*I = ρ := by
    apply Complex.ext <;> simp [z,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
  have hz : z.im ≠ 0 := sub_ne_zero.mpr (Ne.symm hhalf)
  have hzc : (starRingEnd ℂ z).im ≠ 0 := by simpa only [Complex.conj_im,neg_ne_zero] using hz
  have hl : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  have hr : (I*z*(Real.log 4:ℝ)).re = (ρ.re-1/2)*Real.log 4 := by
    simp [Complex.mul_re,Complex.mul_im,z,sub_neg_eq_add] <;> ring
  have hu : ‖cexp (I*z*(Real.log 4:ℝ))‖ < 2 := by
    rw [Complex.norm_exp,hr]
    apply lt_of_lt_of_eq _ (Real.exp_log (by norm_num : (0:ℝ)<2))
    apply Real.exp_lt_exp.mpr
    rw [hl]
    have hh : 2*(ρ.re-1/2) < 1 := by linarith only [h₁]
    linarith only [mul_lt_mul_of_pos_right hh (Real.log_pos (by norm_num : (1:ℝ)<2))]
  have hp : (2:ℂ)-cexp (I*z*(Real.log 4:ℝ)) ≠ 0 := by
    intro h
    rw [← sub_eq_zero.mp h] at hu
    norm_num at hu
  rw [← he,mellin_prime_weight,transform_profile]
  exact mul_ne_zero hp (mul_ne_zero (paperFT_cubicSpline_ne_zero hz)
    (map_ne_zero (starRingEnd ℂ) (paperFT_cubicSpline_ne_zero hzc)))

/-- No finite sum of fractional-part kernels agrees with the square
prime test on the positive half-line, even almost everywhere. -/
theorem nymanCombination_ne_squarePrimeWeight {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ)
    (ha : ∀ i, 0 < a i) :
    ¬ (NymanMellin.nymanCombination c a =ᵐ[volume.restrict (Set.Ioi 0)] squarePrimeWeight) := by
  obtain ⟨ρ,hρ⟩ := criticalSeen_infinite.nonempty
  have hZ : IsNontrivialZero ρ := hρ.1
  have hre := hρ.2.1
  have h₀ := NymanMellin.mellin_nymanCombination c a ha
    (s := ρ) (by rw [hre]; norm_num) (by rw [hre]; norm_num)
  rw [hZ.1,mul_zero,zero_div,neg_zero] at h₀
  intro he
  apply mellin_squarePrimeWeight_ne_zero hρ
  refine Eq.trans ?_ h₀
  unfold mellin
  exact integral_congr_ae (he.mono fun x hx => by rw [hx])

section Approximation
open Set

/-- Among bounded positive errors of fixed mass, the initial interval gives the
largest integral against the decreasing Mellin weight. -/
theorem initial_interval_mellin_bound {E : ℝ → ℝ} {σ B t : ℝ}
    (hσ : 0 < σ) (hσ' : σ ≤ 1) (ht : 0 < t)
    (hpos : ∀ x > 0, 0 ≤ E x) (hcap : ∀ x > 0, E x ≤ B)
    (hE : IntegrableOn E (Ioi 0)) (hW : IntegrableOn (fun x : ℝ => x^(σ-1)*E x) (Ioi 0))
    (hmass : (∫ x in Ioi 0, E x) ≤ B*t) :
    (∫ x in Ioi 0, x^(σ-1)*E x) ≤ B*t^σ/σ := by
  let k := t^(σ-1)
  let D := fun x : ℝ => x^(σ-1)*E x-k*E x
  have hi : IntegrableOn D (Ioi 0) := hW.sub (hE.const_mul k)
  have htail : (∫ x in Ioi t, D x) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : t < x := hx
    exact sub_nonpos.mpr (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos ht hx'.le (sub_nonpos.mpr hσ')) (hpos x (ht.trans hx')))
  have hir : IntervalIntegrable (fun x : ℝ => x^(σ-1)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith only [hσ])
  have hic : IntervalIntegrable (fun _ : ℝ => B*k) volume 0 t := intervalIntegrable_const
  have hhead : (∫ x in Ioc 0 t, D x) ≤ ∫ x in Ioc 0 t, B*x^(σ-1)-B*k := by
    apply setIntegral_mono_on (hi.mono_set Ioc_subset_Ioi_self)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mp ((hir.const_mul B).sub hic)) measurableSet_Ioc
    intro x hx
    have hk : k ≤ x^(σ-1) := Real.rpow_le_rpow_of_nonpos hx.1 hx.2 (sub_nonpos.mpr hσ')
    dsimp only [D]
    linarith only [mul_le_mul_of_nonneg_left (hcap x hx.1) (sub_nonneg.mpr hk)]
  have hpow : -1 < σ-1 := by linarith only [hσ]
  rw [← intervalIntegral.integral_of_le ht.le,← intervalIntegral.integral_of_le ht.le,
    intervalIntegral.integral_sub (hir.const_mul B) hic,intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl hpow),intervalIntegral.integral_const,
    sub_add_cancel,Real.zero_rpow hσ.ne',sub_zero,sub_zero,smul_eq_mul] at hhead
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi (hi.mono_set (Ioi_subset_Ioi ht.le))
  have hex : (∫ x in Ioi 0, D x) = (∫ x in Ioi 0, x^(σ-1)*E x)-k*(∫ x in Ioi 0, E x) := by
    unfold D
    rw [integral_sub hW (hE.const_mul k),integral_const_mul]
  have hk : 0 ≤ k := Real.rpow_nonneg ht.le _
  have hD : (∫ x in Ioi 0, D x) ≤ B*(t^σ/σ)-t*(B*k) := by
    rw [← hsplit]
    exact (add_le_add hhead htail).trans_eq (add_zero _)
  rw [hex] at hD
  calc
    _ ≤ (B*(t^σ/σ)-t*(B*k))+k*(∫ x in Ioi 0, E x) := (sub_le_iff_le_add).mp hD
    _ ≤ (B*(t^σ/σ)-t*(B*k))+k*(B*t) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hmass hk)
    _ = _ := by ring


theorem mellin_difference_initial_interval_bound {f g : ℝ → ℂ} {s : ℂ} {B t : ℝ}
    (hs : 0 < s.re) (hs' : s.re ≤ 1) (ht : 0 < t)
    (hf : MellinConvergent f s) (hg : MellinConvergent g s)
    (hE : IntegrableOn (fun x => ‖f x-g x‖) (Ioi 0))
    (hcap : ∀ x > 0, ‖f x-g x‖ ≤ B)
    (hmass : (∫ x in Ioi 0, ‖f x-g x‖) ≤ B*t) :
    ‖mellin f s-mellin g s‖ ≤ B*t^s.re/s.re := by
  let D := fun x : ℝ => (x:ℂ)^(s-1) • (f x-g x)
  have hi : IntegrableOn D (Ioi 0) :=
    (hf.sub hg).congr_fun (fun x _ => (smul_sub _ _ _).symm) measurableSet_Ioi
  have hnorm (x : ℝ) (hx : 0 < x) : ‖D x‖ = x^(s.re-1)*‖f x-g x‖ := by
    dsimp only [D]
    rw [norm_smul,Complex.norm_cpow_eq_rpow_re_of_pos hx,Complex.sub_re,Complex.one_re]
  have hDnorm : IntegrableOn (fun x => ‖D x‖) (Ioi 0) := hi.norm
  have hW := hDnorm.congr_fun hnorm measurableSet_Ioi
  have he : mellin f s-mellin g s = ∫ x in Ioi 0, D x := by
    rw [mellin,mellin,← integral_sub hf hg]
    exact setIntegral_congr_fun measurableSet_Ioi (fun _ _ => (smul_sub _ _ _).symm)
  rw [he]
  calc _ ≤ ∫ x in Ioi 0, ‖D x‖ := norm_integral_le_integral_norm _
    _ = _ := setIntegral_congr_fun measurableSet_Ioi hnorm
    _ ≤ _ := initial_interval_mellin_bound hs hs' ht (fun _ _ => norm_nonneg _) hcap hE hW hmass

/-- At scale X the cost B controls both the error height and X times the
integrated absolute error. Each nontrivial zero gives a lower bound on B. -/
theorem factorial_cost_at_zero {ρ : ℂ} (hρ : IsNontrivialZero ρ)
    {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ) (ha : ∀ j, 0 < a j)
    {X B : ℝ} (hX : 0 < X)
    (hE : IntegrableOn (fun v => ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) (Set.Ioi 0))
    (hcap : ∀ v > 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖ ≤ B)
    (hmass : (∫ v in Set.Ioi 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) ≤ B/X) :
    ρ.re*‖mellin squarePrimeWeight ρ‖*X^ρ.re ≤ B := by
  by_cases hM : mellin squarePrimeWeight ρ = 0
  · rw [hM,norm_zero,mul_zero,zero_mul]
    exact (norm_nonneg _).trans (hcap 1 one_pos)
  have hW : MellinConvergent squarePrimeWeight ρ := by
    by_contra hin
    exact hM (integral_undef hin)
  have hN := NymanMellin.mellinConvergent_nymanCombination c a ha hρ.2.1 hρ.2.2
  have hZ := NymanMellin.mellin_nymanCombination c a ha hρ.2.1 hρ.2.2
  rw [hρ.1,mul_zero,zero_div,neg_zero] at hZ
  have h := mellin_difference_initial_interval_bound hρ.2.1 hρ.2.2.le (inv_pos.mpr hX)
    hW hN hE hcap (by simpa only [div_eq_mul_inv] using hmass)
  rw [hZ,sub_zero,Real.inv_rpow hX.le,← div_eq_mul_inv] at h
  have hh := (le_div_iff₀ hρ.2.1).mp h
  have hh' := (le_div_iff₀ (Real.rpow_pos_of_pos hX ρ.re)).mp hh
  linarith only [hh']

/-- A fixed positive multiple of the square-root cost is unavoidable for
every balanced factorial comparison at every scale. -/
theorem critical_factorial_cost :
    ∃ C : ℝ, 0 < C ∧ ∀ {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ), (∀ j, 0 < a j) →
      ∀ {X B : ℝ}, 0 < X →
      IntegrableOn (fun v => ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) (Set.Ioi 0) →
      (∀ v > 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖ ≤ B) →
      (∫ v in Set.Ioi 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) ≤ B/X →
      C*X^(1/2:ℝ) ≤ B := by
  obtain ⟨ρ,hρ⟩ := criticalSeen_infinite.nonempty
  have hz : IsNontrivialZero ρ := hρ.1
  refine ⟨ρ.re*‖mellin squarePrimeWeight ρ‖,mul_pos hz.2.1 (norm_pos_iff.mpr (mellin_squarePrimeWeight_ne_zero hρ)),?_⟩
  intro m c a ha X B hX hE hcap hmass
  have h := factorial_cost_at_zero hz c a ha hX hE hcap hmass
  rwa [← hρ.2.1]


/-- Below the rightmost zero abscissa, every fixed power allowance eventually
fails for every factorial comparison, even when the number and scales of its
terms can be chosen anew at each X. -/
theorem factorial_cost_above_power {σ : ℝ} (hσ : 1/2 ≤ σ)
    (hwidth : σ < 1/2+SquareRootThreshold.zetaZeroWidth) (K : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℝ), (∀ j, 0 < a j) →
      ∀ B : ℝ, IntegrableOn (fun v => ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) (Ioi 0) →
      (∀ v > 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖ ≤ B) →
      (∫ v in Ioi 0, ‖squarePrimeWeight v-NymanMellin.nymanCombination c a v‖) ≤ B/X →
      K*X^σ < B := by
  have hn : ¬ ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1/2+(σ-1/2) := by
    intro hall
    have hw := (SquareRootThreshold.zetaZeroWidth_le_iff_re_le (sub_nonneg.mpr hσ)).mpr hall
    linarith only [hw,hwidth]
  push_neg at hn
  obtain ⟨ρ,hz,hr⟩ := hn
  have hρ : IsNontrivialZero ρ := hz
  have hgt : σ < ρ.re := by linarith only [hr]
  let C := ρ.re*‖mellin squarePrimeWeight ρ‖
  have hC : 0 < C := mul_pos hρ.2.1 (norm_pos_iff.mpr
    (mellin_squarePrimeWeight_off_line hρ.2.2 (hσ.trans_lt hgt).ne'))
  have hg := (tendsto_rpow_atTop (sub_pos.mpr hgt)).eventually (eventually_gt_atTop (K/C))
  filter_upwards [hg,eventually_gt_atTop (0:ℝ)] with X hx hX
  intro m c a ha B hE hcap hmass
  have hl := factorial_cost_at_zero hρ c a ha hX hE hcap hmass
  change C*X^ρ.re ≤ B at hl
  have hh : K < C*X^(ρ.re-σ) := by
    simpa only [mul_comm C] using (div_lt_iff₀ hC).mp hx
  calc
    _ < (C*X^(ρ.re-σ))*X^σ := mul_lt_mul_of_pos_right hh (Real.rpow_pos_of_pos hX _)
    _ = C*X^ρ.re := by rw [mul_assoc,← Real.rpow_add hX,sub_add_cancel]
    _ ≤ _ := hl

end Approximation

#print axioms factorial_cost_above_power
#print axioms factorial_cost_at_zero
#print axioms critical_factorial_cost
#print axioms squarePrimeWeight_mean_zero
#print axioms mellin_squarePrimeWeight_ne_zero
#print axioms mellin_squarePrimeWeight_off_line
#print axioms nymanCombination_ne_squarePrimeWeight

end GaloisForLFunctions.CountingHolography.Sections
