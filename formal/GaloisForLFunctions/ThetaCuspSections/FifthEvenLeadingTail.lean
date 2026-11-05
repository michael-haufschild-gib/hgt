import GaloisForLFunctions.ThetaCuspSections.FifthEvenLeadingTailModel
import GaloisForLFunctions.ThetaCuspSections.FifthEvenTailGammaBounds
import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleEightData

/-!
# Integrated positivity of the leading theta atom pairs

Rate-five incomplete-gamma moments retain the two ordered unequal pairs
between atoms one and two. Their gamma enclosure and exponential weight
are paid by the first atom's retained gamma reserve.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ThetaCuspSections.FifthMixedTail
open FifthAtomTail

/-- Radial density of a leading unequal pair. -/
def fiveBoundary (q : ℝ) : ℝ := q^(3/2:ℝ)*Real.exp (-5*q)
/-- Half-integer tail moment with rate five. -/
def fivePowerTail (s q : ℝ) : ℝ := ∫ t in Ioi q, t^s*Real.exp (-5*t)
/-- Rate-five normalized gamma mass, in rate-two coordinates. -/
def fiveGammaMass (q : ℝ) : ℝ := (2/5)*gammaMass ((5/2)*q)

/-- The literal rate-five mass lies between the certified cubic and quadratic bounds. -/
theorem fiveGammaMass_bounds {q : ℝ} (hq : 0<q) :
 zL q≤fiveGammaMass q ∧ fiveGammaMass q≤zU q := by
 have hs : 0<(5/2:ℝ)*q := by positivity
 have hL := mul_le_mul_of_nonneg_left (gammaMass_cubic_lower hs)
   (show (0:ℝ)≤2/5 by norm_num)
 have hU := mul_le_mul_of_nonneg_left (gammaMass_quadratic_upper hs)
   (show (0:ℝ)≤2/5 by norm_num)
 have eL : (2/5:ℝ)*(1/2+3/(8*((5/2)*q))+3/(32*((5/2)*q)^2)-
   3/(128*((5/2)*q)^3))=zL q := by
  unfold zL
  field_simp [hq.ne']
  ring
 have eU : (2/5:ℝ)*(1/2+3/(8*((5/2)*q))+3/(32*((5/2)*q)^2))=zU q := by
  unfold zU
  field_simp [hq.ne']
  ring
 rw [eL] at hL
 rw [eU] at hU
 exact ⟨hL,hU⟩

private theorem five_boundary_scale {q : ℝ} (hq : 0≤q) :
 boundary ((5/2)*q)=(5/2:ℝ)^(3/2:ℝ)*fiveBoundary q := by
 unfold boundary fiveBoundary
 rw [Real.mul_rpow (by norm_num : (0:ℝ)≤5/2) hq,
   show (-2:ℝ)*((5/2)*q)= -5*q by ring]
 ring

/-- Linear scale change identifies the exact leading-pair gamma mass. -/
theorem fivePowerTail_mass {q : ℝ} (hq : 0<q) :
 fivePowerTail (3/2) q=fiveBoundary q*fiveGammaMass q := by
 have hc : (5/2:ℝ)^(3/2:ℝ)≠0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
 have hs : 0<(5/2:ℝ)*q := by positivity
 have hg := powerTail_eq_g 0 hs
 norm_num only [Nat.cast_zero,zero_add,g] at hg
 apply mul_left_cancel₀ hc
 calc
  _ = ∫ t in Ioi q, ((5/2)*t)^(3/2:ℝ)*Real.exp (-2*((5/2)*t)) := by
   rw [fivePowerTail,← integral_const_mul]
   apply setIntegral_congr_fun measurableSet_Ioi
   intro t ht
   dsimp only
   rw [Real.mul_rpow (by norm_num : (0:ℝ)≤5/2) (hq.trans ht).le,
    show (-2:ℝ)*((5/2)*t)= -5*t by ring]
   ring
  _ = (5/2:ℝ)⁻¹*powerTail (3/2) ((5/2)*q) := by
   exact integral_comp_mul_left_Ioi
    (fun t : ℝ => t^(3/2:ℝ)*Real.exp (-2*t)) q (by norm_num : (0:ℝ)<5/2)
  _ = _ := by
   rw [hg,five_boundary_scale hq.le]
   unfold fiveGammaMass
   ring

private theorem five_power_integrable {s q : ℝ} (hs : -1<s) (hq : 0≤q) :
 IntegrableOn (fun t : ℝ => t^s*Real.exp (-5*t)) (Ioi q) := by
 have h := integrableOn_rpow_mul_exp_neg_mul_rpow hs
   (show (1:ℝ)≤1 by rfl) (show (0:ℝ)<5 by norm_num)
 simp only [Real.rpow_one] at h
 exact h.mono_set (Ioi_subset_Ioi hq)

private theorem fivePowerTail_recurrence {s q : ℝ} (hs : 0<s) (hq : 0<q) :
 fivePowerTail s q=q^s*Real.exp (-5*q)/5+s/5*fivePowerTail (s-1) q := by
 have hd (t : ℝ) (ht : t∈Ici q) :
   HasDerivAt (fun t : ℝ => t^s*Real.exp (-5*t))
    (s*(t^(s-1)*Real.exp (-5*t))-5*(t^s*Real.exp (-5*t))) t := by
  have ht0 : 0<t := hq.trans_le ht
  have hp := Real.hasDerivAt_rpow_const (p := s) (Or.inl ht0.ne')
  have he := ((hasDerivAt_id t).const_mul (-5)).exp
  refine (hp.mul he).congr_deriv ?_
  dsimp only [id_eq]
  ring
 have hi := ((five_power_integrable (s := s-1) (by linarith) hq.le).const_mul s).sub
   ((five_power_integrable (s := s) (by linarith) hq.le).const_mul 5)
 have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi
   (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s 5 (by norm_num))
 rw [integral_sub ((five_power_integrable (s := s-1) (by linarith) hq.le).const_mul s)
   ((five_power_integrable (s := s) (by linarith) hq.le).const_mul 5),
   integral_const_mul,integral_const_mul] at h
 change s*fivePowerTail (s-1) q-5*fivePowerTail s q=0-q^s*Real.exp (-5*q) at h
 linarith only [h]

/-- Every exact rate-five power moment obeys the certified model recurrence. -/
theorem fivePowerTail_eq_g5 (n : ℕ) {q : ℝ} (hq : 0<q) :
 fivePowerTail ((n:ℝ)+3/2) q=fiveBoundary q*g5 n q (fiveGammaMass q) := by
 induction n with
 | zero =>
   norm_num only [Nat.cast_zero,zero_add,g5]
   exact fivePowerTail_mass hq
 | succ n ih =>
   have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
   rw [fivePowerTail_recurrence (by positivity) hq]
   have he : ((n+1:ℕ):ℝ)+3/2-1=(n:ℝ)+3/2 := by push_cast; ring
   rw [he,ih]
   have hp : q^(((n+1:ℕ):ℝ)+3/2)=q^(3/2:ℝ)*q^(n+1) := by
    rw [add_comm,Real.rpow_add hq,Real.rpow_natCast]
   rw [hp]
   simp only [g5,fiveBoundary,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
   ring

private theorem mixedLinear_pow (q : ℝ) (k : ℕ) (hk : k≤8) :
 mixedLinear (fun n => q^n) k=
  (_root_.RHTower.thetaPairRadialEvenPolynomial (4*q^2) k).eval (5*q) := by
 rw [EightCrossData.mixed_eq q k hk]
 interval_cases k <;> simp only [mixedLinear,EightCrossData.bMoment,pow_zero,pow_one,mul_one]
 all_goals rfl

private theorem mixedLinear_sum (k : ℕ) (hk : k≤8) (m : ℕ → ℝ) :
 mixedLinear m k=∑ j ∈ Finset.range 19,
  mixedLinear (fun n => if n=j then 1 else 0) k*m j := by
 interval_cases k <;> norm_num [mixedLinear,Finset.sum_range_succ] <;> ring

private theorem integral_mixedLinear {μ : Measure ℝ} (f : ℕ → ℝ → ℝ)
 (hf : ∀ n, Integrable (f n) μ) (k : ℕ) (hk : k≤8) :
 mixedLinear (fun n => ∫ t, f n t ∂μ) k=
  ∫ t, mixedLinear (fun n => f n t) k ∂μ := by
 have he : (fun t => mixedLinear (fun n => f n t) k)=
   (fun t => ∑ j ∈ Finset.range 19,
    mixedLinear (fun n => if n=j then 1 else 0) k*f j t) :=
   funext (fun t => mixedLinear_sum k hk (fun n => f n t))
 rw [he,integral_finsetSum _ (fun j _ => (hf j).const_mul _)]
 rw [mixedLinear_sum k hk (fun n => ∫ t, f n t ∂μ)]
 simp only [integral_const_mul]

private theorem fiveBoundary_mul_pow (n : ℕ) {t : ℝ} (ht : 0<t) :
 fiveBoundary t*t^n=t^((n:ℝ)+3/2)*Real.exp (-5*t) := by
 rw [add_comm (n:ℝ),Real.rpow_add ht,Real.rpow_natCast]
 unfold fiveBoundary
 ring

private theorem five_weighted_integrable (n : ℕ) {q : ℝ} (hq : 0<q) :
 IntegrableOn (fun t : ℝ => fiveBoundary t*t^n) (Ioi q) := by
 have hi := five_power_integrable (s := (n:ℝ)+3/2)
   (by linarith only [show (0:ℝ)≤(n:ℝ) from Nat.cast_nonneg n]) hq.le
 exact hi.congr_fun (fun t ht => (fiveBoundary_mul_pow n (hq.trans ht)).symm) measurableSet_Ioi

private theorem integral_fiveBoundary_mul_pow (n : ℕ) {q : ℝ} (hq : 0<q) :
 (∫ t in Ioi q, fiveBoundary t*t^n)=fiveBoundary q*g5 n q (fiveGammaMass q) := by
 rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => fiveBoundary_mul_pow n (hq.trans ht))]
 exact fivePowerTail_eq_g5 n hq

/-- The leading unequal-pair radial integral equals its rate-five model exactly. -/
theorem mixed_radial_tail_eq (k : ℕ) (hk : k≤8) {q : ℝ} (hq : 0<q) :
 (∫ t in Ioi q, fiveBoundary t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (4*t^2) k).eval (5*t))=
  fiveBoundary q*mixedLinear (fun n => g5 n q (fiveGammaMass q)) k := by
 calc
  _ = ∫ t in Ioi q, mixedLinear (fun n => fiveBoundary t*t^n) k := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    rw [← mixedLinear_pow t k hk,mixedLinear_smul _ _ k hk]
  _ = mixedLinear (fun n => ∫ t in Ioi q, fiveBoundary t*t^n) k :=
    (integral_mixedLinear _ (fun n => five_weighted_integrable n hq) k hk).symm
  _ = mixedLinear (fun n => fiveBoundary q*g5 n q (fiveGammaMass q)) k := by
    congr 1
    funext n
    exact integral_fiveBoundary_mul_pow n hq
  _ = _ := mixedLinear_smul _ _ k hk

/-- The exact radial tail of the two ordered leading unequal pairs. -/
def mixedRadialTailMatrix (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 8*∫ t in Ioi q, fiveBoundary t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (4*t^2) (i.val+j.val)).eval (5*t)

/-- First pure atom and its two ordered cross pairs with atom two, integrated exactly. -/
def leadingRadialTailMatrix (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
 radialTailMatrix q+mixedRadialTailMatrix q

private theorem fiveBoundary_eq (q : ℝ) :
 fiveBoundary q=boundary q*Real.exp (-3*q) := by
 unfold fiveBoundary boundary
 rw [mul_assoc,← Real.exp_add]
 congr 1
 congr 1
 ring

/-- The exact leading tail keeps the unused first-atom gamma reserve. -/
theorem leadingRadialTailMatrix_eq {q : ℝ} (hq : 0<q) :
 leadingRadialTailMatrix q=boundary q •
  (leadingModel q (fiveGammaMass q) (Real.exp (-3*q))+
    (gammaMass q-(1/2+3/(8*q))) • model 0 1) := by
 have hA := model_affine q (gammaMass q)
 have hB := model_affine q (1/2+3/(8*q))
 ext i j
 have he : moment q (gammaMass q) (i.val+j.val)=
   moment q (1/2+3/(8*q)) (i.val+j.val)+
    (gammaMass q-(1/2+3/(8*q)))*moment 0 1 (i.val+j.val) := by
  have ha := congrFun (congrFun hA i) j
  have hb := congrFun (congrFun hB i) j
  dsimp only [model,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] at ha hb
  linear_combination ha-hb
 dsimp only [leadingRadialTailMatrix,radialTailMatrix,Matrix.add_apply,mixedRadialTailMatrix,
   Matrix.smul_apply,smul_eq_mul,leadingModel,totalMoment,model]
 rw [radial_tail_eq_model _ (by omega) hq,mixed_radial_tail_eq _ (by omega) hq,
   he,fiveBoundary_eq,← moment_eq_linearMoment _ _ _ (by omega)]
 ring

/-- The first pure atom pays both leading unequal-pair tails from scale three onward. -/
theorem leadingRadialTailMatrix_posDef {q : ℝ} (hq : 3≤q) :
 (leadingRadialTailMatrix q).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 obtain ⟨hL,hU⟩ := fiveGammaMass_bounds hq0
 have hM := leadingModel_posDef hq hL hU (Real.exp_pos _).le (exponential_envelope hq)
 have hR := mass_model_posDef.posSemidef.smul
   (sub_nonneg.mpr (gammaMass_enhanced_lower hq0))
 rw [leadingRadialTailMatrix_eq hq0]
 exact (hM.add_posSemidef hR).smul (boundary_pos hq0)

/-- The exact leading tail retains an explicit matrix reserve for further atom pairs. -/
theorem leadingRadialTailMatrix_gamma_reserve {q : ℝ} (hq : 0<q) :
 (leadingRadialTailMatrix q-boundary q •
   (leadingModel q (fiveGammaMass q) (Real.exp (-3*q))+
    (3/(32*q^2)-3/(128*q^3)) • model 0 1)).PosSemidef := by
 have he : leadingRadialTailMatrix q-boundary q •
   (leadingModel q (fiveGammaMass q) (Real.exp (-3*q))+
    (3/(32*q^2)-3/(128*q^3)) • model 0 1)=
   (boundary q*(gammaMass q-(1/2+3/(8*q))-(3/(32*q^2)-3/(128*q^3)))) • model 0 1 := by
  rw [leadingRadialTailMatrix_eq hq]
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring
 rw [he]
 apply mass_model_posDef.posSemidef.smul
 apply mul_nonneg (boundary_pos hq).le
 have h := gammaMass_cubic_lower hq
 linarith only [h]

open _root_.RHTower _root_.RHTower.ThetaCuspOddFourThreeAtom _root_.HTGeometry.SignedPoisson

/-- The literal tails of the two ordered unequal pairs between atoms one and two. -/
def mixedTailMatrix (r : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 ∫ s in Ioi r, (-1:ℝ)^(i.val+j.val)*
  (thetaCuspAtomPairReflectionJet (2*(i.val+j.val)) 1 2 (s/2)+
   thetaCuspAtomPairReflectionJet (2*(i.val+j.val)) 2 1 (s/2))

/-- The literal first-atom tail together with both leading unequal-pair tails. -/
def leadingTailMatrix (r : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
 tailMatrix r+mixedTailMatrix r

private theorem mixed_source_scaled (s : ℝ) (k : ℕ) :
 (Real.pi^(1/2:ℝ)/4)*((-1:ℝ)^k*
  (thetaCuspAtomPairReflectionJet (2*k) 1 2 (s/2)+
   thetaCuspAtomPairReflectionJet (2*k) 2 1 (s/2)))=
 (Real.pi*Real.exp s)*(8*fiveBoundary (Real.pi*Real.exp s)*
   (thetaPairRadialEvenPolynomial (4*(Real.pi*Real.exp s)^2) k).eval
    (5*(Real.pi*Real.exp s))) := by
 have hs : thetaCuspSingleAtomReflectionScale 1 (s/2)=Real.pi*Real.exp s := by
  simp only [thetaCuspSingleAtomReflectionScale,Nat.cast_one,one_pow,mul_one]
  congr 1
  congr 1
  ring
 rw [mul_add,mul_add,signed_pair_even 1 2 k (s/2),signed_pair_even 2 1 k (s/2),hs]
 norm_num only [Nat.cast_one,Nat.cast_ofNat,one_pow,one_mul,mul_one]
 have hq := mul_pos Real.pi_pos (Real.exp_pos s)
 have hp : (Real.pi*Real.exp s)^(3/2:ℝ)=
   (Real.pi*Real.exp s)*Real.pi^(1/2:ℝ)*Real.exp (s/2) := by
  rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hq,Real.rpow_one,
   Real.mul_rpow Real.pi_pos.le (Real.exp_pos s).le,← Real.exp_mul,
   show s*(1/2)=s/2 by ring]
  ring
 have he : Real.exp (s/2-5*(Real.pi*Real.exp s))=
   Real.exp (s/2)*Real.exp (-5*(Real.pi*Real.exp s)) := by
  rw [← Real.exp_add]
  congr 1
  ring
 rw [fiveBoundary,hp,he]
 ring

/-- The exact radial change of variable retains the full ordered-pair multiplicity. -/
theorem mixedTailMatrix_scaled (r : ℝ) :
 (Real.pi^(1/2:ℝ)/4) • mixedTailMatrix r=
   mixedRadialTailMatrix (Real.pi*Real.exp r) := by
 ext i j
 change (Real.pi^(1/2:ℝ)/4)*
   (∫ s in Ioi r, (-1:ℝ)^(i.val+j.val)*
    (thetaCuspAtomPairReflectionJet (2*(i.val+j.val)) 1 2 (s/2)+
     thetaCuspAtomPairReflectionJet (2*(i.val+j.val)) 2 1 (s/2)))=_
 rw [← integral_const_mul,mixedRadialTailMatrix,← integral_const_mul,FifthAtomTail.integral_scale]
 apply setIntegral_congr_fun measurableSet_Ioi
 intro s _
 dsimp only
 rw [mixed_source_scaled]
 ring

/-- The literal leading tail is the positive radial model after scale change. -/
theorem leadingTailMatrix_scaled (r : ℝ) :
 (Real.pi^(1/2:ℝ)/4) • leadingTailMatrix r=
  leadingRadialTailMatrix (Real.pi*Real.exp r) := by
 rw [leadingTailMatrix,smul_add,tailMatrix_scaled,mixedTailMatrix_scaled]
 rfl

/-- The first pure atom pays the literal leading unequal-pair tails from scale three. -/
theorem leadingTailMatrix_posDef_of_scale {r : ℝ} (hq : 3≤Real.pi*Real.exp r) :
 (leadingTailMatrix r).PosDef := by
 have hp := leadingRadialTailMatrix_posDef hq
 rw [← leadingTailMatrix_scaled] at hp
 have hc : 0<Real.pi^(1/2:ℝ)/4 := by positivity
 have h := hp.smul (inv_pos.mpr hc)
 simpa only [smul_smul,inv_mul_cancel₀ hc.ne',one_smul] using h

/-- Every nonnegative cutoff has a strictly positive literal leading-pair tail. -/
theorem leadingTailMatrix_posDef {r : ℝ} (hr : 0≤r) :
 (leadingTailMatrix r).PosDef := by
 apply leadingTailMatrix_posDef_of_scale
 have he : 1≤Real.exp r := by linarith only [Real.add_one_le_exp r,hr]
 have hπ := mul_le_mul_of_nonneg_left he Real.pi_pos.le
 rw [mul_one] at hπ
 exact Real.pi_gt_three.le.trans hπ

end GaloisForLFunctions.ThetaCuspSections.FifthMixedTail
