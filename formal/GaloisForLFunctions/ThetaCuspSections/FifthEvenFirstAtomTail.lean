import GaloisForLFunctions.ThetaCuspSections.FifthEvenFirstAtomTailModel
import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleEightData
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
/-!
# Positive fifth even tails of the first theta atom

Exponential scale change identifies the literal atom tails with half-integer
incomplete-gamma moments. Their common mass exceeds one half by at least
`3/(8q)`. The boundary comparison is positive definite from scale three,
covering every nonnegative center-tail cutoff. The retained incomplete-gamma
remainder is a positive definite matrix reserve at every positive scale.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ThetaCuspSections.FifthAtomTail

/-- The common radial density at the tail endpoint. -/
def boundary (q : ℝ) : ℝ := q^(3/2 : ℝ)*Real.exp (-2*q)
/-- An incomplete-gamma moment with rate two. -/
def powerTail (s q : ℝ) : ℝ := ∫ t in Ioi q, t^s*Real.exp (-2*t)
/-- The normalized gamma mass shared by every radial moment. -/
def gammaMass (q : ℝ) : ℝ := powerTail (3/2) q/boundary q

theorem boundary_pos {q : ℝ} (hq : 0<q) : 0<boundary q := by
 unfold boundary
 positivity

private theorem power_integrable {s q : ℝ} (hs : -1<s) (hq : 0≤q) :
 IntegrableOn (fun t : ℝ => t^s*Real.exp (-2*t)) (Ioi q) := by
 have h := integrableOn_rpow_mul_exp_neg_mul_rpow hs
   (show (1:ℝ)≤1 by rfl) (show (0:ℝ)<2 by norm_num)
 simp only [Real.rpow_one] at h
 exact h.mono_set (Ioi_subset_Ioi hq)

theorem powerTail_nonneg (s : ℝ) {q : ℝ} (hq : 0≤q) : 0≤powerTail s q := by
 apply integral_nonneg_of_ae
 filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
 have ht0 : 0≤t := hq.trans ht.le
 exact mul_nonneg (Real.rpow_nonneg ht0 s) (Real.exp_pos _).le

/-- Integration by parts retains the endpoint mass exactly. -/
theorem powerTail_recurrence {s q : ℝ} (hs : 0<s) (hq : 0<q) :
 powerTail s q=q^s*Real.exp (-2*q)/2+s/2*powerTail (s-1) q := by
 have hd (t : ℝ) (ht : t∈Ici q) :
   HasDerivAt (fun t : ℝ => t^s*Real.exp (-2*t))
    (s*(t^(s-1)*Real.exp (-2*t))-2*(t^s*Real.exp (-2*t))) t := by
  have ht0 : 0<t := hq.trans_le ht
  have hp := Real.hasDerivAt_rpow_const (p := s) (Or.inl ht0.ne')
  have he := ((hasDerivAt_id t).const_mul (-2)).exp
  refine (hp.mul he).congr_deriv ?_
  dsimp only [id_eq]
  ring
 have hi := ((power_integrable (s := s-1) (by linarith) hq.le).const_mul s).sub
   ((power_integrable (s := s) (by linarith) hq.le).const_mul 2)
 have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi
   (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s 2 (by norm_num))
 rw [integral_sub ((power_integrable (s := s-1) (by linarith) hq.le).const_mul s)
   ((power_integrable (s := s) (by linarith) hq.le).const_mul 2),
   integral_const_mul,integral_const_mul] at h
 change s*powerTail (s-1) q-2*powerTail s q=0-q^s*Real.exp (-2*q) at h
 linarith only [h]

/-- The endpoint term alone gives half of the normalized gamma mass. -/
theorem gammaMass_lower {q : ℝ} (hq : 0<q) : 1/2≤gammaMass q := by
 have h := powerTail_recurrence (s := 3/2) (by norm_num) hq
 have hn := powerTail_nonneg (1/2) hq.le
 norm_num only [show (3/2:ℝ)-1=1/2 by norm_num] at h
 unfold gammaMass
 apply (le_div_iff₀ (boundary_pos hq)).mpr
 dsimp only [boundary]
 linarith only [h,hn]

/-- The normalized recurrence represents every exact half-integer tail moment. -/
theorem powerTail_eq_g (n : ℕ) {q : ℝ} (hq : 0<q) :
 powerTail ((n:ℝ)+3/2) q=boundary q*g n q (gammaMass q) := by
 induction n with
 | zero =>
   norm_num only [Nat.cast_zero,zero_add,g]
   unfold gammaMass
   field_simp [(boundary_pos hq).ne']
 | succ n ih =>
   have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
   rw [powerTail_recurrence (by positivity) hq]
   have he : ((n+1:ℕ):ℝ)+3/2-1=(n:ℝ)+3/2 := by push_cast; ring
   rw [he,ih]
   have hp : q^(((n+1:ℕ):ℝ)+3/2)=q^(3/2:ℝ)*q^(n+1) := by
    rw [add_comm,Real.rpow_add hq,Real.rpow_natCast]
   rw [hp]
   simp only [g,boundary,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
   ring


private theorem linearMoment_pow (q : ℝ) (k : ℕ) (hk : k≤8) :
 linearMoment (fun n => q^n) k=
  (_root_.RHTower.thetaPairRadialEvenPolynomial (q^2) k).eval (2*q) := by
 rw [EightCrossData.radial_eq q k hk]
 interval_cases k <;> simp only [linearMoment,EightCrossData.rMoment,pow_zero,pow_one,mul_one]
 all_goals rfl

private theorem linearMoment_sum (k : ℕ) (hk : k≤8) (m : ℕ → ℝ) :
 linearMoment m k=∑ j ∈ Finset.range 11,
  linearMoment (fun n => if n=j then 1 else 0) k*m j := by
 interval_cases k <;> norm_num [linearMoment,Finset.sum_range_succ] <;> ring

private theorem integral_linearMoment {μ : Measure ℝ} (f : ℕ → ℝ → ℝ)
 (hf : ∀ n, Integrable (f n) μ) (k : ℕ) (hk : k≤8) :
 linearMoment (fun n => ∫ t, f n t ∂μ) k=
  ∫ t, linearMoment (fun n => f n t) k ∂μ := by
 have he : (fun t => linearMoment (fun n => f n t) k)=
   (fun t => ∑ j ∈ Finset.range 11,
    linearMoment (fun n => if n=j then 1 else 0) k*f j t) :=
   funext (fun t => linearMoment_sum k hk (fun n => f n t))
 rw [he,integral_finsetSum _ (fun j _ => (hf j).const_mul _)]
 rw [linearMoment_sum k hk (fun n => ∫ t, f n t ∂μ)]
 simp only [integral_const_mul]

private theorem boundary_mul_pow (n : ℕ) {t : ℝ} (ht : 0<t) :
 boundary t*t^n=t^((n:ℝ)+3/2)*Real.exp (-2*t) := by
 rw [add_comm (n:ℝ),Real.rpow_add ht,Real.rpow_natCast]
 unfold boundary
 ring

private theorem weighted_power_integrable (n : ℕ) {q : ℝ} (hq : 0<q) :
 IntegrableOn (fun t : ℝ => boundary t*t^n) (Ioi q) := by
 have hi := power_integrable (s := (n:ℝ)+3/2) (by linarith only [show (0:ℝ)≤(n:ℝ) from Nat.cast_nonneg n]) hq.le
 exact hi.congr_fun (fun t ht => (boundary_mul_pow n (hq.trans ht)).symm) measurableSet_Ioi

private theorem integral_boundary_mul_pow (n : ℕ) {q : ℝ} (hq : 0<q) :
 (∫ t in Ioi q, boundary t*t^n)=boundary q*g n q (gammaMass q) := by
 rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => boundary_mul_pow n (hq.trans ht))]
 exact powerTail_eq_g n hq

/-- Every radial tail moment equals its normalized incomplete-gamma model. -/
theorem radial_tail_eq_model (k : ℕ) (hk : k≤8) {q : ℝ} (hq : 0<q) :
 (∫ t in Ioi q, boundary t*
   (_root_.RHTower.thetaPairRadialEvenPolynomial (t^2) k).eval (2*t))=
  boundary q*moment q (gammaMass q) k := by
 calc
  _ = ∫ t in Ioi q, linearMoment (fun n => boundary t*t^n) k := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    rw [← linearMoment_pow t k hk,linearMoment_smul _ _ k hk]
  _ = linearMoment (fun n => ∫ t in Ioi q, boundary t*t^n) k :=
    (integral_linearMoment _ (fun n => weighted_power_integrable n hq) k hk).symm
  _ = linearMoment (fun n => boundary q*g n q (gammaMass q)) k := by
    congr 1
    funext n
    exact integral_boundary_mul_pow n hq
  _ = _ := by rw [linearMoment_smul _ _ k hk,← moment_eq_linearMoment _ _ k hk]

/-- The fifth even tail matrix in the radial coordinate. -/
def radialTailMatrix (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 ∫ t in Ioi q, boundary t*
  (_root_.RHTower.thetaPairRadialEvenPolynomial (t^2) (i.val+j.val)).eval (2*t)

theorem radialTailMatrix_eq {q : ℝ} (hq : 0<q) :
 radialTailMatrix q=boundary q • model q (gammaMass q) := by
 ext i j
 exact radial_tail_eq_model (i.val+j.val) (by omega) hq

/-- The exact radial tail has a strict fifth even section from scale three. -/
theorem radialTailMatrix_posDef {q : ℝ} (hq : 3≤q) : (radialTailMatrix q).PosDef := by
 have hq0 : 0<q := by linarith only [hq]
 rw [radialTailMatrix_eq hq0]
 exact (model_posDef hq (gammaMass_lower hq0)).smul (boundary_pos hq0)


open _root_.RHTower

private theorem signed_atom_radial (s : ℝ) (k : ℕ) :
 (-1:ℝ)^k*thetaCuspFirstAtomReflectionJet (2*k) (s/2)=
  4*(Real.pi*Real.exp s)^2*Real.exp (s/2-2*(Real.pi*Real.exp s))*
   (thetaPairRadialEvenPolynomial ((Real.pi*Real.exp s)^2) k).eval (2*(Real.pi*Real.exp s)) := by
 unfold thetaCuspFirstAtomReflectionJet
 rw [thetaCuspAtomPairEvenJet_eq_radial]
 have hs : thetaCuspSingleAtomReflectionScale 1 (s/2)=Real.pi*Real.exp s := by
  simp only [thetaCuspSingleAtomReflectionScale,Nat.cast_one,one_pow,mul_one]
  congr 1
  congr 1
  ring
 rw [hs]
 have hp : (-1:ℝ)^k*(-1:ℝ)^k=1 := by rw [← mul_pow]; norm_num
 rw [show (Real.pi*Real.exp s)*(Real.pi*Real.exp s)=(Real.pi*Real.exp s)^2 by ring,
  show Real.pi*Real.exp s+Real.pi*Real.exp s=2*(Real.pi*Real.exp s) by ring,
  show s/2-Real.pi*Real.exp s-Real.pi*Real.exp s=s/2-2*(Real.pi*Real.exp s) by ring]
 linear_combination 4*(Real.pi*Real.exp s)^2*Real.exp (s/2-2*(Real.pi*Real.exp s))*
  (thetaPairRadialEvenPolynomial ((Real.pi*Real.exp s)^2) k).eval (2*(Real.pi*Real.exp s))*hp

private theorem image_scale (r : ℝ) :
 (fun s : ℝ => Real.pi*Real.exp s) '' Ioi r=Ioi (Real.pi*Real.exp r) := by
 ext t
 constructor
 · rintro ⟨s,hs,rfl⟩
   exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hs) Real.pi_pos
 · intro ht
   change Real.pi*Real.exp r<t at ht
   have ht0 : 0<t := (mul_pos Real.pi_pos (Real.exp_pos r)).trans ht
   refine ⟨Real.log (t/Real.pi),?_,?_⟩
   · change r<Real.log (t/Real.pi)
     rw [← Real.exp_lt_exp,Real.exp_log (div_pos ht0 Real.pi_pos)]
     apply (lt_div_iff₀ Real.pi_pos).mpr
     simpa only [mul_comm] using ht
   · dsimp only
     rw [Real.exp_log (div_pos ht0 Real.pi_pos)]
     field_simp

private theorem integral_scale (r : ℝ) (f : ℝ → ℝ) :
 (∫ t in Ioi (Real.pi*Real.exp r), f t)=
  ∫ s in Ioi r, (Real.pi*Real.exp s)*f (Real.pi*Real.exp s) := by
 have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
  (fun s (_ : s∈Ioi r) => ((Real.hasDerivAt_exp s).const_mul Real.pi).hasDerivWithinAt)
  (show Set.InjOn (fun s : ℝ => Real.pi*Real.exp s) (Ioi r) from
   fun _ _ _ _ he => Real.exp_injective (mul_left_cancel₀ Real.pi_ne_zero he)) f
 rw [image_scale] at h
 rw [h]
 apply setIntegral_congr_fun measurableSet_Ioi
 intro s _
 dsimp only
 rw [abs_of_pos (mul_pos Real.pi_pos (Real.exp_pos s)),smul_eq_mul]

private theorem source_scaled (s : ℝ) (k : ℕ) :
 (Real.pi^(1/2:ℝ)/4)*((-1:ℝ)^k*thetaCuspFirstAtomReflectionJet (2*k) (s/2))=
  (Real.pi*Real.exp s)*(boundary (Real.pi*Real.exp s)*
   (thetaPairRadialEvenPolynomial ((Real.pi*Real.exp s)^2) k).eval (2*(Real.pi*Real.exp s))) := by
 have hq := mul_pos Real.pi_pos (Real.exp_pos s)
 have hp : (Real.pi*Real.exp s)^(3/2:ℝ)=
   (Real.pi*Real.exp s)*Real.pi^(1/2:ℝ)*Real.exp (s/2) := by
  rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hq,Real.rpow_one,
   Real.mul_rpow Real.pi_pos.le (Real.exp_pos s).le,← Real.exp_mul,
   show s*(1/2)=s/2 by ring]
  ring
 have he : Real.exp (s/2-2*(Real.pi*Real.exp s))=
  Real.exp (s/2)*Real.exp (-2*(Real.pi*Real.exp s)) := by
  rw [← Real.exp_add]
  congr 1
  ring
 rw [signed_atom_radial,boundary,hp,he]
 ring

/-- The literal first-atom fifth even tail in center-tail coordinates. -/
def tailMatrix (r : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 ∫ s in Ioi r, (-1:ℝ)^(i.val+j.val)*
  thetaCuspFirstAtomReflectionJet (2*(i.val+j.val)) (s/2)

/-- Exponential scale change identifies every literal atom-tail entry. -/
theorem tailMatrix_scaled (r : ℝ) :
 (Real.pi^(1/2:ℝ)/4) • tailMatrix r=radialTailMatrix (Real.pi*Real.exp r) := by
 ext i j
 change (Real.pi^(1/2:ℝ)/4)*
  (∫ s in Ioi r, (-1:ℝ)^(i.val+j.val)*thetaCuspFirstAtomReflectionJet (2*(i.val+j.val)) (s/2))=_
 rw [← integral_const_mul]
 rw [radialTailMatrix,integral_scale]
 exact setIntegral_congr_fun measurableSet_Ioi (fun s _ => source_scaled s (i.val+j.val))

/-- The exact first-atom fifth even tail is strict once its endpoint scale reaches three. -/
theorem tailMatrix_posDef_of_scale {r : ℝ} (hq : 3≤Real.pi*Real.exp r) :
 (tailMatrix r).PosDef := by
 have h := radialTailMatrix_posDef hq
 rw [← tailMatrix_scaled] at h
 have hc : 0<Real.pi^(1/2:ℝ)/4 := by positivity
 have hp := h.smul (inv_pos.mpr hc)
 simpa only [smul_smul,inv_mul_cancel₀ hc.ne',one_smul] using hp

/-- Every nonnegative cutoff has a strictly positive first-atom fifth even tail. -/
theorem tailMatrix_posDef {r : ℝ} (hr : 0≤r) : (tailMatrix r).PosDef := by
 apply tailMatrix_posDef_of_scale
 have he : 1≤Real.exp r := by linarith only [Real.add_one_le_exp r,hr]
 have hπ := mul_le_mul_of_nonneg_left he Real.pi_pos.le
 rw [mul_one] at hπ
 exact Real.pi_gt_three.le.trans hπ


/-- The first positive correction to the normalized incomplete-gamma mass. -/
theorem gammaMass_enhanced_lower {q : ℝ} (hq : 0<q) :
 1/2+3/(8*q)≤gammaMass q := by
 have h3 := powerTail_recurrence (s := 3/2) (by norm_num) hq
 have h1 := powerTail_recurrence (s := 1/2) (by norm_num) hq
 have hn := powerTail_nonneg (-1/2) hq.le
 norm_num only [show (3/2:ℝ)-1=1/2 by norm_num] at h3
 norm_num only [show (1/2:ℝ)-1= -1/2 by norm_num] at h1
 have hpow : q*q^(1/2:ℝ)*Real.exp (-2*q)=boundary q := by
  unfold boundary
  rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hq,Real.rpow_one]
 have hbound : boundary q/2≤q*powerTail (1/2) q := by
  have h := mul_nonneg hq.le hn
  rw [h1]
  nlinarith only [h,hpow]
 have hE := boundary_pos hq
 unfold gammaMass
 apply (le_div_iff₀ hE).mpr
 apply (mul_le_mul_iff_right₀ hq).mp
 have heq : q*((1/2+3/(8*q))*boundary q)=
   q*(boundary q/2)+(3/8)*boundary q := by
  field_simp [hq.ne']
 rw [heq]
 rw [h3]
 dsimp only [boundary] at hbound ⊢
 nlinarith only [hbound]

/-- The exact positive gamma reserve beyond the boundary-polynomial matrix. -/
theorem radialTailMatrix_decomposition {q : ℝ} (hq : 0<q) :
 radialTailMatrix q=boundary q • model q (1/2)+
  ((3/4)*powerTail (1/2) q) • model 0 1 := by
 rw [radialTailMatrix_eq hq,model_affine,smul_add,smul_smul]
 congr 1
 have h := powerTail_recurrence (s := 3/2) (by norm_num) hq
 norm_num only [show (3/2:ℝ)-1=1/2 by norm_num] at h
 have hc : boundary q*(gammaMass q-1/2)=(3/4)*powerTail (1/2) q := by
  unfold gammaMass
  have hm : boundary q*(powerTail (3/2) q/boundary q)=powerTail (3/2) q := by
   field_simp [(boundary_pos hq).ne']
  rw [mul_sub,hm]
  dsimp only [boundary]
  linarith only [h]
 rw [hc]

/-- The exact tail exceeds the boundary comparison by a positive definite reserve. -/
theorem radialTailMatrix_sub_half_posDef {q : ℝ} (hq : 0<q) :
 (radialTailMatrix q-boundary q • model q (1/2)).PosDef := by
 rw [radialTailMatrix_eq hq,model_affine,smul_add,add_sub_cancel_left,smul_smul]
 have hz : 0<gammaMass q-1/2 := by
  have h := gammaMass_enhanced_lower hq
  have hp : 0<3/(8*q) := by positivity
  linarith only [h,hp]
 exact mass_model_posDef.smul (mul_pos (boundary_pos hq) hz)

end GaloisForLFunctions.ThetaCuspSections.FifthAtomTail
