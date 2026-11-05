import GaloisForLFunctions.ThetaCuspSections.FifthEvenTailGammaBounds
/-!
# Half-integer tails at arbitrary positive exponential rate

A linear change of scale transfers the first-atom gamma enclosure to each
unequal theta pair. Integration by parts identifies every polynomial moment.
-/
noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ThetaCuspSections.FifthRateTail
open FifthAtomTail

/-- Normalized half-integer tail recurrence at exponential rate `b`. -/
def gRate (b : ℝ) : ℕ → ℝ → ℝ → ℝ
 | 0, _, z => z
 | n+1, q, z => q^(n+1)/b+((2*n+5:ℕ):ℝ)/(2*b)*gRate b n q z
/-- Radial boundary density at exponential rate `b`. -/
def rateBoundary (b q : ℝ) : ℝ := q^(3/2:ℝ)*Real.exp (-b*q)
/-- Half-integer tail integral at exponential rate `b`. -/
def ratePowerTail (b s q : ℝ) : ℝ := ∫ t in Ioi q, t^s*Real.exp (-b*t)
/-- The normalized mass in first-atom coordinates. -/
def rateGammaMass (b q : ℝ) : ℝ := (2/b)*gammaMass ((b/2)*q)
/-- Cubic lower enclosure of the normalized mass. -/
def zLower (b q : ℝ) : ℝ := 1/b+3/(2*b^2*q)+3/(4*b^3*q^2)-3/(8*b^4*q^3)
/-- Quadratic upper enclosure of the normalized mass. -/
def zUpper (b q : ℝ) : ℝ := 1/b+3/(2*b^2*q)+3/(4*b^3*q^2)

/-- The gamma enclosure rescales exactly at every positive rate. -/
theorem rateGammaMass_bounds {b q : ℝ} (hb : 0<b) (hq : 0<q) :
 zLower b q≤rateGammaMass b q ∧ rateGammaMass b q≤zUpper b q := by
 have hs : 0<(b/2)*q := by positivity
 have hL := mul_le_mul_of_nonneg_left (gammaMass_cubic_lower hs)
   (show (0:ℝ)≤2/b by positivity)
 have hU := mul_le_mul_of_nonneg_left (gammaMass_quadratic_upper hs)
   (show (0:ℝ)≤2/b by positivity)
 have eL : (2/b)*(1/2+3/(8*((b/2)*q))+3/(32*((b/2)*q)^2)-
   3/(128*((b/2)*q)^3))=zLower b q := by
  unfold zLower
  field_simp [hb.ne',hq.ne']
  ring
 have eU : (2/b)*(1/2+3/(8*((b/2)*q))+3/(32*((b/2)*q)^2))=zUpper b q := by
  unfold zUpper
  field_simp [hb.ne',hq.ne']
  ring
 rw [eL] at hL
 rw [eU] at hU
 exact ⟨hL,hU⟩

private theorem boundary_scale {b q : ℝ} (hb : 0<b) (hq : 0≤q) :
 boundary ((b/2)*q)=(b/2)^(3/2:ℝ)*rateBoundary b q := by
 unfold boundary rateBoundary
 rw [Real.mul_rpow (by positivity : (0:ℝ)≤b/2) hq,
   show (-2:ℝ)*((b/2)*q)= -b*q by ring]
 ring

/-- Linear substitution identifies the normalized mass with its literal integral. -/
theorem ratePowerTail_mass {b q : ℝ} (hb : 0<b) (hq : 0<q) :
 ratePowerTail b (3/2) q=rateBoundary b q*rateGammaMass b q := by
 have hc : (b/2)^(3/2:ℝ)≠0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
 have hs : 0<(b/2)*q := by positivity
 have hg := powerTail_eq_g 0 hs
 norm_num only [Nat.cast_zero,zero_add,g] at hg
 apply mul_left_cancel₀ hc
 calc
  _ = ∫ t in Ioi q, ((b/2)*t)^(3/2:ℝ)*Real.exp (-2*((b/2)*t)) := by
   rw [ratePowerTail,← integral_const_mul]
   apply setIntegral_congr_fun measurableSet_Ioi
   intro t ht
   dsimp only
   rw [Real.mul_rpow (by positivity : (0:ℝ)≤b/2) (hq.trans ht).le,
    show (-2:ℝ)*((b/2)*t)= -b*t by ring]
   ring
  _ = (b/2)⁻¹*powerTail (3/2) ((b/2)*q) := by
   exact integral_comp_mul_left_Ioi
    (fun t : ℝ => t^(3/2:ℝ)*Real.exp (-2*t)) q (by positivity : (0:ℝ)<b/2)
  _ = _ := by
   rw [hg,boundary_scale hb hq.le]
   unfold rateGammaMass
   field_simp [hb.ne']

/-- Every nonnegative half-integer polynomial moment is integrable on a positive ray. -/
theorem rate_power_integrable {b s q : ℝ} (hb : 0<b) (hs : -1<s) (hq : 0≤q) :
 IntegrableOn (fun t : ℝ => t^s*Real.exp (-b*t)) (Ioi q) := by
 have h := integrableOn_rpow_mul_exp_neg_mul_rpow hs
   (show (1:ℝ)≤1 by rfl) hb
 simp only [Real.rpow_one] at h
 exact h.mono_set (Ioi_subset_Ioi hq)

private theorem ratePowerTail_recurrence {b s q : ℝ}
 (hb : 0<b) (hs : 0<s) (hq : 0<q) :
 ratePowerTail b s q=q^s*Real.exp (-b*q)/b+s/b*ratePowerTail b (s-1) q := by
 have hd (t : ℝ) (ht : t∈Ici q) :
   HasDerivAt (fun t : ℝ => t^s*Real.exp (-b*t))
    (s*(t^(s-1)*Real.exp (-b*t))-b*(t^s*Real.exp (-b*t))) t := by
  have ht0 : 0<t := hq.trans_le ht
  have hp := Real.hasDerivAt_rpow_const (p := s) (Or.inl ht0.ne')
  have he := ((hasDerivAt_id t).const_mul (-b)).exp
  refine (hp.mul he).congr_deriv ?_
  dsimp only [id_eq]
  ring
 have hi := ((rate_power_integrable hb (s := s-1) (by linarith) hq.le).const_mul s).sub
   ((rate_power_integrable hb (s := s) (by linarith) hq.le).const_mul b)
 have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi
   (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb)
 rw [integral_sub ((rate_power_integrable hb (s := s-1) (by linarith) hq.le).const_mul s)
   ((rate_power_integrable hb (s := s) (by linarith) hq.le).const_mul b),
   integral_const_mul,integral_const_mul] at h
 change s*ratePowerTail b (s-1) q-b*ratePowerTail b s q=0-q^s*Real.exp (-b*q) at h
 field_simp [hb.ne']
 simp only [neg_mul] at h
 nlinarith only [h]

/-- Every literal power moment is given by the normalized gamma recurrence. -/
theorem ratePowerTail_eq_gRate (n : ℕ) {b q : ℝ} (hb : 0<b) (hq : 0<q) :
 ratePowerTail b ((n:ℝ)+3/2) q=rateBoundary b q*gRate b n q (rateGammaMass b q) := by
 induction n with
 | zero =>
   norm_num only [Nat.cast_zero,zero_add,gRate]
   exact ratePowerTail_mass hb hq
 | succ n ih =>
   have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
   rw [ratePowerTail_recurrence hb (by positivity) hq]
   have he : ((n+1:ℕ):ℝ)+3/2-1=(n:ℝ)+3/2 := by push_cast; ring
   rw [he,ih]
   have hp : q^(((n+1:ℕ):ℝ)+3/2)=q^(3/2:ℝ)*q^(n+1) := by
    rw [add_comm,Real.rpow_add hq,Real.rpow_natCast]
   rw [hp]
   simp only [gRate,rateBoundary,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
   ring

/-- A radial boundary times an integer power is the corresponding half-integer density. -/
theorem rateBoundary_mul_pow (b : ℝ) (n : ℕ) {t : ℝ} (ht : 0<t) :
 rateBoundary b t*t^n=t^((n:ℝ)+3/2)*Real.exp (-b*t) := by
 rw [add_comm (n:ℝ),Real.rpow_add ht,Real.rpow_natCast]
 unfold rateBoundary
 ring

/-- Polynomially weighted radial densities are integrable on positive rays. -/
theorem weighted_power_integrable {b q : ℝ} (hb : 0<b) (n : ℕ) (hq : 0<q) :
 IntegrableOn (fun t : ℝ => rateBoundary b t*t^n) (Ioi q) := by
 have hi := rate_power_integrable hb (s := (n:ℝ)+3/2)
   (by linarith only [show (0:ℝ)≤(n:ℝ) from Nat.cast_nonneg n]) hq.le
 exact hi.congr_fun (fun t ht => (rateBoundary_mul_pow b n (hq.trans ht)).symm) measurableSet_Ioi

/-- The integral of every polynomially weighted boundary is its exact recurrence moment. -/
theorem integral_rateBoundary_mul_pow {b q : ℝ} (hb : 0<b) (n : ℕ) (hq : 0<q) :
 (∫ t in Ioi q, rateBoundary b t*t^n)=rateBoundary b q*gRate b n q (rateGammaMass b q) := by
 rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => rateBoundary_mul_pow b n (hq.trans ht))]
 exact ratePowerTail_eq_gRate n hb hq

/-- Every rate can be measured relative to the first-atom boundary density. -/
theorem rateBoundary_relative (b q : ℝ) :
 rateBoundary b q=boundary q*Real.exp (-(b-2)*q) := by
 unfold rateBoundary boundary
 rw [mul_assoc,← Real.exp_add]
 congr 1
 congr 1
 ring

/-- Normalized moments depend affinely on the initial gamma mass. -/
theorem gRate_affine (b q a z t : ℝ) (n : ℕ) :
 gRate b n q ((1-t)*a+t*z)=(1-t)*gRate b n q a+t*gRate b n q z := by
 induction n with
 | zero => rfl
 | succ n ih => simp only [gRate,ih]; ring

private theorem exp_three_lower : (20 : ℝ)≤Real.exp 3 := by
 have h1 : (2718/1000:ℝ)≤Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
 have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) h1 3
 rw [← Real.exp_nat_mul] at hp
 norm_num at hp
 linarith only [hp]

/-- Beyond scale three, the exponential pays every power below its endpoint slope. -/
theorem exponential_polynomial_envelope (n d : ℕ) (hd : n≤3*d) {q : ℝ} (hq : 3≤q) :
 Real.exp (-(d:ℝ)*q)≤3^n/((20:ℝ)^d*q^n) := by
 have hq0 : 0<q := by linarith only [hq]
 have hd0 : (n:ℝ)≤3*d := by exact_mod_cast hd
 have ha : q/3≤Real.exp ((q-3)/3) := by
  convert Real.add_one_le_exp ((q-3)/3) using 1
  ring
 have hp := pow_le_pow_left₀ (show (0:ℝ)≤q/3 by positivity) ha n
 rw [← Real.exp_nat_mul] at hp
 have he : (n:ℝ)*((q-3)/3)≤(d:ℝ)*(q-3) := by
  have h := mul_nonneg (show (0:ℝ)≤(d:ℝ)-(n:ℝ)/3 by linarith only [hd0])
    (sub_nonneg.mpr hq)
  nlinarith only [h]
 have hp' : (q/3)^n≤Real.exp ((d:ℝ)*(q-3)) := hp.trans (Real.exp_le_exp.mpr he)
 have hh := mul_le_mul_of_nonneg_right hp' (Real.exp_pos (-(d:ℝ)*q)).le
 rw [← Real.exp_add] at hh
 have heq : (d:ℝ)*(q-3)+(-(d:ℝ)*q)= -((d:ℝ)*3) := by ring
 rw [heq,Real.exp_neg,Real.exp_nat_mul] at hh
 have hc := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤20) exp_three_lower d
 have hi : ((Real.exp 3)^d)⁻¹≤1/(20:ℝ)^d := by
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le (by positivity) hc
 have ht := hh.trans hi
 rw [div_pow] at ht
 apply (le_div_iff₀ (show 0<(20:ℝ)^d*q^n by positivity)).mpr
 have hr := (mul_le_mul_of_nonneg_left ht (show (0:ℝ)≤(3:ℝ)^n*(20:ℝ)^d by positivity))
 have hc0 : (20:ℝ)^d≠0 := by positivity
 field_simp [hc0] at hr
 simp only [neg_mul]
 nlinarith only [hr]

/-- Every remaining unequal-pair rate pays twenty powers on the scale-three ray. -/
theorem exponential_envelope (d : ℕ) (hd : 8≤d) {q : ℝ} (hq : 3≤q) :
 Real.exp (-(d:ℝ)*q)≤3^20/((20:ℝ)^d*q^20) :=
 exponential_polynomial_envelope 20 d (by omega) hq

/-- Normalized gamma moments increase with their initial mass. -/
theorem gRate_mono {b q a z : ℝ} (hb : 0<b) (n : ℕ) (haz : a≤z) :
 gRate b n q a≤gRate b n q z := by
 induction n with
 | zero => exact haz
 | succ n ih =>
   simp only [gRate]
   exact add_le_add le_rfl (mul_le_mul_of_nonneg_left ih
    (show (0:ℝ)≤((2*n+5:ℕ):ℝ)/(2*b) by positivity))

private def nineteenScaled (q : ℝ) : ℝ :=
 q^4/19+(7/38)*(q^3/19+(5/38)*(q^2/19+3*q/(2*19^2)+3/(4*19^3)))
private theorem nineteenScaled_eq {q : ℝ} (hq : q≠0) :
 q^2*gRate 19 2 q (zUpper 19 q)=nineteenScaled q := by
 simp only [gRate,zUpper,nineteenScaled]
 field_simp [hq]
 ring

/-- The second rate-nineteen moment fits its boundary square with denominator seventeen. -/
theorem rate_nineteen_second_le {q : ℝ} (hq : 3≤q) :
 gRate 19 2 q (rateGammaMass 19 q)≤q^2/17 := by
 have hq0 : 0<q := by linarith only [hq]
 have hU := (rateGammaMass_bounds (by norm_num : (0:ℝ)<19) hq0).2
 have h := mul_le_mul_of_nonneg_left (gRate_mono (q := q) (by norm_num : (0:ℝ)<19) 2 hU)
   (sq_nonneg q)
 rw [nineteenScaled_eq hq0.ne'] at h
 have hp : 0≤q^4/17-nineteenScaled q := by
  let y := q-3
  have hy : 0≤y := sub_nonneg.mpr hq
  have he : q=3+y := by dsimp [y]; ring
  rw [he]
  dsimp only [nineteenScaled]
  ring_nf
  positivity
 by_contra hbad
 have hpos := mul_pos (sq_pos_of_pos hq0)
   (sub_pos.mpr (lt_of_not_ge hbad))
 nlinarith only [h,hp,hpos]

/-- Half the cubic gamma reserve pays the fixed Cauchy majorant. -/
theorem remainder_reserve_scalar {q : ℝ} (hq : 3≤q) :
 (400000000/17:ℝ)*q^2*Real.exp (-17*q)≤
  (1/2)*(3/(32*q^2)-3/(128*q^3))*(1/100000000000) := by
 have hq0 : 0<q := by linarith only [hq]
 have he : Real.exp (-17*q)≤3^4/((20:ℝ)^17*q^4) := by
  simpa only [Nat.cast_ofNat] using exponential_polynomial_envelope 4 17 (by norm_num) hq
 calc
  _ ≤ (400000000/17:ℝ)*q^2*(3^4/((20:ℝ)^17*q^4)) :=
   mul_le_mul_of_nonneg_left he (by positivity)
  _ ≤ _ := by
   have e1 : q^3*((400000000/17:ℝ)*q^2*(3^4/((20:ℝ)^17*q^4)))=
     (400000000/17:ℝ)*(3^4/(20:ℝ)^17)*q := by
    field_simp [hq0.ne']
   have e2 : q^3*((1/2)*(3/(32*q^2)-3/(128*q^3))*(1/100000000000:ℝ))=
     (1/2)*(3*q/32-3/128)*(1/100000000000:ℝ) := by
    field_simp [hq0.ne']
   by_contra hbad
   have hpos := mul_pos (pow_pos hq0 3)
     (sub_pos.mpr (lt_of_not_ge hbad))
   rw [mul_sub,e1,e2] at hpos
   norm_num at hpos
   linarith only [hq,hpos]

end GaloisForLFunctions.ThetaCuspSections.FifthRateTail
