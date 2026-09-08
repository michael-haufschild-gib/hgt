import GaloisForLFunctions.RHTower.DivisorTwentyTwoAnalyticBounds
import GaloisForLFunctions.RHTower.MobiusDivisorCoupledTwoSourceCone

/-!
# An actual source circuit with positive inherited-debt covariance

The normalized source profiles at two, eleven and fifteen have a positive
zero-mean circuit whose quadratic covariance is strictly positive. Every
source sign and separation follows from analytic rational enclosures.
No numerical optimizer or experimental value enters this proof.
-/
noncomputable section
open Finset
namespace RHTower

/-- Actual two-coordinate source in the common parent square-root scale. -/
def mobiusDivisorNormalizedTwoProfile (K : ℕ) : ℝ × ℝ :=
  ((mobiusDivisorCoupledTwoProfile K).1/Real.sqrt K,
    (mobiusDivisorCoupledTwoProfile K).2/Real.sqrt K)

private lemma signed_prime (M p : ℕ) (hp : p.Prime) :
    mobiusDivisorDilationChannel M p = -divisorUnsignedDilationChannel M p := by
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,ArithmeticFunction.moebius_apply_prime hp]
  norm_num
private lemma signed_pair (M p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p≠q) :
    mobiusDivisorDilationChannel M (p*q) = divisorUnsignedDilationChannel M (p*q) := by
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (hp.coprime_iff_not_dvd.mpr
      (fun h => hne ((Nat.dvd_prime hq).mp h |>.resolve_left hp.ne_one))),
    ArithmeticFunction.moebius_apply_prime hp,ArithmeticFunction.moebius_apply_prime hq]
  norm_num
private lemma square_zero (M n p : ℕ) (hp : 1<p) (hd : p*p∣n) :
    mobiusDivisorDilationChannel M n=0 := by
  have hn : ¬Squarefree n := by
    intro h
    have he : p=1 := Nat.isUnit_iff.mp (h p hd)
    omega
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
  norm_num
private lemma terminal_zero (M : ℕ) (hM : 0<M) : mobiusDivisorDilationChannel M M=0 := by
  simp [mobiusDivisorDilationChannel,Icc_eq_empty_of_lt (by omega : M-1<M)]
private lemma signed_one (M : ℕ) : mobiusDivisorDilationChannel M 1=divisorUnsignedDilationChannel M 1 := by
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned]; norm_num

private lemma core_fibres {K : ℕ} (hK : K≤15) :
    mobiusDivisorSelectionFibre K mobiusDivisorCoupledTwoCore ∅=mobiusDivisorLastPrimeFree K 2 ∧
    mobiusDivisorSelectionFibre K mobiusDivisorCoupledTwoCore {2}=mobiusDivisorLastPrimeDivisible K 2 :=
  mobiusDivisorSelectionFibre_one_remaining K 2 _ Nat.prime_two
    (by simp [mobiusDivisorCoupledTwoCore]) (mobiusDivisorCoupledTwoCore_covers hK)

private lemma source_boxes :
    (-0.273 ≤ (mobiusDivisorCoupledTwoProfile 11).1 ∧ (mobiusDivisorCoupledTwoProfile 11).1 ≤ -0.271) ∧
    (-0.050 ≤ (mobiusDivisorCoupledTwoProfile 11).2 ∧ (mobiusDivisorCoupledTwoProfile 11).2 ≤ -0.047) ∧
    (-0.286 ≤ (mobiusDivisorCoupledTwoProfile 15).1 ∧ (mobiusDivisorCoupledTwoProfile 15).1 ≤ -0.283) ∧
    (0.055 ≤ (mobiusDivisorCoupledTwoProfile 15).2 ∧ (mobiusDivisorCoupledTwoProfile 15).2 ≤ 0.058) := by
  have hp7 : Nat.Prime 7 := by norm_num
  have hp11 : Nat.Prime 11 := by norm_num
  have hp13 : Nat.Prime 13 := by norm_num
  have s6 (M : ℕ) := signed_pair M 2 3 Nat.prime_two Nat.prime_three (by omega)
  have s10 (M : ℕ) := signed_pair M 2 5 Nat.prime_two Nat.prime_five (by omega)
  have s14 (M : ℕ) := signed_pair M 2 7 Nat.prime_two hp7 (by omega)
  norm_num only at s6 s10 s14
  have z4 (M : ℕ) := square_zero M 4 2 (by omega) (by norm_num)
  have z8 (M : ℕ) := square_zero M 8 2 (by omega) (by norm_num)
  have z9 (M : ℕ) := square_zero M 9 3 (by omega) (by norm_num)
  have z12 (M : ℕ) := square_zero M 12 2 (by omega) (by norm_num)
  dsimp only [mobiusDivisorCoupledTwoProfile]
  rw [(core_fibres (K:=11) (by omega)).1,(core_fibres (K:=11) (by omega)).2,
    (core_fibres (K:=15) (by omega)).1,(core_fibres (K:=15) (by omega)).2]
  norm_num [mobiusDivisorLastPrimeFree,mobiusDivisorLastPrimeDivisible,
    Finset.sum_filter,Finset.sum_Icc_succ_top,z4,z8,z9,z12,
    terminal_zero 11 (by omega),terminal_zero 15 (by omega),
    signed_one,s6,s10,s14,signed_prime 11 2 Nat.prime_two,signed_prime 11 3 Nat.prime_three,
    signed_prime 11 5 Nat.prime_five,signed_prime 11 7 hp7,
    signed_prime 15 2 Nat.prime_two,signed_prime 15 3 Nat.prime_three,
    signed_prime 15 5 Nat.prime_five,signed_prime 15 7 hp7,
    signed_prime 15 11 hp11,signed_prime 15 13 hp13]
  obtain ⟨h11a,h11b⟩ := divisorUnsignedDilationChannel_eleven_debt_profile_boxes
  obtain ⟨h15a,h15b⟩ := divisorUnsignedDilationChannel_fifteen_debt_profile_boxes
  constructor
  · constructor <;> linarith only [h11a.1,h11a.2]
  constructor
  · constructor <;> linarith only [h11b.1,h11b.2]
  constructor <;> constructor <;> linarith only [h15a.1,h15a.2,h15b.1,h15b.2]

/-- The actual normalized directions have the strict horizontal order needed for positive cycle covariance. -/
theorem mobiusDivisorNormalizedTwoProfile_debt_signs :
    0<(mobiusDivisorNormalizedTwoProfile 2).1 ∧ (mobiusDivisorNormalizedTwoProfile 2).2=0 ∧
    (mobiusDivisorNormalizedTwoProfile 11).1<(mobiusDivisorNormalizedTwoProfile 15).1 ∧
    (mobiusDivisorNormalizedTwoProfile 15).1<0 ∧
    (mobiusDivisorNormalizedTwoProfile 11).2<0 ∧ 0<(mobiusDivisorNormalizedTwoProfile 15).2 := by
  obtain ⟨ha,hb,hc,hd⟩ := source_boxes
  have hr2 : 0<Real.sqrt (2:ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hr11 : 0<Real.sqrt (11:ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hr15 : 0<Real.sqrt (15:ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hu : Real.sqrt (11:ℝ)≤10/3 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hl : (15/4:ℝ)≤Real.sqrt 15 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  dsimp only [mobiusDivisorNormalizedTwoProfile]
  norm_num only [Nat.cast_ofNat]
  refine ⟨div_pos mobiusDivisorCoupledTwoProfile_three_signs.1 hr2,?_,?_,?_,?_,?_⟩
  · rw [mobiusDivisorCoupledTwoProfile_three_signs.2.1,zero_div]
  · have hx : (mobiusDivisorCoupledTwoProfile 11).1/Real.sqrt 11<(-0.080:ℝ) := by
      rw [div_lt_iff₀ hr11]; linarith only [ha.2,hu]
    have hz : (-0.078:ℝ)<(mobiusDivisorCoupledTwoProfile 15).1/Real.sqrt 15 := by
      rw [lt_div_iff₀ hr15]; linarith only [hc.1,hl]
    linarith only [hx,hz]
  · exact div_neg_of_neg_of_pos (by linarith only [hc.2]) hr15
  · exact div_neg_of_neg_of_pos (by linarith only [hb.2]) hr11
  · exact div_pos (by linarith only [hd.1]) hr15

/-- A closed actual-source positive circuit balances both coordinates and has strictly positive inherited-debt covariance. -/
theorem exists_mobiusDivisorTwo_positive_debt_circuit :
    ∃ a b c : ℝ,0<a ∧ 0<b ∧ 0<c ∧ a+b+c=1 ∧
      a*(mobiusDivisorNormalizedTwoProfile 2).1+b*(mobiusDivisorNormalizedTwoProfile 11).1+
        c*(mobiusDivisorNormalizedTwoProfile 15).1=0 ∧
      a*(mobiusDivisorNormalizedTwoProfile 2).2+b*(mobiusDivisorNormalizedTwoProfile 11).2+
        c*(mobiusDivisorNormalizedTwoProfile 15).2=0 ∧
      0<a*2*(mobiusDivisorNormalizedTwoProfile 2).1*(mobiusDivisorNormalizedTwoProfile 2).2+
        b*2*(mobiusDivisorNormalizedTwoProfile 11).1*(mobiusDivisorNormalizedTwoProfile 11).2+
        c*2*(mobiusDivisorNormalizedTwoProfile 15).1*(mobiusDivisorNormalizedTwoProfile 15).2 := by
  obtain ⟨hA,hzero,hxz,hz,hy,hw⟩ := mobiusDivisorNormalizedTwoProfile_debt_signs
  let A := (mobiusDivisorNormalizedTwoProfile 2).1
  let x := (mobiusDivisorNormalizedTwoProfile 11).1
  let y := (mobiusDivisorNormalizedTwoProfile 11).2
  let z := (mobiusDivisorNormalizedTwoProfile 15).1
  let w := (mobiusDivisorNormalizedTwoProfile 15).2
  change 0<A at hA
  change x<z at hxz
  change z<0 at hz
  change y<0 at hy
  change 0<w at hw
  let a := (z*y-x*w)/A
  let t := a+w-y
  have hxy : x<0 := hxz.trans hz
  have ha : 0<a := div_pos (by
    have h1 := mul_pos_of_neg_of_neg hz hy
    have h2 := mul_neg_of_neg_of_pos hxy hw
    linarith only [h1,h2]) hA
  have ht : 0<t := by dsimp only [t]; linarith only [ha,hw,hy]
  have hbalance : a*A+w*x-y*z=0 := by
    dsimp only [a]
    field_simp [ne_of_gt hA]; ring
  have hcov : 0<2*y*w*(x-z) := by
    exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (by linarith only [hy]) hw)
      (sub_neg.mpr hxz)
  refine ⟨a/t,w/t,-y/t,div_pos ha ht,div_pos hw ht,div_pos (neg_pos.mpr hy) ht,?_,?_,?_,?_⟩
  · calc
      a/t+w/t+ -y/t=(a+w-y)/t := by ring
      _=1 := div_self (ne_of_gt ht)
  · change a/t*A+w/t*x+(-y/t)*z=0
    calc
      a/t*A+w/t*x+(-y/t)*z=(a*A+w*x-y*z)/t := by ring
      _=0 := by rw [hbalance,zero_div]
  · rw [hzero]
    change a/t*0+w/t*y+(-y/t)*w=0
    ring
  · rw [hzero]
    change 0<a/t*2*A*0+w/t*2*x*y+(-y/t)*2*z*w
    have he : a/t*2*A*0+w/t*2*x*y+(-y/t)*2*z*w=(2*y*w*(x-z))/t := by ring
    rw [he]
    exact div_pos hcov ht

/-- Clipped source normalized by its exact interpolated square-root clock. -/
def mobiusDivisorNormalizedTwoClip (K : ℕ) (u : ℝ) : ℝ × ℝ :=
  ((mobiusDivisorCoupledTwoInterpolatedProfile K u).1 /
    (Real.sqrt K+u*(Real.sqrt (K+1:ℕ)-Real.sqrt K)),
   (mobiusDivisorCoupledTwoInterpolatedProfile K u).2 /
    (Real.sqrt K+u*(Real.sqrt (K+1:ℕ)-Real.sqrt K)))

private lemma clip_zero (K : ℕ) : mobiusDivisorNormalizedTwoClip K 0=mobiusDivisorNormalizedTwoProfile K := by
  simp [mobiusDivisorNormalizedTwoClip,mobiusDivisorCoupledTwoInterpolatedProfile,
    mobiusDivisorNormalizedTwoProfile]

private def debtCross (u v : ℝ × ℝ) : ℝ := u.1*v.2-v.1*u.2
private def debtCovariance (u v w : ℝ × ℝ) : ℝ :=
  debtCross w v*2*u.1*u.2+debtCross u w*2*v.1*v.2+debtCross v u*2*w.1*w.2

private lemma circuit_of_cross (u v w : ℝ × ℝ)
    (h0 : 0<debtCross w v) (h1 : 0<debtCross u w) (h2 : 0<debtCross v u)
    (hcov : 0<debtCovariance u v w) :
    ∃ a b c : ℝ,0<a ∧ 0<b ∧ 0<c ∧ a+b+c=1 ∧
      a*u.1+b*v.1+c*w.1=0 ∧ a*u.2+b*v.2+c*w.2=0 ∧
      0<a*2*u.1*u.2+b*2*v.1*v.2+c*2*w.1*w.2 := by
  let t := debtCross w v+debtCross u w+debtCross v u
  have ht : 0<t := by dsimp only [t]; positivity
  refine ⟨debtCross w v/t,debtCross u w/t,debtCross v u/t,
    div_pos h0 ht,div_pos h1 ht,div_pos h2 ht,?_,?_,?_,?_⟩
  · calc
      _=t/t := by dsimp only [t]; ring
      _=1 := div_self ht.ne'
  · dsimp only [debtCross]; ring
  · dsimp only [debtCross]; ring
  · have he : debtCross w v/t*2*u.1*u.2+debtCross u w/t*2*v.1*v.2+
        debtCross v u/t*2*w.1*w.2=debtCovariance u v w/t := by
      dsimp only [debtCovariance]; ring
    rw [he]
    exact div_pos hcov ht

private lemma source_cross_signs :
    0<debtCross (mobiusDivisorNormalizedTwoProfile 15) (mobiusDivisorNormalizedTwoProfile 11) ∧
    0<debtCross (mobiusDivisorNormalizedTwoProfile 2) (mobiusDivisorNormalizedTwoProfile 15) ∧
    0<debtCross (mobiusDivisorNormalizedTwoProfile 11) (mobiusDivisorNormalizedTwoProfile 2) ∧
    0<debtCovariance (mobiusDivisorNormalizedTwoProfile 2)
      (mobiusDivisorNormalizedTwoProfile 11) (mobiusDivisorNormalizedTwoProfile 15) := by
  obtain ⟨hA,hzero,hxz,hz,hy,hw⟩ := mobiusDivisorNormalizedTwoProfile_debt_signs
  have hx := hxz.trans hz
  have hxy := mul_pos_of_neg_of_neg hz hy
  have hxw := mul_neg_of_neg_of_pos hx hw
  refine ⟨by dsimp only [debtCross]; linarith only [hxy,hxw],?_,?_,?_⟩
  · dsimp only [debtCross]; rw [hzero,mul_zero,sub_zero]; exact mul_pos hA hw
  · dsimp only [debtCross]; rw [hzero,mul_zero,zero_sub]
    exact neg_pos.mpr (mul_neg_of_pos_of_neg hA hy)
  · have he : debtCovariance (mobiusDivisorNormalizedTwoProfile 2)
        (mobiusDivisorNormalizedTwoProfile 11) (mobiusDivisorNormalizedTwoProfile 15)=
        (mobiusDivisorNormalizedTwoProfile 2).1*
          (2*(mobiusDivisorNormalizedTwoProfile 11).2*(mobiusDivisorNormalizedTwoProfile 15).2*
            ((mobiusDivisorNormalizedTwoProfile 11).1-(mobiusDivisorNormalizedTwoProfile 15).1)) := by
      dsimp only [debtCovariance,debtCross]; rw [hzero]; ring
    rw [he]
    exact mul_pos hA (mul_pos_of_neg_of_neg
      (mul_neg_of_neg_of_pos (by linarith only [hy]) hw) (sub_neg.mpr hxz))

private lemma clip_continuousAt_zero (K : ℕ) (hK : 0<K) :
    ContinuousAt (mobiusDivisorNormalizedTwoClip K) 0 := by
  have hd : ContinuousAt (fun u : ℝ => Real.sqrt K+u*(Real.sqrt (K+1:ℕ)-Real.sqrt K)) 0 := by fun_prop
  have hn : Real.sqrt K+(0:ℝ)*(Real.sqrt (K+1:ℕ)-Real.sqrt K)≠0 := by
    simpa using (Real.sqrt_pos.2 (show 0<(K:ℝ) by exact_mod_cast hK)).ne'
  have h0 : ContinuousAt (fun u : ℝ => (mobiusDivisorCoupledTwoInterpolatedProfile K u).1) 0 := by
    dsimp [mobiusDivisorCoupledTwoInterpolatedProfile]; fun_prop
  have h1 : ContinuousAt (fun u : ℝ => (mobiusDivisorCoupledTwoInterpolatedProfile K u).2) 0 := by
    dsimp [mobiusDivisorCoupledTwoInterpolatedProfile]; fun_prop
  exact (h0.div hd hn).prodMk (h1.div hd hn)

open Filter Topology in
/-- Independent small clipping preserves a positive debt-removing source circuit at the exact physical clock. -/
theorem exists_mobiusDivisorTwo_clipped_positive_debt_circuit :
    ∃ ε : ℝ,0<ε ∧ ∀ u v w : ℝ,|u|<ε → |v|<ε → |w|<ε →
      ∃ a b c : ℝ,0<a ∧ 0<b ∧ 0<c ∧ a+b+c=1 ∧
        a*(mobiusDivisorNormalizedTwoClip 2 u).1+b*(mobiusDivisorNormalizedTwoClip 11 v).1+
          c*(mobiusDivisorNormalizedTwoClip 15 w).1=0 ∧
        a*(mobiusDivisorNormalizedTwoClip 2 u).2+b*(mobiusDivisorNormalizedTwoClip 11 v).2+
          c*(mobiusDivisorNormalizedTwoClip 15 w).2=0 ∧
        0<a*2*(mobiusDivisorNormalizedTwoClip 2 u).1*(mobiusDivisorNormalizedTwoClip 2 u).2+
          b*2*(mobiusDivisorNormalizedTwoClip 11 v).1*(mobiusDivisorNormalizedTwoClip 11 v).2+
          c*2*(mobiusDivisorNormalizedTwoClip 15 w).1*(mobiusDivisorNormalizedTwoClip 15 w).2 := by
  let U := fun t : ℝ × ℝ × ℝ => mobiusDivisorNormalizedTwoClip 2 t.1
  let V := fun t : ℝ × ℝ × ℝ => mobiusDivisorNormalizedTwoClip 11 t.2.1
  let W := fun t : ℝ × ℝ × ℝ => mobiusDivisorNormalizedTwoClip 15 t.2.2
  have hU : ContinuousAt U 0 := (clip_continuousAt_zero 2 (by omega)).comp_of_eq
    (show ContinuousAt (fun t : ℝ × ℝ × ℝ => t.1) 0 from continuousAt_fst) rfl
  have hV : ContinuousAt V 0 := (clip_continuousAt_zero 11 (by omega)).comp_of_eq
    (show ContinuousAt (fun t : ℝ × ℝ × ℝ => t.2.1) 0 from continuousAt_snd.fst) rfl
  have hW : ContinuousAt W 0 := (clip_continuousAt_zero 15 (by omega)).comp_of_eq
    (show ContinuousAt (fun t : ℝ × ℝ × ℝ => t.2.2) 0 from continuousAt_snd.snd) rfl
  let D0 := fun t => debtCross (W t) (V t)
  let D1 := fun t => debtCross (U t) (W t)
  let D2 := fun t => debtCross (V t) (U t)
  let C := fun t => debtCovariance (U t) (V t) (W t)
  have hd0 : ContinuousAt D0 0 := (hW.fst.mul hV.snd).sub (hV.fst.mul hW.snd)
  have hd1 : ContinuousAt D1 0 := (hU.fst.mul hW.snd).sub (hW.fst.mul hU.snd)
  have hd2 : ContinuousAt D2 0 := (hV.fst.mul hU.snd).sub (hU.fst.mul hV.snd)
  have hc : ContinuousAt C 0 :=
    (((hd0.mul continuousAt_const).mul hU.fst).mul hU.snd).add
      (((hd1.mul continuousAt_const).mul hV.fst).mul hV.snd) |>.add
      (((hd2.mul continuousAt_const).mul hW.fst).mul hW.snd)
  have hbase : 0<D0 0 ∧ 0<D1 0 ∧ 0<D2 0 ∧ 0<C 0 := by
    simpa only [D0,D1,D2,C,U,V,W,Prod.fst_zero,Prod.snd_zero,clip_zero] using source_cross_signs
  have he := (hd0.eventually (eventually_gt_nhds hbase.1)).and
    ((hd1.eventually (eventually_gt_nhds hbase.2.1)).and
      ((hd2.eventually (eventually_gt_nhds hbase.2.2.1)).and
        (hc.eventually (eventually_gt_nhds hbase.2.2.2))))
  obtain ⟨ε,hε,hnear⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨ε,hε,?_⟩
  intro u v w hu hv hw
  have hdist : dist (u,v,w) (0 : ℝ × ℝ × ℝ)<ε := by
    rw [dist_eq_norm,sub_zero,Prod.norm_def,Prod.norm_def]
    simpa only [Real.norm_eq_abs,max_lt_iff] using And.intro hu (And.intro hv hw)
  obtain ⟨ha,hb,hc,hd⟩ := hnear hdist
  exact circuit_of_cross (U (u,v,w)) (V (u,v,w)) (W (u,v,w)) ha hb hc hd

/-- The normalized clipped profile is exactly the copied child divided by the parent square-root scale. -/
theorem mobiusDivisorNormalizedTwoClip_eq_physical (M p : ℕ) (hp : 0<p) (hM : 0<M) :
    mobiusDivisorNormalizedTwoClip (M/p) (divisorPrimeClipWeight M p)=
      (Real.sqrt p*mobiusDivisorInterpolatedFibre M p mobiusDivisorCoupledTwoCore ∅/Real.sqrt M,
       Real.sqrt p*mobiusDivisorInterpolatedFibre M p mobiusDivisorCoupledTwoCore {2}/Real.sqrt M) := by
  let d := Real.sqrt (M/p:ℕ)+divisorPrimeClipWeight M p*
    (Real.sqrt (M/p+1:ℕ)-Real.sqrt (M/p:ℕ))
  have hs := divisorPrimeClipWeight_mul_step M p hp
  push_cast at hs
  rw [Real.sqrt_mul (Nat.cast_nonneg p)] at hs
  have he : Real.sqrt p*d=Real.sqrt M := by dsimp only [d]; push_cast; nlinarith only [hs]
  have hp0 : 0<Real.sqrt (p:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hp)
  have hM0 : 0<Real.sqrt (M:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hM)
  have hd : d≠0 := by intro hz; rw [hz,mul_zero] at he; exact hM0.ne' he.symm
  have hdiv (x : ℝ) : x/d=Real.sqrt p*x/Real.sqrt M := by
    rw [← he]
    field_simp
  apply Prod.ext
  all_goals dsimp [mobiusDivisorNormalizedTwoClip,mobiusDivisorCoupledTwoInterpolatedProfile,
    mobiusDivisorCoupledTwoProfile]
  all_goals change (_+_*(_-_))/d=_
  all_goals rw [hdiv]
  all_goals dsimp only [mobiusDivisorInterpolatedFibre]
  all_goals ring
end RHTower
