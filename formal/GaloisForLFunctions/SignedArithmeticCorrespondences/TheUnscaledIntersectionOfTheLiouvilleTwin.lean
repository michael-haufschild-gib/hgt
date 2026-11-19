import GaloisForLFunctions.SignedArithmeticCorrespondences.PowerContactsAndTheirOppositeDegrees
import GaloisForLFunctions.SignedArithmeticCorrespondences.ThePoleDefectOfFullIntegralPrefixes
import GaloisForLFunctions.SelectiveArithmetic.TheLiouvilleTwistFailsBeyondTheTrivialAperture

/-!
# The surviving intersection of the Liouville twin

Adding the twisted and ordinary graph contacts before taking a limit retains
all even exponents. Their opposite degrees both vanish, so the surviving
constant is a product of untwisted masses. There is no separation factor.
On the same integral prefixes the divisor column reads the squarefree
part of the conductor. It produces opposite curvature signs on either
side of every square.
-/

noncomputable section

namespace GaloisForLFunctions.SignedArithmeticCorrespondences

open Filter Topology MeasureTheory Finset _root_.RHTower
open scoped ArithmeticFunction.vonMangoldt

private theorem contact_summable (w : ℕ → ℝ) {f g : ℝ → ℝ}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (s : ℝ) :
    Summable (fun n : ℕ => (2*w n/Real.sqrt n) *
      ∫ u : ℝ, f u * g (u+(Real.log n-s))) := by
  obtain ⟨l,hl⟩ := hf.bddBelow
  obtain ⟨b,hb⟩ := hg.bddAbove
  let B := ⌈Real.exp (b-l+s)⌉₊
  apply summable_of_ne_finset_zero (s := Finset.range (B+1))
  intro n hn
  have hn' : B < n := by simpa only [Finset.mem_range, not_lt, Nat.succ_le_iff] using hn
  have he : Real.exp (b-l+s) < n := (Nat.le_ceil _).trans_lt (Nat.cast_lt.mpr hn')
  have hlog := Real.log_lt_log (Real.exp_pos _) he
  rw [Real.log_exp] at hlog
  have hz (u : ℝ) : f u * g (u+(Real.log n-s)) = 0 := by
    by_cases hu : f u = 0
    · rw [hu,zero_mul]
    apply mul_eq_zero_of_right
    by_contra h
    linarith only [hl (subset_tsupport f hu), hb (subset_tsupport g h), hlog]
  simp only [hz,integral_zero,mul_zero]

/-- Exact mixed graph height surviving the contact sign twist at every separation. -/
theorem contact_add_liouville (f g : ℝ → ℝ) (hf : HasCompactSupport f)
    (hg : HasCompactSupport g) (t : ℝ) :
    contact (fun n => Λ n) f g t + contact SelectiveArithmetic.liouvilleWeight f g t =
      2 * contact (powerWeight 2) f g t := by
  classical
  unfold contact
  rw [← (contact_summable _ hf hg t).tsum_add (contact_summable _ hf hg t), ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hs : (∃ k : ℕ, k^2 = n) ↔ IsSquare n := by
    constructor
    · rintro ⟨k,rfl⟩
      exact ⟨k,sq k⟩
    · rintro ⟨k,rfl⟩
      exact ⟨k,sq k⟩
  simp only [powerWeight, hs, SelectiveArithmetic.liouvilleWeight]
  by_cases hn : IsSquare n <;> simp only [hn,if_true,if_false] <;> ring

/-- The two contacts, each measured with its original sign and normalization,
have an unscaled mixed limit. It vanishes precisely when one profile has mass zero. -/
theorem tendsto_contact_add_liouville {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    Tendsto (fun t : ℝ => contact (fun n => Λ n) f g t +
      contact SelectiveArithmetic.liouvilleWeight f g t) atTop
      (𝓝 (2*(∫ u : ℝ, f u)*(∫ v : ℝ, g v))) := by
  have h := (tendsto_power_contact (2 : ℕ+) hf hg hfc hgc).const_mul 2
  simp only [contact_add_liouville f g hfc hgc]
  convert h using 1 <;>
    norm_num [ccmRealExponentialMoment, ccmRealExponentialTilt, mul_assoc]

private theorem first_power_weight : powerWeight 1 = fun n => Λ n := by
  funext n
  simp [powerWeight]

private theorem ordinary_contact_limit {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    Tendsto (fun t : ℝ => Real.exp (-(1/2)*t) * contact (fun n => Λ n) f g t)
      atTop (𝓝 (2*ccmRealExponentialMoment (-(1/2)) f * ccmRealExponentialMoment (1/2) g)) := by
  convert tendsto_power_contact (1 : ℕ+) hf hg hfc hgc using 1 <;> norm_num [first_power_weight]

/-- Keeping the ordinary pole normalization on the sign twin reverses both
profiles' leading cross term. Its discrepancy is present already at order √X. -/
theorem tendsto_liouville_contact {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    Tendsto (fun t : ℝ => Real.exp (-(1/2)*t) * contact SelectiveArithmetic.liouvilleWeight f g t)
      atTop (𝓝 (-(2*ccmRealExponentialMoment (-(1/2)) f * ccmRealExponentialMoment (1/2) g))) := by
  have hone := ordinary_contact_limit hf hg hfc hgc
  have hdec : Tendsto (fun t : ℝ => Real.exp (-(1/2)*t)) atTop (𝓝 0) := by
    simpa only [neg_mul,Function.comp_def,id_eq] using Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ)<1/2) tendsto_id))
  have h := (hdec.mul (tendsto_contact_add_liouville hf hg hfc hgc)).sub hone
  rw [zero_mul,zero_sub] at h
  exact h.congr fun t => by ring

/-- A single fixed pair of smooth compact divisors separates the signs at
every sufficiently large displacement. Opposite tilts of a positive bump
make both pole degrees equal to its ordinary mass. -/
theorem exists_eventually_opposite_contacts :
    ∃ f g : ℝ → ℝ, ContDiff ℝ 2 f ∧ ContDiff ℝ 2 g ∧ HasCompactSupport f ∧ HasCompactSupport g ∧
      ∀ᶠ t : ℝ in atTop, 0 < contact (fun n => Λ n) f g t ∧
        contact SelectiveArithmetic.liouvilleWeight f g t < 0 := by
  let φ : ContDiffBump (0 : ℝ) := ⟨1/2,1,by norm_num,by norm_num⟩
  let F (a x : ℝ) := φ x * Real.exp (a*x)
  have hF (a : ℝ) : ContDiff ℝ 2 (F a) :=
    φ.contDiff.mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  have hK (a : ℝ) : HasCompactSupport (F a) := φ.hasCompactSupport.mul_right
  have hM (a : ℝ) : ccmRealExponentialMoment (-a) (F a) = ∫ x : ℝ, φ x := by
    unfold ccmRealExponentialMoment ccmRealExponentialTilt
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change φ x*Real.exp (a*x)*Real.exp (-a*x) = φ x
      rw [mul_assoc,← Real.exp_add,show a*x + -a*x=0 by ring,Real.exp_zero,mul_one]
  let a : ℝ := 1/2
  have hp : 0 < 2*ccmRealExponentialMoment (-a) (F a)*ccmRealExponentialMoment a (F (-a)) := by
    have hm := hM (-a)
    rw [neg_neg] at hm
    rw [hM a,hm]
    exact mul_pos (mul_pos (by norm_num) φ.integral_pos) φ.integral_pos
  have ht := tendsto_liouville_contact (hF a) (hF (-a)) (hK a) (hK (-a))
  have ho' : Tendsto (fun t : ℝ => Real.exp (-a*t)*contact (fun n => Λ n) (F a) (F (-a)) t)
      atTop (𝓝 (2*ccmRealExponentialMoment (-a) (F a)*ccmRealExponentialMoment a (F (-a)))) :=
    ordinary_contact_limit (hF a) (hF (-a)) (hK a) (hK (-a))
  refine ⟨F a,F (-a),hF a,hF (-a),hK a,hK (-a),?_⟩
  filter_upwards [ho'.eventually_const_lt hp, ht.eventually_lt_const (neg_neg_of_pos hp)] with t h₁ h₂
  exact ⟨(mul_pos_iff_of_pos_left (Real.exp_pos _)).mp h₁,
    neg_of_mul_neg_right h₂ (Real.exp_pos _).le⟩

#print axioms contact_add_liouville
#print axioms tendsto_contact_add_liouville
#print axioms tendsto_liouville_contact
#print axioms exists_eventually_opposite_contacts

/-- Twisted logarithmic column of all graph pairs ending at m. Each
divisor q gives the pair with lower degree m/q and contact ratio q. -/
def twistedColumn (m : ℕ) : ℝ := ∑ q ∈ m.divisors, SelectiveArithmetic.liouvilleWeight q

private theorem square_dvd_column {a b c : ℕ} (ha : Squarefree a) (hb : 0<b) :
    c^2 ∣ b^2*a ↔ c ∣ b := by
  constructor
  · intro h
    have hn := Nat.mul_ne_zero (pow_ne_zero 2 hb.ne') ha.ne_zero
    have hc : c≠0 := by rintro rfl; simp [hn] at h
    apply (Nat.factorization_le_iff_dvd hc hb.ne').mp
    intro p
    have hp := (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hc) hn).mpr h p
    rw [Nat.factorization_mul (pow_ne_zero 2 hb.ne') ha.ne_zero,Nat.factorization_pow,Nat.factorization_pow] at hp
    simp only [two_nsmul,Finsupp.add_apply] at hp
    have h₁ := ha.natFactorization_le_one p
    omega
  · rintro ⟨r,rfl⟩
    exact ⟨r^2*a,by ring⟩

/-- For every squarefree decomposition m=b²a, the entire twisted column
is minus log a. In particular it vanishes on squares. -/
theorem twistedColumn_squarefree_part {a b : ℕ} (ha : Squarefree a) (hb : 0<b) :
    twistedColumn (b^2*a) = -Real.log a := by
  classical
  let m := b^2*a
  have hn : m≠0 := Nat.mul_ne_zero (pow_ne_zero 2 hb.ne') ha.ne_zero
  have he : m.divisors.filter IsSquare = b.divisors.image (fun c : ℕ => c^2) := by
    ext q
    constructor
    · intro h
      obtain ⟨hmem,c,hq⟩ := mem_filter.mp h
      have hc : q=c^2 := hq.trans (sq c).symm
      have hdiv := (Nat.mem_divisors.mp hmem).1
      rw [hc] at hdiv
      exact mem_image.mpr ⟨c,Nat.mem_divisors.mpr ⟨(square_dvd_column ha hb).mp hdiv,hb.ne'⟩,hc.symm⟩
    · rintro h
      obtain ⟨c,hc,rfl⟩ := mem_image.mp h
      exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨(square_dvd_column ha hb).mpr (Nat.mem_divisors.mp hc).1,hn⟩,
        c,sq c⟩
  have hs : (∑ q ∈ m.divisors, if IsSquare q then Λ q else 0) = Real.log b := by
    rw [← sum_filter,he,sum_image (fun c _ d _ h => (pow_left_inj₀ (Nat.zero_le c) (Nat.zero_le d) (by norm_num : 2≠0)).mp h)]
    simpa only [ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : 2≠0)] using
      (ArithmeticFunction.vonMangoldt_sum (n := b))
  have hc (q : ℕ) : SelectiveArithmetic.liouvilleWeight q =
      2*(if IsSquare q then Λ q else 0) - Λ q := by
    by_cases h : IsSquare q <;> simp [SelectiveArithmetic.liouvilleWeight,h]
    ring
  change (∑ q ∈ m.divisors, SelectiveArithmetic.liouvilleWeight q) = _
  simp only [hc,sum_sub_distrib,← mul_sum,hs,ArithmeticFunction.vonMangoldt_sum]
  rw [show (m:ℝ)=(b:ℝ)^2*(a:ℝ) by simp [m],Real.log_mul (by positivity) (Nat.cast_ne_zero.mpr ha.ne_zero),Real.log_pow]
  ring

private theorem nonsquare_column {m : ℕ} (hm : 0 < m) (hs : ¬IsSquare m) :
    twistedColumn m ≤ -Real.log 2 := by
  obtain ⟨a,b,ha,hb,h,hsf⟩ := Nat.sq_mul_squarefree_of_pos hm
  have ha₂ : 2≤a := by
    by_contra hw
    have ha₁ : a=1 := by omega
    rw [ha₁,mul_one] at h
    exact hs ⟨b,h.symm.trans (sq b)⟩
  rw [← h,twistedColumn_squarefree_part hsf hb,neg_le_neg_iff]
  exact Real.log_le_log (by norm_num) (by exact_mod_cast ha₂)

/-- Replace only the finite-place columns by their Liouville twists;
the effective prefixes and their pole products are identical at both signs. -/
def twistedPrefixPoleDefect (m : ℕ) : ℝ :=
  poleProduct m m (fun _ => 1) (fun j => if j=m then 1 else 0) -
    ∑ j ∈ Icc 1 m, twistedColumn j

private theorem twistedPrefixPoleDefect_eq (m : ℕ) :
    twistedPrefixPoleDefect m = prefixPoleDefect m + ∑ j ∈ Icc 1 m, (Real.log j-twistedColumn j) := by
  rw [twistedPrefixPoleDefect,prefixPoleDefect,prefixHeight_eq_sum_log,sum_sub_distrib]
  ring

def twistedPrefixCurvature (m : ℕ) : ℝ :=
  twistedPrefixPoleDefect (m+2)-2*twistedPrefixPoleDefect (m+1)+twistedPrefixPoleDefect m

private theorem twin_curvature (m : ℕ) :
    twistedPrefixCurvature m = 1/((m:ℝ)+1)+twistedColumn (m+1)-twistedColumn (m+2) := by
  have h := prefix_curvature_entry m
  unfold prefixDefectCurvature at h
  simp only [twistedPrefixCurvature,twistedPrefixPoleDefect_eq,
    sum_Icc_succ_top (Nat.succ_pos (m+1)),sum_Icc_succ_top (Nat.succ_pos m),
    Nat.cast_succ,show (m:ℝ)+1+1=m+2 by ring]
  linarith only [h]

private theorem nonsquare_between {l m : ℕ} (hl : l^2 < m) (hu : m<(l+1)^2) : ¬ IsSquare m := by
  rintro ⟨r,hr⟩
  have he : m=r^2 := hr.trans (sq r).symm
  rw [he] at hl hu
  rcases le_or_gt r l with h | h
  · exact hl.not_ge (Nat.pow_le_pow_left h 2)
  · exact hu.not_ge (Nat.pow_le_pow_left h 2)

/-- The same quadratic-form sign that holds for ordinary pole defects
fails at every square boundary of the twin. One adjacent curvature stays
above log 2 and the other is negative by at least one third. -/
theorem opposite_twin_curvatures_at_squares (k : ℕ) :
    let t := k+2
    Real.log 2 ≤ twistedPrefixCurvature (t^2-1) ∧ twistedPrefixCurvature (t^2-2) ≤ -(1/3) := by
  intro t
  have ht : 2≤t := by dsimp only [t]; omega
  have ht₂ : 4≤t^2 := by simpa using Nat.pow_le_pow_left ht 2
  have hz : twistedColumn (t^2) = 0 := by
    simpa using twistedColumn_squarefree_part (a := 1) (b := t) squarefree_one (by omega)
  have hp := nonsquare_column (m := t^2+1) (by omega)
    (nonsquare_between (l := t) (by omega) (by nlinarith only [ht]))
  have hsq : (k+1)^2 < t^2-1 := by
    change (k+1)^2 < (k+2)^2-1
    rw [show (k+2)^2=(k+1)^2+(2*k+3) by ring]
    omega
  have hm := nonsquare_column (m := t^2-1) (by omega)
    (nonsquare_between (l := k+1) hsq (by change t^2-1<t^2; omega))
  have hp' := twin_curvature (t^2-1)
  have hm' := twin_curvature (t^2-2)
  rw [show t^2-1+1=t^2 by omega,show t^2-1+2=t^2+1 by omega,hz] at hp'
  rw [show t^2-2+1=t^2-1 by omega,show t^2-2+2=t^2 by omega,hz] at hm'
  have hlog : 2/3 ≤ Real.log 2 := by
    convert HTGeometry.two_mul_sub_one_div_add_one_le_log (by norm_num : (1:ℝ)≤2) using 1
    norm_num
  have hden : (3:ℝ)≤((t^2-2:ℕ):ℝ)+1 := by exact_mod_cast (show 3≤t^2-2+1 by omega)
  have hsmall := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<3) hden
  constructor
  · linarith only [hp',hp,show 0≤1/(((t^2-1:ℕ):ℝ)+1) by positivity]
  · linarith only [hm',hm,hsmall,hlog]

#print axioms twistedColumn_squarefree_part
#print axioms opposite_twin_curvatures_at_squares

end GaloisForLFunctions.SignedArithmeticCorrespondences
