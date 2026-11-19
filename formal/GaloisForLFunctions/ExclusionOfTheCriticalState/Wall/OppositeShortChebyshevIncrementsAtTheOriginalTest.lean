import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.CompensatingFactorialPrimeIntervalsAtConsecutiveNumerators
import GaloisForLFunctions.RHTower.PsiWindowUpperBound
import GaloisForLFunctions.RHTower.ShortWindowNoGo

/-!
# Opposite short Chebyshev increments on the same signed test

The square roots of the widths of the odd quotient intervals have a harmonic
sum. Cutting each interval into short pieces therefore converts both signed
factorial discrepancies into unweighted increments of the prime sum.
-/

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry _root_.RHTower

/-- On a single ordinary-prime interval every integer has the same odd
quotient throughout the block. The mesh controls the relative interval width. -/
def HasShortThetaIncrement (M H P : ℕ) (S : Finset ℕ) (s B : ℝ) : Prop :=
  ∃ u v q : ℕ, u<v ∧ Finset.Ioc u v ⊆ S ∧ q%2=1 ∧
    (∀ j ∈ Finset.Icc M H, ∀ n ∈ Finset.Ioc u v, j/n=q) ∧
    P*(v-u-1)≤v ∧ B*Real.sqrt (v-u:ℕ) <
      s*(Chebyshev.theta v-Chebyshev.theta u-(v-u:ℕ))

private theorem theta_increment {u v : ℕ} (h : u≤v) :
    (∑ n ∈ Finset.Ioc u v, ordinaryPrimeExcessCoeff n)=
      Chebyshev.theta v-Chebyshev.theta u-(v-u:ℕ) := by
  simp only [ordinaryPrimeExcessCoeff,Finset.sum_sub_distrib,← Finset.sum_filter,
    ← theta_window_eq h,Finset.sum_const,Nat.card_Ioc,nsmul_eq_mul,mul_one]

/-- A quotient interval has length at most its first integer and
square-root length at most twice the square root of the numerator divided by the quotient. -/
private theorem quotient_width {U V H q : ℕ} (huv : U<V) (hq : 0<q)
    (hl : H/(U+1)=q) (hr : H/V=q) (hroot : Real.sqrt H<V) :
    V-U≤U+1 ∧ Real.sqrt (V-U:ℕ) ≤ 2*Real.sqrt H*(1/(q:ℝ)) := by
  have hv := Nat.mul_div_le H V
  rw [hr] at hv
  have hu := Nat.lt_mul_div_succ H (Nat.zero_lt_succ U)
  change H<(U+1)*(H/(U+1)+1) at hu
  rw [hl,Nat.mul_add,Nat.mul_one] at hu
  have hv' : (U+1)*q+(V-(U+1))*q≤H := by
    rw [← Nat.add_mul,show U+1+(V-(U+1))=V by omega]; exact hv
  have hdiff : (V-(U+1))*q<U+1 := Nat.lt_of_add_lt_add_left (hv'.trans_lt hu)
  have hsub : V-(U+1)≤(V-(U+1))*q := Nat.le_mul_of_pos_right _ hq
  have hsq := (Real.sqrt_lt' (Nat.cast_pos.mpr (Nat.zero_lt_of_lt huv))).mp hroot
  have hVV : H<V*V := by simpa only [sq] using (by exact_mod_cast hsq : H<V^2)
  have hqV : q<V := lt_of_not_ge fun h => (not_le_of_gt hVV) ((Nat.mul_le_mul_left V h).trans hv)
  have hqq : q*q≤H := (Nat.mul_le_mul_right q hqV.le).trans hv
  have hspan : (V-U)*q*q≤2*H := by
    have ha := (Nat.mul_le_mul_right q (hdiff.le.trans huv)).trans hv
    calc (V-U)*q*q = (V-(U+1))*q*q+q*q := by rw [show V-U=V-(U+1)+1 by omega]; ring
         _ ≤ 2*H := by omega
  refine ⟨by omega,?_⟩
  rw [mul_one_div,le_div_iff₀ (Nat.cast_pos.mpr hq)]
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg _),Real.sq_sqrt (Nat.cast_nonneg _)]
  have hcast : ((V-U:ℕ):ℝ)*q*q≤2*(H:ℝ) := by exact_mod_cast hspan
  nlinarith only [hcast,Nat.cast_nonneg (α := ℝ) H]

/-- Some consecutive grid piece carries at least the average signed
increment, with both endpoints in the original interval. -/
private theorem grid_piece (f : ℕ → ℝ) {U V P : ℕ} (hUV : U<V) (hP : 0<P)
    {A : ℝ} (hA : 0≤A) (hbig : (P:ℝ)*A < f V-f U) :
    ∃ u v : ℕ, U≤u ∧ u<v ∧ v≤V ∧ P*(v-u-1)≤V-U ∧ A<f v-f u := by
  let D := (V-U)/P+1
  let t := fun i : ℕ => min V (U+i*D)
  have hzero : t 0=U := by simp [t,min_eq_right hUV.le]
  have hcover := Nat.lt_mul_div_succ (V-U) hP
  have hend : t P=V := min_eq_left (by change V≤U+P*((V-U)/P+1); omega)
  have he := Finset.sum_range_sub (fun i => f (t i)) P
  rw [hzero,hend] at he
  have hex : ∃ i ∈ Finset.range P, A<f (t (i+1))-f (t i) := by
    by_contra! hh
    have h := Finset.sum_le_sum hh
    rw [he,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at h
    exact (not_le_of_gt hbig) h
  obtain ⟨i,_,hi⟩ := hex
  have hmono : t i≤t (i+1) := min_le_min_left _ (Nat.add_le_add_left
    (Nat.mul_le_mul_right D (Nat.le_succ i)) U)
  have hlt : t i<t (i+1) := lt_of_le_of_ne hmono (by intro h; rw [h,sub_self] at hi; exact (not_lt_of_ge hA) hi)
  have hmin (x y z : ℕ) : min x (y+z)-min x y≤z := by omega
  have hw : t (i+1)-t i≤D := by
    dsimp only [t]; rw [Nat.add_mul,one_mul,← Nat.add_assoc]; exact hmin ..
  have hcut : t (i+1)-t i-1≤(V-U)/P := by dsimp only [D] at hw; omega
  exact ⟨_,_,le_min hUV.le (Nat.le_add_right ..),hlt,min_le_left ..,
    (Nat.mul_le_mul_left P hcut).trans (Nat.mul_div_le ..),hi⟩

/-- Extract an unweighted short prime interval from a signed discrepancy
of the common factorial divisors. The price for the quotient intervals is harmonic. -/
theorem shortThetaIncrement_of_commonFactorialDivisorDiscrepancy {x y M H P : ℕ}
    (hM : 1≤M) (hMH : M≤H) (hP : 0<P) (hroot : ∀ n ∈ Finset.Ioc x y, Real.sqrt H<n)
    {s B : ℝ} (hB : 0<B)
    (hlarge : 2*B*P*Real.sqrt H*(1+Real.log H) <
      s*commonFactorialDivisorDiscrepancy (Finset.Ioc x y) (Finset.Icc M H)) :
    HasShortThetaIncrement M H P (Finset.Ioc x y) s B := by
  let S := Finset.Ioc x y
  let E := Finset.Icc M H
  let active := S.filter fun n => ∀ j ∈ E, j/n%2=1
  let fibre := fun q : ℕ => active.filter fun n => H/n=q
  let mass := fun q : ℕ => ∑ n ∈ fibre q, ordinaryPrimeExcessCoeff n
  have hHmem : H∈E := Finset.mem_Icc.mpr ⟨hMH,le_rfl⟩
  have hmaps (i : ℕ) (hi : i∈active) : H/i ∈ Finset.Icc 1 H := by
    have ho := (Finset.mem_filter.mp hi).2 H hHmem
    change H/i%2=1 at ho
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (fun h => by simp [h] at ho),Nat.div_le_self ..⟩
  have hsum := Finset.sum_fiberwise_of_maps_to hmaps ordinaryPrimeExcessCoeff
  change (∑ q ∈ Finset.Icc 1 H, mass q)=∑ n ∈ active, ordinaryPrimeExcessCoeff n at hsum
  rw [commonFactorialDivisorDiscrepancy_eq _ _ H (fun _ hj => (Finset.mem_Icc.mp hj).2) hroot,
    commonOddQuotientPrimeExcess,← Finset.sum_filter] at hlarge
  change _ < s*(∑ n ∈ active, ordinaryPrimeExcessCoeff n) at hlarge
  rw [← hsum,Finset.mul_sum] at hlarge
  let C := 2*B*P*Real.sqrt H
  have hC : 0≤C := by dsimp only [C]; positivity
  have hex : ∃ q ∈ Finset.Icc 1 H, C*(1/(q:ℝ)) < s*mass q := by
    by_contra! hall
    have h := Finset.sum_le_sum hall
    rw [← Finset.mul_sum (Finset.Icc 1 H) (fun q : ℕ => 1/(q:ℝ)) C] at h
    exact (not_le_of_gt hlarge) (h.trans (mul_le_mul_of_nonneg_left
      (harmonic_Icc_le_one_add_log H (hM.trans hMH)) hC))
  obtain ⟨q,hq,hgain⟩ := hex
  have hq0 := (Finset.mem_Icc.mp hq).1
  have hne : (fibre q).Nonempty := by
    by_contra! h
    simp only [mass,h,Finset.sum_empty,mul_zero] at hgain
    exact (not_lt_of_ge (mul_nonneg hC (by positivity))) hgain
  let a := (fibre q).min' hne
  let V := (fibre q).max' hne
  have ha : a∈fibre q := Finset.min'_mem ..
  have hv : V∈fibre q := Finset.max'_mem ..
  have hdata (n : ℕ) (hn : n∈fibre q) :
      n∈S ∧ q%2=1 ∧ ∀ j ∈ E, j/n=q := by
    obtain ⟨hn,hval⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn,hodd⟩ := Finset.mem_filter.mp hn
    have hp : 0<n := Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1
    obtain ⟨he,ho,_⟩ := (odd_quotient_throughout_block hMH hp).mp hodd
    refine ⟨hn,hval ▸ ho,fun j hj => le_antisymm ((Nat.div_le_div_right (Finset.mem_Icc.mp hj).2).trans_eq hval) ?_⟩
    exact (he.trans hval).symm.trans_le (Nat.div_le_div_right (Finset.mem_Icc.mp hj).1)
  obtain ⟨has,hodd,haq⟩ := hdata _ ha
  obtain ⟨hvs,_,hvq⟩ := hdata _ hv
  let U := a-1
  have hapos : 0<a := Nat.zero_lt_of_lt (Finset.mem_Ioc.mp has).1
  have hUa : U+1=a := by dsimp only [U]; omega
  have haV : a≤V := Finset.le_max' _ _ ha
  have hUV : U<V := by omega
  have hsub : Finset.Ioc U V ⊆ S := fun n hn => Finset.mem_Ioc.mpr
    ⟨by have := (Finset.mem_Ioc.mp has).1; have := (Finset.mem_Ioc.mp hn).1; omega,
      (Finset.mem_Ioc.mp hn).2.trans (Finset.mem_Ioc.mp hvs).2⟩
  have hconst (j : ℕ) (hj : j∈E) (n : ℕ) (hn : n∈Finset.Ioc U V) : j/n=q := by
    obtain ⟨hUn,hnV⟩ := Finset.mem_Ioc.mp hn
    have han : a≤n := by omega
    exact le_antisymm ((Nat.div_le_div_left han hapos).trans_eq (haq j hj))
      ((hvq j hj).symm.trans_le (Nat.div_le_div_left hnV (hapos.trans_le han)))
  have heq : fibre q=Finset.Ioc U V := by
    ext n
    constructor
    · intro hn
      have hn₁ : a≤n := Finset.min'_le _ _ hn
      exact Finset.mem_Ioc.mpr ⟨by omega,Finset.le_max' _ _ hn⟩
    · intro hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hsub hn,fun j hj => by rw [hconst j hj n hn]; exact hodd⟩,
        hconst H hHmem n hn⟩
  obtain ⟨hw,hsqrt⟩ := quotient_width hUV hq0 (by rw [hUa]; exact haq H hHmem) (hvq H hHmem) (hroot _ hvs)
  let f := fun z : ℕ => s*(Chebyshev.theta z-z)
  have hident {u v : ℕ} (huv : u≤v) :
      f v-f u=s*(Chebyshev.theta v-Chebyshev.theta u-(v-u:ℕ)) := by
    rw [Nat.cast_sub huv]; dsimp only [f]; ring
  have hbig : (P:ℝ)*(B*Real.sqrt (V-U:ℕ)) < f V-f U := by
    rw [hident hUV.le]
    unfold mass at hgain
    rw [heq,theta_increment hUV.le] at hgain
    apply lt_of_le_of_lt _ hgain
    calc _ ≤ (P:ℝ)*(B*(2*Real.sqrt H*(1/(q:ℝ)))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsqrt hB.le) (Nat.cast_nonneg P)
         _ = C*(1/(q:ℝ)) := by dsimp only [C]; ring
  obtain ⟨u,v,hu,huv,hv,hwidth,hread⟩ := grid_piece f hUV hP (by positivity) hbig
  have hin : Finset.Ioc u v ⊆ Finset.Ioc U V := fun n hn => Finset.mem_Ioc.mpr
    ⟨hu.trans_lt (Finset.mem_Ioc.mp hn).1,(Finset.mem_Ioc.mp hn).2.trans hv⟩
  rw [hident huv.le] at hread
  exact ⟨u,v,q,huv,hin.trans hsub,hodd,fun j hj n hn => hconst j hj n (hin hn),
    hwidth.trans (hw.trans (by omega)),lt_of_le_of_lt (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (Nat.cast_le.mpr (by omega : v-u≤V-U))) hB.le) hread⟩

/-- A run of consecutive starts with one fixed interval length. All tested
intervals lie in the same odd quotient interval, including at the two ends
of the run. -/
def HasSlidingThetaIncrements (M H P : ℕ) (S : Finset ℕ) (s B R : ℝ) : Prop :=
  ∃ u v q D : ℕ, u<v ∧ Finset.Ioc u v ⊆ S ∧ q%2=1 ∧
    (∀ j ∈ Finset.Icc M H, ∀ n ∈ Finset.Ioc u v, j/n=q) ∧ P*(v-u-1)≤v ∧
    B*Real.sqrt (v-u:ℕ) < s*(Chebyshev.theta v-Chebyshev.theta u-(v-u:ℕ)) ∧
    2*D<v-u ∧ R*Real.sqrt (v-u:ℕ)<(D:ℝ)+1 ∧
    ∀ r : ℕ, r≤D → R*Real.sqrt (v-u:ℕ) <
      s*(Chebyshev.theta (v-D+r:ℕ)-Chebyshev.theta (u+r:ℕ)-(v-u-D:ℕ))

private theorem signed_theta_upper {u v H : ℕ} (huv : u≤v) (hvH : v≤H)
    {s : ℝ} (hs : s=1 ∨ s= -1) :
    s*(Chebyshev.theta v-Chebyshev.theta u-(v-u:ℕ)) ≤ ((v-u:ℕ):ℝ)*(1+Real.log H) := by
  rw [← theta_increment huv,Finset.mul_sum]
  have hterm (n : ℕ) (hn : n∈Finset.Ioc u v) : s*ordinaryPrimeExcessCoeff n≤1+Real.log H := by
    have h₁ := Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1))
      (Nat.cast_le.mpr ((Finset.mem_Ioc.mp hn).2.trans hvH))
    have h₂ := Real.log_natCast_nonneg n
    have h₃ := Real.log_natCast_nonneg H
    rcases hs with rfl|rfl <;> by_cases hp : n.Prime <;>
      simp only [ordinaryPrimeExcessCoeff,hp,if_true,if_false,one_mul,neg_one_mul] <;> linarith only [h₁,h₂,h₃]
  simpa only [Finset.sum_const,Nat.card_Ioc,nsmul_eq_mul] using Finset.sum_le_sum hterm

/-- Trimming a total of D terms from either end costs at most D(1+log H).
All intermediate translations of the shortened interval retain the sign. -/
theorem HasShortThetaIncrement.sliding {M H P : ℕ} {S : Finset ℕ} {s B R : ℝ}
    (hMH : M≤H) (hs : s=1 ∨ s= -1) (hR : 0<R) (hprice : 2*R*(1+Real.log H)≤B)
    (h : HasShortThetaIncrement M H P S s B) : HasSlidingThetaIncrements M H P S s B R := by
  obtain ⟨u,v,q,huv,hS,hodd,hq,hw,hbig⟩ := h
  have hvq := hq H (Finset.mem_Icc.mpr ⟨hMH,le_rfl⟩) v (Finset.mem_Ioc.mpr ⟨huv,le_rfl⟩)
  have hvH : v≤H := by
    have hpos : 1≤H/v := by rw [hvq]; omega
    simpa using (Nat.le_div_iff_mul_le (Nat.zero_lt_of_lt huv)).mp hpos
  let K := 1+Real.log H
  let A := R*Real.sqrt (v-u:ℕ)
  let D := ⌊A⌋₊
  have hK : 0<K := by dsimp only [K]; have := Real.log_natCast_nonneg H; positivity
  have hA : 0≤A := mul_nonneg hR.le (Real.sqrt_nonneg _)
  have hD : (D:ℝ)≤A := Nat.floor_le hA
  have hraw := mul_le_mul_of_nonneg_right hprice (Real.sqrt_nonneg (v-u:ℕ))
  have hscale : 2*A*K≤B*Real.sqrt (v-u:ℕ) := by
    dsimp only [A,K]; linarith only [hraw]
  have hcap := hbig.trans_le (signed_theta_upper huv.le hvH hs)
  have hhalf : 2*A<((v-u:ℕ):ℝ) := (mul_lt_mul_iff_left₀ hK).mp (hscale.trans_lt hcap)
  have hhalfD : 2*D<v-u := by exact_mod_cast (by linarith only [hhalf,hD] : 2*(D:ℝ)<((v-u:ℕ):ℝ))
  refine ⟨u,v,q,D,huv,hS,hodd,hq,hw,hbig,hhalfD,Nat.lt_floor_add_one A,fun r hr => ?_⟩
  have hleft : u+r≤v := by omega
  have hright : v-D+r≤v := by omega
  have h₁ := signed_theta_upper (Nat.le_add_right u r) (hleft.trans hvH) hs
  have h₂ := signed_theta_upper hright hvH hs
  have hsplit : s*(Chebyshev.theta v-Chebyshev.theta u-(v-u:ℕ)) =
      s*(Chebyshev.theta (u+r:ℕ)-Chebyshev.theta u-(u+r-u:ℕ)) +
      s*(Chebyshev.theta (v-D+r:ℕ)-Chebyshev.theta (u+r:ℕ)-(v-u-D:ℕ)) +
      s*(Chebyshev.theta v-Chebyshev.theta (v-D+r:ℕ)-(v-(v-D+r):ℕ)) := by
    have hlen : v-u=(u+r-u)+(v-u-D)+(v-(v-D+r)) := by omega
    have he := congrArg (Nat.cast (R := ℝ)) hlen
    simp only [Nat.cast_add] at he
    linarith only [congrArg (s*·) he]
  have hlen : u+r-u+(v-(v-D+r))=D := by omega
  have he := congrArg (Nat.cast (R := ℝ)) hlen
  rw [Nat.cast_add] at he
  have hcost := (mul_le_mul_of_nonneg_right hD hK.le)
  have hAK : A≤A*K := le_mul_of_one_le_right hA (by dsimp only [K]; linarith only [Real.log_natCast_nonneg H])
  rw [hsplit] at hbig
  change A < _
  dsimp only [K] at hcost hscale hAK
  linarith only [hbig,h₁,h₂,congrArg (·*(1+Real.log H)) he,hcost,hscale,hAK]

private theorem log_at_numerator {g T : ℝ} {H : ℕ} (hg : 0<g) (hH : 0<H)
    (hpow : (H:ℝ)^(g/6)≤Real.exp (g*T)) : Real.log H≤6*T := by
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hH),Real.exp_le_exp] at hpow
  by_contra! hh
  linarith only [hpow,mul_lt_mul_of_pos_right hh hg]

private theorem eventually_sliding_price {g : ℝ} (hg : 0<g) :
    ∀ᶠ T : ℝ in atTop, ∀ H : ℕ, 0<H → (H:ℝ)^(g/6)≤Real.exp (g*T) →
      2*Real.exp ((g/8)*T)*(1+Real.log H) ≤ Real.exp ((g/4)*T) := by
  let a := g/16
  have ha : 0<a := by dsimp only [a]; positivity
  have hlim := Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop ha)
  filter_upwards [eventually_ge_atTop (0:ℝ),hlim.eventually_ge_atTop (2*(1+6/a))] with T hT hlarge
  intro H hH hpow
  let Y := Real.exp (a*T)
  have hY : 1≤Y := Real.one_le_exp (mul_nonneg ha.le hT)
  have ht : T≤Y/a := (le_div_iff₀ ha).mpr (by
    have h := Real.add_one_le_exp (a*T)
    change _ ≤ Y at h
    linarith only [h])
  change 2*(1+6/a)≤Y at hlarge
  have hlow := log_at_numerator hg hH hpow
  have hlin : 1+Real.log H≤(1+6/a)*Y := calc
    _ ≤ Y+6*(Y/a) := by linarith only [ht,hY,hlow]
    _ = _ := by ring
  have hy : 2*(1+Real.log H)≤Y*Y := by
    calc _ ≤ 2*((1+6/a)*Y) := by linarith only [hlin]
         _ = (2*(1+6/a))*Y := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hlarge (by dsimp [Y]; positivity)
  have hsq : Real.exp ((g/8)*T)=Y*Y := by rw [← Real.exp_add]; congr 1; dsimp only [a]; ring
  have hfour : Real.exp ((g/4)*T)=Real.exp ((g/8)*T)*Real.exp ((g/8)*T) := by rw [← Real.exp_add]; congr 1; ring
  rw [hfour]
  calc _ = Real.exp ((g/8)*T)*(2*(1+Real.log H)) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (hy.trans_eq hsq.symm) (Real.exp_pos _).le

private theorem mesh_price {c g : ℝ} (hc : 0<c) (hg : 0<g) :
    ∀ᶠ T : ℝ in atTop, ∀ H : ℕ, 0<H → (H:ℝ)^(g/6)≤Real.exp (g*T) →
      let B := Real.exp ((g/4)*T)
      2*B*⌈B⌉₊*Real.sqrt H*(1+Real.log H) ≤ c*Real.exp (g*T)*Real.sqrt H := by
  let e := g/4
  have he : 0<e := by dsimp only [e]; positivity
  let K := 1+6/e
  have hK : 0<K := by dsimp only [K]; positivity
  have hlim := Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop he)
  filter_upwards [eventually_ge_atTop (0:ℝ),hlim.eventually_ge_atTop (4*K/c)] with T hT hbig
  intro H hH hpow
  let B := Real.exp (e*T)
  have hB : 1≤B := Real.one_le_exp (mul_nonneg he.le hT)
  have hB₀ : 0≤B := (Real.exp_pos _).le
  change 4*K/c≤B at hbig
  have hprice := (div_le_iff₀ hc).mp hbig
  have hceil : (⌈B⌉₊:ℝ) ≤ 2*B := by linarith only [Nat.ceil_lt_add_one hB₀,hB]
  have hlog := log_at_numerator hg hH hpow
  have htB : T≤B/e := (le_div_iff₀ he).mpr (by
    have h := Real.add_one_le_exp (e*T)
    change _ ≤ B at h
    linarith only [h])
  have hKB : 1+Real.log H≤K*B := by
    calc _ ≤ B+6*(B/e) := by linarith only [hlog,htB,hB]
         _ = _ := by dsimp only [K]; ring
  have heq : Real.exp (g*T)=B^4 := by
    rw [show g*T=e*T+e*T+(e*T+e*T) by dsimp only [e]; ring,Real.exp_add,Real.exp_add]
    dsimp only [B]; ring
  change 2*B*⌈B⌉₊*Real.sqrt H*(1+Real.log H) ≤ _
  rw [heq]
  calc _ ≤ (2*B*(2*B)*Real.sqrt H)*(K*B) := mul_le_mul
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hceil (by positivity)) (Real.sqrt_nonneg _))
              hKB (by have := Real.log_natCast_nonneg H; positivity) (by positivity)
       _ = (4*K)*(B^3*Real.sqrt H) := by ring
       _ ≤ (B*c)*(B^3*Real.sqrt H) := mul_le_mul_of_nonneg_right hprice (by positivity)
       _ = _ := by ring

/-- The original signed tests force a prime excess and a prime deficit on
power-short intervals. Each unweighted error exceeds the square root of its
own interval length by a power of the test scale, and every denominator on
each interval retains a single odd quotient throughout the whole block. -/
theorem riemannHypothesis_or_opposite_short_theta_increments : RiemannHypothesis ∨
    ∃ (W : ℝ) (F Φ : ℝ → ℝ) (c g d : ℝ), 0<W ∧
      (⨅ (a : ℝ) (_ : 0≤a), windowThreshold a)=(W:EReal) ∧ IsCriticalHalfLineGroundState W F ∧
      Continuous Φ ∧ F =ᵐ[volume] Φ ∧ 0<c ∧ 0<g ∧ 0<d ∧ d≤1/4 ∧ ∀ η : ℝ, 0<η → η≤1 →
      ∃ (T : ℕ → ℝ) (k : ℕ → ℕ), Tendsto T atTop atTop ∧
        (∀ i, T i/(1+η) ≤ Real.log (k i) ∧ Real.log (k i) ≤ T i) ∧
        let L := fun i => ⌈Real.exp ((1+η)*T i)⌉₊
        let m := ∫ v, Φ v
        (∀ i, c*Real.exp (g*T i) ≤ m*(∫ t in Ioc (T i/6) (6*T i),
          criticalComplementBand Φ 0 t*fractionalPrimeTest (T i-t)) -
          m*(∫ t in Ioc (T i/6) (6*T i),
          finiteCriticalComplementBand Φ (k i) (L i) t*fractionalPrimeTest (T i-t))) ∧
        ∀ᶠ i in atTop, ∃ (v s : ℝ) (j H a b l u : ℕ), v≤0 ∧ (s=1 ∨ s= -1) ∧ s*m*Φ v<0 ∧
          H=⌊(2:ℝ)^(j+1)*Real.exp (T i-v)⌋₊ ∧ Real.exp (T i)≤H ∧
          k i<a ∧ a≤b ∧ b≤L i ∧ Real.sqrt H<a ∧
          ((ordinaryBandAtDisplacement (k i) (L i) (T i) v).filter fun n : ℕ => Real.sqrt H<n)=Finset.Icc a b ∧
          ((l=⌊Real.sqrt H⌋₊ ∧ u=a-1) ∨ (l=b ∧ u=H)) ∧
          let B := Real.exp ((g/4)*T i)
          ∀ M : ℕ, 1≤M → M≤H → (H:ℝ)-M≤(H:ℝ)^(1/2+d) →
            HasSlidingThetaIncrements M H ⌈B⌉₊ (Finset.Icc a b) s B (Real.exp ((g/8)*T i)) ∧
            HasSlidingThetaIncrements M H ⌈B⌉₊ (Finset.Ioc l u) (-s) B (Real.exp ((g/8)*T i)) := by
  rcases riemannHypothesis_or_consecutive_factorial_discrepancies with hr | ⟨W,F,Φ,c,g,d,hW,ht,hF,hc,he,hc₀,hg,hd,hd₁,hh⟩
  · exact Or.inl hr
  refine Or.inr ⟨W,F,Φ,c,g,d,hW,ht,hF,hc,he,hc₀,hg,hd,hd₁,fun η hη hη₁ => ?_⟩
  obtain ⟨T,k,hT,hk,hgain,hw⟩ := hh η hη hη₁
  refine ⟨T,k,hT,hk,hgain,?_⟩
  filter_upwards [hw,hT.eventually (mesh_price hc₀ hg),hT.eventually (eventually_sliding_price hg)] with i hi hp hslide
  obtain ⟨v,s,j,H,a,b,l,u,hv,hs,hor,hj,hX,hpow,ha,hab,hb,hroot,hcell,hside,hpair⟩ := hi
  refine ⟨v,s,j,H,a,b,l,u,hv,hs,hor,hj,hX,ha,hab,hb,hroot,hcell,hside,fun M hm hMH hwide => ?_⟩
  let B := Real.exp ((g/4)*T i)
  have hB : 0<B := Real.exp_pos _
  have hP : 0<⌈B⌉₊ := Nat.ceil_pos.mpr hB
  have hprice := hp H (hm.trans hMH) hpow
  have hpairs := hpair M hm hMH hwide (Finset.Icc M H) ⟨M,Finset.mem_Icc.mpr ⟨le_rfl,hMH⟩⟩ (by rfl)
  have has : 0<a := Nat.cast_pos.mp ((Real.sqrt_nonneg _).trans_lt hroot)
  have heq : Finset.Icc a b=Finset.Ioc (a-1) b := by ext n; simp only [Finset.mem_Icc,Finset.mem_Ioc]; omega
  rw [heq] at hpairs ⊢
  have hinside (n : ℕ) (hn : n∈Finset.Ioc (a-1) b) : Real.sqrt H<n :=
    hroot.trans_le (Nat.cast_le.mpr (by have := (Finset.mem_Ioc.mp hn).1; omega : a≤n))
  have hout (n : ℕ) (hn : n∈Finset.Ioc l u) : Real.sqrt H<n := by
    rcases hside with ⟨hl,_⟩|⟨hl,_⟩
    · exact (Nat.floor_lt (Real.sqrt_nonneg _)).mp (hl ▸ (Finset.mem_Ioc.mp hn).1)
    · exact hroot.trans_le (Nat.cast_le.mpr (hab.trans (hl ▸ (Finset.mem_Ioc.mp hn).1.le)))
  have hneg : -s=1 ∨ -s= -1 := hs.elim (fun h => Or.inr (by rw [h])) (fun h => Or.inl (by rw [h,neg_neg]))
  have hincr := shortThetaIncrement_of_commonFactorialDivisorDiscrepancy hm hMH hP hinside hB (hprice.trans_lt hpairs.1)
  have houtcr := shortThetaIncrement_of_commonFactorialDivisorDiscrepancy hm hMH hP hout hB (hprice.trans_lt hpairs.2)
  exact ⟨hincr.sliding hMH hs (Real.exp_pos _) (hslide H (hm.trans hMH) hpow),
    houtcr.sliding hMH hneg (Real.exp_pos _) (hslide H (hm.trans hMH) hpow)⟩

#print axioms shortThetaIncrement_of_commonFactorialDivisorDiscrepancy
#print axioms riemannHypothesis_or_opposite_short_theta_increments
end GaloisForLFunctions.ExclusionOfTheCriticalState
