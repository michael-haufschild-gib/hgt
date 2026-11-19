import GaloisForLFunctions.RHTower.XiZeroShortWeightDyadic
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheForbiddenLargePrimeInTheReflectedCofactorIntervals
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.RoughCofactorsAtPrimorialMidpoints
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SignedDivisibilityAveragesOfTheReflectedCofactors
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheClippedCofactorDensityAtThePrimeMidpoint

/-!
# Ordinary prime intervals under signed sampling of the midpoint

Freeze the three prime endpoints before averaging the primitive restrictions.
The coefficient of each centered cofactor interval then has an explicit
divisor sum. Quotient windows may start at different integers.
-/

noncomputable section
open Finset GaloisForLFunctions.ArithmeticEffectivityTheory
open RHTower (truncMoebiusDivisorSum)
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Right-minus-left ordinary prime price, less its clipped continuous length. -/
def centeredOrdinaryCofactorInterval (n Q v : ℕ) : ℝ :=
  Chebyshev.theta (max Q (4*n/v):ℕ) - 2*Chebyshev.theta (max Q (3*n/v):ℕ) +
    Chebyshev.theta (max Q (2*n/v):ℕ) - reflectedCofactorLength n Q v

/-- The endpoints are those of n and the primitive restriction is that of m. -/
def frozenOrdinaryCofactorPrice (n Q m : ℕ) : ℝ :=
  ∑ v ∈ (Icc 2 (4*n/Q)).filter (·.Coprime m), centeredOrdinaryCofactorInterval n Q v

/-- The projected price starts strictly beyond the divisibility cutoff. -/
def projectedOrdinaryCofactorPrice (n Q V : ℕ) : ℝ :=
  ∑ v ∈ Ioc V (4*n/Q), (v.totient:ℝ)/v*truncMoebiusDivisorSum V v*
    centeredOrdinaryCofactorInterval n Q v

private def cofactorPrefixCount (n T : ℕ) : ℝ := (((Icc 2 T).filter (n.Coprime ·)).card:ℝ)

/-- Summing a single theta endpoint over the proper primitive cofactors
counts each ordinary prime with its exact quotient multiplicity. -/
private theorem transpose_ordinary_endpoint {n Q T : ℕ} (hQ : 0 < Q) (hT : T ≤ 4*n) :
    (∑ v ∈ (Icc 2 (4*n/Q)).filter (n.Coprime ·),
      (Chebyshev.theta (max Q (T/v):ℕ)-Chebyshev.theta Q)) =
    ∑ p ∈ (Ioc Q (4*n)).filter Nat.Prime,Real.log p*cofactorPrefixCount n (T/p) := by
  let S := (Ioc Q (4*n)).filter Nat.Prime
  let U := (Icc 2 (4*n/Q)).filter (n.Coprime ·)
  let w (p : ℕ) := if p.Prime then Real.log (p:ℝ) else 0
  have theta (b : ℕ) : Chebyshev.theta b=∑ p ∈ Ioc 0 b,w p := by
    rw [Chebyshev.theta,Nat.floor_natCast,sum_filter]
  have point (v : ℕ) (hv : v ∈ U) : Chebyshev.theta (max Q (T/v):ℕ)-Chebyshev.theta Q =
      ∑ p ∈ S,if v ≤ T/p then Real.log (p:ℝ) else 0 := by
    have hv0 : 0 < v := by have hv2 := (mem_Icc.mp (mem_filter.mp hv).1).1; omega
    rw [theta,theta,←eq_sub_of_add_eq' (sum_Ioc_consecutive w (Nat.zero_le Q) (le_max_left Q (T/v)))]
    have hs : S.filter (fun p => v ≤ T/p)=(Ioc Q (max Q (T/v))).filter Nat.Prime := by
      ext p
      simp only [S,mem_filter,mem_Ioc]
      constructor
      · rintro ⟨⟨⟨hlo,_⟩,hp⟩,hv⟩
        have h := (Nat.le_div_iff_mul_le hp.pos).mp hv
        exact ⟨⟨hlo,(Nat.le_div_iff_mul_le hv0).mpr ((Nat.mul_comm p v).le.trans h) |>.trans (le_max_right ..)⟩,hp⟩
      · rintro ⟨⟨hlo,hcap⟩,hp⟩
        have hc : p ≤ T/v := (le_max_iff.mp hcap).resolve_left hlo.not_ge
        exact ⟨⟨⟨hlo,hc.trans ((Nat.div_le_self _ _).trans hT)⟩,hp⟩,
          (Nat.le_div_iff_mul_le hp.pos).mpr ((Nat.mul_comm v p).le.trans ((Nat.le_div_iff_mul_le hv0).mp hc))⟩
    rw [←sum_filter,hs,sum_filter]
  change (∑ v ∈ U,_)=∑ p ∈ S,_
  rw [sum_congr rfl point,sum_comm]
  apply sum_congr rfl
  intro p hp
  obtain ⟨hIp,hpr⟩ := mem_filter.mp hp
  have hQp := (mem_Ioc.mp hIp).1
  have hcap : T/p ≤ 4*n/Q :=
    (Nat.div_le_div_right hT).trans (Nat.div_le_div_left hQp.le hQ)
  have hs : U.filter (fun v => v ≤ T/p)=(Icc 2 (T/p)).filter (n.Coprime ·) := by
    ext v
    simp only [U,mem_filter,mem_Icc]
    exact ⟨fun h => ⟨⟨h.1.1.1,h.2⟩,h.1.2⟩,fun h => ⟨⟨⟨h.1.1,h.1.2.trans hcap⟩,h.2⟩,h.1.2⟩⟩
  rw [←sum_filter,hs,sum_const,nsmul_eq_mul,mul_comm]
  rfl

private theorem cofactor_prefix_difference (n : ℕ) {a b : ℕ} (hab : a ≤ b) :
    cofactorPrefixCount n b-cofactorPrefixCount n a =
      (((Ioc (max 1 a) b).filter (n.Coprime ·)).card:ℝ) := by
  let s := (Icc 2 b).filter (n.Coprime ·)
  have hl : s.filter (· ≤ a)=(Icc 2 a).filter (n.Coprime ·) := by
    ext v
    simp only [s,mem_filter,mem_Icc]
    exact ⟨fun h => ⟨⟨h.1.1.1,h.2⟩,h.1.2⟩,fun h => ⟨⟨⟨h.1.1,h.1.2.trans hab⟩,h.2⟩,h.1.2⟩⟩
  have hu : s.filter (fun v => ¬v ≤ a)=(Ioc (max 1 a) b).filter (n.Coprime ·) := by
    ext v
    simp only [s,mem_filter,mem_Icc,mem_Ioc,max_lt_iff,not_le]
    omega
  have h := card_filter_add_card_filter_not (s:=s) (p:=fun v => v ≤ a)
  rw [hl,hu] at h
  change (s.card:ℝ)-_=_
  exact sub_eq_iff_eq_add.mpr (by exact_mod_cast (h.symm.trans (Nat.add_comm ..)))

/-- Above twice the square root, the centered frozen price at its own
midpoint is exactly the large-prime price less the primitive clipped length. -/
theorem frozen_ordinary_cofactor_at_midpoint {n Q : ℕ} (hn : 0 < n) (hQ : 0 < Q)
    (hcut : ⌊2*Real.sqrt n⌋₊ ≤ Q) (hcap : Q ≤ 2*n) :
    frozenOrdinaryCofactorPrice n Q n = largePrimeCofactorPrice n Q-primitiveCofactorLength n Q := by
  let U := (Icc 2 (4*n/Q)).filter (n.Coprime ·)
  let S := (Ioc Q (4*n)).filter Nat.Prime
  have hU : (Icc 2 (4*n/Q)).filter (·.Coprime n)=U := by
    ext v; simp only [U,mem_filter,Nat.coprime_comm]
  have hlen : (∑ v ∈ U,reflectedCofactorLength n Q v)=primitiveCofactorLength n Q := by
    apply sum_subset
    · exact fun v h => mem_filter.mpr ⟨Icc_subset_Icc_left (by decide : 1 ≤ 2) (mem_filter.mp h).1,(mem_filter.mp h).2⟩
    · intro v h hnot
      have hi := mem_Icc.mp (mem_filter.mp h).1
      have h2 : ¬2 ≤ v := fun hv => hnot (mem_filter.mpr ⟨mem_Icc.mpr ⟨hv,hi.2⟩,(mem_filter.mp h).2⟩)
      obtain rfl : v=1 := by omega
      exact unit_reflected_cofactor_length hcap
  let F (j : ℕ) (v : ℕ) := Chebyshev.theta (max Q (j*n/v):ℕ)-Chebyshev.theta Q
  have hrow (v : ℕ) : centeredOrdinaryCofactorInterval n Q v =
      F 4 v-2*F 3 v+F 2 v-reflectedCofactorLength n Q v := by
    unfold centeredOrdinaryCofactorInterval F
    ring
  have hsum (j : ℕ) (hj : j ≤ 4) : (∑ v ∈ U,F j v)=
      ∑ p ∈ S,Real.log p*cofactorPrefixCount n (j*n/p) :=
    transpose_ordinary_endpoint hQ (Nat.mul_le_mul_right n hj)
  rw [frozenOrdinaryCofactorPrice,hU]
  simp only [hrow,sum_sub_distrib,sum_add_distrib,←mul_sum,hlen,hsum 4 (by decide),hsum 3 (by decide),hsum 2 (by decide)]
  congr 1
  rw [mul_sum,←sum_sub_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  let A (j : ℕ) := cofactorPrefixCount n (j*n/p)
  change Real.log p*A 4-2*(Real.log p*A 3)+Real.log p*A 2=Real.log p*properCofactorMidpoint n p
  rw [show Real.log p*A 4-2*(Real.log p*A 3)+Real.log p*A 2=Real.log p*(A 4-2*A 3+A 2) by ring]
  congr 1
  by_cases hc : n.Coprime p
  · change _=if n.Coprime p then A 4-2*A 3+A 2 else 0
    rw [if_pos hc]
  · have hpr := (mem_filter.mp hp).2
    have hdiv : p ∣ n := by
      by_contra h
      exact hc (hpr.coprime_iff_not_dvd.mpr h).symm
    have hlarge := hcut.trans_lt (mem_Ioc.mp (mem_filter.mp hp).1).1
    have hpR : 2*Real.sqrt n < (p:ℝ) := (Nat.floor_lt (by positivity)).mp hlarge
    have hs := mul_self_lt_mul_self (by positivity : (0:ℝ)≤2*Real.sqrt n) hpR
    have hsq : 4*(n:ℝ)<(p:ℝ)^2 := by nlinarith only [hs,Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n)]
    have hz := (forbidden_prime_cofactor_boundaries hn hpr hdiv (by exact_mod_cast hsq)).2.2
    rw [←Nat.mul_div_assoc 4 hdiv] at hz
    have h23 : 2*n/p ≤ 3*n/p := Nat.div_le_div_right (by omega)
    have h34 : 3*n/p ≤ 4*n/p := Nat.div_le_div_right (by omega)
    simp only [unrestrictedPrimeCofactorCut,min_self,min_eq_right h34,
      ←cofactor_prefix_difference n h34,←cofactor_prefix_difference n h23] at hz
    change (A 4-A 3)-(A 3-A 2)=0 at hz
    rw [properCofactorMidpoint,if_neg hc]
    linarith only [hz]

private theorem cofactor_theta_motion {m n Q v j : ℕ} (hm : m ≤ n) (hQ : Q ≤ 4*n)
    (hv : 0 < v) (hj : j ≤ 4) :
    let a := max Q (j*m/v)
    let b := max Q (j*n/v)
    0 ≤ Chebyshev.theta b-Chebyshev.theta a ∧
      Chebyshev.theta b-Chebyshev.theta a ≤ (((j:ℝ)*((n:ℝ)-m)/v)+1)*Real.log (4*n:ℕ) := by
  intro a b
  have h := Nat.div_le_div_right (k:=v) (Nat.mul_le_mul_left j hm)
  have hab : a ≤ b := max_le_max_left _ h
  have hb : b ≤ 4*n := max_le hQ ((Nat.div_le_self ..).trans (Nat.mul_le_mul_right n hj))
  have hjv : (j*m/v:ℕ)*v+v > j*m := by simpa [Nat.succ_mul,Nat.mul_comm v] using Nat.lt_mul_div_succ (j*m) hv
  have hnv := Nat.div_mul_le_self (j*n) v
  have hs : (b:ℝ)-a ≤ ((j*n/v:ℕ):ℝ)-(j*m/v:ℕ) := by
    have hh : b+(j*m/v) ≤ (j*n/v)+a := by dsimp only [a,b]; omega
    have hreal : (b:ℝ)+(j*m/v:ℕ) ≤ (j*n/v:ℕ)+(a:ℝ) := by exact_mod_cast hh
    linarith only [hreal]
  have hd : ((j*n/v:ℕ):ℝ)-(j*m/v:ℕ) ≤ ((j:ℝ)*((n:ℝ)-m)/v)+1 := by
    rw [←sub_le_iff_le_add,le_div_iff₀ (Nat.cast_pos.mpr hv)]
    have hm' : (j:ℝ)*m < ((j*m/v:ℕ):ℝ)*v+v := by exact_mod_cast hjv
    have hn' : ((j*n/v:ℕ):ℝ)*v ≤ (j:ℝ)*n := by exact_mod_cast hnv
    linarith only [hm',hn']
  refine ⟨sub_nonneg.mpr (Chebyshev.theta_mono (Nat.cast_le.mpr hab)),?_⟩
  have hlog : Real.log (b:ℝ) ≤ Real.log (4*n:ℕ) := by
    rcases eq_zero_or_pos b with rfl | hpos
    · simpa using Real.log_natCast_nonneg (4*n)
    · exact Real.log_le_log (Nat.cast_pos.mpr hpos) (Nat.cast_le.mpr hb)
  exact (theta_integer_interval_bound hab).trans (mul_le_mul (hs.trans hd) hlog
    (Real.log_natCast_nonneg _) ((sub_nonneg.mpr (Nat.cast_le.mpr hab)).trans (hs.trans hd)))

private theorem ordinary_cofactor_row_motion {m n Q v : ℕ} (hm : m ≤ n) (hQ : Q ≤ 4*n) (hv : 0 < v) :
    |centeredOrdinaryCofactorInterval n Q v-centeredOrdinaryCofactorInterval m Q v| ≤
      (6*(((n:ℝ)-m)/v)+2)*Real.log (4*n:ℕ)+6*(((n:ℝ)-m)/v) := by
  have h4 := cofactor_theta_motion (j:=4) hm hQ hv (by decide)
  have h3 := cofactor_theta_motion (j:=3) hm hQ hv (by decide)
  have h2 := cofactor_theta_motion (j:=2) hm hQ hv (by decide)
  dsimp only at h4 h3 h2
  simp only [Nat.cast_ofNat,mul_div_assoc] at h4 h3 h2
  have hl := abs_le.mp (reflected_cofactor_length_motion hm Q v)
  simp only [centeredOrdinaryCofactorInterval,abs_le]
  constructor <;> linarith only [h4.1,h4.2,h3.1,h3.2,h2.1,h2.2,hl.1,hl.2]

private theorem beyond_cofactor_cut {m Q v : ℕ} (hQ : 0 < Q) (hv : 4*m/Q < v) :
    centeredOrdinaryCofactorInterval m Q v=0 := by
  have hv0 := (Nat.zero_le _).trans_lt hv
  have hlt := (Nat.div_lt_iff_lt_mul hQ).mp hv
  have cut (j : ℕ) (hj : j ≤ 4) : j*m/v ≤ Q := by
    have h := (Nat.mul_le_mul_right m hj).trans_lt hlt
    exact ((Nat.div_lt_iff_lt_mul hv0).mpr (h.trans_eq (Nat.mul_comm ..))).le
  have len : reflectedCofactorLength m Q v=0 := by
    have small (j : ℕ) (hj : j ≤ 4) : ((j*m:ℕ):ℝ)/v ≤ Q := by
      apply (div_le_iff₀ (Nat.cast_pos.mpr hv0)).mpr
      exact_mod_cast ((Nat.mul_le_mul_right m hj).trans hlt.le).trans_eq (Nat.mul_comm ..)
    change max (((4*m:ℕ):ℝ)/v-Q) 0-2*max (((3*m:ℕ):ℝ)/v-Q) 0+max (((2*m:ℕ):ℝ)/v-Q) 0=0
    rw [max_eq_right (sub_nonpos.mpr (small 4 (by decide))),max_eq_right (sub_nonpos.mpr (small 3 (by decide))),
      max_eq_right (sub_nonpos.mpr (small 2 (by decide)))]
    ring
  rw [centeredOrdinaryCofactorInterval,len,max_eq_left (cut 4 (by decide)),max_eq_left (cut 3 (by decide)),
    max_eq_left (cut 2 (by decide))]
  ring

/-- Freeze all three theta endpoints before taking the average over centers.
The crossed integer cells contribute one logarithm per active cofactor. -/
theorem freeze_ordinary_cofactor_window {m n Q : ℕ} (hm : m ≤ n) (hQ : 0 < Q) (hcap : Q ≤ 4*n) :
    |frozenOrdinaryCofactorPrice n Q m-frozenOrdinaryCofactorPrice m Q m| ≤
      6*((n:ℝ)-m)*(1+Real.log (4*n/Q:ℕ))*(1+Real.log (4*n:ℕ))+
      2*(4*n/Q:ℕ)*Real.log (4*n:ℕ) := by
  let T := 4*n/Q
  let U := (Icc 2 T).filter (·.Coprime m)
  let L := Real.log (4*n:ℕ)
  let h := (n:ℝ)-m
  have h0 : 0 ≤ h := sub_nonneg.mpr (Nat.cast_le.mpr hm)
  have hL : 0 ≤ L := Real.log_natCast_nonneg _
  have sup : U ⊆ Icc 1 T := fun v hv => Icc_subset_Icc_left (by decide : 1 ≤ 2) (mem_filter.mp hv).1
  have extend : frozenOrdinaryCofactorPrice m Q m=∑ v ∈ U,centeredOrdinaryCofactorInterval m Q v := by
    apply sum_subset (filter_subset_filter _ (Icc_subset_Icc_right (Nat.div_le_div_right (Nat.mul_le_mul_left 4 hm))))
    intro v hv hnot
    have hcut : 4*m/Q < v := lt_of_not_ge fun hc => hnot (mem_filter.mpr
      ⟨mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hv).1).1,hc⟩,(mem_filter.mp hv).2⟩)
    exact beyond_cofactor_cut hQ hcut
  rw [extend]
  change |(∑ v ∈ U,_)-(∑ v ∈ U,_)| ≤ _
  rw [←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  let f (v : ℕ) := 6*h*(1+L)*(1/(v:ℝ))+2*L
  have hrow (v : ℕ) (hv : v ∈ U) := ordinary_cofactor_row_motion hm hcap (mem_Icc.mp (sup hv)).1
  calc _ ≤ ∑ v ∈ U,f v := sum_le_sum fun v hv => (hrow v hv).trans_eq (by dsimp only [f,h,L]; ring)
       _ ≤ ∑ v ∈ Icc 1 T,f v := sum_le_sum_of_subset_of_nonneg sup fun v _ _ => by dsimp only [f]; positivity
       _ ≤ _ := by
         simp only [f,sum_add_distrib,←mul_sum,sum_const,Nat.card_Icc,Nat.add_one_sub_one,nsmul_eq_mul]
         have hs := mul_le_mul_of_nonneg_left (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log T)
           (by positivity : 0 ≤ 6*h*(1+L))
         dsimp only [T,h,L] at *
         linarith only [hs]

private theorem frozen_price_at_own_center_error {m Q : ℕ} (hm : 1 < m) (hp : 0 < Q)
    (hsmall : ⌊2*Real.sqrt m⌋₊ ≤ Q) (hcap : Q ≤ 2*m) :
    |frozenOrdinaryCofactorPrice m Q m-primeMidpointPrice m| ≤
      (7*(Q:ℝ)+(Chebyshev.psi (4*m:ℕ)-Chebyshev.theta (4*m:ℕ))+1+
        max (4+|reflectedDensity|) 6*Q)*squarefreeDivisorMass m := by
  have h0 := zero_lt_one.trans hm
  rw [frozen_ordinary_cofactor_at_midpoint h0 hp hsmall hcap]
  have h := large_prime_cofactor_centering hm hcap
  have hl := primitive_clipped_density_cutoff h0 hp
  rw [show largePrimeCofactorPrice m Q-primitiveCofactorLength m Q-primeMidpointPrice m =
    (largePrimeCofactorPrice m Q-reflectedDensity*m.totient-primeMidpointPrice m)-
    (primitiveCofactorLength m Q-reflectedDensity*m.totient) by ring]
  exact (abs_sub _ _).trans ((add_le_add h hl).trans_eq (by ring))

private def samplingLog (n : ℕ) := 1+Real.log (4*n:ℕ)

private def samplingMass (η : ℝ) (n : ℕ) := 1+|_root_.RHTower.Sieve.divisorBoundConst η|*((4*n:ℕ):ℝ)^η

private theorem sampling_log_one (n : ℕ) : 1 ≤ samplingLog n :=
  le_add_of_nonneg_right (Real.log_natCast_nonneg _)

private theorem sampling_mass_one (η : ℝ) (n : ℕ) : 1 ≤ samplingMass η n :=
  le_add_of_nonneg_right (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

private theorem sampling_divisor_mass {η : ℝ} (hη : 0 < η) {v n : ℕ} (hv : 0 < v) (hcap : v ≤ 4*n) :
    squarefreeDivisorMass v ≤ samplingMass η n := by
  have h := sum_le_sum (s:=v.divisors) fun d _ =>
    (show |(ArithmeticFunction.moebius d:ℝ)| ≤ 1 by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d))
  simp only [sum_const,nsmul_eq_mul,mul_one] at h
  exact ((h.trans (_root_.RHTower.Sieve.card_divisors_le_rpow hη hv.ne')).trans
    (mul_le_mul (le_abs_self _) (Real.rpow_le_rpow (Nat.cast_nonneg v) (Nat.cast_le.mpr hcap) hη.le)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) (abs_nonneg _))).trans (le_add_of_nonneg_left zero_le_one)

private theorem finite_cofactor_mass {η : ℝ} (hη : 0 < η) {n Q : ℕ} (hn : 0 < n) (hp : 0 < Q)
    (hcap : Q ≤ 4*n) :
    (∑ v ∈ Icc 2 (4*n/Q),squarefreeDivisorMass v*|centeredOrdinaryCofactorInterval n Q v|) ≤
      20*(n:ℝ)*samplingMass η n*(samplingLog n)^2 := by
  let S := Icc 2 (4*n/Q)
  let L := samplingLog n
  let M := samplingMass η n
  have hL : 1 ≤ L := sampling_log_one n
  have hM : 1 ≤ M := sampling_mass_one η n
  have hL0 := zero_le_one.trans hL
  have hM0 := zero_le_one.trans hM
  have subS : S ⊆ Icc 1 (4*n) := Icc_subset_Icc (by decide) (Nat.div_le_self _ _)
  have hpoint (v : ℕ) (hv : v ∈ S) :
      squarefreeDivisorMass v*|centeredOrdinaryCofactorInterval n Q v| ≤
        (20*(n:ℝ)*M*L)*(1/(v:ℝ)) := by
    obtain ⟨hv0,hv4⟩ := mem_Icc.mp (subS hv)
    have A := ordinary_cofactor_row_motion (Nat.zero_le n) hcap hv0
    have zero := beyond_cofactor_cut (m:=0) hp (by simpa using hv0 : 4*0/Q<v)
    rw [zero,sub_zero,Nat.cast_zero,sub_zero] at A
    let R := (n:ℝ)/v
    have hR : 1 ≤ 4*R := by
      rw [show 4*R=(4*(n:ℝ))/v by dsimp only [R]; ring,le_div_iff₀ (Nat.cast_pos.mpr hv0),one_mul]
      exact_mod_cast hv4
    have hR0 : 0 ≤ R := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hcost : |centeredOrdinaryCofactorInterval n Q v| ≤ 20*R*L := by
      change _ ≤ (6*R+2)*Real.log (4*n:ℕ)+6*R at A
      have ht := mul_le_mul_of_nonneg_right (show 6*R+2 ≤ 14*R by linarith only [hR])
        (Real.log_natCast_nonneg (4*n))
      have hl := mul_nonneg hR0 (Real.log_natCast_nonneg (4*n))
      dsimp only [L,samplingLog]
      linarith only [A,ht,hl,hR0]
    exact (mul_le_mul (sampling_divisor_mass hη hv0 hv4) hcost (abs_nonneg _) hM0).trans_eq
      (by dsimp only [R]; ring)
  apply (sum_le_sum hpoint).trans
  rw [←mul_sum]
  have h := (sum_le_sum_of_subset_of_nonneg (f:=fun v : ℕ => 1/(v:ℝ)) subS
    fun _ _ _ => by positivity).trans (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log (4*n))
  exact (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 20*(n:ℝ)*M*L)).trans_eq (by change _=20*(n:ℝ)*M*L^2; ring)

private theorem full_midpoint_motion {m n : ℕ} (hm : m ≤ n) :
    |primeMidpointPrice n-primeMidpointPrice m| ≤ 6*((n:ℝ)-m)*Real.log (4*n:ℕ) := by
  rcases eq_zero_or_pos n with rfl | hn
  · obtain rfl : m=0 := by omega
    simp
  have h (j : ℕ) (hj : 0 < j) (hj4 : j ≤ 4) :
      0 ≤ Chebyshev.theta (j*n:ℕ)-Chebyshev.theta (j*m:ℕ) ∧
      Chebyshev.theta (j*n:ℕ)-Chebyshev.theta (j*m:ℕ) ≤
        ((j:ℝ)*((n:ℝ)-m))*Real.log (4*n:ℕ) := by
    have hc := Nat.mul_le_mul_left j hm
    have ht := theta_integer_interval_bound hc
    refine ⟨sub_nonneg.mpr (Chebyshev.theta_mono (Nat.cast_le.mpr hc)),?_⟩
    apply ht.trans
    rw [Nat.cast_mul,Nat.cast_mul,←mul_sub]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (Nat.cast_pos.mpr (Nat.mul_pos hj hn))
      (Nat.cast_le.mpr (Nat.mul_le_mul_right n hj4))) (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (Nat.cast_le.mpr hm)))
  have h4 := h 4 (by decide) (by decide)
  have h3 := h 3 (by decide) (by decide)
  have h2 := h 2 (by decide) (by decide)
  simp only [Nat.cast_ofNat] at h4 h3 h2
  rw [prime_midpoint_price_eq,prime_midpoint_price_eq,abs_le]
  push_cast at h4 h3 h2 ⊢
  constructor <;> linarith only [h4.1,h4.2,h3.1,h3.2,h2.1,h2.2]

private theorem frozen_window (n Q d a L : ℕ) :
    (∑ k ∈ Ioc a (a+L), frozenOrdinaryCofactorPrice n Q (d*k))/L =
      ∑ v ∈ Icc 2 (4*n/Q), sampledCofactorFrequency v d a L*
        centeredOrdinaryCofactorInterval n Q v := by
  simp only [frozenOrdinaryCofactorPrice,sum_filter,sampledCofactorFrequency]
  rw [sum_comm,sum_div]
  apply sum_congr rfl
  intro v _
  rw [div_mul_eq_mul_div, sum_mul]
  exact congrArg (fun z : ℝ => z/L) (sum_congr rfl fun k _ => by split_ifs <;> simp)

private theorem projected_price_over_all (n Q : ℕ) {V : ℕ} (hV : 1 ≤ V) :
    projectedOrdinaryCofactorPrice n Q V =
      ∑ v ∈ Icc 2 (4*n/Q), (v.totient:ℝ)/v*truncMoebiusDivisorSum V v*
        centeredOrdinaryCofactorInterval n Q v := by
  apply sum_subset
  · intro v hv
    obtain ⟨hl,hr⟩ := mem_Ioc.mp hv
    exact mem_Icc.mpr ⟨by omega,hr⟩
  · intro v hv hx
    obtain ⟨hl,hr⟩ := mem_Icc.mp hv
    have hvV : v ≤ V := by simpa only [mem_Ioc,hr,and_true,not_lt] using hx
    rw [_root_.RHTower.truncMoebiusDivisorSum_of_le (by omega) hvV,if_neg (by omega),mul_zero,zero_mul]

/-- Signed averages of genuine ordinary prime intervals. Only the squarefree
divisor mass of each cofactor enters the finite-window discrepancy. -/
theorem signed_ordinary_cofactor_window (n Q : ℕ) {V : ℕ} (hV : 1 ≤ V) (a L : ℕ → ℕ)
    (hL : ∀ d ∈ Icc 1 V, 0 < L d) :
    |(∑ d ∈ Icc 1 V, mertens (V/d)*
      ((∑ k ∈ Ioc (a d) (a d+L d), frozenOrdinaryCofactorPrice n Q (d*k))/(L d:ℝ)))-
      projectedOrdinaryCofactorPrice n Q V| ≤
      (∑ v ∈ Icc 2 (4*n/Q), squarefreeDivisorMass v*|centeredOrdinaryCofactorInterval n Q v|)*
      ∑ d ∈ Icc 1 V, |mertens (V/d)| / (L d:ℝ) := by
  let Δ := centeredOrdinaryCofactorInterval n Q
  rw [projected_price_over_all n Q hV]
  simp only [frozen_window,mul_sum,←mul_assoc]
  rw [sum_comm]
  simp only [←sum_mul,←sum_sub_distrib,←sub_mul]
  apply (abs_sum_le_sum_abs _ _).trans
  rw [sum_mul]
  apply sum_le_sum
  intro v hv
  have h := signed_window_cofactor_density V (v:=v) (by have := (mem_Icc.mp hv).1; omega) a L hL
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right h (abs_nonneg (Δ v))).trans_eq (by ring)

/-- A window of H consecutive integers has at least ⌊H/d⌋ multiples of d.
The endpoint loss after signed sampling is at most twice the first moment
of the divisibility weights divided by H. -/
theorem ordinary_cofactor_window_cost {V H : ℕ} (hV : 1 ≤ V) (hVH : V ≤ H)
    (L : ℕ → ℕ) (hL : ∀ d ∈ Icc 1 V, H/d ≤ L d) :
    (∑ d ∈ Icc 1 V, |mertens (V/d)| / (L d:ℝ)) ≤ 2*(V:ℝ)^2/H := by
  have hH := (Nat.cast_pos (α:=ℝ)).mpr (lt_of_lt_of_le (by omega : 0 < V) hVH)
  rw [le_div_iff₀ hH,sum_mul]
  have hcost := (cofactor_projection_weight_cost V).2
  calc _ ≤ ∑ d ∈ Icc 1 V, 2*((d:ℝ)*|mertens (V/d)|) := by
             apply sum_le_sum
             intro d hd
             obtain ⟨hd0,hdV⟩ := mem_Icc.mp hd
             have hdH := hdV.trans hVH
             have hq := Nat.div_pos hdH hd0
             have hlen := hL d hd
             have hlt := Nat.lt_mul_div_succ H hd0
             have h1 := Nat.mul_le_mul_left d hq
             have h2 := Nat.mul_le_mul_left d hlen
             have hlen' := (Nat.cast_pos (α:=ℝ)).mpr (hq.trans_le hlen)
             have hbound : (H:ℝ) ≤ 2*((d:ℝ)*(L d:ℝ)) := by
               have hnat : H ≤ 2*(d*L d) := by
                 rw [Nat.mul_succ] at hlt
                 rw [Nat.mul_one] at h1
                 omega
               exact_mod_cast hnat
             calc _ = |mertens (V/d)| * ((H:ℝ)/L d) := by ring
                  _ ≤ |mertens (V/d)| * (2*d) := mul_le_mul_of_nonneg_left
                    ((div_le_iff₀ hlen').mpr (by linarith only [hbound])) (abs_nonneg _)
                  _ = _ := by ring
       _ ≤ _ := by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left hcost (by norm_num)

private theorem nearby_frozen_price {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m n H : ℕ}, 1 ≤ H → 2*H ≤ n → n ≤ H^2 →
      n-H < m → m ≤ n →
      |frozenOrdinaryCofactorPrice n (2*H) m-primeMidpointPrice n| ≤
        C*H*samplingMass η n*(samplingLog n)^2 := by
  obtain ⟨A,hA⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let K := max (4+|reflectedDensity|) 6
  have hK : 0 ≤ K := (by norm_num : (0:ℝ) ≤ 6).trans (le_max_right ..)
  let C := 32+2*|A|+2*K
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro m n H hH hshort hsquare hm hmn
  have hn : 0 < n := by omega
  have hm1 : 1 < m := by omega
  have hp : 0 < 2*H := by omega
  have hh : (1:ℝ) ≤ H := Nat.one_le_cast.mpr hH
  let T := 4*n/(2*H)
  let L := samplingLog n
  let M := samplingMass η n
  have hL := sampling_log_one n
  have hM := sampling_mass_one η n
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hTn : T ≤ 4*n := Nat.div_le_self .. 
  have hlog : 1+Real.log (T:ℝ) ≤ L := by
    rcases eq_zero_or_pos T with ht | ht
    · rw [ht,Nat.cast_zero,Real.log_zero,add_zero]; exact hL
    · exact add_le_add_right (Real.log_le_log (Nat.cast_pos.mpr ht) (Nat.cast_le.mpr hTn)) 1
  have hLM : Real.log (4*n:ℕ) ≤ L := le_add_of_nonneg_left zero_le_one
  have hlog0 := Real.log_natCast_nonneg (4*n)
  have d : (n:ℝ)-m ≤ H := by
    have ht : n ≤ H+m := by omega
    exact sub_le_iff_le_add.mpr (by exact_mod_cast ht)
  have hT : (T:ℝ) ≤ 2*H := by
    apply Nat.cast_div_le.trans
    rw [div_le_iff₀ (Nat.cast_pos.mpr hp)]
    push_cast
    have hs : (n:ℝ) ≤ (H:ℝ)^2 := by exact_mod_cast hsquare
    linarith only [hs]
  have ht := freeze_ordinary_cofactor_window hmn hp (by omega)
  have freeze : |frozenOrdinaryCofactorPrice n (2*H) m-frozenOrdinaryCofactorPrice m (2*H) m| ≤
      10*(H:ℝ)*L^2 := by
    have h1 := mul_le_mul (mul_le_mul_of_nonneg_left d (by norm_num : (0:ℝ) ≤ 6)) hlog
      (add_nonneg zero_le_one (Real.log_natCast_nonneg T)) (by positivity)
    have h2 := mul_le_mul hT hLM hlog0 (by positivity)
    have h3 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL hL0) (Nat.cast_nonneg (α:=ℝ) H)
    apply ht.trans
    change _ ≤ 10*(H:ℝ)*L^2
    change 6*((n:ℝ)-m)*(1+Real.log (T:ℝ))*L+2*(T:ℝ)*Real.log (4*n:ℕ) ≤ _
    linarith only [mul_le_mul_of_nonneg_right h1 hL0,h2,h3]
  have hs : Real.sqrt m ≤ H := (Real.sqrt_le_iff).mpr ⟨Nat.cast_nonneg H,by exact_mod_cast hmn.trans hsquare⟩
  have hcut : ⌊2*Real.sqrt m⌋₊ ≤ 2*H := Nat.floor_le_of_le (by
    push_cast; exact mul_le_mul_of_nonneg_left hs (by norm_num))
  have hproper := (hA ((4*m:ℕ):ℝ)).trans
    (mul_le_mul (le_abs_self A) (show Real.sqrt ((4*m:ℕ):ℝ) ≤ 2*H by
      rw [Nat.cast_mul,Nat.cast_ofNat,Real.sqrt_mul (by norm_num : (0:ℝ)≤4),show Real.sqrt 4=2 by norm_num]
      exact mul_le_mul_of_nonneg_left hs (by norm_num)) (Real.sqrt_nonneg _) (abs_nonneg _))
  have own := frozen_price_at_own_center_error hm1 hp hcut (by omega)
  have hown : |frozenOrdinaryCofactorPrice m (2*H) m-primeMidpointPrice m| ≤
      (15+2*|A|+2*K)*(H:ℝ)*M := by
    apply own.trans
    apply mul_le_mul _ (sampling_divisor_mass hη (by omega) (by omega)) (sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
    push_cast
    dsimp only [K] at ⊢
    linarith only [hproper,hh]
  have hd := (full_midpoint_motion hmn).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left d (by norm_num : (0:ℝ) ≤ 6)) hLM hlog0 (by positivity))
  have hL2 : 1 ≤ L^2 := one_le_pow₀ hL
  have hLsq : L ≤ L^2 := by rw [sq]; exact le_mul_of_one_le_right hL0 hL
  let W := (H:ℝ)*M*L^2
  have W1 : (H:ℝ)*L^2 ≤ W := by
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (Nat.cast_nonneg _) hM) (sq_nonneg L)
  have W2 : (H:ℝ)*M ≤ W := le_mul_of_one_le_right (by positivity) hL2
  have W3 : (H:ℝ)*L ≤ W := (mul_le_mul_of_nonneg_left hLsq (Nat.cast_nonneg H)).trans W1
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  rw [abs_le]
  have hf := abs_le.mp freeze
  have ho := abs_le.mp hown
  have hd' := abs_le.mp hd
  have b1 := mul_le_mul_of_nonneg_left W1 (by norm_num : (0:ℝ) ≤ 10)
  have b2 := mul_le_mul_of_nonneg_left W2 (by positivity : 0 ≤ 15+2*|A|+2*K)
  have b3 := mul_le_mul_of_nonneg_left W3 (by norm_num : (0:ℝ) ≤ 6)
  change -((32+2*|A|+2*K)*(H:ℝ)*M*L^2) ≤ _ ∧ _ ≤ _
  dsimp only [W] at b1 b2 b3 hW
  constructor <;> linarith only [hf.1,hf.2,ho.1,ho.2,hd'.1,hd'.2,b1,b2,b3,hW]

/-- For the actual backward sampling window all endpoints may be frozen
at the original midpoint. The total error retains the signed projection. -/
private theorem projected_price_window_estimate {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n V H : ℕ}, 1 ≤ V → V ≤ H → 2*H ≤ n → n*V ≤ H^2 →
      |projectedOrdinaryCofactorPrice n (2*H) V-primeMidpointPrice n| ≤
        C*(H:ℝ)*V*samplingMass η n*(samplingLog n)^3 := by
  obtain ⟨K,hK,hloc⟩ := nearby_frozen_price hη
  refine ⟨K+40,by positivity,?_⟩
  intro n V H hV hVH hn hsq
  have hH := hV.trans hVH
  have hH0 := (Nat.cast_pos (α:=ℝ)).mpr hH
  have hn0 : 0 < n := by omega
  have hnH := (Nat.le_mul_of_pos_right n hV).trans hsq
  let S := Icc 1 V
  let a (d : ℕ) := (n-H)/d
  let L (d : ℕ) := n/d-a d
  have endpoint (d : ℕ) : a d+L d=n/d :=
    Nat.add_sub_of_le (Nat.div_le_div_right (Nat.sub_le n H))
  have hlen (d : ℕ) (hd : d ∈ S) : H/d ≤ L d := by
    have hpos := (mem_Icc.mp hd).1
    have he : (a d+H/d)*d ≤ n := by
      rw [Nat.add_mul]
      exact (Nat.add_le_add (Nat.div_mul_le_self (n-H) d) (Nat.div_mul_le_self H d)).trans (by omega)
    have h := (Nat.le_div_iff_mul_le hpos).mpr he
    dsimp only [L]; omega
  have hp (d : ℕ) (hd : d ∈ S) : 0 < L d :=
    (Nat.div_pos ((mem_Icc.mp hd).2.trans hVH) (mem_Icc.mp hd).1).trans_le (hlen d hd)
  let X := primeMidpointPrice n
  let M := samplingMass η n
  let G := samplingLog n
  let B := K*H*M*G^2
  let F (d : ℕ) := (∑ k ∈ Ioc (a d) (a d+L d),frozenOrdinaryCofactorPrice n (2*H) (d*k))/(L d:ℝ)
  have hG : 1 ≤ G := sampling_log_one _
  have hM : 1 ≤ M := sampling_mass_one .. 
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have avg (d : ℕ) (hd : d ∈ S) : |F d-X| ≤ B := by
    have hd0 := (mem_Icc.mp hd).1
    have hterm (k : ℕ) (hk : k ∈ Ioc (a d) (a d+L d)) :
        |frozenOrdinaryCofactorPrice n (2*H) (d*k)-X| ≤ B := by
      obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hk
      rw [endpoint] at hhi
      exact hloc hH hn hnH ((Nat.div_lt_iff_lt_mul hd0).mp hlo |>.trans_eq (Nat.mul_comm k d))
        (((Nat.le_div_iff_mul_le hd0).mp hhi).trans_eq' (Nat.mul_comm d k))
    have hassoc : F d-X=(∑ k ∈ Ioc (a d) (a d+L d),(frozenOrdinaryCofactorPrice n (2*H) (d*k)-X))/(L d:ℝ) := by
      rw [sum_sub_distrib,sum_const,Nat.card_Ioc,Nat.add_sub_cancel_left,nsmul_eq_mul,sub_div,mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (hp d hd).ne')]
    rw [hassoc,abs_div,abs_of_nonneg (Nat.cast_nonneg _),div_le_iff₀ (Nat.cast_pos.mpr (hp d hd))]
    exact (abs_sum_le_sum_abs ..).trans ((sum_le_sum hterm).trans_eq (by simp [Nat.card_Ioc,mul_comm]))
  let U := ∑ d ∈ S,mertens (V/d)*F d
  have hU : |U-X| ≤ (V:ℝ)*G*B := by
    have eqn : U-X=∑ d ∈ S,mertens (V/d)*(F d-X) := by
      rw [show (∑ d ∈ S,mertens (V/d)*(F d-X))=
        (∑ d ∈ S,mertens (V/d)*F d)-(∑ d ∈ S,mertens (V/d))*X by simp only [mul_sub,sum_sub_distrib,sum_mul],
        show (∑ d ∈ S,mertens (V/d))=1 from sum_mertens_floor_eq_one hV,one_mul]
    rw [eqn]
    apply (abs_sum_le_sum_abs ..).trans
    calc _ ≤ ∑ d ∈ S,|mertens (V/d)|*B := sum_le_sum fun d hd => by
                rw [abs_mul]; exact mul_le_mul_of_nonneg_left (avg d hd) (abs_nonneg _)
         _ ≤ _ := by
           rw [←sum_mul]
           apply mul_le_mul_of_nonneg_right _ hB
           apply (cofactor_projection_weight_cost V).1.trans
           exact mul_le_mul_of_nonneg_left (add_le_add_right (Real.log_le_log (Nat.cast_pos.mpr hV)
             (Nat.cast_le.mpr (by omega : V ≤ 4*n))) 1) (Nat.cast_nonneg V)
  have hproj := signed_ordinary_cofactor_window n (2*H) hV a L hp
  change |U-projectedOrdinaryCofactorPrice n (2*H) V| ≤ _ at hproj
  have mass := finite_cofactor_mass hη hn0 (by omega : 0 < 2*H) (by omega : 2*H ≤ 4*n)
  have cost := ordinary_cofactor_window_cost hV hVH L hlen
  have bound := hproj.trans (mul_le_mul mass cost (sum_nonneg fun d _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) (by positivity))
  have hb : (n:ℝ)*(V:ℝ) ≤ (H:ℝ)^2 := by exact_mod_cast hsq
  have balance : (n:ℝ)*(2*(V:ℝ)^2/H) ≤ 2*H*V := by
    rw [←mul_div_assoc,div_le_iff₀ hH0]
    nlinarith only [mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg (α:=ℝ) V)]
  have hG3 : G^2 ≤ G^3 := by rw [pow_succ G 2]; exact le_mul_of_one_le_right (sq_nonneg _) hG
  have bd := mul_le_mul_of_nonneg_right balance (by positivity : 0 ≤ 20*M*G^2)
  have up := mul_le_mul_of_nonneg_left hG3 (by positivity : 0 ≤ 40*(H:ℝ)*V*M)
  rw [abs_le]
  have hu := abs_le.mp hU
  have hp' := abs_le.mp bound
  change -((K+40)*(H:ℝ)*V*M*G^3) ≤ _ ∧ _ ≤ _
  dsimp only [B] at hu
  change -_ ≤ U-projectedOrdinaryCofactorPrice n (2*H) V ∧ _ ≤ 20*(n:ℝ)*M*G^2*(2*(V:ℝ)^2/H) at hp'
  constructor <;> linarith only [hu.1,hu.2,hp'.1,hp'.2,bd,up]

/-- The backward averaging interval has length the ceiling of √(nV). -/
def cofactorSamplingWidth (n V : ℕ) := ⌈Real.sqrt ((n:ℝ)*V)⌉₊

private theorem balanced_sampling_width {n V : ℕ} (hn : 64 ≤ n) (hV : 1 ≤ V) (hV3 : V^3 ≤ n) :
    let H := cofactorSamplingWidth n V
    V ≤ H ∧ 2*H ≤ n ∧ n*V ≤ H^2 ∧ (H:ℝ) ≤ 2*Real.sqrt n*Real.sqrt V := by
  intro H
  have hn1 : (1:ℝ) ≤ n := Nat.one_le_cast.mpr (by omega)
  have hv1 : (1:ℝ) ≤ V := Nat.one_le_cast.mpr hV
  let R := Real.sqrt ((n:ℝ)*V)
  have hverts (v : ℕ) (hv : 1 ≤ v) : v ≤ v^3 := by
    have h := Nat.pow_le_pow_right hv (by decide : 1 ≤ 3)
    simpa only [pow_one] using h
  have hvn : V ≤ n := (hverts V hV).trans hV3
  have hdiv : 16*V ≤ n := by
    by_cases h : V < 4
    · omega
    · have hh := Nat.pow_le_pow_left (Nat.le_of_not_gt h) 2
      have h16 : 16 ≤ V^2 := hh
      exact (Nat.mul_le_mul_right V h16).trans ((pow_succ V 2).symm.le.trans hV3)
  have hr : R^2=(n:ℝ)*V := Real.sq_sqrt (by positivity)
  have hr0 : 0 ≤ R := Real.sqrt_nonneg _
  have hr1 : 1 ≤ R := Real.one_le_sqrt.mpr (one_le_mul_of_one_le_of_one_le hn1 hv1)
  have hlow : R ≤ (H:ℝ) := Nat.le_ceil _
  have hu : (H:ℝ) ≤ R+1 := (Nat.ceil_lt_add_one hr0).le
  refine ⟨Nat.cast_le.mp (le_trans ?_ hlow),?_,?_,?_⟩
  · apply (Real.le_sqrt (Nat.cast_nonneg _) (by positivity)).mpr
    simpa only [sq] using mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hvn : (V:ℝ) ≤ n) (Nat.cast_nonneg V)
  · have h16 : 16*(V:ℝ) ≤ n := by exact_mod_cast hdiv
    have hr4 : R ≤ (n:ℝ)/4 := (Real.sqrt_le_iff).mpr ⟨by positivity,by
      nlinarith only [mul_le_mul_of_nonneg_left h16 (Nat.cast_nonneg (α:=ℝ) n)]⟩
    have hn' : (64:ℝ) ≤ n := by exact_mod_cast hn
    have hh : 2*(H:ℝ) ≤ n := by linarith only [hu,hr4,hn']
    exact_mod_cast hh
  · have hh := pow_le_pow_left₀ hr0 hlow 2
    rw [hr] at hh
    exact_mod_cast hh
  · have ht : (H:ℝ) ≤ 2*R := by linarith only [hu,hr1]
    simpa only [R,Real.sqrt_mul (Nat.cast_nonneg (α:=ℝ) n),mul_assoc] using ht

/-- At every integer midpoint, signed sampling removes all proper
cofactors through V at cost Oε(n^(1/2+ε) V^(3/2)). -/
theorem ordinary_cofactor_signed_sampling {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ {n V : ℕ}, 1 ≤ V → V^3 ≤ n →
      |projectedOrdinaryCofactorPrice n (2*cofactorSamplingWidth n V) V-primeMidpointPrice n| ≤
        C*(n:ℝ)^(1/2+ε)*(V:ℝ)^(3/2:ℝ) := by
  let η := ε/2
  have hη : 0 < η := half_pos hε
  obtain ⟨K,hK,h⟩ := projected_price_window_estimate hη
  let J := (1+|_root_.RHTower.Sieve.divisorBoundConst η|)*(1+4/η)^3*(4:ℝ)^ε
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  let E (n V : ℕ) := |projectedOrdinaryCofactorPrice n (2*cofactorSamplingWidth n V) V-primeMidpointPrice n|
  let Z := ∑ n ∈ Icc 1 63,∑ V ∈ Icc 1 63,E n V
  have hZ : 0 ≤ Z := sum_nonneg fun n _ => sum_nonneg fun V _ => abs_nonneg _
  refine ⟨2*K*J+Z,?_⟩
  intro n V hV hV3
  have hv0 := (Nat.cast_pos (α:=ℝ)).mpr hV
  have hv1 := (Nat.one_le_cast (α:=ℝ)).mpr hV
  have hvn : V ≤ n := (by simpa only [pow_one] using Nat.pow_le_pow_right hV (by decide : 1 ≤ 3)).trans hV3
  have hn := hV.trans hvn
  have hn1 := (Nat.one_le_cast (α:=ℝ)).mpr hn
  have hn0 := (Nat.cast_pos (α:=ℝ)).mpr hn
  by_cases hlarge : 64 ≤ n
  · obtain ⟨hVH,hcut,hsq,hwidth⟩ := balanced_sampling_width hlarge hV hV3
    have bound := h hV hVH hcut hsq
    let X : ℝ := (4*n:ℕ)
    have hx : 1 ≤ X := Nat.one_le_cast.mpr (by omega : 1 ≤ 4*n)
    have hxp := Real.one_le_rpow hx hη.le
    have logbound := _root_.RHTower.one_add_log_pow_le_rpow 3 hη hx
    change (samplingLog n)^3 ≤ (1+((3:ℝ)+1)/η)^3*X^η at logbound
    norm_num only [show (3:ℝ)+1=4 by norm_num] at logbound
    have mass : samplingMass η n ≤ (1+|_root_.RHTower.Sieve.divisorBoundConst η|)*X^η := by
      dsimp only [samplingMass,X] at *
      linarith only [hxp]
    have ml := mul_le_mul mass logbound (pow_nonneg (zero_le_one.trans (sampling_log_one n)) _)
      (by positivity)
    have heq : ((1+|_root_.RHTower.Sieve.divisorBoundConst η|)*X^η)*((1+4/η)^3*X^η)=J*(n:ℝ)^ε := by
      have hp : X^η*X^η=X^ε := by rw [←Real.rpow_add (zero_lt_one.trans_le hx),show η+η=ε by dsimp only [η]; ring]
      calc _ = ((1+|_root_.RHTower.Sieve.divisorBoundConst η|)*(1+4/η)^3)*(X^η*X^η) := by ring
           _ = _ := by rw [hp]; dsimp only [X,J]; rw [Nat.cast_mul,Nat.cast_ofNat,Real.mul_rpow (by norm_num) hn0.le]; ring
    rw [heq] at ml
    have w := mul_le_mul_of_nonneg_right hwidth (Nat.cast_nonneg (α:=ℝ) V)
    have p := mul_le_mul w ml (mul_nonneg (zero_le_one.trans (sampling_mass_one η n))
      (pow_nonneg (zero_le_one.trans (sampling_log_one n)) _)) (by positivity)
    have veq : (V:ℝ)^(3/2:ℝ)=Real.sqrt V*V := by
      rw [show (3/2:ℝ)=1/2+1 by norm_num,Real.rpow_add hv0,Real.rpow_one,Real.sqrt_eq_rpow]
    rw [Real.rpow_add hn0,←Real.sqrt_eq_rpow,veq]
    have hb := mul_le_mul_of_nonneg_left p hK
    have hz := mul_nonneg hZ (mul_nonneg (mul_nonneg (Real.sqrt_nonneg n) (Real.rpow_nonneg hn0.le _))
      (mul_nonneg (Real.sqrt_nonneg V) (Nat.cast_nonneg V)))
    linarith only [bound,hb,hz]
  · have hh : E n V ≤ Z :=
      (single_le_sum (f:=E n) (fun _ _ => abs_nonneg _) (mem_Icc.mpr ⟨hV,by omega : V ≤ 63⟩)).trans
        (single_le_sum (s:=Icc 1 63) (f:=fun k => ∑ v ∈ Icc 1 63,E k v)
          (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_Icc.mpr ⟨hn,by omega⟩))
    have pos := add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK) hJ) hZ
    have h1 := Real.one_le_rpow hn1 (by linarith only [hε] : 0 ≤ 1/2+ε)
    have h2 := Real.one_le_rpow hv1 (by norm_num : (0:ℝ) ≤ 3/2)
    exact (hh.trans (le_add_of_nonneg_left (by positivity))).trans
      ((le_mul_of_one_le_right pos h1).trans (le_mul_of_one_le_right (mul_nonneg pos (zero_le_one.trans h1)) h2))

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
