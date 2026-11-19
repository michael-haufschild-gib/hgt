import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheSmallPrimeFactorsOfTheReflectedComposites
import GaloisForLFunctions.RHTower.Sieve.TotientMoebiusNormalisation

/-!
# Opposite cofactor prices across a moving cut

In the prime octave P < p ≤ 2P, split the two intervals about 3UP at
cofactor 2U. The upper part has a nonnegative continuous profile with
a corner at 3P/2. Its lower neighbor cancels that profile separately
for each prime, including primes at the moving endpoints.
-/

noncomputable section
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def primitiveCount (n w : ℕ) : ℝ :=
  (((Icc 1 w).filter (n.Coprime ·)).card : ℝ)

private theorem primitive_quotient_error {n p : ℕ} (hn : 0 < n) (hp : 0 < p) (T : ℕ) :
    |primitiveCount n (T/p)-(n.totient:ℝ)/n*((T:ℝ)/p)| ≤ squarefreeDivisorMass n := by
  rw [primitiveCount,_root_.RHTower.Sieve.coprimeCount_eq_sum_divisors hn,
    ←_root_.RHTower.Sieve.sum_moebius_div_divisors_eq_totient_div hn,sum_mul,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro d hd
  have hd0 := Nat.pos_of_mem_divisors hd
  have hpd := Nat.mul_pos hp hd0
  let m := T/(p*d)
  have hlo : (m:ℝ) ≤ (T:ℝ)/(p*d:ℕ) := Nat.cast_div_le
  have hhi : (T:ℝ)/(p*d:ℕ)<(m:ℝ)+1 := by
    apply (div_lt_iff₀ (Nat.cast_pos.mpr hpd)).mpr
    exact_mod_cast (show T<(m+1)*(p*d) by simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ T hpd)
  rw [Nat.div_div_eq_div_mul]
  have he : (μ d:ℝ)*(m:ℝ)-(μ d:ℝ)/d*((T:ℝ)/p) =
      (μ d:ℝ)*((m:ℝ)-(T:ℝ)/(p*d:ℕ)) := by
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he,abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ⟨by linarith only [hhi],by linarith only [hlo]⟩)

private def upperCofactorCount (n B w : ℕ) : ℝ :=
  (((Ioc B w).filter (n.Coprime ·)).card : ℝ)

private theorem upper_count_ge (n : ℕ) {B w : ℕ} (h : B ≤ w) :
    upperCofactorCount n B w=primitiveCount n w-primitiveCount n B := by
  let f (v : ℕ) : ℝ := if n.Coprime v then 1 else 0
  have hs (a b : ℕ) : (((Ioc a b).filter (n.Coprime ·)).card : ℝ) = ∑ v ∈ Ioc a b, f v := by
    dsimp only [f]
    rw [←sum_filter,sum_const,nsmul_eq_mul,mul_one]
  have hi (k : ℕ) : Icc 1 k=Ioc 0 k := by ext v; simp only [mem_Icc,mem_Ioc]; omega
  simp only [upperCofactorCount,primitiveCount,hi,hs]
  linarith only [sum_Ioc_consecutive f (Nat.zero_le B) h]

private theorem upper_count_le (n : ℕ) {B w : ℕ} (h : w ≤ B) : upperCofactorCount n B w=0 := by
  simp [upperCofactorCount,Ioc_eq_empty (not_lt.mpr h)]

/-- Right-minus-left cofactor count strictly above 2U in the two
adjacent intervals of length UP. -/
def upperOctaveCofactorCount (U P p : ℕ) : ℝ :=
  let n := U*P
  upperCofactorCount n (2*U) (4*n/p)-2*upperCofactorCount n (2*U) (3*n/p)+
    upperCofactorCount n (2*U) (2*n/p)

/-- Continuous cofactor length in units of U. -/
def upperOctaveProfile (P p : ℕ) : ℝ :=
  if 2*p ≤ 3*P then 2-2*(P:ℝ)/p else 4*(P:ℝ)/p-2

/-- The contribution above the moving cut has an explicit piecewise
reciprocal profile, uniformly including the corner and both ends. -/
theorem upper_octave_cofactor_profile {U P p : ℕ} (hU : 0 < U) (hP : 0 < P)
    (hl : P < p) (hu : p ≤ 2*P) :
    |upperOctaveCofactorCount U P p -
      ((U*P).totient:ℝ)/(U*P:ℕ)*(U:ℝ)*upperOctaveProfile P p| ≤ 4*squarefreeDivisorMass (U*P) := by
  let n := U*P
  have hn : 0 < n := Nat.mul_pos hU hP
  have hp : 0 < p := hP.trans hl
  have geom (k : ℕ) : 2*U ≤ k*n/p ↔ 2*p ≤ k*P := by
    rw [Nat.le_div_iff_mul_le hp,show 2*U*p=U*(2*p) by ring,show k*n=U*(k*P) by dsimp only [n]; ring]
    exact ⟨fun h => Nat.le_of_mul_le_mul_left h hU,Nat.mul_le_mul_left U⟩
  have h2 : 2*n/p ≤ 2*U := le_of_lt (lt_of_not_ge (fun h => by have := (geom 2).mp h; omega))
  have h4 := (geom 4).mpr (by omega)
  let density : ℝ := (n.totient:ℝ)/n
  have e (k : ℕ) : |primitiveCount n (k*n/p)-density*((k*n:ℕ)/ (p:ℝ))| ≤ squarefreeDivisorMass n :=
    primitive_quotient_error hn hp (k*n)
  have eB : |primitiveCount n (2*U)-density*(2*(U:ℝ))| ≤ squarefreeDivisorMass n := by
    simpa only [Nat.div_one,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,div_one] using
      primitive_quotient_error (p:=1) hn (by decide) (2*U)
  change |upperCofactorCount n (2*U) (4*n/p)-2*upperCofactorCount n (2*U) (3*n/p)+
      upperCofactorCount n (2*U) (2*n/p)-density*U*upperOctaveProfile P p| ≤ 4*squarefreeDivisorMass n
  rw [upper_count_ge _ h4,upper_count_le _ h2,add_zero]
  have hbase : 0 ≤ squarefreeDivisorMass n := sum_nonneg fun _ _ => abs_nonneg _
  have r4 := abs_le.mp (e 4)
  have rB := abs_le.mp eB
  by_cases hcut : 2*p ≤ 3*P
  · rw [upper_count_ge _ ((geom 3).mpr hcut),upperOctaveProfile,if_pos hcut,abs_le]
    have r3 := abs_le.mp (e 3)
    have hcent : density*((4*n:ℕ)/(p:ℝ))-2*(density*((3*n:ℕ)/(p:ℝ)))+density*(2*(U:ℝ)) =
        density*U*(2-2*(P:ℝ)/p) := by dsimp only [n]; push_cast; ring
    constructor <;> linarith only [r4.1,r4.2,r3.1,r3.2,rB.1,rB.2,hcent]
  · have h3 : 3*n/p ≤ 2*U := le_of_lt (lt_of_not_ge (fun h => hcut ((geom 3).mp h)))
    rw [upper_count_le _ h3,mul_zero,sub_zero,upperOctaveProfile,if_neg hcut,abs_le]
    have hcent : density*((4*n:ℕ)/(p:ℝ))-density*(2*(U:ℝ)) =
        density*U*(4*(P:ℝ)/p-2) := by dsimp only [n]; push_cast; ring
    constructor <;> linarith only [r4.1,r4.2,rB.1,rB.2,hcent,hbase]

/-- Net proper cofactor count after subtracting the upper part. For
p coprime to UP this counts the complementary range 2 ≤ v ≤ 2U. -/
def lowerOctaveCofactorCount (U P p : ℕ) : ℝ :=
  properCofactorMidpoint (U*P) p - upperOctaveCofactorCount U P p

private def upperOctaveMain (U P p : ℕ) : ℝ :=
  ((U*P).totient:ℝ)/(U*P:ℕ)*(U:ℝ)*upperOctaveProfile P p

private theorem octave_net_count {U P p : ℕ} (hU : 0 < U) (hP : 0 < P)
    (hp : p.Prime) (hu : p ≤ 2*P) :
    |properCofactorMidpoint (U*P) p| ≤ squarefreeDivisorMass (U*P) := by
  have hn := Nat.mul_pos hU hP
  have hPP : P ≤ U*P := by simpa only [one_mul] using Nat.mul_le_mul_right P hU
  have h2 : p ≤ 2*(U*P) := hu.trans (Nat.mul_le_mul_left 2 hPP)
  have h := prime_midpoint_count_split hn hp
  simp only [mem_Ioc,show ¬ 2*(U*P)<p by omega,show ¬ 3*(U*P)<p by omega,false_and,
    if_false,sub_self,add_zero] at h
  rw [←h]
  exact abs_coprime_midpoint_multiple_count hn hp.pos

/-- Through each prime, the two errors around the same opposite main
terms cost at most four and five squarefree divisor endpoints. -/
theorem opposite_octave_cofactor_profiles {U P p : ℕ} (hU : 0 < U) (hP : 0 < P)
    (hp : p.Prime) (hl : P < p) (hu : p ≤ 2*P) :
    let main := ((U*P).totient:ℝ)/(U*P:ℕ)*U*upperOctaveProfile P p
    |upperOctaveCofactorCount U P p - main| ≤ 4*squarefreeDivisorMass (U*P) ∧
    |lowerOctaveCofactorCount U P p + main| ≤ 5*squarefreeDivisorMass (U*P) := by
  dsimp only
  have h := upper_octave_cofactor_profile hU hP hl hu
  refine ⟨h,?_⟩
  have tri (x y : ℝ) : |x-y| ≤ |x|+|y| := by
    simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le x 0 y
  have hh := tri (properCofactorMidpoint (U*P) p) (upperOctaveCofactorCount U P p-upperOctaveMain U P p)
  change |properCofactorMidpoint (U*P) p-upperOctaveCofactorCount U P p+upperOctaveMain U P p| ≤ _
  rw [show properCofactorMidpoint (U*P) p-upperOctaveCofactorCount U P p+upperOctaveMain U P p =
      properCofactorMidpoint (U*P) p-(upperOctaveCofactorCount U P p-upperOctaveMain U P p) by ring]
  apply hh.trans
  linarith only [octave_net_count hU hP hp hu,(show |upperOctaveCofactorCount U P p-upperOctaveMain U P p| ≤ _ from h)]

/-- The opposite cofactor prices cancel to one endpoint per squarefree
divisor at every selected ordinary prime, including a partial octave. -/
theorem selected_octave_cofactor_cancellation {U P : ℕ} (hU : 0 < U) (hP : 0 < P)
    (S : Finset ℕ) (hS : S ⊆ (Ioc P (2*P)).filter Nat.Prime) :
    |∑ p ∈ S,Real.log p*(upperOctaveCofactorCount U P p+lowerOctaveCofactorCount U P p)| ≤
      (14*(P:ℝ))*squarefreeDivisorMass (U*P) := by
  have hmass : (∑ p ∈ S,Real.log p) ≤ 14*(P:ℝ) := by
    have hlog : (∑ p ∈ S,Real.log p)=∑ p ∈ S,vonMangoldt p := sum_congr rfl
      fun p hp => (vonMangoldt_apply_prime (mem_filter.mp (hS hp)).2).symm
    have hs : S ⊆ Icc 1 (2*P) := fun p hp => mem_Icc.mpr
      ⟨(mem_filter.mp (hS hp)).2.pos,(mem_Ioc.mp (mem_filter.mp (hS hp)).1).2⟩
    rw [hlog]
    apply (sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => vonMangoldt_nonneg)).trans
    exact (_root_.RHTower.sum_vonMangoldt_Icc_le_seven (2*P)).trans_eq (by push_cast; ring)
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ p ∈ S,Real.log p*squarefreeDivisorMass (U*P) := by
          apply sum_le_sum
          intro p hp
          obtain ⟨hi,hpr⟩ := mem_filter.mp (hS hp)
          have hlog := Real.log_nonneg (Nat.one_le_cast.mpr hpr.pos)
          rw [lowerOctaveCofactorCount,
            show upperOctaveCofactorCount U P p+(properCofactorMidpoint (U*P) p-upperOctaveCofactorCount U P p)=
              properCofactorMidpoint (U*P) p by ring,abs_mul,abs_of_nonneg hlog]
          exact mul_le_mul_of_nonneg_left (octave_net_count hU hP hpr (mem_Ioc.mp hi).2) hlog
       _ ≤ _ := by
          rw [←sum_mul]
          exact mul_le_mul_of_nonneg_right hmass (sum_nonneg fun _ _ => abs_nonneg _)

private theorem clipped_count_error {n p : ℕ} (hn : 0 < n) (hp : 0 < p) (B T : ℕ) :
    |upperCofactorCount n B (T/p)-(n.totient:ℝ)/n*max ((T:ℝ)/p-B) 0| ≤ 2*squarefreeDivisorMass n := by
  have hd : 0 ≤ squarefreeDivisorMass n := sum_nonneg fun _ _ => abs_nonneg _
  have hreal : B ≤ T/p ↔ (B:ℝ) ≤ (T:ℝ)/p := by
    rw [Nat.le_div_iff_mul_le hp,le_div_iff₀ (Nat.cast_pos.mpr hp)]
    exact_mod_cast Iff.rfl
  by_cases hB : B ≤ T/p
  · rw [upper_count_ge n hB,max_eq_left (sub_nonneg.mpr (hreal.mp hB)),abs_le]
    have hr := abs_le.mp (primitive_quotient_error hn hp T)
    have hl := abs_le.mp (primitive_quotient_error (p:=1) hn (by decide) B)
    simp only [Nat.div_one,Nat.cast_one,div_one] at hl
    constructor <;> linarith only [hr.1,hr.2,hl.1,hl.2]
  · rw [upper_count_le n (le_of_not_ge hB),max_eq_right (sub_nonpos.mpr (le_of_not_ge (fun h => hB (hreal.mpr h)))),
      mul_zero,sub_zero,abs_zero]
    linarith only [hd]

/-- Right-minus-left count at any closed upper cut on excluded cofactors.
All eligible cofactors strictly above B are included. -/
def midpointTailCount (n B p : ℕ) : ℝ :=
  upperCofactorCount n B (4*n/p)-2*upperCofactorCount n B (3*n/p)+upperCofactorCount n B (2*n/p)

/-- Continuous signed cofactor length above B at one prime. -/
def midpointTailLength (n B p : ℕ) : ℝ :=
  max ((4*n:ℕ)/(p:ℝ)-B) 0-2*max ((3*n:ℕ)/(p:ℝ)-B) 0+max ((2*n:ℕ)/(p:ℝ)-B) 0

private theorem tail_count_error {n p : ℕ} (hn : 0 < n) (hp : 0 < p) (B : ℕ) :
    |midpointTailCount n B p-(n.totient:ℝ)/n*midpointTailLength n B p| ≤ 8*squarefreeDivisorMass n := by
  have h4 := abs_le.mp (clipped_count_error hn hp B (4*n))
  have h3 := abs_le.mp (clipped_count_error hn hp B (3*n))
  have h2 := abs_le.mp (clipped_count_error hn hp B (2*n))
  rw [midpointTailCount,midpointTailLength,abs_le]
  constructor <;> linarith only [h4.1,h4.2,h3.1,h3.2,h2.1,h2.2]

private theorem past_last_cofactor {n p B : ℕ} (hp : 0 < p) (hB : 0 < B) (h : 4*n/B < p) :
    midpointTailCount n B p=0 ∧ midpointTailLength n B p=0 := by
  have hu := (Nat.div_lt_iff_lt_mul hB).mp h
  have hi {T : ℕ} (hT : T ≤ 4*n) : T/p ≤ B := le_of_lt
    ((Nat.div_lt_iff_lt_mul hp).mpr (by simpa only [Nat.mul_comm] using hT.trans_lt hu))
  have hr {T : ℕ} (hT : T ≤ 4*n) : (T:ℝ)/p-B ≤ 0 := by
    apply sub_nonpos.mpr ((div_le_iff₀ (Nat.cast_pos.mpr hp)).mpr ?_)
    exact_mod_cast (show T ≤ B*p by simpa only [Nat.mul_comm] using hT.trans hu.le)
  simp only [midpointTailCount,midpointTailLength,upper_count_le n (hi (by omega : 4*n ≤ 4*n)),
    upper_count_le n (hi (by omega : 3*n ≤ 4*n)),upper_count_le n (hi (by omega : 2*n ≤ 4*n)),
    max_eq_right (hr (by omega : 4*n ≤ 4*n)),max_eq_right (hr (by omega : 3*n ≤ 4*n)),
    max_eq_right (hr (by omega : 2*n ≤ 4*n)),mul_zero,sub_zero,add_zero,and_self]

/-- Signed discrepancy at one cofactor boundary, for the same selected
ordinary primes on both sides of the middle endpoint. -/
def cofactorBoundaryError (S : Finset ℕ) (n B : ℕ) : ℝ :=
  ∑ p ∈ S,Real.log p*(midpointTailCount n B p-(n.totient:ℝ)/n*midpointTailLength n B p)

/-- Only primes through 4n/B can incur discrepancy at boundary B,
independently of the lower prime cutoff or the selected prime subset. -/
theorem cofactor_boundary_error_bound {n B : ℕ} (hn : 0 < n) (hB : 0 < B)
    (S : Finset ℕ) (hS : ∀ p ∈ S,p.Prime) :
    |cofactorBoundaryError S n B| ≤ (56*((4*n/B:ℕ):ℝ))*squarefreeDivisorMass n := by
  let T := S.filter (· ≤ 4*n/B)
  let f (p : ℕ) := Real.log p*(midpointTailCount n B p-(n.totient:ℝ)/n*midpointTailLength n B p)
  have hs : T ⊆ S := filter_subset _ _
  have hshort : (∑ p ∈ T,f p) = cofactorBoundaryError S n B := by
    apply sum_subset hs
    intro p hp hnot
    have h := past_last_cofactor (n:=n) (hS p hp).pos hB
      (show 4*n/B < p from lt_of_not_ge (fun hh => hnot (mem_filter.mpr ⟨hp,hh⟩)))
    simp only [f,h.1,h.2,mul_zero,sub_zero]
  rw [←hshort]
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ p ∈ T,vonMangoldt p*(8*squarefreeDivisorMass n) := by
          apply sum_le_sum
          intro p hp
          have hpr := hS p (hs hp)
          dsimp only [f]
          rw [abs_mul,vonMangoldt_apply_prime hpr,abs_of_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hpr.pos))]
          exact mul_le_mul_of_nonneg_left (tail_count_error hn hpr.pos B) (Real.log_nonneg (Nat.one_le_cast.mpr hpr.pos))
       _ ≤ _ := by
          have hT : T ⊆ Icc 1 (4*n/B) := fun p hp => mem_Icc.mpr ⟨(hS p (hs hp)).pos,(mem_filter.mp hp).2⟩
          have hm := (sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => vonMangoldt_nonneg)).trans
            (_root_.RHTower.sum_vonMangoldt_Icc_le_seven (4*n/B))
          rw [←sum_mul]
          apply (mul_le_mul_of_nonneg_right hm (mul_nonneg (by norm_num) (sum_nonneg fun _ _ => abs_nonneg _))).trans_eq
          ring

/-- Across adjacent cofactor blocks every interior endpoint discrepancy
telescopes before taking absolute values. -/
theorem joint_cofactor_block_boundary (S : Finset ℕ) (n V W : ℕ) :
    (∑ p ∈ S,Real.log p*((midpointTailCount n V p-midpointTailCount n W p)-
      (n.totient:ℝ)/n*(midpointTailLength n V p-midpointTailLength n W p))) =
      cofactorBoundaryError S n V-cofactorBoundaryError S n W := by
  rw [cofactorBoundaryError,cofactorBoundaryError,←sum_sub_distrib]
  exact sum_congr rfl fun p _ => by ring

/-- If both reflected primitive integers have a prime factor above six,
their cofactors share exactly the part of the first integer dividing six. -/
theorem opposite_prime_cofactor_gcd {n a b p q : ℕ} (hs : a*p+b*q=6*n)
    (hn : (a*p).Coprime n) (hp : p.Prime) (hq : q.Prime) (hp6 : 6 < p) (hq6 : 6 < q) :
    a.gcd b = (a*p).gcd 6 := by
  apply Nat.dvd_antisymm
  · have hx := (Nat.gcd_dvd_left a b).trans (dvd_mul_right a p)
    have hy := (Nat.gcd_dvd_right a b).trans (dvd_mul_right b q)
    have hsum := Nat.dvd_add hx hy
    rw [hs] at hsum
    exact Nat.dvd_gcd hx ((Nat.Coprime.of_dvd_left hx hn).dvd_mul_right.mp hsum)
  · let d := (a*p).gcd 6
    have hd : d ∣ 6 := Nat.gcd_dvd_right _ _
    have hx : d ∣ a*p := Nat.gcd_dvd_left _ _
    have hy : d ∣ b*q := by
      rw [show b*q=6*n-a*p by omega]
      exact Nat.dvd_sub (hd.trans (dvd_mul_right 6 n)) hx
    have drop {r v : ℕ} (hr : r.Prime) (h6 : 6 < r) (h : d ∣ v*r) : d ∣ v := by
      have hc : r.Coprime d := hr.coprime_iff_not_dvd.mpr fun hrd =>
        (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 6) h6) (hrd.trans hd)
      exact hc.symm.dvd_mul_right.mp h
    exact Nat.dvd_gcd (drop hp hp6 hx) (drop hq hq6 hy)

/-- When both partners supply a large factor, their signed log price
differs from the log of the reversed cofactor ratio by at most log two. -/
theorem opposite_factor_log_price {n a b p q : ℕ} (hn : 0 < n) (hs : a*p+b*q=6*n)
    (hlo : 3*n ≤ a*p) (hhi : a*p ≤ 4*n) :
    0 ≤ Real.log p-Real.log q-Real.log ((b:ℝ)/a) ∧
      Real.log p-Real.log q-Real.log ((b:ℝ)/a) ≤ Real.log 2 := by
  have hx : 0 < a*p := by omega
  have hy : 0 < b*q := by omega
  obtain ⟨ha,hp⟩ := mul_ne_zero_iff.mp hx.ne'
  obtain ⟨hb,hq⟩ := mul_ne_zero_iff.mp hy.ne'
  have hy' := (Nat.cast_pos (α:=ℝ)).mpr hy
  have hratio : Real.log p-Real.log q-Real.log ((b:ℝ)/a) =
      Real.log (((a*p:ℕ):ℝ)/(b*q:ℕ)) := by
    rw [Real.log_div (Nat.cast_ne_zero.mpr hb) (Nat.cast_ne_zero.mpr ha),
      Real.log_div (Nat.cast_ne_zero.mpr hx.ne') (Nat.cast_ne_zero.mpr hy.ne')]
    simp only [Nat.cast_mul,Real.log_mul (Nat.cast_ne_zero.mpr ha) (Nat.cast_ne_zero.mpr hp),
      Real.log_mul (Nat.cast_ne_zero.mpr hb) (Nat.cast_ne_zero.mpr hq)]
    ring
  rw [hratio]
  constructor
  · apply Real.log_nonneg
    rw [le_div_iff₀ hy',one_mul]
    exact_mod_cast (show b*q ≤ a*p by omega)
  · apply Real.log_le_log (div_pos (Nat.cast_pos.mpr hx) hy')
    apply (div_le_iff₀ hy').mpr
    exact_mod_cast (show a*p ≤ 2*(b*q) by omega)

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
