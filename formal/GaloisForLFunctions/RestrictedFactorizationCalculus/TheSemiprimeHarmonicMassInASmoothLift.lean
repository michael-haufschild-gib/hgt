import GaloisForLFunctions.RestrictedFactorizationCalculus.TheCostOfFixingTheSemiprimes
import GaloisForLFunctions.RestrictedFactorizationCalculus.SignedFluxOnGrowingQuotientRanges
import GaloisForLFunctions.RHTower.Sieve.MertensSecond
import GaloisForLFunctions.RHTower.Sieve.AlmostPrimeGlobalCount
import GaloisForLFunctions.RHTower.RouteECofactorSquarefreeHarmonic

/-!
# The semiprime harmonic mass in the fixed boundary

Below the prime wall the fixed prefix is lifted over every quotient.
An error of square-root size per prefix costs a bounded amount after
normalizing this lift. The semiprime contribution is bracketed by the
second elementary symmetric sums of primes through √t and through t.
-/
noncomputable section
open Finset Filter RHTower.Sieve
open scoped Classical
open GaloisForLFunctions.QuantitativeFactorizationMatching
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev semis (t : ℕ) := (Icc 1 t).filter (· ∈ squarefreeSemiprimes)
private abbrev recip (n : ℕ) : ℝ := 1/(n:ℝ)
private abbrev pairs (t : ℕ) := ((Nat.primesLE t) ×ˢ (Nat.primesLE t)).filter fun a => a.1<a.2
private abbrev products (t : ℕ) := (pairs t).image (fun a => a.1*a.2)

/-- Reciprocal sum of the squarefree semiprimes through t. -/
def semiprimeHarmonicMass (t : ℕ) := ∑ n ∈ semis t,recip n

private theorem pair_product_injective (t : ℕ) : Set.InjOn (fun a : ℕ × ℕ => a.1*a.2) (↑(pairs t)) := by
  rintro ⟨p,q⟩ hpq ⟨r,s⟩ hrs eq
  obtain ⟨primes,lt⟩ := mem_filter.mp hpq
  obtain ⟨more,lt'⟩ := mem_filter.mp hrs
  obtain ⟨hp,hq⟩ := mem_product.mp primes
  obtain ⟨hr,hs⟩ := mem_product.mp more
  have first {a b c d : ℕ} (pa : a.Prime) (pb : b.Prime) (pc : c.Prime)
      (order : a<b) (same : a*b=c*d) : a ≤ c := by
    have dvd : c ∣ a*b := by rw [same]; exact Nat.dvd_mul_right c d
    rcases pc.dvd_mul.mp dvd with h | h
    · exact ((Nat.prime_dvd_prime_iff_eq pc pa).mp h).symm.le
    · exact order.le.trans ((Nat.prime_dvd_prime_iff_eq pc pb).mp h).symm.le
  change p*q=r*s at eq
  have e := le_antisymm (first (Nat.prime_of_mem_primesLE hp) (Nat.prime_of_mem_primesLE hq)
    (Nat.prime_of_mem_primesLE hr) lt eq) (first (Nat.prime_of_mem_primesLE hr) (Nat.prime_of_mem_primesLE hs)
    (Nat.prime_of_mem_primesLE hp) lt' eq.symm)
  change p = r at e
  subst r
  exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left (Nat.prime_of_mem_primesLE hp).pos eq)

private theorem symmetric_mass (t : ℕ) :
    2*(∑ n ∈ products t,recip n)+(∑ p ∈ Nat.primesLE t,recip p*recip p)=(mertensS t)^2 := by
  let P := Nat.primesLE t
  let E := ∑ p ∈ P,∑ q ∈ P,if p<q then recip p*recip q else 0
  have pair : (∑ n ∈ products t,recip n)=E := by
    rw [sum_image (fun _ h _ k eq => pair_product_injective t h k eq),sum_filter,sum_product]
    apply sum_congr rfl
    intro p _
    apply sum_congr rfl
    intro q _
    by_cases lt : p<q <;> simp [lt,recip,Nat.cast_mul,mul_comm]
  have flip : (∑ p ∈ P,∑ q ∈ P,if q<p then recip p*recip q else 0)=E := by
    rw [sum_comm]
    apply sum_congr rfl
    intro p _
    exact sum_congr rfl (fun q _ => by simp only [mul_comm (recip q) (recip p)])
  have split (p q : ℕ) : recip p*recip q=
      (if p<q then recip p*recip q else 0)+(if q<p then recip p*recip q else 0)+
        (if q=p then recip p*recip p else 0) := by
    rcases lt_trichotomy p q with lt | rfl | gt
    · simp [lt,lt.asymm,lt.ne']
    · simp
    · simp [gt,gt.asymm,gt.ne]
  have all := sum_congr (s₁ := P) rfl (fun p _ => sum_congr (s₁ := P) rfl (fun q _ => split p q))
  simp only [sum_add_distrib] at all
  have diag (p : ℕ) (hp : p ∈ P) : (∑ q ∈ P,if q=p then recip p*recip p else 0)=recip p*recip p := by simp [hp]
  rw [sum_congr rfl diag,flip] at all
  simp only [←mul_sum,←sum_mul] at all
  change 2*(∑ n ∈ products t,recip n)+_=(∑ p ∈ P,recip p)^2
  rw [pair,pow_two,all]; ring

/-- Truncating both independent primes at √t gives the lower bound.
Allowing both through t gives the upper bound. The repeated prime is removed. -/
theorem harmonic_semiprime_sandwich (t : ℕ) :
    (mertensS t.sqrt)^2-mertensS t.sqrt ≤ 2*semiprimeHarmonicMass t ∧
      2*semiprimeHarmonicMass t ≤ (mertensS t)^2 := by
  have lower : products t.sqrt ⊆ semis t := by
    intro n hn
    obtain ⟨⟨p,q⟩,pair,rfl⟩ := mem_image.mp hn
    obtain ⟨both,order⟩ := mem_filter.mp pair
    obtain ⟨hp,hq⟩ := mem_product.mp both
    have pp := Nat.prime_of_mem_primesLE hp
    have qp := Nat.prime_of_mem_primesLE hq
    have size := (Nat.mul_le_mul (Nat.mem_primesLE.mp hp).1 (Nat.mem_primesLE.mp hq).1).trans (Nat.sqrt_le t)
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos pp.pos qp.pos,size⟩,
      RHTower.PrimeCells.squarefree_card_primeFactors_two_iff.mpr ⟨p,q,pp,qp,order,rfl⟩⟩
  have upper : semis t ⊆ products t := by
    intro n hn
    obtain ⟨inside,sq⟩ := mem_filter.mp hn
    obtain ⟨p,q,pp,qp,lt,rfl⟩ := RHTower.PrimeCells.squarefree_card_primeFactors_two_iff.mp sq
    have hp := (Nat.le_mul_of_pos_right p qp.pos).trans (mem_Icc.mp inside).2
    have hq := (Nat.le_mul_of_pos_left q pp.pos).trans (mem_Icc.mp inside).2
    exact mem_image.mpr ⟨(p,q),mem_filter.mpr ⟨mem_product.mpr ⟨Nat.mem_primesLE.mpr ⟨hp,pp⟩,
      Nat.mem_primesLE.mpr ⟨hq,qp⟩⟩,lt⟩,rfl⟩
  have grow {A B : Finset ℕ} (sub : A ⊆ B) : (∑ n ∈ A,recip n) ≤ ∑ n ∈ B,recip n :=
    sum_le_sum_of_subset_of_nonneg sub (fun n _ _ => by dsimp [recip]; positivity)
  have diag (x : ℕ) : (∑ p ∈ Nat.primesLE x,recip p*recip p) ≤ mertensS x := by
    apply sum_le_sum
    intro p hp
    have pos : (1:ℝ) ≤ p := Nat.one_le_cast.mpr (Nat.prime_of_mem_primesLE hp).pos
    exact mul_le_of_le_one_right (by dsimp [recip]; positivity) ((div_le_one (zero_lt_one.trans_le pos)).mpr pos)
  have nonneg := sum_nonneg (s := Nat.primesLE t) (fun p _ => mul_self_nonneg (recip p))
  unfold semiprimeHarmonicMass
  exact ⟨by linarith only [symmetric_mass t.sqrt,diag t.sqrt,grow lower],
    by linarith only [symmetric_mass t,nonneg,grow upper]⟩

private theorem lifted_card_as_floor_sum (t : ℕ) :
    (∑ d ∈ Icc 1 t,(squarefreeOmegaCount 2 (t/d):ℝ))=∑ m ∈ semis t,((t/m:ℕ):ℝ) := by
  have each (d : ℕ) (hd : d ∈ Icc 1 t) :
      (squarefreeOmegaCount 2 (t/d):ℝ)=∑ m ∈ semis t,if m ≤ t/d then (1:ℝ) else 0 := by
    have eq : (semis t).filter (· ≤ t/d)=semis (t/d) := by
      ext n; simp only [mem_filter,mem_Icc]
      constructor
      · rintro ⟨⟨⟨np,_⟩,sq⟩,hi⟩; exact ⟨⟨np,hi⟩,sq⟩
      · rintro ⟨⟨np,hi⟩,sq⟩; exact ⟨⟨⟨np,hi.trans (Nat.div_le_self ..)⟩,sq⟩,hi⟩
    rw [←sum_filter,eq,sum_const,nsmul_eq_mul,mul_one]
    congr 1
    unfold squarefreeOmegaCount
    apply congrArg Finset.card
    ext n
    simp only [semis,mem_filter,squarefreeSemiprimes,Set.mem_setOf_eq]
  rw [sum_congr rfl each,sum_comm]
  apply sum_congr rfl
  intro m hm
  have mp := (mem_Icc.mp (mem_filter.mp hm).1).1
  have eq : (Icc 1 t).filter (fun d => m ≤ t/d)=Icc 1 (t/m) := by
    ext d
    rw [mem_filter,mem_Icc,mem_Icc]
    by_cases pos : 0<d
    · simp only [Nat.le_div_iff_mul_le pos,Nat.le_div_iff_mul_le mp]
      constructor
      · rintro ⟨⟨p,_⟩,h⟩; exact ⟨p,by simpa only [Nat.mul_comm d m] using h⟩
      · rintro ⟨p,h⟩
        have h' := (Nat.le_div_iff_mul_le mp).mpr h
        exact ⟨⟨p,h'.trans (Nat.div_le_self ..)⟩,by simpa only [Nat.mul_comm m d] using h⟩
    · simp [show d=0 by omega]
  rw [←sum_filter,eq]
  simp

/-- The reciprocal semiprime mass and the actual normalized fixed lift
differ by an absolute constant, uniformly all the way to the sieve wall. -/
theorem fixed_lift_tracks_the_semiprime_harmonic_mass {G : ℕ → ℕ}
    (prescribed : ∀ t : ℕ,0<t → |fixedSignedPrefix G t-((squarefreeOmegaCount 2 t:ℝ)+1)| ≤ Real.sqrt t)
    {y t : ℕ} (tp : 0<t) (wall : t ≤ y) :
    |smoothLiftedPrefix (fixedSignedPrefix G) y t/(t:ℝ)-semiprimeHarmonicMass t| ≤ 4 := by
  let S := Icc 1 t
  let F := smoothLiftedPrefix (fixedSignedPrefix G) y t
  have t0 : 0<(t:ℝ) := Nat.cast_pos.mpr tp
  have eq : RHTower.Sieve.smoothUpTo (Nat.primesLE y) t=S := by
    apply filter_eq_self.mpr
    intro d hd p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (mem_Icc.mp hd).1 (Nat.dvd_of_mem_primeFactors hp)).trans
      ((mem_Icc.mp hd).2.trans wall),Nat.prime_of_mem_primeFactors hp⟩
  have floor (m : ℕ) (mp : 0< m) : ((t/m:ℕ):ℝ) ≤ (t:ℝ)/m :=
    (le_div_iff₀ (Nat.cast_pos.mpr mp)).mpr (by exact_mod_cast Nat.div_mul_le_self t m)
  have one (d : ℕ) (hd : d ∈ S) : |fixedSignedPrefix G (t/d)-((squarefreeOmegaCount 2 (t/d):ℝ)+1)| ≤
      Real.sqrt t*(Real.sqrt d)⁻¹ := by
    have dp := (mem_Icc.mp hd).1
    have hit := (Nat.le_div_iff_mul_le dp).mpr (by simpa using (mem_Icc.mp hd).2 : 1*d ≤ t)
    have small := Real.sqrt_le_sqrt (floor d dp)
    rw [Real.sqrt_div t0.le] at small
    exact (prescribed _ hit).trans (small.trans_eq (div_eq_mul_inv ..))
  have sum := (abs_sum_le_sum_abs ..).trans (sum_le_sum one)
  rw [sum_sub_distrib,sum_add_distrib,←mul_sum] at sum
  have square : Real.sqrt t * (∑ d ∈ S, (Real.sqrt d)⁻¹) ≤ 2*(t:ℝ) := calc
    _ ≤ Real.sqrt t * (2 * Real.sqrt t) :=
      mul_le_mul_of_nonneg_left (RHTower.Sieve.sum_sqrtInv_le t) (Real.sqrt_nonneg t)
    _ = 2*(t:ℝ) := by rw [mul_left_comm,Real.mul_self_sqrt t0.le]
  have err := sum.trans square
  change |(∑ d ∈ S,fixedSignedPrefix G (t/d))-((∑ d ∈ S,(squarefreeOmegaCount 2 (t/d):ℝ))+∑ _d ∈ S,(1:ℝ))| ≤ 2*t at err
  have fixedSum : (∑ d ∈ S,fixedSignedPrefix G (t/d))=F := by
    change _=∑ d ∈ RHTower.Sieve.smoothUpTo (Nat.primesLE y) t,fixedSignedPrefix G (t/d)
    rw [eq]
  rw [fixedSum,show (∑ _d ∈ S,(1:ℝ))=t by simp [S],lifted_card_as_floor_sum] at err
  have residue (m : ℕ) (hm : m ∈ semis t) :
      |((t/m:ℕ):ℝ)-(t:ℝ)*recip m| ≤ 1 := by
    have mp := (mem_Icc.mp (mem_filter.mp hm).1).1
    have natGap : t ≤ (t/m+1)*m := calc
      t = m*(t/m)+t%m := (Nat.div_add_mod t m).symm
      _ ≤ (t/m+1)*m := by
        rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm m]
        exact Nat.add_le_add_left (Nat.mod_lt _ mp).le _
    have gap : (t:ℝ)/m ≤ ((t/m:ℕ):ℝ)+1 :=
      (div_le_iff₀ (Nat.cast_pos.mpr mp)).mpr (by exact_mod_cast natGap)
    rw [show (t:ℝ)*recip m=(t:ℝ)/m by dsimp only [recip]; ring]
    exact abs_le.mpr ⟨by linarith only [gap],by linarith only [floor m mp]⟩
  have rounding := (abs_sum_le_sum_abs ..).trans (sum_le_sum residue)
  rw [sum_sub_distrib,←mul_sum,sum_const,nsmul_eq_mul,mul_one] at rounding
  have count : (semis t).card ≤ t := (card_filter_le ..).trans (by simp)
  have total : |F-(t:ℝ)*semiprimeHarmonicMass t| ≤ 4*t := by
    have lift := abs_le.mp err
    have rounded := abs_le.mp rounding
    dsimp only [semiprimeHarmonicMass]
    exact abs_le.mpr ⟨by linarith only [lift.1,rounded.1,(Nat.cast_le (α := ℝ)).mpr count,t0],
      by linarith only [lift.2,rounded.2,(Nat.cast_le (α := ℝ)).mpr count]⟩
  rw [show F/(t:ℝ)-semiprimeHarmonicMass t=(F-t*semiprimeHarmonicMass t)/(t:ℝ) by field_simp [t0.ne'],
    abs_div,abs_of_pos t0]
  exact (div_le_iff₀ t0).mpr total

private theorem semiprime_harmonic_profile :
    ∃ C : ℝ,0 ≤ C ∧ ∀ᶠ t : ℕ in atTop,|semiprimeHarmonicMass t-(logLog t)^2/2| ≤ C*(1+logLog t) := by
  let K := 1+|mertensSecondUpperConst|+|mertensSecondLowerConst|+Real.log 4
  have log4 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
  have k1 : 1 ≤ K := by dsimp only [K]; linarith only [abs_nonneg mertensSecondUpperConst,abs_nonneg mertensSecondLowerConst,log4]
  have k0 := zero_le_one.trans k1
  have top : Tendsto (fun t : ℕ => logLog t) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine ⟨K^2+2*K+2,by positivity,?_⟩
  filter_upwards [top.eventually_ge_atTop (K+1),eventually_ge_atTop (16:ℕ)] with t late big
  let u := t.sqrt
  let L := logLog t
  have l0 : 0 ≤ L := by linarith only [late,k0]
  have up : 2 ≤ u := Nat.le_sqrt.mpr (by omega)
  have ur : (2:ℝ) ≤ u := by exact_mod_cast up
  have t0 : 0<(t:ℝ) := Nat.cast_pos.mpr (by omega)
  have u0 : 0<(u:ℝ) := by linarith only [ur]
  have uq : (u:ℝ)+1 ≤ (u:ℝ)^2 := by nlinarith only [ur,mul_nonneg (sub_nonneg.mpr ur) u0.le]
  have sq : t<(u+1)*(u+1) := lt_of_not_ge (fun h => (Nat.not_succ_le_self u) (Nat.le_sqrt.mpr h))
  have bound : (t:ℝ) ≤ (u:ℝ)^4 := by
    have h : (t:ℝ) ≤ ((u:ℝ)+1)*((u:ℝ)+1) := by exact_mod_cast sq.le
    have prod := mul_self_le_mul_self (by positivity : 0 ≤ (u:ℝ)+1) uq
    exact h.trans (prod.trans_eq (by ring))
  have ulo : 0<Real.log u := Real.log_pos (by linarith only [ur])
  have tp : 1<(t:ℝ) := by exact_mod_cast (show 1<t by omega)
  have outer := Real.log_le_log (Real.log_pos tp) (Real.log_le_log t0 bound)
  rw [Real.log_pow] at outer
  norm_num1 at outer
  rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) ulo.ne'] at outer
  have lower : L-K ≤ mertensS u := by
    have h := le_mertensS up
    change L ≤ Real.log 4+logLog u at outer
    dsimp only [K] at *
    linarith only [outer,h,le_abs_self mertensSecondLowerConst,abs_nonneg mertensSecondUpperConst]
  have upper : mertensS t ≤ L+K := by
    have h := mertensS_le (by omega : 2 ≤ t)
    dsimp only [K]
    linarith only [h,le_abs_self mertensSecondUpperConst,abs_nonneg mertensSecondLowerConst,log4]
  have m0 : 0 ≤ mertensS t := sum_nonneg (fun n _ => by positivity)
  have upperSq := mul_self_le_mul_self m0 upper
  have lowerSq := mul_nonneg (sub_nonneg.mpr lower)
    (by linarith only [lower,late] : 0 ≤ mertensS u+(L-K)-1)
  have price := harmonic_semiprime_sandwich t
  change |semiprimeHarmonicMass t-L^2/2| ≤ (K^2+2*K+2)*(1+L)
  apply abs_le.mpr
  constructor <;> nlinarith only [price.1,price.2,upperSq,lowerSq,k0,l0,sq_nonneg K,
    mul_nonneg k0 l0,mul_nonneg (sq_nonneg K) l0]

/-- One density-one legal matching has the predicted semiprime mass in its
normalized fixed lift, uniformly for all walls above a given quotient. -/
theorem a_semiprime_prescription_in_the_original_quotient_lift :
    ∃ (G : ℕ → ℕ) (C : ℝ),Function.Involutive G ∧ (∀ n,G n=n ∨ GlobalDyadicOneTwoRel n (G n)) ∧
      (∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,((prefixUnpaid G X).card:ℝ) ≤ ε*X) ∧ 0 ≤ C ∧
      ∀ᶠ t : ℕ in atTop,∀ y : ℕ,t ≤ y →
        |smoothLiftedPrefix (fixedSignedPrefix G) y t/(t:ℝ)-(logLog t)^2/2| ≤ C*(1+logLog t) := by
  have root : Tendsto (fun t : ℕ => Real.sqrt t) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨G,back,legal,sparse,prescribed⟩ := opposite_charges_from_the_semiprime_population _ (fun t => Real.sqrt_nonneg _) root
  obtain ⟨C,c0,asymp⟩ := semiprime_harmonic_profile
  have top : Tendsto (fun t : ℕ => logLog t) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine ⟨G,C+4,back,legal,sparse,by linarith only [c0],?_⟩
  filter_upwards [asymp,top.eventually_ge_atTop 0,eventually_ge_atTop (1:ℕ)] with t profile l0 tp
  intro y wall
  have near := fixed_lift_tracks_the_semiprime_harmonic_mass (fun z zp => (prescribed z zp).1) tp wall
  have tri := abs_sub_le (smoothLiftedPrefix (fixedSignedPrefix G) y t/(t:ℝ)) (semiprimeHarmonicMass t) ((logLog t)^2/2)
  linarith only [tri,near,profile,l0]

end GaloisForLFunctions.RestrictedFactorizationCalculus
