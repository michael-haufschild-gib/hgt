import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.FullPrimeFrequencySupportOfTheMoebiusAmbiguity
import Mathlib.RingTheory.PowerBasis
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Vanishing of integral Fourier readings at prime-power order

Reduce the sample exponents modulo the character order p^(k+1).
The reading vanishes precisely when the p lifts of each residue
modulo p^k have equal coefficient sums. Subtracting one lift leaves
the first φ(p^(k+1)) powers, which are rationally independent.
-/
noncomputable section
open Finset Complex Polynomial
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

private theorem block_criterion {t k : ℕ} (hp : (t+1).Prime) {z : ℂ}
    (hz : IsPrimitiveRoot z ((t+1)^(k+1))) (f : Fin (t+1) → Fin ((t+1)^k) → ℤ) :
    (∑ j, ∑ r, (f j r:ℂ)*z^(r.val+(t+1)^k*j.val))=0 ↔
      ∀ r j l, f j r=f l r := by
  let m := (t+1)^k
  have hm : 0 < m := pow_pos hp.pos _
  have hd : (minpoly ℚ z).natDegree=t*m := by
    rw [←cyclotomic_eq_minpoly_rat hz (pow_pos hp.pos _),natDegree_cyclotomic,Nat.totient_prime_pow_succ hp]
    simp only [Nat.add_sub_cancel]; exact Nat.mul_comm _ _
  have hli : LinearIndependent ℚ (fun i : Fin (t*m) => z^i.val) := by
    rw [← hd]
    exact linearIndependent_pow (K := ℚ) z
  let e : Fin t × Fin m ≃ Fin (t*m) := finProdFinEquiv
  have hbase := hli.comp (fun i => e i) e.injective
  have root : IsPrimitiveRoot (z^m) (t+1) := by
    have h := hz.pow_of_dvd hm.ne' (show m ∣ (t+1)^(k+1) from ⟨t+1,pow_succ _ _⟩)
    change IsPrimitiveRoot (z^m) (m*(t+1)/m) at h
    simpa only [Nat.mul_div_cancel_left _ hm] using h
  have hsum : ∑ j : Fin (t+1), (z^m)^j.val=0 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => (z^m)^j)]
    exact root.geom_sum_eq_zero hp.one_lt
  let b := fun r : Fin m => f (Fin.last t) r
  have hflat : (∑ j : Fin (t+1), ∑ r : Fin m, (b r:ℂ)*z^(r.val+m*j.val)) = 0 := by
    rw [sum_comm]
    refine sum_eq_zero fun r _ => ?_
    simp only [pow_add,pow_mul,←mul_assoc,←mul_sum,hsum,mul_zero]
  constructor
  · intro h
    let g (i : Fin t × Fin m) : ℚ := (f i.1.castSucc i.2:ℚ)-b i.2
    have hdiff : (∑ j : Fin (t+1), ∑ r : Fin m,
        ((f j r:ℂ)-(b r:ℂ))*z^(r.val+m*j.val))=0 := by
      simp_rw [sub_mul,sum_sub_distrib]
      exact sub_eq_zero.mpr (h.trans hflat.symm)
    rw [Fin.sum_univ_castSucc] at hdiff
    simp only [b,sub_self,zero_mul,sum_const_zero,add_zero,Fin.val_castSucc] at hdiff
    have hzero : ∑ i : Fin t × Fin m, g i • z^(e i).val = 0 := by
      rw [Fintype.sum_prod_type]
      change (∑ j : Fin t, ∑ r : Fin m, g (j,r) • z^(r.val+m*j.val))=0
      simpa [g,b,Algebra.smul_def] using hdiff
    have ha := (Fintype.linearIndependent_iff.mp hbase) g hzero
    have heq (j : Fin (t+1)) (r : Fin m) : f j r = b r := by
      refine Fin.lastCases (motive := fun l => f l r=b r) rfl (fun i => ?_) j
      have hh := ha (i,r)
      change (f i.castSucc r:ℚ)-(b r:ℚ)=0 at hh
      exact_mod_cast sub_eq_zero.mp hh
    exact fun r j l => (heq j r).trans (heq l r).symm
  · intro heq
    calc
      _ = ∑ j : Fin (t+1), ∑ r : Fin m, (b r:ℂ)*z^(r.val+m*j.val) :=
        sum_congr rfl fun j _ => sum_congr rfl fun r _ =>
          congrArg (fun c : ℤ => (c:ℂ)*z^(r.val+m*j.val)) (heq r j (Fin.last t))
      _ = 0 := hflat

/-- Coordinates of an exponent reduced modulo p^(k+1). The second
coordinate is its residue modulo p^k; the first distinguishes its lifts. -/
def primePowerDigits (p k : ℕ) [Fact p.Prime] (u : ℕ) : Fin p × Fin (p^k) :=
  finProdFinEquiv.symm ⟨u%(p*p^k),Nat.mod_lt _ (Nat.mul_pos (Fact.out : p.Prime).pos
    (pow_pos (Fact.out : p.Prime).pos _))⟩

private theorem digits_power {p k : ℕ} [Fact p.Prime] {z : ℂ}
    (hz : IsPrimitiveRoot z (p^(k+1))) (u : ℕ) :
    z^u=z^((primePowerDigits p k u).2.val+p^k*(primePowerDigits p k u).1.val) := by
  have h := congrArg Fin.val (finProdFinEquiv.apply_symm_apply
    (⟨u%(p*p^k),Nat.mod_lt _ (Nat.mul_pos (Fact.out : p.Prime).pos (pow_pos (Fact.out : p.Prime).pos _))⟩ :
      Fin (p*p^k)))
  change (primePowerDigits p k u).2.val+p^k*(primePowerDigits p k u).1.val=u%(p*p^k) at h
  rw [h]
  have hw : z^(p*p^k)=1 := by simpa only [pow_succ'] using hz.pow_eq_one
  calc z^u = z^(u%(p*p^k)+(p*p^k)*(u/(p*p^k))) := congrArg (z^·) (Nat.mod_add_div _ _).symm
       _ = z^(u%(p*p^k)) := by rw [pow_add,pow_mul,hw,one_pow,mul_one]

/-- Integer sample mass in one lifted residue class. -/
def liftedFrequencyMass {ι : Type*} [Fintype ι] (p k : ℕ) [Fact p.Prime]
    (a : ι → ℤ) (u : ι → ℕ) (j : Fin p) (r : Fin (p^k)) : ℤ :=
  ∑ i ∈ univ.filter (fun i => primePowerDigits p k (u i)=(j,r)),a i

/-- At every prime-power order, vanishing is equivalent to equality
of the p lifted masses above each lower residue, for arbitrary finite
integer samples with arbitrary exponent multiplicities. -/
theorem prime_power_fourier_zero_iff_equal_lifts {ι : Type*} [Fintype ι]
    {p k : ℕ} [Fact p.Prime] {z : ℂ} (hz : IsPrimitiveRoot z (p^(k+1)))
    (a : ι → ℤ) (u : ι → ℕ) :
    (∑ i,(a i:ℂ)*z^(u i))=0 ↔
      ∀ r j l,liftedFrequencyMass p k a u j r=liftedFrequencyMass p k a u l r := by
  classical
  have hp : p.Prime := Fact.out
  let d := fun i => primePowerDigits p k (u i)
  have hs : ∑ i,(a i:ℂ)*z^(u i) =
      ∑ j,∑ r,(liftedFrequencyMass p k a u j r:ℂ)*z^(r.val+p^k*j.val) := by
    rw [←Fintype.sum_prod_type (fun x : Fin p × Fin (p^k) =>
      (liftedFrequencyMass p k a u x.1 x.2 : ℂ) * z^(x.2.val+p^k*x.1.val)),
      ←sum_fiberwise univ d (fun i => (a i:ℂ)*z^(u i))]
    refine sum_congr rfl fun x _ => ?_
    simp only [liftedFrequencyMass,Int.cast_sum,sum_mul]
    refine sum_congr rfl fun i hi => ?_
    have he : primePowerDigits p k (u i)=x := (mem_filter.mp hi).2
    rw [digits_power hz,he]
  rw [hs]
  cases p with
  | zero => exact False.elim (Nat.not_prime_zero hp)
  | succ t => exact block_criterion hp hz _

/-- A vanishing prime-power reading forces its underlying integer
total to be divisible by that prime. -/
theorem prime_dvd_total_of_prime_power_fourier_zero {ι : Type*} [Fintype ι]
    {p k : ℕ} [Fact p.Prime] {z : ℂ} (hz : IsPrimitiveRoot z (p^(k+1)))
    (a : ι → ℤ) (u : ι → ℕ) (h : (∑ i,(a i:ℂ)*z^(u i))=0) :
    (p:ℤ) ∣ ∑ i,a i := by
  classical
  have he := (prime_power_fourier_zero_iff_equal_lifts hz a u).mp h
  let f := liftedFrequencyMass p k a u
  have hs : (∑ j,∑ r,f j r) = ∑ i,a i := by
    rw [←Fintype.sum_prod_type (fun x : Fin p × Fin (p^k) => f x.1 x.2)]
    exact sum_fiberwise univ (fun i => primePowerDigits p k (u i)) a
  obtain ⟨j⟩ := (inferInstance : Nonempty (Fin p))
  refine ⟨∑ r,f j r,?_⟩
  rw [←hs]
  calc (∑ l, ∑ r,f l r) = ∑ _l : Fin p,∑ r,f j r :=
         sum_congr rfl fun l _ => sum_congr rfl fun r _ => he r l j
       _ = _ := by simp

/-- If the prime does not divide the integer autocorrelation at a lag,
every frequency has positive Möbius ambiguity weight at that lag. -/
theorem full_prime_power_moebius_row_of_autocorrelation {p : ℕ} [Fact p.Prime]
    (h : ℕ) (a b : ZMod (p^h))
    (ht : ¬ (p:ℤ) ∣ ∑ x : ZMod (p^h),
      (ArithmeticFunction.moebius ((x+b).val+1):ℤ)*ArithmeticFunction.moebius (x.val+1)) :
    0 < cyclicAmbiguityWeight (cyclicMoebiusProfile (p^h)) a b := by
  classical
  let f (x : ZMod (p^h)) : ℤ :=
    ArithmeticFunction.moebius ((x+b).val+1)*ArithmeticFunction.moebius (x.val+1)
  let χ : AddChar (ZMod (p^h)) ℂ := ZMod.stdAddChar
  let z := χ (-a)
  have hpow (n : ℕ) : z^n=χ (-(a*(n:ZMod (p^h)))) := by
    rw [show z^n=χ (n • (-a)) from (AddChar.map_nsmul_eq_pow χ n (-a)).symm,nsmul_eq_mul]
    congr 1
    ring
  have hperiod : z^(p^h)=1 := by
    rw [hpow,ZMod.natCast_self,mul_zero,neg_zero,AddChar.map_zero_eq_one]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hv
  have he : (∑ x : ZMod (p^h),(f x:ℂ)*z^x.val)=0 := by
    convert hv using 1
    unfold cyclicAmbiguityAmplitude
    refine sum_congr rfl fun x _ => ?_
    simp only [hpow,ZMod.natCast_zmod_val,cyclicMoebiusProfile,f,Int.cast_mul,map_intCast,χ]
  obtain ⟨j,_,hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp
    (orderOf_dvd_of_pow_eq_one hperiod)
  cases j with
  | zero =>
    have hz := pow_orderOf_eq_one z
    rw [hj,pow_zero,pow_one] at hz
    simp only [hz,one_pow,mul_one,←Int.cast_sum,Int.cast_eq_zero] at he
    apply ht
    change (p:ℤ) ∣ ∑ x,f x
    rw [he]
    exact dvd_zero _
  | succ k =>
    have hroot : IsPrimitiveRoot z (p^(k+1)) := hj ▸ IsPrimitiveRoot.orderOf z
    exact ht (prime_dvd_total_of_prime_power_fourier_zero hroot f ZMod.val he)

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
