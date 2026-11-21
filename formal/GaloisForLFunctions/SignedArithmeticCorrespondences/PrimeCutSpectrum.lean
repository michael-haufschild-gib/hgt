import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheCombOfUnitMassesFixesTheContacts
import GaloisForLFunctions.RHTower.CHMDPrimeChainVariance
import GaloisForLFunctions.SignedArithmeticCorrespondences.WeilMassOnDilatedCombWindows

/-!
# The prime contacts across a divisibility cut

The separated-column Gram argument for Vandermonde measurements becomes
exact on the Weil comb. Splitting at divisibility by p leaves only
p-power contacts across the cut. Each multiple has at most one neighbor
on the coprime side. The Gram matrix is diagonal and its entries count
the available powers of p above the corresponding site.
-/

noncomputable section
open Finset Filter ArithmeticFunction
open scoped ArithmeticFunction.vonMangoldt
open GaloisForLFunctions.HodgeTheoryOfAFixedPart
namespace GaloisForLFunctions.SignedArithmeticCorrespondences.PrimeCut

private theorem core_free {p n : ℕ} (hn : ¬p ∣ n) : ordCompl[p] n=n := by
  change n/p^(n.factorization p)=n
  rw [Nat.factorization_eq_zero_of_not_dvd hn,pow_zero,Nat.div_one]

private theorem lift_core {p m : ℕ} (hp : p.Prime) (hm : 0< m) (hd : p ∣ m) :
    ∃ j : ℕ, 0<j ∧ m=(ordCompl[p] m)*p^j := by
  refine ⟨m.factorization p,hp.factorization_pos_of_dvd hm.ne' hd,?_⟩
  rw [mul_comm]
  exact (Nat.ordProj_mul_ordCompl_eq_self m p).symm

/-- The full Mangoldt contact across the cut has at most one nonzero
column in each row. This holds for every prime and every pair of sites. -/
theorem cross_contact {p m n : ℕ} (hp : p.Prime) (hm : 0< m) (hn : 0<n)
    (hpm : p ∣ m) (hpn : ¬p ∣ n) :
    contactW vonMangoldt m n = if ordCompl[p] m=n then Real.log p else 0 := by
  have hmn : ¬m ∣ n := fun h => hpn (hpm.trans h)
  rw [contactW,if_neg hmn,zero_add]
  by_cases he : ordCompl[p] m=n
  · obtain ⟨j,hj,h⟩ := lift_core hp hm hpm
    rw [he] at h
    rw [if_pos he,if_pos (show n ∣ m from ⟨_,h⟩),h,Nat.mul_div_cancel_left _ hn,
      vonMangoldt_apply_pow hj.ne',vonMangoldt_apply_prime hp]
  · rw [if_neg he]
    split_ifs with hnm
    · apply vonMangoldt_eq_zero_iff.mpr
      intro h
      obtain ⟨q,j,hq,hj,hpow⟩ := (isPrimePow_nat_iff _).mp h
      have heq : m=n*q^j := by rw [hpow,Nat.mul_div_cancel' hnm]
      have hd : p ∣ n*q^j := heq ▸ hpm
      have hpq := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow ((hp.dvd_mul.mp hd).resolve_left hpn))
      subst q
      exact he (by rw [heq,Nat.ordCompl_mul,Nat.ordCompl_self_pow hp,mul_one,core_free hpn])
    · rfl

/-- Coprime columns, divisible rows, and the number of descendants present. -/
def columns (p : ℕ) (S : Finset ℕ) := S.filter (fun n => ¬p ∣ n)
def rows (p : ℕ) (S : Finset ℕ) := S.filter (fun n => p ∣ n)
def degree (p : ℕ) (S : Finset ℕ) (n : ℕ) := ((rows p S).filter (fun m => ordCompl[p] m=n)).card

/-- Image of a profile under the mixed prime block. -/
def applyContacts (p : ℕ) (S : Finset ℕ) (c : ℕ → ℝ) (m : ℕ) :=
  ∑ n ∈ columns p S, contactW vonMangoldt m n * c n

private theorem row_value {p : ℕ} (hp : p.Prime) {S : Finset ℕ} (hS : ∀ n ∈ S, 0<n)
    (c : ℕ → ℝ) {m : ℕ} (hm : m ∈ rows p S) :
    applyContacts p S c m =
      if ordCompl[p] m ∈ columns p S then Real.log p*c (ordCompl[p] m) else 0 := by
  have hm' := mem_filter.mp hm
  unfold applyContacts
  have term (n : ℕ) (hn : n ∈ columns p S) : contactW vonMangoldt m n*c n =
      if ordCompl[p] m=n then Real.log p*c n else 0 := by
    have hn' := mem_filter.mp hn
    rw [cross_contact hp (hS m hm'.1) (hS n hn'.1) hm'.2 hn'.2]
    split_ifs <;> simp
  rw [sum_congr rfl term,Finset.sum_ite_eq]

/-- The mixed Gram form, including signs and all off-diagonal entries.
The squared singular values are (log p)² times the descendant counts. -/
theorem mixed_gram {p : ℕ} (hp : p.Prime) {S : Finset ℕ} (hS : ∀ n ∈ S, 0<n)
    (a b : ℕ → ℝ) :
    (∑ m ∈ rows p S, applyContacts p S a m*applyContacts p S b m) =
      (Real.log p)^2*∑ n ∈ columns p S, (degree p S n:ℝ)*a n*b n := by
  have hr (m : ℕ) (hm : m ∈ rows p S) : applyContacts p S a m*applyContacts p S b m =
      ∑ n ∈ columns p S, if ordCompl[p] m=n then Real.log p^2*(a n*b n) else 0 := by
    rw [row_value hp hS a hm,row_value hp hS b hm,Finset.sum_ite_eq]
    split_ifs <;> ring
  rw [sum_congr rfl hr,sum_comm,mul_sum]
  apply sum_congr rfl
  intro n _
  rw [← sum_filter,sum_const,nsmul_eq_mul]
  unfold degree
  ring

/-- Sharp norm criterion on an arbitrary finite comb. Testing one column
per prime-free core attains every candidate singular value. -/
theorem norm_bound_iff {p : ℕ} (hp : p.Prime) {S : Finset ℕ} (hS : ∀ n ∈ S, 0<n) (C : ℝ) :
    (∀ a : ℕ → ℝ, (∑ m ∈ rows p S, (applyContacts p S a m)^2) ≤
      C*∑ n ∈ columns p S, (a n)^2) ↔
      ∀ n ∈ columns p S, Real.log p^2*(degree p S n:ℝ) ≤ C := by
  constructor
  · intro h n hn
    let a (k : ℕ) : ℝ := if k=n then 1 else 0
    have hh := h a
    simp_rw [sq (applyContacts p S a _)] at hh
    rw [mixed_gram hp hS] at hh
    simpa [a,Finset.sum_ite_eq',hn,Finset.mul_sum] using hh
  · intro h a
    simp_rw [sq (applyContacts p S a _)]
    rw [mixed_gram hp hS,mul_sum,mul_sum]
    apply sum_le_sum
    intro n hn
    simpa only [sq,mul_assoc] using mul_le_mul_of_nonneg_right (h n hn) (sq_nonneg (a n))

/-- On an interval the squared singular value at n is the integer
logarithm of the terminal quotient times (log p)². -/
theorem interval_degree {p A B n : ℕ} (hp : p.Prime) (hn : n ∈ columns p (Ioc A B)) :
    degree p (Ioc A B) n = Nat.log p (B/n) := by
  have h := mem_filter.mp hn
  have hAB := mem_Ioc.mp h.1
  have hpos : 0<n := Nat.zero_le A |>.trans_lt hAB.1
  have hb : 0 < B/n := Nat.div_pos hAB.2 hpos
  let R := Nat.log p (B/n)
  have hset : (rows p (Ioc A B)).filter (fun m => ordCompl[p] m=n) =
      (Icc 1 R).image (fun j => n*p^j) := by
    ext m
    constructor
    · intro hm
      obtain ⟨hm,hcore⟩ := mem_filter.mp hm
      obtain ⟨hm,hpm⟩ := mem_filter.mp hm
      have hm' := mem_Ioc.mp hm
      obtain ⟨j,hj,he⟩ := lift_core hp ((Nat.zero_le A).trans_lt hm'.1) hpm
      rw [hcore] at he
      refine mem_image.mpr ⟨j,mem_Icc.mpr ⟨hj,?_⟩,he.symm⟩
      apply (Nat.le_log_iff_pow_le hp.one_lt hb.ne').mpr
      apply (Nat.le_div_iff_mul_le hpos).mpr
      simpa only [Nat.mul_comm (p^j) n,← he] using hm'.2
    · rintro hm
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hm
      have hj' := mem_Icc.mp hj
      have he := (Nat.le_div_iff_mul_le hpos).mp ((Nat.le_log_iff_pow_le hp.one_lt hb.ne').mp hj'.2)
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_,by simpa only [Nat.mul_comm] using he⟩,
        dvd_mul_of_dvd_right (dvd_pow_self p (by omega : j≠0)) n⟩,?_⟩
      · exact hAB.1.trans_le (Nat.le_mul_of_pos_right n (pow_pos hp.pos j))
      · rw [Nat.ordCompl_mul,Nat.ordCompl_self_pow hp,core_free h.2,mul_one]
  have hinj : Function.Injective (fun j : ℕ => n*p^j) := fun i j he =>
    (Nat.pow_right_injective hp.one_lt) (Nat.eq_of_mul_eq_mul_left hpos he)
  rw [degree,hset,card_image_of_injective _ hinj,Nat.card_Icc]
  dsimp only [R]
  omega

private theorem degree_upper {p Q N k n : ℕ} (hp : p.Prime) (hQ : Q ≤ p^(k+1))
    (hn : n ∈ columns p (Ioc N (Q*N))) : degree p (Ioc N (Q*N)) n ≤ k := by
  rw [interval_degree hp hn]
  have hm := mem_Ioc.mp (mem_filter.mp hn).1
  have hn₀ := (Nat.zero_le N).trans_lt hm.1
  rw [← Nat.lt_add_one_iff]
  rw [Nat.log_lt_iff_lt_pow hp.one_lt (Nat.div_pos hm.2 hn₀).ne',Nat.div_lt_iff_lt_mul hn₀]
  exact (Nat.mul_le_mul_right N hQ).trans_lt (Nat.mul_lt_mul_of_pos_left hm.1 (pow_pos hp.pos _))

private theorem free_neighbor (p N : ℕ) (hp : p.Prime) :
    ∃ n, N<n ∧ n≤N+2 ∧ ¬ p ∣ n := by
  by_cases h : p ∣ N+1
  · refine ⟨N+2,by omega,le_rfl,fun hh => ?_⟩
    have h1 : p ∣ 1 := by simpa using Nat.dvd_sub hh h
    exact hp.not_dvd_one h1
  · exact ⟨N+1,by omega,by omega,h⟩

/-- For a fixed width Q the norm eventually takes its exact constant
value. At a width equal to a power of p the open left endpoint drops
the last possible descendant. -/
theorem sharp_interval_norm {p Q k N : ℕ} (hp : p.Prime) (hlo : p^k<Q)
    (hhi : Q ≤ p^(k+1)) (hN : 2*p^k ≤ N) (C : ℝ) :
    let S := Ioc N (Q*N)
    (∀ a : ℕ → ℝ, (∑ m ∈ rows p S,applyContacts p S a m^2) ≤ C*∑ n ∈ columns p S,a n^2) ↔
      Real.log p^2*(k:ℝ) ≤ C := by
  intro S
  rw [norm_bound_iff hp (fun _ hn => (Nat.zero_le _).trans_lt (mem_Ioc.mp hn).1)]
  constructor
  · intro h
    obtain ⟨n,hn,hnear,hfree⟩ := free_neighbor p N hp
    have hn₀ := (Nat.zero_le N).trans_lt hn
    have hfit : p^k*n ≤ Q*N := by
      calc p^k*n ≤ p^k*(N+2) := Nat.mul_le_mul_left _ hnear
           _ ≤ (p^k+1)*N := by rw [Nat.mul_add,Nat.add_mul,one_mul,Nat.mul_comm _ 2]; omega
           _ ≤ Q*N := Nat.mul_le_mul_right _ hlo
    have hnW : n ∈ columns p S := mem_filter.mpr ⟨mem_Ioc.mpr ⟨hn,
      (Nat.le_mul_of_pos_left n (pow_pos hp.pos k)).trans hfit⟩,hfree⟩
    have hdeg : degree p S n=k := by
      apply le_antisymm (degree_upper hp hhi hnW)
      rw [interval_degree hp hnW]
      exact (Nat.le_log_iff_pow_le hp.one_lt (Nat.div_pos (mem_Ioc.mp (mem_filter.mp hnW).1).2 hn₀).ne').mpr
        ((Nat.le_div_iff_mul_le hn₀).mpr hfit)
    have hdeg' : degree p (Ioc N (Q*N)) n = k := hdeg
    simpa only [hdeg'] using h n hnW
  · intro h n hn
    exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (degree_upper hp hhi hn)) (sq_nonneg _)).trans h

/-- Mixed contact energy can be split between the two sides, with an
arbitrary positive price on the divisible side and its reciprocal on the
coprime side. The exact descendant multiplicities enter individually. -/
theorem mixed_payment {p : ℕ} (hp : p.Prime) {S : Finset ℕ} (hS : ∀ n ∈ S,0<n)
    (a b : ℕ → ℝ) {D : ℝ} (hD : 0<D) :
    2*|∑ m ∈ rows p S,b m*applyContacts p S a m| ≤ D*(∑ m ∈ rows p S,b m^2) +
      (Real.log p^2/D)*∑ n ∈ columns p S,(degree p S n:ℝ)*a n^2 := by
  have hr (m : ℕ) : 2*|b m*applyContacts p S a m| ≤ D*b m^2+applyContacts p S a m^2/D := by
    rw [abs_mul]
    apply (mul_le_mul_iff_left₀ hD).mp
    rw [add_mul,div_mul_cancel₀ _ hD.ne']
    have hs := sq_nonneg (D*|b m|-|applyContacts p S a m|)
    rw [sub_sq,mul_pow,sq_abs,sq_abs] at hs
    linarith only [hs]
  have hsum := sum_le_sum (s := rows p S) (fun m _ => hr m)
  rw [sum_add_distrib,←mul_sum,←mul_sum,←sum_div] at hsum
  have he := mixed_gram hp hS a a
  simp only [mul_assoc,← sq] at he
  rw [he] at hsum
  exact (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by norm_num : (0:ℝ)≤2)).trans
    (hsum.trans_eq (by ring))

private theorem divisible_floor (p Q : ℕ) (hp : p.Prime) (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ → ℝ,
      B*(∑ m ∈ rows p (Ioc N (Q*N)),b m^2) ≤ combForm (rows p (Ioc N (Q*N))) b := by
  let d : ℕ+ := ⟨p,hp.pos⟩
  let q : ℕ+ := ⟨2*Q+1,by omega⟩
  obtain ⟨M,hM⟩ := eventually_atTop.mp (eventually_dilated_comb_floor d hp.two_le q B)
  filter_upwards [eventually_ge_atTop ((M+1)*p)] with N hN
  have hbase : M+1 ≤ N/p := (Nat.le_div_iff_mul_le hp.pos).mpr hN
  let V := rows p (Ioc N (Q*N))
  let U := V.image (·/p)
  have he (m : ℕ) (hm : m ∈ V) : p*(m/p)=m := Nat.mul_div_cancel' (mem_filter.mp hm).2
  have him : U.image (fun n => p*n) = V := by
    ext m
    constructor
    · intro hm
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hm
      obtain ⟨n,hn,rfl⟩ := mem_image.mp hj
      rwa [he n hn]
    · intro hm
      exact mem_image.mpr ⟨m/p,mem_image_of_mem _ hm,he m hm⟩
  have hsub : U ⊆ Ioc (N/p) (N/p+(q:ℕ)*(N/p)) := by
    intro j hj
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hj
    have hw := mem_Ioc.mp (mem_filter.mp hm).1
    have h₁ : N/p< m/p := by
      by_contra! ht
      have h := (Nat.mul_le_mul_left p ht).trans (Nat.mul_div_le N p)
      rw [he m hm] at h
      omega
    have h₂ : N ≤ p*(2*(N/p)) := by
      have hlt := Nat.mod_lt N hp.pos
      have hsum := Nat.mod_add_div N p
      have hbound := Nat.mul_le_mul_left p (show N/p+1 ≤ 2*(N/p) by omega)
      rw [Nat.mul_add,Nat.mul_one] at hbound
      omega
    have hupper : m/p ≤ 2*Q*(N/p) := by
      apply (Nat.le_of_mul_le_mul_left (c := p) · hp.pos)
      rw [he m hm]
      calc m ≤ Q*N := hw.2
           _ ≤ Q*(p*(2*(N/p))) := Nat.mul_le_mul_left _ h₂
           _ = p*(2*Q*(N/p)) := by ring
    exact mem_Ioc.mpr ⟨h₁,hupper.trans (by dsimp [q]; rw [Nat.add_mul]; omega)⟩
  intro b
  have h := hM (N/p) (by omega) U hsub b
  change B*(∑ m ∈ U.image (fun n => p*n),b m^2) ≤ combForm (U.image (fun n => p*n)) b at h
  simpa only [him] using h

/-- Across the divisibility cut the entire mixed prime debit is
infinitesimally bounded by the Weil form on divisible sites plus the
ordinary squared mass on coprime sites, uniformly in both profiles. -/
theorem negligible_mixed_contact {p : ℕ} (hp : p.Prime) (Q : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ a b : ℕ → ℝ, let S := Ioc N (Q*N)
      2*|∑ m ∈ rows p S,b m*applyContacts p S a m| ≤
        ε*(combForm (rows p S) b + ∑ n ∈ columns p S,a n^2) := by
  let D := (Real.log p^2*(Q:ℝ)+1)/ε
  have hD : 0<D := by dsimp [D]; positivity
  have hQ : Q ≤ p^(Q+1) := by
    have h : Q+1 < p^(Q+1) := Nat.lt_pow_self hp.one_lt
    omega
  filter_upwards [divisible_floor p Q hp (D/ε)] with N hfloor
  intro a b S
  have hS : ∀ n ∈ S,0<n := fun _ hn => (Nat.zero_le N).trans_lt (mem_Ioc.mp hn).1
  have h := mixed_payment hp hS a b hD
  have hev := mul_le_mul_of_nonneg_left (hfloor b) hε.le
  have hleft : D*(∑ m ∈ rows p S,b m^2) ≤ ε*combForm (rows p S) b := by
    calc _ = ε*((D/ε)*(∑ m ∈ rows p S,b m^2)) := by field_simp
         _ ≤ _ := hev
  have htot : (Real.log p^2/D)*(∑ n ∈ columns p S,(degree p S n:ℝ)*a n^2) ≤
      ε*∑ n ∈ columns p S,a n^2 := by
    rw [mul_sum,mul_sum]
    apply sum_le_sum
    intro n hn
    have hd : (degree p S n:ℝ) ≤ Q := Nat.cast_le.mpr (degree_upper hp hQ hn)
    have hmax : Real.log p^2*(Q:ℝ) ≤ ε*D := by
      dsimp only [D]
      rw [mul_comm ε,div_mul_cancel₀ _ hε.ne']
      linarith
    have hprice := (div_le_iff₀ hD).mpr ((mul_le_mul_of_nonneg_left hd (sq_nonneg _)).trans hmax)
    calc _ = (Real.log p^2*(degree p S n:ℝ)/D)*a n^2 := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hprice (sq_nonneg _)
  rw [mul_add]
  exact h.trans (add_le_add hleft htot)

end GaloisForLFunctions.SignedArithmeticCorrespondences.PrimeCut
