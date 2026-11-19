import GaloisForLFunctions.SignedArithmeticCorrespondences.DivisorIncidenceOnLateCombs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Totient

/-!
# The isolated sites of the prime contact matrix

Wu and Yang detect diagonal projections by testing their commutator on
single matrix entries (arXiv:2611.05863, Proposition 3.4). On a finite
integer comb the off-diagonal Mangoldt matrix has isolated coordinates.
Their exact locations follow from the first upward and last downward contacts.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.vonMangoldt
namespace GaloisForLFunctions.SignedArithmeticCorrespondences

open HodgeTheoryOfAFixedPart (contactW)
noncomputable section

/-- The greatest proper divisor, extended by zero at one. -/
def lastDivisor (n : ℕ) : ℕ := if n = 1 then 0 else n / n.minFac

/-- All off-diagonal prime contacts at a site vanish. -/
def isolatedPrimeSites (A U : ℕ) : Finset ℕ :=
  (Ioc A U).filter fun n => ∀ m ∈ (Ioc A U).erase n, contactW Λ n m = 0

private theorem ordered_contact {m n : ℕ} (hm : 0 < m) (h : m < n) :
    contactW Λ m n = if m ∣ n then Λ (n/m) else 0 := by
  have hn : ¬n ∣ m := fun hd => (not_le_of_gt h) (Nat.le_of_dvd hm hd)
  simp only [contactW, if_neg hn, add_zero]

private theorem prime_step {n p : ℕ} (hn : 0 < n) (hp : Nat.Prime p) :
    contactW Λ n (n*p) ≠ 0 := by
  have hlt : n < n*p := by simpa only [Nat.mul_one] using
    (Nat.mul_lt_mul_of_pos_left hp.one_lt hn)
  rw [ordered_contact hn hlt, if_pos (dvd_mul_right n p), Nat.mul_div_cancel_left _ hn]
  exact vonMangoldt_ne_zero_iff.mpr hp.prime.isPrimePow

private theorem proper_dvd_le_last {m n : ℕ} (hm : 0 < m) (hmn : m < n) (hd : m ∣ n) :
    m ≤ lastDivisor n := by
  obtain ⟨q, rfl⟩ := hd
  have hq : 2 ≤ q := by
    by_contra! h
    rcases (show q=0 ∨ q=1 by omega) with rfl|rfl <;> simp at hmn
  have hfac := Nat.minFac_le_of_dvd hq (dvd_mul_left q m)
  have hn : m*q ≠ 1 := by omega
  rw [lastDivisor, if_neg hn, Nat.le_div_iff_mul_le (Nat.minFac_pos _)]
  exact Nat.mul_le_mul_left m hfac

/-- A single test at 2n and one at the greatest proper divisor decide whether
a coordinate couples to any other coordinate in the entire interval. -/
theorem mem_isolatedPrimeSites_iff (A U n : ℕ) :
    n ∈ isolatedPrimeSites A U ↔ n ∈ Ioc A U ∧ U < 2*n ∧ lastDivisor n ≤ A := by
  constructor
  · intro h
    obtain ⟨hn, hh⟩ := mem_filter.mp h
    obtain ⟨hAn,hnU⟩ := mem_Ioc.mp hn
    have hnpos : 0 < n := Nat.zero_lt_of_lt hAn
    refine ⟨hn, ?_, ?_⟩
    · by_contra! hle
      have h2 : n*2 ∈ (Ioc A U).erase n := mem_erase.mpr
        ⟨by omega, mem_Ioc.mpr ⟨by omega, by omega⟩⟩
      exact prime_step hnpos Nat.prime_two (hh _ h2)
    · by_cases hone : n=1
      · simp [lastDivisor, hone]
      let q := n/n.minFac
      have hp := Nat.minFac_prime hone
      have hprod : q*n.minFac = n := Nat.div_mul_cancel (Nat.minFac_dvd n)
      have hq : 0 < q := by
        by_contra! hz
        change n/n.minFac*n.minFac = n at hprod
        change n/n.minFac ≤ 0 at hz
        rw [Nat.eq_zero_of_le_zero hz, zero_mul] at hprod
        omega
      have hlt : q < n := by
        simpa only [Nat.mul_one, hprod] using Nat.mul_lt_mul_of_pos_left hp.one_lt hq
      change (if n = 1 then 0 else q) ≤ A
      rw [if_neg hone]
      by_contra! hA
      have hmem : q ∈ (Ioc A U).erase n :=
        mem_erase.mpr ⟨hlt.ne, mem_Ioc.mpr ⟨hA,hlt.le.trans hnU⟩⟩
      have hz := hh _ hmem
      rw [contactW_comm] at hz
      exact prime_step hq hp (by rwa [hprod])
  · rintro ⟨hn,hupper,hlower⟩
    obtain ⟨ha,hu⟩ := mem_Ioc.mp hn
    refine mem_filter.mpr ⟨hn,fun m hm => ?_⟩
    obtain ⟨hne,hmem⟩ := mem_erase.mp hm
    obtain ⟨ham,hmu⟩ := mem_Ioc.mp hmem
    rcases lt_or_gt_of_ne hne with h|h
    · rw [contactW_comm, ordered_contact (Nat.zero_lt_of_lt ham) h,
        if_neg (fun hd => (not_le_of_gt ham) ((proper_dvd_le_last (Nat.zero_lt_of_lt ham) h hd).trans hlower))]
    · rw [ordered_contact (Nat.zero_lt_of_lt ha) h, if_neg]
      rintro ⟨q,rfl⟩
      have hq : 2 ≤ q := by
        by_contra! hq
        rcases (show q=0 ∨ q=1 by omega) with rfl|rfl <;> simp at h
      have hsize := Nat.mul_le_mul_left n hq
      omega

/-- Mangoldt contact entries on the complete integer interval. -/
def primeContactMatrix (A U : ℕ) : Matrix (Ioc A U) (Ioc A U) ℝ :=
  fun i j => contactW Λ i.val j.val

/-- The rank-one coordinate projector commutes with the prime contact
matrix precisely at the isolated sites classified above. -/
theorem singleton_commutes_primeContactMatrix (A U : ℕ) (i : Ioc A U) :
    Commute (Matrix.diagonal (fun j : Ioc A U => if j=i then (1:ℝ) else 0))
      (primeContactMatrix A U) ↔ i.val ∈ isolatedPrimeSites A U := by
  constructor
  · intro h
    refine mem_filter.mpr ⟨i.property,fun m hm => ?_⟩
    obtain ⟨hne,hm⟩ := mem_erase.mp hm
    let j : Ioc A U := ⟨m,hm⟩
    have hji : j ≠ i := fun e => hne (congrArg Subtype.val e)
    have he := congrArg (fun M : Matrix (Ioc A U) (Ioc A U) ℝ => M i j) h.eq
    simpa only [Matrix.diagonal_mul, Matrix.mul_diagonal, if_pos rfl, if_neg hji, one_mul,
      mul_zero, primeContactMatrix] using he
  · intro hi
    have hz := (mem_filter.mp hi).2
    show _ * _ = _ * _
    ext a b
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases ha : a=i <;> by_cases hb : b=i
    · simp [ha,hb]
    · subst a
      have h := hz b (mem_erase.mpr ⟨(fun e => hb (Subtype.ext e)),b.property⟩)
      simp [hb, primeContactMatrix, h]
    · subst b
      have h := hz a (mem_erase.mpr ⟨(fun e => ha (Subtype.ext e)),a.property⟩)
      rw [contactW_comm] at h
      simp [ha, primeContactMatrix, h]
    · simp [ha,hb]

/-- All contact weights vanish off the diagonal at these sites, including
signed weights. The same pruning therefore works for every sign twist. -/
theorem arbitrary_contact_at_isolated {A U n : ℕ} (hn : n ∈ isolatedPrimeSites A U)
    (w : ℕ → ℝ) {m : ℕ} (hm : m ∈ (Ioc A U).erase n) : contactW w n m = 0 := by
  obtain ⟨hmem, htop, hbot⟩ := (mem_isolatedPrimeSites_iff A U n).mp hn
  obtain ⟨ha,hu⟩ := mem_Ioc.mp hmem
  obtain ⟨hne, hm⟩ := mem_erase.mp hm
  obtain ⟨ham,hmu⟩ := mem_Ioc.mp hm
  have hmn : ¬ m ∣ n := by
    intro h
    have hlt := lt_of_le_of_ne (Nat.le_of_dvd (Nat.zero_lt_of_lt ha) h) hne
    exact (not_le_of_gt ham) ((proper_dvd_le_last (Nat.zero_lt_of_lt ham) hlt h).trans hbot)
  have hnm : ¬ n ∣ m := by
    rintro ⟨q,rfl⟩
    have hq : 2 ≤ q := by
      by_contra! hq
      rcases (show q=0 ∨ q=1 by omega) with rfl|rfl <;> simp_all
    have hsize := Nat.mul_le_mul_left n hq
    omega
  simp [contactW, hnm, hmn]

/-- Deleting every isolated coordinate preserves the complete bilinear prime
debit even when the two profiles and the contact weight differ. -/
theorem contactTerm_delete_isolated (A U : ℕ) (w c e : ℕ → ℝ) :
    contactTerm w (Ioc A U) c e = contactTerm w (Ioc A U \ isolatedPrimeSites A U) c e := by
  let S := Ioc A U
  let T := S \ isolatedPrimeSites A U
  have hsub : T ⊆ S := sdiff_subset
  have houter (n : ℕ) (hn : n ∈ S) (h : n ∉ T) :
      ∑ m ∈ S.erase n, c m * e n * contactW w m n = 0 := by
    have hi : n ∈ isolatedPrimeSites A U := by
      by_contra hi
      exact h (mem_sdiff.mpr ⟨hn,hi⟩)
    exact sum_eq_zero fun m hm => by rw [contactW_comm, arbitrary_contact_at_isolated hi w hm, mul_zero]
  change (∑ n ∈ S, _) = ∑ n ∈ T, _
  rw [← sum_subset hsub houter]
  refine sum_congr rfl fun n hn => (sum_subset (erase_subset_erase n hsub) ?_).symm
  intro m hm ht
  obtain ⟨hne,hmS⟩ := mem_erase.mp hm
  have hi : m ∈ isolatedPrimeSites A U := by
    by_contra hi
    exact ht (mem_erase.mpr ⟨hne,mem_sdiff.mpr ⟨hmS,hi⟩⟩)
  rw [arbitrary_contact_at_isolated hi w (mem_erase.mpr ⟨hne.symm,hsub hn⟩), mul_zero]

/-- On a denominator band (jN,(j+1)N], isolation on the upper half
of the comb is exactly coprimality to j!. -/
theorem isolatedPrimeSites_band {j N U : ℕ} (hj : 1 ≤ j)
    (hU : (j+1)*N ≤ U) (htop : U ≤ 2*(j*N)) :
    (Ioc (j*N) ((j+1)*N)).filter (· ∈ isolatedPrimeSites N U) =
      (Ioc (j*N) ((j+1)*N)).filter fun n => (Nat.factorial j).Coprime n := by
  apply filter_congr
  intro n hn
  obtain ⟨hl,hu⟩ := mem_Ioc.mp hn
  have hN : N ≤ j*N := by simpa using Nat.mul_le_mul_right N hj
  have hNpos : 0<N := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hl hu; omega
  have hn1 : n ≠ 1 := by omega
  rw [mem_isolatedPrimeSites_iff, and_iff_right (mem_Ioc.mpr ⟨hN.trans_lt hl,hu.trans hU⟩),
    and_iff_right (show U<2*n by omega), lastDivisor, if_neg hn1, Nat.coprime_comm,
    Nat.coprime_factorial_iff hn1]
  have hm := Nat.div_mul_cancel (Nat.minFac_dvd n)
  constructor
  · intro h
    by_contra! hle
    have hprod := Nat.mul_le_mul h hle
    rw [hm, Nat.mul_comm N j] at hprod
    omega
  · intro h
    have hlim := hu.trans (Nat.mul_le_mul_right N h)
    rw [Nat.mul_comm n.minFac N] at hlim
    exact Nat.le_of_mul_le_mul_right (hm.le.trans hlim) (Nat.minFac_pos n)

private theorem coprime_blocks (a n k : ℕ) :
    ((Ico n (n+k*a)).filter fun x => a.Coprime x).card = k*a.totient := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hu : Ico n (n+(k+1)*a) = Ico n (n+k*a) ∪ Ico (n+k*a) (n+k*a+a) := by
      ext x
      simp only [mem_Ico, mem_union, Nat.succ_mul]
      omega
    rw [hu, filter_union, card_union_of_disjoint, ih, Nat.filter_coprime_Ico_eq_totient, Nat.succ_mul]
    exact disjoint_left.mpr fun x hx hy =>
      (not_le_of_gt (mem_Ico.mp (mem_filter.mp hx).1).2) (mem_Ico.mp (mem_filter.mp hy).1).1

/-- Exact number of isolated sites in every aligned complete band. -/
theorem card_isolatedPrimeSites_band (j k U : ℕ) (hj : 1 ≤ j)
    (hU : (j+1)*(k*j.factorial) ≤ U) (htop : U ≤ 2*(j*(k*j.factorial))) :
    ((Ioc (j*(k*j.factorial)) ((j+1)*(k*j.factorial))).filter
      (· ∈ isolatedPrimeSites (k*j.factorial) U)).card = k*j.factorial.totient := by
  rw [isolatedPrimeSites_band hj hU htop]
  let N := k*j.factorial
  have he : Ioc (j*N) ((j+1)*N) = Ico (j*N+1) ((j*N+1)+k*j.factorial) := by
    ext n
    simp only [mem_Ioc, mem_Ico, Nat.succ_mul]
    dsimp [N]
    omega
  rw [he]
  exact coprime_blocks _ _ _

/-- On (6k,24k] exactly 5k of the 18k coordinates are isolated.
The two upper bands retain residues coprime to 2 and 6 respectively. -/
theorem isolatedPrimeSites_fourfold_card (k : ℕ) :
    (isolatedPrimeSites (6*k) (24*k)).card = 5*k := by
  let N := 6*k
  let S := isolatedPrimeSites N (24*k)
  have he : S = ((Ioc (2*N) (3*N)).filter (· ∈ S)) ∪
      ((Ioc (3*N) (4*N)).filter (· ∈ S)) := by
    ext n
    simp only [mem_union,mem_filter,mem_Ioc]
    constructor
    · intro hn
      have hh := (mem_isolatedPrimeSites_iff N (24*k) n).mp hn
      obtain ⟨hA,hU⟩ := mem_Ioc.mp hh.1
      have hu := hh.2.1
      dsimp [N] at *
      by_cases h : n ≤ 18*k
      · exact Or.inl ⟨⟨by omega, by omega⟩,hn⟩
      · exact Or.inr ⟨⟨by omega,by omega⟩,hn⟩
    · rintro (h|h) <;> exact h.2
  have h₂ := card_isolatedPrimeSites_band 2 (3*k) (24*k) (by decide)
    (by norm_num [Nat.factorial]; omega) (by norm_num [Nat.factorial]; omega)
  have h₃ := card_isolatedPrimeSites_band 3 k (24*k) (by decide)
    (by norm_num [Nat.factorial]; omega) (by norm_num [Nat.factorial]; omega)
  have c₂ : (2:ℕ).factorial=2 := rfl
  have c₃ : (3:ℕ).factorial=6 := rfl
  have t₂ : Nat.totient 2=1 := by norm_num
  have t₃ : Nat.totient 6=2 := by norm_num
  rw [c₂,t₂, show 3*k*2=N by dsimp [N]; omega] at h₂
  rw [c₃,t₃, show k*6=N by dsimp [N]; omega] at h₃
  change S.card = _
  rw [he, card_union_of_disjoint, h₂, h₃]
  · omega
  · exact disjoint_left.mpr fun n h h' =>
      (not_lt_of_ge (mem_Ioc.mp (mem_filter.mp h).1).2) (mem_Ioc.mp (mem_filter.mp h').1).1

#print axioms isolatedPrimeSites_fourfold_card
#print axioms mem_isolatedPrimeSites_iff
#print axioms contactTerm_delete_isolated

end
end GaloisForLFunctions.SignedArithmeticCorrespondences
