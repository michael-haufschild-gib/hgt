import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.WeightedSectionsOfTheUnitaryFactorPairs

/-!
# Near-diagonal factor pairs in the signed unitary midpoint

After fixing the full prime power b at one prime of k, the signed price
is supported on coprime factorizations d e of the cofactor. Both d/e
and e/d must be strictly smaller than b. Thus the size of the chosen
block determines an explicit symmetric neighborhood of the diagonal.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Coprime factorizations of n with both factor ratios strictly below b,
indexed by the first factor. -/
def nearDiagonalUnitaryFactors (b n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => d.Coprime (n/d) ∧ d<b*(n/d) ∧ n/d<b*d)

private theorem cofactor_strip {k p d : ℕ} (hp : p∈k.primeFactors)
    (dvd : d∣ordCompl[p] k) :
    let n := ordCompl[p] k
    let b := p^k.factorization p
    (d^2≤k ∧ n<b*d^2) ↔ (d<b*(n/d) ∧ n/d<b*d) := by
  intro n b
  let e := n/d
  obtain ⟨pr,pk,k0⟩ := Nat.mem_primeFactors.mp hp
  have npos : 0<n := Nat.ordCompl_pos p k0
  have dpos := Nat.pos_of_dvd_of_pos dvd npos
  have mult : d*e=n := Nat.mul_div_cancel' dvd
  have block : b*n=k := Nat.ordProj_mul_ordCompl_eq_self k p
  have low : d^2≤k ↔ d≤b*e := by
    rw [show k=d*(b*e) by rw [←block,←mult]; ring,pow_two]
    exact ⟨fun h => Nat.le_of_mul_le_mul_left h dpos,fun h => Nat.mul_le_mul_left d h⟩
  have high : b*d^2≤n ↔ b*d≤e := by
    rw [show b*d^2=d*(b*d) by ring,←mult]
    exact ⟨fun h => Nat.le_of_mul_le_mul_left h dpos,fun h => Nat.mul_le_mul_left d h⟩
  have no : d≠b*e := by
    intro equal
    have pb : p∣b := dvd_pow_self p (pr.factorization_pos_of_dvd k0 pk).ne'
    have pd : p∣d := equal ▸ pb.trans (dvd_mul_right b e)
    exact Nat.not_dvd_ordCompl pr k0 (pd.trans dvd)
  have high' : n<b*d^2 ↔ e<b*d := by simpa only [not_le] using not_congr high
  exact and_congr (low.trans ⟨fun h => lt_of_le_of_ne h no,le_of_lt⟩) high'

/-- For every prime block the complete signed midpoint price equals its
cofactor's signed unitary-divisor count in the open multiplicative strip. -/
theorem unitary_midpoint_near_diagonal_sum {k p : ℕ} (hp : p∈k.primeFactors) :
    let n := ordCompl[p] k
    let b := p^k.factorization p
    unitaryHalfWeight k=∑ d ∈ nearDiagonalUnitaryFactors b n,(-1:ℤ)^d.primeFactors.card := by
  intro n b
  have npos : 0<n := Nat.ordCompl_pos p (Nat.mem_primeFactors.mp hp).2.2
  let test (d : ℕ) := d^2≤k ∧ n<b*d^2
  have piv : unitaryPivots k p=n.primeFactors.powerset.filter (fun S => test (primePowerSubset n S)) := by
    ext S
    have point : S∈unitaryPivots k p ↔ S⊆n.primeFactors ∧ test (primePowerSubset n S) :=
      unitary_pivot_cofactor_window hp S
    exact point.trans (by simp only [mem_filter,mem_powerset])
  have factors : n.divisors.filter (fun d => d.Coprime (n/d) ∧ test d)=nearDiagonalUnitaryFactors b n := by
    ext d
    simp only [nearDiagonalUnitaryFactors,mem_filter]
    exact and_congr_right fun hd => and_congr_right fun _ => cofactor_strip hp (Nat.dvd_of_mem_divisors hd)
  rw [unitaryHalfWeight_eq_sum_pivots hp,piv,←factors]
  exact unitary_sum_on_divisor_section npos test (fun _ S => (-1:ℤ)^S.card)

private theorem partner_in_strip {b n d : ℕ} (hd : d∈nearDiagonalUnitaryFactors b n) :
    n/(n/d)=d ∧ n/d∈nearDiagonalUnitaryFactors b n := by
  obtain ⟨div,cop,low,high⟩ := mem_filter.mp hd
  obtain ⟨dvd,n0⟩ := Nat.mem_divisors.mp div
  have npos := Nat.pos_of_ne_zero n0
  have dpos := Nat.pos_of_dvd_of_pos dvd npos
  have epos := Nat.div_pos (Nat.le_of_dvd npos dvd) dpos
  have mult : n/d*d=n := by rw [mul_comm,Nat.mul_div_cancel' dvd]
  have inv := Nat.mul_div_cancel_left d epos
  rw [mult] at inv
  refine ⟨inv,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨⟨d,mult.symm⟩,n0⟩,?_⟩⟩
  rw [inv]
  exact ⟨cop.symm,high,low⟩

private theorem unequal_partners {b n d : ℕ} (hn : 1<n) (hd : d∈nearDiagonalUnitaryFactors b n) :
    d≠n/d := by
  obtain ⟨div,cop,_,_⟩ := mem_filter.mp hd
  intro eq
  have gcd : d.gcd (n/d)=1 := cop
  rw [←eq,Nat.gcd_self] at gcd
  have mult := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors div)
  rw [←eq,gcd,one_mul] at mult
  exact hn.ne mult

private theorem partner_sign {b n d : ℕ} (hd : d∈nearDiagonalUnitaryFactors b n) :
    (-1:ℤ)^(n/d).primeFactors.card=(-1:ℤ)^n.primeFactors.card*(-1:ℤ)^d.primeFactors.card := by
  obtain ⟨div,cop,_,_⟩ := mem_filter.mp hd
  have mult := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors div)
  have card : n.primeFactors.card=d.primeFactors.card+(n/d).primeFactors.card := by
    calc _ = (d*(n/d)).primeFactors.card := congrArg (fun m : ℕ => m.primeFactors.card) mult.symm
         _ = _ := by rw [cop.primeFactors_mul,card_union_of_disjoint cop.disjoint_primeFactors]
  have sq : (-1:ℤ)^d.primeFactors.card*(-1)^d.primeFactors.card=1 := by rw [←mul_pow]; norm_num
  rw [card,pow_add]
  calc _ = ((-1:ℤ)^d.primeFactors.card*(-1)^d.primeFactors.card)*(-1)^(n/d).primeFactors.card := by rw [sq,one_mul]
       _ = _ := by ring

/-- Pairing the two orders of each factorization gives the complete
parity multiplier on the lower half of the cofactor strip. For an
even number of cofactor primes it doubles each remaining sign. -/
theorem unitary_midpoint_ordered_factor_strip {k p : ℕ} (hp : p∈k.primeFactors)
    (hn : 1<ordCompl[p] k) :
    let n := ordCompl[p] k
    let b := p^k.factorization p
    unitaryHalfWeight k=(1+(-1:ℤ)^n.primeFactors.card)*
      ∑ d ∈ (nearDiagonalUnitaryFactors b n).filter (fun d => d<n/d),(-1:ℤ)^d.primeFactors.card := by
  intro n b
  let F := nearDiagonalUnitaryFactors b n
  let L := F.filter (fun d => d<n/d)
  let R := F.filter (fun d => ¬ d<n/d)
  let w (d : ℕ) := (-1:ℤ)^d.primeFactors.card
  have reverse : (∑ d ∈ L,w (n/d))=∑ d ∈ R,w d := by
    apply sum_nbij' (fun d => n/d) (fun d => n/d)
    · intro d hd
      obtain ⟨row,less⟩ := mem_filter.mp hd
      obtain ⟨inv,swap⟩ := partner_in_strip row
      refine mem_filter.mpr ⟨swap,?_⟩
      rw [inv]
      exact less.not_gt
    · intro d hd
      obtain ⟨row,ge⟩ := mem_filter.mp hd
      obtain ⟨inv,swap⟩ := partner_in_strip row
      refine mem_filter.mpr ⟨swap,?_⟩
      rw [inv]
      exact lt_of_le_of_ne (le_of_not_gt ge) (unequal_partners hn row).symm
    · exact fun _ hd => (partner_in_strip (mem_filter.mp hd).1).1
    · exact fun _ hd => (partner_in_strip (mem_filter.mp hd).1).1
    · exact fun _ _ => rfl
  have split := sum_filter_add_sum_filter_not F (fun d => d<n/d) w
  change (∑ d ∈ L,w d)+(∑ d ∈ R,w d)=∑ d ∈ F,w d at split
  have cost : (∑ d ∈ L,w (n/d))=(-1:ℤ)^n.primeFactors.card*∑ d ∈ L,w d := by
    rw [mul_sum]
    exact sum_congr rfl fun d hd => partner_sign (mem_filter.mp hd).1
  rw [unitary_midpoint_near_diagonal_sum hp]
  change (∑ d ∈ F,w d)=(1+(-1:ℤ)^n.primeFactors.card)*∑ d ∈ L,w d
  rw [←split,←reverse,cost,add_mul,one_mul]

/-- Each ordered near-diagonal pair contributes the sum of its two
individual prime-count signs. Opposite parities cancel pair by pair. -/
theorem unitary_midpoint_sum_of_factor_signs {k p : ℕ} (hp : p∈k.primeFactors)
    (hn : 1<ordCompl[p] k) :
    let n := ordCompl[p] k
    let b := p^k.factorization p
    unitaryHalfWeight k=∑ d ∈ (nearDiagonalUnitaryFactors b n).filter (fun d => d<n/d),
      ((-1:ℤ)^d.primeFactors.card+(-1:ℤ)^(n/d).primeFactors.card) := by
  intro n b
  rw [unitary_midpoint_ordered_factor_strip hp hn,mul_sum]
  refine sum_congr rfl fun d hd => ?_
  rw [partner_sign (mem_filter.mp hd).1,add_mul,one_mul]

#print axioms unitary_midpoint_sum_of_factor_signs
#print axioms unitary_midpoint_ordered_factor_strip
#print axioms unitary_midpoint_near_diagonal_sum
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
