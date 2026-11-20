import GaloisForLFunctions.SignedArithmeticCorrespondences.TheFirstOddMomentOfThePrimeContactMatrix
import GaloisForLFunctions.HTGeometry.VonMangoldtSelfConvolution

/-!
# Prime-power triangles in the Mangoldt contact matrix

The three vertices of every contact triangle lie on one prime ray. When
its outer ratio is p^a, precisely a-1 intermediate sites are possible.
Summing by the smallest vertex counts the entire cubic spectral moment.
-/
noncomputable section
open Finset ArithmeticFunction
open GaloisForLFunctions.HodgeTheoryOfAFixedPart
open scoped ArithmeticFunction.vonMangoldt
namespace GaloisForLFunctions.SignedArithmeticCorrespondences.PrimeContactMoments

private theorem edge_comm (i j : ℕ) : edge i j=edge j i := add_comm _ _
private theorem diag_zero {i : ℕ} (hi : 0<i) : edge i i=0 := by simp [edge,contactW,Nat.div_self hi]
private theorem edge_above {i j : ℕ} (hi : 0<i) (hij : i<j) :
    edge i j=if i∣j then Λ (j/i) else 0 := by
  have hn : ¬j∣i := fun h => hij.not_ge (Nat.le_of_dvd hi h)
  simp [edge,contactW,hn]
private theorem mul_contact {i r : ℕ} (hi : 0<i) (hr : 1<r) :
    edge i (i*r)=Λ r := by
  have hlt : i<i*r := by simpa using Nat.mul_lt_mul_of_pos_left hr hi
  rw [edge_above hi hlt,if_pos (dvd_mul_right _ _),Nat.mul_div_cancel_left _ hi]

/-- Each ordered triangle has all three edges in the same prime direction.
Conversely every choice of two positive exponent gaps gives a triangle. -/
theorem ordered_prime_triangle {i j k : ℕ} (hi : 0<i) (hij : i<j) (hjk : j<k) :
    edge i j*edge j k*edge k i ≠ 0 ↔
      ∃ p a b : ℕ,p.Prime ∧ 0<a ∧ a<b ∧ j=i*p^a ∧ k=i*p^b := by
  constructor
  · intro h
    rw [mul_ne_zero_iff,mul_ne_zero_iff] at h
    obtain ⟨⟨h₁,h₂⟩,h₃⟩ := h
    rw [edge_above hi hij] at h₁
    rw [edge_above (hi.trans hij) hjk] at h₂
    rw [edge_comm,edge_above hi (hij.trans hjk)] at h₃
    split_ifs at h₁ with hd₁ <;> try contradiction
    split_ifs at h₂ with hd₂ <;> try contradiction
    split_ifs at h₃ with hd₃ <;> try contradiction
    obtain ⟨p,b,hp,hb,hpow⟩ := (isPrimePow_nat_iff _).mp (vonMangoldt_ne_zero_iff.mp h₃)
    obtain ⟨d,hd⟩ := hd₁
    obtain ⟨e,he⟩ := hd₂
    have hk : k=i*p^b := by rw [hpow,Nat.mul_div_cancel' hd₃]
    have hde : d*e=p^b := Nat.eq_of_mul_eq_mul_left hi (by rw [←Nat.mul_assoc,←hd,←he,←hk])
    obtain ⟨a,hab,ha⟩ := (Nat.dvd_prime_pow hp).mp (show d∣p^b from ⟨e,hde.symm⟩)
    have hj : j=i*p^a := hd.trans (congrArg (i*·) ha)
    refine ⟨p,a,b,hp,?_,lt_of_le_of_ne hab ?_,hj,hk⟩
    · by_contra! hzero
      rw [Nat.eq_zero_of_le_zero hzero,pow_zero,mul_one] at hj
      exact hij.ne hj.symm
    · rintro rfl
      exact hjk.ne (hj.trans hk.symm)
  · rintro ⟨p,a,b,hp,ha,hb,rfl,rfl⟩
    have he : i*p^b=(i*p^a)*p^(b-a) := by rw [mul_assoc,←pow_add,Nat.add_sub_of_le hb.le]
    have hpos := Real.log_pos (show (1:ℝ)<p by exact_mod_cast hp.one_lt)
    rw [edge_comm (i*p^b) i,mul_contact hi (one_lt_pow₀ hp.one_lt ha.ne'),
      mul_contact hi (one_lt_pow₀ hp.one_lt (ha.trans hb).ne'),he,
      mul_contact (Nat.mul_pos hi (pow_pos hp.pos a)) (one_lt_pow₀ hp.one_lt (by omega)),
      vonMangoldt_apply_pow ha.ne',vonMangoldt_apply_pow (by omega : b-a≠0),
      vonMangoldt_apply_pow (ha.trans hb).ne',vonMangoldt_apply_prime hp]
    exact (mul_pos (mul_pos hpos hpos) hpos).ne'

private def triangle (i j k : ℕ) : ℝ := edge i j*edge j k*edge k i
private def ordered (i j k : ℕ) : ℝ := if i<j ∧ j<k then triangle i j k else 0
private theorem rotate (i j k : ℕ) : triangle j k i=triangle i j k := by unfold triangle;ring
private theorem reflect (i j k : ℕ) : triangle i k j=triangle i j k := by
  unfold triangle
  rw [edge_comm i k,edge_comm k j,edge_comm j i]; ring

private theorem split_six {i j k : ℕ} (hi : 0<i) (hj : 0<j) (hk : 0<k) :
    triangle i j k=ordered i j k+ordered i k j+ordered j i k+
      ordered j k i+ordered k i j+ordered k j i := by
  by_cases h₁ : i=j
  · subst j
    have hh : ¬(i<k ∧ k<i) := by omega
    simp [ordered,triangle,diag_zero hi,hh]
  by_cases h₂ : j=k
  · subst k
    have hh : ¬(j<i ∧ i<j) := by omega
    simp [ordered,triangle,diag_zero hj,hh]
  by_cases h₃ : i=k
  · subst k
    have hh : ¬(i<j ∧ j<i) := by omega
    simp [ordered,triangle,diag_zero hi,hh]
  have ht₁ := reflect i j k
  have ht₂ := rotate i j k
  have ht₃ := (reflect j k i).trans ht₂
  have ht₄ := (rotate j k i).trans ht₂
  have ht₅ := (reflect k i j).trans ht₄
  rcases lt_or_gt_of_ne h₁ with h₁|h₁ <;> rcases lt_or_gt_of_ne h₂ with h₂|h₂ <;>
    rcases lt_or_gt_of_ne h₃ with h₃|h₃ <;>
    first | omega | simp (disch := omega) only [ordered,if_pos,if_neg,ht₁,ht₂,ht₃,ht₄,ht₅,zero_add,add_zero]

private def sumThree (S : Finset ℕ) (f : ℕ → ℕ → ℕ → ℝ) :=
  ∑ i∈S,∑ j∈S,∑ k∈S,f i j k

private theorem swap_first (S : Finset ℕ) (f : ℕ → ℕ → ℕ → ℝ) :
    sumThree S (fun i j k => f j i k)=sumThree S f := by
  unfold sumThree
  rw [sum_comm]

private theorem swap_last (S : Finset ℕ) (f : ℕ → ℕ → ℕ → ℝ) :
    sumThree S (fun i j k => f i k j)=sumThree S f := by
  unfold sumThree
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]

/-- The cubic trace counts every strictly increasing prime triangle six times. -/
theorem cubic_trace_ordered (N B : ℕ) :
    cubicTrace (Ioc N B)=6*∑ i∈Ioc N B,∑ j∈Ioc N B,∑ k∈Ioc N B,
      (if i<j ∧ j<k then edge i j*edge j k*edge k i else 0) := by
  let S := Ioc N B
  have hs {i : ℕ} (hi : i∈S) : 0<i := Nat.zero_lt_of_lt (mem_Ioc.mp hi).1
  have h : cubicTrace S=sumThree S (fun i j k => ordered i j k+ordered i k j+ordered j i k+
      ordered j k i+ordered k i j+ordered k j i) :=
    sum_congr rfl fun _ hi => sum_congr rfl fun _ hj => sum_congr rfl fun _ hk => split_six (hs hi) (hs hj) (hs hk)
  have h₁ := swap_last S ordered
  have h₂ := swap_first S ordered
  have h₄ := (swap_first S (fun i j k => ordered i k j)).trans h₁
  have h₅ := (swap_last S (fun i j k => ordered j i k)).trans h₂
  have h₆ := (swap_first S (fun i j k => ordered k i j)).trans h₅
  change cubicTrace S=6*sumThree S ordered
  rw [h]
  simp only [sumThree,sum_add_distrib] at h₁ h₂ h₄ h₅ h₆ ⊢
  rw [h₁,h₂,h₄,h₅,h₆]
  ring

private theorem divides_of_contact {i j : ℕ} (hi : 0<i) (hij : i<j)
    (h : edge i j≠0) : i∣j := by
  by_contra hn
  exact h (by rw [edge_above hi hij,if_neg hn])

/-- Price attached to an outer ratio. It is supported on proper prime powers. -/
def trianglePrice (r : ℕ) : ℝ := (Λ*Λ) r*Λ r

theorem trianglePrice_prime_power {p b : ℕ} (hp : p.Prime) (hb : 0<b) :
    trianglePrice (p^b)=((b:ℝ)-1)*Real.log p^3 := by
  rw [trianglePrice,GaloisForLFunctions.HTGeometry.vonMangoldt_mul_self_prime_pow hp hb,
    vonMangoldt_apply_pow hb.ne',vonMangoldt_apply_prime hp]; ring

private theorem ordered_ratio {N B i r : ℕ} (hi : i∈Ioc N B) (hk : i*r∈Ioc N B) (hr : 1<r) :
    (∑ j∈Ioc N B, ordered i j (i*r))=trianglePrice r := by
  classical
  have hi0 := Nat.zero_lt_of_lt (mem_Ioc.mp hi).1
  have hr0 := Nat.zero_lt_one.trans hr
  let T := r.divisors.image (fun d => i*d)
  have sub : T ⊆ Ioc N B := by
    intro j hj
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hj
    have hpos := Nat.pos_of_mem_divisors hd
    have hle := Nat.le_of_dvd hr0 (Nat.dvd_of_mem_divisors hd)
    exact mem_Ioc.mpr ⟨(mem_Ioc.mp hi).1.trans_le (Nat.le_mul_of_pos_right _ hpos),
      (Nat.mul_le_mul_left _ hle).trans (mem_Ioc.mp hk).2⟩
  have hz (j : ℕ) (_ : j∈Ioc N B) (hj : j∉T) : ordered i j (i*r)=0 := by
    by_contra hn
    unfold ordered at hn
    split_ifs at hn with ho <;> try contradiction
    change edge i j*edge j (i*r)*edge (i*r) i≠0 at hn
    obtain ⟨h₁,h₂⟩ := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1
    obtain ⟨d,he⟩ := divides_of_contact hi0 ho.1 h₁
    obtain ⟨e,hf⟩ := divides_of_contact (hi0.trans ho.1) ho.2 h₂
    have hde : r=d*e := Nat.eq_of_mul_eq_mul_left hi0 (by rw [←Nat.mul_assoc,←he,←hf])
    exact hj (mem_image.mpr ⟨d,Nat.mem_divisors.mpr ⟨⟨e,hde⟩,hr0.ne'⟩,he.symm⟩)
  rw [←sum_subset sub hz]
  dsimp only [T]
  rw [sum_image (fun _ _ _ _ he => Nat.eq_of_mul_eq_mul_left hi0 he)]
  have price (d : ℕ) (hd : d∈r.divisors) : ordered i (i*d) (i*r)=Λ d*Λ (r/d)*Λ r := by
    have hd0 := Nat.pos_of_mem_divisors hd
    by_cases h1 : d=1
    · simp [h1,ordered]
    by_cases he : d=r
    · simp [he,ordered,Nat.div_self hr0]
    have hlt : d<r := lt_of_le_of_ne (Nat.le_of_dvd hr0 (Nat.dvd_of_mem_divisors hd)) he
    have hd1 : 1<d := by omega
    have hdraw := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    have heq : i*r=(i*d)*(r/d) := by rw [Nat.mul_assoc,hdraw]
    have he1 : 1<r/d := by
      apply Nat.lt_of_mul_lt_mul_left (show d*1<d*(r/d) by simpa only [Nat.mul_one,hdraw] using hlt)
    have hleft : i<i*d := by simpa using Nat.mul_lt_mul_of_pos_left hd1 hi0
    have hright := Nat.mul_lt_mul_of_pos_left hlt hi0
    rw [ordered,if_pos ⟨hleft,hright⟩,triangle,edge_comm (i*r) i,mul_contact hi0 hr,
      mul_contact hi0 hd1,heq,mul_contact (Nat.mul_pos hi0 hd0) he1]
  rw [sum_congr rfl price,trianglePrice,ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => Λ a*Λ b),sum_mul]

private theorem sum_middle {N B i k : ℕ} (hi : i∈Ioc N B) (hk : k∈Ioc N B) :
    (∑ j∈Ioc N B,ordered i j k)=if i<k ∧ i∣k then trianglePrice (k/i) else 0 := by
  have hi0 := Nat.zero_lt_of_lt (mem_Ioc.mp hi).1
  split_ifs with h
  · obtain ⟨r,hr⟩ := h.2
    subst k
    have hlt : 1<r := Nat.lt_of_mul_lt_mul_left (by simpa using h.1 : i*1<i*r)
    rw [Nat.mul_div_cancel_left _ hi0]
    exact ordered_ratio hi hk hlt
  · apply sum_eq_zero
    intro j _
    by_cases hj : i<j ∧ j<k
    · have hd : ¬i∣k := fun he => h ⟨hj.1.trans hj.2,he⟩
      rw [ordered,if_pos hj,triangle,edge_comm k i,edge_above hi0 (hj.1.trans hj.2),if_neg hd,mul_zero]
    · exact if_neg hj

/-- One scalar arithmetic convolution determines the complete third moment. -/
theorem cubic_trace_outer_pairs (N B : ℕ) : cubicTrace (Ioc N B) =
    6*∑ i∈Ioc N B,∑ k∈Ioc N B,if i<k ∧ i∣k then trianglePrice (k/i) else 0 := by
  rw [cubic_trace_ordered]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  rw [sum_comm]
  exact sum_congr rfl fun k hk => sum_middle hi hk

private theorem sum_ratios {N B i : ℕ} (hi : i∈Ioc N B) :
    (∑ k∈Ioc N B,if i<k ∧ i∣k then trianglePrice (k/i) else 0)=
      ∑ r∈Icc 2 B,if i*r≤B then trianglePrice r else 0 := by
  classical
  let V := (Icc 2 B).filter (fun r => i*r≤B)
  let T := V.image (fun r => i*r)
  have hi0 := Nat.zero_lt_of_lt (mem_Ioc.mp hi).1
  have hlt {r : ℕ} (hr : r∈V) : i<i*r := by
    have hh := (mem_Icc.mp (mem_filter.mp hr).1).1
    simpa using Nat.mul_lt_mul_of_pos_left (show 1<r from hh) hi0
  have hs : T ⊆ Ioc N B := by
    intro k hk
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hk
    exact mem_Ioc.mpr ⟨(mem_Ioc.mp hi).1.trans (hlt hr),(mem_filter.mp hr).2⟩
  have hz (k : ℕ) (hk : k∈Ioc N B) (ht : k∉T) :
      (if i<k ∧ i∣k then trianglePrice (k/i) else 0)=0 := by
    apply if_neg
    rintro ⟨hlt,⟨r,rfl⟩⟩
    have hr : 1<r := Nat.lt_of_mul_lt_mul_left (by simpa using hlt : i*1<i*r)
    exact ht (mem_image.mpr ⟨r,mem_filter.mpr ⟨mem_Icc.mpr
      ⟨hr,(Nat.le_mul_of_pos_left _ hi0).trans (mem_Ioc.mp hk).2⟩,(mem_Ioc.mp hk).2⟩,rfl⟩)
  rw [←sum_subset hs hz,←sum_filter]
  dsimp only [T]
  rw [sum_image (fun _ _ _ _ he => Nat.eq_of_mul_eq_mul_left hi0 he)]
  exact sum_congr rfl fun r hr => by rw [if_pos ⟨hlt hr,dvd_mul_right i r⟩,Nat.mul_div_cancel_left _ hi0]

/-- Exact floor sum for the cubic moment, including all proper powers of every prime.
For outer ratio p^a, the multiplicity is (a-1) times the number of integers
strictly above N whose p^a-multiple remains in the interval. -/
theorem cubic_prime_contact_floor_sum (N B : ℕ) :
    Matrix.trace ((primeContactMatrix N B)^3) =
      6*∑ r∈Icc 2 B,((B/r-N:ℕ):ℝ)*trianglePrice r := by
  rw [cubic_prime_contact_matrix,cubic_trace_outer_pairs]
  congr 1
  rw [sum_congr rfl (fun i hi => sum_ratios hi),sum_comm]
  refine sum_congr rfl fun r hr => ?_
  have hr0 : 0<r := by have := (mem_Icc.mp hr).1; omega
  have hpair (i : ℕ) : i*r≤B ↔ i≤B/r := (Nat.le_div_iff_mul_le hr0).symm
  simp_rw [hpair]
  rw [←sum_filter]
  have he : ((Ioc N B).filter (fun i => i≤B/r))=Ioc N (B/r) := by
    ext i
    simp only [mem_filter,mem_Ioc]
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,h.2.trans (Nat.div_le_self _ _)⟩,h.2⟩⟩
  rw [he,sum_const,Nat.card_Ioc,nsmul_eq_mul]


/-- Spectral increment caused by adjoining the last site of a full prefix. -/
theorem cubic_prefix_increment (B : ℕ) :
    Matrix.trace ((primeContactMatrix 0 (B+1))^3)-Matrix.trace ((primeContactMatrix 0 B)^3)=
      6*∑ r∈(B+1).divisors,trianglePrice r := by
  classical
  let S := Icc 2 (B+1)
  have hs : Icc 2 B ⊆ S := Icc_subset_Icc le_rfl (Nat.le_succ B)
  have hz (r : ℕ) (h : r∈S) (hn : r∉Icc 2 B) : ((B/r:ℕ):ℝ)*trianglePrice r=0 := by
    have hlt : B<r := by have hr := mem_Icc.mp h; by_contra! hh; exact hn (mem_Icc.mpr ⟨hr.1,hh⟩)
    rw [Nat.div_eq_of_lt hlt,Nat.cast_zero,zero_mul]
  have hone : trianglePrice 1=0 := by simp [trianglePrice]
  have hsum : (∑ r∈S,if r∣B+1 then trianglePrice r else 0)=∑ r∈(B+1).divisors,trianglePrice r := by
    rw [←sum_filter]
    refine sum_subset ?_ ?_
    · intro r hr
      exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hr).2,Nat.succ_ne_zero _⟩
    · intro r hr hn
      have hpos := Nat.pos_of_mem_divisors hr
      have hdiv := Nat.dvd_of_mem_divisors hr
      have hub := Nat.le_of_dvd (Nat.succ_pos B) hdiv
      by_cases h1 : r=1
      · simpa only [h1] using hone
      · exact (hn (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hub⟩,hdiv⟩)).elim
  rw [cubic_prime_contact_floor_sum,cubic_prime_contact_floor_sum]
  simp only [Nat.sub_zero]
  rw [sum_subset hs hz,←mul_sub,←sum_sub_distrib,←hsum]
  congr 1
  apply sum_congr rfl
  intro r _
  by_cases hd : r∣B+1
  · rw [if_pos hd,Nat.succ_div_of_dvd hd,Nat.cast_add,Nat.cast_one]; ring
  · rw [if_neg hd,Nat.succ_div_of_not_dvd hd,sub_self]

private theorem price_nonneg (r : ℕ) : 0≤trianglePrice r := by
  unfold trianglePrice
  apply mul_nonneg _ vonMangoldt_nonneg
  rw [ArithmeticFunction.mul_apply]
  exact sum_nonneg fun _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg

private theorem price_in_squarefree {r : ℕ} (hs : Squarefree r) : trianglePrice r=0 := by
  by_cases hp : Λ r=0
  · simp [trianglePrice,hp]
  obtain ⟨p,b,hp',hb,rfl⟩ := (isPrimePow_nat_iff _).mp (vonMangoldt_ne_zero_iff.mp hp)
  have hb1 : b=1 := by
    by_contra hh
    have hsq : p*p∣p^b := by rw [←sq]; exact pow_dvd_pow _ (by omega)
    exact Nat.squarefree_iff_prime_squarefree.mp hs _ hp' hsq
  rw [trianglePrice_prime_power hp' hb,hb1];norm_num

/-- A single site leaves the cubic spectrum unchanged exactly when its index
is squarefree. Every repeated prime factor creates a positive new triangle. -/
theorem squarefree_iff_cubic_prefix_unchanged (B : ℕ) :
    Squarefree (B+1) ↔ Matrix.trace ((primeContactMatrix 0 (B+1))^3)=
      Matrix.trace ((primeContactMatrix 0 B)^3) := by
  rw [←sub_eq_zero,cubic_prefix_increment,mul_eq_zero]
  simp only [OfNat.ofNat_ne_zero,false_or]
  constructor
  · intro hs
    exact sum_eq_zero fun r hr => price_in_squarefree (hs.squarefree_of_dvd (Nat.dvd_of_mem_divisors hr))
  · intro hz
    apply Nat.squarefree_iff_prime_squarefree.mpr
    intro p hp hd
    have hmem : p^2∈(B+1).divisors := Nat.mem_divisors.mpr ⟨by simpa only [sq] using hd,Nat.succ_ne_zero _⟩
    have he := (sum_eq_zero_iff_of_nonneg (fun r _ => price_nonneg r)).mp hz _ hmem
    rw [trianglePrice_prime_power hp (by decide : 0<2)] at he
    have hl := Real.log_pos (show (1:ℝ)<p by exact_mod_cast hp.one_lt)
    norm_num at he
    exact hl.ne' he

end GaloisForLFunctions.SignedArithmeticCorrespondences.PrimeContactMoments
