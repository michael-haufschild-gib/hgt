import GaloisForLFunctions.CountingHolography.Sections.ThreeSquareConductorsWithZeroPoleDegree

/-!
# Prime contacts of two independently translated groups of conductors

If each group occupies a bounded multiplicative window, every long
contact is mixed. Reversing one group's signs reverses the entire row.
On disjoint labels the resolutions of both divisors agree exactly.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset AbsoluteGeometryOfSpecZ ArithmeticFunction

/-- Ratios of active conductors in the divisor are at most R. -/
def boundedConductorRatios {N : ℕ} (R : ℝ) (a : Fin N → ℤ) : Prop :=
  ∀ i j, a i ≠ 0 → a j ≠ 0 → (j:ℝ)+1 ≤ R*((i:ℝ)+1)

private theorem bounded_rows_vanish (R : ℝ) : ∃ Q : ℕ, ∀ (N : ℕ) (a : Fin N → ℤ),
    boundedConductorRatios R a → ∀ {L r k : ℕ}, Q < k →
      contactMultiplicity (packet a) L r k = 0 := by
  obtain ⟨D,hD,h⟩ := contactMultiplicity_support
  refine ⟨⌈D*R⌉₊,fun N a ha {L r k} hk => ?_⟩
  by_contra hne
  obtain ⟨i,j,hi,hj,h₁,_⟩ := h N a L r k hne
  have hhigh : (⌈D*R⌉₊ : ℝ) < k := by exact_mod_cast hk
  have hlow : (k:ℝ) ≤ D*R := by
    apply (mul_le_mul_iff_left₀ (by positivity : 0 < (i:ℝ)+1)).mp
    linarith only [h₁,mul_le_mul_of_nonneg_left (ha i j hi hj) (zero_le_one.trans hD)]
  exact hhigh.not_ge (hlow.trans (Nat.le_ceil _))

private theorem resolution_add_sub {N : ℕ} {a b : Fin N → ℤ} (h : ∀ i, a i = 0 ∨ b i = 0) :
    resolution (a+b) = resolution (a-b) := by
  unfold resolution
  apply sum_congr rfl
  intro i _
  rcases h i with hi | hi <;> simp [Pi.add_apply,Pi.sub_apply,hi]

private theorem paired_rows {N : ℕ} (a b : Fin N → ℤ) (L r k : ℕ) :
    contactMultiplicity (packet (a+b)) L r k + contactMultiplicity (packet (a-b)) L r k =
      2*(contactMultiplicity (packet a) L r k + contactMultiplicity (packet b) L r k) := by
  have hplus (j : ℕ) : degreeSample (packet (a+b)) r j =
      degreeSample (packet a) r j+degreeSample (packet b) r j := by
    simp only [degreeSample,packet,splineSource,Pi.add_apply,Int.cast_add,add_mul,sum_add_distrib]
  have hminus (j : ℕ) : degreeSample (packet (a-b)) r j =
      degreeSample (packet a) r j-degreeSample (packet b) r j := by
    simp only [degreeSample,packet,splineSource,Pi.sub_apply,Int.cast_sub,sub_mul,sum_sub_distrib]
  let F := degreeSample (packet a) r
  let G := degreeSample (packet b) r
  have row (j : ℕ) : (F j+G j)*(F (j*k)+G (j*k))/j + (F j-G j)*(F (j*k)-G (j*k))/j =
      2*(F j*F (j*k)/j+G j*G (j*k)/j) := by ring
  unfold contactMultiplicity
  simp only [hplus,hminus]
  rw [← mul_add,← sum_add_distrib]
  simp_rw [row,← mul_sum,sum_add_distrib]
  ring

/-- At every long lag the two integral valuations sum to zero or minus
one. Equality to zero occurs precisely at unrounded integral contacts. -/
theorem complementary_contact_valuations (R : ℝ) : ∃ Q : ℕ, ∀ (N : ℕ) (a b : Fin N → ℤ),
    boundedConductorRatios R a → boundedConductorRatios R b → ∀ {L r k : ℕ}, Q < k →
    let x := contactMultiplicity (packet (a+b)) L r k
    let y := contactMultiplicity (packet (a-b)) L r k
    -1 ≤ ⌊x⌋+⌊y⌋ ∧ ⌊x⌋+⌊y⌋ ≤ 0 ∧ (⌊x⌋+⌊y⌋ = 0 ↔ x = (⌊x⌋ : ℝ)) := by
  obtain ⟨Q,h⟩ := bounded_rows_vanish R
  refine ⟨Q,fun N a b ha hb {L r k} hk => ?_⟩
  let x := contactMultiplicity (packet (a+b)) L r k
  let y := contactMultiplicity (packet (a-b)) L r k
  have he := paired_rows a b L r k
  rw [h N a ha hk,h N b hb hk,add_zero,mul_zero] at he
  have hy : y = -x := by change x+y=0 at he; linarith only [he]
  change -1 ≤ ⌊x⌋+⌊y⌋ ∧ ⌊x⌋+⌊y⌋ ≤ 0 ∧ (⌊x⌋+⌊y⌋ = 0 ↔ x = (⌊x⌋ : ℝ))
  rw [hy,Int.floor_neg]
  have hl := Int.floor_le_ceil x
  have hu := Int.ceil_le_floor_add_one x
  refine ⟨by omega,by omega,?_⟩
  constructor
  · intro hzero
    have hi : ⌈x⌉ = ⌊x⌋ := by omega
    exact le_antisymm (by simpa only [hi] using Int.le_ceil x) (Int.floor_le x)
  · intro hfloor
    have heq := congrArg Int.ceil hfloor
    simp only [Int.ceil_intCast] at heq
    omega

/-- The product of the two actual ordinary-prime generators has a
uniform quadratic logarithmic upper bound at every finite resolution.
The distance between the two conductor windows is unrestricted. -/
theorem complementary_ordinaryPrimeGenerators (R : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (N : ℕ) (a b : Fin N → ℤ), boundedConductorRatios R a → boundedConductorRatios R b →
    (∀ i, a i = 0 ∨ b i = 0) →
    Real.log (ordinaryPrimeGenerator (a+b) : ℝ)+Real.log (ordinaryPrimeGenerator (a-b) : ℝ) ≤
      C*((∑ i, |(a i:ℝ)|)^2+(∑ i, |(b i:ℝ)|)^2) := by
  obtain ⟨Q,hQ⟩ := bounded_rows_vanish R
  obtain ⟨A,hA,hsize⟩ := contactMultiplicity_size
  let W := ∑ k ∈ Icc 2 Q, vonMangoldt k
  have hW : 0 ≤ W := sum_nonneg fun _ _ => vonMangoldt_nonneg
  have hA' := zero_le_one.trans hA
  refine ⟨2*A*W,by positivity,fun N a b ha hb hdisj => ?_⟩
  let L := 3*windowEnd N
  let r := resolution (a-b)
  let S := (Icc 2 L).filter Nat.Prime
  let J := S.filter (· ≤ Q)
  let X := fun v : Fin N → ℤ => contactMultiplicity (packet v) L r
  let M := (∑ i, |(a i:ℝ)|)^2+(∑ i, |(b i:ℝ)|)^2
  have hM : 0 ≤ M := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hs {k : ℕ} (hk : k ∈ S) (v : Fin N → ℤ) : X v k ≤ A*(∑ i, |(v i:ℝ)|)^2 := by
    have hk' : (1:ℝ) ≤ k := by exact_mod_cast (mem_filter.mp hk).2.one_le
    have hrt : 1 ≤ Real.sqrt k := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hk'
    exact (le_abs_self _).trans ((hsize N v L r k).trans (div_le_self (by positivity) hrt))
  have htail : ∀ k ∈ S, k ∉ J → (2*(X a k+X b k))*vonMangoldt k = 0 := by
    intro k hk hj
    have hl : Q < k := lt_of_not_ge fun h => hj (mem_filter.mpr ⟨hk,h⟩)
    unfold X
    rw [hQ N a ha hl,hQ N b hb hl,add_zero,mul_zero,zero_mul]
  have hJ : J ⊆ Icc 2 Q := fun k hk => mem_Icc.mpr
    ⟨(mem_Icc.mp (mem_filter.mp (mem_filter.mp hk).1).1).1,(mem_filter.mp hk).2⟩
  rw [log_ordinaryPrimeGenerator,log_ordinaryPrimeGenerator,resolution_add_sub hdisj,← sum_add_distrib]
  change (∑ k ∈ S, (⌊X (a+b) k⌋:ℝ)*vonMangoldt k+(⌊X (a-b) k⌋:ℝ)*vonMangoldt k) ≤ _
  calc _ ≤ ∑ k ∈ S, (2*(X a k+X b k))*vonMangoldt k := by
          refine sum_le_sum fun k _ => ?_
          rw [← add_mul]
          exact mul_le_mul_of_nonneg_right ((add_le_add (Int.floor_le _) (Int.floor_le _)).trans_eq
            (paired_rows a b L r k)) vonMangoldt_nonneg
    _ = ∑ k ∈ J, (2*(X a k+X b k))*vonMangoldt k := (sum_subset (filter_subset _ _) htail).symm
    _ ≤ ∑ k ∈ J, (2*A*M)*vonMangoldt k := by
          apply sum_le_sum
          intro k hk
          apply mul_le_mul_of_nonneg_right _ vonMangoldt_nonneg
          unfold M
          linarith only [hs (mem_filter.mp hk).1 a,hs (mem_filter.mp hk).1 b]
    _ ≤ (2*A*M)*W := by
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hJ
            (fun _ _ _ => vonMangoldt_nonneg)) (by positivity)
    _ = _ := by unfold M; ring

/-- Reverse the signs on the conductors larger than one. -/
def reverseUpperGraphs {N : ℕ} (a : Fin N → ℤ) (i : Fin N) :=
  if i.val = 0 then a i else -a i

private theorem upper_square_band {n : ℕ} (hn : 0 < n) {i : Fin ((2*n+1)^2+1)}
    (hi : i.val ≠ 0) (ha : successorSquareTriple n i ≠ 0) :
    (n:ℝ)^2 ≤ (i:ℝ)+1 ∧ (i:ℝ)+1 ≤ 9*(n:ℝ)^2 := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlo : (n:ℝ)^2 ≤ ((2*n+1:ℕ):ℝ)^2 := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    push_cast
    linarith only [hn']
  have hhi : ((2*n+1:ℕ):ℝ)^2 ≤ 9*(n:ℝ)^2 := by
    have he := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2*n+1)
      (by linarith only [hn'] : 2*(n:ℝ)+1 ≤ 3*n) 2
    push_cast
    linarith only [he]
  rcases successorSquareTriple_support hn ha with he | he | he
  · have hz : (i:ℝ) = 0 := by linarith only [he]
    exact (hi (by exact_mod_cast hz)).elim
  · rw [he]
    exact ⟨le_rfl,by linarith only [sq_nonneg (n:ℝ)]⟩
  · rw [he]; exact ⟨hlo,hhi⟩

/-- At every square conductor and every multiplicity, the ordinary
prime product and its sign-reversed companion together fit in one base. -/
theorem successorSquare_complementary_power : ∃ B : ℕ, 0 < B ∧
    ∀ {n : ℕ}, 0 < n → ∀ m : ℕ,
      ordinaryPrimeGenerator (m • successorSquareTriple n) *
        ordinaryPrimeGenerator (m • reverseUpperGraphs (successorSquareTriple n)) ≤ (B:ℚ)^(m^2) := by
  obtain ⟨C,hC,h⟩ := complementary_ordinaryPrimeGenerators 9
  let B := ⌈Real.exp (32*C)⌉₊
  have hB : 0 < B := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hlog : 32*C ≤ Real.log B := (Real.le_log_iff_exp_le (Nat.cast_pos.mpr hB)).mpr (Nat.le_ceil _)
  refine ⟨B,hB,fun {n} hn m => ?_⟩
  let d := successorSquareTriple n
  let c := m • d
  let a := fun i : Fin ((2*n+1)^2+1) => if i.val = 0 then c i else 0
  let b := fun i : Fin ((2*n+1)^2+1) => if i.val = 0 then 0 else c i
  have ha : boundedConductorRatios 9 a := by
    intro i j hi hj
    by_cases hx : i.val = 0 <;> by_cases hy : j.val = 0 <;> simp [a,hx,hy] at hi hj ⊢
  have hb (i) (hi : b i ≠ 0) : (n:ℝ)^2 ≤ (i:ℝ)+1 ∧ (i:ℝ)+1 ≤ 9*(n:ℝ)^2 := by
    have hx : i.val ≠ 0 := fun he => hi (by simp [b,he])
    apply upper_square_band hn hx
    intro he
    apply hi
    simp [b,c,d,hx,Pi.smul_apply,he]
  have hb' : boundedConductorRatios 9 b := fun i j hi hj =>
    (hb j hj).2.trans (mul_le_mul_of_nonneg_left (hb i hi).1 (by norm_num))
  have hdisj (i) : a i = 0 ∨ b i = 0 := by by_cases hx : i.val = 0 <;> simp [a,b,hx]
  have he₁ : a+b = c := by funext i; by_cases hx : i.val = 0 <;> simp [a,b,Pi.add_apply,hx]
  have he₂ : a-b = m • reverseUpperGraphs d := by
    funext i
    by_cases hx : i.val = 0 <;> simp [a,b,c,reverseUpperGraphs,Pi.sub_apply,Pi.smul_apply,hx]
  have hc : (∑ i, |(c i:ℝ)|) ≤ 4*(m:ℝ) := by
    simp only [c,Pi.smul_apply,nsmul_eq_mul,Int.cast_mul,Int.cast_natCast,abs_mul,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) m),← mul_sum]
    exact (mul_le_mul_of_nonneg_left (successorSquareTriple_mass n) (Nat.cast_nonneg _)).trans_eq (mul_comm _ _)
  have hsplit (i) : |(a i:ℝ)| ≤ |(c i:ℝ)| ∧ |(b i:ℝ)| ≤ |(c i:ℝ)| := by
    by_cases hx : i.val = 0 <;> simp [a,b,hx,abs_nonneg]
  have hsa := pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) ((sum_le_sum fun i _ => (hsplit i).1).trans hc) 2
  have hsb := pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) ((sum_le_sum fun i _ => (hsplit i).2).trans hc) 2
  have hm : C*((∑ i, |(a i:ℝ)|)^2+(∑ i, |(b i:ℝ)|)^2) ≤ 32*C*(m:ℝ)^2 := by
    have he := mul_le_mul_of_nonneg_left (add_le_add hsa hsb) hC
    linarith only [he]
  have hh := (h _ a b ha hb' hdisj).trans (hm.trans (mul_le_mul_of_nonneg_right hlog (sq_nonneg _)))
  rw [he₁,he₂] at hh
  have hpos {N : ℕ} (v : Fin N → ℤ) : 0 < (ordinaryPrimeGenerator v : ℝ) := by
    exact_mod_cast (prod_pos (fun k _ => zpow_pos (Nat.cast_pos.mpr (contactBase_pos k)) _) :
      0 < ordinaryPrimeGenerator v)
  have hreal : (ordinaryPrimeGenerator c : ℝ)*(ordinaryPrimeGenerator (m • reverseUpperGraphs d) : ℝ) ≤
      (B:ℝ)^(m^2) := by
    apply (Real.log_le_log_iff (mul_pos (hpos _) (hpos _)) (pow_pos (Nat.cast_pos.mpr hB) _)).mp
    rw [Real.log_mul (hpos _).ne' (hpos _).ne',Real.log_pow,Nat.cast_pow,mul_comm _ (Real.log B)]
    exact hh
  exact_mod_cast hreal

#print axioms successorSquare_complementary_power
#print axioms complementary_contact_valuations
#print axioms complementary_ordinaryPrimeGenerators

end GaloisForLFunctions.CountingHolography.Sections
