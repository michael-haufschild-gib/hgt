import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.WalshConstraintsAtTheUnitaryMidpoint

/-!
# Large values at a positive fraction of prime-block sign assignments

The sign selection in Ghosh–Shuin, Lemma 3.7, guarantees one assignment
by a second moment. On the prime-block cube the fourth moment costs a
weight of three per active coordinate. A second-moment argument then
bounds how many sign assignments must witness a large value.
-/

open Finset GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- Real Walsh series on the subsets of a finite block set. -/
def blockSynthesis (P : Finset ℕ) (c : Finset ℕ → ℝ) (A : Finset ℕ) : ℝ :=
  ∑ T ∈ P.powerset, c T*(blockCharacter T A:ℝ)

/-- Quadratic coefficient mass with a rank price. -/
def blockRankEnergy (P : Finset ℕ) (r : ℝ) (c : Finset ℕ → ℝ) : ℝ :=
  ∑ T ∈ P.powerset, r^T.card*(c T)^2

private theorem rank_energy_nonneg (P : Finset ℕ) {r : ℝ} (hr : 0≤r) (c : Finset ℕ → ℝ) :
    0≤blockRankEnergy P r c := sum_nonneg fun T _ => mul_nonneg (pow_nonneg hr _) (sq_nonneg _)

private theorem rank_energy_insert {P : Finset ℕ} {p : ℕ} (hp : p∉P)
    (r : ℝ) (c : Finset ℕ → ℝ) :
    blockRankEnergy (insert p P) r c =
      blockRankEnergy P r c+r*blockRankEnergy P r (fun T => c (insert p T)) := by
  simp only [blockRankEnergy,sum_powerset_insert hp,mul_sum]
  congr 1
  apply sum_congr rfl
  intro T ht
  rw [card_insert_of_notMem (fun h => hp ((mem_powerset.mp ht) h)),pow_succ]
  ring

private theorem insert_mode {T : Finset ℕ} {p : ℕ} (hp : p∉T) (A : Finset ℕ) :
    (blockCharacter (insert p T) A:ℝ) = (if p∈A then -1 else 1)*(blockCharacter T A:ℝ) := by
  simp only [blockCharacter,prod_insert hp,Int.cast_mul]
  split_ifs <;> simp

private theorem synthesis_insert {P : Finset ℕ} {p : ℕ} (hp : p∉P)
    (c : Finset ℕ → ℝ) (A : Finset ℕ) :
    blockSynthesis (insert p P) c A = blockSynthesis P c A+
      (if p∈A then -1 else 1)*blockSynthesis P (fun T => c (insert p T)) A := by
  rw [blockSynthesis,sum_powerset_insert hp]
  unfold blockSynthesis
  rw [mul_sum]
  congr 1
  apply sum_congr rfl
  intro T ht
  rw [insert_mode (fun h => hp ((mem_powerset.mp ht) h))]
  ring

private theorem synthesis_off_axis {P A : Finset ℕ} {p : ℕ} (hp : p∉P) (ha : A⊆P)
    (c : Finset ℕ → ℝ) : blockSynthesis P c (insert p A)=blockSynthesis P c A := by
  apply sum_congr rfl
  intro T ht
  have hpt : p∉T := fun h => hp ((mem_powerset.mp ht) h)
  rw [blockCharacter_comm T (insert p A),insert_mode (fun h => hp (ha h)),if_neg hpt,one_mul,
    blockCharacter_comm A T]

/-- Fourth moment bounded by the square of the rank-three weighted mass.
The bound holds on every finite prime-block cube with no dimension factor
after averaging. -/
theorem block_fourth_rank_bound (P : Finset ℕ) (c : Finset ℕ → ℝ) :
    (∑ A ∈ P.powerset, (blockSynthesis P c A)^4) ≤
      (2:ℝ)^P.card*(blockRankEnergy P 3 c)^2 := by
  induction P using Finset.induction_on generalizing c with
  | empty => simp [blockSynthesis,blockRankEnergy,blockCharacter,←pow_mul]
  | @insert p P hp ih =>
    let b (T : Finset ℕ) := c (insert p T)
    let f := blockSynthesis P c
    let g := blockSynthesis P b
    let X := blockRankEnergy P 3 c
    let Y := blockRankEnergy P 3 b
    let N := (2:ℝ)^P.card
    have hX : 0≤X := rank_energy_nonneg P (by norm_num) _
    have hY : 0≤Y := rank_energy_nonneg P (by norm_num) _
    have hN : 0≤N := pow_nonneg (by norm_num) _
    have hf : (∑ A ∈ P.powerset, (f A)^4)≤N*X^2 := ih c
    have hg : (∑ A ∈ P.powerset, (g A)^4)≤N*Y^2 := ih b
    have pair : (∑ A ∈ P.powerset, (f A)^2*(g A)^2)≤N*X*Y := by
      have cs := sum_mul_sq_le_sq_mul_sq P.powerset (fun A => (f A)^2) (fun A => (g A)^2)
      simp only [←pow_mul] at cs
      have prod := mul_le_mul hf hg (sum_nonneg fun A _ => by positivity)
        (mul_nonneg hN (sq_nonneg X))
      apply le_of_sq_le_sq _ (mul_nonneg (mul_nonneg hN hX) hY)
      calc _ ≤ _ := cs.trans prod
           _ = _ := by ring
    have cell (A : Finset ℕ) (ha : A∈P.powerset) :
        (blockSynthesis (insert p P) c A)^4+(blockSynthesis (insert p P) c (insert p A))^4 =
          2*((f A)^4+6*((f A)^2*(g A)^2)+(g A)^4) := by
      have sub := mem_powerset.mp ha
      have miss : p∉A := fun h => hp (sub h)
      simp only [synthesis_insert hp,if_neg miss,mem_insert_self,if_true,one_mul,neg_one_mul,
        synthesis_off_axis hp sub]
      change (f A+g A)^4+(f A+ -(g A))^4=_
      ring
    rw [sum_powerset_insert hp,←sum_add_distrib,sum_congr rfl cell,←mul_sum,sum_add_distrib,
      sum_add_distrib,←mul_sum,rank_energy_insert hp,card_insert_of_notMem hp,pow_succ]
    change 2*((∑ A ∈ P.powerset, f A^4)+6*(∑ A ∈ P.powerset,f A^2*g A^2)+
      (∑ A ∈ P.powerset,g A^4))≤N*2*(X+3*Y)^2
    linarith only [hf,hg,pair,mul_nonneg hN (sq_nonneg Y)]

/-- Parseval in the same normalization used for the fourth-moment bound. -/
theorem block_second_exact (P : Finset ℕ) (c : Finset ℕ → ℝ) :
    (∑ A ∈ P.powerset, (blockSynthesis P c A)^2)=(2:ℝ)^P.card*blockRankEnergy P 1 c := by
  have orth (T : Finset ℕ) (ht : T∈P.powerset) (U : Finset ℕ) (hu : U∈P.powerset) :
      (∑ A ∈ P.powerset, (blockCharacter T A:ℝ)*(blockCharacter U A:ℝ)) =
        if T=U then (2:ℝ)^P.card else 0 := by
    simp_rw [blockCharacter_comm T,blockCharacter_comm U]
    exact_mod_cast blockCharacter_column_orthogonality (mem_powerset.mp ht) (mem_powerset.mp hu)
  have point A : (blockSynthesis P c A)^2 =
      ∑ T ∈ P.powerset, ∑ U ∈ P.powerset, c T*c U*((blockCharacter T A:ℝ)*(blockCharacter U A:ℝ)) := by
    rw [sq,blockSynthesis,sum_mul_sum]
    exact sum_congr rfl fun T _ => sum_congr rfl fun U _ => by ring
  rw [sum_congr rfl (fun A _ => point A),sum_comm,blockRankEnergy,mul_sum]
  apply sum_congr rfl
  intro T ht
  rw [sum_comm]
  simp only [← mul_sum]
  rw [sum_eq_single T]
  · rw [orth T ht T ht,if_pos rfl,one_pow,one_mul]
    ring
  · intro U hu hne
    rw [orth T ht U hu,if_neg hne.symm,mul_zero]
  · exact fun h => (h ht).elim

/-- Price for seeing at least half of the mean square. The numerator is
the squared unweighted coefficient energy; high-rank concentration pays
through the explicit rank-weighted denominator. -/
theorem block_large_value_count (P : Finset ℕ) (c : Finset ℕ → ℝ) :
    let E := blockRankEnergy P 1 c
    let B := blockRankEnergy P 3 c
    let large := P.powerset.filter (fun A => E/2≤(blockSynthesis P c A)^2)
    (2:ℝ)^P.card*E^2 ≤ 4*large.card*B^2 := by
  classical
  intro E B large
  let f := blockSynthesis P c
  let N := (2:ℝ)^P.card
  have hN : 0<N := pow_pos (by norm_num) _
  have hE : 0≤E := rank_energy_nonneg P (by norm_num) _
  have split (A : Finset ℕ) (_ : A∈P.powerset) :
      (f A)^2≤E/2 + (if E/2≤(f A)^2 then (f A)^2 else 0) := by
    split_ifs with h
    · linarith only [hE]
    · linarith only [h]
  have half := sum_le_sum split
  rw [sum_add_distrib,sum_const,nsmul_eq_mul,←sum_filter,card_powerset,Nat.cast_pow,Nat.cast_ofNat] at half
  change (∑ A ∈ P.powerset, (f A)^2)≤N*(E/2)+∑ A ∈ large, (f A)^2 at half
  rw [show (∑ A ∈ P.powerset, (f A)^2)=N*E from block_second_exact P c] at half
  have small : N*E/2 ≤ ∑ A ∈ large, (f A)^2 := by linarith only [half]
  have cs := sum_mul_sq_le_sq_mul_sq large (fun _ => (1:ℝ)) (fun A => (f A)^2)
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,←pow_mul] at cs
  have sub : (∑ A ∈ large, (f A)^4) ≤ N*B^2 :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => by positivity)).trans
      (block_fourth_rank_bound P c)
  have chain := (pow_le_pow_left₀ (div_nonneg (mul_nonneg hN.le hE) (by norm_num)) small 2).trans
    (cs.trans (mul_le_mul_of_nonneg_left sub (Nat.cast_nonneg large.card)))
  apply (le_of_mul_le_mul_left ?_ hN)
  linarith only [chain]

/-- If all active characters have rank at most q, at least a fraction
1/(4·9^q) of all assignments reaches half the mean square. -/
theorem block_low_rank_large_fraction (P : Finset ℕ) (c : Finset ℕ → ℝ) (q : ℕ)
    (degree : ∀ T ∈ P.powerset, c T≠0 → T.card≤q) :
    let E := blockRankEnergy P 1 c
    let large := P.powerset.filter (fun A => E/2≤(blockSynthesis P c A)^2)
    2^P.card ≤ 4*9^q*large.card := by
  classical
  intro E large
  have hE : 0≤E := rank_energy_nonneg P (by norm_num) _
  rcases hE.eq_or_lt with hzero|hpos
  · have all : large=P.powerset := filter_true_of_mem fun A _ => by
      rw [←hzero,zero_div]
      exact sq_nonneg _
    rw [all,card_powerset]
    have hp : 1≤4*9^q := Nat.succ_le_of_lt (by positivity)
    simpa only [one_mul] using Nat.mul_le_mul_right (2^P.card) hp
  · have wt : blockRankEnergy P 3 c ≤ 3^q*E := by
      change (∑ T ∈ P.powerset, (3:ℝ)^T.card*(c T)^2)≤3^q*∑ T ∈ P.powerset, (1:ℝ)^T.card*(c T)^2
      rw [mul_sum]
      apply sum_le_sum
      intro T hT
      simp only [one_pow,one_mul]
      by_cases hn : c T=0
      · simp [hn]
      · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (degree T hT hn)) (sq_nonneg _)
    have hh := block_large_value_count P c
    change (2:ℝ)^P.card*E^2≤4*large.card*(blockRankEnergy P 3 c)^2 at hh
    have hn := pow_le_pow_left₀ (rank_energy_nonneg P (by norm_num) c) wt 2
    have chain := hh.trans (mul_le_mul_of_nonneg_left hn (by positivity))
    rw [mul_pow,←pow_mul,(Nat.mul_comm q 2),pow_mul,show (3:ℝ)^2=9 by norm_num] at chain
    have bound : (2:ℝ)^P.card≤4*9^q*large.card := by
      apply le_of_mul_le_mul_right _ (sq_pos_of_pos hpos)
      linarith only [chain]
    exact_mod_cast bound

/-- A positive fraction of actual prime-block configurations reads at
least half the mean square of the rank-q part of the arithmetic cut. -/
theorem unitary_truncated_contrast_large_fraction (k q : ℕ) :
    let P := k.primeFactors
    let c (T : Finset ℕ) : ℝ := if T.card≤q then (unitaryWalshContrast k T:ℝ) else 0
    let E := blockRankEnergy P 1 c
    2^P.card ≤ 4*9^q*(P.powerset.filter (fun A => E/2≤(blockSynthesis P c A)^2)).card := by
  intro P c E
  apply block_low_rank_large_fraction
  intro T _ h
  by_contra he
  exact h (if_neg he)

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
