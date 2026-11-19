import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.FirstPrimesBeyondTheConductorInTheSignedPrefix

/-!
# One prime cut for every conductor in the fragment

The cost of removing all first primes through P is uniform in the terminal
conductor. Above the largest geometric threshold in the fragment, one
prime list suffices and only the two natural product endpoints remain.
-/

noncomputable section
open Finset Filter
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem firstPrimeReadingAbove_clip (P U n : ℕ) :
    firstPrimeReadingAbove P U n = firstPrimeReadingAbove (min P (splineHorizon n)) U n := by
  by_cases hP : P≤ splineHorizon n
  · rw [min_eq_left hP]
  rw [min_eq_right (le_of_not_ge hP)]
  unfold firstPrimeReadingAbove splineCountReading
  apply sum_congr rfl
  intro k hk
  have zero (r : ℕ) (h : k ≤ r) : ordinaryFactorTail (max 4 r) k
      (cappedCoprimeSlice 1 1 k (max (productLower 1 k) U) n)=0 := by
    simp [ordinaryFactorTail,Ioc_eq_empty_of_le (h.trans (le_max_right _ _))]
  beta_reduce
  rw [zero P ((mem_Icc.mp hk).2.trans (le_of_not_ge hP)),zero _ (mem_Icc.mp hk).2]

private theorem uniform_first_prime_cut_price :
    ∃ C : ℝ, 0≤C ∧ ∀ {n : ℕ}, 0<n → ∀ P : ℕ,
      let U := ⌊(n:ℝ)^(17/9:ℝ)⌋₊
      |(n:ℝ)^2*(cappedUpperProductReading U n n-firstPrimeReadingAbove P U n)| ≤
        C*(n:ℝ)*((P:ℝ)+1)*conductorLog n := by
  obtain ⟨A,hA,h⟩ := first_prime_cut_price
  obtain ⟨b,hb⟩ := eventually_atTop.mp eventually_seventeenNinths_above_lower
  let U (n : ℕ) := ⌊(n:ℝ)^(17/9:ℝ)⌋₊
  let E (n j : ℕ) := |(n:ℝ)^2*(cappedUpperProductReading (U n) n n-firstPrimeReadingAbove j (U n) n)|
  let D (n : ℕ) := ∑ j ∈ range (splineHorizon n+1), E n j
  let B := ∑ n ∈ range b, D n
  have hD (n : ℕ) : 0≤D n := sum_nonneg fun _ _ => abs_nonneg _
  have hB : 0≤B := sum_nonneg fun n _ => hD n
  refine ⟨A+B,add_nonneg hA hB,fun {n} hn P => ?_⟩
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlog := conductorLog_one_le n
  by_cases hbn : b≤n
  · apply (h P hn (hb n hbn)).trans
    apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hlog)
    exact mul_le_mul (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) (Nat.cast_nonneg n))
      (le_add_of_nonneg_right zero_le_one) (Nat.cast_nonneg P) (by positivity)
  · change E n P ≤ _
    have hj : min P (splineHorizon n) ∈ range (splineHorizon n+1) :=
      mem_range.mpr (Nat.lt_succ_of_le (min_le_right _ _))
    have he : E n P=E n (min P (splineHorizon n)) := by
      dsimp only [E]; rw [←firstPrimeReadingAbove_clip]
    have hrow := (single_le_sum (fun j _ => abs_nonneg _) hj :
      E n (min P (splineHorizon n)) ≤ D n)
    have hnb : D n≤B := single_le_sum (fun m _ => hD m) (mem_range.mpr (lt_of_not_ge hbn))
    rw [he]
    apply (hrow.trans hnb).trans
    have hscale : 1 ≤ (n:ℝ)*((P:ℝ)+1)*conductorLog n :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn'
        (le_add_of_nonneg_left (Nat.cast_nonneg P))) hlog
    exact ((le_add_of_nonneg_left hA).trans (le_mul_of_one_le_right (add_nonneg hA hB) hscale)).trans_eq (by ring)

/-- Largest geometric prime cutoff over precisely the positive conductors
in the terminal prefix. -/
def commonFirstPrimeCut (M : ℕ) := (Icc 1 M).sup capFreeFirstPrimeCut

theorem commonFirstPrimeCut_linear :
    ∃ K : ℝ, 0≤K ∧ ∀ M : ℕ, (commonFirstPrimeCut M:ℝ) ≤ K*M := by
  obtain ⟨K,hK,h⟩ := capFreeFirstPrimeCut_linear
  refine ⟨K,hK,fun M => ?_⟩
  have he : commonFirstPrimeCut M≤⌊K*(M:ℝ)⌋₊ := by
    apply Finset.sup_le
    intro n hn
    exact Nat.le_floor ((h (mem_Icc.mp hn).1).trans
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (mem_Icc.mp hn).2) hK))
  exact (Nat.cast_le.mpr he).trans (Nat.floor_le (mul_nonneg hK (Nat.cast_nonneg M)))

/-- A single first-prime cut works across the whole fragment. Its cost
is quadratic in the terminal conductor and linear in the size of the cut. -/
theorem common_first_prime_cut_fragments :
    ∃ C : ℝ, 0≤C ∧ ∀ (J M P : ℕ), commonFirstPrimeCut M ≤ P →
      |∑ n ∈ Ioc J M, (n:ℝ)^2*(cappedUpperProductReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n n -
        unrestrictedFirstPrimeReading P ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n)| ≤ C*(M:ℝ)^2*((P:ℝ)+1)*conductorLog M := by
  obtain ⟨C,hC,h⟩ := uniform_first_prime_cut_price
  refine ⟨C,hC,fun J M P hP => ?_⟩
  let X := C*(M:ℝ)*((P:ℝ)+1)*conductorLog M
  have hx : 0≤X := mul_nonneg (by positivity) (zero_le_one.trans (conductorLog_one_le M))
  have bound (n : ℕ) (hn : n ∈ Ioc J M) :
      |(n:ℝ)^2*(cappedUpperProductReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n n -
        unrestrictedFirstPrimeReading P ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n)| ≤ X := by
    have hn' := (Nat.zero_le J).trans_lt (mem_Ioc.mp hn).1
    have hnM := (mem_Ioc.mp hn).2
    have hcut : capFreeFirstPrimeCut n ≤ commonFirstPrimeCut M :=
      Finset.le_sup (f := capFreeFirstPrimeCut) (mem_Icc.mpr ⟨hn',hnM⟩)
    rw [←firstPrimeReadingAbove_eq_unrestricted (hcut.trans hP)]
    apply (h hn' P).trans
    dsimp only [X]
    exact mul_le_mul (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hnM) hC) (by positivity))
      (conductorLog_mono hn' hnM) (zero_le_one.trans (conductorLog_one_le n)) (by positivity)
  apply (abs_sum_le_sum_abs _ _).trans ((sum_le_sum bound).trans ?_)
  rw [sum_const,Nat.card_Ioc,nsmul_eq_mul]
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le M J)) hx).trans_eq (by dsimp only [X]; ring)

/-- At every terminal and throughout every partial fragment, the physical
upper cofactor cap and moving lower horizon can be removed using a single
prime list with only cubic-logarithmic loss. -/
theorem common_cap_free_prime_fragments :
    ∃ C : ℝ, 0≤C ∧ ∀ (J M : ℕ), 0<M →
      |∑ n ∈ Ioc J M, (n:ℝ)^2*(cappedUpperProductReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n n -
        unrestrictedFirstPrimeReading (commonFirstPrimeCut M) ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n)| ≤
        C*(M:ℝ)^3*conductorLog M := by
  obtain ⟨A,hA,h⟩ := common_first_prime_cut_fragments
  obtain ⟨D,hD,hcut⟩ := commonFirstPrimeCut_linear
  refine ⟨A*(D+1),by positivity,fun J M hM => ?_⟩
  apply (h J M _ le_rfl).trans
  have hm : (1:ℝ)≤M := by exact_mod_cast hM
  have hs : (commonFirstPrimeCut M:ℝ)+1≤(D+1)*M := (add_le_add (hcut M) hm).trans_eq (by ring)
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by positivity : 0≤A*(M:ℝ)^2))
    (zero_le_one.trans (conductorLog_one_le M))).trans_eq (by ring)

/-- One terminal prime list for the eleven-thirds price. All cofactors in
the retained reading have their natural endpoints. -/
def elevenThirdsFirstPrimeCut (M : ℕ) :=
  max (commonFirstPrimeCut M) ⌊(M:ℝ)^(5/3:ℝ)/conductorLog M⌋₊

theorem eleven_thirds_common_first_prime_fragments :
    ∃ C : ℝ, 0≤C ∧ ∀ (J M : ℕ), 0<M →
      |∑ n ∈ Ioc J M, (n:ℝ)^2*(cappedUpperProductReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n n -
        unrestrictedFirstPrimeReading (elevenThirdsFirstPrimeCut M) ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n)| ≤
        C*(M:ℝ)^(11/3:ℝ) := by
  obtain ⟨A,hA,h⟩ := common_first_prime_cut_fragments
  obtain ⟨D,hD,hcut⟩ := commonFirstPrimeCut_linear
  obtain ⟨E,hE,hlog⟩ := conductorLog_subpower (by norm_num : (0:ℝ)<2/3)
  refine ⟨A*((D+1)*E+1),by positivity,fun J M hM => ?_⟩
  have hm : (1:ℝ)≤M := by exact_mod_cast hM
  have hm0 := zero_lt_one.trans_le hm
  let H := conductorLog M
  let Q := (M:ℝ)^(5/3:ℝ)
  have hQ : 0≤Q := Real.rpow_nonneg hm0.le _
  have hH := conductorLog_one_le M
  have hH0 : 0<H := zero_lt_one.trans_le hH
  have hL : H ≤ E*(M:ℝ)^(2/3:ℝ) :=
    (le_self_pow₀ hH (by decide : 6≠0)).trans (hlog hM)
  have h5 : (M:ℝ)*(M:ℝ)^(2/3:ℝ)=Q := by
    dsimp only [Q]
    rw [show (5/3:ℝ)=1+2/3 by norm_num,Real.rpow_add hm0,Real.rpow_one]
  have hsum : ((commonFirstPrimeCut M:ℝ)+1)*H ≤ (D+1)*E*Q := by
    have hl := (add_le_add (hcut M) hm).trans_eq (show D*M+M=(D+1)*M by ring)
    exact (mul_le_mul hl hL hH0.le (by positivity)).trans_eq (by rw [←h5]; ring)
  have hf : (⌊Q/H⌋₊:ℝ)*H ≤ Q :=
    (le_div_iff₀ hH0).mp (Nat.floor_le (div_nonneg hQ hH0.le))
  have hcap : ((elevenThirdsFirstPrimeCut M:ℝ)+1)*H ≤ ((D+1)*E+1)*Q := by
    change ((max (commonFirstPrimeCut M) ⌊Q/H⌋₊:ℕ)+1:ℝ)*H ≤ _
    rw [Nat.cast_max]
    have hm' : max (commonFirstPrimeCut M:ℝ) (⌊Q/H⌋₊:ℝ) ≤ commonFirstPrimeCut M+(⌊Q/H⌋₊:ℝ) :=
      max_le (le_add_of_nonneg_right (Nat.cast_nonneg _)) (le_add_of_nonneg_left (Nat.cast_nonneg _))
    calc _ ≤ ((commonFirstPrimeCut M:ℝ)+(⌊Q/H⌋₊:ℝ)+1)*H :=
           mul_le_mul_of_nonneg_right (add_le_add hm' le_rfl) hH0.le
         _ ≤ _ := by linarith only [hsum,hf]
  apply (h J M _ (le_max_left _ _)).trans
  rw [show (11/3:ℝ)=2+5/3 by norm_num,Real.rpow_add hm0,Real.rpow_two]
  exact (le_of_eq (show A*(M:ℝ)^2*((elevenThirdsFirstPrimeCut M:ℝ)+1)*conductorLog M =
      (A*(M:ℝ)^2)*(((elevenThirdsFirstPrimeCut M:ℝ)+1)*H) by ring)).trans
    ((mul_le_mul_of_nonneg_left hcap (by positivity : 0≤A*(M:ℝ)^2)).trans_eq (by dsimp only [Q]; ring))

#print axioms commonFirstPrimeCut_linear
#print axioms common_first_prime_cut_fragments
#print axioms common_cap_free_prime_fragments
#print axioms eleven_thirds_common_first_prime_fragments
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
