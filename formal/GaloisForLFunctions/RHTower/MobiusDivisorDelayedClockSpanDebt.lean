import GaloisForLFunctions.RHTower.MobiusDivisorInheritedPrimeInsertionProducer
import GaloisForLFunctions.RHTower.MobiusDivisorPrescribedClockBlock
import GaloisForLFunctions.RHTower.Sieve.MertensIntervalShell

/-!
# Positive inherited debt across delayed logarithmic prime spans

The actual omitted-prime producer forces a positive reciprocal-prime cost
for half repayment. Mertens' interval theorem bounds the entire helper
window, without restricting cardinality or inverse-square-root mass.

Consequently an actual positive debt survives every helper set whose prime
clocks lie between tau and (1+kappa)*tau after a source threshold. One
common eventual cutoff tail carries the positive lower bound in the full
logarithmically weighted finite clock energy for every helper subset.

This closes the short delayed-span repayment candidate. Paid exhaustive
continuation still requires older active helpers or a wider clock span,
with cumulative control of the complete mixed source terms and cutoffs.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

private lemma window_reciprocal_mass (S : Finset ℕ) {τ κ : ℝ}
    (hτ : 0 < τ) (hκ : 0 ≤ κ)
    (hS : ∀p∈S,p.Prime ∧ τ < Real.log p ∧ Real.log p ≤ (1+κ)*τ) :
    τ*(∑p∈S,1/((p:ℝ)+1)) ≤ 
      κ*τ+Real.log 2+Sieve.mertensIntervalConst := by
  classical
  by_cases hne : S.Nonempty
  · let m := S.min' hne
    let a := m-1
    let b := S.max' hne
    have hm : m∈S := S.min'_mem hne
    have hb : b∈S := S.max'_mem hne
    have hm2 : 2 ≤ m := (hS m hm).1.two_le
    have ha1 : 1 ≤ a := by dsimp [a]; omega
    have hab : a ≤ b := (Nat.sub_le m 1).trans (S.min'_le_max' hne)
    have ha0 : (0:ℝ) < a := by exact_mod_cast ha1
    have hm0 : (0:ℝ) < m := by exact_mod_cast (hS m hm).1.pos
    have hme : (a:ℝ)=(m:ℝ)-1 := by
      dsimp [a]
      rw [Nat.cast_sub (by omega : 1 ≤ m)]
      norm_num
    have hmle : (m:ℝ) ≤ 2*(a:ℝ) := by
      have hm2R : (2:ℝ) ≤ m := by exact_mod_cast hm2
      linarith only [hme,hm2R]
    have hlogm := Real.log_le_log hm0 hmle
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) ha0.ne'] at hlogm
    have hloga : τ-Real.log 2 ≤ Real.log (a:ℝ) := by
      have h := (hS m hm).2.1
      linarith only [h,hlogm]
    have hlogb := (hS b hb).2.2
    have hsub : S⊆Nat.primesLE b \ Nat.primesLE a := by
      intro p hp
      apply Finset.mem_sdiff.mpr
      refine ⟨Nat.mem_primesLE.mpr ⟨S.le_max' p hp,(hS p hp).1⟩,?_⟩
      intro hpa
      have hle := (Nat.mem_primesLE.mp hpa).1
      have hmin : m ≤ p := S.min'_le p hp
      dsimp [a] at hle
      omega
    have hM := Sieve.sum_log_div_prime_interval_le ha1 hab hsub
    have hterm (p : ℕ) (hp : p∈S) : τ*(1/((p:ℝ)+1)) ≤ Real.log p/(p:ℝ) := by
      have hp0 : (0:ℝ) < p := by exact_mod_cast (hS p hp).1.pos
      calc
        _ ≤ τ*(1/(p:ℝ)) := mul_le_mul_of_nonneg_left
          (one_div_le_one_div_of_le hp0 (by linarith)) hτ.le
        _ = τ/(p:ℝ) := by ring
        _ ≤ _ := div_le_div_of_nonneg_right (hS p hp).2.1.le hp0.le
    have hs := sum_le_sum hterm
    rw [← mul_sum] at hs
    linarith only [hs,hM,hloga,hlogb]
  · have he : S=∅ := not_nonempty_iff_eq_empty.mp hne
    rw [he]
    simp only [sum_empty,mul_zero]
    exact add_nonneg (add_nonneg (mul_nonneg hκ hτ.le)
      (Real.log_nonneg (by norm_num))) Sieve.mertensIntervalConst_nonneg

/-- Actual omitted-prime debt survives every delayed helper batch in a
short logarithmic span, with no cardinality or source-mass restriction.
The full finite-clock lower bound holds on one common tail for all helper
subsets in that span. This excludes a local preparation strategy, not RH. -/
theorem exists_mobiusDivisorLogClockSpanDebt :
    ∀P : Finset ℕ,P.Nonempty → (∀p∈P,p.Prime) → Even P.card → ∀N : ℕ,
      ∃r : ℕ,∃δ κ T : ℝ,
        r.Prime ∧ N < r ∧ r∉P ∧ 0 < δ ∧ 0 < κ ∧ 0 < T ∧
        (∑'n,mobiusDivisorFixedCoreBlockMass P n)+2*δ=
          ∑'n,mobiusDivisorFixedCoreBlockMass (insert r P) n ∧
        ∀τ : ℝ,T ≤ τ →
          (∀S : Finset ℕ,
            (∀p∈S,p.Prime ∧ τ < Real.log p ∧ Real.log p ≤ (1+κ)*τ) →
            (∑'n,mobiusDivisorFixedCoreBlockMass P n)+δ < 
              ∑'n,mobiusDivisorFixedCoreBlockMass (insert r (P∪S)) n) ∧
          ∀ᶠ M : ℕ in atTop,∀S : Finset ℕ,
            (∀p∈S,p.Prime ∧ τ < Real.log p ∧ Real.log p ≤ (1+κ)*τ) →
            δ*(M:ℝ)^2*(1+Real.log M) ≤ 
              mobiusDivisorFiniteClockEnergy 1 M (insert r (P∪S))-
                mobiusDivisorFiniteClockEnergy 1 M P := by
  classical
  intro P hP hprime heven N
  obtain ⟨r,δ,η,W,K,τ₀,hr,hNr,hrP,hδ,hη,hW,hK,hgap,hcost,hprep⟩ :=
    exists_mobiusDivisorClockDelayedInsertionProducer P hP hprime heven N
  let κ := η/4
  let C := Real.log 2+Sieve.mertensIntervalConst
  let T := max τ₀ (max 1 (4*(C+1)/η))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hC : 0 ≤ C := add_nonneg (Real.log_nonneg (by norm_num)) Sieve.mertensIntervalConst_nonneg
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one
    ((le_max_left 1 _).trans (le_max_right τ₀ _))
  refine ⟨r,δ,κ,T,hr,hNr,hrP,hδ,hκ,hT,hgap,?_⟩
  intro τ hTτ
  have hτ : 0 < τ := hT.trans_le hTτ
  have hτ₀ : τ₀ ≤ τ := (le_max_left _ _).trans hTτ
  have hsize : 4*(C+1) ≤ η*τ := by
    have h : 4*(C+1)/η ≤ τ :=
      (le_max_right 1 _).trans ((le_max_right τ₀ _).trans hTτ)
    have hm := (div_le_iff₀ hη).mp h
    simpa only [mul_comm] using hm
  have hsurvive (S : Finset ℕ)
      (hS : ∀p∈S,p.Prime ∧ τ < Real.log p ∧ Real.log p ≤ (1+κ)*τ) :
      (∑'n,mobiusDivisorFixedCoreBlockMass P n)+δ < 
        ∑'n,mobiusDivisorFixedCoreBlockMass (insert r (P∪S)) n := by
    have hmass := window_reciprocal_mass S hτ hκ.le hS
    have hupper : (∑p∈S,1/((p:ℝ)+1)) ≤ η := by
      by_contra hn
      have hh := mul_lt_mul_of_pos_left (lt_of_not_ge hn) hτ
      rw [add_assoc] at hmass
      change τ*(∑p∈S,1/((p:ℝ)+1)) ≤ κ*τ+C at hmass
      dsimp [κ] at hmass
      nlinarith only [hmass,hh,hsize,hη,hτ]
    by_contra hn
    have hneed := (hcost τ hτ₀ S (fun p hp => ⟨(hS p hp).1,(hS p hp).2.1⟩)
      (le_of_not_gt hn)).1
    exact (not_lt_of_ge hupper) hneed
  refine ⟨hsurvive,?_⟩
  let A := Nat.primesLE ⌊Real.exp ((1+κ)*τ)⌋₊
  have hmem (S : Finset ℕ)
      (hS : ∀p∈S,p.Prime ∧ τ < Real.log p ∧ Real.log p ≤ (1+κ)*τ) : S∈A.powerset := by
    apply mem_powerset.mpr
    intro p hp
    apply Nat.mem_primesLE.mpr
    refine ⟨?_,(hS p hp).1⟩
    apply Nat.le_floor
    calc
      (p:ℝ) = Real.exp (Real.log p) := (Real.exp_log (by exact_mod_cast (hS p hp).1.pos)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (hS p hp).2.2
  have hevent (S : Finset ℕ) (_hSA : S∈A.powerset) :
      ∀ᶠ M : ℕ in atTop,
        (∀p∈S,p.Prime ∧ τ < Real.log p ∧ Real.log p ≤ (1+κ)*τ) →
        δ*(M:ℝ)^2*(1+Real.log M) ≤ 
          mobiusDivisorFiniteClockEnergy 1 M (insert r (P∪S))-
            mobiusDivisorFiniteClockEnergy 1 M P := by
    by_cases hS : ∀p∈S,p.Prime ∧ τ < Real.log p ∧ Real.log p ≤ (1+κ)*τ
    · have hpr : ∀p∈insert r (P∪S),p.Prime := by
        intro p hp
        rcases mem_insert.mp hp with rfl|hp
        · exact hr
        · exact (mem_union.mp hp).elim (hprime p) (fun hpS => (hS p hpS).1)
      have hlim := (tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log _ hpr).sub
        (tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log P hprime)
      have hstrict : δ < (∑'n,mobiusDivisorFixedCoreBlockMass (insert r (P∪S)) n)-
          (∑'n,mobiusDivisorFixedCoreBlockMass P n) := by linarith only [hsurvive S hS]
      filter_upwards [hlim.eventually (eventually_gt_nhds hstrict),
        eventually_ge_atTop (1:ℕ)] with M hM hM1
      intro _
      have hMR : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
      have hlog : 0 ≤ Real.log (M:ℝ) := Real.log_nonneg (by exact_mod_cast hM1)
      have hden : 0 < (M:ℝ)^2*(1+Real.log M) := by positivity
      simp only [← sub_div] at hM
      have hm := (le_div_iff₀ hden).mp hM.le
      simpa only [mul_assoc] using hm
    · exact Filter.Eventually.of_forall (fun _ h => (hS h).elim)
  filter_upwards [(Filter.eventually_all_finset A.powerset).mpr hevent] with M hM
  intro S hS
  exact hM S (hmem S hS) hS

end RHTower
