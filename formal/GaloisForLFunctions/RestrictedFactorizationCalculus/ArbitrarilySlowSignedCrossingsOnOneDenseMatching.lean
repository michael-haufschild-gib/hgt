import GaloisForLFunctions.RestrictedFactorizationCalculus.BoundedCrossingChargeAtEveryPairOfWalls
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheMertensAbscissaOnOneDensityZeroFixedSet

/-!
# Arbitrarily slow signed crossings on one density-one matching

A different bounded cofactor cap may be used in each disjoint block.
Place its left wall where the prescribed growth function already pays
the local bound. Every sharp cutoff reads at most one block.
-/

noncomputable section

open Finset Filter ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev tol (j : ℕ) : ℝ := 1/((j:ℝ)+2)

private structure CappedTable (j : ℕ) where
  swap : ℕ → ℕ
  onset : ℕ
  cost : ℝ
  law : ∀ n,Squarefree n → swap (swap n)=n ∧ (swap n=n ∨ GlobalDyadicOneTwoRel n (swap n))
  near : ∀ n,Squarefree n → |(swap n:ℝ)-n| ≤ tol j*n
  count : ∀ X,onset ≤ X → ((prefixUnpaid swap X).card:ℝ) ≤ tol j*X
  signed : ∀ L U X,|∑ n ∈ wallCrossings swap L U X,(μ n:ℝ)| ≤ cost

private def cappedTable (j : ℕ) : CappedTable j := Classical.choice (by
  obtain ⟨F,hF,hcnt,C,_,hC⟩ := dense_short_table_with_bounded_signed_walls (by positivity : 0<tol j)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hcnt
  exact ⟨⟨F,N,C,fun n h => ⟨(hF n h).1,(hF n h).2.1⟩,fun n h => (hF n h).2.2,hN,hC⟩⟩)

private def onsetFor (w : ℕ → ℝ) (top : Tendsto w atTop atTop) (j : ℕ) : ℕ :=
  max (cappedTable j).onset ((eventually_atTop.mp (top.eventually_ge_atTop (cappedTable j).cost)).choose)

private def chargeWalls (N : ℕ → ℕ) : ℕ → ℕ
  | 0 => N 0+1
  | j+1 => max ((j+2)*chargeWalls N j) (N (j+1))+1

private theorem onset_le_wall (N : ℕ → ℕ) (j : ℕ) : N j ≤ chargeWalls N j := by
  cases j with
  | zero => exact Nat.le_succ _
  | succ j => exact (le_max_right ..).trans (Nat.le_succ _)

/-- One global matching moves all but a density-zero subset of the
squarefree vertices, with sublinear displacement. The signed part from
all its moving vertices is bounded at every sharp cutoff by any
prescribed nonnegative function tending to infinity. -/
theorem arbitrarily_slow_signed_crossings (w : ℕ → ℝ) (positive : ∀ n,0 ≤ w n)
    (top : Tendsto w atTop atTop) :
    ∃ G : ℕ → ℕ,(∀ n,G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n))) ∧
      (∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,((prefixUnpaid G X).card:ℝ) ≤ ε*X ∧ |(G X:ℝ)-X| ≤ ε*X) ∧
      ∀ X,|crossingSignedPrefix G X| ≤ w X ∧ |coprimeMoebiusSum 1 X-fixedSignedPrefix G X| ≤ w X := by
  classical
  let N := onsetFor w top
  let L := chargeWalls N
  let F := fun j => (cappedTable j).swap
  let H := blockSwitch L F
  let G := fun n : ℕ => if Squarefree n then H n else n
  have space (j : ℕ) : (j+2)*L j<L (j+1) := Nat.lt_succ_of_le (le_max_left ..)
  have strict : StrictMono L := strictMono_nat_of_lt_succ
    (fun j => (Nat.le_mul_of_pos_left _ (by omega : 0<j+2)).trans_lt (space j))
  have law := fun j => (cappedTable j).law
  have hH := block_law strict.monotone law
  have hg {n : ℕ} (hs : Squarefree n) : G n=H n := if_pos hs
  have hlay (n : ℕ) : G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n)) := by
    by_cases hs : Squarefree n
    · obtain ⟨back,edge⟩ := hH n hs
      have moved : Squarefree (H n) := by
        rcases edge with fixed | rel
        · change H n=n at fixed
          rwa [fixed]
        · exact rel.2.1
      simpa only [hg hs,hg moved] using And.intro back edge
    · simp [G,hs]
  have population (X : ℕ) : prefixUnpaid G X=prefixUnpaid H X := by
    ext n
    simp only [prefixUnpaid,mem_filter]
    exact and_congr_right (fun h => by rw [hg (mem_filter.mp h).2])
  have fixed (X : ℕ) : fixedSignedPrefix G X=fixedSignedPrefix H X := by
    unfold fixedSignedPrefix
    congr 1
    ext n
    simp only [mem_filter]
    exact and_congr_right (fun h => by rw [hg (mem_filter.mp h).2])
  have cfg := dense_blocks_of_spaced_walls L F strict space law
    (fun j n hn => (cappedTable j).count n ((le_max_left ..).trans ((onset_le_wall N j).trans hn)))
    (fun j => (cappedTable j).near)
  refine ⟨G,hlay,?_,?_⟩
  · intro ε hε
    filter_upwards [cfg ε hε] with X h
    rw [population]
    refine ⟨h.1,?_⟩
    by_cases hs : Squarefree X
    · rw [hg hs]; exact h.2 hs
    · simp [G,hs,mul_nonneg hε.le (Nat.cast_nonneg X)]
  intro X
  have base : |crossingSignedPrefix H X| ≤ w X := by
    by_cases hi : L 0<X
    · obtain ⟨j,_,hx⟩ := block_above strict hi
      rw [crossingSignedPrefix,block_crossings strict.monotone F hx]
      apply ((cappedTable j).signed _ _ _).trans
      have ht := (eventually_atTop.mp (top.eventually_ge_atTop (cappedTable j).cost)).choose_spec
      apply ht
      exact (le_max_right ..).trans ((onset_le_wall N j).trans hx.1.le)
    · have no (n : ℕ) (hn : n ≤ X) : H n=n := by
        apply dif_neg
        rintro ⟨j,hj⟩
        exact hi ((strict.monotone (Nat.zero_le j)).trans_lt (hj.1.trans_le hn))
      have hem : (Icc 1 X).filter (fun n => X<H n)=∅ := filter_eq_empty_iff.mpr (fun n hn => by
        rw [no n (mem_Icc.mp hn).2]; exact (mem_Icc.mp hn).2.not_gt)
      simpa only [crossingSignedPrefix,hem,sum_empty,abs_zero] using positive X
  have gsum := fixed_add_crossing G (fun n _ => hlay n) X
  have hsum := fixed_add_crossing H hH X
  rw [fixed] at gsum
  have eq : crossingSignedPrefix G X=crossingSignedPrefix H X := by linarith only [gsum,hsum]
  have dif : coprimeMoebiusSum 1 X-fixedSignedPrefix G X=crossingSignedPrefix H X := by
    rw [fixed]; linarith only [hsum]
  rw [eq,dif]; exact ⟨base,base⟩

/-- The fixed set of one sublinearly short matching has density zero and
the same power bounds as the full prefix, including every positive
endpoint. Their pointwise difference is at most log(X+1). -/
theorem one_density_zero_fixed_set_with_logarithmic_pointwise_error :
    ∃ G : ℕ → ℕ,(∀ n,G (G n)=n ∧ (G n=n ∨ GlobalDyadicOneTwoRel n (G n))) ∧
      (∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,((prefixUnpaid G X).card:ℝ) ≤ ε*X ∧ |(G X:ℝ)-X| ≤ ε*X) ∧
      (∀ X,|coprimeMoebiusSum 1 X-fixedSignedPrefix G X| ≤ Real.log ((X:ℝ)+1)) ∧
      ∀ s : ℝ,0<s → (PrefixPower s (fixedSignedPrefix G) ↔ PrefixPower s (coprimeMoebiusSum 1)) := by
  let w := fun X : ℕ => Real.log ((X:ℝ)+1)
  have pos (X : ℕ) : 0 ≤ w X := Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg X))
  have grow : Tendsto w atTop atTop := by
    apply Real.tendsto_log_atTop.comp
    exact tendsto_atTop_mono (show ∀ n : ℕ,(n:ℝ) ≤ n+1 by intro n; linarith) tendsto_natCast_atTop_atTop
  obtain ⟨G,hG,pop,hw⟩ := arbitrarily_slow_signed_crossings w pos grow
  refine ⟨G,hG,pop,fun X => (hw X).2,?_⟩
  intro s hs
  let K := (2:ℝ)^s/s
  have hK : 0 ≤ K := by positivity
  have cap (X : ℕ) : w X ≤ K*(X:ℝ)^s := by
    by_cases z : X=0
    · simp [w,z,Real.zero_rpow hs.ne']
    have hX : (1:ℝ) ≤ X := by exact_mod_cast Nat.pos_of_ne_zero z
    have h := Real.log_le_rpow_div (by positivity : (0:ℝ) ≤ X+1) hs
    have hpow := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ X+1) (by linarith only [hX] : (X:ℝ)+1 ≤ 2*X) hs.le
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Nat.cast_nonneg _)] at hpow
    exact h.trans ((div_le_div_of_nonneg_right hpow hs.le).trans_eq (by dsimp only [K]; ring))
  constructor <;> rintro ⟨C,hC,h⟩ <;> refine ⟨C+K,add_nonneg hC hK,fun X => ?_⟩
  · have tri := abs_add_le (fixedSignedPrefix G X) (coprimeMoebiusSum 1 X-fixedSignedPrefix G X)
    rw [show fixedSignedPrefix G X+(coprimeMoebiusSum 1 X-fixedSignedPrefix G X)=
      coprimeMoebiusSum 1 X by ring] at tri
    exact tri.trans ((add_le_add (h X) ((hw X).2.trans (cap X))).trans_eq (add_mul ..).symm)
  · have tri := abs_sub (coprimeMoebiusSum 1 X) (coprimeMoebiusSum 1 X-fixedSignedPrefix G X)
    rw [sub_sub_cancel] at tri
    exact tri.trans ((add_le_add (h X) ((hw X).2.trans (cap X))).trans_eq (add_mul ..).symm)

#print axioms arbitrarily_slow_signed_crossings
#print axioms one_density_zero_fixed_set_with_logarithmic_pointwise_error

end GaloisForLFunctions.RestrictedFactorizationCalculus
