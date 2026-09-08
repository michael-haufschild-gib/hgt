import GaloisForLFunctions.RHTower.MobiusDivisorCoareaMassSplit

/-!
# Every complete one-prime order crosses a superquadratic coarea barrier

A bounded-increment sequence crossing half its total mass has an endpoint
within half a jump of the crossing. Applied to consumed late-prime mass,
this gives a prefix head action at least `(T²-(9/25)M)/4`. Since the actual
late mass satisfies `T(4N)/(4N) → ∞`, no complete insertion order can keep
head action uniformly quadratic. The statement quantifies over all orders
and permits arbitrary interleaving, repeated indices, and nonprime indices.
-/
noncomputable section
set_option autoImplicit false
open Finset Filter Topology
namespace RHTower

/-- A bounded jump across half the total mass gives a sharp product lower bound at a prefix. -/
theorem exists_prefix_mass_product_ge (x : ℕ → ℝ) (T D : ℝ) (k : ℕ)
    (hT : 0 ≤ T) (_hD : 0 ≤ D) (h0 : x 0=0) (hk : x k=T)
    (hstep : ∀ n<k, x (n+1)-x n ≤ D) :
    ∃ n≤k, (T^2-D^2)/4 ≤ x n*(T-x n) := by
  by_cases hT0 : T=0
  · refine ⟨0,Nat.zero_le _,?_⟩
    rw [h0,hT0]
    nlinarith only [sq_nonneg D]
  have hTp : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
  have hex : ∃ n, T/2 ≤ x n := ⟨k,by rw [hk]; linarith⟩
  let j := Nat.find hex
  have hj : T/2 ≤ x j := Nat.find_spec hex
  have hjk : j ≤ k := Nat.find_min' hex (by rw [hk]; linarith)
  have hj0 : j ≠ 0 := by intro he; rw [he,h0] at hj; linarith
  have hlo : x (j-1) < T/2 := lt_of_not_ge (Nat.find_min hex (by omega : j-1<j))
  have hinc := hstep (j-1) (by omega)
  have he : j-1+1=j := by omega
  rw [he] at hinc
  by_cases hnear : T/2-x (j-1) ≤ D/2
  · refine ⟨j-1,by omega,?_⟩
    have ha : 0 ≤ x (j-1)-(T-D)/2 := by linarith
    have hb : 0 ≤ (T+D)/2-x (j-1) := by linarith
    nlinarith only [mul_nonneg ha hb]
  · refine ⟨j,hjk,?_⟩
    have ha : 0 ≤ x j-(T-D)/2 := by linarith
    have hb : 0 ≤ (T+D)/2-x j := by linarith
    nlinarith only [mul_nonneg ha hb]

/-- Every complete insertion chain has the same arithmetic late-mass coarea barrier. -/
theorem exists_mobiusDivisorCoareaHeadAction_prefix_ge (M k : ℕ)
    (P : ℕ → Finset ℕ) (q : ℕ → ℕ)
    (h0 : Disjoint (mobiusDivisorActiveLatePrimes M) (P 0))
    (hk : mobiusDivisorActiveLatePrimes M ⊆ P k)
    (hstep : ∀ n<k, P (n+1)=insert (q n) (P n)) :
    ∃ n≤k, ((mobiusDivisorLatePrimeMass M)^2-(9/25:ℝ)*M)/4 ≤
      mobiusDivisorCoareaHeadAction M (P n) := by
  have hx0 : mobiusDivisorConsumedLateMass M (P 0)=0 := by
    simp [mobiusDivisorConsumedLateMass,Finset.disjoint_iff_inter_eq_empty.mp h0]
  have hxk : mobiusDivisorConsumedLateMass M (P k)=mobiusDivisorLatePrimeMass M := by
    have hr : mobiusDivisorRemainingLateMass M (P k)=0 := by
      simp [mobiusDivisorRemainingLateMass,sdiff_eq_empty_iff_subset.mpr hk]
    simpa only [hr,add_zero] using mobiusDivisorConsumed_add_remainingLateMass M (P k)
  have hT : 0 ≤ mobiusDivisorLatePrimeMass M := by
    rw [← sum_mobiusDivisorActiveLatePrimes]
    exact sum_nonneg (fun p _ => divisorUnsignedDilationChannel_nonneg M p)
  obtain ⟨n,hn,hb⟩ := exists_prefix_mass_product_ge
    (fun n => mobiusDivisorConsumedLateMass M (P n))
    (mobiusDivisorLatePrimeMass M) ((3/5:ℝ)*Real.sqrt M) k hT (by positivity) hx0 hxk
    (fun n hn => by rw [hstep n hn]; exact mobiusDivisorConsumedLateMass_insert_step_le M (P n) (q n))
  have hsplit := mobiusDivisorCoareaHeadAction_ge_late_mass_split M (P n)
  have hsum := mobiusDivisorConsumed_add_remainingLateMass M (P n)
  have hs : ((3/5:ℝ)*Real.sqrt M)^2 = (9/25:ℝ)*M := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg M)]
    ring
  rw [hs] at hb
  refine ⟨n,hn,?_⟩
  rw [← hsum,add_sub_cancel_left] at hb
  simpa only [hsum] using hb.trans hsplit

/-- Uniform quadratic head-coarea control fails for every complete prime order, unconditionally. -/
theorem eventually_every_mobiusDivisorCoarea_order_exceeds_quadratic (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ (k : ℕ) (P : ℕ → Finset ℕ) (q : ℕ → ℕ),
      Disjoint (mobiusDivisorActiveLatePrimes (4*N)) (P 0) →
      mobiusDivisorActiveLatePrimes (4*N) ⊆ P k →
      (∀ n<k, P (n+1)=insert (q n) (P n)) →
      ∃ n≤k, C*(4*(N:ℝ))^2 < mobiusDivisorCoareaHeadAction (4*N) (P n) := by
  have hT := tendsto_mobiusDivisorLatePrimeMass_div_atTop.eventually_gt_atTop (2*(|C|+1))
  filter_upwards [hT,eventually_ge_atTop (1:ℕ)] with N hT hN
  intro k P q h0 hk hstep
  obtain ⟨n,hn,hb⟩ := exists_mobiusDivisorCoareaHeadAction_prefix_ge (4*N) k P q h0 hk hstep
  have hM : (1:ℝ) ≤ 4*N := by exact_mod_cast (show 1≤4*N by omega)
  have hMp : (0:ℝ) < 4*N := by linarith
  have hlarge := (lt_div_iff₀ hMp).mp hT
  have hpos : 0 ≤ 2*(|C|+1)*(4*(N:ℝ)) := by positivity
  have hsq : (2*(|C|+1)*(4*(N:ℝ)))^2 < (mobiusDivisorLatePrimeMass (4*N))^2 := by
    nlinarith only [hlarge,hpos]
  have hc : 4*C+1 ≤ (2*(|C|+1))^2 := by nlinarith [le_abs_self C,sq_nonneg |C|]
  have hcM := mul_le_mul_of_nonneg_right hc (sq_nonneg (4*(N:ℝ)))
  have hlin : (9/25:ℝ)*(4*N) ≤ (4*(N:ℝ))^2 := by nlinarith only [hM]
  push_cast at hb
  refine ⟨n,hn,?_⟩
  nlinarith only [hb,hsq,hcM,hlin]

end RHTower
