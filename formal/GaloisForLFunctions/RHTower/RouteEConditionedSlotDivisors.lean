import GaloisForLFunctions.RHTower.RouteEHistogramMixedOrientationMass
import Mathlib.Data.Nat.Dist

/-!
# Integer divisors of conditioned singleton receivers

Inactive factors divide every receiver pair avoiding their unique active slot.
The exact ordered-pair product therefore forces A^(q-2) <= W^q for q distinct
receiver integers inside a window of width W. This law applies to a single
literal history and survives arbitrary conditioning.

A fixed source bound b_i <= a_i^K and sufficiently many slots force the
inactive baseline from the conserved histogram product. The actual growing
window then excludes five distinct receivers, without a baseline-limit
premise, independence, or coprimality. The statement restricts physical
support; it does not establish a signed Möbius covariance bound.
-/

open Finset Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower.IntegerCubeAperture

variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]

def inactivePairProduct (a : C → ℕ) (h : S → C → Bool) (r s : S) : ℕ :=
  ∏ i, if h r i = false ∧ h s i = false then a i else 1

omit [DecidableEq C] [Fintype S] [DecidableEq S] in
theorem inactivePairProduct_dvd_left (a b : C → ℕ) (h : S → C → Bool) (r s : S) :
    inactivePairProduct a h r s ∣ boolCorner (fun i z => if z then b i else a i) (h r) := by
  unfold inactivePairProduct boolCorner
  apply prod_dvd_prod_of_dvd
  intro i hi
  cases h r i <;> cases h s i <;> simp

omit [DecidableEq C] [Fintype S] [DecidableEq S] in
theorem inactivePairProduct_dvd_right (a b : C → ℕ) (h : S → C → Bool) (r s : S) :
    inactivePairProduct a h r s ∣ boolCorner (fun i z => if z then b i else a i) (h s) := by
  unfold inactivePairProduct boolCorner
  apply prod_dvd_prod_of_dvd
  intro i hi
  cases h r i <;> cases h s i <;> simp

theorem common_divisor_le_width (a x y : ℕ) (L W : ℝ)
    (hax : a ∣ x) (hay : a ∣ y) (hxy : x ≠ y)
    (hx : (x:ℝ) ∈ Set.Icc L (L+W)) (hy : (y:ℝ) ∈ Set.Icc L (L+W)) :
    (a:ℝ) ≤ W := by
  have hdiv : a ∣ Nat.dist x y := by
    unfold Nat.dist
    exact dvd_add (Nat.dvd_sub hax hay) (Nat.dvd_sub hay hax)
  have hle : (a:ℝ) ≤ (Nat.dist x y:ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.dist_pos_of_ne hxy) hdiv
  apply hle.trans
  rcases le_total x y with he | he
  · rw [Nat.dist_eq_sub_of_le he,Nat.cast_sub he]
    linarith [hx.1,hy.2]
  · rw [Nat.dist_eq_sub_of_le_right he,Nat.cast_sub he]
    linarith [hy.1,hx.2]

omit [Fintype C] [DecidableEq C] in
theorem inactive_slot_card_lower (h : S → C → Bool)
    (hsingle : ∀ i r s, h r i = true → h s i = true → r = s) (i : C) :
    Fintype.card S-1 ≤ (univ.filter fun r => h r i = false).card := by
  have hone : (univ.filter fun r => h r i = true).card ≤ 1 := by
    apply card_le_one.mpr
    intro r hr s hs
    exact hsingle i r s (mem_filter.mp hr).2 (mem_filter.mp hs).2
  have he : (univ.filter fun r => h r i = false) = (univ.filter fun r => h r i = true)ᶜ := by
    ext r
    cases hr : h r i <;> simp [hr]
  rw [he,card_compl]
  omega

omit [DecidableEq C] [DecidableEq S] in
/-- Exact product of the common inactive divisors over ordered distinct pairs. -/
theorem prod_inactivePairProduct (a : C → ℕ) (h : S → C → Bool) :
    ∏ rs ∈ (univ : Finset S).offDiag, inactivePairProduct a h rs.1 rs.2 =
      ∏ i, a i ^ ((univ.filter fun r => h r i = false).card *
        ((univ.filter fun r => h r i = false).card-1)) := by
  simp only [inactivePairProduct]
  rw [Finset.prod_comm]
  apply prod_congr rfl
  intro i hi
  have he : (univ : Finset S).offDiag.filter
      (fun rs => h rs.1 i = false ∧ h rs.2 i = false) =
      (univ.filter fun r => h r i = false).offDiag := by
    ext rs
    simp only [mem_filter,mem_offDiag,mem_univ,true_and]
    tauto
  rw [← prod_filter,he,prod_const,offDiag_card]
  congr 1
  simp only [Nat.mul_sub_left_distrib,Nat.mul_one]

omit [DecidableEq C] in
/-- The singleton incidence forces a power of the entire inactive baseline. -/
theorem baseline_pow_le_pairProduct (a : C → ℕ) (h : S → C → Bool)
    (ha : ∀ i, 1 ≤ a i)
    (hsingle : ∀ i r s, h r i = true → h s i = true → r = s) :
    (∏ i, a i)^((Fintype.card S-1)*(Fintype.card S-2)) ≤
      ∏ rs ∈ (univ : Finset S).offDiag, inactivePairProduct a h rs.1 rs.2 := by
  rw [prod_inactivePairProduct,← prod_pow]
  apply Finset.prod_le_prod
  · intros; exact Nat.zero_le _
  · intro i hi
    apply pow_le_pow_right₀ (ha i)
    have hf := inactive_slot_card_lower h hsingle i
    exact Nat.mul_le_mul hf (by omega)

omit [DecidableEq C] [DecidableEq S] in
/-- Distinct physical receivers bound every pair divisor by the original aperture. -/
theorem pairProduct_le_width_pow (a b : C → ℕ) (h : S → C → Bool) (L W : ℝ)
    (hinj : Function.Injective (fun r => boolCorner (fun i z => if z then b i else a i) (h r)))
    (hwindow : ∀ r, (boolCorner (fun i z => if z then b i else a i) (h r) : ℝ) ∈
      Set.Icc L (L+W)) :
    (∏ rs ∈ (univ : Finset S).offDiag, (inactivePairProduct a h rs.1 rs.2 : ℝ)) ≤
      W^(Fintype.card S*(Fintype.card S-1)) := by
  calc
    _ ≤ ∏ _rs ∈ (univ : Finset S).offDiag, W := by
      apply Finset.prod_le_prod
      · intros; positivity
      · intro rs hrs
        exact common_divisor_le_width _ _ _ L W
          (inactivePairProduct_dvd_left a b h rs.1 rs.2)
          (inactivePairProduct_dvd_right a b h rs.1 rs.2)
          (fun he => (mem_offDiag.mp hrs).2.2 (hinj he))
          (hwindow rs.1) (hwindow rs.2)
    _ = _ := by rw [prod_const,offDiag_card,card_univ]; simp only [Nat.mul_sub_left_distrib,Nat.mul_one]

omit [DecidableEq C] in
/-- Integer receiver support forces a quantitative bound on the entire inactive baseline. -/
theorem baseline_pow_le_width_pow (a b : C → ℕ) (h : S → C → Bool) (L W : ℝ)
    (hq : 2 ≤ Fintype.card S) (ha : ∀ i, 1 ≤ a i) (hW : 0 ≤ W)
    (hsingle : ∀ i r s, h r i = true → h s i = true → r = s)
    (hinj : Function.Injective (fun r => boolCorner (fun i z => if z then b i else a i) (h r)))
    (hwindow : ∀ r, (boolCorner (fun i z => if z then b i else a i) (h r) : ℝ) ∈
      Set.Icc L (L+W)) :
    ((∏ i, a i : ℕ) : ℝ)^(Fintype.card S-2) ≤ W^Fintype.card S := by
  have hbase : ((∏ i, a i : ℕ) : ℝ)^((Fintype.card S-1)*(Fintype.card S-2)) ≤
      ∏ rs ∈ (univ : Finset S).offDiag, (inactivePairProduct a h rs.1 rs.2 : ℝ) := by
    exact_mod_cast baseline_pow_le_pairProduct a h ha hsingle
  have htop := hbase.trans (pairProduct_le_width_pow a b h L W hinj hwindow)
  have hp : (((∏ i, a i : ℕ) : ℝ)^(Fintype.card S-2))^(Fintype.card S-1) ≤
      (W^Fintype.card S)^(Fintype.card S-1) := by
    simpa only [← pow_mul,Nat.mul_comm] using htop
  exact (pow_le_pow_iff_left₀ (by positivity) (pow_nonneg hW _) (by omega)).mp hp

/-- The support bound applies to selected distinct receivers of one literal singleton history. -/
theorem singleton_history_selected_baseline_bound
    (m q : ℕ) (k : C → Bool → ℕ) (a b : C → ℕ)
    (history : RouteEComponentHistory (fun _ : C => Bool) m)
    (e : Fin q → Fin m) (he : Function.Injective e)
    (hmem : history ∈ routeEComponentHistogramCell (fun _ : C => Bool) m k)
    (hone : ∀ i, k i true = 1) (hq : 2 ≤ q) (ha : ∀ i, 1 ≤ a i)
    (L W : ℝ) (hW : 0 ≤ W)
    (hinj : Function.Injective (fun r => routeEComponentSlotReceiver (fun _ : C => Bool)
      (fun i z => if z then (b i:ℝ) else (a i:ℝ)) history (e r)))
    (hwindow : ∀ r, routeEComponentSlotReceiver (fun _ : C => Bool)
      (fun i z => if z then (b i:ℝ) else (a i:ℝ)) history (e r) ∈ Set.Icc L (L+W)) :
    ((∏ i, a i : ℕ) : ℝ)^(q-2) ≤ W^q := by
  have hsingle : ∀ i r s, history (e r) i = true → history (e s) i = true → r = s := by
    intro i r s hr hs
    apply he
    have hhist := (mem_filter.mp hmem).2 i
    have hcount : (univ.filter fun t => history t i = true).card = 1 := by
      simpa only [GaloisForLFunctions.HTGeometry.tupleHistogram,hone i] using congrFun hhist true
    have hle : (univ.filter fun t => history t i = true).card ≤ 1 := by omega
    exact (card_le_one.mp hle) (e r) (mem_filter.mpr ⟨mem_univ _,hr⟩)
      (e s) (mem_filter.mpr ⟨mem_univ _,hs⟩)
  have hreceiver (r : Fin q) :
      (boolCorner (fun i z => if z then b i else a i) (history (e r)) : ℝ) =
      routeEComponentSlotReceiver (fun _ : C => Bool)
        (fun i z => if z then (b i:ℝ) else (a i:ℝ)) history (e r) := by
    unfold boolCorner routeEComponentSlotReceiver
    push_cast
    apply prod_congr rfl
    intro i hi
    cases history (e r) i <;> rfl
  simpa only [Fintype.card_fin] using baseline_pow_le_width_pow a b
    (fun r => history (e r)) L W (by simpa using hq) ha hW hsingle
    (by intro r s hrs; apply hinj; dsimp; rw [← hreceiver r,← hreceiver s]
        exact congrArg (fun n : ℕ => (n:ℝ)) hrs)
    (by intro r; rw [hreceiver]; exact hwindow r)

theorem tendsto_log_twice_growing_window (X : ℕ → ℝ) (hX : Tendsto X atTop atTop) :
    Tendsto (fun n => Real.log (2*Sieve.growingReciprocalMarkerWindow (X n))/Real.log (X n))
      atTop (𝓝 ((1:ℝ)/2)) := by
  have hc := (tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hX)).const_mul (Real.log 2)
  have hw := Sieve.tendsto_log_growingReciprocalMarkerWindow_div_log_half.comp hX
  have ht := hc.add hw
  simp only [mul_zero,zero_add] at ht
  refine ht.congr' ?_
  filter_upwards [hX.eventually (eventually_gt_atTop (0:ℝ))] with n hn
  have hp : 0 < Sieve.growingReciprocalMarkerWindow (X n) :=
    mul_pos (Real.sqrt_pos.mpr hn) (Sieve.growingReciprocalMarkerH_pos (X n))
  dsimp only [Function.comp_apply]
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hp.ne']
  ring

/-- A baseline on the full receiver logarithmic scale cannot support five distinct slots. -/
theorem eventually_growing_window_five_receiver_gap (A X : ℕ → ℝ)
    (hA : ∀ n, 0 < A n) (hX : Tendsto X atTop atTop)
    (hscale : Tendsto (fun n => Real.log (A n)/Real.log (X n)) atTop (𝓝 1)) :
    ∀ᶠ n in atTop, (2*Sieve.growingReciprocalMarkerWindow (X n))^(5 : ℕ) < (A n)^(3 : ℕ) := by
  have ht := (hscale.const_mul (3:ℝ)).sub ((tendsto_log_twice_growing_window X hX).const_mul (5:ℝ))
  have hpositive := ht.eventually (Ioi_mem_nhds (show (0:ℝ) < 3*1-5*(1/2) by norm_num))
  filter_upwards [hpositive,hX.eventually (eventually_gt_atTop (1:ℝ))] with n hn hxn
  have hp : 0 < Sieve.growingReciprocalMarkerWindow (X n) :=
    mul_pos (Real.sqrt_pos.mpr (by linarith)) (Sieve.growingReciprocalMarkerH_pos (X n))
  have hl : 0 < Real.log (X n) := Real.log_pos hxn
  have hquot : 0 < (3*Real.log (A n)-5*Real.log (2*Sieve.growingReciprocalMarkerWindow (X n)))/
      Real.log (X n) := by
    have he : (3*Real.log (A n)-5*Real.log (2*Sieve.growingReciprocalMarkerWindow (X n)))/
        Real.log (X n) = 3*(Real.log (A n)/Real.log (X n))-
          5*(Real.log (2*Sieve.growingReciprocalMarkerWindow (X n))/Real.log (X n)) := by ring
    rw [he]
    exact hn
  have hnum : 0 < 3*Real.log (A n)-5*Real.log (2*Sieve.growingReciprocalMarkerWindow (X n)) :=
    (div_pos_iff.mp hquot).resolve_right (by intro h; linarith [h.2]) |>.1
  apply (Real.log_lt_log_iff (by positivity) (pow_pos (hA n) _)).mp
  rw [Real.log_pow,Real.log_pow]
  norm_num
  linarith

/-- Arbitrary conditioning cannot restore five distinct receivers when the inactive baseline
stays on the full physical logarithmic scale. -/
theorem eventually_singleton_no_five_distinct_receivers
    (d m : ℕ → ℕ) (k : ∀ n, Fin (d n) → Bool → ℕ)
    (a b : ∀ n, Fin (d n) → ℕ) (X : ℕ → ℝ)
    (ha : ∀ n i, 1 ≤ a n i) (hone : ∀ n i, k n i true = 1)
    (hX : Tendsto X atTop atTop)
    (hscale : Tendsto (fun n => Real.log ((∏ i, a n i : ℕ) : ℝ)/Real.log (X n))
      atTop (𝓝 1)) :
    ∀ᶠ n in atTop, ∀ history ∈ routeEComponentHistogramCell (fun _ : Fin (d n) => Bool) (m n) (k n),
      ∀ e : Fin 5 → Fin (m n),
        (∀ r, routeEComponentSlotReceiver (fun _ : Fin (d n) => Bool)
          (fun i z => if z then (b n i:ℝ) else (a n i:ℝ)) history (e r) ∈
            Set.Icc (X n-Sieve.growingReciprocalMarkerWindow (X n))
              (X n+Sieve.growingReciprocalMarkerWindow (X n))) →
        ¬ Function.Injective (fun r => routeEComponentSlotReceiver (fun _ : Fin (d n) => Bool)
          (fun i z => if z then (b n i:ℝ) else (a n i:ℝ)) history (e r)) := by
  have hA (n : ℕ) : (0:ℝ) < ((∏ i, a n i : ℕ) : ℝ) := by
    exact_mod_cast (Finset.prod_pos fun i _ => ha n i)
  have hgap := eventually_growing_window_five_receiver_gap _ X hA hX hscale
  filter_upwards [hgap,hX.eventually growing_window_aperture] with n hn hw
  intro history hmem e hwindow hinj
  have he : Function.Injective e := by
    intro r s hrs
    apply hinj
    dsimp
    rw [hrs]
  have hbound := singleton_history_selected_baseline_bound (m n) 5 (k n) (a n) (b n)
    history e he hmem (hone n) (by norm_num) (ha n)
    (X n-Sieve.growingReciprocalMarkerWindow (X n))
    (2*Sieve.growingReciprocalMarkerWindow (X n)) (by linarith [hw.1]) hinj
    (by intro r
        have he : X n-Sieve.growingReciprocalMarkerWindow (X n)+
            2*Sieve.growingReciprocalMarkerWindow (X n) =
            X n+Sieve.growingReciprocalMarkerWindow (X n) := by ring
        simpa only [he] using hwindow r)
  norm_num at hbound
  exact (not_le_of_gt hn) (by simpa only [Nat.cast_prod] using hbound)

/-- The exact multiplicative source conserved by a literal singleton history. -/
theorem singleton_history_receiver_product (m : ℕ) (k : C → Bool → ℕ) (a b : C → ℕ)
    (history : RouteEComponentHistory (fun _ : C => Bool) m)
    (hmem : history ∈ routeEComponentHistogramCell (fun _ : C => Bool) m k)
    (hone : ∀ i, k i true = 1) :
    (∏ r, routeEComponentSlotReceiver (fun _ : C => Bool)
      (fun i z => if z then (b i:ℝ) else (a i:ℝ)) history r) =
      ((∏ i, a i : ℕ) : ℝ)^(m-1)*((∏ i, b i : ℕ) : ℝ) := by
  have hhist (i : C) := (mem_filter.mp hmem).2 i
  have hfalse (i : C) : k i false = m-1 := by
    have ht := GaloisForLFunctions.HTGeometry.sum_tupleHistogram (fun r => history r i)
    rw [hhist i] at ht
    simp only [Fintype.sum_bool,hone i] at ht
    omega
  rw [routeE_componentSlotReceiver_product_eq_histogram]
  have hcomponent (i : C) :
      (∏ z : Bool, (if z then (b i:ℝ) else (a i:ℝ))^
        GaloisForLFunctions.HTGeometry.tupleHistogram (fun r => history r i) z) =
      (a i:ℝ)^(m-1)*(b i:ℝ) := by
    simp [hhist i,hfalse i,hone i,mul_comm]
  simp only [hcomponent,Finset.prod_mul_distrib,Finset.prod_pow,Nat.cast_prod]

/-- A fixed activation power bound forces a large inactive baseline from the original products. -/
theorem singleton_history_baseline_tenth_power (m K : ℕ) (k : C → Bool → ℕ) (a b : C → ℕ)
    (history : RouteEComponentHistory (fun _ : C => Bool) m)
    (hmem : history ∈ routeEComponentHistogramCell (fun _ : C => Bool) m k)
    (hone : ∀ i, k i true = 1) (ha : ∀ i, 1 ≤ a i)
    (hactivation : ∀ i, b i ≤ a i^K) (hm : 10*(K+1) ≤ m)
    (L : ℝ) (hL : 0 ≤ L)
    (hlower : ∀ r, L ≤ routeEComponentSlotReceiver (fun _ : C => Bool)
      (fun i z => if z then (b i:ℝ) else (a i:ℝ)) history r) :
    L^(10 : ℕ) ≤ ((∏ i, a i : ℕ) : ℝ)^(11 : ℕ) := by
  let A : ℝ := ((∏ i, a i : ℕ) : ℝ)
  have hA : 1 ≤ A := by
    dsimp [A]
    exact_mod_cast Nat.succ_le_of_lt (Finset.prod_pos fun i _ => ha i)
  have hB : ((∏ i, b i : ℕ) : ℝ) ≤ A^K := by
    have hn : (∏ i, b i) ≤ (∏ i, a i)^K := by
      rw [← prod_pow]
      exact Finset.prod_le_prod (by intros; exact Nat.zero_le _) (fun i _ => hactivation i)
    dsimp [A]
    exact_mod_cast hn
  have hwhole : L^m ≤ A^(m-1+K) := by
    calc
      L^m = ∏ _r : Fin m, L := by simp
      _ ≤ ∏ r, routeEComponentSlotReceiver (fun _ : C => Bool)
          (fun i z => if z then (b i:ℝ) else (a i:ℝ)) history r :=
        Finset.prod_le_prod (fun _ _ => hL) (fun r _ => hlower r)
      _ = A^(m-1)*((∏ i, b i : ℕ) : ℝ) :=
        singleton_history_receiver_product m k a b history hmem hone
      _ ≤ A^(m-1)*A^K := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = A^(m-1+K) := (pow_add _ _ _).symm
  have hraised := pow_le_pow_left₀ (pow_nonneg hL _) hwhole 10
  have hexp : (m-1+K)*10 ≤ 11*m := by omega
  have ht : (L^(10 : ℕ))^m ≤ (A^(11 : ℕ))^m := by
    calc
      (L^(10 : ℕ))^m = (L^m)^(10 : ℕ) := by rw [← pow_mul,← pow_mul]; congr 1; omega
      _ ≤ (A^(m-1+K))^(10 : ℕ) := hraised
      _ ≤ (A^(11 : ℕ))^m := by
        rw [← pow_mul,← pow_mul]
        exact pow_le_pow_right₀ hA hexp
  exact (pow_le_pow_iff_left₀ (pow_nonneg hL _) (by positivity) (by omega)).mp ht

/-- Arbitrarily conditioned singleton histories with bounded activation powers have small
physical support when the aperture obeys the displayed source inequality. -/
theorem singleton_history_no_five_of_power_activation
    (m K : ℕ) (k : C → Bool → ℕ) (a b : C → ℕ)
    (history : RouteEComponentHistory (fun _ : C => Bool) m)
    (hmem : history ∈ routeEComponentHistogramCell (fun _ : C => Bool) m k)
    (hone : ∀ i, k i true = 1) (ha : ∀ i, 1 ≤ a i)
    (hactivation : ∀ i, b i ≤ a i^K) (hm : 10*(K+1) ≤ m)
    (L W : ℝ) (hL : 0 ≤ L) (hW : 0 ≤ W) (hgap : W^(55 : ℕ) < L^(30 : ℕ))
    (hwindow : ∀ r, routeEComponentSlotReceiver (fun _ : C => Bool)
      (fun i z => if z then (b i:ℝ) else (a i:ℝ)) history r ∈ Set.Icc L (L+W))
    (e : Fin 5 → Fin m) :
    ¬ Function.Injective (fun r => routeEComponentSlotReceiver (fun _ : C => Bool)
      (fun i z => if z then (b i:ℝ) else (a i:ℝ)) history (e r)) := by
  intro hinj
  have he : Function.Injective e := by
    intro r s hrs
    apply hinj
    dsimp
    rw [hrs]
  have hbase := singleton_history_baseline_tenth_power m K k a b history hmem hone ha
    hactivation hm L hL (fun r => (hwindow r).1)
  have hwidth := singleton_history_selected_baseline_bound m 5 k a b history e he hmem hone
    (by norm_num) ha L W hW hinj (fun r => hwindow (e r))
  norm_num only at hwidth
  have ht1 := pow_le_pow_left₀ (pow_nonneg hL 10) hbase 3
  have ht2 := pow_le_pow_left₀ (by positivity) hwidth 11
  have hbad : L^(30 : ℕ) ≤ W^(55 : ℕ) := by
    calc
      L^(30 : ℕ) = (L^(10 : ℕ))^(3 : ℕ) := by ring
      _ ≤ (((∏ i, a i : ℕ) : ℝ)^(11 : ℕ))^(3 : ℕ) := ht1
      _ = (((∏ i, a i : ℕ) : ℝ)^(3 : ℕ))^(11 : ℕ) := by ring
      _ ≤ (W^(5 : ℕ))^(11 : ℕ) := ht2
      _ = W^(55 : ℕ) := by ring
  exact hgap.not_ge hbad

/-- The actual window pays the stronger power separation needed by bounded activations. -/
theorem growing_window_divisor_aperture (X : ℕ → ℝ) (hX : Tendsto X atTop atTop) :
    ∀ᶠ n in atTop,
      0 ≤ X n-Sieve.growingReciprocalMarkerWindow (X n) ∧
      0 ≤ 2*Sieve.growingReciprocalMarkerWindow (X n) ∧
      (2*Sieve.growingReciprocalMarkerWindow (X n))^(55 : ℕ) <
        (X n-Sieve.growingReciprocalMarkerWindow (X n))^(30 : ℕ) := by
  have hc := (tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hX)).const_mul (Real.log 2)
  have hhalfLog : Tendsto (fun n => Real.log (X n/2)/Real.log (X n)) atTop (𝓝 1) := by
    have ht := (tendsto_const_nhds (x := (1:ℝ))).sub hc
    simp only [mul_zero,sub_zero] at ht
    refine ht.congr' ?_
    filter_upwards [hX.eventually (eventually_gt_atTop (1:ℝ))] with n hn
    dsimp only [Function.comp_apply]
    rw [Real.log_div (by linarith : X n ≠ 0) (by norm_num : (2:ℝ) ≠ 0),
      sub_div,div_self (Real.log_pos hn).ne']
    ring
  have ht := (hhalfLog.const_mul (30:ℝ)).sub ((tendsto_log_twice_growing_window X hX).const_mul (55:ℝ))
  have hpositive := ht.eventually (Ioi_mem_nhds (show (0:ℝ) < 30*1-55*(1/2) by norm_num))
  filter_upwards [hpositive,hX.eventually (eventually_gt_atTop (27:ℝ)),
    hX.eventually growing_window_aperture] with n hn hxn hw
  have hp : 0 < Sieve.growingReciprocalMarkerWindow (X n) :=
    mul_pos (Real.sqrt_pos.mpr (by linarith)) (Sieve.growingReciprocalMarkerH_pos (X n))
  have hL0 : 0 ≤ X n-Sieve.growingReciprocalMarkerWindow (X n) := sub_nonneg.mpr hw.2.1
  have hhalf : Sieve.growingReciprocalMarkerWindow (X n) ≤ X n/2 := by
    by_contra hh
    have hcube : (X n)^(3 : ℕ) ≤ (2*Sieve.growingReciprocalMarkerWindow (X n))^(3 : ℕ) :=
      pow_le_pow_left₀ (by linarith) (by linarith) 3
    have hsquare : (X n-Sieve.growingReciprocalMarkerWindow (X n))^(2 : ℕ) ≤ (X n)^(2 : ℕ) :=
      pow_le_pow_left₀ hL0 (by linarith [hw.1]) 2
    have hpos : 0 < (X n-27)*(X n)^(2 : ℕ) := mul_pos (by linarith) (by positivity)
    nlinarith [hw.2.2]
  have hquot : 0 < (30*Real.log (X n/2)-55*Real.log (2*Sieve.growingReciprocalMarkerWindow (X n)))/
      Real.log (X n) := by
    have he : (30*Real.log (X n/2)-55*Real.log (2*Sieve.growingReciprocalMarkerWindow (X n)))/
        Real.log (X n) = 30*(Real.log (X n/2)/Real.log (X n))-
          55*(Real.log (2*Sieve.growingReciprocalMarkerWindow (X n))/Real.log (X n)) := by ring
    rw [he]
    exact hn
  have hl : 0 < Real.log (X n) := Real.log_pos (by linarith)
  have hnum : 0 < 30*Real.log (X n/2)-55*Real.log (2*Sieve.growingReciprocalMarkerWindow (X n)) :=
    (div_pos_iff.mp hquot).resolve_right (by intro h; linarith [h.2]) |>.1
  have hgap : (2*Sieve.growingReciprocalMarkerWindow (X n))^(55 : ℕ) < (X n/2)^(30 : ℕ) := by
    apply (Real.log_lt_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_pow,Real.log_pow]
    norm_num
    linarith
  exact ⟨hL0,by linarith, hgap.trans_le (pow_le_pow_left₀ (by linarith) (by linarith) 30)⟩

/-- Fixed activation powers force at most four distinct admitted receiver values even after
arbitrary conditioning; no logarithmic baseline hypothesis is needed. -/
theorem eventually_singleton_bounded_activation_no_five
    (d m : ℕ → ℕ) (K : ℕ) (k : ∀ n, Fin (d n) → Bool → ℕ)
    (a b : ∀ n, Fin (d n) → ℕ) (X : ℕ → ℝ)
    (ha : ∀ n i, 1 ≤ a n i) (hone : ∀ n i, k n i true = 1)
    (hactivation : ∀ n i, b n i ≤ a n i^K) (hm : ∀ n, 10*(K+1) ≤ m n)
    (hX : Tendsto X atTop atTop) :
    ∀ᶠ n in atTop, ∀ history ∈ routeEComponentHistogramCell (fun _ : Fin (d n) => Bool) (m n) (k n),
      (∀ r, routeEComponentSlotReceiver (fun _ : Fin (d n) => Bool)
        (fun i z => if z then (b n i:ℝ) else (a n i:ℝ)) history r ∈
          Set.Icc (X n-Sieve.growingReciprocalMarkerWindow (X n))
            (X n+Sieve.growingReciprocalMarkerWindow (X n))) →
      ∀ e : Fin 5 → Fin (m n),
        ¬ Function.Injective (fun r => routeEComponentSlotReceiver (fun _ : Fin (d n) => Bool)
          (fun i z => if z then (b n i:ℝ) else (a n i:ℝ)) history (e r)) := by
  filter_upwards [growing_window_divisor_aperture X hX] with n hn
  intro history hmem hwindow e
  apply singleton_history_no_five_of_power_activation (m n) K (k n) (a n) (b n)
    history hmem (hone n) (ha n) (hactivation n) (hm n)
    (X n-Sieve.growingReciprocalMarkerWindow (X n))
    (2*Sieve.growingReciprocalMarkerWindow (X n)) hn.1 hn.2.1 hn.2.2 _ e
  intro r
  have he : X n-Sieve.growingReciprocalMarkerWindow (X n)+
      2*Sieve.growingReciprocalMarkerWindow (X n) =
      X n+Sieve.growingReciprocalMarkerWindow (X n) := by ring
  simpa only [he] using hwindow r


end RHTower.IntegerCubeAperture
