import GaloisForLFunctions.RHTower.MobiusDivisorMiddleReserveEscape
import GaloisForLFunctions.RHTower.RetainedPrimeSupportThreshold

noncomputable section
open Finset Filter Topology
namespace RHTower

theorem mobiusDivisorSelectionFibre_singleton_union_product_barrier
    (M p : ℕ) (P L : Finset ℕ) (hpL : p ∉ L)
    (hbar : ∀ q ∈ L, M ≤ p * q) :
    mobiusDivisorSelectionFibre M (P ∪ L) {p} =
      mobiusDivisorSelectionFibre M P {p} := by
  revert hpL hbar
  induction L using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert q L hqL ih =>
    intro hpL hbar
    have hpq : p ≠ q := by
      intro he
      exact hpL (he ▸ mem_insert_self q L)
    have hpL' : p ∉ L := by
      exact fun h => hpL (mem_insert_of_mem h)
    have hbar' : ∀ r ∈ L, M ≤ p * r :=
      fun r hr => hbar r (mem_insert_of_mem hr)
    have hz : mobiusDivisorSelectionFibre M (P ∪ L) (insert q {p}) = 0 := by
      apply mobiusDivisorSelectionFibre_eq_zero_of_le_product
      simpa [prod_insert, hpq.symm, Nat.mul_comm] using
        hbar q (mem_insert_self q L)
    rw [union_insert, mobiusDivisorSelectionFibre_insert]
    simp only [show q ∉ ({p} : Finset ℕ) by simpa using hpq.symm, if_false]
    rw [hz, add_zero]
    exact ih hpL' hbar'

theorem mobiusDivisorMiddlePrimeFibre_union_bridge_barrier
    {N : ℕ} (L : Finset ℕ)
    (hL : ∀ q ∈ L, 8 * N ≤ q)
    (hLU : Disjoint L (GaloisForLFunctions.HTGeometry.primesInIoc (8 * N) (9 * N)))
    {p : ℕ}
    (hp : p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (8 * N) (9 * N)) :
    mobiusDivisorSelectionFibre (64 * N ^ (2 : ℕ))
        (mobiusDivisorSelectionPrimes (4 * N) ∪ L) {p} =
      mobiusDivisorSelectionFibre (64 * N ^ (2 : ℕ))
        (mobiusDivisorSelectionPrimes (4 * N)) {p} := by
  have hpL : p ∉ L := by
    intro h
    exact disjoint_left.mp hLU h hp
  apply mobiusDivisorSelectionFibre_singleton_union_product_barrier _ _ _ _ hpL
  intro q hq
  have hp8 := (GaloisForLFunctions.HTGeometry.mem_primesInIoc hp).2.1
  have hq8 := hL q hq
  calc
    64 * N ^ (2 : ℕ) = (8 * N) * (8 * N) := by ring
    _ ≤ p * q := Nat.mul_le_mul hp8.le hq8

private theorem eventually_eight_nine_count_bridge :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / (2 * Real.log (8 * (N : ℝ))) ≤
        (GaloisForLFunctions.HTGeometry.primesInIoc (8 * N) (9 * N)).card := by
  have hcast : Tendsto (fun N : ℕ => 8 * (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hc := hcast.eventually
    (GaloisForLFunctions.HTGeometry.eventually_primeCount_window_ge
      (K := (9 : ℝ) / 8) (by norm_num))
  filter_upwards [hc] with N hc
  have he : (9 / 8 : ℝ) * (8 * (N : ℝ)) = (9 * N : ℕ) := by
    push_cast
    ring
  have hf : 8 * (N : ℝ) = (8 * N : ℕ) := by push_cast; rfl
  rw [he, hf, Nat.floor_natCast, Nat.floor_natCast,
    ← GaloisForLFunctions.HTGeometry.card_primesInIoc
      (show 8 * N ≤ 9 * N by omega)] at hc
  convert hc using 1 <;> push_cast <;> ring

theorem eventually_mobiusDivisorMiddleEnergy_lower_bridge_barrier :
    ∀ᶠ N : ℕ in atTop, ∀ L : Finset ℕ,
      (∀ q ∈ L, 8 * N ≤ q) →
      Disjoint L (GaloisForLFunctions.HTGeometry.primesInIoc (8 * N) (9 * N)) →
      (N : ℝ) / (52428800 * Real.log (8 * (N : ℝ)) ^ (3 : ℕ)) ≤
        mobiusDivisorSelectionEnergy (64 * N ^ (2 : ℕ))
          (mobiusDivisorSelectionPrimes (4 * N) ∪ L) /
            (((64 * N ^ (2 : ℕ) : ℕ) : ℝ) ^ (2 : ℕ)) := by
  filter_upwards [eventually_mobiusDivisorMiddlePrimeFibre_upper,
    eventually_eight_nine_count_bridge,
    eventually_ge_atTop (1 : ℕ)] with N hf hc hN
  intro L hL hdis
  have hl : 0 < Real.log (8 * (N : ℝ)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 8 * N by omega))
  let a := (N : ℝ) ^ (2 : ℕ) / (80 * Real.log (8 * (N : ℝ)))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hsum := sum_le_sum
    (s := GaloisForLFunctions.HTGeometry.primesInIoc (8 * N) (9 * N))
    (fun p hp => show a ^ (2 : ℕ) ≤
      (mobiusDivisorSelectionFibre (64 * N ^ (2 : ℕ))
        (mobiusDivisorSelectionPrimes (4 * N) ∪ L) {p}) ^ (2 : ℕ) from by
      rw [mobiusDivisorMiddlePrimeFibre_union_bridge_barrier L hL hdis hp]
      have hfp : mobiusDivisorSelectionFibre (64 * N ^ (2 : ℕ))
          (mobiusDivisorSelectionPrimes (4 * N)) {p} ≤ -a := by
        simpa only [a, neg_div] using hf p hp
      have hs := mul_nonneg
        (by linarith only [hfp] : 0 ≤
          -mobiusDivisorSelectionFibre (64 * N ^ (2 : ℕ))
            (mobiusDivisorSelectionPrimes (4 * N)) {p} - a)
        (by linarith only [hfp, ha] : 0 ≤
          -mobiusDivisorSelectionFibre (64 * N ^ (2 : ℕ))
            (mobiusDivisorSelectionPrimes (4 * N)) {p} + a)
      nlinarith only [hs])
  simp only [sum_const, nsmul_eq_mul] at hsum
  have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg a)
  have hsub : GaloisForLFunctions.HTGeometry.primesInIoc (8 * N) (9 * N) ⊆
      mobiusDivisorSelectionPrimes (64 * N ^ (2 : ℕ)) := by
    intro p hp
    obtain ⟨hpp, hlo, hhi⟩ :=
      GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
    exact mem_filter.mpr ⟨mem_range.mpr (by nlinarith), hpp⟩
  have hraw := (hm.trans hsum).trans
    (sum_mobiusDivisorSelectionSingleton_sq_le_energy _ _ _ hsub)
  have hd := div_le_div_of_nonneg_right hraw
    (sq_nonneg (((64 * N ^ (2 : ℕ) : ℕ) : ℝ)))
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have he :
      ((N : ℝ) / (2 * Real.log (8 * (N : ℝ))) * a ^ (2 : ℕ)) /
        (((64 * N ^ (2 : ℕ) : ℕ) : ℝ) ^ (2 : ℕ)) =
        (N : ℝ) / (52428800 * Real.log (8 * (N : ℝ)) ^ (3 : ℕ)) := by
    dsimp [a]
    push_cast
    field_simp
    ring
  rwa [he] at hd

private theorem middle_bridge_escape_rate :
    Tendsto (fun N : ℕ =>
      (N : ℝ) / (52428800 * Real.log (8 * (N : ℝ)) ^ (3 : ℕ)))
      atTop atTop := by
  have hzero : Tendsto (fun x : ℝ => Real.log x ^ (3 : ℕ) / x)
      atTop (𝓝 0) :=
    (Real.isLittleO_pow_log_id_atTop (n := 3)).tendsto_div_nhds_zero
  have hwithin : Tendsto (fun x : ℝ => Real.log x ^ (3 : ℕ) / x)
      atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hzero
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (pow_pos (Real.log_pos hx) 3) (by linarith)
  have hr : Tendsto (fun x : ℝ => x / Real.log x ^ (3 : ℕ))
      atTop atTop := by
    exact hwithin.inv_tendsto_nhdsGT_zero.congr (fun x => by
      change (Real.log x ^ (3 : ℕ) / x)⁻¹ = x / Real.log x ^ (3 : ℕ)
      rw [inv_div])
  have hcast : Tendsto (fun N : ℕ => 8 * (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have h := (hr.comp hcast).const_mul_atTop
    (show (0 : ℝ) < 1 / (8 * 52428800) by norm_num)
  convert h using 1
  funext N
  simp only [Function.comp_def]
  ring

theorem eventually_mobiusDivisorMiddleEnergy_escape_bridge_barrier (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ L : Finset ℕ,
      (∀ q ∈ L, 8 * N ≤ q) →
      Disjoint L (GaloisForLFunctions.HTGeometry.primesInIoc (8 * N) (9 * N)) →
      C * (((64 * N ^ (2 : ℕ) : ℕ) : ℝ) ^ (2 : ℕ)) <
        mobiusDivisorSelectionEnergy (64 * N ^ (2 : ℕ))
          (mobiusDivisorSelectionPrimes (4 * N) ∪ L) := by
  filter_upwards [middle_bridge_escape_rate.eventually_gt_atTop C,
    eventually_mobiusDivisorMiddleEnergy_lower_bridge_barrier,
    eventually_ge_atTop (1 : ℕ)] with N hrate hlower hN
  intro L hL hdis
  have h := hrate.trans_le (hlower L hL hdis)
  have hden : (0 : ℝ) < (((64 * N ^ (2 : ℕ) : ℕ) : ℝ) ^ (2 : ℕ)) := by
    positivity
  exact (lt_div_iff₀ hden).mp h

end RHTower
