import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Valuation classification of triangular rational resonance rows

Every coefficient solution depends only on the maximal numerator power dividing
its index. This includes composite numerators and uses no coefficient bounds.
-/

open Finset
noncomputable section
namespace RHTower.WeilSpectral

theorem quantization_padic_mul_coprime {u v m : ℕ} (hu : 2 ≤ u)
    (hv : 1 ≤ v) (hm : 1 ≤ m) (huv : u.Coprime v) :
    padicValNat u (m * v) = padicValNat u m := by
  have hm0 : m ≠ 0 := by omega
  have hmv0 : m * v ≠ 0 := mul_ne_zero hm0 (by omega)
  apply Nat.le_antisymm
  · apply (Nat.pow_dvd_iff_le_padicValNat (by omega) hm0).mp
    exact (huv.pow_left _).dvd_of_dvd_mul_right pow_padicValNat_dvd
  · apply (Nat.pow_dvd_iff_le_padicValNat (by omega) hmv0).mp
    exact dvd_mul_of_dvd_left pow_padicValNat_dvd v

theorem quantization_padic_shift {u v m k : ℕ} (hu : 2 ≤ u)
    (hv : 1 ≤ v) (hm : 1 ≤ m) (huv : u.Coprime v)
    (hk : k ≤ padicValNat u m) :
    1 ≤ m / u ^ k * v ^ k ∧
      padicValNat u (m / u ^ k * v ^ k) = padicValNat u m - k := by
  have hu0 : 0 < u := by omega
  have hm0 : 0 < m := by omega
  have hd : u ^ k ∣ m := (Nat.pow_dvd_iff_le_padicValNat (by omega) hm0.ne').mpr hk
  have hmdiv : 0 < m / u ^ k := Nat.div_pos (Nat.le_of_dvd hm0 hd) (pow_pos hu0 k)
  have hvpow : 1 ≤ v ^ k := Nat.one_le_pow k v hv
  refine ⟨Nat.mul_pos hmdiv hvpow, ?_⟩
  rw [quantization_padic_mul_coprime hu hvpow hmdiv (huv.pow_right k)]
  have he := padicValNat_base_pow_mul (show 1 < u by omega) hmdiv.ne' k
  rw [Nat.mul_comm, Nat.div_mul_cancel hd] at he
  omega

/-- Exact coefficient classification of every triangular rational resonance system. -/
theorem quantization_rational_rows_classification {u v : ℕ} (hu : 2 ≤ u)
    (hv : 1 ≤ v) (huv : u.Coprime v) {a c : ℕ → ℂ} (hc : c 0 ≠ 0)
    (hrows : ∀ m : ℕ, 1 ≤ m →
      (∑ k ∈ range (padicValNat u m + 1), c k * a (m / u ^ k * v ^ k)) = c 0) :
    ∀ m : ℕ, 1 ≤ m → a m = a (u ^ padicValNat u m) := by
  suffices H : ∀ j m : ℕ, 1 ≤ m → padicValNat u m = j → a m = a (u ^ j) by
    intro m hm
    exact H _ m hm rfl
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro m hm he
    have huj : 1 ≤ u ^ j := Nat.one_le_pow j u (by omega)
    have hrowm := hrows m hm
    have hrowu := hrows (u ^ j) huj
    rw [he, sum_range_succ'] at hrowm
    rw [padicValNat_base_pow (by omega), sum_range_succ'] at hrowu
    simp only [pow_zero, Nat.div_one, Nat.mul_one] at hrowm hrowu
    have htail : (∑ k ∈ range j, c (k + 1) * a (m / u ^ (k + 1) * v ^ (k + 1))) =
        ∑ k ∈ range j, c (k + 1) * a (u ^ j / u ^ (k + 1) * v ^ (k + 1)) := by
      apply sum_congr rfl
      intro k hk
      have hkj : k + 1 ≤ j := by simpa only [mem_range, Nat.lt_iff_add_one_le] using hk
      obtain ⟨hmm, hmmv⟩ := quantization_padic_shift hu hv hm huv (by omega : k+1 ≤ padicValNat u m)
      obtain ⟨huu, huuv⟩ := quantization_padic_shift hu hv huj huv
        (by simpa only [padicValNat_base_pow (by omega : 1 < u)] using hkj)
      rw [he] at hmmv
      rw [padicValNat_base_pow (by omega)] at huuv
      rw [ih (j-(k+1)) (by omega) _ hmm hmmv,
        ih (j-(k+1)) (by omega) _ huu huuv]
    rw [htail] at hrowm
    exact mul_left_cancel₀ hc (add_left_cancel (hrowm.trans hrowu.symm))

/-- The complete solution space: valuation dependence plus a scalar convolution. -/
theorem quantization_rational_rows_iff {u v : ℕ} (hu : 2 ≤ u)
    (hv : 1 ≤ v) (huv : u.Coprime v) {a c : ℕ → ℂ} (hc : c 0 ≠ 0) :
    (∀ m : ℕ, 1 ≤ m →
      (∑ k ∈ range (padicValNat u m + 1), c k * a (m / u ^ k * v ^ k)) = c 0) ↔
    (∀ m : ℕ, 1 ≤ m → a m = a (u ^ padicValNat u m)) ∧
      ∀ j : ℕ, (∑ k ∈ range (j+1), c k * a (u ^ (j-k))) = c 0 := by
  have hsum (ha : ∀ m : ℕ, 1 ≤ m → a m = a (u ^ padicValNat u m))
      (m : ℕ) (hm : 1 ≤ m) :
      (∑ k ∈ range (padicValNat u m + 1), c k * a (m / u ^ k * v ^ k)) =
        ∑ k ∈ range (padicValNat u m + 1), c k * a (u ^ (padicValNat u m-k)) := by
    apply sum_congr rfl
    intro k hk
    obtain ⟨hpos, he⟩ := quantization_padic_shift hu hv hm huv (by simpa using hk)
    rw [ha _ hpos, he]
  constructor
  · intro hr
    have ha := quantization_rational_rows_classification hu hv huv hc hr
    refine ⟨ha, fun j => ?_⟩
    have h := hr (u ^ j) (Nat.one_le_pow j u (by omega))
    rw [hsum ha (u^j) (Nat.one_le_pow j u (by omega)), padicValNat_base_pow (by omega)] at h
    exact h
  · rintro ⟨ha, hj⟩ m hm
    rw [hsum ha m hm]
    exact hj _

end RHTower.WeilSpectral
