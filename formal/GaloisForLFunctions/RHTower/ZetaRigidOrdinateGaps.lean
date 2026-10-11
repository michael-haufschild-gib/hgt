import GaloisForLFunctions.RHTower.XiOrderedZeroCopyEnumeration
import GaloisForLFunctions.RHTower.XiLogDerivLineOneWindowLower
import GaloisForLFunctions.RHTower.LorentzianZeroMass

/-!
# Rigid ordinates and their normalized gaps

Let `γ_n = xiOrderedPositiveOrdinate n` be the positive ordinates of the zeros of `ξ` in
nondecreasing order, with multiplicity, and `g_n = γ_{n+1} − γ_n`. The ordinates are **`h`-rigid
from `N₀` on** (`RigidOrdinates h N₀`) if for `n ≥ N₀` they increase strictly and consecutive gaps
satisfy `g_{n+1} ≤ g_n e^{(g_n+g_{n+1})/h}` and `g_n ≤ g_{n+1} e^{(g_n+g_{n+1})/h}`.

* `RigidOrdinates.gap_chain`: along a chain the exponents add up, so two gaps of a chain of total
  span `D` differ by a factor at most `e^{2D/h}`.
* `RigidOrdinates.exists_gap_mul_log_le`: rigid gaps are at most `c₂/log γ_n`. A window
  `(γ_n, γ_n + 2w]` holds at least `log γ_n` zeros (`exists_xiZeroCount_window_ge_log`), and all
  their gaps are at least `g_n e^{−4w/h}`.
* `RigidOrdinates.exists_le_gap_mul_log`: rigid gaps are at least `c₁/log γ_n`. A tiny gap would
  propagate to so many tiny gaps that `[γ_n, γ_n + 1]` holds more zeros than the Lorentzian mass
  `8(C + log(γ_n + 4))` allows (`lorentzMass_le_log`).
-/

open Complex Filter Topology Set Finset

namespace RHTower

noncomputable section

/-- The `n`-th gap of the ordered positive ordinates. -/
def ordinateGap (n : ℕ) : ℝ := xiOrderedPositiveOrdinate (n + 1) - xiOrderedPositiveOrdinate n

theorem ordinateGap_nonneg (n : ℕ) : 0 ≤ ordinateGap n :=
  sub_nonneg.mpr (xiOrderedPositiveOrdinate_monotone (Nat.le_succ n))

/-- **Rigid ordinates.** From the index `N₀` on, the ordered ordinates increase strictly and
consecutive gaps `g, g'` obey `g' ≤ g e^{(g+g')/h}` and `g ≤ g' e^{(g+g')/h}`. -/
structure RigidOrdinates (h : ℝ) (N₀ : ℕ) : Prop where
  strict : ∀ n, N₀ ≤ n → xiOrderedPositiveOrdinate n < xiOrderedPositiveOrdinate (n + 1)
  up : ∀ n, N₀ ≤ n →
    ordinateGap (n + 1) ≤ ordinateGap n * Real.exp ((ordinateGap n + ordinateGap (n + 1)) / h)
  down : ∀ n, N₀ ≤ n →
    ordinateGap n ≤ ordinateGap (n + 1) * Real.exp ((ordinateGap n + ordinateGap (n + 1)) / h)

/-- The count up to a strictly isolated ordinate is its index plus one. -/
theorem xiZeroCount_ordinate_eq {n : ℕ}
    (hn : xiOrderedPositiveOrdinate n < xiOrderedPositiveOrdinate (n + 1)) :
    xiZeroCount (xiOrderedPositiveOrdinate n) = ((n + 1 : ℕ) : ℤ) := by
  have h1 : ((n + 1 : ℕ) : ℤ) ≤ xiZeroCount (xiOrderedPositiveOrdinate n) :=
    xiOrderedPositiveOrdinate_le_iff.mp le_rfl
  have h2 : ¬ (((n + 1 + 1 : ℕ) : ℤ) ≤ xiZeroCount (xiOrderedPositiveOrdinate n)) := fun h =>
    absurd (xiOrderedPositiveOrdinate_le_iff.mpr h) (not_le.mpr hn)
  push_cast at h1 h2 ⊢
  omega

/-- Telescoping of the gaps. -/
theorem sum_ordinateGap (n j : ℕ) :
    ∑ i ∈ Finset.range j, ordinateGap (n + i) =
      xiOrderedPositiveOrdinate (n + j) - xiOrderedPositiveOrdinate n := by
  have := Finset.sum_range_sub (fun i => xiOrderedPositiveOrdinate (n + i)) j
  simp only [add_zero] at this
  rw [← this]
  exact Finset.sum_congr rfl fun i _ => by simp only [ordinateGap, add_assoc]

/-- **Gap chains.** Along a chain from `n` to `n + j`, the gap ratio exponents add up to
`(γ_{n+j} − γ_n) + (γ_{n+j+1} − γ_{n+1})`. -/
theorem RigidOrdinates.gap_chain {h : ℝ} {N₀ : ℕ} (H : RigidOrdinates h N₀) {n : ℕ}
    (hn : N₀ ≤ n) (j : ℕ) :
    ordinateGap (n + j) ≤ ordinateGap n * Real.exp (((xiOrderedPositiveOrdinate (n + j) -
        xiOrderedPositiveOrdinate n) + (xiOrderedPositiveOrdinate (n + j + 1) -
        xiOrderedPositiveOrdinate (n + 1))) / h) ∧
    ordinateGap n ≤ ordinateGap (n + j) * Real.exp (((xiOrderedPositiveOrdinate (n + j) -
        xiOrderedPositiveOrdinate n) + (xiOrderedPositiveOrdinate (n + j + 1) -
        xiOrderedPositiveOrdinate (n + 1))) / h) := by
  induction j with
  | zero => simp
  | succ j ih =>
    set γ := xiOrderedPositiveOrdinate with hγ
    have hnj : N₀ ≤ n + j := le_trans hn (Nat.le_add_right n j)
    have hup := H.up (n + j) hnj
    have hdown := H.down (n + j) hnj
    have g0 := ordinateGap_nonneg n
    have g1 := ordinateGap_nonneg (n + j)
    have g2 := ordinateGap_nonneg (n + j + 1)
    have hE : ((γ (n + (j + 1)) - γ n) + (γ (n + (j + 1) + 1) - γ (n + 1))) / h =
        ((γ (n + j) - γ n) + (γ (n + j + 1) - γ (n + 1))) / h +
          (ordinateGap (n + j) + ordinateGap (n + j + 1)) / h := by
      simp only [ordinateGap, hγ]
      rw [show n + (j + 1) = n + j + 1 by ring, show n + j + 1 + 1 = n + j + 1 + 1 by ring]
      ring
    rw [show n + (j + 1) = n + j + 1 by ring] at hE ⊢
    rw [hE, Real.exp_add]
    constructor
    · calc ordinateGap (n + j + 1)
          ≤ ordinateGap (n + j) * Real.exp ((ordinateGap (n + j) + ordinateGap (n + j + 1)) / h) :=
            hup
        _ ≤ (ordinateGap n * Real.exp (((γ (n + j) - γ n) + (γ (n + j + 1) - γ (n + 1))) / h)) *
              Real.exp ((ordinateGap (n + j) + ordinateGap (n + j + 1)) / h) :=
            mul_le_mul_of_nonneg_right ih.1 (Real.exp_pos _).le
        _ = _ := by ring
    · calc ordinateGap n
          ≤ ordinateGap (n + j) * Real.exp (((γ (n + j) - γ n) + (γ (n + j + 1) - γ (n + 1))) / h) :=
            ih.2
        _ ≤ (ordinateGap (n + j + 1) *
              Real.exp ((ordinateGap (n + j) + ordinateGap (n + j + 1)) / h)) *
              Real.exp (((γ (n + j) - γ n) + (γ (n + j + 1) - γ (n + 1))) / h) :=
            mul_le_mul_of_nonneg_right hdown (Real.exp_pos _).le
        _ = _ := by ring

/-- The chain exponent is at most twice the span. -/
theorem chain_exponent_le (n j : ℕ) :
    (xiOrderedPositiveOrdinate (n + j) - xiOrderedPositiveOrdinate n) +
        (xiOrderedPositiveOrdinate (n + j + 1) - xiOrderedPositiveOrdinate (n + 1)) ≤
      2 * (xiOrderedPositiveOrdinate (n + j + 1) - xiOrderedPositiveOrdinate n) := by
  have h1 := xiOrderedPositiveOrdinate_monotone (Nat.le_succ (n + j))
  have h2 := xiOrderedPositiveOrdinate_monotone (Nat.le_succ n)
  linarith

/-- Chain bounds in span form: for a chain of span at most `D`, the gaps are within `e^{2D/h}`. -/
theorem RigidOrdinates.gap_chain_span {h : ℝ} (hh : 0 < h) {N₀ : ℕ} (H : RigidOrdinates h N₀)
    {n : ℕ} (hn : N₀ ≤ n) (j : ℕ) {D : ℝ}
    (hD : xiOrderedPositiveOrdinate (n + j + 1) - xiOrderedPositiveOrdinate n ≤ D) :
    ordinateGap (n + j) ≤ ordinateGap n * Real.exp (2 * D / h) ∧
    ordinateGap n ≤ ordinateGap (n + j) * Real.exp (2 * D / h) := by
  obtain ⟨h1, h2⟩ := H.gap_chain hn j
  have hE : Real.exp (((xiOrderedPositiveOrdinate (n + j) - xiOrderedPositiveOrdinate n) +
      (xiOrderedPositiveOrdinate (n + j + 1) - xiOrderedPositiveOrdinate (n + 1))) / h) ≤
      Real.exp (2 * D / h) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ hh.le
    linarith [chain_exponent_le n j]
  exact ⟨h1.trans (mul_le_mul_of_nonneg_left hE (ordinateGap_nonneg n)),
    h2.trans (mul_le_mul_of_nonneg_left hE (ordinateGap_nonneg _))⟩

/-- **Upper normalized gap bound.** Rigid gaps are `O(1/log γ_n)`. -/
theorem RigidOrdinates.exists_gap_mul_log_le {h : ℝ} (hh : 0 < h) {N₀ : ℕ}
    (H : RigidOrdinates h N₀) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ T₂ : ℝ, ∀ n, N₀ ≤ n → T₂ ≤ xiOrderedPositiveOrdinate n →
      ordinateGap n * Real.log (xiOrderedPositiveOrdinate n) ≤ c₂ := by
  obtain ⟨w, hw, T₁, hT₁4, hwin⟩ := exists_xiZeroCount_window_ge_log
  refine ⟨4 * w * Real.exp (4 * w / h), by positivity, max T₁ (Real.exp 2), fun n hn hγ => ?_⟩
  set γ := xiOrderedPositiveOrdinate with hγdef
  have hγT₁ : T₁ ≤ γ n := le_trans (le_max_left _ _) hγ
  have hγe : Real.exp 2 ≤ γ n := le_trans (le_max_right _ _) hγ
  have hγ0 : 0 < γ n := lt_of_lt_of_le (Real.exp_pos _) hγe
  have hlog2 : 2 ≤ Real.log (γ n) := by
    have := Real.log_le_log (Real.exp_pos _) hγe; rwa [Real.log_exp] at this
  -- the window `(γ_n, γ_n + 2w]`
  have hwinn := hwin (γ n + w) (by linarith)
  rw [show γ n + w - w = γ n by ring, show γ n + w + w = γ n + 2 * w by ring] at hwinn
  have hcount := xiZeroCount_ordinate_eq (H.strict n hn)
  rw [← hγdef] at hcount
  set m : ℤ := xiZeroCount (γ n + 2 * w) - ((n + 1 : ℕ) : ℤ) with hm
  have hlogw : Real.log (γ n) ≤ Real.log (γ n + w) := Real.log_le_log hγ0 (by linarith)
  have hmR : Real.log (γ n) ≤ (m : ℝ) := by
    have hc : ((xiZeroCount (γ n) : ℤ) : ℝ) = (n : ℝ) + 1 := by rw [hcount]; push_cast; ring
    rw [hc] at hwinn
    rw [hm]; push_cast
    linarith
  have hm2 : (2 : ℤ) ≤ m := by
    have : (2 : ℝ) ≤ (m : ℝ) := le_trans hlog2 hmR
    exact_mod_cast this
  set M : ℕ := m.toNat with hM
  have hMm : (M : ℤ) = m := Int.toNat_of_nonneg (by omega)
  have hMR : (M : ℝ) = (m : ℝ) := by exact_mod_cast hMm
  have hM2 : 2 ≤ M := by omega
  -- `γ_{n+M} ≤ γ_n + 2w`
  have hγM : γ (n + M) ≤ γ n + 2 * w := by
    apply xiOrderedPositiveOrdinate_le_iff.mpr
    have : xiZeroCount (γ n + 2 * w) = m + ((n + 1 : ℕ) : ℤ) := by rw [hm]; ring
    rw [this, ← hMm]; push_cast; omega
  -- the gaps `g_{n+1}, …, g_{n+M−1}`
  have hsum := sum_ordinateGap (n + 1) (M - 1)
  rw [show n + 1 + (M - 1) = n + M by omega] at hsum
  have hterm : ∀ i ∈ Finset.range (M - 1),
      ordinateGap n * Real.exp (-(4 * w / h)) ≤ ordinateGap (n + 1 + i) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hspan : γ (n + (1 + i) + 1) - γ n ≤ 2 * w := by
      have := xiOrderedPositiveOrdinate_monotone (show n + (1 + i) + 1 ≤ n + M by omega)
      linarith
    have hc := (H.gap_chain_span hh hn (1 + i) hspan).2
    rw [show n + (1 + i) = n + 1 + i by ring, show 2 * (2 * w) / h = 4 * w / h by ring] at hc
    rw [Real.exp_neg]
    calc ordinateGap n * (Real.exp (4 * w / h))⁻¹
        ≤ (ordinateGap (n + 1 + i) * Real.exp (4 * w / h)) * (Real.exp (4 * w / h))⁻¹ :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = ordinateGap (n + 1 + i) := by field_simp
  have hlow := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hsum] at hlow
  have hspan1 : γ (n + M) - γ (n + 1) ≤ 2 * w := by
    have := xiOrderedPositiveOrdinate_monotone (Nat.le_succ n)
    linarith
  have hM1 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [hM1] at hlow
  have hexp : 0 < Real.exp (-(4 * w / h)) := Real.exp_pos _
  have hg0 := ordinateGap_nonneg n
  -- `(M − 1) g_n e^{−4w/h} ≤ 2w`, `M − 1 ≥ log γ_n / 2`
  have hfin : ((M : ℝ) - 1) * ordinateGap n ≤ 2 * w * Real.exp (4 * w / h) := by
    have h1 : ((M : ℝ) - 1) * (ordinateGap n * Real.exp (-(4 * w / h))) ≤ 2 * w := by linarith
    have h2 : Real.exp (-(4 * w / h)) * Real.exp (4 * w / h) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (4 * w / h)).le
    calc ((M : ℝ) - 1) * ordinateGap n
        = ((M : ℝ) - 1) * (ordinateGap n * Real.exp (-(4 * w / h))) * Real.exp (4 * w / h) := by
          rw [mul_assoc, mul_assoc, h2, mul_one]
      _ ≤ 2 * w * Real.exp (4 * w / h) := h3
  have hMl : Real.log (γ n) ≤ 2 * ((M : ℝ) - 1) := by rw [hMR]; linarith
  calc ordinateGap n * Real.log (γ n) ≤ ordinateGap n * (2 * ((M : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left hMl hg0
    _ = 2 * (((M : ℝ) - 1) * ordinateGap n) := by ring
    _ ≤ 2 * (2 * w * Real.exp (4 * w / h)) := by linarith
    _ = 4 * w * Real.exp (4 * w / h) := by ring


theorem xiOrderedPositiveZeroCopy_injective : Function.Injective xiOrderedPositiveZeroCopy :=
  fun _ _ hab => xiOrderedPositiveZeroCopyMap_injective (Subtype.ext hab)

/-- Distinct ordered copies with ordinates within `½` of `t` number at most `2 lorentzMass t`. -/
theorem card_le_two_lorentzMass {t : ℝ} {n K : ℕ}
    (hK : ∀ j ≤ K, |xiOrderedPositiveOrdinate (n + j) - t| ≤ 1 / 2) :
    ((K + 1 : ℕ) : ℝ) ≤ 2 * lorentzMass t := by
  classical
  have hterm : ∀ j ∈ Finset.range (K + 1),
      (1 / 2 : ℝ) ≤ lorentzMassTerm t (xiOrderedPositiveZeroCopy (n + j)) := by
    intro j hj
    have hj' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hd := hK j hj'
    rw [lorentzMassTerm, xiOrderedPositiveZeroCopy_im_eq]
    have hsq : (t - xiOrderedPositiveOrdinate (n + j)) ^ 2 ≤ 1 / 4 := by
      rw [abs_sub_comm] at hd
      have := sq_abs (t - xiOrderedPositiveOrdinate (n + j))
      nlinarith [abs_nonneg (t - xiOrderedPositiveOrdinate (n + j))]
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hinj : Set.InjOn (fun j => xiOrderedPositiveZeroCopy (n + j)) (Finset.range (K + 1)) :=
    fun a _ b _ hab => by
      have := xiOrderedPositiveZeroCopy_injective hab
      omega
  have himage : ∑ j ∈ Finset.range (K + 1), lorentzMassTerm t (xiOrderedPositiveZeroCopy (n + j)) =
      ∑ q ∈ (Finset.range (K + 1)).image (fun j => xiOrderedPositiveZeroCopy (n + j)),
        lorentzMassTerm t q := (Finset.sum_image hinj).symm
  have htsum : ∑ q ∈ (Finset.range (K + 1)).image (fun j => xiOrderedPositiveZeroCopy (n + j)),
      lorentzMassTerm t q ≤ lorentzMass t :=
    (summable_lorentzMassTerm t).sum_le_tsum _ fun q _ => lorentzMassTerm_nonneg t q
  push_cast at hsum ⊢
  linarith

/-- **Lower normalized gap bound.** Rigid gaps are at least `c₁/log γ_n`. -/
theorem RigidOrdinates.exists_le_gap_mul_log {h : ℝ} (hh : 0 < h) {N₀ : ℕ}
    (H : RigidOrdinates h N₀) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ T₃ : ℝ, ∀ n, N₀ ≤ n → T₃ ≤ xiOrderedPositiveOrdinate n →
      c₁ ≤ ordinateGap n * Real.log (xiOrderedPositiveOrdinate n) := by
  obtain ⟨c₂, hc₂, T₂, hU⟩ := H.exists_gap_mul_log_le hh
  set C₀ := xiLineTwoLogDerivConstant with hC₀
  have hC₀0 : 0 ≤ C₀ := xiLineTwoLogDerivConstant_nonneg
  refine ⟨Real.exp (-(2 / h)) / 64, by positivity,
    max (max T₂ 4) (max (Real.exp (2 * c₂)) (Real.exp (C₀ + 1))), fun n hn hγ => ?_⟩
  set γ := xiOrderedPositiveOrdinate with hγdef
  have hγT₂ : T₂ ≤ γ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hγ
  have hγ4 : 4 ≤ γ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hγ
  have hγc : Real.exp (2 * c₂) ≤ γ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hγ
  have hγC : Real.exp (C₀ + 1) ≤ γ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hγ
  have hγ0 : 0 < γ n := by linarith
  have hlogc : 2 * c₂ ≤ Real.log (γ n) := by
    have := Real.log_le_log (Real.exp_pos _) hγc; rwa [Real.log_exp] at this
  have hlogC : C₀ + 1 ≤ Real.log (γ n) := by
    have := Real.log_le_log (Real.exp_pos _) hγC; rwa [Real.log_exp] at this
  have hlog0 : 0 < Real.log (γ n) := by linarith
  -- gaps from `n` on are at most `1/2`
  have hsmall : ∀ j, ordinateGap (n + j) ≤ c₂ / Real.log (γ n) := by
    intro j
    have hmono : γ n ≤ γ (n + j) := xiOrderedPositiveOrdinate_monotone (Nat.le_add_right n j)
    have h1 := hU (n + j) (le_trans hn (Nat.le_add_right n j)) (le_trans hγT₂ hmono)
    have hlj : Real.log (γ n) ≤ Real.log (γ (n + j)) := Real.log_le_log hγ0 hmono
    rw [le_div_iff₀ hlog0]
    calc ordinateGap (n + j) * Real.log (γ n) ≤ ordinateGap (n + j) * Real.log (γ (n + j)) :=
          mul_le_mul_of_nonneg_left hlj (ordinateGap_nonneg _)
      _ ≤ c₂ := h1
  have hhalf : c₂ / Real.log (γ n) ≤ 1 / 2 := by
    rw [div_le_iff₀ hlog0]; linarith
  set ε := ordinateGap n * Real.exp (2 / h) with hε
  have hg0 : 0 < ordinateGap n := sub_pos.mpr (H.strict n hn)
  have hε0 : 0 < ε := by positivity
  -- the propagation `γ_{n+j} − γ_n ≤ jε` while `jε ≤ 1/2`
  have hprop : ∀ j : ℕ, (j : ℝ) * ε ≤ 1 / 2 → γ (n + j) - γ n ≤ j * ε := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      push_cast at hj ⊢
      have hj' : (j : ℝ) * ε ≤ 1 / 2 := by nlinarith
      have h1 := ih hj'
      have h2 := hsmall j
      have hspan : γ (n + j + 1) - γ n ≤ 1 := by
        have : γ (n + j + 1) - γ n = (γ (n + j) - γ n) + ordinateGap (n + j) := by
          simp only [ordinateGap, hγdef]; ring
        rw [this]; linarith
      have hc := (H.gap_chain_span hh hn j hspan).1
      rw [show 2 * 1 / h = 2 / h by ring] at hc
      have : γ (n + (j + 1)) - γ n = (γ (n + j) - γ n) + ordinateGap (n + j) := by
        simp only [ordinateGap, hγdef]; ring_nf
      rw [this]
      linarith
  set K : ℕ := ⌊1 / (2 * ε)⌋₊ with hK
  have hKε : (K : ℝ) * ε ≤ 1 / 2 := by
    have := Nat.floor_le (show 0 ≤ 1 / (2 * ε) by positivity)
    rw [← hK] at this
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hwin : ∀ j ≤ K, |γ (n + j) - γ n| ≤ 1 / 2 := by
    intro j hj
    have hjK : (j : ℝ) * ε ≤ (K : ℝ) * ε :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hε0.le
    have h1 := hprop j (le_trans hjK hKε)
    have h2 : γ n ≤ γ (n + j) := xiOrderedPositiveOrdinate_monotone (Nat.le_add_right n j)
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hcard := card_le_two_lorentzMass (t := γ n) (n := n) (K := K) hwin
  have hmass := lorentzMass_le_log (γ n)
  rw [abs_of_pos hγ0] at hmass
  have hlog4 : Real.log (γ n + 4) ≤ Real.log 2 + Real.log (γ n) := by
    rw [← Real.log_mul (by norm_num) hγ0.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hKlt : 1 / (2 * ε) < (K : ℝ) + 1 := by
    rw [hK]; exact Nat.lt_floor_add_one _
  push_cast at hcard
  -- `1/(2ε) < K + 1 ≤ 16 (C₀ + log(γ_n + 4)) ≤ 32 log γ_n`
  have hbound : 1 / (2 * ε) < 32 * Real.log (γ n) := by linarith
  rw [div_lt_iff₀ (by positivity)] at hbound
  have hexp : Real.exp (-(2 / h)) * Real.exp (2 / h) = 1 := by rw [← Real.exp_add]; simp
  have : Real.exp (-(2 / h)) / 64 ≤ ordinateGap n * Real.log (γ n) := by
    have h1 : 1 ≤ 64 * (ordinateGap n * Real.log (γ n)) * Real.exp (2 / h) := by
      rw [hε] at hbound; nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-(2 / h))).le
    rw [mul_one] at h2
    have e : Real.exp (-(2 / h)) * (64 * (ordinateGap n * Real.log (γ n)) * Real.exp (2 / h)) =
        64 * (ordinateGap n * Real.log (γ n)) := by
      rw [show Real.exp (-(2 / h)) * (64 * (ordinateGap n * Real.log (γ n)) * Real.exp (2 / h)) =
        64 * (ordinateGap n * Real.log (γ n)) * (Real.exp (-(2 / h)) * Real.exp (2 / h)) by ring,
        hexp, mul_one]
    rw [e] at h2
    linarith
  exact this

end

end RHTower
