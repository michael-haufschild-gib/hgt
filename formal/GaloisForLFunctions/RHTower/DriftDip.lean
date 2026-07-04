/-
Doc 51 §4 (task #158): the drift-robust dip theorem — the (DRIFT-dip) core,
fully proved.

A cumulative angle walk with per-step increments in [θmin, θmax] ⊂ (0, π/3]
provably enters the down-window [2π/3, 4π/3] (mod 2π) within one wrap of
angle progress and stays there for every j with j·θmax ≤ π/3; on that block
cos ≤ −1/2, so a constant-amplitude walk takes a negative excursion of size
(L+1)·a/2. No exact lattice is needed — only step bounds, which the certified
drift formula (doc 50 §4) supplies blockwise. This is what discharges the
kill side of the cascade outside the resonance window: rotation alone cannot
absorb (doc 51 §3), rotation-with-drift provably dips.

(DEEP-FATE) computational check (deep_fate_tracker.py, pre-registered):
excursions die on the ~3·N^{1/3} entry clock, exactly this mechanism's rate.
-/
import Mathlib

namespace RHTower

/-- Linear lower growth of the angle walk. -/
theorem angle_growth {ψ : ℕ → ℝ} {θmin : ℝ}
    (hlo : ∀ m, θmin ≤ ψ (m + 1) - ψ m) :
    ∀ n : ℕ, ψ 0 + n * θmin ≤ ψ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h := hlo n
    push_cast
    have : ψ 0 + (n : ℝ) * θmin ≤ ψ n := ih
    linarith

/-- Linear upper span of the angle walk from any base index. -/
theorem angle_span {ψ : ℕ → ℝ} {θmax : ℝ}
    (hhi : ∀ m, ψ (m + 1) - ψ m ≤ θmax) :
    ∀ M j : ℕ, ψ (M + j) ≤ ψ M + j * θmax := by
  intro M j
  induction j with
  | zero => simp
  | succ j ih =>
    have h := hhi (M + j)
    push_cast
    push_cast at ih
    have : ψ (M + j + 1) ≤ ψ (M + j) + θmax := by linarith
    calc ψ (M + (j + 1)) = ψ (M + j + 1) := by ring_nf
      _ ≤ ψ (M + j) + θmax := this
      _ ≤ ψ M + j * θmax + θmax := by linarith
      _ = ψ M + (j + 1) * θmax := by ring

/-- First passage of a bounded-step increasing walk: it cannot jump over a
window of width θmax. -/
theorem exists_first_passage {ψ : ℕ → ℝ} {θmax c : ℝ}
    (hstep : ∀ m, ψ (m + 1) - ψ m ≤ θmax)
    {n : ℕ} (h0 : ψ 0 < c) (hn : c ≤ ψ n) :
    ∃ m ≤ n, c ≤ ψ m ∧ ψ m < c + θmax := by
  induction n with
  | zero => exact absurd hn (not_le.mpr h0)
  | succ n ih =>
    by_cases hc : c ≤ ψ n
    · obtain ⟨m, hm, h⟩ := ih hc
      exact ⟨m, hm.trans (Nat.le_succ n), h⟩
    · rw [not_le] at hc
      refine ⟨n + 1, le_refl _, hn, ?_⟩
      have := hstep n
      linarith

/-- On the shifted down-window [2π/3 + 2πk, 4π/3 + 2πk] the cosine is at
most −1/2. -/
theorem cos_le_neg_half_on_window {y : ℝ} {k : ℤ}
    (h1 : 2 * Real.pi / 3 + k * (2 * Real.pi) ≤ y)
    (h2 : y ≤ 4 * Real.pi / 3 + k * (2 * Real.pi)) :
    Real.cos y ≤ -(1 / 2) := by
  have hrw : y = (y - k * (2 * Real.pi)) + k * (2 * Real.pi) := by ring
  rw [hrw, Real.cos_add_int_mul_two_pi]
  set x := y - k * (2 * Real.pi) with hx
  have hx1 : 2 * Real.pi / 3 ≤ x := by simp only [hx]; linarith
  have hx2 : x ≤ 4 * Real.pi / 3 := by simp only [hx]; linarith
  have hpi : x = Real.pi - (Real.pi - x) := by ring
  rw [hpi, Real.cos_pi_sub]
  set u := Real.pi - x with hu
  have habs : |u| ≤ Real.pi / 3 := by
    rw [abs_le]
    constructor <;> simp only [hu] <;> linarith
  have hcos : Real.cos (Real.pi / 3) ≤ Real.cos |u| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg u)
      (by linarith [Real.pi_pos]) habs
  rw [Real.cos_abs] at hcos
  rw [Real.cos_pi_div_three] at hcos
  linarith

/-- **The drift-robust dip ((DRIFT-dip) core, doc 51 §4)**: a bounded-step
angle walk reaches, within 2π + θmax of angle progress, a base index from
which every offset j with j·θmax ≤ π/3 has cos(ψ(M+j)) ≤ −1/2. -/
theorem drift_dip {ψ : ℕ → ℝ} {θmin θmax : ℝ}
    (hθ0 : 0 < θmin) (hmax : θmax ≤ Real.pi / 3)
    (hlo : ∀ m, θmin ≤ ψ (m + 1) - ψ m)
    (hhi : ∀ m, ψ (m + 1) - ψ m ≤ θmax) :
    ∃ M : ℕ, ψ M ≤ ψ 0 + 2 * Real.pi + θmax ∧
      ∀ j : ℕ, (j : ℝ) * θmax ≤ Real.pi / 3 →
        Real.cos (ψ (M + j)) ≤ -(1 / 2) := by
  have hθmm : θmin ≤ θmax := le_trans (hlo 0) (hhi 0)
  have hθmax0 : 0 < θmax := lt_of_lt_of_le hθ0 hθmm
  -- the target window base c = 2π/3 + k·2π, strictly above ψ 0, within 2π
  set base : ℝ := 2 * Real.pi / 3 with hbase
  set k : ℤ := ⌊(ψ 0 - base) / (2 * Real.pi)⌋ + 1 with hk
  set c : ℝ := base + k * (2 * Real.pi) with hc
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hc0 : ψ 0 < c := by
    have hfl := Int.lt_floor_add_one ((ψ 0 - base) / (2 * Real.pi))
    have hkr : (ψ 0 - base) / (2 * Real.pi) < (k : ℝ) := by
      simp only [hk]
      push_cast
      linarith
    have h' : ψ 0 - base < (k : ℝ) * (2 * Real.pi) := by
      calc ψ 0 - base = (ψ 0 - base) / (2 * Real.pi) * (2 * Real.pi) := by
            field_simp
        _ < (k : ℝ) * (2 * Real.pi) := mul_lt_mul_of_pos_right hkr h2pi
    simp only [hc]
    linarith
  have hcup : c ≤ ψ 0 + 2 * Real.pi := by
    have hfl := Int.floor_le ((ψ 0 - base) / (2 * Real.pi))
    have hkr : (k : ℝ) ≤ (ψ 0 - base) / (2 * Real.pi) + 1 := by
      simp only [hk]
      push_cast
      linarith
    have h' : (k : ℝ) * (2 * Real.pi) ≤ (ψ 0 - base) + 2 * Real.pi := by
      calc (k : ℝ) * (2 * Real.pi)
          ≤ ((ψ 0 - base) / (2 * Real.pi) + 1) * (2 * Real.pi) :=
            mul_le_mul_of_nonneg_right hkr h2pi.le
        _ = (ψ 0 - base) + 2 * Real.pi := by field_simp
    simp only [hc]
    linarith
  -- reach the window: some n with ψ n ≥ c
  obtain ⟨n, hn⟩ : ∃ n : ℕ, c ≤ ψ n := by
    refine ⟨(⌈(c - ψ 0) / θmin⌉).toNat, ?_⟩
    have hnn : (0 : ℤ) ≤ ⌈(c - ψ 0) / θmin⌉ :=
      Int.ceil_nonneg (div_nonneg (by linarith) hθ0.le)
    have hcast : (((⌈(c - ψ 0) / θmin⌉).toNat : ℕ) : ℝ)
        = ((⌈(c - ψ 0) / θmin⌉ : ℤ) : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hnn)
    have hgrow := angle_growth hlo (⌈(c - ψ 0) / θmin⌉).toNat
    have hceil : (c - ψ 0) / θmin ≤ ((⌈(c - ψ 0) / θmin⌉ : ℤ) : ℝ) := Int.le_ceil _
    have : c - ψ 0 ≤ (((⌈(c - ψ 0) / θmin⌉).toNat : ℕ) : ℝ) * θmin := by
      rw [hcast]
      calc c - ψ 0 = (c - ψ 0) / θmin * θmin := by field_simp
        _ ≤ ((⌈(c - ψ 0) / θmin⌉ : ℤ) : ℝ) * θmin :=
            mul_le_mul_of_nonneg_right hceil hθ0.le
    linarith
  obtain ⟨M, _, hM1, hM2⟩ := exists_first_passage hhi hc0 hn
  refine ⟨M, by linarith, ?_⟩
  intro j hj
  have hspan := angle_span hhi M j
  have hwin1 : base + k * (2 * Real.pi) ≤ ψ (M + j) := by
    have hmono : ψ M ≤ ψ (M + j) := by
      have hgrow := angle_growth (ψ := fun i => ψ (M + i)) (θmin := θmin)
        (fun m => hlo (M + m)) j
      simp only [Nat.add_zero] at hgrow
      have hj0 : (0 : ℝ) ≤ (j : ℝ) * θmin := by positivity
      linarith
    simp only [hc] at hM1
    linarith
  have hwin2 : ψ (M + j) ≤ 4 * Real.pi / 3 + k * (2 * Real.pi) := by
    have : ψ (M + j) ≤ ψ M + (j : ℝ) * θmax := hspan
    simp only [hc, hbase] at hM2
    linarith
  exact cos_le_neg_half_on_window (by simpa [hbase] using hwin1) hwin2

/-- **The excursion form**: with amplitude floor a ≥ 0 on the block, the walk
takes a negative excursion of size (L+1)·a/2 within one wrap. -/
theorem drift_dip_excursion {ψ : ℕ → ℝ} {θmin θmax a : ℝ}
    (hθ0 : 0 < θmin) (hmax : θmax ≤ Real.pi / 3) (ha : 0 ≤ a)
    (hlo : ∀ m, θmin ≤ ψ (m + 1) - ψ m)
    (hhi : ∀ m, ψ (m + 1) - ψ m ≤ θmax)
    (L : ℕ) (hL : (L : ℝ) * θmax ≤ Real.pi / 3) :
    ∃ M : ℕ, ψ M ≤ ψ 0 + 2 * Real.pi + θmax ∧
      ∑ j ∈ Finset.range (L + 1), a * Real.cos (ψ (M + j))
        ≤ -(((L : ℝ) + 1) * a / 2) := by
  obtain ⟨M, hMb, hcos⟩ := drift_dip hθ0 hmax hlo hhi
  refine ⟨M, hMb, ?_⟩
  have hθmax0 : 0 < θmax := lt_of_lt_of_le hθ0 (le_trans (hlo 0) (hhi 0))
  have hterm : ∀ j ∈ Finset.range (L + 1),
      a * Real.cos (ψ (M + j)) ≤ a * (-(1 / 2)) := by
    intro j hj
    have hjL : j ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hjθ : (j : ℝ) * θmax ≤ Real.pi / 3 := by
      calc (j : ℝ) * θmax ≤ (L : ℝ) * θmax := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjL) hθmax0.le
        _ ≤ Real.pi / 3 := hL
    exact mul_le_mul_of_nonneg_left (hcos j hjθ) ha
  calc ∑ j ∈ Finset.range (L + 1), a * Real.cos (ψ (M + j))
      ≤ ∑ _j ∈ Finset.range (L + 1), a * (-(1 / 2)) :=
        Finset.sum_le_sum hterm
    _ = ((L : ℝ) + 1) * (a * (-(1 / 2))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ = -(((L : ℝ) + 1) * a / 2) := by ring

end RHTower
