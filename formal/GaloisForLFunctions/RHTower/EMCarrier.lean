/-
Chain link 5 made UNCONDITIONAL (doc 75 §1 table item 5; doc 78): the
Euler–Maclaurin carrier.

`ZetaCarrier` reduced deck/seam transport to two named interfaces on the
matched carrier `gN` — (AFE) accuracy and (LOW) floor — with the R–S-grade
accuracy constant classical-cited, not formalized. This module supplies a
carrier whose accuracy is a THEOREM: for every `N ≥ 1` and every `s` with
`0 < re s`, `s ≠ 1`,

  `riemannZeta s = emCarrier N s − s · emTail N s`,
  `‖riemannZeta s − emCarrier N s‖ ≤ ‖s‖ · N^(−re s) / re s`,

where `emCarrier N s = dirichletPoly N s + N^(1−s)/(s−1)` is finite data plus
one explicit term, and the remainder bound is exact telescoping — no
asymptotics, no cited constants. Wired consequences:

* `zeta_ne_zero_of_em_domination` — an unconditional zero-free certificate
  from finite data, anywhere in the strip.
* `afeAccurateOn_of_emCarrier_close` — `ZetaCarrier`'s (AFE) interface
  discharged from the EM bound plus a FINITE-vs-FINITE closeness input
  `‖emCarrier M − gN N‖ ≤ δ` (no ζ in that input: the classical R–S debt of
  link 5 is relocated into a comparison of two finite objects).
* `completed_domination_of_em` — the pointwise `hdom` premise of
  `anneal_seam_L_transport` / `anneal_deck_transport` supplied the same way.

Proof route: per-interval closed forms (pure cpow algebra), the telescoped
finite identity, tail limits at `re s > 1` against mathlib's
`zeta_eq_tsum_one_div_nat_cpow`, Weierstrass M-test differentiability of the
tail on the strip, connectivity of the punctured half-plane from four convex
pieces, and the identity theorem.
-/
import Mathlib
import GaloisForLFunctions.RHTower.ZetaCarrier
import GaloisForLFunctions.RHTower.SeamSignTransport
import GaloisForLFunctions.RHTower.AnnealWindowRelation

noncomputable section

namespace RHTower

open Complex Filter Topology

/-! ### §1 The carrier, the per-interval term, and the tail -/

/-- The continuation term of the Euler–Maclaurin representation. -/
def emPole (N : ℕ) : ℂ → ℂ := fun s => (N : ℂ) ^ (1 - s) / (s - 1)

/-- The EM carrier: finite Dirichlet block plus the explicit pole term. -/
def emCarrier (N : ℕ) : ℂ → ℂ := fun s => dirichletPoly N s + emPole N s

/-- Per-interval EM term, in closed form (equal to
`∫ x in m..m+1, (x − m)·x^(−s−1)` — see `emTerm_eq_integral`). -/
def emTerm (m : ℕ) : ℂ → ℂ := fun s =>
  (((m + 1 : ℕ) : ℂ) ^ (1 - s) - ((m : ℕ) : ℂ) ^ (1 - s)) / (1 - s)
    - ((m : ℕ) : ℂ) * (((m : ℕ) : ℂ) ^ (-s) - ((m + 1 : ℕ) : ℂ) ^ (-s)) / s

/-- The EM tail from level `N`. -/
def emTail (N : ℕ) : ℂ → ℂ := fun s => ∑' j : ℕ, emTerm (N + j) s

theorem natCast_succ_ne_zero (m : ℕ) : ((m + 1 : ℕ) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)

theorem natCast_ne_zero_of_one_le {m : ℕ} (hm : 1 ≤ m) : ((m : ℕ) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by omega)

/-- The EM carrier is analytic away from its explicit pole at `1`. -/
theorem emCarrier_analyticAt_of_ne_one {N : ℕ} (hN : 1 ≤ N) {z : ℂ} (hz1 : z ≠ 1) :
    AnalyticAt ℂ (emCarrier N) z := by
  have hU : IsOpen ({w : ℂ | w ≠ 1}) := isOpen_ne
  have hzU : z ∈ ({w : ℂ | w ≠ 1}) := hz1
  apply (DifferentiableOn.analyticOnNhd ?_ hU) z hzU
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  have hpole : DifferentiableAt ℂ (emPole N) w := by
    have hwm1 : w - 1 ≠ 0 := sub_ne_zero.mpr hw
    exact (((differentiable_const (1 : ℂ)).differentiableAt.sub
      differentiableAt_id).const_cpow
        (Or.inl (natCast_ne_zero_of_one_le hN))).div
      (differentiableAt_id.sub (differentiable_const 1).differentiableAt)
      hwm1
  exact ((dirichletPoly_differentiable N) w).add hpole

/-- The per-interval identity: one tail term of the zeta series, exactly. -/
theorem emTerm_key {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    ((m + 1 : ℕ) : ℂ) ^ (-s)
      = (((m + 1 : ℕ) : ℂ) ^ (1 - s) - ((m : ℕ) : ℂ) ^ (1 - s)) / (1 - s)
        - s * emTerm m s := by
  have hm0 : ((m : ℕ) : ℂ) ≠ 0 := natCast_ne_zero_of_one_le hm
  have hm10 : ((m + 1 : ℕ) : ℂ) ≠ 0 := natCast_succ_ne_zero m
  have hne1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have e1 : ((m : ℕ) : ℂ) ^ (1 - s) = ((m : ℕ) : ℂ) * ((m : ℕ) : ℂ) ^ (-s) := by
    rw [show (1 : ℂ) - s = 1 + -s by ring, Complex.cpow_add _ _ hm0,
      Complex.cpow_one]
  have e2 : ((m + 1 : ℕ) : ℂ) ^ (1 - s)
      = ((m + 1 : ℕ) : ℂ) * ((m + 1 : ℕ) : ℂ) ^ (-s) := by
    rw [show (1 : ℂ) - s = 1 + -s by ring, Complex.cpow_add _ _ hm10,
      Complex.cpow_one]
  have hcast : ((m + 1 : ℕ) : ℂ) = ((m : ℕ) : ℂ) + 1 := by push_cast; ring
  rw [emTerm, e1, e2, hcast]
  field_simp
  ring

/-! ### §2 The integral form and the norm bounds -/

/-- The closed form is the interval integral `∫ (x − m)·x^(−s−1)`. -/
theorem emTerm_eq_integral {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs0 : s ≠ 0)
    (hs1 : s ≠ 1) :
    emTerm m s
      = ∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1),
          ((x : ℂ) - ((m : ℕ) : ℂ)) * (x : ℂ) ^ (-s - 1) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hnotin : (0 : ℝ) ∉ Set.uIcc (m : ℝ) ((m : ℝ) + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    have := h.1
    linarith
  have hr1 : (-s : ℂ) ≠ -1 := fun h => hs1 (neg_inj.mp h)
  have hr2 : (-s - 1 : ℂ) ≠ -1 := by
    intro h
    have h' : (-s : ℂ) = 0 := by
      have := congrArg (· + 1) h
      simpa using this
    exact hs0 (neg_eq_zero.mp h')
  have hint1 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s))
      MeasureTheory.volume (m : ℝ) ((m : ℝ) + 1) :=
    intervalIntegral.intervalIntegrable_cpow (Or.inr hnotin)
  have hint2 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s - 1))
      MeasureTheory.volume (m : ℝ) ((m : ℝ) + 1) :=
    intervalIntegral.intervalIntegrable_cpow (Or.inr hnotin)
  have hcongr : Set.EqOn
      (fun x : ℝ => ((x : ℂ) - ((m : ℕ) : ℂ)) * (x : ℂ) ^ (-s - 1))
      (fun x : ℝ => (x : ℂ) ^ (-s) - ((m : ℕ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (Set.uIcc (m : ℝ) ((m : ℝ) + 1)) := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hx0 : (x : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      intro h
      rw [h] at hx
      linarith [hx.1]
    have hxpow : (x : ℂ) ^ (-s) = (x : ℂ) * (x : ℂ) ^ (-s - 1) := by
      have h := Complex.cpow_add 1 (-s - 1) hx0
      rw [Complex.cpow_one, show (1 : ℂ) + (-s - 1) = -s by ring] at h
      exact h
    simp only
    rw [hxpow]
    ring
  rw [intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_sub hint1 (hint2.const_mul _),
    intervalIntegral.integral_const_mul,
    integral_cpow (Or.inr ⟨hr1, hnotin⟩),
    integral_cpow (Or.inr ⟨hr2, hnotin⟩)]
  have hne1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  rw [show (-s + 1 : ℂ) = 1 - s by ring, show (-s - 1 + 1 : ℂ) = -s by ring,
    emTerm]
  push_cast
  field_simp
  ring

/-- Sharp per-term bound: the telescoping rpow difference. -/
theorem norm_emTerm_le {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hσ : 0 < s.re)
    (hs1 : s ≠ 1) :
    ‖emTerm m s‖
      ≤ ((m : ℝ) ^ (-s.re) - ((m : ℝ) + 1) ^ (-s.re)) / s.re := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hσ
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [emTerm_eq_integral hm hs0 hs1]
  have hab : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hbound : ∀ t : ℝ, t ∈ Set.Ioc (m : ℝ) ((m : ℝ) + 1) →
      ‖((t : ℂ) - ((m : ℕ) : ℂ)) * (t : ℂ) ^ (-s - 1)‖ ≤ t ^ (-s.re - 1) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := by linarith [ht.1]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0,
      show (-s - 1).re = -s.re - 1 by simp]
    have hn1 : ‖(t : ℂ) - ((m : ℕ) : ℂ)‖ ≤ 1 := by
      rw [show (t : ℂ) - ((m : ℕ) : ℂ) = ((t - m : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [ht.1.le])]
      linarith [ht.2]
    calc ‖(t : ℂ) - ((m : ℕ) : ℂ)‖ * t ^ (-s.re - 1)
        ≤ 1 * t ^ (-s.re - 1) :=
          mul_le_mul_of_nonneg_right hn1 (Real.rpow_nonneg ht0.le _)
      _ = t ^ (-s.re - 1) := one_mul _
  have hnotin : (0 : ℝ) ∉ Set.uIcc (m : ℝ) ((m : ℝ) + 1) := by
    rw [Set.uIcc_of_le hab]
    intro h
    have := h.1
    linarith
  have hg : IntervalIntegrable (fun t : ℝ => t ^ (-s.re - 1))
      MeasureTheory.volume (m : ℝ) ((m : ℝ) + 1) :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hnotin)
  have hr : (-s.re - 1 : ℝ) ≠ -1 := by
    intro h
    have : s.re = 0 := by linarith
    exact absurd this (ne_of_gt hσ)
  calc ‖∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1),
          ((x : ℂ) - ((m : ℕ) : ℂ)) * (x : ℂ) ^ (-s - 1)‖
      ≤ ∫ t : ℝ in (m : ℝ)..((m : ℝ) + 1), t ^ (-s.re - 1) :=
        intervalIntegral.norm_integral_le_of_norm_le hab
          (Filter.Eventually.of_forall hbound) hg
    _ = ((m : ℝ) ^ (-s.re) - ((m : ℝ) + 1) ^ (-s.re)) / s.re := by
        rw [integral_rpow (Or.inr ⟨hr, hnotin⟩),
          show (-s.re - 1 + 1 : ℝ) = -s.re by ring]
        rw [div_neg, ← neg_div, neg_sub]

/-- Crude per-term bound, uniform on half-planes — the M-test input. -/
theorem norm_emTerm_le' {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hσ : 0 < s.re)
    (hs1 : s ≠ 1) :
    ‖emTerm m s‖ ≤ (m : ℝ) ^ (-s.re - 1) := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hσ
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  rw [emTerm_eq_integral hm hs0 hs1]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := (m : ℝ) ^ (-s.re - 1))
    (f := fun x : ℝ => ((x : ℂ) - ((m : ℕ) : ℂ)) * (x : ℂ) ^ (-s - 1))
    (a := (m : ℝ)) (b := (m : ℝ) + 1) ?_
  · calc ‖∫ x : ℝ in (m : ℝ)..((m : ℝ) + 1),
            ((x : ℂ) - ((m : ℕ) : ℂ)) * (x : ℂ) ^ (-s - 1)‖
        ≤ (m : ℝ) ^ (-s.re - 1) * |(m : ℝ) + 1 - (m : ℝ)| := hb
      _ = (m : ℝ) ^ (-s.re - 1) := by norm_num
  · intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
      show (-s - 1).re = -s.re - 1 by simp]
    have hn1 : ‖(x : ℂ) - ((m : ℕ) : ℂ)‖ ≤ 1 := by
      rw [show (x : ℂ) - ((m : ℕ) : ℂ) = ((x - m : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [hx.1.le])]
      linarith [hx.2]
    have hmono : x ^ (-s.re - 1) ≤ (m : ℝ) ^ (-s.re - 1) :=
      Real.rpow_le_rpow_of_nonpos hm0 hx.1.le (by linarith)
    calc ‖(x : ℂ) - ((m : ℕ) : ℂ)‖ * x ^ (-s.re - 1)
        ≤ 1 * x ^ (-s.re - 1) :=
          mul_le_mul_of_nonneg_right hn1 (Real.rpow_nonneg hx0.le _)
      _ = x ^ (-s.re - 1) := one_mul _
      _ ≤ (m : ℝ) ^ (-s.re - 1) := hmono

/-! ### §3 Summability and the tail bound -/

theorem summable_norm_emTerm {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hσ : 0 < s.re)
    (hs1 : s ≠ 1) :
    Summable fun j : ℕ => ‖emTerm (N + j) s‖ := by
  have hfpos : ∀ j : ℕ, (0 : ℝ) ≤ ((N + j : ℕ) : ℝ) ^ (-s.re) :=
    fun j => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hfanti : ∀ j : ℕ,
      ((N + (j + 1) : ℕ) : ℝ) ^ (-s.re) ≤ ((N + j : ℕ) : ℝ) ^ (-s.re) := by
    intro j
    have h1 : (0 : ℝ) < ((N + j : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have h2 : ((N + j : ℕ) : ℝ) ≤ ((N + (j + 1) : ℕ) : ℝ) := by
      exact_mod_cast by omega
    exact Real.rpow_le_rpow_of_nonpos h1 h2 (by linarith)
  have hB : Summable (fun j : ℕ =>
      ((N + j : ℕ) : ℝ) ^ (-s.re) - ((N + (j + 1) : ℕ) : ℝ) ^ (-s.re)) := by
    apply summable_of_sum_range_le (c := ((N + 0 : ℕ) : ℝ) ^ (-s.re))
      (fun j => sub_nonneg.mpr (hfanti j))
    intro n
    rw [Finset.sum_range_sub' (fun j => ((N + j : ℕ) : ℝ) ^ (-s.re)) n]
    linarith [hfpos n]
  apply Summable.of_nonneg_of_le (fun j => norm_nonneg _) ?_ (hB.div_const s.re)
  intro j
  have h := norm_emTerm_le (m := N + j) (by omega) hσ hs1
  have hc : ((N + j : ℕ) : ℝ) + 1 = ((N + (j + 1) : ℕ) : ℝ) := by
    push_cast; ring
  rw [hc] at h
  exact h

theorem tsum_norm_emTerm_le {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hσ : 0 < s.re)
    (hs1 : s ≠ 1) :
    ∑' j : ℕ, ‖emTerm (N + j) s‖ ≤ (N : ℝ) ^ (-s.re) / s.re := by
  have hfpos : ∀ j : ℕ, (0 : ℝ) ≤ ((N + j : ℕ) : ℝ) ^ (-s.re) :=
    fun j => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hfanti : ∀ j : ℕ,
      ((N + (j + 1) : ℕ) : ℝ) ^ (-s.re) ≤ ((N + j : ℕ) : ℝ) ^ (-s.re) := by
    intro j
    have h1 : (0 : ℝ) < ((N + j : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have h2 : ((N + j : ℕ) : ℝ) ≤ ((N + (j + 1) : ℕ) : ℝ) := by
      exact_mod_cast by omega
    exact Real.rpow_le_rpow_of_nonpos h1 h2 (by linarith)
  have hB : Summable (fun j : ℕ =>
      ((N + j : ℕ) : ℝ) ^ (-s.re) - ((N + (j + 1) : ℕ) : ℝ) ^ (-s.re)) := by
    apply summable_of_sum_range_le (c := ((N + 0 : ℕ) : ℝ) ^ (-s.re))
      (fun j => sub_nonneg.mpr (hfanti j))
    intro n
    rw [Finset.sum_range_sub' (fun j => ((N + j : ℕ) : ℝ) ^ (-s.re)) n]
    linarith [hfpos n]
  have hper : ∀ j : ℕ, ‖emTerm (N + j) s‖
      ≤ (((N + j : ℕ) : ℝ) ^ (-s.re) - ((N + (j + 1) : ℕ) : ℝ) ^ (-s.re))
          / s.re := by
    intro j
    have h := norm_emTerm_le (m := N + j) (by omega) hσ hs1
    have hc : ((N + j : ℕ) : ℝ) + 1 = ((N + (j + 1) : ℕ) : ℝ) := by
      push_cast; ring
    rw [hc] at h
    exact h
  calc ∑' j : ℕ, ‖emTerm (N + j) s‖
      ≤ ∑' j : ℕ, (((N + j : ℕ) : ℝ) ^ (-s.re)
          - ((N + (j + 1) : ℕ) : ℝ) ^ (-s.re)) / s.re :=
        (summable_norm_emTerm hN hσ hs1).tsum_mono (hB.div_const _) hper
    _ = (∑' j : ℕ, (((N + j : ℕ) : ℝ) ^ (-s.re)
          - ((N + (j + 1) : ℕ) : ℝ) ^ (-s.re))) / s.re := tsum_div_const
    _ ≤ ((N : ℝ) ^ (-s.re)) / s.re := by
        have h4 : ∑' j : ℕ, (((N + j : ℕ) : ℝ) ^ (-s.re)
            - ((N + (j + 1) : ℕ) : ℝ) ^ (-s.re)) ≤ (N : ℝ) ^ (-s.re) := by
          apply Real.tsum_le_of_sum_range_le
            (fun j => sub_nonneg.mpr (hfanti j))
          intro n
          rw [Finset.sum_range_sub' (fun j => ((N + j : ℕ) : ℝ) ^ (-s.re)) n]
          have h5 : ((N + 0 : ℕ) : ℝ) ^ (-s.re) = (N : ℝ) ^ (-s.re) := by
            norm_num
          rw [h5]
          linarith [hfpos n]
        gcongr
    _ = (N : ℝ) ^ (-s.re) / s.re := rfl

theorem norm_emTail_le {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hσ : 0 < s.re)
    (hs1 : s ≠ 1) :
    ‖emTail N s‖ ≤ (N : ℝ) ^ (-s.re) / s.re :=
  le_trans (norm_tsum_le_tsum_norm (summable_norm_emTerm hN hσ hs1))
    (tsum_norm_emTerm_le hN hσ hs1)

/-! ### §4 The identity at `re s > 1` -/

theorem dirichletPoly_eq_sum_range (N : ℕ) (s : ℂ) :
    dirichletPoly N s = ∑ i ∈ Finset.range N, ((i + 1 : ℕ) : ℂ) ^ (-s) := by
  induction N with
  | zero => simp [dirichletPoly]
  | succ N ih =>
      rw [dirichletPoly] at ih ⊢
      rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem finite_em_identity {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs0 : s ≠ 0)
    (hs1 : s ≠ 1) (M : ℕ) :
    ∑ j ∈ Finset.range M, ((N + j + 1 : ℕ) : ℂ) ^ (-s)
      = (((N + M : ℕ) : ℂ) ^ (1 - s) - ((N : ℕ) : ℂ) ^ (1 - s)) / (1 - s)
        - s * ∑ j ∈ Finset.range M, emTerm (N + j) s := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ,
        emTerm_key (m := N + M) (by omega) hs0 hs1,
        show N + (M + 1) = N + M + 1 by omega]
      ring

theorem zeta_eq_emCarrier_of_one_lt {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hs : 1 < s.re) :
    riemannZeta s = emCarrier N s - s * emTail N s := by
  have hσ : 0 < s.re := lt_trans one_pos hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    simp at hs
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hσ
    simp at hσ
  have hne1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hsm1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hsum : Summable (fun n : ℕ => ((n : ℕ) : ℂ) ^ (-s)) := by
    have h0 := Complex.summable_one_div_nat_cpow.mpr hs
    have heq : (fun n : ℕ => 1 / ((n : ℕ) : ℂ) ^ s)
        = fun n : ℕ => ((n : ℕ) : ℂ) ^ (-s) := by
      funext n
      rw [Complex.cpow_neg, one_div]
    rwa [heq] at h0
  have hzeta : riemannZeta s = ∑' n : ℕ, ((n : ℕ) : ℂ) ^ (-s) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hs]
    congr 1
    funext n
    rw [Complex.cpow_neg, one_div]
  have hsplit := hsum.sum_add_tsum_nat_add (N + 1)
  have hhead : ∑ i ∈ Finset.range (N + 1), ((i : ℕ) : ℂ) ^ (-s)
      = dirichletPoly N s := by
    rw [Finset.sum_range_succ', dirichletPoly_eq_sum_range]
    simp [Complex.zero_cpow (neg_ne_zero.mpr hs0)]
  have hshift : Summable (fun j : ℕ => ((j + (N + 1) : ℕ) : ℂ) ^ (-s)) :=
    (summable_nat_add_iff (f := fun n : ℕ => ((n : ℕ) : ℂ) ^ (-s)) (N + 1)).mpr
      hsum
  have htend1 : Tendsto
      (fun M : ℕ => ∑ j ∈ Finset.range M, ((N + j + 1 : ℕ) : ℂ) ^ (-s))
      atTop (𝓝 (∑' j : ℕ, ((j + (N + 1) : ℕ) : ℂ) ^ (-s))) := by
    have h := hshift.hasSum.tendsto_sum_nat
    have hfe : (fun M : ℕ =>
        ∑ j ∈ Finset.range M, ((j + (N + 1) : ℕ) : ℂ) ^ (-s))
        = fun M : ℕ => ∑ j ∈ Finset.range M, ((N + j + 1 : ℕ) : ℂ) ^ (-s) := by
      funext M
      exact Finset.sum_congr rfl fun j _ => by
        rw [show j + (N + 1) = N + j + 1 by omega]
    rwa [hfe] at h
  have hfe2 : (fun M : ℕ =>
      ∑ j ∈ Finset.range M, ((N + j + 1 : ℕ) : ℂ) ^ (-s))
      = fun M : ℕ =>
        ((((N + M : ℕ) : ℂ) ^ (1 - s) - ((N : ℕ) : ℂ) ^ (1 - s)) / (1 - s))
          - s * ∑ j ∈ Finset.range M, emTerm (N + j) s := by
    funext M
    exact finite_em_identity hN hs0 hs1 M
  have hcM : Tendsto (fun M : ℕ => ((N + M : ℕ) : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : (fun M : ℕ => ‖((N + M : ℕ) : ℂ) ^ (1 - s)‖)
        = fun M : ℕ => (((N + M : ℕ) : ℝ)) ^ (-(s.re - 1)) := by
      funext M
      rw [Complex.norm_natCast_cpow_of_pos (by omega)]
      congr 1
      simp [Complex.sub_re, Complex.one_re]
    rw [hnorm]
    have houter : Tendsto (fun x : ℝ => x ^ (-(s.re - 1))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    have hinner : Tendsto (fun M : ℕ => ((N + M : ℕ) : ℝ)) atTop atTop := by
      apply tendsto_natCast_atTop_atTop.comp
      exact tendsto_atTop_mono (fun M => Nat.le_add_left M N) tendsto_id
    exact houter.comp hinner
  have hPM : Tendsto (fun M : ℕ => ∑ j ∈ Finset.range M, emTerm (N + j) s)
      atTop (𝓝 (emTail N s)) := by
    have hsummableT : Summable fun j : ℕ => emTerm (N + j) s :=
      (summable_norm_emTerm hN hσ hs1).of_norm
    exact hsummableT.hasSum.tendsto_sum_nat
  have hRHS : Tendsto (fun M : ℕ =>
      ((((N + M : ℕ) : ℂ) ^ (1 - s) - ((N : ℕ) : ℂ) ^ (1 - s)) / (1 - s))
        - s * ∑ j ∈ Finset.range M, emTerm (N + j) s) atTop
      (𝓝 (((0 - ((N : ℕ) : ℂ) ^ (1 - s)) / (1 - s)) - s * emTail N s)) :=
    ((hcM.sub tendsto_const_nhds).div_const _).sub (hPM.const_mul s)
  rw [hfe2] at htend1
  have htau : ∑' j : ℕ, ((j + (N + 1) : ℕ) : ℂ) ^ (-s)
      = ((0 - ((N : ℕ) : ℂ) ^ (1 - s)) / (1 - s)) - s * emTail N s :=
    tendsto_nhds_unique htend1 hRHS
  rw [hzeta, ← hsplit, hhead, htau, emCarrier, emPole]
  have hdiv : (0 - ((N : ℕ) : ℂ) ^ (1 - s)) / (1 - s)
      = ((N : ℕ) : ℂ) ^ (1 - s) / (s - 1) := by
    rw [zero_sub, neg_div, show (s - 1 : ℂ) = -(1 - s) by ring, div_neg]
  rw [hdiv]
  ring

/-! ### §5 Differentiability of the tail on the strip -/

theorem differentiableAt_emTerm {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs0 : s ≠ 0)
    (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (emTerm m) s := by
  have hm0 : ((m : ℕ) : ℂ) ≠ 0 := natCast_ne_zero_of_one_le hm
  have hm10 : ((m + 1 : ℕ) : ℂ) ≠ 0 := natCast_succ_ne_zero m
  have hne1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hd1s : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s :=
    (differentiable_const (1 : ℂ)).differentiableAt.sub differentiableAt_id
  have hdneg : DifferentiableAt ℂ (fun z : ℂ => -z) s :=
    differentiableAt_id.neg
  have d1 : DifferentiableAt ℂ (fun z : ℂ => ((m + 1 : ℕ) : ℂ) ^ (1 - z)) s :=
    hd1s.const_cpow (Or.inl hm10)
  have d2 : DifferentiableAt ℂ (fun z : ℂ => ((m : ℕ) : ℂ) ^ (1 - z)) s :=
    hd1s.const_cpow (Or.inl hm0)
  have d3 : DifferentiableAt ℂ (fun z : ℂ => ((m : ℕ) : ℂ) ^ (-z)) s :=
    hdneg.const_cpow (Or.inl hm0)
  have d4 : DifferentiableAt ℂ (fun z : ℂ => ((m + 1 : ℕ) : ℂ) ^ (-z)) s :=
    hdneg.const_cpow (Or.inl hm10)
  exact ((d1.sub d2).div hd1s hne1).sub
    (((d3.sub d4).const_mul _).div differentiableAt_id hs0)

theorem differentiableOn_emTail {N : ℕ} (hN : 1 ≤ N) :
    DifferentiableOn ℂ (emTail N) {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  intro s₀ hs₀
  obtain ⟨hσ₀, hs₀1⟩ := hs₀
  set δ : ℝ := s₀.re / 2 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    linarith
  set V : Set ℂ := {s : ℂ | δ < s.re} ∩ {s : ℂ | s ≠ 1} with hVdef
  have hVopen : IsOpen V :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  have hs₀V : s₀ ∈ V := by
    constructor
    · show δ < s₀.re
      rw [hδdef]
      linarith
    · exact hs₀1
  have hu : Summable (fun j : ℕ => ((N + j : ℕ) : ℝ) ^ (-δ - 1)) := by
    have heq : (fun j : ℕ => ((N + j : ℕ) : ℝ) ^ (-δ - 1))
        = fun j : ℕ => ((j + N : ℕ) : ℝ) ^ (-δ - 1) := by
      funext j
      rw [Nat.add_comm]
    rw [heq]
    exact (summable_nat_add_iff
        (f := fun n : ℕ => ((n : ℕ) : ℝ) ^ (-δ - 1)) N).mpr
      (Real.summable_nat_rpow.mpr (by linarith))
  have hb : ∀ (j : ℕ), ∀ z ∈ V, ‖emTerm (N + j) z‖
      ≤ ((N + j : ℕ) : ℝ) ^ (-δ - 1) := by
    intro j z hz
    have hδz : δ < z.re := hz.1
    have hz1 : z ≠ 1 := hz.2
    have hσz : 0 < z.re := lt_trans hδpos hδz
    have h1 := norm_emTerm_le' (m := N + j) (by omega) hσz hz1
    refine le_trans h1 ?_
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
    · linarith
  have htu : TendstoUniformlyOn
      (fun (t : Finset ℕ) z => ∑ j ∈ t, emTerm (N + j) z)
      (emTail N) atTop V := tendstoUniformlyOn_tsum hu hb
  have hdiff : DifferentiableOn ℂ (emTail N) V := by
    apply (htu.tendstoLocallyUniformlyOn).differentiableOn ?_ hVopen
    apply Filter.Eventually.of_forall
    intro t z hz
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.fun_sum
    intro j _
    have hδz : δ < z.re := hz.1
    have hz1 : z ≠ 1 := hz.2
    have hσz : 0 < z.re := lt_trans hδpos hδz
    exact differentiableAt_emTerm (by omega)
      (fun h => by simp [h] at hσz) hz1
  exact (hdiff.differentiableAt (hVopen.mem_nhds hs₀V)).differentiableWithinAt

/-! ### §6 Connectivity and the identity theorem -/

theorem isOpen_emStrip : IsOpen ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s ≠ 1}) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne

theorem isPreconnected_emStrip :
    IsPreconnected ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s ≠ 1}) := by
  set C₁ : Set ℂ := {z : ℂ | 0 < z.re} ∩ {z : ℂ | z.re < 1} with hC₁def
  set C₂ : Set ℂ := {z : ℂ | 1 < z.re} with hC₂def
  set Cp : Set ℂ := {z : ℂ | 0 < z.re} ∩ {z : ℂ | 0 < z.im} with hCpdef
  set Cm : Set ℂ := {z : ℂ | 0 < z.re} ∩ {z : ℂ | z.im < 0} with hCmdef
  have hC₁ : IsPreconnected C₁ :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have hC₂ : IsPreconnected C₂ := (convex_halfSpace_re_gt 1).isPreconnected
  have hCp : IsPreconnected Cp :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hCm : IsPreconnected Cm :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hA : IsPreconnected (C₁ ∪ Cp) := by
    apply IsPreconnected.union (⟨1/2, 1/2⟩ : ℂ)
    · exact ⟨show (0:ℝ) < 1/2 by norm_num, show (1:ℝ)/2 < 1 by norm_num⟩
    · exact ⟨show (0:ℝ) < 1/2 by norm_num, show (0:ℝ) < 1/2 by norm_num⟩
    · exact hC₁
    · exact hCp
  have hB : IsPreconnected ((C₁ ∪ Cp) ∪ C₂) := by
    apply IsPreconnected.union (⟨2, 1⟩ : ℂ)
    · exact Or.inr ⟨show (0:ℝ) < 2 by norm_num, show (0:ℝ) < 1 by norm_num⟩
    · exact show (1:ℝ) < 2 by norm_num
    · exact hA
    · exact hC₂
  have hC : IsPreconnected (((C₁ ∪ Cp) ∪ C₂) ∪ Cm) := by
    apply IsPreconnected.union (⟨1/2, -(1/2)⟩ : ℂ)
    · exact Or.inl (Or.inl ⟨show (0:ℝ) < 1/2 by norm_num,
        show (1:ℝ)/2 < 1 by norm_num⟩)
    · exact ⟨show (0:ℝ) < 1/2 by norm_num, show -(1/2 : ℝ) < 0 by norm_num⟩
    · exact hB
    · exact hCm
  have hcover : {s : ℂ | 0 < s.re} ∩ {s : ℂ | s ≠ 1}
      = ((C₁ ∪ Cp) ∪ C₂) ∪ Cm := by
    ext z
    simp only [hC₁def, hC₂def, hCpdef, hCmdef, Set.mem_inter_iff,
      Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hre, hne⟩
      rcases lt_trichotomy z.im 0 with him | him | him
      · exact Or.inr ⟨hre, him⟩
      · have hre1 : z.re ≠ 1 := by
          intro h
          apply hne
          apply Complex.ext
          · rw [Complex.one_re]; exact h
          · rw [Complex.one_im]; exact him
        rcases lt_or_gt_of_ne hre1 with h | h
        · exact Or.inl (Or.inl (Or.inl ⟨hre, h⟩))
        · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl (Or.inr ⟨hre, him⟩))
    · rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩) | h) | ⟨h1, h2⟩)
      · exact ⟨h1, fun he => by
          rw [he, Complex.one_re] at h2
          exact lt_irrefl 1 h2⟩
      · exact ⟨h1, fun he => by
          rw [he, Complex.one_im] at h2
          exact lt_irrefl 0 h2⟩
      · exact ⟨lt_trans one_pos h, fun he => by
          rw [he, Complex.one_re] at h
          exact lt_irrefl 1 h⟩
      · exact ⟨h1, fun he => by
          rw [he, Complex.one_im] at h2
          exact lt_irrefl 0 h2⟩
  rw [hcover]
  exact hC

/-- **The Euler–Maclaurin representation of ζ on the strip — unconditional.**
For `N ≥ 1`, `0 < re s`, `s ≠ 1`:
`ζ(s) = Σ_{n≤N} n^(−s) + N^(1−s)/(s−1) − s·emTail N s`. -/
theorem zeta_eq_emCarrier_sub {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hσ : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = emCarrier N s - s * emTail N s := by
  have hU : IsOpen ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s ≠ 1}) := isOpen_emStrip
  have hzeta : AnalyticOnNhd ℂ riemannZeta
      ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s ≠ 1}) := by
    apply DifferentiableOn.analyticOnNhd ?_ hU
    intro z hz
    have hz1 : z ≠ 1 := hz.2
    exact (differentiableAt_riemannZeta hz1).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ (fun z => emCarrier N z - z * emTail N z)
      ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s ≠ 1}) := by
    apply DifferentiableOn.analyticOnNhd ?_ hU
    intro z hz
    have hz1 : z ≠ 1 := hz.2
    apply DifferentiableAt.differentiableWithinAt
    have hcar : DifferentiableAt ℂ (emCarrier N) z := by
      have hpole : DifferentiableAt ℂ (emPole N) z := by
        have hzm1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
        exact (((differentiable_const (1 : ℂ)).differentiableAt.sub
          differentiableAt_id).const_cpow
            (Or.inl (natCast_ne_zero_of_one_le hN))).div
          (differentiableAt_id.sub (differentiable_const 1).differentiableAt)
          hzm1
      exact ((dirichletPoly_differentiable N) z).add hpole
    have htail : DifferentiableAt ℂ (emTail N) z :=
      (differentiableOn_emTail hN).differentiableAt (hU.mem_nhds hz)
    exact hcar.sub (differentiableAt_id.mul htail)
  have h2mem : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} ∩ {s : ℂ | s ≠ 1} := by
    constructor
    · show (0 : ℝ) < (2 : ℂ).re
      simp
    · show (2 : ℂ) ≠ 1
      norm_num
  have hev : riemannZeta =ᶠ[𝓝 (2 : ℂ)]
      fun z => emCarrier N z - z * emTail N z := by
    have hopen' : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have h2' : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by
      show (1 : ℝ) < (2 : ℂ).re
      simp
    filter_upwards [hopen'.mem_nhds h2'] with z hz
    exact zeta_eq_emCarrier_of_one_lt hN hz
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hzeta hg
    isPreconnected_emStrip h2mem hev ⟨hσ, hs1⟩

/-! ### §7 The wired supplies: accuracy, zero-freeness, domination -/

/-- **The unconditional (AFE)-grade accuracy of the EM carrier**: explicit,
machine-checked, no cited constants. -/
theorem zeta_sub_emCarrier_norm_le {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hσ : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s - emCarrier N s‖ ≤ ‖s‖ * (N : ℝ) ^ (-s.re) / s.re := by
  rw [zeta_eq_emCarrier_sub hN hσ hs1,
    show emCarrier N s - s * emTail N s - emCarrier N s
      = -(s * emTail N s) by ring,
    norm_neg, norm_mul, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (norm_emTail_le hN hσ hs1) (norm_nonneg s)

/-- **Unconditional zero-free certificate from finite data**: wherever the EM
carrier beats its own explicit remainder, ζ does not vanish. -/
theorem zeta_ne_zero_of_em_domination {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hσ : 0 < s.re) (hs1 : s ≠ 1)
    (h : ‖s‖ * (N : ℝ) ^ (-s.re) / s.re < ‖emCarrier N s‖) :
    riemannZeta s ≠ 0 := by
  intro h0
  have hb := zeta_sub_emCarrier_norm_le hN hσ hs1
  rw [h0, zero_sub, norm_neg] at hb
  exact absurd (lt_of_le_of_lt hb h) (lt_irrefl _)

/-- **The (AFE) interface of `ZetaCarrier`, discharged**: EM accuracy `ε₁`
(machine-checked above) plus a FINITE-vs-FINITE closeness `δ` between the two
carriers gives `AFEAccurateOn S N (ε₁ + δ)`. The classical R–S content of
chain link 5 lives entirely in the `hclose` input — a statement about two
finite objects, with no ζ in it. -/
theorem afeAccurateOn_of_emCarrier_close {S : Set ℂ} {N M : ℕ} (hM : 1 ≤ M)
    {ε₁ δ : ℝ}
    (hstrip : ∀ z ∈ S, 0 < z.re ∧ z ≠ 1)
    (hE : ∀ z ∈ S, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ S, ‖emCarrier M z - gN N z‖ ≤ δ) :
    AFEAccurateOn S N (ε₁ + δ) := by
  intro z hz
  obtain ⟨h1, h2⟩ := hstrip z hz
  calc ‖riemannZeta z - gN N z‖
      ≤ ‖riemannZeta z - emCarrier M z‖ + ‖emCarrier M z - gN N z‖ := by
        have := dist_triangle (riemannZeta z) (emCarrier M z) (gN N z)
        simpa [dist_eq_norm] using this
    _ ≤ ε₁ + δ :=
        add_le_add (le_trans (zeta_sub_emCarrier_norm_le hM h1 h2) (hE z hz))
          (hclose z hz)

/-- Raw finite-carrier domination from EM remainder, finite-carrier closeness, and a LOW floor.
This is the pointwise finite-data inequality consumed before passing to completed-carrier
domination or finite-side transport. -/
theorem raw_domination_of_emCarrier_close_floor {S : Set ℂ} {N M : ℕ} {ε₁ δ : ℝ}
    (hE : ∀ z ∈ S, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ S, ‖emCarrier M z - gN N z‖ ≤ δ)
    (hF : CarrierFloorOn S N (ε₁ + δ)) :
    ∀ z ∈ S,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖ <
        ‖gN N z‖ := by
  intro z hz
  exact lt_of_le_of_lt (add_le_add (hE z hz) (hclose z hz)) (hF z hz)

/-- Completed-carrier domination from EM remainder, finite-carrier closeness, and a LOW floor.
This is the set-level EM finite-data version of `completed_domination_of_interfaces`. -/
theorem completed_domination_of_emCarrier_close_floor {S : Set ℂ} {N M : ℕ} (hM : 1 ≤ M)
    {ε₁ δ : ℝ}
    (hstrip : ∀ z ∈ S, 0 < z.re ∧ z.re < 1)
    (hE : ∀ z ∈ S, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ S, ‖emCarrier M z - gN N z‖ ≤ δ)
    (hF : CarrierFloorOn S N (ε₁ + δ)) :
    ∀ z ∈ S, ‖xi z - completedGN N z‖ < ‖completedGN N z‖ := by
  have hstripAFE : ∀ z ∈ S, 0 < z.re ∧ z ≠ 1 := by
    intro z hz
    refine ⟨(hstrip z hz).1, ?_⟩
    intro hz1
    have hzlt : z.re < 1 := (hstrip z hz).2
    rw [hz1] at hzlt
    norm_num at hzlt
  have hA : AFEAccurateOn S N (ε₁ + δ) :=
    afeAccurateOn_of_emCarrier_close hM hstripAFE hE hclose
  exact completed_domination_of_interfaces hstrip hA hF

/-- **The pointwise `hdom` premise of the seam/deck transports, supplied**:
EM remainder plus finite-vs-finite closeness under the `gN` floor gives
completed-level domination `‖ξ − Φ̃_N‖ < ‖Φ̃_N‖` — the exact hypothesis shape
of `anneal_seam_L_transport` and `anneal_deck_transport`. -/
theorem completed_domination_of_em {N M : ℕ} (hM : 1 ≤ M) {s : ℂ}
    (hσ : 0 < s.re) (h1 : s ≠ 1) (hG : Gammaℝ s ≠ 0)
    (h : ‖s‖ * (M : ℝ) ^ (-s.re) / s.re + ‖emCarrier M s - gN N s‖
      < ‖gN N s‖) :
    ‖xi s - completedGN N s‖ < ‖completedGN N s‖ := by
  have h0 : s ≠ 0 := fun hh => by simp [hh] at hσ
  refine (completed_domination_iff h0 h1 hG).mpr ?_
  calc ‖riemannZeta s - gN N s‖
      ≤ ‖riemannZeta s - emCarrier M s‖ + ‖emCarrier M s - gN N s‖ := by
        have := dist_triangle (riemannZeta s) (emCarrier M s) (gN N s)
        simpa [dist_eq_norm] using this
    _ ≤ ‖s‖ * (M : ℝ) ^ (-s.re) / s.re + ‖emCarrier M s - gN N s‖ :=
        add_le_add (zeta_sub_emCarrier_norm_le hM hσ h1) le_rfl
    _ < ‖gN N s‖ := h

end RHTower

namespace RHTower

open Complex Filter Topology

/-- EM-supplied ANNEAL deck transport: the abstract `(AFE)` premise is replaced by
Euler-Maclaurin remainder control plus finite carrier closeness. -/
theorem anneal_deck_transport_of_emCarrier_close {N M : ℕ}
    {F₁ F₂ G₁ G₂ : ℂ → ℂ} {a : ℂ} {R ε₁ δ : ℝ}
    (k : ℕ) (hM : 1 ≤ M) (hR : 0 < R)
    (hstrip : ∀ z ∈ chartR a R ∪ chartL a R, 0 < z.re ∧ z.re < 1)
    (hE : ∀ z ∈ chartR a R ∪ chartL a R, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ chartR a R ∪ chartL a R, ‖emCarrier M z - gN N z‖ ≤ δ)
    (hF : CarrierFloorOn (chartR a R ∪ chartL a R) N (ε₁ + δ))
    (hF₁ : AnalyticOnNhd ℂ F₁ (chartR a R)) (hF₂ : AnalyticOnNhd ℂ F₂ (chartL a R))
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hpF₁ : ∀ z ∈ chartR a R, F₁ z ^ 2 ^ k = xi z)
    (hpF₂ : ∀ z ∈ chartL a R, F₂ z ^ 2 ^ k = xi z)
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ 2 ^ k = completedGN N z)
    (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ 2 ^ k = completedGN N z) :
    deckClass F₁ F₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) =
      deckClass G₁ G₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) := by
  have hstripAFE : ∀ z ∈ chartR a R ∪ chartL a R, 0 < z.re ∧ z ≠ 1 := by
    intro z hz
    refine ⟨(hstrip z hz).1, ?_⟩
    intro hz1
    have hzlt : z.re < 1 := (hstrip z hz).2
    rw [hz1] at hzlt
    norm_num at hzlt
  have hA : AFEAccurateOn (chartR a R ∪ chartL a R) N (ε₁ + δ) :=
    afeAccurateOn_of_emCarrier_close hM hstripAFE hE hclose
  exact anneal_deck_transport k hR hstrip hA hF hF₁ hF₂ hG₁ hG₂ hpF₁ hpF₂ hpG₁ hpG₂

end RHTower

namespace RHTower

open Complex Filter Topology

/-- EM-supplied seam L-transport: the two pointwise completed-domination inputs are
replaced by Euler-Maclaurin remainder control plus finite carrier closeness. -/
theorem anneal_seam_L_transport_of_emCarrier_close {N M : ℕ} {g₁ g₂ G₁ G₂ : ℂ → ℂ}
    {U : Set ℂ} (hMpos : 1 ≤ M)
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUstrip : ∀ z ∈ U, 0 < z.re ∧ z.re < 1)
    (hg₁ : AnalyticOnNhd ℂ g₁ U) (hg₂ : AnalyticOnNhd ℂ g₂ (lineReflect ⁻¹' U))
    (hG₁ : AnalyticOnNhd ℂ G₁ U) (hG₂ : AnalyticOnNhd ℂ G₂ (lineReflect ⁻¹' U))
    (hp₁ : ∀ s ∈ U, g₁ s ^ 2 = xi s) (hp₂ : ∀ s ∈ lineReflect ⁻¹' U, g₂ s ^ 2 = xi s)
    (hP₁ : ∀ s ∈ U, G₁ s ^ 2 = completedGN N s)
    (hP₂ : ∀ s ∈ lineReflect ⁻¹' U, G₂ s ^ 2 = completedGN N s)
    {pP pM : ℂ} (hpP : pP ∈ U) (hpM : pM ∈ U)
    (hPline : pP.re = 1 / 2) (hMline : pM.re = 1 / 2)
    (hEMP : ‖pP‖ * (M : ℝ) ^ (-pP.re) / pP.re + ‖emCarrier M pP - gN N pP‖
      < ‖gN N pP‖)
    (hEMM : ‖pM‖ * (M : ℝ) ^ (-pM.re) / pM.re + ‖emCarrier M pM - gN N pM‖
      < ‖gN N pM‖) :
    deckClass g₁ g₂ pP pM = deckClass G₁ G₂ pP pM := by
  have hPσ : 0 < pP.re := by rw [hPline]; norm_num
  have hMσ : 0 < pM.re := by rw [hMline]; norm_num
  have hPne1 : pP ≠ 1 := by
    intro hp
    rw [hp] at hPline
    norm_num at hPline
  have hMne1 : pM ≠ 1 := by
    intro hp
    rw [hp] at hMline
    norm_num at hMline
  have hdomP := completed_domination_of_em hMpos hPσ hPne1
    (Gammaℝ_ne_zero_of_re_pos hPσ) hEMP
  have hdomM := completed_domination_of_em hMpos hMσ hMne1
    (Gammaℝ_ne_zero_of_re_pos hMσ) hEMM
  exact anneal_seam_L_transport hU hUc hUstrip hg₁ hg₂ hG₁ hG₂ hp₁ hp₂ hP₁ hP₂ hpP
    hpM hPline hMline hdomP hdomM

/-- EM-supplied seam L-transport from the set-level finite-data interfaces.
The Euler-Maclaurin bound and finite `emCarrier`/`gN` closeness give `(AFE)`;
the LOW floor then supplies the strict domination at the two seam basepoints. -/
theorem anneal_seam_L_transport_of_emCarrier_close_floor {N M : ℕ}
    {g₁ g₂ G₁ G₂ : ℂ → ℂ} {U : Set ℂ} {ε₁ δ : ℝ}
    (hMpos : 1 ≤ M)
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUstrip : ∀ z ∈ U, 0 < z.re ∧ z.re < 1)
    (hE : ∀ z ∈ U, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ U, ‖emCarrier M z - gN N z‖ ≤ δ)
    (hF : CarrierFloorOn U N (ε₁ + δ))
    (hg₁ : AnalyticOnNhd ℂ g₁ U) (hg₂ : AnalyticOnNhd ℂ g₂ (lineReflect ⁻¹' U))
    (hG₁ : AnalyticOnNhd ℂ G₁ U) (hG₂ : AnalyticOnNhd ℂ G₂ (lineReflect ⁻¹' U))
    (hp₁ : ∀ s ∈ U, g₁ s ^ 2 = xi s) (hp₂ : ∀ s ∈ lineReflect ⁻¹' U, g₂ s ^ 2 = xi s)
    (hP₁ : ∀ s ∈ U, G₁ s ^ 2 = completedGN N s)
    (hP₂ : ∀ s ∈ lineReflect ⁻¹' U, G₂ s ^ 2 = completedGN N s)
    {pP pM : ℂ} (hpP : pP ∈ U) (hpM : pM ∈ U)
    (hPline : pP.re = 1 / 2) (hMline : pM.re = 1 / 2) :
    deckClass g₁ g₂ pP pM = deckClass G₁ G₂ pP pM := by
  have hdom : ∀ z ∈ U, ‖xi z - completedGN N z‖ < ‖completedGN N z‖ :=
    completed_domination_of_emCarrier_close_floor hMpos hUstrip hE hclose hF
  exact anneal_seam_L_transport hU hUc hUstrip hg₁ hg₂ hG₁ hG₂ hp₁ hp₂ hP₁ hP₂ hpP
    hpM hPline hMline (hdom pP hpP) (hdom pM hpM)

end RHTower

namespace RHTower

open Complex Filter Topology Metric

/-- EM-supplied finite-side rung theorem: chart domination is replaced by the
Euler-Maclaurin remainder plus finite EM-to-`gN` comparison on the annulus charts. -/
theorem xi_rung_of_finite_side_of_emCarrier_close {N M : ℕ} (k : ℕ)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (hMpos : 1 ≤ M) (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hchartStrip : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z.re < 1)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hEMdom : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖ < ‖gN N z‖)
    (hL : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
        ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)])
    (hfin : 2 ^ k ∣ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z) :
    2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z := by
  have hdom : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖xi z - completedGN N z‖ < ‖completedGN N z‖ := by
    intro z hz
    have hσ : 0 < z.re := (hchartStrip z hz).1
    have hz_ne_one : z ≠ 1 := by
      intro hz1
      have hzlt : z.re < 1 := (hchartStrip z hz).2
      rw [hz1] at hzlt
      norm_num at hzlt
    exact completed_domination_of_em hMpos hσ hz_ne_one (Gammaℝ_ne_zero_of_re_pos hσ)
      (hEMdom z hz)
  exact xi_rung_of_finite_side_of_domination k h0 hrR hm₁ hcl₁ hstrip hm₂ hcl₂ hρ₁ hρ₂
    hh hh0 hh' hh0' hfact₁ hfact₂ hdom hL hfin

/-- EM-supplied finite-side rung theorem from the set-level LOW floor.
The EM remainder bound and finite `emCarrier`/`gN` closeness are compared against
`CarrierFloorOn` to supply the pointwise domination table required by the rung
transport. -/
theorem xi_rung_of_finite_side_of_emCarrier_close_floor {N M : ℕ} (k : ℕ)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R ε₁ δ : ℝ}
    (hMpos : 1 ≤ M) (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hchartStrip : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z.re < 1)
    (hE : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖emCarrier M z - gN N z‖ ≤ δ)
    (hF : CarrierFloorOn (chartRA a r₀ R ∪ chartLA a r₀ R) N (ε₁ + δ))
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hL : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
        ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)])
    (hfin : 2 ^ k ∣ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z) :
    2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z := by
  have hEMdom : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖ < ‖gN N z‖ :=
    raw_domination_of_emCarrier_close_floor hE hclose hF
  exact xi_rung_of_finite_side_of_emCarrier_close k hMpos h0 hrR hchartStrip hm₁ hcl₁
    hstrip hm₂ hcl₂ hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hEMdom hL hfin

end RHTower

namespace RHTower

/-- Pointwise finite comparison of the EM carrier and `gN` from its three visible pieces. -/
theorem emCarrier_gN_norm_le_of_components {M N : ℕ} {z : ℂ}
    {δD δP δχ δ : ℝ}
    (hD : ‖dirichletPoly M z - dirichletPoly N z‖ ≤ δD)
    (hP : ‖emPole M z‖ ≤ δP)
    (hχ : ‖zetaChi z * dirichletPoly N (1 - z)‖ ≤ δχ)
    (hδ : δD + δP + δχ ≤ δ) :
    ‖emCarrier M z - gN N z‖ ≤ δ := by
  have hshape : emCarrier M z - gN N z =
      (dirichletPoly M z - dirichletPoly N z) + emPole M z -
        zetaChi z * dirichletPoly N (1 - z) := by
    simp [emCarrier, emPole, gN, chiSymmetrize]
    ring
  rw [hshape]
  have htri1 : ‖(dirichletPoly M z - dirichletPoly N z) + emPole M z -
        zetaChi z * dirichletPoly N (1 - z)‖
      ≤ ‖(dirichletPoly M z - dirichletPoly N z) + emPole M z‖ +
          ‖zetaChi z * dirichletPoly N (1 - z)‖ := by
    simpa [sub_eq_add_neg, norm_neg] using
      norm_add_le ((dirichletPoly M z - dirichletPoly N z) + emPole M z)
        (-(zetaChi z * dirichletPoly N (1 - z)))
  have htri2 : ‖(dirichletPoly M z - dirichletPoly N z) + emPole M z‖
      ≤ ‖dirichletPoly M z - dirichletPoly N z‖ + ‖emPole M z‖ :=
    norm_add_le (dirichletPoly M z - dirichletPoly N z) (emPole M z)
  linarith

/-- Set-level finite comparison of the EM carrier and `gN` from three finite budgets. -/
theorem emCarrier_gN_close_on_of_components {S : Set ℂ} {M N : ℕ}
    {δD δP δχ δ : ℝ}
    (hD : ∀ z ∈ S, ‖dirichletPoly M z - dirichletPoly N z‖ ≤ δD)
    (hP : ∀ z ∈ S, ‖emPole M z‖ ≤ δP)
    (hχ : ∀ z ∈ S, ‖zetaChi z * dirichletPoly N (1 - z)‖ ≤ δχ)
    (hδ : δD + δP + δχ ≤ δ) :
    ∀ z ∈ S, ‖emCarrier M z - gN N z‖ ≤ δ := by
  intro z hz
  exact emCarrier_gN_norm_le_of_components
    (hD z hz) (hP z hz) (hχ z hz) hδ

end RHTower

namespace RHTower

open Complex Filter Topology

/-- Uniform scalar bound for the Euler-Maclaurin pole term on a critical-line disk.
If `z` lies in the radius-`RJ` disk about `1/2 + iτ` and `RJ < 1/2`, then the pole
is bounded by the explicit numerator budget over the distance gap to `1`. -/
theorem emPole_norm_le_line_closedBall {M : ℕ} {τ RJ : ℝ}
    (hM : 1 ≤ M) (hRJ : RJ < 1 / 2) :
    ∀ z ∈ Metric.closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖emPole M z‖ ≤ (M : ℝ) ^ (1 / 2 + RJ) / (1 / 2 - RJ) := by
  intro z hz
  have hdist : ‖z - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤ RJ := by
    rw [← dist_eq_norm]
    exact Metric.mem_closedBall.mp hz
  have hre_abs : |z.re - 1 / 2| ≤ RJ := by
    calc |z.re - 1 / 2|
        = |(z - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)).re| := by simp [sub_re]
      _ ≤ ‖z - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := Complex.abs_re_le_norm _
      _ ≤ RJ := hdist
  have hre_ge : 1 / 2 - RJ ≤ z.re := by
    have := (abs_le.mp hre_abs).1
    linarith
  have hre_le : z.re ≤ 1 / 2 + RJ := by
    have := (abs_le.mp hre_abs).2
    linarith
  have hden0 : 0 < 1 / 2 - RJ := by linarith
  have hzre_lt1 : z.re < 1 := by linarith
  have hdist_one_re : 1 - z.re ≤ ‖z - 1‖ := by
    calc 1 - z.re
        = |(z - 1).re| := by
          have hnonpos : (z - 1).re ≤ 0 := by simp [sub_re]; linarith
          rw [abs_of_nonpos hnonpos]
          simp [sub_re]
      _ ≤ ‖z - 1‖ := Complex.abs_re_le_norm _
  have hdenle : 1 / 2 - RJ ≤ ‖z - 1‖ := by linarith
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hM
  have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hpow_eq : ‖(M : ℂ) ^ (1 - z)‖ = (M : ℝ) ^ (1 - z).re := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hMpos (1 - z)
  have hexp_le : (1 - z).re ≤ 1 / 2 + RJ := by
    simp [sub_re]
    linarith
  have hpow_le : ‖(M : ℂ) ^ (1 - z)‖ ≤ (M : ℝ) ^ (1 / 2 + RJ) := by
    rw [hpow_eq]
    exact Real.rpow_le_rpow_of_exponent_le hMone hexp_le
  have hnum_nonneg : 0 ≤ (M : ℝ) ^ (1 / 2 + RJ) := Real.rpow_nonneg hMpos.le _
  calc ‖emPole M z‖
      = ‖(M : ℂ) ^ (1 - z) / (z - 1)‖ := by rfl
    _ = ‖(M : ℂ) ^ (1 - z)‖ / ‖z - 1‖ := norm_div _ _
    _ ≤ (M : ℝ) ^ (1 / 2 + RJ) / ‖z - 1‖ := by
      exact div_le_div_of_nonneg_right hpow_le (norm_nonneg _)
    _ ≤ (M : ℝ) ^ (1 / 2 + RJ) / (1 / 2 - RJ) := by
      exact div_le_div_of_nonneg_left hnum_nonneg hden0 hdenle

/-- A scalar center-height budget controls the Euler-Maclaurin remainder majorant on the whole
critical-line disk. -/
theorem em_remainder_norm_le_line_closedBall_of_center_bound {M : ℕ} {τ RJ ε₁ : ℝ}
    (hM : 1 ≤ M) (hRJ12 : RJ < 1 / 2)
    (hbudget : (‖(((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ + RJ) *
      (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ) ≤ ε₁) :
    ∀ z ∈ Metric.closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁ := by
  intro z hz
  set c : ℂ := ((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I with hc
  have hdist : ‖z - c‖ ≤ RJ := by
    rw [← dist_eq_norm]
    simpa [c] using Metric.mem_closedBall.mp hz
  have hRJnonneg : 0 ≤ RJ := le_trans (norm_nonneg (z - c)) hdist
  have hre_abs : |z.re - 1 / 2| ≤ RJ := by
    calc |z.re - 1 / 2|
        = |(z - c).re| := by simp [c, sub_re]
      _ ≤ ‖z - c‖ := Complex.abs_re_le_norm _
      _ ≤ RJ := hdist
  have hre_ge : 1 / 2 - RJ ≤ z.re := by
    have := (abs_le.mp hre_abs).1
    linarith
  have hre_pos : 0 < z.re := by linarith
  have hden0 : 0 < 1 / 2 - RJ := by linarith
  have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hpow_le : (M : ℝ) ^ (-z.re) ≤ (M : ℝ) ^ (-(1 / 2 - RJ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hMone
    linarith
  have hpow_nonneg : 0 ≤ (M : ℝ) ^ (-z.re) := Real.rpow_nonneg (Nat.cast_nonneg M) _
  have hpowB_nonneg : 0 ≤ (M : ℝ) ^ (-(1 / 2 - RJ)) :=
    Real.rpow_nonneg (Nat.cast_nonneg M) _
  have hnorm_le : ‖z‖ ≤ ‖c‖ + RJ := by
    calc ‖z‖ = ‖(z - c) + c‖ := by ring_nf
      _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ RJ + ‖c‖ := add_le_add hdist le_rfl
      _ = ‖c‖ + RJ := by ring
  have hcenter_nonneg : 0 ≤ ‖c‖ + RJ := add_nonneg (norm_nonneg c) hRJnonneg
  have hnum_le : ‖z‖ * (M : ℝ) ^ (-z.re) ≤
      (‖c‖ + RJ) * (M : ℝ) ^ (-(1 / 2 - RJ)) := by
    exact mul_le_mul hnorm_le hpow_le hpow_nonneg hcenter_nonneg
  have hbig_nonneg : 0 ≤ (‖c‖ + RJ) * (M : ℝ) ^ (-(1 / 2 - RJ)) := by
    exact mul_nonneg hcenter_nonneg hpowB_nonneg
  have hstep1 : ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤
      ((‖c‖ + RJ) * (M : ℝ) ^ (-(1 / 2 - RJ))) / z.re := by
    exact div_le_div_of_nonneg_right hnum_le hre_pos.le
  have hstep2 : ((‖c‖ + RJ) * (M : ℝ) ^ (-(1 / 2 - RJ))) / z.re ≤
      ((‖c‖ + RJ) * (M : ℝ) ^ (-(1 / 2 - RJ))) / (1 / 2 - RJ) := by
    exact div_le_div_of_nonneg_left hbig_nonneg hden0 hre_ge
  calc ‖z‖ * (M : ℝ) ^ (-z.re) / z.re
      ≤ ((‖c‖ + RJ) * (M : ℝ) ^ (-(1 / 2 - RJ))) / z.re := hstep1
    _ ≤ ((‖c‖ + RJ) * (M : ℝ) ^ (-(1 / 2 - RJ))) / (1 / 2 - RJ) := hstep2
    _ ≤ ε₁ := by simpa [c, mul_div_assoc] using hbudget

end RHTower

namespace RHTower

open Complex Filter Topology

/-- Dirichlet-polynomial drift is bounded by the finite tail on any half-plane `σ ≤ Re z`. -/
theorem dirichletPoly_sub_norm_le_tail_of_re_ge {N M : ℕ} (hNM : N ≤ M)
    {σ : ℝ} {z : ℂ} (hzre : σ ≤ z.re) :
    ‖dirichletPoly M z - dirichletPoly N z‖ ≤
      ∑ i ∈ Finset.Ico N M, (((i + 1 : ℕ) : ℝ) ^ (-σ)) := by
  let f : ℕ → ℂ := fun i => ((i + 1 : ℕ) : ℂ) ^ (-z)
  have hsplit := Finset.sum_range_add_sum_Ico f hNM
  have hdiff : dirichletPoly M z - dirichletPoly N z = ∑ i ∈ Finset.Ico N M, f i := by
    rw [dirichletPoly_eq_sum_range M z, dirichletPoly_eq_sum_range N z]
    change (∑ i ∈ Finset.range M, f i) - (∑ i ∈ Finset.range N, f i) =
      ∑ i ∈ Finset.Ico N M, f i
    rw [← hsplit]
    abel
  rw [hdiff]
  calc ‖∑ i ∈ Finset.Ico N M, f i‖
      ≤ ∑ i ∈ Finset.Ico N M, ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.Ico N M, (((i + 1 : ℕ) : ℝ) ^ (-σ)) := by
      apply Finset.sum_le_sum
      intro i _
      have hi1 : (1 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos i
      have hipos : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hi1
      have hnorm : ‖f i‖ = ((i + 1 : ℕ) : ℝ) ^ (-z).re := by
        dsimp [f]
        simpa using Complex.norm_cpow_eq_rpow_re_of_pos hipos (-z)
      rw [hnorm]
      have hexp : (-z).re ≤ -σ := by
        simp
        linarith
      exact Real.rpow_le_rpow_of_exponent_le hi1 hexp

/-- Uniform finite-tail drift bound for Dirichlet polynomials on a critical-line disk. -/
theorem dirichletPoly_sub_norm_le_tail_line_closedBall {N M : ℕ} {τ RJ : ℝ}
    (hNM : N ≤ M) :
    ∀ z ∈ Metric.closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖dirichletPoly M z - dirichletPoly N z‖ ≤
        ∑ i ∈ Finset.Ico N M, (((i + 1 : ℕ) : ℝ) ^ (-(1 / 2 - RJ))) := by
  intro z hz
  have hdist : ‖z - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤ RJ := by
    rw [← dist_eq_norm]
    exact Metric.mem_closedBall.mp hz
  have hre_abs : |z.re - 1 / 2| ≤ RJ := by
    calc |z.re - 1 / 2|
        = |(z - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)).re| := by simp [sub_re]
      _ ≤ ‖z - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := Complex.abs_re_le_norm _
      _ ≤ RJ := hdist
  have hzre : 1 / 2 - RJ ≤ z.re := by
    have := (abs_le.mp hre_abs).1
    linarith
  exact dirichletPoly_sub_norm_le_tail_of_re_ge (N := N) (M := M) hNM hzre

end RHTower

namespace RHTower

open Complex Filter Topology

/-- Reflected Dirichlet polynomial bound from an upper bound on `Re z`. -/
theorem dirichletPoly_one_sub_norm_le_sum_of_re_le {N : ℕ} {σ : ℝ} {z : ℂ}
    (hzre : z.re ≤ σ) :
    ‖dirichletPoly N (1 - z)‖ ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (σ - 1) := by
  rw [dirichletPoly]
  calc ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-(1 - z))‖
      ≤ ∑ n ∈ Finset.Icc 1 N, ‖(n : ℂ) ^ (-(1 - z))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (σ - 1) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
      have hnorm : ‖(n : ℂ) ^ (-(1 - z))‖ = (n : ℝ) ^ (-(1 - z)).re := by
        simpa using Complex.norm_cpow_eq_rpow_re_of_pos hnpos (-(1 - z))
      rw [hnorm]
      have hexp : (-(1 - z)).re ≤ σ - 1 := by
        simp [sub_re]
        linarith
      exact Real.rpow_le_rpow_of_exponent_le hn1 hexp

/-- Reflected Dirichlet polynomial bound on a critical-line boundary circle. -/
theorem dirichletPoly_one_sub_norm_le_sum_line_sphere {N : ℕ} {τ RJ : ℝ} :
    ∀ z ∈ Metric.sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖dirichletPoly N (1 - z)‖ ≤
        ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 - RJ)) := by
  intro z hz
  have hdist : ‖z - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ = RJ := by
    rw [← dist_eq_norm]
    exact Metric.mem_sphere.mp hz
  have hre_abs : |z.re - 1 / 2| ≤ RJ := by
    calc |z.re - 1 / 2|
        = |(z - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)).re| := by simp [sub_re]
      _ ≤ ‖z - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := Complex.abs_re_le_norm _
      _ = RJ := hdist
  have hzre : z.re ≤ 1 / 2 + RJ := by
    have := (abs_le.mp hre_abs).2
    linarith
  have h := dirichletPoly_one_sub_norm_le_sum_of_re_le (N := N)
    (σ := 1 / 2 + RJ) (z := z) hzre
  convert h using 1
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  ring

/-- Reflected χ-product circle budget from a χ envelope and the explicit reflected finite sum. -/
theorem reflected_chi_norm_le_chi_bound_line_sphere {N : ℕ} {τ RJ χB δχ : ℝ} {z : ℂ}
    (hχ : ‖zetaChi z‖ ≤ χB)
    (hz : z ∈ Metric.sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ)
    (hbudget : χB * (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 - RJ))) ≤ δχ) :
    ‖zetaChi z * dirichletPoly N (1 - z)‖ ≤ δχ := by
  have hD := dirichletPoly_one_sub_norm_le_sum_line_sphere (N := N) (τ := τ) (RJ := RJ) z hz
  have hχB0 : 0 ≤ χB := le_trans (norm_nonneg _) hχ
  calc ‖zetaChi z * dirichletPoly N (1 - z)‖
      = ‖zetaChi z‖ * ‖dirichletPoly N (1 - z)‖ := norm_mul _ _
    _ ≤ χB * (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 - RJ))) := by
      exact mul_le_mul hχ hD (norm_nonneg _) hχB0
    _ ≤ δχ := hbudget

end RHTower
