import Mathlib

/-!
# Quasinilpotence of a compact filtration-lowering operator

If a bounded operator `B` is annihilated by each projection block past the nilpotence index —
`B^k P_n = 0` for `k ≥ n+1` — then past that index the powers factor through the complementary
block:

```text
B^{m+1} = B^m · ((1 − P_n) B),      m ≥ n + 1,
```

so `‖B^{n+1+j}‖ ≤ ‖B^{n+1}‖ · ‖(1 − P_n) B‖^j`.  Every spectral point is therefore bounded by
`‖(1 − P_n) B‖`, and if those shrink to zero the spectrum collapses to `{0}`.

Compactness supplies the shrinking: `tendsto_norm_comp_of_isCompactOperator` shows that an
equibounded sequence of operators tending to zero pointwise tends to zero *in norm* after
composition with a compact operator, because the image of the unit ball is totally bounded.

This avoids Riesz eigenvalue-perturbation theory entirely.
-/

noncomputable section

open Filter Topology Metric

namespace GaloisForLFunctions.HTGeometry.QuasinilpotentLowering

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- One step of the triangular recursion: past the nilpotence index the projection block drops
out. -/
theorem pow_succ_eq_mul_shrink (B : H →L[ℂ] H) (P : H →L[ℂ] H) {m : ℕ}
    (hnil : (B ^ m) * P = 0) : B ^ (m + 1) = (B ^ m) * ((1 - P) * B) := by
  have h : (B ^ m) * ((1 - P) * B) = (B ^ m) * B - ((B ^ m) * P) * B := by noncomm_ring
  rw [h, hnil, zero_mul, sub_zero, pow_succ]

/-- Geometric decay of the operator powers. -/
theorem norm_pow_le_geometric (B : H →L[ℂ] H) (P : ℕ → H →L[ℂ] H) (n : ℕ)
    (hnil : ∀ k : ℕ, n + 1 ≤ k → (B ^ k) * (P n) = 0) (j : ℕ) :
    ‖B ^ (n + 1 + j)‖ ≤ ‖B ^ (n + 1)‖ * ‖(1 - P n) * B‖ ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hstep : B ^ (n + 1 + j + 1) = (B ^ (n + 1 + j)) * ((1 - P n) * B) :=
        pow_succ_eq_mul_shrink B (P n) (hnil (n + 1 + j) (by omega))
      have hle : ‖B ^ (n + 1 + j + 1)‖ ≤ ‖B ^ (n + 1 + j)‖ * ‖(1 - P n) * B‖ := by
        rw [hstep]
        exact norm_mul_le _ _
      calc ‖B ^ (n + 1 + (j + 1))‖ = ‖B ^ (n + 1 + j + 1)‖ := by
            rw [show n + 1 + (j + 1) = n + 1 + j + 1 from by omega]
        _ ≤ ‖B ^ (n + 1 + j)‖ * ‖(1 - P n) * B‖ := hle
        _ ≤ (‖B ^ (n + 1)‖ * ‖(1 - P n) * B‖ ^ j) * ‖(1 - P n) * B‖ :=
            mul_le_mul_of_nonneg_right ih (norm_nonneg _)
        _ = ‖B ^ (n + 1)‖ * ‖(1 - P n) * B‖ ^ (j + 1) := by ring

variable [CompleteSpace H] [Nontrivial H]

/-- Every spectral point is bounded by each shrink constant. -/
theorem norm_le_shrink_of_mem_spectrum (B : H →L[ℂ] H) (P : ℕ → H →L[ℂ] H) (n : ℕ)
    (hnil : ∀ k : ℕ, n + 1 ≤ k → (B ^ k) * (P n) = 0)
    {lam : ℂ} (hlam : lam ∈ spectrum ℂ B) : ‖lam‖ ≤ ‖(1 - P n) * B‖ := by
  by_contra hcon
  rw [not_le] at hcon
  set eta : ℝ := ‖(1 - P n) * B‖ with heta
  have hetann : 0 ≤ eta := norm_nonneg _
  have hlampos : 0 < ‖lam‖ := lt_of_le_of_lt hetann hcon
  have hkey : ∀ j : ℕ, ‖lam‖ ^ (n + 1 + j) ≤ ‖B ^ (n + 1)‖ * eta ^ j := by
    intro j
    have h1 : lam ^ (n + 1 + j) ∈ spectrum ℂ (B ^ (n + 1 + j)) :=
      spectrum.pow_mem_pow B (n + 1 + j) hlam
    have h2 : ‖lam ^ (n + 1 + j)‖ ≤ ‖B ^ (n + 1 + j)‖ := spectrum.norm_le_norm_of_mem h1
    rw [norm_pow] at h2
    exact le_trans h2 (norm_pow_le_geometric B P n hnil j)
  rcases eq_or_lt_of_le hetann with heta0 | hetapos
  · have h1 := hkey 1
    rw [← heta0] at h1
    simp only [pow_one, mul_zero] at h1
    have h2 : (0 : ℝ) < ‖lam‖ ^ (n + 1 + 1) := by positivity
    linarith
  · have hratio : 1 < ‖lam‖ / eta := (one_lt_div hetapos).mpr hcon
    have hdiv : ∀ j : ℕ, (‖lam‖ / eta) ^ j ≤ ‖B ^ (n + 1)‖ / ‖lam‖ ^ (n + 1) := by
      intro j
      have h1 := hkey j
      rw [pow_add] at h1
      have h3 : ‖lam‖ ^ j ≤ (‖B ^ (n + 1)‖ / ‖lam‖ ^ (n + 1)) * eta ^ j := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        calc ‖lam‖ ^ j * ‖lam‖ ^ (n + 1) = ‖lam‖ ^ (n + 1) * ‖lam‖ ^ j := by ring
          _ ≤ ‖B ^ (n + 1)‖ * eta ^ j := h1
      rw [div_pow, div_le_iff₀ (by positivity)]
      exact h3
    have hdiverge : Tendsto (fun j : ℕ => (‖lam‖ / eta) ^ j) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hratio
    obtain ⟨j, hj⟩ := (hdiverge.eventually_gt_atTop
      (‖B ^ (n + 1)‖ / ‖lam‖ ^ (n + 1))).exists
    exact absurd (hdiv j) (not_le.mpr hj)

/-- **Quasinilpotence.**  A bounded operator that is nilpotent on each projection block and whose
complementary blocks shrink it to zero has spectrum `{0}`. -/
theorem eq_zero_of_mem_spectrum (B : H →L[ℂ] H) (P : ℕ → H →L[ℂ] H)
    (hnil : ∀ n k : ℕ, n + 1 ≤ k → (B ^ k) * (P n) = 0)
    (hshrink : Tendsto (fun n => ‖(1 - P n) * B‖) atTop (𝓝 0))
    {lam : ℂ} (hlam : lam ∈ spectrum ℂ B) : lam = 0 := by
  have hle : ‖lam‖ ≤ 0 :=
    ge_of_tendsto hshrink
      (Filter.Eventually.of_forall
        (fun n => norm_le_shrink_of_mem_spectrum B P n (hnil n) hlam))
  rw [← norm_eq_zero]
  exact le_antisymm hle (norm_nonneg _)

/-! ## Compactness supplies the shrinking hypothesis -/

/-- **Uniform smallness on the compact image.**  An equibounded sequence of operators tending to
zero pointwise tends to zero in norm after composition with a compact operator. -/
theorem tendsto_norm_comp_of_isCompactOperator (Q : ℕ → H →L[ℂ] H) (hbdd : ∀ n, ‖Q n‖ ≤ 1)
    (hptw : ∀ x : H, Tendsto (fun n => Q n x) atTop (𝓝 0))
    (B : H →L[ℂ] H) (hB : IsCompactOperator B) :
    Tendsto (fun n => ‖(Q n) * B‖) atTop (𝓝 0) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  set S : Set H := closure (B '' Metric.closedBall 0 1) with hS
  have hScompact : IsCompact S := hB.isCompact_closure_image_closedBall 1
  have hStb : TotallyBounded S := hScompact.totallyBounded
  obtain ⟨t, htfin, htcover⟩ :=
    (Metric.totallyBounded_iff.mp hStb) (ε / 3) (by linarith)
  have hfin : ∀ᶠ n in atTop, ∀ y ∈ htfin.toFinset, ‖Q n y‖ < ε / 3 := by
    rw [Filter.eventually_all_finset]
    intro y _
    have hy := (hptw y).norm
    rw [norm_zero] at hy
    exact hy.eventually_lt_const (by linarith)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hfin
  refine ⟨N, fun n hn => ?_⟩
  have hbound : ‖(Q n) * B‖ ≤ 2 * ε / 3 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) (fun x => ?_)
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hxc : ((‖x‖ : ℂ)) ≠ 0 := by
        simpa using hxpos.ne'
      set u : H := ((‖x‖ : ℂ))⁻¹ • x with hu
      have hunorm : ‖u‖ = 1 := by
        rw [hu, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hxpos.ne']
      have hxu : ((‖x‖ : ℂ)) • u = x := by
        rw [hu, smul_smul, mul_inv_cancel₀ hxc, one_smul]
      have hmem : B u ∈ S := by
        refine subset_closure ⟨u, ?_, rfl⟩
        simp [Metric.mem_closedBall, hunorm]
      obtain ⟨y, hy, hdist⟩ := Set.mem_iUnion₂.mp (htcover hmem)
      have hyfin : y ∈ htfin.toFinset := htfin.mem_toFinset.mpr hy
      have h1 : ‖Q n (B u)‖ ≤ ‖Q n (B u - y)‖ + ‖Q n y‖ := by
        have : Q n (B u) = Q n (B u - y) + Q n y := by
          rw [← map_add]
          congr 1
          abel
        rw [this]
        exact norm_add_le _ _
      have h2 : ‖Q n (B u - y)‖ ≤ ε / 3 := by
        refine le_trans ((Q n).le_opNorm _) ?_
        have h3 : ‖B u - y‖ < ε / 3 := by
          simpa [Metric.mem_ball, dist_eq_norm] using hdist
        calc ‖Q n‖ * ‖B u - y‖ ≤ 1 * ‖B u - y‖ :=
              mul_le_mul_of_nonneg_right (hbdd n) (norm_nonneg _)
          _ = ‖B u - y‖ := one_mul _
          _ ≤ ε / 3 := h3.le
      have h4 : ‖Q n y‖ < ε / 3 := hN n hn y hyfin
      have hu' : ‖(Q n) (B u)‖ ≤ 2 * ε / 3 := by linarith
      have h5 : (Q n) (B (((‖x‖ : ℂ)) • u)) = ((‖x‖ : ℂ)) • ((Q n) (B u)) := by
        rw [map_smul, map_smul]
      have hscale : ((Q n) * B) x = ((‖x‖ : ℂ)) • ((Q n) (B u)) := by
        rw [ContinuousLinearMap.mul_apply, ← h5, hxu]
      rw [hscale, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)]
      calc ‖x‖ * ‖(Q n) (B u)‖ ≤ ‖x‖ * (2 * ε / 3) :=
            mul_le_mul_of_nonneg_left hu' (norm_nonneg _)
        _ = 2 * ε / 3 * ‖x‖ := by ring
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith

/-- **Quasinilpotence of a compact strictly lowering extension.**  This is the card's step: the
truncations are nilpotent, the complementary blocks shrink because the operator is compact, and the
spectrum collapses to `{0}`. -/
theorem eq_zero_of_mem_spectrum_of_isCompactOperator (B : H →L[ℂ] H) (P : ℕ → H →L[ℂ] H)
    (hbdd : ∀ n, ‖1 - P n‖ ≤ 1)
    (hptw : ∀ x : H, Tendsto (fun n => (1 - P n) x) atTop (𝓝 0))
    (hnil : ∀ n k : ℕ, n + 1 ≤ k → (B ^ k) * (P n) = 0)
    (hB : IsCompactOperator B) {lam : ℂ} (hlam : lam ∈ spectrum ℂ B) : lam = 0 :=
  eq_zero_of_mem_spectrum B P hnil
    (tendsto_norm_comp_of_isCompactOperator (fun n => 1 - P n) hbdd hptw B hB) hlam

end GaloisForLFunctions.HTGeometry.QuasinilpotentLowering
