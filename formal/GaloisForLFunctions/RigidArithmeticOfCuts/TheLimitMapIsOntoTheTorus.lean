import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheHurwitzLimitSetEmbedsInTheGaugeTorus
import GaloisForLFunctions.«arithmetic-positivity-theory».SingleHeightPhaseSelectiveApertureAndPowerSaving
import GaloisForLFunctions.RHTower.LiouvilleDirichletSeries

/-!
# The limit map is onto the torus

A limit of vertical translates of `ζ` on `Re s > 1` determines a point of the gauge torus: a unitary
completely multiplicative `ω`. The map is **onto**: every such `ω` is the limit of phases along some
`τ_j → ∞`, by Kronecker, and then `ζ(s + iτ_j) → Σ ω(n) n^{-s}` on `Re s > 1`.

**The twin is a limit of translates.** Taking `ω = λ`,

`ζ(s + iτ_j) → Σ λ(n) n^{-s} = ζ(2s)/ζ(s)`  on `Re s > 1`.

So the Liouville twin lies in the closure of the translates of `ζ`. Any argument that is stable under limits of
translates on `Re s > 1` cannot tell `ζ` from its twin: this is the parity barrier in the language of transport.
A proof that uses recurrence must use information left of the abscissa of absolute convergence.
-/

open Finset Filter Topology Complex
open GaloisForLFunctions.ArithmeticAuxiliaryDynamics
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- A point of the gauge torus: a unitary completely multiplicative function on the positive integers. -/
structure IsGaugePoint (ω : ℕ → ℂ) : Prop where
  norm_one : ∀ n, 0 < n → ‖ω n‖ = 1
  map_mul : ∀ a b, 0 < a → 0 < b → ω (a * b) = ω a * ω b

theorem IsGaugePoint.map_one {ω : ℕ → ℂ} (h : IsGaugePoint ω) : ω 1 = 1 := by
  have h1 := h.map_mul 1 1 one_pos one_pos
  rw [mul_one] at h1
  have h0 : ω 1 ≠ 0 := by
    intro h0
    have := h.norm_one 1 one_pos
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  exact (mul_left_cancel₀ h0 (by rw [← h1, mul_one])).symm

/-- The phase at `n` as the conjugate of the Kronecker exponential. -/
private lemma phaseAt_eq_conj (ξ : ℝ) {p : ℕ} (hp : 0 < p) :
    phaseAt (2 * Real.pi * ξ) p =
      (starRingEnd ℂ) (cexp (2 * Real.pi * I * (ξ : ℂ) * (Real.log p : ℂ))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hne : ((p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  rw [phaseAt, Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hp0.le, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast
  ring

/-- **Kronecker on the torus.** Every gauge point is the limit of phases along some `τ_j → ∞`. -/
theorem exists_tendsto_phaseAt {ω : ℕ → ℂ} (hω : IsGaugePoint ω) :
    ∃ τ : ℕ → ℝ, Tendsto τ atTop atTop ∧
      ∀ n, 0 < n → Tendsto (fun j => phaseAt (τ j) n) atTop (𝓝 (ω n)) := by
  set θ : ℕ → ℝ := fun p => -Complex.arg (ω p) with hθ
  have hθval : ∀ p, 0 < p → cexp ((θ p : ℝ) * I) = (starRingEnd ℂ) (ω p) := by
    intro p hp
    have hn := hω.norm_one p hp
    have h1 : ω p = cexp ((Complex.arg (ω p) : ℝ) * I) := by
      have := Complex.norm_mul_exp_arg_mul_I (ω p)
      rw [hn] at this
      simpa using this.symm
    conv_rhs => rw [h1]
    rw [← Complex.exp_conj]
    congr 1
    simp only [hθ, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hex : ∀ j : ℕ, ∃ ξ : ℝ, (j : ℝ) < ξ ∧ ∀ p ∈ primeIndices j,
      ‖cexp (2 * Real.pi * I * ξ * Real.log p) - cexp ((θ p : ℝ) * I)‖ < 1 / ((j : ℝ) + 1) :=
    fun j => exists_gt_height_prime_phase_approx j θ (by positivity) (j : ℝ)
  choose ξ hξ₁ hξ₂ using hex
  refine ⟨fun j => 2 * Real.pi * ξ j, ?_, ?_⟩
  · refine Filter.Tendsto.const_mul_atTop Real.two_pi_pos ?_
    exact tendsto_atTop_mono (fun j => (hξ₁ j).le) tendsto_natCast_atTop_atTop
  · have hprime : ∀ p : ℕ, p.Prime →
        Tendsto (fun j => phaseAt (2 * Real.pi * ξ j) p) atTop (𝓝 (ω p)) := by
      intro p hp
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
        tendsto_one_div_add_atTop_nhds_zero_nat
      filter_upwards [eventually_ge_atTop p] with j hj
      have hmem : p ∈ primeIndices j := by
        refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.two_le, hj⟩, hp⟩
      have h := hξ₂ j p hmem
      rw [hθval p hp.pos] at h
      rw [phaseAt_eq_conj _ hp.pos]
      have hsub : (starRingEnd ℂ) (cexp (2 * Real.pi * I * (ξ j : ℂ) * (Real.log p : ℂ))) - ω p =
          (starRingEnd ℂ) (cexp (2 * Real.pi * I * (ξ j : ℂ) * (Real.log p : ℂ)) -
            (starRingEnd ℂ) (ω p)) := by
        rw [map_sub, Complex.conj_conj]
      rw [hsub, Complex.norm_conj]
      exact h.le
    intro n hn
    induction n using Nat.recOnMul with
    | zero => exact absurd hn (lt_irrefl 0)
    | one =>
      rw [hω.map_one]
      have : ∀ j, phaseAt (2 * Real.pi * ξ j) 1 = 1 := fun j => by simp [phaseAt]
      simp only [this]
      exact tendsto_const_nhds
    | prime p hp => exact hprime p hp
    | mul a b ha hb =>
      have ha0 : 0 < a := Nat.pos_of_mul_pos_right hn
      have hb0 : 0 < b := Nat.pos_of_mul_pos_left hn
      rw [hω.map_mul a b ha0 hb0]
      simp only [phaseAt_mul]
      exact (ha ha0).mul (hb hb0)

/-- **The limit map is onto the torus.** -/
theorem exists_tendsto_translate {ω : ℕ → ℂ} (hω : IsGaugePoint ω) :
    ∃ τ : ℕ → ℝ, Tendsto τ atTop atTop ∧ ∀ s : ℂ, 1 < s.re →
      Tendsto (fun j => riemannZeta (s + (τ j : ℂ) * I)) atTop
        (𝓝 (∑' n, zetaTerm s n * ω (n + 1))) := by
  obtain ⟨τ, hτ, hphase⟩ := exists_tendsto_phaseAt hω
  refine ⟨τ, hτ, fun s hs => ?_⟩
  have hfun : ∀ j, riemannZeta (s + (τ j : ℂ) * I) =
      ∑' n, zetaTerm s n * phaseAt (τ j) (n + 1) := by
    intro j
    have hre : 1 < (s + (τ j : ℂ) * I).re := by simpa using hs
    rw [← (hasSum_zetaTerm hre).tsum_eq]
    refine tsum_congr fun n => ?_
    rw [zetaTerm_add, phaseAt]
    push_cast
    rfl
  simp only [hfun]
  refine tendsto_tsum_of_dominated_convergence (summable_norm_zetaTerm hs) (fun n => ?_)
    (Eventually.of_forall fun j n => ?_)
  · exact (hphase (n + 1) (Nat.succ_pos n)).const_mul _
  · rw [norm_mul, norm_phaseAt (Nat.succ_pos n), mul_one]

/-- `λ` is a gauge point. -/
theorem isGaugePoint_liouville : IsGaugePoint fun n => RHTower.liouvilleC n where
  norm_one n hn := by
    rw [RHTower.liouvilleC_apply, ArithmeticFunction.liouville_apply hn.ne']
    push_cast
    rw [norm_pow]
    simp
  map_mul a b _ _ := RHTower.liouvilleC_mul a b

/-- **The twin is a limit of translates.** Along some `τ_j → ∞`, `ζ(s + iτ_j) → ζ(2s)/ζ(s)` on `Re s > 1`. -/
theorem exists_tendsto_translate_twin :
    ∃ τ : ℕ → ℝ, Tendsto τ atTop atTop ∧ ∀ s : ℂ, 1 < s.re →
      Tendsto (fun j => riemannZeta (s + (τ j : ℂ) * I)) atTop
        (𝓝 (riemannZeta (2 * s) / riemannZeta s)) := by
  obtain ⟨τ, hτ, h⟩ := exists_tendsto_translate isGaugePoint_liouville
  refine ⟨τ, hτ, fun s hs => ?_⟩
  have hval : ∑' n, zetaTerm s n * RHTower.liouvilleC (n + 1) =
      riemannZeta (2 * s) / riemannZeta s := by
    have hne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
    rw [eq_div_iff hne, ← RHTower.LSeries_liouvilleC_mul_riemannZeta hs]
    congr 1
    have hsm := RHTower.LSeriesSummable_liouvilleC hs
    rw [LSeries, hsm.tsum_eq_zero_add]
    simp only [LSeries.term_zero, zero_add]
    refine tsum_congr fun n => ?_
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), zetaTerm, Complex.cpow_neg, div_eq_mul_inv,
      mul_comm]
    push_cast
    rfl
  have := h s hs
  rwa [hval] at this

end GaloisForLFunctions.RigidArithmeticOfCuts
