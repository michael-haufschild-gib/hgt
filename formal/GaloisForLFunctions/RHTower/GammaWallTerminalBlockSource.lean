import GaloisForLFunctions.RHTower.SuzukiGammaWallCutoffCommutator

/-!
# `(15)`: a one-sided exponential source lies in the block class

The block norm weights the `m`-th unit block by `e^{max(0,-m)}`, so a two-sided wall must decay at
rate one to survive the negative ray — that is `gammaWallBlockNorm_lt_top_of_exp_wall`.  A source
*supported on a terminal ray*, however, has only finitely many nonzero negative blocks, and the
weight is bounded on them; the only constraint left is that the weight `e^{σL}` be beaten by the
source's own rate.  That is the case the differentiated analytic forcing produces: `χG′` and the
cutoff commutator both vanish below the transition region and decay at rate `δ` and `1` above it.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A block on which the weighted profile is bounded has block norm at most that bound. -/
theorem eLpNorm_unitBlock_le {σ : ℝ} {G : ℝ → X} {a C : ℝ}
    (hb : ∀ L ∈ Icc a (a + 1), ‖Real.exp (σ * L) • G L‖ ≤ C) :
    eLpNorm (fun L => Real.exp (σ * L) • G L) 2 (volume.restrict (Icc a (a + 1)))
      ≤ ENNReal.ofReal C := by
  have hae : ∀ᵐ L ∂(volume.restrict (Icc a (a + 1))),
      ‖Real.exp (σ * L) • G L‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with L hL
    exact hb L hL
  refine le_trans (eLpNorm_le_of_ae_bound hae) (le_of_eq ?_)
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

/-- A block below the support of the profile contributes nothing. -/
theorem eLpNorm_unitBlock_eq_zero {σ : ℝ} {G : ℝ → X} {a b : ℝ} (hab : a + 1 ≤ b)
    (hsupp : ∀ L : ℝ, L < b → G L = 0) :
    eLpNorm (fun L => Real.exp (σ * L) • G L) 2 (volume.restrict (Icc a (a + 1))) = 0 := by
  have hsub : ∀ᵐ L ∂(volume.restrict (Icc a (a + 1))), L < a + 1 := by
    rw [← Measure.restrict_congr_set (Ico_ae_eq_Icc (a := a) (b := a + 1))]
    filter_upwards [ae_restrict_mem measurableSet_Ico] with L hL
    exact hL.2
  have hae : (fun L => Real.exp (σ * L) • G L)
      =ᵐ[volume.restrict (Icc a (a + 1))] 0 := by
    filter_upwards [hsub] with L hL
    have hLb : L < b := lt_of_lt_of_le hL (by linarith)
    show Real.exp (σ * L) • G L = 0
    rw [hsupp L hLb, smul_zero]
  rw [eLpNorm_congr_ae hae, eLpNorm_zero]

set_option maxHeartbeats 1000000 in
/-- **`(15)`: a terminal-ray source with a rate above the weight is in the block class.** -/
theorem gammaWallBlockNorm_lt_top_of_terminal_exp_wall {σ δ b C : ℝ}
    (hσδ : σ < δ) (hC : 0 ≤ C) {G : ℝ → X}
    (hsupp : ∀ L : ℝ, L < b → G L = 0)
    (hwall : ∀ L : ℝ, ‖G L‖ ≤ C * Real.exp (-(δ * L))) :
    gammaWallBlockNorm σ G < ⊤ := by
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℤ, (m₀ : ℝ) ≤ b := ⟨⌊b⌋, Int.floor_le b⟩
  set A : ℝ := Real.exp (max 0 (-(m₀ : ℝ))) * C with hAdef
  have hA : 0 ≤ A := by positivity
  set ρ : ℝ := σ - δ with hρdef
  have hρneg : ρ < 0 := by rw [hρdef]; linarith
  set B : ℤ → ℝ≥0∞ := fun m => ENNReal.ofReal (Real.exp (max 0 (-(m : ℝ)))) *
    eLpNorm (fun L => Real.exp (σ * L) • G L) 2 (volume.restrict (Icc (m : ℝ) ((m : ℝ) + 1)))
    with hBdef
  -- every block obeys one of two bounds
  have hblock : ∀ m : ℤ, m₀ ≤ m → B m ≤ ENNReal.ofReal (A * Real.exp (ρ * (m : ℝ))) := by
    intro m hm
    have hmR : ((m₀ : ℝ)) ≤ (m : ℝ) := by exact_mod_cast hm
    have hw : Real.exp (max 0 (-(m : ℝ))) ≤ Real.exp (max 0 (-(m₀ : ℝ))) := by
      refine Real.exp_le_exp.mpr ?_
      exact max_le_max le_rfl (by linarith)
    have hbnd : ∀ L ∈ Icc (m : ℝ) ((m : ℝ) + 1),
        ‖Real.exp (σ * L) • G L‖ ≤ C * Real.exp (ρ * (m : ℝ)) := by
      intro L hL
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have h1 : ‖G L‖ ≤ C * Real.exp (-(δ * L)) := hwall L
      have h2 : Real.exp (σ * L) * (C * Real.exp (-(δ * L))) = C * Real.exp (ρ * L) := by
        have hexp : Real.exp (ρ * L) = Real.exp (σ * L) * Real.exp (-(δ * L)) := by
          rw [← Real.exp_add, hρdef]
          ring_nf
        rw [hexp]
        ring
      have h3 : Real.exp (ρ * L) ≤ Real.exp (ρ * (m : ℝ)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hL.1 hρneg.le)
      calc Real.exp (σ * L) * ‖G L‖
          ≤ Real.exp (σ * L) * (C * Real.exp (-(δ * L))) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = C * Real.exp (ρ * L) := h2
        _ ≤ C * Real.exp (ρ * (m : ℝ)) := mul_le_mul_of_nonneg_left h3 hC
    have hnorm := eLpNorm_unitBlock_le (σ := σ) (G := G) (a := (m : ℝ)) hbnd
    calc B m ≤ ENNReal.ofReal (Real.exp (max 0 (-(m₀ : ℝ))))
          * ENNReal.ofReal (C * Real.exp (ρ * (m : ℝ))) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hw) hnorm
      _ = ENNReal.ofReal (A * Real.exp (ρ * (m : ℝ))) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, hAdef]
          ring_nf
  have hzero : ∀ m : ℤ, m < m₀ → B m = 0 := by
    intro m hm
    have hmR : (m : ℝ) + 1 ≤ (m₀ : ℝ) := by
      have : m + 1 ≤ m₀ := hm
      exact_mod_cast this
    rw [hBdef]
    simp only
    rw [eLpNorm_unitBlock_eq_zero (σ := σ) (G := G) (a := (m : ℝ)) (b := b) (by linarith) hsupp,
      mul_zero]
  -- split the two-sided sum
  have hsplit : ∑' m : ℤ, B m = (∑' n : ℕ, B (n : ℤ)) + ∑' n : ℕ, B (-((n : ℤ) + 1)) :=
    tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable
  have hgeom : (∑' n : ℕ, B (n : ℤ)) < ⊤ := by
    have hle : ∀ n : ℕ, B (n : ℤ)
        ≤ ENNReal.ofReal A * ENNReal.ofReal (Real.exp ρ) ^ n := by
      intro n
      rcases le_or_gt m₀ (n : ℤ) with h | h
      · refine le_trans (hblock _ h) (le_of_eq ?_)
        rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← ENNReal.ofReal_mul hA]
        congr 1
        rw [← Real.exp_nat_mul]
        push_cast
        ring_nf
      · rw [hzero _ h]
        exact zero_le
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hle) ?_
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    have hlt : ENNReal.ofReal (Real.exp ρ) < 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.exp_pos _).le |>.mpr
        (Real.exp_lt_one_iff.mpr hρneg)
    exact ENNReal.inv_lt_top.mpr (tsub_pos_of_lt hlt)
  have hneg : (∑' n : ℕ, B (-((n : ℤ) + 1))) < ⊤ := by
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → -((n : ℤ) + 1) < m₀ := by
      obtain ⟨N, hN⟩ := exists_nat_gt (-(m₀ : ℝ))
      refine ⟨N, fun n hn => ?_⟩
      have h1 : (-(m₀ : ℝ)) < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hn)
      have : (-((n : ℤ) + 1) : ℝ) < (m₀ : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hfin : ∀ n : ℕ, N ≤ n → B (-((n : ℤ) + 1)) = 0 := fun n hn => hzero _ (hN n hn)
    have heq : (∑' n : ℕ, B (-((n : ℤ) + 1)))
        = ∑ n ∈ Finset.range N, B (-((n : ℤ) + 1)) := by
      refine tsum_eq_sum ?_
      intro n hn
      exact hfin n (by simpa using Nat.not_lt.mp (by simpa using hn))
    rw [heq]
    refine ENNReal.sum_lt_top.mpr fun n _ => ?_
    rcases le_or_gt m₀ (-((n : ℤ) + 1)) with h | h
    · exact lt_of_le_of_lt (hblock _ h) ENNReal.ofReal_lt_top
    · rw [hzero _ h]
      exact ENNReal.zero_lt_top
  rw [gammaWallBlockNorm, ← hBdef, hsplit]
  exact ENNReal.add_lt_top.mpr ⟨hgeom, hneg⟩

end GaloisForLFunctions.RHTower
