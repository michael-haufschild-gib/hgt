import GaloisForLFunctions.HTGeometry.CanonicalThermalReesFormationField
import GaloisForLFunctions.RHTower.WeightedCodiagonalDichotomy

/-!
# Canonical formation-graph codiagonal topology fracture

Constant codiagonal recovery is closable in the base `ℓ²` gauge exactly when its coefficient
vanishes. The same recovery is bounded for every coefficient after canonical `(N+1)` formation
loading, because the inverse-grade weights `(n+1)⁻¹` lie in `ℓ²`.

Thus compact formation-resolvent properness cannot itself select the zero coefficient: changing to
the formation graph topology regularizes precisely the response whose base-gauge nonclosability is
the shell Ward selector. This is the Lean certificate for ULF-TAFM-29.
-/

open scoped BigOperators ENNReal NNReal

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem natCast_add_one_ne_zero (n : ℕ) : (n : ℂ) + 1 ≠ 0 := by
  exact_mod_cast Nat.succ_ne_zero n

/-- Multiply grade `n` by `n+1` on the finite formation core. -/
def formationGraphLoad (x : ℕ →₀ ℂ) : ℕ →₀ ℂ :=
  x.sum fun n z => Finsupp.single n (((n : ℂ) + 1) * z)

@[simp] theorem formationGraphLoad_apply (x : ℕ →₀ ℂ) (n : ℕ) :
    formationGraphLoad x n = ((n : ℂ) + 1) * x n := by
  classical
  simp [formationGraphLoad, Finsupp.sum, Finsupp.single_apply,
    natCast_add_one_ne_zero]

theorem support_formationGraphLoad (x : ℕ →₀ ℂ) :
    (formationGraphLoad x).support = x.support := by
  ext n
  simp [Finsupp.mem_support_iff, formationGraphLoad_apply,
    natCast_add_one_ne_zero]

/-- The canonical inverse-grade weights are square summable. -/
theorem summable_sq_norm_formationResolventMultiplier :
    Summable fun n : ℕ => ‖formationResolventMultiplier n‖ ^ 2 := by
  have h := (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
  convert h using 1
  funext n
  rw [formationResolventMultiplier, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (by positivity))]
  norm_num [Real.rpow_two]

/-- Unit codiagonal recovery factors through bounded inverse-grade recovery after formation load. -/
theorem inverseGradeCodiagonal_after_formationGraphLoad (x : ℕ →₀ ℂ) :
    RHTower.codiagCLM summable_sq_norm_formationResolventMultiplier
        (RHTower.codiagEmbed (formationGraphLoad x)) =
      RHTower.codiag (fun _ : ℕ => (1 : ℂ)) x := by
  rw [RHTower.codiagCLM_codiagEmbed]
  rw [RHTower.codiag_apply, RHTower.codiag_apply]
  rw [support_formationGraphLoad]
  apply Finset.sum_congr rfl
  intro n hn
  rw [formationGraphLoad_apply]
  rw [show formationResolventMultiplier n = ((n : ℂ) + 1)⁻¹ by
    simp [formationResolventMultiplier]]
  simp only [smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (natCast_add_one_ne_zero n), one_mul]

/-- Canonical formation resolvent exactly inverts formation loading on the finite core. -/
theorem formationResolvent_after_formationGraphLoad (x : ℕ →₀ ℂ) :
    formationResolvent (RHTower.codiagEmbed (formationGraphLoad x)) =
      RHTower.codiagEmbed x := by
  ext n
  rw [formationResolvent_apply]
  simp only [RHTower.codiagEmbed_apply, formationGraphLoad_apply]
  rw [show formationResolventMultiplier n = ((n : ℂ) + 1)⁻¹ by
    simp [formationResolventMultiplier]]
  rw [← mul_assoc, inv_mul_cancel₀ (natCast_add_one_ne_zero n), one_mul]

/-- Bounded recovery of a constant response in the canonical formation graph gauge. -/
def formationGraphRecovery (c : ℂ) : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] ℂ :=
  c • RHTower.codiagCLM summable_sq_norm_formationResolventMultiplier

theorem formationGraphRecovery_after_load (c : ℂ) (x : ℕ →₀ ℂ) :
    formationGraphRecovery c (RHTower.codiagEmbed (formationGraphLoad x)) =
      RHTower.codiag (fun _ : ℕ => c) x := by
  rw [formationGraphRecovery, smul_apply,
    inverseGradeCodiagonal_after_formationGraphLoad]
  rw [RHTower.codiag_apply, RHTower.codiag_apply]
  simp only [smul_eq_mul]
  rw [Finset.mul_sum]
  simp

theorem not_summable_sq_norm_const (c : ℂ) (hc : c ≠ 0) :
    ¬ Summable fun _ : ℕ => ‖c‖ ^ 2 := by
  intro hs
  have hzero := hs.tendsto_atTop_zero
  have hconst : Tendsto (fun _ : ℕ => ‖c‖ ^ 2) atTop (nhds (‖c‖ ^ 2)) :=
    tendsto_const_nhds
  have : ‖c‖ ^ 2 = 0 := tendsto_nhds_unique hconst hzero
  exact hc (norm_eq_zero.mp (sq_eq_zero_iff.mp this))

/-- In the base Hilbert gauge, constant recovery is closable exactly at zero coefficient. -/
theorem constantCodiagonal_closable_iff (c : ℂ) :
    RHTower.IsSequentiallyClosableBetween
        ((RHTower.codiag (H := ℂ) (fun _ => c)).restrictScalars ℝ)
        ((RHTower.codiagEmbed (H := ℂ)).restrictScalars ℝ) ↔
      c = 0 := by
  constructor
  · intro hclose
    by_contra hc
    exact (RHTower.not_isSequentiallyClosableBetween_codiag
      (not_summable_sq_norm_const c hc) hc) hclose
  · rintro rfl
    intro u hu y hy
    have hzero : Tendsto
        (fun n => ((RHTower.codiag (H := ℂ) (fun _ => (0 : ℂ))).restrictScalars ℝ) (u n))
        atTop (nhds 0) := by
      convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0)) using 1
      funext n
      simp [RHTower.codiag_apply]
    exact tendsto_nhds_unique hy hzero

/-- **Topology-fracture law.** For every coefficient, base closability still selects zero, while
the canonical formation graph admits a bounded recovery of that same finite-core response. -/
theorem formationGraphTopologyFracture :
    ∀ c : ℂ,
      (RHTower.IsSequentiallyClosableBetween
          ((RHTower.codiag (H := ℂ) (fun _ => c)).restrictScalars ℝ)
          ((RHTower.codiagEmbed (H := ℂ)).restrictScalars ℝ) ↔ c = 0) ∧
      ∃ T : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] ℂ,
        ∀ x : ℕ →₀ ℂ,
          T (RHTower.codiagEmbed (formationGraphLoad x)) =
            RHTower.codiag (fun _ : ℕ => c) x := by
  intro c
  exact ⟨constantCodiagonal_closable_iff c,
    ⟨formationGraphRecovery c, formationGraphRecovery_after_load c⟩⟩

end

end GaloisForLFunctions.HTGeometry
