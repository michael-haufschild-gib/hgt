import GaloisForLFunctions.HTGeometry.GomesTruncatedJetGaugeSplitting
import GaloisForLFunctions.HTGeometry.GomesTruncatedJetGaugeComparison

/-!
# The sharp boundary where the actual gauge group becomes scalar

Scalar matrices are detected intrinsically by the split character. The full
unipotent subgroup disappears exactly when the phase has no nonconstant
resonance below the horizon, including infinite-order and zero phases.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- A gauge transformation equals its observed scalar section exactly when its matrix is scalar. -/
theorem gomesTruncatedJetGaugeGroup_scalar_iff (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetGaugeGroup n z) :
    u = gomesTruncatedJetScalarSection n z (gomesTruncatedJetGaugeCharacter n z u) ↔
      u.val.val ∈ (⊥ : Subalgebra ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) := by
  constructor
  · intro h
    have hv := congrArg (fun v : gomesTruncatedJetGaugeGroup n z => v.val.val) h
    rw [hv, gomesTruncatedJetScalarSection_val]
    exact (⊥ : Subalgebra ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).algebraMap_mem _
  · intro h
    obtain ⟨c, hc⟩ := Algebra.mem_bot.mp h
    have hχ : (gomesTruncatedJetGaugeCharacter n z u).val = c := by
      rw [gomesTruncatedJetGaugeCharacter_val, ← hc]
      simp [Matrix.algebraMap_eq_diagonal]
    apply Subtype.ext
    apply Units.ext
    rw [gomesTruncatedJetScalarSection_val, hχ]
    exact hc.symm

/-- Scalar symmetries are exactly those with trivial normalized unipotent part. -/
theorem gomesTruncatedJetUnipotentPart_eq_one_iff (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetGaugeGroup n z) :
    gomesTruncatedJetUnipotentPart n z u = 1 ↔
      u.val.val ∈ (⊥ : Subalgebra ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) := by
  rw [← gomesTruncatedJetGaugeGroup_scalar_iff]
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    have he := congrArg (fun v =>
      gomesTruncatedJetScalarSection n z (gomesTruncatedJetGaugeCharacter n z u) * v) hv
    simpa only [gomesTruncatedJetUnipotentPart_val, OneMemClass.coe_one,
      mul_inv_cancel_left, mul_one] using he
  · intro h
    apply Subtype.ext
    change (gomesTruncatedJetScalarSection n z (gomesTruncatedJetGaugeCharacter n z u))⁻¹ * u = 1
    calc
      _ = (gomesTruncatedJetScalarSection n z (gomesTruncatedJetGaugeCharacter n z u))⁻¹ *
          (gomesTruncatedJetScalarSection n z (gomesTruncatedJetGaugeCharacter n z u)) :=
        congrArg (fun v => (gomesTruncatedJetScalarSection n z
          (gomesTruncatedJetGaugeCharacter n z u))⁻¹ * v) h
      _ = 1 := inv_mul_cancel _

/-- The zero-phase gauge group is exactly the scalar endpoint of every phase family. -/
theorem gomesTruncatedJetGaugeGroup_eq_zero_phase_iff (n : ℕ) (z : ℂ) :
    gomesTruncatedJetGaugeGroup n z = gomesTruncatedJetGaugeGroup n 0 ↔
      orderOf z = 0 ∨ n + 1 ≤ orderOf z := by
  rw [gomesTruncatedJetGaugeGroup_eq_iff_algebra, gomesTruncatedJetJointAlgebra_zero,
    gomesTruncatedJetJointAlgebra_eq_bot_iff]

/-- All invertible joint symmetries are scalar exactly when the full joint algebra is scalar. -/
theorem gomesTruncatedJetGaugeGroup_all_scalar_iff (n : ℕ) (z : ℂ) :
    (∀ u : gomesTruncatedJetGaugeGroup n z,
      u.val.val ∈ (⊥ : Subalgebra ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))) ↔
      gomesTruncatedJetJointAlgebra n z = ⊥ := by
  constructor
  · intro h
    have hG : gomesTruncatedJetGaugeGroup n z ≤ gomesTruncatedJetGaugeGroup n 0 := by
      intro u hu
      rw [gomesTruncatedJetGaugeGroup_mem_iff, gomesTruncatedJetJointAlgebra_zero]
      exact h ⟨u, hu⟩
    have hJ := (gomesTruncatedJetGaugeGroup_le_iff_algebra n z 0).mp hG
    rw [gomesTruncatedJetJointAlgebra_zero] at hJ
    exact le_antisymm hJ bot_le
  · intro h u
    simpa only [h] using (show u.val.val ∈ gomesTruncatedJetJointAlgebra n z from u.property)

/-- The entire unipotent subgroup is trivial exactly at the sharp scalar-collapse boundary. -/
theorem gomesTruncatedJetUnipotentGroup_eq_bot_iff (n : ℕ) (z : ℂ) :
    gomesTruncatedJetUnipotentGroup n z = ⊥ ↔ orderOf z = 0 ∨ n + 1 ≤ orderOf z := by
  rw [← gomesTruncatedJetJointAlgebra_eq_bot_iff, ← gomesTruncatedJetGaugeGroup_all_scalar_iff]
  constructor
  · intro h u
    have hm := (gomesTruncatedJetUnipotentPart n z u).property
    have hm0 : (gomesTruncatedJetUnipotentPart n z u).val ∈
        (⊥ : Subgroup (gomesTruncatedJetGaugeGroup n z)) := h.le hm
    apply (gomesTruncatedJetUnipotentPart_eq_one_iff n z u).mp
    exact Subtype.ext (Subgroup.mem_bot.mp hm0)
  · intro h
    apply le_antisymm
    · intro u hu
      rw [Subgroup.mem_bot]
      have hs := (gomesTruncatedJetGaugeGroup_scalar_iff n z u).mpr (h u)
      have hχ : gomesTruncatedJetGaugeCharacter n z u = 1 := hu
      rw [hχ, map_one] at hs
      exact hs
    · exact bot_le

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
