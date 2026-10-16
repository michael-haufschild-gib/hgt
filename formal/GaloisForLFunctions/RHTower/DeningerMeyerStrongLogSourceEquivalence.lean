import GaloisForLFunctions.RHTower.DeningerDampedPrimeCircleContraction
import GaloisForLFunctions.RHTower.DeningerMeyerStrongLogTopology
import GaloisForLFunctions.RHTower.DeningerMeyerStrictEmbedding

/-!
# The natural strong logarithmic and nuclear Meyer source topologies agree

The Route E landing into exponential Schwartz space preserves the full source
topology, in both directions. This identifies the two actual Poisson boundary
maps and transfers closedness of the nuclear Poisson image to the strong
logarithmic target used by causal division.
-/

open Asymptotics Complex Filter Set Topology
open scoped BoundedContinuousFunction SchwartzMap

namespace RHTower
noncomputable section

theorem deningerExpSchwartz_strongLogDecay (h : DeningerExpSchwartz) :
    DeningerMeyerStrongLogDecay (h.val : ℝ → ℂ) where
  smooth := h.val.smooth'
  decayTop := by
    intro n a
    obtain ⟨C, hC⟩ := h.property a n
    apply IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hb := hC t
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, abs_of_nonneg ht] at hb
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (Real.exp_pos t) (-a)),
      ← Real.exp_mul]
    have hm := mul_le_mul_of_nonneg_left hb (Real.exp_pos (-(a * t))).le
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at hm
    simpa only [mul_neg, neg_mul, mul_comm] using hm
  decayBot := by
    intro n a
    obtain ⟨C, hC⟩ := h.property a n
    apply IsBigO.of_bound C
    filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
    have hb := hC t
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, abs_of_nonpos ht] at hb
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (Real.exp_pos t) a),
      ← Real.exp_mul]
    have hm := mul_le_mul_of_nonneg_left hb (Real.exp_pos (a * t)).le
    rw [← mul_assoc, ← Real.exp_add,
      show a * t + a * -t = 0 by ring, Real.exp_zero, one_mul] at hm
    simpa only [mul_comm] using hm

/-- The same original logarithmic function, in the full strong target. -/
def deningerMeyerOriginalStrongLogLM :
    DeningerMeyerSource →ₗ[ℂ] DeningerMeyerStrongLogTarget where
  toFun h := ⟨(DeningerMeyerSource.toSource h).val,
    deningerExpSchwartz_strongLogDecay (DeningerMeyerSource.toSource h)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem deningerMeyerOriginalStrongLogLM_apply
    (h : DeningerMeyerSource) (t : ℝ) :
    (deningerMeyerOriginalStrongLogLM h).val t =
      (DeningerMeyerSource.toSource h).val t := rfl

/-- No source choice is involved: the equivalence is the identity on profiles. -/
def deningerMeyerStrongLogSourceEquiv :
    DeningerMeyerStrongLogTarget ≃ₗ[ℂ] DeningerMeyerSource :=
  LinearEquiv.ofLinear deningerDampedStrongLogOriginalSourceLM
    deningerMeyerOriginalStrongLogLM
    (by ext h; rfl)
    (by ext g; rfl)

theorem deningerMeyerStrongLogSourceEquiv_boundary (f : DeningerMeyerCap) :
    deningerMeyerStrongLogSourceEquiv (deningerMeyerStrongLogSumLM f) =
      deningerPoissonMeyerLM f := by
  apply DeningerMeyerSource.toSource.injective
  apply Subtype.ext
  ext t
  rw [deningerPoissonMeyerLM_toSource, deningerPoissonSource_apply]
  rfl

private theorem gauge_norm_at (n : ℕ) (k : ℤ)
    (g : DeningerMeyerStrongLogTarget) (t : ℝ) :
    Real.exp ((k : ℝ) * t) * ‖iteratedDeriv n g.val t‖ ≤
      ‖deningerMeyerStrongLogGauge n k g‖ := by
  have h := (deningerMeyerStrongLogGauge n k g).norm_coe_le_norm t
  rw [deningerMeyerStrongLogGauge_apply, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (Real.exp_pos t) (k : ℝ)),
    ← Real.exp_mul] at h
  simpa only [mul_comm t] using h

theorem deningerMeyerStrongLogSourceEquiv_seminorm_le
    (m n : ℕ) (g : DeningerMeyerStrongLogTarget) :
    DeningerMeyerSource.seminorms (m, n) (deningerMeyerStrongLogSourceEquiv g) ≤
      ‖deningerMeyerStrongLogGauge n (m : ℤ) g‖ +
        ‖deningerMeyerStrongLogGauge n (-(m : ℤ)) g‖ := by
  apply deningerMeyerSeminormFun_le
  intro t
  change Real.exp ((m : ℝ) * |t|) *
    ‖iteratedFDeriv ℝ n g.val t‖ ≤ _
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    have h := gauge_norm_at n (m : ℤ) g t
    push_cast at h
    exact h.trans (le_add_of_nonneg_right (norm_nonneg _))
  · rw [abs_of_nonpos ht]
    have h := gauge_norm_at n (-(m : ℤ)) g t
    push_cast at h
    rw [mul_neg, neg_mul] at *
    exact h.trans (le_add_of_nonneg_left (norm_nonneg _))

local instance : TopologicalSpace DeningerMeyerStrongLogTarget :=
  deningerMeyerStrongLogTopology

local instance : IsTopologicalAddGroup DeningerMeyerStrongLogTarget := by
  exact topologicalAddGroup_iInf
    (ts' := fun i : ℕ × ℤ => TopologicalSpace.induced
      (deningerMeyerStrongLogGaugeLinear i.1 i.2) inferInstance) fun i =>
    topologicalAddGroup_induced (deningerMeyerStrongLogGaugeLinear i.1 i.2)

theorem deningerMeyerStrongLogSourceEquiv_continuous :
    Continuous deningerMeyerStrongLogSourceEquiv := by
  apply WithSeminorms.continuous_of_continuous_comp
    DeningerMeyerSource.withSeminorms deningerMeyerStrongLogSourceEquiv.toLinearMap
  intro i
  let p : Seminorm ℂ DeningerMeyerStrongLogTarget :=
    (normSeminorm ℂ (ℝ →ᵇ ℂ)).comp
      (deningerMeyerStrongLogGaugeLinear i.2 (i.1 : ℤ)) +
    (normSeminorm ℂ (ℝ →ᵇ ℂ)).comp
      (deningerMeyerStrongLogGaugeLinear i.2 (-(i.1 : ℤ)))
  have hp : Continuous p :=
    (continuous_deningerMeyerStrongLogGaugeLinear i.2 (i.1 : ℤ)).norm.add
      (continuous_deningerMeyerStrongLogGaugeLinear i.2 (-(i.1 : ℤ))).norm
  exact Seminorm.continuous_of_le hp
    (deningerMeyerStrongLogSourceEquiv_seminorm_le i.1 i.2)

theorem deningerMeyerOriginalStrongLogLM_gauge_le
    (n : ℕ) (k : ℤ) (h : DeningerMeyerSource) :
    ‖deningerMeyerStrongLogGauge n k (deningerMeyerOriginalStrongLogLM h)‖ ≤
      DeningerMeyerSource.seminorms (k.natAbs, n) h := by
  apply (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).mpr
  intro t
  rw [deningerMeyerStrongLogGauge_apply, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (Real.exp_pos t) (k : ℝ)),
    ← Real.exp_mul]
  have hk : (t * (k : ℝ)) ≤ (k.natAbs : ℝ) * |t| := by
    calc
      t * (k : ℝ) ≤ |t * (k : ℝ)| := le_abs_self _
      _ = (k.natAbs : ℝ) * |t| := by
        have habs : (k.natAbs : ℝ) = |(k : ℝ)| := by
          cases k with
          | ofNat k => simp
          | negSucc k =>
              simp
              rw [abs_of_nonpos (by have := Nat.cast_nonneg (α := ℝ) k; linarith)]
              ring
        rw [abs_mul, habs]
        ring
  calc
    _ ≤ Real.exp ((k.natAbs : ℝ) * |t|) *
        ‖iteratedDeriv n (deningerMeyerOriginalStrongLogLM h).val t‖ :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hk) (norm_nonneg _)
    _ = deningerMeyerWeight (k.natAbs : ℝ) n (DeningerMeyerSource.toSource h) t := by
      rw [deningerMeyerWeight, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      rfl
    _ ≤ _ := deningerMeyerWeight_le _ _ _ t

theorem deningerMeyerOriginalStrongLogLM_continuous :
    Continuous deningerMeyerOriginalStrongLogLM := by
  change @Continuous DeningerMeyerSource DeningerMeyerStrongLogTarget _
    (⨅ i : ℕ × ℤ, TopologicalSpace.induced
      (deningerMeyerStrongLogGaugeLinear i.1 i.2) inferInstance) _
  rw [continuous_iInf_rng]
  intro i
  rw [continuous_induced_rng]
  apply WithSeminorms.continuous_normedSpace_rng (ℝ →ᵇ ℂ)
    DeningerMeyerSource.withSeminorms
    ((deningerMeyerStrongLogGaugeLinear i.1 i.2).comp deningerMeyerOriginalStrongLogLM)
  refine ⟨{(i.2.natAbs, i.1)}, 1, ?_⟩
  intro h
  simpa only [Seminorm.comp_apply, coe_normSeminorm, Finset.sup_singleton,
    one_smul, LinearMap.comp_apply, deningerMeyerStrongLogGaugeLinear_apply]
    using deningerMeyerOriginalStrongLogLM_gauge_le i.1 i.2 h

/-- Exact topological identification of the two full source presentations. -/
def deningerMeyerStrongLogSourceContinuousEquiv :
    DeningerMeyerStrongLogTarget ≃L[ℂ] DeningerMeyerSource where
  toLinearEquiv := deningerMeyerStrongLogSourceEquiv
  continuous_toFun := deningerMeyerStrongLogSourceEquiv_continuous
  continuous_invFun := deningerMeyerOriginalStrongLogLM_continuous

/-- The actual Poisson boundary space is closed in the natural strong topology. -/
theorem deningerMeyerStrongLogSum_range_isClosed :
    IsClosed (Set.range deningerMeyerStrongLogSumLM) := by
  have heq : Set.range deningerMeyerStrongLogSumLM =
      deningerMeyerStrongLogSourceEquiv ⁻¹' Set.range deningerPoissonMeyerLM := by
    ext g
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨f, (deningerMeyerStrongLogSourceEquiv_boundary f).symm⟩
    · rintro ⟨f, hf⟩
      refine ⟨f, deningerMeyerStrongLogSourceEquiv.injective ?_⟩
      rw [deningerMeyerStrongLogSourceEquiv_boundary, hf]
  rw [heq]
  exact deningerPoissonMeyer_range_isClosed.preimage
    deningerMeyerStrongLogSourceEquiv_continuous

end
end RHTower
