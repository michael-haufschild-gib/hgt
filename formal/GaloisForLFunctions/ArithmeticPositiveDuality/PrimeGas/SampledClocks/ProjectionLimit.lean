import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.RepeatedObservations
import GaloisForLFunctions.HTGeometry.LpCoordinateProjection
import GaloisForLFunctions.RHTower.StrongTraceNormMultiplierLimit
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Strong convergence of sampled clock projections

Each fixed state loses vanishing mass to words falsely accepted at a finite
stage. For two copies some unit occupation vector realizes error one at
any chosen finite stage.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks

open CopyExchange Filter HTGeometry
open scoped Classical Topology

variable {I E : Type*}

/-- Orthogonal projection onto the occupations passing a clock test. -/
def project (P : (I → ℕ+) → Prop) : LabelSpace (I → ℕ+) →L[ℂ] LabelSpace (I → ℕ+) :=
  lpCoordinateProjection {x | P x}

private theorem project_at (P : (I → ℕ+) → Prop) (f : LabelSpace (I → ℕ+)) (x : I → ℕ+) :
    project P f x = if P x then f x else 0 :=
  Set.indicator_apply {y | P y} (fun j => f j) x

private theorem project_norm_le_one (P : (I → ℕ+) → Prop) : ‖project P‖ ≤ 1 := by
  apply (project P).opNorm_le_bound zero_le_one
  intro f
  rw [one_mul]
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro x
  rw [project_at]
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (f x)

namespace Network

variable (G : Network I E) (r : {r : ℝ // 0 < r})

private theorem error_at (N : ℕ) (f : LabelSpace (I → ℕ+)) (x : I → ℕ+) :
    (project (G.Prefix r.val N) f - project G.Resonant f) x =
      if G.Prefix r.val N x ∧ ¬G.Resonant x then f x else 0 := by
  rw [lp.coeFn_sub,Pi.sub_apply,project_at,project_at]
  by_cases hx : G.Resonant x
  · simp only [hx,G.resonant_prefix r N x hx,if_true,not_true_eq_false,and_false,if_false,sub_self]
  · simp only [hx,not_false_eq_true,and_true,if_false,sub_zero]

private theorem error_le (N : ℕ) (f : LabelSpace (I → ℕ+)) (x : I → ℕ+) :
    ‖(project (G.Prefix r.val N) f - project G.Resonant f) x‖ ≤ ‖f x‖ := by
  rw [G.error_at]
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (f x)

/-- Positive-radius dyadic observations recover the exact projector strongly. -/
theorem projection_tendsto (hr : r.val ≤ Real.sqrt 3) (f : LabelSpace (I → ℕ+)) :
    Tendsto (fun N => project (G.Prefix r.val N) f) atTop (𝓝 (project G.Resonant f)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  let v (N : ℕ) := project (G.Prefix r.val N) f - project G.Resonant f
  have hs : Tendsto (fun N => ‖v N‖^2) atTop (𝓝 0) := by
    simp_rw [HilbertSchmidt.lp_norm_sq_eq]
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun N x => ‖v N x‖^2) (g := fun _ => (0 : ℝ)) (HilbertSchmidt.summable_coe_sq f)
      (fun x => ?_) ?_
    · simpa only [tsum_zero] using h
    · apply tendsto_const_nhds.congr'
      filter_upwards [G.prefix_eventually r hr x] with N hN
      have hn : ¬(G.Prefix r.val N x ∧ ¬G.Resonant x) := fun h => h.2 (hN.mp h.1)
      simp only [v,G.error_at,if_neg hn,norm_zero,zero_pow (two_ne_zero : (2 : ℕ) ≠ 0)]
    · refine Eventually.of_forall fun N x => ?_
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (G.error_le r N f x)
  have h := (Real.continuous_sqrt.tendsto 0).comp hs
  simp only [Real.sqrt_zero] at h
  exact h.congr fun N => Real.sqrt_sq (norm_nonneg (v N))

/-- After any fixed trace-class preparation the readout error vanishes in trace norm. -/
theorem prepared_projection_tendsto (hr : r.val ≤ Real.sqrt 3)
    (T : {T : LabelSpace (I → ℕ+) →L[ℂ] LabelSpace (I → ℕ+) // T.IsTraceClass}) :
    Tendsto (fun N => _root_.RHTower.traceNorm (LabelSpace (I → ℕ+))
      ((project (G.Prefix r.val N) - project G.Resonant) ∘L T.val)) atTop (𝓝 0) :=
  _root_.RHTower.traceNorm_comp_tendsto_of_strong_tendsto_of_uniform_bound T.property 1 zero_le_one
    (Eventually.of_forall fun _ => project_norm_le_one _) (G.projection_tendsto r hr)

end Network

/-- Every finite binary readout has operator-norm error exactly one. -/
theorem binary_projection_error (t : {t : ℝ // t ≠ 0}) (r : {r : ℝ // 0 < r}) (N : ℕ) :
    ‖project ((binary t.val).Prefix r.val N) - project (binary t.val).Resonant‖ = 1 := by
  let G := binary t.val
  let T := project (G.Prefix r.val N) - project G.Resonant
  change ‖T‖ = 1
  apply le_antisymm
  · apply T.opNorm_le_bound zero_le_one
    intro f
    rw [one_mul]
    exact lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) (G.error_le r N f)
  · obtain ⟨x,hx,hn⟩ := binary_false_positive t r N
    let d : LabelSpace (Bool → ℕ+) := lp.single 2 x (1 : ℂ)
    have hd : ‖d‖ = 1 :=
      (lp.norm_single (E := fun _ : Bool → ℕ+ => ℂ) (by norm_num : 0 < (2 : ENNReal)) x 1).trans norm_one
    have he : T d x = 1 := by
      change (project (G.Prefix r.val N) d - project G.Resonant d) x = _
      rw [G.error_at,if_pos ⟨hx,hn⟩]
      exact lp.single_apply_self (E := fun _ : Bool → ℕ+ => ℂ) 2 x 1
    have hl := (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (T d) x).trans (T.le_opNorm d)
    simpa only [he,norm_one,hd,mul_one] using hl

#print axioms Network.projection_tendsto
#print axioms Network.prepared_projection_tendsto
#print axioms binary_projection_error

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks
