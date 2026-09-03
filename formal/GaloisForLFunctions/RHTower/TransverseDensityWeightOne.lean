import Mathlib
import GaloisForLFunctions.RHTower.ArchimedeanTransverseMassLaw

/-!
# The weight-one transverse density and the exclusion of invariant transverse traces

In the Deninger–Singhof polarization the top leafwise cohomology is `H² = ℂ(−1)`: the flow acts
on the Kähler class by `e^{t}`.  A trace on `H²` that is invariant under the flow cannot exist,
because it would give `T(ω) = T(φ^{t*} ω) = e^{t} T(ω)`.  So the transverse density integrating
leafwise forms must itself scale by the flow with weight one: on the height line `u > 0` with the
flow `u ↦ e^{t} u` the density is `du`, whose pushforward is `e^{−t} du`.  This density has finite
mass at the `u → 0` end and infinite mass at the `u → ∞` end, which is the real apex; the
flow-invariant measure `du/u` of `ArchimedeanTransverseMassLaw` is not the polarization density.
-/

open MeasureTheory Set

namespace RHTower

/-- **No invariant trace on a weight-one top class.**  A functional invariant under a flow that
scales a vector by `e^{t}` vanishes on that vector. -/
theorem no_invariant_trace_of_weight_one {E : Type*} [AddCommGroup E] [Module ℝ E]
    (T : E →ₗ[ℝ] ℝ) (φ : ℝ → E →ₗ[ℝ] E) (hinv : ∀ t x, T (φ t x) = T x) (ω : E)
    (hω : ∀ t, φ t ω = Real.exp t • ω) (hT : T ω ≠ 0) : False := by
  have h1 := hinv 1 ω
  rw [hω 1, map_smul, smul_eq_mul] at h1
  have h2 : (Real.exp 1 - 1) * T ω = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · have := Real.exp_one_gt_d9
    linarith
  · exact hT h3

/-- The transverse density of weight one on the height line: Lebesgue measure on `u > 0`. -/
noncomputable def heightDensity : Measure ℝ := volume.restrict (Ioi 0)

/-- The suspension flow on the height line. -/
noncomputable def heightFlow (t : ℝ) (u : ℝ) : ℝ := Real.exp t * u

theorem heightFlow_preimage_Ioi (t : ℝ) : heightFlow t ⁻¹' Ioi 0 = Ioi 0 := by
  ext u
  simp only [heightFlow, mem_preimage, mem_Ioi]
  constructor
  · intro h
    exact pos_of_mul_pos_right h (Real.exp_pos t).le
  · intro h
    exact mul_pos (Real.exp_pos t) h

/-- **Weight one.**  The suspension flow pushes the height density to `e^{−t}` times itself. -/
theorem heightDensity_map_heightFlow (t : ℝ) :
    heightDensity.map (heightFlow t) = ENNReal.ofReal (Real.exp (-t)) • heightDensity := by
  have hm : Measurable (heightFlow t) := by
    unfold heightFlow
    fun_prop
  unfold heightDensity
  rw [← heightFlow_preimage_Ioi t, ← Measure.restrict_map hm measurableSet_Ioi,
    heightFlow_preimage_Ioi]
  have h := Real.map_volume_mul_left (a := Real.exp t) (Real.exp_pos t).ne'
  unfold heightFlow
  rw [h, Measure.restrict_smul]
  congr 1
  rw [abs_of_pos (inv_pos.mpr (Real.exp_pos t)), Real.exp_neg]

/-- The `u → 0` end carries finite weight-one mass. -/
theorem heightDensity_Ioo_zero_one : heightDensity (Ioo 0 1) = 1 := by
  unfold heightDensity
  rw [Measure.restrict_apply measurableSet_Ioo, Ioo_inter_Ioi, Real.volume_Ioo]
  norm_num

/-- The `u → ∞` end, the real apex, carries infinite weight-one mass. -/
theorem heightDensity_Ioi_one : heightDensity (Ioi 1) = ⊤ := by
  unfold heightDensity
  rw [Measure.restrict_apply measurableSet_Ioi]
  have h : Ioi (1 : ℝ) ∩ Ioi 0 = Ioi 1 := by
    ext u
    simp only [mem_inter_iff, mem_Ioi]
    constructor
    · exact fun h => h.1
    · intro h; exact ⟨h, by linarith⟩
  rw [h, Real.volume_Ioi]

end RHTower
