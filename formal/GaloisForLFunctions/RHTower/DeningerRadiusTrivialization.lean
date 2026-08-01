import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Homeomorph.Defs

/-!
# Equivariant trivialization along a radius

A continuous real action carrying a positive radius function that scales exponentially is
trivial: the space splits as the unit-radius slice times the positive reals, equivariantly.  The
chart sends a point to its flow-translate onto the slice together with its radius, and the
inverse flows back by the logarithm of the radius.

Freeness is immediate from the same identity: a period fixes the radius, so its exponential is
one.

* `DeningerRadiusFlow` : the data and its axioms.
* `deningerRadiusChart` : the equivariant chart, as an equivalence.
* `deningerRadiusChart_equivariant`, `deningerRadiusFlow_free` : equivariance and freeness.
* `deningerRadiusHomeomorph` : the chart as a homeomorphism.
-/

namespace RHTower

section RadiusTrivialization

/-- A continuous real action together with an exponentially scaling positive radius. -/
structure DeningerRadiusFlow (X : Type*) [TopologicalSpace X] where
  /-- The action. -/
  act : ℝ → X → X
  /-- The action is unital. -/
  act_zero : ∀ p, act 0 p = p
  /-- The action is additive. -/
  act_add : ∀ s t p, act (s + t) p = act s (act t p)
  /-- The radius. -/
  radius : X → ℝ
  /-- The radius is positive. -/
  radius_pos : ∀ p, 0 < radius p
  /-- The radius scales exponentially along the action. -/
  radius_act : ∀ t p, radius (act t p) = Real.exp t * radius p
  /-- The action is jointly continuous. -/
  continuous_act : Continuous fun q : ℝ × X => act q.1 q.2
  /-- The radius is continuous. -/
  continuous_radius : Continuous radius

variable {X : Type*} [TopologicalSpace X] (F : DeningerRadiusFlow X)

/-- The unit-radius slice. -/
def deningerRadiusSlice : Set X := {p | F.radius p = 1}

/-- Flowing a point onto the unit-radius slice. -/
theorem deningerRadius_normalize_mem (p : X) :
    F.act (-(Real.log (F.radius p))) p ∈ deningerRadiusSlice F := by
  have hpos := F.radius_pos p
  show F.radius (F.act (-(Real.log (F.radius p))) p) = 1
  rw [F.radius_act, Real.exp_neg, Real.exp_log hpos]
  field_simp

/-- **The equivariant chart.**  A point corresponds to its normalization together with its
radius. -/
noncomputable def deningerRadiusChart :
    X ≃ (deningerRadiusSlice F) × {r : ℝ // 0 < r} where
  toFun p := (⟨F.act (-(Real.log (F.radius p))) p, deningerRadius_normalize_mem F p⟩,
    ⟨F.radius p, F.radius_pos p⟩)
  invFun qr := F.act (Real.log (qr.2 : ℝ)) (qr.1 : X)
  left_inv p := by
    show F.act (Real.log (F.radius p)) (F.act (-(Real.log (F.radius p))) p) = p
    rw [← F.act_add, add_neg_cancel, F.act_zero]
  right_inv qr := by
    obtain ⟨⟨q, hq⟩, ⟨r, hr⟩⟩ := qr
    have hq1 : F.radius q = 1 := hq
    have hrad : F.radius (F.act (Real.log r) q) = r := by
      rw [F.radius_act, hq1, mul_one, Real.exp_log hr]
    refine Prod.ext ?_ ?_
    · refine Subtype.ext ?_
      show F.act (-(Real.log (F.radius (F.act (Real.log r) q)))) (F.act (Real.log r) q) = q
      rw [hrad, ← F.act_add, neg_add_cancel, F.act_zero]
    · exact Subtype.ext hrad

/-- **Equivariance of the chart.**  The action becomes scaling of the radius coordinate. -/
theorem deningerRadiusChart_equivariant (t : ℝ) (p : X) :
    deningerRadiusChart F (F.act t p)
      = ((deningerRadiusChart F p).1, ⟨Real.exp t * F.radius p, by
          have := F.radius_pos p
          positivity⟩) := by
  have hpos := F.radius_pos p
  have hrad : F.radius (F.act t p) = Real.exp t * F.radius p := F.radius_act t p
  refine Prod.ext ?_ ?_
  · refine Subtype.ext ?_
    show F.act (-(Real.log (F.radius (F.act t p)))) (F.act t p)
      = F.act (-(Real.log (F.radius p))) p
    rw [hrad, Real.log_mul (Real.exp_ne_zero t) hpos.ne', Real.log_exp,
      ← F.act_add]
    congr 1
    ring
  · exact Subtype.ext hrad

/-- **The action is free.**  A period scales the radius by one. -/
theorem deningerRadiusFlow_free {t : ℝ} {p : X} (h : F.act t p = p) : t = 0 := by
  have hpos := F.radius_pos p
  have hrad : F.radius p = Real.exp t * F.radius p := by
    conv_lhs => rw [← h]
    exact F.radius_act t p
  have hone : Real.exp t = 1 := by
    have h1 : Real.exp t * F.radius p = 1 * F.radius p := by
      rw [one_mul, ← hrad]
    exact mul_right_cancel₀ hpos.ne' h1
  have hexp : Real.exp t = Real.exp 0 := by
    rw [Real.exp_zero]
    exact hone
  exact Real.exp_eq_exp.mp hexp

/-- The logarithmic radius is continuous. -/
theorem deningerRadius_continuous_log : Continuous fun p : X => Real.log (F.radius p) := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  exact (Real.continuousAt_log (F.radius_pos p).ne').comp F.continuous_radius.continuousAt

theorem continuous_deningerRadiusChart : Continuous (deningerRadiusChart F) := by
  refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (F.continuous_radius.subtype_mk _)
  exact F.continuous_act.comp
    (Continuous.prodMk (deningerRadius_continuous_log F).neg continuous_id)

theorem continuous_deningerRadiusChart_symm :
    Continuous (deningerRadiusChart F).symm := by
  have hlog : Continuous fun r : {r : ℝ // 0 < r} => Real.log (r : ℝ) := by
    refine continuous_iff_continuousAt.mpr fun r => ?_
    exact (Real.continuousAt_log r.2.ne').comp continuous_subtype_val.continuousAt
  exact F.continuous_act.comp
    (Continuous.prodMk (hlog.comp continuous_snd) (continuous_subtype_val.comp continuous_fst))

/-- **The chart is a homeomorphism.** -/
noncomputable def deningerRadiusHomeomorph :
    X ≃ₜ (deningerRadiusSlice F) × {r : ℝ // 0 < r} where
  toEquiv := deningerRadiusChart F
  continuous_toFun := continuous_deningerRadiusChart F
  continuous_invFun := continuous_deningerRadiusChart_symm F

/-- **Properness of the action.**  The preimage of a compact set under `(t, p) ↦ (φ^t p, p)` is
compact: the radius quotient pins the time down to the compact set of logarithmic radius
differences. -/
theorem deningerRadiusFlow_isCompact_preimage [T2Space X] {K : Set (X × X)} (hK : IsCompact K) :
    IsCompact {q : ℝ × X | (F.act q.1 q.2, q.2) ∈ K} := by
  have hcontmap : Continuous fun q : ℝ × X => (F.act q.1 q.2, q.2) :=
    F.continuous_act.prodMk continuous_snd
  have hclosed : IsClosed {q : ℝ × X | (F.act q.1 q.2, q.2) ∈ K} :=
    (hK.isClosed).preimage hcontmap
  have hdiff : Continuous fun z : X × X =>
      Real.log (F.radius z.1) - Real.log (F.radius z.2) :=
    ((deningerRadius_continuous_log F).comp continuous_fst).sub
      ((deningerRadius_continuous_log F).comp continuous_snd)
  have hS : IsCompact ((fun z : X × X =>
      Real.log (F.radius z.1) - Real.log (F.radius z.2)) '' K) := hK.image hdiff
  have hT : IsCompact (Prod.snd '' K) := hK.image continuous_snd
  refine IsCompact.of_isClosed_subset (hS.prod hT) hclosed ?_
  rintro ⟨t, p⟩ hq
  refine ⟨⟨(F.act t p, p), hq, ?_⟩, ⟨(F.act t p, p), hq, rfl⟩⟩
  show Real.log (F.radius (F.act t p)) - Real.log (F.radius p) = t
  rw [F.radius_act, Real.log_mul (Real.exp_ne_zero t) (F.radius_pos p).ne', Real.log_exp]
  ring

/-! ## The half-density circle refinement -/

/-- The half-density line bundle `{(p, z) : |z|² = x(p)}`. -/
def deningerHalfDensity : Set (X × ℂ) := {q | ‖q.2‖ ^ 2 = F.radius q.1}

/-- The fibre coordinate never vanishes, because the radius is positive. -/
theorem deningerHalfDensity_ne_zero {q : X × ℂ} (hq : q ∈ deningerHalfDensity F) :
    q.2 ≠ 0 := by
  intro hz
  have h : (0 : ℝ) = F.radius q.1 := by
    have := hq
    rw [deningerHalfDensity, Set.mem_setOf_eq, hz] at this
    simpa using this
  exact absurd h.symm (F.radius_pos q.1).ne'

/-- The half-density flow `Φ^t(p, z) = (φ^t p, e^{t/2} z)`. -/
noncomputable def deningerHalfDensityFlow (t : ℝ) (q : X × ℂ) : X × ℂ :=
  (F.act t q.1, (Real.exp (t / 2) : ℂ) * q.2)

/-- The circle rotation `R_θ(p, z) = (p, e^{iθ} z)`. -/
noncomputable def deningerHalfDensityRotate (theta : ℝ) (q : X × ℂ) : X × ℂ :=
  (q.1, Complex.exp ((theta : ℂ) * Complex.I) * q.2)

theorem deningerHalfDensityFlow_mem (t : ℝ) {q : X × ℂ}
    (hq : q ∈ deningerHalfDensity F) :
    deningerHalfDensityFlow F t q ∈ deningerHalfDensity F := by
  have hq' : ‖q.2‖ ^ 2 = F.radius q.1 := hq
  show ‖(Real.exp (t / 2) : ℂ) * q.2‖ ^ 2 = F.radius (F.act t q.1)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _), mul_pow, F.radius_act, hq']
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem deningerHalfDensityRotate_mem (theta : ℝ) {q : X × ℂ}
    (hq : q ∈ deningerHalfDensity F) :
    deningerHalfDensityRotate theta q ∈ deningerHalfDensity F := by
  have hq' : ‖q.2‖ ^ 2 = F.radius q.1 := hq
  have hnorm : ‖Complex.exp ((theta : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : ((theta : ℂ) * Complex.I).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero]
  show ‖Complex.exp ((theta : ℂ) * Complex.I) * q.2‖ ^ 2 = F.radius q.1
  rw [norm_mul, hnorm, one_mul, hq']

/-- **The two actions commute.** -/
theorem deningerHalfDensity_flow_rotate_comm (t theta : ℝ) (q : X × ℂ) :
    deningerHalfDensityFlow F t (deningerHalfDensityRotate theta q)
      = deningerHalfDensityRotate theta (deningerHalfDensityFlow F t q) := by
  refine Prod.ext rfl ?_
  show (Real.exp (t / 2) : ℂ) * (Complex.exp ((theta : ℂ) * Complex.I) * q.2)
    = Complex.exp ((theta : ℂ) * Complex.I) * ((Real.exp (t / 2) : ℂ) * q.2)
  ring

/-- **The half-density chart `(7)`.**  The bundle is the slice times the punctured plane. -/
noncomputable def deningerHalfDensityChart :
    (deningerHalfDensity F) ≃ (deningerRadiusSlice F) × {z : ℂ // z ≠ 0} where
  toFun q :=
    (⟨F.act (-(Real.log (F.radius (q : X × ℂ).1))) (q : X × ℂ).1,
        deningerRadius_normalize_mem F _⟩,
      ⟨(q : X × ℂ).2, deningerHalfDensity_ne_zero F q.2⟩)
  invFun qz :=
    ⟨(F.act (Real.log (‖(qz.2 : ℂ)‖ ^ 2)) (qz.1 : X), (qz.2 : ℂ)), by
      have hz : ‖(qz.2 : ℂ)‖ ^ 2 > 0 := by
        have := norm_pos_iff.mpr qz.2.2
        positivity
      have hq1 : F.radius (qz.1 : X) = 1 := qz.1.2
      show ‖(qz.2 : ℂ)‖ ^ 2 = F.radius (F.act (Real.log (‖(qz.2 : ℂ)‖ ^ 2)) (qz.1 : X))
      rw [F.radius_act, hq1, mul_one, Real.exp_log hz]⟩
  left_inv q := by
    refine Subtype.ext (Prod.ext ?_ rfl)
    have hmem : ‖(q : X × ℂ).2‖ ^ 2 = F.radius (q : X × ℂ).1 := q.2
    show F.act (Real.log (‖(q : X × ℂ).2‖ ^ 2))
        (F.act (-(Real.log (F.radius (q : X × ℂ).1))) (q : X × ℂ).1) = (q : X × ℂ).1
    rw [hmem, ← F.act_add, add_neg_cancel, F.act_zero]
  right_inv qz := by
    obtain ⟨⟨q, hq⟩, ⟨z, hz⟩⟩ := qz
    have hq1 : F.radius q = 1 := hq
    have hzpos : ‖z‖ ^ 2 > 0 := by
      have := norm_pos_iff.mpr hz
      positivity
    have hrad : F.radius (F.act (Real.log (‖z‖ ^ 2)) q) = ‖z‖ ^ 2 := by
      rw [F.radius_act, hq1, mul_one, Real.exp_log hzpos]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext rfl)
    show F.act (-(Real.log (F.radius (F.act (Real.log (‖z‖ ^ 2)) q))))
        (F.act (Real.log (‖z‖ ^ 2)) q) = q
    rw [hrad, ← F.act_add, neg_add_cancel, F.act_zero]

/-- **The flow becomes fibrewise scaling.** -/
theorem deningerHalfDensityChart_flow (t : ℝ) (q : deningerHalfDensity F) :
    (deningerHalfDensityChart F
        ⟨deningerHalfDensityFlow F t (q : X × ℂ),
          deningerHalfDensityFlow_mem F t q.2⟩).1
      = (deningerHalfDensityChart F q).1 := by
  refine Subtype.ext ?_
  have hpos := F.radius_pos (q : X × ℂ).1
  show F.act (-(Real.log (F.radius (F.act t (q : X × ℂ).1)))) (F.act t (q : X × ℂ).1)
    = F.act (-(Real.log (F.radius (q : X × ℂ).1))) (q : X × ℂ).1
  rw [F.radius_act, Real.log_mul (Real.exp_ne_zero t) hpos.ne', Real.log_exp, ← F.act_add]
  congr 1
  ring

/-- **The rotation becomes fibrewise rotation.** -/
theorem deningerHalfDensityChart_rotate (theta : ℝ) (q : deningerHalfDensity F) :
    (deningerHalfDensityChart F
        ⟨deningerHalfDensityRotate theta (q : X × ℂ),
          deningerHalfDensityRotate_mem F theta q.2⟩).1
      = (deningerHalfDensityChart F q).1 := rfl

end RadiusTrivialization

end RHTower
