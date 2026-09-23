import GaloisForLFunctions.RHTower.ReflectionCocycleArchimedean
import GaloisForLFunctions.HTGeometry.FundamentalParallelogram

/-!
# Gamma's normalization horizon

The Gamma recurrence leaves a pointed periodic gauge invisible.  This file proves the exact
finite-horizon/cofinal transition for the transverse log-convexity selector.

For a horizon `B`, `gammaCurvatureHorizon B` consists of pointed twice-differentiable periodic
gauges whose curvature can be added to trigamma without destroying nonnegativity on `(0, B]`.
Every positive finite horizon contains an explicit nonzero analytic gauge.  Nevertheless, a gauge
which belongs to every positive horizon is zero.  Thus no bounded normalization window is
conservative, while the cofinal nonlinear incidence is conservative.

The proof mechanism is general: a periodic defect recurs unchanged along integer translates, while
the positive background curvature tends to zero.  Global positivity therefore forces the defect
curvature itself to be nonnegative; a convex periodic function is constant, and pointing kills the
constant.
-/

open Filter Function Topology

namespace HTGeometry

noncomputable section

/-- If a periodic defect can be hidden under a background which vanishes along every positive
integer orbit, and the combined field is nonnegative on the positive ray, then the defect is
nonnegative everywhere. -/
theorem vanishing_background_periodic_nonneg_of_pos
    (background defect : ℝ → ℝ)
    (hbackground : ∀ x : ℝ,
      Tendsto (fun n : ℕ => background (x + (n : ℝ))) atTop (𝓝 0))
    (hdefect : Periodic defect 1)
    (hcombined : ∀ x : ℝ, 0 < x → 0 ≤ background x + defect x) :
    ∀ x : ℝ, 0 ≤ defect x := by
  intro x
  have hperiodic : ∀ n : ℕ, defect (x + (n : ℝ)) = defect x := by
    intro n
    simpa using hdefect.nat_mul n x
  have htendsto :
      Tendsto (fun n : ℕ =>
        background (x + (n : ℝ)) + defect (x + (n : ℝ)))
        atTop (𝓝 (defect x)) := by
    convert (hbackground x).add tendsto_const_nhds using 1
    ext n
    rw [hperiodic n]
    simp
  apply ge_of_tendsto htendsto
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop (-x)] with n hn
  exact hcombined (x + (n : ℝ)) (by linarith)

/-- A convex real function with period one is constant. -/
theorem convex_periodic_eq_const
    (f : ℝ → ℝ) (hperiodic : Periodic f 1)
    (hconvex : ConvexOn ℝ Set.univ f) :
    f = fun _ => f 0 := by
  funext x
  have hone : f 1 = f 0 := by
    simpa using hperiodic 0
  have hfract : f (Int.fract x) = f 0 := by
    have hmem : Int.fract x ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
    have hle : f (Int.fract x) ≤ f 0 := by
      have hsegment : Int.fract x ∈ segment ℝ (0 : ℝ) 1 := by
        rwa [segment_eq_Icc zero_le_one]
      have h := hconvex.le_on_segment (Set.mem_univ 0) (Set.mem_univ 1) hsegment
      simpa [hone] using h
    have hge : f 0 ≤ f (Int.fract x) := by
      have hsegment : (1 : ℝ) ∈ segment ℝ (Int.fract x) (Int.fract x + 1) := by
        rw [segment_eq_Icc (by linarith)]
        exact ⟨hmem.2, by linarith [hmem.1]⟩
      have h := hconvex.le_on_segment
        (Set.mem_univ (Int.fract x)) (Set.mem_univ (Int.fract x + 1)) hsegment
      have hshift : f (Int.fract x + 1) = f (Int.fract x) := hperiodic _
      simpa [hone, hshift] using h
    exact le_antisymm hle hge
  have hreduce : f x = f (Int.fract x) := by
    have h := hperiodic.int_mul ⌊x⌋ (Int.fract x)
    simpa [Int.fract_add_floor] using h
  exact hreduce.trans hfract

/-- Differentiation preserves a real additive period: the real case of
`GaloisForLFunctions.HTGeometry.periodic_deriv`. -/
theorem periodic_deriv {f : ℝ → ℝ} {c : ℝ} (h : Periodic f c) :
    Periodic (deriv f) c :=
  GaloisForLFunctions.HTGeometry.periodic_deriv h

/-- Vanishing background curvature plus global positive-ray admissibility makes a twice
differentiable periodic gauge constant. -/
theorem vanishing_background_periodic_curvature_rigidity_of_pos
    (background f : ℝ → ℝ)
    (hbackground : ∀ x : ℝ,
      Tendsto (fun n : ℕ => background (x + (n : ℝ))) atTop (𝓝 0))
    (hperiodic : Periodic f 1)
    (hf' : Differentiable ℝ f)
    (hf'' : Differentiable ℝ (deriv f))
    (hcombined : ∀ x : ℝ, 0 < x →
      0 ≤ background x + deriv (deriv f) x) :
    f = fun _ => f 0 := by
  have hcurvature : ∀ x : ℝ, 0 ≤ deriv (deriv f) x :=
    vanishing_background_periodic_nonneg_of_pos background (deriv (deriv f)) hbackground
      (periodic_deriv (periodic_deriv hperiodic)) hcombined
  have hconvex : ConvexOn ℝ Set.univ f :=
    convexOn_univ_of_deriv2_nonneg hf' hf'' (by
      simpa [Function.iterate_succ_apply] using hcurvature)
  exact convex_periodic_eq_const f hperiodic hconvex

/-- The real trigamma background along the positive real axis. -/
def realTrigamma (x : ℝ) : ℝ :=
  (deriv Complex.digamma (x : ℂ)).re

/-- Real trigamma tends to zero along every positive integer orbit. -/
theorem tendsto_realTrigamma_add_nat (x : ℝ) :
    Tendsto (fun n : ℕ => realTrigamma (x + (n : ℝ))) atTop (𝓝 0) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (RHTower.deriv_digamma_add_nat_tendsto (x : ℂ))
  simpa [realTrigamma] using! h

/-- The first positive summand gives the elementary lower bound `1/x² ≤ ψ'(x)`. -/
theorem one_div_sq_le_realTrigamma {x : ℝ} (hx : 0 < x) :
    1 / x ^ (2 : ℕ) ≤ realTrigamma x := by
  simpa [realTrigamma] using RHTower.one_div_sq_le_re_deriv_digamma_of_pos hx

/-- An explicit pointed analytic periodic gauge small enough to survive up to horizon `B`. -/
def gammaLocalGauge (B : ℝ) (x : ℝ) : ℝ :=
  (1 / (2 * B ^ (2 : ℕ) * (2 * Real.pi) ^ (2 : ℕ))) * (1 - Real.cos (2 * Real.pi * x))

theorem gammaLocalGauge_periodic (B : ℝ) :
    Periodic (gammaLocalGauge B) 1 := by
  intro x
  simp only [gammaLocalGauge]
  congr 2
  rw [show 2 * Real.pi * (x + 1) = 2 * Real.pi * x + 2 * Real.pi by ring,
    Real.cos_add_two_pi]

@[simp]
theorem gammaLocalGauge_zero (B : ℝ) : gammaLocalGauge B 0 = 0 := by
  simp [gammaLocalGauge]

theorem gammaLocalGauge_ne_zero {B : ℝ} (hB : 0 < B) :
    gammaLocalGauge B ≠ 0 := by
  intro hzero
  have hvalue := congrFun hzero (1 / 2)
  rw [Pi.zero_apply] at hvalue
  have hpi : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by ring
  rw [gammaLocalGauge, hpi, Real.cos_pi] at hvalue
  have hcoeff : 0 < 1 / (2 * B ^ (2 : ℕ) * (2 * Real.pi) ^ (2 : ℕ)) := by positivity
  nlinarith

theorem gammaLocalGauge_hasDerivAt (B x : ℝ) :
    HasDerivAt (gammaLocalGauge B)
      ((1 / (2 * B ^ (2 : ℕ) * (2 * Real.pi) ^ (2 : ℕ))) *
        ((2 * Real.pi) * Real.sin (2 * Real.pi * x))) x := by
  let a : ℝ := 2 * Real.pi
  let c : ℝ := 1 / (2 * B ^ (2 : ℕ) * (2 * Real.pi) ^ (2 : ℕ))
  have hinner : HasDerivAt (fun y : ℝ => a * y) a x :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul a
  have hcore := (hasDerivAt_const x 1).sub
    ((Real.hasDerivAt_cos (a * x)).comp x hinner)
  have h := hcore.const_mul c
  convert! h using 1
  simp only [a, c]
  ring

theorem gammaLocalGauge_hasDerivAt_deriv (B x : ℝ) :
    HasDerivAt (deriv (gammaLocalGauge B))
      ((1 / (2 * B ^ (2 : ℕ) * (2 * Real.pi) ^ (2 : ℕ))) *
        ((2 * Real.pi) ^ (2 : ℕ) * Real.cos (2 * Real.pi * x))) x := by
  have hfun : deriv (gammaLocalGauge B) = fun y =>
      (1 / (2 * B ^ (2 : ℕ) * (2 * Real.pi) ^ (2 : ℕ))) *
        ((2 * Real.pi) * Real.sin (2 * Real.pi * y)) := by
    funext y
    exact (gammaLocalGauge_hasDerivAt B y).deriv
  rw [hfun]
  let a : ℝ := 2 * Real.pi
  let c : ℝ := 1 / (2 * B ^ (2 : ℕ) * (2 * Real.pi) ^ (2 : ℕ))
  have hinner : HasDerivAt (fun y : ℝ => a * y) a x :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul a
  have h := ((Real.hasDerivAt_sin (a * x)).comp x hinner).const_mul (c * a)
  convert! h using 1 <;>
    simp only [a, c, Function.comp_def] <;> ring

theorem gammaLocalGauge_deriv2 (B x : ℝ) :
    deriv (deriv (gammaLocalGauge B)) x =
      (1 / (2 * B ^ (2 : ℕ) * (2 * Real.pi) ^ (2 : ℕ))) *
        ((2 * Real.pi) ^ (2 : ℕ) * Real.cos (2 * Real.pi * x)) :=
  (gammaLocalGauge_hasDerivAt_deriv B x).deriv

theorem differentiable_gammaLocalGauge (B : ℝ) :
    Differentiable ℝ (gammaLocalGauge B) :=
  fun x => (gammaLocalGauge_hasDerivAt B x).differentiableAt

theorem differentiable_deriv_gammaLocalGauge (B : ℝ) :
    Differentiable ℝ (deriv (gammaLocalGauge B)) :=
  fun x => (gammaLocalGauge_hasDerivAt_deriv B x).differentiableAt

/-- The explicit gauge is strictly admissible on every positive finite horizon. -/
theorem gammaLocalGauge_strictly_admissible {B x : ℝ}
    (hB : 0 < B) (hx : 0 < x) (hxB : x ≤ B) :
    0 < realTrigamma x + deriv (deriv (gammaLocalGauge B)) x := by
  have htri := one_div_sq_le_realTrigamma hx
  have hx2 : x ^ (2 : ℕ) ≤ B ^ (2 : ℕ) := by nlinarith
  have hrecip : 1 / B ^ (2 : ℕ) ≤ 1 / x ^ (2 : ℕ) := one_div_le_one_div_of_le (sq_pos_of_pos hx) hx2
  have hcos : -1 ≤ Real.cos (2 * Real.pi * x) := Real.neg_one_le_cos _
  rw [gammaLocalGauge_deriv2]
  have hcoeff :
      (1 / (2 * B ^ (2 : ℕ) * (2 * Real.pi) ^ (2 : ℕ))) * (2 * Real.pi) ^ (2 : ℕ) =
        1 / (2 * B ^ (2 : ℕ)) := by
    field_simp
  have hcurvature :
      -(1 / (2 * B ^ (2 : ℕ))) ≤
        (1 / (2 * B ^ (2 : ℕ) * (2 * Real.pi) ^ (2 : ℕ))) *
          ((2 * Real.pi) ^ (2 : ℕ) * Real.cos (2 * Real.pi * x)) := by
    rw [← mul_assoc, hcoeff]
    have hnonneg : 0 ≤ 1 / (2 * B ^ (2 : ℕ)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hcos hnonneg]
  have hbase : 1 / B ^ (2 : ℕ) ≤ realTrigamma x := hrecip.trans htri
  have hpositive : 0 < 1 / B ^ (2 : ℕ) := by positivity
  have hhalf : 1 / (2 * B ^ (2 : ℕ)) = (1 / B ^ (2 : ℕ)) / 2 := by ring
  rw [hhalf] at hcurvature
  nlinarith

/-- A globally admissible periodic logarithmic gauge over Gamma is constant. -/
theorem gamma_periodic_curvature_rigidity
    (f : ℝ → ℝ)
    (hperiodic : Periodic f 1)
    (hf' : Differentiable ℝ f)
    (hf'' : Differentiable ℝ (deriv f))
    (hcombined : ∀ x : ℝ, 0 < x →
      0 ≤ realTrigamma x + deriv (deriv f) x) :
    f = fun _ => f 0 :=
  vanishing_background_periodic_curvature_rigidity_of_pos realTrigamma f
    tendsto_realTrigamma_add_nat hperiodic hf' hf'' hcombined

/-- Pointing turns Gamma's global curvature selector into exact gauge reconstruction. -/
theorem gamma_pointed_periodic_curvature_rigidity
    (f : ℝ → ℝ)
    (hperiodic : Periodic f 1)
    (hf' : Differentiable ℝ f)
    (hf'' : Differentiable ℝ (deriv f))
    (hcombined : ∀ x : ℝ, 0 < x →
      0 ≤ realTrigamma x + deriv (deriv f) x)
    (hpoint : f 0 = 0) :
    f = 0 := by
  rw [gamma_periodic_curvature_rigidity f hperiodic hf' hf'' hcombined, hpoint]
  rfl

/-- The admissible pointed periodic gauges visible up to positive horizon `B`. -/
def gammaCurvatureHorizon (B : ℝ) : Set (ℝ → ℝ) :=
  {f | Periodic f 1 ∧ Differentiable ℝ f ∧ Differentiable ℝ (deriv f) ∧ f 0 = 0 ∧
    ∀ x : ℝ, 0 < x → x ≤ B →
      0 ≤ realTrigamma x + deriv (deriv f) x}

/-- The Gamma normalization horizons form a decreasing field of cones. -/
theorem gammaCurvatureHorizon_antitone :
    Antitone gammaCurvatureHorizon := by
  intro B₁ B₂ hB f hf
  exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1,
    fun x hx hxB => hf.2.2.2.2 x hx (hxB.trans hB)⟩

theorem zero_mem_gammaCurvatureHorizon (B : ℝ) :
    (0 : ℝ → ℝ) ∈ gammaCurvatureHorizon B := by
  refine ⟨fun _ => rfl, differentiable_const 0, ?_, rfl, ?_⟩
  · simp
  · intro x hx _
    have htri := one_div_sq_le_realTrigamma hx
    have hnonneg : 0 ≤ 1 / x ^ (2 : ℕ) := by positivity
    simpa using hnonneg.trans htri

/-- Every positive finite normalization horizon has a nonzero pointed periodic gauge. -/
theorem gammaCurvatureHorizon_nontrivial {B : ℝ} (hB : 0 < B) :
    ∃ f ∈ gammaCurvatureHorizon B, f ≠ 0 := by
  refine ⟨gammaLocalGauge B, ?_, gammaLocalGauge_ne_zero hB⟩
  exact ⟨gammaLocalGauge_periodic B, differentiable_gammaLocalGauge B,
    differentiable_deriv_gammaLocalGauge B, gammaLocalGauge_zero B,
    fun x hx hxB => (gammaLocalGauge_strictly_admissible hB hx hxB).le⟩

/-- Every bounded-curvature pointed periodic direction is absorbed by every finite positive
normalization horizon after a sufficiently small positive rescaling.  This is the radial form of
the statement that finite-horizon linearization retains the full residual gauge space. -/
theorem gammaCurvatureHorizon_absorbs_bounded_direction
    {B M : ℝ} (hB : 0 < B) (hM : 0 ≤ M)
    (f : ℝ → ℝ)
    (hperiodic : Periodic f 1)
    (hf' : Differentiable ℝ f)
    (hf'' : Differentiable ℝ (deriv f))
    (hpoint : f 0 = 0)
    (hbound : ∀ x : ℝ, 0 < x → x ≤ B → |deriv (deriv f) x| ≤ M) :
    ∃ ε : ℝ, 0 < ε ∧ (fun x => ε * f x) ∈ gammaCurvatureHorizon B := by
  let ε : ℝ := 1 / (2 * B ^ (2 : ℕ) * (M + 1))
  have hM1 : 0 < M + 1 := by linarith
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  refine ⟨ε, hε, ?_⟩
  have hperiodic_scaled : Periodic (fun x => ε * f x) 1 := by
    simpa [Pi.smul_apply, smul_eq_mul] using hperiodic.smul ε
  refine ⟨hperiodic_scaled, hf'.const_mul ε, ?_, by simp [hpoint], ?_⟩
  · have hderiv : deriv (fun x => ε * f x) = fun x => ε * deriv f x := by
      exact deriv_const_mul_field' ε
    rw [hderiv]
    exact hf''.const_mul ε
  · intro x hx hxB
    have htri := one_div_sq_le_realTrigamma hx
    have hx2 : x ^ (2 : ℕ) ≤ B ^ (2 : ℕ) := by nlinarith
    have hrecip : 1 / B ^ (2 : ℕ) ≤ 1 / x ^ (2 : ℕ) :=
      one_div_le_one_div_of_le (sq_pos_of_pos hx) hx2
    have hbase : 1 / B ^ (2 : ℕ) ≤ realTrigamma x := hrecip.trans htri
    have hbelow : -M ≤ deriv (deriv f) x := neg_le_of_abs_le (hbound x hx hxB)
    have hscaled :
        deriv (deriv (fun y => ε * f y)) x = ε * deriv (deriv f) x := by
      simp only [deriv_const_mul_field']
    rw [hscaled]
    have hεM : ε * M ≤ 1 / (2 * B ^ (2 : ℕ)) := by
      dsimp [ε]
      field_simp
      nlinarith
    have hcurv : -(1 / (2 * B ^ (2 : ℕ))) ≤ ε * deriv (deriv f) x := by
      nlinarith [mul_le_mul_of_nonneg_left hbelow hε.le]
    have hpositive : 0 < 1 / B ^ (2 : ℕ) := by positivity
    have hhalf : 1 / (2 * B ^ (2 : ℕ)) = (1 / B ^ (2 : ℕ)) / 2 := by ring
    rw [hhalf] at hcurv
    nlinarith

/-- A gauge direction is radially admissible at every finite horizon when the positive rescaling
may depend on the horizon. -/
def GammaFiniteHorizonRadial (f : ℝ → ℝ) : Prop :=
  ∀ B : ℝ, 0 < B →
    ∃ ε : ℝ, 0 < ε ∧ (fun x => ε * f x) ∈ gammaCurvatureHorizon B

/-- A gauge direction is uniformly radially admissible cofinally when one positive rescaling works
at every horizon. -/
def GammaCofinalRadial (f : ℝ → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ B : ℝ, 0 < B → (fun x => ε * f x) ∈ gammaCurvatureHorizon B

/-- Pointed twice-differentiable periodic gauges with curvature bounded on every finite positive
horizon are radially admissible horizon by horizon. -/
theorem gammaFiniteHorizonRadial_of_locallyBoundedCurvature
    (f : ℝ → ℝ)
    (hperiodic : Periodic f 1)
    (hf' : Differentiable ℝ f)
    (hf'' : Differentiable ℝ (deriv f))
    (hpoint : f 0 = 0)
    (hloc : ∀ B : ℝ, 0 < B → ∃ M : ℝ, 0 ≤ M ∧
      ∀ x : ℝ, 0 < x → x ≤ B → |deriv (deriv f) x| ≤ M) :
    GammaFiniteHorizonRadial f := by
  intro B hB
  obtain ⟨M, hM, hbound⟩ := hloc B hB
  exact gammaCurvatureHorizon_absorbs_bounded_direction hB hM f hperiodic hf' hf''
    hpoint hbound

/-- A pointed gauge which survives every positive normalization horizon is zero. -/
theorem gammaCurvatureHorizon_cofinal_rigidity
    (f : ℝ → ℝ)
    (hall : ∀ B : ℝ, 0 < B → f ∈ gammaCurvatureHorizon B) :
    f = 0 := by
  have hone := hall 1 one_pos
  apply gamma_pointed_periodic_curvature_rigidity f hone.1 hone.2.1 hone.2.2.1
  · intro x hx
    exact (hall x hx).2.2.2.2 x hx le_rfl
  · exact hone.2.2.2.1

/-- **Gamma normalization-horizon phase transition.**  Every finite positive horizon has
nontrivial gauge, but the cofinal intersection consists exactly of the zero gauge. -/
theorem gammaCurvatureHorizon_cofinal_iff
    (f : ℝ → ℝ) :
    (∀ B : ℝ, 0 < B → f ∈ gammaCurvatureHorizon B) ↔ f = 0 := by
  constructor
  · exact gammaCurvatureHorizon_cofinal_rigidity f
  · rintro rfl B _
    exact zero_mem_gammaCurvatureHorizon B

/-- A direction admits one cofinal positive rescaling exactly when it is zero. -/
theorem gammaCofinalRadial_iff (f : ℝ → ℝ) :
    GammaCofinalRadial f ↔ f = 0 := by
  constructor
  · rintro ⟨ε, hε, hall⟩
    have hscaled : (fun x => ε * f x) = 0 :=
      gammaCurvatureHorizon_cofinal_rigidity (fun x => ε * f x) hall
    funext x
    have hx := congrFun hscaled x
    simp only [Pi.zero_apply] at hx
    exact (mul_eq_zero.mp hx).resolve_left hε.ne'
  · rintro rfl
    refine ⟨1, one_pos, ?_⟩
    intro B _
    simpa using! zero_mem_gammaCurvatureHorizon B

/-- **Gamma radial quantifier-exchange defect.**  Every nonzero regular periodic direction with
locally bounded curvature is admissible after a horizon-dependent rescaling, but no single positive
rescaling works at every horizon. -/
theorem gammaRadial_quantifier_exchange_defect
    (f : ℝ → ℝ)
    (hperiodic : Periodic f 1)
    (hf' : Differentiable ℝ f)
    (hf'' : Differentiable ℝ (deriv f))
    (hpoint : f 0 = 0)
    (hloc : ∀ B : ℝ, 0 < B → ∃ M : ℝ, 0 ≤ M ∧
      ∀ x : ℝ, 0 < x → x ≤ B → |deriv (deriv f) x| ≤ M)
    (hne : f ≠ 0) :
    GammaFiniteHorizonRadial f ∧ ¬ GammaCofinalRadial f := by
  refine ⟨gammaFiniteHorizonRadial_of_locallyBoundedCurvature f hperiodic hf' hf'' hpoint hloc,
    ?_⟩
  rw [gammaCofinalRadial_iff f]
  exact hne

end

end HTGeometry
