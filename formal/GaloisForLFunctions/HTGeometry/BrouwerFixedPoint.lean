import GaloisForLFunctions.HTGeometry.SmoothNoRetraction
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Brouwer's fixed point theorem

A continuous self-map of the closed unit ball of a finite-dimensional real inner product space has a
fixed point.  A fixed-point-free map would produce a `C¹` retraction of the ball onto its boundary
sphere — send `x` to the point where the ray from `f x` through `x` leaves the ball — which the
no-retraction theorem forbids.  The continuous case follows from the differentiable one by uniform
approximation: a map without fixed points has displacement bounded below on the compact ball, and a
sufficiently close smooth approximation, rescaled back into the ball, would have to fix a point.

A compact set carrying a continuous retraction of the ambient space inherits the fixed point
property; this is the form in which the Poincaré–Miranda theorem uses it for a box.
-/

open MeasureTheory Metric Set Filter

namespace GaloisForLFunctions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Brouwer's fixed point theorem, differentiable case.**  A `C¹` self-map of the closed unit
ball has a fixed point. -/
theorem exists_fixedPoint_of_contDiffOn {f : E → E} {U : Set E} (hU : IsOpen U)
    (hBU : closedBall (0 : E) 1 ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hmaps : ∀ x ∈ closedBall (0 : E) 1, f x ∈ closedBall (0 : E) 1) :
    ∃ x ∈ closedBall (0 : E) 1, f x = x := by
  classical
  by_contra hcon
  push Not at hcon
  set d : E → E := fun x => x - f x with hddef
  set u : E → E := fun x => ‖d x‖⁻¹ • d x with hudef
  set a : E → ℝ := fun x => inner ℝ x (u x) with hadef
  set D : E → ℝ := fun x => (a x) ^ 2 + 1 - ‖x‖ ^ 2 with hDdef
  set τ : E → ℝ := fun x => -(a x) + Real.sqrt (D x) with hτdef
  set ρ : E → E := fun x => x + (τ x) • (u x) with hρdef
  -- on the ball the difference is nonzero
  have hdne : ∀ x ∈ closedBall (0 : E) 1, d x ≠ 0 := by
    intro x hx hzero
    exact hcon x hx (by
      have : x = f x := sub_eq_zero.mp hzero
      exact this.symm)
  have hunorm : ∀ x, d x ≠ 0 → ‖u x‖ = 1 := by
    intro x hx
    rw [hudef]
    simp only
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    field_simp
  -- positivity of the discriminant on the ball
  have hDpos : ∀ x ∈ closedBall (0 : E) 1, 0 < D x := by
    intro x hx
    rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hx) with hlt | heq
    · have h1 : ‖x‖ ^ 2 < 1 := by nlinarith [norm_nonneg x]
      have h2 : 0 ≤ (a x) ^ 2 := sq_nonneg _
      rw [hDdef]
      simp only
      linarith
    · -- ‖x‖ = 1 : the discriminant is a x ^ 2 and a x ≠ 0
      have hane : a x ≠ 0 := by
        intro h0
        have hdx : d x ≠ 0 := hdne x hx
        have hinner0 : (inner ℝ x (d x) : ℝ) = 0 := by
          have : (inner ℝ x (u x) : ℝ) = ‖d x‖⁻¹ * inner ℝ x (d x) := by
            rw [hudef]
            simp only
            rw [real_inner_smul_right]
          rw [hadef] at h0
          simp only at h0
          rw [this] at h0
          have hnormne : ‖d x‖⁻¹ ≠ 0 := by
            simp [norm_ne_zero_iff.mpr hdx]
          exact (mul_eq_zero.mp h0).resolve_left hnormne
        -- ⟪x, x - f x⟫ = 0 forces ‖x - f x‖ ^ 2 ≤ 0
        have hfx : ‖f x‖ ≤ 1 := mem_closedBall_zero_iff.mp (hmaps x hx)
        have hxfx : (inner ℝ x (f x) : ℝ) = 1 := by
          have hexp : (inner ℝ x (d x) : ℝ) = inner ℝ x x - inner ℝ x (f x) := by
            rw [hddef]
            simp only
            rw [inner_sub_right]
          rw [hinner0, real_inner_self_eq_norm_sq, heq] at hexp
          norm_num at hexp
          linarith
        have hsq : ‖d x‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x (f x) + ‖f x‖ ^ 2 := by
          rw [hddef]
          simp only
          rw [← real_inner_self_eq_norm_sq, inner_sub_sub_self]
          rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
            real_inner_comm (f x) x]
          ring
        rw [hxfx, heq] at hsq
        have : ‖d x‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg (f x)]
        have : ‖d x‖ = 0 := by nlinarith [norm_nonneg (d x)]
        exact hdne x hx (norm_eq_zero.mp this)
      rw [hDdef]
      simp only [heq]
      have : (0:ℝ) < (a x) ^ 2 := by positivity
      norm_num
      linarith
  -- the open set where the retraction formula is smooth
  have hdcont : ContinuousOn d U := continuousOn_id.sub hf.continuousOn
  set V : Set E := U ∩ (d ⁻¹' ({(0 : E)}ᶜ)) with hVdef
  have hVopen : IsOpen V := hdcont.isOpen_inter_preimage hU isOpen_compl_singleton
  have hVd : ∀ x ∈ V, d x ≠ 0 := fun x hx => hx.2
  have hVU : V ⊆ U := fun x hx => hx.1
  have hDcont : ContinuousOn D V := by
    have h1 : ContinuousOn d V := hdcont.mono hVU
    have h2 : ContinuousOn (fun x => ‖d x‖⁻¹) V := by
      refine ContinuousOn.inv₀ (h1.norm) ?_
      intro x hx
      simpa using hVd x hx
    have h3 : ContinuousOn u V := h2.smul h1
    have h4 : ContinuousOn a V := continuousOn_id.inner h3
    exact ((h4.pow 2).add continuousOn_const).sub ((continuousOn_id.norm).pow 2)
  set W : Set E := V ∩ (D ⁻¹' (Ioi 0)) with hWdef
  have hWopen : IsOpen W := hDcont.isOpen_inter_preimage hVopen isOpen_Ioi
  have hBW : closedBall (0 : E) 1 ⊆ W := by
    intro x hx
    exact ⟨⟨hBU hx, hdne x hx⟩, hDpos x hx⟩
  -- the retraction is continuously differentiable there
  have hρsmooth : ContDiffOn ℝ 1 ρ W := by
    intro x hx
    have hxU : x ∈ U := hx.1.1
    have hdx : d x ≠ 0 := hx.1.2
    have hDx : 0 < D x := hx.2
    have hdC : ContDiffAt ℝ 1 d x := (contDiffOn_id.sub hf).contDiffAt (hU.mem_nhds hxU)
    have hnC : ContDiffAt ℝ 1 (fun y => ‖d y‖) x := hdC.norm ℝ hdx
    have hiC : ContDiffAt ℝ 1 (fun y => ‖d y‖⁻¹) x := by
      have := hnC.inv (by simpa using hdx)
      exact this
    have huC : ContDiffAt ℝ 1 u x := hiC.smul hdC
    have haC : ContDiffAt ℝ 1 a x := contDiffAt_id.inner ℝ huC
    have hDC : ContDiffAt ℝ 1 D x :=
      ((haC.pow 2).add contDiffAt_const).sub ((contDiff_norm_sq ℝ).contDiffAt)
    have hτC : ContDiffAt ℝ 1 τ x := (haC.neg).add (hDC.sqrt (ne_of_gt hDx))
    exact (contDiffAt_id.add (hτC.smul huC)).contDiffWithinAt
  -- it takes values on the unit sphere over the ball
  have hsphereρ : ∀ x ∈ closedBall (0 : E) 1, ‖ρ x‖ = 1 := by
    intro x hx
    have hdx : d x ≠ 0 := hdne x hx
    have hu1 : ‖u x‖ = 1 := hunorm x hdx
    have hD : 0 ≤ D x := (hDpos x hx).le
    have hsqrt : Real.sqrt (D x) ^ 2 = D x := Real.sq_sqrt hD
    have hexp : ‖ρ x‖ ^ 2 = ‖x‖ ^ 2 + 2 * (τ x * a x) + (τ x) ^ 2 := by
      rw [hρdef]
      simp only
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hu1, mul_one,
        sq_abs]
    have hval : ‖ρ x‖ ^ 2 = 1 := by
      rw [hexp, hτdef]
      simp only
      have hDeq : D x = (a x) ^ 2 + 1 - ‖x‖ ^ 2 := by rw [hDdef]
      nlinarith [hsqrt, hDeq]
    nlinarith [norm_nonneg (ρ x), hval]
  -- and it fixes the boundary sphere
  have hfixρ : ∀ x, ‖x‖ = 1 → ρ x = x := by
    intro x hx1
    have hxB : x ∈ closedBall (0 : E) 1 := mem_closedBall_zero_iff.mpr (le_of_eq hx1)
    have hdx : d x ≠ 0 := hdne x hxB
    have hfx : ‖f x‖ ≤ 1 := mem_closedBall_zero_iff.mp (hmaps x hxB)
    have hage : 0 ≤ a x := by
      have hinner : (inner ℝ x (d x) : ℝ) = ‖x‖ ^ 2 - inner ℝ x (f x) := by
        rw [hddef]
        simp only
        rw [inner_sub_right, real_inner_self_eq_norm_sq]
      have hcs : (inner ℝ x (f x) : ℝ) ≤ ‖x‖ * ‖f x‖ := real_inner_le_norm x (f x)
      have hnn : 0 ≤ (inner ℝ x (d x) : ℝ) := by
        rw [hinner, hx1]
        nlinarith
      have hsc : a x = ‖d x‖⁻¹ * inner ℝ x (d x) := by
        rw [hadef, hudef]
        simp only
        rw [real_inner_smul_right]
      rw [hsc]
      have : (0:ℝ) ≤ ‖d x‖⁻¹ := by positivity
      exact mul_nonneg this hnn
    have hτ0 : τ x = 0 := by
      have hDeq : D x = (a x) ^ 2 := by
        rw [hDdef]
        simp only [hx1]
        norm_num
      rw [hτdef]
      simp only
      rw [hDeq, Real.sqrt_sq hage]
      ring
    rw [hρdef]
    simp only [hτ0, zero_smul, add_zero]
  exact GaloisForLFunctions.no_contDiff_retraction_closedBall ((Module.finBasis ℝ E).addHaar) hWopen hBW hρsmooth
    hsphereρ hfixρ

/-- **Brouwer's fixed point theorem for the closed unit ball.** -/
theorem exists_fixedPoint_closedBall {f : E → E} (hf : Continuous f)
    (hmaps : ∀ x ∈ closedBall (0 : E) 1, f x ∈ closedBall (0 : E) 1) :
    ∃ x ∈ closedBall (0 : E) 1, f x = x := by
  classical
  -- a continuous retraction of the whole space onto the ball
  set r : E → E := fun x => (max 1 ‖x‖)⁻¹ • x with hrdef
  have hrcont : Continuous r := by
    refine Continuous.smul ?_ continuous_id
    exact (continuous_const.max continuous_norm).inv₀ (fun x => by positivity)
  have hrmem : ∀ x : E, r x ∈ closedBall (0 : E) 1 := by
    intro x
    rw [mem_closedBall_zero_iff, hrdef]
    simp only
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one (le_max_left _ _))]
    rw [inv_mul_le_iff₀ (by positivity)]
    simp
  have hrid : ∀ x ∈ closedBall (0 : E) 1, r x = x := by
    intro x hx
    have : max 1 ‖x‖ = 1 := max_eq_left (mem_closedBall_zero_iff.mp hx)
    rw [hrdef]
    simp [this]
  set F : E → E := fun x => f (r x) with hFdef
  have hFcont : Continuous F := hf.comp hrcont
  have hFmem : ∀ x : E, F x ∈ closedBall (0 : E) 1 := fun x => hmaps (r x) (hrmem x)
  by_contra hcon
  push Not at hcon
  have hFnofix : ∀ x : E, F x ≠ x := by
    intro x hx
    have hxB : x ∈ closedBall (0 : E) 1 := hx ▸ hFmem x
    have hfx : f x = x := by
      have hFx : F x = f x := by
        rw [hFdef]
        simp [hrid x hxB]
      rw [← hFx]
      exact hx
    exact hcon x hxB hfx
  -- the displacement is bounded below on the ball
  obtain ⟨x₀, hx₀B, hx₀min⟩ := (isCompact_closedBall (0 : E) 1).exists_isMinOn
    (nonempty_closedBall.mpr zero_le_one)
    ((hFcont.sub continuous_id).norm).continuousOn
  set δ : ℝ := ‖F x₀ - x₀‖ with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef, norm_pos_iff, sub_ne_zero]
    exact hFnofix x₀
  have hδle : ∀ x ∈ closedBall (0 : E) 1, δ ≤ ‖F x - x‖ := fun x hx => hx₀min hx
  -- smooth approximation
  have happrox : ∃ g : E → E, ContDiff ℝ 1 g ∧ ∀ x, ‖g x - F x‖ < δ / 4 := by
    have hconv : ∀ x : E, Convex ℝ (ball (F x) (δ / 4)) := fun x => convex_ball _ _
    have hloc : ∀ x : E, ∃ V ∈ nhds x, ∃ g : E → E,
        ContMDiffOn (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ((1 : ℕ∞) : WithTop ℕ∞)
          g V ∧ ∀ y ∈ V, g y ∈ ball (F y) (δ / 4) := by
      intro x
      refine ⟨F ⁻¹' (ball (F x) (δ / 4)),
        hFcont.continuousAt (ball_mem_nhds _ (by positivity)), fun _ => F x, contMDiffOn_const, ?_⟩
      intro y hy
      rw [mem_ball, dist_comm]
      exact hy
    obtain ⟨g, hg⟩ :=
      exists_contMDiffMap_forall_mem_convex_of_local (modelWithCornersSelf ℝ E) hconv hloc
    refine ⟨g, ?_, fun x => ?_⟩
    · exact contMDiff_iff_contDiff.mp g.contMDiff
    · have := hg x
      rw [mem_ball, dist_eq_norm] at this
      exact this
  obtain ⟨g, hgsmooth, hgclose⟩ := happrox
  -- rescale so that it maps the ball into itself
  set c : ℝ := (1 + δ / 4)⁻¹ with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  set h : E → E := fun x => c • g x with hhdef
  have hhsmooth : ContDiff ℝ 1 h := hgsmooth.const_smul c
  have hgbound : ∀ x, ‖g x‖ ≤ 1 + δ / 4 := by
    intro x
    have h1 : ‖g x - F x‖ < δ / 4 := hgclose x
    have h2 : ‖F x‖ ≤ 1 := mem_closedBall_zero_iff.mp (hFmem x)
    calc ‖g x‖ = ‖(g x - F x) + F x‖ := by abel_nf
      _ ≤ ‖g x - F x‖ + ‖F x‖ := norm_add_le _ _
      _ ≤ 1 + δ / 4 := by linarith
  have hhmaps : ∀ x ∈ closedBall (0 : E) 1, h x ∈ closedBall (0 : E) 1 := by
    intro x _
    rw [mem_closedBall_zero_iff, hhdef]
    simp only
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcpos.le, hcdef]
    rw [inv_mul_le_iff₀ (by positivity)]
    simpa using hgbound x
  obtain ⟨y, hyB, hyfix⟩ :=
    exists_fixedPoint_of_contDiffOn isOpen_univ (subset_univ _) hhsmooth.contDiffOn hhmaps
  -- the fixed point of the approximation nearly fixes `F`
  have hclose : ‖h y - g y‖ ≤ δ / 4 := by
    have hexp : h y - g y = (c - 1) • g y := by
      rw [hhdef]
      simp only
      rw [sub_smul, one_smul]
    rw [hexp, norm_smul, Real.norm_eq_abs]
    have hcle : |c - 1| = 1 - c := by
      rw [abs_of_nonpos]
      · ring
      · rw [hcdef, sub_nonpos, inv_le_one_iff₀]
        right; linarith
    rw [hcle]
    have h1 : (1 - c) * (1 + δ / 4) = δ / 4 := by
      rw [hcdef]
      field_simp
      ring
    calc (1 - c) * ‖g y‖ ≤ (1 - c) * (1 + δ / 4) := by
          have : 0 ≤ 1 - c := by
            rw [hcdef, sub_nonneg, inv_le_one_iff₀]
            right; linarith
          exact mul_le_mul_of_nonneg_left (hgbound y) this
      _ = δ / 4 := h1
  have hfinal : ‖F y - y‖ < δ := by
    have hy : y = h y := hyfix.symm
    calc ‖F y - y‖ = ‖F y - h y‖ := by rw [← hy]
      _ ≤ ‖F y - g y‖ + ‖g y - h y‖ := by
          have := norm_add_le (F y - g y) (g y - h y)
          simpa using this
      _ < δ / 4 + δ / 4 := by
          have h1 : ‖F y - g y‖ < δ / 4 := by
            rw [← norm_neg]
            simpa using hgclose y
          have h2 : ‖g y - h y‖ ≤ δ / 4 := by
            rw [← norm_neg]
            simpa using hclose
          linarith
      _ < δ := by linarith
  exact absurd (hδle y hyB) (not_le.mpr hfinal)

/-- Brouwer's fixed point theorem for a ball of arbitrary positive radius. -/
theorem exists_fixedPoint_closedBall_radius {R : ℝ} (hR : 0 < R) {f : E → E} (hf : Continuous f)
    (hmaps : ∀ x ∈ closedBall (0 : E) R, f x ∈ closedBall (0 : E) R) :
    ∃ x ∈ closedBall (0 : E) R, f x = x := by
  set f' : E → E := fun x => R⁻¹ • f (R • x) with hf'def
  have hf'cont : Continuous f' := (hf.comp (continuous_const_smul R)).const_smul _
  have hf'maps : ∀ x ∈ closedBall (0 : E) 1, f' x ∈ closedBall (0 : E) 1 := by
    intro x hx
    have hxR : R • x ∈ closedBall (0 : E) R := by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hR.le]
      have := mem_closedBall_zero_iff.mp hx
      nlinarith [norm_nonneg x]
    have hval := mem_closedBall_zero_iff.mp (hmaps _ hxR)
    rw [mem_closedBall_zero_iff, hf'def]
    simp only
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg hR.le]
    rw [inv_mul_le_iff₀ hR]
    simpa using hval
  obtain ⟨x, hx, hfx⟩ := exists_fixedPoint_closedBall hf'cont hf'maps
  refine ⟨R • x, ?_, ?_⟩
  · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hR.le]
    have := mem_closedBall_zero_iff.mp hx
    nlinarith [norm_nonneg x]
  · have h := congrArg (fun y : E => R • y) hfx
    simp only [hf'def] at h
    rw [smul_inv_smul₀ hR.ne'] at h
    exact h

/-- **Fixed point property of a compact retract.**  If a bounded set `K` is the image of a
continuous retraction of the whole space, every continuous self-map of `K` has a fixed point. -/
theorem exists_fixedPoint_of_retraction {K : Set E} {P : E → E} (hP : Continuous P)
    (hPmem : ∀ x, P x ∈ K) (hPid : ∀ x ∈ K, P x = x) (hKb : Bornology.IsBounded K)
    {T : E → E} (hT : Continuous T) (hTmaps : ∀ x ∈ K, T x ∈ K) :
    ∃ x ∈ K, T x = x := by
  obtain ⟨R₀, hR₀⟩ := hKb.subset_closedBall (0 : E)
  set R : ℝ := max R₀ 1 with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hKR : K ⊆ closedBall (0 : E) R := hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hScont : Continuous (T ∘ P) := hT.comp hP
  have hSmaps : ∀ x ∈ closedBall (0 : E) R, (T ∘ P) x ∈ closedBall (0 : E) R := fun x _ =>
    hKR (hTmaps (P x) (hPmem x))
  obtain ⟨y, _, hy⟩ := exists_fixedPoint_closedBall_radius hRpos hScont hSmaps
  have hyK : y ∈ K := by
    rw [← hy]
    exact hTmaps (P y) (hPmem y)
  refine ⟨y, hyK, ?_⟩
  have hPy : P y = y := hPid y hyK
  have := hy
  simp only [Function.comp_apply, hPy] at this
  exact this

end GaloisForLFunctions
