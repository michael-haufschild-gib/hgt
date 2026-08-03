import GaloisForLFunctions.HTGeometry.ClockProbeCovectorSlicing

/-!
# Clock probes along a foliation

The slicing reductions all specialise one identity: for any smooth scalar `φ` and any twice
differentiable `w`,

`□ (w ∘ φ) = Γ(φ,φ) · (w'' ∘ φ) + (□φ) · (w' ∘ φ)`.

Both coefficients are geometric invariants of the foliation by level sets of `φ`. Whenever they are
themselves functions of the leaf label — `Γ(φ,φ) = P ∘ φ` and `□φ = R ∘ φ` with `P` nowhere zero —
the clock equation reduces to the linear ordinary equation `P w'' + R w' + V w = 0`, and local
existence for that equation produces clock probes and determines the potential.

This is strictly weaker than asking the chart data themselves to be constant on the leaves: only
the two invariants must be. The chart may vary arbitrarily along the leaves.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped ContDiff

/-! ## The chain rule for the chart d'Alembertian -/

/-- Partial derivatives of a composite: the chain rule in coordinate form. -/
theorem coordPartial_comp {d : ℕ} {φ : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hφ : DifferentiableAt ℝ φ x) {w : ℝ → ℝ} {c : ℝ} (hw : HasDerivAt w c (φ x))
    (i : Fin d) : coordPartial i (fun y => w (φ y)) x = c * coordPartial i φ x := by
  have hcomp := hw.comp_hasFDerivAt x hφ.hasFDerivAt
  have hEq : (w ∘ φ) = fun y => w (φ y) := rfl
  rw [hEq] at hcomp
  rw [coordPartial, hcomp.fderiv, coordPartial]
  simp

theorem differentiableAt_comp {d : ℕ} {φ : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hφ : DifferentiableAt ℝ φ x) {w : ℝ → ℝ} {c : ℝ} (hw : HasDerivAt w c (φ x)) :
    DifferentiableAt ℝ (fun y => w (φ y)) x :=
  (hw.comp_hasFDerivAt x hφ.hasFDerivAt).differentiableAt

/-- **Chain rule for the chart d'Alembertian.** The carré du champ of the level function carries
the second derivative and its d'Alembertian carries the first. -/
theorem dalembert_comp {d : ℕ} (M : SmoothMetricChart d) {φ : (Fin d → ℝ) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {w dw ddw : ℝ → ℝ} {S : Set ℝ} (hS : IsOpen S)
    (hw1 : ∀ t ∈ S, HasDerivAt w (dw t) t)
    (hw2 : ∀ t ∈ S, HasDerivAt dw (ddw t) t)
    {x : Fin d → ℝ} (hx : φ x ∈ S) :
    M.dalembert (fun y => w (φ y)) x
      = M.gradPair φ φ x * ddw (φ x) + M.dalembert φ x * dw (φ x) := by
  have hφd : ∀ y : Fin d → ℝ, DifferentiableAt ℝ φ y := fun y =>
    differentiableAt_of_contDiff_infty hφ y
  have hnhds : φ ⁻¹' S ∈ nhds x := (hS.preimage hφ.continuous).mem_nhds hx
  have hev : ∀ i : Fin d, M.flux (fun y => w (φ y)) i =ᶠ[nhds x]
      fun y => dw (φ y) * M.flux φ i y := by
    intro i
    refine Filter.eventuallyEq_of_mem hnhds ?_
    intro y hy
    have hyS : φ y ∈ S := hy
    have hstep : ∑ j, M.inverseMetric y i j * coordPartial j (fun z => w (φ z)) y
        = dw (φ y) * ∑ j, M.inverseMetric y i j * coordPartial j φ y := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [coordPartial_comp (hφd y) (hw1 _ hyS) j]
      ring
    simp only [SmoothMetricChart.flux]
    rw [hstep]
    ring
  have hcpEq : ∀ i : Fin d, coordPartial i (M.flux (fun y => w (φ y)) i) x
      = coordPartial i (fun y => dw (φ y) * M.flux φ i y) x := by
    intro i
    rw [coordPartial, coordPartial, (hev i).fderiv_eq]
  have hdwφ : DifferentiableAt ℝ (fun y => dw (φ y)) x :=
    differentiableAt_comp (hφd x) (hw2 _ hx)
  have hfluxd : ∀ i : Fin d, DifferentiableAt ℝ (M.flux φ i) x := fun i =>
    differentiableAt_of_contDiff_infty (M.contDiff_flux hφ i) x
  have hsum : ∑ i, coordPartial i (M.flux (fun y => w (φ y)) i) x
      = dw (φ x) * (∑ i, coordPartial i (M.flux φ i) x)
        + ddw (φ x) * (∑ i, coordPartial i φ x * M.flux φ i x) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcpEq i, coordPartial_mul hdwφ (hfluxd i) i,
      coordPartial_comp (hφd x) (hw2 _ hx) i]
    ring
  have hgp : (M.density x)⁻¹ * (∑ i, coordPartial i φ x * M.flux φ i x)
      = M.gradPair φ φ x := M.inv_density_mul_sum_flux φ φ x
  have hdal : (M.density x)⁻¹ * (∑ i, coordPartial i (M.flux φ i) x)
      = M.dalembert φ x := rfl
  rw [SmoothMetricChart.dalembert, hsum]
  calc (M.density x)⁻¹ * (dw (φ x) * (∑ i, coordPartial i (M.flux φ i) x)
        + ddw (φ x) * (∑ i, coordPartial i φ x * M.flux φ i x))
      = ddw (φ x) * ((M.density x)⁻¹ * (∑ i, coordPartial i φ x * M.flux φ i x))
        + dw (φ x) * ((M.density x)⁻¹ * (∑ i, coordPartial i (M.flux φ i) x)) := by ring
    _ = M.gradPair φ φ x * ddw (φ x) + M.dalembert φ x * dw (φ x) := by
        rw [hgp, hdal]; ring

/-! ## Local existence for the general linear second-order equation -/

/-- Autonomised first-order field of `u'' + p u' + q u = 0`. -/
noncomputable def linField (p q : ℝ → ℝ) : (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ) :=
  fun z => (1, z.2.2, -(p z.1) * z.2.2 - (q z.1) * z.2.1)

theorem contDiff_linField {p q : ℝ → ℝ} (hp : ContDiff ℝ 1 p) (hq : ContDiff ℝ 1 q) :
    ContDiff ℝ 1 (linField p q) := by
  refine ContDiff.prodMk contDiff_const (ContDiff.prodMk ?_ ?_)
  · exact contDiff_snd.comp contDiff_snd
  · exact (((hp.comp contDiff_fst).neg).mul (contDiff_snd.comp contDiff_snd)).sub
      ((hq.comp contDiff_fst).mul (contDiff_fst.comp contDiff_snd))

/-- **Local existence for the general linear second-order equation.** -/
theorem exists_localLinearProbe {p q : ℝ → ℝ} (hp : ContDiff ℝ 1 p) (hq : ContDiff ℝ 1 q)
    (a : ℝ) :
    ∃ (w dw ddw : ℝ → ℝ) (ε : ℝ), 0 < ε ∧ w a = 1 ∧
      (∀ t ∈ Ioo (a - ε) (a + ε), HasDerivAt w (dw t) t) ∧
      (∀ t ∈ Ioo (a - ε) (a + ε), HasDerivAt dw (ddw t) t) ∧
      (∀ t : ℝ, ddw t + p t * dw t + q t * w t = 0) := by
  obtain ⟨α, hα0, ε, hε, hode⟩ :=
    (contDiff_linField hp
        hq).contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
      (x₀ := ((a, 1, 0) : ℝ × ℝ × ℝ)) 0
  have hIoo : ∀ t : ℝ, t ∈ Ioo (-ε) ε → t ∈ Ioo (0 - ε) (0 + ε) := by
    intro t ht
    simpa using ht
  have hcomp1 : ∀ t ∈ Ioo (-ε) ε, HasDerivAt (fun s => (α s).1) 1 t := by
    intro t ht
    exact projOne.hasFDerivAt.comp_hasDerivAt t (hode t (hIoo t ht))
  have hcomp2 : ∀ t ∈ Ioo (-ε) ε, HasDerivAt (fun s => (α s).2.1) ((α t).2.2) t := by
    intro t ht
    exact projTwo.hasFDerivAt.comp_hasDerivAt t (hode t (hIoo t ht))
  have hcomp3 : ∀ t ∈ Ioo (-ε) ε, HasDerivAt (fun s => (α s).2.2)
      (-(p ((α t).1)) * (α t).2.2 - (q ((α t).1)) * (α t).2.1) t := by
    intro t ht
    exact projThree.hasFDerivAt.comp_hasDerivAt t (hode t (hIoo t ht))
  have haffine := first_component_affine hε hα0 hcomp1
  have hshift : ∀ y : ℝ, HasDerivAt (fun z : ℝ => z - a) 1 y := by
    intro y
    simpa using (hasDerivAt_id y).sub_const a
  refine ⟨fun t => (α (t - a)).2.1, fun t => (α (t - a)).2.2,
    fun t => -(p t) * (α (t - a)).2.2 - (q t) * (α (t - a)).2.1, ε, hε, ?_, ?_, ?_, ?_⟩
  · simp [hα0]
  · intro t ht
    have hta : t - a ∈ Ioo (-ε) ε := by
      obtain ⟨h1, h2⟩ := ht
      constructor <;> linarith
    have hc := (hcomp2 (t - a) hta).comp t (hshift t)
    rw [mul_one] at hc
    exact hc
  · intro t ht
    have hta : t - a ∈ Ioo (-ε) ε := by
      obtain ⟨h1, h2⟩ := ht
      constructor <;> linarith
    have hc := (hcomp3 (t - a) hta).comp t (hshift t)
    rw [mul_one, haffine (t - a) hta] at hc
    have hxx : a + (t - a) = t := by ring
    rw [hxx] at hc
    exact hc
  · intro t
    ring

/-! ## Clock probes and determination along a foliation -/

/-- **Clock probes along a foliation whose invariants are functions of the leaf label.** -/
theorem exists_foliation_localProbe {d : ℕ} {M : SmoothMetricChart d}
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) {P R : ℝ → ℝ}
    (hP : ∀ x, M.gradPair φ φ x = P (φ x))
    (hR : ∀ x, M.dalembert φ x = R (φ x))
    (hPc : ContDiff ℝ 1 P) (hRc : ContDiff ℝ 1 R) (hP0 : ∀ t, P t ≠ 0)
    {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) (a : ℝ) :
    ∃ (u : (Fin d → ℝ) → ℝ) (ε : ℝ), 0 < ε ∧
      (∀ x : Fin d → ℝ, φ x = a → u x = 1) ∧
      (∀ x : Fin d → ℝ, φ x ∈ Ioo (a - ε) (a + ε) →
        SolvesPotentialWaveAt M.dalembert (fun y => V (φ y)) u x) := by
  obtain ⟨w, dw, ddw, ε, hε, hwa, hd1, hd2, heq⟩ :=
    exists_localLinearProbe (hRc.div hPc hP0) (hV.div hPc hP0) a
  refine ⟨fun y => w (φ y), ε, hε, ?_, ?_⟩
  · intro x hx
    show w (φ x) = 1
    rw [hx, hwa]
  · intro x hx
    have hred := dalembert_comp M hφ isOpen_Ioo hd1 hd2 hx
    have hPne := hP0 (φ x)
    have hE : ddw (φ x) + R (φ x) / P (φ x) * dw (φ x)
        + V (φ x) / P (φ x) * w (φ x) = 0 := heq (φ x)
    have hPR : P (φ x) * (R (φ x) / P (φ x)) = R (φ x) := by field_simp
    have hPV : P (φ x) * (V (φ x) / P (φ x)) = V (φ x) := by field_simp
    have hzero : P (φ x) * (ddw (φ x) + R (φ x) / P (φ x) * dw (φ x)
        + V (φ x) / P (φ x) * w (φ x)) = 0 := by rw [hE]; ring
    have hmul : P (φ x) * ddw (φ x) + R (φ x) * dw (φ x) + V (φ x) * w (φ x) = 0 := by
      calc P (φ x) * ddw (φ x) + R (φ x) * dw (φ x) + V (φ x) * w (φ x)
          = P (φ x) * ddw (φ x) + P (φ x) * (R (φ x) / P (φ x)) * dw (φ x)
            + P (φ x) * (V (φ x) / P (φ x)) * w (φ x) := by rw [hPR, hPV]
        _ = P (φ x) * (ddw (φ x) + R (φ x) / P (φ x) * dw (φ x)
            + V (φ x) / P (φ x) * w (φ x)) := by ring
        _ = 0 := hzero
    show M.dalembert (fun y => w (φ y)) x + V (φ x) * w (φ x) = 0
    rw [hred, hP x, hR x]
    linarith [hmul]

/-- **Determination of the potential along a foliation, unconditionally.** -/
theorem chartPotential_eq_of_foliation {d : ℕ} {M : SmoothMetricChart d}
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) {P R : ℝ → ℝ}
    (hP : ∀ x, M.gradPair φ φ x = P (φ x))
    (hR : ∀ x, M.dalembert φ x = R (φ x))
    (hPc : ContDiff ℝ 1 P) (hRc : ContDiff ℝ 1 R) (hP0 : ∀ t, P t ≠ 0)
    {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) {other : (Fin d → ℝ) → ℝ}
    (hother : ∀ (b : ℝ) (u : (Fin d → ℝ) → ℝ) (ε : ℝ), 0 < ε →
      (∀ x : Fin d → ℝ, φ x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt M.dalembert (fun y => V (φ y)) u x) →
      (∀ x : Fin d → ℝ, φ x ∈ Ioo (b - ε) (b + ε) →
        SolvesPotentialWaveAt M.dalembert other u x)) :
    other = fun y => V (φ y) := by
  funext x
  obtain ⟨u, ε, hε, hu1, hsolve⟩ :=
    exists_foliation_localProbe hφ hP hR hPc hRc hP0 hV (φ x)
  have hx : φ x ∈ Ioo (φ x - ε) (φ x + ε) := by constructor <;> linarith
  refine potential_eq_of_solvesPotentialWaveAt
    (hother (φ x) u ε hε hsolve x hx) (hsolve x hx) ?_
  rw [hu1 x rfl]
  exact one_ne_zero

end GaloisForLFunctions.HTGeometry
