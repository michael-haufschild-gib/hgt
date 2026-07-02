/-
# The m-step branch `ψ = bottcherCoord ∘ f^[N]` — the concrete construction

For a viable parameter, `exists_clearance_escapeOpen` produces a window ball `ball 0 r` (`r > 1`,
crossing `u₀`'s natural boundary `|z| = 1`) all of whose points land in the escape region
`escapeOpen b` after a uniform number of steps `N`.  The m-step branch is then simply

    ψ(z) = bottcherCoord b (f_b^[N] z),

the genuine Böttcher coordinate `N` steps ahead — NO per-step normalization, NO root extraction.
It is analytic on the window ball (composition of the polynomial iterate `f^[N]` with the slit-free
`analyticOnNhd_bottcherCoord_full`) and nowhere zero.  This is the concrete branch that the
branch-conditional capstone `U0MStepBranch.u0_mstep_independence_of_branch` consumes; the sole
remaining input to the UNCONDITIONAL m-step independence is its transcendence over `ℂ(z)`, which is
the far-Böttcher transcendence `Bottcher.bottcher_transcendental_far` transported along `f^[N]`
(the `pMapB`/`descend_algebraicP` descent, exactly as in `phiB_transcendental`).
-/
import GaloisForLFunctions.U0.U0MStepBranch
import GaloisForLFunctions.Bottcher.BottcherCoord

open Complex Set Bottcher Metric Filter Topology
open U0MStepBranch

namespace U0PhiMStep

/-- Persistence of the escape region under one step: `max 2 ‖b‖ < ‖w‖ ⟹ max 2 ‖b‖ < ‖f_b w‖`. -/
theorem escapeOpen_persist {b w : ℂ} (hw : max 2 ‖b‖ < ‖w‖) :
    max 2 ‖b‖ < ‖quadratic b w‖ := by
  have hM2 : (2 : ℝ) ≤ max 2 ‖b‖ := le_max_left _ _
  have hMb : ‖b‖ ≤ max 2 ‖b‖ := le_max_right _ _
  have hstep : ‖w‖ ^ 2 - ‖b‖ ≤ ‖quadratic b w‖ := by
    have : ‖w ^ 2‖ - ‖b‖ ≤ ‖w ^ 2 + b‖ := by
      have := norm_sub_norm_le (w ^ 2) (-b)
      simpa [sub_neg_eq_add] using this
    rwa [norm_pow] at this
  nlinarith [hstep, hw, hM2, hMb, norm_nonneg w]

/-- **Uniform clearance into the escape region.**  For `2 < ‖b‖`, if the closed unit disk avoids
`K_b`, a strictly larger disk `D̄(0,r)` (`r > 1`) lands in `escapeOpen b` after a uniform number of
steps `N` — the window on which the Böttcher branch `bottcherCoord ∘ f^[N]` is analytic. -/
theorem exists_clearance_escapeOpen {b : ℂ}
    (hviab : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b) :
    ∃ r : ℝ, 1 < r ∧ ∃ N : ℕ,
      ∀ z : ℂ, ‖z‖ ≤ r → (quadratic b)^[N] z ∈ escapeOpen b := by
  set A : ℕ → Set ℂ := fun N => {z : ℂ | max 2 ‖b‖ < ‖(quadratic b)^[N] z‖} with hA
  have hAopen : ∀ N, IsOpen (A N) := by
    intro N
    exact isOpen_lt continuous_const
      (continuous_norm.comp ((continuous_quadratic b).iterate N))
  have hAmono : ∀ {M N : ℕ}, M ≤ N → A M ⊆ A N := by
    intro M N hMN z hz
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hMN
    have hstep : ∀ j : ℕ, max 2 ‖b‖ < ‖(quadratic b)^[M] z‖ →
        max 2 ‖b‖ < ‖(quadratic b)^[M + j] z‖ := by
      intro j
      induction j with
      | zero => intro h; rwa [Nat.add_zero]
      | succ k ih =>
        intro h0
        rw [show M + (k + 1) = (M + k) + 1 from rfl, Function.iterate_succ_apply']
        exact escapeOpen_persist (ih h0)
    exact hstep d hz
  have hcover : closedBall (0 : ℂ) 1 ⊆ ⋃ N, A N := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hz
    obtain ⟨N, hN⟩ := exists_orbit_gt (hviab z hz1) (max 2 ‖b‖)
    exact mem_iUnion.mpr ⟨N, hN⟩
  obtain ⟨t, ht⟩ := (isCompact_closedBall (0 : ℂ) 1).elim_finite_subcover A hAopen hcover
  have hsub : closedBall (0 : ℂ) 1 ⊆ A (t.sup id) := by
    intro z hz
    obtain ⟨i, hit, hzi⟩ := mem_iUnion₂.mp (ht hz)
    exact hAmono (Finset.le_sup (f := id) hit) hzi
  obtain ⟨δ, hδpos, hδ⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open (hAopen (t.sup id)) hsub
  refine ⟨1 + δ / 2, by linarith, t.sup id, ?_⟩
  intro z hz
  have hzin : z ∈ thickening δ (closedBall (0 : ℂ) 1) := by
    rw [Metric.mem_thickening_iff]
    by_cases h1 : ‖z‖ ≤ 1
    · exact ⟨z, by simpa [mem_closedBall, dist_zero_right] using h1, by simpa using hδpos⟩
    · push Not at h1
      have hzpos : (0 : ℝ) < ‖z‖ := by linarith
      have hzne : (‖z‖ : ℝ) ≠ 0 := ne_of_gt hzpos
      refine ⟨(‖z‖)⁻¹ • z, ?_, ?_⟩
      · rw [mem_closedBall, dist_zero_right, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hzne]
      · rw [dist_eq_norm]
        have hcalc : z - (‖z‖)⁻¹ • z = ((1 - (‖z‖)⁻¹ : ℝ)) • z := by
          rw [sub_smul, one_smul]
        rw [hcalc, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (by rw [sub_nonneg]; exact inv_le_one_of_one_le₀ h1.le)]
        have : (1 - (‖z‖)⁻¹) * ‖z‖ = ‖z‖ - 1 := by field_simp
        rw [this]; linarith
  exact hδ hzin

/-- **The m-step branch** `ψ = bottcherCoord b ∘ f_b^[N]`. -/
noncomputable def psiN (b : ℂ) (N : ℕ) : ℂ → ℂ := fun z => bottcherCoord b ((quadratic b)^[N] z)

theorem psiN_ne_zero (b : ℂ) (N : ℕ) (z : ℂ) : psiN b N z ≠ 0 :=
  bottcherCoord_ne_zero b _

/-- The quadratic map is analytic everywhere. -/
theorem analyticAt_quadratic (b w : ℂ) : AnalyticAt ℂ (quadratic b) w := by
  have : quadratic b = fun z => z ^ 2 + b := rfl
  rw [this]
  exact (analyticAt_id.pow 2).add analyticAt_const

/-- The iterate `f^[N]` is analytic everywhere. -/
theorem analyticAt_iterate (b : ℂ) (N : ℕ) (w : ℂ) :
    AnalyticAt ℂ (fun u => (quadratic b)^[N] u) w := by
  induction N generalizing w with
  | zero => simpa using analyticAt_id
  | succ k ih =>
    have hcomp : (fun u => (quadratic b)^[k + 1] u)
        = (quadratic b) ∘ (fun u => (quadratic b)^[k] u) := by
      funext u; rw [Function.iterate_succ_apply']; rfl
    rw [hcomp]
    exact (analyticAt_quadratic b _).comp (ih w)

/-- **`ψ` is analytic on the window ball**: `f^[N]` is a polynomial iterate and lands in
`escapeOpen b`, where the Böttcher coordinate is analytic (slit-free). -/
theorem psiN_analyticOnNhd {b : ℂ} {r : ℝ} {N : ℕ}
    (hcl : ∀ z : ℂ, ‖z‖ ≤ r → (quadratic b)^[N] z ∈ escapeOpen b) :
    AnalyticOnNhd ℂ (psiN b N) (ball (0 : ℂ) r) := by
  intro z hz
  have hziter : (quadratic b)^[N] z ∈ escapeOpen b := by
    refine hcl z ?_
    have : ‖z‖ < r := by simpa [mem_ball, dist_zero_right] using hz
    exact this.le
  exact (analyticOnNhd_bottcherCoord_full b _ hziter).comp (analyticAt_iterate b N z)

/-- **The m-step Böttcher branch exists — UNCONDITIONALLY, for every viable parameter.**  If the
closed unit disk avoids `K_b`, there is a window disk `ball 0 r` (`r > 1`, crossing `u₀`'s natural
boundary `|z| = 1`) and a step count `N` on which `ψ = bottcherCoord ∘ f^[N]` is analytic and
nowhere zero.  No hypothesis beyond viability, no assumed transcendence. -/
theorem exists_mstep_branch {b : ℂ}
    (hviab : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b) :
    ∃ (r : ℝ) (N : ℕ), 1 < r ∧ AnalyticOnNhd ℂ (psiN b N) (ball (0 : ℂ) r) ∧
      (∀ z : ℂ, psiN b N z ≠ 0) := by
  obtain ⟨r, hr, N, hcl⟩ := exists_clearance_escapeOpen hviab
  exact ⟨r, N, hr, psiN_analyticOnNhd hcl, fun z => psiN_ne_zero b N z⟩

open U0MeroCarrier

/-- The m-step branch as an analytic germ on the carrier `annMB r`. -/
noncomputable def psiNAn {b : ℂ} {r : ℝ} {N : ℕ}
    (hcl : ∀ z : ℂ, ‖z‖ ≤ r → (quadratic b)^[N] z ∈ escapeOpen b) :
    analyticSubring (annMB r) :=
  ⟨Germ.coeRingHom (𝓟 (annMB r)) (psiN b N),
    ⟨psiN b N, (psiN_analyticOnNhd hcl).mono inter_subset_left, rfl⟩⟩

/-- **`u₀ ⟂ ψ` for a viable parameter, with the CONCRETE m-step branch `ψ = bottcherCoord ∘ f^[N]`
built in** — the only remaining hypothesis is `ψ`'s transcendence over `ℂ(z)` (which is the
far-Böttcher transcendence `bottcher_transcendental_far` transported along `f^[N]`).  Feeds the
concrete branch to the branch-conditional capstone. -/
theorem u0_psiN_independence {b : ℂ} {r : ℝ} {N : ℕ} (hr : 1 < r)
    (hcl : ∀ z : ℂ, ‖z‖ ≤ r → (quadratic b)^[N] z ∈ escapeOpen b)
    (htrans :
      letI := isDomain_analyticSubring (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr)
        (annMB_nonempty hr)
      letI : Algebra (RatFunc ℂ) (meroField (annMB r)) :=
        (ratfuncToMero (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr) (annMB_nonempty hr)
          (annMB_infinite hr)).toAlgebra
      Transcendental (RatFunc ℂ)
        (algebraMap (analyticSubring (annMB r)) (meroField (annMB r)) (psiNAn hcl))) :
    letI := isDomain_analyticSubring (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr)
      (annMB_nonempty hr)
    letI : Algebra (RatFunc ℂ) (meroField (annMB r)) :=
      (ratfuncToMero (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr) (annMB_nonempty hr)
        (annMB_infinite hr)).toAlgebra
    NoRelation (RatFunc ℂ)
      (algebraMap (analyticSubring (annMB r)) (meroField (annMB r)) (psiNAn hcl))
      (algebraMap (analyticSubring (annMB r)) (meroField (annMB r))
        (u0AnSub annMB_subset_Ext)) :=
  u0_mstep_independence_of_branch hr (psiN b N) (psiN_analyticOnNhd hcl) (psiNAn hcl) rfl htrans

end U0PhiMStep
