/-
# The m-step branch `ψ = bottcherCoord ∘ f^[N]` is transcendental over `ℂ(z)` — UNCONDITIONAL

The last input to unconditional viable-region independence.  `ψ = bottcherCoord ∘ f_b^[N]` on the
window annulus `annMB r`; its transcendence is `Bottcher.bottcher_transcendental_far` transported
along `f^[N] = pMapB b (N-1)` by the carrier-generic descent (`descend_algebraicP`, `pullAn`,
`kappaP`), EXACTLY as in `U0PhiLargeDescent.phiB_transcendental`, but on the m-step carrier and
with no `2^k` power (ψ IS `bottcherCoord ∘ pMapB`).

The one place the sharp descent used `‖b‖ > 2+√2` was `pMapB_deriv_ne_zero` → openness of the far
image.  That derivative hypothesis is **not needed**: a positive-degree polynomial map is an open
map on all of `ℂ` (`Polynomial.isOpenQuotientMap_eval`), so the far image `pMapB b m '' annMB r` is
open with no condition on the orbit avoiding the critical point.  This removes the last obstruction
to running the descent for every viable parameter — no puncturing, no genericity argument.
-/
import GaloisForLFunctions.U0.U0PhiMStep
import GaloisForLFunctions.U0.U0PhiLargeDescent

open Complex Set Metric Polynomial Filter Topology Bottcher
open U0MStepBranch U0PhiMStep U0MeroCarrier
open U0PhiFourFarCarrier U0PhiFourDescent U0PhiLargeCarrier U0PhiLargeDescent

namespace U0PhiMStepFar

/-! ## Viability gives `0 ∉ K_b` and clearance past the far bound -/

/-- A viable parameter has `0 ∉ K_b` (the origin lies in the closed unit disk). -/
theorem zero_not_mem_of_viable {b : ℂ}
    (hviab : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b) : (0 : ℂ) ∉ filledJulia b :=
  hviab 0 (by simp)

/-- Persistence of any escape threshold `M ≥ max 2 ‖b‖`: once the orbit norm exceeds `M`, the next
step still exceeds `M` (since `‖f w‖ ≥ ‖w‖² − ‖b‖ > M² − M ≥ M`). -/
theorem persist_past_M {b w : ℂ} {M : ℝ} (hM : max 2 ‖b‖ ≤ M) (hw : M < ‖w‖) :
    M < ‖quadratic b w‖ := by
  have hM2 : (2 : ℝ) ≤ M := le_trans (le_max_left _ _) hM
  have hMb : ‖b‖ ≤ M := le_trans (le_max_right _ _) hM
  have hstep : ‖w‖ ^ (2 : ℕ) - ‖b‖ ≤ ‖quadratic b w‖ := by
    have : ‖w ^ (2 : ℕ)‖ - ‖b‖ ≤ ‖w ^ (2 : ℕ) + b‖ := by
      have := norm_sub_norm_le (w ^ (2 : ℕ)) (-b)
      simpa [sub_neg_eq_add] using this
    rwa [norm_pow] at this
  nlinarith [hstep, hw, hM2, hMb, norm_nonneg w]

/-- **Uniform clearance past the Böttcher far bound.**  For a viable parameter, a disk `D̄(0,r)`
(`r > 1`, crossing `|z| = 1`) lands strictly beyond `bottcherFarBound b hc` after a uniform number
of steps `N ≥ 1`.  Same compactness argument as `exists_clearance_escapeOpen`, with the larger
threshold `M := max (bottcherFarBound b hc) (max 2 ‖b‖)`. -/
theorem exists_clearance_farBound {b : ℂ}
    (hviab : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b) (hc : (0 : ℂ) ∉ filledJulia b) :
    ∃ r : ℝ, 1 < r ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ z : ℂ, ‖z‖ ≤ r →
        (quadratic b)^[N] z ∈ escapeOpen b ∧ bottcherFarBound b hc < ‖(quadratic b)^[N] z‖ := by
  set M : ℝ := max (bottcherFarBound b hc) (max 2 ‖b‖) with hMdef
  have hMge : max 2 ‖b‖ ≤ M := le_max_right _ _
  have hFBle : bottcherFarBound b hc ≤ M := le_max_left _ _
  set A : ℕ → Set ℂ := fun N => {z : ℂ | M < ‖(quadratic b)^[N] z‖} with hA
  have hAopen : ∀ N, IsOpen (A N) := fun N =>
    isOpen_lt continuous_const (continuous_norm.comp ((continuous_quadratic b).iterate N))
  have hAmono : ∀ {P Q : ℕ}, P ≤ Q → A P ⊆ A Q := by
    intro P Q hPQ z hz
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hPQ
    have hstep : ∀ j : ℕ, M < ‖(quadratic b)^[P] z‖ → M < ‖(quadratic b)^[P + j] z‖ := by
      intro j
      induction j with
      | zero => intro h; rwa [Nat.add_zero]
      | succ k ih =>
        intro h0
        rw [show P + (k + 1) = (P + k) + 1 from rfl, Function.iterate_succ_apply']
        exact persist_past_M hMge (ih h0)
    exact hstep d hz
  have hcover : closedBall (0 : ℂ) 1 ⊆ ⋃ N, A N := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hz
    obtain ⟨N, hN⟩ := exists_orbit_gt (hviab z hz1) M
    exact mem_iUnion.mpr ⟨N, hN⟩
  obtain ⟨t, ht⟩ := (isCompact_closedBall (0 : ℂ) 1).elim_finite_subcover A hAopen hcover
  have hsub : closedBall (0 : ℂ) 1 ⊆ A (t.sup id) := by
    intro z hz
    obtain ⟨i, hit, hzi⟩ := mem_iUnion₂.mp (ht hz)
    exact hAmono (Finset.le_sup (f := id) hit) hzi
  obtain ⟨δ, hδpos, hδ⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open (hAopen (t.sup id)) hsub
  refine ⟨1 + δ / 2, by linarith, (t.sup id) + 1, Nat.le_add_left 1 _, ?_⟩
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
  have hzA : z ∈ A (t.sup id) := hδ hzin
  have hstep1 : M < ‖(quadratic b)^[(t.sup id) + 1] z‖ := by
    rw [Function.iterate_succ_apply']
    exact persist_past_M hMge hzA
  exact ⟨lt_of_le_of_lt hMge hstep1, lt_of_le_of_lt hFBle hstep1⟩

/-! ## The far image is open — by the open mapping theorem, no derivative condition -/

/-- **The far image `pMapB b m '' annMB r` is open** — via the open mapping theorem for the
positive-degree polynomial `pPolyB b m` (`pMapB b m = (pPolyB b m).eval`), with NO derivative
hypothesis.  This is the `annMB` analogue of the carrier theorem `isOpen_pMapB_image`. -/
theorem isOpen_pMapB_image_annMB (b : ℂ) (m : ℕ) (r : ℝ) :
    IsOpen (pMapB b m '' annMB r) := by
  have hfun : pMapB b m = fun z => Polynomial.eval z (pPolyB b m) := by
    funext z; exact (pPolyB_eval b m z).symm
  rw [hfun]
  exact (Polynomial.isOpenQuotientMap_eval (pPolyB b m) (pPolyB_natDegree_ne_zero b m)).isOpenMap
    _ (isOpen_annMB r)

/-! ## The transcendence of `ψ`, and unconditional m-step independence -/

/-- **`ψ = bottcherCoord ∘ f^[N]` is transcendental over `ℂ(z)`** on the m-step carrier `annMB r`,
for every viable parameter — the descent of `bottcher_transcendental_far` along `f^[N]`, on the
UNPUNCTURED carrier.  No `‖b‖ > 2+√2`, no derivative condition. -/
theorem psiN_transcendental {b : ℂ} {r : ℝ} {N : ℕ} (hr : 1 < r) (hN : 1 ≤ N)
    (hc : (0 : ℂ) ∉ filledJulia b)
    (hcl : ∀ z : ℂ, ‖z‖ ≤ r → (quadratic b)^[N] z ∈ escapeOpen b)
    (hfarbound : ∀ z : ℂ, ‖z‖ ≤ r → bottcherFarBound b hc < ‖(quadratic b)^[N] z‖) :
    letI := isDomain_analyticSubring (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr)
      (annMB_nonempty hr)
    letI : Algebra (RatFunc ℂ) (meroField (annMB r)) :=
      (ratfuncToMero (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr) (annMB_nonempty hr)
        (annMB_infinite hr)).toAlgebra
    Transcendental (RatFunc ℂ)
      (algebraMap (analyticSubring (annMB r)) (meroField (annMB r)) (psiNAn hcl)) := by
  letI := isDomain_analyticSubring (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr)
    (annMB_nonempty hr)
  letI algR : Algebra (RatFunc ℂ) (meroField (annMB r)) :=
    (ratfuncToMero (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr) (annMB_nonempty hr)
      (annMB_infinite hr)).toAlgebra
  intro halg
  -- Write `N = m + 1`, so `pMapB b m = f^[m+1] = f^[N]`.
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos hN).symm⟩
  have hpMapB_eq : ∀ z, pMapB b m z = (quadratic b)^[m + 1] z := fun z =>
    (Function.iterate_succ_apply (quadratic b) m z).symm
  set W : Set ℂ := pMapB b m '' annMB r with hW
  have hWo : IsOpen W := isOpen_pMapB_image_annMB b m r
  have hWc : IsPreconnected W :=
    (isPreconnected_annMB hr).image _
      (((pMapB_analyticOnNhd b m).continuousOn).mono (subset_univ _))
  have hWne : W.Nonempty := (annMB_nonempty hr).image _
  have hWinf : W.Infinite := infinite_of_isOpen_nonempty hWo hWne
  have hfar : ∀ w ∈ W, bottcherFarBound b hc < ‖w‖ := by
    rintro w ⟨z, hz, rfl⟩
    rw [hpMapB_eq z]
    have hzr : ‖z‖ < r := by
      have hzb : z ∈ ball (0 : ℂ) r := hz.1
      simpa [mem_ball, dist_zero_right] using hzb
    exact hfarbound z hzr.le
  letI := isDomain_analyticSubring W hWo hWc hWne
  letI algW : Algebra (RatFunc ℂ) (meroField W) :=
    (ratfuncToMero W hWo hWc hWne hWinf).toAlgebra
  obtain ⟨a₂, ha₂, _⟩ := bottcherFarBound_spec b hc W hWo hWc hWne hWinf hfar
  have htr := bottcher_transcendental_far b hc hWo hWc hWne hWinf hfar ha₂
  set x : meroField (annMB r) :=
    algebraMap (analyticSubring (annMB r)) (meroField (annMB r)) (psiNAn hcl) with hx
  obtain ⟨Q, hQ0, hQev⟩ := halg
  rw [aeval_def, RingHom.algebraMap_toAlgebra] at hQev
  obtain ⟨S, hS0, hSev⟩ := descend_algebraicP (isOpen_annMB r) (isPreconnected_annMB hr)
    (annMB_nonempty hr) (annMB_infinite hr)
    (pPolyB_monic b m) (pPolyB_natDegree_ne_zero b m) x Q hQ0 hQev
  have hmaps : Set.MapsTo (pMapB b m) (annMB r) W := Set.mapsTo_image _ _
  have hganal : AnalyticOnNhd ℂ (pMapB b m) (annMB r) :=
    (pMapB_analyticOnNhd b m).mono (subset_univ _)
  have hsurj : W ⊆ pMapB b m '' annMB r := subset_rfl
  have hpullinj : Function.Injective
      ((algebraMap (analyticSubring (annMB r)) (meroField (annMB r))).comp
        (pullAn hmaps hganal)) :=
    (IsFractionRing.injective (analyticSubring (annMB r)) (meroField (annMB r))).comp
      (pullAn_injective hmaps hganal hsurj)
  set Φ : meroField W →+* meroField (annMB r) := IsFractionRing.lift hpullinj with hΦ
  have hpull_poly : ∀ a : Polynomial ℂ,
      pullAn hmaps hganal (polyToAnalytic W a)
        = polyToAnalytic (annMB r) (a.comp (pPolyB b m)) := by
    intro a
    apply Subtype.ext
    rw [pullAn_coe]
    have h1 : ((polyToAnalytic W a : analyticSubring W) : Germ (𝓟 W) ℂ)
        = ↑(fun z => a.eval z) := rfl
    have h2 : ((polyToAnalytic (annMB r) (a.comp (pPolyB b m)) : analyticSubring (annMB r))
        : Germ (𝓟 (annMB r)) ℂ) = ↑(fun z => (a.comp (pPolyB b m)).eval z) := rfl
    rw [h1, h2, germPullback_coe, Germ.coe_eq]
    apply eventually_principal.mpr
    intro z _
    show a.eval (pMapB b m z) = (a.comp (pPolyB b m)).eval z
    rw [eval_comp, pPolyB_eval]
  have hΦρ : kappaP (isOpen_annMB r) (isPreconnected_annMB hr) (annMB_nonempty hr)
      (annMB_infinite hr) (pPolyB_monic b m) (pPolyB_natDegree_ne_zero b m)
      = Φ.comp (ratfuncToMero W hWo hWc hWne hWinf) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial ℂ))
    apply RingHom.ext
    intro a
    show kappaP (isOpen_annMB r) (isPreconnected_annMB hr) (annMB_nonempty hr)
        (annMB_infinite hr) (pPolyB_monic b m) (pPolyB_natDegree_ne_zero b m)
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) a)
      = Φ (ratfuncToMero W hWo hWc hWne hWinf (algebraMap (Polynomial ℂ) (RatFunc ℂ) a))
    rw [kappaP_algebraMap, ratfuncToMero_algebraMap_polynomial]
    show polyToMero (annMB r) (a.comp (pPolyB b m))
      = Φ (algebraMap (analyticSubring W) (meroField W) (polyToAnalytic W a))
    rw [hΦ, IsFractionRing.lift_algebraMap]
    show polyToMero (annMB r) (a.comp (pPolyB b m))
      = algebraMap (analyticSubring (annMB r)) (meroField (annMB r))
          (pullAn hmaps hganal (polyToAnalytic W a))
    rw [hpull_poly]
    rfl
  have hx2 : Φ (algebraMap (analyticSubring W) (meroField W) a₂) = x := by
    rw [hΦ, IsFractionRing.lift_algebraMap]
    show algebraMap (analyticSubring (annMB r)) (meroField (annMB r))
      (pullAn hmaps hganal a₂) = x
    rw [hx]
    congr 1
    apply Subtype.ext
    rw [pullAn_coe]
    have ha₂v : (a₂ : Germ (𝓟 W) ℂ) = ↑(bottcherCoord b) := ha₂.symm
    rw [ha₂v, germPullback_coe]
    have h2 : ((psiNAn hcl : analyticSubring (annMB r)) : Germ (𝓟 (annMB r)) ℂ)
        = ↑(psiN b (m + 1)) := rfl
    rw [h2, Germ.coe_eq]
    apply eventually_principal.mpr
    intro z _
    show (bottcherCoord b ∘ pMapB b m) z = psiN b (m + 1) z
    show bottcherCoord b (pMapB b m z) = bottcherCoord b ((quadratic b)^[m + 1] z)
    rw [hpMapB_eq z]
  have h0 : S.eval₂ (ratfuncToMero W hWo hWc hWne hWinf)
      (algebraMap (analyticSubring W) (meroField W) a₂) = 0 := by
    apply Φ.injective
    rw [map_zero, hom_eval₂, ← hΦρ, hx2]
    exact hSev
  exact htr ⟨S, hS0, by rw [aeval_def, RingHom.algebraMap_toAlgebra]; exact h0⟩

/-! ## Unconditional m-step independence over the whole viable region -/

/-- **m-step independence at parameter `b`**: there is a window disk `ball 0 r` (`r > 1`, crossing
the natural boundary `|z| = 1`) and a uniform step count `N` on which the m-step Böttcher branch
`ψ = bottcherCoord ∘ f_b^[N]` is analytic and algebraically independent of `u₀` over `ℂ(z)`. -/
def MStepIndependence (b : ℂ) : Prop :=
  ∃ (r : ℝ) (N : ℕ) (hr : 1 < r)
    (hcl : ∀ z : ℂ, ‖z‖ ≤ r → (quadratic b)^[N] z ∈ escapeOpen b),
    letI := isDomain_analyticSubring (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr)
      (annMB_nonempty hr)
    letI : Algebra (RatFunc ℂ) (meroField (annMB r)) :=
      (ratfuncToMero (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr) (annMB_nonempty hr)
        (annMB_infinite hr)).toAlgebra
    NoRelation (RatFunc ℂ)
      (algebraMap (analyticSubring (annMB r)) (meroField (annMB r)) (psiNAn hcl))
      (algebraMap (analyticSubring (annMB r)) (meroField (annMB r))
        (u0AnSub annMB_subset_Ext))

/-- **`u₀ ⟂ ψ` for EVERY viable parameter — UNCONDITIONAL.**  For any `b` whose filled Julia set
avoids the closed unit disk, `MStepIndependence b` holds: the m-step Böttcher branch
`ψ = bottcherCoord ∘ f_b^[N]` is analytic and algebraically independent of `u₀` over `ℂ(z)` on a
window crossing `|z| = 1`.  No `‖b‖ > 2+√2`, no assumed transcendence — the last gap (`ψ`
transcendental) is discharged by `psiN_transcendental`.  This closes the m-step program below the
sharp threshold: it holds throughout the viable region, in every direction. -/
theorem u0_mstep_independence {b : ℂ}
    (hviab : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b) : MStepIndependence b := by
  have hc : (0 : ℂ) ∉ filledJulia b := zero_not_mem_of_viable hviab
  obtain ⟨r, hr, N, hN, hcl_far⟩ := exists_clearance_farBound hviab hc
  have hcl : ∀ z : ℂ, ‖z‖ ≤ r → (quadratic b)^[N] z ∈ escapeOpen b :=
    fun z hz => (hcl_far z hz).1
  have hfarbound : ∀ z : ℂ, ‖z‖ ≤ r → bottcherFarBound b hc < ‖(quadratic b)^[N] z‖ :=
    fun z hz => (hcl_far z hz).2
  exact ⟨r, N, hr, hcl,
    u0_psiN_independence hr hcl (psiN_transcendental hr hN hc hcl hfarbound)⟩

end U0PhiMStepFar
