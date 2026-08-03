import GaloisForLFunctions.HTGeometry.MassShiftObservationContinuity

/-!
# One residual set of mass parameters for every collision-free shift

Patchwise avoidance transfers from the finite atom slice to the bounded exponential parameter,
because a finitely supported perturbation of the parameter is exactly an exponential rescaling of
finitely many masses, and its sup norm is the size of the rescaling.

Joint continuity makes patchwise avoidance open, the collision-free shift tuples are sigma-compact,
and Baire's theorem then produces one residual set of mass parameters which stays at full evaluation
rank at *every* tuple of distinct real shifts.
-/

open Filter Topology MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Tuples of distinct real shifts. -/
abbrev RealShiftConfiguration (r : ℕ) := {t : Fin r → ℝ // Function.Injective t}

theorem injectiveRealShiftSet_isOpen (r : ℕ) :
    IsOpen {t : Fin r → ℝ | Function.Injective t} := by
  classical
  have hset : {t : Fin r → ℝ | Function.Injective t}
      = ⋂ i : Fin r, ⋂ j : Fin r, ⋂ _ : i ≠ j, {t : Fin r → ℝ | t i ≠ t j} := by
    ext t
    simp only [mem_setOf_eq, mem_iInter]
    constructor
    · intro hinj i j hij heq
      exact hij (hinj heq)
    · intro hpairs i j heq
      by_contra hij
      exact hpairs i j hij heq
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  refine isOpen_iInter_of_finite fun _ => ?_
  have hcont : Continuous fun t : Fin r → ℝ => t i - t j :=
    (continuous_apply i).sub (continuous_apply j)
  have hopen := hcont.isOpen_preimage {y : ℝ | y ≠ 0} isOpen_ne
  convert hopen using 1
  ext t
  simp only [mem_preimage, mem_setOf_eq, sub_ne_zero]

noncomputable instance realShiftConfigurationSigmaCompactSpace (r : ℕ) :
    SigmaCompactSpace (RealShiftConfiguration r) := by
  letI : LocallyCompactSpace (RealShiftConfiguration r) :=
    (injectiveRealShiftSet_isOpen r).locallyCompactSpace
  infer_instance

/-- **Patchwise density in the bounded exponential parameter.**  A finitely supported perturbation
of the parameter is an exponential rescaling of finitely many masses, so the finite-dimensional
density transfers. -/
theorem dense_massShift_avoidance {row : Type} [Fintype row] [DecidableEq row]
    {κ : Type} [Fintype κ] [DecidableEq κ] {z : row → ℂ} (hzinj : Function.Injective z)
    (hupper : ∀ b, 0 < (z b).im) (hsep : ∀ b b', b ≠ b' → (z b).im ≠ (z b').im)
    {r d D q : ℕ} (hD : r * (d + 1) = D)
    {exponent : κ → (Fin D →₀ ℕ)} (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (q + 1)) + q < Fintype.card row)
    (hdim : r < 2 * (Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1))
    {x : ℕ → ℝ} (hx : Function.Injective x) {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n)
    (hε : Summable ε)
    {carrier : (Fin r → ℝ) → ((Σ _ : row × Fin r, Fin (d + 1)) → ℂ)}
    (hcarrier : ContDiff ℝ (⊤ : ℕ∞) carrier)
    {Kset : Set (Fin r → ℝ)} (hKcompact : IsCompact Kset)
    (hKinj : ∀ t ∈ Kset, Function.Injective t) :
    Dense (compactConfigurationAvoidance (massShiftObservation z d x ε carrier)
      (outerShiftBad row r d D q hD z exponent) Kset) := by
  classical
  rw [Metric.dense_iff]
  intro u₀ δ hδ
  set w : ℕ → ℝ := fun n => ε n * Real.exp (u₀ n) with hwdef
  have hwpos : ∀ n, 0 < w n := fun n => mul_pos (hεpos n) (Real.exp_pos _)
  have hwnn : ∀ n, 0 ≤ w n := fun n => (hwpos n).le
  have hwsum : Summable w := summable_expParameter (fun n => (hεpos n).le) hε u₀
  obtain ⟨Kat, a, hainj, hspan⟩ := exists_uniform_massJet_atoms hupper hsep
    (fun _ : row × Fin r => d + 1) hx (fun n => (hwpos n).ne') hKcompact hKinj
  have hdenseSlice := dense_avoidance_outerShiftObservation hzinj hupper hD hexponent hrows hdim
    x hwnn hwsum hainj hcarrier hspan
  obtain ⟨s, hsball, hsgood⟩ :=
    (Metric.dense_iff.mp hdenseSlice) 0 (δ / 2) (by linarith)
  have hslt : ∀ k, |s k| < δ / 2 := by
    intro k
    have hd : dist s (0 : Fin Kat → ℝ) < δ / 2 := Metric.mem_ball.mp hsball
    have hk := (dist_pi_lt_iff (by linarith : (0:ℝ) < δ / 2)).mp hd k
    simpa [Real.dist_eq] using hk
  have hc : (0 : ℝ) ≤ δ / 2 := by linarith
  have hsle : ∀ k, |s k| ≤ δ / 2 := fun k => (hslt k).le
  refine ⟨u₀ + pertParameter a s hainj hc hsle, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    have hnorm := norm_pertParameter_le hainj hc hsle
    simpa using lt_of_le_of_lt hnorm (by linarith)
  · intro t ht
    rw [massShiftObservation_pertParameter z d x carrier u₀ hainj hc hsle t]
    exact hsgood t ht

/-- **One residual set of mass parameters works at every tuple of distinct real shifts.** -/
theorem residual_globalAvoidance_massShift {row : Type} [Fintype row] [DecidableEq row]
    {κ : Type} [Fintype κ] [DecidableEq κ] {z : row → ℂ} (hzinj : Function.Injective z)
    (hupper : ∀ b, 0 < (z b).im) (hsep : ∀ b b', b ≠ b' → (z b).im ≠ (z b').im)
    {r d D q : ℕ} (hD : r * (d + 1) = D)
    {exponent : κ → (Fin D →₀ ℕ)} (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (q + 1)) + q < Fintype.card row)
    (hdim : r < 2 * (Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1))
    {x : ℕ → ℝ} (hx : Function.Injective x) {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n)
    (hε : Summable ε)
    {carrier : (Fin r → ℝ) → ((Σ _ : row × Fin r, Fin (d + 1)) → ℂ)}
    (hcarrier : ContDiff ℝ (⊤ : ℕ∞) carrier) :
    {u : MassParameter | ∀ τ : RealShiftConfiguration r,
        massShiftObservation z d x ε carrier (u, τ.1)
          ∉ outerShiftBad row r d D q hD z exponent} ∈ residual MassParameter := by
  have hcont : Continuous fun p : MassParameter × RealShiftConfiguration r =>
      massShiftObservation z d x ε carrier (p.1, p.2.1) :=
    (continuous_massShiftObservation hupper d x hεpos hε hcarrier.continuous).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hglobal := globalConfigurationAvoidance_dense_residual_of_sigmaCompact
    (fun p : MassParameter × RealShiftConfiguration r =>
      massShiftObservation z d x ε carrier (p.1, p.2.1))
    hcont (outerShiftBad row r d D q hD z exponent)
    (isClosed_outerShiftBad row r d D q hD z exponent) ?_
  · exact hglobal.2
  · intro Kpatch hKpatch
    have hKimage : IsCompact (Subtype.val '' Kpatch) := hKpatch.image continuous_subtype_val
    have hKinj : ∀ t ∈ Subtype.val '' Kpatch, Function.Injective t := by
      rintro t ⟨τ, -, rfl⟩
      exact τ.2
    have hdense := dense_massShift_avoidance hzinj hupper hsep hD hexponent hrows hdim hx
      hεpos hε hcarrier hKimage hKinj
    refine hdense.mono fun u hu τ hτ => ?_
    exact hu τ.1 ⟨τ, hτ, rfl⟩

end

end GaloisForLFunctions.HTGeometry
