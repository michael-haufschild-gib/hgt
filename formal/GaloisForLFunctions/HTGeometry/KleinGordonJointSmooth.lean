import GaloisForLFunctions.HTGeometry.KleinGordonSupportBounds

/-!
# The Klein–Gordon operator applied to a jointly smooth potential

A potential given as a smooth function of the event is, for each time, a smooth function of the
point; the probe construction needs the resulting curve of functions to be bounded and Lipschitz in
time after finitely many applications of `1 - (2π)⁻²Δ`.

Both follow from joint smoothness once the *partial* derivatives in the space variable are known to
be jointly smooth, which is the parametric derivative theorem applied twice. Boundedness is then
compactness of the support, and the Lipschitz bound is the mean value inequality applied to the
partial derivative in time.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory InnerProductSpace

open scoped SchwartzMap ContDiff Laplacian

section Joint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## Partial derivatives of a jointly smooth function -/

omit [FiniteDimensional ℝ E] in
/-- **The derivative in the space variable of a jointly smooth function is jointly smooth.** -/
theorem contDiff_partialFDeriv {H : ℝ × E → F} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ fun p : ℝ × E => fderiv ℝ (fun x : E => H (p.1, x)) p.2 := by
  have hslice : ContDiff ℝ ∞ fun q : (ℝ × E) × E => H (q.1.1, q.2) := by
    have hmap : ContDiff ℝ ∞ fun q : (ℝ × E) × E => ((q.1.1, q.2) : ℝ × E) := by fun_prop
    exact hH.comp hmap
  exact hslice.fderiv contDiff_snd (by simp)

omit [FiniteDimensional ℝ E] in
/-- **The derivative in the time variable of a jointly smooth function is jointly smooth.** -/
theorem contDiff_partialFDerivTime {H : ℝ × E → F} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ fun p : ℝ × E => fderiv ℝ (fun t : ℝ => H (t, p.2)) p.1 := by
  have hslice : ContDiff ℝ ∞ fun q : (ℝ × E) × ℝ => H (q.2, q.1.2) := by
    have hmap : ContDiff ℝ ∞ fun q : (ℝ × E) × ℝ => ((q.2, q.1.2) : ℝ × E) := by fun_prop
    exact hH.comp hmap
  exact hslice.fderiv contDiff_fst (by simp)

omit [FiniteDimensional ℝ E] in
/-- The second derivative in the space variable of a jointly smooth function is jointly smooth. -/
theorem contDiff_partialFDeriv_two {H : ℝ × E → F} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ fun p : ℝ × E => fderiv ℝ (fderiv ℝ fun x : E => H (p.1, x)) p.2 := by
  have hfirst := contDiff_partialFDeriv hH
  have hsecond := contDiff_partialFDeriv hfirst
  exact hsecond

/-! ## The partial Laplacian -/

/-- **The Laplacian in the space variable of a jointly smooth function is jointly smooth.** -/
theorem contDiff_partialLaplacian {H : ℝ × E → ℂ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ fun p : ℝ × E => Δ (fun x : E => H (p.1, x)) p.2 := by
  have hlap : (fun p : ℝ × E => Δ (fun x : E => H (p.1, x)) p.2)
      = fun p : ℝ × E => ∑ i, (fderiv ℝ (fderiv ℝ fun x : E => H (p.1, x)) p.2)
          ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) i) := by
    funext p
    rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    simp [iteratedFDeriv_two_apply]
  rw [hlap]
  refine ContDiff.sum fun i _ => ?_
  exact ((contDiff_partialFDeriv_two hH).clm_apply contDiff_const).clm_apply contDiff_const

/-- **The Klein–Gordon operator of a jointly smooth potential is jointly smooth.** -/
theorem contDiff_kgFunOp_param {H : ℝ × E → ℂ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ fun p : ℝ × E => kgFunOp (fun x : E => H (p.1, x)) p.2 := by
  have hval : (fun p : ℝ × E => kgFunOp (fun x : E => H (p.1, x)) p.2)
      = fun p : ℝ × E => H (p.1, p.2)
        - (((2 * Real.pi) ^ 2 : ℝ))⁻¹ • Δ (fun x : E => H (p.1, x)) p.2 := rfl
  rw [hval]
  have hfirst : ContDiff ℝ ∞ fun p : ℝ × E => H (p.1, p.2) := by
    simpa using hH
  exact hfirst.sub ((contDiff_partialLaplacian hH).const_smul _)

/-- **Iterating the operator preserves joint smoothness.** -/
theorem contDiff_kgFunOp_iterate_param (j : ℕ) {H : ℝ × E → ℂ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ fun p : ℝ × E => (kgFunOp^[j] fun x : E => H (p.1, x)) p.2 := by
  induction j generalizing H with
  | zero =>
    simpa using hH
  | succ j ih =>
    have hstep := ih (contDiff_kgFunOp_param hH)
    have hval : (fun p : ℝ × E => (kgFunOp^[j + 1] fun x : E => H (p.1, x)) p.2)
        = fun p : ℝ × E =>
          (kgFunOp^[j] fun x : E => kgFunOp (fun y : E => H (p.1, y)) x) p.2 := by
      funext p
      rw [Function.iterate_succ_apply]
    rw [hval]
    exact hstep

/-! ## Supports -/

/-- The operator does not enlarge supports, at the level of functions. -/
theorem kgFunOp_support {g : E → ℂ} {K : Set E} (hK : IsClosed K)
    (hsupp : ∀ x : E, x ∉ K → g x = 0) : ∀ x : E, x ∉ K → kgFunOp g x = 0 := by
  intro x hx
  have hnhds : ∀ᶠ y in nhds x, g y = 0 :=
    Filter.eventually_of_mem (hK.isOpen_compl.mem_nhds hx) fun y hy => hsupp y hy
  have hlap : Δ g x = 0 := by
    have hcongr : Δ g =ᶠ[nhds x] Δ (fun _ : E => (0 : ℂ)) := laplacian_congr_nhds hnhds
    have hval := hcongr.self_of_nhds
    rw [hval, laplacian_const]
    rfl
  rw [kgFunOp, hsupp x hx, hlap, smul_zero, sub_zero]

theorem kgFunOp_iterate_support {g : E → ℂ} {K : Set E} (hK : IsClosed K)
    (hsupp : ∀ x : E, x ∉ K → g x = 0) (j : ℕ) :
    ∀ x : E, x ∉ K → (kgFunOp^[j] g) x = 0 := by
  induction j generalizing g with
  | zero => simpa using hsupp
  | succ j ih =>
    intro x hx
    rw [Function.iterate_succ_apply]
    exact ih (kgFunOp_support hK hsupp) x hx

/-- The operator kills the zero function. -/
theorem kgFunOp_iterate_zero (j : ℕ) : kgFunOp^[j] (fun _ : E => (0 : ℂ)) = fun _ : E => 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hstep : kgFunOp (fun _ : E => (0 : ℂ)) = fun _ : E => 0 := by
      funext x
      rw [kgFunOp, laplacian_const]
      simp
    rw [Function.iterate_succ_apply, hstep, ih]

/-! ## Uniform bounds from a compact spacetime support -/

/-- A potential vanishing off a closed set of events has all its iterated operators vanishing
there. -/
theorem kgFunOp_iterate_param_support {H : ℝ × E → ℂ} {S : Set (ℝ × E)} (hS : IsClosed S)
    (hsupp : ∀ p : ℝ × E, p ∉ S → H p = 0) (j : ℕ) :
    ∀ p : ℝ × E, p ∉ S → (kgFunOp^[j] fun y : E => H (p.1, y)) p.2 = 0 := by
  intro p hp
  have hslice : IsClosed {x : E | (p.1, x) ∈ S} := by
    have hcont : Continuous fun x : E => ((p.1, x) : ℝ × E) := by fun_prop
    exact hS.preimage hcont
  have hzero : ∀ x : E, x ∉ {x : E | (p.1, x) ∈ S} → H (p.1, x) = 0 := fun x hx => hsupp _ hx
  exact kgFunOp_iterate_support hslice hzero j p.2 (by simpa using hp)

/-- **A uniform bound for the iterated operator of a potential supported in a compact set of
events.** -/
theorem exists_bound_kgFunOp_iterate {H : ℝ × E → ℂ} (hH : ContDiff ℝ ∞ H)
    {S : Set (ℝ × E)} (hS : IsCompact S) (hsupp : ∀ p : ℝ × E, p ∉ S → H p = 0) (j : ℕ) :
    ∃ C : ℝ, ∀ (t : ℝ) (x : E), ‖(kgFunOp^[j] fun y : E => H (t, y)) x‖ ≤ C := by
  have hGsmooth : ContDiff ℝ ∞ fun p : ℝ × E => (kgFunOp^[j] fun y : E => H (p.1, y)) p.2 :=
    contDiff_kgFunOp_iterate_param j hH
  have hGzero : ∀ p : ℝ × E, p ∉ S → (kgFunOp^[j] fun y : E => H (p.1, y)) p.2 = 0 :=
    kgFunOp_iterate_param_support hS.isClosed hsupp j
  obtain ⟨C, hC⟩ := hGsmooth.continuous.bounded_above_of_compact_support
    (HasCompactSupport.intro hS hGzero)
  exact ⟨C, fun t x => hC (t, x)⟩

/-- **A Lipschitz-in-time bound for the iterated operator**, by the mean value inequality applied to
the partial derivative in time, which is again continuous and compactly supported. -/
theorem exists_lipschitz_kgFunOp_iterate {H : ℝ × E → ℂ} (hH : ContDiff ℝ ∞ H)
    {S : Set (ℝ × E)} (hS : IsCompact S) (hsupp : ∀ p : ℝ × E, p ∉ S → H p = 0) (j : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (t t' : ℝ) (x : E),
      ‖(kgFunOp^[j] fun y : E => H (t, y)) x - (kgFunOp^[j] fun y : E => H (t', y)) x‖
        ≤ L * |t - t'| := by
  set G : ℝ × E → ℂ := fun p : ℝ × E => (kgFunOp^[j] fun y : E => H (p.1, y)) p.2 with hGdef
  have hGsmooth : ContDiff ℝ ∞ G := contDiff_kgFunOp_iterate_param j hH
  have hGzero : ∀ p : ℝ × E, p ∉ S → G p = 0 :=
    kgFunOp_iterate_param_support hS.isClosed hsupp j
  set D : ℝ × E → ℂ := fun p : ℝ × E => fderiv ℝ (fun t : ℝ => G (t, p.2)) p.1 1 with hDdef
  have hDsmooth : ContDiff ℝ ∞ D :=
    (contDiff_partialFDerivTime hGsmooth).clm_apply contDiff_const
  have hDzero : ∀ p : ℝ × E, p ∉ S → D p = 0 := by
    intro p hp
    have hmem : {t : ℝ | (t, p.2) ∈ Sᶜ} ∈ nhds p.1 := by
      have hcont : Continuous fun t : ℝ => ((t, p.2) : ℝ × E) := by fun_prop
      exact (hS.isClosed.isOpen_compl.preimage hcont).mem_nhds (by simpa using hp)
    have hnhds : (fun t : ℝ => G (t, p.2)) =ᶠ[nhds p.1] fun _ : ℝ => (0 : ℂ) :=
      Filter.eventually_of_mem hmem fun t ht => hGzero (t, p.2) ht
    show fderiv ℝ (fun t : ℝ => G (t, p.2)) p.1 1 = 0
    rw [hnhds.fderiv_eq]
    simp
  obtain ⟨L, hL⟩ := hDsmooth.continuous.bounded_above_of_compact_support
    (HasCompactSupport.intro hS hDzero)
  refine ⟨L, le_trans (norm_nonneg (D 0)) (hL 0), ?_⟩
  intro t t' x
  have hderiv : ∀ s : ℝ, HasDerivAt (fun r : ℝ => G (r, x)) (D (s, x)) s := by
    intro s
    have hsl : ContDiff ℝ ∞ fun r : ℝ => ((r, x) : ℝ × E) := by fun_prop
    have hdiff : DifferentiableAt ℝ (fun r : ℝ => G (r, x)) s :=
      (hGsmooth.comp hsl).differentiable (by simp) s
    exact hdiff.hasFDerivAt.hasDerivAt
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun r : ℝ => G (r, x)) (f' := fun s : ℝ => D (s, x)) (s := Set.univ)
    (fun s _ => (hderiv s).hasDerivWithinAt) (fun s _ => hL (s, x)) convex_univ
    (Set.mem_univ t') (Set.mem_univ t)
  rw [Real.norm_eq_abs] at hmv
  exact hmv

end Joint

end GaloisForLFunctions.HTGeometry
