import GaloisForLFunctions.HTGeometry.KleinGordonConformalProbe

/-!
# From sup bounds to the decay functional

The decay functional of the family constructor is an `L¹` norm, but what a concrete potential comes
with is a *pointwise* bound on a compact set. The two are related by the obvious estimate

`∫‖f‖ ≤ (sup‖f‖) · vol(supp f)`,

and the operator `1 - (2π)⁻²Δ` does not enlarge supports, so the compact set is the one of the
potential itself.

This turns the hypotheses of the time-dependent probe theorem into sup bounds on finitely many
derivatives — the form in which a smooth compactly supported potential supplies them.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory InnerProductSpace

open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## The `L¹` norm of a function supported in a compact set -/

theorem integral_norm_le_of_support {f : E → ℂ} {K : Set E} (hKmeas : MeasurableSet K)
    (hKfin : volume K ≠ ⊤) (hf : Integrable f (volume : Measure E))
    (hsupp : ∀ x : E, x ∉ K → f x = 0) {C : ℝ} (hC : ∀ x : E, ‖f x‖ ≤ C) :
    (∫ x : E, ‖f x‖) ≤ C * (volume K).toReal := by
  have hzero : ∀ x : E, x ∉ K → ‖f x‖ = 0 := by
    intro x hx
    rw [hsupp x hx, norm_zero]
  have hrestrict : (∫ x : E, ‖f x‖) = ∫ x in K, ‖f x‖ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  rw [hrestrict]
  have hmono : (∫ x in K, ‖f x‖) ≤ ∫ _x in K, C := by
    refine setIntegral_mono_on hf.norm.integrableOn ?_ hKmeas fun x _ => hC x
    exact integrableOn_const hKfin
  refine hmono.trans_eq ?_
  rw [setIntegral_const, smul_eq_mul, measureReal_def]
  ring

/-! ## Supports are not enlarged -/

theorem kgSchwartzOp_support {f : 𝓢(E, ℂ)} {K : Set E} (hK : IsClosed K)
    (hsupp : ∀ x : E, x ∉ K → f x = 0) :
    ∀ x : E, x ∉ K → (kgSchwartzOp f) x = 0 := by
  intro x hx
  have hnhds : ∀ᶠ y in nhds x, f y = 0 := by
    have hopen : IsOpen (Kᶜ) := hK.isOpen_compl
    exact Filter.eventually_of_mem (hopen.mem_nhds hx) fun y hy => hsupp y hy
  have hlap : Δ (f : E → ℂ) x = 0 := by
    have hcongr : Δ (f : E → ℂ) =ᶠ[nhds x] Δ (fun _ : E => (0 : ℂ)) :=
      laplacian_congr_nhds hnhds
    have hval := hcongr.self_of_nhds
    rw [hval, laplacian_const]
    rfl
  have hval : (kgSchwartzOp f) x = f x - (((2 * Real.pi) ^ 2 : ℝ))⁻¹ • Δ (f : E → ℂ) x := by
    rw [kgSchwartzOp_eq, sub_apply, smul_apply, SchwartzMap.laplacian_apply]
  rw [hval, hsupp x hx, hlap, smul_zero, sub_zero]

theorem kgSchwartzOp_iterate_support {f : 𝓢(E, ℂ)} {K : Set E} (hK : IsClosed K)
    (hsupp : ∀ x : E, x ∉ K → f x = 0) (j : ℕ) :
    ∀ x : E, x ∉ K → (kgSchwartzOp^[j] f) x = 0 := by
  induction j generalizing f with
  | zero =>
    simpa using hsupp
  | succ j ih =>
    intro x hx
    rw [Function.iterate_succ_apply]
    exact ih (kgSchwartzOp_support hK hsupp) x hx

/-! ## The decay functional from sup bounds -/

theorem integral_kgSchwartzOp_le {f : 𝓢(E, ℂ)} {K : Set E} (hK : IsClosed K)
    (hKmeas : MeasurableSet K) (hKfin : volume K ≠ ⊤)
    (hsupp : ∀ x : E, x ∉ K → f x = 0) (j : ℕ) {C : ℝ}
    (hC : ∀ x : E, ‖(kgSchwartzOp^[j] f) x‖ ≤ C) :
    (∫ v : E, ‖(kgSchwartzOp^[j] f) v‖) ≤ C * (volume K).toReal :=
  integral_norm_le_of_support hKmeas hKfin (kgSchwartzOp^[j] f).integrable
    (kgSchwartzOp_iterate_support hK hsupp j) hC

/-! ## Probes from sup bounds -/

section SupProbe

variable {d N j m : ℕ}

/-- **Clock probes for a time-dependent potential given by sup bounds.** The curve of potentials is
supported in a fixed compact set, and finitely many of its derivatives are bounded uniformly in time
and Lipschitz in time; that is the form a smooth compactly supported potential supplies. -/
theorem openProbes_of_schwartzCurve_sup {Φ : ℝ → 𝓢(EuclideanSpace ℝ (Fin d), ℂ)}
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsClosed K) (hKmeas : MeasurableSet K)
    (hKfin : volume K ≠ ⊤)
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    (hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < m) (hj : N + m ≤ 2 * j)
    (hsupp : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), x ∉ K → Φ t x = 0)
    {M L : ℝ} (hM : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)),
      ‖(kgSchwartzOp^[j] (Φ t)) x‖ ≤ M) (hL0 : 0 ≤ L)
    (hL : ∀ (t t' : ℝ) (x : EuclideanSpace ℝ (Fin d)),
      ‖(kgSchwartzOp^[j] (Φ t - Φ t')) x‖ ≤ L * |t - t'|)
    (hreal : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), (starRingEnd ℂ) (Φ t x) = Φ t x) :
    OpenProbes (kgWaveOp d)
      (fun y : Fin (d + 1) → ℝ => (Φ (y 0) (kgSpatial d y)).re - 1) := by
  have hvol : (0 : ℝ) ≤ (volume K).toReal := ENNReal.toReal_nonneg
  have hM' : ∀ t : ℝ, (∫ v : EuclideanSpace ℝ (Fin d), ‖(kgSchwartzOp^[j] (Φ t)) v‖)
      ≤ M * (volume K).toReal := fun t =>
    integral_kgSchwartzOp_le hK hKmeas hKfin (hsupp t) j (hM t)
  have hsuppSub : ∀ t t' : ℝ, ∀ x : EuclideanSpace ℝ (Fin d), x ∉ K → (Φ t - Φ t') x = 0 := by
    intro t t' x hx
    rw [sub_apply, hsupp t x hx, hsupp t' x hx, sub_zero]
  have hL' : ∀ t t' : ℝ,
      (∫ v : EuclideanSpace ℝ (Fin d), ‖(kgSchwartzOp^[j] (Φ t - Φ t')) v‖)
        ≤ L * (volume K).toReal * |t - t'| := by
    intro t t'
    have hbase := integral_kgSchwartzOp_le hK hKmeas hKfin (hsuppSub t t') j (hL t t')
    refine hbase.trans_eq ?_
    ring
  exact openProbes_of_schwartzCurve hN hdim hj hM' (mul_nonneg hL0 hvol) hL' hreal

end SupProbe

/-! ## The operator at the level of functions -/

/-- The Klein–Gordon operator on functions. -/
noncomputable def kgFunOp (g : E → ℂ) : E → ℂ :=
  fun x => g x - (((2 * Real.pi) ^ 2 : ℝ))⁻¹ • Δ g x

theorem coe_kgSchwartzOp (f : 𝓢(E, ℂ)) : ⇑(kgSchwartzOp f) = kgFunOp (f : E → ℂ) := by
  funext x
  rw [kgSchwartzOp_eq, sub_apply, smul_apply, SchwartzMap.laplacian_apply, kgFunOp]

/-- **The Schwartz-level iterate is the function-level iterate.** This is what lets the sup bounds of
the probe theorem be checked on an explicit differential expression. -/
theorem coe_kgSchwartzOp_iterate (j : ℕ) (f : 𝓢(E, ℂ)) :
    ⇑(kgSchwartzOp^[j] f) = kgFunOp^[j] (f : E → ℂ) := by
  induction j generalizing f with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih (kgSchwartzOp f),
      coe_kgSchwartzOp]

end GaloisForLFunctions.HTGeometry
