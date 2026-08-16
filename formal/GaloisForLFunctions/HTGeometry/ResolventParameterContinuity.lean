import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The resolvent as a function of the spectral parameter

On the resolvent set the resolvent is continuous in its parameter: it is the composition of the
affine map `r ↦ algebraMap r - a` with inversion, which is continuous at units.  Consequently every
quadratic form `⟪u, R(r) v⟫` of the resolvent is continuous in `r`.

Far from the spectrum the resolvent not only vanishes but does so at the exact rate `1/r`: from
`(algebraMap r - a) · R(r) = 1` and `R(r) → 0` one gets `r • R(r) → 1`.  So the normalised quadratic
forms converge to the inner products themselves, and any scale-invariant ratio of two of them
converges to the ratio of the corresponding inner products.

These are the two inputs an intermediate-value argument on a resolvent-defined angle needs: interior
continuity, and the free endpoint.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Bornology

section Algebra

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
  [CompleteSpace A]

/-- **Parameter continuity of the resolvent.** -/
theorem continuousAt_resolvent (a : A) {r : 𝕜} (hr : r ∈ resolventSet 𝕜 a) :
    ContinuousAt (resolvent a) r := by
  have hshift : ContinuousAt (fun t : 𝕜 => algebraMap 𝕜 A t - a) r := by
    exact (continuous_algebraMap 𝕜 A).continuousAt.sub continuousAt_const
  have hunit : IsUnit (algebraMap 𝕜 A r - a) := hr
  obtain ⟨u, hu⟩ := hunit
  have hinv : ContinuousAt Ring.inverse (algebraMap 𝕜 A r - a) := by
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  have hcomp : ContinuousAt (Ring.inverse ∘ fun t : 𝕜 => algebraMap 𝕜 A t - a) r :=
    ContinuousAt.comp hinv hshift
  exact hcomp

/-- The resolvent is continuous on the whole resolvent set. -/
theorem continuousOn_resolvent (a : A) : ContinuousOn (resolvent a) (resolventSet 𝕜 a) :=
  fun _ hr => (continuousAt_resolvent a hr).continuousWithinAt

omit [CompleteSpace A] in
/-- On the resolvent set the resolvent really inverts the shift. -/
theorem shift_mul_resolvent (a : A) {r : 𝕜} (hr : r ∈ resolventSet 𝕜 a) :
    (algebraMap 𝕜 A r - a) * resolvent a r = 1 :=
  Ring.mul_inverse_cancel _ hr

/-- **The exact free rate.**  Far from the spectrum the resolvent behaves like `1/r`. -/
theorem tendsto_smul_resolvent (a : A) :
    Tendsto (fun r : 𝕜 => r • resolvent a r) (cobounded 𝕜 ⊓ 𝓟 (resolventSet 𝕜 a)) (𝓝 1) := by
  have hzero : Tendsto (resolvent a) (cobounded 𝕜 ⊓ 𝓟 (resolventSet 𝕜 a)) (𝓝 0) :=
    (spectrum.resolvent_tendsto_cobounded a).mono_left inf_le_left
  have hmul : Tendsto (fun r : 𝕜 => a * resolvent a r)
      (cobounded 𝕜 ⊓ 𝓟 (resolventSet 𝕜 a)) (𝓝 (a * 0)) :=
    Filter.Tendsto.const_mul a hzero
  have hlim : Tendsto (fun r : 𝕜 => 1 + a * resolvent a r)
      (cobounded 𝕜 ⊓ 𝓟 (resolventSet 𝕜 a)) (𝓝 1) := by
    have h : Tendsto (fun r : 𝕜 => (1 : A) + a * resolvent a r)
        (cobounded 𝕜 ⊓ 𝓟 (resolventSet 𝕜 a)) (𝓝 ((1 : A) + a * 0)) :=
      (tendsto_const_nhds (x := (1 : A))).add hmul
    simpa using h
  refine Filter.Tendsto.congr' ?_ hlim
  filter_upwards [mem_inf_of_right (mem_principal_self _)] with r hr
  have hid := shift_mul_resolvent a hr
  rw [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at hid
  rw [← hid]
  abel

end Algebra

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Parameter continuity of a resolvent quadratic form.** -/
theorem continuousAt_resolvent_inner (a : H →L[ℝ] H) (u v : H) {r : ℝ}
    (hr : r ∈ resolventSet ℝ a) :
    ContinuousAt (fun t : ℝ => inner ℝ u ((resolvent a t) v)) r := by
  have heval : Continuous fun T : H →L[ℝ] H => inner ℝ u (T v) := by
    exact (innerSL ℝ u).continuous.comp (ContinuousLinearMap.apply ℝ H v).continuous
  exact heval.continuousAt.comp (continuousAt_resolvent a hr)

/-- The projective polarization of the two resolvent energies of a pair of vectors. -/
noncomputable def resolventPolarization (a : H →L[ℝ] H) (u v : H) (t : ℝ) : ℝ :=
  (inner ℝ u ((resolvent a t) u) - inner ℝ v ((resolvent a t) v)) /
    (inner ℝ u ((resolvent a t) u) + inner ℝ v ((resolvent a t) v))

/-- **Interior continuity of the polarization.** -/
theorem continuousAt_resolventPolarization (a : H →L[ℝ] H) (u v : H) {r : ℝ}
    (hr : r ∈ resolventSet ℝ a)
    (hsum : inner ℝ u ((resolvent a r) u) + inner ℝ v ((resolvent a r) v) ≠ (0 : ℝ)) :
    ContinuousAt (resolventPolarization a u v) r := by
  have hE := continuousAt_resolvent_inner a u u hr
  have hO := continuousAt_resolvent_inner a v v hr
  exact (hE.sub hO).div (hE.add hO) hsum

/-- The normalised energy converges to the squared norm. -/
theorem tendsto_smul_resolvent_inner (a : H →L[ℝ] H) (u : H) :
    Tendsto (fun t : ℝ => t * inner ℝ u ((resolvent a t) u))
      (cobounded ℝ ⊓ 𝓟 (resolventSet ℝ a)) (𝓝 (‖u‖ ^ 2)) := by
  have heval : Continuous fun T : H →L[ℝ] H => inner ℝ u (T u) :=
    (innerSL ℝ u).continuous.comp (ContinuousLinearMap.apply ℝ H u).continuous
  have h := heval.continuousAt.tendsto.comp (tendsto_smul_resolvent (𝕜 := ℝ) a)
  have hone : inner ℝ u ((1 : H →L[ℝ] H) u) = ‖u‖ ^ 2 := by
    simp
  rw [Function.comp_def, hone] at h
  refine h.congr fun t => ?_
  simp [real_inner_smul_right]

/-- **The free endpoint of the polarization.**  Far from the spectrum the polarization is the
projective polarization of the two squared norms. -/
theorem tendsto_resolventPolarization (a : H →L[ℝ] H) (u v : H)
    (hne : ‖u‖ ^ 2 + ‖v‖ ^ 2 ≠ 0) :
    Tendsto (resolventPolarization a u v) (cobounded ℝ ⊓ 𝓟 (resolventSet ℝ a))
      (𝓝 ((‖u‖ ^ 2 - ‖v‖ ^ 2) / (‖u‖ ^ 2 + ‖v‖ ^ 2))) := by
  have hE := tendsto_smul_resolvent_inner a u
  have hO := tendsto_smul_resolvent_inner a v
  have hquot := (hE.sub hO).div (hE.add hO) hne
  refine hquot.congr' ?_
  have hden : ∀ᶠ t : ℝ in cobounded ℝ ⊓ 𝓟 (resolventSet ℝ a),
      t * inner ℝ u ((resolvent a t) u) + t * inner ℝ v ((resolvent a t) v) ≠ 0 :=
    (hE.add hO).eventually_ne hne
  have hzero : ∀ᶠ t : ℝ in cobounded ℝ ⊓ 𝓟 (resolventSet ℝ a), t ≠ 0 := by
    refine Filter.Eventually.filter_mono inf_le_left ?_
    exact Bornology.eventually_ne_cobounded (0 : ℝ)
  filter_upwards [hden, hzero] with t hd ht
  simp only [Pi.div_apply]
  rw [resolventPolarization]
  rw [show t * inner ℝ u ((resolvent a t) u) - t * inner ℝ v ((resolvent a t) v)
      = t * (inner ℝ u ((resolvent a t) u) - inner ℝ v ((resolvent a t) v)) by ring,
    show t * inner ℝ u ((resolvent a t) u) + t * inner ℝ v ((resolvent a t) v)
      = t * (inner ℝ u ((resolvent a t) u) + inner ℝ v ((resolvent a t) v)) by ring]
  rw [mul_div_mul_left _ _ ht]

/-! ## The ground endpoint

At an eigenvalue the resolvent has an exact simple pole along the eigenvector, so the *residue* of a
quadratic form is the overlap with that eigenvector — an identity, not a limit.  A source splits into
its ground component and a remainder; if the remainder's resolvent stays bounded, the whole
normalised energy converges to the ground overlap.
-/

omit [CompleteSpace H] in
/-- The resolvent inverts the shift on the other side as well. -/
theorem resolvent_mul_shift (a : H →L[ℝ] H) {t : ℝ} (ht : t ∈ resolventSet ℝ a) :
    resolvent a t * (algebraMap ℝ (H →L[ℝ] H) t - a) = 1 :=
  Ring.inverse_mul_cancel _ ht

omit [CompleteSpace H] in
/-- **The resolvent acts on an eigenvector by the scalar resolvent.** -/
theorem resolvent_apply_of_eigen {a : H →L[ℝ] H} {lam0 : ℝ} {g : H} (hg : a g = lam0 • g)
    {t : ℝ} (ht : t ∈ resolventSet ℝ a) (hne : t ≠ lam0) :
    (resolvent a t) g = (t - lam0)⁻¹ • g := by
  have hsub : t - lam0 ≠ 0 := sub_ne_zero.mpr hne
  have halg : (algebraMap ℝ (H →L[ℝ] H) t) g = t • g := by
    rw [Algebra.algebraMap_eq_smul_one]
    simp
  have hshift : (algebraMap ℝ (H →L[ℝ] H) t - a) g = (t - lam0) • g := by
    have happ : (algebraMap ℝ (H →L[ℝ] H) t - a) g
        = (algebraMap ℝ (H →L[ℝ] H) t) g - a g := rfl
    rw [happ, halg, hg, sub_smul]
  have hcancel : (resolvent a t) ((algebraMap ℝ (H →L[ℝ] H) t - a) g) = g := by
    have h := congrArg (fun T : H →L[ℝ] H => T g) (resolvent_mul_shift a ht)
    simpa using h
  rw [hshift, ContinuousLinearMap.map_smul] at hcancel
  have hscaled := congrArg (fun x : H => (t - lam0)⁻¹ • x) hcancel
  simpa [smul_smul, inv_mul_cancel₀ hsub] using hscaled

omit [CompleteSpace H] in
/-- **The residue at an eigenvalue is the overlap.**  This is an identity in the parameter, not a
limiting statement. -/
theorem sub_mul_inner_resolvent_eigen {a : H →L[ℝ] H} {lam0 : ℝ} {g : H} (hg : a g = lam0 • g)
    (u : H) {t : ℝ} (ht : t ∈ resolventSet ℝ a) (hne : t ≠ lam0) :
    (t - lam0) * inner ℝ u ((resolvent a t) g) = inner ℝ u g := by
  have hsub : t - lam0 ≠ 0 := sub_ne_zero.mpr hne
  rw [resolvent_apply_of_eigen hg ht hne, real_inner_smul_right, ← mul_assoc,
    mul_inv_cancel₀ hsub, one_mul]

omit [CompleteSpace H] in
/-- **The ground endpoint under a splitting.**  A source that is a ground eigenvector plus a
remainder of bounded resolvent has normalised energy converging to the ground overlap. -/
theorem tendsto_sub_mul_inner_resolvent_of_splitting {a : H →L[ℝ] H} {lam0 : ℝ} {g w : H}
    (hg : a g = lam0 • g) (u : H) {C : ℝ}
    (hres : ∀ᶠ t in 𝓝[<] lam0, t ∈ resolventSet ℝ a ∧ ‖(resolvent a t) w‖ ≤ C) :
    Tendsto (fun t : ℝ => (t - lam0) * inner ℝ u ((resolvent a t) (g + w)))
      (𝓝[<] lam0) (𝓝 (inner ℝ u g)) := by
  have hCnn : 0 ≤ C := by
    obtain ⟨t, ht⟩ := hres.exists
    exact le_trans (norm_nonneg _) ht.2
  have hsmall : Tendsto (fun t : ℝ => (t - lam0) * inner ℝ u ((resolvent a t) w))
      (𝓝[<] lam0) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun t : ℝ => |t - lam0| * (‖u‖ * C)) ?_ ?_
    · filter_upwards [hres] with t ht
      rw [norm_mul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc ‖inner ℝ u ((resolvent a t) w)‖ ≤ ‖u‖ * ‖(resolvent a t) w‖ :=
            norm_inner_le_norm _ _
        _ ≤ ‖u‖ * C := mul_le_mul_of_nonneg_left ht.2 (norm_nonneg _)
    · have hc : Tendsto (fun t : ℝ => t - lam0) (𝓝[<] lam0) (𝓝 0) := by
        have h0 : Tendsto (fun t : ℝ => t - lam0) (𝓝 lam0) (𝓝 (lam0 - lam0)) :=
          ((continuous_sub_right lam0).tendsto lam0)
        rw [sub_self] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      have habs : Tendsto (fun t : ℝ => |t - lam0|) (𝓝[<] lam0) (𝓝 0) := by
        simpa using hc.abs
      simpa using habs.mul_const (‖u‖ * C)
  have hground : Tendsto (fun t : ℝ => (t - lam0) * inner ℝ u ((resolvent a t) g))
      (𝓝[<] lam0) (𝓝 (inner ℝ u g)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hres, self_mem_nhdsWithin] with t ht hlt
    exact (sub_mul_inner_resolvent_eigen hg u ht.1 (ne_of_lt hlt)).symm
  have hsum := hground.add hsmall
  rw [add_zero] at hsum
  refine hsum.congr fun t => ?_
  rw [map_add, inner_add_right]
  ring

omit [CompleteSpace H] in
/-- **The ground endpoint of the polarization.**  With both sources split into a ground eigenvector
and a remainder of bounded resolvent, the polarization tends to the projective polarization of the
two ground overlaps. -/
theorem tendsto_resolventPolarization_ground {a : H →L[ℝ] H} {lam0 : ℝ} {gu gv wu wv : H}
    (hgu : a gu = lam0 • gu) (hgv : a gv = lam0 • gv) {Cu Cv : ℝ}
    (hu : ∀ᶠ t in 𝓝[<] lam0, t ∈ resolventSet ℝ a ∧ ‖(resolvent a t) wu‖ ≤ Cu)
    (hv : ∀ᶠ t in 𝓝[<] lam0, t ∈ resolventSet ℝ a ∧ ‖(resolvent a t) wv‖ ≤ Cv)
    (hne : inner ℝ (gu + wu) gu + inner ℝ (gv + wv) gv ≠ (0 : ℝ)) :
    Tendsto (resolventPolarization a (gu + wu) (gv + wv)) (𝓝[<] lam0)
      (𝓝 ((inner ℝ (gu + wu) gu - inner ℝ (gv + wv) gv)
        / (inner ℝ (gu + wu) gu + inner ℝ (gv + wv) gv))) := by
  have hE := tendsto_sub_mul_inner_resolvent_of_splitting hgu (gu + wu) hu
  have hO := tendsto_sub_mul_inner_resolvent_of_splitting hgv (gv + wv) hv
  have hquot := (hE.sub hO).div (hE.add hO) hne
  refine hquot.congr' ?_
  have hden : ∀ᶠ t : ℝ in 𝓝[<] lam0,
      (t - lam0) * inner ℝ (gu + wu) ((resolvent a t) (gu + wu))
        + (t - lam0) * inner ℝ (gv + wv) ((resolvent a t) (gv + wv)) ≠ 0 :=
    (hE.add hO).eventually_ne hne
  filter_upwards [hden, self_mem_nhdsWithin] with t hd hlt
  have ht : t - lam0 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hlt)
  simp only [Pi.div_apply]
  rw [resolventPolarization]
  rw [show (t - lam0) * inner ℝ (gu + wu) ((resolvent a t) (gu + wu))
        - (t - lam0) * inner ℝ (gv + wv) ((resolvent a t) (gv + wv))
      = (t - lam0) * (inner ℝ (gu + wu) ((resolvent a t) (gu + wu))
          - inner ℝ (gv + wv) ((resolvent a t) (gv + wv))) by ring,
    show (t - lam0) * inner ℝ (gu + wu) ((resolvent a t) (gu + wu))
        + (t - lam0) * inner ℝ (gv + wv) ((resolvent a t) (gv + wv))
      = (t - lam0) * (inner ℝ (gu + wu) ((resolvent a t) (gu + wu))
          + inner ℝ (gv + wv) ((resolvent a t) (gv + wv))) by ring]
  rw [mul_div_mul_left _ _ ht]

end Hilbert

end GaloisForLFunctions.HTGeometry
