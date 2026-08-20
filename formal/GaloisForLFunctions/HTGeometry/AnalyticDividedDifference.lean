import GaloisForLFunctions.HTGeometry.CriticalTraceSpace
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Analytic divided differences on a collar

The translation defect of a differentiable function over a convex collar obeys the mean value
inequality, so its critically normalised form `(1+|λ|)/|λ| · ‖T_λ f - f‖` is bounded by the
derivative size on the collar: the raw source defects of an analytic germ lie in the critical trace
topology.  Sharpening the comparison function from `0` to the derivative at the base point shows
that the normalised defect converges to the vertical derivative as the period tends to zero — the
zero-period boundary of the critically completed source action is differentiation, not an extra
evolution law.

The same argument iterates: an `r`-fold divided difference over a collar closed under each
translation is bounded by the `r`-th derivative size times the product of the periods.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The translation defect `T_λ f - f` of a function by one period. -/
def translationDefect (f : ℂ → X) (lam : ℂ) : ℂ → X := fun z => f (z + lam) - f z

/-- The iterated translation defect along a list of periods. -/
def iterTranslationDefect (f : ℂ → X) : List ℂ → ℂ → X
  | [] => f
  | lam :: rest => iterTranslationDefect (translationDefect f lam) rest

/-! ### The collar bound -/

/-- **(7)** The mean value inequality on a convex collar. -/
theorem norm_translationDefect_le {f f' : ℂ → X} {s : Set ℂ} {C : ℝ} (hs : Convex ℝ s)
    (hf : ∀ w ∈ s, HasDerivAt f (f' w) w) (hb : ∀ w ∈ s, ‖f' w‖ ≤ C)
    {z lam : ℂ} (hz : z ∈ s) (hzl : z + lam ∈ s) :
    ‖translationDefect f lam z‖ ≤ C * ‖lam‖ := by
  have h := hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hf x hx).hasDerivWithinAt) hb hz hzl
  simpa [translationDefect] using h

/-- **(7), critical form.**  On a collar of radius `ε` the critically normalised defect of an
analytic germ is bounded by `(1+ε)` times the derivative size: the raw source-defect family lies in
the critical trace topology. -/
theorem critical_norm_translationDefect_le {f f' : ℂ → X} {s : Set ℂ} {C ε : ℝ} (hs : Convex ℝ s)
    (hf : ∀ w ∈ s, HasDerivAt f (f' w) w) (hb : ∀ w ∈ s, ‖f' w‖ ≤ C)
    {z lam : ℂ} (hz : z ∈ s) (hzl : z + lam ∈ s) (hlam : lam ≠ 0) (hle : ‖lam‖ ≤ ε) :
    (1 + ‖lam‖) / ‖lam‖ * ‖translationDefect f lam z‖ ≤ (1 + ε) * C := by
  have hpos : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hb z hz)
  have hdef := norm_translationDefect_le hs hf hb hz hzl
  have hstep : (1 + ‖lam‖) / ‖lam‖ * ‖translationDefect f lam z‖
      ≤ (1 + ‖lam‖) / ‖lam‖ * (C * ‖lam‖) := by
    have hcoef : 0 ≤ (1 + ‖lam‖) / ‖lam‖ := by positivity
    exact mul_le_mul_of_nonneg_left hdef hcoef
  have hval : (1 + ‖lam‖) / ‖lam‖ * (C * ‖lam‖) = (1 + ‖lam‖) * C := by
    field_simp
  rw [hval] at hstep
  have hmono : (1 + ‖lam‖) * C ≤ (1 + ε) * C := by
    have : (1 : ℝ) + ‖lam‖ ≤ 1 + ε := by linarith
    exact mul_le_mul_of_nonneg_right this hC
  linarith

/-- The collar bound for a germ holomorphic on an open convex collar.  A meromorphic germ
restricted to a pole-free collar is such a germ, so its raw translation-defect family lies in the
critical trace topology. -/
theorem norm_translationDefect_le_of_differentiableOn {f : ℂ → X} {s : Set ℂ} {C : ℝ}
    (hs : Convex ℝ s) (hso : IsOpen s) (hf : DifferentiableOn ℂ f s)
    (hb : ∀ w ∈ s, ‖deriv f w‖ ≤ C) {z lam : ℂ} (hz : z ∈ s) (hzl : z + lam ∈ s) :
    ‖translationDefect f lam z‖ ≤ C * ‖lam‖ :=
  norm_translationDefect_le hs
    (fun _ hw => (hf.differentiableAt (hso.mem_nhds hw)).hasDerivAt) hb hz hzl

/-! ### Convergence to the vertical derivative -/

/-- **(8)** Comparing with the derivative at the base point: the normalised defect differs from the
derivative by at most the oscillation of the derivative on the collar. -/
theorem norm_translationDefect_sub_smul_deriv_le {f f' : ℂ → X} {s : Set ℂ} {C : ℝ}
    (hs : Convex ℝ s) (hf : ∀ w ∈ s, HasDerivAt f (f' w) w) {z : ℂ} (hz : z ∈ s)
    (hb : ∀ w ∈ s, ‖f' w - f' z‖ ≤ C) {lam : ℂ} (hzl : z + lam ∈ s) :
    ‖translationDefect f lam z - lam • f' z‖ ≤ C * ‖lam‖ := by
  set g : ℂ → X := fun w => f w - w • f' z with hg
  have hgd : ∀ w ∈ s, HasDerivAt g (f' w - f' z) w := by
    intro w hw
    have h1 : HasDerivAt (fun w : ℂ => w • f' z) (f' z) w := by
      simpa using (hasDerivAt_id w).smul_const (f' z)
    exact (hf w hw).sub h1
  have h := hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hgd x hx).hasDerivWithinAt) hb hz hzl
  have hval : g (z + lam) - g z = translationDefect f lam z - lam • f' z := by
    rw [hg, translationDefect]
    simp only [add_smul]
    abel
  rw [hval] at h
  simpa using h

/-- The normalised defect converges to the vertical derivative as the period tends to zero. -/
theorem tendsto_normalized_translationDefect {f : ℂ → X} {z : ℂ} {d : X}
    (hf : HasDerivAt f d z) :
    Tendsto (fun lam : ℂ => lam⁻¹ • translationDefect f lam z) (𝓝[≠] (0 : ℂ)) (𝓝 d) := by
  have hslope : Tendsto (slope f z) (𝓝[≠] z) (𝓝 d) := hasDerivAt_iff_tendsto_slope.mp hf
  have hmap : Tendsto (fun lam : ℂ => z + lam) (𝓝[≠] (0 : ℂ)) (𝓝[≠] z) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Tendsto (fun lam : ℂ => z + lam) (𝓝 (0 : ℂ)) (𝓝 z) := by
        simpa using Filter.Tendsto.const_add z (tendsto_id : Tendsto (id : ℂ → ℂ) (𝓝 0) (𝓝 0))
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with lam hlam
      have hlam0 : lam ≠ 0 := hlam
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hcon
      exact hlam0 (by simpa using hcon)
  have hcomp := hslope.comp hmap
  refine hcomp.congr fun lam => ?_
  simp [Function.comp_apply, slope, translationDefect]

/-! ### Mixed divided differences -/

/-- **(9)** An `r`-fold divided difference on a collar closed under each translation is bounded by
the `r`-th derivative size times the product of the periods. -/
theorem norm_iterTranslationDefect_le {s : Set ℂ} (hs : Convex ℝ s) :
    ∀ (L : List ℂ) (g : ℕ → ℂ → X) (C : ℝ),
      (∀ k, ∀ w ∈ s, HasDerivAt (g k) (g (k + 1) w) w) →
      (∀ lam ∈ L, ∀ w ∈ s, w + lam ∈ s) →
      (∀ w ∈ s, ‖g L.length w‖ ≤ C) →
      ∀ z ∈ s, ‖iterTranslationDefect (g 0) L z‖ ≤ C * (L.map (fun lam => ‖lam‖)).prod := by
  intro L
  induction L with
  | nil =>
      intro g C _ _ hb z hz
      simpa [iterTranslationDefect] using hb z hz
  | cons lam rest ih =>
      intro g C hd hin hb z hz
      have hlamS : ∀ w ∈ s, w + lam ∈ s := hin lam List.mem_cons_self
      have hdh : ∀ k, ∀ w ∈ s,
          HasDerivAt (fun w' : ℂ => translationDefect (g k) lam w')
            (translationDefect (g (k + 1)) lam w) w := by
        intro k w hw
        have hinner : HasDerivAt (fun z' : ℂ => z' + lam) 1 w := by
          simpa using (hasDerivAt_id w).add_const lam
        have houter := hd k (w + lam) (hlamS w hw)
        have h1 : HasDerivAt (fun z' : ℂ => g k (z' + lam)) (g (k + 1) (w + lam)) w := by
          simpa [Function.comp_def] using houter.scomp w hinner
        exact h1.sub (hd k w hw)
      have hbh : ∀ w ∈ s, ‖translationDefect (g rest.length) lam w‖ ≤ C * ‖lam‖ := by
        intro w hw
        refine norm_translationDefect_le hs (fun x hx => hd rest.length x hx)
          (fun x hx => ?_) hw (hlamS w hw)
        simpa using hb x hx
      have hinr : ∀ mu ∈ rest, ∀ w ∈ s, w + mu ∈ s :=
        fun mu hmu => hin mu (List.mem_cons_of_mem _ hmu)
      have hstep := ih (fun k => translationDefect (g k) lam) (C * ‖lam‖) hdh hinr hbh z hz
      have hprod : ((lam :: rest).map (fun mu : ℂ => ‖mu‖)).prod
          = ‖lam‖ * (rest.map (fun mu : ℂ => ‖mu‖)).prod := by
        simp
      rw [iterTranslationDefect, hprod, ← mul_assoc]
      exact hstep

end GaloisForLFunctions.HTGeometry
