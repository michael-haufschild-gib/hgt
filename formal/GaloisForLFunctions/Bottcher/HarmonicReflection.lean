/-
# Harmonic Schwarz reflection — building blocks

Toward the harmonic reflection principle that discharges `hu` (`BottcherArcExtension.lean`).  This
file collects the reusable harmonic-analysis lemmas on top of the Dirichlet-problem solution
(`HarmonicMaxPrinciple.lean`, `PoissonHarmonic.lean`, `PoissonBoundary.lean`):

* `harmonic_eqZero_of_boundary_zero` — bounded-domain vanishing (Koebe keystone): harmonic on a
  bounded preconnected open set, continuous up to the closure and zero on the frontier ⟹ zero.
* `harmonicAt_comp_conj` — harmonicity is preserved by domain conjugation (`u ∘ conj`), via the local
  `Re(conj ∘ F ∘ conj)` structure.
* `harmonicAt_comp_analytic` — harmonic ∘ holomorphic is harmonic (`u ∘ h`, `h` analytic), via the
  local `Re(F ∘ h)` structure.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/
import Mathlib
import GaloisForLFunctions.Bottcher.HarmonicMaxPrinciple
import GaloisForLFunctions.Bottcher.PoissonHarmonic
import GaloisForLFunctions.Bottcher.PoissonBoundary

open Complex Set Metric InnerProductSpace Topology Filter
open scoped Classical

namespace Bottcher

/-- **Bounded-domain vanishing (Koebe keystone).**  A harmonic function on a bounded preconnected
open set `B` (nonempty frontier), continuous up to `closure B` and vanishing on `frontier B`, vanishes
on all of `B`.  Both `u` and `-u` attain a compact maximum; if positive it lies at an interior point,
forcing `u` constant (`harmonic_eqOn_const_of_isMaxOn`), hence equal to its zero frontier value. -/
theorem harmonic_eqZero_of_boundary_zero {u : ℂ → ℝ} {B : Set ℂ}
    (hBo : IsOpen B) (hBc : IsPreconnected B) (hBbdd : Bornology.IsBounded B)
    (hBfront : (frontier B).Nonempty)
    (hu : HarmonicOnNhd u B) (hucont : ContinuousOn u (closure B))
    (hbdry : ∀ z ∈ frontier B, u z = 0) : ∀ z ∈ B, u z = 0 := by
  have hKcomp : IsCompact (closure B) :=
    isCompact_of_isClosed_isBounded isClosed_closure hBbdd.closure
  have hclne : (closure B).Nonempty := hBfront.mono frontier_subset_closure
  have hle : ∀ v : ℂ → ℝ, HarmonicOnNhd v B → ContinuousOn v (closure B) →
      (∀ z ∈ frontier B, v z = 0) → ∀ z ∈ B, v z ≤ 0 := by
    intro v hv hvc hvb z hzB
    obtain ⟨p, hpcl, hpmax⟩ := hKcomp.exists_isMaxOn hclne hvc
    by_contra hlt
    have hvz_pos : 0 < v z := not_le.mp hlt
    have hvp_pos : 0 < v p := lt_of_lt_of_le hvz_pos (hpmax (subset_closure hzB))
    have hpB : p ∈ B := by
      by_contra hpnB
      have hpf : p ∈ frontier B := ⟨hpcl, fun h => hpnB (hBo.interior_eq ▸ h)⟩
      exact (ne_of_gt hvp_pos) (hvb p hpf)
    have hconst : Set.EqOn v (fun _ => v p) B :=
      harmonic_eqOn_const_of_isMaxOn hBc hBo hv hpB (fun y hyB => hpmax (subset_closure hyB))
    have hconstCl : Set.EqOn v (fun _ => v p) (closure B) :=
      hconst.of_subset_closure hvc continuousOn_const subset_closure (le_refl _)
    obtain ⟨q, hqf⟩ := hBfront
    have hvq : v q = v p := hconstCl (frontier_subset_closure hqf)
    rw [hvb q hqf] at hvq
    exact (ne_of_gt hvp_pos) hvq.symm
  have h1 : ∀ z ∈ B, u z ≤ 0 := hle u hu hucont hbdry
  have h2 : ∀ z ∈ B, (-u) z ≤ 0 :=
    hle (-u) hu.neg hucont.neg (fun z hz => by simp [Pi.neg_apply, hbdry z hz])
  intro z hzB
  have := h2 z hzB
  simp only [Pi.neg_apply] at this
  linarith [h1 z hzB]

/-- **Harmonicity under domain conjugation.**  If `u` is harmonic at `conj w`, then `u ∘ conj` is
harmonic at `w`.  Locally `u = Re F` (`F` analytic), so `u(conj z) = Re(conj (F (conj z)))` and
`conj ∘ F ∘ conj` is analytic (`differentiableAt_conj_conj_iff`). -/
theorem harmonicAt_comp_conj {u : ℂ → ℝ} {w : ℂ}
    (h : HarmonicAt u ((starRingEnd ℂ) w)) :
    HarmonicAt (fun z => u ((starRingEnd ℂ) z)) w := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h.eventually
  have hdist : ∀ z : ℂ, dist ((starRingEnd ℂ) z) ((starRingEnd ℂ) w) = dist z w := by
    intro z; rw [dist_eq_norm, dist_eq_norm, ← map_sub, RCLike.norm_conj]
  have hHar : HarmonicOnNhd u (ball ((starRingEnd ℂ) w) ε) := fun y hy => hball (mem_ball.mp hy)
  obtain ⟨F, hFan, hFre⟩ := hHar.exists_analyticOnNhd_ball_re_eq
  set G : ℂ → ℂ := fun z => (starRingEnd ℂ) (F ((starRingEnd ℂ) z)) with hG
  have hconjmem : ∀ z ∈ ball w ε, (starRingEnd ℂ) z ∈ ball ((starRingEnd ℂ) w) ε := by
    intro z hz; rw [mem_ball, hdist]; exact mem_ball.mp hz
  have hGan : AnalyticAt ℂ G w := by
    apply DifferentiableOn.analyticAt (s := ball w ε) _ (ball_mem_nhds w hε)
    intro z hz
    have hFd : DifferentiableAt ℂ F ((starRingEnd ℂ) z) := (hFan _ (hconjmem z hz)).differentiableAt
    have : DifferentiableAt ℂ (⇑(starRingEnd ℂ) ∘ F ∘ ⇑(starRingEnd ℂ)) z := by
      rw [differentiableAt_conj_conj_iff]; exact hFd
    exact this.differentiableWithinAt
  have hre := hGan.harmonicAt_re
  refine (harmonicAt_congr_nhds ?_).mp hre
  filter_upwards [ball_mem_nhds w hε] with z hz
  have hre2 : (F ((starRingEnd ℂ) z)).re = u ((starRingEnd ℂ) z) := hFre (hconjmem z hz)
  show (G z).re = u ((starRingEnd ℂ) z)
  rw [hG]; simp only [Complex.conj_re]; exact hre2

/-- **Harmonic ∘ holomorphic is harmonic.**  If `u` is harmonic at `h w` and `h` is analytic at `w`,
then `u ∘ h` is harmonic at `w`.  Locally `u = Re F`, so `u(h z) = Re(F(h z))` with `F ∘ h` analytic. -/
theorem harmonicAt_comp_analytic {u : ℂ → ℝ} {h : ℂ → ℂ} {w : ℂ}
    (hu : HarmonicAt u (h w)) (hh : AnalyticAt ℂ h w) :
    HarmonicAt (fun z => u (h z)) w := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hu.eventually
  have hHar : HarmonicOnNhd u (ball (h w) ε) := fun y hy => hball (mem_ball.mp hy)
  obtain ⟨F, hFan, hFre⟩ := hHar.exists_analyticOnNhd_ball_re_eq
  have hhmem : ∀ᶠ z in 𝓝 w, h z ∈ ball (h w) ε :=
    hh.continuousAt.eventually (ball_mem_nhds (h w) hε)
  have hGan : AnalyticAt ℂ (fun z => F (h z)) w := (hFan (h w) (mem_ball_self hε)).comp hh
  have hre := hGan.harmonicAt_re
  refine (harmonicAt_congr_nhds ?_).mp hre
  filter_upwards [hhmem] with z hz
  show (F (h z)).re = u (h z)
  exact hFre hz


noncomputable def poissonExt (p : ℂ) (R : ℝ) (f : ℂ → ℝ) : ℂ → ℝ :=
  fun w => if w ∈ ball p R then Real.circleAverage (poissonKernel p w • f) p R else f w

theorem poissonExt_harmonicOnNhd {p : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℝ}
    (hf : ContinuousOn f (sphere p R)) : HarmonicOnNhd (poissonExt p R f) (ball p R) := by
  have hHar := poissonInt_harmonicOnNhd hR hf
  intro w hw
  refine (harmonicAt_congr_nhds ?_).mpr (hHar w hw)
  filter_upwards [isOpen_ball.mem_nhds hw] with z hz
  simp only [poissonExt, if_pos hz]

theorem poissonExt_eq_on_sphere {p : ℂ} {R : ℝ} {f : ℂ → ℝ} :
    ∀ z ∈ sphere p R, poissonExt p R f z = f z := by
  intro z hz
  have hnb : z ∉ ball p R := by
    rw [mem_sphere] at hz; rw [mem_ball, hz]; exact lt_irrefl R
  simp only [poissonExt, if_neg hnb]

theorem poissonExt_continuousOn {p : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℝ}
    (hf : ContinuousOn f (closedBall p R)) : ContinuousOn (poissonExt p R f) (closedBall p R) := by
  intro ζ hζcl
  rcases eq_or_lt_of_le (mem_closedBall.mp hζcl) with hζsp | hζin
  · have hζs : ζ ∈ sphere p R := mem_sphere.mpr hζsp
    have hcover : (closedBall p R : Set ℂ) = ball p R ∪ sphere p R := ball_union_sphere.symm
    rw [ContinuousWithinAt, poissonExt_eq_on_sphere ζ hζs, hcover, nhdsWithin_union, tendsto_sup]
    refine ⟨?_, ?_⟩
    · have htend := poissonInt_tendsto_boundary hR (hf.mono sphere_subset_closedBall) hζs
      refine htend.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [poissonExt, if_pos hz]
    · have hfc : Tendsto f (𝓝[sphere p R] ζ) (𝓝 (f ζ)) :=
        (hf ζ hζcl).mono sphere_subset_closedBall
      refine hfc.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz using (poissonExt_eq_on_sphere z hz).symm
  · have hin : ζ ∈ ball p R := mem_ball.mpr hζin
    exact ((poissonExt_harmonicOnNhd hR (hf.mono sphere_subset_closedBall) ζ hin).1.continuousAt).continuousWithinAt


-- geometry helpers for p real (im p = 0)
theorem conj_mem_ball_of_real {p : ℂ} (hp : p.im = 0) {R : ℝ} {z : ℂ} (hz : z ∈ ball p R) :
    (starRingEnd ℂ) z ∈ ball p R := by
  rw [mem_ball, dist_eq_norm] at hz ⊢
  have : (starRingEnd ℂ) z - p = (starRingEnd ℂ) (z - p) := by
    rw [map_sub]; congr 1; exact (Complex.conj_eq_iff_im.mpr hp).symm
  rw [this, RCLike.norm_conj]; exact hz

theorem conj_mem_sphere_of_real {p : ℂ} (hp : p.im = 0) {R : ℝ} {z : ℂ} (hz : z ∈ sphere p R) :
    (starRingEnd ℂ) z ∈ sphere p R := by
  rw [mem_sphere, dist_eq_norm] at hz ⊢
  have : (starRingEnd ℂ) z - p = (starRingEnd ℂ) (z - p) := by
    rw [map_sub]; congr 1; exact (Complex.conj_eq_iff_im.mpr hp).symm
  rw [this, RCLike.norm_conj]; exact hz

theorem conj_mem_closedBall_of_real {p : ℂ} (hp : p.im = 0) {R : ℝ} {z : ℂ}
    (hz : z ∈ closedBall p R) : (starRingEnd ℂ) z ∈ closedBall p R := by
  rw [mem_closedBall, dist_eq_norm] at hz ⊢
  have : (starRingEnd ℂ) z - p = (starRingEnd ℂ) (z - p) := by
    rw [map_sub]; congr 1; exact (Complex.conj_eq_iff_im.mpr hp).symm
  rw [this, RCLike.norm_conj]; exact hz


end Bottcher
