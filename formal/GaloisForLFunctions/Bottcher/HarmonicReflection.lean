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



theorem harmonicAt_reflect_line {f : ℂ → ℝ} {p : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hp : p.im = 0)
    (hf_off : ∀ z ∈ ball p ρ, z.im ≠ 0 → HarmonicAt f z)
    (hf_cont : ContinuousOn f (ball p ρ))
    (hf_odd : ∀ z ∈ ball p ρ, f ((starRingEnd ℂ) z) = - f z) :
    HarmonicAt f p := by
  set ρ' : ℝ := ρ / 2 with hρ'
  have hρ'0 : 0 < ρ' := by rw [hρ']; linarith
  have hρ'ρ : ρ' ≤ ρ := by rw [hρ']; linarith
  have hballsub : ball p ρ' ⊆ ball p ρ := ball_subset_ball hρ'ρ
  have hcb : closedBall p ρ' ⊆ ball p ρ := Metric.closedBall_subset_ball (by rw [hρ']; linarith)
  have hfcb : ContinuousOn f (closedBall p ρ') := hf_cont.mono hcb
  set P : ℂ → ℝ := poissonExt p ρ' f with hPdef
  have hPharm : HarmonicOnNhd P (ball p ρ') :=
    poissonExt_harmonicOnNhd hρ'0 (hfcb.mono sphere_subset_closedBall)
  have hPcont : ContinuousOn P (closedBall p ρ') := poissonExt_continuousOn hρ'0 hfcb
  have hPsph : ∀ z ∈ sphere p ρ', P z = f z := poissonExt_eq_on_sphere
  have hfront : frontier (ball p ρ') = sphere p ρ' := frontier_ball p hρ'0.ne'
  -- P is odd: P = 0 on the real axis
  have hPaxis : ∀ z ∈ ball p ρ', z.im = 0 → P z = 0 := by
    have hQharm : HarmonicOnNhd (fun z => P z + P ((starRingEnd ℂ) z)) (ball p ρ') := fun z hz =>
      (hPharm z hz).add (harmonicAt_comp_conj (hPharm _ (conj_mem_ball_of_real hp hz)))
    have hQcont : ContinuousOn (fun z => P z + P ((starRingEnd ℂ) z)) (closure (ball p ρ')) := by
      rw [closure_ball p hρ'0.ne']
      exact hPcont.add (hPcont.comp Complex.continuous_conj.continuousOn
        (fun z hz => conj_mem_closedBall_of_real hp hz))
    have hQbdry : ∀ z ∈ frontier (ball p ρ'), (fun z => P z + P ((starRingEnd ℂ) z)) z = 0 := by
      rw [hfront]; intro z hz
      have hzball : z ∈ ball p ρ := hcb (sphere_subset_closedBall hz)
      show P z + P ((starRingEnd ℂ) z) = 0
      rw [hPsph z hz, hPsph _ (conj_mem_sphere_of_real hp hz), hf_odd z hzball]; ring
    have hQ0 := harmonic_eqZero_of_boundary_zero isOpen_ball (convex_ball p ρ').isPreconnected
      isBounded_ball (hfront ▸ NormedSpace.sphere_nonempty.mpr hρ'0.le) hQharm hQcont hQbdry
    intro z hz hzim
    have hcz : (starRingEnd ℂ) z = z := Complex.conj_eq_iff_im.mpr hzim
    have h := hQ0 z hz
    simp only [hcz] at h; linarith
  -- half-plane vanishing helper
  have hhalf : ∀ (S : Set ℂ), IsOpen S → IsPreconnected S → S ⊆ ball p ρ' →
      (∀ z ∈ S, z.im ≠ 0) → (frontier S).Nonempty →
      (∀ w ∈ frontier S, w.im = 0 ∨ w ∈ sphere p ρ') → ∀ z ∈ S, f z = P z := by
    intro S hSo hSc hSsub hSim hSfne hSfr z hzS
    have hSbdd : Bornology.IsBounded S := (isBounded_ball (x := p) (r := ρ')).subset hSsub
    have hclS : closure S ⊆ closedBall p ρ' :=
      (closure_mono hSsub).trans (le_of_eq (closure_ball p hρ'0.ne'))
    have hg : HarmonicOnNhd (fun w => f w - P w) S := fun w hw =>
      (hf_off w (hballsub (hSsub hw)) (hSim w hw)).sub (hPharm w (hSsub hw))
    have hgc : ContinuousOn (fun w => f w - P w) (closure S) :=
      (hf_cont.mono (hclS.trans hcb)).sub (hPcont.mono hclS)
    have hgb : ∀ w ∈ frontier S, (fun w => f w - P w) w = 0 := by
      intro w hwf
      have hwcl : w ∈ closedBall p ρ' := hclS (frontier_subset_closure hwf)
      have hwball : w ∈ ball p ρ := hcb hwcl
      rcases hSfr w hwf with him | hsph
      · rcases lt_or_eq_of_le (mem_closedBall.mp hwcl) with hlt | heq
        · have hf0 : f w = 0 := by
            have := hf_odd w hwball; rw [Complex.conj_eq_iff_im.mpr him] at this; linarith
          show f w - P w = 0; rw [hf0, hPaxis w (mem_ball.mpr hlt) him]; ring
        · show f w - P w = 0; rw [hPsph w (mem_sphere.mpr heq)]; ring
      · show f w - P w = 0; rw [hPsph w hsph]; ring
    have := harmonic_eqZero_of_boundary_zero hSo hSc hSbdd hSfne hg hgc hgb z hzS
    linarith
  -- f = P on the ball
  have hfP : ∀ z ∈ ball p ρ', f z = P z := by
    have hSu_o : IsOpen ({z : ℂ | 0 < z.im} ∩ ball p ρ') :=
      (isOpen_lt continuous_const continuous_im).inter isOpen_ball
    have hSl_o : IsOpen ({z : ℂ | z.im < 0} ∩ ball p ρ') :=
      (isOpen_lt continuous_im continuous_const).inter isOpen_ball
    have hclim_up : closure {z : ℂ | 0 < z.im} = {z : ℂ | 0 ≤ z.im} := by
      exact closure_setOf_lt_im 0
    have hclim_lo : closure {z : ℂ | z.im < 0} = {z : ℂ | z.im ≤ 0} := by
      exact closure_setOf_im_lt 0
    -- upper
    have hfrSu : ∀ w ∈ frontier ({z : ℂ | 0 < z.im} ∩ ball p ρ'), w.im = 0 ∨ w ∈ sphere p ρ' := by
      intro w hwf
      have hwcl := frontier_subset_closure hwf
      have hwnS : w ∉ {z : ℂ | 0 < z.im} ∩ ball p ρ' := by
        rw [← hSu_o.interior_eq]; exact hwf.2
      have hclSu : closure ({z : ℂ | 0 < z.im} ∩ ball p ρ') ⊆
          {z : ℂ | 0 ≤ z.im} ∩ closedBall p ρ' := by
        refine closure_inter_subset.trans ?_
        rw [closure_ball p hρ'0.ne', hclim_up]
      obtain ⟨hwim, hwcb⟩ := hclSu hwcl
      by_cases hwsph : w ∈ sphere p ρ'
      · exact Or.inr hwsph
      · have hwball : w ∈ ball p ρ' := by
          rcases lt_or_eq_of_le (mem_closedBall.mp hwcb) with h | h
          · exact mem_ball.mpr h
          · exact absurd (mem_sphere.mpr h) hwsph
        exact Or.inl (le_antisymm (not_lt.mp fun h => hwnS ⟨h, hwball⟩) hwim)
    have hfrSl : ∀ w ∈ frontier ({z : ℂ | z.im < 0} ∩ ball p ρ'), w.im = 0 ∨ w ∈ sphere p ρ' := by
      intro w hwf
      have hwcl := frontier_subset_closure hwf
      have hwnS : w ∉ {z : ℂ | z.im < 0} ∩ ball p ρ' := by
        rw [← hSl_o.interior_eq]; exact hwf.2
      have hclSl : closure ({z : ℂ | z.im < 0} ∩ ball p ρ') ⊆
          {z : ℂ | z.im ≤ 0} ∩ closedBall p ρ' := by
        refine closure_inter_subset.trans ?_
        rw [closure_ball p hρ'0.ne', hclim_lo]
      obtain ⟨hwim, hwcb⟩ := hclSl hwcl
      by_cases hwsph : w ∈ sphere p ρ'
      · exact Or.inr hwsph
      · have hwball : w ∈ ball p ρ' := by
          rcases lt_or_eq_of_le (mem_closedBall.mp hwcb) with h | h
          · exact mem_ball.mpr h
          · exact absurd (mem_sphere.mpr h) hwsph
        exact Or.inl (le_antisymm hwim (not_lt.mp fun h => hwnS ⟨h, hwball⟩))
    have hmk : ∀ (σ : ℝ), σ = 1 ∨ σ = -1 → p ∈ closure ({z : ℂ | 0 < σ * z.im} ∩ ball p ρ') := by
      intro σ hσ
      rw [Metric.mem_closure_iff]
      intro ε hε
      set t : ℝ := min (ε / 2) (ρ' / 2) with ht
      have ht0 : 0 < t := lt_min (by linarith) (by linarith)
      have hnorm : ‖p + Complex.I * (σ * t : ℝ) - p‖ = t := by
        rw [show p + Complex.I * (σ * t : ℝ) - p = Complex.I * (σ * t : ℝ) by ring,
          norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        rcases hσ with h | h <;> rw [h] <;> simp [abs_of_pos ht0]
      refine ⟨p + Complex.I * (σ * t : ℝ), ⟨?_, ?_⟩, ?_⟩
      · show 0 < σ * (p + Complex.I * (σ * t : ℝ)).im
        have him : (p + Complex.I * (σ * t : ℝ)).im = σ * t := by
          simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
            Complex.ofReal_im, hp]; ring
        rw [him]; rcases hσ with h | h <;> rw [h] <;> nlinarith [ht0]
      · rw [mem_ball, dist_eq_norm, hnorm]; calc t ≤ ρ'/2 := min_le_right _ _
          _ < ρ' := by linarith
      · rw [dist_comm, dist_eq_norm, hnorm]; calc t ≤ ε/2 := min_le_left _ _
          _ < ε := by linarith
    have hpfrU : p ∈ frontier ({z : ℂ | 0 < z.im} ∩ ball p ρ') := by
      refine ⟨?_, ?_⟩
      · have := hmk 1 (Or.inl rfl); simpa using this
      · rw [hSu_o.interior_eq]; exact fun h => lt_irrefl (0:ℝ) (hp ▸ h.1)
    have hpfrL : p ∈ frontier ({z : ℂ | z.im < 0} ∩ ball p ρ') := by
      refine ⟨?_, ?_⟩
      · have := hmk (-1) (Or.inr rfl)
        have heq : ({z : ℂ | 0 < (-1 : ℝ) * z.im} ∩ ball p ρ') = ({z : ℂ | z.im < 0} ∩ ball p ρ') := by
          ext w; simp only [mem_inter_iff, mem_setOf_eq]; constructor <;> (rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩)
        rwa [heq] at this
      · rw [hSl_o.interior_eq]; exact fun h => lt_irrefl (0:ℝ) (hp ▸ h.1)
    intro z hz
    rcases lt_trichotomy z.im 0 with hlt | heq | hgt
    · exact hhalf _ hSl_o ((convex_halfSpace_im_lt 0).inter (convex_ball p ρ')).isPreconnected
        inter_subset_right (fun w hw => ne_of_lt hw.1) ⟨p, hpfrL⟩ hfrSl z ⟨hlt, hz⟩
    · have := hf_odd z (hballsub hz); rw [Complex.conj_eq_iff_im.mpr heq] at this
      rw [(by linarith : f z = 0), hPaxis z hz heq]
    · exact hhalf _ hSu_o ((convex_halfSpace_im_gt 0).inter (convex_ball p ρ')).isPreconnected
        inter_subset_right (fun w hw => ne_of_gt hw.1) ⟨p, hpfrU⟩ hfrSu z ⟨hgt, hz⟩
  have hfharm : HarmonicOnNhd f (ball p ρ') := fun z hz =>
    (harmonicAt_congr_nhds (by
      filter_upwards [isOpen_ball.mem_nhds hz] with y hy using (hfP y hy))).mpr (hPharm z hz)
  exact hfharm p (mem_ball_self hρ'0)

end Bottcher
