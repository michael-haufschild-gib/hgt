import GaloisForLFunctions.HTGeometry.HelsonContinuationData

/-!
# Certificates at every level assemble to a meromorphic continuation

Each level certificate gives a meromorphic model `∑ c n w ^ n / ∏ (w - u i)` on its disc.  Two models
agree wherever both denominators are nonzero: the two products of a series with the other's
polynomial are holomorphic on the smaller disc and agree near `s = 2`, so the identity theorem makes
them equal.  Consequently the models have a common germ at every point, up to the finitely many
roots of the two polynomials, and the value obtained by putting the local model into meromorphic
normal form does not depend on the level.

That common value is a meromorphic function on the whole plane which agrees with the Euler product
on the half plane of absolute convergence, because there the polynomial has no roots.
-/

open Complex Filter Topology

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The meromorphic model attached to a level certificate. -/
def levelModel {d : ℕ} (u : Fin d → ℂ) (c : ℕ → ℂ) : ℂ → ℂ :=
  fun s => seriesSum c (s - 2) / rootPoly u (s - 2)

/-- Normal forms of two functions with the same punctured germ agree at the point. -/
theorem toMeromorphicNFAt_apply_congr {f g : ℂ → ℂ} {x : ℂ}
    (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) (h : f =ᶠ[𝓝[≠] x] g) :
    toMeromorphicNFAt f x x = toMeromorphicNFAt g x x := by
  have h₁ : toMeromorphicNFAt f x =ᶠ[𝓝[≠] x] toMeromorphicNFAt g x :=
    ((hf.eq_nhdsNE_toMeromorphicNFAt).symm.trans h).trans hg.eq_nhdsNE_toMeromorphicNFAt
  have h₂ : toMeromorphicNFAt f x =ᶠ[𝓝 x] toMeromorphicNFAt g x :=
    (MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      meromorphicNFAt_toMeromorphicNFAt meromorphicNFAt_toMeromorphicNFAt).1 h₁
  exact h₂.eq_of_nhds

/-- The shifted polynomial of a root vector is entire. -/
theorem analyticAt_rootPoly_shift {d : ℕ} (u : Fin d → ℂ) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => rootPoly u (z - 2)) s := by
  have hprod : AnalyticAt ℂ (∏ i : Fin d, fun z : ℂ => z - 2 - u i) s := by
    refine Finset.analyticAt_prod (f := fun (i : Fin d) (z : ℂ) => z - 2 - u i) _ fun i _ => ?_
    have h1 : AnalyticAt ℂ (fun z : ℂ => z) s := analyticAt_id
    exact (h1.sub analyticAt_const).sub analyticAt_const
  have heq : (∏ i : Fin d, fun z : ℂ => z - 2 - u i) = fun z : ℂ => rootPoly u (z - 2) := by
    funext z
    rw [rootPoly, Finset.prod_apply]
  rwa [heq] at hprod

/-- The series of a level certificate is holomorphic on its disc. -/
theorem analyticAt_seriesSum_shift {N B : ℕ} {c : ℕ → ℂ}
    (hc : ∀ n, ‖c n‖ * levelRadius N ^ n ≤ (B : ℝ)) {s : ℂ} (hs : ‖s - 2‖ < levelRadius N) :
    AnalyticAt ℂ (fun z : ℂ => seriesSum c (z - 2)) s := by
  have hinner : AnalyticAt ℂ (fun z : ℂ => z - 2) s := analyticAt_id.sub analyticAt_const
  have houter : AnalyticAt ℂ (seriesSum c) (s - 2) := by
    refine analyticOnNhd_seriesSum_of_levelData (N := N) (B := B) hc (s - 2) ?_
    simpa [Metric.mem_ball, dist_eq_norm] using hs
  have hcomp : AnalyticAt ℂ ((seriesSum c) ∘ fun z : ℂ => z - 2) s :=
    AnalyticAt.comp (g := seriesSum c) (f := fun z : ℂ => z - 2) (x := s) houter hinner
  simpa [Function.comp_def] using hcomp

/-- The model of a level certificate is meromorphic on the disc of that level. -/
theorem meromorphicAt_levelModel {N B d : ℕ} {u : Fin d → ℂ} {c : ℕ → ℂ}
    (hc : ∀ n, ‖c n‖ * levelRadius N ^ n ≤ (B : ℝ)) {s : ℂ} (hs : ‖s - 2‖ < levelRadius N) :
    MeromorphicAt (levelModel u c) s :=
  ((analyticAt_seriesSum_shift (N := N) (B := B) hc hs).meromorphicAt).div
    ((analyticAt_rootPoly_shift u s).meromorphicAt)

/-- The roots of a level polynomial, as points of the plane. -/
theorem rootPoly_shift_ne_zero_of_notMem {d : ℕ} (u : Fin d → ℂ) {z : ℂ}
    (hz : z ∉ Set.range (fun i => 2 + u i)) : rootPoly u (z - 2) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  intro h
  refine hz ⟨i, ?_⟩
  show (2 : ℂ) + u i = z
  have h2 : z - 2 = u i := sub_eq_zero.mp h
  rw [← h2]
  ring

/-- **The models of two levels agree off the roots of the two polynomials.** -/
theorem levelModel_eqOn_of_le {χ : PhaseTorus} {M N BM BN dM dN : ℕ}
    {uM : Fin dM → ℂ} {cM : ℕ → ℂ} {uN : Fin dN → ℂ} {cN : ℕ → ℂ}
    (hM : LevelData χ M BM uM cM) (hN : LevelData χ N BN uN cN) (hMN : M ≤ N) :
    ∀ z : ℂ, ‖z - 2‖ < levelRadius M →
      seriesSum cM (z - 2) * rootPoly uN (z - 2)
        = seriesSum cN (z - 2) * rootPoly uM (z - 2) := by
  have hρ : levelRadius M ≤ levelRadius N := by
    have hcast : (M : ℝ) ≤ (N : ℝ) := Nat.cast_le.2 hMN
    simp only [levelRadius]
    linarith
  have hMpos : (3 : ℝ) ≤ levelRadius M := by
    simp only [levelRadius]
    have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  set U : Set ℂ := Metric.ball (2 : ℂ) (levelRadius M) with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUconn : IsPreconnected U := (convex_ball (2 : ℂ) (levelRadius M)).isPreconnected
  have hmemU : ∀ z : ℂ, z ∈ U ↔ ‖z - 2‖ < levelRadius M := by
    intro z
    simp [hU, Metric.mem_ball, dist_eq_norm]
  have hf : AnalyticOnNhd ℂ (fun z : ℂ => seriesSum cM (z - 2) * rootPoly uN (z - 2)) U := by
    intro z hz
    exact (analyticAt_seriesSum_shift (N := M) (B := BM) hM.2.1 ((hmemU z).1 hz)).mul
      (analyticAt_rootPoly_shift uN z)
  have hg : AnalyticOnNhd ℂ (fun z : ℂ => seriesSum cN (z - 2) * rootPoly uM (z - 2)) U := by
    intro z hz
    have hzN : ‖z - 2‖ < levelRadius N := lt_of_lt_of_le ((hmemU z).1 hz) hρ
    exact (analyticAt_seriesSum_shift (N := N) (B := BN) hN.2.1 hzN).mul
      (analyticAt_rootPoly_shift uM z)
  have hnear : (fun z : ℂ => seriesSum cM (z - 2) * rootPoly uN (z - 2))
      =ᶠ[𝓝 (2 : ℂ)] fun z : ℂ => seriesSum cN (z - 2) * rootPoly uM (z - 2) := by
    have hball : Metric.ball (2 : ℂ) 1 ∈ 𝓝 (2 : ℂ) :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos)
    filter_upwards [hball] with z hz
    have hnorm : ‖z - 2‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hre : 1 < z.re := by
      have h1 : |z.re - 2| ≤ ‖z - 2‖ := by
        simpa using Complex.abs_re_le_norm (z - 2)
      have := abs_lt.1 (lt_of_le_of_lt h1 hnorm)
      linarith [this.1]
    have hzM : ‖z - 2‖ < levelRadius M := by linarith
    have hzN : ‖z - 2‖ < levelRadius N := lt_of_lt_of_le hzM hρ
    have hidM := hM.2.2 z hzM hre
    have hidN := hN.2.2 z hzN hre
    rw [← hidM, ← hidN]
    ring
  have h2mem : ‖(2 : ℂ) - 2‖ < levelRadius M := by
    simp only [sub_self, norm_zero]
    linarith
  have := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hf hg hUconn
    (z₀ := (2 : ℂ)) ((hmemU 2).2 h2mem) hnear
  intro z hz
  exact this ((hmemU z).2 hz)

end GaloisForLFunctions.HTGeometry

end

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Complex Filter Topology

theorem levelRadius_mono {M N : ℕ} (h : M ≤ N) : levelRadius M ≤ levelRadius N := by
  have hcast : (M : ℝ) ≤ (N : ℝ) := Nat.cast_le.2 h
  simp only [levelRadius]
  linarith

/-- **Two level models have the same punctured germ at every point of the smaller disc.** -/
theorem levelModel_eventuallyEq {χ : PhaseTorus} {M N BM BN dM dN : ℕ}
    {uM : Fin dM → ℂ} {cM : ℕ → ℂ} {uN : Fin dN → ℂ} {cN : ℕ → ℂ}
    (hM : LevelData χ M BM uM cM) (hN : LevelData χ N BN uN cN) (hMN : M ≤ N)
    {s : ℂ} (hs : ‖s - 2‖ < levelRadius M) :
    levelModel uM cM =ᶠ[𝓝[≠] s] levelModel uN cN := by
  classical
  set Zbad : Set ℂ :=
    (((Set.range fun i => 2 + uM i) ∪ (Set.range fun i => 2 + uN i)) \ {s}) with hZ
  have hfin : Zbad.Finite := by
    refine Set.Finite.sdiff ?_
    exact (Set.finite_range _).union (Set.finite_range _)
  set A : Set ℂ := {z : ℂ | ‖z - 2‖ < levelRadius M} ∩ Zbadᶜ with hA
  have hAopen : IsOpen A := by
    refine IsOpen.inter ?_ hfin.isClosed.isOpen_compl
    have : {z : ℂ | ‖z - 2‖ < levelRadius M} = Metric.ball (2 : ℂ) (levelRadius M) := by
      ext z
      simp [Metric.mem_ball, dist_eq_norm]
    rw [this]
    exact Metric.isOpen_ball
  have hsA : s ∈ A := by
    refine ⟨hs, ?_⟩
    simp [hZ]
  filter_upwards [nhdsWithin_le_nhds (hAopen.mem_nhds hsA), self_mem_nhdsWithin] with z hzA hzne
  have hzne' : z ≠ s := hzne
  have hznot : z ∉ (Set.range fun i => 2 + uM i) ∪ (Set.range fun i => 2 + uN i) := by
    intro hmem
    exact hzA.2 ⟨hmem, hzne'⟩
  have hqM : rootPoly uM (z - 2) ≠ 0 :=
    rootPoly_shift_ne_zero_of_notMem uM (fun h => hznot (Or.inl h))
  have hqN : rootPoly uN (z - 2) ≠ 0 :=
    rootPoly_shift_ne_zero_of_notMem uN (fun h => hznot (Or.inr h))
  have hid := levelModel_eqOn_of_le hM hN hMN z hzA.1
  simp only [levelModel]
  field_simp
  linear_combination hid

/-- **Certificates at every level give a meromorphic continuation.** -/
theorem mem_continuableStratum_of_continuationCriterion {χ : PhaseTorus}
    (hcrit : ContinuationCriterion χ) : χ ∈ continuableStratum := by
  classical
  choose B d u c hdata using hcrit
  set ν : ℂ → ℕ := fun s => ⌈‖s - 2‖⌉₊ with hνdef
  have hνlt : ∀ s : ℂ, ‖s - 2‖ < levelRadius (ν s) := by
    intro s
    have h1 : ‖s - 2‖ ≤ ((⌈‖s - 2‖⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    simp only [levelRadius, hνdef]
    linarith
  have hmodelmero : ∀ (N : ℕ) (s : ℂ), ‖s - 2‖ < levelRadius N →
      MeromorphicAt (levelModel (u N) (c N)) s := fun N s hs =>
    meromorphicAt_levelModel (N := N) (B := B N) (hdata N).2.1 hs
  set F : ℂ → ℂ := fun s => toMeromorphicNFAt (levelModel (u (ν s)) (c (ν s))) s s with hFdef
  have hFval : ∀ (N : ℕ) (s : ℂ), ν s ≤ N →
      F s = toMeromorphicNFAt (levelModel (u N) (c N)) s s := by
    intro N s hle
    refine toMeromorphicNFAt_apply_congr (hmodelmero (ν s) s (hνlt s))
      (hmodelmero N s (lt_of_lt_of_le (hνlt s) (levelRadius_mono hle))) ?_
    exact levelModel_eventuallyEq (hdata (ν s)) (hdata N) hle (hνlt s)
  refine ⟨F, ?_, ?_⟩
  · intro s₀ _
    set M : ℕ := ν s₀ + 1 with hMdef
    set W : Set ℂ := Metric.ball s₀ 1 with hWdef
    have hWopen : IsOpen W := Metric.isOpen_ball
    have hWmem : s₀ ∈ W := Metric.mem_ball_self one_pos
    have hWbound : ∀ z ∈ W, ν z ≤ M := by
      intro z hz
      have hdist : ‖z - s₀‖ < 1 := by simpa [hWdef, Metric.mem_ball, dist_eq_norm] using hz
      have hsplit : ‖z - 2‖ ≤ ‖z - s₀‖ + ‖s₀ - 2‖ := by
        have : z - 2 = (z - s₀) + (s₀ - 2) := by ring
        rw [this]
        exact norm_add_le _ _
      have h2 : ‖s₀ - 2‖ ≤ ((ν s₀ : ℕ) : ℝ) := Nat.le_ceil _
      refine Nat.ceil_le.2 ?_
      rw [hMdef]
      push_cast
      linarith
    have hWrad : ∀ z ∈ W, ‖z - 2‖ < levelRadius M := fun z hz =>
      lt_of_lt_of_le (hνlt z) (levelRadius_mono (hWbound z hz))
    have hmeroW : MeromorphicOn (levelModel (u M) (c M)) W :=
      fun z hz => hmodelmero M z (hWrad z hz)
    have hFeqW : ∀ z ∈ W, F z = toMeromorphicNFOn (levelModel (u M) (c M)) W z := by
      intro z hz
      rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hmeroW hz]
      exact hFval M z (hWbound z hz)
    have hNFmero : MeromorphicAt (toMeromorphicNFOn (levelModel (u M) (c M)) W) s₀ :=
      (meromorphicNFOn_toMeromorphicNFOn _ _).meromorphicOn s₀ hWmem
    refine hNFmero.congr ?_
    filter_upwards [nhdsWithin_le_nhds (hWopen.mem_nhds hWmem)] with z hz
    exact (hFeqW z hz).symm
  · intro s hs
    have hre : -1 < (s - 2).re := by
      have : (s - 2).re = s.re - 2 := by simp
      rw [this]
      linarith
    have hqne : rootPoly (u (ν s)) (s - 2) ≠ 0 :=
      rootPoly_ne_zero_of_mem_rootBox (hdata (ν s)).1 hre
    have hana : AnalyticAt ℂ (levelModel (u (ν s)) (c (ν s))) s := by
      refine AnalyticAt.div ?_ (analyticAt_rootPoly_shift _ s) hqne
      exact analyticAt_seriesSum_shift (N := ν s) (B := B (ν s)) (hdata (ν s)).2.1 (hνlt s)
    have hFs : F s = levelModel (u (ν s)) (c (ν s)) s := by
      rw [hFdef]
      exact congrFun (toMeromorphicNFAt_eq_self.2 hana.meromorphicNFAt) s
    have hval : levelModel (u (ν s)) (c (ν s)) s = helsonZetaValue s χ := by
      have hid := (hdata (ν s)).2.2 s (hνlt s) hs
      simp only [levelModel]
      rw [← hid]
      field_simp
    rw [hFs, hval, helsonZetaValue]
    exact (multipliable_helsonEuler (norm_phase_le_one χ) hs).hasProd

end

end GaloisForLFunctions.HTGeometry
