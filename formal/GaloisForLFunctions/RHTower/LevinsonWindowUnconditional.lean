import GaloisForLFunctions.RHTower.LevinsonLineZeroFactorization
import GaloisForLFunctions.RHTower.LevinsonFactoredPolar
import GaloisForLFunctions.RHTower.HardySignSubchainCount
import GaloisForLFunctions.HTGeometry.RectangleNodeProductVariation

/-!
# The Levinson window inequality with no hypothesis on the critical edge

The window inequality of `LevinsonWindowAdvance` assumes the detector does not vanish on the
critical segment.  That hypothesis is removable at no cost in the constant.

Write `G♯ = Q·H` with `Q` the node polynomial of the critical-line zeros of `G♯` in the window.  Two
exact facts do the work.

* On the left edge `Re (Q'/Q)(½+iτ) = 0`, because the singular part `m/(i(τ−τ_j))` is purely
  imaginary; so the left-edge integral of `G♯` and of `H` agree.
* On the other three edges the node polynomial contributes exactly `π` per unit of multiplicity
  (`nodeProduct_three_edge_variation`), while removing the nodes from the box lowers the zero count
  by exactly the same total multiplicity.

Together `∫_{left} Re (G♯'/G♯) = (three edges) − 2π·N_closed + π·M`, and the surplus `π·M` pays for
the `M` sign changes of the real node amplitude that the counting step loses.  What survives is the
zero-free bound with `n+1` replaced by `n+2`: one extra half-turn, independent of the window.
-/

open Complex Set MeasureTheory

noncomputable section

namespace RHTower

/-- **The Levinson window inequality without any hypothesis on the critical edge.** -/
theorem le_xiOddFiberCount_of_levinson_window_unconditional_of_Y_pos
    {lam : ℝ} (hlam0 : lam ≠ 0)
    {d T₁ T₂ : ℝ} (hd : (1 / 2 : ℝ) < d) (h20 : 20 ≤ T₁) (hT : T₁ < T₂) {n : ℕ}
    (hY : ∀ u ∈ Icc T₁ T₂, (0 : ℝ) < (levinsonY (lam : ℂ) (linePt u)).re)
    (hbot : ∀ x ∈ uIcc (1 / 2 : ℝ) d, levinsonGEntire (lam : ℂ) ((x : ℂ) + T₁ * I) ≠ 0)
    (htop : ∀ x ∈ uIcc (1 / 2 : ℝ) d, levinsonGEntire (lam : ℂ) ((x : ℂ) + T₂ * I) ≠ 0)
    (hright : ∀ t ∈ uIcc T₁ T₂, levinsonGEntire (lam : ℂ) ((d : ℂ) + t * I) ≠ 0)
    (hbound : ∀ Z : Finset ℂ,
      (∀ z : ℂ, z ∈ Z ↔
        z ∈ (uIcc (1 / 2 : ℝ) d ×ℂ uIcc T₁ T₂) ∧ levinsonGEntire (lam : ℂ) z = 0) →
      ((n : ℝ) + 2) * Real.pi ≤
        (gammaHardyTheta T₂ - gammaHardyTheta T₁)
          + (∫ t in T₁..T₂, (logDeriv (levinsonGEntire (lam : ℂ)) ((d : ℂ) + t * I)).re)
          + (∫ x in (1 / 2 : ℝ)..d,
              (logDeriv (levinsonGEntire (lam : ℂ)) ((x : ℂ) + T₁ * I)).im)
          - (∫ x in (1 / 2 : ℝ)..d,
              (logDeriv (levinsonGEntire (lam : ℂ)) ((x : ℂ) + T₂ * I)).im)
          - 2 * Real.pi *
            (∑ w ∈ Z, ((analyticOrderAt (levinsonGEntire (lam : ℂ)) w).toNat : ℝ))) :
    n ≤ xiOddFiberCount T₂ := by
  classical
  have hlamC : ((lam : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlam0
  obtain ⟨pts, m, H, hmemiff, hmpos, hordeq, hHdiff, hfact, hHline⟩ :=
    exists_levinson_line_factorization hlamC hT.le
  set F : ℂ → ℂ := levinsonGEntire (lam : ℂ) with hF
  set Qm : ℂ → ℂ := fun z => ∏ c ∈ pts, (z - c) ^ (m c) with hQm
  have hlinePtEq : ∀ t : ℝ, ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I = linePt t := fun t => rfl
  -- the nodes sit in the open left edge
  have hnodes : ∀ c ∈ pts, c.re = 1 / 2 ∧ T₁ < c.im ∧ c.im < T₂ := by
    intro c hc
    obtain ⟨⟨τ, hτ, rfl⟩, hz⟩ := (hmemiff c).mp hc
    refine ⟨linePt_re τ, ?_, ?_⟩
    · rw [linePt_im]
      rcases lt_or_eq_of_le hτ.1 with h | h
      · exact h
      · exfalso
        refine hbot (1 / 2 : ℝ) (by rw [uIcc_of_le hd.le]; exact ⟨le_rfl, hd.le⟩) ?_
        rw [hlinePtEq, h]
        exact hz
    · rw [linePt_im]
      rcases lt_or_eq_of_le hτ.2 with h | h
      · exact h
      · exfalso
        refine htop (1 / 2 : ℝ) (by rw [uIcc_of_le hd.le]; exact ⟨le_rfl, hd.le⟩) ?_
        rw [hlinePtEq, ← h]
        exact hz
  have hline : ∀ c ∈ pts, c.re = 1 / 2 := fun c hc => (hnodes c hc).1
  have hfun : F = fun z => Qm z * H z := by funext z; exact hfact z
  -- `H` is nonvanishing on the boundary of the rectangle
  have hHfromF : ∀ z : ℂ, F z ≠ 0 → H z ≠ 0 := by
    intro z hz h
    exact hz (by rw [hfact z, h, mul_zero])
  have hHbot : ∀ x ∈ uIcc (1 / 2 : ℝ) d, H ((x : ℂ) + T₁ * I) ≠ 0 :=
    fun x hx => hHfromF _ (hbot x hx)
  have hHtop : ∀ x ∈ uIcc (1 / 2 : ℝ) d, H ((x : ℂ) + T₂ * I) ≠ 0 :=
    fun x hx => hHfromF _ (htop x hx)
  have hHright : ∀ t ∈ uIcc T₁ T₂, H ((d : ℂ) + t * I) ≠ 0 :=
    fun t ht => hHfromF _ (hright t ht)
  have hHleft : ∀ t ∈ uIcc T₁ T₂, H (((1 / 2 : ℝ) : ℂ) + t * I) ≠ 0 := by
    intro t ht
    rw [uIcc_of_le hT.le] at ht
    rw [hlinePtEq]
    exact hHline t ht
  have hHan : AnalyticOnNhd ℂ H Set.univ := hHdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hHnz : ∃ z : ℂ, H z ≠ 0 :=
    ⟨linePt T₁, hHline T₁ ⟨le_rfl, hT.le⟩⟩
  obtain ⟨ZH, hZH, hHid⟩ := exists_entire_argument_variation_rectangle
    hHan hHnz hd hT hHbot hHtop hHright hHleft
  -- the zero set of `F` in the closed box
  have hHnodes : ∀ c ∈ pts, H c ≠ 0 := by
    intro c hc
    obtain ⟨⟨τ, hτ, rfl⟩, _⟩ := (hmemiff c).mp hc
    exact hHline τ hτ
  have hdisj : Disjoint ZH pts := by
    rw [Finset.disjoint_right]
    intro c hc hcZ
    exact hHnodes c hc ((hZH c).mp hcZ).2
  have hptsBox : ∀ c ∈ pts, c ∈ (uIcc (1 / 2 : ℝ) d ×ℂ uIcc T₁ T₂) := by
    intro c hc
    obtain ⟨hre, h1, h2⟩ := hnodes c hc
    rw [Complex.mem_reProdIm, hre, uIcc_of_le hd.le, uIcc_of_le hT.le]
    exact ⟨⟨le_rfl, hd.le⟩, ⟨h1.le, h2.le⟩⟩
  set ZG : Finset ℂ := ZH ∪ pts with hZGdef
  have hZGmem : ∀ z : ℂ, z ∈ ZG ↔ z ∈ (uIcc (1 / 2 : ℝ) d ×ℂ uIcc T₁ T₂) ∧ F z = 0 := by
    intro z
    rw [hZGdef, Finset.mem_union]
    constructor
    · rintro (hz | hz)
      · obtain ⟨hbox, hH0⟩ := (hZH z).mp hz
        exact ⟨hbox, by rw [hfact z, hH0, mul_zero]⟩
      · exact ⟨hptsBox z hz, ((hmemiff z).mp hz).2⟩
    · rintro ⟨hbox, hz⟩
      by_cases hH0 : H z = 0
      · exact Or.inl ((hZH z).mpr ⟨hbox, hH0⟩)
      · right
        have hQ0 : Qm z = 0 := by
          rcases mul_eq_zero.mp (by rw [← hfact z]; exact hz) with h | h
          · exact h
          · exact absurd h hH0
        by_contra hznot
        exact multiplicityFactor_ne_zero pts m hznot hQ0
  have hordsum : (∑ w ∈ ZG, ((analyticOrderAt F w).toNat : ℝ))
      = (∑ w ∈ ZH, ((analyticOrderAt H w).toNat : ℝ)) + (∑ c ∈ pts, (m c : ℝ)) := by
    rw [hZGdef, Finset.sum_union hdisj]
    congr 1
    · refine Finset.sum_congr rfl fun w hw => ?_
      have hwnot : w ∉ pts := Finset.disjoint_left.mp hdisj hw
      have hQ : Qm w ≠ 0 := multiplicityFactor_ne_zero pts m hwnot
      rw [analyticOrderAt_eq_of_factor_ne_zero (analyticAt_multiplicityFactor pts m w)
        (hHan w (mem_univ w)) hfact hQ]
    · refine Finset.sum_congr rfl fun c hc => ?_
      rw [hordeq c hc]
      simp
  -- edge conversion
  have hQman : ∀ z : ℂ, AnalyticAt ℂ Qm z := analyticAt_multiplicityFactor pts m
  have hFan : ∀ z : ℂ, AnalyticAt ℂ F z := fun z => analyticOnNhd_levinsonGEntire (lam : ℂ) z
    (mem_univ z)
  have hlogcont : ∀ (f : ℂ → ℂ), (∀ z, AnalyticAt ℂ f z) → ∀ (γ : ℝ → ℂ), Continuous γ →
      ∀ (S : Set ℝ), (∀ t ∈ S, f (γ t) ≠ 0) →
      ContinuousOn (fun t : ℝ => logDeriv f (γ t)) S := by
    intro f hf γ hγ S hS
    have h1 : Continuous fun t : ℝ => deriv f (γ t) :=
      continuous_iff_continuousAt.mpr fun t =>
        (((hf (γ t)).deriv).continuousAt).comp hγ.continuousAt
    have h2 : Continuous fun t : ℝ => f (γ t) :=
      continuous_iff_continuousAt.mpr fun t => ((hf (γ t)).continuousAt).comp hγ.continuousAt
    have h3 := ContinuousOn.div h1.continuousOn h2.continuousOn hS
    simpa [logDeriv_apply, Pi.div_def] using h3
  have hγR : Continuous fun t : ℝ => ((d : ℂ) + (t : ℂ) * I) := by fun_prop
  have hγB : Continuous fun x : ℝ => ((x : ℂ) + (T₁ : ℂ) * I) := by fun_prop
  have hγT : Continuous fun x : ℝ => ((x : ℂ) + (T₂ : ℂ) * I) := by fun_prop
  have hQmR : ∀ t : ℝ, Qm ((d : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t
    refine multiplicityFactor_ne_zero pts m ?_
    intro hmem
    have := (hnodes _ hmem).1
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at this
    linarith
  have hQmB : ∀ x : ℝ, Qm ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := by
    intro x
    refine multiplicityFactor_ne_zero pts m ?_
    intro hmem
    have := (hnodes _ hmem).2.1
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add] at this
    linarith
  have hQmT : ∀ x : ℝ, Qm ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := by
    intro x
    refine multiplicityFactor_ne_zero pts m ?_
    intro hmem
    have := (hnodes _ hmem).2.2
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add] at this
    linarith
  have hsplit : ∀ z : ℂ, Qm z ≠ 0 → H z ≠ 0 →
      logDeriv F z = logDeriv Qm z + logDeriv H z := by
    intro z hQ hH0
    rw [hfun]
    exact logDeriv_mul z hQ hH0 ((hQman z).differentiableAt) (hHdiff z)
  have hcontRe : ∀ (f : ℂ → ℂ), (∀ z, AnalyticAt ℂ f z) → ∀ (γ : ℝ → ℂ), Continuous γ →
      ∀ (S : Set ℝ), (∀ t ∈ S, f (γ t) ≠ 0) →
      ContinuousOn (fun t : ℝ => (logDeriv f (γ t)).re) S := by
    intro f hf γ hγ S hS
    simpa [Function.comp_def] using
      Complex.continuous_re.comp_continuousOn (hlogcont f hf γ hγ S hS)
  have hcontIm : ∀ (f : ℂ → ℂ), (∀ z, AnalyticAt ℂ f z) → ∀ (γ : ℝ → ℂ), Continuous γ →
      ∀ (S : Set ℝ), (∀ t ∈ S, f (γ t) ≠ 0) →
      ContinuousOn (fun t : ℝ => (logDeriv f (γ t)).im) S := by
    intro f hf γ hγ S hS
    simpa [Function.comp_def] using
      Complex.continuous_im.comp_continuousOn (hlogcont f hf γ hγ S hS)
  have hHan' : ∀ z : ℂ, AnalyticAt ℂ H z := fun z => hHan z (mem_univ z)
  have hIR : (∫ t in T₁..T₂, (logDeriv F ((d : ℂ) + (t : ℂ) * I)).re)
      = (∫ t in T₁..T₂, (logDeriv Qm ((d : ℂ) + (t : ℂ) * I)).re)
        + (∫ t in T₁..T₂, (logDeriv H ((d : ℂ) + (t : ℂ) * I)).re) := by
    rw [← intervalIntegral.integral_add
      ((hcontRe Qm hQman _ hγR (uIcc T₁ T₂) (fun t _ => hQmR t)).intervalIntegrable)
      ((hcontRe H hHan' _ hγR (uIcc T₁ T₂) hHright).intervalIntegrable)]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [hsplit _ (hQmR t) (hHright t ht), Complex.add_re]
  have hIB : (∫ x in (1 / 2 : ℝ)..d, (logDeriv F ((x : ℂ) + (T₁ : ℂ) * I)).im)
      = (∫ x in (1 / 2 : ℝ)..d, (logDeriv Qm ((x : ℂ) + (T₁ : ℂ) * I)).im)
        + (∫ x in (1 / 2 : ℝ)..d, (logDeriv H ((x : ℂ) + (T₁ : ℂ) * I)).im) := by
    rw [← intervalIntegral.integral_add
      ((hcontIm Qm hQman _ hγB (uIcc (1 / 2 : ℝ) d) (fun x _ => hQmB x)).intervalIntegrable)
      ((hcontIm H hHan' _ hγB (uIcc (1 / 2 : ℝ) d) hHbot).intervalIntegrable)]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [hsplit _ (hQmB x) (hHbot x hx), Complex.add_im]
  have hIT : (∫ x in (1 / 2 : ℝ)..d, (logDeriv F ((x : ℂ) + (T₂ : ℂ) * I)).im)
      = (∫ x in (1 / 2 : ℝ)..d, (logDeriv Qm ((x : ℂ) + (T₂ : ℂ) * I)).im)
        + (∫ x in (1 / 2 : ℝ)..d, (logDeriv H ((x : ℂ) + (T₂ : ℂ) * I)).im) := by
    rw [← intervalIntegral.integral_add
      ((hcontIm Qm hQman _ hγT (uIcc (1 / 2 : ℝ) d) (fun x _ => hQmT x)).intervalIntegrable)
      ((hcontIm H hHan' _ hγT (uIcc (1 / 2 : ℝ) d) hHtop).intervalIntegrable)]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [hsplit _ (hQmT x) (hHtop x hx), Complex.add_im]
  have hQmEdges := nodeProduct_three_edge_variation (pts := pts) m
    (c := (1 / 2 : ℝ)) (d := d) (T₁ := T₁) (T₂ := T₂) hd hnodes
  -- the factored polar form
  obtain ⟨ρ, φ, hφc, hρpos, hpolarZ, hadvH⟩ :=
    exists_factored_polar_hardyZ_advance_of_Y_pos (lam := lam) hT.le hY
      hline hHdiff hfact hHline
  set Mtot : ℕ := ∑ c ∈ pts, m c with hMtot
  have hMcast : ((Mtot : ℕ) : ℝ) = ∑ c ∈ pts, (m c : ℝ) := by
    rw [hMtot]; push_cast; ring
  have hbnd := hbound ZG hZGmem
  have hleftEq : (∫ τ in T₁..T₂, (logDeriv H (linePt τ)).re)
      = ∫ t in T₁..T₂, (logDeriv H (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re := rfl
  rw [hleftEq] at hadvH
  have hkey : ((n : ℝ) + 2) * Real.pi + Real.pi * (Mtot : ℝ) ≤ φ T₂ - φ T₁ := by
    rw [hMcast]
    rw [hordsum] at hbnd
    rw [hIR, hIB, hIT] at hbnd
    linarith [hadvH, hHid, hQmEdges, hbnd]
  have hadvFinal : φ T₁ + (((n + Mtot : ℕ) : ℝ) + 1) * Real.pi ≤ φ T₂ := by
    have hcast : ((n + Mtot : ℕ) : ℝ) = (n : ℝ) + (Mtot : ℝ) := by push_cast; ring
    rw [hcast]
    nlinarith [Real.pi_pos, hkey]
  have hPcont : ContinuousOn (fun τ : ℝ => ∏ c ∈ pts, (τ - c.im) ^ (m c)) (Icc T₁ T₂) := by
    refine Continuous.continuousOn ?_
    exact continuous_finsetProd pts fun c _ => by fun_prop
  have hPz : ∀ τ ∈ Icc T₁ T₂, (∏ c ∈ pts, (τ - c.im) ^ (m c)) = 0 →
      τ ∈ pts.image (fun c : ℂ => c.im) := by
    intro τ _ hz
    obtain ⟨c, hc, hcz⟩ := Finset.prod_eq_zero_iff.mp hz
    have : τ - c.im = 0 := pow_eq_zero_iff'.mp hcz |>.1
    exact Finset.mem_image.mpr ⟨c, hc, by linarith⟩
  have hcount := le_xiOddFiberCount_add_card_of_factored_advance
    (T₁ := T₁) (T₂ := T₂) (by linarith : (0 : ℝ) < T₁) hT.le
    (P := fun τ : ℝ => ∏ c ∈ pts, (τ - c.im) ^ (m c)) (ρ := ρ) (φ := φ) (n := n + Mtot)
    (S := pts.image (fun c : ℂ => c.im)) hPcont hPz hφc hρpos hpolarZ hadvFinal
  have hcard1 : (pts.image (fun c : ℂ => c.im)).card ≤ pts.card := Finset.card_image_le
  have hcard2 : pts.card ≤ Mtot := by
    have := Finset.card_nsmul_le_sum pts m 1 (fun c hc => hmpos c hc)
    simpa [hMtot] using this
  omega

/-- Legacy negative-shift specialization of the unconditional Levinson window inequality. -/
theorem le_xiOddFiberCount_of_levinson_window_unconditional {lam : ℝ} (hlam0 : lam < 0)
    {d T₁ T₂ : ℝ} (hd : (1 / 2 : ℝ) < d) (h20 : 20 ≤ T₁) (hT : T₁ < T₂) {n : ℕ}
    (hbot : ∀ x ∈ uIcc (1 / 2 : ℝ) d, levinsonGEntire (lam : ℂ) ((x : ℂ) + T₁ * I) ≠ 0)
    (htop : ∀ x ∈ uIcc (1 / 2 : ℝ) d, levinsonGEntire (lam : ℂ) ((x : ℂ) + T₂ * I) ≠ 0)
    (hright : ∀ t ∈ uIcc T₁ T₂, levinsonGEntire (lam : ℂ) ((d : ℂ) + t * I) ≠ 0)
    (hbound : ∀ Z : Finset ℂ,
      (∀ z : ℂ, z ∈ Z ↔
        z ∈ (uIcc (1 / 2 : ℝ) d ×ℂ uIcc T₁ T₂) ∧ levinsonGEntire (lam : ℂ) z = 0) →
      ((n : ℝ) + 2) * Real.pi ≤
        (gammaHardyTheta T₂ - gammaHardyTheta T₁)
          + (∫ t in T₁..T₂, (logDeriv (levinsonGEntire (lam : ℂ)) ((d : ℂ) + t * I)).re)
          + (∫ x in (1 / 2 : ℝ)..d,
              (logDeriv (levinsonGEntire (lam : ℂ)) ((x : ℂ) + T₁ * I)).im)
          - (∫ x in (1 / 2 : ℝ)..d,
              (logDeriv (levinsonGEntire (lam : ℂ)) ((x : ℂ) + T₂ * I)).im)
          - 2 * Real.pi *
            (∑ w ∈ Z, ((analyticOrderAt (levinsonGEntire (lam : ℂ)) w).toNat : ℝ))) :
    n ≤ xiOddFiberCount T₂ := by
  apply le_xiOddFiberCount_of_levinson_window_unconditional_of_Y_pos
    (lam := lam) (ne_of_lt hlam0) hd h20 hT
  · intro u hu
    rw [levinsonY_line_eq, Complex.ofReal_re]
    have hdig := log_pi_lt_re_digamma_quarter (le_trans h20 hu.1)
    have hmul : lam * ((Complex.digamma (((1 / 4 : ℝ) : ℂ)
        + ((u / 2 : ℝ) : ℂ) * Complex.I)).re - Real.log Real.pi) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hlam0.le (sub_nonneg.mpr hdig.le)
    linarith
  · exact hbot
  · exact htop
  · exact hright
  · exact hbound

/-- The unconditional Levinson window inequality in singleton-fibre form, assuming the exact
positive-weight condition needed by the polar argument. -/
theorem xiSingletonFiberCount_ge_of_levinson_window_unconditional_of_Y_pos
    {lam : ℝ} (hlam0 : lam ≠ 0)
    {d T₁ T₂ : ℝ} (hd : (1 / 2 : ℝ) < d) (h20 : 20 ≤ T₁) (hT : T₁ < T₂) {n : ℕ}
    (hY : ∀ u ∈ Icc T₁ T₂, (0 : ℝ) < (levinsonY (lam : ℂ) (linePt u)).re)
    (hbot : ∀ x ∈ uIcc (1 / 2 : ℝ) d, levinsonGEntire (lam : ℂ) ((x : ℂ) + T₁ * I) ≠ 0)
    (htop : ∀ x ∈ uIcc (1 / 2 : ℝ) d, levinsonGEntire (lam : ℂ) ((x : ℂ) + T₂ * I) ≠ 0)
    (hright : ∀ t ∈ uIcc T₁ T₂, levinsonGEntire (lam : ℂ) ((d : ℂ) + t * I) ≠ 0)
    (hbound : ∀ Z : Finset ℂ,
      (∀ z : ℂ, z ∈ Z ↔
        z ∈ (uIcc (1 / 2 : ℝ) d ×ℂ uIcc T₁ T₂) ∧ levinsonGEntire (lam : ℂ) z = 0) →
      ((n : ℝ) + 2) * Real.pi ≤
        (gammaHardyTheta T₂ - gammaHardyTheta T₁)
          + (∫ t in T₁..T₂, (logDeriv (levinsonGEntire (lam : ℂ)) ((d : ℂ) + t * I)).re)
          + (∫ x in (1 / 2 : ℝ)..d,
              (logDeriv (levinsonGEntire (lam : ℂ)) ((x : ℂ) + T₁ * I)).im)
          - (∫ x in (1 / 2 : ℝ)..d,
              (logDeriv (levinsonGEntire (lam : ℂ)) ((x : ℂ) + T₂ * I)).im)
          - 2 * Real.pi *
            (∑ w ∈ Z, ((analyticOrderAt (levinsonGEntire (lam : ℂ)) w).toNat : ℝ))) :
    (3 / 2 : ℝ) * (n : ℝ) - (xiPosZeroCount T₂ : ℝ) / 2
      ≤ (xiSingletonFiberCount T₂ : ℝ) := by
  have h1 := le_xiOddFiberCount_of_levinson_window_unconditional_of_Y_pos
    hlam0 hd h20 hT hY hbot htop hright hbound
  have h2 := three_mul_xiOddFiberCount_le T₂
  have hR : (3 : ℝ) * (n : ℝ)
      ≤ 2 * (xiSingletonFiberCount T₂ : ℝ) + (xiPosZeroCount T₂ : ℝ) := by
    have : 3 * n ≤ 2 * xiSingletonFiberCount T₂ + xiPosZeroCount T₂ := by omega
    exact_mod_cast this
  linarith

/-- Legacy negative-shift specialization of the singleton-fibre window inequality. -/
theorem xiSingletonFiberCount_ge_of_levinson_window_unconditional {lam : ℝ} (hlam0 : lam < 0)
    {d T₁ T₂ : ℝ} (hd : (1 / 2 : ℝ) < d) (h20 : 20 ≤ T₁) (hT : T₁ < T₂) {n : ℕ}
    (hbot : ∀ x ∈ uIcc (1 / 2 : ℝ) d, levinsonGEntire (lam : ℂ) ((x : ℂ) + T₁ * I) ≠ 0)
    (htop : ∀ x ∈ uIcc (1 / 2 : ℝ) d, levinsonGEntire (lam : ℂ) ((x : ℂ) + T₂ * I) ≠ 0)
    (hright : ∀ t ∈ uIcc T₁ T₂, levinsonGEntire (lam : ℂ) ((d : ℂ) + t * I) ≠ 0)
    (hbound : ∀ Z : Finset ℂ,
      (∀ z : ℂ, z ∈ Z ↔
        z ∈ (uIcc (1 / 2 : ℝ) d ×ℂ uIcc T₁ T₂) ∧ levinsonGEntire (lam : ℂ) z = 0) →
      ((n : ℝ) + 2) * Real.pi ≤
        (gammaHardyTheta T₂ - gammaHardyTheta T₁)
          + (∫ t in T₁..T₂, (logDeriv (levinsonGEntire (lam : ℂ)) ((d : ℂ) + t * I)).re)
          + (∫ x in (1 / 2 : ℝ)..d,
              (logDeriv (levinsonGEntire (lam : ℂ)) ((x : ℂ) + T₁ * I)).im)
          - (∫ x in (1 / 2 : ℝ)..d,
              (logDeriv (levinsonGEntire (lam : ℂ)) ((x : ℂ) + T₂ * I)).im)
          - 2 * Real.pi *
            (∑ w ∈ Z, ((analyticOrderAt (levinsonGEntire (lam : ℂ)) w).toNat : ℝ))) :
    (3 / 2 : ℝ) * (n : ℝ) - (xiPosZeroCount T₂ : ℝ) / 2
      ≤ (xiSingletonFiberCount T₂ : ℝ) := by
  have h1 := le_xiOddFiberCount_of_levinson_window_unconditional hlam0 hd h20 hT
    hbot htop hright hbound
  have h2 := three_mul_xiOddFiberCount_le T₂
  have hR : (3 : ℝ) * (n : ℝ)
      ≤ 2 * (xiSingletonFiberCount T₂ : ℝ) + (xiPosZeroCount T₂ : ℝ) := by
    have : 3 * n ≤ 2 * xiSingletonFiberCount T₂ + xiPosZeroCount T₂ := by omega
    exact_mod_cast this
  linarith

end RHTower

end
