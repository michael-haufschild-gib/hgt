import GaloisForLFunctions.HTGeometry.RungeSelection

/-!
# Runge approximation: the surviving edges are approximable

Each surviving grid edge lies in one selected square (so the source is analytic on it) and in one
non-selected square (so its poles can be pushed off `Ω` or to infinity).  Hence the contour integral
over a surviving edge is uniformly approximable on the tube around `K` by functions analytic and
differentially algebraic on `Ω`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set

noncomputable section

variable {Ω K : Set ℂ} {s R δ : ℝ} {S : Finset (ℤ × ℤ)} {F : ℂ → ℂ}

theorem approxOn_gridH (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω) (hΩne : Ω.Nonempty)
    (hΩinf : Ω.Infinite) (hK : IsCompact K) (hs : 0 < s) (hR : 0 < R)
    (h4s : 4 * s < δ) (h16s : 16 * s < R) (hKR : ∀ z ∈ K, ‖z‖ ≤ R / 8)
    (hΩtube : ∀ w : ℂ, (∃ z ∈ K, dist w z < δ) → w ∈ Ω)
    (hmemS : ∀ q : ℤ × ℤ, q ∈ S ↔ SelSquare s Ω R q) (hF : AnalyticOnNhd ℂ F Ω)
    {p : ℤ × ℤ} (hne : hCoeff S p ≠ 0) :
    ApproxOn (tubeAround K (2 * s)) (RungeDA Ω)
      (fun z => gridH (fun w => F w * (w - z)⁻¹) s p.1 p.2) := by
  classical
  set γ : ℝ → ℂ := fun x => (x : ℂ) + ((s * (p.2 : ℝ) : ℝ) : ℂ) * Complex.I with hγdef
  have hab : s * (p.1 : ℝ) ≤ s * ((p.1 : ℝ) + 1) := by nlinarith
  have hboth : ∀ x ∈ Set.Icc (s * (p.1 : ℝ)) (s * ((p.1 : ℝ) + 1)),
      γ x ∈ gridSquare s p.1 p.2 ∧ γ x ∈ gridSquare s p.1 (p.2 - 1) :=
    fun x hx => hEdgePoint_mem_squares hs p hx
  obtain ⟨pb, pg, hbad, hgood, hmemb, hmemg⟩ :
      ∃ pb pg : ℤ × ℤ, ¬ SelSquare s Ω R pb ∧ SelSquare s Ω R pg ∧
        (∀ x ∈ Set.Icc (s * (p.1 : ℝ)) (s * ((p.1 : ℝ) + 1)), γ x ∈ gridSquare s pb.1 pb.2) ∧
        (∀ x ∈ Set.Icc (s * (p.1 : ℝ)) (s * ((p.1 : ℝ) + 1)), γ x ∈ gridSquare s pg.1 pg.2) := by
    rcases exists_notSelSquare_of_hCoeff_ne hmemS hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨p, (p.1, p.2 - 1), h1, h2, fun x hx => (hboth x hx).1, fun x hx => (hboth x hx).2⟩
    · exact ⟨(p.1, p.2 - 1), p, h2, h1, fun x hx => (hboth x hx).2, fun x hx => (hboth x hx).1⟩
  have hpole : ∀ x ∈ Set.Icc (s * (p.1 : ℝ)) (s * ((p.1 : ℝ) + 1)),
      (∀ z ∈ tubeAround K (2 * s), γ x ≠ z) ∧
        ApproxOn (tubeAround K (2 * s)) (RungeDA Ω) (fun z => (z - γ x)⁻¹) := fun x hx =>
    approxOn_kernel_of_notSelSquare hΩo hΩc hΩne hΩinf hs hR h4s h16s hKR hΩtube hbad
      (hmemb x hx)
  have hedgeΩ : ∀ x ∈ Set.Icc (s * (p.1 : ℝ)) (s * ((p.1 : ℝ) + 1)), γ x ∈ Ω := fun x hx =>
    hgood.1 (hmemg x hx)
  have hFc : ContinuousOn F (γ '' Set.Icc (s * (p.1 : ℝ)) (s * ((p.1 : ℝ) + 1))) := by
    rintro w ⟨x, hx, rfl⟩
    exact ((hF _ (hedgeΩ x hx)).continuousAt).continuousWithinAt
  have hγc : ContinuousOn γ (Set.Icc (s * (p.1 : ℝ)) (s * ((p.1 : ℝ) + 1))) := by
    apply Continuous.continuousOn
    rw [hγdef]
    fun_prop
  have hmain := approxOn_edgeCauchyIntegral (Ω := Ω) (K := tubeAround K (2 * s))
    hΩo hΩc hΩne hΩinf (isCompact_tubeAround hK (2 * s)) hab hγc hFc
    (fun x hx z hz => (hpole x hx).1 z hz) (fun x hx => (hpole x hx).2)
  exact hmain

theorem approxOn_gridV (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω) (hΩne : Ω.Nonempty)
    (hΩinf : Ω.Infinite) (hK : IsCompact K) (hs : 0 < s) (hR : 0 < R)
    (h4s : 4 * s < δ) (h16s : 16 * s < R) (hKR : ∀ z ∈ K, ‖z‖ ≤ R / 8)
    (hΩtube : ∀ w : ℂ, (∃ z ∈ K, dist w z < δ) → w ∈ Ω)
    (hmemS : ∀ q : ℤ × ℤ, q ∈ S ↔ SelSquare s Ω R q) (hF : AnalyticOnNhd ℂ F Ω)
    {p : ℤ × ℤ} (hne : vCoeff S p ≠ 0) :
    ApproxOn (tubeAround K (2 * s)) (RungeDA Ω)
      (fun z => gridV (fun w => F w * (w - z)⁻¹) s p.1 p.2) := by
  classical
  set γ : ℝ → ℂ := fun t => ((s * (p.1 : ℝ) : ℝ) : ℂ) + (t : ℂ) * Complex.I with hγdef
  have hab : s * (p.2 : ℝ) ≤ s * ((p.2 : ℝ) + 1) := by nlinarith
  have hboth : ∀ t ∈ Set.Icc (s * (p.2 : ℝ)) (s * ((p.2 : ℝ) + 1)),
      γ t ∈ gridSquare s p.1 p.2 ∧ γ t ∈ gridSquare s (p.1 - 1) p.2 :=
    fun t ht => vEdgePoint_mem_squares hs p ht
  obtain ⟨pb, pg, hbad, hgood, hmemb, hmemg⟩ :
      ∃ pb pg : ℤ × ℤ, ¬ SelSquare s Ω R pb ∧ SelSquare s Ω R pg ∧
        (∀ t ∈ Set.Icc (s * (p.2 : ℝ)) (s * ((p.2 : ℝ) + 1)), γ t ∈ gridSquare s pb.1 pb.2) ∧
        (∀ t ∈ Set.Icc (s * (p.2 : ℝ)) (s * ((p.2 : ℝ) + 1)), γ t ∈ gridSquare s pg.1 pg.2) := by
    rcases exists_notSelSquare_of_vCoeff_ne hmemS hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨p, (p.1 - 1, p.2), h1, h2, fun t ht => (hboth t ht).1, fun t ht => (hboth t ht).2⟩
    · exact ⟨(p.1 - 1, p.2), p, h2, h1, fun t ht => (hboth t ht).2, fun t ht => (hboth t ht).1⟩
  have hpole : ∀ t ∈ Set.Icc (s * (p.2 : ℝ)) (s * ((p.2 : ℝ) + 1)),
      (∀ z ∈ tubeAround K (2 * s), γ t ≠ z) ∧
        ApproxOn (tubeAround K (2 * s)) (RungeDA Ω) (fun z => (z - γ t)⁻¹) := fun t ht =>
    approxOn_kernel_of_notSelSquare hΩo hΩc hΩne hΩinf hs hR h4s h16s hKR hΩtube hbad
      (hmemb t ht)
  have hedgeΩ : ∀ t ∈ Set.Icc (s * (p.2 : ℝ)) (s * ((p.2 : ℝ) + 1)), γ t ∈ Ω := fun t ht =>
    hgood.1 (hmemg t ht)
  have hFc : ContinuousOn F (γ '' Set.Icc (s * (p.2 : ℝ)) (s * ((p.2 : ℝ) + 1))) := by
    rintro w ⟨t, ht, rfl⟩
    exact ((hF _ (hedgeΩ t ht)).continuousAt).continuousWithinAt
  have hγc : ContinuousOn γ (Set.Icc (s * (p.2 : ℝ)) (s * ((p.2 : ℝ) + 1))) := by
    apply Continuous.continuousOn
    rw [hγdef]
    fun_prop
  have hmain := approxOn_edgeCauchyIntegral (Ω := Ω) (K := tubeAround K (2 * s))
    hΩo hΩc hΩne hΩinf (isCompact_tubeAround hK (2 * s)) hab hγc hFc
    (fun t ht z hz => (hpole t ht).1 z hz) (fun t ht => (hpole t ht).2)
  have hfun : (fun z => gridV (fun w => F w * (w - z)⁻¹) s p.1 p.2)
      = fun z => Complex.I * edgeCauchyIntegral F γ (s * (p.2 : ℝ)) (s * ((p.2 : ℝ) + 1)) z := by
    funext z
    rfl
  rw [hfun]
  exact approxOn_smul (rungeDA_smul hΩo hΩc hΩne hΩinf) Complex.I hmain


/-! ## The contour functional -/

/-- The signed sum of the surviving edge integrals. -/
def contourFunctional (F : ℂ → ℂ) (s : ℝ) (S : Finset (ℤ × ℤ)) (z : ℂ) : ℂ :=
  (∑ p ∈ S ∪ S.image shiftUp, hCoeff S p * gridH (fun w => F w * (w - z)⁻¹) s p.1 p.2)
    + ∑ p ∈ S ∪ S.image shiftRight, vCoeff S p * gridV (fun w => F w * (w - z)⁻¹) s p.1 p.2

theorem approxOn_contourFunctional (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω) (hΩne : Ω.Nonempty)
    (hΩinf : Ω.Infinite) (hK : IsCompact K) (hs : 0 < s) (hR : 0 < R)
    (h4s : 4 * s < δ) (h16s : 16 * s < R) (hKR : ∀ z ∈ K, ‖z‖ ≤ R / 8)
    (hΩtube : ∀ w : ℂ, (∃ z ∈ K, dist w z < δ) → w ∈ Ω)
    (hmemS : ∀ q : ℤ × ℤ, q ∈ S ↔ SelSquare s Ω R q) (hF : AnalyticOnNhd ℂ F Ω) :
    ApproxOn (tubeAround K (2 * s)) (RungeDA Ω) (contourFunctional F s S) := by
  classical
  have hHterm : ∀ p ∈ S ∪ S.image shiftUp,
      ApproxOn (tubeAround K (2 * s)) (RungeDA Ω)
        (fun z => hCoeff S p * gridH (fun w => F w * (w - z)⁻¹) s p.1 p.2) := by
    intro p _
    by_cases hc : hCoeff S p = 0
    · have hfun : (fun z => hCoeff S p * gridH (fun w => F w * (w - z)⁻¹) s p.1 p.2)
          = fun _ : ℂ => (0 : ℂ) := by
        funext z
        rw [hc, zero_mul]
      rw [hfun]
      exact approxOn_of_mem rungeDA_zero
    · exact approxOn_smul (rungeDA_smul hΩo hΩc hΩne hΩinf) _
        (approxOn_gridH hΩo hΩc hΩne hΩinf hK hs hR h4s h16s hKR hΩtube hmemS hF hc)
  have hVterm : ∀ p ∈ S ∪ S.image shiftRight,
      ApproxOn (tubeAround K (2 * s)) (RungeDA Ω)
        (fun z => vCoeff S p * gridV (fun w => F w * (w - z)⁻¹) s p.1 p.2) := by
    intro p _
    by_cases hc : vCoeff S p = 0
    · have hfun : (fun z => vCoeff S p * gridV (fun w => F w * (w - z)⁻¹) s p.1 p.2)
          = fun _ : ℂ => (0 : ℂ) := by
        funext z
        rw [hc, zero_mul]
      rw [hfun]
      exact approxOn_of_mem rungeDA_zero
    · exact approxOn_smul (rungeDA_smul hΩo hΩc hΩne hΩinf) _
        (approxOn_gridV hΩo hΩc hΩne hΩinf hK hs hR h4s h16s hKR hΩtube hmemS hF hc)
  have hH := approxOn_finsetSum (K := tubeAround K (2 * s)) (C := RungeDA Ω) rungeDA_zero
    (rungeDA_add hΩo hΩc hΩne hΩinf) (S ∪ S.image shiftUp) hHterm
  have hV := approxOn_finsetSum (K := tubeAround K (2 * s)) (C := RungeDA Ω) rungeDA_zero
    (rungeDA_add hΩo hΩc hΩne hΩinf) (S ∪ S.image shiftRight) hVterm
  exact approxOn_add (rungeDA_add hΩo hΩc hΩne hΩinf) hH hV

theorem contourFunctional_eq (hF : AnalyticOnNhd ℂ F Ω) (hs : 0 < s)
    (hSsub : ∀ p ∈ S, gridSquare s p.1 p.2 ⊆ Ω) {z : ℂ}
    (hzre : ∀ k : ℤ, z.re ≠ s * k) (hzim : ∀ k : ℤ, z.im ≠ s * k)
    (hmemS : (⌊z.re / s⌋, ⌊z.im / s⌋) ∈ S) :
    contourFunctional F s S z = 2 * Real.pi * Complex.I * F z := by
  rw [contourFunctional, ← sum_gridRect_eq_edges]
  exact sum_gridRect_cauchyKernel hF hs hSsub hzre hzim hmemS


/-! ## Runge approximation -/

private theorem floor_grid_le {s x : ℝ} (hs : 0 < s) :
    s * ((⌊x / s⌋ : ℤ) : ℝ) ≤ x ∧ x < s * (((⌊x / s⌋ : ℤ) : ℝ) + 1) := by
  have hfl : ((⌊x / s⌋ : ℤ) : ℝ) ≤ x / s := Int.floor_le (x / s)
  have hfu : x / s < ((⌊x / s⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one (x / s)
  have hkey : s * (x / s) = x := by field_simp
  constructor
  · calc s * ((⌊x / s⌋ : ℤ) : ℝ) ≤ s * (x / s) := by nlinarith
      _ = x := hkey
  · calc x = s * (x / s) := hkey.symm
      _ < s * (((⌊x / s⌋ : ℤ) : ℝ) + 1) := by nlinarith

/-- **Runge approximation.**  Every function analytic on a domain is uniformly approximable on
every compact subset by functions that are analytic *and differentially algebraic* on the whole
domain. -/
theorem approxOn_rungeDA_of_analyticOnNhd (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hΩne : Ω.Nonempty) (hΩinf : Ω.Infinite) (hF : AnalyticOnNhd ℂ F Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ApproxOn K (RungeDA Ω) F := by
  classical
  obtain ⟨s, R, δ, S, hs, hR, hδ, h4s, h16s, hKR, hΩtube, hmemS, hSel⟩ :=
    exists_rungeSelection hΩo hK hKΩ
  have hSsub : ∀ p ∈ S, gridSquare s p.1 p.2 ⊆ Ω := fun p hp => ((hmemS p).1 hp).1
  set c : ℂ := (2 * Real.pi * Complex.I)⁻¹ with hcdef
  set Φ : ℂ → ℂ := fun z => c * contourFunctional F s S z with hΦdef
  have hΦapprox : ApproxOn (tubeAround K (2 * s)) (RungeDA Ω) Φ :=
    approxOn_smul (rungeDA_smul hΩo hΩc hΩne hΩinf) c
      (approxOn_contourFunctional hΩo hΩc hΩne hΩinf hK hs hR h4s h16s hKR hΩtube hmemS hF)
  have hcne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hΦeq : ∀ w : ℂ, (∀ k : ℤ, w.re ≠ s * k) → (∀ k : ℤ, w.im ≠ s * k) →
      (⌊w.re / s⌋, ⌊w.im / s⌋) ∈ S → Φ w = F w := by
    intro w h1 h2 h3
    have := contourFunctional_eq hF hs hSsub h1 h2 h3
    rw [hΦdef]
    simp only []
    rw [this, hcdef]
    field_simp
  intro ε hε
  obtain ⟨G, hGmem, hG⟩ := hΦapprox ε hε
  refine ⟨G, hGmem, fun z hz => ?_⟩
  set m : ℤ := ⌊z.re / s⌋ with hmdef
  set n : ℤ := ⌊z.im / s⌋ with hndef
  obtain ⟨hre₁, hre₂⟩ := floor_grid_le (x := z.re) hs
  obtain ⟨him₁, him₂⟩ := floor_grid_le (x := z.im) hs
  have hzsq : z ∈ gridSquare s m n :=
    mem_gridSquare.2 ⟨⟨hre₁, hre₂.le⟩, ⟨him₁, him₂.le⟩⟩
  have hmn : (m, n) ∈ S := hSel (m, n) ⟨z, hzsq, hz⟩
  -- an approach sequence strictly inside the square of `z`
  set u : ℕ → ℂ := fun j =>
    ((z.re + (s * ((m : ℝ) + 1) - z.re) / ((j : ℝ) + 2) : ℝ) : ℂ) +
      ((z.im + (s * ((n : ℝ) + 1) - z.im) / ((j : ℝ) + 2) : ℝ) : ℂ) * Complex.I with hudef
  have hj2 : ∀ j : ℕ, (2 : ℝ) ≤ (j : ℝ) + 2 := by
    intro j
    have : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hure : ∀ j, (u j).re = z.re + (s * ((m : ℝ) + 1) - z.re) / ((j : ℝ) + 2) :=
    fun j => cornerPt_re _ _
  have huim : ∀ j, (u j).im = z.im + (s * ((n : ℝ) + 1) - z.im) / ((j : ℝ) + 2) :=
    fun j => cornerPt_im _ _
  have hposre : ∀ j : ℕ, 0 < (s * ((m : ℝ) + 1) - z.re) / ((j : ℝ) + 2) := by
    intro j
    have h1 : 0 < s * ((m : ℝ) + 1) - z.re := by linarith
    have h2 : (0:ℝ) < (j : ℝ) + 2 := by linarith [hj2 j]
    positivity
  have hposim : ∀ j : ℕ, 0 < (s * ((n : ℝ) + 1) - z.im) / ((j : ℝ) + 2) := by
    intro j
    have h1 : 0 < s * ((n : ℝ) + 1) - z.im := by linarith
    have h2 : (0:ℝ) < (j : ℝ) + 2 := by linarith [hj2 j]
    positivity
  have hlere : ∀ j : ℕ, (s * ((m : ℝ) + 1) - z.re) / ((j : ℝ) + 2) ≤ s / 2 := by
    intro j
    have h1 : s * ((m : ℝ) + 1) - z.re ≤ s := by nlinarith
    have h2 : (0:ℝ) < (j : ℝ) + 2 := by linarith [hj2 j]
    rw [div_le_iff₀ h2]
    nlinarith [hj2 j, hs]
  have hleim : ∀ j : ℕ, (s * ((n : ℝ) + 1) - z.im) / ((j : ℝ) + 2) ≤ s / 2 := by
    intro j
    have h1 : s * ((n : ℝ) + 1) - z.im ≤ s := by nlinarith
    have h2 : (0:ℝ) < (j : ℝ) + 2 := by linarith [hj2 j]
    rw [div_le_iff₀ h2]
    nlinarith [hj2 j, hs]
  have hbox : ∀ j : ℕ, s * (m : ℝ) < (u j).re ∧ (u j).re < s * ((m : ℝ) + 1) ∧
      s * (n : ℝ) < (u j).im ∧ (u j).im < s * ((n : ℝ) + 1) := by
    intro j
    have h2 : (0:ℝ) < (j : ℝ) + 2 := by linarith [hj2 j]
    have hre' : (s * ((m : ℝ) + 1) - z.re) / ((j : ℝ) + 2) < s * ((m : ℝ) + 1) - z.re := by
      rw [div_lt_iff₀ h2]
      nlinarith [hj2 j, hposre j]
    have him' : (s * ((n : ℝ) + 1) - z.im) / ((j : ℝ) + 2) < s * ((n : ℝ) + 1) - z.im := by
      rw [div_lt_iff₀ h2]
      nlinarith [hj2 j, hposim j]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hure j]; linarith [hposre j]
    · rw [hure j]; linarith
    · rw [huim j]; linarith [hposim j]
    · rw [huim j]; linarith
  have hfloor : ∀ j : ℕ, (⌊(u j).re / s⌋, ⌊(u j).im / s⌋) = (m, n) := by
    intro j
    obtain ⟨b1, b2, b3, b4⟩ := hbox j
    have hm : ⌊(u j).re / s⌋ = m := by
      rw [Int.floor_eq_iff]
      constructor
      · rw [le_div_iff₀ hs]; nlinarith
      · rw [div_lt_iff₀ hs]; nlinarith
    have hn : ⌊(u j).im / s⌋ = n := by
      rw [Int.floor_eq_iff]
      constructor
      · rw [le_div_iff₀ hs]; nlinarith
      · rw [div_lt_iff₀ hs]; nlinarith
    rw [hm, hn]
  have hoffre : ∀ (j : ℕ) (k : ℤ), (u j).re ≠ s * k := by
    intro j k hcon
    obtain ⟨b1, b2, _, _⟩ := hbox j
    rw [hcon] at b1 b2
    have hkm : (m : ℝ) < (k : ℝ) := by nlinarith
    have hkm2 : (k : ℝ) < (m : ℝ) + 1 := by nlinarith
    have h1 : m < k := by exact_mod_cast hkm
    have h2 : k < m + 1 := by exact_mod_cast hkm2
    omega
  have hoffim : ∀ (j : ℕ) (k : ℤ), (u j).im ≠ s * k := by
    intro j k hcon
    obtain ⟨_, _, b3, b4⟩ := hbox j
    rw [hcon] at b3 b4
    have hkm : (n : ℝ) < (k : ℝ) := by nlinarith
    have hkm2 : (k : ℝ) < (n : ℝ) + 1 := by nlinarith
    have h1 : n < k := by exact_mod_cast hkm
    have h2 : k < n + 1 := by exact_mod_cast hkm2
    omega
  have hutube : ∀ j : ℕ, u j ∈ tubeAround K (2 * s) := by
    intro j
    refine mem_tubeAround.2 ⟨z, hz, ?_⟩
    have hd : dist (u j) z ≤ |(u j).re - z.re| + |(u j).im - z.im| := by
      rw [dist_eq_norm]
      have := Complex.norm_le_abs_re_add_abs_im (u j - z)
      simpa [Complex.sub_re, Complex.sub_im] using this
    have h1 : |(u j).re - z.re| ≤ s / 2 := by
      rw [hure j]
      rw [abs_of_nonneg (by linarith [hposre j] : (0:ℝ) ≤ z.re +
        (s * ((m : ℝ) + 1) - z.re) / ((j : ℝ) + 2) - z.re)]
      linarith [hlere j]
    have h2 : |(u j).im - z.im| ≤ s / 2 := by
      rw [huim j]
      rw [abs_of_nonneg (by linarith [hposim j] : (0:ℝ) ≤ z.im +
        (s * ((n : ℝ) + 1) - z.im) / ((j : ℝ) + 2) - z.im)]
      linarith [hleim j]
    linarith
  have hbound : ∀ j : ℕ, ‖F (u j) - G (u j)‖ ≤ ε := by
    intro j
    have h1 : Φ (u j) = F (u j) := by
      refine hΦeq (u j) (hoffre j) (hoffim j) ?_
      rw [hfloor j]
      exact hmn
    have h2 := hG (u j) (hutube j)
    rwa [h1] at h2
  -- pass to the limit
  have hutend : Filter.Tendsto u Filter.atTop (nhds z) := by
    have hre : Filter.Tendsto (fun j : ℕ => (s * ((m : ℝ) + 1) - z.re) / ((j : ℝ) + 2))
        Filter.atTop (nhds 0) := by
      have h := tendsto_natCast_atTop_atTop (R := ℝ)
      have h2 : Filter.Tendsto (fun j : ℕ => (j : ℝ) + 2) Filter.atTop Filter.atTop :=
        h.atTop_add tendsto_const_nhds
      simpa using h2.const_div_atTop (s * ((m : ℝ) + 1) - z.re)
    have him : Filter.Tendsto (fun j : ℕ => (s * ((n : ℝ) + 1) - z.im) / ((j : ℝ) + 2))
        Filter.atTop (nhds 0) := by
      have h := tendsto_natCast_atTop_atTop (R := ℝ)
      have h2 : Filter.Tendsto (fun j : ℕ => (j : ℝ) + 2) Filter.atTop Filter.atTop :=
        h.atTop_add tendsto_const_nhds
      simpa using h2.const_div_atTop (s * ((n : ℝ) + 1) - z.im)
    have hC1 : Filter.Tendsto
        (fun j : ℕ => ((z.re + (s * ((m : ℝ) + 1) - z.re) / ((j : ℝ) + 2) : ℝ) : ℂ))
        Filter.atTop (nhds ((z.re : ℝ) : ℂ)) := by
      have hRe : Filter.Tendsto
          (fun j : ℕ => z.re + (s * ((m : ℝ) + 1) - z.re) / ((j : ℝ) + 2))
          Filter.atTop (nhds (z.re + 0)) := tendsto_const_nhds.add hre
      rw [add_zero] at hRe
      exact (Complex.continuous_ofReal.tendsto (z.re)).comp hRe
    have hC2 : Filter.Tendsto
        (fun j : ℕ => ((z.im + (s * ((n : ℝ) + 1) - z.im) / ((j : ℝ) + 2) : ℝ) : ℂ))
        Filter.atTop (nhds ((z.im : ℝ) : ℂ)) := by
      have hIm : Filter.Tendsto
          (fun j : ℕ => z.im + (s * ((n : ℝ) + 1) - z.im) / ((j : ℝ) + 2))
          Filter.atTop (nhds (z.im + 0)) := tendsto_const_nhds.add him
      rw [add_zero] at hIm
      exact (Complex.continuous_ofReal.tendsto (z.im)).comp hIm
    have hmul : Filter.Tendsto
        (fun j : ℕ => ((z.im + (s * ((n : ℝ) + 1) - z.im) / ((j : ℝ) + 2) : ℝ) : ℂ) * Complex.I)
        Filter.atTop (nhds (((z.im : ℝ) : ℂ) * Complex.I)) :=
      hC2.mul (tendsto_const_nhds (x := Complex.I))
    have hsum := hC1.add hmul
    rw [hudef]
    simpa [Complex.re_add_im] using hsum
  have hFcont : ContinuousAt F z := (hF z (hKΩ hz)).continuousAt
  have hGcont : ContinuousAt G z := (hGmem.1 z (hKΩ hz)).continuousAt
  have hlim : Filter.Tendsto (fun j : ℕ => ‖F (u j) - G (u j)‖) Filter.atTop
      (nhds ‖F z - G z‖) := by
    have h1 := hFcont.tendsto.comp hutend
    have h2 := hGcont.tendsto.comp hutend
    exact (h1.sub h2).norm
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hbound)

end

end GaloisForLFunctions.HTGeometry
