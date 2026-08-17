import GaloisForLFunctions.RHTower.Sieve.ChebyshevTwistRouteTBound

/-!
# The twisted Route-T bound, graded by abscissa

The seven pieces of the twisted contour do not all live at the same abscissa.  The left vertical
edges sit on the Route-T line `σ`, where the cutoff's Mellin transform is *already* damped by
`(N+H)^{-w}`; the truncation tail and the two horizontal edges sit on the Perron line `d > 1`, where
it is not.  Reading a single decay constant at `d` and using it on the left edge throws away exactly
the saving the contour was moved to obtain, so the constant is carried as a function of the
abscissa:

```text
‖2π ∑ₙ Λ(n) n^{-iτ} w(n)‖ ≤ 2·Σ(d)·C(d)/T
                            + ((|τ|-T)⁻¹ + C'·log K/w(K+1))
                              · (2(N+H)^σ/σ + 2C(σ) + 2C(d)(d-σ)/T²),
```

`K = |τ| + T`, `σ` the Route-T abscissa at `K`.  With the balanced smoothing width the two competing
exponents are `C(σ) ≍ (N+H)^σ·(N/H)²` against `(N+H)^σ = (N+H)·(N+H)^{-w}`, and the contour saves
precisely when `w·log N` beats `2 log(N/H)`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- **The twisted Route-T bound with the Mellin constant graded by abscissa.**  The left edge is
read at the contour abscissa, where the cutoff's transform is already small; the tail and the
horizontal edges are read at the Perron abscissa.  Using one constant for all of them would throw
away exactly the saving the contour was moved to obtain. -/
theorem exists_norm_tsum_vonMangoldtTwist_routeT_graded :
    ∃ A Creg delta K₀ : ℝ, 0 < Creg ∧ 0 < delta ∧ 3 ≤ K₀ ∧
      ∀ (N H d T τ : ℝ) (Cfun : ℝ → ℝ), 0 < N → 0 < H → 1 < d → d ≤ 9 / 8 → 1 ≤ T → T < |τ| →
        K₀ ≤ |τ| + T →
        (∀ σ' : ℝ, σ' ≤ d → ∀ s : ℂ, 0 < s.re → s.re ≤ σ' →
          |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ Cfun σ') →
        ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
            vonMangoldtTwist τ n * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
          ≤ 2 * ((∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d)) * Cfun d) / T
            + (((|τ| - T)⁻¹ * Cfun d / T ^ 2
                    * (d - routeTTwistAbscissa A delta (|τ| + T))
                  + (|τ| - T)⁻¹ * Cfun d / T ^ 2
                    * (d - routeTTwistAbscissa A delta (|τ| + T))
                  + (|τ| - T)⁻¹
                    * (2 * ((N + H) ^ routeTTwistAbscissa A delta (|τ| + T)
                        / routeTTwistAbscissa A delta (|τ| + T)) + 2 * Cfun (routeTTwistAbscissa A delta (|τ| + T))))
              + ((Creg * Real.log (|τ| + T) / routeTZeroFreeWidth A (|τ| + T + 1))
                    * Cfun d / T ^ 2 * (d - routeTTwistAbscissa A delta (|τ| + T))
                  + (Creg * Real.log (|τ| + T) / routeTZeroFreeWidth A (|τ| + T + 1))
                    * Cfun d / T ^ 2 * (d - routeTTwistAbscissa A delta (|τ| + T))
                  + (Creg * Real.log (|τ| + T) / routeTZeroFreeWidth A (|τ| + T + 1))
                    * (2 * ((N + H) ^ routeTTwistAbscissa A delta (|τ| + T)
                        / routeTTwistAbscissa A delta (|τ| + T)) + 2 * Cfun (routeTTwistAbscissa A delta (|τ| + T))))) := by
  obtain ⟨A, Creg, delta, K₀, hCreg, hdelta, hK₀, hzfstrip, hsize⟩ :=
    exists_bound_zetaLogDerivReg_routeT_uniform
  refine ⟨A, Creg, delta, K₀, hCreg, hdelta, hK₀, ?_⟩
  intro N H d T τ Cfun hN hH hd hd98 hT hτ hK hbd
  have hpow : ∀ z : ℝ, z ^ (1 + 1) = z ^ 2 := fun z => by norm_num
  set K : ℝ := |τ| + T with hKdef
  set c : ℝ := routeTTwistAbscissa A delta K with hcdef
  have hcval : c = 1 - routeTUniformRegWidth A delta K := routeTTwistAbscissa_eq A delta K
  have hc0 : 0 < c := routeTTwistAbscissa_pos A delta K
  have hc1 : c < 1 := routeTTwistAbscissa_lt_one hdelta
  have hcd : c ≤ d := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hTabs : |T| = T := abs_of_pos hT0
  have hnegTabs : |(-T)| = T := by rw [abs_neg, hTabs]
  have hτ0 : (0 : ℝ) < |τ| - T := by linarith
  have hK3 : (3 : ℝ) ≤ K := le_trans hK₀ hK
  have hbdc : ∀ s : ℂ, 0 < s.re → s.re ≤ c →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ Cfun c :=
    fun s h1 h2 => hbd c hcd s h1 h2
  have hbdd : ∀ s : ℂ, 0 < s.re → s.re ≤ d →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ Cfun d :=
    fun s h1 h2 => hbd d le_rfl s h1 h2
  set Mreg : ℝ := Creg * Real.log K / routeTZeroFreeWidth A (K + 1) with hMregdef
  have hMreg0 : 0 ≤ Mreg := by
    have hlog : (0 : ℝ) ≤ Real.log K := Real.log_nonneg (by linarith)
    have hw : (0 : ℝ) < routeTZeroFreeWidth A (K + 1) := routeTZeroFreeWidth_pos A _
    rw [hMregdef]
    positivity
  -- every point of the shifted rectangle sits inside the Route-T strip and misses the pole
  have hedge : ∀ u : ℝ, |u| ≤ T → ∀ x : ℝ, c ≤ x → x ≤ d →
      ((x : ℂ) + (u : ℝ) * Complex.I + (τ : ℂ) * Complex.I) ≠ 1 ∧
      riemannZeta ((x : ℂ) + (u : ℝ) * Complex.I + (τ : ℂ) * Complex.I) ≠ 0 ∧
      ‖zetaLogDerivReg ((x : ℂ) + (u : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mreg := by
    intro u hu x hx hxd
    have hre : ((x : ℂ) + (u : ℝ) * Complex.I + (τ : ℂ) * Complex.I).re = x := by simp
    have him : ((x : ℂ) + (u : ℝ) * Complex.I + (τ : ℂ) * Complex.I).im = u + τ := by simp
    have himK : |((x : ℂ) + (u : ℝ) * Complex.I + (τ : ℂ) * Complex.I).im| ≤ K := by
      rw [him, hKdef]
      have h1 : |u + τ| ≤ |u| + |τ| := abs_add_le _ _
      linarith
    have hlow : 1 - routeTUniformRegWidth A delta K
        ≤ ((x : ℂ) + (u : ℝ) * Complex.I + (τ : ℂ) * Complex.I).re := by
      rw [hre, ← hcval]
      exact hx
    have hne1 : ((x : ℂ) + (u : ℝ) * Complex.I + (τ : ℂ) * Complex.I) ≠ 1 := by
      intro h
      have him0 := congrArg Complex.im h
      rw [him, Complex.one_im] at him0
      have habs : |τ| = |u| := by
        have hτu : τ = -u := by linarith
        rw [hτu, abs_neg]
      linarith
    exact ⟨hne1, hzfstrip _ K hK himK hlow hne1,
      hsize _ K hK himK hlow (by rw [hre]; linarith)⟩
  -- the truncation tail
  have htail := norm_truncation_error_chebyshev_twist (N := N) (H := H) (C := Cfun d) hN hH τ hd hT hbdd
  -- the pole factor
  have hpoleleft := norm_integral_left_vertical_twistPoleInv_le (N := N) (H := H) (C := Cfun c)
    (τ := τ) hN hH hc0 hT hτ hbdc
  have hpoletop := norm_horizontal_edge_twistPoleInv_le (N := N) (H := H) 1 (c := c) (d := d)
    (T := T) (C := Cfun d) (τ := τ) hc0 hcd (by linarith) (by rw [hTabs]; exact hτ) hbdd
  have hpolebot := norm_horizontal_edge_twistPoleInv_le (N := N) (H := H) 1 (c := c) (d := d)
    (T := -T) (C := Cfun d) (τ := τ) hc0 hcd (by linarith) (by rw [hnegTabs]; exact hτ) hbdd
  rw [hTabs, hpow] at hpoletop
  rw [hnegTabs, hpow] at hpolebot
  have hpole := norm_integral_twistPoleInvW_truncated_le hH hc0 hcd hT0.le hτ
    hpoletop hpolebot hpoleleft
  -- the regular part
  have hzu : ∀ y ∈ Set.uIcc (-T) T,
      zetaResidueUnit ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I) ≠ 0 := by
    intro y hy
    rw [Set.uIcc_of_le (by linarith : (-T : ℝ) ≤ T)] at hy
    obtain ⟨hne1, hz, _⟩ := hedge y (abs_le.2 ⟨hy.1, hy.2⟩) c (le_refl c) hcd
    exact (zetaResidueUnit_ne_zero_iff hne1).2 hz
  have hregleft := norm_integral_left_vertical_zetaLogDerivRegTwist_le (N := N) (H := H)
    (C := Cfun c) (M := Mreg) (τ := τ) hN hH hc0 hT hMreg0 hbdc hzu
    (fun y hy => (hedge y (abs_le.2 ⟨hy.1, hy.2⟩) c (le_refl c) hcd).2.2)
  have hregtop := norm_horizontal_edge_zetaLogDerivRegTwist_le (N := N) (H := H) 1 (c := c)
    (d := d) (T := T) (M := Mreg) (C := Cfun d) (τ := τ) hc0 hcd (by linarith) hMreg0 hbdd
    (fun x hx => (hedge T (by rw [hTabs]) x hx.1.le hx.2).2.2)
  have hregbot := norm_horizontal_edge_zetaLogDerivRegTwist_le (N := N) (H := H) 1 (c := c)
    (d := d) (T := -T) (M := Mreg) (C := Cfun d) (τ := τ) hc0 hcd (by linarith) hMreg0 hbdd
    (fun x hx => (hedge (-T) (by rw [hnegTabs]) x hx.1.le hx.2).2.2)
  rw [hTabs, hpow] at hregtop
  rw [hnegTabs, hpow] at hregbot
  have hzfrect : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-(|τ| + T)) (|τ| + T),
      s ≠ 1 → riemannZeta s ≠ 0 := by
    intro s hs hs1
    rw [Complex.mem_reProdIm, Set.uIcc_of_le hcd,
      Set.uIcc_of_le (by linarith [abs_nonneg τ] : -(|τ| + T) ≤ |τ| + T)] at hs
    have himK : |s.im| ≤ K := by
      rw [hKdef]
      exact abs_le.2 ⟨hs.2.1, hs.2.2⟩
    have hlow : 1 - routeTUniformRegWidth A delta K ≤ s.re := by
      rw [← hcval]
      exact hs.1.1
    exact hzfstrip s K hK himK hlow hs1
  have hreg := norm_integral_zetaLogDerivRegTwist_truncated_le hH τ hc0 hcd hT0.le hzfrect
    hregtop hregbot hregleft
  have hfinal := norm_tsum_vonMangoldtTwist_le_of_split_two τ hN hH hd htail hpole hreg
  linarith

end RHTower.Sieve
