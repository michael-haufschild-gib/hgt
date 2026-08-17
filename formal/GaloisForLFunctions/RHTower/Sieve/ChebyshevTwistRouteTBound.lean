import GaloisForLFunctions.RHTower.Sieve.ChebyshevTwistQuantitativeEdges
import GaloisForLFunctions.RHTower.Sieve.ChebyshevTwistShiftedBound
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegRouteTUniform

/-!
# The twisted Chebyshev sum on the Route-T contour

Above the truncation height the twisted sum has no main term, and every one of its seven pieces is
explicit: the truncation tail, and the left and two horizontal edges of each of the pole factor and
the regular part.  The abscissa is the Route-T one at the parameter `|τ| + T`, which is the largest
height the shifted rectangle reaches.

```text
‖2π ∑ₙ Λ(n) n^{-iτ} w(n)‖  ≤  2·Σ(d)·C/T
                             + (|τ|-T)⁻¹ · (edge mass)
                             + C'·log(|τ|+T)/w(|τ|+T+1) · (edge mass),
```

with `edge mass = 2(N+H)^σ/σ + 2C + 2C(d-σ)/T²` at the Route-T abscissa `σ`.  The pole contributes
a factor that *improves* as the twist grows; the regular part contributes the reciprocal zero-free
width, and the saving `(N+H)^σ = (N+H)·(N+H)^{-w}` is bought by the width itself.

The rectangle misses the pole for a reason that has nothing to do with the abscissa: its centre is
the twist, and `T < |τ|` puts height `0` outside it.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- The Route-T contour abscissa at parameter `K`. -/
noncomputable def routeTTwistAbscissa (A delta K : ℝ) : ℝ :=
  1 - routeTUniformRegWidth A delta K

theorem routeTTwistAbscissa_eq (A delta K : ℝ) :
    routeTTwistAbscissa A delta K = 1 - routeTUniformRegWidth A delta K := rfl

theorem routeTTwistAbscissa_lt_one {A delta K : ℝ} (hdelta : 0 < delta) :
    routeTTwistAbscissa A delta K < 1 := by
  unfold routeTTwistAbscissa
  linarith [routeTUniformRegWidth_pos (A := A) (K := K) hdelta]

theorem routeTTwistAbscissa_pos (A delta K : ℝ) :
    0 < routeTTwistAbscissa A delta K := by
  unfold routeTTwistAbscissa
  have h1 := routeTUniformRegWidth_le_half (A := A) (delta := delta) (K := K)
  have h2 := routeTZeroFreeWidth_le_one_sixtieth A (K + 1)
  linarith

/-- **The twisted smoothed Chebyshev sum on the Route-T contour, above the truncation height.** -/
theorem exists_norm_tsum_vonMangoldtTwist_routeT_le :
    ∃ A Creg delta K₀ : ℝ, 0 < Creg ∧ 0 < delta ∧ 3 ≤ K₀ ∧
      ∀ (N H d T τ C : ℝ), 0 < N → 0 < H → 1 < d → d ≤ 9 / 8 → 1 ≤ T → T < |τ| →
        K₀ ≤ |τ| + T →
        (∀ s : ℂ, 0 < s.re → s.re ≤ d →
          |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C) →
        ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
            vonMangoldtTwist τ n * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
          ≤ 2 * ((∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d)) * C) / T
            + (((|τ| - T)⁻¹ * C / T ^ 2
                    * (d - routeTTwistAbscissa A delta (|τ| + T))
                  + (|τ| - T)⁻¹ * C / T ^ 2
                    * (d - routeTTwistAbscissa A delta (|τ| + T))
                  + (|τ| - T)⁻¹
                    * (2 * ((N + H) ^ routeTTwistAbscissa A delta (|τ| + T)
                        / routeTTwistAbscissa A delta (|τ| + T)) + 2 * C))
              + ((Creg * Real.log (|τ| + T) / routeTZeroFreeWidth A (|τ| + T + 1))
                    * C / T ^ 2 * (d - routeTTwistAbscissa A delta (|τ| + T))
                  + (Creg * Real.log (|τ| + T) / routeTZeroFreeWidth A (|τ| + T + 1))
                    * C / T ^ 2 * (d - routeTTwistAbscissa A delta (|τ| + T))
                  + (Creg * Real.log (|τ| + T) / routeTZeroFreeWidth A (|τ| + T + 1))
                    * (2 * ((N + H) ^ routeTTwistAbscissa A delta (|τ| + T)
                        / routeTTwistAbscissa A delta (|τ| + T)) + 2 * C))) := by
  obtain ⟨A, Creg, delta, K₀, hCreg, hdelta, hK₀, hzfstrip, hsize⟩ :=
    exists_bound_zetaLogDerivReg_routeT_uniform
  refine ⟨A, Creg, delta, K₀, hCreg, hdelta, hK₀, ?_⟩
  intro N H d T τ C hN hH hd hd98 hT hτ hK hbd
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
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C :=
    fun s h1 h2 => hbd s h1 (le_trans h2 hcd)
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
  have htail := norm_truncation_error_chebyshev_twist (N := N) (H := H) (C := C) hN hH τ hd hT hbd
  -- the pole factor
  have hpoleleft := norm_integral_left_vertical_twistPoleInv_le (N := N) (H := H) (C := C)
    (τ := τ) hN hH hc0 hT hτ hbdc
  have hpoletop := norm_horizontal_edge_twistPoleInv_le (N := N) (H := H) 1 (c := c) (d := d)
    (T := T) (C := C) (τ := τ) hc0 hcd (by linarith) (by rw [hTabs]; exact hτ) hbd
  have hpolebot := norm_horizontal_edge_twistPoleInv_le (N := N) (H := H) 1 (c := c) (d := d)
    (T := -T) (C := C) (τ := τ) hc0 hcd (by linarith) (by rw [hnegTabs]; exact hτ) hbd
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
    (C := C) (M := Mreg) (τ := τ) hN hH hc0 hT hMreg0 hbdc hzu
    (fun y hy => (hedge y (abs_le.2 ⟨hy.1, hy.2⟩) c (le_refl c) hcd).2.2)
  have hregtop := norm_horizontal_edge_zetaLogDerivRegTwist_le (N := N) (H := H) 1 (c := c)
    (d := d) (T := T) (M := Mreg) (C := C) (τ := τ) hc0 hcd (by linarith) hMreg0 hbd
    (fun x hx => (hedge T (by rw [hTabs]) x hx.1.le hx.2).2.2)
  have hregbot := norm_horizontal_edge_zetaLogDerivRegTwist_le (N := N) (H := H) 1 (c := c)
    (d := d) (T := -T) (M := Mreg) (C := C) (τ := τ) hc0 hcd (by linarith) hMreg0 hbd
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
