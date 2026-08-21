import GaloisForLFunctions.HTGeometry.CauchyPompeiu

/-!
# The logarithmic cutoff has energy `4π / log ε⁻¹`

Lemma 6.6 (3) of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of the
Laplacian* (arXiv:2509.06151v2), builds the test functions that produce the upper bound
`λ_k(s) ≤ K/log|s|⁻¹` of Proposition 6.1.  On the annulus `ε < r < √ε` around each node the cutoff
is the normalized logarithm

```text
ψ_ε(z) = (2 / log ε⁻¹) ∫_ε^{|z|} dρ/ρ ,        |dψ_ε(z)| = 2 / (log ε⁻¹ · |z|) ,
```

and the whole point is that its Dirichlet energy is small.  The computation is the conformal area
of the annulus in the cylindrical metric `|dz|²/|z|²`:

```text
∫_{a<|z|<b} |dz|² / |z|²  =  2π log(b/a) ,
```

which for `b = √ε`, `a = ε` is `π log ε⁻¹`, so the energy is `(2/log ε⁻¹)² · π log ε⁻¹ =
4π / log ε⁻¹`.  The paper only needs an upper bound of this shape; the identity proved here is
exact.
-/

open MeasureTheory Set Real

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

open _root_.HTGeometry (deningerAnnulus polarCoord_symm_eq_circleMap)

/-- **The conformal area of an annulus.**  `∫_{a<|z|<b} |z|^{-2} = 2π log(b/a)`. -/
theorem setIntegral_annulus_inv_normSq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ w in deningerAnnulus a b, (‖w‖ ^ 2)⁻¹) = 2 * π * Real.log (b / a) := by
  set A : Set ℂ := deningerAnnulus a b with hA
  set f : ℂ → ℝ := fun w => (‖w‖ ^ 2)⁻¹ with hf
  have hAopen : IsOpen A := by
    have hpre : A = (fun w : ℂ => ‖w‖) ⁻¹' (Set.Ioo a b) := by
      ext w; simp [hA, deningerAnnulus, Set.mem_Ioo]
    rw [hpre]
    exact isOpen_Ioo.preimage continuous_norm
  have hAmeas : MeasurableSet A := hAopen.measurableSet
  have hBmeas : MeasurableSet (Set.Ioo a b ×ˢ Set.Ioo (-π) π) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hpolar := Complex.integral_comp_polarCoord_symm (Set.indicator A f)
  rw [MeasureTheory.integral_indicator hAmeas] at hpolar
  have htgt : polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π := rfl
  rw [← hpolar, htgt]
  have key : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π,
      p.1 • Set.indicator A f (Complex.polarCoord.symm p)
        = Set.indicator (Set.Ioo a b ×ˢ Set.Ioo (-π) π)
            (fun q : ℝ × ℝ => (1 / q.1) * (1 : ℝ)) p := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    simp only [Set.mem_Ioi] at hr
    have hsymm : Complex.polarCoord.symm (r, θ) = circleMap 0 r θ :=
      polarCoord_symm_eq_circleMap (r, θ)
    have hnorm : ‖circleMap 0 r θ‖ = r := by
      rw [norm_circleMap_zero, abs_of_pos hr]
    by_cases hmem : a < r ∧ r < b
    · have h1 : circleMap 0 r θ ∈ A := by
        rw [hA]
        simp only [deningerAnnulus, Set.mem_setOf_eq, hnorm]
        exact hmem
      have h2 : ((r, θ) : ℝ × ℝ) ∈ Set.Ioo a b ×ˢ Set.Ioo (-π) π := ⟨hmem, hθ⟩
      rw [hsymm, Set.indicator_of_mem h1, Set.indicator_of_mem h2, hf]
      show r • (‖circleMap 0 r θ‖ ^ 2)⁻¹ = 1 / r * (1 : ℝ)
      rw [hnorm, smul_eq_mul]
      field_simp
    · have h1 : circleMap 0 r θ ∉ A := by
        rw [hA]
        simp only [deningerAnnulus, Set.mem_setOf_eq, hnorm]
        exact hmem
      have h2 : ((r, θ) : ℝ × ℝ) ∉ Set.Ioo a b ×ˢ Set.Ioo (-π) π := by
        intro hc
        exact hmem hc.1
      rw [hsymm, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, smul_zero]
  rw [MeasureTheory.setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) key,
    MeasureTheory.setIntegral_indicator hBmeas]
  have hInter : Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π ∩ (Set.Ioo a b ×ˢ Set.Ioo (-π) π)
      = Set.Ioo a b ×ˢ Set.Ioo (-π) π :=
    Set.inter_eq_self_of_subset_right
      (Set.prod_mono (fun x hx => lt_trans ha hx.1) (subset_refl _))
  rw [hInter, MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.setIntegral_prod_mul (fun r : ℝ => 1 / r) (fun _ : ℝ => (1 : ℝ))
      (Set.Ioo a b) (Set.Ioo (-π) π)]
  have h1 : (∫ r in Set.Ioo a b, 1 / r) = Real.log (b / a) := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]
    exact integral_one_div_of_pos ha (lt_of_lt_of_le ha hab)
  have h2 : (∫ _θ in Set.Ioo (-π) π, (1 : ℝ)) = 2 * π := by
    simp only [MeasureTheory.setIntegral_const, Real.volume_real_Ioo, smul_eq_mul, mul_one]
    rw [max_eq_left (by linarith [Real.pi_pos] : (0 : ℝ) ≤ π - -π)]
    ring
  rw [h1, h2]
  ring

/-- **Lemma 6.6 (3) of Dai–Yoshikawa, in exact form.**

The normalized logarithmic cutoff on the annulus `ε < |z| < √ε` has Dirichlet energy exactly
`4π / log ε⁻¹`, hence tends to zero as `ε → 0`. -/
theorem setIntegral_logCutoff_energy {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    (∫ w in deningerAnnulus eps (Real.sqrt eps), ((2 / Real.log eps⁻¹) * ‖w‖⁻¹) ^ 2)
      = 4 * π / Real.log eps⁻¹ := by
  have hlogneg : Real.log eps < 0 := Real.log_neg heps heps1
  have hL : 0 < Real.log eps⁻¹ := by
    rw [Real.log_inv]
    linarith
  have hle : eps ≤ Real.sqrt eps := by
    have hsq : eps ^ 2 ≤ eps := by nlinarith
    have h2 := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq heps.le] at h2
  have hconst : ∀ w : ℂ,
      ((2 / Real.log eps⁻¹) * ‖w‖⁻¹) ^ 2 = (2 / Real.log eps⁻¹) ^ 2 * (‖w‖ ^ 2)⁻¹ := by
    intro w
    rw [mul_pow, ← inv_pow]
  simp only [hconst]
  rw [MeasureTheory.integral_const_mul, setIntegral_annulus_inv_normSq heps hle]
  have hlog : Real.log (Real.sqrt eps / eps) = Real.log eps⁻¹ / 2 := by
    rw [Real.log_div (Real.sqrt_pos.mpr heps).ne' (ne_of_gt heps), Real.log_sqrt heps.le,
      Real.log_inv]
    ring
  rw [hlog]
  field_simp
  ring

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
