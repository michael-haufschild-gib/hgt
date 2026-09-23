import GaloisForLFunctions.HTGeometry.AbstractSpectralMass

/-!
# The co-moving mass cone

Let `p = R + iJ` be an admissible spectral point and let `M + iK` be its mass shift by `a`.
The deformation conserves `M K = R J`.  If the spectral height floor is at least `1/2`, then
`R² > J²`, hence `M > a`.  It follows that vertical time inside the mass cone, `|u| ≤ a`, spends
at most half of the original height:

`u K ≤ |u| |K| ≤ M |K| = R |J| ≤ R/2`.

Consequently the trace of a mass that co-moves at least linearly with vertical time is uniformly
bounded by the original real-time trace at time `sigma - 1/2`.  The mass may vary with `u`; this is
therefore not a fixed-family vertical-line rigidity statement.
-/

open Complex

namespace HTGeometry

noncomputable section

namespace AbstractSpectralFamily

variable {ι : Type*} (F : AbstractSpectralFamily ι)

/-- If the original spectral height floor is at least `1/2`, every shifted height strictly exceeds
the mass parameter itself.  The base-floor hypothesis is essential for abstract families. -/
theorem lt_re_mass_of_base_half {a : ℝ} (ha : 1 / 2 ≤ a)
    (hbase : 1 / 2 ≤ F.base) (i : ι) :
    a < ((F.mass ha).pt i).re := by
  have hR : 1 / 2 ≤ (F.pt i).re := hbase.trans (F.base_le i)
  have hJ := F.abs_im_lt i
  have hgap : 0 < (F.pt i).re ^ (2 : ℕ) - (F.pt i).im ^ (2 : ℕ) := by
    nlinarith [sq_abs (F.pt i).im, abs_nonneg ((F.pt i).im)]
  have harg := F.massArg_re a i
  have hle := re_le_sq_csqrtRe (F.massArg_re_pos ha i)
  have hM0 := csqrtRe_nonneg (F.massArg a i)
  rw [F.mass_pt, csqrt_re]
  rw [harg] at hle
  nlinarith [sq_nonneg a]

/-- **Pointwise co-moving cone estimate.**  Inside `|u| ≤ a`, the mass-shifted multiplier at
vertical time `u` is bounded by the original multiplier at the reduced positive real time
`sigma - 1/2`. -/
theorem norm_mass_term_le_comoving_weight
    {a σ u : ℝ} (ha : 1 / 2 ≤ a) (hbase : 1 / 2 ≤ F.base)
    (hu : |u| ≤ a) (hσ : 1 / 2 < σ) (i : ι) :
    ‖(F.mass ha).term ((σ : ℂ) + u * I) i‖ ≤ F.weight (σ - 1 / 2) i := by
  have hM : a < ((F.mass ha).pt i).re := F.lt_re_mass_of_base_half ha hbase i
  have hMR : (F.pt i).re < ((F.mass ha).pt i).re := by
    simpa only [mass_pt, csqrt_re] using F.re_lt_csqrtRe_massArg ha i
  have hMpos : 0 < ((F.mass ha).pt i).re := lt_trans (by linarith : 0 < a) hM
  have hRpos : 0 < (F.pt i).re := F.re_pos i
  have hprod := F.re_mul_im_mass ha i
  have hprodAbs :
      ((F.mass ha).pt i).re * |((F.mass ha).pt i).im| =
        (F.pt i).re * |(F.pt i).im| := by
    have habs := congrArg abs hprod
    simpa only [abs_mul, abs_of_pos hMpos, abs_of_pos hRpos] using habs
  have huK : u * ((F.mass ha).pt i).im ≤ (F.pt i).re / 2 := by
    calc
      u * ((F.mass ha).pt i).im ≤ |u * ((F.mass ha).pt i).im| := le_abs_self _
      _ = |u| * |((F.mass ha).pt i).im| := abs_mul _ _
      _ ≤ a * |((F.mass ha).pt i).im| :=
        mul_le_mul_of_nonneg_right hu (abs_nonneg _)
      _ ≤ ((F.mass ha).pt i).re * |((F.mass ha).pt i).im| :=
        mul_le_mul_of_nonneg_right hM.le (abs_nonneg _)
      _ = (F.pt i).re * |(F.pt i).im| := hprodAbs
      _ ≤ (F.pt i).re * (1 / 2) :=
        mul_le_mul_of_nonneg_left (F.abs_im_lt i).le hRpos.le
      _ = (F.pt i).re / 2 := by ring
  have hσ0 : 0 ≤ σ := by linarith
  have hσMR : σ * (F.pt i).re ≤ σ * ((F.mass ha).pt i).re :=
    mul_le_mul_of_nonneg_left hMR.le hσ0
  rw [(F.mass ha).norm_term, weight]
  apply Real.exp_le_exp.mpr
  have hre : (((σ : ℂ) + u * I)).re = σ := by simp [Complex.mul_re]
  have him : (((σ : ℂ) + u * I)).im = u := by simp [Complex.mul_im]
  rw [hre, him]
  linarith

/-- **Universal co-moving mass cone.**  For every admissible family with height floor at least
`1/2`, a mass aperture containing the vertical time has a uniform trace bound. -/
theorem norm_mass_traceC_le_comoving
    {a σ u : ℝ} (ha : 1 / 2 ≤ a) (hbase : 1 / 2 ≤ F.base)
    (hu : |u| ≤ a) (hσ : 1 / 2 < σ) :
    ‖(F.mass ha).traceC ((σ : ℂ) + u * I)‖ ≤ F.traceReal (σ - 1 / 2) := by
  have hτ : 0 < (((σ : ℂ) + u * I)).re := by
    simpa [Complex.mul_re] using (show 0 < σ by linarith)
  have hdelta : 0 < σ - 1 / 2 := by linarith
  refine le_trans (norm_tsum_le_tsum_norm ((F.mass ha).summable_norm_term hτ)) ?_
  rw [traceReal]
  exact Summable.tsum_le_tsum
    (fun i => F.norm_mass_term_le_comoving_weight ha hbase hu hσ i)
    ((F.mass ha).summable_norm_term hτ) (F.summable_weight hdelta)

end AbstractSpectralFamily

end

end HTGeometry
