import GaloisForLFunctions.RHTower.Sieve.PerronKernelResidue
import GaloisForLFunctions.HTGeometry.PerronKernelSegments

/-!
# Perron's lemma

The truncated vertical integral of the kernel `y^s/s` on a line `Re s = σ > 0` detects whether `y`
exceeds `1`, with an error inversely proportional to the height of the truncation and to `|log y|`:

`‖(1/2π)∫_{−T}^{T} y^{σ+it}/(σ+it) dt − 1_{y>1}‖ ≤ y^σ/(π T |log y|)`.

Both cases are a contour shift.  For `y > 1` the rectangle with corners `−A − iT` and `σ + iT`
contains the simple pole at the origin, whose residue is `1`; for `y < 1` the rectangle with corners
`σ − iT` and `A + iT` contains no pole and the boundary integral vanishes.  In either case the edge
at distance `A` from the origin contributes at most `2T·y^{∓A}/A`, which tends to `0`, and the two
horizontal edges contribute `y^σ/(T|log y|)` each, uniformly in `A`.

The constant in front of the kernel is `y^σ` alone: unlike a smoothing weight, whose Mellin transform
costs an extra power of the reciprocal window width, the sharp cutoff pays for itself entirely
through the factor `1/(T|log y|)`, which is a genuine saving once `y` is bounded away from `1`.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

/-- The truncated Perron integral: the vertical integral of `y^s/s` over `Re s = σ`, `|Im s| ≤ T`,
normalised by `1/2π`. -/
def perronVertical (σ T y : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t in (-T)..T, ((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) / ((σ : ℂ) + (t : ℝ) * I)

/-- The Perron kernel is holomorphic off the origin. -/
theorem holomorphicOn_perronKernel {y : ℝ} (hy : 0 < y) :
    DifferentiableOn ℂ (fun s : ℂ => (y : ℂ) ^ s / s) ({(0 : ℂ)}ᶜ) := by
  have hy0 : ((y : ℂ)) ≠ 0 := by simpa using hy.ne'
  intro s hs
  have hsne : s ≠ 0 := by simpa using hs
  refine DifferentiableWithinAt.div ?_ differentiableWithinAt_id hsne
  exact (differentiableAt_id.const_cpow (Or.inl hy0)).differentiableWithinAt

/-- The vertical edge of the contour, at distance `|a|` from the origin, in the form the rectangle
integral produces it. -/
theorem norm_vIntegral_cpow_div_le {y : ℝ} (hy : 0 < y) {a T : ℝ} (ha : a ≠ 0) (hT : 0 ≤ T) :
    ‖VIntegral (fun s : ℂ => (y : ℂ) ^ s / s) a (-T) T‖ ≤ 2 * T * (y ^ a / |a|) := by
  rw [VIntegral, norm_smul, Complex.norm_I, one_mul]
  exact norm_integral_vertical_edge_cpow_le hy ha hT

/-- **Perron's lemma for `y > 1`.**  The truncated integral is `1` up to `y^σ/(π T log y)`. -/
theorem norm_perronVertical_sub_one_le {y : ℝ} (hy : 1 < y) {σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    ‖perronVertical σ T y - 1‖ ≤ y ^ σ / (Real.pi * T * Real.log y) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hlog : (0 : ℝ) < Real.log y := Real.log_pos hy
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set B : ℝ := y ^ σ / (Real.pi * T * Real.log y) with hB
  -- the bound at a finite shift `A`
  have key : ∀ A : ℝ, 0 < A →
      ‖perronVertical σ T y - 1‖ ≤ B + T * y ^ (-A) / (Real.pi * A) := by
    intro A hA
    set f : ℂ → ℂ := fun s : ℂ => (y : ℂ) ^ s / s with hf
    set z : ℂ := ((-A : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I with hz
    set w : ℂ := ((σ : ℝ) : ℂ) + ((T : ℝ) : ℂ) * I with hw
    have hzre : z.re = -A := by simp [hz]
    have hzim : z.im = -T := by simp [hz]
    have hwre : w.re = σ := by simp [hw]
    have hwim : w.im = T := by simp [hw]
    have h0 : Complex.Rectangle z w ∈ 𝓝 (0 : ℂ) := by
      rw [rectangle_mem_nhds_iff]
      refine Complex.mem_reProdIm.2 ⟨?_, ?_⟩
      · rw [hzre, hwre, Set.uIoo_of_le (by linarith)]
        simp only [Complex.zero_re]
        exact Set.mem_Ioo.2 ⟨by linarith, hσ⟩
      · rw [hzim, hwim, Set.uIoo_of_le (by linarith)]
        simp only [Complex.zero_im]
        exact Set.mem_Ioo.2 ⟨by linarith, hT⟩
    have hres := rectangleIntegral'_cpow_div_eq_one hy0 (z := z) (w := w)
      (by rw [hzre, hwre]; linarith) (by rw [hzim, hwim]; linarith) h0
    rw [RectangleIntegral', RectangleIntegral, hzre, hzim, hwre, hwim, smul_eq_mul] at hres
    set H₁ : ℂ := HIntegral f (-A) σ (-T) with hH₁
    set H₂ : ℂ := HIntegral f (-A) σ T with hH₂
    set V : ℂ := ∫ t in (-T)..T, f ((σ : ℂ) + (t : ℝ) * I) with hV
    set VA : ℂ := ∫ t in (-T)..T, f (((-A : ℝ) : ℂ) + (t : ℝ) * I) with hVA
    have hVeq : VIntegral f σ (-T) T = I * V := by
      rw [VIntegral, smul_eq_mul, hV]
    have hVAeq : VIntegral f (-A) (-T) T = I * VA := by
      rw [VIntegral, smul_eq_mul, hVA]
    rw [hVeq, hVAeq] at hres
    have h2pi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
      exact_mod_cast hpi.ne'
    have heq : H₁ - H₂ + I * V - I * VA = 2 * (Real.pi : ℂ) * I := by
      rw [one_div, inv_mul_eq_iff_eq_mul₀ h2pi] at hres
      simpa using hres
    have hVsub : I * (V - 2 * (Real.pi : ℂ)) = -H₁ + H₂ + I * VA := by
      linear_combination heq
    have hnormV : ‖V - 2 * (Real.pi : ℂ)‖ ≤ ‖H₁‖ + ‖H₂‖ + ‖VA‖ := by
      have hI : ‖I * (V - 2 * (Real.pi : ℂ))‖ = ‖V - 2 * (Real.pi : ℂ)‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
      calc ‖V - 2 * (Real.pi : ℂ)‖ = ‖-H₁ + H₂ + I * VA‖ := by rw [← hI, hVsub]
        _ ≤ ‖-H₁‖ + ‖H₂‖ + ‖I * VA‖ := norm_add₃_le
        _ = ‖H₁‖ + ‖H₂‖ + ‖VA‖ := by
            rw [norm_neg, norm_mul, Complex.norm_I, one_mul]
    -- the three segment estimates
    have hH₁le : ‖H₁‖ ≤ y ^ σ / (T * Real.log y) := by
      have h := norm_integral_horizontal_le (y := y) hy (σ := σ) (A := A) (T := -T)
        (by simpa using hT.ne') (by linarith)
      rw [hH₁, HIntegral, hf]
      refine le_trans h (le_of_eq ?_)
      rw [abs_of_nonpos (by linarith : -T ≤ (0:ℝ))]
      ring_nf
    have hH₂le : ‖H₂‖ ≤ y ^ σ / (T * Real.log y) := by
      have h := norm_integral_horizontal_le (y := y) hy (σ := σ) (A := A) (T := T)
        hT.ne' (by linarith)
      rw [hH₂, HIntegral, hf]
      refine le_trans h (le_of_eq ?_)
      rw [abs_of_nonneg hT.le]
    have hVAle : ‖VA‖ ≤ 2 * T * (y ^ (-A) / A) := by
      have h := norm_integral_vertical_edge_cpow_le (y := y) hy0 (a := -A)
        (by simpa using hA.ne') hT.le
      rw [hVA, hf]
      refine le_trans h (le_of_eq ?_)
      rw [abs_of_nonpos (by linarith : -A ≤ (0:ℝ))]
      ring_nf
    -- assemble
    have hpv : perronVertical σ T y - 1 = ((1 / (2 * Real.pi) : ℝ) : ℂ) * (V - 2 * (Real.pi : ℂ)) := by
      rw [perronVertical, hV, hf]
      have h2 : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (2 * (Real.pi : ℂ)) = 1 := by
        push_cast
        field_simp
      calc ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (∫ t in (-T)..T, ((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) / ((σ : ℂ) + (t : ℝ) * I)) - 1
          = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            (∫ t in (-T)..T, ((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) / ((σ : ℂ) + (t : ℝ) * I))
              - ((1 / (2 * Real.pi) : ℝ) : ℂ) * (2 * (Real.pi : ℂ)) := by rw [h2]
        _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ((∫ t in (-T)..T, ((y : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)) / ((σ : ℂ) + (t : ℝ) * I))
              - 2 * (Real.pi : ℂ)) := by ring
    rw [hpv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (2 * Real.pi))]
    have hmono : (1 / (2 * Real.pi)) * ‖V - 2 * (Real.pi : ℂ)‖
        ≤ (1 / (2 * Real.pi)) * (‖H₁‖ + ‖H₂‖ + ‖VA‖) :=
      mul_le_mul_of_nonneg_left hnormV (by positivity)
    refine le_trans hmono ?_
    have hsum : ‖H₁‖ + ‖H₂‖ + ‖VA‖
        ≤ 2 * (y ^ σ / (T * Real.log y)) + 2 * T * (y ^ (-A) / A) := by
      linarith
    refine le_trans (mul_le_mul_of_nonneg_left hsum (by positivity)) (le_of_eq ?_)
    rw [hB]
    field_simp
  -- let the shift tend to infinity
  have hstep : ∀ n : ℕ, 1 ≤ n →
      B + T * y ^ (-(n : ℝ)) / (Real.pi * (n : ℝ)) ≤ B + T * (y⁻¹) ^ n / Real.pi := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hpow : y ^ (-(n : ℝ)) = (y⁻¹) ^ n := by
      rw [Real.rpow_neg hy0.le, Real.rpow_natCast, ← inv_pow]
    rw [hpow]
    have hnum : (0 : ℝ) ≤ T * (y⁻¹) ^ n := by positivity
    have hle : Real.pi ≤ Real.pi * (n : ℝ) := by nlinarith
    have := div_le_div_of_nonneg_left hnum hpi hle
    linarith
  have hlim : Tendsto (fun n : ℕ => B + T * (y⁻¹) ^ n / Real.pi) atTop (𝓝 B) := by
    have hbase : Tendsto (fun n : ℕ => (y⁻¹) ^ n) atTop (𝓝 0) := by
      refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
      rw [inv_lt_one_iff₀]
      exact Or.inr hy
    have := ((hbase.const_mul T).div_const Real.pi).const_add B
    simpa using this
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  exact le_trans (key (n : ℝ) hn0) (hstep n hn)

/-- **Perron's lemma for `y < 1`.**  There is no pole to the right, so the truncated integral is
`0` up to `y^σ/(π T |log y|)`. -/
theorem norm_perronVertical_le {y : ℝ} (hy0 : 0 < y) (hy : y < 1) {σ T : ℝ} (hσ : 0 < σ)
    (hT : 0 < T) :
    ‖perronVertical σ T y‖ ≤ y ^ σ / (Real.pi * T * |Real.log y|) := by
  have hlog : Real.log y < 0 := Real.log_neg hy0 hy
  have hlogabs : (0 : ℝ) < |Real.log y| := abs_pos.mpr (ne_of_lt hlog)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set B : ℝ := y ^ σ / (Real.pi * T * |Real.log y|) with hB
  have key : ∀ A : ℝ, σ ≤ A → 0 < A →
      ‖perronVertical σ T y‖ ≤ B + T * y ^ A / (Real.pi * A) := by
    intro A hσA hA
    set f : ℂ → ℂ := fun s : ℂ => (y : ℂ) ^ s / s with hf
    set z : ℂ := ((σ : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I with hz
    set w : ℂ := ((A : ℝ) : ℂ) + ((T : ℝ) : ℂ) * I with hw
    have hzre : z.re = σ := by simp [hz]
    have hzim : z.im = -T := by simp [hz]
    have hwre : w.re = A := by simp [hw]
    have hwim : w.im = T := by simp [hw]
    have hsub : Complex.Rectangle z w ⊆ ({(0 : ℂ)}ᶜ) := by
      intro s hs
      rw [Complex.Rectangle, hzre, hzim, hwre, hwim] at hs
      have hre := (Complex.mem_reProdIm.1 hs).1
      rw [Set.uIcc_of_le hσA] at hre
      have hspos : 0 < s.re := lt_of_lt_of_le hσ hre.1
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      rw [h] at hspos
      simp at hspos
    have hres : RectangleIntegral f z w = 0 :=
      HolomorphicOn.vanishesOnRectangle (holomorphicOn_perronKernel hy0) hsub
    rw [RectangleIntegral, hzre, hzim, hwre, hwim] at hres
    set H₁ : ℂ := HIntegral f σ A (-T) with hH₁
    set H₂ : ℂ := HIntegral f σ A T with hH₂
    set V : ℂ := ∫ t in (-T)..T, f ((σ : ℂ) + (t : ℝ) * I) with hV
    set VA : ℂ := ∫ t in (-T)..T, f (((A : ℝ) : ℂ) + (t : ℝ) * I) with hVA
    have hVeq : VIntegral f σ (-T) T = I * V := by
      rw [VIntegral, smul_eq_mul, hV]
    have hVAeq : VIntegral f A (-T) T = I * VA := by
      rw [VIntegral, smul_eq_mul, hVA]
    rw [hVeq, hVAeq] at hres
    have hVsub : I * V = H₁ - H₂ + I * VA := by linear_combination -hres
    have hnormV : ‖V‖ ≤ ‖H₁‖ + ‖H₂‖ + ‖VA‖ := by
      have hI : ‖I * V‖ = ‖V‖ := by rw [norm_mul, Complex.norm_I, one_mul]
      calc ‖V‖ = ‖H₁ + -H₂ + I * VA‖ := by rw [← hI, hVsub]; ring_nf
        _ ≤ ‖H₁‖ + ‖-H₂‖ + ‖I * VA‖ := norm_add₃_le
        _ = ‖H₁‖ + ‖H₂‖ + ‖VA‖ := by rw [norm_neg, norm_mul, Complex.norm_I, one_mul]
    have hH₁le : ‖H₁‖ ≤ y ^ σ / (T * |Real.log y|) := by
      have h := norm_integral_horizontal_le' (y := y) hy0 hy (σ := σ) (A := A) (T := -T)
        (by simpa using hT.ne') hσA
      rw [hH₁, HIntegral, hf]
      refine le_trans h (le_of_eq ?_)
      rw [abs_of_nonpos (by linarith : -T ≤ (0:ℝ))]
      ring_nf
    have hH₂le : ‖H₂‖ ≤ y ^ σ / (T * |Real.log y|) := by
      have h := norm_integral_horizontal_le' (y := y) hy0 hy (σ := σ) (A := A) (T := T)
        hT.ne' hσA
      rw [hH₂, HIntegral, hf]
      refine le_trans h (le_of_eq ?_)
      rw [abs_of_nonneg hT.le]
    have hVAle : ‖VA‖ ≤ 2 * T * (y ^ A / A) := by
      have h := norm_integral_vertical_edge_cpow_le (y := y) hy0 (a := A) hA.ne' hT.le
      rw [hVA, hf]
      refine le_trans h (le_of_eq ?_)
      rw [abs_of_nonneg hA.le]
    have hpv : ‖perronVertical σ T y‖ = (1 / (2 * Real.pi)) * ‖V‖ := by
      rw [perronVertical, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (2 * Real.pi)), hV, hf]
    rw [hpv]
    have hmono : (1 / (2 * Real.pi)) * ‖V‖ ≤ (1 / (2 * Real.pi)) * (‖H₁‖ + ‖H₂‖ + ‖VA‖) :=
      mul_le_mul_of_nonneg_left hnormV (by positivity)
    refine le_trans hmono ?_
    have hsum : ‖H₁‖ + ‖H₂‖ + ‖VA‖
        ≤ 2 * (y ^ σ / (T * |Real.log y|)) + 2 * T * (y ^ A / A) := by linarith
    refine le_trans (mul_le_mul_of_nonneg_left hsum (by positivity)) (le_of_eq ?_)
    rw [hB]
    field_simp
  have hstep : ∀ n : ℕ, max 1 ⌈σ⌉₊ ≤ n →
      B + T * y ^ ((n : ℝ)) / (Real.pi * (n : ℝ)) ≤ B + T * y ^ n / Real.pi := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have : 1 ≤ n := le_trans (le_max_left _ _) hn
      exact_mod_cast this
    have hpow : y ^ ((n : ℝ)) = y ^ n := Real.rpow_natCast y n
    rw [hpow]
    have hnum : (0 : ℝ) ≤ T * y ^ n := by positivity
    have hle : Real.pi ≤ Real.pi * (n : ℝ) := by nlinarith
    have := div_le_div_of_nonneg_left hnum hpi hle
    linarith
  have hlim : Tendsto (fun n : ℕ => B + T * y ^ n / Real.pi) atTop (𝓝 B) := by
    have hbase : Tendsto (fun n : ℕ => y ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hy0.le hy
    have := ((hbase.const_mul T).div_const Real.pi).const_add B
    simpa using this
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop (max 1 ⌈σ⌉₊)] with n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  have hσn : σ ≤ (n : ℝ) := by
    have hceil : ⌈σ⌉₊ ≤ n := le_trans (le_max_right _ _) hn
    calc σ ≤ (⌈σ⌉₊ : ℝ) := Nat.le_ceil σ
      _ ≤ (n : ℝ) := by exact_mod_cast hceil
  exact le_trans (key (n : ℝ) hσn hn0) (hstep n hn)

end RHTower.Sieve
end
