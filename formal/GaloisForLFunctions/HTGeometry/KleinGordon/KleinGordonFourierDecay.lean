import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonProbeAnywhere

/-!
# Uniform decay of a Fourier transform

The admissible families ask for a *uniform* weighted bound on a curve of densities, so the decay of a
Fourier transform has to be quantified: the constant must be an explicit functional of the function,
not an unnamed constant produced by the Schwartz axioms.

The Klein–Gordon multiplier supplies it. Its symbol is `⟨η⟩²`, so applying it `j` times multiplies
the transform by `⟨η⟩²ʲ`, and the transform of any function is bounded by the `L¹` norm of that
function. Hence

`‖𝓕f(η)‖ ≤ ⟨η⟩⁻²ʲ ‖(1 - (2π)⁻²Δ)ʲ f‖₁`,

an estimate whose right-hand side is an explicit norm — which is what a family of potentials can be
required to bound uniformly in time.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory SchwartzMap Function

open scoped SchwartzMap FourierTransform RealInnerProductSpace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## The Klein–Gordon multiplier -/

/-- The Klein–Gordon operator on Schwartz functions, as a multiplier. -/
noncomputable def kgSchwartzOp (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  fourierMultiplierCLM ℂ (fun ξ : E => ((kgFreq ξ ^ (2 : ℕ) : ℝ) : ℂ)) f

theorem kgSchwartzOp_eq (f : 𝓢(E, ℂ)) :
    kgSchwartzOp f = f - (((2 * Real.pi) ^ (2 : ℕ) : ℝ))⁻¹ • Δ f := by
  rw [kgSchwartzOp, ← fourierMultiplierCLM_kgFreqSq (F := ℂ) f]
  exact fourierMultiplierCLM_ofReal ℂ ((hasTemperateGrowth_kgFreq E).pow 2) f

/-- **The multiplier multiplies the transform by the symbol.** -/
theorem fourier_kgSchwartzOp (f : 𝓢(E, ℂ)) (η : E) :
    (𝓕 (kgSchwartzOp f)) η = ((kgFreq η ^ (2 : ℕ) : ℝ) : ℂ) * (𝓕 f) η := by
  have hgrow : Function.HasTemperateGrowth fun ξ : E => ((kgFreq ξ ^ (2 : ℕ) : ℝ) : ℂ) :=
    Complex.hasTemperateGrowth_ofReal.comp ((hasTemperateGrowth_kgFreq E).pow 2)
  have hval : 𝓕 (kgSchwartzOp f)
      = smulLeftCLM ℂ (fun ξ : E => ((kgFreq ξ ^ (2 : ℕ) : ℝ) : ℂ)) (𝓕 f) := by
    rw [kgSchwartzOp, fourierMultiplierCLM_apply]
    exact FourierInvPair.fourier_fourierInv_eq _
  rw [hval, smulLeftCLM_apply_apply hgrow (𝓕 f) η, smul_eq_mul]

/-- Iterating the multiplier multiplies by a power of the symbol. -/
theorem fourier_kgSchwartzOp_iterate (j : ℕ) (f : 𝓢(E, ℂ)) (η : E) :
    (𝓕 (kgSchwartzOp^[j] f)) η = ((kgFreq η ^ (2 * j) : ℝ) : ℂ) * (𝓕 f) η := by
  induction j generalizing f with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih (kgSchwartzOp f), fourier_kgSchwartzOp f η]
    have harith : 2 * j + 2 = 2 * (j + 1) := by ring
    rw [← mul_assoc, ← Complex.ofReal_mul, ← pow_add, harith]

/-! ## The bound -/

theorem norm_fourier_le_integral (g : 𝓢(E, ℂ)) (η : E) :
    ‖(𝓕 g) η‖ ≤ ∫ v : E, ‖g v‖ := by
  have hcoe : (𝓕 g) η = 𝓕 (g : E → ℂ) η := congrFun (SchwartzMap.fourier_coe g) η
  rw [hcoe, Real.fourier_eq]
  have hbound : ∀ v : E, ‖(𝐞 (-⟪v, η⟫) : Circle) • g v‖ = ‖g v‖ := fun v => Circle.norm_smul _ _
  have hint : Integrable (fun v : E => ‖g v‖) (volume : Measure E) := g.integrable.norm
  refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun v => ?_))
  exact le_of_eq (hbound v)

/-- **Quantified decay of a Fourier transform.** -/
theorem norm_fourier_le_weight (j : ℕ) (f : 𝓢(E, ℂ)) (η : E) :
    ‖(𝓕 f) η‖ ≤ (kgFreq η ^ (2 * j))⁻¹ * ∫ v : E, ‖(kgSchwartzOp^[j] f) v‖ := by
  have hpos : (0 : ℝ) < kgFreq η ^ (2 * j) := pow_pos (kgFreq_pos η) (2 * j)
  have hval := fourier_kgSchwartzOp_iterate j f η
  have hnorm : kgFreq η ^ (2 * j) * ‖(𝓕 f) η‖ = ‖(𝓕 (kgSchwartzOp^[j] f)) η‖ := by
    rw [hval, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  have hle := norm_fourier_le_integral (kgSchwartzOp^[j] f) η
  rw [← hnorm] at hle
  rw [← le_div_iff₀' hpos] at hle
  refine hle.trans_eq ?_
  rw [inv_mul_eq_div]

/-! ## Curves of Schwartz potentials -/

section Curve

variable {N : ℕ}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem inv_pow_le_inv_pow_of_le {k l : ℕ} (hkl : k ≤ l) (η : E) :
    (kgFreq η ^ l)⁻¹ ≤ (kgFreq η ^ k)⁻¹ := by
  have hone : (1 : ℝ) ≤ kgFreq η := one_le_kgFreq η
  have hk : (0 : ℝ) < kgFreq η ^ k := pow_pos (kgFreq_pos η) k
  refine inv_anti₀ hk ?_
  exact pow_le_pow_right₀ hone hkl

/-- **A curve of Schwartz potentials is an admissible family**, provided the explicit decay
functional is bounded uniformly in time and Lipschitz in time. -/
noncomputable def WienerFamily.ofSchwartzCurve {Φ : ℝ → 𝓢(E, ℂ)} {j m : ℕ} {M L : ℝ}
    (hdim : (Module.finrank ℝ E : ℝ) < m) (hj : N + m ≤ 2 * j)
    (hM : ∀ t : ℝ, (∫ v : E, ‖(kgSchwartzOp^[j] (Φ t)) v‖) ≤ M) (hL0 : 0 ≤ L)
    (hL : ∀ t t' : ℝ, (∫ v : E, ‖(kgSchwartzOp^[j] (Φ t - Φ t')) v‖) ≤ L * |t - t'|) :
    WienerFamily E N := by
  refine WienerFamily.ofWeightedBounds (N := N) (m := m) (M := M) (L := L)
    (a := fun t => fun η : E => (𝓕 (Φ t)) η)
    hdim (fun t => (𝓕 (Φ t)).continuous.aestronglyMeasurable) (fun t η => ?_) hL0
    (fun t t' η => ?_)
  · have hbound := norm_fourier_le_weight j (Φ t) η
    have hmono : (kgFreq η ^ (2 * j))⁻¹ ≤ (kgFreq η ^ (N + m))⁻¹ :=
      inv_pow_le_inv_pow_of_le hj η
    have hM0 : (0 : ℝ) ≤ ∫ v : E, ‖(kgSchwartzOp^[j] (Φ t)) v‖ :=
      integral_nonneg fun v => norm_nonneg _
    calc ‖(𝓕 (Φ t)) η‖
        ≤ (kgFreq η ^ (2 * j))⁻¹ * ∫ v : E, ‖(kgSchwartzOp^[j] (Φ t)) v‖ := hbound
      _ ≤ (kgFreq η ^ (N + m))⁻¹ * ∫ v : E, ‖(kgSchwartzOp^[j] (Φ t)) v‖ :=
          mul_le_mul_of_nonneg_right hmono hM0
      _ ≤ (kgFreq η ^ (N + m))⁻¹ * M :=
          mul_le_mul_of_nonneg_left (hM t) (inv_nonneg.mpr (pow_pos (kgFreq_pos η) (N + m)).le)
  · have hmap : 𝓕 (Φ t - Φ t') = 𝓕 (Φ t) - 𝓕 (Φ t') := by
      rw [sub_eq_add_neg, sub_eq_add_neg, FourierTransform.fourier_add,
        FourierTransform.fourier_neg]
    have hsub : (𝓕 (Φ t)) η - (𝓕 (Φ t')) η = (𝓕 (Φ t - Φ t')) η := by
      rw [hmap]
      rfl
    have hbound := norm_fourier_le_weight j (Φ t - Φ t') η
    have hmono : (kgFreq η ^ (2 * j))⁻¹ ≤ (kgFreq η ^ (N + m))⁻¹ :=
      inv_pow_le_inv_pow_of_le hj η
    have hL0' : (0 : ℝ) ≤ ∫ v : E, ‖(kgSchwartzOp^[j] (Φ t - Φ t')) v‖ :=
      integral_nonneg fun v => norm_nonneg _
    rw [hsub]
    calc ‖(𝓕 (Φ t - Φ t')) η‖
        ≤ (kgFreq η ^ (2 * j))⁻¹ * ∫ v : E, ‖(kgSchwartzOp^[j] (Φ t - Φ t')) v‖ := hbound
      _ ≤ (kgFreq η ^ (N + m))⁻¹ * ∫ v : E, ‖(kgSchwartzOp^[j] (Φ t - Φ t')) v‖ :=
          mul_le_mul_of_nonneg_right hmono hL0'
      _ ≤ (kgFreq η ^ (N + m))⁻¹ * (L * |t - t'|) :=
          mul_le_mul_of_nonneg_left (hL t t')
            (inv_nonneg.mpr (pow_pos (kgFreq_pos η) (N + m)).le)

theorem WienerFamily.ofSchwartzCurve_density_apply {Φ : ℝ → 𝓢(E, ℂ)} {j m : ℕ} {M L : ℝ}
    (hdim : (Module.finrank ℝ E : ℝ) < m) (hj : N + m ≤ 2 * j)
    (hM : ∀ t : ℝ, (∫ v : E, ‖(kgSchwartzOp^[j] (Φ t)) v‖) ≤ M) (hL0 : 0 ≤ L)
    (hL : ∀ t t' : ℝ, (∫ v : E, ‖(kgSchwartzOp^[j] (Φ t - Φ t')) v‖) ≤ L * |t - t'|)
    (t : ℝ) (η : E) :
    (WienerFamily.ofSchwartzCurve (N := N) hdim hj hM hL0 hL).density t η = (𝓕 (Φ t)) η := rfl

theorem isRealFamily_ofSchwartzCurve {Φ : ℝ → 𝓢(E, ℂ)} {j m : ℕ} {M L : ℝ}
    (hdim : (Module.finrank ℝ E : ℝ) < m) (hj : N + m ≤ 2 * j)
    (hM : ∀ t : ℝ, (∫ v : E, ‖(kgSchwartzOp^[j] (Φ t)) v‖) ≤ M) (hL0 : 0 ≤ L)
    (hL : ∀ t t' : ℝ, (∫ v : E, ‖(kgSchwartzOp^[j] (Φ t - Φ t')) v‖) ≤ L * |t - t'|)
    (hreal : ∀ (t : ℝ) (x : E), (starRingEnd ℂ) (Φ t x) = Φ t x) :
    IsRealFamily (WienerFamily.ofSchwartzCurve (N := N) hdim hj hM hL0 hL) := by
  intro t η
  exact isRealDensity_ofSchwartz_fourier (Φ t) (hreal t) N η

theorem kgPotential_ofSchwartzCurve {Φ : ℝ → 𝓢(E, ℂ)} {j m : ℕ} {M L : ℝ}
    (hdim : (Module.finrank ℝ E : ℝ) < m) (hj : N + m ≤ 2 * j)
    (hM : ∀ t : ℝ, (∫ v : E, ‖(kgSchwartzOp^[j] (Φ t)) v‖) ≤ M) (hL0 : 0 ≤ L)
    (hL : ∀ t t' : ℝ, (∫ v : E, ‖(kgSchwartzOp^[j] (Φ t - Φ t')) v‖) ≤ L * |t - t'|)
    (t : ℝ) (x : E) :
    kgPotential ((WienerFamily.ofSchwartzCurve (N := N) hdim hj hM hL0 hL).density t) x
      = Φ t x :=
  kgPotential_ofSchwartz_fourier (Φ t) N x

end Curve

/-! ## Probes for a time-dependent Schwartz potential -/

section CurveProbe

variable {d N j m : ℕ}

/-- **Clock probes for a time-dependent potential** given by a curve of Schwartz functions whose
decay functional is uniformly bounded and Lipschitz in time. The chart potential is the given
function of the event, shifted by the mass. -/
theorem openProbes_of_schwartzCurve {Φ : ℝ → 𝓢(EuclideanSpace ℝ (Fin d), ℂ)} {M L : ℝ}
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    (hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < m) (hj : N + m ≤ 2 * j)
    (hM : ∀ t : ℝ, (∫ v : EuclideanSpace ℝ (Fin d), ‖(kgSchwartzOp^[j] (Φ t)) v‖) ≤ M)
    (hL0 : 0 ≤ L)
    (hL : ∀ t t' : ℝ,
      (∫ v : EuclideanSpace ℝ (Fin d), ‖(kgSchwartzOp^[j] (Φ t - Φ t')) v‖) ≤ L * |t - t'|)
    (hreal : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), (starRingEnd ℂ) (Φ t x) = Φ t x) :
    OpenProbes (kgWaveOp d)
      (fun y : Fin (d + 1) → ℝ => (Φ (y 0) (kgSpatial d y)).re - 1) := by
  have hfun : (fun y : Fin (d + 1) → ℝ => (Φ (y 0) (kgSpatial d y)).re - 1)
      = kgChartPotential (WienerFamily.ofSchwartzCurve (N := N) hdim hj hM hL0 hL) := by
    funext y
    rw [kgChartPotential, kgPotential_ofSchwartzCurve]
  rw [hfun]
  exact openProbes_kgChartPotential _ hN (isRealFamily_ofSchwartzCurve hdim hj hM hL0 hL hreal)

end CurveProbe

end GaloisForLFunctions.HTGeometry
