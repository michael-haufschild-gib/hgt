import GaloisForLFunctions.BiScaleUncertainty.DyadicRenewalChain

/-!
# The Plancherel form of the packet energy

The signed packet `signedSource f N (u) = ∫ f(u+s) dν_N(s)` is the correlation of the compact source
`f` with the signed prime–polar measure, so its Fourier transform factors,

`𝓕(signedSource f N)(ξ) = 𝓕f(ξ) · ν̂_N(−ξ)`,

and Plancherel gives the spectral form of the packet energy,

`packetEnergy f N = ∫ ‖𝓕f(ξ)‖² ‖ν̂_N(ξ)‖² dξ = ∫ ‖𝓕f(ξ)‖² (¼ + 4π²ξ²) S_N(ξ) dξ`.

Every compact-source Gram energy of the field is therefore the spectral energy of `ν_N` seen through
the window `|𝓕f|²`.  A source of width `w` has its window concentrated on `|ξ| ≲ 1/w`; probing the
band `|ξ| ≤ √x` that carries the square-root barrier requires sources of width `≲ 1/√x`: the
bi-scale uncertainty of probes.  Since `ν_N` is a real measure, `‖ν̂_N(−ξ)‖ = ‖ν̂_N(ξ)‖`.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators CompactlySupported Real FourierTransform ComplexConjugate

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

noncomputable section
set_option autoImplicit false

/-! ## Conjugation symmetry of the spectral density -/

theorem pairingC_conj (N : ℕ) (h : ℝ → ℂ) :
    pairingC N (fun s => conj (h s)) = conj (pairingC N h) := by
  unfold pairingC
  rw [map_sub, map_sum, ← integral_conj]
  congr 1
  · exact Finset.sum_congr rfl fun n _ => by rw [map_mul, Complex.conj_ofReal]
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show (polarDensity x : ℂ) * conj (h x) = conj ((polarDensity x : ℂ) * h x)
    rw [map_mul, Complex.conj_ofReal]

theorem frequencyCharacter_neg (ξ t : ℝ) :
    frequencyCharacter (-ξ) t = conj (frequencyCharacter ξ t) := by
  unfold frequencyCharacter
  rw [← Complex.exp_conj, map_mul, Complex.conj_I, map_neg, Complex.conj_ofReal]
  congr 1
  push_cast; ring

theorem frequencyCharacter_neg_arg (ξ s : ℝ) :
    frequencyCharacter ξ (-s) = frequencyCharacter (-ξ) s := by
  unfold frequencyCharacter
  congr 1
  push_cast; ring

theorem fourierPairing_neg (N : ℕ) (ξ : ℝ) :
    fourierPairing N (-ξ) = conj (fourierPairing N ξ) := by
  unfold fourierPairing
  rw [← pairingC_conj]
  exact congrArg (pairingC N) (funext fun s => frequencyCharacter_neg ξ s)

theorem norm_fourierPairing_neg (N : ℕ) (ξ : ℝ) :
    ‖fourierPairing N (-ξ)‖ = ‖fourierPairing N ξ‖ := by
  rw [fourierPairing_neg, Complex.norm_conj]

theorem spectralDensity_neg (N : ℕ) (ξ : ℝ) : spectralDensity N (-ξ) = spectralDensity N ξ := by
  unfold spectralDensity
  rw [norm_fourierPairing_neg]
  congr 1; ring

/-! ## The Fourier transform of a translated compact source -/

theorem integral_frequencyCharacter_mul_shift (f : C_c(ℝ, ℝ)) (ξ s : ℝ) :
    (∫ u, frequencyCharacter ξ u * (f (u + s) : ℂ)) =
      frequencyCharacter ξ (-s) * 𝓕 (fun u => (f u : ℂ)) ξ := by
  have e : ∀ v, frequencyCharacter ξ (-s) * (frequencyCharacter ξ v * (f v : ℂ)) =
      frequencyCharacter ξ (v - s) * (f v : ℂ) := by
    intro v
    rw [sub_eq_add_neg, frequencyCharacter_add]; ring
  rw [fourierTransform_eq_integral_exp, ← integral_const_mul]
  symm
  calc (∫ v, frequencyCharacter ξ (-s) *
        (Complex.exp (-(2 * π * v * ξ : ℝ) * Complex.I) * (f v : ℂ)))
      = ∫ v, frequencyCharacter ξ (v - s) * (f v : ℂ) :=
        integral_congr_ae (Eventually.of_forall fun v => e v)
    _ = ∫ u, frequencyCharacter ξ (u + s - s) * (f (u + s) : ℂ) :=
        (integral_add_right_eq_self (μ := volume)
          (fun v => frequencyCharacter ξ (v - s) * (f v : ℂ)) s).symm
    _ = ∫ u, frequencyCharacter ξ u * (f (u + s) : ℂ) := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        show frequencyCharacter ξ (u + s - s) * (f (u + s) : ℂ) =
          frequencyCharacter ξ u * (f (u + s) : ℂ)
        rw [add_sub_cancel_right]

/-! ## The Fourier transform of the signed packet -/

/-- **`𝓕(signedSource f N)(ξ) = 𝓕f(ξ) · ν̂_N(−ξ)`.** -/
theorem fourier_signedSource (f : C_c(ℝ, ℝ)) (N : ℕ) (ξ : ℝ) :
    𝓕 (fun u => (signedSource f N u : ℂ)) ξ =
      𝓕 (fun u => (f u : ℂ)) ξ * fourierPairing N (-ξ) := by
  obtain ⟨R, hR0, hR⟩ := f.hasCompactSupport.exists_pos_le_norm
  obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  -- the source windowed in the pairing variable
  set W : ℝ → ℝ → ℝ := fun u s => f (u + s) * (Icc (0 : ℝ) (cutoff N)).indicator (fun _ => (1 : ℝ)) s
    with hWdef
  have hW : ∀ u, ∀ s ∈ Icc (0 : ℝ) (cutoff N), W u s = f (u + s) := fun u s hs => by
    simp [hWdef, Set.indicator_of_mem hs]
  have hWm : Measurable (Function.uncurry W) :=
    (f.continuous.measurable.comp (measurable_fst.add measurable_snd)).mul
      ((measurable_const.indicator measurableSet_Icc).comp measurable_snd)
  have hFm : Measurable (Function.uncurry fun u s => frequencyCharacter ξ u * (W u s : ℂ)) :=
    ((measurable_frequencyCharacter ξ).comp measurable_fst).mul
      (Complex.measurable_ofReal.comp hWm)
  -- the majorant: the source translates live in `[−R−L, R]`
  have hbound : ∀ u s, ‖frequencyCharacter ξ u * (W u s : ℂ)‖ ≤
      |(Icc (-R - cutoff N) R).indicator (fun _ => (1 : ℝ)) u| * M := by
    intro u s
    rw [norm_mul, norm_frequencyCharacter, one_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hs : s ∈ Icc (0 : ℝ) (cutoff N)
    · rw [hW u s hs]
      by_cases hu : u ∈ Icc (-R - cutoff N) R
      · rw [Set.indicator_of_mem hu, abs_one, one_mul, ← Real.norm_eq_abs]
        exact hM (u + s)
      · have hf0 : f (u + s) = 0 := by
          apply hR
          rw [Real.norm_eq_abs]
          simp only [mem_Icc, not_and_or, not_le] at hu
          rcases hu with hu | hu
          · rw [abs_of_neg (by linarith [hs.2, hR0])]; linarith [hs.2]
          · rw [abs_of_pos (by linarith [hs.1, hR0])]; linarith [hs.1]
        rw [hf0, abs_zero]
        positivity
    · have : W u s = 0 := by simp [hWdef, Set.indicator_of_notMem hs]
      rw [this, abs_zero]
      positivity
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (-R - cutoff N) R) :=
    integrableOn_const measure_Icc_lt_top.ne (by simp)
  have hw : Integrable ((Icc (-R - cutoff N) R).indicator fun _ => (1 : ℝ)) :=
    hconst.integrable_indicator measurableSet_Icc
  have hswap := integral_pairingC_of_dominated N
    (fun u s => frequencyCharacter ξ u * (W u s : ℂ)) hFm hw hbound
  calc 𝓕 (fun u => (signedSource f N u : ℂ)) ξ
      = ∫ u, frequencyCharacter ξ u * (signedSource f N u : ℂ) :=
        fourierTransform_eq_integral_exp _ ξ
    _ = ∫ u, pairingC N fun s => frequencyCharacter ξ u * (W u s : ℂ) := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        show frequencyCharacter ξ u * (signedSource f N u : ℂ) =
          pairingC N fun s => frequencyCharacter ξ u * (W u s : ℂ)
        rw [pairingC_const_mul, pairingC_ofReal]
        congr 2
        show pairing N (fun s => f (u + s)) = pairing N fun s => W u s
        exact pairing_congr_window N fun s hs => (hW u s hs).symm
    _ = pairingC N fun s => ∫ u, frequencyCharacter ξ u * (W u s : ℂ) := hswap
    _ = pairingC N fun s => frequencyCharacter ξ (-s) * 𝓕 (fun u => (f u : ℂ)) ξ := by
        refine pairingC_congr_window N fun s hs => ?_
        rw [← integral_frequencyCharacter_mul_shift f ξ s]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        show frequencyCharacter ξ u * (W u s : ℂ) = frequencyCharacter ξ u * (f (u + s) : ℂ)
        rw [hW u s hs]
    _ = 𝓕 (fun u => (f u : ℂ)) ξ * fourierPairing N (-ξ) := by
        rw [pairingC_mul_const, mul_comm]
        unfold fourierPairing
        congr 1
        exact congrArg (pairingC N) (funext fun s => frequencyCharacter_neg_arg ξ s)

/-! ## Plancherel for the packet energy -/

theorem packetEnergy_eq_integral_norm_sq (f : C_c(ℝ, ℝ)) (N : ℕ) :
    packetEnergy f N = ∫ u, ‖(signedSource f N u : ℂ)‖ ^ 2 := by
  unfold packetEnergy autocorr
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show signedSource f N u * signedSource f N (u + 0) = ‖(signedSource f N u : ℂ)‖ ^ 2
  rw [add_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs, sq]

/-- **Plancherel form of the packet energy:** `packetEnergy f N = ∫ ‖𝓕f‖² ‖ν̂_N(−ξ)‖²`. -/
theorem packetEnergy_eq_integral_fourier_sq_neg (f : C_c(ℝ, ℝ)) (N : ℕ) :
    packetEnergy f N =
      ∫ ξ, ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2 * ‖fourierPairing N (-ξ)‖ ^ 2 := by
  have hSi : Integrable fun u => (signedSource f N u : ℂ) :=
    ((signedSource f N).continuous.integrable_of_hasCompactSupport
      (signedSource f N).hasCompactSupport).ofReal
  have hS2 : MemLp (fun u => (signedSource f N u : ℂ)) 2 := by
    rw [memLp_two_iff_integrable_sq_norm hSi.aestronglyMeasurable]
    refine (integrable_sq (signedSource f N).continuous
      (signedSource f N).hasCompactSupport).congr (Eventually.of_forall fun u => ?_)
    show signedSource f N u ^ 2 = ‖(signedSource f N u : ℂ)‖ ^ 2
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hP := GaloisForLFunctions.HTGeometry.integral_norm_sq_fourier hSi hS2
  rw [packetEnergy_eq_integral_norm_sq, ← hP]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  show ‖𝓕 (fun u => (signedSource f N u : ℂ)) ξ‖ ^ 2 =
    ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2 * ‖fourierPairing N (-ξ)‖ ^ 2
  rw [fourier_signedSource, norm_mul, mul_pow]

/-- **Plancherel form of the packet energy:** `packetEnergy f N = ∫ ‖𝓕f(ξ)‖² ‖ν̂_N(ξ)‖² dξ`. -/
theorem packetEnergy_eq_integral_fourier_sq (f : C_c(ℝ, ℝ)) (N : ℕ) :
    packetEnergy f N = ∫ ξ, ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2 * ‖fourierPairing N ξ‖ ^ 2 := by
  rw [packetEnergy_eq_integral_fourier_sq_neg]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  show ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2 * ‖fourierPairing N (-ξ)‖ ^ 2 =
    ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2 * ‖fourierPairing N ξ‖ ^ 2
  rw [norm_fourierPairing_neg]

/-- The packet energy as the spectral density weighted by `|𝓕f|² |s|²`. -/
theorem packetEnergy_eq_integral_fourier_mul_spectralDensity (f : C_c(ℝ, ℝ)) (N : ℕ) :
    packetEnergy f N =
      ∫ ξ, ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2 * (1 / 4 + (2 * π * ξ) ^ 2) * spectralDensity N ξ := by
  rw [packetEnergy_eq_integral_fourier_sq]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  show ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2 * ‖fourierPairing N ξ‖ ^ 2 =
    ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ^ 2 * (1 / 4 + (2 * π * ξ) ^ 2) * spectralDensity N ξ
  unfold spectralDensity
  have : (0 : ℝ) < 1 / 4 + (2 * π * ξ) ^ 2 := by positivity
  field_simp

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
