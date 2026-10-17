import GaloisForLFunctions.BiScaleUncertainty.CoherentSourceProjection

/-!
# An exact finite filter for coherent hyperbolic leakage

Actual source support cuts off the centered pairing exactly. A finite symmetric
hyperbolic filter therefore produces the coherent multiplier slope without an
infinite tail estimate. Its full signed Schur energy controls the odd moment
and transfers to the full plastic functional.
-/

open MeasureTheory Set Filter
open scoped BigOperators CompactlySupported Topology

namespace GaloisForLFunctions.BiScaleUncertainty.LocalCoherentFilter
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open CenteredHyperbolicGram ProjectedHyperbolicGram ArithmeticMultiplierCollisions
open DyadicMultiplierFrame DyadicHyperbolicMoment HyperbolicRay SourceLattice SignedCoherentMoment
noncomputable section

private theorem exists_cutoff (f : C_c(ℝ, ℝ)) :
    ∃ L : ℕ, 2 * multiplierSourceRadius f < (L : ℝ) * Real.log 2 := by
  have hd := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  obtain ⟨L, hL⟩ := exists_nat_gt (2 * multiplierSourceRadius f / Real.log 2)
  exact ⟨L, (div_lt_iff₀ hd).mp hL⟩

/-- Intrinsic finite cutoff, chosen from the actual source support. -/
def sourceCutoff (f : C_c(ℝ, ℝ)) : ℕ := Nat.find (exists_cutoff f)

theorem sourceCutoff_gap (f : C_c(ℝ, ℝ)) :
    2 * multiplierSourceRadius f < (sourceCutoff f : ℝ) * Real.log 2 :=
  Nat.find_spec (exists_cutoff f)

private theorem source_product_zero (f : C_c(ℝ, ℝ)) (x : ℝ)
    (hx : 2 * multiplierSourceRadius f < |x|) (u : ℝ) : f u * f (u + x) = 0 := by
  by_cases hu : f u = 0
  · simp [hu]
  by_cases hv : f (u + x) = 0
  · simp [hv]
  have hbu := abs_le.mp (abs_le_multiplierSourceRadius f u hu)
  have hbv := abs_le.mp (abs_le_multiplierSourceRadius f (u + x) hv)
  have hh : |x| ≤ 2 * multiplierSourceRadius f := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith only [hx, hh]

private theorem cutoff_lag (f : C_c(ℝ, ℝ)) (k : ℕ) (hk : sourceCutoff f ≤ k) :
    2 * multiplierSourceRadius f < |((k : ℝ) + 1) * Real.log 2| := by
  have hd := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hkc : (sourceCutoff f : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  rw [abs_of_nonneg (by positivity)]
  have hl := sourceCutoff_gap f
  nlinarith only [hl, hkc, hd]

private theorem correlations_zero (f : C_c(ℝ, ℝ)) (k : ℕ) (hk : sourceCutoff f ≤ k) :
    autocorr f (((k : ℝ) + 1) * Real.log 2) = 0 ∧
      autocorr (sinhCompact (1 / 2) f) (((k : ℝ) + 1) * Real.log 2) = 0 := by
  have hz := source_product_zero f _ (cutoff_lag f k hk)
  constructor
  · unfold autocorr
    simp_rw [hz]
    simp
  · unfold autocorr
    have he (u : ℝ) : sinhCompact (1 / 2) f u *
        sinhCompact (1 / 2) f (u + ((k : ℝ) + 1) * Real.log 2) = 0 := by
      change (_ * f u) * (_ * f _) = 0
      calc
        _ = (Real.sinh ((1 / 2 : ℝ) * u) *
            Real.sinh ((1 / 2 : ℝ) * (u + ((k : ℝ) + 1) * Real.log 2))) *
              (f u * f (u + ((k : ℝ) + 1) * Real.log 2)) := by ring
        _ = 0 := by rw [hz, mul_zero]
    simp_rw [he]
    simp

/-- Exact zero truncation error in the centered pairing outside the constructed window. -/
theorem odd_centered_pairing_zero (f : C_c(ℝ, ℝ)) (k : ℕ)
    (hk : sourceCutoff (oddCompactSource f) ≤ k) :
    (∫ u, centeredSource (oddCompactSource f) (1 / 2)
      (sourceMean (oddCompactSource f) (1 / 2)) u *
        oddCompactSource f (u + ((k : ℝ) + 1) * Real.log 2)) = 0 := by
  rw [odd_centered_cross_identity]
  have hz := correlations_zero (oddCompactSource f) k hk
  rw [hz.1, hz.2]
  ring

private def nodes (L : ℕ) : Finset (ℕ ⊕ ℕ) := (Finset.range L).disjSum (Finset.range L)
private def shifts : ℕ ⊕ ℕ → ℝ := Sum.elim
  (fun k => ((k : ℝ) + 1) * Real.log 2) (fun k => -(((k : ℝ) + 1) * Real.log 2))
private def weights : ℕ ⊕ ℕ → ℝ := Sum.elim
  (fun k => 1 / (2 * Real.cosh ((((k : ℝ) + 1) * Real.log 2) / 2)))
  (fun k => 1 / (2 * Real.cosh ((((k : ℝ) + 1) * Real.log 2) / 2)))

/-- Explicit finite symmetric source filter, with all signed interactions retained. -/
def sourceFilter (f : C_c(ℝ, ℝ)) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => ∑ i ∈ nodes (sourceCutoff f), weights i * f (u + shifts i),
    continuous_finsetSum _ fun i _ =>
      continuous_const.mul (f.continuous.comp (continuous_add_const _))⟩, by
    have hs := HasCompactSupport.finset_sum (s := nodes (sourceCutoff f))
      (f := fun i u => weights i * f (u + shifts i))
      (fun i _ => (hasCompactSupport_comp_add f.hasCompactSupport _).mul_left)
    have he : (∑ i ∈ nodes (sourceCutoff f), fun u => weights i * f (u + shifts i)) =
        (fun u => ∑ i ∈ nodes (sourceCutoff f), weights i * f (u + shifts i)) := by
      funext u
      simp only [Finset.sum_apply]
    rwa [he] at hs⟩

theorem sourceFilter_apply (f : C_c(ℝ, ℝ)) (u : ℝ) :
    sourceFilter f u = ∑ k ∈ Finset.range (sourceCutoff f),
      (f (u + ((k : ℝ) + 1) * Real.log 2) + f (u - ((k : ℝ) + 1) * Real.log 2)) /
        (2 * Real.cosh ((((k : ℝ) + 1) * Real.log 2) / 2)) := by
  change (∑ i ∈ nodes (sourceCutoff f), weights i * f (u + shifts i)) = _
  simp only [nodes, Finset.sum_disjSum, weights, shifts, Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by rw [sub_eq_add_neg]; ring

/-- Covariance of the finite filter with its original source. -/
def filterCovariance (f : C_c(ℝ, ℝ)) : ℝ := ∫ u, f u * sourceFilter f u

/-- The finite filter with its exact source component removed. -/
def orthogonalFilter (f : C_c(ℝ, ℝ)) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => sourceFilter f u - filterCovariance f / autocorr f 0 * f u,
    (sourceFilter f).continuous.sub (continuous_const.mul f.continuous)⟩,
    (sourceFilter f).hasCompactSupport.sub f.hasCompactSupport.mul_left⟩

/-- Full signed finite-filter Schur energy. -/
def filterEnergy (f : C_c(ℝ, ℝ)) : ℝ :=
  autocorr (sourceFilter f) 0 - filterCovariance f ^ 2 / autocorr f 0

private theorem pairing_filter (f q : C_c(ℝ, ℝ)) :
    (∫ u, q u * sourceFilter f u) =
      ∑ i ∈ nodes (sourceCutoff f), weights i * (∫ u, q u * f (u + shifts i)) := by
  have hi (i : ℕ ⊕ ℕ) : Integrable (fun u => weights i * (q u * f (u + shifts i))) :=
    ((q.continuous.mul (f.continuous.comp (continuous_add_const _))).integrable_of_hasCompactSupport
      q.hasCompactSupport.mul_right).const_mul _
  have he : (fun u => q u * sourceFilter f u) =
      fun u => ∑ i ∈ nodes (sourceCutoff f), weights i * (q u * f (u + shifts i)) := by
    funext u
    change q u * (∑ i ∈ nodes (sourceCutoff f), weights i * f (u + shifts i)) = _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [he, integral_finsetSum _ (fun i _ => hi i)]
  exact Finset.sum_congr rfl fun _ _ => integral_const_mul _ _

/-- Source covariance agrees exactly with the previous limiting coefficient. -/
theorem filterCovariance_eq_covarianceMass (f : C_c(ℝ, ℝ)) :
    filterCovariance f = CoherentSourceProjection.covarianceMass f := by
  have hs : filterCovariance f = ∑ k ∈ Finset.range (sourceCutoff f),
      autocorr f (((k : ℝ) + 1) * Real.log 2) / Real.cosh ((((k : ℝ) + 1) * Real.log 2) / 2) := by
    unfold filterCovariance
    rw [pairing_filter]
    simp only [nodes, Finset.sum_disjSum, weights, shifts, Sum.elim_inl, Sum.elim_inr]
    change (∑ k ∈ Finset.range (sourceCutoff f), _ * autocorr f (((k : ℝ) + 1) * Real.log 2)) +
      (∑ k ∈ Finset.range (sourceCutoff f), _ * autocorr f (-(((k : ℝ) + 1) * Real.log 2))) = _
    simp_rw [autocorr_neg]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hs]
  unfold CoherentSourceProjection.covarianceMass
  change _ = ∑' k : ℕ, sourceSample f ((k : ℤ) + 1) /
    Real.cosh ((((k : ℝ) + 1) * Real.log 2) / 2)
  simp only [sourceSample, Int.cast_add, Int.cast_natCast, Int.cast_one]
  symm
  apply tsum_eq_sum
  intro k hk
  rw [(correlations_zero f k (by have := Finset.mem_range.not.mp hk; omega)).1, zero_div]

/-- Explicit finite signed Gram formula: both difference and reflected-sum lags survive. -/
theorem sourceFilter_energy_eq (f : C_c(ℝ, ℝ)) :
    autocorr (sourceFilter f) 0 =
      ∑ k ∈ Finset.range (sourceCutoff f), ∑ l ∈ Finset.range (sourceCutoff f),
        (autocorr f (((l : ℝ) - k) * Real.log 2) +
          autocorr f (((l : ℝ) + k + 2) * Real.log 2)) /
        (2 * Real.cosh ((((k : ℝ) + 1) * Real.log 2) / 2) *
          Real.cosh ((((l : ℝ) + 1) * Real.log 2) / 2)) := by
  have he : autocorr (sourceFilter f) 0 =
      translationGramEnergy f (nodes (sourceCutoff f)) weights shifts := by
    rw [← integral_sq_eq_autocorr_zero, translationGramEnergy_eq_integral]
    rfl
  rw [he]
  unfold translationGramEnergy
  simp only [nodes, Finset.sum_disjSum, weights, shifts, Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  have h1 : ((l : ℝ) + 1) * Real.log 2 - ((k : ℝ) + 1) * Real.log 2 =
      ((l : ℝ) - k) * Real.log 2 := by ring
  have h2 : -(((l : ℝ) + 1) * Real.log 2) - ((k : ℝ) + 1) * Real.log 2 =
      -(((l : ℝ) + k + 2) * Real.log 2) := by ring
  have h3 : ((l : ℝ) + 1) * Real.log 2 - -(((k : ℝ) + 1) * Real.log 2) =
      ((l : ℝ) + k + 2) * Real.log 2 := by ring
  have h4 : -(((l : ℝ) + 1) * Real.log 2) - -(((k : ℝ) + 1) * Real.log 2) =
      -(((l : ℝ) - k) * Real.log 2) := by ring
  rw [h1, h2, h3, h4, autocorr_neg, autocorr_neg]
  ring

private theorem pairing_orthogonal (f q : C_c(ℝ, ℝ)) :
    (∫ u, q u * orthogonalFilter f u) =
      (∫ u, q u * sourceFilter f u) - filterCovariance f / autocorr f 0 * (∫ u, q u * f u) := by
  have hp : Integrable (fun u => q u * sourceFilter f u) :=
    (q.continuous.mul (sourceFilter f).continuous).integrable_of_hasCompactSupport q.hasCompactSupport.mul_right
  have hf : Integrable (fun u => q u * f u) :=
    (q.continuous.mul f.continuous).integrable_of_hasCompactSupport q.hasCompactSupport.mul_right
  have he : (fun u => q u * orthogonalFilter f u) =
      fun u => q u * sourceFilter f u - filterCovariance f / autocorr f 0 * (q u * f u) := by
    funext u
    change q u * (_ - _ * _) = _
    ring
  rw [he, integral_sub hp (hf.const_mul _), integral_const_mul]

/-- The Schur price is the energy of a constructed compact source, including zero energy. -/
theorem orthogonalFilter_energy (f : C_c(ℝ, ℝ)) :
    autocorr (orthogonalFilter f) 0 = filterEnergy f := by
  have hc (p q : C_c(ℝ, ℝ)) : (∫ u, p u * q u) = ∫ u, q u * p u := by simp only [mul_comm]
  have hs (p : C_c(ℝ, ℝ)) : (∫ u, p u * p u) = autocorr p 0 := by simp only [autocorr, add_zero]
  rw [← hs, pairing_orthogonal, hc (orthogonalFilter f), pairing_orthogonal,
    hc (orthogonalFilter f), pairing_orthogonal, hs, hs, hc (sourceFilter f) f]
  change _ = autocorr (sourceFilter f) 0 - filterCovariance f ^ 2 / autocorr f 0
  change autocorr (sourceFilter f) 0 - filterCovariance f / autocorr f 0 * filterCovariance f -
    filterCovariance f / autocorr f 0 * (filterCovariance f - filterCovariance f / autocorr f 0 * autocorr f 0) = _
  by_cases hR : autocorr f 0 = 0
  · simp [hR]
  · field_simp
    ring

theorem filterEnergy_nonneg (f : C_c(ℝ, ℝ)) : 0 ≤ filterEnergy f := by
  rw [← orthogonalFilter_energy]
  exact autocorr_zero_nonneg _

/-- Exact source orthogonality, with the zero-energy case discharged from Cauchy--Schwarz. -/
theorem orthogonalFilter_source_pairing (f : C_c(ℝ, ℝ)) :
    (∫ u, f u * orthogonalFilter f u) = 0 := by
  have hs : (∫ u, f u * f u) = autocorr f 0 := by simp only [autocorr, add_zero]
  rw [pairing_orthogonal, hs]
  change filterCovariance f - filterCovariance f / autocorr f 0 * autocorr f 0 = 0
  by_cases hR : autocorr f 0 = 0
  · have h := HTGeometry.sq_integral_mul_le (f := (f : ℝ → ℝ)) (g := (sourceFilter f : ℝ → ℝ))
      f.continuous.aestronglyMeasurable (sourceFilter f).continuous.aestronglyMeasurable
      (integrable_sq f.continuous f.hasCompactSupport)
      (integrable_sq (sourceFilter f).continuous (sourceFilter f).hasCompactSupport)
    rw [integral_sq_eq_autocorr_zero, integral_sq_eq_autocorr_zero, hR, zero_mul] at h
    change filterCovariance f ^ 2 ≤ 0 at h
    have hK : filterCovariance f = 0 := by nlinarith only [h, sq_nonneg (filterCovariance f)]
    simp [hK]
  · field_simp
    ring

private theorem centered_filter_bound (f : C_c(ℝ, ℝ)) :
    (∫ u, centeredSource f (1 / 2) (sourceMean f (1 / 2)) u * sourceFilter f u) ≤
      Real.sqrt (autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 * filterEnergy f) := by
  let q := centeredSource f (1 / 2) (sourceMean f (1 / 2))
  let p := orthogonalFilter f
  have hp : (∫ u, q u * p u) = ∫ u, q u * sourceFilter f u := by
    dsimp [p]
    rw [pairing_orthogonal, centered_source_orthogonal, mul_zero, sub_zero]
  have h := HTGeometry.sq_integral_mul_le (f := (q : ℝ → ℝ)) (g := (p : ℝ → ℝ))
    q.continuous.aestronglyMeasurable p.continuous.aestronglyMeasurable
    (integrable_sq q.continuous q.hasCompactSupport) (integrable_sq p.continuous p.hasCompactSupport)
  rw [integral_sq_eq_autocorr_zero, integral_sq_eq_autocorr_zero, hp, orthogonalFilter_energy] at h
  exact (le_abs_self _).trans (by rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt h)

private theorem correction_sum (f : C_c(ℝ, ℝ)) :
    signedCorrectionMass f = 2 * ∑ k ∈ Finset.range (sourceCutoff f), correctionSample f ((k : ℤ) + 1) := by
  rw [signedCorrectionMass_eq_positive]
  congr 1
  apply tsum_eq_sum
  intro k hk
  have hz := (correlations_zero f k (by have := Finset.mem_range.not.mp hk; omega)).1
  simp only [correctionSample, sourceSample, Int.cast_add, Int.cast_natCast, Int.cast_one]
  rw [hz]
  simp

/-- The finite filter reproduces the complete signed coherent multiplier slope exactly. -/
theorem odd_filter_pairing_identity (f : C_c(ℝ, ℝ)) :
    signedCorrectionMass (oddCompactSource f) +
      (∫ u, centeredSource (oddCompactSource f) (1 / 2) (sourceMean (oddCompactSource f) (1 / 2)) u *
        sourceFilter (oddCompactSource f) u) =
      2 * ∑ k ∈ Finset.range (sourceCutoff (oddCompactSource f)),
        autocorr (sinhCompact (1 / 2) (oddCompactSource f)) (((k : ℝ) + 1) * Real.log 2) := by
  rw [pairing_filter, correction_sum]
  simp only [nodes, Finset.sum_disjSum, shifts, weights, Sum.elim_inl, Sum.elim_inr]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [odd_centered_cross_identity, odd_centered_cross_identity]
  simp only [mul_neg, Real.cosh_neg, autocorr_neg]
  simp only [correctionSample, sourceSample, Int.cast_add, Int.cast_natCast, Int.cast_one]
  rw [if_neg (by omega : (k : ℤ) + 1 ≠ 0)]
  rw [show (1 / 2 : ℝ) * (((k : ℝ) + 1) * Real.log 2) = (((k : ℝ) + 1) * Real.log 2) / 2 by ring]
  field_simp [(Real.cosh_pos ((((k : ℝ) + 1) * Real.log 2) / 2)).ne']
  ring

private theorem even_chain_sum (k : ℤ → ℝ) (heven : ∀ z, k (-z) = k z) (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), k ((j : ℤ) - (i : ℤ))) =
      ((N : ℝ) + 1) * k 0 + 2 * ∑ m ∈ Finset.range N, ((N : ℝ) - m) * k ((m : ℤ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hi (i : ℕ) :
        (∑ j ∈ Finset.range (N + 1 + 1), k ((j : ℤ) - (i : ℤ))) =
          (∑ j ∈ Finset.range (N + 1), k ((j : ℤ) - (i : ℤ))) +
            k (((N + 1 : ℕ) : ℤ) - (i : ℤ)) := Finset.sum_range_succ _ _
    have hc : (∑ i ∈ Finset.range (N + 1), k (((N + 1 : ℕ) : ℤ) - (i : ℤ))) =
        ∑ m ∈ Finset.range (N + 1), k ((m : ℤ) + 1) := by
      rw [← Finset.sum_range_reflect (fun m => k ((m : ℤ) + 1)) (N + 1)]
      apply Finset.sum_congr rfl
      intro i hi
      have := Finset.mem_range.mp hi
      congr 1
      omega
    have hr : (∑ j ∈ Finset.range (N + 1), k ((j : ℤ) - ((N + 1 : ℕ) : ℤ))) =
        ∑ i ∈ Finset.range (N + 1), k (((N + 1 : ℕ) : ℤ) - (i : ℤ)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show (j : ℤ) - ((N + 1 : ℕ) : ℤ) = -(((N + 1 : ℕ) : ℤ) - (j : ℤ)) by ring, heven]
    have ht : (∑ m ∈ Finset.range (N + 1), (((N + 1 : ℕ) : ℝ) - (m : ℝ)) * k ((m : ℤ) + 1)) =
        (∑ m ∈ Finset.range N, ((N : ℝ) - (m : ℝ)) * k ((m : ℤ) + 1)) +
          ∑ m ∈ Finset.range (N + 1), k ((m : ℤ) + 1) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ (f := fun m => k ((m : ℤ) + 1))]
      simp only [Nat.cast_add, Nat.cast_one]
      have he (m : ℕ) : ((N : ℝ) + 1 - (m : ℝ)) * k ((m : ℤ) + 1) =
          ((N : ℝ) - (m : ℝ)) * k ((m : ℤ) + 1) + k ((m : ℤ) + 1) := by ring
      simp_rw [he]
      rw [Finset.sum_add_distrib]
      ring
    change (∑ i ∈ Finset.range (N + 1 + 1), ∑ j ∈ Finset.range (N + 1 + 1),
      k ((j : ℤ) - (i : ℤ))) = _
    rw [Finset.sum_range_succ]
    simp_rw [hi]
    rw [Finset.sum_add_distrib, sub_self, hr, hc, ih, ht]
    push_cast
    ring

private theorem gram_triangle (g : C_c(ℝ, ℝ)) (N : ℕ) :
    translationGramEnergy g (Finset.range (N + 1)) (fun _ => 1) (chainNode (Real.log 2)) =
      ((N : ℝ) + 1) * autocorr g 0 +
        2 * ∑ k ∈ Finset.range N, ((N : ℝ) - k) * autocorr g (((k : ℝ) + 1) * Real.log 2) := by
  have h := even_chain_sum (sourceSample g) (sourceSample_neg g) N
  simpa only [sourceSample, Int.cast_sub, Int.cast_natCast, Int.cast_add, Int.cast_one,
    Int.cast_zero, zero_mul, sub_mul, translationGramEnergy, one_mul, chainNode] using h

private theorem gram_affine (g : C_c(ℝ, ℝ)) (M N : ℕ) (hMN : M ≤ N)
    (hz : ∀ k : ℕ, M ≤ k → autocorr g (((k : ℝ) + 1) * Real.log 2) = 0) :
    translationGramEnergy g (Finset.range (N + 1)) (fun _ => 1) (chainNode (Real.log 2)) =
      ((N : ℝ) + 1) * (autocorr g 0 +
        2 * ∑ k ∈ Finset.range M, autocorr g (((k : ℝ) + 1) * Real.log 2)) -
        2 * ∑ k ∈ Finset.range M, ((k : ℝ) + 1) * autocorr g (((k : ℝ) + 1) * Real.log 2) := by
  have hs : (∑ k ∈ Finset.range N, ((N : ℝ) - k) * autocorr g (((k : ℝ) + 1) * Real.log 2)) =
      ∑ k ∈ Finset.range M, ((N : ℝ) - k) * autocorr g (((k : ℝ) + 1) * Real.log 2) := by
    symm
    apply Finset.sum_subset (by
      intro k hk
      exact Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans_le hMN))
    intro k _ hk
    rw [hz k (by have := Finset.mem_range.not.mp hk; omega), mul_zero]
  rw [gram_triangle, hs]
  have ht : ((N : ℝ) + 1) * (2 * ∑ k ∈ Finset.range M, autocorr g (((k : ℝ) + 1) * Real.log 2)) -
      2 * ∑ k ∈ Finset.range M, ((k : ℝ) + 1) * autocorr g (((k : ℝ) + 1) * Real.log 2) =
      2 * ∑ k ∈ Finset.range M, ((N : ℝ) - k) * autocorr g (((k : ℝ) + 1) * Real.log 2) := by
    rw [← mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  linarith only [ht]

/-- Fixed, signed boundary intercept of the coherent multiplier Gram. -/
def filterBoundary (f : C_c(ℝ, ℝ)) : ℝ :=
  2 * ∑ k ∈ Finset.range (sourceCutoff f),
    ((k : ℝ) + 1) * autocorr (sinhCompact (1 / 2) f) (((k : ℝ) + 1) * Real.log 2)

/-- Exact coherent growth law produced by the finite filter at every length beyond its cutoff. -/
theorem odd_coherentGram_eq_filter (f : C_c(ℝ, ℝ)) (K : ℕ) :
    translationGramEnergy (sinhCompact (1 / 2) (oddCompactSource f))
      (Finset.range (sourceCutoff (oddCompactSource f) + K + 1)) (fun _ => 1) (chainNode (Real.log 2)) =
      ((sourceCutoff (oddCompactSource f) : ℝ) + K + 1) *
        (autocorr (sinhCompact (1 / 2) (oddCompactSource f)) 0 + signedCorrectionMass (oddCompactSource f) +
          (∫ u, centeredSource (oddCompactSource f) (1 / 2) (sourceMean (oddCompactSource f) (1 / 2)) u *
            sourceFilter (oddCompactSource f) u)) - filterBoundary (oddCompactSource f) := by
  rw [gram_affine _ (sourceCutoff (oddCompactSource f)) _ (by omega)
    (fun k hk => (correlations_zero (oddCompactSource f) k hk).2), ← odd_filter_pairing_identity]
  simp only [Nat.cast_add, filterBoundary]
  ring

/-- Moment price retaining the finite producer's complete signed Schur energy. -/
def localBudget (f : C_c(ℝ, ℝ)) : ℝ :=
  autocorr (sinhCompact (1 / 2) f) 0 + signedCorrectionMass f +
    Real.sqrt (autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 * filterEnergy f)

private theorem integral_sq_le_affine (g : C_c(ℝ, ℝ)) (C D : ℝ) (M : ℕ)
    (hframe : ∀ N : ℕ, M ≤ N → translationGramEnergy g (Finset.range (N + 1))
      (fun _ => 1) (chainNode (Real.log 2)) ≤ C * ((N : ℝ) + 1) + D) :
    (∫ u, g u) ^ 2 ≤ Real.log 2 * C := by
  by_contra hn
  let A := (∫ u, g u) ^ 2
  let B := 2 * (multiplierSourceRadius g + 1)
  let d := Real.log 2
  let K := (B - d) * C + d * D
  let J := (B - d) * D
  have heps : 0 < A - d * C := by dsimp [A, d]; linarith only [hn]
  obtain ⟨N, hN⟩ := exists_nat_gt (max (M : ℝ) ((|K| + |J|) / (A - d * C)))
  have hMN : M ≤ N := by
    have := (le_max_left (M : ℝ) ((|K| + |J|) / (A - d * C))).trans_lt hN
    exact_mod_cast this.le
  have hlarge := (div_lt_iff₀ heps).mp
    ((le_max_right (M : ℝ) ((|K| + |J|) / (A - d * C))).trans_lt hN)
  have hh := (integral_sq_le_chain_gram g N).trans
    (mul_le_mul_of_nonneg_left (hframe N hMN) (chainSpan_pos g N).le)
  have hm : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
    linarith only [hN0]
  have hmpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hpoly : (A - d * C) * ((N : ℝ) + 1) ^ 2 ≤ K * ((N : ℝ) + 1) + J := by
    dsimp [A, B, d, K, J]
    unfold chainSpan at hh
    nlinarith only [hh]
  have hK := mul_le_mul_of_nonneg_right (le_abs_self K) hmpos.le
  have hJ : J ≤ |J| * ((N : ℝ) + 1) :=
    (le_abs_self J).trans (by nlinarith only [hm, abs_nonneg J])
  have hlin : (A - d * C) * ((N : ℝ) + 1) ≤ |K| + |J| :=
    le_of_mul_le_mul_right (by nlinarith only [hpoly, hK, hJ]) hmpos
  nlinarith only [hlin, hlarge, heps]

/-- Exact signed-pairing endpoint before applying the finite producer's norm bound. -/
theorem odd_moment_sq_le_filter_pairing (f : C_c(ℝ, ℝ)) :
    (∫ u, oddCompactSource f u * Real.sinh (u / 2)) ^ 2 ≤ Real.log 2 *
      (autocorr (sinhCompact (1 / 2) (oddCompactSource f)) 0 + signedCorrectionMass (oddCompactSource f) +
        (∫ u, centeredSource (oddCompactSource f) (1 / 2) (sourceMean (oddCompactSource f) (1 / 2)) u *
          sourceFilter (oddCompactSource f) u)) := by
  rw [← integral_sinhCompact_eq_moment]
  let F := oddCompactSource f
  apply integral_sq_le_affine _ _ (-filterBoundary F) (sourceCutoff F)
  intro N hN
  rw [gram_affine _ (sourceCutoff F) N hN (fun k hk => (correlations_zero F k hk).2)]
  have he := odd_filter_pairing_identity f
  change _ = 2 * ∑ k ∈ Finset.range (sourceCutoff F), _ at he
  rw [← he]
  unfold filterBoundary
  dsimp only [F]
  nlinarith only []

/-- Unconditional odd moment bound from the actual finite source producer. -/
theorem odd_moment_sq_le_localBudget (f : C_c(ℝ, ℝ)) :
    (∫ u, oddCompactSource f u * Real.sinh (u / 2)) ^ 2 ≤ Real.log 2 * localBudget (oddCompactSource f) := by
  have hm := odd_moment_sq_le_filter_pairing f
  have hd := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hh := mul_le_mul_of_nonneg_left (centered_filter_bound (oddCompactSource f)) hd
  unfold localBudget
  nlinarith only [hm, hh]

theorem odd_localBudget_nonneg (f : C_c(ℝ, ℝ)) : 0 ≤ localBudget (oddCompactSource f) := by
  have h := (sq_nonneg _).trans (odd_moment_sq_le_localBudget f)
  have hd := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  nlinarith only [h, hd]

/-- Full plastic transfer with finite signed source Gram data and no analytic premise. -/
theorem odd_plasticCrossover_ge_localBudget (f : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ y in (0 : ℝ)..Real.log 2, optimizedCollar (oddCompactSource f) N (-y)) +
      plasticRemainderEnergy (oddCompactSource f) - 2 * Real.log 2 * localBudget (oddCompactSource f) ≤
        plasticCrossover (oddCompactSource f) := by
  have hp := odd_plasticCrossover_ge_optimized f N
  have hm := odd_moment_sq_le_localBudget f
  nlinarith only [hp, hm]

end
end GaloisForLFunctions.BiScaleUncertainty.LocalCoherentFilter
