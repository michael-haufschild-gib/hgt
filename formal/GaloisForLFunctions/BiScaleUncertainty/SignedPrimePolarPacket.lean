import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarCoupling

/-!
# The actual signed prime–polar translation packet

The continuum polar packet is constructed from each compact continuous source.
Its compact support and mixed Fubini identity require no analytic interface.
The squared norm of the resulting signed packet retains arithmetic–polar
cancellation and controls signed correlation increments.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
noncomputable section
set_option autoImplicit false

private theorem source_bound (f : C_c(ℝ, ℝ)) :
    ∃ B : ℝ, 0 < B ∧ ∀ u, f u ≠ 0 → |u| ≤ B := by
  obtain ⟨B, hB, hb⟩ := f.hasCompactSupport.isCompact.isBounded.exists_pos_norm_le
  exact ⟨B, hB, fun u hu => by
    simpa only [Real.norm_eq_abs] using hb u (subset_closure hu)⟩

private theorem polar_support (f : C_c(ℝ, ℝ)) (N : ℕ) :
    HasCompactSupport (fun u => ∫ t in Icc 0 (cutoff N), polarDensity t * f (u + t)) := by
  obtain ⟨B, _, hB⟩ := source_bound f
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc (-B - cutoff N) B))
  intro u hu
  by_contra hout
  have hz : (∫ t in Icc 0 (cutoff N), polarDensity t * f (u + t)) = 0 := by
    calc
      _ = ∫ _t in Icc 0 (cutoff N), (0 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro t ht
        have hf : f (u + t) = 0 := by
          by_contra hn
          have hb := abs_le.mp (hB (u + t) hn)
          exact hout ⟨by linarith [ht.2], by linarith [ht.1]⟩
        simp only [hf, mul_zero]
      _ = 0 := integral_zero _ _
  exact hu hz

/-- Continuum polar translates form an actual compact continuous source. -/
def polarSource (f : C_c(ℝ, ℝ)) (N : ℕ) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => ∫ t in Icc 0 (cutoff N), polarDensity t * f (u + t),
    continuous_parametric_integral_of_continuous
      ((continuous_polarDensity.comp continuous_snd).mul
        (f.continuous.comp (continuous_fst.add continuous_snd))) isCompact_Icc⟩,
    polar_support f N⟩

/-- All actual von Mangoldt atoms, including the harmless zero atom at n=1. -/
def atomicSource (f : C_c(ℝ, ℝ)) (N : ℕ) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => ∑ n ∈ Finset.Icc 1 (N+2), primeWeight n * f (u + Real.log n),
    continuous_finsetSum _ fun n _ =>
      continuous_const.mul (f.continuous.comp (continuous_add_const _))⟩, by
    have hs := HasCompactSupport.finset_sum (s := Finset.Icc 1 (N+2))
      (f := fun n u => primeWeight n * f (u + Real.log n))
      (fun n _ => (hasCompactSupport_comp_add f.hasCompactSupport (Real.log n)).mul_left)
    have he : (∑ n ∈ Finset.Icc 1 (N+2), fun u => primeWeight n * f (u + Real.log n)) =
        (fun u => ∑ n ∈ Finset.Icc 1 (N+2), primeWeight n * f (u + Real.log n)) := by
      funext u
      simp only [Finset.sum_apply]
    rwa [he] at hs⟩

/-- The signed packet is formed before taking its norm. -/
def signedSource (f : C_c(ℝ, ℝ)) (N : ℕ) : C_c(ℝ, ℝ) :=
  atomicSource f N - polarSource f N

/-- Full signed Gram energy, with prime–polar cancellation retained. -/
def packetEnergy (f : C_c(ℝ, ℝ)) (N : ℕ) : ℝ := autocorr (signedSource f N) 0

theorem packetEnergy_nonneg (f : C_c(ℝ, ℝ)) (N : ℕ) : 0 ≤ packetEnergy f N :=
  autocorr_zero_nonneg _

private theorem mixed_support (q f : C_c(ℝ, ℝ)) :
    HasCompactSupport (fun p : ℝ × ℝ => q p.1 * (polarDensity p.2 * f (p.1 + p.2))) := by
  obtain ⟨B, _, hB⟩ := source_bound q
  obtain ⟨C, _, hC⟩ := source_bound f
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc.prod isCompact_Icc :
      IsCompact ((Icc (-B) B) ×ˢ (Icc (-C-B) (C+B))))
  intro p hp
  have hq : q p.1 ≠ 0 := by intro hz; simp [Function.mem_support, hz] at hp
  have hf : f (p.1 + p.2) ≠ 0 := by intro hz; simp [Function.mem_support, hz] at hp
  have hb := abs_le.mp (hB _ hq)
  have hc := abs_le.mp (hC _ hf)
  exact ⟨hb, ⟨by linarith, by linarith⟩⟩

/-- Mixed Fubini is justified by the two actual source supports. -/
theorem integral_mul_polarSource (q f : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ u, q u * polarSource f N u) =
      ∫ t in Icc 0 (cutoff N), polarDensity t * (∫ u, q u * f (u + t)) := by
  calc
    _ = ∫ u, ∫ t in Icc 0 (cutoff N), q u * (polarDensity t * f (u + t)) := by
      congr 1 with u
      rw [integral_const_mul]
      rfl
    _ = ∫ t in Icc 0 (cutoff N), ∫ u, q u * (polarDensity t * f (u + t)) :=
      integral_integral_swap_of_hasCompactSupport
        ((q.continuous.comp continuous_fst).mul
          ((continuous_polarDensity.comp continuous_snd).mul
            (f.continuous.comp (continuous_fst.add continuous_snd)))) (mixed_support q f)
    _ = _ := by
      congr 1 with t
      simp_rw [show ∀ u, q u * (polarDensity t * f (u + t)) =
        polarDensity t * (q u * f (u + t)) from fun u => by ring]
      exact integral_const_mul _ _

private theorem integral_mul_atomicSource (q f : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ u, q u * atomicSource f N u) =
      ∑ n ∈ Finset.Icc 1 (N+2), primeWeight n * (∫ u, q u * f (u + Real.log n)) := by
  have hi (n : ℕ) : Integrable (fun u => primeWeight n * (q u * f (u + Real.log n))) :=
    ((q.continuous.mul (f.continuous.comp (continuous_add_const _))).integrable_of_hasCompactSupport
      q.hasCompactSupport.mul_right).const_mul _
  have he : (fun u => q u * atomicSource f N u) =
      fun u => ∑ n ∈ Finset.Icc 1 (N+2), primeWeight n * (q u * f (u + Real.log n)) := by
    funext u
    change q u * (∑ n ∈ Finset.Icc 1 (N+2), primeWeight n * f (u + Real.log n)) = _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [he, integral_finsetSum _ (fun n _ => hi n)]
  exact Finset.sum_congr rfl fun _ _ => integral_const_mul _ _

/-- The exact signed functional is a source pairing with the constructed packet. -/
theorem integral_mul_signedSource (q f : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ u, q u * signedSource f N u) =
      pairing N (fun t => ∫ u, q u * f (u + t)) := by
  have ha : Integrable (fun u => q u * atomicSource f N u) :=
    (q.continuous.mul (atomicSource f N).continuous).integrable_of_hasCompactSupport
    q.hasCompactSupport.mul_right
  have hp : Integrable (fun u => q u * polarSource f N u) :=
    (q.continuous.mul (polarSource f N).continuous).integrable_of_hasCompactSupport
    q.hasCompactSupport.mul_right
  change (∫ u, q u * (atomicSource f N u - polarSource f N u)) = _
  simp_rw [mul_sub]
  rw [integral_sub ha hp, integral_mul_atomicSource, integral_mul_polarSource]
  rfl

/-- Exact covariance against the original source, with every signed node retained. -/
theorem integral_source_signedSource (f : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ u, f u * signedSource f N u) = pairing N (autocorr f) :=
  integral_mul_signedSource f f N

/-- The original signed scalar pairing is bounded by the actual signed packet norm. -/
theorem pairing_sq_le_packetEnergy (f : C_c(ℝ, ℝ)) (N : ℕ) :
    pairing N (autocorr f) ^ 2 ≤ autocorr f 0 * packetEnergy f N := by
  have hs := HTGeometry.sq_integral_mul_le (f := (f : ℝ → ℝ))
    (g := (signedSource f N : ℝ → ℝ))
    f.continuous.aestronglyMeasurable (signedSource f N).continuous.aestronglyMeasurable
    (integrable_sq f.continuous f.hasCompactSupport)
    (integrable_sq (signedSource f N).continuous (signedSource f N).hasCompactSupport)
  rw [integral_source_signedSource, integral_sq_eq_autocorr_zero,
    integral_sq_eq_autocorr_zero] at hs
  exact hs

/-- Actual translated source chord; no source derivative is used. -/
private def sourceChord (f : C_c(ℝ, ℝ)) (y : ℝ) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => f (u + (-y)) - f u,
    (f.continuous.comp (continuous_add_const (-y))).sub f.continuous⟩,
    (hasCompactSupport_comp_add f.hasCompactSupport (-y)).sub f.hasCompactSupport⟩

private theorem mixed_sourceChord (f : C_c(ℝ, ℝ)) (y t : ℝ) :
    (∫ u, sourceChord f y u * f (u + t)) = autocorr f (t + y) - autocorr f t := by
  have hi₁ : Integrable (fun u => f (u + (-y)) * f (u + t)) :=
    ((f.continuous.comp (continuous_add_const (-y))).mul
    (f.continuous.comp (continuous_add_const t))).integrable_of_hasCompactSupport
      (hasCompactSupport_comp_add f.hasCompactSupport (-y)).mul_right
  have hi₂ := integrable_mul_shift (g := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport t
  change (∫ u, (f (u + (-y)) - f u) * f (u + t)) = _
  simp_rw [sub_mul]
  rw [integral_sub hi₁ hi₂]
  congr 1
  change (∫ u, f (u + (-y)) * f (u + t)) = ∫ u, f u * f (u + (t + y))
  calc
    _ = ∫ u, f (u + (-y)) * f (u + (-y) + (t + y)) := by
      congr 1 with u
      rw [show u + (-y) + (t + y) = u + t by ring]
    _ = _ := integral_add_right_eq_self (μ := volume) (fun u => f u * f (u + (t + y))) (-y)

/-- A single signed packet controls all correlation increments. -/
theorem pairing_increment_sq_le_packetEnergy (f : C_c(ℝ, ℝ)) (N : ℕ) (y : ℝ) :
    pairing N (fun t => autocorr f (t + y) - autocorr f t) ^ 2 ≤
      2 * packetEnergy f N * (autocorr f 0 - autocorr f y) := by
  have hs := HTGeometry.sq_integral_mul_le (f := (sourceChord f y : ℝ → ℝ))
    (g := (signedSource f N : ℝ → ℝ))
    (sourceChord f y).continuous.aestronglyMeasurable
    (signedSource f N).continuous.aestronglyMeasurable
    (integrable_sq (sourceChord f y).continuous (sourceChord f y).hasCompactSupport)
    (integrable_sq (signedSource f N).continuous (signedSource f N).hasCompactSupport)
  rw [integral_mul_signedSource, integral_sq_eq_autocorr_zero (signedSource f N)] at hs
  simp_rw [mixed_sourceChord] at hs
  have hn : (∫ u, sourceChord f y u ^ 2) = 2 * (autocorr f 0 - autocorr f y) := by
    change (∫ u, (f (u + (-y)) - f u) ^ 2) = _
    simpa only [add_zero, sub_zero, autocorr_neg] using
      integral_shift_sub_shift_sq f.hasCompactSupport f.continuous (-y) 0
  rw [hn] at hs
  calc
    _ ≤ _ := hs
    _ = _ := by unfold packetEnergy; ring

/-- Cancellation-sensitive Krein bound for the actual signed measure. -/
theorem abs_pairing_increment_le_packetEnergy (f : C_c(ℝ, ℝ)) (N : ℕ) (y : ℝ) :
    |pairing N (fun t => autocorr f (t + y) - autocorr f t)| ≤
      Real.sqrt (2 * packetEnergy f N * (autocorr f 0 - autocorr f y)) := by
  simpa only [Real.sqrt_sq_eq_abs] using
    Real.sqrt_le_sqrt (pairing_increment_sq_le_packetEnergy f N y)

private def translateSource (f : C_c(ℝ, ℝ)) (t : ℝ) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => f (u + t), f.continuous.comp (continuous_add_const t)⟩,
    hasCompactSupport_comp_add f.hasCompactSupport t⟩

private theorem mixed_translateSource (f : C_c(ℝ, ℝ)) (t s : ℝ) :
    (∫ u, translateSource f t u * f (u + s)) = autocorr f (s - t) := by
  change (∫ u, f (u + t) * f (u + s)) = ∫ u, f u * f (u + (s - t))
  calc
    _ = ∫ u, f (u + t) * f (u + t + (s - t)) := by
      congr 1 with u
      rw [show u + t + (s - t) = u + s by ring]
    _ = _ := integral_add_right_eq_self (μ := volume) (fun u => f u * f (u + (s - t))) t

/-- Exact Gram representation of the signed measure, including both mixed terms. -/
theorem packetEnergy_eq_iterated_pairing (f : C_c(ℝ, ℝ)) (N : ℕ) :
    packetEnergy f N = pairing N (fun t => pairing N (fun s => autocorr f (s - t))) := by
  calc
    _ = ∫ u, signedSource f N u * signedSource f N u := by
      simp only [packetEnergy, autocorr, add_zero]
    _ = pairing N (fun t => ∫ u, signedSource f N u * f (u + t)) :=
      integral_mul_signedSource (signedSource f N) f N
    _ = _ := by
      congr 1
      funext t
      calc
        _ = ∫ u, translateSource f t u * signedSource f N u := by
          congr 1 with u
          change signedSource f N u * f (u + t) = f (u + t) * signedSource f N u
          ring
        _ = pairing N (fun s => ∫ u, translateSource f t u * f (u + s)) :=
          integral_mul_signedSource (translateSource f t) f N
        _ = _ := by simp_rw [mixed_translateSource]

/-- Uniform absolute control for the literal signed functional. -/
theorem abs_pairing_le_mass_mul (N : ℕ) (H : ℝ → ℝ) (B : ℝ)
    (hb : ∀ t, |H t| ≤ B) : |pairing N H| ≤ mass N * B := by
  have hs : |∑ n ∈ Finset.Icc 1 (N+2), primeWeight n * H (Real.log n)| ≤
      (∑ n ∈ Finset.Icc 1 (N+2), primeWeight n) * B := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 (N+2), |primeWeight n * H (Real.log n)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 (N+2), primeWeight n * B := by
        apply Finset.sum_le_sum
        intro n _
        rw [abs_mul, abs_of_nonneg (primeWeight_nonneg n)]
        exact mul_le_mul_of_nonneg_left (hb _) (primeWeight_nonneg n)
      _ = _ := (Finset.sum_mul ..).symm
  have hi : |∫ x in Icc 0 (cutoff N), polarDensity x * H x| ≤
      (∫ x in Icc 0 (cutoff N), polarDensity x) * B := by
    have hmajor : IntegrableOn (fun x => polarDensity x * B) (Icc 0 (cutoff N)) :=
      (continuous_polarDensity.mul_const B).integrableOn_Icc
    have hbound := norm_integral_le_of_norm_le (f := fun x => polarDensity x * H x) hmajor
      (Filter.Eventually.of_forall fun x => ?_)
    · simpa only [Real.norm_eq_abs, integral_mul_const] using hbound
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (polarDensity_nonneg x)]
      exact mul_le_mul_of_nonneg_left (hb x) (polarDensity_nonneg x)
  calc
    _ ≤ |∑ n ∈ Finset.Icc 1 (N+2), primeWeight n * H (Real.log n)| +
        |∫ x in Icc 0 (cutoff N), polarDensity x * H x| := abs_sub _ _
    _ ≤ _ := by dsimp [mass]; nlinarith only [hs, hi]

/-- The signed packet budget never exceeds the unsigned-mass budget. -/
theorem packetEnergy_le_mass_sq (f : C_c(ℝ, ℝ)) (N : ℕ) :
    packetEnergy f N ≤ mass N ^ 2 * autocorr f 0 := by
  calc
    _ ≤ |packetEnergy f N| := le_abs_self _
    _ = |pairing N (fun t => pairing N (fun s => autocorr f (s - t)))| := by
      rw [packetEnergy_eq_iterated_pairing]
    _ ≤ mass N * (mass N * autocorr f 0) :=
      abs_pairing_le_mass_mul N _ _ fun t =>
        abs_pairing_le_mass_mul N _ _ fun s =>
          abs_autocorr_le_zero f.hasCompactSupport f.continuous (s - t)
    _ = _ := by ring

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
