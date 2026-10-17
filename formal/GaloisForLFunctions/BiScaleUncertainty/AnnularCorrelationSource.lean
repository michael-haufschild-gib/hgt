import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarPacket

/-!
# The coherent source behind annular correlation transport

Backward source averaging realizes the regularized correlation as an actual
mixed source pairing. Its norm is the full double collar Gram integral.
Pairing this source with the signed prime–polar packet gives exact Chebyshev work.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
noncomputable section
set_option autoImplicit false

private theorem source_bound (f : C_c(ℝ, ℝ)) :
    ∃ M : ℝ, 0 < M ∧ ∀ u, f u ≠ 0 → |u| ≤ M := by
  obtain ⟨M, hM, hb⟩ := f.hasCompactSupport.isCompact.isBounded.exists_pos_norm_le
  exact ⟨M, hM, fun u hu => by
    simpa only [Real.norm_eq_abs] using hb u (subset_closure hu)⟩

private theorem collar_support (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    HasCompactSupport (fun u =>
      (∫ y in Icc (Real.exp a) (Real.exp a + Real.exp b), f (u - y)) / Real.exp b) := by
  obtain ⟨M, _, hM⟩ := source_bound f
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc (-M) (M + Real.exp a + Real.exp b)))
  intro u hu
  by_contra hout
  have hz : (∫ y in Icc (Real.exp a) (Real.exp a + Real.exp b), f (u - y)) = 0 := by
    calc
      _ = ∫ _y in Icc (Real.exp a) (Real.exp a + Real.exp b), (0 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro y hy
        by_contra hn
        have hb := abs_le.mp (hM (u - y) hn)
        exact hout ⟨by linarith [Real.exp_pos a, hy.1], by linarith [hy.2]⟩
      _ = 0 := integral_zero _ _
  exact hu (by simp only [hz, zero_div])

/-- Average of the actual backward source translates over a positive annulus. -/
def collarSource (f : C_c(ℝ, ℝ)) (a b : ℝ) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u =>
    (∫ y in Icc (Real.exp a) (Real.exp a + Real.exp b), f (u - y)) / Real.exp b,
    (continuous_parametric_integral_of_continuous (f := fun u y : ℝ => f (u - y))
      (f.continuous.comp (continuous_fst.sub continuous_snd)) isCompact_Icc).div_const _⟩,
    collar_support f a b⟩

private theorem mixed_support (q f : C_c(ℝ, ℝ)) :
    HasCompactSupport (fun p : ℝ × ℝ => q p.1 * f (p.1 - p.2)) := by
  obtain ⟨M, _, hM⟩ := source_bound q
  obtain ⟨T, _, hT⟩ := source_bound f
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc.prod isCompact_Icc :
      IsCompact ((Icc (-M) M) ×ˢ (Icc (-M-T) (M+T))))
  intro p hp
  have hq : q p.1 ≠ 0 := by intro hz; simp [Function.mem_support, hz] at hp
  have hf : f (p.1 - p.2) ≠ 0 := by intro hz; simp [Function.mem_support, hz] at hp
  have hm := abs_le.mp (hM _ hq)
  have ht := abs_le.mp (hT _ hf)
  exact ⟨hm, ⟨by linarith, by linarith⟩⟩

/-- Actual compact supports justify the collar Fubini interchange. -/
theorem integral_mul_collarSource (q f : C_c(ℝ, ℝ)) (a b : ℝ) :
    (∫ u, q u * collarSource f a b u) =
      (∫ y in Icc (Real.exp a) (Real.exp a + Real.exp b),
        ∫ u, q u * f (u - y)) / Real.exp b := by
  calc
    _ = (∫ u, ∫ y in Icc (Real.exp a) (Real.exp a + Real.exp b),
        q u * f (u - y)) / Real.exp b := by
      change (∫ u, q u * ((∫ y in Icc (Real.exp a) (Real.exp a + Real.exp b),
        f (u - y)) / Real.exp b)) = _
      simp_rw [← mul_div_assoc, ← integral_const_mul]
      rw [integral_div]
    _ = _ := by
      congr 1
      exact integral_integral_swap_of_hasCompactSupport
        (f := fun u y : ℝ => q u * f (u - y))
        ((q.continuous.comp continuous_fst).mul
          (f.continuous.comp (continuous_fst.sub continuous_snd))) (mixed_support q f)

private def shiftSource (f : C_c(ℝ, ℝ)) (t : ℝ) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => f (u + t), f.continuous.comp (continuous_add_const t)⟩,
    hasCompactSupport_comp_add f.hasCompactSupport t⟩

private theorem mixed_shift (f : C_c(ℝ, ℝ)) (t y : ℝ) :
    (∫ u, shiftSource f t u * f (u - y)) = autocorr f (t + y) := by
  change (∫ u, f (u + t) * f (u - y)) = ∫ u, f u * f (u + (t + y))
  calc
    _ = ∫ u, f (u + (-y)) * f (u + (-y) + (t + y)) := by
      congr 1 with u
      rw [show u + (-y) + (t + y) = u + t by ring]
      simp only [sub_eq_add_neg, mul_comm]
    _ = _ := integral_add_right_eq_self (μ := volume)
      (fun u => f u * f (u + (t + y))) (-y)

/-- The averaged correlation is a mixed pairing, not an assumed autocorrelation. -/
theorem integral_collarSource_mul_shift (f : C_c(ℝ, ℝ)) (a b t : ℝ) :
    (∫ u, collarSource f a b u * f (u + t)) = correlationAverage f a b t := by
  calc
    _ = ∫ u, shiftSource f t u * collarSource f a b u := by
      congr 1 with u
      change collarSource f a b u * f (u + t) = f (u + t) * collarSource f a b u
      ring
    _ = _ := by
      rw [integral_mul_collarSource]
      simp_rw [mixed_shift]
      rw [correlationAverage, annularAverage_eq_shift,
        intervalIntegral.integral_of_le (le_add_of_nonneg_right (Real.exp_pos b).le),
        ← integral_Icc_eq_integral_Ioc]
      rfl

theorem integral_collarSource_mul_source (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    (∫ u, collarSource f a b u * f u) = correlationAverage f a b 0 := by
  simpa only [add_zero] using integral_collarSource_mul_shift f a b 0

/-- Energy of the whole collar, retaining correlations between its shifts. -/
def collarEnergy (f : C_c(ℝ, ℝ)) (a b : ℝ) : ℝ := autocorr (collarSource f a b) 0

theorem collarEnergy_nonneg (f : C_c(ℝ, ℝ)) (a b : ℝ) : 0 ≤ collarEnergy f a b :=
  autocorr_zero_nonneg _

theorem collarEnergy_eq_average (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    collarEnergy f a b =
      (∫ y in Real.exp a..Real.exp a + Real.exp b, correlationAverage f a b (-y)) / Real.exp b := by
  calc
    _ = ∫ u, collarSource f a b u * collarSource f a b u := by
      simp only [collarEnergy, autocorr, add_zero]
    _ = (∫ y in Icc (Real.exp a) (Real.exp a + Real.exp b),
        ∫ u, collarSource f a b u * f (u - y)) / Real.exp b :=
      integral_mul_collarSource _ _ _ _
    _ = _ := by
      simp_rw [sub_eq_add_neg, integral_collarSource_mul_shift]
      rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right (Real.exp_pos b).le),
        ← integral_Icc_eq_integral_Ioc]

/-- The exact double Gram integral of every pair of collar translates. -/
theorem collarEnergy_eq_double_average (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    collarEnergy f a b =
      (∫ y in Real.exp a..Real.exp a + Real.exp b,
        ∫ z in Real.exp a..Real.exp a + Real.exp b, autocorr f (z - y)) / Real.exp b ^ 2 := by
  rw [collarEnergy_eq_average]
  simp_rw [correlationAverage, annularAverage_eq_shift,
    show ∀ y z : ℝ, -y + z = z - y from fun y z => by ring]
  rw [intervalIntegral.integral_div, div_div]
  simp only [pow_two]
  rfl

private theorem average_le (F : ℝ → ℝ) (hF : Continuous F) (a b B : ℝ)
    (hB : ∀ y, F y ≤ B) :
    (∫ y in Real.exp a..Real.exp a + Real.exp b, F y) / Real.exp b ≤ B := by
  have hab : Real.exp a ≤ Real.exp a + Real.exp b :=
    le_add_of_nonneg_right (Real.exp_pos b).le
  calc
    _ ≤ (∫ _y in Real.exp a..Real.exp a + Real.exp b, B) / Real.exp b :=
      div_le_div_of_nonneg_right
        (intervalIntegral.integral_mono_on hab (hF.intervalIntegrable _ _)
          intervalIntegrable_const (fun y _ => hB y)) (Real.exp_pos b).le
    _ = B := by
      rw [intervalIntegral.integral_const]
      dsimp
      field_simp
      ring

theorem correlationAverage_le_origin (f : C_c(ℝ, ℝ)) (a b t : ℝ) :
    correlationAverage f a b t ≤ autocorr f 0 := by
  rw [correlationAverage, annularAverage_eq_shift]
  exact average_le _ ((continuous_autocorr_compact f).comp
    (continuous_const.add continuous_id)) a b _ fun y =>
    (le_abs_self _).trans (abs_autocorr_le_zero f.hasCompactSupport f.continuous (t+y))

/-- Coherent averaging cannot create source energy. -/
theorem collarEnergy_le_origin (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    collarEnergy f a b ≤ autocorr f 0 := by
  rw [collarEnergy_eq_average]
  exact average_le _ ((continuous_correlationAverage f a b).comp continuous_neg)
    a b _ fun y => correlationAverage_le_origin f a b (-y)

/-- Exact Chebyshev work is the covariance of two constructed compact sources. -/
theorem integral_collarSource_signedSource (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    (∫ u, collarSource f a b u * signedSource f N u) = chebyshevWork f a b N := by
  rw [integral_mul_signedSource]
  simp_rw [integral_collarSource_mul_shift]
  exact pairing_correlationAverage_eq f a b N

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
