import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarPacket

/-!
# Cancellation-sensitive signed Chebyshev transport

The actual signed packet energy replaces the squared unsigned-mass budget.
Compact-window Fubini transfers the packet's increment estimate through the
annular average. One origin-energy budget then controls all prime and polar
terms together, with the exact reciprocal archimedean penalty.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
noncomputable section
set_option autoImplicit false

private theorem continuous_pairing_parametric (F : ℝ → ℝ → ℝ)
    (hF : Continuous (Function.uncurry F)) (N : ℕ) :
    Continuous (fun y => pairing N (fun t => F t y)) := by
  apply Continuous.sub
  · exact continuous_finsetSum _ fun n _ => continuous_const.mul
      (hF.comp (continuous_const.prodMk continuous_id))
  · exact continuous_parametric_integral_of_continuous
      ((continuous_polarDensity.comp continuous_snd).mul
        (hF.comp (continuous_snd.prodMk continuous_fst))) isCompact_Icc

private theorem integral_integral_Icc_swap (F : ℝ → ℝ → ℝ)
    (hF : Continuous (Function.uncurry F)) (a b c d : ℝ) :
    (∫ x in Icc a b, ∫ y in Icc c d, F x y) =
      ∫ y in Icc c d, ∫ x in Icc a b, F x y := by
  apply integral_integral_swap
  rw [Measure.prod_restrict]
  exact hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

private theorem integral_pairing (F : ℝ → ℝ → ℝ)
    (hF : Continuous (Function.uncurry F)) (N : ℕ) (a b : ℝ) :
    (∫ y in Icc a b, pairing N (fun t => F t y)) =
      pairing N (fun t => ∫ y in Icc a b, F t y) := by
  have hs : Continuous (fun y => ∑ n ∈ Finset.Icc 1 (N+2), primeWeight n * F (Real.log n) y) :=
    continuous_finsetSum _ fun n _ => continuous_const.mul
      (hF.comp (continuous_const.prodMk continuous_id))
  have hp : Continuous (fun y => ∫ t in Icc 0 (cutoff N), polarDensity t * F t y) :=
    continuous_parametric_integral_of_continuous
      ((continuous_polarDensity.comp continuous_snd).mul
        (hF.comp (continuous_snd.prodMk continuous_fst))) isCompact_Icc
  have hn (n : ℕ) : IntegrableOn (fun y => primeWeight n * F (Real.log n) y) (Icc a b) :=
    (continuous_const.mul (hF.comp (continuous_const.prodMk continuous_id))).integrableOn_Icc
  simp only [pairing]
  rw [integral_sub hs.integrableOn_Icc hp.integrableOn_Icc,
    integral_finsetSum _ (fun n _ => hn n)]
  simp_rw [integral_const_mul]
  congr 1
  rw [integral_integral_Icc_swap (fun y t => polarDensity t * F t y)
    ((continuous_polarDensity.comp continuous_snd).mul
      (hF.comp (continuous_snd.prodMk continuous_fst)))]
  simp_rw [integral_const_mul]

private theorem pairing_sub (N : ℕ) (H K : ℝ → ℝ) (hH : Continuous H) (hK : Continuous K) :
    pairing N (fun t => H t - K t) = pairing N H - pairing N K := by
  have hiH : IntegrableOn (fun t => polarDensity t * H t) (Icc 0 (cutoff N)) :=
    (continuous_polarDensity.mul hH).integrableOn_Icc
  have hiK : IntegrableOn (fun t => polarDensity t * K t) (Icc 0 (cutoff N)) :=
    (continuous_polarDensity.mul hK).integrableOn_Icc
  simp only [pairing, mul_sub, Finset.sum_sub_distrib, integral_sub hiH hiK]
  ring

private theorem pairing_div (N : ℕ) (H : ℝ → ℝ) (d : ℝ) :
    pairing N (fun t => H t / d) = pairing N H / d := by
  simp only [pairing, ← mul_div_assoc, integral_div, ← Finset.sum_div, sub_div]

/-- Exact interchange of signed pairing and annular source transport. -/
theorem pairing_average_sub_eq (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    pairing N (correlationAverage f a b) - pairing N (autocorr f) =
      (∫ y in Real.exp a..Real.exp a + Real.exp b,
        pairing N (fun t => autocorr f (t + y) - autocorr f t)) / Real.exp b := by
  have hh := continuous_autocorr_compact f
  have hab : Real.exp a ≤ Real.exp a + Real.exp b := le_add_of_nonneg_right (Real.exp_pos b).le
  have he (t : ℝ) : correlationAverage f a b t - autocorr f t =
      (∫ y in Icc (Real.exp a) (Real.exp a + Real.exp b),
        autocorr f (t + y) - autocorr f t) / Real.exp b := by
    rw [correlationAverage, annularAverage_eq_shift,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    have hi : IntervalIntegrable (fun y => autocorr f (t + y)) volume
        (Real.exp a) (Real.exp a + Real.exp b) :=
      (hh.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
    have hk : IntervalIntegrable (fun _y : ℝ => autocorr f t) volume
        (Real.exp a) (Real.exp a + Real.exp b) := intervalIntegrable_const
    rw [intervalIntegral.integral_sub hi hk, intervalIntegral.integral_const]
    dsimp
    field_simp
    ring
  rw [← pairing_sub N _ _ (continuous_correlationAverage f a b) hh]
  simp_rw [he]
  rw [pairing_div, ← integral_pairing (fun t y => autocorr f (t + y) - autocorr f t)
    ((hh.comp (continuous_fst.add continuous_snd)).sub (hh.comp continuous_fst)),
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]

/-- Cancellation-sensitive uniform annular transport cost. -/
def packetTransportCost (f : C_c(ℝ, ℝ)) (N : ℕ) (a b : ℝ) : ℝ :=
  (∫ y in Real.exp a..Real.exp a + Real.exp b,
    Real.sqrt (2 * packetEnergy f N * (autocorr f 0 - autocorr f y))) / Real.exp b

/-- The cancellation-sensitive cost is always bounded by the earlier unsigned cost. -/
theorem packetTransportCost_le_mass_cost (f : C_c(ℝ, ℝ)) (N : ℕ) (a b : ℝ) :
    packetTransportCost f N a b ≤ mass N * correlationTransportCost f a b := by
  have hh := continuous_autocorr_compact f
  have hab : Real.exp a ≤ Real.exp a + Real.exp b := le_add_of_nonneg_right (Real.exp_pos b).le
  have hpoint (y : ℝ) :
      Real.sqrt (2 * packetEnergy f N * (autocorr f 0 - autocorr f y)) ≤
        mass N * Real.sqrt (2 * autocorr f 0 * (autocorr f 0 - autocorr f y)) := by
    calc
      _ ≤ Real.sqrt (2 * (mass N ^ 2 * autocorr f 0) * (autocorr f 0 - autocorr f y)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (packetEnergy_le_mass_sq f N) (by norm_num))
          (autocorr_sub_nonneg f.hasCompactSupport f.continuous y))
      _ = Real.sqrt (mass N ^ 2 * (2 * autocorr f 0 * (autocorr f 0 - autocorr f y))) := by
        congr 1
        ring
      _ = _ := by
        rw [Real.sqrt_mul (sq_nonneg (mass N)), Real.sqrt_sq_eq_abs,
          abs_of_nonneg (mass_nonneg N)]
  unfold packetTransportCost correlationTransportCost
  calc
    _ ≤ (∫ y in Real.exp a..Real.exp a + Real.exp b,
        mass N * Real.sqrt (2 * autocorr f 0 * (autocorr f 0 - autocorr f y))) / Real.exp b := by
      apply div_le_div_of_nonneg_right _ (Real.exp_pos b).le
      exact intervalIntegral.integral_mono_on hab
        ((continuous_const.mul (continuous_const.sub hh)).sqrt.intervalIntegrable _ _)
        ((continuous_const.mul ((continuous_const.mul (continuous_const.sub hh)).sqrt)).intervalIntegrable _ _)
        (fun y _ => hpoint y)
    _ = _ := by rw [intervalIntegral.integral_const_mul]; ring

/-- The exact Chebyshev work is reached while retaining signed packet cancellation. -/
theorem abs_pairing_sub_chebyshevWork_le_packet (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    |pairing N (autocorr f) - chebyshevWork f a b N| ≤ packetTransportCost f N a b := by
  have he : pairing N (correlationAverage f a b) = chebyshevWork f a b N :=
    pairing_correlationAverage_eq f a b N
  rw [← he, abs_sub_comm, pairing_average_sub_eq, abs_div, abs_of_pos (Real.exp_pos b)]
  apply div_le_div_of_nonneg_right _ (Real.exp_pos b).le
  have hab : Real.exp a ≤ Real.exp a + Real.exp b := le_add_of_nonneg_right (Real.exp_pos b).le
  have hh := continuous_autocorr_compact f
  have hc := continuous_pairing_parametric (fun t y => autocorr f (t + y) - autocorr f t)
    ((hh.comp (continuous_fst.add continuous_snd)).sub (hh.comp continuous_fst)) N
  calc
    _ ≤ ∫ y in Real.exp a..Real.exp a + Real.exp b,
        |pairing N (fun t => autocorr f (t + y) - autocorr f t)| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ _ := intervalIntegral.integral_mono_on hab (hc.abs.intervalIntegrable _ _)
      ((continuous_const.mul (continuous_const.sub hh)).sqrt.intervalIntegrable _ _)
      (fun y _ => abs_pairing_increment_le_packetEnergy f N y)

/-- One origin-energy budget, paid by the full signed Gram energy rather than
by a separate unsigned estimate for each atom and each polar contribution. -/
theorem packetTransportCost_le_levy (f : C_c(ℝ, ℝ)) (N : ℕ) (a b c : ℝ) :
    packetTransportCost f N a b ≤
      Real.exp c * (∫ y in Real.exp a..Real.exp a + Real.exp b,
        (autocorr f 0 - autocorr f y) * archLevySinhWeight y) +
      packetEnergy f N / (2 * Real.exp c * Real.exp b ^ 2) *
        ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y := by
  have hab : Real.exp a ≤ Real.exp a + Real.exp b := le_add_of_nonneg_right (Real.exp_pos b).le
  have hh := continuous_autocorr_compact f
  have hw : ContinuousOn archLevySinhWeight (Icc (Real.exp a) (Real.exp a + Real.exp b)) :=
    continuousOn_archLevySinhWeight fun _ hy => (Real.exp_pos a).trans_le hy.1
  have hi : IntervalIntegrable (fun y => (autocorr f 0 - autocorr f y) *
      archLevySinhWeight y) volume (Real.exp a) (Real.exp a + Real.exp b) :=
    ((continuousOn_const.sub hh.continuousOn).mul hw).intervalIntegrable_of_Icc hab
  have hc : Continuous (fun y : ℝ => Real.exp (-y / 2) * Real.sinh y) := by fun_prop
  have hj := hc.intervalIntegrable (μ := volume) (Real.exp a) (Real.exp a + Real.exp b)
  have hm : (∫ y in Real.exp a..Real.exp a + Real.exp b,
      Real.sqrt (2 * packetEnergy f N * (autocorr f 0 - autocorr f y)) / Real.exp b) ≤
      ∫ y in Real.exp a..Real.exp a + Real.exp b,
        Real.exp c * ((autocorr f 0 - autocorr f y) * archLevySinhWeight y) +
          packetEnergy f N / (2 * Real.exp c * Real.exp b ^ 2) *
            (Real.exp (-y / 2) * Real.sinh y) := by
    apply intervalIntegral.integral_mono_on hab
      (((continuous_const.mul (continuous_const.sub hh)).sqrt.div_const _).intervalIntegrable _ _)
      ((hi.const_mul _).add (hj.const_mul _))
    intro y hy
    have hW := archLevySinhWeight_pos ((Real.exp_pos a).trans_le hy.1)
    have hY := signed_collar_young_bound (w := 1 / Real.exp b)
      (mul_pos (Real.exp_pos c) hW) (packetEnergy_nonneg f N)
      (autocorr_sub_nonneg f.hasCompactSupport f.continuous y)
    have hp : (1 / Real.exp b) ^ 2 / (2 * (Real.exp c * archLevySinhWeight y)) *
        packetEnergy f N = packetEnergy f N / (2 * Real.exp c * Real.exp b ^ 2) *
          (Real.exp (-y / 2) * Real.sinh y) := by
      rw [← inv_archLevySinhWeight_eq]
      ring
    rw [hp] at hY
    dsimp only [Pi.mul_apply, Pi.sub_apply]
    convert hY using 1 <;> ring
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hi.const_mul _)
    (hj.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hm
  exact hm

/-- Direct signed arithmetic coupling with a cancellation-sensitive archimedean penalty. -/
theorem abs_pairing_sub_chebyshevWork_le_packet_levy (f : C_c(ℝ, ℝ))
    (a b c : ℝ) (N : ℕ) :
    |pairing N (autocorr f) - chebyshevWork f a b N| ≤
      Real.exp c * (∫ y in Real.exp a..Real.exp a + Real.exp b,
        (autocorr f 0 - autocorr f y) * archLevySinhWeight y) +
      packetEnergy f N / (2 * Real.exp c * Real.exp b ^ 2) *
        ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y :=
  (abs_pairing_sub_chebyshevWork_le_packet f a b N).trans
    (packetTransportCost_le_levy f N a b c)

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
