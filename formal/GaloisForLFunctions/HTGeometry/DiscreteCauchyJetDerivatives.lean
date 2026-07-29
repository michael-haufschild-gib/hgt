import GaloisForLFunctions.HTGeometry.DiscreteCauchyJetPacket
import GaloisForLFunctions.HTGeometry.GammaDifferentialFE
import GaloisForLFunctions.HTGeometry.DifferentiallyAlgebraicInvariance

/-!
# Normalized Cauchy packets are the actual differential jets

The `m`-th derivative of `(t-z)⁻¹` is `m! (t-z)⁻¹^(m+1)`.  Local uniform summability of every
Cauchy power permits termwise iterated differentiation of a discrete Herglotz series throughout the
upper half-plane.  Consequently the packet in `DiscreteCauchyJetPacket` is exactly the actual
differential jet divided by the nonzero factorial diagonal.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Filter

/-- The iterated derivative of the real-pole Cauchy kernel, in the sign convention used by the
Herglotz source. -/
theorem iteratedDeriv_realCauchyKernel
    (t : ℝ) (m : ℕ) (z : ℂ) (hz : 0 < z.im) :
    iteratedDeriv m (fun w : ℂ => ((t : ℂ) - w)⁻¹) z =
      (m.factorial : ℂ) * (((t : ℂ) - z)⁻¹) ^ (m + 1) := by
  have hne : z + (-(t : ℂ)) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact (ne_of_gt hz) him
  have hfun : (fun w : ℂ => ((t : ℂ) - w)⁻¹) =
      fun w => (-1 : ℂ) * (w + (-(t : ℂ)))⁻¹ := by
    funext w
    have htw : (t : ℂ) - w = -(w + (-(t : ℂ))) := by ring
    rw [htw, inv_neg]
    ring
  rw [hfun, congrFun (iteratedDeriv_const_mul_field (-1 : ℂ)
    (fun w : ℂ => (w + (-(t : ℂ)))⁻¹) m) z]
  rw [iteratedDeriv_inv_add_const (-(t : ℂ)) m z hne]
  have hbase : (t : ℂ) - z = -(z + (-(t : ℂ))) := by ring
  change (-1 : ℂ) * ((-1) ^ m * (m.factorial : ℂ) *
      ((z - (t : ℂ)) ^ (m + 1))⁻¹) =
    (m.factorial : ℂ) * (((t : ℂ) - z)⁻¹) ^ (m + 1)
  rw [← inv_pow]
  rw [hbase, inv_neg, neg_pow]
  ring

/-- Every fixed Cauchy-power series is locally uniformly summable on the upper half-plane when its
coefficients are absolutely summable. -/
theorem summableLocallyUniformlyOn_discreteCauchyPower
    {κ : Type*} (support : κ → ℝ) (coeff : κ → ℂ)
    (hcoeff : Summable fun p => ‖coeff p‖) (m : ℕ) :
    SummableLocallyUniformlyOn
      (fun p z => coeff p * (((support p : ℂ) - z)⁻¹) ^ (m + 1)) upperHalfPlane := by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  intro z hz
  have hzpos : 0 < z.im := hz
  refine ⟨Metric.ball z (z.im / 2),
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z (half_pos hzpos)), ?_⟩
  apply HasSumUniformlyOn.of_norm_le_summable
    (hcoeff.mul_right (((z.im / 2)⁻¹) ^ (m + 1)))
  intro p x hx
  have hnorm : ‖x - z‖ < z.im / 2 := by
    simpa [dist_eq_norm] using (Metric.mem_ball.mp hx)
  have himnorm : |(x - z).im| ≤ ‖x - z‖ := Complex.abs_im_le_norm _
  have habs : |x.im - z.im| < z.im / 2 := by
    exact lt_of_le_of_lt (by simpa [Complex.sub_im] using himnorm) hnorm
  have hxim : z.im / 2 < x.im := by
    rw [abs_lt] at habs
    linarith
  have hxim0 : 0 < x.im := (half_pos hzpos).trans hxim
  have hden : z.im / 2 ≤ ‖(support p : ℂ) - x‖ := by
    have hi : x.im ≤ ‖(support p : ℂ) - x‖ := by
      have h1 : |((support p : ℂ) - x).im| ≤ ‖(support p : ℂ) - x‖ :=
        Complex.abs_im_le_norm _
      have h2 : ((support p : ℂ) - x).im = -x.im := by simp [Complex.sub_im]
      rw [h2, abs_neg, abs_of_pos hxim0] at h1
      exact h1
    exact hxim.le.trans hi
  rw [norm_mul, norm_pow, norm_inv]
  gcongr

/-- The iterated derivative within the upper half-plane of one weighted Cauchy term. -/
theorem iteratedDerivWithin_discreteCauchyTerm
    (t w : ℝ) (m : ℕ) (z : ℂ) (hz : z ∈ upperHalfPlane) :
    iteratedDerivWithin m (fun x : ℂ => (w : ℂ) * ((t : ℂ) - x)⁻¹)
      upperHalfPlane z =
      (w : ℂ) * (m.factorial : ℂ) * (((t : ℂ) - z)⁻¹) ^ (m + 1) := by
  rw [iteratedDerivWithin_of_isOpen isOpen_upperHalfPlane hz]
  rw [congrFun (iteratedDeriv_const_mul_field (w : ℂ)
    (fun x : ℂ => ((t : ℂ) - x)⁻¹) m) z]
  rw [iteratedDeriv_realCauchyKernel t m z hz]
  ring

/-- Termwise iterated differentiation of an absolutely summable discrete Herglotz series. -/
theorem iteratedDeriv_discreteHerglotz_eq_factorial_mul
    {κ : Type*} (support weight : κ → ℝ)
    (hweight : Summable fun p => ‖(weight p : ℂ)‖)
    (m : ℕ) (z : ℂ) (hz : z ∈ upperHalfPlane) :
    iteratedDeriv m (discreteHerglotz support weight) z =
      (m.factorial : ℂ) *
        ∑' p, (weight p : ℂ) * (((support p : ℂ) - z)⁻¹) ^ (m + 1) := by
  rw [← iteratedDerivWithin_of_isOpen isOpen_upperHalfPlane hz]
  change iteratedDerivWithin m
    (fun x => ∑' p, (weight p : ℂ) * ((support p : ℂ) - x)⁻¹)
    upperHalfPlane z = _
  rw [iteratedDerivWithin_tsum m isOpen_upperHalfPlane hz]
  · calc
      (∑' p, iteratedDerivWithin m
          (fun x : ℂ => (weight p : ℂ) * ((support p : ℂ) - x)⁻¹)
          upperHalfPlane z) =
          ∑' p, (weight p : ℂ) * (m.factorial : ℂ) *
            (((support p : ℂ) - z)⁻¹) ^ (m + 1) := by
        apply tsum_congr
        intro p
        exact iteratedDerivWithin_discreteCauchyTerm (support p) (weight p) m z hz
      _ = (m.factorial : ℂ) *
          ∑' p, (weight p : ℂ) * (((support p : ℂ) - z)⁻¹) ^ (m + 1) := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro p
        ring
  · intro t ht
    exact summable_discreteHerglotz_term support weight t ht hweight
  · intro k hk hkm
    have hcoeff : Summable fun p => ‖(weight p : ℂ) * (k.factorial : ℂ)‖ := by
      simpa [norm_mul] using hweight.mul_right ‖(k.factorial : ℂ)‖
    apply SummableLocallyUniformlyOn_congr
      (f := fun p z => (weight p : ℂ) * (k.factorial : ℂ) *
        (((support p : ℂ) - z)⁻¹) ^ (k + 1))
    · intro p z hz
      exact (iteratedDerivWithin_discreteCauchyTerm (support p) (weight p) k z hz).symm
    · exact summableLocallyUniformlyOn_discreteCauchyPower support
        (fun p => (weight p : ℂ) * (k.factorial : ℂ)) hcoeff k
  · intro p k r hkm hr
    have hEq : iteratedDerivWithin k
        (fun x : ℂ => (weight p : ℂ) * ((support p : ℂ) - x)⁻¹)
        upperHalfPlane =ᶠ[nhds r]
        fun x => (weight p : ℂ) * (k.factorial : ℂ) *
          (((support p : ℂ) - x)⁻¹) ^ (k + 1) := by
      filter_upwards [isOpen_upperHalfPlane.mem_nhds hr] with x hx
      exact iteratedDerivWithin_discreteCauchyTerm (support p) (weight p) k x hx
    apply hEq.differentiableAt_iff.mpr
    have hne : (support p : ℂ) - r ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      exact (ne_of_gt hr) him
    exact ((((differentiableAt_const (c := (support p : ℂ))).sub differentiableAt_id).inv hne).pow
      (k + 1)).const_mul _

/-- The normalized prime-log Cauchy packet is exactly the actual differential jet divided by the
factorial diagonal. -/
theorem iteratedDeriv_primeLogHerglotz_eq_factorial_mul_packet
    {ι : Type*} (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (nodes : ι → ℂ) (hupper : ∀ i, 0 < (nodes i).im) (orders : ι → ℕ)
    (s : Σ i, Fin (orders i)) :
    iteratedDeriv s.2.1 (primeLogHerglotz u) (nodes s.1) =
      (s.2.1.factorial : ℂ) * primeLogCauchyJetPacket u nodes orders s := by
  have h := iteratedDeriv_discreteHerglotz_eq_factorial_mul
    primeLogSupport (primeDyadicWeight u)
    (summable_norm_primeDyadicWeight u C hu) s.2.1 (nodes s.1) (hupper s.1)
  have hsource :
      primeLogHerglotz u =
        discreteHerglotz primeLogSupport (primeDyadicWeight u) := by
    funext z
    rfl
  rw [hsource]
  simpa [primeLogCauchyJetPacket, discreteCauchyJetPacket, cauchyJetColumn] using h

end GaloisForLFunctions.HTGeometry
