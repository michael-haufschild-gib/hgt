import GaloisForLFunctions.HTGeometry.PrimaryFactorLogExpansion
import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGammaSharpness

/-!
# The regularized free energy of the infinite-order product

Each primary factor is, inside the unit disc, the exponential of the negative uncancelled logarithm
tail.  That tail is dominated by the `(g+1)`-power of its argument, so the tails of the whole
occupation spectrum form a summable family whenever the nome family is `(g+1)`-summable.

Since the exponential carries convergent sums to convergent products, the infinite-order product is
the exponential of the negative summed tails: the regularized free energy is the sum of the local
free energies, with no rearrangement or interchange used.
-/

namespace HTGeometry

open Filter Topology
open scoped BigOperators

/-- The exponential carries a convergent sum to a convergent product. -/
theorem hasProd_cexp {ι : Type*} {w : ι → ℂ} {s : ℂ} (h : HasSum w s) :
    HasProd (fun i => Complex.exp (w i)) (Complex.exp s) := by
  have hlim : Tendsto (fun F : Finset ι => Complex.exp (∑ i ∈ F, w i)) atTop
      (𝓝 (Complex.exp s)) := (Complex.continuous_exp.tendsto s).comp h
  refine hlim.congr fun F => ?_
  rw [Complex.exp_sum]

/-- **The logarithm tail is dominated by the leading power.** -/
theorem norm_primaryLogTail_le (g : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖primaryLogTail g z‖ ≤ ‖z‖ ^ (g + 1) / (((g : ℝ) + 1) * (1 - ‖z‖)) := by
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hd : (0 : ℝ) < (g : ℝ) + 1 := by positivity
  have hone : (0 : ℝ) < 1 - ‖z‖ := by linarith
  have hterm : ∀ m : ℕ, ‖z ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℂ)‖
      ≤ ‖z‖ ^ (g + 1) / ((g : ℝ) + 1) * ‖z‖ ^ m := by
    intro m
    have hcast : ((m + (g + 1) : ℕ) : ℝ) = (m : ℝ) + ((g : ℝ) + 1) := by push_cast; ring
    have hge : (g : ℝ) + 1 ≤ ((m + (g + 1) : ℕ) : ℝ) := by
      rw [hcast]
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hpos : (0 : ℝ) < ((m + (g + 1) : ℕ) : ℝ) := lt_of_lt_of_le hd hge
    rw [norm_div, norm_pow, Complex.norm_natCast]
    rw [div_le_iff₀ hpos]
    have hnn : (0 : ℝ) ≤ ‖z‖ ^ (g + 1) * ‖z‖ ^ m := by positivity
    have hsplit : ‖z‖ ^ (m + (g + 1)) = ‖z‖ ^ (g + 1) * ‖z‖ ^ m := by
      rw [pow_add]
      ring
    rw [hsplit]
    have hcoef : ‖z‖ ^ (g + 1) / ((g : ℝ) + 1) * ‖z‖ ^ m * ((m + (g + 1) : ℕ) : ℝ)
        = (‖z‖ ^ (g + 1) * ‖z‖ ^ m) * (((m + (g + 1) : ℕ) : ℝ) / ((g : ℝ) + 1)) := by
      field_simp
    rw [hcoef]
    have hfac : (1 : ℝ) ≤ ((m + (g + 1) : ℕ) : ℝ) / ((g : ℝ) + 1) := by
      rw [le_div_iff₀ hd]
      linarith
    nlinarith
  have hgeom : Summable (fun m : ℕ => ‖z‖ ^ (g + 1) / ((g : ℝ) + 1) * ‖z‖ ^ m) :=
    (summable_geometric_of_lt_one hz0 hz).mul_left _
  have hnormsum : Summable (fun m : ℕ => ‖z ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hterm hgeom
  calc ‖primaryLogTail g z‖
      ≤ ∑' m : ℕ, ‖z ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℂ)‖ :=
        norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' m : ℕ, ‖z‖ ^ (g + 1) / ((g : ℝ) + 1) * ‖z‖ ^ m :=
        Summable.tsum_le_tsum hterm hnormsum hgeom
    _ = ‖z‖ ^ (g + 1) / (((g : ℝ) + 1) * (1 - ‖z‖)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hz0 hz]
        field_simp

/-- **The regularized free energy.**  Inside the unit disc the infinite-order product is the
exponential of the negative sum of the local logarithm tails over the whole occupation spectrum. -/
theorem infiniteMultipleEllipticGamma_eq_exp_neg_tsum {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1)))
    {x : ℂ} (hx : ‖x‖ < 1) :
    infiniteMultipleEllipticGamma g p x
      = Complex.exp (-∑' ν : ι →₀ ℕ, primaryLogTail g (x * nomeMonomial p ν)) := by
  have hq_le : ∀ ν : ι →₀ ℕ, ‖nomeMonomial p ν‖ ≤ 1 := norm_nomeMonomial_le_one p hp_lt
  have hzlt : ∀ ν : ι →₀ ℕ, ‖x * nomeMonomial p ν‖ < 1 := by
    intro ν
    rw [norm_mul]
    nlinarith [norm_nonneg x, norm_nonneg (nomeMonomial p ν), hq_le ν]
  have hq_sum : Summable (fun ν : ι →₀ ℕ => ‖nomeMonomial p ν‖ ^ (g + 1)) :=
    (summable_nomeMonomial_pow_iff g p hp_lt).2 hsum
  have hd : (0 : ℝ) < (g : ℝ) + 1 := by positivity
  have honex : (0 : ℝ) < 1 - ‖x‖ := by linarith [norm_nonneg x]
  have hbound : ∀ ν : ι →₀ ℕ, ‖primaryLogTail g (x * nomeMonomial p ν)‖
      ≤ ‖x‖ ^ (g + 1) / (((g : ℝ) + 1) * (1 - ‖x‖)) * ‖nomeMonomial p ν‖ ^ (g + 1) := by
    intro ν
    have hle := norm_primaryLogTail_le g (hzlt ν)
    have hnm : ‖x * nomeMonomial p ν‖ = ‖x‖ * ‖nomeMonomial p ν‖ := norm_mul _ _
    have hmono : ‖x * nomeMonomial p ν‖ ≤ ‖x‖ := by
      rw [hnm]
      nlinarith [norm_nonneg x, norm_nonneg (nomeMonomial p ν), hq_le ν]
    have hpos : (0 : ℝ) < ((g : ℝ) + 1) * (1 - ‖x * nomeMonomial p ν‖) := by
      have := hzlt ν
      have h0 : (0 : ℝ) ≤ ‖x * nomeMonomial p ν‖ := norm_nonneg _
      have : (0 : ℝ) < 1 - ‖x * nomeMonomial p ν‖ := by linarith
      positivity
    refine hle.trans ?_
    rw [div_le_iff₀ hpos]
    have hnum : ‖x * nomeMonomial p ν‖ ^ (g + 1) = ‖x‖ ^ (g + 1) * ‖nomeMonomial p ν‖ ^ (g + 1) := by
      rw [hnm, mul_pow]
    rw [hnum]
    have hden : ((g : ℝ) + 1) * (1 - ‖x‖) ≤ ((g : ℝ) + 1) * (1 - ‖x * nomeMonomial p ν‖) := by
      have : (1 : ℝ) - ‖x‖ ≤ 1 - ‖x * nomeMonomial p ν‖ := by linarith
      exact mul_le_mul_of_nonneg_left this (le_of_lt hd)
    have hxq : (0 : ℝ) ≤ ‖x‖ ^ (g + 1) * ‖nomeMonomial p ν‖ ^ (g + 1) := by positivity
    have hkey : ‖x‖ ^ (g + 1) * ‖nomeMonomial p ν‖ ^ (g + 1)
        = (‖x‖ ^ (g + 1) / (((g : ℝ) + 1) * (1 - ‖x‖)) * ‖nomeMonomial p ν‖ ^ (g + 1)) *
            (((g : ℝ) + 1) * (1 - ‖x‖)) := by
      field_simp
    rw [hkey]
    refine mul_le_mul_of_nonneg_left hden ?_
    positivity
  have hWsum : Summable (fun ν : ι →₀ ℕ => primaryLogTail g (x * nomeMonomial p ν)) := by
    refine Summable.of_norm ?_
    exact Summable.of_nonneg_of_le (fun ν => norm_nonneg _) hbound (hq_sum.mul_left _)
  have hHS := hWsum.hasSum.neg
  have hP := hasProd_cexp hHS
  rw [infiniteMultipleEllipticGamma, canonicalWeightProduct, ← hP.tprod_eq]
  refine tprod_congr fun ν => ?_
  exact primaryFactor_eq_exp_neg_primaryLogTail g (hzlt ν)

end HTGeometry
