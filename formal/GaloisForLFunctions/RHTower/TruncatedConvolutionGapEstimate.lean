import GaloisForLFunctions.RHTower.TruncatedConvolutionCompressedGround

/-!
# The spectral-gap estimate for a truncated convolution

An isolated simple ground of the truncated-convolution form makes the form control the distance to
the ground line: the excess of the Rayleigh quotient over the bottom bounds the squared `L²`
distance to the ground, divided by the gap.  This is the estimate that turns a minimizing sequence
into a sequence converging to the ground.
-/

open MeasureTheory Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem truncConv_add {k : ℝ → ℝ} (hkc : Continuous k) {f g : ℝ → ℂ} (hf : Continuous f)
    (hg : Continuous g) (x : ℝ) :
    truncConv k (fun y => f y + g y) x = truncConv k f x + truncConv k g x := by
  rw [truncConv, truncConv, truncConv, ← intervalIntegral.integral_add]
  · refine intervalIntegral.integral_congr fun y _ => ?_
    ring
  · refine Continuous.intervalIntegrable ?_ _ _
    exact (Complex.continuous_ofReal.comp (hkc.comp (continuous_const.sub continuous_id))).mul hf
  · refine Continuous.intervalIntegrable ?_ _ _
    exact (Complex.continuous_ofReal.comp (hkc.comp (continuous_const.sub continuous_id))).mul hg

/-- The variational data of a simple isolated odd ground of a truncated convolution. -/
structure TruncConvOddGround (k : ℝ → ℝ) (lam gap : ℝ) (xi : ℝ → ℂ) : Prop where
  contXi : Continuous xi
  normXi : l2NormSq xi = 1
  oddXi : ∀ x, xi (1 - x) = -xi x
  eig : ∀ x ∈ Set.Icc (0 : ℝ) 1, truncConv k xi x = (lam : ℂ) * xi x
  gapPos : 0 < gap
  gapLower : ∀ f : ℝ → ℂ, Continuous f → l2Pair xi f = 0 →
    (lam + gap) * l2NormSq f ≤ (l2Pair f (truncConv k f)).re

/-- The component of `f` orthogonal to the ground. -/
def truncConvResidual (xi f : ℝ → ℂ) : ℝ → ℂ := fun x => f x - l2Pair xi f * xi x

theorem truncConvResidual_eq (xi f : ℝ → ℂ) :
    truncConvResidual xi f = fun x => f x - l2Pair xi f * xi x := rfl

theorem continuous_truncConvResidual {xi f : ℝ → ℂ} (hxi : Continuous xi) (hf : Continuous f) :
    Continuous (truncConvResidual xi f) := by
  rw [truncConvResidual_eq]
  exact hf.sub (continuous_const.mul hxi)

theorem l2Pair_xi_xi {k : ℝ → ℝ} {lam gap : ℝ} {xi : ℝ → ℂ}
    (H : TruncConvOddGround k lam gap xi) : l2Pair xi xi = 1 := by
  rw [l2Pair_self, H.normXi]
  norm_num

theorem l2Pair_xi_truncConvResidual {k : ℝ → ℝ} {lam gap : ℝ} {xi : ℝ → ℂ}
    (H : TruncConvOddGround k lam gap xi) {f : ℝ → ℂ} (hf : Continuous f) :
    l2Pair xi (truncConvResidual xi f) = 0 := by
  rw [truncConvResidual_eq,
    l2Pair_sub_right (f := xi) (g := f) (h := fun x => l2Pair xi f * xi x)
      H.contXi hf (continuous_const.mul H.contXi),
    l2Pair_smul_right (l2Pair xi f) xi xi, l2Pair_xi_xi H, mul_one, sub_self]

theorem truncConvResidual_add {xi f : ℝ → ℂ} (x : ℝ) :
    f x = l2Pair xi f * xi x + truncConvResidual xi f x := by
  rw [truncConvResidual_eq]
  simp only
  ring

theorem l2NormSq_truncConvResidual {k : ℝ → ℝ} {lam gap : ℝ} {xi : ℝ → ℂ}
    (H : TruncConvOddGround k lam gap xi) {f : ℝ → ℂ} (hf : Continuous f) :
    l2NormSq (truncConvResidual xi f) = l2NormSq f - ‖l2Pair xi f‖ ^ (2 : ℕ) := by
  set c : ℂ := l2Pair xi f with hc
  set g : ℝ → ℂ := truncConvResidual xi f with hg
  have hgc : Continuous g := continuous_truncConvResidual H.contXi hf
  have hgz : l2Pair xi g = 0 := l2Pair_xi_truncConvResidual H hf
  have hgz' : l2Pair g xi = 0 := by
    rw [← l2Pair_conj xi g, hgz, map_zero]
  have hf' : f = fun x => c * xi x + g x := funext fun x => truncConvResidual_add x
  have hu : Continuous fun x => c * xi x := continuous_const.mul H.contXi
  have hexp : l2Pair f f = ((‖c‖ ^ (2 : ℕ) : ℝ) : ℂ) + l2Pair g g := by
    conv_lhs => rw [hf']
    rw [l2Pair_add_left (f := fun x => c * xi x) (g := g) (h := fun x => c * xi x + g x)
      hu hgc (hu.add hgc)]
    rw [l2Pair_add_right (fun x => c * xi x) (fun x => c * xi x) g hu hgc hu]
    rw [l2Pair_add_right g (fun x => c * xi x) g hu hgc hgc]
    rw [l2Pair_smul_left c xi (fun x => c * xi x), l2Pair_smul_right c xi xi,
      l2Pair_smul_left c xi g, l2Pair_smul_right c g xi, l2Pair_xi_xi H, hgz, hgz']
    have hnorm : ((‖c‖ ^ (2 : ℕ) : ℝ) : ℂ) = (starRingEnd ℂ) c * c := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    rw [hnorm]
    ring
  rw [l2Pair_self, l2Pair_self] at hexp
  have hre := congrArg Complex.re hexp
  simp only [Complex.ofReal_re, Complex.add_re] at hre
  rw [hre]
  ring

theorem l2Pair_form_decompose {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (heven : ∀ u, k (-u) = k u) {lam gap : ℝ} {xi : ℝ → ℂ}
    (H : TruncConvOddGround k lam gap xi) {f : ℝ → ℂ} (hf : Continuous f) :
    l2Pair f (truncConv k f)
      = ((‖l2Pair xi f‖ ^ (2 : ℕ) * lam : ℝ) : ℂ)
        + l2Pair (truncConvResidual xi f) (truncConv k (truncConvResidual xi f)) := by
  have hkc : Continuous k := continuous_iff_continuousAt.2 fun u => (hk u).continuousAt
  set c : ℂ := l2Pair xi f with hc
  set g : ℝ → ℂ := truncConvResidual xi f with hg
  have hgc : Continuous g := continuous_truncConvResidual H.contXi hf
  have hgz : l2Pair xi g = 0 := l2Pair_xi_truncConvResidual H hf
  have hgz' : l2Pair g xi = 0 := by
    rw [← l2Pair_conj xi g, hgz, map_zero]
  have hf' : f = fun x => c * xi x + g x := funext fun x => truncConvResidual_add x
  have hu : Continuous fun x => c * xi x := continuous_const.mul H.contXi
  have hAxi : ∀ x ∈ Set.Icc (0 : ℝ) 1, truncConv k xi x = (lam : ℂ) * xi x := H.eig
  have hcross1 : l2Pair xi (truncConv k g) = 0 := by
    rw [truncConv_selfAdjoint hkc heven H.contXi hgc,
      l2Pair_congr_left hAxi, l2Pair_smul_left (lam : ℂ) xi g, Complex.conj_ofReal, hgz, mul_zero]
  have hcross2 : l2Pair g (truncConv k xi) = 0 := by
    rw [l2Pair_congr_right hAxi, l2Pair_smul_right (lam : ℂ) g xi, hgz', mul_zero]
  have hxixi : l2Pair xi (truncConv k xi) = (lam : ℂ) := by
    rw [l2Pair_congr_right hAxi, l2Pair_smul_right (lam : ℂ) xi xi, l2Pair_xi_xi H, mul_one]
  have hAf : truncConv k f = fun x => c * truncConv k xi x + truncConv k g x := by
    funext x
    conv_lhs => rw [hf']
    rw [truncConv_add hkc hu hgc x, truncConv_const_mul]
  have hAc : Continuous fun x => c * truncConv k xi x :=
    continuous_const.mul (continuous_truncConv hkc H.contXi)
  have hAgc : Continuous (truncConv k g) := continuous_truncConv hkc hgc
  rw [hAf]
  conv_lhs => rw [hf']
  rw [l2Pair_add_left (f := fun x => c * xi x) (g := g)
    (h := fun x => c * truncConv k xi x + truncConv k g x) hu hgc (hAc.add hAgc)]
  rw [l2Pair_add_right (fun x => c * xi x) (fun x => c * truncConv k xi x) (truncConv k g)
      hAc hAgc hu]
  rw [l2Pair_add_right g (fun x => c * truncConv k xi x) (truncConv k g) hAc hAgc hgc]
  rw [l2Pair_smul_left c xi (fun x => c * truncConv k xi x),
    l2Pair_smul_right c xi (truncConv k xi), l2Pair_smul_left c xi (truncConv k g),
    l2Pair_smul_right c g (truncConv k xi), hxixi, hcross1, hcross2]
  have hnorm : ((‖c‖ ^ (2 : ℕ) * lam : ℝ) : ℂ) = (starRingEnd ℂ) c * (c * (lam : ℂ)) := by
    have h1 : ((‖c‖ ^ (2 : ℕ) : ℝ) : ℂ) = (starRingEnd ℂ) c * c := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    rw [Complex.ofReal_mul, h1]
    ring
  rw [hnorm]
  ring

/-- **The spectral-gap estimate.** -/
theorem truncConv_gap_estimate {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (heven : ∀ u, k (-u) = k u) {lam gap : ℝ} {xi : ℝ → ℂ}
    (H : TruncConvOddGround k lam gap xi) {f : ℝ → ℂ} (hf : Continuous f) :
    gap * l2NormSq (truncConvResidual xi f)
      ≤ (l2Pair f (truncConv k f)).re - lam * l2NormSq f := by
  have hgc : Continuous (truncConvResidual xi f) := continuous_truncConvResidual H.contXi hf
  have hdec := l2Pair_form_decompose hk heven H hf
  have hre := congrArg Complex.re hdec
  simp only [Complex.add_re, Complex.ofReal_re] at hre
  have hlow := H.gapLower _ hgc (l2Pair_xi_truncConvResidual H hf)
  have hsplit := l2NormSq_truncConvResidual H hf
  rw [hre]
  have h1 : l2NormSq f = l2NormSq (truncConvResidual xi f) + ‖l2Pair xi f‖ ^ (2 : ℕ) := by
    rw [hsplit]
    ring
  rw [h1]
  linarith [hlow]

/-- **The bottom of the form.** -/
theorem truncConv_form_lower {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (heven : ∀ u, k (-u) = k u) {lam gap : ℝ} {xi : ℝ → ℂ}
    (H : TruncConvOddGround k lam gap xi) {f : ℝ → ℂ} (hf : Continuous f) :
    lam * l2NormSq f ≤ (l2Pair f (truncConv k f)).re := by
  have h := truncConv_gap_estimate hk heven H hf
  have hnn : 0 ≤ gap * l2NormSq (truncConvResidual xi f) :=
    mul_nonneg H.gapPos.le (l2NormSq_nonneg (truncConvResidual xi f))
  linarith

end

end RHTower
