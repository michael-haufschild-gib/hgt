import GaloisForLFunctions.RHTower.TruncatedConvolutionGapEstimate

/-!
# Selection of the compressed ground below the spectral gap

Below the gap the kernel of the shifted compressed packet is a line, and the reflection forces its
generator to be odd.  The two facts have the same source: a kernel vector orthogonal to the ground
would have Rayleigh quotient equal to the compressed minimum, which the gap forbids.
-/

open Matrix MeasureTheory Filter Topology

open scoped Matrix ComplexOrder

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The reflection acting on compressed coefficient vectors. -/
def reflVec (N : ℕ) (w : CCMCenteredParityIndex N → ℂ) : CCMCenteredParityIndex N → ℂ :=
  fun i => w (ccmCenteredParityReflection N i)

theorem indexTrigPoly_add_smul {ι : Type*} [Fintype ι] (m : ι → ℤ) (a b : ℂ) (v w : ι → ℂ)
    (x : ℝ) :
    indexTrigPoly m (fun i => a * v i + b * w i) x
      = a * indexTrigPoly m v x + b * indexTrigPoly m w x := by
  rw [indexTrigPoly, indexTrigPoly, indexTrigPoly, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Reflecting the coefficients reflects the trigonometric polynomial. -/
theorem truncConvModePoly_reflVec {N : ℕ} (w : CCMCenteredParityIndex N → ℂ) (x : ℝ) :
    truncConvModePoly (reflVec N w) x = truncConvModePoly w (1 - x) := by
  simp only [truncConvModePoly, indexTrigPoly, reflVec]
  rw [← Equiv.sum_comp (ccmCenteredParityReflection N)
    (fun i => w (ccmCenteredParityReflection N i) * fourierChar (ccmParityCenteredMode N i) x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ccmCenteredParityReflection_involutive, ccmParityCenteredMode_reflection]
  congr 1
  exact (fourierChar_neg_one_sub (-(ccmParityCenteredMode N i)) x).symm ▸ by
    rw [neg_neg]

/-- Pairing an odd ground against a reflected function changes the sign. -/
theorem l2Pair_odd_reflect {xi P : ℝ → ℂ} (hodd : ∀ x, xi (1 - x) = -xi x) :
    l2Pair xi (fun x => P (1 - x)) = -l2Pair xi P := by
  have hcomp := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := (1 : ℝ))
    (fun x : ℝ => (starRingEnd ℂ) (xi x) * P (1 - x)) (1 : ℝ)
  simp only [sub_zero, sub_self] at hcomp
  rw [l2Pair, ← hcomp, l2Pair, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun u _ => ?_
  have harg : (1 : ℝ) - (1 - u) = u := by ring
  rw [harg, hodd u, map_neg]
  ring

/-- The compressed packet commutes with the reflection. -/
theorem truncConvParityPacket_mulVec_reflVec {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (hk'c : Continuous k') (heven : ∀ u, k (-u) = k u) {N : ℕ} (mu : ℝ)
    (w : CCMCenteredParityIndex N → ℂ) :
    truncConvParityPacket k N mu *ᵥ reflVec N w
      = reflVec N (truncConvParityPacket k N mu *ᵥ w) := by
  funext i
  have hentry : ∀ a b : CCMCenteredParityIndex N,
      truncConvParityPacket k N mu (ccmCenteredParityReflection N a)
          (ccmCenteredParityReflection N b)
        = truncConvParityPacket k N mu a b := by
    intro a b
    rw [truncConvParityPacket_apply hk hk'c heven, truncConvParityPacket_apply hk hk'c heven,
      ccmParityCenteredMode_reflection, ccmParityCenteredMode_reflection,
      convMatrix_reflect heven]
    congr 2
    by_cases hab : a = b
    · simp [hab]
    · have : ¬ (ccmCenteredParityReflection N a = ccmCenteredParityReflection N b) := by
        intro h
        exact hab ((ccmCenteredParityReflection N).injective h)
      simp [hab, this]
  simp only [Matrix.mulVec, dotProduct, reflVec]
  rw [← Equiv.sum_comp (ccmCenteredParityReflection N)
    (fun j => truncConvParityPacket k N mu i j * w (ccmCenteredParityReflection N j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ccmCenteredParityReflection_involutive]
  congr 1
  have h := hentry i (ccmCenteredParityReflection N j)
  rw [ccmCenteredParityReflection_involutive] at h
  exact h.symm

/-! ## The kernel is a line and its generator is odd -/

theorem truncConvModePoly_combo {N : ℕ} (a b : ℂ) (v w : CCMCenteredParityIndex N → ℂ) (x : ℝ) :
    truncConvModePoly (fun i => a * v i - b * w i) x
      = a * truncConvModePoly v x - b * truncConvModePoly w x := by
  simp only [truncConvModePoly, indexTrigPoly]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem mulVec_combo {N : ℕ} (M : Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ)
    (a b : ℂ) (v w : CCMCenteredParityIndex N → ℂ) (i : CCMCenteredParityIndex N) :
    (M *ᵥ fun j => a * v j - b * w j) i = a * (M *ᵥ v) i - b * (M *ᵥ w) i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem l2NormSq_truncConvModePoly_pos {N : ℕ} {u : CCMCenteredParityIndex N → ℂ} (hu : u ≠ 0) :
    0 < l2NormSq (truncConvModePoly u) := by
  rw [l2NormSq_truncConvModePoly]
  obtain ⟨i₀, hi₀⟩ : ∃ i, u i ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hu (funext hcon)
  refine Finset.sum_pos' (fun i _ => by positivity) ⟨i₀, Finset.mem_univ i₀, ?_⟩
  have : ‖u i₀‖ ≠ 0 := by simpa using hi₀
  positivity

/-- **The compressed ground is not orthogonal to the true ground.** -/
theorem truncConv_ground_pairing_ne_zero {k : ℝ → ℝ} {lam gap : ℝ} {xi : ℝ → ℂ}
    (H : TruncConvOddGround k lam gap xi) {N : ℕ} {w : CCMCenteredParityIndex N → ℂ}
    (hw : w ∈ truncConvSphere N)
    (hlt : truncConvRayleigh k N w < lam + gap) :
    l2Pair xi (truncConvModePoly w) ≠ 0 := by
  intro hzero
  have hcont : Continuous (truncConvModePoly w) := continuous_truncConvModePoly w
  have hnorm : l2NormSq (truncConvModePoly w) = 1 := by
    rw [l2NormSq_truncConvModePoly]
    exact hw
  have hgap := H.gapLower _ hcont hzero
  rw [hnorm, mul_one] at hgap
  exact absurd hgap (not_le.2 hlt)

/-- **Below the gap the compressed kernel is the line through the ground.** -/
theorem truncConv_kernel_line {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (hk'c : Continuous k') (heven : ∀ u, k (-u) = k u) {lam gap : ℝ} {xi : ℝ → ℂ}
    (H : TruncConvOddGround k lam gap xi) {N : ℕ} {w : CCMCenteredParityIndex N → ℂ}
    (hw : w ∈ truncConvSphere N)
    (hmin : ∀ v ∈ truncConvSphere N, truncConvRayleigh k N w ≤ truncConvRayleigh k N v)
    (hlt : truncConvRayleigh k N w < lam + gap)
    (v : CCMCenteredParityIndex N → ℂ)
    (hv : truncConvParityPacket k N (truncConvRayleigh k N w) *ᵥ v = 0) :
    ∃ z : ℂ, v = fun i => z * w i := by
  have hkc : Continuous k := continuous_iff_continuousAt.2 fun u => (hk u).continuousAt
  have hpsd := truncConvParityPacket_posSemidef_of_min hk hk'c heven hmin
  have hgw := truncConvParityPacket_ground_mulVec hk hk'c heven hw hmin
  set beta : ℂ := l2Pair xi (truncConvModePoly w) with hbeta
  set alpha : ℂ := l2Pair xi (truncConvModePoly v) with halpha
  have hbne : beta ≠ 0 := truncConv_ground_pairing_ne_zero H hw hlt
  set u : CCMCenteredParityIndex N → ℂ := fun i => beta * v i - alpha * w i with hu
  have hker : truncConvParityPacket k N (truncConvRayleigh k N w) *ᵥ u = 0 := by
    funext i
    rw [hu, mulVec_combo]
    rw [hv, hgw]
    simp
  have hPu : truncConvModePoly u
      = fun x => beta * truncConvModePoly v x - alpha * truncConvModePoly w x := by
    funext x
    rw [hu]
    exact truncConvModePoly_combo beta alpha v w x
  have hpair : l2Pair xi (truncConvModePoly u) = 0 := by
    rw [hPu]
    rw [l2Pair_sub_right (f := xi) (g := fun x => beta * truncConvModePoly v x)
        (h := fun x => alpha * truncConvModePoly w x) H.contXi
        (continuous_const.mul (continuous_truncConvModePoly v))
        (continuous_const.mul (continuous_truncConvModePoly w))]
    rw [l2Pair_smul_right beta xi (truncConvModePoly v),
      l2Pair_smul_right alpha xi (truncConvModePoly w), ← hbeta, ← halpha]
    ring
  have huz : u = 0 := by
    by_contra hune
    have hpos := l2NormSq_truncConvModePoly_pos hune
    have hgapu := H.gapLower _ (continuous_truncConvModePoly u) hpair
    have hform := (truncConvParityPacket_mulVec_eq_zero_iff hk hk'c heven hpsd u).1 hker
    have hformre : (l2Pair (truncConvModePoly u) (truncConv k (truncConvModePoly u))).re
        = truncConvRayleigh k N w * l2NormSq (truncConvModePoly u) := by
      have h1 : l2Pair (truncConvModePoly u) (truncConv k (truncConvModePoly u))
          = ((truncConvRayleigh k N w : ℂ)) * ((l2NormSq (truncConvModePoly u) : ℝ) : ℂ) := by
        rw [← l2Pair_self (truncConvModePoly u)]
        exact hform
      rw [h1, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hformre] at hgapu
    nlinarith [hgapu, hpos, hlt]
  refine ⟨alpha / beta, ?_⟩
  funext i
  have hi : beta * v i - alpha * w i = 0 := congrFun huz i
  field_simp
  linear_combination hi

/-- **The compressed ground is odd.** -/
theorem truncConv_ground_odd {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (hk'c : Continuous k') (heven : ∀ u, k (-u) = k u) {lam gap : ℝ} {xi : ℝ → ℂ}
    (H : TruncConvOddGround k lam gap xi) {N : ℕ} {w : CCMCenteredParityIndex N → ℂ}
    (hw : w ∈ truncConvSphere N)
    (hmin : ∀ v ∈ truncConvSphere N, truncConvRayleigh k N w ≤ truncConvRayleigh k N v)
    (hlt : truncConvRayleigh k N w < lam + gap) :
    ∀ i, w (ccmCenteredParityReflection N i) = -w i := by
  have hgw := truncConvParityPacket_ground_mulVec hk hk'c heven hw hmin
  have hbne : l2Pair xi (truncConvModePoly w) ≠ 0 :=
    truncConv_ground_pairing_ne_zero H hw hlt
  have hrker : truncConvParityPacket k N (truncConvRayleigh k N w) *ᵥ reflVec N w = 0 := by
    rw [truncConvParityPacket_mulVec_reflVec hk hk'c heven, hgw]
    funext i
    simp [reflVec]
  obtain ⟨z, hz⟩ := truncConv_kernel_line hk hk'c heven H hw hmin hlt _ hrker
  have hPz : truncConvModePoly (reflVec N w) = fun x => z * truncConvModePoly w x := by
    rw [hz]
    funext x
    simp only [truncConvModePoly, indexTrigPoly, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hleft : l2Pair xi (truncConvModePoly (reflVec N w))
      = -l2Pair xi (truncConvModePoly w) := by
    have hrefl : truncConvModePoly (reflVec N w) = fun x => truncConvModePoly w (1 - x) :=
      funext fun x => truncConvModePoly_reflVec w x
    rw [hrefl]
    exact l2Pair_odd_reflect H.oddXi
  rw [hPz, l2Pair_smul_right z xi (truncConvModePoly w)] at hleft
  have hzval : z = -1 := by
    have hstep : (z + 1) * l2Pair xi (truncConvModePoly w) = 0 := by
      rw [add_mul, one_mul, hleft]
      ring
    rcases mul_eq_zero.1 hstep with h | h
    · exact eq_neg_of_add_eq_zero_left h
    · exact absurd h hbne
  intro i
  have := congrFun hz i
  rw [hzval] at this
  simpa [reflVec] using this

/-- The odd coordinates of a compressed ground. -/
def oddGroundCoeffOf (N : ℕ) (w : CCMCenteredParityIndex N → ℂ) (j : Fin N) : ℂ :=
  w (some (j, false)) / ccmParityFrameScale

/-- **An odd compressed vector is the odd frame applied to its coordinates.** -/
theorem ccmOddParityFrame_mulVec_oddGroundCoeffOf {N : ℕ} {w : CCMCenteredParityIndex N → ℂ}
    (hodd : ∀ i, w (ccmCenteredParityReflection N i) = -w i) :
    ccmOddParityFrame N *ᵥ oddGroundCoeffOf N w = w := by
  funext i
  have hzero : w none = 0 := by
    have h := hodd none
    have hn : (ccmCenteredParityReflection N) none = none := rfl
    rw [hn] at h
    linear_combination h / 2
  have hs : ccmParityFrameScale ≠ 0 := ccmParityFrameScale_ne_zero
  rcases i with _ | ⟨j, b⟩
  · simp only [Matrix.mulVec, dotProduct]
    rw [hzero]
    simp [ccmOddParityFrame]
  · cases b
    · have hmul : (ccmOddParityFrame N *ᵥ oddGroundCoeffOf N w) (some (j, false))
          = ccmParityFrameScale * oddGroundCoeffOf N w j := by
        rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j]
        · simp [ccmOddParityFrame]
        · intro l _ hlj
          simp [ccmOddParityFrame, Ne.symm hlj]
        · intro hcon
          exact absurd (Finset.mem_univ j) hcon
      rw [hmul, oddGroundCoeffOf]
      field_simp
    · have hmul : (ccmOddParityFrame N *ᵥ oddGroundCoeffOf N w) (some (j, true))
          = -ccmParityFrameScale * oddGroundCoeffOf N w j := by
        rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j]
        · simp [ccmOddParityFrame]
        · intro l _ hlj
          simp [ccmOddParityFrame, Ne.symm hlj]
        · intro hcon
          exact absurd (Finset.mem_univ j) hcon
      have h := hodd (some (j, false))
      have hn : (ccmCenteredParityReflection N) (some (j, false)) = some (j, true) := rfl
      rw [hn] at h
      rw [hmul, oddGroundCoeffOf, h]
      field_simp

end

end RHTower
