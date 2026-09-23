import GaloisForLFunctions.RHTower.TruncatedConvolutionModeBridge

/-!
# The compressed ground of a truncated convolution

On the unit sphere of a symmetric Fourier compression the truncated-convolution form attains its
minimum.  The minimum value shifts the compressed packet to a positive semidefinite matrix whose
kernel contains the minimizer, and the minimizer's trigonometric polynomial realizes the minimum of
the form on that compression.
-/

open Matrix MeasureTheory Filter Topology

open scoped Matrix ComplexOrder

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The `ℓ²` unit sphere of a symmetric Fourier compression. -/
def truncConvSphere (N : ℕ) : Set (CCMCenteredParityIndex N → ℂ) :=
  {v | ∑ i, ‖v i‖ ^ (2 : ℕ) = 1}

/-- The truncated-convolution quadratic form in compressed coordinates. -/
def truncConvRayleigh (k : ℝ → ℝ) (N : ℕ) (v : CCMCenteredParityIndex N → ℂ) : ℝ :=
  (l2Pair (truncConvModePoly v) (truncConv k (truncConvModePoly v))).re

theorem continuous_truncConvModePoly {N : ℕ} (v : CCMCenteredParityIndex N → ℂ) :
    Continuous (truncConvModePoly v) :=
  continuous_indexTrigPoly _ _

/-- The `L²` norm of a compressed trigonometric polynomial is the `ℓ²` norm of its coefficients. -/
theorem l2NormSq_truncConvModePoly {N : ℕ} (v : CCMCenteredParityIndex N → ℂ) :
    l2NormSq (truncConvModePoly v) = ∑ i, ‖v i‖ ^ (2 : ℕ) := by
  have hminj : Function.Injective (ccmParityCenteredMode N) := ccmParityCenteredMode_injective N
  have h := integral_indexTrigPoly_normSq hminj v
  have hl : l2Pair (truncConvModePoly v) (truncConvModePoly v)
      = ∑ i, (starRingEnd ℂ) (v i) * v i := h
  rw [l2Pair_self] at hl
  have hre := congrArg Complex.re hl
  rw [Complex.ofReal_re, Complex.re_sum] at hre
  rw [hre]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hz : (starRingEnd ℂ) (v i) * v i = ((‖v i‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rw [hz, Complex.ofReal_re]

/-- The compressed quadratic form in matrix coordinates. -/
theorem truncConvRayleigh_eq_dotProduct {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (hk'c : Continuous k') (heven : ∀ u, k (-u) = k u) {N : ℕ}
    (v : CCMCenteredParityIndex N → ℂ) :
    truncConvRayleigh k N v = (star v ⬝ᵥ (truncConvParityPacket k N 0 *ᵥ v)).re := by
  rw [truncConvParityPacket_form hk hk'c heven 0 v, truncConvRayleigh, l2Pair]
  simp

theorem continuous_truncConvRayleigh {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (_hk'c : Continuous k') (_heven : ∀ u, k (-u) = k u) (N : ℕ) :
    Continuous (truncConvRayleigh k N) := by
  have hkc : Continuous k := continuous_iff_continuousAt.2 fun u => (hk u).continuousAt
  have hcong : truncConvRayleigh k N = fun v : CCMCenteredParityIndex N → ℂ =>
      (∑ i, ∑ j, (starRingEnd ℂ) (v i)
        * convMatrix k (ccmParityCenteredMode N i) (ccmParityCenteredMode N j) * v j).re := by
    funext v
    rw [truncConvRayleigh, l2Pair]
    simp only [truncConvModePoly]
    rw [integral_indexTrigPoly_truncConv hkc]
  rw [hcong]
  refine Complex.continuous_re.comp ?_
  refine continuous_finsetSum _ fun i _ => ?_
  refine continuous_finsetSum _ fun j _ => ?_
  exact ((Complex.continuous_conj.comp (continuous_apply i)).mul continuous_const).mul
    (continuous_apply j)

theorem isCompact_truncConvSphere (N : ℕ) : IsCompact (truncConvSphere N) := by
  have hcont : Continuous fun v : CCMCenteredParityIndex N → ℂ => ∑ i, ‖v i‖ ^ (2 : ℕ) := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((continuous_apply i).norm).pow 2
  have hclosed : IsClosed (truncConvSphere N) := isClosed_eq hcont continuous_const
  have hbdd : Bornology.IsBounded (truncConvSphere N) := by
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun v hv => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun i => ?_
    have hsum : ∑ j, ‖v j‖ ^ (2 : ℕ) = 1 := hv
    have hle : ‖v i‖ ^ (2 : ℕ) ≤ 1 := by
      rw [← hsum]
      refine Finset.single_le_sum (f := fun j => ‖v j‖ ^ (2 : ℕ)) (fun j _ => by positivity)
        (Finset.mem_univ i)
    nlinarith [norm_nonneg (v i)]
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd

theorem truncConvSphere_nonempty (N : ℕ) : (truncConvSphere N).Nonempty := by
  classical
  refine ⟨fun i => if i = (none : CCMCenteredParityIndex N) then 1 else 0, ?_⟩
  show ∑ i, ‖(if i = (none : CCMCenteredParityIndex N) then (1 : ℂ) else 0)‖ ^ (2 : ℕ) = 1
  rw [Finset.sum_eq_single (none : CCMCenteredParityIndex N)]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The compressed ground exists.** -/
theorem exists_truncConv_compressed_ground {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (hk'c : Continuous k') (heven : ∀ u, k (-u) = k u) (N : ℕ) :
    ∃ w ∈ truncConvSphere N, ∀ v ∈ truncConvSphere N,
      truncConvRayleigh k N w ≤ truncConvRayleigh k N v := by
  obtain ⟨w, hw, hmin⟩ := (isCompact_truncConvSphere N).exists_isMinOn
    (truncConvSphere_nonempty N)
    ((continuous_truncConvRayleigh hk hk'c heven N).continuousOn)
  exact ⟨w, hw, fun v hv => hmin hv⟩

/-! ## Homogeneity and the spectral floor -/

theorem indexTrigPoly_const_mul {ι : Type*} [Fintype ι] (m : ι → ℤ) (c : ℂ) (v : ι → ℂ)
    (x : ℝ) :
    indexTrigPoly m (fun i => c * v i) x = c * indexTrigPoly m v x := by
  rw [indexTrigPoly, indexTrigPoly, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem truncConv_const_mul (k : ℝ → ℝ) (c : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    truncConv k (fun y => c * f y) x = c * truncConv k f x := by
  rw [truncConv, truncConv, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun y _ => by ring

theorem truncConvRayleigh_const_mul (k : ℝ → ℝ) {N : ℕ} (t : ℝ)
    (v : CCMCenteredParityIndex N → ℂ) :
    truncConvRayleigh k N (fun i => (t : ℂ) * v i) = t ^ (2 : ℕ) * truncConvRayleigh k N v := by
  have hP : truncConvModePoly (fun i => (t : ℂ) * v i)
      = fun x => (t : ℂ) * truncConvModePoly v x := by
    funext x
    simp only [truncConvModePoly]
    exact indexTrigPoly_const_mul _ _ _ _
  rw [truncConvRayleigh, truncConvRayleigh, hP]
  have hA : (truncConv k fun x => (t : ℂ) * truncConvModePoly v x)
      = fun x => (t : ℂ) * truncConv k (truncConvModePoly v) x := by
    funext x
    exact truncConv_const_mul k _ _ x
  rw [hA, l2Pair_smul_left, l2Pair_smul_right, Complex.conj_ofReal]
  have hval : ((t : ℂ) * ((t : ℂ) * l2Pair (truncConvModePoly v)
      (truncConv k (truncConvModePoly v)))).re
      = t ^ (2 : ℕ) * (l2Pair (truncConvModePoly v) (truncConv k (truncConvModePoly v))).re := by
    have hre : ∀ (a : ℝ) (z : ℂ), ((a : ℂ) * z).re = a * z.re := fun a z => by
      simp [Complex.mul_re]
    rw [hre, hre]
    ring
  exact hval

theorem truncConvRayleigh_zero (k : ℝ → ℝ) (N : ℕ) :
    truncConvRayleigh k N (fun _ => 0) = 0 := by
  have hP : truncConvModePoly (fun _ : CCMCenteredParityIndex N => (0 : ℂ)) = fun _ : ℝ => 0 := by
    funext x
    simp [truncConvModePoly, indexTrigPoly]
  rw [truncConvRayleigh, hP]
  have hA : (truncConv k fun _ : ℝ => (0 : ℂ)) = fun _ : ℝ => 0 := by
    funext x
    simp [truncConv]
  rw [hA, l2Pair]
  simp

/-- **The compressed minimum is a spectral floor.** -/
theorem truncConvRayleigh_min_le {k : ℝ → ℝ} {N : ℕ} {w : CCMCenteredParityIndex N → ℂ}
    (hmin : ∀ v ∈ truncConvSphere N, truncConvRayleigh k N w ≤ truncConvRayleigh k N v)
    (v : CCMCenteredParityIndex N → ℂ) :
    truncConvRayleigh k N w * (∑ i, ‖v i‖ ^ (2 : ℕ)) ≤ truncConvRayleigh k N v := by

  by_cases hv : ∀ i, v i = 0
  · have hz : v = fun _ => 0 := funext hv
    subst hz
    simp [truncConvRayleigh_zero]
  · simp only [not_forall] at hv
    obtain ⟨i₀, hi₀⟩ := hv
    have hs : 0 < ∑ i, ‖v i‖ ^ (2 : ℕ) := by
      refine Finset.sum_pos' (fun i _ => by positivity) ⟨i₀, Finset.mem_univ i₀, ?_⟩
      have : ‖v i₀‖ ≠ 0 := by simpa using hi₀
      positivity
    set s : ℝ := ∑ i, ‖v i‖ ^ (2 : ℕ) with hsdef
    set t : ℝ := (Real.sqrt s)⁻¹ with ht
    have hsq : Real.sqrt s ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hs)
    have htsq : t ^ (2 : ℕ) * s = 1 := by
      rw [ht, inv_pow, Real.sq_sqrt hs.le]
      field_simp
    have hmem : (fun i => (t : ℂ) * v i) ∈ truncConvSphere N := by
      show ∑ i, ‖(t : ℂ) * v i‖ ^ (2 : ℕ) = 1
      have hnorm : ∀ i, ‖(t : ℂ) * v i‖ ^ (2 : ℕ) = t ^ (2 : ℕ) * ‖v i‖ ^ (2 : ℕ) := by
        intro i
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [Finset.sum_congr rfl fun i _ => hnorm i, ← Finset.mul_sum, ← hsdef, htsq]
    have hle := hmin _ hmem
    rw [truncConvRayleigh_const_mul] at hle
    calc truncConvRayleigh k N w * s
        ≤ (t ^ (2 : ℕ) * truncConvRayleigh k N v) * s := mul_le_mul_of_nonneg_right hle hs.le
      _ = (t ^ (2 : ℕ) * s) * truncConvRayleigh k N v := by ring
      _ = truncConvRayleigh k N v := by rw [htsq, one_mul]

theorem truncConvRayleigh_complex_mul (k : ℝ → ℝ) {N : ℕ} (c : ℂ)
    (v : CCMCenteredParityIndex N → ℂ) :
    truncConvRayleigh k N (fun i => c * v i) = ‖c‖ ^ (2 : ℕ) * truncConvRayleigh k N v := by
  have hP : truncConvModePoly (fun i => c * v i) = fun x => c * truncConvModePoly v x := by
    funext x
    simp only [truncConvModePoly]
    exact indexTrigPoly_const_mul _ _ _ _
  rw [truncConvRayleigh, truncConvRayleigh, hP]
  have hA : (truncConv k fun x => c * truncConvModePoly v x)
      = fun x => c * truncConv k (truncConvModePoly v) x := by
    funext x
    exact truncConv_const_mul k _ _ x
  rw [hA, l2Pair_smul_left, l2Pair_smul_right]
  have hnorm : (starRingEnd ℂ) c * (c * l2Pair (truncConvModePoly v)
      (truncConv k (truncConvModePoly v)))
      = ((‖c‖ ^ (2 : ℕ) : ℝ) : ℂ) * l2Pair (truncConvModePoly v)
        (truncConv k (truncConvModePoly v)) := by
    have h1 : ((‖c‖ ^ (2 : ℕ) : ℝ) : ℂ) = (starRingEnd ℂ) c * c := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    rw [h1]
    ring
  rw [hnorm]
  have hre : ∀ (a : ℝ) (z : ℂ), ((a : ℂ) * z).re = a * z.re := fun a z => by
    simp [Complex.mul_re]
  exact hre _ _

/-! ## The compressed packet at the minimum -/

/-- **The compressed packet shifted by the compressed minimum is positive semidefinite.** -/
theorem truncConvParityPacket_posSemidef_of_min {k k' : ℝ → ℝ}
    (hk : ∀ u, HasDerivAt k (k' u) u) (hk'c : Continuous k') (heven : ∀ u, k (-u) = k u)
    {N : ℕ} {w : CCMCenteredParityIndex N → ℂ}
    (hmin : ∀ v ∈ truncConvSphere N, truncConvRayleigh k N w ≤ truncConvRayleigh k N v) :
    (truncConvParityPacket k N (truncConvRayleigh k N w)).PosSemidef := by
  have hkc : Continuous k := continuous_iff_continuousAt.2 fun u => (hk u).continuousAt
  refine truncConvParityPacket_posSemidef hk hk'c heven fun v => ?_
  have hcont : Continuous (truncConvModePoly v) := continuous_truncConvModePoly v
  have hnorm : (∫ x in (0 : ℝ)..1,
      (starRingEnd ℂ) (truncConvModePoly v x) * truncConvModePoly v x)
      = ((∑ i, ‖v i‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    show l2Pair (truncConvModePoly v) (truncConvModePoly v) = _
    rw [l2Pair_self, l2NormSq_truncConvModePoly]
  rw [hnorm, Complex.le_def]
  refine ⟨?_, ?_⟩
  · rw [← Complex.ofReal_mul, Complex.ofReal_re]
    exact truncConvRayleigh_min_le hmin v
  · rw [← Complex.ofReal_mul, Complex.ofReal_im]
    exact (l2Pair_truncConv_self_im hkc heven hcont).symm

/-- **The compressed ground lies in the kernel of the shifted packet.** -/
theorem truncConvParityPacket_ground_mulVec {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (hk'c : Continuous k') (heven : ∀ u, k (-u) = k u)
    {N : ℕ} {w : CCMCenteredParityIndex N → ℂ} (hw : w ∈ truncConvSphere N)
    (hmin : ∀ v ∈ truncConvSphere N, truncConvRayleigh k N w ≤ truncConvRayleigh k N v) :
    truncConvParityPacket k N (truncConvRayleigh k N w) *ᵥ w = 0 := by
  have hkc : Continuous k := continuous_iff_continuousAt.2 fun u => (hk u).continuousAt
  have hpsd := truncConvParityPacket_posSemidef_of_min hk hk'c heven hmin
  rw [truncConvParityPacket_mulVec_eq_zero_iff hk hk'c heven hpsd w]
  have hnorm : (∫ x in (0 : ℝ)..1,
      (starRingEnd ℂ) (truncConvModePoly w x) * truncConvModePoly w x) = 1 := by
    show l2Pair (truncConvModePoly w) (truncConvModePoly w) = _
    rw [l2Pair_self, l2NormSq_truncConvModePoly]
    have hone : ∑ i, ‖w i‖ ^ (2 : ℕ) = 1 := hw
    rw [hone]
    norm_num
  rw [hnorm, mul_one]
  refine Complex.ext rfl ?_
  exact (l2Pair_truncConv_self_im hkc heven (continuous_truncConvModePoly w)).trans
    (Complex.ofReal_im _).symm

end

end RHTower
