import GaloisForLFunctions.HTGeometry.SchwartzSpectralPullbackForm
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Centered quadratic spectral separators for positive Schwartz forms

Momentum symmetry is stable under real centered quadratic functional calculus.  The resulting
strictly positive multiplier is the natural separator for two compact spectral packets: after a
choice of center and scale it is uniformly below one on one packet and uniformly above one on the
other, while its reciprocal is globally smooth.

This module supplies the exact symmetric operator needed by the power-separation locality theorem.
The remaining analytic step is convergence of its direct and reciprocal powers on separated
compact packets.
-/

open Complex Function Filter
open scoped SchwartzMap FourierTransform Topology

noncomputable section

namespace SchwartzMap

/-- Faà di Bruno specialized to a smooth scalar multiplier raised to a natural power. -/
theorem iteratedDeriv_pow_comp_eq_orderedFinpartition
    (m : ℝ → ℝ) (hm : ContDiff ℝ (⊤ : ℕ∞) m) (n i : ℕ) (t : ℝ) :
    iteratedDeriv i (fun x => m x ^ n) t =
      ∑ c : OrderedFinpartition i,
        (∏ j, iteratedDeriv (c.partSize j) m t) *
          (n.descFactorial c.length * m t ^ (n - c.length)) := by
  rw [show (fun x => m x ^ n) = (fun y : ℝ => y ^ n) ∘ m by rfl]
  rw [iteratedDeriv_scomp_eq_sum_orderedFinpartition (by fun_prop)
    hm.contDiffAt (by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))]
  apply Finset.sum_congr rfl
  intro c _hc
  rw [iteratedDeriv_pow]
  ring

/-- All-order Leibniz expansion for a real multiplier power acting on a complex Schwartz map. -/
theorem iteratedDeriv_real_pow_mul_schwartz_eq_sum
    (m : ℝ → ℝ) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (f : SchwartzMap ℝ ℂ) (n k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun x => (m x ^ n : ℂ) * f x) t =
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℂ) * iteratedDeriv i (fun x => (m x ^ n : ℂ)) t *
          iteratedDeriv (k - i) f t := by
  have hmC : ContDiff ℝ (⊤ : ℕ∞) (fun x => (m x : ℂ)) :=
    ContDiff.continuousLinearMap_comp Complex.ofRealCLM hm
  exact iteratedDeriv_fun_mul ((hmC.pow n).contDiffAt.of_le
      (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))
    (f.smooth k).contDiffAt

/-- Convergence of every defining Schwartz seminorm upgrades to convergence in the full Schwartz
topology. -/
theorem tendsto_zero_of_tendsto_seminorm
    {ι : Type*} {l : Filter ι} (F : ι → SchwartzMap ℝ ℂ)
    (hF : ∀ a k : ℕ,
      Tendsto (fun i => SchwartzMap.seminorm ℂ a k (F i)) l (nhds 0)) :
    Tendsto F l (nhds 0) := by
  rw [(schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds]
  rintro ⟨a, k⟩ ε hε
  have hev := (hF a k) (Iio_mem_nhds hε)
  rw [Filter.mem_map] at hev
  change {i | SchwartzMap.seminorm ℂ a k (F i) < ε} ∈ l at hev
  change {i | schwartzSeminormFamily ℂ ℝ ℂ (a, k) (F i - 0) < ε} ∈ l
  simpa only [schwartzSeminormFamily_apply, sub_zero] using hev

/-- On uniformly compact support, convergence of the zero-weight derivative seminorm controls
every polynomially weighted seminorm of the same derivative order. -/
theorem seminorm_le_pow_mul_seminorm_zero_of_tsupport_subset
    {T : ℝ} (hT : 0 ≤ T) (f : SchwartzMap ℝ ℂ)
    (hf : tsupport f ⊆ {t : ℝ | |t| ≤ T}) (a k : ℕ) :
    SchwartzMap.seminorm ℂ a k f ≤
      T ^ a * SchwartzMap.seminorm ℂ 0 k f := by
  apply SchwartzMap.seminorm_le_bound' (𝕜 := ℂ) a k
  · positivity
  · intro t
    by_cases hd : iteratedDeriv k f t = 0
    · rw [hd, norm_zero, mul_zero]
      positivity
    · have hdF : iteratedFDeriv ℝ k f t ≠ 0 := by
        intro hzero
        have hnorm : ‖iteratedDeriv k f t‖ = 0 := by
          rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, hzero, norm_zero]
        exact hd (norm_eq_zero.mp hnorm)
      have ht : t ∈ tsupport f := support_iteratedFDeriv_subset k hdF
      have habs := hf ht
      change |t| ≤ T at habs
      calc
        |t| ^ a * ‖iteratedDeriv k f t‖ ≤
            T ^ a * ‖iteratedDeriv k f t‖ := by gcongr
        _ ≤ T ^ a * SchwartzMap.seminorm ℂ 0 k f := by
          gcongr
          have hsem := SchwartzMap.le_seminorm ℂ 0 k f t
          rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hsem
          simpa only [pow_zero, one_mul] using hsem

theorem tendsto_seminorm_of_tsupport_subset_of_tendsto_seminorm_zero
    {ι : Type*} {l : Filter ι} {T : ℝ} (hT : 0 ≤ T)
    (F : ι → SchwartzMap ℝ ℂ)
    (hF : ∀ i, tsupport (F i) ⊆ {t : ℝ | |t| ≤ T})
    {k : ℕ}
    (hzero : Tendsto (fun i => SchwartzMap.seminorm ℂ 0 k (F i)) l (nhds 0))
    (a : ℕ) :
    Tendsto (fun i => SchwartzMap.seminorm ℂ a k (F i)) l (nhds 0) := by
  have hbound : Tendsto
      (fun i => T ^ a * SchwartzMap.seminorm ℂ 0 k (F i)) l (nhds 0) := by
    simpa using hzero.const_mul (T ^ a)
  exact squeeze_zero (fun i => by positivity)
    (fun i => seminorm_le_pow_mul_seminorm_zero_of_tsupport_subset hT (F i) (hF i) a k)
    hbound

/-- For a uniformly compactly supported family, convergence of all zero-spatial-weight
derivative seminorms is exactly the remaining input needed for full Schwartz convergence. -/
theorem tendsto_zero_of_uniform_tsupport_of_tendsto_zero_weight_seminorms
    {ι : Type*} {l : Filter ι} {T : ℝ} (hT : 0 ≤ T)
    (F : ι → SchwartzMap ℝ ℂ)
    (hF : ∀ i, tsupport (F i) ⊆ {t : ℝ | |t| ≤ T})
    (hzero : ∀ k : ℕ,
      Tendsto (fun i => SchwartzMap.seminorm ℂ 0 k (F i)) l (nhds 0)) :
    Tendsto F l (nhds 0) := by
  apply tendsto_zero_of_tendsto_seminorm F
  intro a k
  exact tendsto_seminorm_of_tsupport_subset_of_tendsto_seminorm_zero
    hT F hF (hzero k) a

/-- Spectral momentum centered at the real coordinate `lambda`. -/
def centeredSpectralMomentumCLM (lambda : ℝ) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  spectralMomentumCLM - (lambda : ℂ) • ContinuousLinearMap.id ℂ _

@[simp] theorem centeredSpectralMomentumCLM_apply
    (lambda : ℝ) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    centeredSpectralMomentumCLM lambda f t =
      ((2 * Real.pi * t - lambda : ℝ) : ℂ) * f t := by
  simp [centeredSpectralMomentumCLM, spectralMomentumCLM_apply,
    spectralMomentumMultiplier]
  ring

/-- Centering by a real scalar preserves symmetry of the spectral momentum. -/
theorem ContinuousSchwartzSesquilinearForm.fourierPullback_centeredSpectralMomentum_symmetric
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (lambda : ℝ) (f g : SchwartzMap ℝ ℂ) :
    Q.fourierPullback (centeredSpectralMomentumCLM lambda f) g =
      Q.fourierPullback f (centeredSpectralMomentumCLM lambda g) := by
  change Q.fourierPullback
      (spectralMomentumCLM f - (lambda : ℂ) • f) g =
    Q.fourierPullback f (spectralMomentumCLM g - (lambda : ℂ) • g)
  rw [Q.fourierPullback.apply_sub_left, Q.fourierPullback.apply_smul_left,
    Q.fourierPullback.apply_sub_right, Q.fourierPullback.apply_smul_right,
    Q.fourierPullback_spectralMomentumSymmetric hQ]
  simp

/-- The positive centered quadratic spectral separator
`C⁻¹(1 + (2πt-lambda)²)`. -/
def quadraticSpectralSeparatorCLM (lambda C : ℝ) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  (C⁻¹ : ℂ) •
    (1 + centeredSpectralMomentumCLM lambda * centeredSpectralMomentumCLM lambda)

@[simp] theorem quadraticSpectralSeparatorCLM_apply
    (lambda C : ℝ) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    quadraticSpectralSeparatorCLM lambda C f t =
      (((1 + (2 * Real.pi * t - lambda) ^ 2) / C : ℝ) : ℂ) * f t := by
  simp [quadraticSpectralSeparatorCLM, centeredSpectralMomentumCLM_apply]
  ring

/-- Pointwise powers of the quadratic separator are the corresponding scalar multiplier
powers. -/
theorem quadraticSpectralSeparatorCLM_pow_apply
    (lambda C : ℝ) (n : ℕ) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    (quadraticSpectralSeparatorCLM lambda C ^ n) f t =
      ((((1 + (2 * Real.pi * t - lambda) ^ 2) / C) ^ n : ℝ) : ℂ) * f t := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_apply_eq_comp, ih,
        quadraticSpectralSeparatorCLM_apply]
      push_cast
      ring

/-- Scalar multiplier underlying the centered quadratic separator. -/
def quadraticSpectralSeparatorMultiplier (lambda C t : ℝ) : ℝ :=
  (1 + (2 * Real.pi * t - lambda) ^ 2) / C

theorem contDiff_quadraticSpectralSeparatorMultiplier (lambda C : ℝ) :
    ContDiff ℝ ⊤ (quadraticSpectralSeparatorMultiplier lambda C) := by
  unfold quadraticSpectralSeparatorMultiplier
  fun_prop

theorem hasDerivAt_quadraticSpectralSeparatorMultiplier
    (lambda C t : ℝ) :
  HasDerivAt (quadraticSpectralSeparatorMultiplier lambda C)
      (4 * Real.pi * (2 * Real.pi * t - lambda) / C) t := by
  unfold quadraticSpectralSeparatorMultiplier
  have hu : HasDerivAt (fun x : ℝ => 2 * Real.pi * x - lambda)
      (2 * Real.pi) t := by
    convert ((hasDerivAt_id t).const_mul (2 * Real.pi)).sub_const lambda using 1
    all_goals first | rfl | exact Subsingleton.elim _ _ | ring
  convert (((hasDerivAt_const t 1).add (hu.pow 2)).div_const C) using 1
  all_goals first | rfl | exact Subsingleton.elim _ _ | ring

/-- Exact all-order derivative expansion for powers of the quadratic separator.  Every summand
contains the falling-factorial/geometric factor isolated by
`tendsto_natDescFactorial_mul_pow_sub_zero` below. -/
theorem iteratedDeriv_quadraticSpectralSeparatorMultiplier_pow
    (lambda C : ℝ) (n i : ℕ) (t : ℝ) :
    iteratedDeriv i
        (fun x => quadraticSpectralSeparatorMultiplier lambda C x ^ n) t =
      ∑ c : OrderedFinpartition i,
        (∏ j, iteratedDeriv (c.partSize j)
          (quadraticSpectralSeparatorMultiplier lambda C) t) *
        (n.descFactorial c.length *
          quadraticSpectralSeparatorMultiplier lambda C t ^ (n - c.length)) := by
  exact iteratedDeriv_pow_comp_eq_orderedFinpartition
    (quadraticSpectralSeparatorMultiplier lambda C)
    ((contDiff_quadraticSpectralSeparatorMultiplier lambda C).of_le (by simp)) n i t

/-- Product rule for a power of the quadratic separator multiplier. -/
theorem deriv_quadraticSpectralSeparator_pow_mul
    (lambda C : ℝ) (n : ℕ) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    deriv (fun x : ℝ =>
      (quadraticSpectralSeparatorMultiplier lambda C x : ℂ) ^ n * f x) t =
      (n : ℂ) * (quadraticSpectralSeparatorMultiplier lambda C t : ℂ) ^ (n - 1) *
          (4 * Real.pi * (2 * Real.pi * t - lambda) / C : ℝ) * f t +
        (quadraticSpectralSeparatorMultiplier lambda C t : ℂ) ^ n * deriv f t := by
  have hm : HasDerivAt
      (fun x : ℝ => (quadraticSpectralSeparatorMultiplier lambda C x : ℂ))
      (4 * Real.pi * (2 * Real.pi * t - lambda) / C : ℝ) t := by
    exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_quadraticSpectralSeparatorMultiplier lambda C t)
  have hf : HasDerivAt (fun x : ℝ => f x) (deriv f t) t :=
    f.differentiable.differentiableAt.hasDerivAt
  have hfun :
      (fun x : ℝ =>
        (quadraticSpectralSeparatorMultiplier lambda C x : ℂ) ^ n * f x) =
      (fun x : ℝ => (quadraticSpectralSeparatorMultiplier lambda C x : ℂ)) ^ n *
        fun x : ℝ => f x := by
    funext x
    rw [Pi.mul_apply, Pi.pow_apply]
  rw [hfun]
  simpa only [Pi.pow_apply, Pi.mul_apply] using ((hm.pow n).mul hf).deriv

theorem iteratedDeriv_two_quadraticSpectralSeparatorMultiplier
    (lambda C t : ℝ) :
    iteratedDeriv 2 (quadraticSpectralSeparatorMultiplier lambda C) t =
      8 * Real.pi ^ 2 / C := by
  rw [show iteratedDeriv 2
      (quadraticSpectralSeparatorMultiplier lambda C) t =
      deriv (deriv (quadraticSpectralSeparatorMultiplier lambda C)) t by
        rw [show 2 = 1 + 1 by norm_num, congrFun iteratedDeriv_succ' t,
          congrFun iteratedDeriv_one t]]
  have hderiv : deriv (quadraticSpectralSeparatorMultiplier lambda C) =
      fun x => 4 * Real.pi * (2 * Real.pi * x - lambda) / C := by
    funext x
    exact (hasDerivAt_quadraticSpectralSeparatorMultiplier lambda C x).deriv
  rw [hderiv]
  have h : HasDerivAt (fun x : ℝ => 4 * Real.pi * (2 * Real.pi * x - lambda) / C)
      (8 * Real.pi ^ 2 / C) t := by
    convert (((((hasDerivAt_id t).const_mul (2 * Real.pi)).sub_const lambda).const_mul
      (4 * Real.pi)).div_const C) using 1
    all_goals first | rfl | exact Subsingleton.elim _ _ | ring
  exact h.deriv

theorem iteratedDeriv_add_three_quadraticSpectralSeparatorMultiplier
    (lambda C t : ℝ) (k : ℕ) :
    iteratedDeriv (k + 3) (quadraticSpectralSeparatorMultiplier lambda C) t = 0 := by
  rw [show k + 3 = (k + 2) + 1 by omega, congrFun iteratedDeriv_succ' t,
    show k + 2 = (k + 1) + 1 by omega, congrFun iteratedDeriv_succ' t]
  have hdd : deriv (deriv (quadraticSpectralSeparatorMultiplier lambda C)) =
      fun _x => 8 * Real.pi ^ 2 / C := by
    funext x
    have h2 := iteratedDeriv_two_quadraticSpectralSeparatorMultiplier lambda C x
    rw [show iteratedDeriv 2
        (quadraticSpectralSeparatorMultiplier lambda C) x =
        deriv (deriv (quadraticSpectralSeparatorMultiplier lambda C)) x by
          rw [show 2 = 1 + 1 by norm_num, congrFun iteratedDeriv_succ' x,
            congrFun iteratedDeriv_one x]] at h2
    exact h2
  rw [hdd, iteratedDeriv_const]
  simp

/-- Canonical scale strictly between the inner and outer quadratic levels. -/
def quadraticSeparationScale (r R : ℝ) : ℝ :=
  1 + (r ^ 2 + R ^ 2) / 2

/-- An explicit ordinary-coordinate bound for a packet bounded in the centered spectral
coordinate. -/
def quadraticPacketCoordinateBound (lambda r : ℝ) : ℝ :=
  (|lambda| + r) / (2 * Real.pi)

theorem quadraticPacketCoordinateBound_nonneg
    (lambda : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ quadraticPacketCoordinateBound lambda r := by
  unfold quadraticPacketCoordinateBound
  positivity

theorem abs_le_quadraticPacketCoordinateBound
    {lambda r t : ℝ} (ht : |2 * Real.pi * t - lambda| ≤ r) :
    |t| ≤ quadraticPacketCoordinateBound lambda r := by
  have htri : |2 * Real.pi * t| ≤ |2 * Real.pi * t - lambda| + |lambda| := by
    calc
      |2 * Real.pi * t| = |(2 * Real.pi * t - lambda) + lambda| := by ring_nf
      _ ≤ |2 * Real.pi * t - lambda| + |lambda| := abs_add_le _ _
  have hmul : 2 * Real.pi * |t| ≤ r + |lambda| := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos Real.pi_pos] at htri
    linarith
  unfold quadraticPacketCoordinateBound
  rw [le_div_iff₀ (mul_pos (by norm_num) Real.pi_pos)]
  linarith

/-- Multiplying by a separator power does not enlarge topological support. -/
theorem tsupport_quadraticSpectralSeparator_pow_subset
    (lambda C : ℝ) (n : ℕ) (f : SchwartzMap ℝ ℂ) :
    tsupport ((quadraticSpectralSeparatorCLM lambda C ^ n) f) ⊆ tsupport f := by
  apply closure_mono
  intro t ht
  change ((quadraticSpectralSeparatorCLM lambda C ^ n) f) t ≠ 0 at ht
  change f t ≠ 0
  intro hft
  rw [quadraticSpectralSeparatorCLM_pow_apply, hft, mul_zero] at ht
  exact ht rfl

theorem tsupport_quadraticSpectralSeparator_pow_packet
    {lambda r R : ℝ} (f : SchwartzMap ℝ ℂ)
    (hf : tsupport f ⊆ {t : ℝ | |2 * Real.pi * t - lambda| ≤ r})
    (n : ℕ) :
    tsupport ((quadraticSpectralSeparatorCLM lambda (quadraticSeparationScale r R) ^ n) f) ⊆
      {t : ℝ | |t| ≤ quadraticPacketCoordinateBound lambda r} := by
  intro t ht
  have htf := tsupport_quadraticSpectralSeparator_pow_subset
    lambda (quadraticSeparationScale r R) n f ht
  exact abs_le_quadraticPacketCoordinateBound (hf htf)

theorem quadraticSeparationScale_pos (r R : ℝ) :
    0 < quadraticSeparationScale r R := by
  unfold quadraticSeparationScale
  positivity

/-- On an inner packet `|u| ≤ r`, the canonical quadratic separator is uniformly below one. -/
theorem quadraticSeparator_inner_lt_one
    {r R u : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) (hrR : r < R)
    (hu : |u| ≤ r) :
    (1 + u ^ 2) / quadraticSeparationScale r R < 1 := by
  have hu2 : u ^ 2 ≤ r ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg u) hr).2 hu
  have hr2 : r ^ 2 < R ^ 2 := (sq_lt_sq₀ hr hR).2 hrR
  have hC := quadraticSeparationScale_pos r R
  rw [div_lt_one hC]
  unfold quadraticSeparationScale
  nlinarith

/-- On an outer packet `R ≤ |u|`, the reciprocal canonical separator is uniformly below one. -/
theorem quadraticSeparator_outer_inv_lt_one
    {r R u : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) (hrR : r < R)
    (hu : R ≤ |u|) :
    quadraticSeparationScale r R / (1 + u ^ 2) < 1 := by
  have hu2 : R ^ 2 ≤ u ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ hR (abs_nonneg u)).2 hu
  have hr2 : r ^ 2 < R ^ 2 := (sq_lt_sq₀ hr hR).2 hrR
  have hden : 0 < 1 + u ^ 2 := by positivity
  rw [div_lt_one hden]
  unfold quadraticSeparationScale
  nlinarith

/-- A uniform bound for every derivative of the quadratic separator on an inner packet. -/
def quadraticInnerDerivativeBound (r R : ℝ) : ℝ :=
  let C := quadraticSeparationScale r R
  let q := (1 + r ^ 2) / C
  let L := 4 * Real.pi * r / C
  let B := 8 * Real.pi ^ 2 / C
  1 + q + L + B

theorem quadraticInnerDerivativeBound_nonneg
    {r R : ℝ} (hr : 0 ≤ r) :
    0 ≤ quadraticInnerDerivativeBound r R := by
  unfold quadraticInnerDerivativeBound
  have hC := quadraticSeparationScale_pos r R
  positivity

theorem norm_iteratedDeriv_quadraticSpectralSeparatorMultiplier_le
    {lambda r R t : ℝ} (hr : 0 ≤ r)
    (ht : |2 * Real.pi * t - lambda| ≤ r) (j : ℕ) :
    ‖iteratedDeriv j
      (quadraticSpectralSeparatorMultiplier lambda (quadraticSeparationScale r R)) t‖ ≤
      quadraticInnerDerivativeBound r R := by
  let C := quadraticSeparationScale r R
  let q := (1 + r ^ 2) / C
  let L := 4 * Real.pi * r / C
  let B := 8 * Real.pi ^ 2 / C
  have hC : 0 < C := quadraticSeparationScale_pos r R
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  obtain _ | _ | _ | k := j
  · rw [iteratedDeriv_zero, Real.norm_eq_abs]
    have hm0 : 0 ≤ quadraticSpectralSeparatorMultiplier lambda C t := by
      unfold quadraticSpectralSeparatorMultiplier
      positivity
    rw [abs_of_nonneg hm0]
    have ht2 : (2 * Real.pi * t - lambda) ^ 2 ≤ r ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr).2 ht
    have hm : quadraticSpectralSeparatorMultiplier lambda C t ≤ q := by
      unfold quadraticSpectralSeparatorMultiplier
      dsimp [q]
      exact div_le_div_of_nonneg_right (by linarith) hC.le
    unfold quadraticInnerDerivativeBound
    dsimp only
    linarith
  · rw [congrFun iteratedDeriv_one t,
      (hasDerivAt_quadraticSpectralSeparatorMultiplier lambda C t).deriv,
      Real.norm_eq_abs]
    have hmp : |4 * Real.pi * (2 * Real.pi * t - lambda) / C| ≤ L := by
      dsimp [L]
      rw [abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
        abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hC]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left ht (mul_nonneg (by norm_num) Real.pi_pos.le)) hC.le
    unfold quadraticInnerDerivativeBound
    dsimp only
    linarith
  · rw [iteratedDeriv_two_quadraticSpectralSeparatorMultiplier]
    change |B| ≤ quadraticInnerDerivativeBound r R
    rw [abs_of_nonneg hB0]
    unfold quadraticInnerDerivativeBound
    dsimp only
    linarith
  · rw [show k + 3 = k + 3 by rfl,
      iteratedDeriv_add_three_quadraticSpectralSeparatorMultiplier lambda C t k,
      norm_zero]
    exact quadraticInnerDerivativeBound_nonneg hr

/-- Zeroth Schwartz-seminorm contraction on an inner quadratic packet.  This is the base case of
the full all-seminorm compact-packet contraction theorem. -/
theorem seminorm_zero_zero_quadraticSpectralSeparator_pow_le
    {lambda r R : ℝ} (hr : 0 ≤ r)
    (f : SchwartzMap ℝ ℂ)
    (hf : ∀ t : ℝ, f t ≠ 0 → |2 * Real.pi * t - lambda| ≤ r)
    (n : ℕ) :
    SchwartzMap.seminorm ℂ 0 0
        ((quadraticSpectralSeparatorCLM lambda (quadraticSeparationScale r R) ^ n) f) ≤
      ((1 + r ^ 2) / quadraticSeparationScale r R) ^ n *
        SchwartzMap.seminorm ℂ 0 0 f := by
  apply SchwartzMap.seminorm_le_bound' (𝕜 := ℂ) 0 0
  · exact mul_nonneg
      (pow_nonneg (div_nonneg (by positivity)
        (quadraticSeparationScale_pos r R).le) n)
      (by positivity)
  · intro t
    simp only [pow_zero, one_mul, iteratedDeriv_zero]
    rw [quadraticSpectralSeparatorCLM_pow_apply]
    rw [norm_mul, norm_real, Real.norm_eq_abs]
    let C := quadraticSeparationScale r R
    have hC : 0 < C := quadraticSeparationScale_pos r R
    have hq0 : 0 ≤ (1 + r ^ 2) / C := div_nonneg (by positivity) hC.le
    by_cases hft : f t = 0
    · rw [hft, norm_zero, mul_zero]
      positivity
    · have hu := hf t hft
      have hu2 : (2 * Real.pi * t - lambda) ^ 2 ≤ r ^ 2 := by
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) hr).2 hu
      have hm0 : 0 ≤ (1 + (2 * Real.pi * t - lambda) ^ 2) / C :=
        div_nonneg (by positivity) hC.le
      have hm : (1 + (2 * Real.pi * t - lambda) ^ 2) / C ≤
          (1 + r ^ 2) / C := by
        exact div_le_div_of_nonneg_right (by linarith) hC.le
      rw [abs_of_nonneg (pow_nonneg hm0 n)]
      calc
        ((1 + (2 * Real.pi * t - lambda) ^ 2) / C) ^ n * ‖f t‖ ≤
            ((1 + r ^ 2) / C) ^ n * ‖f t‖ := by gcongr
        _ ≤ ((1 + r ^ 2) / C) ^ n * SchwartzMap.seminorm ℂ 0 0 f := by
          gcongr
          simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero] using
            SchwartzMap.le_seminorm ℂ 0 0 f t

/-- The direct separator powers converge to zero in the zeroth Schwartz seminorm on every strict
inner packet.  Higher derivative seminorms require the corresponding polynomial-times-geometric
decay estimate and remain the next analytic layer. -/
theorem tendsto_seminorm_zero_zero_quadraticSpectralSeparator_pow_zero
    {lambda r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) (hrR : r < R)
    (f : SchwartzMap ℝ ℂ)
    (hf : ∀ t : ℝ, f t ≠ 0 → |2 * Real.pi * t - lambda| ≤ r) :
    Tendsto
      (fun n : ℕ => SchwartzMap.seminorm ℂ 0 0
        ((quadraticSpectralSeparatorCLM lambda (quadraticSeparationScale r R) ^ n) f))
      atTop (𝓝 0) := by
  let q : ℝ := (1 + r ^ 2) / quadraticSeparationScale r R
  have hq0 : 0 ≤ q := div_nonneg (by positivity) (quadraticSeparationScale_pos r R).le
  have hqlt : q < 1 := by
    exact quadraticSeparator_inner_lt_one hr hR hrR (by simp [abs_of_nonneg hr])
  have hpow : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hqlt
  have hbound : Tendsto
      (fun n : ℕ => q ^ n * SchwartzMap.seminorm ℂ 0 0 f) atTop (𝓝 0) := by
    simpa using hpow.mul_const (SchwartzMap.seminorm ℂ 0 0 f)
  exact squeeze_zero (fun n => by positivity)
    (fun n => seminorm_zero_zero_quadraticSpectralSeparator_pow_le hr f hf n)
    hbound

/-- First-derivative Schwartz-seminorm estimate on an inner quadratic packet.  The derivative of
the separator contributes the expected linear factor in the power, while the packet gap retains
geometric decay. -/
theorem seminorm_zero_one_quadraticSpectralSeparator_pow_le
    {lambda r R : ℝ} (hr : 0 ≤ r)
    (f : SchwartzMap ℝ ℂ)
    (hf : tsupport f ⊆ {t : ℝ | |2 * Real.pi * t - lambda| ≤ r})
    (n : ℕ) :
    SchwartzMap.seminorm ℂ 0 1
        ((quadraticSpectralSeparatorCLM lambda (quadraticSeparationScale r R) ^ n) f) ≤
      (n : ℝ) * ((1 + r ^ 2) / quadraticSeparationScale r R) ^ (n - 1) *
          (4 * Real.pi * r / quadraticSeparationScale r R) *
          SchwartzMap.seminorm ℂ 0 0 f +
        ((1 + r ^ 2) / quadraticSeparationScale r R) ^ n *
          SchwartzMap.seminorm ℂ 0 1 f := by
  let C := quadraticSeparationScale r R
  let q := (1 + r ^ 2) / C
  let L := 4 * Real.pi * r / C
  have hC : 0 < C := quadraticSeparationScale_pos r R
  have hq0 : 0 ≤ q := div_nonneg (by positivity) hC.le
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  apply SchwartzMap.seminorm_le_bound' (𝕜 := ℂ) 0 1
  · positivity
  · intro t
    simp only [pow_zero, one_mul]
    rw [show iteratedDeriv 1
        (fun x : ℝ => ((quadraticSpectralSeparatorCLM lambda C ^ n) f) x) t =
      deriv (fun x : ℝ =>
        (quadraticSpectralSeparatorMultiplier lambda C x : ℂ) ^ n * f x) t by
          rw [congrFun iteratedDeriv_one t]
          congr 1
          funext x
          rw [quadraticSpectralSeparatorCLM_pow_apply]
          simp only [quadraticSpectralSeparatorMultiplier]
          push_cast
          ring]
    rw [deriv_quadraticSpectralSeparator_pow_mul]
    by_cases ht : f t ≠ 0 ∨ deriv f t ≠ 0
    · have htSupp : t ∈ tsupport f := by
        rcases ht with hft | hdt
        · exact subset_tsupport _ hft
        · exact support_deriv_subset hdt
      have hu := hf htSupp
      have hu2 : (2 * Real.pi * t - lambda) ^ 2 ≤ r ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr).2 hu
      have hm0 : 0 ≤ quadraticSpectralSeparatorMultiplier lambda C t := by
        dsimp [quadraticSpectralSeparatorMultiplier]
        positivity
      have hm : quadraticSpectralSeparatorMultiplier lambda C t ≤ q := by
        dsimp [quadraticSpectralSeparatorMultiplier, q]
        exact div_le_div_of_nonneg_right (by linarith) hC.le
      have hmp : |4 * Real.pi * (2 * Real.pi * t - lambda) / C| ≤ L := by
        dsimp [L]
        rw [abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
          abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hC]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hu (mul_nonneg (by norm_num) Real.pi_pos.le)) hC.le
      have hmnorm : ‖(quadraticSpectralSeparatorMultiplier lambda C t : ℂ)‖ ≤ q := by
        simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm0] using hm
      have hmpnorm :
          ‖(4 * Real.pi * (2 * Real.pi * t - lambda) / C : ℝ)‖ ≤ L := by
        simpa only [Real.norm_eq_abs] using hmp
      have hf0 : ‖f t‖ ≤ SchwartzMap.seminorm ℂ 0 0 f := by
        simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero] using
          SchwartzMap.le_seminorm ℂ 0 0 f t
      have hf1 : ‖deriv f t‖ ≤ SchwartzMap.seminorm ℂ 0 1 f := by
        have h := SchwartzMap.le_seminorm ℂ 0 1 f t
        rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
        simpa only [pow_zero, one_mul, iteratedDeriv_one] using h
      calc
        ‖(n : ℂ) * (quadraticSpectralSeparatorMultiplier lambda C t : ℂ) ^ (n - 1) *
              (4 * Real.pi * (2 * Real.pi * t - lambda) / C : ℝ) * f t +
            (quadraticSpectralSeparatorMultiplier lambda C t : ℂ) ^ n * deriv f t‖ ≤
            ‖(n : ℂ) * (quadraticSpectralSeparatorMultiplier lambda C t : ℂ) ^ (n - 1) *
              (4 * Real.pi * (2 * Real.pi * t - lambda) / C : ℝ) * f t‖ +
            ‖(quadraticSpectralSeparatorMultiplier lambda C t : ℂ) ^ n * deriv f t‖ :=
          norm_add_le _ _
        _ ≤ (n : ℝ) * q ^ (n - 1) * L * ‖f t‖ + q ^ n * ‖deriv f t‖ := by
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, norm_pow,
            Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_pow,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm0]
          gcongr
        _ ≤ (n : ℝ) * q ^ (n - 1) * L * SchwartzMap.seminorm ℂ 0 0 f +
            q ^ n * SchwartzMap.seminorm ℂ 0 1 f := by
          gcongr
    · push Not at ht
      rw [ht.1, ht.2]
      simp only [mul_zero, add_zero, norm_zero]
      positivity

/-- Every fixed falling-factorial loss is absorbed by a strict geometric packet gap. -/
theorem tendsto_natDescFactorial_mul_pow_sub_zero
    (k : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun n : ℕ => (n.descFactorial k : ℝ) * q ^ (n - k))
      atTop (nhds 0) := by
  by_cases hq : q = 0
  · rw [hq]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    have hsub : n - k ≠ 0 := by omega
    simp [hsub]
  · have hpoly := tendsto_pow_const_mul_const_pow_of_lt_one k hq0 hq1
    have hscaled : Tendsto (fun n : ℕ => (n : ℝ) ^ k * q ^ n * (q ^ k)⁻¹)
        atTop (nhds 0) := by
      simpa using hpoly.mul_const ((q ^ k)⁻¹)
    have hupper : Tendsto (fun n : ℕ => (n : ℝ) ^ k * q ^ (n - k))
        atTop (nhds 0) := by
      apply hscaled.congr'
      filter_upwards [eventually_ge_atTop k] with n hn
      have hpow : q ^ n = q ^ (n - k) * q ^ k := by
        calc
          q ^ n = q ^ ((n - k) + k) := by congr 1; omega
          _ = q ^ (n - k) * q ^ k := pow_add q (n - k) k
      calc
        (n : ℝ) ^ k * q ^ n * (q ^ k)⁻¹ =
            (n : ℝ) ^ k * (q ^ (n - k) * q ^ k) * (q ^ k)⁻¹ := by rw [hpow]
        _ = (n : ℝ) ^ k * q ^ (n - k) := by field_simp
    exact squeeze_zero (fun n => by positivity)
      (fun n => by
        gcongr
        exact_mod_cast Nat.descFactorial_le_pow n k)
      hupper

/-- Linear times geometric decay in the predecessor exponent. -/
theorem tendsto_natCast_mul_pow_pred_zero
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) * q ^ (n - 1)) atTop (nhds 0) := by
  simpa using tendsto_natDescFactorial_mul_pow_sub_zero 1 hq0 hq1

/-- A finite Faà-di-Bruno envelope for the `i`th derivative of the `n`th separator power. -/
def quadraticPowerDerivativeEnvelope (r R : ℝ) (i n : ℕ) : ℝ :=
  let C := quadraticSeparationScale r R
  let q := (1 + r ^ 2) / C
  let D := quadraticInnerDerivativeBound r R
  ∑ c : OrderedFinpartition i,
    D ^ c.length * (n.descFactorial c.length : ℝ) * q ^ (n - c.length)

theorem quadraticPowerDerivativeEnvelope_nonneg
    {r R : ℝ} (hr : 0 ≤ r) (i n : ℕ) :
    0 ≤ quadraticPowerDerivativeEnvelope r R i n := by
  unfold quadraticPowerDerivativeEnvelope
  have hD : 0 ≤ quadraticInnerDerivativeBound r R :=
    quadraticInnerDerivativeBound_nonneg hr
  have hq : 0 ≤ (1 + r ^ 2) / quadraticSeparationScale r R := by
    exact div_nonneg (by positivity) (quadraticSeparationScale_pos r R).le
  apply Finset.sum_nonneg
  intro c _hc
  exact mul_nonneg (mul_nonneg (pow_nonneg hD _) (Nat.cast_nonneg _))
    (pow_nonneg hq _)

theorem tendsto_quadraticPowerDerivativeEnvelope_zero
    {r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) (hrR : r < R) (i : ℕ) :
    Tendsto (quadraticPowerDerivativeEnvelope r R i) atTop (nhds 0) := by
  let C := quadraticSeparationScale r R
  let q := (1 + r ^ 2) / C
  let D := quadraticInnerDerivativeBound r R
  have hq0 : 0 ≤ q := by
    dsimp [q, C]
    exact div_nonneg (by positivity) (quadraticSeparationScale_pos r R).le
  have hq1 : q < 1 := by
    exact quadraticSeparator_inner_lt_one hr hR hrR (by simp [abs_of_nonneg hr])
  change Tendsto (fun n : ℕ => ∑ c : OrderedFinpartition i,
      D ^ c.length * (n.descFactorial c.length : ℝ) * q ^ (n - c.length))
    atTop (nhds 0)
  have hsum := tendsto_finsetSum Finset.univ
    (fun (c : OrderedFinpartition i) _hc => by
      simpa [mul_assoc] using
        (tendsto_natDescFactorial_mul_pow_sub_zero c.length hq0 hq1).const_mul
          (D ^ c.length))
  simpa only [mul_assoc, Finset.sum_const_zero] using hsum

theorem norm_iteratedDeriv_quadraticSpectralSeparatorMultiplier_pow_le
    {lambda r R t : ℝ} (hr : 0 ≤ r)
    (ht : |2 * Real.pi * t - lambda| ≤ r) (i n : ℕ) :
    ‖iteratedDeriv i
      (fun x => quadraticSpectralSeparatorMultiplier lambda
        (quadraticSeparationScale r R) x ^ n) t‖ ≤
      quadraticPowerDerivativeEnvelope r R i n := by
  let C := quadraticSeparationScale r R
  let q := (1 + r ^ 2) / C
  let D := quadraticInnerDerivativeBound r R
  have hC : 0 < C := quadraticSeparationScale_pos r R
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hD0 : 0 ≤ D := quadraticInnerDerivativeBound_nonneg hr
  have hm0 : 0 ≤ quadraticSpectralSeparatorMultiplier lambda C t := by
    unfold quadraticSpectralSeparatorMultiplier
    positivity
  have ht2 : (2 * Real.pi * t - lambda) ^ 2 ≤ r ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr).2 ht
  have hm : quadraticSpectralSeparatorMultiplier lambda C t ≤ q := by
    unfold quadraticSpectralSeparatorMultiplier
    dsimp [q]
    exact div_le_div_of_nonneg_right (by linarith) hC.le
  rw [iteratedDeriv_quadraticSpectralSeparatorMultiplier_pow]
  calc
    ‖∑ c : OrderedFinpartition i,
        (∏ j, iteratedDeriv (c.partSize j)
          (quadraticSpectralSeparatorMultiplier lambda C) t) *
        (n.descFactorial c.length *
          quadraticSpectralSeparatorMultiplier lambda C t ^ (n - c.length))‖ ≤
      ∑ c : OrderedFinpartition i,
        ‖(∏ j, iteratedDeriv (c.partSize j)
          (quadraticSpectralSeparatorMultiplier lambda C) t) *
        (n.descFactorial c.length *
          quadraticSpectralSeparatorMultiplier lambda C t ^ (n - c.length))‖ :=
      norm_sum_le _ _
    _ ≤ quadraticPowerDerivativeEnvelope r R i n := by
      unfold quadraticPowerDerivativeEnvelope
      dsimp only
      apply Finset.sum_le_sum
      intro c _hc
      rw [norm_mul, norm_prod, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg (n.descFactorial c.length)), abs_pow,
        abs_of_nonneg hm0]
      have hprod : (∏ j, ‖iteratedDeriv (c.partSize j)
          (quadraticSpectralSeparatorMultiplier lambda C) t‖) ≤
          D ^ c.length := by
        calc
          (∏ j, ‖iteratedDeriv (c.partSize j)
              (quadraticSpectralSeparatorMultiplier lambda C) t‖) ≤
              ∏ _j : Fin c.length, D :=
            Finset.prod_le_prod (fun j _hj => norm_nonneg _)
              (fun j _hj => norm_iteratedDeriv_quadraticSpectralSeparatorMultiplier_le
                hr ht (c.partSize j))
          _ = D ^ c.length := by simp
      have hdf : 0 ≤ (n.descFactorial c.length : ℝ) := Nat.cast_nonneg _
      have hmpow : 0 ≤ quadraticSpectralSeparatorMultiplier lambda C t ^
          (n - c.length) := pow_nonneg hm0 _
      calc
        (∏ j, ‖iteratedDeriv (c.partSize j)
            (quadraticSpectralSeparatorMultiplier lambda C) t‖) *
            ((n.descFactorial c.length : ℝ) *
              quadraticSpectralSeparatorMultiplier lambda C t ^ (n - c.length)) ≤
            D ^ c.length * ((n.descFactorial c.length : ℝ) *
              quadraticSpectralSeparatorMultiplier lambda C t ^ (n - c.length)) :=
          mul_le_mul_of_nonneg_right hprod (mul_nonneg hdf hmpow)
        _ ≤ D ^ c.length * ((n.descFactorial c.length : ℝ) *
              q ^ (n - c.length)) := by
          gcongr
        _ = D ^ c.length * (n.descFactorial c.length : ℝ) *
              q ^ (n - c.length) := by ring

theorem iteratedDeriv_eq_zero_of_not_mem_tsupport
    (f : SchwartzMap ℝ ℂ) (k : ℕ) {t : ℝ} (ht : t ∉ tsupport f) :
    iteratedDeriv k f t = 0 := by
  have hF : iteratedFDeriv ℝ k f t = 0 := by
    by_contra hne
    exact ht (support_iteratedFDeriv_subset k hne)
  apply norm_eq_zero.mp
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, hF, norm_zero]

theorem iteratedDeriv_ofReal
    (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (i : ℕ) (t : ℝ) :
    iteratedDeriv i (fun x => (h x : ℂ)) t =
      ((iteratedDeriv i h t : ℝ) : ℂ) := by
  rw [show (fun x => (h x : ℂ)) = fun x => h x • (1 : ℂ) by
    funext x
    simp]
  rw [iteratedDeriv_smul_const (hh.contDiffAt.of_le
    (by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))) (1 : ℂ)]
  simp

/-- The complete Leibniz--Faà-di-Bruno envelope for a separator power acting on a fixed Schwartz
packet. -/
def quadraticSchwartzDerivativeEnvelope
    (f : SchwartzMap ℝ ℂ) (r R : ℝ) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * quadraticPowerDerivativeEnvelope r R i n *
      SchwartzMap.seminorm ℂ 0 (k - i) f

theorem quadraticSchwartzDerivativeEnvelope_nonneg
    (f : SchwartzMap ℝ ℂ) {r R : ℝ} (hr : 0 ≤ r) (k n : ℕ) :
    0 ≤ quadraticSchwartzDerivativeEnvelope f r R k n := by
  unfold quadraticSchwartzDerivativeEnvelope
  apply Finset.sum_nonneg
  intro i _hi
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _)
      (quadraticPowerDerivativeEnvelope_nonneg hr i n))
    (by positivity)

theorem tendsto_quadraticSchwartzDerivativeEnvelope_zero
    (f : SchwartzMap ℝ ℂ) {r R : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) (hrR : r < R) (k : ℕ) :
    Tendsto (quadraticSchwartzDerivativeEnvelope f r R k) atTop (nhds 0) := by
  unfold quadraticSchwartzDerivativeEnvelope
  have hsum := tendsto_finsetSum (Finset.range (k + 1)) (fun i _hi => by
    simpa [mul_assoc] using
      (tendsto_quadraticPowerDerivativeEnvelope_zero hr hR hrR i).const_mul
        ((k.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 (k - i) f))
  simpa only [mul_assoc, mul_comm, mul_left_comm, Finset.sum_const_zero] using hsum

theorem seminorm_zero_quadraticSpectralSeparator_pow_le_envelope
    {lambda r R : ℝ} (hr : 0 ≤ r)
    (f : SchwartzMap ℝ ℂ)
    (hf : tsupport f ⊆ {t : ℝ | |2 * Real.pi * t - lambda| ≤ r})
    (k n : ℕ) :
    SchwartzMap.seminorm ℂ 0 k
      ((quadraticSpectralSeparatorCLM lambda (quadraticSeparationScale r R) ^ n) f) ≤
      quadraticSchwartzDerivativeEnvelope f r R k n := by
  apply SchwartzMap.seminorm_le_bound' (𝕜 := ℂ) 0 k
  · exact quadraticSchwartzDerivativeEnvelope_nonneg f hr k n
  · intro t
    simp only [pow_zero, one_mul]
    rw [show iteratedDeriv k
        (fun x => ((quadraticSpectralSeparatorCLM lambda
          (quadraticSeparationScale r R) ^ n) f) x) t =
        iteratedDeriv k (fun x =>
          (quadraticSpectralSeparatorMultiplier lambda
            (quadraticSeparationScale r R) x ^ n : ℂ) * f x) t by
      congr 1
      funext x
      rw [quadraticSpectralSeparatorCLM_pow_apply]
      simp only [quadraticSpectralSeparatorMultiplier]
      push_cast
      ring]
    rw [iteratedDeriv_real_pow_mul_schwartz_eq_sum
      (quadraticSpectralSeparatorMultiplier lambda (quadraticSeparationScale r R))
      ((contDiff_quadraticSpectralSeparatorMultiplier lambda
        (quadraticSeparationScale r R)).of_le (by simp))]
    by_cases ht : t ∈ tsupport f
    · have hpacket := hf ht
      calc
        ‖∑ i ∈ Finset.range (k + 1),
            (k.choose i : ℂ) *
              iteratedDeriv i (fun x =>
                (quadraticSpectralSeparatorMultiplier lambda
                  (quadraticSeparationScale r R) x ^ n : ℂ)) t *
              iteratedDeriv (k - i) f t‖ ≤
            ∑ i ∈ Finset.range (k + 1),
              ‖(k.choose i : ℂ) *
                iteratedDeriv i (fun x =>
                  (quadraticSpectralSeparatorMultiplier lambda
                    (quadraticSeparationScale r R) x ^ n : ℂ)) t *
                iteratedDeriv (k - i) f t‖ := norm_sum_le _ _
        _ ≤ quadraticSchwartzDerivativeEnvelope f r R k n := by
          unfold quadraticSchwartzDerivativeEnvelope
          apply Finset.sum_le_sum
          intro i _hi
          have hcast : iteratedDeriv i (fun x =>
              (quadraticSpectralSeparatorMultiplier lambda
                (quadraticSeparationScale r R) x : ℂ) ^ n) t =
              ((iteratedDeriv i (fun x =>
                quadraticSpectralSeparatorMultiplier lambda
                  (quadraticSeparationScale r R) x ^ n) t : ℝ) : ℂ) := by
            convert iteratedDeriv_ofReal
              (fun x => quadraticSpectralSeparatorMultiplier lambda
                (quadraticSeparationScale r R) x ^ n)
              ((contDiff_quadraticSpectralSeparatorMultiplier lambda
                (quadraticSeparationScale r R)).pow n |>.of_le (by simp)) i t using 1
            congr 2
            funext x
            push_cast
            rfl
          rw [hcast, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real,
            Real.norm_eq_abs]
          have hpow := norm_iteratedDeriv_quadraticSpectralSeparatorMultiplier_pow_le
            (R := R) hr hpacket i n
          have hpowabs : |iteratedDeriv i (fun x =>
              quadraticSpectralSeparatorMultiplier lambda
                (quadraticSeparationScale r R) x ^ n) t| ≤
              quadraticPowerDerivativeEnvelope r R i n := by
            simpa only [Real.norm_eq_abs] using hpow
          have hfderiv : ‖iteratedDeriv (k - i) f t‖ ≤
              SchwartzMap.seminorm ℂ 0 (k - i) f := by
            have hsem := SchwartzMap.le_seminorm ℂ 0 (k - i) f t
            rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hsem
            simpa only [pow_zero, one_mul] using hsem
          calc
            (k.choose i : ℝ) *
                |iteratedDeriv i (fun x => quadraticSpectralSeparatorMultiplier lambda
                  (quadraticSeparationScale r R) x ^ n) t| *
                ‖iteratedDeriv (k - i) f t‖ =
              (k.choose i : ℝ) *
                (|iteratedDeriv i (fun x => quadraticSpectralSeparatorMultiplier lambda
                  (quadraticSeparationScale r R) x ^ n) t| *
                ‖iteratedDeriv (k - i) f t‖) := by ring
            _ ≤ (k.choose i : ℝ) *
                (quadraticPowerDerivativeEnvelope r R i n *
                  SchwartzMap.seminorm ℂ 0 (k - i) f) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul hpowabs hfderiv (norm_nonneg _)
                  (quadraticPowerDerivativeEnvelope_nonneg hr i n))
                (Nat.cast_nonneg _)
            _ = (k.choose i : ℝ) * quadraticPowerDerivativeEnvelope r R i n *
                SchwartzMap.seminorm ℂ 0 (k - i) f := by ring
    · have hzero : ∀ i ∈ Finset.range (k + 1),
          iteratedDeriv (k - i) f t = 0 := by
        intro i _hi
        exact iteratedDeriv_eq_zero_of_not_mem_tsupport f (k - i) ht
      have hsumzero : ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℂ) *
            iteratedDeriv i (fun x =>
              (quadraticSpectralSeparatorMultiplier lambda
                (quadraticSeparationScale r R) x : ℂ) ^ n) t *
            iteratedDeriv (k - i) f t = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hzero i hi, mul_zero]
      rw [hsumzero, norm_zero]
      exact quadraticSchwartzDerivativeEnvelope_nonneg f hr k n

/-- Direct powers contract every inner compact packet in every derivative seminorm. -/
theorem tendsto_seminorm_zero_all_quadraticSpectralSeparator_pow_zero
    {lambda r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) (hrR : r < R)
    (f : SchwartzMap ℝ ℂ)
    (hf : tsupport f ⊆ {t : ℝ | |2 * Real.pi * t - lambda| ≤ r})
    (k : ℕ) :
    Tendsto (fun n : ℕ => SchwartzMap.seminorm ℂ 0 k
      ((quadraticSpectralSeparatorCLM lambda (quadraticSeparationScale r R) ^ n) f))
      atTop (nhds 0) := by
  exact squeeze_zero (fun n => by positivity)
    (fun n => seminorm_zero_quadraticSpectralSeparator_pow_le_envelope hr f hf k n)
    (tendsto_quadraticSchwartzDerivativeEnvelope_zero f hr hR hrR k)

/-- Direct powers of the quadratic separator converge to zero in the full Schwartz topology on
every strict inner compact packet. -/
theorem tendsto_quadraticSpectralSeparator_pow_zero
    {lambda r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) (hrR : r < R)
    (f : SchwartzMap ℝ ℂ)
    (hf : tsupport f ⊆ {t : ℝ | |2 * Real.pi * t - lambda| ≤ r}) :
    Tendsto
      (fun n : ℕ =>
        (quadraticSpectralSeparatorCLM lambda (quadraticSeparationScale r R) ^ n) f)
      atTop (nhds 0) := by
  apply tendsto_zero_of_uniform_tsupport_of_tendsto_zero_weight_seminorms
    (quadraticPacketCoordinateBound_nonneg lambda hr)
  · exact fun n => tsupport_quadraticSpectralSeparator_pow_packet f hf n
  · exact fun k => tendsto_seminorm_zero_all_quadraticSpectralSeparator_pow_zero
      hr hR hrR f hf k

/-! ## General compact-packet contraction for smooth temperate multipliers -/

def smoothPowerDerivativeEnvelope (D q : ℝ) (i n : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition i,
    D ^ c.length * (n.descFactorial c.length : ℝ) * q ^ (n - c.length)

theorem smoothPowerDerivativeEnvelope_nonneg
    {D q : ℝ} (hD : 0 ≤ D) (hq : 0 ≤ q) (i n : ℕ) :
    0 ≤ smoothPowerDerivativeEnvelope D q i n := by
  unfold smoothPowerDerivativeEnvelope
  apply Finset.sum_nonneg
  intro c _hc
  positivity

theorem tendsto_smoothPowerDerivativeEnvelope_zero
    {D q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (i : ℕ) :
    Tendsto (smoothPowerDerivativeEnvelope D q i) atTop (nhds 0) := by
  unfold smoothPowerDerivativeEnvelope
  have hsum := tendsto_finsetSum Finset.univ
    (fun (c : OrderedFinpartition i) _hc => by
      simpa [mul_assoc] using
        (tendsto_natDescFactorial_mul_pow_sub_zero c.length hq0 hq1).const_mul
          (D ^ c.length))
  simpa only [mul_assoc, Finset.sum_const_zero] using hsum

theorem norm_iteratedDeriv_pow_le_smoothPowerDerivativeEnvelope
    (m : ℝ → ℝ) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    {D q t : ℝ} (hD : 0 ≤ D)
    (hm0 : 0 ≤ m t) (hmq : m t ≤ q) (i n : ℕ)
    (hder : ∀ j : ℕ, j ≤ i → ‖iteratedDeriv j m t‖ ≤ D) :
    ‖iteratedDeriv i (fun x => m x ^ n) t‖ ≤
      smoothPowerDerivativeEnvelope D q i n := by
  rw [iteratedDeriv_pow_comp_eq_orderedFinpartition m hm]
  calc
    ‖∑ c : OrderedFinpartition i,
        (∏ j, iteratedDeriv (c.partSize j) m t) *
          (n.descFactorial c.length * m t ^ (n - c.length))‖ ≤
      ∑ c : OrderedFinpartition i,
        ‖(∏ j, iteratedDeriv (c.partSize j) m t) *
          (n.descFactorial c.length * m t ^ (n - c.length))‖ := norm_sum_le _ _
    _ ≤ smoothPowerDerivativeEnvelope D q i n := by
      unfold smoothPowerDerivativeEnvelope
      apply Finset.sum_le_sum
      intro c _hc
      rw [norm_mul, norm_prod, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg (n.descFactorial c.length)), abs_pow,
        abs_of_nonneg hm0]
      have hprod : (∏ j, ‖iteratedDeriv (c.partSize j) m t‖) ≤ D ^ c.length := by
        calc
          (∏ j, ‖iteratedDeriv (c.partSize j) m t‖) ≤
              ∏ _j : Fin c.length, D :=
            Finset.prod_le_prod (fun j _hj => norm_nonneg _)
              (fun j _hj => hder (c.partSize j) (OrderedFinpartition.partSize_le c j))
          _ = D ^ c.length := by simp
      have hdf : 0 ≤ (n.descFactorial c.length : ℝ) := Nat.cast_nonneg _
      have hmpow : 0 ≤ m t ^ (n - c.length) := pow_nonneg hm0 _
      calc
        (∏ j, ‖iteratedDeriv (c.partSize j) m t‖) *
            ((n.descFactorial c.length : ℝ) * m t ^ (n - c.length)) ≤
          D ^ c.length * ((n.descFactorial c.length : ℝ) * m t ^ (n - c.length)) :=
            mul_le_mul_of_nonneg_right hprod (mul_nonneg hdf hmpow)
        _ ≤ D ^ c.length * ((n.descFactorial c.length : ℝ) * q ^ (n - c.length)) := by
          gcongr
        _ = D ^ c.length * (n.descFactorial c.length : ℝ) * q ^ (n - c.length) := by
          ring

def smoothSchwartzDerivativeEnvelope
    (f : SchwartzMap ℝ ℂ) (D q : ℝ) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * smoothPowerDerivativeEnvelope D q i n *
      SchwartzMap.seminorm ℂ 0 (k - i) f

theorem smoothSchwartzDerivativeEnvelope_nonneg
    (f : SchwartzMap ℝ ℂ) {D q : ℝ} (hD : 0 ≤ D) (hq : 0 ≤ q) (k n : ℕ) :
    0 ≤ smoothSchwartzDerivativeEnvelope f D q k n := by
  unfold smoothSchwartzDerivativeEnvelope
  apply Finset.sum_nonneg
  intro i _hi
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _)
      (smoothPowerDerivativeEnvelope_nonneg hD hq i n)) (by positivity)

theorem tendsto_smoothSchwartzDerivativeEnvelope_zero
    (f : SchwartzMap ℝ ℂ) {D q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (k : ℕ) :
    Tendsto (smoothSchwartzDerivativeEnvelope f D q k) atTop (nhds 0) := by
  unfold smoothSchwartzDerivativeEnvelope
  have hsum := tendsto_finsetSum (Finset.range (k + 1)) (fun i _hi => by
    simpa [mul_assoc] using
      (tendsto_smoothPowerDerivativeEnvelope_zero (D := D) hq0 hq1 i).const_mul
        ((k.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 (k - i) f))
  simpa only [mul_assoc, mul_comm, mul_left_comm, Finset.sum_const_zero] using hsum

theorem seminorm_zero_smulLeftCLM_pow_le_smoothEnvelope
    (m : ℝ → ℝ) (hm : Function.HasTemperateGrowth m)
    (f : SchwartzMap ℝ ℂ) {D q : ℝ} (hD : 0 ≤ D) (hq : 0 ≤ q)
    (hpacket : ∀ t ∈ tsupport f, 0 ≤ m t ∧ m t ≤ q)
    (k n : ℕ)
    (hder : ∀ t ∈ tsupport f, ∀ j : ℕ, j ≤ k → ‖iteratedDeriv j m t‖ ≤ D) :
    SchwartzMap.seminorm ℂ 0 k
      ((SchwartzMap.smulLeftCLM ℂ (fun t => (m t : ℂ)) ^ n) f) ≤
      smoothSchwartzDerivativeEnvelope f D q k n := by
  apply SchwartzMap.seminorm_le_bound' (𝕜 := ℂ) 0 k
  · exact smoothSchwartzDerivativeEnvelope_nonneg f hD hq k n
  · intro t
    simp only [pow_zero, one_mul]
    have hmC : Function.HasTemperateGrowth (fun t => (m t : ℂ)) :=
      Complex.ofRealCLM.hasTemperateGrowth.comp hm
    have hmTop : ContDiff ℝ (⊤ : ℕ∞) m := hm.1
    have hpowapply : ∀ n : ℕ, ∀ f : SchwartzMap ℝ ℂ, ∀ t : ℝ,
        (SchwartzMap.smulLeftCLM ℂ (fun t => (m t : ℂ)) ^ n) f t =
          (m t : ℂ) ^ n * f t := by
      intro p
      induction p with
      | zero => simp
      | succ p ih =>
          intro u x
          rw [pow_succ, mul_apply_eq_comp, ih,
            SchwartzMap.smulLeftCLM_apply_apply hmC]
          ring
    rw [show iteratedDeriv k
        (fun x => ((SchwartzMap.smulLeftCLM ℂ (fun t => (m t : ℂ)) ^ n) f) x) t =
        iteratedDeriv k (fun x => (m x : ℂ) ^ n * f x) t by
      congr 1
      funext x
      exact hpowapply n f x]
    rw [iteratedDeriv_real_pow_mul_schwartz_eq_sum m hmTop f n k t]
    by_cases ht : t ∈ tsupport f
    · rcases hpacket t ht with ⟨hmt0, hmtq⟩
      calc
        ‖∑ i ∈ Finset.range (k + 1),
            (k.choose i : ℂ) * iteratedDeriv i (fun x => (m x ^ n : ℂ)) t *
              iteratedDeriv (k - i) f t‖ ≤
          ∑ i ∈ Finset.range (k + 1),
            ‖(k.choose i : ℂ) * iteratedDeriv i (fun x => (m x ^ n : ℂ)) t *
              iteratedDeriv (k - i) f t‖ := norm_sum_le _ _
        _ ≤ smoothSchwartzDerivativeEnvelope f D q k n := by
          unfold smoothSchwartzDerivativeEnvelope
          apply Finset.sum_le_sum
          intro i _hi
          have hcast : iteratedDeriv i (fun x => (m x : ℂ) ^ n) t =
              ((iteratedDeriv i (fun x => m x ^ n) t : ℝ) : ℂ) := by
            convert iteratedDeriv_ofReal (fun x => m x ^ n) (hmTop.pow n) i t using 1
            congr 2
            funext x
            push_cast
            rfl
          rw [hcast, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real,
            Real.norm_eq_abs]
          have hp := norm_iteratedDeriv_pow_le_smoothPowerDerivativeEnvelope
            m hmTop hD hmt0 hmtq i n
              (fun j hj => hder t ht j (hj.trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp _hi))))
          have hpabs : |iteratedDeriv i (fun x => m x ^ n) t| ≤
              smoothPowerDerivativeEnvelope D q i n := by
            simpa only [Real.norm_eq_abs] using hp
          have hfderiv : ‖iteratedDeriv (k - i) f t‖ ≤
              SchwartzMap.seminorm ℂ 0 (k - i) f := by
            have hsem := SchwartzMap.le_seminorm ℂ 0 (k - i) f t
            rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hsem
            simpa only [pow_zero, one_mul] using hsem
          calc
            (k.choose i : ℝ) * |iteratedDeriv i (fun x => m x ^ n) t| *
                ‖iteratedDeriv (k - i) f t‖ =
              (k.choose i : ℝ) * (|iteratedDeriv i (fun x => m x ^ n) t| *
                ‖iteratedDeriv (k - i) f t‖) := by ring
            _ ≤ (k.choose i : ℝ) * (smoothPowerDerivativeEnvelope D q i n *
                SchwartzMap.seminorm ℂ 0 (k - i) f) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul hpabs hfderiv (norm_nonneg _)
                  (smoothPowerDerivativeEnvelope_nonneg hD hq i n))
                (Nat.cast_nonneg _)
            _ = (k.choose i : ℝ) * smoothPowerDerivativeEnvelope D q i n *
                SchwartzMap.seminorm ℂ 0 (k - i) f := by ring
    · have hzero : ∀ i ∈ Finset.range (k + 1), iteratedDeriv (k - i) f t = 0 := by
        intro i _hi
        exact iteratedDeriv_eq_zero_of_not_mem_tsupport f (k - i) ht
      have hsumzero : ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℂ) * iteratedDeriv i (fun x => (m x : ℂ) ^ n) t *
            iteratedDeriv (k - i) f t = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hzero i hi, mul_zero]
      rw [hsumzero, norm_zero]
      exact smoothSchwartzDerivativeEnvelope_nonneg f hD hq k n

theorem tsupport_smulLeftCLM_pow_ofReal_subset
    (m : ℝ → ℝ) (n : ℕ) (f : SchwartzMap ℝ ℂ) :
    tsupport ((SchwartzMap.smulLeftCLM ℂ (fun t => (m t : ℂ)) ^ n) f) ⊆ tsupport f := by
  apply closure_mono
  intro t ht
  change ((SchwartzMap.smulLeftCLM ℂ (fun t => (m t : ℂ)) ^ n) f) t ≠ 0 at ht
  change f t ≠ 0
  intro hft
  by_cases hm : Function.HasTemperateGrowth m
  · have hmC : Function.HasTemperateGrowth (fun t => (m t : ℂ)) :=
      Complex.ofRealCLM.hasTemperateGrowth.comp hm
    have hpowapply : ∀ p : ℕ, ∀ u : SchwartzMap ℝ ℂ, ∀ x : ℝ,
        (SchwartzMap.smulLeftCLM ℂ (fun t => (m t : ℂ)) ^ p) u x =
          (m x : ℂ) ^ p * u x := by
      intro p
      induction p with
      | zero => simp
      | succ p ih =>
          intro u x
          rw [pow_succ, mul_apply_eq_comp, ih,
            SchwartzMap.smulLeftCLM_apply_apply hmC]
          ring
    rw [hpowapply n f t, hft, mul_zero] at ht
    exact ht rfl
  · have hmCnot : ¬Function.HasTemperateGrowth (fun t => (m t : ℂ)) := by
      intro hmC
      have hre : Function.HasTemperateGrowth m := by
        have hreal := Complex.reCLM.hasTemperateGrowth.comp hmC
        have hfun : (Complex.reCLM ∘ fun t => (m t : ℂ)) = m := by
          funext t
          rfl
        rw [hfun] at hreal
        exact hreal
      exact hm hre
    cases n with
    | zero => simp [hft] at ht
    | succ n => simp [SchwartzMap.smulLeftCLM, hmCnot] at ht

theorem tendsto_seminorm_zero_smulLeftCLM_pow_zero_of_compact_packet
    (m : ℝ → ℝ) (hm : Function.HasTemperateGrowth m)
    (f : SchwartzMap ℝ ℂ) {T q : ℝ} (hT : 0 ≤ T) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hsupp : tsupport f ⊆ {t : ℝ | |t| ≤ T})
    (hpacket : ∀ t ∈ tsupport f, 0 ≤ m t ∧ m t ≤ q)
    (k : ℕ) :
    Tendsto (fun n : ℕ => SchwartzMap.seminorm ℂ 0 k
      ((SchwartzMap.smulLeftCLM ℂ (fun t => (m t : ℂ)) ^ n) f))
      atTop (nhds 0) := by
  rcases hm.norm_iteratedFDeriv_le_uniform k with ⟨p, C, hC, hbound⟩
  let D := C * (1 + T) ^ p
  have hD : 0 ≤ D := mul_nonneg hC (pow_nonneg (by linarith) _)
  have hder : ∀ t ∈ tsupport f, ∀ j : ℕ, j ≤ k → ‖iteratedDeriv j m t‖ ≤ D := by
    intro t ht j hj
    have hb := hbound j hj t
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hb
    calc
      ‖iteratedDeriv j m t‖ ≤ C * (1 + ‖t‖) ^ p := hb
      _ ≤ C * (1 + T) ^ p := by
        gcongr
        have htT := hsupp ht
        change |t| ≤ T at htT
        simpa only [Real.norm_eq_abs] using htT
  exact squeeze_zero (fun n => by positivity)
    (fun n => seminorm_zero_smulLeftCLM_pow_le_smoothEnvelope
      m hm f hD hq0 hpacket k n hder)
    (tendsto_smoothSchwartzDerivativeEnvelope_zero f hq0 hq1 k)

/-- Every smooth temperate scalar multiplier that is uniformly below one on a compact packet has
powers converging to zero in the full Schwartz topology. -/
theorem tendsto_smulLeftCLM_pow_zero_of_compact_packet
    (m : ℝ → ℝ) (hm : Function.HasTemperateGrowth m)
    (f : SchwartzMap ℝ ℂ) {T q : ℝ} (hT : 0 ≤ T) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hsupp : tsupport f ⊆ {t : ℝ | |t| ≤ T})
    (hpacket : ∀ t ∈ tsupport f, 0 ≤ m t ∧ m t ≤ q) :
    Tendsto (fun n : ℕ =>
      (SchwartzMap.smulLeftCLM ℂ (fun t => (m t : ℂ)) ^ n) f)
      atTop (nhds 0) := by
  apply tendsto_zero_of_uniform_tsupport_of_tendsto_zero_weight_seminorms hT
  · exact fun n => (tsupport_smulLeftCLM_pow_ofReal_subset m n f).trans hsupp
  · exact fun k => tendsto_seminorm_zero_smulLeftCLM_pow_zero_of_compact_packet
      m hm f hT hq0 hq1 hsupp hpacket k

/-- Reciprocal scalar multiplier `C / (1 + (2πt-λ)²)`. -/
def inverseQuadraticSpectralSeparatorMultiplier (lambda C t : ℝ) : ℝ :=
  C / (1 + (2 * Real.pi * t - lambda) ^ 2)

theorem hasTemperateGrowth_inverseQuadraticSpectralSeparatorMultiplier
    (lambda C : ℝ) :
    Function.HasTemperateGrowth (inverseQuadraticSpectralSeparatorMultiplier lambda C) := by
  have hu : Function.HasTemperateGrowth (fun t : ℝ => 2 * Real.pi * t - lambda) := by
    fun_prop
  have hbase : Function.HasTemperateGrowth (fun x : ℝ => (1 + x ^ 2)⁻¹) := by
    simpa only [Real.norm_eq_abs, sq_abs, Real.rpow_neg_one] using
      Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (-1)
  have hbaseComp : Function.HasTemperateGrowth
      (fun t : ℝ => (1 + (2 * Real.pi * t - lambda) ^ 2)⁻¹) := by
    have hcomp := hbase.comp hu
    have hfun :
        (fun x : ℝ => (1 + x ^ 2)⁻¹) ∘ (fun t : ℝ => 2 * Real.pi * t - lambda) =
          fun t : ℝ => (1 + (2 * Real.pi * t - lambda) ^ 2)⁻¹ := by
      funext t
      rfl
    rw [hfun] at hcomp
    exact hcomp
  have hconst : Function.HasTemperateGrowth (fun _t : ℝ => C) := by fun_prop
  have hmul : Function.HasTemperateGrowth
      (fun t : ℝ => C * (1 + (2 * Real.pi * t - lambda) ^ 2)⁻¹) :=
    hconst.mul hbaseComp
  have hfun :
      (fun t : ℝ => C * (1 + (2 * Real.pi * t - lambda) ^ 2)⁻¹) =
        inverseQuadraticSpectralSeparatorMultiplier lambda C := by
    funext t
    rw [inverseQuadraticSpectralSeparatorMultiplier, div_eq_mul_inv]
  rw [hfun] at hmul
  exact hmul

/-- Continuous Schwartz multiplier by the reciprocal quadratic separator. -/
def inverseQuadraticSpectralSeparatorCLM (lambda C : ℝ) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ
    (fun t => (inverseQuadraticSpectralSeparatorMultiplier lambda C t : ℂ))

@[simp] theorem inverseQuadraticSpectralSeparatorCLM_apply
    (lambda C : ℝ) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    inverseQuadraticSpectralSeparatorCLM lambda C f t =
      (inverseQuadraticSpectralSeparatorMultiplier lambda C t : ℂ) * f t := by
  unfold inverseQuadraticSpectralSeparatorCLM
  rw [SchwartzMap.smulLeftCLM_apply_apply]
  · simp
  · exact Complex.ofRealCLM.hasTemperateGrowth.comp
      (hasTemperateGrowth_inverseQuadraticSpectralSeparatorMultiplier lambda C)

theorem inverseQuadraticSpectralSeparatorCLM_pow_apply
    (lambda C : ℝ) (n : ℕ) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    (inverseQuadraticSpectralSeparatorCLM lambda C ^ n) f t =
      (inverseQuadraticSpectralSeparatorMultiplier lambda C t : ℂ) ^ n * f t := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_apply_eq_comp, ih,
        inverseQuadraticSpectralSeparatorCLM_apply]
      ring

theorem quadratic_inverse_separator_mul (lambda : ℝ) {C : ℝ}
    (hC : C ≠ 0) (t : ℝ) :
    (quadraticSpectralSeparatorMultiplier lambda C t : ℂ) *
      inverseQuadraticSpectralSeparatorMultiplier lambda C t = 1 := by
  unfold quadraticSpectralSeparatorMultiplier inverseQuadraticSpectralSeparatorMultiplier
  push_cast
  have hdenR : 0 < 1 + (2 * Real.pi * t - lambda) ^ 2 := by positivity
  have hden : (1 + (2 * (Real.pi : ℂ) * (t : ℂ) - (lambda : ℂ)) ^ 2) ≠ 0 := by
    exact_mod_cast hdenR.ne'
  have hCC : (C : ℂ) ≠ 0 := by exact_mod_cast hC
  field_simp [hden, hCC]

/-- The reciprocal power is an exact inverse factor on every Schwartz packet. -/
theorem quadraticSpectralSeparator_pow_inverse_factor
    (lambda : ℝ) {C : ℝ} (hC : C ≠ 0) (n : ℕ) (g : SchwartzMap ℝ ℂ) :
    (quadraticSpectralSeparatorCLM lambda C ^ n)
      ((inverseQuadraticSpectralSeparatorCLM lambda C ^ n) g) = g := by
  ext t
  rw [quadraticSpectralSeparatorCLM_pow_apply,
    inverseQuadraticSpectralSeparatorCLM_pow_apply]
  push_cast
  have hab := quadratic_inverse_separator_mul lambda hC t
  unfold quadraticSpectralSeparatorMultiplier at hab
  push_cast at hab
  rw [← mul_assoc, ← mul_pow, hab, one_pow, one_mul]

/-- Reciprocal powers contract every compact packet lying beyond a strict outer quadratic level. -/
theorem tendsto_inverseQuadraticSpectralSeparator_pow_zero
    {lambda r R S : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) (hrR : r < R) (hS : 0 ≤ S)
    (g : SchwartzMap ℝ ℂ)
    (hgOuter : tsupport g ⊆ {t : ℝ | R ≤ |2 * Real.pi * t - lambda|})
    (hgUpper : tsupport g ⊆ {t : ℝ | |2 * Real.pi * t - lambda| ≤ S}) :
    Tendsto (fun n : ℕ =>
      (inverseQuadraticSpectralSeparatorCLM lambda (quadraticSeparationScale r R) ^ n) g)
      atTop (nhds 0) := by
  let C := quadraticSeparationScale r R
  let q := C / (1 + R ^ 2)
  let T := quadraticPacketCoordinateBound lambda S
  have hC : 0 < C := quadraticSeparationScale_pos r R
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    exact quadraticSeparator_outer_inv_lt_one hr hR hrR (by simp [abs_of_nonneg hR])
  have hT : 0 ≤ T := quadraticPacketCoordinateBound_nonneg lambda hS
  have hsupp : tsupport g ⊆ {t : ℝ | |t| ≤ T} := by
    intro t ht
    exact abs_le_quadraticPacketCoordinateBound (hgUpper ht)
  have hpacket : ∀ t ∈ tsupport g,
      0 ≤ inverseQuadraticSpectralSeparatorMultiplier lambda C t ∧
        inverseQuadraticSpectralSeparatorMultiplier lambda C t ≤ q := by
    intro t ht
    have hout := hgOuter ht
    have hu2 : R ^ 2 ≤ (2 * Real.pi * t - lambda) ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ hR (abs_nonneg _)).2 hout
    constructor
    · unfold inverseQuadraticSpectralSeparatorMultiplier
      positivity
    · unfold inverseQuadraticSpectralSeparatorMultiplier
      dsimp [q]
      exact div_le_div_of_nonneg_left hC.le (by positivity) (by linarith)
  simpa only [inverseQuadraticSpectralSeparatorCLM] using
    tendsto_smulLeftCLM_pow_zero_of_compact_packet
      (inverseQuadraticSpectralSeparatorMultiplier lambda C)
      (hasTemperateGrowth_inverseQuadraticSpectralSeparatorMultiplier lambda C)
      g hT hq0 hq1 hsupp hpacket

/-- The direct separator powers converge to zero in the first derivative Schwartz seminorm on
every strict inner packet. -/
theorem tendsto_seminorm_zero_one_quadraticSpectralSeparator_pow_zero
    {lambda r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) (hrR : r < R)
    (f : SchwartzMap ℝ ℂ)
    (hf : tsupport f ⊆ {t : ℝ | |2 * Real.pi * t - lambda| ≤ r}) :
    Tendsto
      (fun n : ℕ => SchwartzMap.seminorm ℂ 0 1
        ((quadraticSpectralSeparatorCLM lambda (quadraticSeparationScale r R) ^ n) f))
      atTop (nhds 0) := by
  let C := quadraticSeparationScale r R
  let q := (1 + r ^ 2) / C
  let L := 4 * Real.pi * r / C
  have hq0 : 0 ≤ q := div_nonneg (by positivity) (quadraticSeparationScale_pos r R).le
  have hq1 : q < 1 := by
    exact quadraticSeparator_inner_lt_one hr hR hrR (by simp [abs_of_nonneg hr])
  have hfirst : Tendsto
      (fun n : ℕ => (n : ℝ) * q ^ (n - 1) * L * SchwartzMap.seminorm ℂ 0 0 f)
      atTop (nhds 0) := by
    simpa [mul_assoc] using
      (tendsto_natCast_mul_pow_pred_zero hq0 hq1).mul_const
        (L * SchwartzMap.seminorm ℂ 0 0 f)
  have hsecond : Tendsto
      (fun n : ℕ => q ^ n * SchwartzMap.seminorm ℂ 0 1 f) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const
      (SchwartzMap.seminorm ℂ 0 1 f)
  exact squeeze_zero (fun n => by positivity)
    (fun n => seminorm_zero_one_quadraticSpectralSeparator_pow_le hr f hf n)
    (by simpa [C, q, L] using hfirst.add hsecond)

/-- Direct separator powers converge in every polynomially weighted zeroth-derivative Schwartz
seminorm on a strict inner packet. -/
theorem tendsto_seminorm_weight_zero_quadraticSpectralSeparator_pow_zero
    {lambda r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) (hrR : r < R)
    (f : SchwartzMap ℝ ℂ)
    (hf : tsupport f ⊆ {t : ℝ | |2 * Real.pi * t - lambda| ≤ r})
    (a : ℕ) :
    Tendsto
      (fun n : ℕ => SchwartzMap.seminorm ℂ a 0
        ((quadraticSpectralSeparatorCLM lambda (quadraticSeparationScale r R) ^ n) f))
      atTop (nhds 0) := by
  apply tendsto_seminorm_of_tsupport_subset_of_tendsto_seminorm_zero
    (quadraticPacketCoordinateBound_nonneg lambda hr)
  · exact fun n => tsupport_quadraticSpectralSeparator_pow_packet f hf n
  · exact tendsto_seminorm_zero_zero_quadraticSpectralSeparator_pow_zero hr hR hrR f
      (fun t hft => hf (subset_tsupport f hft))

/-- Direct separator powers converge in every polynomially weighted first-derivative Schwartz
seminorm on a strict inner packet. -/
theorem tendsto_seminorm_weight_one_quadraticSpectralSeparator_pow_zero
    {lambda r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) (hrR : r < R)
    (f : SchwartzMap ℝ ℂ)
    (hf : tsupport f ⊆ {t : ℝ | |2 * Real.pi * t - lambda| ≤ r})
    (a : ℕ) :
    Tendsto
      (fun n : ℕ => SchwartzMap.seminorm ℂ a 1
        ((quadraticSpectralSeparatorCLM lambda (quadraticSeparationScale r R) ^ n) f))
      atTop (nhds 0) := by
  apply tendsto_seminorm_of_tsupport_subset_of_tendsto_seminorm_zero
    (quadraticPacketCoordinateBound_nonneg lambda hr)
  · exact fun n => tsupport_quadraticSpectralSeparator_pow_packet f hf n
  · exact tendsto_seminorm_zero_one_quadraticSpectralSeparator_pow_zero hr hR hrR f hf

/-- Every positive centered quadratic separator is symmetric for the Fourier pullback of a
momentum-symmetric form. -/
theorem ContinuousSchwartzSesquilinearForm.fourierPullback_quadraticSpectralSeparator_symmetric
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (lambda C : ℝ) (f g : SchwartzMap ℝ ℂ) :
    Q.fourierPullback (quadraticSpectralSeparatorCLM lambda C f) g =
      Q.fourierPullback f (quadraticSpectralSeparatorCLM lambda C g) := by
  let A := centeredSpectralMomentumCLM lambda
  have hA : ∀ u v, Q.fourierPullback (A u) v = Q.fourierPullback u (A v) :=
    Q.fourierPullback_centeredSpectralMomentum_symmetric hQ lambda
  have hA2 (u v : SchwartzMap ℝ ℂ) :
      Q.fourierPullback ((A ^ 2) u) v = Q.fourierPullback u ((A ^ 2) v) :=
    Q.fourierPullback_clm_pow_symmetric A hA 2 u v
  change Q.fourierPullback
      ((C⁻¹ : ℂ) • ((1 + A * A) f)) g =
    Q.fourierPullback f ((C⁻¹ : ℂ) • ((1 + A * A) g))
  rw [Q.fourierPullback.apply_smul_left, Q.fourierPullback.apply_smul_right]
  rw [map_inv₀, Complex.conj_ofReal]
  congr 1
  calc
    Q.fourierPullback ((1 + A * A) f) g =
        Q.fourierPullback f g + Q.fourierPullback (A (A f)) g := by
      simp
    _ = Q.fourierPullback f g + Q.fourierPullback f (A (A g)) := by
      rw [show Q.fourierPullback (A (A f)) g =
        Q.fourierPullback f (A (A g)) by
          simpa [pow_two] using hA2 f g]
    _ = Q.fourierPullback f ((1 + A * A) g) := by
      simp

/-- **Kernel-free compact spectral locality.** Momentum symmetry alone makes every inner packet
orthogonal to every compact packet beyond a strict centered spectral gap. -/
theorem ContinuousSchwartzSesquilinearForm.fourierPullback_eq_zero_of_disjoint_quadratic_packets
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    {lambda r R S : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) (hrR : r < R) (hS : 0 ≤ S)
    (f g : SchwartzMap ℝ ℂ)
    (hf : tsupport f ⊆ {t : ℝ | |2 * Real.pi * t - lambda| ≤ r})
    (hgOuter : tsupport g ⊆ {t : ℝ | R ≤ |2 * Real.pi * t - lambda|})
    (hgUpper : tsupport g ⊆ {t : ℝ | |2 * Real.pi * t - lambda| ≤ S}) :
    Q.fourierPullback f g = 0 := by
  let C := quadraticSeparationScale r R
  apply Q.fourierPullback_eq_zero_of_clmPower_separation
    (quadraticSpectralSeparatorCLM lambda C)
    (Q.fourierPullback_quadraticSpectralSeparator_symmetric hQ lambda C)
    f g (fun n => (inverseQuadraticSpectralSeparatorCLM lambda C ^ n) g)
  · intro n
    exact quadraticSpectralSeparator_pow_inverse_factor lambda
      (quadraticSeparationScale_pos r R).ne' n g
  · exact tendsto_quadraticSpectralSeparator_pow_zero hr hR hrR f hf
  · exact tendsto_inverseQuadraticSpectralSeparator_pow_zero hr hR hrR hS g
      hgOuter hgUpper

/-- Two compact spectral packets contained in disjoint closed intervals are orthogonal. -/
theorem ContinuousSchwartzSesquilinearForm.fourierPullback_eq_zero_of_separated_interval_packets
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    {lambda mu r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hsep : r + s < |mu - lambda|)
    (f g : SchwartzMap ℝ ℂ)
    (hf : tsupport f ⊆ {t : ℝ | |2 * Real.pi * t - lambda| ≤ r})
    (hg : tsupport g ⊆ {t : ℝ | |2 * Real.pi * t - mu| ≤ s}) :
    Q.fourierPullback f g = 0 := by
  let d := |mu - lambda|
  let R := d - s
  let S := d + s
  have hR : 0 ≤ R := by dsimp [R, d]; linarith
  have hrR : r < R := by dsimp [R, d]; linarith
  have hS : 0 ≤ S := by dsimp [S, d]; positivity
  have hgOuter : tsupport g ⊆ {t : ℝ | R ≤ |2 * Real.pi * t - lambda|} := by
    intro t ht
    have hgt := hg ht
    change |2 * Real.pi * t - mu| ≤ s at hgt
    have htri : d ≤ |2 * Real.pi * t - lambda| + |2 * Real.pi * t - mu| := by
      dsimp [d]
      calc
        |mu - lambda| = |(2 * Real.pi * t - lambda) - (2 * Real.pi * t - mu)| := by
          congr 1
          ring
        _ ≤ |2 * Real.pi * t - lambda| + |2 * Real.pi * t - mu| := by
          simpa [abs_sub_comm] using
            abs_sub_le (2 * Real.pi * t - lambda) 0 (2 * Real.pi * t - mu)
    change R ≤ |2 * Real.pi * t - lambda|
    dsimp [R]
    linarith
  have hgUpper : tsupport g ⊆ {t : ℝ | |2 * Real.pi * t - lambda| ≤ S} := by
    intro t ht
    have hgt := hg ht
    change |2 * Real.pi * t - mu| ≤ s at hgt
    have htri : |2 * Real.pi * t - lambda| ≤
        |2 * Real.pi * t - mu| + d := by
      dsimp [d]
      calc
        |2 * Real.pi * t - lambda| =
            |(2 * Real.pi * t - mu) + (mu - lambda)| := by
              congr 1
              ring
        _ ≤ |2 * Real.pi * t - mu| + |mu - lambda| := abs_add_le _ _
    change |2 * Real.pi * t - lambda| ≤ S
    dsimp [S]
    linarith
  exact Q.fourierPullback_eq_zero_of_disjoint_quadratic_packets hQ hr hR hrR hS
    f g hf hgOuter hgUpper

end SchwartzMap
