import GaloisForLFunctions.RHTower.XiShiftEulerCommonDivisorIndex
import GaloisForLFunctions.RHTower.CCM.CCMEulerRayLoewner

/-!
# One real Euler ray carries the complete shifted-Xi index

The vertical ray `z = i y`, `y > 1/2 + omega`, is an interior accumulation set for the analytic
shifted-Xi kernel.  This leaf proves source-specific locality on that ray, identifies its literal
kernel with the real Cauchy--Loewner kernel of the Xi quotient, and proves exact dense nested
finite-section exhaustion.  All results include exceptional common-divisor cancellation and the
value `⊤`; nonexceptional shifts recover the raw strict-right Xi divisor count.
-/

open Complex Set Topology Filter Matrix
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Real parameters whose vertical-ray nodes lie in the ordinary Euler convergence region. -/
def xiShiftEulerRaySet (omega : ℝ) : Set ℝ := Set.Ioi (1 / 2 + omega)

/-- Embedding of the positive Euler ray into the complex sampling half-plane. -/
def xiShiftEulerRayNode {omega : ℝ} (y : xiShiftEulerRaySet omega) : ℂ :=
  I * (y.1 : ℂ)

/-- Xi is real on the real axis, stated as equality with the coercion of its real part. -/
theorem xi_ofReal_eq_ofReal_re (t : ℝ) :
    xi (t : ℂ) = ((xi (t : ℂ)).re : ℂ) := by
  symm
  apply Complex.conj_eq_iff_re.mp
  rw [← xi_conj]
  simp

/-- Literal positive-real shifted-Xi quotient on the Euler ray. -/
def xiShiftEulerRayQuotient (omega y : ℝ) : ℝ :=
  (xi ((1 / 2 - omega + y : ℝ) : ℂ)).re /
    (xi ((1 / 2 + omega + y : ℝ) : ℂ)).re

/-- The complex shifted quotient restricts to the coercion of the real Xi quotient. -/
theorem suzukiCanonicalTheta_ray_eq_ofReal (omega y : ℝ) :
    suzukiCanonicalTheta omega (I * (y : ℂ)) =
      (xiShiftEulerRayQuotient omega y : ℂ) := by
  rw [suzukiCanonicalTheta]
  have hIy : I * (y : ℂ) * I = -(y : ℂ) := by
    calc
      I * (y : ℂ) * I = (y : ℂ) * (I * I) := by ring
      _ = -(y : ℂ) := by rw [I_mul_I]; ring
  have hminus :
      1 / 2 - (omega : ℂ) - (I * (y : ℂ)) * I =
        ((1 / 2 - omega + y : ℝ) : ℂ) := by
    rw [hIy]
    push_cast
    ring
  have hplus :
      1 / 2 + (omega : ℂ) - (I * (y : ℂ)) * I =
        ((1 / 2 + omega + y : ℝ) : ℂ) := by
    rw [hIy]
    push_cast
    ring
  rw [hminus, hplus,
    xi_ofReal_eq_ofReal_re (1 / 2 - omega + y),
    xi_ofReal_eq_ofReal_re (1 / 2 + omega + y)]
  norm_cast

/-- Literal shifted-Xi Pick kernel restricted to the real Euler ray. -/
def xiShiftEulerRayKernel (omega : ℝ)
    (x y : xiShiftEulerRaySet omega) : ℂ :=
  eulerXiShiftPick omega (xiShiftEulerRayNode x) (xiShiftEulerRayNode y)

/-- The literal ray kernel is exactly the displayed real Cauchy--Loewner kernel. -/
theorem xiShiftEulerRayKernel_eq_loewner
    {omega : ℝ} (homega : 0 < omega)
    (x y : xiShiftEulerRaySet omega) :
    xiShiftEulerRayKernel omega x y =
      (GaloisForLFunctions.RHTower.loewnerKernel
        (xiShiftEulerRayQuotient omega) x.1 y.1 : ℂ) := by
  have hxy : x.1 + y.1 ≠ 0 := by
    have hx : 0 < x.1 := by
      have hx' : 1 / 2 + omega < x.1 := by
        simpa [xiShiftEulerRaySet] using x.2
      linarith
    have hy : 0 < y.1 := by
      have hy' : 1 / 2 + omega < y.1 := by
        simpa [xiShiftEulerRaySet] using y.2
      linarith
    positivity
  rw [xiShiftEulerRayKernel,
    eulerXiShiftPick_eq_upperHalfPlaneSchurKernel,
    upperHalfPlaneSchurKernel]
  simp only [xiShiftEulerRayNode]
  rw [suzukiCanonicalTheta_ray_eq_ofReal,
    suzukiCanonicalTheta_ray_eq_ofReal]
  calc
    I / (I * (x.1 : ℂ) - (starRingEnd ℂ) (I * (y.1 : ℂ))) *
        (1 - (xiShiftEulerRayQuotient omega x.1 : ℂ) *
          (starRingEnd ℂ) (xiShiftEulerRayQuotient omega y.1 : ℂ)) =
      I * (1 - (xiShiftEulerRayQuotient omega x.1 : ℂ) *
          (starRingEnd ℂ) (xiShiftEulerRayQuotient omega y.1 : ℂ)) /
        (I * (x.1 : ℂ) - (starRingEnd ℂ) (I * (y.1 : ℂ))) := by ring
    _ = (GaloisForLFunctions.RHTower.loewnerKernel
        (xiShiftEulerRayQuotient omega) y.1 x.1 : ℂ) := by
      exact GaloisForLFunctions.RHTower.schur_ray_eq_loewner
        (by simpa [add_comm] using hxy)
    _ = (GaloisForLFunctions.RHTower.loewnerKernel
        (xiShiftEulerRayQuotient omega) x.1 y.1 : ℂ) := by
      simp only [GaloisForLFunctions.RHTower.loewnerKernel]
      congr 1
      ring

/-- The ray embedding is injective. -/
theorem xiShiftEulerRayNode_injective {omega : ℝ} :
    Function.Injective (@xiShiftEulerRayNode omega) := by
  intro x y hxy
  apply Subtype.ext
  have him := congrArg Complex.im hxy
  simpa [xiShiftEulerRayNode] using him

/-- The whole open vertical ray accumulates at an interior point of the upper half-plane. -/
theorem xiShiftEulerRay_accumulation (b : ℝ) :
    ∃ᶠ w in nhdsWithin (I * ((b + 1 : ℝ) : ℂ))
        ({I * ((b + 1 : ℝ) : ℂ)}ᶜ),
      w ∈ Set.range (fun y : Set.Ioi b => I * (y.1 : ℂ)) := by
  let p : ℂ := I * ((b + 1 : ℝ) : ℂ)
  let D : Set ℂ := Set.range (fun y : Set.Ioi b => I * (y.1 : ℂ))
  have hpclosure : p ∈ closure (D ∩ {p}ᶜ) := by
    rw [Metric.mem_closure_iff]
    intro epsilon hepsilon
    let delta : ℝ := min (epsilon / 2) (1 / 2)
    have hdelta : 0 < delta := lt_min (half_pos hepsilon) (by norm_num)
    have hdeltalt : delta < epsilon :=
      (min_le_left (epsilon / 2) (1 / 2)).trans_lt (half_lt_self hepsilon)
    let y : Set.Ioi b := ⟨b + 1 + delta, by
      change b < b + 1 + delta
      linarith⟩
    refine ⟨I * (y.1 : ℂ), ?_, ?_⟩
    · refine ⟨⟨y, rfl⟩, ?_⟩
      change I * (y.1 : ℂ) ≠ p
      intro heq
      have him := congrArg Complex.im heq
      simp [y, p] at him
      linarith
    · rw [Complex.dist_eq]
      have heq : p - I * (y.1 : ℂ) = -I * (delta : ℂ) := by
        simp only [p, y]
        push_cast
        ring
      rw [heq, norm_mul, norm_neg, norm_I, one_mul, norm_real, Real.norm_eq_abs,
        abs_of_pos hdelta]
      exact hdeltalt
  apply frequently_nhdsWithin_iff.mpr
  have hfreq := mem_closure_iff_frequently.mp hpclosure
  exact hfreq.mono fun w hw => ⟨hw.1, hw.2⟩

/-- Every dense sequence in the real Euler ray has a complex interior accumulation point after
vertical embedding. -/
theorem denseRange_xiShiftEulerRayNode_range_accumulates
    {omega : ℝ} (homega : 0 < omega)
    (z : ℕ → xiShiftEulerRaySet omega) (hz : DenseRange z) :
    ∃ p : ℂ, p ∈ upperHalfPlaneSet ∧
      ∃ᶠ w in nhdsWithin p ({p}ᶜ),
        w ∈ Set.range (fun n => xiShiftEulerRayNode (z n)) := by
  let b : ℝ := 1 / 2 + omega
  let yp : xiShiftEulerRaySet omega := ⟨b + 1, by
    change b < b + 1
    linarith⟩
  let p : ℂ := xiShiftEulerRayNode yp
  let D : Set ℂ := Set.range (fun n => xiShiftEulerRayNode (z n))
  have hpUpper : p ∈ upperHalfPlaneSet := by
    change 0 < p.im
    simp [p, yp, xiShiftEulerRayNode, b]
    have hb : 0 < b := by dsimp [b]; linarith
    linarith
  have hpclosure : p ∈ closure (D ∩ {p}ᶜ) := by
    rw [Metric.mem_closure_iff]
    intro epsilon hepsilon
    let delta : ℝ := min (epsilon / 4) (1 / 4)
    have hdelta : 0 < delta := lt_min (by positivity) (by norm_num)
    have hdeltale : delta ≤ epsilon / 4 := min_le_left _ _
    let yq : xiShiftEulerRaySet omega := ⟨yp.1 + delta, by
      change b < yp.1 + delta
      have hyp : b < yp.1 := by
        simpa [b, xiShiftEulerRaySet] using yp.2
      linarith⟩
    have hclose : yq ∈ closure (Set.range z) := hz yq
    obtain ⟨_, ⟨n, rfl⟩, hyn⟩ :=
      (Metric.mem_closure_iff.mp hclose) (delta / 2) (half_pos hdelta)
    refine ⟨xiShiftEulerRayNode (z n), ?_, ?_⟩
    · refine ⟨⟨n, rfl⟩, ?_⟩
      change xiShiftEulerRayNode (z n) ≠ p
      intro heq
      have him := congrArg Complex.im heq
      have hval : (z n).1 = yp.1 := by
        simpa [xiShiftEulerRayNode, p] using him
      have hdist : dist yq (z n) = delta := by
        rw [Subtype.dist_eq, Real.dist_eq]
        simp only [yq, hval]
        rw [show yp.1 + delta - yp.1 = delta by ring,
          abs_of_pos hdelta]
      rw [hdist] at hyn
      linarith
    · rw [Complex.dist_eq]
      have hnorm : ‖p - xiShiftEulerRayNode (z n)‖ =
          |yp.1 - (z n).1| := by
        rw [show p - xiShiftEulerRayNode (z n) =
            I * ((yp.1 - (z n).1 : ℝ) : ℂ) by
          simp only [p, xiShiftEulerRayNode]
          push_cast
          ring,
          norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs]
      rw [hnorm]
      have hyn' : |yq.1 - (z n).1| < delta / 2 := by
        simpa [Subtype.dist_eq, Real.dist_eq] using hyn
      have htri : |yp.1 - (z n).1| ≤
          |yp.1 - yq.1| + |yq.1 - (z n).1| := by
        simpa [Subtype.dist_eq, Real.dist_eq] using dist_triangle yp yq (z n)
      have hpq : |yp.1 - yq.1| = delta := by
        simp only [yq]
        rw [show yp.1 - (yp.1 + delta) = -delta by ring,
          abs_neg, abs_of_pos hdelta]
      rw [hpq] at htri
      calc
        |yp.1 - (z n).1| ≤ delta + |yq.1 - (z n).1| := htri
        _ < delta + delta / 2 := by linarith
        _ ≤ 3 * (epsilon / 4) / 2 := by linarith
        _ < epsilon := by linarith
  refine ⟨p, hpUpper, frequently_nhdsWithin_iff.mpr ?_⟩
  have hfreq := mem_closure_iff_frequently.mp hpclosure
  exact hfreq.mono fun w hw => ⟨hw.1, hw.2⟩

/-- The real Euler ray preserves every finite negative dimension of the complete shifted-Xi
kernel, with exact common-divisor cancellation at every positive shift. -/
theorem xiShiftEulerRay_negativeDimension_iff_uncancelledDivisorQuotient
    {omega : ℝ} (homega : 0 < omega) (r : ℕ) :
    HasFiniteKernelNegativeDimension (xiShiftEulerRayKernel omega) r ↔
      HasIndependentDimensionAtLeast
        (XiShiftUncancelledDivisorQuotient homega.le) r := by
  let D : Set ℂ := Set.range (@xiShiftEulerRayNode omega)
  let e : xiShiftEulerRaySet omega ≃ D :=
    Equiv.ofInjective (@xiShiftEulerRayNode omega)
      xiShiftEulerRayNode_injective
  let KD := fun z w : D => eulerXiShiftPick omega z.1 w.1
  have heq : HasFiniteKernelNegativeDimension (xiShiftEulerRayKernel omega) r ↔
      HasFiniteKernelNegativeDimension KD r := by
    apply hasFiniteKernelNegativeDimension_diagonal_equiv_iff
      (xiShiftEulerRayKernel omega) KD e (fun _ => 1)
        (fun _ => one_ne_zero)
    intro x y
    simp only [one_mul, map_one, mul_one]
    rfl
  have hsub : D ⊆ upperHalfPlaneSet := by
    rintro w ⟨y, rfl⟩
    change 0 < (xiShiftEulerRayNode y).im
    simp only [xiShiftEulerRayNode, I_re, ofReal_re, mul_im, I_im, ofReal_im,
      zero_mul, one_mul]
    have hy : 1 / 2 + omega < y.1 := by
      simpa [xiShiftEulerRaySet] using y.2
    have hy0 : 0 < y.1 := lt_trans (by linarith : 0 < 1 / 2 + omega) hy
    simpa using hy0
  have hregular : ∀ w ∈ D, suzukiCanonicalE omega w ≠ 0 := by
    rintro w ⟨y, rfl⟩
    apply suzukiCanonicalE_ne_zero_of_mem_xiShiftEulerUpperSet homega
    change 1 / 2 + omega < (xiShiftEulerRayNode y).im
    simpa [xiShiftEulerRaySet, xiShiftEulerRayNode] using y.2
  let p : ℂ := I * ((1 / 2 + omega + 1 : ℝ) : ℂ)
  have hpUpper : p ∈ upperHalfPlaneSet := by
    change 0 < p.im
    simp [p]
    linarith
  have hfreq : ∃ᶠ w in nhdsWithin p ({p}ᶜ), w ∈ D := by
    simpa [p, D, xiShiftEulerRaySet, xiShiftEulerRayNode] using
      xiShiftEulerRay_accumulation (1 / 2 + omega)
  have hlocal := xiShiftRegularUpperKernel_accumulationSet_negativeDimension_iff
    omega D hsub hregular p hpUpper hfreq r
  rw [heq, show HasFiniteKernelNegativeDimension KD r ↔
      HasFiniteKernelNegativeDimension (xiShiftRegularUpperKernel omega) r by
    simpa only [KD, eulerXiShiftPick_eq_upperHalfPlaneSchurKernel] using hlocal,
    xiShiftRegularUpperKernel_negativeDimension_iff_uncancelledDivisorQuotient
      homega.le r]

/-- Nested real Euler-ray Pick matrix. -/
def xiShiftEulerRayFiniteSectionMatrix (omega : ℝ)
    (z : ℕ → xiShiftEulerRaySet omega) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  kernelFiniteSectionMatrix (xiShiftEulerRayKernel omega) z N

/-- Strict negative inertia of a nested real Euler-ray Pick matrix. -/
def xiShiftEulerRayFiniteSectionNegIndex (omega : ℝ)
    (z : ℕ → xiShiftEulerRaySet omega) (N : ℕ) : ℕ :=
  kernelFiniteSectionNegIndex (xiShiftEulerRayKernel omega) z N

/-- Supremum of the nested real Euler-ray inertias. -/
def xiShiftEulerRayFiniteSectionNegIndexSup (omega : ℝ)
    (z : ℕ → xiShiftEulerRaySet omega) : WithTop ℕ :=
  kernelFiniteSectionNegIndexSup (xiShiftEulerRayKernel omega) z

theorem star_xiShiftEulerRayKernel_swap
    (omega : ℝ) (x y : xiShiftEulerRaySet omega) :
    (starRingEnd ℂ) (xiShiftEulerRayKernel omega x y) =
      xiShiftEulerRayKernel omega y x := by
  exact star_eulerXiShiftPick_swap omega
    (xiShiftEulerRayNode x) (xiShiftEulerRayNode y)

/-- Ray finite-section inertia is literally its negative-eigenvalue multiplicity. -/
theorem xiShiftEulerRayFiniteSectionNegIndex_eq_card_neg_eigenvalues
    (omega : ℝ) (z : ℕ → xiShiftEulerRaySet omega) (N : ℕ) :
    xiShiftEulerRayFiniteSectionNegIndex omega z N =
      ({i | (kernelFiniteSectionMatrix_isHermitian
        (star_xiShiftEulerRayKernel_swap omega) z N).eigenvalues i < 0} :
        Finset (Fin N)).card := by
  exact kernelFiniteSectionNegIndex_eq_card_neg_eigenvalues
    (star_xiShiftEulerRayKernel_swap omega) z N

/-- Every finite uncancelled-divisor rank occurs in one prefix of every dense real ray sequence,
and every prefix rank is an uncancelled-divisor rank. -/
theorem xiShiftEulerRay_denseFiniteSection_rankProfile
    {omega : ℝ} (homega : 0 < omega)
    (z : ℕ → xiShiftEulerRaySet omega) (hz : DenseRange z) (r : ℕ) :
    HasIndependentDimensionAtLeast
        (XiShiftUncancelledDivisorQuotient homega.le) r ↔
      ∃ N : ℕ, r ≤ xiShiftEulerRayFiniteSectionNegIndex omega z N := by
  let D : Set ℂ := Set.range (fun n => xiShiftEulerRayNode (z n))
  let zd : ℕ → D := fun n => ⟨xiShiftEulerRayNode (z n), ⟨n, rfl⟩⟩
  have hzd : Function.Surjective zd := by
    intro w
    obtain ⟨n, hn⟩ := w.2
    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact hn
  obtain ⟨p, hpUpper, hfreq⟩ :=
    denseRange_xiShiftEulerRayNode_range_accumulates homega z hz
  have hsub : D ⊆ upperHalfPlaneSet := by
    rintro w ⟨n, rfl⟩
    change 0 < (xiShiftEulerRayNode (z n)).im
    simp only [xiShiftEulerRayNode, mul_im, I_re, ofReal_im, I_im,
      ofReal_re, zero_mul, one_mul]
    have hn : 1 / 2 + omega < (z n).1 := by
      simpa [xiShiftEulerRaySet] using (z n).2
    linarith
  have hregular : ∀ w ∈ D, suzukiCanonicalE omega w ≠ 0 := by
    rintro w ⟨n, rfl⟩
    apply suzukiCanonicalE_ne_zero_of_mem_xiShiftEulerUpperSet homega
    change 1 / 2 + omega < (xiShiftEulerRayNode (z n)).im
    simpa [xiShiftEulerRaySet, xiShiftEulerRayNode] using (z n).2
  let K := fun u v : D => eulerXiShiftPick omega u.1 v.1
  have hlocal := xiShiftRegularUpperKernel_accumulationSet_negativeDimension_iff
    omega D hsub hregular p hpUpper hfreq
  have hsection (N : ℕ) :
      kernelFiniteSectionNegIndex K zd N =
        xiShiftEulerRayFiniteSectionNegIndex omega z N := by
    rfl
  constructor
  · intro hq
    have hglobal : HasFiniteKernelNegativeDimension
        (xiShiftRegularUpperKernel omega) r :=
      (xiShiftRegularUpperKernel_negativeDimension_iff_uncancelledDivisorQuotient
        homega.le r).mpr hq
    have hk : HasFiniteKernelNegativeDimension K r := by
      have h := (hlocal r).mpr hglobal
      simpa only [K, eulerXiShiftPick_eq_upperHalfPlaneSchurKernel] using h
    obtain ⟨N, hN⟩ :=
      exists_le_kernelFiniteSectionNegIndex_of_surjective K zd hzd hk
    exact ⟨N, by simpa only [hsection] using hN⟩
  · rintro ⟨N, hN⟩
    have hk : HasFiniteKernelNegativeDimension (xiShiftEulerRayKernel omega)
        (xiShiftEulerRayFiniteSectionNegIndex omega z N) := by
      simpa only [xiShiftEulerRayFiniteSectionNegIndex] using
        (hasFiniteKernelNegativeDimension_kernelFiniteSectionNegIndex
          (xiShiftEulerRayKernel omega) z N)
    have hq :=
      (xiShiftEulerRay_negativeDimension_iff_uncancelledDivisorQuotient
        homega (xiShiftEulerRayFiniteSectionNegIndex omega z N)).mp hk
    exact hasIndependentDimensionAtLeast_of_le hN hq

/-- Dense real Euler-ray matrices exhaust the full cancellation-aware index, including `⊤`. -/
theorem xiShiftEulerRayFiniteSectionNegIndexSup_eq_uncancelledDivisorIndex
    {omega : ℝ} (homega : 0 < omega)
    (z : ℕ → xiShiftEulerRaySet omega) (hz : DenseRange z) :
    xiShiftEulerRayFiniteSectionNegIndexSup omega z =
      xiShiftUncancelledDivisorIndex homega.le := by
  apply le_antisymm
  · apply iSup_le
    intro N
    have hk : HasFiniteKernelNegativeDimension (xiShiftEulerRayKernel omega)
        (xiShiftEulerRayFiniteSectionNegIndex omega z N) := by
      simpa only [xiShiftEulerRayFiniteSectionNegIndex] using
        (hasFiniteKernelNegativeDimension_kernelFiniteSectionNegIndex
          (xiShiftEulerRayKernel omega) z N)
    have hq :=
      (xiShiftEulerRay_negativeDimension_iff_uncancelledDivisorQuotient
        homega (xiShiftEulerRayFiniteSectionNegIndex omega z N)).mp hk
    exact le_iSup_of_le
      (⟨xiShiftEulerRayFiniteSectionNegIndex omega z N, hq⟩ :
        {r : ℕ // HasIndependentDimensionAtLeast
          (XiShiftUncancelledDivisorQuotient homega.le) r}) le_rfl
  · apply iSup_le
    rintro ⟨r, hr⟩
    obtain ⟨N, hN⟩ :=
      (xiShiftEulerRay_denseFiniteSection_rankProfile homega z hz r).mp hr
    exact (WithTop.coe_le_coe.mpr hN).trans
      (le_iSup (fun N : ℕ =>
        (xiShiftEulerRayFiniteSectionNegIndex omega z N : WithTop ℕ)) N)

/-- At a nonexceptional shift, every dense real Euler-ray sequence recovers the raw strict-right
Xi divisor count, finite or infinite. -/
theorem xiShiftEulerRay_denseFiniteSection_nonexceptional_classification
    {omega : ℝ} (homega : 0 < omega)
    (hnon : SuzukiShiftNonexceptional omega)
    (z : ℕ → xiShiftEulerRaySet omega) (hz : DenseRange z) :
    (Finite (XiShiftRightZeroCopy omega) ∧
      xiShiftEulerRayFiniteSectionNegIndexSup omega z =
        (Nat.card (XiShiftRightZeroCopy omega) : WithTop ℕ)) ∨
    (Infinite (XiShiftRightZeroCopy omega) ∧
      xiShiftEulerRayFiniteSectionNegIndexSup omega z = ⊤) := by
  rw [xiShiftEulerRayFiniteSectionNegIndexSup_eq_uncancelledDivisorIndex
    homega z hz]
  exact xiShiftUncancelledDivisorIndex_nonexceptional_classification homega hnon

/-- At a nonexceptional shift, the full real ray itself has exactly the raw strict-right Xi
divisor negative-index profile. -/
theorem xiShiftEulerRay_negativeIndex_nonexceptional_classification
    {omega : ℝ} (homega : 0 < omega)
    (hnon : SuzukiShiftNonexceptional omega) :
    (Finite (XiShiftRightZeroCopy omega) ∧
      HasFiniteKernelNegativeDimension (xiShiftEulerRayKernel omega)
        (Nat.card (XiShiftRightZeroCopy omega)) ∧
      ∀ r, HasFiniteKernelNegativeDimension (xiShiftEulerRayKernel omega) r →
        r ≤ Nat.card (XiShiftRightZeroCopy omega)) ∨
    (Infinite (XiShiftRightZeroCopy omega) ∧
      ∀ r, HasFiniteKernelNegativeDimension (xiShiftEulerRayKernel omega) r) := by
  rcases xiShiftRegularUpperKernel_negativeIndex_classification homega hnon with
    hfinite | hinfinite
  · left
    refine ⟨hfinite.1, ?_, ?_⟩
    · apply (xiShiftEulerRay_negativeDimension_iff_uncancelledDivisorQuotient
        homega _).mpr
      exact (xiShiftRegularUpperKernel_negativeDimension_iff_uncancelledDivisorQuotient
        homega.le _).mp hfinite.2.1
    · intro r hr
      apply hfinite.2.2 r
      apply (xiShiftRegularUpperKernel_negativeDimension_iff_uncancelledDivisorQuotient
        homega.le r).mpr
      exact (xiShiftEulerRay_negativeDimension_iff_uncancelledDivisorQuotient
        homega r).mp hr
  · right
    refine ⟨hinfinite.1, ?_⟩
    intro r
    apply (xiShiftEulerRay_negativeDimension_iff_uncancelledDivisorQuotient
      homega r).mpr
    exact (xiShiftRegularUpperKernel_negativeDimension_iff_uncancelledDivisorQuotient
      homega.le r).mp (hinfinite.2 r)

/-- Every finite real-ray Pick matrix is positive semidefinite exactly when no uncancelled divisor
direction survives. -/
theorem xiShiftEulerRay_everySample_posSemidef_iff_no_uncancelledDivisor
    {omega : ℝ} (homega : 0 < omega) :
    (∀ (N : ℕ) (w : Fin N → xiShiftEulerRaySet omega),
      (Matrix.of fun i j => xiShiftEulerRayKernel omega (w j) (w i)).PosSemidef) ↔
      ¬ HasIndependentDimensionAtLeast
        (XiShiftUncancelledDivisorQuotient homega.le) 1 := by
  let K := xiShiftEulerRayKernel omega
  have hHerm (N : ℕ) (w : Fin N → xiShiftEulerRaySet omega) :
      (Matrix.of fun i j => K (w j) (w i)).IsHermitian := by
    ext i j
    simp only [Matrix.of_apply, conjTranspose_apply]
    change (starRingEnd ℂ) (xiShiftEulerRayKernel omega (w i) (w j)) =
      xiShiftEulerRayKernel omega (w j) (w i)
    exact star_xiShiftEulerRayKernel_swap omega (w i) (w j)
  have hpsd :
      (∀ (N : ℕ) (w : Fin N → xiShiftEulerRaySet omega),
          (Matrix.of fun i j => K (w j) (w i)).PosSemidef) ↔
        ∀ (N : ℕ) (w : Fin N → xiShiftEulerRaySet omega),
          hermNegIndex (Matrix.of fun i j => K (w j) (w i)) ≤ 0 := by
    constructor
    · intro h N w
      rw [Nat.le_zero]
      exact (hermNegIndex_eq_zero_iff_posSemidef
        (hHerm N w)).mpr (h N w)
    · intro h N w
      apply (hermNegIndex_eq_zero_iff_posSemidef
        (hHerm N w)).mp
      exact Nat.eq_zero_of_le_zero (h N w)
  rw [hpsd, finite_sample_negIndex_le_iff_global_bound]
  constructor
  · intro hbound hbad
    have hneg :=
      (xiShiftEulerRay_negativeDimension_iff_uncancelledDivisorQuotient
        homega 1).mpr hbad
    exact (Nat.not_succ_le_self 0) (hbound 1 hneg)
  · intro hnot r hr
    have hq :=
      (xiShiftEulerRay_negativeDimension_iff_uncancelledDivisorQuotient
        homega r).mp hr
    by_contra hrle
    have h1r : 1 ≤ r := by omega
    exact hnot (hasIndependentDimensionAtLeast_of_le h1r hq)

/-- At a nonexceptional shift, absence of strict-right Xi zeros is equivalent to positive
semidefiniteness of every finite real Euler-ray Cauchy--Loewner matrix. -/
theorem xiShiftEulerRay_noZero_iff_everySample_posSemidef
    {omega : ℝ} (homega : 0 < omega)
    (hnon : SuzukiShiftNonexceptional omega) :
    IsEmpty (XiShiftRightZeroCopy omega) ↔
      ∀ (N : ℕ) (w : Fin N → xiShiftEulerRaySet omega),
        (Matrix.of fun i j => xiShiftEulerRayKernel omega (w j) (w i)).PosSemidef := by
  have hzeroQ : IsEmpty (XiShiftRightZeroCopy omega) ↔
      ¬ HasIndependentDimensionAtLeast
        (XiShiftUncancelledDivisorQuotient homega.le) 1 :=
    (eulerXiShiftPick_noZero_iff_everySample_posSemidef homega hnon).trans
      (eulerXiShiftPick_everySample_posSemidef_iff_no_uncancelledDivisor homega)
  exact hzeroQ.trans
    (xiShiftEulerRay_everySample_posSemidef_iff_no_uncancelledDivisor homega).symm

end
end RHTower
