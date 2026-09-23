import GaloisForLFunctions.RHTower.SlabFullWidthAdmissibility
import GaloisForLFunctions.RHTower.CCMTwoPoleSourceCriterion

/-!
# The conjugated germ theorem on the slab

The germ-residue transport (`SlabGermResidueTransport`, with admissibility discharged in
`SlabFullWidthAdmissibility`) evaluates holomorphic boundary weights on the slab
`S(γ, h) = [γ − h, γ + h] × [−c, c]` against the continued prime–archimedean source trace,
producing multiplicity-weighted divisor sums over the height fiber.  This module extends the
boundary calculus to **conjugated** weights `conj((z − γ)^a) · (z − γ)^b` and to the
displacement weight `Im(z − γ) · (z − γ)`, through the thin-slab reduction:

* **the fiber is purely imaginary in the centered frame** — every fiber point `w` has
  `Re(w − γ) = 0`, so `conj(w − γ) = −(w − γ)` exactly
  (`conj_sub_center_of_mem_heightFiber`); consequently the fiber Hermitian Gram
  `∑ m_w · conj((w − γ)^a) · (w − γ)^b` collapses to `(−1)^a` times the centered fiber
  moment of order `a + b` (`heightFiberHermitianGram_eq`);
* **general entire-weight transport** (`slabWeightedContour_eq_packetSum`) — the contour
  pairing of any entire weight with the continued trace equals the multiplicity-weighted
  packet sum, extending the monomial transport of `SlabGermResidueTransport`;
* **the conjugated germ theorem** (`exists_conjugatedGermTheorem`) — at every height there
  are a band and a gap below which the reflected boundary moment (`conj` replaced by the
  reflection `u ↦ −u`, an entire weight) equals the fiber Hermitian Gram for **all**
  bidegrees `(a, b)`: Hermitian fiber data is divisor-free boundary-computable;
* **exact conjugation-defect decompositions** at every positive half-width
  (`slabConjugatedMoment_one_decomposition`, `slabConjugatedMoment_two_decomposition`,
  `slabDisplacementMoment_decomposition`) — the genuinely conjugated boundary moment equals
  the reflected moment plus a contour term whose weight carries an explicit factor
  `Re(z − γ)`, bounded by the half-width on the slab (`norm_defect_weight_one`,
  `norm_defect_weight_two`, `norm_displacement_defect_weight`, with
  `abs_re_sub_center_le`): the conjugation defect is `O(h)` pointwise on the boundary;
* **the displacement-weighted germ** (`exists_displacementGerm_rh_equivalence`) — below the
  gap the reflected displacement moment (weight `−i (z − γ)²`, the reflected form of
  `Im(z − γ) · (z − γ)`) equals `i` times the **fiber variance** `∑ m_w (Im w)²`, and its
  vanishing is equivalent to the height fiber lying on the critical line, to the fiber
  being a single point, and to the vanishing of the slab contour Gram expression of
  `SlabGermResidueTransport` — all at one common band and gap.

The remaining analytic surface for the genuinely conjugated germs is the vanishing of the
defect contour terms as `h → 0⁺`; their integrands are already exhibited here with the
explicit `Re(z − γ)` factor and pointwise slab bounds.
-/

open Complex Set Filter Topology

namespace RHTower
namespace SlabConjugatedGermTheorem

open SlabGermResidueTransport SlabFullWidthAdmissibility

noncomputable section

/-! ## §1 The height fiber is purely imaginary in the centered frame -/

/-- The centered coordinate of a height-fiber point is purely imaginary. -/
theorem sub_center_eq_im_mul_I {γ c : ℝ} (hc : 0 ≤ c) {w : ℂ}
    (hw : w ∈ heightFiber γ c) : w - (γ : ℂ) = ((w.im : ℝ) : ℂ) * I := by
  have hre : w.re = γ := ((mem_heightFiber hc).mp hw).1
  apply Complex.ext
  · simp [Complex.mul_re, hre]
  · simp [Complex.mul_im]

/-- On the height fiber, conjugation of the centered coordinate is the reflection
`u ↦ −u`. -/
theorem conj_sub_center_of_mem_heightFiber {γ c : ℝ} (hc : 0 ≤ c) {w : ℂ}
    (hw : w ∈ heightFiber γ c) :
    (starRingEnd ℂ) (w - (γ : ℂ)) = -(w - (γ : ℂ)) := by
  have hre : w.re = γ := ((mem_heightFiber hc).mp hw).1
  apply Complex.ext
  · simp [hre]
  · simp

/-- Conjugation preserves the height fiber: the centered Xi divisor is symmetric under the
Schwarz reflection of the spectral coordinate. -/
theorem heightFiber_conj_mem {γ c : ℝ} (hc : 0 ≤ c) {w : ℂ}
    (hw : w ∈ heightFiber γ c) : (starRingEnd ℂ) w ∈ heightFiber γ c := by
  obtain ⟨hre, ⟨h1, h2⟩, hXi⟩ := (mem_heightFiber hc).mp hw
  have hcre : ((starRingEnd ℂ) w).re = γ := by simp [hre]
  have hcim : ((starRingEnd ℂ) w).im = -w.im := Complex.conj_im w
  refine (mem_heightFiber hc).mpr ⟨hcre, ⟨?_, ?_⟩, ?_⟩
  · rw [hcim]; linarith
  · rw [hcim]; linarith
  · rw [XiC_conj, hXi, map_zero]

/-- **The line dichotomy of the fiber.**  The height fiber lies on the critical line
(`Im w = 0` throughout) iff it is a single point: one direction pins every fiber point to
the real height `γ`, the other uses the conjugation symmetry of the fiber. -/
theorem heightFiber_im_eq_zero_iff_subsingleton {γ c : ℝ} (hc : 0 ≤ c) :
    (∀ w ∈ heightFiber γ c, w.im = 0) ↔
      ∀ w ∈ heightFiber γ c, ∀ w' ∈ heightFiber γ c, w = w' := by
  constructor
  · intro hline w hw w' hw'
    have h1 : w = (γ : ℂ) :=
      Complex.ext (by rw [((mem_heightFiber hc).mp hw).1, Complex.ofReal_re])
        (by rw [hline w hw, Complex.ofReal_im])
    have h2 : w' = (γ : ℂ) :=
      Complex.ext (by rw [((mem_heightFiber hc).mp hw').1, Complex.ofReal_re])
        (by rw [hline w' hw', Complex.ofReal_im])
    rw [h1, h2]
  · intro hpt w hw
    have heq : w = (starRingEnd ℂ) w := hpt w hw _ (heightFiber_conj_mem hc hw)
    have him := congrArg Complex.im heq
    rw [Complex.conj_im] at him
    linarith

/-! ## §2 The fiber Hermitian Gram, the centered moments, and the fiber variance -/

/-- The `k`-th centered multiplicity-weighted divisor moment of the height fiber:
`∑ m_w (w − γ)^k` in the frame centered at the height. -/
def heightFiberCenteredMoment (k : ℕ) (γ c : ℝ) : ℂ :=
  ∑ w ∈ heightFiber γ c, ((analyticOrderAt XiC w).toNat : ℂ) * (w - (γ : ℂ)) ^ k

/-- The fiber Hermitian Gram entry of bidegree `(a, b)`:
`∑ m_w · conj((w − γ)^a) · (w − γ)^b` — the genuinely conjugated (sesquilinear) pairing of
centered monomials over the height fiber. -/
def heightFiberHermitianGram (a b : ℕ) (γ c : ℝ) : ℂ :=
  ∑ w ∈ heightFiber γ c,
    ((analyticOrderAt XiC w).toNat : ℂ) * (starRingEnd ℂ) ((w - (γ : ℂ)) ^ a) *
      (w - (γ : ℂ)) ^ b

/-- The fiber variance: the multiplicity-weighted second moment of the imaginary offsets of
the height fiber, a nonnegative real. -/
def fiberVariance (γ c : ℝ) : ℝ :=
  ∑ w ∈ heightFiber γ c, xiPacketMass w * w.im ^ (2 : ℕ)

theorem xiPacketMass_nonneg (w : ℂ) : 0 ≤ xiPacketMass w := by
  unfold xiPacketMass
  exact Nat.cast_nonneg _

theorem fiberVariance_nonneg (γ c : ℝ) : 0 ≤ fiberVariance γ c :=
  Finset.sum_nonneg fun w _ => mul_nonneg (xiPacketMass_nonneg w) (sq_nonneg _)

/-- The fiber variance vanishes iff the height fiber lies on the critical line. -/
theorem fiberVariance_eq_zero_iff {γ c : ℝ} (hc : 0 ≤ c) :
    fiberVariance γ c = 0 ↔ ∀ w ∈ heightFiber γ c, w.im = 0 := by
  unfold fiberVariance
  rw [Finset.sum_eq_zero_iff_of_nonneg
    fun w _ => mul_nonneg (xiPacketMass_nonneg w) (sq_nonneg _)]
  constructor
  · intro hz w hw
    have hm : xiPacketMass w ≠ 0 :=
      (xiPacketMass_pos ((mem_heightFiber hc).mp hw).2.2).ne'
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp (hz w hw)).resolve_left hm)
  · intro hz w hw
    rw [hz w hw]
    ring

/-- **Hermitian collapse on the imaginary fiber.**  Because the centered fiber coordinate
is purely imaginary, the Hermitian Gram entry of bidegree `(a, b)` is `(−1)^a` times the
centered fiber moment of order `a + b`: sesquilinear fiber data is linear fiber data. -/
theorem heightFiberHermitianGram_eq {γ c : ℝ} (hc : 0 ≤ c) (a b : ℕ) :
    heightFiberHermitianGram a b γ c =
      (-1) ^ a * heightFiberCenteredMoment (a + b) γ c := by
  unfold heightFiberHermitianGram heightFiberCenteredMoment
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [map_pow, conj_sub_center_of_mem_heightFiber hc hw, neg_pow, pow_add]
  ring

/-- The second centered fiber moment is minus the fiber variance. -/
theorem heightFiberCenteredMoment_two {γ c : ℝ} (hc : 0 ≤ c) :
    heightFiberCenteredMoment 2 γ c = -((fiberVariance γ c : ℝ) : ℂ) := by
  have hcast : ((fiberVariance γ c : ℝ) : ℂ) =
      ∑ w ∈ heightFiber γ c,
        ((analyticOrderAt XiC w).toNat : ℂ) * ((w.im : ℝ) : ℂ) ^ (2 : ℕ) := by
    unfold fiberVariance xiPacketMass
    push_cast
    rfl
  have hterm : heightFiberCenteredMoment 2 γ c =
      ∑ w ∈ heightFiber γ c,
        -(((analyticOrderAt XiC w).toNat : ℂ) * ((w.im : ℝ) : ℂ) ^ (2 : ℕ)) := by
    unfold heightFiberCenteredMoment
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [sub_center_eq_im_mul_I hc hw, mul_pow, Complex.I_sq]
    ring
  rw [hterm, hcast]
  simp

/-- Sanity value: the `(1, 1)` Hermitian Gram entry is the fiber variance itself — the
Hermitian pairing of the displacement coordinate with itself is nonnegative real. -/
theorem heightFiberHermitianGram_one_one {γ c : ℝ} (hc : 0 ≤ c) :
    heightFiberHermitianGram 1 1 γ c = ((fiberVariance γ c : ℝ) : ℂ) := by
  have h2 : (1 + 1 : ℕ) = 2 := rfl
  rw [heightFiberHermitianGram_eq hc 1 1, h2, heightFiberCenteredMoment_two hc, pow_one]
  ring

/-! ## §3 General entire-weight contour transport -/

/-- The normalized boundary pairing of a weight `g` with the continued prime–archimedean
source trace on the slab: `(2πi)⁻¹ ∮_{∂S(γ,h)} g · trace`. -/
def slabWeightedContour (g : ℂ → ℂ) (γ h c : ℝ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ *
    rectIntegral (fun z => g z * continuedPrimeArchSourceRelativeTrace z)
      (slabLower γ h c) (slabUpper γ h c)

private theorem two_pi_I_ne_zero : (2 * Real.pi * I : ℂ) ≠ 0 := by
  apply mul_ne_zero (mul_ne_zero two_ne_zero ?_) I_ne_zero
  exact_mod_cast Real.pi_ne_zero

/-- **Entire-weight transport.**  On an admissible slab the normalized boundary pairing of
any entire weight equals its multiplicity-weighted sum over the enclosed packet. -/
theorem slabWeightedContour_eq_packetSum {γ h c : ℝ} (hh : 0 < h) (hc : 0 < c)
    (hadm : SlabAdmissible γ h c) {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ) :
    slabWeightedContour g γ h c =
      ∑ w ∈ slabPacket γ h c, ((analyticOrderAt XiC w).toNat : ℂ) * g w := by
  have hre : (slabLower γ h c).re < (slabUpper γ h c).re := by
    rw [slabLower_re, slabUpper_re]; linarith
  have him : (slabLower γ h c).im < (slabUpper γ h c).im := by
    rw [slabLower_im, slabUpper_im]; linarith
  have hbot : ∀ x ∈ uIcc (slabLower γ h c).re (slabUpper γ h c).re,
      XiExplicitAdmissible ((x : ℂ) + ((slabLower γ h c).im : ℂ) * I) := by
    intro x hx
    rw [slabLower_re, slabUpper_re] at hx
    rw [slabLower_im]
    exact hadm.bottom x hx
  have htop : ∀ x ∈ uIcc (slabLower γ h c).re (slabUpper γ h c).re,
      XiExplicitAdmissible ((x : ℂ) + ((slabUpper γ h c).im : ℂ) * I) := by
    intro x hx
    rw [slabLower_re, slabUpper_re] at hx
    rw [slabUpper_im]
    exact hadm.top x hx
  have hrig : ∀ y ∈ uIcc (slabLower γ h c).im (slabUpper γ h c).im,
      XiExplicitAdmissible (((slabUpper γ h c).re : ℂ) + (y : ℂ) * I) := by
    intro y hy
    rw [slabLower_im, slabUpper_im] at hy
    rw [slabUpper_re]
    exact hadm.right y hy
  have hlef : ∀ y ∈ uIcc (slabLower γ h c).im (slabUpper γ h c).im,
      XiExplicitAdmissible (((slabLower γ h c).re : ℂ) + (y : ℂ) * I) := by
    intro y hy
    rw [slabLower_im, slabUpper_im] at hy
    rw [slabLower_re]
    exact hadm.left y hy
  have hmain := rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_closedRectangleZeroSum
    hg hre him hbot htop hrig hlef
  unfold slabWeightedContour
  rw [hmain, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]
  rfl

/-! ## §4 Edgewise integrability and additivity of the boundary pairing -/

private theorem continuousAt_logDeriv_XiC {z : ℂ} (hz : XiC z ≠ 0) :
    ContinuousAt (logDeriv XiC) z := by
  have hA : AnalyticAt ℂ XiC z := XiC_analytic z (Set.mem_univ z)
  have hld : AnalyticAt ℂ (logDeriv XiC) z := by
    rw [show logDeriv XiC = fun w => deriv XiC w / XiC w from rfl]
    exact hA.deriv.div hA hz
  exact hld.continuousAt

/-- Along an admissible edge parametrization, any continuous weight times the continued
trace is interval integrable: on the admissible set the trace agrees with the continuous
logarithmic derivative of `XiC`. -/
private theorem intervalIntegrable_admissible_edge {F : ℂ → ℂ} (hF : Continuous F)
    {e : ℝ → ℂ} (he : Continuous e) {a b : ℝ}
    (hadm : ∀ t ∈ uIcc a b, XiExplicitAdmissible (e t)) :
    IntervalIntegrable
      (fun t => F (e t) * continuedPrimeArchSourceRelativeTrace (e t))
      MeasureTheory.volume a b := by
  have hcont : ContinuousOn (fun t => F (e t) * logDeriv XiC (e t)) (uIcc a b) := by
    refine ContinuousOn.mul (hF.comp he).continuousOn ?_
    intro t ht
    exact ((continuousAt_logDeriv_XiC
      (XiC_ne_zero_of_admissible (hadm t ht))).comp he.continuousAt).continuousWithinAt
  have heq : Set.EqOn
      (fun t => F (e t) * continuedPrimeArchSourceRelativeTrace (e t))
      (fun t => F (e t) * logDeriv XiC (e t)) (uIcc a b) := by
    intro t ht
    have hA := hadm t ht
    have h1 : continuedPrimeArchSourceRelativeTrace (e t) = xiRelativeResolventTrace (e t) :=
      continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
        hA.re_pos hA.ne_one hA.zeta_ne
    have h2 : logDeriv XiC (e t) = xiRelativeResolventTrace (e t) :=
      logDeriv_XiC_eq_relativeResolventTrace (XiC_ne_zero_of_admissible hA)
    dsimp only
    rw [h1, h2]
  exact (hcont.congr heq).intervalIntegrable

/-- **Additivity of the boundary pairing** over a sum of continuous weights, on an
admissible slab. -/
theorem slabWeightedContour_add {γ h c : ℝ} (hadm : SlabAdmissible γ h c)
    {F G : ℂ → ℂ} (hF : Continuous F) (hG : Continuous G) :
    slabWeightedContour (fun z => F z + G z) γ h c =
      slabWeightedContour F γ h c + slabWeightedContour G γ h c := by
  have hbot : ∀ x ∈ uIcc (slabLower γ h c).re (slabUpper γ h c).re,
      XiExplicitAdmissible ((x : ℂ) + ((slabLower γ h c).im : ℂ) * I) := by
    intro x hx
    rw [slabLower_re, slabUpper_re] at hx
    rw [slabLower_im]
    exact hadm.bottom x hx
  have htop : ∀ x ∈ uIcc (slabLower γ h c).re (slabUpper γ h c).re,
      XiExplicitAdmissible ((x : ℂ) + ((slabUpper γ h c).im : ℂ) * I) := by
    intro x hx
    rw [slabLower_re, slabUpper_re] at hx
    rw [slabUpper_im]
    exact hadm.top x hx
  have hrig : ∀ y ∈ uIcc (slabLower γ h c).im (slabUpper γ h c).im,
      XiExplicitAdmissible (((slabUpper γ h c).re : ℂ) + (y : ℂ) * I) := by
    intro y hy
    rw [slabLower_im, slabUpper_im] at hy
    rw [slabUpper_re]
    exact hadm.right y hy
  have hlef : ∀ y ∈ uIcc (slabLower γ h c).im (slabUpper γ h c).im,
      XiExplicitAdmissible (((slabLower γ h c).re : ℂ) + (y : ℂ) * I) := by
    intro y hy
    rw [slabLower_im, slabUpper_im] at hy
    rw [slabLower_re]
    exact hadm.left y hy
  have hebot : Continuous fun x : ℝ => (x : ℂ) + ((slabLower γ h c).im : ℂ) * I :=
    Complex.continuous_ofReal.add continuous_const
  have hetop : Continuous fun x : ℝ => (x : ℂ) + ((slabUpper γ h c).im : ℂ) * I :=
    Complex.continuous_ofReal.add continuous_const
  have herig : Continuous fun y : ℝ => ((slabUpper γ h c).re : ℂ) + (y : ℂ) * I :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have helef : Continuous fun y : ℝ => ((slabLower γ h c).re : ℂ) + (y : ℂ) * I :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  unfold slabWeightedContour
  rw [← mul_add]
  congr 1
  rw [show (fun z => (F z + G z) * continuedPrimeArchSourceRelativeTrace z)
      = fun z => F z * continuedPrimeArchSourceRelativeTrace z
          + G z * continuedPrimeArchSourceRelativeTrace z from
    funext fun z => add_mul _ _ _]
  exact rectIntegral_add
    (intervalIntegrable_admissible_edge hF hebot hbot)
    (intervalIntegrable_admissible_edge hG hebot hbot)
    (intervalIntegrable_admissible_edge hF hetop htop)
    (intervalIntegrable_admissible_edge hG hetop htop)
    (intervalIntegrable_admissible_edge hF herig hrig)
    (intervalIntegrable_admissible_edge hG herig hrig)
    (intervalIntegrable_admissible_edge hF helef hlef)
    (intervalIntegrable_admissible_edge hG helef hlef)

/-! ## §5 Conjugated, reflected, and displacement boundary moments -/

/-- The genuinely conjugated slab boundary moment of bidegree `(a, b)`:
`(2πi)⁻¹ ∮ conj((z − γ)^a) · (z − γ)^b · trace`. -/
def slabConjugatedMoment (a b : ℕ) (γ h c : ℝ) : ℂ :=
  slabWeightedContour
    (fun z => (starRingEnd ℂ) ((z - (γ : ℂ)) ^ a) * (z - (γ : ℂ)) ^ b) γ h c

/-- The reflected slab boundary moment of bidegree `(a, b)`: the conjugation replaced by
the reflection `u ↦ −u` of the centered coordinate — an entire weight. -/
def slabReflectedMoment (a b : ℕ) (γ h c : ℝ) : ℂ :=
  slabWeightedContour (fun z => (-(z - (γ : ℂ))) ^ a * (z - (γ : ℂ)) ^ b) γ h c

/-- The displacement-weighted slab boundary moment:
`(2πi)⁻¹ ∮ Im(z − γ) · (z − γ) · trace`. -/
def slabDisplacementMoment (γ h c : ℝ) : ℂ :=
  slabWeightedContour (fun z => (((z - (γ : ℂ)).im : ℝ) : ℂ) * (z - (γ : ℂ))) γ h c

/-- The reflected displacement moment: the entire weight `−i (z − γ)²`, obtained from the
displacement weight `Im(z − γ) · (z − γ) = (u − conj u) u / (2i)` by the reflection
`conj u ↦ −u`. -/
def slabDisplacementReflectedMoment (γ h c : ℝ) : ℂ :=
  slabWeightedContour (fun z => -I * (z - (γ : ℂ)) ^ (2 : ℕ)) γ h c

private theorem conj_eq_two_re_sub (u : ℂ) :
    (starRingEnd ℂ) u = ((2 * u.re : ℝ) : ℂ) - u := by
  have h := Complex.add_conj u
  linear_combination h

private theorem analyticOnNhd_reflectedWeight (γ : ℝ) (a b : ℕ) :
    AnalyticOnNhd ℂ (fun z : ℂ => (-(z - (γ : ℂ))) ^ a * (z - (γ : ℂ)) ^ b) Set.univ := by
  have h1 : Differentiable ℂ fun z : ℂ => z - (γ : ℂ) := differentiable_id.sub_const _
  exact ((h1.neg.pow a).mul (h1.pow b)).differentiableOn.analyticOnNhd isOpen_univ

private theorem analyticOnNhd_displacementReflectedWeight (γ : ℝ) :
    AnalyticOnNhd ℂ (fun z : ℂ => -I * (z - (γ : ℂ)) ^ (2 : ℕ)) Set.univ := by
  have h1 : Differentiable ℂ fun z : ℂ => z - (γ : ℂ) := differentiable_id.sub_const _
  exact ((differentiable_const _).mul (h1.pow 2)).differentiableOn.analyticOnNhd isOpen_univ

/-! ## §6 The conjugated germ theorem -/

/-- **The conjugated germ theorem.**  At every height there are a band strictly inside the
critical strip and a gap below which the reflected boundary moment of every bidegree
`(a, b)` equals the fiber Hermitian Gram entry of the full height fiber: genuinely
conjugated (sesquilinear) fiber data is evaluated by divisor-free boundary integrals of
entire weights.  Unconditional at every height. -/
theorem exists_conjugatedGermTheorem (γ : ℝ) :
    ∃ c h₀ : ℝ, 0 < c ∧ c < 1 / 2 ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ a b : ℕ,
      slabReflectedMoment a b γ h c = heightFiberHermitianGram a b γ (1 / 2) := by
  obtain ⟨c, h₁, hc0, hc12, hh₁pos, hfib, hadm⟩ := exists_slabAdmissible_family γ
  obtain ⟨g₀, hg₀pos, _, hgap⟩ := exists_slabGap γ c hc0.le
  refine ⟨c, min g₀ h₁, hc0, hc12, lt_min hg₀pos hh₁pos, ?_⟩
  intro h hh0 hh a b
  rw [slabReflectedMoment,
    slabWeightedContour_eq_packetSum hh0 hc0 (hadm h hh0 (hh.trans (min_le_right _ _)))
      (analyticOnNhd_reflectedWeight γ a b),
    hgap h hh0 (hh.trans (min_le_left _ _)), hfib]
  unfold heightFiberHermitianGram
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [map_pow, conj_sub_center_of_mem_heightFiber (by norm_num : (0 : ℝ) ≤ 1 / 2) hw]
  ring

/-! ## §7 Exact conjugation-defect decompositions at positive half-width -/

/-- **Thin-slab decomposition, bidegree `(1, b)`.**  At every positive half-width the
conjugated boundary moment is the reflected moment plus a defect contour term whose weight
carries the explicit factor `2 · Re(z − γ)`. -/
theorem slabConjugatedMoment_one_decomposition {γ h c : ℝ}
    (hadm : SlabAdmissible γ h c) (b : ℕ) :
    slabConjugatedMoment 1 b γ h c =
      slabReflectedMoment 1 b γ h c +
        slabWeightedContour
          (fun z => ((2 * (z - (γ : ℂ)).re : ℝ) : ℂ) * (z - (γ : ℂ)) ^ b) γ h c := by
  have hsub : Continuous fun z : ℂ => z - (γ : ℂ) := continuous_id.sub continuous_const
  have hre : Continuous fun z : ℂ => (z - (γ : ℂ)).re := Complex.continuous_re.comp hsub
  have hF : Continuous fun z : ℂ => (-(z - (γ : ℂ))) ^ (1 : ℕ) * (z - (γ : ℂ)) ^ b :=
    (hsub.neg.pow 1).mul (hsub.pow b)
  have hG : Continuous fun z : ℂ =>
      ((2 * (z - (γ : ℂ)).re : ℝ) : ℂ) * (z - (γ : ℂ)) ^ b :=
    (Complex.continuous_ofReal.comp (continuous_const.mul hre)).mul (hsub.pow b)
  have hw : (fun z : ℂ => (starRingEnd ℂ) ((z - (γ : ℂ)) ^ (1 : ℕ)) * (z - (γ : ℂ)) ^ b)
      = fun z : ℂ => (-(z - (γ : ℂ))) ^ (1 : ℕ) * (z - (γ : ℂ)) ^ b
          + ((2 * (z - (γ : ℂ)).re : ℝ) : ℂ) * (z - (γ : ℂ)) ^ b := by
    funext z
    rw [map_pow, conj_eq_two_re_sub (z - (γ : ℂ))]
    push_cast
    ring
  unfold slabConjugatedMoment slabReflectedMoment
  rw [hw, slabWeightedContour_add hadm hF hG]

/-- **Thin-slab decomposition, bidegree `(2, b)`.**  The defect weight carries the factor
`4 · Re(z − γ)` against the purely imaginary part `Re(z − γ) − (z − γ)` of the centered
coordinate. -/
theorem slabConjugatedMoment_two_decomposition {γ h c : ℝ}
    (hadm : SlabAdmissible γ h c) (b : ℕ) :
    slabConjugatedMoment 2 b γ h c =
      slabReflectedMoment 2 b γ h c +
        slabWeightedContour
          (fun z => ((4 * (z - (γ : ℂ)).re : ℝ) : ℂ) *
            ((((z - (γ : ℂ)).re : ℝ) : ℂ) - (z - (γ : ℂ))) * (z - (γ : ℂ)) ^ b)
          γ h c := by
  have hsub : Continuous fun z : ℂ => z - (γ : ℂ) := continuous_id.sub continuous_const
  have hre : Continuous fun z : ℂ => (z - (γ : ℂ)).re := Complex.continuous_re.comp hsub
  have hF : Continuous fun z : ℂ => (-(z - (γ : ℂ))) ^ (2 : ℕ) * (z - (γ : ℂ)) ^ b :=
    (hsub.neg.pow 2).mul (hsub.pow b)
  have hG : Continuous fun z : ℂ =>
      ((4 * (z - (γ : ℂ)).re : ℝ) : ℂ) *
        ((((z - (γ : ℂ)).re : ℝ) : ℂ) - (z - (γ : ℂ))) * (z - (γ : ℂ)) ^ b :=
    ((Complex.continuous_ofReal.comp (continuous_const.mul hre)).mul
      ((Complex.continuous_ofReal.comp hre).sub hsub)).mul (hsub.pow b)
  have hw : (fun z : ℂ => (starRingEnd ℂ) ((z - (γ : ℂ)) ^ (2 : ℕ)) * (z - (γ : ℂ)) ^ b)
      = fun z : ℂ => (-(z - (γ : ℂ))) ^ (2 : ℕ) * (z - (γ : ℂ)) ^ b
          + ((4 * (z - (γ : ℂ)).re : ℝ) : ℂ) *
              ((((z - (γ : ℂ)).re : ℝ) : ℂ) - (z - (γ : ℂ))) * (z - (γ : ℂ)) ^ b := by
    funext z
    rw [map_pow, conj_eq_two_re_sub (z - (γ : ℂ))]
    push_cast
    ring
  unfold slabConjugatedMoment slabReflectedMoment
  rw [hw, slabWeightedContour_add hadm hF hG]

/-- **Thin-slab decomposition of the displacement moment.**  The displacement weight
`Im(z − γ) · (z − γ)` is the reflected weight `−i (z − γ)²` plus the defect weight
`i · Re(z − γ) · (z − γ)`. -/
theorem slabDisplacementMoment_decomposition {γ h c : ℝ} (hadm : SlabAdmissible γ h c) :
    slabDisplacementMoment γ h c =
      slabDisplacementReflectedMoment γ h c +
        slabWeightedContour
          (fun z => I * (((z - (γ : ℂ)).re : ℝ) : ℂ) * (z - (γ : ℂ))) γ h c := by
  have hsub : Continuous fun z : ℂ => z - (γ : ℂ) := continuous_id.sub continuous_const
  have hre : Continuous fun z : ℂ => (z - (γ : ℂ)).re := Complex.continuous_re.comp hsub
  have hF : Continuous fun z : ℂ => -I * (z - (γ : ℂ)) ^ (2 : ℕ) :=
    continuous_const.mul (hsub.pow 2)
  have hG : Continuous fun z : ℂ => I * (((z - (γ : ℂ)).re : ℝ) : ℂ) * (z - (γ : ℂ)) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp hre)).mul hsub
  have hw : (fun z : ℂ => (((z - (γ : ℂ)).im : ℝ) : ℂ) * (z - (γ : ℂ)))
      = fun z : ℂ => -I * (z - (γ : ℂ)) ^ (2 : ℕ)
          + I * (((z - (γ : ℂ)).re : ℝ) : ℂ) * (z - (γ : ℂ)) := by
    funext z
    have hu : z - (γ : ℂ) =
        (((z - (γ : ℂ)).re : ℝ) : ℂ) + (((z - (γ : ℂ)).im : ℝ) : ℂ) * I :=
      (Complex.re_add_im (z - (γ : ℂ))).symm
    linear_combination ((z - (γ : ℂ)) * I) * hu
      + ((z - (γ : ℂ)) * (((z - (γ : ℂ)).im : ℝ) : ℂ)) * Complex.I_sq
  unfold slabDisplacementMoment slabDisplacementReflectedMoment
  rw [hw, slabWeightedContour_add hadm hF hG]

/-! ## §8 Pointwise slab bounds on the defect weights -/

/-- On the closed slab the centered real part is bounded by the half-width. -/
theorem abs_re_sub_center_le {γ h : ℝ} {z : ℂ} (h1 : γ - h ≤ z.re) (h2 : z.re ≤ γ + h) :
    |(z - (γ : ℂ)).re| ≤ h := by
  rw [Complex.sub_re, Complex.ofReal_re, abs_le]
  constructor <;> linarith

/-- The bidegree-`(1, b)` defect weight is `O(h)` pointwise on the slab. -/
theorem norm_defect_weight_one {γ h : ℝ} {z : ℂ} (hre : |(z - (γ : ℂ)).re| ≤ h) (b : ℕ) :
    ‖((2 * (z - (γ : ℂ)).re : ℝ) : ℂ) * (z - (γ : ℂ)) ^ b‖ ≤
      2 * h * ‖z - (γ : ℂ)‖ ^ b := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two]
  exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (norm_nonneg _) b)

private theorem norm_ofReal_re_sub (u : ℂ) : ‖((u.re : ℝ) : ℂ) - u‖ = |u.im| := by
  have h : ((u.re : ℝ) : ℂ) - u = -(((u.im : ℝ) : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [h, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- The bidegree-`(2, b)` defect weight is `O(h)` pointwise on the slab. -/
theorem norm_defect_weight_two {γ h : ℝ} {z : ℂ} (hre : |(z - (γ : ℂ)).re| ≤ h) (b : ℕ) :
    ‖((4 * (z - (γ : ℂ)).re : ℝ) : ℂ) *
        ((((z - (γ : ℂ)).re : ℝ) : ℂ) - (z - (γ : ℂ))) * (z - (γ : ℂ)) ^ b‖ ≤
      4 * h * |(z - (γ : ℂ)).im| * ‖z - (γ : ℂ)‖ ^ b := by
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    norm_ofReal_re_sub]
  have h4 : |(4 : ℝ)| = 4 := by norm_num
  rw [h4]
  have hstep : 4 * |(z - (γ : ℂ)).re| * |(z - (γ : ℂ)).im| ≤
      4 * h * |(z - (γ : ℂ)).im| :=
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  exact mul_le_mul_of_nonneg_right hstep (pow_nonneg (norm_nonneg _) b)

/-- The displacement defect weight is `O(h)` pointwise on the slab. -/
theorem norm_displacement_defect_weight {γ h : ℝ} {z : ℂ}
    (hre : |(z - (γ : ℂ)).re| ≤ h) :
    ‖I * (((z - (γ : ℂ)).re : ℝ) : ℂ) * (z - (γ : ℂ))‖ ≤ h * ‖z - (γ : ℂ)‖ := by
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hre (norm_nonneg _)

/-! ## §9 The displacement germ and the line criterion -/

/-- **The displacement-weighted germ, final form.**  At every height there are one band
and one gap below which, simultaneously: the reflected displacement moment equals `i`
times the fiber variance; its vanishing is equivalent to the height fiber lying on the
critical line, and equivalent to the vanishing of the slab contour Gram expression; and
the genuinely displacement-weighted moment differs from `i` times the fiber variance by
the explicit defect contour term.  The critical line at height `γ` is thereby read off a
single divisor-free boundary integral. -/
theorem exists_displacementGerm_rh_equivalence (γ : ℝ) :
    ∃ c h₀ : ℝ, 0 < c ∧ c < 1 / 2 ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
      slabDisplacementReflectedMoment γ h c =
        I * ((fiberVariance γ (1 / 2) : ℝ) : ℂ) ∧
      (slabDisplacementReflectedMoment γ h c = 0 ↔
        ∀ w ∈ heightFiber γ (1 / 2), w.im = 0) ∧
      (slabDisplacementReflectedMoment γ h c = 0 ↔ slabContourGram γ h c = 0) ∧
      slabDisplacementMoment γ h c =
        I * ((fiberVariance γ (1 / 2) : ℝ) : ℂ) +
          slabWeightedContour
            (fun z => I * (((z - (γ : ℂ)).re : ℝ) : ℂ) * (z - (γ : ℂ))) γ h c := by
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  obtain ⟨c, h₁, hc0, hc12, hh₁pos, hfib, hadm⟩ := exists_slabAdmissible_family γ
  obtain ⟨g₀, hg₀pos, _, hgap⟩ := exists_slabGap γ c hc0.le
  obtain ⟨h₂, hh₂pos, _, hGram⟩ := exists_slabContourGram_germ hc0 hh₁pos hadm
  refine ⟨c, min (min g₀ h₁) h₂, hc0, hc12,
    lt_min (lt_min hg₀pos hh₁pos) hh₂pos, ?_⟩
  intro h hh0 hh
  have hh_g₀ : h ≤ g₀ := hh.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hh_h₁ : h ≤ h₁ := hh.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hh_h₂ : h ≤ h₂ := hh.trans (min_le_right _ _)
  have hadm' := hadm h hh0 hh_h₁
  have hval : slabDisplacementReflectedMoment γ h c =
      I * ((fiberVariance γ (1 / 2) : ℝ) : ℂ) := by
    rw [slabDisplacementReflectedMoment,
      slabWeightedContour_eq_packetSum hh0 hc0 hadm'
        (analyticOnNhd_displacementReflectedWeight γ),
      hgap h hh0 hh_g₀, hfib]
    have hsum : ∑ w ∈ heightFiber γ (1 / 2),
        ((analyticOrderAt XiC w).toNat : ℂ) * (-I * (w - (γ : ℂ)) ^ (2 : ℕ))
        = -I * heightFiberCenteredMoment 2 γ (1 / 2) := by
      rw [heightFiberCenteredMoment, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [hsum, heightFiberCenteredMoment_two hhalf]
    ring
  have hIV : I * ((fiberVariance γ (1 / 2) : ℝ) : ℂ) = 0 ↔
      ∀ w ∈ heightFiber γ (1 / 2), w.im = 0 := by
    constructor
    · intro h0
      refine (fiberVariance_eq_zero_iff hhalf).mp ?_
      rcases mul_eq_zero.mp h0 with hI | hV
      · exact absurd hI I_ne_zero
      · exact_mod_cast hV
    · intro hline
      rw [(fiberVariance_eq_zero_iff hhalf).mpr hline]
      simp
  refine ⟨hval, ?_, ?_, ?_⟩
  · rw [hval]
    exact hIV
  · obtain ⟨hGeq, _, _⟩ := hGram h hh0 hh_h₂
    have hfg : heightFiberGram γ c = heightFiberGram γ (1 / 2) := by
      simp only [heightFiberGram]
      rw [hfib]
    rw [hval, hGeq, hfg, heightFiberGram_eq_zero_iff hhalf, hIV,
      heightFiber_im_eq_zero_iff_subsingleton hhalf]
  · rw [slabDisplacementMoment_decomposition hadm', hval]

end

end SlabConjugatedGermTheorem
end RHTower
