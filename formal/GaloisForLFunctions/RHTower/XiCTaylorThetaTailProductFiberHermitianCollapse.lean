import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberPhaseOrientation
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberCurrent

/-!
# Hermitian collapse of the product-fibre displacement current

The complete centered divisor phase has strictly negative upper oriented current.  The raw Taylor
core, however, uses a Dirichlet-convolution coefficient `D_m * conj(V_n)` on `mn = k`, rather than
the current of the coherent divisor sum.  This module computes the seam-free common-tail model of
that Hermitian convolution exactly.

Divisor reflection makes the Hermitian phase trace real and centers the logarithmic derivative at
`log(k) / 2`.  The displacement derivative which carries the prime-factor orientation cancels.
The surviving current is therefore a real fibre trace times the common-tail current with the
explicit common-centre drift.  This is a positive exact identity: it identifies an additional
algebraic bridge which must be crossed before swept-window or finite-translation estimates can
transfer the strict divisor-phase sign to the raw core.
-/

open Complex Real Finset

namespace RHTower

noncomputable section

private theorem finset_sum_swap_eq
    {R : Type*} [AddCommMonoid R]
    (s : Finset (ℕ × ℕ)) (f : (ℕ × ℕ) → R)
    (hmem : ∀ q, q ∈ s → q.swap ∈ s) :
    (∑ q ∈ s, f q.swap) = ∑ q ∈ s, f q := by
  refine Finset.sum_bij' (fun q _ => q.swap) (fun q _ => q.swap)
    hmem hmem ?_ ?_ ?_
  · intro q _hq
    exact Prod.swap_swap q
  · intro q _hq
    exact Prod.swap_swap q
  · intro q _hq
    rfl

/-- A swap-conjugate finite packet has zero total imaginary part. -/
theorem finset_sum_im_eq_zero_of_swap_conj
    (s : Finset (ℕ × ℕ)) (c : (ℕ × ℕ) → ℂ)
    (hmem : ∀ q, q ∈ s → q.swap ∈ s)
    (hconj : ∀ q, q ∈ s → c q.swap = (starRingEnd ℂ) (c q)) :
    ∑ q ∈ s, (c q).im = 0 := by
  have hswap : (∑ q ∈ s, (c q.swap).im) = ∑ q ∈ s, (c q).im :=
    finset_sum_swap_eq s (fun q => (c q).im) hmem
  have hneg : (∑ q ∈ s, (c q.swap).im) = -(∑ q ∈ s, (c q).im) := by
    calc
      (∑ q ∈ s, (c q.swap).im) = ∑ q ∈ s, -(c q).im := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [hconj q hq]
        simp
      _ = -(∑ q ∈ s, (c q).im) := by
        rw [Finset.sum_neg_distrib]
  linarith

/-- In a swap-conjugate packet whose logarithmic labels are reflected about `L`, the real
logarithmic trace is exactly `L` times the real mass. -/
theorem finset_sum_log_mul_re_eq_center_mul_sum_re
    (s : Finset (ℕ × ℕ)) (c : (ℕ × ℕ) → ℂ)
    (ell : (ℕ × ℕ) → ℝ) (L : ℝ)
    (hmem : ∀ q, q ∈ s → q.swap ∈ s)
    (hconj : ∀ q, q ∈ s → c q.swap = (starRingEnd ℂ) (c q))
    (hcenter : ∀ q, q ∈ s → ell q.swap = 2 * L - ell q) :
    (∑ q ∈ s, ell q * (c q).re) =
      L * ∑ q ∈ s, (c q).re := by
  have hswap : (∑ q ∈ s, ell q.swap * (c q.swap).re) =
      ∑ q ∈ s, ell q * (c q).re :=
    finset_sum_swap_eq s (fun q => ell q * (c q).re) hmem
  have hreflect : (∑ q ∈ s, ell q.swap * (c q.swap).re) =
      2 * L * (∑ q ∈ s, (c q).re) -
        ∑ q ∈ s, ell q * (c q).re := by
    calc
      (∑ q ∈ s, ell q.swap * (c q.swap).re) =
          ∑ q ∈ s, (2 * L - ell q) * (c q).re := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [hcenter q hq, hconj q hq]
        simp
      _ = 2 * L * (∑ q ∈ s, (c q).re) -
          ∑ q ∈ s, ell q * (c q).re := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro q _hq
        ring
  linarith

/-- Hermitian correlation of a swap-conjugate translate packet against one common value--
derivative vector. -/
def hermitianCommonTailPacketCurrent
    (s : Finset (ℕ × ℕ)) (c : (ℕ × ℕ) → ℂ)
    (ell : (ℕ × ℕ) → ℝ) (F F' : ℂ) : ℝ :=
  ∑ q ∈ s,
    (c q *
      ((F' - ((ell q : ℝ) : ℂ) * I * F) * (starRingEnd ℂ) F)).im

/-- Exact Hermitian-collapse identity.  The reflected displacement derivative is absent from the
right side; only the real packet trace and the common logarithmic centre survive. -/
theorem hermitianCommonTailPacketCurrent_eq_centered
    (s : Finset (ℕ × ℕ)) (c : (ℕ × ℕ) → ℂ)
    (ell : (ℕ × ℕ) → ℝ) (L : ℝ) (F F' : ℂ)
    (hIm : ∑ q ∈ s, (c q).im = 0)
    (hlog : (∑ q ∈ s, ell q * (c q).re) =
      L * ∑ q ∈ s, (c q).re) :
    hermitianCommonTailPacketCurrent s c ell F F' =
      (∑ q ∈ s, (c q).re) *
        ((F' * (starRingEnd ℂ) F).im - L * Complex.normSq F) := by
  let A : ℂ := F' * (starRingEnd ℂ) F
  have hterm (q : ℕ × ℕ) :
      (c q *
          ((F' - ((ell q : ℝ) : ℂ) * I * F) *
            (starRingEnd ℂ) F)).im =
        (c q).re * A.im + (c q).im * A.re -
          ell q * (c q).re * Complex.normSq F := by
    dsimp only [A]
    rw [show
      c q *
          ((F' - ((ell q : ℝ) : ℂ) * I * F) *
            (starRingEnd ℂ) F) =
        c q * (F' * (starRingEnd ℂ) F) -
          (((ell q : ℝ) : ℂ) * I * c q) *
            (F * (starRingEnd ℂ) F) by ring,
      mul_conj]
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_re,
      zero_mul, add_zero, zero_add, mul_zero]
    ring
  unfold hermitianCommonTailPacketCurrent
  rw [show
      (∑ q ∈ s,
        (c q *
          ((F' - ((ell q : ℝ) : ℂ) * I * F) *
            (starRingEnd ℂ) F)).im) =
        ∑ q ∈ s,
          ((c q).re * A.im + (c q).im * A.re -
            ell q * (c q).re * Complex.normSq F) by
      apply Finset.sum_congr rfl
      intro q _hq
      exact hterm q]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
  dsimp only [A]
  rw [hIm, hlog]
  ring

/-- Critical translate coefficient carried by the positive square index `n`. -/
def thetaCriticalTranslateCoefficient (n : ℕ) (z : ℂ) : ℂ :=
  ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) *
    Complex.exp (((-Real.log n : ℝ) : ℂ) * I * z)

/-- Hermitian phase trace attached to an ordered positive factor pair. -/
def thetaProductFiberHermitianPhaseCoefficient
    (q : ℕ × ℕ) (z : ℂ) : ℂ :=
  thetaCriticalTranslateCoefficient (q.1 + 1) z *
    (starRingEnd ℂ) (thetaCriticalTranslateCoefficient (q.2 + 1) z)

theorem thetaProductFiberHermitianPhaseCoefficient_swap
    (q : ℕ × ℕ) (z : ℂ) :
    thetaProductFiberHermitianPhaseCoefficient q.swap z =
      (starRingEnd ℂ) (thetaProductFiberHermitianPhaseCoefficient q z) := by
  rcases q with ⟨a, b⟩
  unfold thetaProductFiberHermitianPhaseCoefficient
  simp only [Prod.swap_prod_mk, map_mul, Complex.conj_conj]
  ring

/-- Exact real trace of one Hermitian factor pair.  It is a critical positive amplitude times a
real-axis cosine; the upper-half-plane radial current of the analytic centered divisor phase is
not present. -/
theorem thetaProductFiberHermitianPhaseCoefficient_re
    (q : ℕ × ℕ) (z : ℂ) :
    (thetaProductFiberHermitianPhaseCoefficient q z).re =
      ((q.1 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((q.2 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.exp
          ((Real.log (q.1 + 1 : ℕ) + Real.log (q.2 + 1 : ℕ)) * z.im) *
        Real.cos
          ((Real.log (q.2 + 1 : ℕ) - Real.log (q.1 + 1 : ℕ)) * z.re) := by
  let a : ℝ := ((q.1 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
  let b : ℝ := ((q.2 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
  let u : ℝ := Real.log (q.1 + 1 : ℕ)
  let v : ℝ := Real.log (q.2 + 1 : ℕ)
  let e₁ : ℂ := ((-u : ℝ) : ℂ) * I * z
  let e₂ : ℂ := ((-v : ℝ) : ℂ) * I * z
  have hre : (e₁ + (starRingEnd ℂ) e₂).re = (u + v) * z.im := by
    dsimp only [e₁, e₂]
    simp only [Complex.add_re, Complex.conj_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero, zero_add]
    ring
  have him : (e₁ + (starRingEnd ℂ) e₂).im = (v - u) * z.re := by
    dsimp only [e₁, e₂]
    simp only [Complex.add_im, Complex.conj_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero, zero_add]
    ring
  have hproduct :
      (((a : ℝ) : ℂ) * Complex.exp e₁) *
          (starRingEnd ℂ) (((b : ℝ) : ℂ) * Complex.exp e₂) =
        (((a * b : ℝ) : ℂ)) *
          Complex.exp (e₁ + (starRingEnd ℂ) e₂) := by
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, ← Complex.exp_add]
    push_cast
    ring
  change ((((a : ℝ) : ℂ) * Complex.exp e₁) *
      (starRingEnd ℂ) (((b : ℝ) : ℂ) * Complex.exp e₂)).re = _
  rw [hproduct, Complex.mul_re, Complex.exp_re, hre, him]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rfl

/-- The full Hermitian fibre trace is an explicit signed cosine packet with positive critical
amplitudes. -/
theorem sum_thetaProductFiberHermitianPhaseCoefficient_re
    (k : ℕ) (z : ℂ) :
    (∑ q ∈ thetaPositiveFactorPairs k,
      (thetaProductFiberHermitianPhaseCoefficient q z).re) =
      ∑ q ∈ thetaPositiveFactorPairs k,
        ((q.1 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
          ((q.2 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.exp
            ((Real.log (q.1 + 1 : ℕ) + Real.log (q.2 + 1 : ℕ)) * z.im) *
          Real.cos
            ((Real.log (q.2 + 1 : ℕ) - Real.log (q.1 + 1 : ℕ)) * z.re) := by
  apply Finset.sum_congr rfl
  intro q _hq
  exact thetaProductFiberHermitianPhaseCoefficient_re q z

/-- The seam-free common-tail model of one fixed-product Hermitian convolution fibre. -/
def thetaProductFiberCommonTailHermitianCurrent
    (k : ℕ) (z F F' : ℂ) : ℝ :=
  hermitianCommonTailPacketCurrent
    (thetaPositiveFactorPairs k)
    (fun q => thetaProductFiberHermitianPhaseCoefficient q z)
    (fun q => Real.log (q.1 + 1 : ℕ)) F F'

/-- Exact product-fibre collapse.  In the Hermitian convolution the strict centered-divisor phase
current is replaced by a real trace multiplying the common-tail current and the explicit
common-centre drift `-log(k)|F|^2/2`. -/
theorem thetaProductFiberCommonTailHermitianCurrent_eq
    (k : ℕ) (z F F' : ℂ) :
    thetaProductFiberCommonTailHermitianCurrent k z F F' =
      (∑ q ∈ thetaPositiveFactorPairs k,
          (thetaProductFiberHermitianPhaseCoefficient q z).re) *
        ((F' * (starRingEnd ℂ) F).im -
          (Real.log k / 2) * Complex.normSq F) := by
  apply hermitianCommonTailPacketCurrent_eq_centered
  · exact finset_sum_im_eq_zero_of_swap_conj
      (thetaPositiveFactorPairs k)
      (fun q => thetaProductFiberHermitianPhaseCoefficient q z)
      (fun q hq => thetaPositiveFactorPairs_swap_mem hq)
      (fun q _hq => thetaProductFiberHermitianPhaseCoefficient_swap q z)
  · apply finset_sum_log_mul_re_eq_center_mul_sum_re
    · exact fun q hq => thetaPositiveFactorPairs_swap_mem hq
    · exact fun q _hq => thetaProductFiberHermitianPhaseCoefficient_swap q z
    · intro q hq
      have hqlog := thetaFactorPair_log_decomposition hq
      change Real.log (q.2 + 1 : ℕ) =
        2 * (Real.log k / 2) - Real.log (q.1 + 1 : ℕ)
      linarith

/-- If the real Hermitian fibre trace is negative, even the seam-free common unit tail has
strictly positive current.  Thus negativity of the coherent analytic divisor phase cannot be
transferred through Hermitian convolution without an additional value relation controlling this
trace. -/
theorem thetaProductFiberCommonTailHermitianCurrent_one_pos_of_trace_neg
    {k : ℕ} (hk : 1 < k) {z : ℂ}
    (htrace : (∑ q ∈ thetaPositiveFactorPairs k,
      (thetaProductFiberHermitianPhaseCoefficient q z).re) < 0) :
    0 < thetaProductFiberCommonTailHermitianCurrent k z 1 0 := by
  rw [thetaProductFiberCommonTailHermitianCurrent_eq]
  have hlog : 0 < Real.log k := Real.log_pos (by exact_mod_cast hk)
  simp only [map_one, mul_one, Complex.zero_im, zero_sub]
  exact mul_pos_of_neg_of_neg htrace (by linarith)

/-! ## Exact model-plus-joint-defect decomposition of the canonical moment fibre -/

/-- Common-tail translate model for the value packet of the zero-based density index `n`. -/
def thetaProductFiberCommonTailModelValue
    (z F : ℂ) (n : ℕ) : ℂ :=
  thetaCriticalTranslateCoefficient (n + 1) z * F

/-- Common-tail translate model for the derivative packet.  The logarithmic drift is kept inside
the derivative vector rather than estimated separately. -/
def thetaProductFiberCommonTailModelDerivative
    (z F F' : ℂ) (n : ℕ) : ℂ :=
  thetaCriticalTranslateCoefficient (n + 1) z *
    (F' - ((Real.log (n + 1 : ℕ) : ℝ) : ℂ) * I * F)

/-- Exact value defect between the canonical finite moment packet and a chosen common-tail
translate model. -/
def thetaProductFiberCoreValueJointDefect
    (d : ℕ) (z F : ℂ) (n : ℕ) : ℂ :=
  thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z n -
    thetaProductFiberCommonTailModelValue z F n

/-- Exact derivative defect.  It is deliberately paired with the value defect before any norm or
absolute-value estimate is introduced. -/
def thetaProductFiberCoreDerivativeJointDefect
    (d : ℕ) (z F F' : ℂ) (n : ℕ) : ℂ :=
  thetaCuspTailSecondDensityAtomCoreDerivativeMomentPacket d z n -
    thetaProductFiberCommonTailModelDerivative z F F' n

/-- Algebraic four-term Hermitian expansion which keeps the two mixed defects and their
self-current together. -/
theorem complexHermitianModelJointDefectIdentity
    (D V D₀ V₀ : ℂ) :
    (D * (starRingEnd ℂ) V).im =
      (D₀ * (starRingEnd ℂ) V₀).im +
        (D₀ * (starRingEnd ℂ) (V - V₀)).im +
        ((D - D₀) * (starRingEnd ℂ) V₀).im +
        ((D - D₀) * (starRingEnd ℂ) (V - V₀)).im := by
  have hcomplex :
      D * (starRingEnd ℂ) V =
        D₀ * (starRingEnd ℂ) V₀ +
          D₀ * (starRingEnd ℂ) (V - V₀) +
          (D - D₀) * (starRingEnd ℂ) V₀ +
          (D - D₀) * (starRingEnd ℂ) (V - V₀) := by
    rw [map_sub]
    ring
  rw [hcomplex]
  simp only [Complex.add_im]

/-- Seam-free common-tail base carried by one fixed product fibre. -/
def xiCTaylorThetaTailCoreProductFiberCommonTailBaseCurrent
    (k : ℕ) (z F F' : ℂ) : ℝ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    (thetaProductFiberCommonTailModelDerivative z F F' q.1 *
      (starRingEnd ℂ)
        (thetaProductFiberCommonTailModelValue z F q.2)).im

/-- The complete joint defect of one product fibre.  The model--defect mixed currents and the
defect self-current remain in one signed expression. -/
def xiCTaylorThetaTailCoreProductFiberJointDefectCurrent
    (d k : ℕ) (z F F' : ℂ) : ℝ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    ((thetaProductFiberCommonTailModelDerivative z F F' q.1 *
          (starRingEnd ℂ)
            (thetaProductFiberCoreValueJointDefect d z F q.2)).im +
      (thetaProductFiberCoreDerivativeJointDefect d z F F' q.1 *
          (starRingEnd ℂ)
            (thetaProductFiberCommonTailModelValue z F q.2)).im +
      (thetaProductFiberCoreDerivativeJointDefect d z F F' q.1 *
          (starRingEnd ℂ)
            (thetaProductFiberCoreValueJointDefect d z F q.2)).im)

/-- The common-tail base is exactly the collapsed Hermitian packet computed above. -/
theorem xiCTaylorThetaTailCoreProductFiberCommonTailBaseCurrent_eq
    (k : ℕ) (z F F' : ℂ) :
    xiCTaylorThetaTailCoreProductFiberCommonTailBaseCurrent k z F F' =
      thetaProductFiberCommonTailHermitianCurrent k z F F' := by
  unfold xiCTaylorThetaTailCoreProductFiberCommonTailBaseCurrent
    thetaProductFiberCommonTailHermitianCurrent
    hermitianCommonTailPacketCurrent
    thetaProductFiberCommonTailModelDerivative
    thetaProductFiberCommonTailModelValue
    thetaProductFiberHermitianPhaseCoefficient
  apply Finset.sum_congr rfl
  intro q _hq
  rw [map_mul]
  ring

/-- **Exact canonical fibre decomposition.**  For every choice of common-tail vector, the actual
finite moment-convolution coefficient is the collapsed base plus one joint defect current.  No
piece has been bounded or assigned a sign. -/
theorem xiCTaylorThetaTailCoreProductFiberMomentCurrent_eq_commonTail_add_jointDefect
    (d k : ℕ) (z F F' : ℂ) :
    xiCTaylorThetaTailCoreProductFiberMomentCurrent d z k =
      xiCTaylorThetaTailCoreProductFiberCommonTailBaseCurrent k z F F' +
        xiCTaylorThetaTailCoreProductFiberJointDefectCurrent d k z F F' := by
  rw [xiCTaylorThetaTailCoreProductFiberMomentCurrent_eq_unsymmetrized]
  unfold xiCTaylorThetaTailCoreAtomPairComplexMomentCorrelation
    xiCTaylorThetaTailCoreProductFiberCommonTailBaseCurrent
    xiCTaylorThetaTailCoreProductFiberJointDefectCurrent
    thetaProductFiberCoreValueJointDefect
    thetaProductFiberCoreDerivativeJointDefect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  simpa only [add_assoc] using
    (complexHermitianModelJointDefectIdentity
      (thetaCuspTailSecondDensityAtomCoreDerivativeMomentPacket d z q.1)
      (thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z q.2)
      (thetaProductFiberCommonTailModelDerivative z F F' q.1)
      (thetaProductFiberCommonTailModelValue z F q.2))

end

end RHTower
