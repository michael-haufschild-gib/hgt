import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberPhaseOrientation

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
      zero_mul, add_zero, zero_add, one_mul, mul_zero]
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
    {k : ℕ} (hk : k ≠ 0) (z F F' : ℂ) :
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
  rw [thetaProductFiberCommonTailHermitianCurrent_eq (by omega)]
  have hlog : 0 < Real.log k := Real.log_pos (by exact_mod_cast hk)
  simp only [zero_mul, map_one, mul_one, Complex.zero_im, Complex.normSq_one,
    zero_sub]
  exact mul_pos_of_neg_of_neg htrace (by linarith)

end

end RHTower
