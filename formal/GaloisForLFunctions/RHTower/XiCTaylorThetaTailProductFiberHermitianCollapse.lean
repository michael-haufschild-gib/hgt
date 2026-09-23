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
    simp only [Complex.add_re, Complex.conj_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero]
    ring
  have him : (e₁ + (starRingEnd ℂ) e₂).im = (v - u) * z.re := by
    dsimp only [e₁, e₂]
    simp only [Complex.add_im, Complex.conj_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero]
    ring
  have hproduct :
      (((a : ℝ) : ℂ) * Complex.exp e₁) *
          (starRingEnd ℂ) (((b : ℝ) : ℂ) * Complex.exp e₂) =
        (((a * b : ℝ) : ℂ)) *
          Complex.exp (e₁ + (starRingEnd ℂ) e₂) := by
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    calc
      (((a : ℝ) : ℂ) * Complex.exp e₁) *
          (((b : ℝ) : ℂ) * Complex.exp ((starRingEnd ℂ) e₂)) =
        ((((a : ℝ) : ℂ) * ((b : ℝ) : ℂ))) *
          (Complex.exp e₁ * Complex.exp ((starRingEnd ℂ) e₂)) := by ring
      _ = (((a * b : ℝ) : ℂ)) *
          Complex.exp (e₁ + (starRingEnd ℂ) e₂) := by
        rw [← Complex.exp_add]
        norm_cast
  change ((((a : ℝ) : ℂ) * Complex.exp e₁) *
      (starRingEnd ℂ) (((b : ℝ) : ℂ) * Complex.exp e₂)).re = _
  rw [hproduct, Complex.mul_re, Complex.exp_re, hre, him]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  dsimp only [a, b, u, v]
  ring

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

/-- The Hermitian fibre trace is not a new arithmetic packet: it is the positive critical
amplitude times the complete centered-divisor packet on the real spectral slice `2 * z.re`.
Unlike the upper-half-plane phase current, this is a signed real value and may oscillate. -/
theorem sum_thetaProductFiberHermitianPhaseCoefficient_re_eq_centeredPhase_real
    (k : ℕ) (z : ℂ) :
    (∑ q ∈ thetaPositiveFactorPairs k,
        (thetaProductFiberHermitianPhaseCoefficient q z).re) =
      (k : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (Real.log k * z.im) *
          (thetaProductFiberCenteredPhase k (((2 * z.re : ℝ) : ℂ))).re := by
  rw [sum_thetaProductFiberHermitianPhaseCoefficient_re]
  unfold thetaProductFiberCenteredPhase
  rw [Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hdecomp := thetaFactorPair_log_decomposition hq
  have hprod : (q.1 + 1) * (q.2 + 1) = k :=
    (Finset.mem_filter.mp hq).2
  have hweight :
      ((q.1 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
          ((q.2 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) =
        (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    exact_mod_cast hprod
  rw [hweight, hdecomp.1, hdecomp.2]
  simp only [Complex.exp_re, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, zero_add, mul_zero, one_mul]
  ring_nf
  rw [Real.cos_neg]
  simp

/-- Prime-power value factorization of the Hermitian trace.  It is an exact arithmetic signed
polarization, but its coefficients are real Euler-packet values rather than favorable norm
squares. -/
theorem sum_thetaProductFiberHermitianPhaseCoefficient_re_eq_factorized_real
    {k : ℕ} (hk : k ≠ 0) (z : ℂ) :
    (∑ q ∈ thetaPositiveFactorPairs k,
        (thetaProductFiberHermitianPhaseCoefficient q z).re) =
      (k : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (Real.log k * z.im) *
          (GaloisForLFunctions.HTGeometry.factorizedCenteredDivisorPhase
            k (((2 * z.re : ℝ) : ℂ))).re := by
  rw [sum_thetaProductFiberHermitianPhaseCoefficient_re_eq_centeredPhase_real]
  rw [thetaProductFiberCenteredPhase_eq_centeredDivisorPhase hk]
  rw [GaloisForLFunctions.HTGeometry.centeredDivisorPhase_eq_factorized hk]

/-- The first nontrivial positive product fibre consists of the two reflected ordered pairs. -/
theorem thetaPositiveFactorPairs_two :
    thetaPositiveFactorPairs 2 = {(0, 1), (1, 0)} := by
  norm_num [thetaPositiveFactorPairs, Finset.ext_iff]
  intro a b
  constructor
  · rintro ⟨⟨ha, hb⟩, hab⟩
    interval_cases a <;> interval_cases b <;> norm_num at hab
    all_goals norm_num
  · rintro (h | h)
    · rcases h with ⟨rfl, rfl⟩
      norm_num
    · rcases h with ⟨rfl, rfl⟩
      norm_num

/-- Closed trace formula on the first nontrivial product fibre.  The trace is a boundary cosine,
so its sign oscillates with the real coordinate even though the coherent analytic fibre current
is strictly negative throughout the upper half-plane. -/
theorem sum_thetaProductFiberHermitianPhaseCoefficient_re_two
    (z : ℂ) :
    ( ∑ q ∈ thetaPositiveFactorPairs 2,
        (thetaProductFiberHermitianPhaseCoefficient q z).re) =
      2 * ((2 : ℝ) ^ (-(1 / 2 : ℝ))) *
        Real.exp (Real.log 2 * z.im) *
          Real.cos (Real.log 2 * z.re) := by
  rw [thetaPositiveFactorPairs_two,
    Finset.sum_insert (by norm_num), Finset.sum_singleton,
    thetaProductFiberHermitianPhaseCoefficient_re,
    thetaProductFiberHermitianPhaseCoefficient_re]
  norm_num only [Prod.fst, Prod.snd, Nat.cast_ofNat, Real.one_rpow,
    Real.log_one, zero_add, add_zero, sub_zero, zero_sub, Real.cos_neg]
  rw [show -Real.log 2 * z.re = -(Real.log 2 * z.re) by ring,
    Real.cos_neg]
  ring

/-- Exact upper-half-plane point at which Hermitian fixed-product polarization reverses the
favorable coherent-fibre sign. -/
def thetaProductFiberHermitianSignReversalPoint : ℂ :=
  ⟨Real.pi / Real.log 2, 1 / 4⟩

@[simp] theorem thetaProductFiberHermitianSignReversalPoint_re :
    thetaProductFiberHermitianSignReversalPoint.re = Real.pi / Real.log 2 := rfl

@[simp] theorem thetaProductFiberHermitianSignReversalPoint_im :
    thetaProductFiberHermitianSignReversalPoint.im = 1 / 4 := rfl

/-- The Hermitian trace on the first nontrivial fibre is strictly negative at the exact reversal
point.  No endpoint window or finite-section top edge is involved. -/
theorem sum_thetaProductFiberHermitianPhaseCoefficient_re_two_lt_zero :
    ( ∑ q ∈ thetaPositiveFactorPairs 2,
        (thetaProductFiberHermitianPhaseCoefficient q
          thetaProductFiberHermitianSignReversalPoint).re) < 0 := by
  rw [sum_thetaProductFiberHermitianPhaseCoefficient_re_two]
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hphase :
      Real.log (2 : ℝ) * (Real.pi / Real.log (2 : ℝ)) = Real.pi := by
    field_simp
  rw [thetaProductFiberHermitianSignReversalPoint_re,
    thetaProductFiberHermitianSignReversalPoint_im, hphase, Real.cos_pi]
  have hamp : 0 <
      ((2 : ℝ) ^ (-(1 / 2 : ℝ))) *
        Real.exp (Real.log 2 * (1 / 4 : ℝ)) :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.exp_pos _)
  nlinarith

/-- The seam-free common-tail model of one fixed-product Hermitian convolution fibre. -/
def thetaProductFiberCommonTailHermitianCurrent
    (k : ℕ) (z F F' : ℂ) : ℝ :=
  hermitianCommonTailPacketCurrent
    (thetaPositiveFactorPairs k)
    (fun q => thetaProductFiberHermitianPhaseCoefficient q z)
    (fun q => Real.log (q.1 + 1 : ℕ)) F F'

/-- Exact product-fibre collapse.  In the Hermitian convolution the strict centered-divisor phase
current is replaced by a real trace multiplying the common-tail current and the explicit
common-centre drift `-log(k)|F|^(2 : ℕ)/2`. -/
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

/-- Full multiplicative form of the collapsed Hermitian base.  The critical amplitude is
positive; every sign change is therefore carried jointly by the real prime-power divisor packet
and the common-tail current with its centered logarithmic drift. -/
theorem thetaProductFiberCommonTailHermitianCurrent_eq_factorized_real
    {k : ℕ} (hk : k ≠ 0) (z F F' : ℂ) :
    thetaProductFiberCommonTailHermitianCurrent k z F F' =
      ((k : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (Real.log k * z.im) *
          (GaloisForLFunctions.HTGeometry.factorizedCenteredDivisorPhase
            k (((2 * z.re : ℝ) : ℂ))).re) *
        ((F' * (starRingEnd ℂ) F).im -
          (Real.log k / 2) * Complex.normSq F) := by
  rw [thetaProductFiberCommonTailHermitianCurrent_eq,
    sum_thetaProductFiberHermitianPhaseCoefficient_re_eq_factorized_real hk]

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

/-- **Exact polarization sign reversal.**  At one explicit point in the canonical upper strip,
the coherent divisor-phase current on the fibre `k = 2` is strictly negative while the seam-free
Hermitian current of the common unit tail is strictly positive.  Consequently the coherent
prime-factor sign cannot furnish a nonpositive base for the fixed-product Hermitian convolution
with an error consisting only of endpoint windows and finite translation edges: a separate
polarization defect is already present when both of those seams vanish. -/
theorem thetaProductFiberHermitianPolarization_sign_reversal :
    (thetaProductFiberCenteredPhaseDerivative 2
          thetaProductFiberHermitianSignReversalPoint *
        (starRingEnd ℂ) (thetaProductFiberCenteredPhase 2
          thetaProductFiberHermitianSignReversalPoint)).im < 0 ∧
      0 < thetaProductFiberCommonTailHermitianCurrent 2
        thetaProductFiberHermitianSignReversalPoint 1 0 := by
  constructor
  · exact thetaProductFiberCenteredPhase_current_lt_zero
      (k := 2) (by norm_num)
      (z := thetaProductFiberHermitianSignReversalPoint) (by norm_num)
  · exact thetaProductFiberCommonTailHermitianCurrent_one_pos_of_trace_neg
      (k := 2) (by norm_num)
        sum_thetaProductFiberHermitianPhaseCoefficient_re_two_lt_zero

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

/-! ## Corrected coherent-base bridge and the unavoidable polarization defect -/

/-- Coherent analytic divisor-phase current weighted by the common-tail norm square.  Unlike the
Hermitian anti-diagonal base, this is the quantity to which prime-factor polarization applies. -/
def xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent
    (k : ℕ) (z F : ℂ) : ℝ :=
  Complex.normSq F *
    (thetaProductFiberCenteredPhaseDerivative k z *
      (starRingEnd ℂ) (thetaProductFiberCenteredPhase k z)).im

/-- The coherent base retains the exact prime-factor signed polarization, with the common-tail
norm square absorbed into each complementary packet coefficient. -/
theorem xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent_eq_primeFactors
    {k : ℕ} (hk : k ≠ 0) (z F : ℂ) :
    xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent k z F =
      ∑ p ∈ k.primeFactors,
        (Complex.normSq F *
          Complex.normSq
            (∏ q ∈ k.primeFactors.erase p,
              GaloisForLFunctions.HTGeometry.primePowerCenteredDivisorPhase
                q (k.factorization q) z)) *
          (GaloisForLFunctions.HTGeometry.primePowerCenteredDivisorPhaseDerivative
              p (k.factorization p) z *
            (starRingEnd ℂ)
              (GaloisForLFunctions.HTGeometry.primePowerCenteredDivisorPhase
                p (k.factorization p) z)).im := by
  unfold xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent
  rw [thetaProductFiberCenteredPhase_current_eq_sum_primeFactors hk,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  ring

/-- Every nontrivial coherent product-fibre base has favorable nonpositive upper orientation. -/
theorem xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent_nonpos
    {k : ℕ} (hk : 1 < k) {z : ℂ} (hz : 0 < z.im) (F : ℂ) :
    xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent k z F ≤ 0 := by
  unfold xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent
  exact mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg F)
    (thetaProductFiberCenteredPhase_current_lt_zero hk hz).le

/-- Algebraic defect between the Hermitian anti-diagonal common-tail base and the coherent
prime-oriented phase base.  It is present before endpoint restriction and finite translation. -/
def xiCTaylorThetaTailCoreProductFiberPolarizationDefectCurrent
    (k : ℕ) (z F F' : ℂ) : ℝ :=
  xiCTaylorThetaTailCoreProductFiberCommonTailBaseCurrent k z F F' -
    xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent k z F

/-- The corrected joint seam is the sum of the algebraic Hermitian-polarization defect and the
unsplit canonical model defect.  No absolute values or separate piece estimates occur here. -/
def xiCTaylorThetaTailCoreProductFiberCorrectedJointSeamCurrent
    (d k : ℕ) (z F F' : ℂ) : ℝ :=
  xiCTaylorThetaTailCoreProductFiberPolarizationDefectCurrent k z F F' +
    xiCTaylorThetaTailCoreProductFiberJointDefectCurrent d k z F F'

/-- **Corrected exact fixed-product bridge.**  The actual canonical coefficient is a favorable
coherent prime-factor base plus one joint seam, but that seam necessarily contains the additional
Hermitian-polarization defect besides endpoint and finite-translation defects. -/
theorem xiCTaylorThetaTailCoreProductFiberMomentCurrent_eq_coherentBase_add_correctedJointSeam
    (d k : ℕ) (z F F' : ℂ) :
    xiCTaylorThetaTailCoreProductFiberMomentCurrent d z k =
      xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent k z F +
        xiCTaylorThetaTailCoreProductFiberCorrectedJointSeamCurrent d k z F F' := by
  rw [xiCTaylorThetaTailCoreProductFiberMomentCurrent_eq_commonTail_add_jointDefect]
  unfold xiCTaylorThetaTailCoreProductFiberCorrectedJointSeamCurrent
    xiCTaylorThetaTailCoreProductFiberPolarizationDefectCurrent
  ring

/-- The coherent prime-oriented base is nonpositive on every product fibre.  The fibres `0` and
`1` carry no centered phase current; every nontrivial fibre has the strict prime-factor sign. -/
theorem xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent_nonpos_all
    (k : ℕ) {z : ℂ} (hz : 0 < z.im) (F : ℂ) :
    xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent k z F ≤ 0 := by
  by_cases hk : 1 < k
  · exact xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent_nonpos hk hz F
  · have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · simp [xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent,
        thetaProductFiberCenteredPhase, thetaProductFiberCenteredPhaseDerivative,
        thetaPositiveFactorPairs, thetaFactorPairLogDisplacement]
    · have hpairs : thetaPositiveFactorPairs 1 = {(0, 0)} := by
        ext q
        rcases q with ⟨a, b⟩
        simp [thetaPositiveFactorPairs]
      have hderivative : thetaProductFiberCenteredPhaseDerivative 1 z = 0 := by
        rw [thetaProductFiberCenteredPhaseDerivative, hpairs]
        simp [thetaFactorPairLogDisplacement]
      simp [xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent, hderivative]

/-- **The corrected seam dominates the RH-bearing fibre current.**  Once the coherent
prime-factor base has been extracted, its favorable sign makes the remaining joint seam an upper
majorant of the actual canonical coefficient, not a smaller error term. -/
theorem xiCTaylorThetaTailCoreProductFiberMomentCurrent_le_correctedJointSeam
    (d k : ℕ) {z : ℂ} (hz : 0 < z.im) (F F' : ℂ) :
    xiCTaylorThetaTailCoreProductFiberMomentCurrent d z k ≤
      xiCTaylorThetaTailCoreProductFiberCorrectedJointSeamCurrent d k z F F' := by
  rw [xiCTaylorThetaTailCoreProductFiberMomentCurrent_eq_coherentBase_add_correctedJointSeam]
  linarith [xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent_nonpos_all k hz F]

/-- On every nontrivial fibre and for every nonzero common tail, the domination is strict.  Thus
the polarization defect cannot be absorbed into a negligible endpoint/top-edge remainder even at
the level of an upper estimate. -/
theorem xiCTaylorThetaTailCoreProductFiberMomentCurrent_lt_correctedJointSeam
    (d : ℕ) {k : ℕ} (hk : 1 < k) {z : ℂ} (hz : 0 < z.im)
    {F : ℂ} (hF : F ≠ 0) (F' : ℂ) :
    xiCTaylorThetaTailCoreProductFiberMomentCurrent d z k <
      xiCTaylorThetaTailCoreProductFiberCorrectedJointSeamCurrent d k z F F' := by
  have hbase :
      xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent k z F < 0 := by
    unfold xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent
    exact mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr hF)
      (thetaProductFiberCenteredPhase_current_lt_zero hk hz)
  rw [xiCTaylorThetaTailCoreProductFiberMomentCurrent_eq_coherentBase_add_correctedJointSeam]
  linarith

/-- Finite product-fibre summation preserves the domination for arbitrary fibre-dependent common
tails.  This is the exact finite form relevant before any cofinal summability passage. -/
theorem sum_xiCTaylorThetaTailCoreProductFiberMomentCurrent_le_correctedJointSeam
    (d K : ℕ) {z : ℂ} (hz : 0 < z.im) (F F' : ℕ → ℂ) :
    (∑ k ∈ Finset.range K,
        xiCTaylorThetaTailCoreProductFiberMomentCurrent d z k) ≤
      ∑ k ∈ Finset.range K,
        xiCTaylorThetaTailCoreProductFiberCorrectedJointSeamCurrent
          d k z (F k) (F' k) := by
  exact Finset.sum_le_sum fun k _hk =>
    xiCTaylorThetaTailCoreProductFiberMomentCurrent_le_correctedJointSeam
      d k hz (F k) (F' k)

/-- The extra polarization defect is strictly positive at the exact sign-reversal point, even for
the common unit tail.  Hence it cannot be omitted from the corrected seam or represented solely
by swept windows and finite translation edges, both of which vanish in this model. -/
theorem xiCTaylorThetaTailCoreProductFiberPolarizationDefectCurrent_two_pos :
    0 < xiCTaylorThetaTailCoreProductFiberPolarizationDefectCurrent 2
      thetaProductFiberHermitianSignReversalPoint 1 0 := by
  have hsign := thetaProductFiberHermitianPolarization_sign_reversal
  have hhermitian : 0 <
      xiCTaylorThetaTailCoreProductFiberCommonTailBaseCurrent 2
        thetaProductFiberHermitianSignReversalPoint 1 0 := by
    rw [xiCTaylorThetaTailCoreProductFiberCommonTailBaseCurrent_eq]
    exact hsign.2
  have hcoherent :
      xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent 2
        thetaProductFiberHermitianSignReversalPoint 1 < 0 := by
    simpa only [xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent,
      Complex.normSq_one, one_mul] using hsign.1
  unfold xiCTaylorThetaTailCoreProductFiberPolarizationDefectCurrent
  linarith

end

end RHTower
