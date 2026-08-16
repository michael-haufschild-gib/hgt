import GaloisForLFunctions.HTGeometry.TruncatedConvolutionCommutator
import GaloisForLFunctions.RHTower.CCMGeneralParityOddGroundAdapter

/-!
# The Fourier compression of a truncated convolution is a centered divided-difference packet

The exact commutator law for an even `C¹` kernel says that the matrix of the truncated convolution
in the exponential basis is the divided difference of its boundary source.  Transporting that
statement to the centered parity index of the parity-free odd-ground law identifies the compressed
form as a centered divided-difference matrix with an odd source and a reflection-even diagonal:
exactly the matrix class for which a simple odd kernel vector has a real-rooted Fourier transform.
-/

open Matrix

open scoped Matrix ComplexOrder

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The centered source of the truncated-convolution packet. -/
def truncConvParitySource (k : ℝ → ℝ) (N : ℕ) (i : CCMCenteredParityIndex N) : ℝ :=
  -(convSource k (ccmParityCenteredMode N i)).re

/-- The centered diagonal of the truncated-convolution packet. -/
def truncConvParityDiagonal (k : ℝ → ℝ) (N : ℕ) (i : CCMCenteredParityIndex N) : ℝ :=
  (convMatrix k (ccmParityCenteredMode N i) (ccmParityCenteredMode N i)).re

/-- **The source is odd.** -/
theorem truncConvParitySource_odd (k : ℝ → ℝ) (N : ℕ) (i : CCMCenteredParityIndex N) :
    truncConvParitySource k N (ccmCenteredParityReflection N i)
      = -truncConvParitySource k N i := by
  rw [truncConvParitySource, truncConvParitySource, ccmParityCenteredMode_reflection,
    convSource_re_neg]

/-- **The diagonal is reflection even.** -/
theorem truncConvParityDiagonal_even {k : ℝ → ℝ} (heven : ∀ u, k (-u) = k u) (N : ℕ)
    (i : CCMCenteredParityIndex N) :
    truncConvParityDiagonal k N (ccmCenteredParityReflection N i)
      = truncConvParityDiagonal k N i := by
  rw [truncConvParityDiagonal, truncConvParityDiagonal, ccmParityCenteredMode_reflection,
    convMatrix_reflect heven]

/-- **The matrix identification.**  Every entry of the compressed truncated convolution is the
corresponding entry of the centered divided-difference matrix built from its boundary source and
its own diagonal. -/
theorem ccmDividedDifferenceMatrix_truncConv {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (hk'c : Continuous k') (heven : ∀ u, k (-u) = k u) (N : ℕ)
    (i j : CCMCenteredParityIndex N) :
    ccmDividedDifferenceMatrix (ccmParityCenteredClock N) (truncConvParitySource k N)
        (truncConvParityDiagonal k N) i j
      = (convMatrix k (ccmParityCenteredMode N i) (ccmParityCenteredMode N j)).re := by
  rw [ccmDividedDifferenceMatrix]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, truncConvParityDiagonal]
  · rw [if_neg hij]
    have hclock : ccmParityCenteredClock N i - ccmParityCenteredClock N j ≠ 0 := by
      intro h
      exact hij (ccmParityCenteredClock_injective N (by linarith [sub_eq_zero.1 h]))
    have hmode : ccmParityCenteredClock N i - ccmParityCenteredClock N j
        = ((ccmParityCenteredMode N i : ℝ) - (ccmParityCenteredMode N j : ℝ)) := by
      rw [ccmParityCenteredClock, ccmParityCenteredClock]
    have hcomm := convMatrix_re_commutator hk hk'c heven
      (ccmParityCenteredMode N i) (ccmParityCenteredMode N j)
    rw [truncConvParitySource, truncConvParitySource]
    rw [hmode] at hclock ⊢
    field_simp
    linarith [hcomm]

/-- The truncated-convolution packet on the centered parity index. -/
def truncConvParityPacket (k : ℝ → ℝ) (N : ℕ) (mu : ℝ) :
    Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ :=
  ccmCenteredParityPacket (truncConvParitySource k N) (truncConvParityDiagonal k N) mu

/-- **The compressed truncated convolution, shifted by any spectral floor, is a centered parity
packet.**  Its entries away from the diagonal are the divided differences of the boundary source,
its source is odd, and its diagonal is reflection even, so a simple odd kernel vector of the packet
has a real-rooted band-limited Fourier transform. -/
theorem truncConvParityPacket_compactFourier_zero_im_eq_zero {k k' : ℝ → ℝ}
    (_hk : ∀ u, HasDerivAt k (k' u) u) (_hk'c : Continuous k') (heven : ∀ u, k (-u) = k u)
    {N : ℕ} {mu : ℝ} (hpsd : (truncConvParityPacket k N mu).PosSemidef)
    {c : Fin N → ℂ} (hc : c ≠ 0)
    (hground : truncConvParityPacket k N mu *ᵥ (ccmOddParityFrame N *ᵥ c) = 0)
    (hline : ∀ v : CCMCenteredParityIndex N → ℂ,
      truncConvParityPacket k N mu *ᵥ v = 0 →
        ∃ z : ℂ, v = z • (ccmOddParityFrame N *ᵥ c))
    {z : ℂ}
    (hzero : compactFourier (ccmTrigPoly N (ccmOddGroundCoeff N c)) 0 (2 * Real.pi) z = 0) :
    z.im = 0 :=
  ccmCenteredDividedDifferenceOddGround_compactFourier_zero_im_eq_zero
    (truncConvParitySource_odd k N) (truncConvParityDiagonal_even heven N)
    hpsd hc hground hline hzero

/-! ## The compressed quadratic form -/

/-- The trigonometric polynomial attached to a centered parity coefficient vector. -/
def truncConvModePoly {N : ℕ} (v : CCMCenteredParityIndex N → ℂ) : ℝ → ℂ :=
  indexTrigPoly (ccmParityCenteredMode N) v

theorem truncConvParityPacket_apply {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (hk'c : Continuous k') (heven : ∀ u, k (-u) = k u) (N : ℕ) (mu : ℝ)
    (i j : CCMCenteredParityIndex N) :
    truncConvParityPacket k N mu i j
      = convMatrix k (ccmParityCenteredMode N i) (ccmParityCenteredMode N j)
        - (mu : ℂ) * (if i = j then 1 else 0) := by
  rw [truncConvParityPacket, ccmCenteredParityPacket, ccmScalarShift]
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  rw [ccmDividedDifferenceMatrix_truncConv hk hk'c heven]
  simp only [Complex.coe_algebraMap, Complex.ofReal_sub, Complex.ofReal_mul,
    convMatrix_ofReal_re heven]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

/-- **The compressed form is the truncated-convolution form.** -/
theorem truncConvParityPacket_form {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (hk'c : Continuous k') (heven : ∀ u, k (-u) = k u) {N : ℕ} (mu : ℝ)
    (v : CCMCenteredParityIndex N → ℂ) :
    star v ⬝ᵥ (truncConvParityPacket k N mu *ᵥ v)
      = (∫ x in (0 : ℝ)..1, (starRingEnd ℂ) (truncConvModePoly v x)
            * truncConv k (truncConvModePoly v) x)
        - (mu : ℂ) * ∫ x in (0 : ℝ)..1,
            (starRingEnd ℂ) (truncConvModePoly v x) * truncConvModePoly v x := by
  have hkc : Continuous k := continuous_iff_continuousAt.2 fun u => (hk u).continuousAt
  have hexpand : star v ⬝ᵥ (truncConvParityPacket k N mu *ᵥ v)
      = ∑ i, ∑ j, (starRingEnd ℂ) (v i) * truncConvParityPacket k N mu i j * v j := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hexpand]
  have hterm : ∀ i j : CCMCenteredParityIndex N,
      (starRingEnd ℂ) (v i) * truncConvParityPacket k N mu i j * v j
        = (starRingEnd ℂ) (v i)
            * convMatrix k (ccmParityCenteredMode N i) (ccmParityCenteredMode N j) * v j
          - (mu : ℂ) * ((if i = j then 1 else 0) * ((starRingEnd ℂ) (v i) * v j)) := by
    intro i j
    rw [truncConvParityPacket_apply hk hk'c heven]
    ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j]
  simp only [Finset.sum_sub_distrib, truncConvModePoly]
  have hminj : Function.Injective (ccmParityCenteredMode N) := by
    intro a b hab
    refine ccmParityCenteredClock_injective N ?_
    rw [ccmParityCenteredClock, ccmParityCenteredClock, hab]
  have hdiag : ∀ i : CCMCenteredParityIndex N,
      (∑ j, (mu : ℂ) * ((if i = j then 1 else 0) * ((starRingEnd ℂ) (v i) * v j)))
        = (mu : ℂ) * ((starRingEnd ℂ) (v i) * v i) := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [integral_indexTrigPoly_truncConv hkc (ccmParityCenteredMode N) v,
    integral_indexTrigPoly_normSq hminj v,
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hdiag i, ← Finset.mul_sum]

/-! ## Positive semidefiniteness from the quadratic form -/

theorem truncConvParityPacket_isHermitian {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (hk'c : Continuous k') (heven : ∀ u, k (-u) = k u) (N : ℕ) (mu : ℝ) :
    (truncConvParityPacket k N mu).IsHermitian := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.conjTranspose_apply, truncConvParityPacket_apply hk hk'c heven,
    truncConvParityPacket_apply hk hk'c heven]
  have hc : (starRingEnd ℂ) (convMatrix k (ccmParityCenteredMode N j) (ccmParityCenteredMode N i))
      = convMatrix k (ccmParityCenteredMode N i) (ccmParityCenteredMode N j) := by
    rw [convMatrix_conj, convMatrix_reflect heven,
      convMatrix_symm hk hk'c heven (ccmParityCenteredMode N j)]
  have hite : (starRingEnd ℂ) (if j = i then (1 : ℂ) else 0) = if i = j then (1 : ℂ) else 0 := by
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  rw [star_sub, star_mul', RCLike.star_def, hc, hite, Complex.conj_ofReal]

/-- **The compressed packet is positive semidefinite whenever the truncated-convolution form
dominates `mu` times the `L²` norm on the compression.** -/
theorem truncConvParityPacket_posSemidef {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (hk'c : Continuous k') (heven : ∀ u, k (-u) = k u) {N : ℕ} {mu : ℝ}
    (hform : ∀ v : CCMCenteredParityIndex N → ℂ,
      (mu : ℂ) * (∫ x in (0 : ℝ)..1,
          (starRingEnd ℂ) (truncConvModePoly v x) * truncConvModePoly v x)
        ≤ ∫ x in (0 : ℝ)..1,
            (starRingEnd ℂ) (truncConvModePoly v x) * truncConv k (truncConvModePoly v) x) :
    (truncConvParityPacket k N mu).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (truncConvParityPacket_isHermitian hk hk'c heven N mu) fun v => ?_
  rw [truncConvParityPacket_form hk hk'c heven mu v]
  exact sub_nonneg.2 (hform v)
/-- **The kernel of the compressed packet is exactly the set of minimizers of the
truncated-convolution form.** -/
theorem truncConvParityPacket_mulVec_eq_zero_iff {k k' : ℝ → ℝ}
    (hk : ∀ u, HasDerivAt k (k' u) u) (hk'c : Continuous k') (heven : ∀ u, k (-u) = k u)
    {N : ℕ} {mu : ℝ} (hpsd : (truncConvParityPacket k N mu).PosSemidef)
    (v : CCMCenteredParityIndex N → ℂ) :
    truncConvParityPacket k N mu *ᵥ v = 0
      ↔ (∫ x in (0 : ℝ)..1,
            (starRingEnd ℂ) (truncConvModePoly v x) * truncConv k (truncConvModePoly v) x)
          = (mu : ℂ) * ∫ x in (0 : ℝ)..1,
              (starRingEnd ℂ) (truncConvModePoly v x) * truncConvModePoly v x := by
  rw [← hpsd.dotProduct_mulVec_zero_iff v, truncConvParityPacket_form hk hk'c heven mu v,
    sub_eq_zero]

end

end RHTower
