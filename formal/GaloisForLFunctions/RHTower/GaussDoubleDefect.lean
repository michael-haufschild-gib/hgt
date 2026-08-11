import GaloisForLFunctions.RHTower.GaussConvolutionCoefficient
import GaloisForLFunctions.RHTower.GaussIteratedAmplitude
import GaloisForLFunctions.HTGeometry.HarmonicPowerConvolution
import GaloisForLFunctions.HTGeometry.FarBandPowerTail
import GaloisForLFunctions.HTGeometry.BandSplitVanishingSum

/-!
# The double-defect estimate of the principal step

The relative deviation of the principal step from the moving amplitude contains one term in which
a moving-translation defect is applied to the output of another: the vector

`Δ (B⁻² (Δ* b))`,  `Δ* = S* - T_δ`,  `Δ = S - T_{-δ}`,

with `b` the prime-scale amplitude.  Its `ℓ²` norm carries two ratio defects at convolution-offset
frequencies, so no single moving-translation estimate applies.

The estimate here is rate-free.  The squared norm is dominated by a lattice double sum whose
weight is the harmonic-convolution decay `(1+|j|)^{-3/2}` in each variable separately, and whose
defect factor is the product `‖ρ(j)‖²‖ρ(l)‖²`.  For `m ≥ 2` the fourth power of a sampled ratio
is controlled by the harmonic factor `K·I/|I+·|` — this is where `m ≥ 2` enters, through
`r⁴ ≤ 1 + r^{2m}` — so the product of two defects splits into a constant and two single
harmonic factors, never a product of two.  Dominated convergence with the far-band power tail
at exponent `3/2` closes the sum.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions Filter Topology
open scoped ENNReal

noncomputable section

/-! ## Lattice helpers -/

theorem natAbs_cast_eq_abs (x : ℤ) : ((x.natAbs : ℝ)) = |(x : ℝ)| := by
  rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]

theorem natAbs_sub_symm (a b : ℤ) : (a - b).natAbs = (b - a).natAbs := by
  omega

/-- The paired harmonic kernel is summable. -/
theorem summable_harmonicPairKernel (j : ℤ) :
    Summable (fun l : ℤ => 1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))) := by
  have h1 := summable_sq_harmonicKernel 1 j
  have h2 := summable_sq_harmonicKernel 1 0
  have h2' : Summable (fun l : ℤ => (1 / (1 + (l.natAbs : ℝ))) ^ 2) := by
    refine h2.congr fun l => ?_
    rw [sub_zero]
  have hdom : Summable (fun l : ℤ =>
      ((1 / (1 + ((l - j).natAbs : ℝ))) ^ 2 + (1 / (1 + (l.natAbs : ℝ))) ^ 2) / 2) :=
    (h1.add h2').div_const 2
  refine Summable.of_nonneg_of_le (fun l => by positivity) (fun l => ?_) hdom
  have ha : (0 : ℝ) < 1 + ((l - j).natAbs : ℝ) := by positivity
  have hb : (0 : ℝ) < 1 + (l.natAbs : ℝ) := by positivity
  have hkey : 1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))
      = (1 / (1 + ((l - j).natAbs : ℝ))) * (1 / (1 + (l.natAbs : ℝ))) := by
    rw [div_mul_div_comm, one_mul]
  rw [hkey]
  nlinarith [sq_nonneg (1 / (1 + ((l - j).natAbs : ℝ)) - 1 / (1 + (l.natAbs : ℝ)))]

/-- Uniform bound for the ratio defect at a fixed frequency. -/
theorem norm_gaussSampleRatioDefect_le_uniform {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) (i l : ℤ) :
    ‖gaussSampleRatioDefect k p l i‖
      ≤ 1 + gaussSampleValueBound hm k p / ‖gaussSampleValue k p i‖ := by
  have htri : ‖gaussSampleRatioDefect k p l i‖
      ≤ ‖gaussSampleValue k p (i + l) / gaussSampleValue k p i‖ + 1 := by
    rw [gaussSampleRatioDefect]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_gaussSampleRotation (m := m)]
  refine htri.trans ?_
  rw [norm_div]
  have hratio : ‖gaussSampleValue k p (i + l)‖ / ‖gaussSampleValue k p i‖
      ≤ gaussSampleValueBound hm k p / ‖gaussSampleValue k p i‖ := by
    rcases eq_or_ne ‖gaussSampleValue k p i‖ 0 with h0 | h0
    · rw [h0, div_zero, div_zero]
    · have hpos : 0 < ‖gaussSampleValue k p i‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      gcongr
      exact norm_gaussSampleValue_le hm k p (i + l)
  linarith [hratio]

/-- **Product cap for two ratio defects.**  For `m ≥ 2` the product of two squared defects splits
into a constant plus two single harmonic factors; no product of harmonic factors survives. -/
theorem norm_gaussSampleRatioDefect_sq_mul_sq_le {m : ℕ} (hm2 : 2 ≤ m) (k : Fin m)
    (p : Nat.Primes) {K : ℝ}
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    (I : ℕ) (j l : ℤ) :
    ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2 * ‖gaussSampleRatioDefect k p l (I : ℤ)‖ ^ 2
      ≤ 24 + 6 * K * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ) +
          6 * K * (I : ℝ) / (((I : ℤ) + l).natAbs : ℝ) := by
  have hm1 : 1 ≤ m := by omega
  set Rj : ℝ := ‖gaussSampleValue k p ((I : ℤ) + j)‖ / ‖gaussSampleValue k p (I : ℤ)‖ with hRj
  set Rl : ℝ := ‖gaussSampleValue k p ((I : ℤ) + l)‖ / ‖gaussSampleValue k p (I : ℤ)‖ with hRl
  have hRj0 : 0 ≤ Rj := by positivity
  have hRl0 : 0 ≤ Rl := by positivity
  have htri : ∀ x : ℤ, ‖gaussSampleRatioDefect k p x (I : ℤ)‖
      ≤ ‖gaussSampleValue k p ((I : ℤ) + x)‖ / ‖gaussSampleValue k p (I : ℤ)‖ + 1 := by
    intro x
    rw [gaussSampleRatioDefect]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div, norm_gaussSampleRotation (m := m)]
  have hsqj : ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2 ≤ 2 * Rj ^ 2 + 2 := by
    have h := htri j
    rw [← hRj] at h
    nlinarith [sq_nonneg (Rj - 1), norm_nonneg (gaussSampleRatioDefect k p j (I : ℤ))]
  have hsql : ‖gaussSampleRatioDefect k p l (I : ℤ)‖ ^ 2 ≤ 2 * Rl ^ 2 + 2 := by
    have h := htri l
    rw [← hRl] at h
    nlinarith [sq_nonneg (Rl - 1), norm_nonneg (gaussSampleRatioDefect k p l (I : ℤ))]
  have hfour : ∀ {R : ℝ}, 0 ≤ R → R ^ 4 ≤ 1 + R ^ (2 * m) := by
    intro R hR
    rcases le_or_gt R 1 with h | h
    · have h1 : R ^ 4 ≤ 1 := pow_le_one₀ hR h
      have h2 : (0 : ℝ) ≤ R ^ (2 * m) := by positivity
      linarith
    · have h1 : R ^ 4 ≤ R ^ (2 * m) := pow_le_pow_right₀ h.le (by omega)
      linarith
  have hcapj : Rj ^ (2 * m) ≤ K * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ) :=
    norm_gaussSampleRatio_pow_le hm1 k p hKb I j
  have hcapl : Rl ^ (2 * m) ≤ K * (I : ℝ) / (((I : ℤ) + l).natAbs : ℝ) :=
    norm_gaussSampleRatio_pow_le hm1 k p hKb I l
  have hj4 : Rj ^ 4 ≤ 1 + K * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ) :=
    le_trans (hfour hRj0) (by linarith)
  have hl4 : Rl ^ 4 ≤ 1 + K * (I : ℝ) / (((I : ℤ) + l).natAbs : ℝ) :=
    le_trans (hfour hRl0) (by linarith)
  have hj2 : Rj ^ 2 ≤ 1 + Rj ^ 4 := by nlinarith [sq_nonneg (Rj ^ 2 - 1)]
  have hl2 : Rl ^ 2 ≤ 1 + Rl ^ 4 := by nlinarith [sq_nonneg (Rl ^ 2 - 1)]
  have hprod : Rj ^ 2 * Rl ^ 2 ≤ (Rj ^ 4 + Rl ^ 4) / 2 := by
    nlinarith [sq_nonneg (Rj ^ 2 - Rl ^ 2)]
  have hnnj : (0 : ℝ) ≤ ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2 := by positivity
  have hnnl : (0 : ℝ) ≤ ‖gaussSampleRatioDefect k p l (I : ℤ)‖ ^ 2 := by positivity
  calc ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2 *
        ‖gaussSampleRatioDefect k p l (I : ℤ)‖ ^ 2
      ≤ (2 * Rj ^ 2 + 2) * (2 * Rl ^ 2 + 2) := by
        exact mul_le_mul hsqj hsql hnnl (by nlinarith)
    _ = 4 * (Rj ^ 2 * Rl ^ 2) + 4 * Rj ^ 2 + 4 * Rl ^ 2 + 4 := by ring
    _ ≤ 4 * ((Rj ^ 4 + Rl ^ 4) / 2) + 4 * (1 + Rj ^ 4) + 4 * (1 + Rl ^ 4) + 4 := by
        have h1 := mul_le_mul_of_nonneg_left hprod (by norm_num : (0:ℝ) ≤ 4)
        have h2 := mul_le_mul_of_nonneg_left hj2 (by norm_num : (0:ℝ) ≤ 4)
        have h3 := mul_le_mul_of_nonneg_left hl2 (by norm_num : (0:ℝ) ≤ 4)
        linarith
    _ = 6 * Rj ^ 4 + 6 * Rl ^ 4 + 12 := by ring
    _ ≤ 6 * (1 + K * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ)) +
          6 * (1 + K * (I : ℝ) / (((I : ℤ) + l).natAbs : ℝ)) + 12 := by
        have h1 := mul_le_mul_of_nonneg_left hj4 (by norm_num : (0:ℝ) ≤ 6)
        have h2 := mul_le_mul_of_nonneg_left hl4 (by norm_num : (0:ℝ) ≤ 6)
        linarith
    _ = 24 + 6 * K * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ) +
          6 * K * (I : ℝ) / (((I : ℤ) + l).natAbs : ℝ) := by ring

/-- Near/far split of a harmonic factor: it is uniformly at most `2` off the far band. -/
theorem harmonic_factor_near_far {K' : ℝ} (hK' : 0 ≤ K') (I : ℕ) (x : ℤ) :
    K' * (I : ℝ) / (((I : ℤ) + x).natAbs : ℝ)
      ≤ 2 * K' + (if I < 2 * x.natAbs ∧ ((I : ℤ) + x).natAbs ≠ 0 then
          K' * (I : ℝ) / (((I : ℤ) + x).natAbs : ℝ) else 0) := by
  by_cases hcase : I < 2 * x.natAbs ∧ ((I : ℤ) + x).natAbs ≠ 0
  · rw [if_pos hcase]
    have : (0 : ℝ) ≤ K' * (I : ℝ) / (((I : ℤ) + x).natAbs : ℝ) := by positivity
    linarith
  · rw [if_neg hcase, add_zero]
    by_cases h0 : ((I : ℤ) + x).natAbs = 0
    · rw [h0, Nat.cast_zero, div_zero]
      positivity
    · have hnear : 2 * x.natAbs ≤ I := by
        rcases Nat.lt_or_ge I (2 * x.natAbs) with h | h
        · exact absurd ⟨h, h0⟩ hcase
        · exact h
      have hI2 : I ≤ 2 * ((I : ℤ) + x).natAbs := by omega
      have hnpos : (0 : ℝ) < (((I : ℤ) + x).natAbs : ℝ) := by
        have : 0 < ((I : ℤ) + x).natAbs := Nat.pos_of_ne_zero h0
        exact_mod_cast this
      rw [div_le_iff₀ hnpos]
      have hI2R : (I : ℝ) ≤ 2 * ((((I : ℤ) + x).natAbs : ℝ)) := by exact_mod_cast hI2
      nlinarith

/-! ## The double-defect vector and its lattice bound -/

/-- The double-defect vector: the unconjugated moving-translation defect applied to the
reciprocal-square image of the conjugate defect of the prime-scale amplitude. -/
def gaussDoubleDefectVector {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  gaussShiftedBlockDiag hm k p i
      (gaussPrimeScaleInvSqBlock hp
        (gaussShiftedBlockOf hm k p i (gaussPrimeScaleBlock hp (fourierLp 2 0)) -
          gaussRotationBlock ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
            (gaussPrimeScaleBlock hp (fourierLp 2 0)))) -
    gaussRotationBlockInv ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
      (gaussPrimeScaleInvSqBlock hp
        (gaussShiftedBlockOf hm k p i (gaussPrimeScaleBlock hp (fourierLp 2 0)) -
          gaussRotationBlock ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
            (gaussPrimeScaleBlock hp (fourierLp 2 0))))

/-- The dominating lattice double sum of the double defect. -/
def gaussDoubleDefectBound {m : ℕ} (k : Fin m) (p : Nat.Primes) (i : ℤ) : ℝ≥0∞ :=
  ∑' jl : ℤ × ℤ, ENNReal.ofReal
    (128 * (p : ℝ) ^ 2 * 2 ^ ((3 : ℝ) / 4) *
        (∑' x : ℤ, intPowWeight (5 / 4) x).toReal *
      (1 / (1 + (jl.1.natAbs : ℝ)) ^ ((3 : ℝ) / 4)) *
      (1 / ((1 + ((jl.2 - jl.1).natAbs : ℝ)) * (1 + (jl.2.natAbs : ℝ)))) *
      (‖gaussSampleRatioDefect k p jl.1 i‖ ^ 2 * ‖gaussSampleRatioDefect k p jl.2 i‖ ^ 2))

/-- The lattice bound is even in the frequency. -/
theorem gaussDoubleDefectBound_neg {m : ℕ} (k : Fin m) (p : Nat.Primes) (i : ℤ) :
    gaussDoubleDefectBound k p (-i) = gaussDoubleDefectBound k p i := by
  rw [gaussDoubleDefectBound, gaussDoubleDefectBound,
    ← ((Equiv.neg ℤ).prodCongr (Equiv.neg ℤ)).tsum_eq]
  refine tsum_congr fun jl => ?_
  obtain ⟨j, l⟩ := jl
  have hρ : ∀ x : ℤ, ‖gaussSampleRatioDefect k p (-x) (-i)‖
      = ‖gaussSampleRatioDefect k p x i‖ := by
    intro x
    rw [gaussSampleRatioDefect_neg, RCLike.norm_conj]
  have happly : ((Equiv.neg ℤ).prodCongr (Equiv.neg ℤ)) (j, l) = (-j, -l) := by
    simp [Equiv.prodCongr_apply, Equiv.neg_apply]
  rw [happly]
  congr 1
  rw [hρ j, hρ l]
  have h1 : ((-j : ℤ).natAbs : ℝ) = (j.natAbs : ℝ) := by rw [Int.natAbs_neg]
  have h2 : (((-l : ℤ) - (-j : ℤ)).natAbs : ℝ) = ((l - j).natAbs : ℝ) := by
    have : ((-l : ℤ) - (-j : ℤ)).natAbs = (l - j).natAbs := by omega
    rw [this]
  have h3 : ((-l : ℤ).natAbs : ℝ) = (l.natAbs : ℝ) := by rw [Int.natAbs_neg]
  rw [h1, h2, h3]

theorem gaussDoubleDefectBound_natAbs {m : ℕ} (k : Fin m) (p : Nat.Primes) (i : ℤ) :
    gaussDoubleDefectBound k p ((i.natAbs : ℤ)) = gaussDoubleDefectBound k p i := by
  rcases Int.natAbs_eq i with h | h
  · rw [← h]
  · have hb := gaussDoubleDefectBound_neg k p ((i.natAbs : ℤ))
    rw [← h] at hb
    exact hb.symm

/-! ## The master inequality -/

/-- **Master bound.**  The squared norm of the double-defect vector is dominated by the lattice
double sum. -/
theorem norm_gaussDoubleDefectVector_sq_le {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    ENNReal.ofReal (‖gaussDoubleDefectVector hm k p hp i‖ ^ (2 : ℝ))
      ≤ gaussDoubleDefectBound k p i := by
  classical
  set δ : AddCircle (1 : ℝ) := ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ)) with hδ
  set b : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussPrimeScaleBlock hp (fourierLp 2 0) with hbdef
  set w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussShiftedBlockOf hm k p i b - gaussRotationBlock δ b with hwdef
  set v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussPrimeScaleInvSqBlock hp w with hvdef
  set DD : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussDoubleDefectVector hm k p hp i with hDDdef
  set Wr : ℝ := (∑' x : ℤ, intPowWeight (5 / 4) x).toReal with hWr
  have hWrnn : 0 ≤ Wr := ENNReal.toReal_nonneg
  have hWtop : (∑' x : ℤ, intPowWeight (5 / 4) x) ≠ ⊤ :=
    tsum_intPowWeight_ne_top (by norm_num)
  have hWof : ENNReal.ofReal Wr = ∑' x : ℤ, intPowWeight (5 / 4) x :=
    ENNReal.ofReal_toReal hWtop
  -- coefficients of the double-defect vector
  have hDDcoeff : ∀ j : ℤ,
      ‖fourierCoeff ((DD : AddCircle (1 : ℝ) → ℂ)) j‖
        = ‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) j‖ *
          ‖gaussSampleRatioDefect k p j i‖ := by
    intro j
    have hsub : fourierCoeff ((DD : AddCircle (1 : ℝ) → ℂ)) j
        = fourierCoeff ((gaussShiftedBlockDiag hm k p i v : AddCircle (1 : ℝ) → ℂ)) j -
          fourierCoeff ((gaussRotationBlockInv δ v : AddCircle (1 : ℝ) → ℂ)) j := by
      rw [← fourierBasis_repr, ← fourierBasis_repr, ← fourierBasis_repr, hDDdef,
        gaussDoubleDefectVector, ← hδ, ← hbdef, ← hwdef, ← hvdef, map_sub]
      rfl
    rw [hsub, hδ, norm_fourierCoeff_shiftedBlockDiag_sub_rotationInv hm k p]
  -- coefficients of the intermediate vector
  have hwcoeff : ∀ l : ℤ,
      ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖
        ≤ 4 * (p : ℝ) / (1 + (l.natAbs : ℝ)) * ‖gaussSampleRatioDefect k p l i‖ := by
    intro l
    have hsub : fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l
        = fourierCoeff ((gaussShiftedBlockOf hm k p i b : AddCircle (1 : ℝ) → ℂ)) l -
          fourierCoeff ((gaussRotationBlock δ b : AddCircle (1 : ℝ) → ℂ)) l := by
      rw [← fourierBasis_repr, ← fourierBasis_repr, ← fourierBasis_repr, hwdef, map_sub]
      rfl
    have hval : ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖
        = ‖fourierCoeff ((b : AddCircle (1 : ℝ) → ℂ)) l‖ *
          ‖gaussSampleRatioDefect k p l i‖ := by
      rw [hsub, hδ, norm_fourierCoeff_shiftedBlockOf_sub_rotation hm k p]
    rw [hval]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have h1pow : (gaussMovingAmplitudeBlock hp ((0 : ℝ) : AddCircle (1 : ℝ)) ^ 0)
        (fourierLp 2 0) = (fourierLp 2 0 : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) := by
      rw [pow_zero]
      rfl
    have hbb0 := norm_fourierCoeff_gaussPrimeScaleBlock_amplitudePow hp
      (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) < 1) 0 l
    rw [h1pow, zero_add, pow_one] at hbb0
    exact hbb0
  -- uniform bound on the defect at this frequency
  set Rmax : ℝ := 1 + gaussSampleValueBound hm k p / ‖gaussSampleValue k p i‖ with hRmax
  have hRmax0 : 0 ≤ Rmax := by
    have h1 : 0 ≤ gaussSampleValueBound hm k p := gaussSampleValueBound_nonneg hm k p
    have h2 : 0 ≤ gaussSampleValueBound hm k p / ‖gaussSampleValue k p i‖ := by positivity
    simp only [hRmax]
    linarith
  have hρuni : ∀ l : ℤ, ‖gaussSampleRatioDefect k p l i‖ ≤ Rmax :=
    fun l => norm_gaussSampleRatioDefect_le_uniform hm k p i l
  -- the convolution majorant of `v`
  have hgnn : ∀ j l : ℤ, (0 : ℝ) ≤
      8 * (p : ℝ) * (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))) *
        ‖gaussSampleRatioDefect k p l i‖ := by
    intro j l
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    positivity
  have hgsummable : ∀ j : ℤ, Summable (fun l : ℤ =>
      8 * (p : ℝ) * (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))) *
        ‖gaussSampleRatioDefect k p l i‖) := by
    intro j
    have hmaj : Summable (fun l : ℤ =>
        (8 * (p : ℝ) * Rmax) * (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ))))) :=
      (summable_harmonicPairKernel j).mul_left _
    refine Summable.of_nonneg_of_le (fun l => hgnn j l) (fun l => ?_) hmaj
    have hker : (0 : ℝ) ≤ 1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ))) := by
      positivity
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    calc 8 * (p : ℝ) * (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))) *
          ‖gaussSampleRatioDefect k p l i‖
        ≤ 8 * (p : ℝ) * (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))) * Rmax := by
          refine mul_le_mul_of_nonneg_left (hρuni l) ?_
          positivity
      _ = (8 * (p : ℝ) * Rmax) *
            (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))) := by ring
  have hvcoeff : ∀ j : ℤ,
      ‖fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) j‖
        ≤ ∑' l : ℤ, 8 * (p : ℝ) *
            (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))) *
            ‖gaussSampleRatioDefect k p l i‖ := by
    intro j
    have hconv := norm_fourierCoeff_gaussPrimeScaleInvSqBlock_le hp w j
    rw [← hvdef] at hconv
    refine hconv.trans ?_
    have hsum1 : Summable (fun l : ℤ => 2 / (1 + ((l - j).natAbs : ℝ)) *
        ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖) :=
      summable_harmonicKernel_mul_fourierCoeff
        (κ := fun x => 2 / (1 + (x.natAbs : ℝ))) (A := 2)
        (fun x => by positivity) (fun x => le_refl _) w j
    refine hsum1.tsum_le_tsum (fun l => ?_) (hgsummable j)
    have h1 := hwcoeff l
    have hker : (0 : ℝ) ≤ 2 / (1 + ((l - j).natAbs : ℝ)) := by positivity
    calc 2 / (1 + ((l - j).natAbs : ℝ)) * ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖
        ≤ 2 / (1 + ((l - j).natAbs : ℝ)) *
            (4 * (p : ℝ) / (1 + (l.natAbs : ℝ)) * ‖gaussSampleRatioDefect k p l i‖) :=
          mul_le_mul_of_nonneg_left h1 hker
      _ = 8 * (p : ℝ) * (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))) *
            ‖gaussSampleRatioDefect k p l i‖ := by
          field_simp
          ring
  -- the ENNReal expansion of the inner majorant
  have hVof : ∀ j : ℤ,
      ENNReal.ofReal (∑' l : ℤ, 8 * (p : ℝ) *
          (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))) *
          ‖gaussSampleRatioDefect k p l i‖)
        = ∑' l : ℤ, ENNReal.ofReal (8 * (p : ℝ) *
            (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))) *
            ‖gaussSampleRatioDefect k p l i‖) :=
    fun j => ENNReal.ofReal_tsum_of_nonneg (hgnn j) (hgsummable j)
  -- the kernel-only sum collapses by the harmonic power convolution
  have hkernelsum : ∀ j : ℤ,
      (∑' l : ℤ, ENNReal.ofReal (8 * (p : ℝ) *
          (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ))))))
        ≤ ENNReal.ofReal (8 * (p : ℝ) * (2 ^ ((3:ℝ)/4) / (1 + (j.natAbs : ℝ)) ^ ((3:ℝ)/4)) *
            (2 * Wr)) := by
    intro j
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hconv := tsum_harmonicPowConv_le (j := j) (β := 1) (γ := (3:ℝ)/4)
      (le_refl 1) (by norm_num) (by norm_num)
    have hcongr : ∀ l : ℤ,
        ENNReal.ofReal (8 * (p : ℝ) *
          (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))))
        = ENNReal.ofReal (8 * (p : ℝ)) * ENNReal.ofReal
            (1 / ((1 + |(l : ℝ)|) ^ (1:ℝ) * (1 + |((j - l : ℤ) : ℝ)|))) := by
      intro l
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.rpow_one, natAbs_sub_symm l j, natAbs_cast_eq_abs (j - l),
        natAbs_cast_eq_abs l]
      ring
    calc (∑' l : ℤ, ENNReal.ofReal (8 * (p : ℝ) *
          (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ))))))
        = ENNReal.ofReal (8 * (p : ℝ)) * ∑' l : ℤ, ENNReal.ofReal
            (1 / ((1 + |(l : ℝ)|) ^ (1:ℝ) * (1 + |((j - l : ℤ) : ℝ)|))) := by
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr hcongr
      _ ≤ ENNReal.ofReal (8 * (p : ℝ)) *
            (ENNReal.ofReal (2 ^ ((3:ℝ)/4) / (1 + |(j : ℝ)|) ^ ((3:ℝ)/4)) *
              (2 * ∑' x : ℤ, intPowWeight (1 + 1 - (3:ℝ)/4) x)) := by
          refine mul_le_mul' le_rfl ?_
          exact hconv
      _ = ENNReal.ofReal (8 * (p : ℝ) * (2 ^ ((3:ℝ)/4) / (1 + (j.natAbs : ℝ)) ^ ((3:ℝ)/4)) *
            (2 * Wr)) := by
          have hexp : (1 : ℝ) + 1 - (3:ℝ)/4 = 5/4 := by norm_num
          rw [hexp]
          have h2W : (2 : ℝ≥0∞) * (∑' x : ℤ, intPowWeight (5/4) x)
              = ENNReal.ofReal (2 * Wr) := by
            rw [← hWof, ← ENNReal.ofReal_ofNat 2,
              ← ENNReal.ofReal_mul (by norm_num)]
          rw [h2W, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by
            have h2 : (0:ℝ) < (2:ℝ) ^ ((3:ℝ)/4) := Real.rpow_pos_of_pos (by norm_num) _
            have hZ : (0:ℝ) < (1 + |(j : ℝ)|) ^ ((3:ℝ)/4) :=
              Real.rpow_pos_of_pos (by have := abs_nonneg ((j:ℝ)); linarith) _
            positivity)]
          rw [natAbs_cast_eq_abs j]
          congr 1
          ring
  -- per-frequency master step
  have hperj : ∀ j : ℤ,
      ENNReal.ofReal (‖fourierCoeff ((DD : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2:ℝ))
        ≤ ∑' l : ℤ, ENNReal.ofReal
            (128 * (p : ℝ) ^ 2 * 2 ^ ((3:ℝ)/4) * Wr *
              (1 / (1 + (j.natAbs : ℝ)) ^ ((3:ℝ)/4)) *
              (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))) *
              (‖gaussSampleRatioDefect k p j i‖ ^ 2 *
                ‖gaussSampleRatioDefect k p l i‖ ^ 2)) := by
    intro j
    set V : ℝ := ∑' l : ℤ, 8 * (p : ℝ) *
        (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))) *
        ‖gaussSampleRatioDefect k p l i‖ with hV
    have hVnn : 0 ≤ V := tsum_nonneg (hgnn j)
    have hcoeffbound : ‖fourierCoeff ((DD : AddCircle (1 : ℝ) → ℂ)) j‖
        ≤ V * ‖gaussSampleRatioDefect k p j i‖ := by
      rw [hDDcoeff j]
      exact mul_le_mul_of_nonneg_right (hvcoeff j) (norm_nonneg _)
    have hsq : ‖fourierCoeff ((DD : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2:ℝ)
        ≤ V ^ 2 * ‖gaussSampleRatioDefect k p j i‖ ^ 2 := by
      have h1 : ‖fourierCoeff ((DD : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2:ℝ)
          = ‖fourierCoeff ((DD : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2:ℕ) := by
        rw [← Real.rpow_natCast ‖fourierCoeff ((DD : AddCircle (1 : ℝ) → ℂ)) j‖ 2]
        norm_num
      rw [h1]
      calc ‖fourierCoeff ((DD : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2:ℕ)
          ≤ (V * ‖gaussSampleRatioDefect k p j i‖) ^ (2:ℕ) :=
            pow_le_pow_left₀ (norm_nonneg _) hcoeffbound 2
        _ = V ^ 2 * ‖gaussSampleRatioDefect k p j i‖ ^ 2 := by ring
    refine le_trans (ENNReal.ofReal_le_ofReal hsq) ?_
    -- expand `V²` as a double sum and symmetrize
    set g : ℤ → ℝ := fun l => 8 * (p : ℝ) *
        (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))) *
        ‖gaussSampleRatioDefect k p l i‖ with hg
    set gker : ℤ → ℝ := fun l => 8 * (p : ℝ) *
        (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))) with hgker
    have hgkernn : ∀ l, 0 ≤ gker l := by
      intro l
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      simp only [hgker]
      positivity
    have hVsq : ENNReal.ofReal (V ^ 2 * ‖gaussSampleRatioDefect k p j i‖ ^ 2)
        = ENNReal.ofReal (‖gaussSampleRatioDefect k p j i‖ ^ 2) *
          ((∑' l : ℤ, ENNReal.ofReal (g l)) * ∑' l : ℤ, ENNReal.ofReal (g l)) := by
      rw [← hVof j, ← hV]
      rw [← ENNReal.ofReal_mul hVnn, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    rw [hVsq]
    -- collapse the square by AM–GM inside the double sum
    have hsquare : (∑' l : ℤ, ENNReal.ofReal (g l)) * (∑' l : ℤ, ENNReal.ofReal (g l))
        ≤ (∑' l : ℤ, ENNReal.ofReal (gker l)) *
          ∑' l : ℤ, ENNReal.ofReal (gker l * ‖gaussSampleRatioDefect k p l i‖ ^ 2) := by
      set A : ℝ≥0∞ := ∑' l : ℤ, ENNReal.ofReal (gker l) with hA
      set B : ℝ≥0∞ := ∑' l : ℤ,
        ENNReal.ofReal (gker l * ‖gaussSampleRatioDefect k p l i‖ ^ 2) with hB
      have hexpand : (∑' l : ℤ, ENNReal.ofReal (g l)) * (∑' l : ℤ, ENNReal.ofReal (g l))
          = ∑' l : ℤ, ∑' l' : ℤ, ENNReal.ofReal (g l) * ENNReal.ofReal (g l') := by
        have hinner : ∀ l : ℤ,
            (∑' l' : ℤ, ENNReal.ofReal (g l) * ENNReal.ofReal (g l'))
              = ENNReal.ofReal (g l) * ∑' l' : ℤ, ENNReal.ofReal (g l') :=
          fun l => ENNReal.tsum_mul_left
        rw [tsum_congr hinner, ENNReal.tsum_mul_right]
      rw [hexpand]
      have hBA : (∑' l : ℤ, ∑' l' : ℤ,
            ENNReal.ofReal (gker l * ‖gaussSampleRatioDefect k p l i‖ ^ 2) *
              ENNReal.ofReal (gker l')) = B * A := by
        have hinner : ∀ l : ℤ,
            (∑' l' : ℤ, ENNReal.ofReal (gker l * ‖gaussSampleRatioDefect k p l i‖ ^ 2) *
              ENNReal.ofReal (gker l'))
              = ENNReal.ofReal (gker l * ‖gaussSampleRatioDefect k p l i‖ ^ 2) * A :=
          fun l => ENNReal.tsum_mul_left
        rw [tsum_congr hinner, ENNReal.tsum_mul_right]
      have hAB : (∑' l : ℤ, ∑' l' : ℤ,
            ENNReal.ofReal (gker l' * ‖gaussSampleRatioDefect k p l' i‖ ^ 2) *
              ENNReal.ofReal (gker l)) = A * B := by
        have hinner : ∀ l : ℤ,
            (∑' l' : ℤ, ENNReal.ofReal (gker l' * ‖gaussSampleRatioDefect k p l' i‖ ^ 2) *
              ENNReal.ofReal (gker l))
              = B * ENNReal.ofReal (gker l) :=
          fun l => ENNReal.tsum_mul_right
        rw [tsum_congr hinner, ENNReal.tsum_mul_left, mul_comm]
      have hhalf : ∀ l l' : ℤ, ENNReal.ofReal (g l) * ENNReal.ofReal (g l')
          ≤ ENNReal.ofReal (2⁻¹) *
              (ENNReal.ofReal (gker l * ‖gaussSampleRatioDefect k p l i‖ ^ 2) *
                  ENNReal.ofReal (gker l') +
                ENNReal.ofReal (gker l' * ‖gaussSampleRatioDefect k p l' i‖ ^ 2) *
                  ENNReal.ofReal (gker l)) := by
        intro l l'
        rw [← ENNReal.ofReal_mul (by
            have := hgkernn l
            have := norm_nonneg (gaussSampleRatioDefect k p l i)
            simp only [hg]
            positivity),
          ← ENNReal.ofReal_mul (by
            have := hgkernn l
            positivity),
          ← ENNReal.ofReal_mul (by
            have := hgkernn l'
            positivity),
          ← ENNReal.ofReal_add (by
            have h1 := hgkernn l
            have h2 := hgkernn l'
            positivity) (by
            have h1 := hgkernn l
            have h2 := hgkernn l'
            positivity),
          ← ENNReal.ofReal_mul (by norm_num)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := hgkernn l
        have h2 := hgkernn l'
        have hgl : g l = gker l * ‖gaussSampleRatioDefect k p l i‖ := by
          simp only [hg, hgker]
        have hgl' : g l' = gker l' * ‖gaussSampleRatioDefect k p l' i‖ := by
          simp only [hg, hgker]
        rw [hgl, hgl']
        have hAMGM : ‖gaussSampleRatioDefect k p l i‖ * ‖gaussSampleRatioDefect k p l' i‖
            ≤ (‖gaussSampleRatioDefect k p l i‖ ^ 2 +
                ‖gaussSampleRatioDefect k p l' i‖ ^ 2) / 2 := by
          nlinarith [sq_nonneg (‖gaussSampleRatioDefect k p l i‖ -
            ‖gaussSampleRatioDefect k p l' i‖)]
        have hker2 : 0 ≤ gker l * gker l' := mul_nonneg h1 h2
        nlinarith [mul_le_mul_of_nonneg_left hAMGM hker2]
      calc ∑' l : ℤ, ∑' l' : ℤ, ENNReal.ofReal (g l) * ENNReal.ofReal (g l')
          ≤ ∑' l : ℤ, ∑' l' : ℤ, ENNReal.ofReal (2⁻¹) *
              (ENNReal.ofReal (gker l * ‖gaussSampleRatioDefect k p l i‖ ^ 2) *
                  ENNReal.ofReal (gker l') +
                ENNReal.ofReal (gker l' * ‖gaussSampleRatioDefect k p l' i‖ ^ 2) *
                  ENNReal.ofReal (gker l)) := by
            refine ENNReal.tsum_le_tsum fun l => ENNReal.tsum_le_tsum fun l' => hhalf l l'
        _ = ENNReal.ofReal (2⁻¹) *
              ((∑' l : ℤ, ∑' l' : ℤ,
                  ENNReal.ofReal (gker l * ‖gaussSampleRatioDefect k p l i‖ ^ 2) *
                    ENNReal.ofReal (gker l')) +
                ∑' l : ℤ, ∑' l' : ℤ,
                  ENNReal.ofReal (gker l' * ‖gaussSampleRatioDefect k p l' i‖ ^ 2) *
                    ENNReal.ofReal (gker l)) := by
            have hpull : ∀ l : ℤ,
                (∑' l' : ℤ, ENNReal.ofReal (2⁻¹) *
                  (ENNReal.ofReal (gker l * ‖gaussSampleRatioDefect k p l i‖ ^ 2) *
                      ENNReal.ofReal (gker l') +
                    ENNReal.ofReal (gker l' * ‖gaussSampleRatioDefect k p l' i‖ ^ 2) *
                      ENNReal.ofReal (gker l)))
                  = ENNReal.ofReal (2⁻¹) *
                    ((∑' l' : ℤ,
                        ENNReal.ofReal (gker l * ‖gaussSampleRatioDefect k p l i‖ ^ 2) *
                          ENNReal.ofReal (gker l')) +
                      ∑' l' : ℤ,
                        ENNReal.ofReal (gker l' * ‖gaussSampleRatioDefect k p l' i‖ ^ 2) *
                          ENNReal.ofReal (gker l)) := by
              intro l
              rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
            rw [tsum_congr hpull, ENNReal.tsum_mul_left, ENNReal.tsum_add]
        _ = ENNReal.ofReal (2⁻¹) * (B * A + A * B) := by rw [hBA, hAB]
        _ = A * B := by
            have hcomm : B * A + A * B = 2 * (A * B) := by
              rw [mul_comm B A, two_mul]
            rw [hcomm, ← mul_assoc]
            have h12 : ENNReal.ofReal (2⁻¹) * 2 = 1 := by
              rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
              norm_num
            rw [h12, one_mul]
    calc ENNReal.ofReal (‖gaussSampleRatioDefect k p j i‖ ^ 2) *
          ((∑' l : ℤ, ENNReal.ofReal (g l)) * ∑' l : ℤ, ENNReal.ofReal (g l))
        ≤ ENNReal.ofReal (‖gaussSampleRatioDefect k p j i‖ ^ 2) *
            ((∑' l : ℤ, ENNReal.ofReal (gker l)) *
              ∑' l : ℤ, ENNReal.ofReal (gker l * ‖gaussSampleRatioDefect k p l i‖ ^ 2)) :=
          mul_le_mul' le_rfl hsquare
      _ ≤ ENNReal.ofReal (‖gaussSampleRatioDefect k p j i‖ ^ 2) *
            (ENNReal.ofReal (8 * (p : ℝ) *
                (2 ^ ((3:ℝ)/4) / (1 + (j.natAbs : ℝ)) ^ ((3:ℝ)/4)) * (2 * Wr)) *
              ∑' l : ℤ, ENNReal.ofReal (gker l * ‖gaussSampleRatioDefect k p l i‖ ^ 2)) := by
          refine mul_le_mul' le_rfl (mul_le_mul' ?_ le_rfl)
          exact hkernelsum j
      _ = ∑' l : ℤ, ENNReal.ofReal (‖gaussSampleRatioDefect k p j i‖ ^ 2) *
            ENNReal.ofReal (8 * (p : ℝ) *
              (2 ^ ((3:ℝ)/4) / (1 + (j.natAbs : ℝ)) ^ ((3:ℝ)/4)) * (2 * Wr)) *
            ENNReal.ofReal (gker l * ‖gaussSampleRatioDefect k p l i‖ ^ 2) := by
          rw [← mul_assoc, ← ENNReal.tsum_mul_left]
      _ ≤ ∑' l : ℤ, ENNReal.ofReal
            (128 * (p : ℝ) ^ 2 * 2 ^ ((3:ℝ)/4) * Wr *
              (1 / (1 + (j.natAbs : ℝ)) ^ ((3:ℝ)/4)) *
              (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))) *
              (‖gaussSampleRatioDefect k p j i‖ ^ 2 *
                ‖gaussSampleRatioDefect k p l i‖ ^ 2)) := by
          refine ENNReal.tsum_le_tsum fun l => ?_
          have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
          have hpj : (0:ℝ) < (1 + (j.natAbs : ℝ)) ^ ((3:ℝ)/4) :=
            Real.rpow_pos_of_pos (by positivity) _
          have h2r : (0:ℝ) < (2:ℝ) ^ ((3:ℝ)/4) := Real.rpow_pos_of_pos (by norm_num) _
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by
            have := hgkernn j
            positivity)]
          refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
          simp only [hgker]
          field_simp
          ring
    -- (the calc target matches the goal)
  -- assemble over `j`
  have hsummable : Summable (fun j : ℤ =>
      ‖fourierCoeff ((DD : AddCircle (1 : ℝ) → ℂ)) j‖ ^ (2:ℝ)) := by
    have hmem := lp.memℓp ((fourierBasis (T := (1 : ℝ))).repr DD)
    have hs := hmem.summable (p := 2) (by norm_num)
    simp only [ENNReal.toReal_ofNat] at hs
    refine hs.congr fun j => ?_
    rw [fourierBasis_repr]
  rw [norm_sq_eq_tsum_fourierCoeff DD,
    ENNReal.ofReal_tsum_of_nonneg (fun j => Real.rpow_nonneg (norm_nonneg _) _) hsummable]
  rw [gaussDoubleDefectBound, ENNReal.tsum_prod']
  exact ENNReal.tsum_le_tsum hperj

/-! ## Vanishing of the lattice bound -/

/-- The pair kernel collapses to the harmonic-power convolution decay. -/
theorem tsum_ofReal_pairKernel_le (j : ℤ) :
    (∑' l : ℤ, ENNReal.ofReal
        (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))))
      ≤ ENNReal.ofReal (2 ^ ((3:ℝ)/4) * (1 / (1 + (j.natAbs : ℝ)) ^ ((3:ℝ)/4)) *
          (2 * (∑' x : ℤ, intPowWeight (5 / 4) x).toReal)) := by
  have hWtop : (∑' x : ℤ, intPowWeight (5 / 4) x) ≠ ⊤ :=
    tsum_intPowWeight_ne_top (by norm_num)
  have hWof : ENNReal.ofReal ((∑' x : ℤ, intPowWeight (5 / 4) x).toReal)
      = ∑' x : ℤ, intPowWeight (5 / 4) x := ENNReal.ofReal_toReal hWtop
  have hconv := tsum_harmonicPowConv_le (j := j) (β := 1) (γ := (3:ℝ)/4)
    (le_refl 1) (by norm_num) (by norm_num)
  have hcongr : ∀ l : ℤ,
      ENNReal.ofReal (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ))))
        = ENNReal.ofReal (1 / ((1 + |(l : ℝ)|) ^ (1:ℝ) * (1 + |((j - l : ℤ) : ℝ)|))) := by
    intro l
    congr 1
    rw [Real.rpow_one, natAbs_sub_symm l j, natAbs_cast_eq_abs (j - l),
      natAbs_cast_eq_abs l]
    ring
  rw [tsum_congr hcongr]
  refine hconv.trans (le_of_eq ?_)
  have hexp : (1 : ℝ) + 1 - (3:ℝ)/4 = 5/4 := by norm_num
  rw [hexp]
  have h2W : (2 : ℝ≥0∞) * (∑' x : ℤ, intPowWeight (5/4) x)
      = ENNReal.ofReal (2 * (∑' x : ℤ, intPowWeight (5 / 4) x).toReal) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat, hWof]
  rw [h2W, ← ENNReal.ofReal_mul (by
    have h2 : (0:ℝ) < (2:ℝ) ^ ((3:ℝ)/4) := Real.rpow_pos_of_pos (by norm_num) _
    have hZ : (0:ℝ) < (1 + |(j : ℝ)|) ^ ((3:ℝ)/4) :=
      Real.rpow_pos_of_pos (by have := abs_nonneg ((j:ℝ)); linarith) _
    positivity)]
  congr 1
  rw [natAbs_cast_eq_abs j]
  ring

/-- The weighted pair kernel summed over the first variable collapses at the second. -/
theorem tsum_ofReal_weightedPairKernel_le (l : ℤ) :
    (∑' j : ℤ, ENNReal.ofReal
        ((1 / (1 + (j.natAbs : ℝ)) ^ ((3:ℝ)/4)) *
          (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ))))))
      ≤ ENNReal.ofReal ((1 / (1 + (l.natAbs : ℝ))) *
          (2 ^ ((1:ℝ)/2) / (1 + (l.natAbs : ℝ)) ^ ((1:ℝ)/2)) *
          (2 * (∑' x : ℤ, intPowWeight (5 / 4) x).toReal)) := by
  have hWtop : (∑' x : ℤ, intPowWeight (5 / 4) x) ≠ ⊤ :=
    tsum_intPowWeight_ne_top (by norm_num)
  have hWof : ENNReal.ofReal ((∑' x : ℤ, intPowWeight (5 / 4) x).toReal)
      = ∑' x : ℤ, intPowWeight (5 / 4) x := ENNReal.ofReal_toReal hWtop
  have hconv := tsum_harmonicPowConv_le (j := l) (β := (3:ℝ)/4) (γ := (1:ℝ)/2)
    (by norm_num) (by norm_num) (by norm_num)
  have hlnn : (0 : ℝ) < 1 + (l.natAbs : ℝ) := by positivity
  have hcongr : ∀ j : ℤ,
      ENNReal.ofReal ((1 / (1 + (j.natAbs : ℝ)) ^ ((3:ℝ)/4)) *
          (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))))
        = ENNReal.ofReal (1 / (1 + (l.natAbs : ℝ))) * ENNReal.ofReal
            (1 / ((1 + |(j : ℝ)|) ^ ((3:ℝ)/4) * (1 + |((l - j : ℤ) : ℝ)|))) := by
    intro j
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [natAbs_cast_eq_abs (l - j), natAbs_cast_eq_abs j]
    have hjnn : (0 : ℝ) < (1 + |(j : ℝ)|) ^ ((3:ℝ)/4) :=
      Real.rpow_pos_of_pos (by have := abs_nonneg ((j:ℝ)); linarith) _
    have hljnn : (0 : ℝ) < 1 + |((l - j : ℤ) : ℝ)| := by
      have := abs_nonneg (((l - j : ℤ) : ℝ)); linarith
    field_simp
  rw [tsum_congr hcongr, ENNReal.tsum_mul_left]
  calc ENNReal.ofReal (1 / (1 + (l.natAbs : ℝ))) *
        ∑' j : ℤ, ENNReal.ofReal
          (1 / ((1 + |(j : ℝ)|) ^ ((3:ℝ)/4) * (1 + |((l - j : ℤ) : ℝ)|)))
      ≤ ENNReal.ofReal (1 / (1 + (l.natAbs : ℝ))) *
          (ENNReal.ofReal (2 ^ ((1:ℝ)/2) / (1 + |(l : ℝ)|) ^ ((1:ℝ)/2)) *
            (2 * ∑' x : ℤ, intPowWeight ((3:ℝ)/4 + 1 - (1:ℝ)/2) x)) :=
        mul_le_mul' le_rfl hconv
    _ = ENNReal.ofReal ((1 / (1 + (l.natAbs : ℝ))) *
          (2 ^ ((1:ℝ)/2) / (1 + (l.natAbs : ℝ)) ^ ((1:ℝ)/2)) *
          (2 * (∑' x : ℤ, intPowWeight (5 / 4) x).toReal)) := by
        have hexp : (3:ℝ)/4 + 1 - (1:ℝ)/2 = 5/4 := by norm_num
        rw [hexp]
        have h2W : (2 : ℝ≥0∞) * (∑' x : ℤ, intPowWeight (5/4) x)
            = ENNReal.ofReal (2 * (∑' x : ℤ, intPowWeight (5 / 4) x).toReal) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat, hWof]
        rw [h2W, ← ENNReal.ofReal_mul (by
          have h2 : (0:ℝ) < (2:ℝ) ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos (by norm_num) _
          have hZ : (0:ℝ) < (1 + |(l : ℝ)|) ^ ((1:ℝ)/2) :=
            Real.rpow_pos_of_pos (by have := abs_nonneg ((l:ℝ)); linarith) _
          positivity), ← ENNReal.ofReal_mul (by
          have h2 : (0:ℝ) < (2:ℝ) ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos (by norm_num) _
          have hZ : (0:ℝ) < (1 + |(l : ℝ)|) ^ ((1:ℝ)/2) :=
            Real.rpow_pos_of_pos (by have := abs_nonneg ((l:ℝ)); linarith) _
          positivity)]
        congr 1
        rw [natAbs_cast_eq_abs l]
        ring

set_option maxHeartbeats 2000000 in
/-- **The lattice bound vanishes** along the natural frequencies, for `m ≥ 2`. -/
theorem tendsto_gaussDoubleDefectBound {m : ℕ} (hm2 : 2 ≤ m) (k : Fin m) (p : Nat.Primes) :
    Tendsto (fun I : ℕ => gaussDoubleDefectBound k p (I : ℤ)) atTop (nhds 0) := by
  classical
  have hm1 : 1 ≤ m := by omega
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  obtain ⟨K, hK, hKb⟩ := exists_norm_gaussSampleValue_pow_ratio_bound hm1 k p
  set Wr : ℝ := (∑' x : ℤ, intPowWeight (5 / 4) x).toReal with hWr
  have hWrnn : 0 ≤ Wr := ENNReal.toReal_nonneg
  set c₁ : ℝ := 128 * (p : ℝ) ^ 2 * 2 ^ ((3:ℝ)/4) * Wr with hc₁
  have hc₁nn : 0 ≤ c₁ := by
    have h2 : (0:ℝ) < (2:ℝ) ^ ((3:ℝ)/4) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  set u : ℤ → ℝ := fun j => 1 / (1 + (j.natAbs : ℝ)) ^ ((3:ℝ)/4) with hu
  have hunn : ∀ j, 0 ≤ u j := by
    intro j
    have := Real.rpow_pos_of_pos (show (0:ℝ) < 1 + (j.natAbs : ℝ) by positivity) ((3:ℝ)/4)
    simp only [hu]
    positivity
  set v : ℤ → ℤ → ℝ := fun j l => 1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))
    with hv
  have hvnn : ∀ j l, 0 ≤ v j l := by
    intro j l
    simp only [hv]
    positivity
  have humerge : ∀ j : ℤ, u j * u j = 1 / (1 + (j.natAbs : ℝ)) ^ ((3:ℝ)/2) := by
    intro j
    have hpos : (0:ℝ) < 1 + (j.natAbs : ℝ) := by positivity
    have hadd : ((3:ℝ)/4) + ((3:ℝ)/4) = (3:ℝ)/2 := by norm_num
    simp only [hu]
    rw [div_mul_div_comm, one_mul, ← Real.rpow_add hpos, hadd]
  have hfun : (fun I : ℕ => gaussDoubleDefectBound k p (I : ℤ))
      = fun I : ℕ => ∑' jl : ℤ × ℤ, ENNReal.ofReal
          (c₁ * u jl.1 * v jl.1 jl.2 *
            (‖gaussSampleRatioDefect k p jl.1 (I : ℤ)‖ ^ 2 *
              ‖gaussSampleRatioDefect k p jl.2 (I : ℤ)‖ ^ 2)) := by
    funext I
    rw [gaussDoubleDefectBound]
  rw [hfun]
  refine tendsto_tsum_zero_of_dominated
    (F := fun (jl : ℤ × ℤ) (I : ℕ) => ENNReal.ofReal
      (c₁ * u jl.1 * v jl.1 jl.2 *
        (‖gaussSampleRatioDefect k p jl.1 (I : ℤ)‖ ^ 2 *
          ‖gaussSampleRatioDefect k p jl.2 (I : ℤ)‖ ^ 2)))
    (G := fun (jl : ℤ × ℤ) (_ : ℕ) => ENNReal.ofReal (c₁ * u jl.1 * v jl.1 jl.2 * (24 + 24 * K)))
    (H := fun (jl : ℤ × ℤ) (I : ℕ) =>
      (if I < 2 * jl.1.natAbs ∧ ((I : ℤ) + jl.1).natAbs ≠ 0 then
        ENNReal.ofReal (c₁ * u jl.1 * v jl.1 jl.2 *
          (6 * K * (I : ℝ) / ((((I : ℤ) + jl.1).natAbs : ℝ)))) else 0) +
      (if I < 2 * jl.2.natAbs ∧ ((I : ℤ) + jl.2).natAbs ≠ 0 then
        ENNReal.ofReal (c₁ * u jl.1 * v jl.1 jl.2 *
          (6 * K * (I : ℝ) / ((((I : ℤ) + jl.2).natAbs : ℝ)))) else 0))
    ?_ ?_ ?_ ?_
  · -- every mode vanishes
    intro jl
    have hj := tendsto_gaussSampleRatioDefect_nat hm1 k p jl.1
    have hl := tendsto_gaussSampleRatioDefect_nat hm1 k p jl.2
    have hjn : Tendsto (fun I : ℕ => ‖gaussSampleRatioDefect k p jl.1 (I : ℤ)‖ ^ 2)
        atTop (nhds 0) := by
      have h := (tendsto_zero_iff_norm_tendsto_zero.mp hj)
      simpa using h.pow 2
    have hln : Tendsto (fun I : ℕ => ‖gaussSampleRatioDefect k p jl.2 (I : ℤ)‖ ^ 2)
        atTop (nhds 0) := by
      have h := (tendsto_zero_iff_norm_tendsto_zero.mp hl)
      simpa using h.pow 2
    have hprod := hjn.mul hln
    rw [mul_zero] at hprod
    have hmul := hprod.const_mul (c₁ * u jl.1 * v jl.1 jl.2)
    rw [mul_zero] at hmul
    have hcont := (ENNReal.continuous_ofReal.tendsto 0).comp hmul
    simpa [Function.comp_def] using hcont
  · -- the pointwise domination
    intro jl I
    set x : ℝ := c₁ * u jl.1 * v jl.1 jl.2 with hx
    have hxnn : 0 ≤ x := by
      simp only [hx]
      exact mul_nonneg (mul_nonneg hc₁nn (hunn _)) (hvnn _ _)
    have hcap := norm_gaussSampleRatioDefect_sq_mul_sq_le hm2 k p hKb I jl.1 jl.2
    have hnf1 := harmonic_factor_near_far (K' := 6 * K) (by positivity) I jl.1
    have hnf2 := harmonic_factor_near_far (K' := 6 * K) (by positivity) I jl.2
    have hreal : x * (‖gaussSampleRatioDefect k p jl.1 (I : ℤ)‖ ^ 2 *
          ‖gaussSampleRatioDefect k p jl.2 (I : ℤ)‖ ^ 2)
        ≤ x * (24 + 24 * K) +
          ((if I < 2 * jl.1.natAbs ∧ ((I : ℤ) + jl.1).natAbs ≠ 0 then
            x * (6 * K * (I : ℝ) / ((((I : ℤ) + jl.1).natAbs : ℝ))) else 0) +
          (if I < 2 * jl.2.natAbs ∧ ((I : ℤ) + jl.2).natAbs ≠ 0 then
            x * (6 * K * (I : ℝ) / ((((I : ℤ) + jl.2).natAbs : ℝ))) else 0)) := by
      have h1 : x * (‖gaussSampleRatioDefect k p jl.1 (I : ℤ)‖ ^ 2 *
            ‖gaussSampleRatioDefect k p jl.2 (I : ℤ)‖ ^ 2)
          ≤ x * (24 + 6 * K * (I : ℝ) / (((I : ℤ) + jl.1).natAbs : ℝ) +
              6 * K * (I : ℝ) / (((I : ℤ) + jl.2).natAbs : ℝ)) :=
        mul_le_mul_of_nonneg_left hcap hxnn
      have h2 : x * (6 * K * (I : ℝ) / (((I : ℤ) + jl.1).natAbs : ℝ))
          ≤ x * (2 * (6 * K)) +
            (if I < 2 * jl.1.natAbs ∧ ((I : ℤ) + jl.1).natAbs ≠ 0 then
              x * (6 * K * (I : ℝ) / ((((I : ℤ) + jl.1).natAbs : ℝ))) else 0) := by
        have := mul_le_mul_of_nonneg_left hnf1 hxnn
        rw [mul_add, mul_ite, mul_zero] at this
        exact this
      have h3 : x * (6 * K * (I : ℝ) / (((I : ℤ) + jl.2).natAbs : ℝ))
          ≤ x * (2 * (6 * K)) +
            (if I < 2 * jl.2.natAbs ∧ ((I : ℤ) + jl.2).natAbs ≠ 0 then
              x * (6 * K * (I : ℝ) / ((((I : ℤ) + jl.2).natAbs : ℝ))) else 0) := by
        have := mul_le_mul_of_nonneg_left hnf2 hxnn
        rw [mul_add, mul_ite, mul_zero] at this
        exact this
      have hxmul : x * (24 + 6 * K * (I : ℝ) / (((I : ℤ) + jl.1).natAbs : ℝ) +
            6 * K * (I : ℝ) / (((I : ℤ) + jl.2).natAbs : ℝ))
          = x * 24 + x * (6 * K * (I : ℝ) / (((I : ℤ) + jl.1).natAbs : ℝ)) +
            x * (6 * K * (I : ℝ) / (((I : ℤ) + jl.2).natAbs : ℝ)) := by ring
      have hcollect : x * 24 + x * (2 * (6 * K)) + x * (2 * (6 * K))
          = x * (24 + 24 * K) := by ring
      rw [hxmul] at h1
      linarith [h1, h2, h3]
    have hK6 : (0 : ℝ) ≤ 6 * K := by positivity
    have hite1nn : (0:ℝ) ≤ (if I < 2 * jl.1.natAbs ∧ ((I : ℤ) + jl.1).natAbs ≠ 0 then
        x * (6 * K * (I : ℝ) / ((((I : ℤ) + jl.1).natAbs : ℝ))) else 0) := by
      split_ifs
      · exact mul_nonneg hxnn (by positivity)
      · exact le_refl 0
    have hite2nn : (0:ℝ) ≤ (if I < 2 * jl.2.natAbs ∧ ((I : ℤ) + jl.2).natAbs ≠ 0 then
        x * (6 * K * (I : ℝ) / ((((I : ℤ) + jl.2).natAbs : ℝ))) else 0) := by
      split_ifs
      · exact mul_nonneg hxnn (by positivity)
      · exact le_refl 0
    have hconv1 : ENNReal.ofReal
        (if I < 2 * jl.1.natAbs ∧ ((I : ℤ) + jl.1).natAbs ≠ 0 then
          x * (6 * K * (I : ℝ) / ((((I : ℤ) + jl.1).natAbs : ℝ))) else 0)
        = (if I < 2 * jl.1.natAbs ∧ ((I : ℤ) + jl.1).natAbs ≠ 0 then
          ENNReal.ofReal (x * (6 * K * (I : ℝ) / ((((I : ℤ) + jl.1).natAbs : ℝ)))) else 0) := by
      split_ifs
      · rfl
      · exact ENNReal.ofReal_zero
    have hconv2 : ENNReal.ofReal
        (if I < 2 * jl.2.natAbs ∧ ((I : ℤ) + jl.2).natAbs ≠ 0 then
          x * (6 * K * (I : ℝ) / ((((I : ℤ) + jl.2).natAbs : ℝ))) else 0)
        = (if I < 2 * jl.2.natAbs ∧ ((I : ℤ) + jl.2).natAbs ≠ 0 then
          ENNReal.ofReal (x * (6 * K * (I : ℝ) / ((((I : ℤ) + jl.2).natAbs : ℝ)))) else 0) := by
      split_ifs
      · rfl
      · exact ENNReal.ofReal_zero
    refine le_trans (ENNReal.ofReal_le_ofReal hreal) ?_
    rw [ENNReal.ofReal_add (mul_nonneg hxnn (by positivity))
      (add_nonneg hite1nn hite2nn), ENNReal.ofReal_add hite1nn hite2nn,
      hconv1, hconv2]
  · -- uniformly small `G`-tails
    intro ε hε
    have hstep : ∀ j : ℤ, (∑' l : ℤ, ENNReal.ofReal (c₁ * u j * v j l * (24 + 24 * K)))
        ≤ ENNReal.ofReal ((24 + 24 * K) * c₁ * 2 ^ ((3:ℝ)/4) * (2 * Wr)) *
          intPowWeight ((3:ℝ)/2) j := by
      intro j
      have hpull : ∀ l : ℤ, ENNReal.ofReal (c₁ * u j * v j l * (24 + 24 * K))
          = ENNReal.ofReal (c₁ * (24 + 24 * K) * u j) * ENNReal.ofReal (v j l) := by
        intro l
        rw [← ENNReal.ofReal_mul (by
          have := hunn j
          positivity)]
        congr 1
        ring
      rw [tsum_congr hpull, ENNReal.tsum_mul_left]
      have hpair := tsum_ofReal_pairKernel_le j
      rw [← hWr] at hpair
      have hvform : (∑' l : ℤ, ENNReal.ofReal (v j l))
          = ∑' l : ℤ, ENNReal.ofReal
              (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))) := rfl
      calc ENNReal.ofReal (c₁ * (24 + 24 * K) * u j) * ∑' l : ℤ, ENNReal.ofReal (v j l)
          ≤ ENNReal.ofReal (c₁ * (24 + 24 * K) * u j) *
              ENNReal.ofReal (2 ^ ((3:ℝ)/4) * (1 / (1 + (j.natAbs : ℝ)) ^ ((3:ℝ)/4)) *
                (2 * Wr)) := by
            refine mul_le_mul' le_rfl ?_
            rw [hvform]
            exact hpair
        _ = ENNReal.ofReal ((24 + 24 * K) * c₁ * 2 ^ ((3:ℝ)/4) * (2 * Wr)) *
              intPowWeight ((3:ℝ)/2) j := by
            rw [← ENNReal.ofReal_mul (by
              have := hunn j
              positivity)]
            rw [intPowWeight, ← ENNReal.ofReal_mul (by
              have h2 : (0:ℝ) < (2:ℝ) ^ ((3:ℝ)/4) := Real.rpow_pos_of_pos (by norm_num) _
              positivity)]
            congr 1
            rw [← natAbs_cast_eq_abs j]
            have hmerge := humerge j
            have hexpand : c₁ * (24 + 24 * K) * u j *
                (2 ^ ((3:ℝ)/4) * (1 / (1 + (j.natAbs : ℝ)) ^ ((3:ℝ)/4)) * (2 * Wr))
                = (24 + 24 * K) * c₁ * 2 ^ ((3:ℝ)/4) * (2 * Wr) * (u j * u j) := by
              simp only [hu]
              ring
            rw [hexpand, hmerge]
    have hGle : (∑' jl : ℤ × ℤ,
        ENNReal.ofReal (c₁ * u jl.1 * v jl.1 jl.2 * (24 + 24 * K)))
        ≤ ENNReal.ofReal ((24 + 24 * K) * c₁ * 2 ^ ((3:ℝ)/4) * (2 * Wr)) *
          ∑' j : ℤ, intPowWeight ((3:ℝ)/2) j := by
      rw [ENNReal.tsum_prod']
      refine le_trans (ENNReal.tsum_le_tsum hstep) ?_
      rw [ENNReal.tsum_mul_left]
    have hGtot : (∑' jl : ℤ × ℤ,
        ENNReal.ofReal (c₁ * u jl.1 * v jl.1 jl.2 * (24 + 24 * K))) ≠ ⊤ :=
      ne_top_of_le_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (tsum_intPowWeight_ne_top (by norm_num))) hGle
    have htail := ENNReal.tendsto_tsum_compl_atTop_zero hGtot
    obtain ⟨S, hS⟩ := (ENNReal.tendsto_nhds_zero.mp htail ε hε).exists
    exact ⟨S, fun _ => hS⟩
  · -- the far-band totals vanish
    have hsqueeze : ∀ {f g : ℕ → ℝ≥0∞}, (∀ I, f I ≤ g I) →
        Tendsto g atTop (nhds 0) → Tendsto f atTop (nhds 0) := by
      intro f g hle hg
      rw [ENNReal.tendsto_nhds_zero] at hg ⊢
      intro ε hε
      filter_upwards [hg ε hε] with I hI
      exact le_trans (hle I) hI
    set cH₁ : ℝ := c₁ * (6 * K) * (2 ^ ((3:ℝ)/4) * (2 * Wr)) with hcH₁
    have hcH₁nn : 0 ≤ cH₁ := by
      have h2 : (0:ℝ) < (2:ℝ) ^ ((3:ℝ)/4) := Real.rpow_pos_of_pos (by norm_num) _
      have := hc₁nn
      positivity
    set cH₂ : ℝ := c₁ * (6 * K) * (2 ^ ((1:ℝ)/2) * (2 * Wr)) with hcH₂
    have hcH₂nn : 0 ≤ cH₂ := by
      have h2 : (0:ℝ) < (2:ℝ) ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos (by norm_num) _
      have := hc₁nn
      positivity
    have hH1 : Tendsto (fun I : ℕ => ∑' jl : ℤ × ℤ,
        (if I < 2 * jl.1.natAbs ∧ ((I : ℤ) + jl.1).natAbs ≠ 0 then
          ENNReal.ofReal (c₁ * u jl.1 * v jl.1 jl.2 *
            (6 * K * (I : ℝ) / ((((I : ℤ) + jl.1).natAbs : ℝ)))) else 0))
        atTop (nhds 0) := by
      refine hsqueeze (g := fun I : ℕ => ∑' j : ℤ,
        (if I < 2 * j.natAbs ∧ ((I : ℤ) + j).natAbs ≠ 0 then
          ENNReal.ofReal (cH₁ * (I : ℝ) /
            ((1 + (j.natAbs : ℝ)) ^ ((3:ℝ)/2) * (((I : ℤ) + j).natAbs : ℝ))) else 0))
        ?_ (tendsto_tsum_farBandPower_zero hcH₁nn (by norm_num))
      intro I
      rw [ENNReal.tsum_prod']
      refine ENNReal.tsum_le_tsum fun j => ?_
      by_cases hPj : I < 2 * j.natAbs ∧ ((I : ℤ) + j).natAbs ≠ 0
      · simp only [if_pos hPj]
        have hpull : ∀ l : ℤ, ENNReal.ofReal (c₁ * u j * v j l *
            (6 * K * (I : ℝ) / ((((I : ℤ) + j).natAbs : ℝ))))
            = ENNReal.ofReal (c₁ * u j *
                (6 * K * (I : ℝ) / ((((I : ℤ) + j).natAbs : ℝ)))) *
              ENNReal.ofReal (v j l) := by
          intro l
          rw [← ENNReal.ofReal_mul (by
            have := hunn j
            positivity)]
          congr 1
          ring
        rw [tsum_congr hpull, ENNReal.tsum_mul_left]
        have hpair := tsum_ofReal_pairKernel_le j
        rw [← hWr] at hpair
        have hvform : (∑' l : ℤ, ENNReal.ofReal (v j l))
            = ∑' l : ℤ, ENNReal.ofReal
                (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))) := rfl
        calc ENNReal.ofReal (c₁ * u j *
              (6 * K * (I : ℝ) / ((((I : ℤ) + j).natAbs : ℝ)))) *
              ∑' l : ℤ, ENNReal.ofReal (v j l)
            ≤ ENNReal.ofReal (c₁ * u j *
                (6 * K * (I : ℝ) / ((((I : ℤ) + j).natAbs : ℝ)))) *
                ENNReal.ofReal (2 ^ ((3:ℝ)/4) * (1 / (1 + (j.natAbs : ℝ)) ^ ((3:ℝ)/4)) *
                  (2 * Wr)) := by
              refine mul_le_mul' le_rfl ?_
              rw [hvform]
              exact hpair
          _ = ENNReal.ofReal (cH₁ * (I : ℝ) /
                ((1 + (j.natAbs : ℝ)) ^ ((3:ℝ)/2) * (((I : ℤ) + j).natAbs : ℝ))) := by
              rw [← ENNReal.ofReal_mul (by
                have := hunn j
                positivity)]
              congr 1
              have hmerge := humerge j
              have h34 : (0:ℝ) < (1 + (j.natAbs : ℝ)) ^ ((3:ℝ)/4) :=
                Real.rpow_pos_of_pos (by positivity) _
              have h32 : (0:ℝ) < (1 + (j.natAbs : ℝ)) ^ ((3:ℝ)/2) :=
                Real.rpow_pos_of_pos (by positivity) _
              have hexpand : c₁ * u j * (6 * K * (I : ℝ) / ((((I : ℤ) + j).natAbs : ℝ))) *
                  (2 ^ ((3:ℝ)/4) * (1 / (1 + (j.natAbs : ℝ)) ^ ((3:ℝ)/4)) * (2 * Wr))
                  = cH₁ * (I : ℝ) / ((((I : ℤ) + j).natAbs : ℝ)) * (u j * u j) := by
                simp only [hu, hcH₁]
                ring
              rw [hexpand, hmerge]
              rw [div_mul_div_comm, mul_one]
              congr 1
              ring
      · simp only [if_neg hPj, tsum_zero]
        exact le_rfl
    have hH2 : Tendsto (fun I : ℕ => ∑' jl : ℤ × ℤ,
        (if I < 2 * jl.2.natAbs ∧ ((I : ℤ) + jl.2).natAbs ≠ 0 then
          ENNReal.ofReal (c₁ * u jl.1 * v jl.1 jl.2 *
            (6 * K * (I : ℝ) / ((((I : ℤ) + jl.2).natAbs : ℝ)))) else 0))
        atTop (nhds 0) := by
      have hlmerge : ∀ l : ℤ, (1 / (1 + (l.natAbs:ℝ))) *
          (1 / (1 + (l.natAbs:ℝ)) ^ ((1:ℝ)/2)) = 1 / (1 + (l.natAbs:ℝ)) ^ ((3:ℝ)/2) := by
        intro l
        have hpos : (0:ℝ) < 1 + (l.natAbs : ℝ) := by positivity
        rw [div_mul_div_comm, one_mul]
        congr 1
        nth_rewrite 1 [← Real.rpow_one (1 + (l.natAbs : ℝ))]
        rw [← Real.rpow_add hpos]
        norm_num
      refine hsqueeze (g := fun I : ℕ => ∑' l : ℤ,
        (if I < 2 * l.natAbs ∧ ((I : ℤ) + l).natAbs ≠ 0 then
          ENNReal.ofReal (cH₂ * (I : ℝ) /
            ((1 + (l.natAbs : ℝ)) ^ ((3:ℝ)/2) * (((I : ℤ) + l).natAbs : ℝ))) else 0))
        ?_ (tendsto_tsum_farBandPower_zero hcH₂nn (by norm_num))
      intro I
      have hswap := Equiv.tsum_eq (Equiv.prodComm ℤ ℤ)
        (fun jl : ℤ × ℤ =>
          (if I < 2 * jl.2.natAbs ∧ ((I : ℤ) + jl.2).natAbs ≠ 0 then
            ENNReal.ofReal (c₁ * u jl.1 * v jl.1 jl.2 *
              (6 * K * (I : ℝ) / ((((I : ℤ) + jl.2).natAbs : ℝ)))) else 0))
      rw [← hswap]
      rw [ENNReal.tsum_prod']
      refine ENNReal.tsum_le_tsum fun l => ?_
      by_cases hPl : I < 2 * l.natAbs ∧ ((I : ℤ) + l).natAbs ≠ 0
      · simp only [Equiv.prodComm_apply, Prod.swap_prod_mk, if_pos hPl]
        have hpull : ∀ j : ℤ, ENNReal.ofReal (c₁ * u j * v j l *
            (6 * K * (I : ℝ) / ((((I : ℤ) + l).natAbs : ℝ))))
            = ENNReal.ofReal (c₁ *
                (6 * K * (I : ℝ) / ((((I : ℤ) + l).natAbs : ℝ)))) *
              ENNReal.ofReal (u j * v j l) := by
          intro j
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
        rw [tsum_congr hpull, ENNReal.tsum_mul_left]
        have hpair := tsum_ofReal_weightedPairKernel_le l
        rw [← hWr] at hpair
        have huvform : (∑' j : ℤ, ENNReal.ofReal (u j * v j l))
            = ∑' j : ℤ, ENNReal.ofReal
                ((1 / (1 + (j.natAbs : ℝ)) ^ ((3:ℝ)/4)) *
                  (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ))))) := rfl
        calc ENNReal.ofReal (c₁ * (6 * K * (I : ℝ) / ((((I : ℤ) + l).natAbs : ℝ)))) *
              ∑' j : ℤ, ENNReal.ofReal (u j * v j l)
            ≤ ENNReal.ofReal (c₁ * (6 * K * (I : ℝ) / ((((I : ℤ) + l).natAbs : ℝ)))) *
                ENNReal.ofReal ((1 / (1 + (l.natAbs : ℝ))) *
                  (2 ^ ((1:ℝ)/2) / (1 + (l.natAbs : ℝ)) ^ ((1:ℝ)/2)) * (2 * Wr)) := by
              refine mul_le_mul' le_rfl ?_
              rw [huvform]
              exact hpair
          _ = ENNReal.ofReal (cH₂ * (I : ℝ) /
                ((1 + (l.natAbs : ℝ)) ^ ((3:ℝ)/2) * (((I : ℤ) + l).natAbs : ℝ))) := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              congr 1
              have h12 : (0:ℝ) < (1 + (l.natAbs : ℝ)) ^ ((1:ℝ)/2) :=
                Real.rpow_pos_of_pos (by positivity) _
              have h32 : (0:ℝ) < (1 + (l.natAbs : ℝ)) ^ ((3:ℝ)/2) :=
                Real.rpow_pos_of_pos (by positivity) _
              have hexpand : c₁ * (6 * K * (I : ℝ) / ((((I : ℤ) + l).natAbs : ℝ))) *
                  ((1 / (1 + (l.natAbs : ℝ))) *
                    (2 ^ ((1:ℝ)/2) / (1 + (l.natAbs : ℝ)) ^ ((1:ℝ)/2)) * (2 * Wr))
                  = cH₂ * (I : ℝ) / ((((I : ℤ) + l).natAbs : ℝ)) *
                    ((1 / (1 + (l.natAbs:ℝ))) * (1 / (1 + (l.natAbs:ℝ)) ^ ((1:ℝ)/2))) := by
                simp only [hcH₂]
                field_simp
              rw [hexpand, hlmerge l]
              rw [div_mul_div_comm, mul_one]
              congr 1
              ring
      · simp only [Equiv.prodComm_apply, Prod.swap_prod_mk, if_neg hPl, tsum_zero]
        exact le_rfl
    have hsum := hH1.add hH2
    rw [add_zero] at hsum
    refine hsum.congr fun I => ?_
    rw [← ENNReal.tsum_add]

/-- The lattice bound vanishes along every escaping frequency sequence. -/
theorem tendsto_gaussDoubleDefectBound_comp {m : ℕ} (hm2 : 2 ≤ m) (k : Fin m)
    (p : Nat.Primes) {ι : ℕ → ℤ}
    (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop) :
    Tendsto (fun n : ℕ => gaussDoubleDefectBound k p (ι n)) atTop (nhds 0) := by
  have hcomp := (tendsto_gaussDoubleDefectBound hm2 k p).comp hι
  refine hcomp.congr fun n => ?_
  simp only [Function.comp_apply]
  exact gaussDoubleDefectBound_natAbs k p (ι n)

/-- **The double defect vanishes** along every escaping frequency sequence, for `m ≥ 2`. -/
theorem tendsto_norm_gaussDoubleDefectVector_comp {m : ℕ} (hm2 : 2 ≤ m) (k : Fin m)
    (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) {ι : ℕ → ℤ}
    (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop) :
    Tendsto (fun n : ℕ =>
      ‖gaussDoubleDefectVector (le_trans one_le_two hm2) k p hp (ι n)‖)
      atTop (nhds 0) := by
  have hm1 : 1 ≤ m := le_trans one_le_two hm2
  have hbound := tendsto_gaussDoubleDefectBound_comp hm2 k p hι
  rw [ENNReal.tendsto_nhds_zero] at hbound
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hbound (ENNReal.ofReal ((ε / 2) ^ 2)) (by simpa using pow_pos (half_pos hε) 2))
  refine ⟨N, fun n hn => ?_⟩
  have hmaster := norm_gaussDoubleDefectVector_sq_le hm1 k p hp (ι n)
  have hofReal : ENNReal.ofReal
      (‖gaussDoubleDefectVector hm1 k p hp (ι n)‖ ^ (2:ℝ))
      ≤ ENNReal.ofReal ((ε / 2) ^ 2) := le_trans hmaster (hN n hn)
  have hle : ‖gaussDoubleDefectVector hm1 k p hp (ι n)‖ ^ (2:ℝ) ≤ (ε / 2) ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hofReal
  have hnorm2 : ‖gaussDoubleDefectVector hm1 k p hp (ι n)‖ ^ (2:ℕ) ≤ (ε / 2) ^ 2 := by
    have hcast : ‖gaussDoubleDefectVector hm1 k p hp (ι n)‖ ^ (2:ℕ)
        = ‖gaussDoubleDefectVector hm1 k p hp (ι n)‖ ^ (2:ℝ) := by
      rw [← Real.rpow_natCast (‖gaussDoubleDefectVector hm1 k p hp (ι n)‖) 2]
      norm_num
    rw [hcast]
    exact hle
  have hfinal : ‖gaussDoubleDefectVector hm1 k p hp (ι n)‖ ≤ ε / 2 := by
    have h := Real.sqrt_le_sqrt hnorm2
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (half_pos hε).le] at h
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith

end

end RHTower
