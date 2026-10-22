import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaLogCofinalTraceNoGo
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmStokesOrientedFirstTraceQuantizedJump

/-!
# Route P primitive Gamma--Julia Stokes aperture residue transport

P-G105H isolates the unique nonsummable face of the prime-log-conjugated P-G186 trace: at depth
zero its density is `1/(4p)`, while the strictly positive-depth remainder is regular.  This file
constructs the exact source-derived Radon--Nikodym transport of that face into the corpus's literal
oriented Stokes first-trace current.

For right aperture depth `d>0`, the positive diagonal multiplier has square

```text
32 d log(p) p^(-2d).
```

Multiplying `1/(4p)` by this square gives exactly

```text
8 d log(p) p^(-(1+2d)),
```

the existing label-faithful oriented Stokes prime term.  Congruence by the square-root diagonal is
performed on the actual finite P-G186 log-conjugated Gram, so off-diagonal incidence is retained.
The all-prime transported face is summable for every `d>0`; adding the already source-derived
higher-valuation/archimedean polar countercurrent gives the completed prime--Gamma current and
cancels the wall residue continuously.

This closes trace-level source/Stokes provenance and exact residue cancellation.  It does not yet
construct a cofinal operator determinant carrying the polar channel, prove that P-G105G bivariate
stability survives that operator limit, or identify the limiting divisor with Xi.
-/

open Complex Matrix Filter Topology

namespace RHTower

noncomputable section

/-- Squared right-aperture Radon--Nikodym multiplier on the singular depth-zero prime face. -/
def routePPrimitiveGammaJuliaStokesApertureScaleSq
    (d : ℝ) (p : Nat.Primes) : ℝ :=
  32 * d * Real.log (p : ℝ) * (p : ℝ) ^ (-2 * d)

/-- The aperture multiplier is strictly positive on the physical right ray. -/
theorem routePPrimitiveGammaJuliaStokesApertureScaleSq_pos
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    0 < routePPrimitiveGammaJuliaStokesApertureScaleSq d p := by
  rw [routePPrimitiveGammaJuliaStokesApertureScaleSq]
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  exact mul_pos
    (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 32) hd)
      (Real.log_pos (by exact_mod_cast p.property.one_lt)))
    (Real.rpow_pos_of_pos hp _)

/-- P-G105H singular trace density after aperture transport. -/
def routePPrimitiveGammaJuliaStokesTransportedPrimeWeight
    (d : ℝ) (p : Nat.Primes) : ℝ :=
  routePPrimitiveGammaJuliaStokesApertureScaleSq d p *
    routePPrimitiveGammaJuliaLogCofinalTraceWeight (p, 0)

/-- Exact labelwise identification with the literal oriented Stokes current. -/
theorem routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_eq
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p =
      gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm d p := by
  rw [routePPrimitiveGammaJuliaStokesTransportedPrimeWeight,
    routePPrimitiveGammaJuliaStokesApertureScaleSq,
    routePPrimitiveGammaJuliaLogCofinalTraceWeight_prime_zero,
    gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm,
    xiMassPrimeSquareEulerWeight_eq]
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  rw [abs_of_pos hd]
  calc
    32 * d * Real.log (p : ℝ) * (p : ℝ) ^ (-2 * d) *
          (1 / 4 * (1 / (p : ℝ))) =
        8 * d * Real.log (p : ℝ) *
          ((p : ℝ) ^ (-2 * d) * (p : ℝ)⁻¹) := by ring
    _ = 8 * d * Real.log (p : ℝ) *
          ((p : ℝ) ^ (-2 * d) * (p : ℝ) ^ (-1 : ℝ)) := by
      rw [Real.rpow_neg_one]
    _ = 8 * d * Real.log (p : ℝ) *
          (p : ℝ) ^ (-(1 + 2 * d)) := by
      rw [← Real.rpow_add hp]
      congr 2
      ring
    _ = 8 * d * (Real.log (p : ℝ) *
          (p : ℝ) ^ (-(1 + 2 * d))) := by ring

/-- The transported singular face is summable at every positive aperture. -/
theorem summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight
    {d : ℝ} (hd : 0 < d) :
    Summable (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d) := by
  exact (summable_gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm d).congr
    fun p => (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_eq hd p).symm

/-- The all-prime transported trace is exactly the literal oriented first-trace current. -/
theorem tsum_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight
    {d : ℝ} (hd : 0 < d) :
    (∑' p : Nat.Primes,
      routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p) =
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d := by
  rw [gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent]
  exact tsum_congr
    (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_eq hd)

/-- Strictly positive-depth part of the raw P-G105H promoted trace. -/
def routePPrimitiveGammaJuliaLogCofinalTraceRegularTailWeight
    (pk : Nat.Primes × ℕ) : ℝ :=
  routePPrimitiveGammaJuliaLogCofinalTraceWeight (pk.1, pk.2 + 1)

/-- Explicit summable majorant for the strictly positive-depth remainder. -/
theorem routePPrimitiveGammaJuliaLogCofinalTraceRegularTailWeight_le
    (pk : Nat.Primes × ℕ) :
    routePPrimitiveGammaJuliaLogCofinalTraceRegularTailWeight pk ≤
      (4 * Real.log 2)⁻¹ * xiPrimeLogHigherValuationWeight pk := by
  rw [routePPrimitiveGammaJuliaLogCofinalTraceRegularTailWeight,
    routePPrimitiveGammaJuliaLogCofinalTraceWeight_eq,
    xiPrimeLogHigherValuationWeight]
  simp only [Nat.cast_add, Nat.cast_one]
  have hp : (0 : ℝ) < (pk.1 : ℝ) := by exact_mod_cast pk.1.property.pos
  have hp2 : (2 : ℝ) ≤ (pk.1 : ℝ) := by exact_mod_cast pk.1.property.two_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log (pk.1 : ℝ) :=
    Real.log_le_log (by norm_num) hp2
  have hk : (1 : ℝ) ≤ ((pk.2 : ℝ) + 2) ^ 3 := by
    have hknn : (0 : ℝ) ≤ pk.2 := Nat.cast_nonneg pk.2
    exact one_le_pow₀ (by linarith)
  have hpow : ((pk.1 : ℝ)⁻¹) ^ (pk.2 + 2) =
      ((pk.1 : ℝ)⁻¹) ^ ((pk.2 : ℝ) + 2) := by
    rw [← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  rw [hpow]
  rw [show (pk.2 : ℝ) + 1 + 1 = (pk.2 : ℝ) + 2 by ring]
  have hbase : 0 ≤ ((pk.1 : ℝ)⁻¹) ^ ((pk.2 : ℝ) + 2) := by positivity
  have hcoeff : (1 / 4 : ℝ) * ((((pk.2 : ℝ) + 2) ^ 3)⁻¹) ≤
      (4 * Real.log 2)⁻¹ * Real.log (pk.1 : ℝ) := by
    have hkinv : ((((pk.2 : ℝ) + 2) ^ 3)⁻¹) ≤ 1 := by
      exact (inv_le_one₀ (by positivity)).mpr hk
    calc
      (1 / 4 : ℝ) * ((((pk.2 : ℝ) + 2) ^ 3)⁻¹) ≤ 1 / 4 := by nlinarith
      _ = (4 * Real.log 2)⁻¹ * Real.log 2 := by field_simp [hlog2.ne']
      _ ≤ (4 * Real.log 2)⁻¹ * Real.log (pk.1 : ℝ) := by gcongr
  calc
    (1 / 4 : ℝ) * ((pk.1 : ℝ)⁻¹) ^ ((pk.2 : ℝ) + 2) *
          (((pk.2 : ℝ) + 2) ^ 3)⁻¹ =
        ((1 / 4 : ℝ) * (((pk.2 : ℝ) + 2) ^ 3)⁻¹) *
          ((pk.1 : ℝ)⁻¹) ^ ((pk.2 : ℝ) + 2) := by ring
    _ ≤ ((4 * Real.log 2)⁻¹ * Real.log (pk.1 : ℝ)) *
          ((pk.1 : ℝ)⁻¹) ^ ((pk.2 : ℝ) + 2) :=
      mul_le_mul_of_nonneg_right hcoeff hbase
    _ = (4 * Real.log 2)⁻¹ *
          (Real.log (pk.1 : ℝ) *
            ((pk.1 : ℝ)⁻¹) ^ ((pk.2 : ℝ) + 2)) := by ring

/-- P-G105H divergence is localized completely on the depth-zero prime face. -/
theorem summable_routePPrimitiveGammaJuliaLogCofinalTraceRegularTailWeight :
    Summable routePPrimitiveGammaJuliaLogCofinalTraceRegularTailWeight := by
  refine Summable.of_nonneg_of_le (fun pk => ?_)
    routePPrimitiveGammaJuliaLogCofinalTraceRegularTailWeight_le ?_
  · rw [routePPrimitiveGammaJuliaLogCofinalTraceRegularTailWeight]
    exact routePPrimitiveGammaJuliaLogCofinalTraceWeight_nonneg _
  · exact summable_xiPrimeLogHigherValuationWeight.mul_left
      (4 * Real.log 2)⁻¹

/-- Square-root aperture diagonal on a finite depth-zero prime packet. -/
def routePPrimitiveGammaJuliaStokesApertureDiagonal {N : ℕ}
    (d : ℝ) (p : Fin N → Nat.Primes) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i =>
    (Real.sqrt (routePPrimitiveGammaJuliaStokesApertureScaleSq d (p i)) : ℂ)

/-- Actual P-G186 depth-zero Gram after prime-log and Stokes aperture congruences. -/
def routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram {N : ℕ}
    (d : ℝ) (p : Fin N → Nat.Primes) (kappa : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  let pe : Fin N → Nat.Primes × ℕ := fun i => (p i, 0)
  routePPrimitiveGammaJuliaStokesApertureDiagonal d p *
    routePPrimitiveJointDepthPrimeLogConjugate pe
      (routePPrimitiveBurnolWindowGramMatrix pe kappa) *
    routePPrimitiveGammaJuliaStokesApertureDiagonal d p

/-- Finite actual-matrix trace equals the finite source-derived Stokes current. -/
theorem routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram_trace
    {N : ℕ} {d : ℝ} (hd : 0 < d) (p : Fin N → Nat.Primes)
    (kappa : Fin N → ℝ) :
    (routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram
      d p kappa).trace.re =
      ∑ i, routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d (p i) := by
  rw [Matrix.trace, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Matrix.diag_apply]
  rw [routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram,
    routePPrimitiveGammaJuliaStokesApertureDiagonal,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [routePPrimitiveJointDepthPrimeLogConjugate_apply,
    routePPrimitiveBurnolWindowGramMatrix_eq_baseCauchy,
    routePPrimitiveBaseCauchyCubicKernelMatrix_diagonal (by norm_num)]
  have hsqrt :
      Real.sqrt (routePPrimitiveGammaJuliaStokesApertureScaleSq d (p i)) ^ 2 =
        routePPrimitiveGammaJuliaStokesApertureScaleSq d (p i) :=
    Real.sq_sqrt (le_of_lt
      (routePPrimitiveGammaJuliaStokesApertureScaleSq_pos hd (p i)))
  rw [routePPrimitiveGammaJuliaStokesTransportedPrimeWeight]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero]
  rw [routePPrimitiveGammaJuliaLogCofinalTraceWeight]
  ring_nf
  rw [hsqrt]
  ring

/-- Completed renormalized trace: transported singular face plus literal polar/Gamma channel. -/
def routePPrimitiveGammaJuliaStokesCompletedRenormalizedTrace (d : ℝ) : ℝ :=
  (∑' p : Nat.Primes,
    routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p) +
    gammaSewnMobiusApertureStokesOrientedPolarCountercurrent d

/-- The constructed source trace is exactly the corpus's completed prime--Gamma current. -/
theorem routePPrimitiveGammaJuliaStokesCompletedRenormalizedTrace_eq
    {d : ℝ} (hd : 0 < d) :
    routePPrimitiveGammaJuliaStokesCompletedRenormalizedTrace d =
      gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent d := by
  rw [routePPrimitiveGammaJuliaStokesCompletedRenormalizedTrace,
    tsum_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd]
  exact
    (gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent_eq_firstTrace_add_counter
      d hd.ne').symm

/-- Exact polar cancellation gives zero right-wall limit after source transport. -/
theorem tendsto_routePPrimitiveGammaJuliaStokesCompletedRenormalizedTrace :
    Tendsto routePPrimitiveGammaJuliaStokesCompletedRenormalizedTrace
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine
    tendsto_gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent_nhdsGT_zero.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with d hd
  exact (routePPrimitiveGammaJuliaStokesCompletedRenormalizedTrace_eq hd).symm

/-- **P-G105I capstone.** The P-G105H singular face has an exact positive diagonal transport to
the literal Stokes current; every actual finite matrix has the corresponding trace, the remaining
depths are summable, and the source-derived polar channel cancels the wall residue. -/
theorem routePPrimitive_GammaJulia_StokesApertureResidueTransport :
    (∀ (d : ℝ), 0 < d → ∀ p : Nat.Primes,
      routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p =
        gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm d p) ∧
    Summable routePPrimitiveGammaJuliaLogCofinalTraceRegularTailWeight ∧
    (∀ (N : ℕ) (d : ℝ), 0 < d →
      ∀ (p : Fin N → Nat.Primes) (kappa : Fin N → ℝ),
        (routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram
          d p kappa).trace.re =
          ∑ i, routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d (p i)) ∧
    Tendsto routePPrimitiveGammaJuliaStokesCompletedRenormalizedTrace
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  exact ⟨fun _ hd p =>
      routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_eq hd p,
    summable_routePPrimitiveGammaJuliaLogCofinalTraceRegularTailWeight,
    fun _ _ hd p kappa =>
      routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram_trace hd p kappa,
    tendsto_routePPrimitiveGammaJuliaStokesCompletedRenormalizedTrace⟩

end

end RHTower
