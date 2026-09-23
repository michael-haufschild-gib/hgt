import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaPhysicalStokesStableSpecialization
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace

/-!
# Route P primitive Gamma--Julia cofinal Stokes child kernel

P-G105J proves stability only on finite aperture-transported P-G186 packets.  This file constructs
their single cofinal prime kernel without deleting any Cauchy off-diagonal incidence.  At zero
ordinate it is the literal depth-zero P-G186 Burnol Gram after prime-log and aperture diagonal
congruences.

For transported diagonal weight `w_d(p)`, its exact Schur law is

```text
‖K_d(p,q)‖² = w_d(p) w_d(q)
  * 64 log(p)^(3 : ℕ) log(q)^(3 : ℕ) / (log(p)+log(q))^(6 : ℕ).
```

The last factor is at most one.  Since `w_d` is summable for every `d>0`, the full double kernel is
Hilbert--Schmidt.  Its diagonal is exactly `w_d`; hence its cofinal diagonal sum is the literal
oriented Stokes first-trace current.  Every finite pullback is definitionally the actual matrix
from P-G105I, and the global kernel is Hermitian, so its represented Hilbert--Schmidt operator is
self-adjoint.

This closes the cofinal child-operator existence gate while retaining all source incidence.  The
polar channel, trace-restored determinant, cofinal stability, and Xi divisor identification remain
separate gates.
-/

open Complex Matrix Filter Topology Set
open scoped Kronecker ComplexOrder BigOperators

namespace RHTower

noncomputable section

/-- Full zero-ordinate aperture-transported P-G186 kernel on the cofinal prime carrier. -/
def routePPrimitiveGammaJuliaStokesCofinalChildKernel
    (d : ℝ) (pq : Nat.Primes × Nat.Primes) : ℂ :=
  let p := pq.1
  let q := pq.2
  (Real.sqrt (routePPrimitiveGammaJuliaStokesApertureScaleSq d p) : ℂ) *
    (Real.log (p : ℝ) : ℂ) *
      (finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (p, 0)) *
        routePBaseCauchyCubicKernel 1
          (xiGammaEulerPrimitiveLogFrequency (p, 0))
          (xiGammaEulerPrimitiveLogFrequency (q, 0)) 0 *
        star (finiteVonMangoldtDepthOneAmplitude
          (xiGammaEulerValuationNat (q, 0)))) *
    (Real.log (q : ℝ) : ℂ) *
  (Real.sqrt (routePPrimitiveGammaJuliaStokesApertureScaleSq d q) : ℂ)

theorem xiGammaEulerPrimitiveLogFrequency_prime_zero (p : Nat.Primes) :
    xiGammaEulerPrimitiveLogFrequency (p, 0) = Real.log (p : ℝ) := by
  simp [xiGammaEulerPrimitiveLogFrequency, xiGammaEulerValuationNat]

theorem finiteVonMangoldtDepthOneAmplitude_sq_prime_zero (p : Nat.Primes) :
    finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (p, 0)) ^ (2 : ℕ) =
      ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) := by
  have hn : xiGammaEulerValuationNat (p, 0) ≠ 0 := by
    simpa [xiGammaEulerValuationNat] using p.property.ne_zero
  rw [finiteVonMangoldtDepthOneAmplitude_sq hn,
    finiteVonMangoldtWeight, LSeries.term_of_ne_zero hn]
  simp [xiGammaEulerValuationNat,
    ArithmeticFunction.vonMangoldt_apply_prime p.property]

theorem normSq_finiteVonMangoldtDepthOneAmplitude_prime_zero (p : Nat.Primes) :
    Complex.normSq
      (finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (p, 0))) =
        Real.log (p : ℝ) / (p : ℝ) := by
  rw [finiteVonMangoldtDepthOneAmplitude, Complex.normSq_ofReal]
  have hp : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt
      (xiGammaEulerValuationNat (p, 0)) /
        (xiGammaEulerValuationNat (p, 0) : ℝ) := by positivity
  rw [Real.mul_self_sqrt hp]
  simp [xiGammaEulerValuationNat,
    ArithmeticFunction.vonMangoldt_apply_prime p.property]

private theorem normSq_star (z : ℂ) : Complex.normSq (star z) = Complex.normSq z := by
  change Complex.normSq ((starRingEnd ℂ) z) = Complex.normSq z
  exact Complex.normSq_conj z

/-- Exact sharp Schur law for every cofinal child-kernel entry. -/
theorem normSq_routePPrimitiveGammaJuliaStokesCofinalChildKernel
    {d : ℝ} (hd : 0 < d) (p q : Nat.Primes) :
    Complex.normSq
        (routePPrimitiveGammaJuliaStokesCofinalChildKernel d (p, q)) =
      routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p *
        routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d q *
          routePBaseCauchyCubicNormalizedCoherenceSq
            (Real.log (p : ℝ)) (Real.log (q : ℝ)) 0 := by
  rw [routePPrimitiveGammaJuliaStokesCofinalChildKernel]
  simp only [Complex.normSq_mul, Complex.normSq_ofReal]
  rw [xiGammaEulerPrimitiveLogFrequency_prime_zero,
    xiGammaEulerPrimitiveLogFrequency_prime_zero,
    normSq_routePBaseCauchyCubicKernel
      (Real.log_pos (by exact_mod_cast p.property.one_lt))
      (Real.log_pos (by exact_mod_cast q.property.one_lt))]
  rw [normSq_finiteVonMangoldtDepthOneAmplitude_prime_zero,
    normSq_star, normSq_finiteVonMangoldtDepthOneAmplitude_prime_zero]
  rw [Real.mul_self_sqrt
      (routePPrimitiveGammaJuliaStokesApertureScaleSq_pos hd p).le,
    Real.mul_self_sqrt
      (routePPrimitiveGammaJuliaStokesApertureScaleSq_pos hd q).le]
  rw [routePPrimitiveGammaJuliaStokesTransportedPrimeWeight,
    routePPrimitiveGammaJuliaStokesTransportedPrimeWeight,
    routePPrimitiveGammaJuliaLogCofinalTraceWeight_prime_zero,
    routePPrimitiveGammaJuliaLogCofinalTraceWeight_prime_zero,
    routePBaseCauchyCubicNormalizedCoherenceSq]
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have hq : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.property.pos
  have hlp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hlq : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast q.property.one_lt)
  field_simp [hp.ne', hq.ne', hlp.ne', hlq.ne']
  ring

/-- Equal-ordinate normalized cubic coherence never exceeds one. -/
theorem routePBaseCauchyCubicNormalizedCoherenceSq_primeLog_zero_le_one
    (p q : Nat.Primes) :
    routePBaseCauchyCubicNormalizedCoherenceSq
      (Real.log (p : ℝ)) (Real.log (q : ℝ)) 0 ≤ 1 := by
  have hp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hq : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast q.property.one_lt)
  by_cases h : Real.log (p : ℝ) = Real.log (q : ℝ)
  · rw [h]
    unfold routePBaseCauchyCubicNormalizedCoherenceSq
    field_simp [hq.ne']
    ring_nf
    exact le_refl _
  · exact (routePBaseCauchyCubicNormalizedCoherenceSq_lt_one hp hq
      (Or.inl h)).le

theorem routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_nonneg
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    0 ≤ routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p := by
  rw [routePPrimitiveGammaJuliaStokesTransportedPrimeWeight]
  exact (mul_pos
    (routePPrimitiveGammaJuliaStokesApertureScaleSq_pos hd p)
    (by
      rw [routePPrimitiveGammaJuliaLogCofinalTraceWeight_prime_zero]
      have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
      positivity)).le

/-- Sharp product-diagonal majorant retaining the complete off-diagonal kernel. -/
theorem norm_sq_routePPrimitiveGammaJuliaStokesCofinalChildKernel_le
    {d : ℝ} (hd : 0 < d) (pq : Nat.Primes × Nat.Primes) :
    ‖routePPrimitiveGammaJuliaStokesCofinalChildKernel d pq‖ ^ (2 : ℕ) ≤
      routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d pq.1 *
        routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d pq.2 := by
  rw [Complex.sq_norm,
    normSq_routePPrimitiveGammaJuliaStokesCofinalChildKernel hd]
  exact mul_le_of_le_one_right
    (mul_nonneg
      (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_nonneg hd _)
      (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_nonneg hd _))
    (routePBaseCauchyCubicNormalizedCoherenceSq_primeLog_zero_le_one _ _)

/-- Full cofinal child kernel is Hilbert--Schmidt at every positive aperture. -/
theorem routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS
    {d : ℝ} (hd : 0 < d) :
    HilbertSchmidt.IsHS
      (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) := by
  rw [HilbertSchmidt.IsHS]
  refine Summable.of_nonneg_of_le (fun pq => sq_nonneg _)
    (fun pq =>
      norm_sq_routePPrimitiveGammaJuliaStokesCofinalChildKernel_le hd pq) ?_
  have hw := summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd
  exact summable_mul_of_summable_norm hw.norm hw.norm

/-- Every finite pullback is entrywise the actual P-G105I matrix at zero ordinate. -/
theorem routePPrimitiveGammaJuliaStokesCofinalChildKernel_eq_actual_apply
    {N : ℕ} (d : ℝ) (p : Fin N → Nat.Primes) (i j : Fin N) :
    routePPrimitiveGammaJuliaStokesCofinalChildKernel d (p i, p j) =
      routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram
        d p (fun _ => 0) i j := by
  rw [routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram,
    routePPrimitiveGammaJuliaStokesApertureDiagonal,
    Matrix.mul_diagonal, Matrix.diagonal_mul,
    routePPrimitiveJointDepthPrimeLogConjugate_apply,
    routePPrimitiveBurnolWindowGramMatrix_eq_baseCauchy,
    routePPrimitiveBaseCauchyCubicKernelMatrix_apply]
  simp only [sub_self]
  rw [routePPrimitiveGammaJuliaStokesCofinalChildKernel]
  ring

theorem routePPrimitiveGammaJuliaStokesCofinalChildKernel_matrix_eq_actual
    {N : ℕ} (d : ℝ) (p : Fin N → Nat.Primes) :
    (fun i j =>
      routePPrimitiveGammaJuliaStokesCofinalChildKernel d (p i, p j)) =
      routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram
        d p (fun _ => 0) := by
  ext i j
  exact
    routePPrimitiveGammaJuliaStokesCofinalChildKernel_eq_actual_apply d p i j

/-- The cofinal kernel diagonal is exactly the transported Stokes prime weight. -/
theorem routePPrimitiveGammaJuliaStokesCofinalChildKernel_diagonal
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    routePPrimitiveGammaJuliaStokesCofinalChildKernel d (p, p) =
      (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p : ℂ) := by
  let f : Fin 1 → Nat.Primes := fun _ => p
  have htrace :=
    routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram_trace
      hd f (fun _ => 0)
  have happ :=
    routePPrimitiveGammaJuliaStokesCofinalChildKernel_eq_actual_apply
      d f (0 : Fin 1) (0 : Fin 1)
  have hentry :
      (routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram
        d f (fun _ => 0) 0 0).re =
        routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p := by
    simpa [Matrix.trace, f] using htrace
  have hre :
      (routePPrimitiveGammaJuliaStokesCofinalChildKernel d (p, p)).re =
        routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p := by
    rw [happ]
    simpa [f] using hentry
  have him :
      (routePPrimitiveGammaJuliaStokesCofinalChildKernel d (p, p)).im = 0 := by
    have hherm :=
      (routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram_posSemidef
        d f (fun _ => 0)).isHermitian
    rw [Matrix.IsHermitian] at hherm
    have hstar := congrArg
      (fun M : Matrix (Fin 1) (Fin 1) ℂ =>
        M (0 : Fin 1) (0 : Fin 1)) hherm
    have hstar' :
        star (routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram
          d f (fun _ => 0) (0 : Fin 1) (0 : Fin 1)) =
        routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram
          d f (fun _ => 0) (0 : Fin 1) (0 : Fin 1) := by
      simpa only [Matrix.conjTranspose_apply] using hstar
    have himentry :
        (routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram
          d f (fun _ => 0) 0 0).im = 0 := by
      have himEq := congrArg Complex.im hstar'
      change -((routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram
        d f (fun _ => 0) 0 0).im) =
          (routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram
            d f (fun _ => 0) 0 0).im at himEq
      linarith
    rw [happ]
    simpa [f] using himentry
  apply Complex.ext
  · simpa using hre
  · simpa using him

theorem summable_routePPrimitiveGammaJuliaStokesCofinalChildKernel_diagonal
    {d : ℝ} (hd : 0 < d) :
    Summable (fun p : Nat.Primes =>
      routePPrimitiveGammaJuliaStokesCofinalChildKernel d (p, p)) := by
  exact (Complex.summable_ofReal.mpr
    (summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd)).congr
      (fun p =>
        (routePPrimitiveGammaJuliaStokesCofinalChildKernel_diagonal hd p).symm)

/-- Cofinal child trace is the literal oriented Stokes first-trace current. -/
theorem tsum_routePPrimitiveGammaJuliaStokesCofinalChildKernel_diagonal
    {d : ℝ} (hd : 0 < d) :
    (∑' p : Nat.Primes,
      routePPrimitiveGammaJuliaStokesCofinalChildKernel d (p, p)) =
      (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ) := by
  rw [tsum_congr
    (routePPrimitiveGammaJuliaStokesCofinalChildKernel_diagonal hd)]
  rw [← Complex.ofReal_tsum,
    tsum_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd]

/-- Cofinal child kernel is Hermitian, inherited from its actual two-prime P-G186 pullbacks. -/
theorem routePPrimitiveGammaJuliaStokesCofinalChildKernel_hsAdjoint
    (d : ℝ) :
    HilbertSchmidt.hsAdjoint
      (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) =
        routePPrimitiveGammaJuliaStokesCofinalChildKernel d := by
  funext pq
  let f : Fin 2 → Nat.Primes := ![pq.1, pq.2]
  let M := routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram
    d f (fun _ => 0)
  have hherm :=
    (routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram_posSemidef
      d f (fun _ => 0)).isHermitian
  rw [Matrix.IsHermitian] at hherm
  have hentry := congrArg
    (fun A : Matrix (Fin 2) (Fin 2) ℂ => A (0 : Fin 2) (1 : Fin 2)) hherm
  have hstar : star (M 1 0) = M 0 1 := by
    simpa only [Matrix.conjTranspose_apply] using hentry
  have h10 :=
    routePPrimitiveGammaJuliaStokesCofinalChildKernel_eq_actual_apply
      d f (1 : Fin 2) (0 : Fin 2)
  have h01 :=
    routePPrimitiveGammaJuliaStokesCofinalChildKernel_eq_actual_apply
      d f (0 : Fin 2) (1 : Fin 2)
  rw [HilbertSchmidt.hsAdjoint]
  change star
      (routePPrimitiveGammaJuliaStokesCofinalChildKernel d (pq.2, pq.1)) =
    routePPrimitiveGammaJuliaStokesCofinalChildKernel d (pq.1, pq.2)
  rw [show routePPrimitiveGammaJuliaStokesCofinalChildKernel d (pq.2, pq.1) =
        M 1 0 by simpa [f, M] using h10,
    show routePPrimitiveGammaJuliaStokesCofinalChildKernel d (pq.1, pq.2) =
        M 0 1 by simpa [f, M] using h01]
  exact hstar

/-- Represented cofinal child operator is self-adjoint. -/
theorem routePPrimitiveGammaJuliaStokesCofinalChildOperator_isSelfAdjoint
    {d : ℝ} (hd : 0 < d) :
    IsSelfAdjoint (HilbertSchmidt.toOperator
      (routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd)) := by
  rw [IsSelfAdjoint]
  change ContinuousLinearMap.adjoint
      (HilbertSchmidt.toOperator
        (routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd)) = _
  rw [HilbertSchmidt.adjoint_toOperator]
  exact HilbertSchmidt.toOperator_congr _ _
    (routePPrimitiveGammaJuliaStokesCofinalChildKernel_hsAdjoint d)

/-- **P-G105K capstone.**  Exact finite-source pullback, Hilbert--Schmidt cofinality, literal Stokes
trace, and self-adjointness hold simultaneously at every positive aperture. -/
theorem routePPrimitive_GammaJulia_StokesCofinalChildKernel :
    ∀ (d : ℝ) (hd : 0 < d),
      HilbertSchmidt.IsHS
        (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) ∧
      (∀ (N : ℕ) (p : Fin N → Nat.Primes),
        (fun i j =>
          routePPrimitiveGammaJuliaStokesCofinalChildKernel d (p i, p j)) =
        routePPrimitiveGammaJuliaStokesApertureConjugatedDepthZeroGram
          d p (fun _ => 0)) ∧
      (∑' p : Nat.Primes,
        routePPrimitiveGammaJuliaStokesCofinalChildKernel d (p, p)) =
        (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ) ∧
      IsSelfAdjoint (HilbertSchmidt.toOperator
        (routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd)) := by
  intro d hd
  exact ⟨routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd,
    fun _ p =>
      routePPrimitiveGammaJuliaStokesCofinalChildKernel_matrix_eq_actual d p,
    tsum_routePPrimitiveGammaJuliaStokesCofinalChildKernel_diagonal hd,
    routePPrimitiveGammaJuliaStokesCofinalChildOperator_isSelfAdjoint hd⟩

end

end RHTower
