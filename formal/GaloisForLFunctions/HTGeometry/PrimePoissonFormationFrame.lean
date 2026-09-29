import GaloisForLFunctions.HTGeometry.PrimeClockGammaTotality
import GaloisForLFunctions.HTGeometry.SquareSummableFrameSynthesis
import GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearDefect
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaPhysicalStokesStableSpecialization

/-!
# The prime–Poisson formation frame

Fix an aperture `d > 0`, put `t_p = log p`, `u_d(p)` for the transported Stokes prime weight,
`U_d = ∑ u_d` and `μ_d = u_d/U_d`.

* **(PPTI-B)** The cofinal Stokes child kernel is Poisson degree three:
  `K_d(p,q) = √(u_d(p) u_d(q)) ⟨ψ_{t_p}^{(3)}, ψ_{t_q}^{(3)}⟩`, so
  `A_d(p,q) = K_d(p,q)/U_d = √(μ_d(p)μ_d(q)) ⟨ψ^{(3)}, ψ^{(3)}⟩` and
  `|K_d|²/(u_d u_d) = poissonScaleHistoryGram(t_p,t_q)³`.
* The frame `W_d^{(k)} e_p = √μ_d(p) ψ_{t_p}^{(k)}` is Hilbert–Schmidt of norm one; `A_d = W*W` is
  positive with `Tr A_d = ‖A_d‖₁ = 1`.
* **(PPTI-C)** The channel `Q_d e_{(n,p)} = √(w_n μ_d(p)) e_n ⊗ ψ_{t_p}^{(3)}` into `ℓ²(ℕ; H)` is
  Hilbert–Schmidt of norm one and `Q_d* Q_d` is exactly the prime–Hodge integral–nuclear defect.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

section Law

variable {d : ℝ}

/-- The normalized prime formation law `μ_d(p) = u_d(p)/U_d`. -/
def primeFormationLaw (d : ℝ) (p : Nat.Primes) : ℝ :=
  routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p /
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d

theorem primeFormationLaw_pos (hd : 0 < d) (p : Nat.Primes) : 0 < primeFormationLaw d p :=
  div_pos (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_pos hd p)
    (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd)

theorem hasSum_primeFormationLaw (hd : 0 < d) : HasSum (primeFormationLaw d) 1 := by
  have h := (summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd).hasSum.div_const
    (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)
  rwa [tsum_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd,
    div_self (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd).ne'] at h

/-- The frame vector `√μ_d(p) ψ_{log p}^{(k)}`. -/
def primeCoherentFrame (k : ℕ) [NeZero k] (d : ℝ) (p : Nat.Primes) : HalfLineL2 :=
  ((Real.sqrt (primeFormationLaw d p) : ℝ) : ℂ) • gammaCoherentVector k (primeClock_pos p)

theorem norm_sq_primeCoherentFrame (k : ℕ) [NeZero k] (hd : 0 < d) (p : Nat.Primes) :
    ‖primeCoherentFrame k d p‖ ^ 2 = primeFormationLaw d p := by
  rw [primeCoherentFrame, norm_smul, norm_gammaCoherentVector, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (primeFormationLaw_pos hd p).le]

theorem summable_norm_sq_primeCoherentFrame (k : ℕ) [NeZero k] (hd : 0 < d) :
    Summable fun p => ‖primeCoherentFrame k d p‖ ^ 2 := by
  simp_rw [norm_sq_primeCoherentFrame k hd]
  exact (hasSum_primeFormationLaw hd).summable

theorem tsum_norm_sq_primeCoherentFrame (k : ℕ) [NeZero k] (hd : 0 < d) :
    ∑' p, ‖primeCoherentFrame k d p‖ ^ 2 = 1 := by
  simp_rw [norm_sq_primeCoherentFrame k hd]
  exact (hasSum_primeFormationLaw hd).tsum_eq

/-- The prime formation frame `W_d^{(k)} : ℓ²(Primes) → H`. -/
def primeCoherentSynthesis (k : ℕ) [NeZero k] (hd : 0 < d) :
    lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ] HalfLineL2 :=
  squareSummableSynthesis (primeCoherentFrame k d) (summable_norm_sq_primeCoherentFrame k hd)

theorem primeCoherentSynthesis_single (k : ℕ) [NeZero k] (hd : 0 < d) (p : Nat.Primes) :
    primeCoherentSynthesis k hd (lp.single 2 p 1) = primeCoherentFrame k d p := by
  rw [primeCoherentSynthesis, squareSummableSynthesis_single, one_smul]

theorem hsNormSq_primeCoherentSynthesis (k : ℕ) [NeZero k] (hd : 0 < d) :
    ContinuousLinearMap.hsNormSq (primeCoherentSynthesis k hd) = 1 := by
  rw [primeCoherentSynthesis, hsNormSq_squareSummableSynthesis,
    tsum_norm_sq_primeCoherentFrame k hd]

theorem inner_primeCoherentFrame (k : ℕ) [NeZero k] (p q : Nat.Primes) :
    ⟪primeCoherentFrame k d p, primeCoherentFrame k d q⟫_ℂ =
      ((Real.sqrt (primeFormationLaw d p) * Real.sqrt (primeFormationLaw d q) *
        (2 * Real.sqrt (Real.log p * Real.log q) / (Real.log p + Real.log q)) ^ k : ℝ) : ℂ) := by
  rw [primeCoherentFrame, primeCoherentFrame, inner_smul_left, inner_smul_right,
    inner_gammaCoherentVector, Complex.conj_ofReal]
  push_cast
  ring

end Law

/-! ## Theorem B: the source kernel is Poisson degree three -/

section KernelIdentity

variable {d : ℝ}

theorem routePBaseCauchyCubicKernel_one_zero (a b : ℝ) :
    routePBaseCauchyCubicKernel 1 a b 0 = 2 / (((a + b : ℝ)) : ℂ) ^ 3 := by
  rw [routePBaseCauchyCubicKernel, routePCollisionPairFrequency]
  push_cast
  ring

theorem finiteVonMangoldtDepthOneAmplitude_prime_zero (p : Nat.Primes) :
    finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (p, 0)) =
      ((Real.sqrt (Real.log p) / Real.sqrt p : ℝ) : ℂ) := by
  rw [finiteVonMangoldtDepthOneAmplitude, xiGammaEulerValuationNat, zero_add, pow_one,
    ArithmeticFunction.vonMangoldt_apply_prime p.2, Real.sqrt_div' _ (by positivity)]

theorem transportedPrimeWeight_eq_scale (p : Nat.Primes) :
    routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p =
      routePPrimitiveGammaJuliaStokesApertureScaleSq d p / (4 * p) := by
  rw [routePPrimitiveGammaJuliaStokesTransportedPrimeWeight,
    routePPrimitiveGammaJuliaLogCofinalTraceWeight_prime_zero]
  ring

/-- **Theorem PPTI-B (PPTI.9).**  `K_d(p,q) = √(u_d(p) u_d(q)) ⟨ψ_{t_p}^{(3)}, ψ_{t_q}^{(3)}⟩`. -/
theorem cofinalChildKernel_eq_coherent (hd : 0 < d) (p q : Nat.Primes) :
    routePPrimitiveGammaJuliaStokesCofinalChildKernel d (p, q) =
      ((Real.sqrt (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p *
        routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d q) : ℝ) : ℂ) *
        ⟪gammaCoherentVector 3 (primeClock_pos p), gammaCoherentVector 3 (primeClock_pos q)⟫_ℂ := by
  rw [inner_gammaCoherentVector, routePPrimitiveGammaJuliaStokesCofinalChildKernel]
  simp only
  rw [xiGammaEulerPrimitiveLogFrequency_prime_zero, xiGammaEulerPrimitiveLogFrequency_prime_zero,
    routePBaseCauchyCubicKernel_one_zero, finiteVonMangoldtDepthOneAmplitude_prime_zero,
    finiteVonMangoldtDepthOneAmplitude_prime_zero, transportedPrimeWeight_eq_scale,
    transportedPrimeWeight_eq_scale]
  have hsp := routePPrimitiveGammaJuliaStokesApertureScaleSq_pos hd p
  have hsq := routePPrimitiveGammaJuliaStokesApertureScaleSq_pos hd q
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hq : (0 : ℝ) < q := by exact_mod_cast q.2.pos
  have hlp := primeClock_pos p
  have hlq := primeClock_pos q
  set a := Real.sqrt (routePPrimitiveGammaJuliaStokesApertureScaleSq d p)
  set b := Real.sqrt (routePPrimitiveGammaJuliaStokesApertureScaleSq d q)
  set x := Real.sqrt (Real.log p)
  set y := Real.sqrt (Real.log q)
  set P := Real.sqrt p
  set Q := Real.sqrt q
  have ha : a ^ 2 = routePPrimitiveGammaJuliaStokesApertureScaleSq d p := Real.sq_sqrt hsp.le
  have hb : b ^ 2 = routePPrimitiveGammaJuliaStokesApertureScaleSq d q := Real.sq_sqrt hsq.le
  have hx : x ^ 2 = Real.log p := Real.sq_sqrt hlp.le
  have hy : y ^ 2 = Real.log q := Real.sq_sqrt hlq.le
  have hP : P ^ 2 = p := Real.sq_sqrt hp.le
  have hQ : Q ^ 2 = q := Real.sq_sqrt hq.le
  have hxpos : 0 < x := Real.sqrt_pos.2 hlp
  have hypos : 0 < y := Real.sqrt_pos.2 hlq
  have hPpos : 0 < P := Real.sqrt_pos.2 hp
  have hQpos : 0 < Q := Real.sqrt_pos.2 hq
  have hapos : 0 < a := Real.sqrt_pos.2 hsp
  have hbpos : 0 < b := Real.sqrt_pos.2 hsq
  have hroot : Real.sqrt (routePPrimitiveGammaJuliaStokesApertureScaleSq d p / (4 * p) *
      (routePPrimitiveGammaJuliaStokesApertureScaleSq d q / (4 * q))) = a * b / (4 * P * Q) := by
    rw [← ha, ← hb, ← hP, ← hQ, show a ^ 2 / (4 * P ^ 2) * (b ^ 2 / (4 * Q ^ 2)) =
      (a * b / (4 * P * Q)) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  have hxy : Real.sqrt (Real.log p * Real.log q) = x * y := Real.sqrt_mul hlp.le _
  rw [hroot, hxy, ← hx, ← hy]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [← hP, ← hQ] at *
  push_cast
  field_simp
  ring

/-- **(PPTI.10).**  `A_d(p,q) = √(μ_d(p)μ_d(q)) ⟨ψ^{(3)}, ψ^{(3)}⟩ = ⟨v_p, v_q⟩`. -/
theorem normalizedStokesPrimeKernel_eq_frame (hd : 0 < d) (p q : Nat.Primes) :
    normalizedStokesPrimeKernel d (p, q) =
      ⟪primeCoherentFrame 3 d p, primeCoherentFrame 3 d q⟫_ℂ := by
  have hU := gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd
  have hup := routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_pos hd p
  have huq := routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_pos hd q
  rw [normalizedStokesPrimeKernel, cofinalChildKernel_eq_coherent hd, primeCoherentFrame,
    primeCoherentFrame, inner_smul_left, inner_smul_right, Complex.conj_ofReal, primeFormationLaw,
    primeFormationLaw, Real.sqrt_div' _ hU.le, Real.sqrt_div' _ hU.le, Real.sqrt_mul hup.le]
  have hsU : 0 < Real.sqrt (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d) :=
    Real.sqrt_pos.2 hU
  have hU2 : (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ) =
      ((Real.sqrt (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d) : ℝ) : ℂ) *
        ((Real.sqrt (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hU.le]
  rw [hU2]
  have hsU' : ((Real.sqrt (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d) : ℝ) : ℂ) ≠
      0 := Complex.ofReal_ne_zero.mpr hsU.ne'
  push_cast
  field_simp

/-- **(PPTI.11).**  `|K_d(p,q)|²/(u_d(p) u_d(q)) = poissonScaleHistoryGram(t_p, t_q)³`. -/
theorem normSq_cofinalChildKernel_div (hd : 0 < d) (p q : Nat.Primes) :
    Complex.normSq (routePPrimitiveGammaJuliaStokesCofinalChildKernel d (p, q)) /
        (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p *
          routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d q) =
      poissonScaleHistoryGram (Real.log p) (Real.log q) ^ 3 := by
  have hup := routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_pos hd p
  have huq := routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_pos hd q
  rw [cofinalChildKernel_eq_coherent hd, inner_gammaCoherentVector, ← Complex.ofReal_mul,
    Complex.normSq_ofReal, poissonScaleHistoryGram_eq_coherent (primeClock_pos p)
      (primeClock_pos q)]
  field_simp
  rw [Real.sq_sqrt (mul_pos hup huq).le]

end KernelIdentity

/-! ## The prime organ and the history channel -/

section Organs

variable {d : ℝ} (hd : 0 < d)
include hd

/-- **(PPTI.15).**  `A_d = W*W` has the normalized Stokes child matrix, is positive and has
`Tr A_d = ‖A_d‖₁ = 1`. -/
theorem primeFormationGram_properties :
    (∀ p q : Nat.Primes, ⟪(lp.single 2 p (1 : ℂ) : lp (fun _ : Nat.Primes => ℂ) 2),
        (ContinuousLinearMap.adjoint (primeCoherentSynthesis 3 hd) ∘L primeCoherentSynthesis 3 hd)
          (lp.single 2 q 1)⟫_ℂ = normalizedStokesPrimeKernel d (p, q)) ∧
      (ContinuousLinearMap.adjoint (primeCoherentSynthesis 3 hd) ∘L
        primeCoherentSynthesis 3 hd).IsPositive ∧
      MemSchattenClass 1 (ContinuousLinearMap.adjoint (primeCoherentSynthesis 3 hd) ∘L
        primeCoherentSynthesis 3 hd) ∧
      (ContinuousLinearMap.adjoint (primeCoherentSynthesis 3 hd) ∘L
        primeCoherentSynthesis 3 hd).opTrace = 1 ∧
      traceNorm (lp (fun _ : Nat.Primes => ℂ) 2)
        (ContinuousLinearMap.adjoint (primeCoherentSynthesis 3 hd) ∘L
          primeCoherentSynthesis 3 hd) = 1 := by
  obtain ⟨hpos, hS, htr⟩ := rightGram_traceClass (summable_norm_sq_primeCoherentFrame 3 hd)
  rw [tsum_norm_sq_primeCoherentFrame 3 hd, Complex.ofReal_one] at htr
  refine ⟨fun p q => ?_, hpos, hS, htr, ?_⟩
  · rw [primeCoherentSynthesis, inner_single_rightGram_single,
      normalizedStokesPrimeKernel_eq_frame hd]
  · have h := traceNorm_eq_re_opTrace_of_isPositive hS hpos
    rw [htr, Complex.one_re] at h
    exact h

/-- The history–prime frame vector `√(w_n μ_d(p)) e_n ⊗ ψ_{log p}^{(3)}`. -/
def historyPrimeFrame (d : ℝ) (np : ℕ × Nat.Primes) : lp (fun _ : ℕ => HalfLineL2) 2 :=
  ((Real.sqrt (PrimeHodgeHistory.w np.1 * primeFormationLaw d np.2) : ℝ) : ℂ) •
    lp.single 2 np.1 (gammaCoherentVector 3 (primeClock_pos np.2))

omit hd in
theorem norm_sq_historyPrimeFrame (hd : 0 < d) (np : ℕ × Nat.Primes) :
    ‖historyPrimeFrame d np‖ ^ 2 = PrimeHodgeHistory.w np.1 * primeFormationLaw d np.2 := by
  rw [historyPrimeFrame, norm_smul, lp.norm_single (by norm_num), norm_gammaCoherentVector, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (mul_pos (PrimeHodgeHistory.w_pos _) (primeFormationLaw_pos hd _)).le]

omit hd in
theorem summable_norm_sq_historyPrimeFrame (hd : 0 < d) :
    Summable fun np : ℕ × Nat.Primes => ‖historyPrimeFrame d np‖ ^ 2 := by
  simp_rw [norm_sq_historyPrimeFrame hd]
  exact summable_mul_of_summable_norm (f := PrimeHodgeHistory.w) (g := primeFormationLaw d)
    (by simpa [Real.norm_of_nonneg (PrimeHodgeHistory.w_pos _).le] using
      PrimeHodgeHistory.summable_w)
    (by simpa [Real.norm_of_nonneg (primeFormationLaw_pos hd _).le] using
      (hasSum_primeFormationLaw hd).summable)

/-- **(PPTI.17).**  The formation channel `Q_d = Φ^{1/2} ⊗ W_d^{(3)}`. -/
def historyFormationChannel :
    PrimeHodgeHistoryHilbert →L[ℂ] lp (fun _ : ℕ => HalfLineL2) 2 :=
  squareSummableSynthesis (historyPrimeFrame d) (summable_norm_sq_historyPrimeFrame hd)

theorem inner_historyPrimeFrame (a b : ℕ × Nat.Primes) :
    ⟪historyPrimeFrame d a, historyPrimeFrame d b⟫_ℂ = primeHodgeHistoryDefectKernel d (a, b) := by
  obtain ⟨n, p⟩ := a
  obtain ⟨m, q⟩ := b
  rw [historyPrimeFrame, historyPrimeFrame, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    lp.inner_single_left, primeHodgeHistoryDefectKernel]
  simp only
  by_cases h : n = m
  · subst h
    rw [lp.single_apply_self, if_pos rfl, normalizedStokesPrimeKernel_eq_frame hd,
      primeCoherentFrame, primeCoherentFrame, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal,
      Real.sqrt_mul (PrimeHodgeHistory.w_pos n).le, Real.sqrt_mul (PrimeHodgeHistory.w_pos n).le]
    have hw := Real.mul_self_sqrt (PrimeHodgeHistory.w_pos n).le
    push_cast
    rw [show ((Real.sqrt (PrimeHodgeHistory.w n) : ℂ) * (Real.sqrt (primeFormationLaw d p) : ℂ)) *
        ((Real.sqrt (PrimeHodgeHistory.w n) : ℂ) * (Real.sqrt (primeFormationLaw d q) : ℂ) *
          ⟪gammaCoherentVector 3 (primeClock_pos p), gammaCoherentVector 3 (primeClock_pos q)⟫_ℂ) =
      ((Real.sqrt (PrimeHodgeHistory.w n) * Real.sqrt (PrimeHodgeHistory.w n) : ℝ) : ℂ) *
        ((Real.sqrt (primeFormationLaw d p) : ℂ) * ((Real.sqrt (primeFormationLaw d q) : ℂ) *
          ⟪gammaCoherentVector 3 (primeClock_pos p), gammaCoherentVector 3 (primeClock_pos q)⟫_ℂ))
      by push_cast; ring, hw]
  · rw [lp.single_apply_ne _ _ _ h, if_neg h, inner_zero_right, mul_zero, mul_zero]

/-- **Theorem PPTI-C (PPTI.19)–(PPTI.20).**  `Q_d* Q_d` is the prime–Hodge integral–nuclear
defect. -/
theorem adjoint_comp_historyFormationChannel :
    ContinuousLinearMap.adjoint (historyFormationChannel hd) ∘L historyFormationChannel hd =
      primeHodgeHistoryDefectOperator hd := by
  refine ext_of_inner_single fun a b => ?_
  rw [historyFormationChannel, inner_single_rightGram_single, inner_historyPrimeFrame hd,
    primeHodgeHistoryDefectOperator, lp.inner_single_left, HilbertSchmidt.toOperator_single]
  simp

/-- `‖Q_d‖²_HS = Tr Φ · Tr A_d = 1`. -/
theorem hsNormSq_historyFormationChannel :
    ContinuousLinearMap.hsNormSq (historyFormationChannel hd) = 1 := by
  rw [historyFormationChannel, hsNormSq_squareSummableSynthesis]
  simp_rw [norm_sq_historyPrimeFrame hd]
  rw [tsum_mul_tsum_of_summable_norm (f := PrimeHodgeHistory.w) (g := primeFormationLaw d)
    (by simpa [Real.norm_of_nonneg (PrimeHodgeHistory.w_pos _).le] using
      PrimeHodgeHistory.summable_w)
    (by simpa [Real.norm_of_nonneg (primeFormationLaw_pos hd _).le] using
      (hasSum_primeFormationLaw hd).summable) |>.symm,
    PrimeHodgeHistory.tsum_w, (hasSum_primeFormationLaw hd).tsum_eq, mul_one]

end Organs

end GaloisForLFunctions.HTGeometry
