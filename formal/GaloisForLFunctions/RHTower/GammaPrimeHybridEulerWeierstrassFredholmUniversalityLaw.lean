import GaloisForLFunctions.RHTower.GammaXiHybridWeierstrassFredholmUniversalityLaw
import GaloisForLFunctions.HTGeometry.FredholmDeterminantZeta

/-!
# Gamma--prime hybrid Euler--Weierstrass--Fredholm universality

One diagonal operator joins the archimedean Gamma Weierstrass spectrum to the Euler prime
spectrum.  Its regularized determinant is the product of the reciprocal Gamma factor, reciprocal
Riemann zeta function, and the Hilbert--Carleman exponential of the prime trace.
-/

open Filter Topology
open scoped ENNReal

namespace RHTower

open GaloisForLFunctions HilbertSchmidt

noncomputable section

/-- Disjoint archimedean/Euler spectrum at real scale `sigma`. -/
def gammaPrimeHybridEigenvalue (sigma : ℝ) : ℕ ⊕ Nat.Primes → ℂ
  | Sum.inl n => -(sigma : ℂ) / ((n : ℂ) + 1)
  | Sum.inr p => ((p : ℕ) : ℂ) ^ (-(sigma : ℂ))

/-- Absolute summability of the prime branch in the Euler half-plane. -/
theorem summable_norm_gammaPrimeHybrid_prime
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun p : Nat.Primes =>
      ‖((p : ℕ) : ℂ) ^ (-(sigma : ℂ))‖) := by
  have hnorm :
      ∀ p : Nat.Primes,
        ‖((p : ℕ) : ℂ) ^ (-(sigma : ℂ))‖ =
          ((p : ℕ) : ℝ) ^ (-sigma) := by
    intro p
    rw [show ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast p.2.pos)]
    simp
  simp_rw [hnorm]
  rw [Nat.Primes.summable_rpow]
  linarith

/-- Square summability of the Euler prime branch. -/
theorem summable_normSq_gammaPrimeHybrid_prime
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun p : Nat.Primes =>
      ‖((p : ℕ) : ℂ) ^ (-(sigma : ℂ))‖ ^ 2) := by
  have hsum := summable_norm_gammaPrimeHybrid_prime hsigma
  apply Summable.of_nonneg_of_le (fun p => sq_nonneg _)
    (fun p => ?_) hsum
  have hlt :
      ‖((p : ℕ) : ℂ) ^ (-(sigma : ℂ))‖ < 1 := by
    rw [show ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast p.2.pos)]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.2.one_lt) (by simp; linarith)
  rw [sq]
  exact mul_le_of_le_one_right (norm_nonneg _) hlt.le

/-- The complete archimedean/Euler spectrum is square summable. -/
theorem summable_normSq_gammaPrimeHybridEigenvalue
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun i : ℕ ⊕ Nat.Primes =>
      ‖gammaPrimeHybridEigenvalue sigma i‖ ^ 2) := by
  apply Summable.sum _
  · simpa only [Function.comp_apply, gammaPrimeHybridEigenvalue] using!
      summable_normSq_gammaWeierstrassEigenvalue sigma
  · simpa only [Function.comp_apply, gammaPrimeHybridEigenvalue] using!
      summable_normSq_gammaPrimeHybrid_prime hsigma

/-- Hybrid Gamma/Euler diagonal kernel. -/
def gammaPrimeHybridKernel (sigma : ℝ) :
    (ℕ ⊕ Nat.Primes) × (ℕ ⊕ Nat.Primes) → ℂ :=
  diagMul (gammaPrimeHybridEigenvalue sigma)

theorem gammaPrimeHybridKernel_isHS
    {sigma : ℝ} (hsigma : 1 < sigma) :
    IsHS (gammaPrimeHybridKernel sigma) :=
  isHS_diagMul_infinite _
    (summable_normSq_gammaPrimeHybridEigenvalue hsigma)

/-- Hybrid operator on the square-summable disjoint spectral carrier. -/
def gammaPrimeHybridOperator (sigma : ℝ) (hsigma : 1 < sigma) :
    lp (fun _ : ℕ ⊕ Nat.Primes => ℂ) 2 →L[ℂ]
      lp (fun _ : ℕ ⊕ Nat.Primes => ℂ) 2 :=
  toOperator (gammaPrimeHybridKernel_isHS hsigma)

theorem gammaPrimeHybridOperator_apply
    (sigma : ℝ) (hsigma : 1 < sigma)
    (f : lp (fun _ : ℕ ⊕ Nat.Primes => ℂ) 2)
    (i : ℕ ⊕ Nat.Primes) :
    gammaPrimeHybridOperator sigma hsigma f i =
      gammaPrimeHybridEigenvalue sigma i * f i := by
  rw [gammaPrimeHybridOperator,
    toOperator_apply (gammaPrimeHybridKernel_isHS hsigma),
    tsum_eq_single i]
  · simp [gammaPrimeHybridKernel, diagMul]
  · intro j hji
    simp [gammaPrimeHybridKernel, diagMul, hji.symm]

/-- The hybrid operator is compact throughout the Euler half-plane. -/
theorem gammaPrimeHybridOperator_isCompact
    (sigma : ℝ) (hsigma : 1 < sigma) :
    IsCompactOperator (gammaPrimeHybridOperator sigma hsigma) :=
  (isHilbertSchmidt_toOperator
    (gammaPrimeHybridKernel_isHS hsigma)).isCompactOperator

theorem gammaPrimeHybridEigenvalue_ne_zero
    {sigma : ℝ} (hsigma : 1 < sigma) (i : ℕ ⊕ Nat.Primes) :
    gammaPrimeHybridEigenvalue sigma i ≠ 0 := by
  cases i with
  | inl n =>
      have hsigmaC : (sigma : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hsigma))
      have hnC : (n : ℂ) + 1 ≠ 0 := by
        intro hn
        have hre := congrArg Complex.re hn
        have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        exact hpos.ne' (by simpa using hre)
      exact div_ne_zero (neg_ne_zero.mpr hsigmaC) hnC
  | inr p =>
      change ((p : ℕ) : ℂ) ^ (-(sigma : ℂ)) ≠ 0
      rw [Complex.cpow_ne_zero_iff]
      left
      exact_mod_cast p.2.ne_zero

/-- Every diagonal coordinate is nonzero, so the hybrid operator is injective. -/
theorem gammaPrimeHybridOperator_injective
    (sigma : ℝ) (hsigma : 1 < sigma) :
    Function.Injective (gammaPrimeHybridOperator sigma hsigma) := by
  intro x y hxy
  apply lp.ext
  funext i
  have hi := congrArg
    (fun z : lp (fun _ : ℕ ⊕ Nat.Primes => ℂ) 2 => z i) hxy
  change gammaPrimeHybridOperator sigma hsigma x i =
    gammaPrimeHybridOperator sigma hsigma y i at hi
  rw [gammaPrimeHybridOperator_apply,
    gammaPrimeHybridOperator_apply] at hi
  exact mul_left_cancel₀
    (gammaPrimeHybridEigenvalue_ne_zero hsigma i) hi

theorem gammaPrimeHybridOperator_single_inl
    (sigma : ℝ) (hsigma : 1 < sigma) (n : ℕ) :
    gammaPrimeHybridOperator sigma hsigma
        (lp.single 2 (Sum.inl n : ℕ ⊕ Nat.Primes) 1) =
      (-(sigma : ℂ) / ((n : ℂ) + 1)) •
        lp.single 2 (Sum.inl n : ℕ ⊕ Nat.Primes) 1 := by
  apply lp.ext
  funext i
  rw [gammaPrimeHybridOperator_apply]
  by_cases hi : i = Sum.inl n
  · subst i
    simp [gammaPrimeHybridEigenvalue]
  · simp [gammaPrimeHybridEigenvalue, hi]

/-- Natural-number modes form an approximate unit kernel. -/
theorem gammaPrimeHybridOperator_hasApproximateUnitKernel
    (sigma : ℝ) (hsigma : 1 < sigma) :
    HasApproximateUnitKernel (gammaPrimeHybridOperator sigma hsigma) := by
  refine ⟨fun n => lp.single 2 (Sum.inl n : ℕ ⊕ Nat.Primes) (1 : ℂ), ?_, ?_⟩
  · intro n
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
    norm_num
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have ht :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul |sigma|
    have htzero :
        Tendsto (fun n : ℕ => |sigma| * (1 / ((n : ℝ) + 1)))
          atTop (nhds 0) := by
      simpa using ht
    convert htzero using 1
    funext n
    rw [gammaPrimeHybridOperator_single_inl, norm_smul,
      lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_one, mul_one,
      norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [show ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 by
      rw [show (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnpos]]
    ring

/-- Approximate blindness is exact nonclosedness of the injective hybrid range. -/
theorem gammaPrimeHybridOperator_not_isClosed_range
    (sigma : ℝ) (hsigma : 1 < sigma) :
    ¬ IsClosed (Set.range (gammaPrimeHybridOperator sigma hsigma)) :=
  (hasApproximateUnitKernel_iff_not_isClosed_range
    (gammaPrimeHybridOperator sigma hsigma)
    (gammaPrimeHybridOperator_injective sigma hsigma)).mp
      (gammaPrimeHybridOperator_hasApproximateUnitKernel sigma hsigma)

/-- Both real spectral branches make the Hilbert--Schmidt kernel self-adjoint. -/
theorem hsAdjoint_gammaPrimeHybridKernel_eq
    (sigma : ℝ) :
    hsAdjoint (gammaPrimeHybridKernel sigma) =
      gammaPrimeHybridKernel sigma := by
  funext p
  rcases p with ⟨i, j⟩
  by_cases hij : i = j
  · subst j
    cases i with
    | inl n =>
        simp [hsAdjoint, gammaPrimeHybridKernel, diagMul,
          gammaPrimeHybridEigenvalue]
    | inr p =>
        have hpnonneg : (0 : ℝ) ≤ (p : ℕ) := by positivity
        simp only [hsAdjoint, gammaPrimeHybridKernel, diagMul,
          gammaPrimeHybridEigenvalue, if_pos]
        rw [show (-(sigma : ℂ)) = ((-sigma : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_natCast, ← Complex.ofReal_cpow hpnonneg]
        simp
  · have hji : j ≠ i := Ne.symm hij
    simp [hsAdjoint, gammaPrimeHybridKernel, diagMul, hij, hji]

/-- The hybrid real Euler/archimedean diagonal is self-adjoint unconditionally. -/
theorem gammaPrimeHybridOperator_isSelfAdjoint
    (sigma : ℝ) (hsigma : 1 < sigma) :
    IsSelfAdjoint (gammaPrimeHybridOperator sigma hsigma) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  rw [gammaPrimeHybridOperator,
    adjoint_toOperator (gammaPrimeHybridKernel_isHS hsigma)]
  exact toOperator_congr _ _
    (hsAdjoint_gammaPrimeHybridKernel_eq sigma)

/-- Convergent prime trace appearing in the Hilbert--Carleman correction. -/
def gammaPrimeHybridPrimeTrace (sigma : ℝ) : ℂ :=
  ∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-(sigma : ℂ))

set_option maxHeartbeats 800000 in
/-- The hybrid determinant is the reciprocal Gamma factor times reciprocal zeta times the
exponential prime-trace correction. -/
theorem fredholmDet_gammaPrimeHybridKernel_eq_gamma_mul_zeta_mul_primeTrace
    (sigma : ℝ) (hsigma : 1 < sigma) (r : ℝ)
    (hrHybrid : r * hsNorm (gammaPrimeHybridKernel sigma) < 1)
    (hrPrime :
      r * hsNorm
        (diagMul (fun p : Nat.Primes =>
          ((p : ℕ) : ℂ) ^ (-(sigma : ℂ)))) < 1)
    (hz1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) r) :
    fredholmDet (gammaPrimeHybridKernel sigma) 1 =
      ((sigma : ℂ) *
          Complex.exp ((Real.eulerMascheroniConstant : ℂ) * (sigma : ℂ)) *
          Complex.Gamma (sigma : ℂ))⁻¹ *
        (riemannZeta (sigma : ℂ))⁻¹ *
        Complex.exp (gammaPrimeHybridPrimeTrace sigma) := by
  rw [gammaPrimeHybridKernel,
    fredholmDet_tprod_diagMul
      (gammaPrimeHybridEigenvalue sigma)
      (summable_normSq_gammaPrimeHybridEigenvalue hsigma)
      r hrHybrid 1 hz1]
  let primeEigenvalue : Nat.Primes → ℂ := fun p =>
    ((p : ℕ) : ℂ) ^ (-(sigma : ℂ))
  let factor : ℕ ⊕ Nat.Primes → ℂ := fun i =>
    (1 - gammaPrimeHybridEigenvalue sigma i) *
      Complex.exp (gammaPrimeHybridEigenvalue sigma i)
  have hregular : ∀ m : ℕ, (sigma : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    have hspos : 0 < sigma := lt_trans zero_lt_one hsigma
    simp at hre
    linarith
  have hgammaMult :
      Multipliable (fun n : ℕ => factor (Sum.inl n)) := by
    apply (multipliable_weierstrassFactor (sigma : ℂ)).congr
    intro n
    simp only [factor, gammaPrimeHybridEigenvalue]
    congr 1 <;> ring_nf
  have hprimeSummable : Summable primeEigenvalue := by
    apply Summable.of_norm
    simpa only [primeEigenvalue] using
      summable_norm_gammaPrimeHybrid_prime hsigma
  have hprimeSq :
      Summable (fun p : Nat.Primes => ‖primeEigenvalue p‖ ^ 2) := by
    simpa only [primeEigenvalue] using
      summable_normSq_gammaPrimeHybrid_prime hsigma
  have hprimeBare :
      HasProd (fun p : Nat.Primes => 1 - primeEigenvalue p)
        (fredholmDet1 (diagMul primeEigenvalue) 1) := by
    simpa only [one_mul] using
      hasProd_fredholmDet1_diagMul primeEigenvalue hprimeSq
        hprimeSummable r (by simpa only [primeEigenvalue] using hrPrime) 1 hz1
  have hprimeExp :
      HasProd (fun p : Nat.Primes => Complex.exp (primeEigenvalue p))
        (Complex.exp (∑' p : Nat.Primes, primeEigenvalue p)) := by
    simpa only [Function.comp_apply] using! hprimeSummable.hasSum.cexp
  have hprimeHas :
      HasProd (fun p : Nat.Primes => factor (Sum.inr p))
        (fredholmDet1 (diagMul primeEigenvalue) 1 *
          Complex.exp (∑' p : Nat.Primes, primeEigenvalue p)) := by
    simpa only [factor, gammaPrimeHybridEigenvalue, primeEigenvalue] using
      hprimeBare.mul hprimeExp
  simp only [one_mul]
  change (∏' i : ℕ ⊕ Nat.Primes, factor i) = _
  rw [(Multipliable.tprod_sum (f := factor) hgammaMult) hprimeHas.multipliable]
  have hgammaProduct :
      (∏' n : ℕ, factor (Sum.inl n)) =
        ((sigma : ℂ) *
          Complex.exp ((Real.eulerMascheroniConstant : ℂ) * (sigma : ℂ)) *
          Complex.Gamma (sigma : ℂ))⁻¹ := by
    let W : ℂ :=
      ∏' n : ℕ,
        (1 + (sigma : ℂ) / ((n : ℂ) + 1)) *
          Complex.exp (-((sigma : ℂ) / ((n : ℂ) + 1)))
    have hW :
        W = ((sigma : ℂ) *
          Complex.exp ((Real.eulerMascheroniConstant : ℂ) * (sigma : ℂ)) *
          Complex.Gamma (sigma : ℂ))⁻¹ := by
      have hweierstrass :=
        Gamma_inv_weierstrass (sigma : ℂ) hregular
      have hGamma : Complex.Gamma (sigma : ℂ) ≠ 0 :=
        Complex.Gamma_ne_zero hregular
      refine eq_inv_of_mul_eq_one_right ?_
      calc
        ((sigma : ℂ) *
              Complex.exp
                ((Real.eulerMascheroniConstant : ℂ) * (sigma : ℂ)) *
              Complex.Gamma (sigma : ℂ)) * W =
            Complex.Gamma (sigma : ℂ) *
              ((sigma : ℂ) *
                Complex.exp
                  ((Real.eulerMascheroniConstant : ℂ) * (sigma : ℂ)) * W) := by
                  ring
        _ = Complex.Gamma (sigma : ℂ) *
              (Complex.Gamma (sigma : ℂ))⁻¹ := by
              rw [← hweierstrass]
        _ = 1 := mul_inv_cancel₀ hGamma
    calc
      (∏' n : ℕ, factor (Sum.inl n)) = W := by
        apply tprod_congr
        intro n
        simp only [factor, gammaPrimeHybridEigenvalue]
        congr 1 <;> ring_nf
      _ = _ := hW
  have hprimeDet :
      fredholmDet1 (diagMul primeEigenvalue) 1 =
        (riemannZeta (sigma : ℂ))⁻¹ := by
    exact fredholmDet1_eq_inv_riemannZeta
      (sigma : ℂ) (by simpa using hsigma) r
      (by simpa only [primeEigenvalue] using hrPrime) hz1
  have hprimeProduct :
      (∏' p : Nat.Primes, factor (Sum.inr p)) =
        (riemannZeta (sigma : ℂ))⁻¹ *
          Complex.exp (gammaPrimeHybridPrimeTrace sigma) := by
    rw [hprimeHas.tprod_eq, hprimeDet]
    rfl
  rw [hgammaProduct, hprimeProduct]
  ring

/-- **Gamma--prime hybrid Euler--Weierstrass--Fredholm universality law.**

One operator is compact, injective, self-adjoint, and observability-unstable, while its corrected
regularized determinant simultaneously carries the archimedean Gamma and Euler zeta factors. -/
theorem gammaPrimeHybrid_eulerWeierstrassFredholmUniversality
    (sigma : ℝ) (hsigma : 1 < sigma) :
    IsCompactOperator (gammaPrimeHybridOperator sigma hsigma) ∧
      Function.Injective (gammaPrimeHybridOperator sigma hsigma) ∧
      HasApproximateUnitKernel (gammaPrimeHybridOperator sigma hsigma) ∧
      ¬ IsClosed (Set.range (gammaPrimeHybridOperator sigma hsigma)) ∧
      IsSelfAdjoint (gammaPrimeHybridOperator sigma hsigma) ∧
      ∀ r : ℝ,
        r * hsNorm (gammaPrimeHybridKernel sigma) < 1 →
        r * hsNorm
          (diagMul (fun p : Nat.Primes =>
            ((p : ℕ) : ℂ) ^ (-(sigma : ℂ)))) < 1 →
        (1 : ℂ) ∈ Metric.ball (0 : ℂ) r →
        fredholmDet (gammaPrimeHybridKernel sigma) 1 =
          ((sigma : ℂ) *
              Complex.exp
                ((Real.eulerMascheroniConstant : ℂ) * (sigma : ℂ)) *
              Complex.Gamma (sigma : ℂ))⁻¹ *
            (riemannZeta (sigma : ℂ))⁻¹ *
            Complex.exp (gammaPrimeHybridPrimeTrace sigma) := by
  exact ⟨gammaPrimeHybridOperator_isCompact sigma hsigma,
    gammaPrimeHybridOperator_injective sigma hsigma,
    gammaPrimeHybridOperator_hasApproximateUnitKernel sigma hsigma,
    gammaPrimeHybridOperator_not_isClosed_range sigma hsigma,
    gammaPrimeHybridOperator_isSelfAdjoint sigma hsigma,
    fun r hrHybrid hrPrime hz1 =>
      fredholmDet_gammaPrimeHybridKernel_eq_gamma_mul_zeta_mul_primeTrace
        sigma hsigma r hrHybrid hrPrime hz1⟩

end

end RHTower
