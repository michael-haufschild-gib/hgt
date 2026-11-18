import GaloisForLFunctions.ExclusionOfTheCriticalState.Analysis.OrderedHarmonicMoebiusConvolution
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.MoebiusInversionOfTheIntegerQuadrature
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ThePrimeNumberTheoremOnTheState
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.LogarithmicMangoldtTail
import GaloisForLFunctions.RHTower.Deninger.DeningerVonMangoldtMoebiusConvolution
import GaloisForLFunctions.WindowTowerOfSpecZ.TheWindowZetaIsAPlethysticExponential

/-!
# Ordinary primes as an ordered sum of centered divisor rows

The inverse coefficient is the Dirichlet convolution of the ordinary-prime
logarithm with Möbius. Proper prime powers have finite reciprocal mass, so
removing them leaves the harmonic normalization equal to one.
-/

noncomputable section
open Filter Topology Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open WindowTowerOfSpecZ _root_.RHTower MeasureTheory HTGeometry ArithmeticHodgeTheoryOfDegenerations
  ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory

/-- The coefficient of the row of multiples of a divisor in the ordinary-prime wave. -/
def ordinaryPrimeDivisorWeight : ArithmeticFunction ℝ := primeLog * (μ : ArithmeticFunction ℝ)

/-- Summing the inverse coefficients over the divisors gives the prime logarithm. -/
theorem sum_ordinaryPrimeDivisorWeight (n : ℕ) :
    ∑ d ∈ n.divisors, ordinaryPrimeDivisorWeight d = primeLog n := by
  rw [← coe_mul_zeta_apply, ordinaryPrimeDivisorWeight, mul_assoc, coe_moebius_mul_coe_zeta, mul_one]

/-- In absolute value each prime divisor costs at most its logarithm. -/
theorem abs_ordinaryPrimeDivisorWeight_le (n : ℕ) :
    |ordinaryPrimeDivisorWeight n| ≤ Real.log n := by
  rw [ordinaryPrimeDivisorWeight, arithmetic_product_at]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum (g := fun d => vonMangoldt d) ?_).trans_eq vonMangoldt_sum)
  intro d _
  have hm : |((moebius (n/d) : ℤ):ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
  by_cases hd : d.Prime
  · change |(if d.Prime then Real.log d else 0)*((moebius (n/d) : ℤ):ℝ)| ≤ _
    rw [if_pos hd, abs_mul, abs_of_nonneg (Real.log_natCast_nonneg d), vonMangoldt_apply_prime hd]
    exact (mul_le_mul_of_nonneg_left hm (Real.log_natCast_nonneg d)).trans_eq (mul_one _)
  · rw [primeLog_of_not_prime hd, zero_mul, abs_zero]
    exact vonMangoldt_nonneg

/-- The ordered ordinary-prime inverse weight has harmonic mass one. The
proper-power correction has harmonic mass zero after Möbius inversion. -/
theorem ordinaryPrimeDivisorWeight_harmonic_limit :
    Tendsto (fun N : ℕ => ∑ d ∈ range (N+1), ordinaryPrimeDivisorWeight d/(d:ℝ)) atTop (𝓝 1) := by
  let Q : ArithmeticFunction ℝ := vonMangoldt - primeLog
  have hQ : Summable fun n : ℕ => Q n/(n:ℝ) := by
    apply RenormalizedIntersectionArithmeticCounts.summable_nonprime_mangoldt_reciprocal.congr
    intro n
    change (if n.Prime then 0 else vonMangoldt n/(n:ℝ)) =
      (vonMangoldt n-(if n.Prime then Real.log n else 0))/(n:ℝ)
    split_ifs with h
    · rw [vonMangoldt_apply_prime h, sub_self, zero_div]
    · rw [sub_zero]
  have hc := tendsto_harmonic_moebius_product_zero Q hQ
  have h := Sieve.tendsto_moebiusLogHarmonicPartial_one.sub hc
  rw [sub_zero] at h
  have hcoef (n : ℕ) : Sieve.moebiusLogHarmonicTerm n =
      (vonMangoldt * (μ : ArithmeticFunction ℝ)) n/(n:ℝ) := by
    rw [GaloisForLFunctions.vonMangoldt_mul_moebius]
    change -((moebius n : ℤ):ℝ)*Real.log n*(n:ℝ)^(-1:ℝ) =
      -(((moebius n : ℤ):ℝ)*Real.log n)/(n:ℝ)
    rw [Real.rpow_neg_one, div_eq_mul_inv, neg_mul]
  have heq : vonMangoldt * (μ : ArithmeticFunction ℝ) - Q * μ = ordinaryPrimeDivisorWeight := by
    dsimp only [Q, ordinaryPrimeDivisorWeight]
    rw [sub_mul, sub_sub_cancel]
  apply h.congr' (Eventually.of_forall fun N => ?_)
  change (∑ n ∈ range (N+1), Sieve.moebiusLogHarmonicTerm n) - (∑ n ∈ range (N+1), _) = _
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [hcoef, ← sub_div, ← heq] <;> rfl

private theorem primeLog_atom_sum (Φ : ℝ → ℝ) (t : ℝ) :
    (∑' n : ℕ, primeLog n*continuousIntegerAtom Φ n t) = (ordinaryPrimeWave Φ t).re := by
  let P : Set ℕ := {n | n.Prime}
  let q := fun n : ℕ => Real.log n*continuousIntegerAtom Φ n t
  have heq (n : ℕ) : primeLog n*continuousIntegerAtom Φ n t = P.indicator q n := by
    by_cases h : n.Prime
    · simp only [primeLog, ArithmeticFunction.coe_mk, if_pos h, Set.indicator_of_mem (show n ∈ P from h), q]
    · rw [primeLog_of_not_prime h, zero_mul, Set.indicator_of_notMem (show n ∉ P from h)]
  simp_rw [heq]
  rw [← tsum_subtype P q]
  have h : ordinaryPrimeWave Φ t = ((∑' p : Nat.Primes, q p : ℝ):ℂ) := by
    rw [ordinaryPrimeWave, Complex.ofReal_tsum]
    apply tsum_congr fun p => ?_
    simp only [q, continuousIntegerAtom, vonMangoldtAtom, if_pos p.property.two_le,
      vonMangoldt_apply_prime p.property, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_inv]
    ring
  rw [h, Complex.ofReal_re]

/-- In increasing divisor order the actual ordinary-prime error is recovered
at every time, with the density subtracted inside each multiple row. -/
theorem tendsto_ordinaryPrimeDivisorWeight_centredMultipleRow {Φ : ℝ → ℝ} {C : ℝ}
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) (A t : ℝ) :
    Tendsto (fun N : ℕ => ∑ d ∈ range (N+1), ordinaryPrimeDivisorWeight d*centredMultipleRow Φ A d t)
      atTop (𝓝 ((ordinaryPrimeWave Φ t).re-Real.exp (t/2)*A)) := by
  have hs : Summable fun d : ℕ => |ordinaryPrimeDivisorWeight d|/(d:ℝ)^2 :=
    Summable.of_nonneg_of_le (fun _ => div_nonneg (abs_nonneg _) (sq_nonneg _))
      (fun d => div_le_div_of_nonneg_right (abs_ordinaryPrimeDivisorWeight_le d) (sq_nonneg _))
      GaloisForLFunctions.summable_log_nat_div_sq
  have h := tendsto_centredMultipleRow_of_harmonic_limit hb hs ordinaryPrimeDivisorWeight_harmonic_limit A t
  simpa only [sum_ordinaryPrimeDivisorWeight, primeLog_atom_sum, one_mul] using h

/-- On a squarefree integer each divisor contributing to the Mangoldt
convolution is already prime. The ordinary and full inverse weights agree. -/
theorem ordinaryPrimeDivisorWeight_of_squarefree {n : ℕ} (hn : Squarefree n) :
    ordinaryPrimeDivisorWeight n = -((moebius n : ℤ):ℝ)*Real.log n := by
  have h (d : ℕ) (hd : d ∈ n.divisors) : primeLog d = vonMangoldt d := by
    by_cases hp : d.Prime
    · change (if d.Prime then Real.log d else 0) = _
      rw [if_pos hp, vonMangoldt_apply_prime hp]
    · rw [primeLog_of_not_prime hp]
      exact (vonMangoldt_eq_zero_iff.2 fun hpow => hp
        (Nat.squarefree_and_prime_pow_iff_prime.1
          ⟨Squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd) hn, hpow⟩)).symm
  calc ordinaryPrimeDivisorWeight n = (vonMangoldt * (μ : ArithmeticFunction ℝ)) n := by
         rw [ordinaryPrimeDivisorWeight, arithmetic_product_at, arithmetic_product_at]
         exact sum_congr rfl fun d hd => congrArg (· * (μ (n/d) : ℝ)) (h d hd)
    _ = _ := by
         rw [GaloisForLFunctions.vonMangoldt_mul_moebius]
         change -(((moebius n : ℤ):ℝ)*Real.log n) = _
         rw [neg_mul]

/-- All nonsquarefree rows together account exactly for the difference
between the ordinary-prime and full Mangoldt waves. Their polar terms cancel. -/
theorem tendsto_nonsquarefree_ordinaryPrimeDivisorWeight {Φ : ℝ → ℝ} {C : ℝ}
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) (A t : ℝ) :
    Tendsto (fun N : ℕ => ∑ d ∈ range (N+1),
      if Squarefree d then 0 else ordinaryPrimeDivisorWeight d*centredMultipleRow Φ A d t) atTop
        (𝓝 ((ordinaryPrimeWave Φ t).re-∑' n : ℕ, vonMangoldt n*continuousIntegerAtom Φ n t)) := by
  have h := (tendsto_ordinaryPrimeDivisorWeight_centredMultipleRow hb A t).sub
    (tendsto_moebius_log_centredMultipleRow hb A t)
  rw [sub_sub_sub_cancel_right] at h
  apply h.congr' (Eventually.of_forall fun N => ?_)
  change (∑ d ∈ range (N+1), _) - (∑ d ∈ range (N+1), _) = _
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun d _ => ?_
  by_cases hd : Squarefree d
  · rw [if_pos hd, ordinaryPrimeDivisorWeight_of_squarefree hd, sub_self]
  · rw [if_neg hd, moebius_eq_zero_of_not_squarefree hd]
    simp only [Int.cast_zero, neg_zero, zero_mul, sub_zero]

private theorem mangoldt_atom_sum_split {Φ : ℝ → ℝ} {C : ℝ}
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) (t : ℝ) :
    (∑' n : ℕ, vonMangoldt n*continuousIntegerAtom Φ n t) = (ordinaryPrimeWave Φ t).re +
      ∑' j, vonMangoldtAtom (properPrimePowerIndex j)*Φ (t-Real.log (properPrimePowerIndex j)) := by
  let v := fun n : ℕ => vonMangoldt n*continuousIntegerAtom Φ n t
  let f := fun n : ℕ => (vonMangoldtAtom n:ℂ)*(Φ (t-Real.log n):ℂ)
  have he (n : ℕ) : (v n : ℂ) = f n := by
    by_cases hn : 2 ≤ n
    · simp only [v, f, continuousIntegerAtom, vonMangoldtAtom, if_pos hn, div_eq_mul_inv,
        Complex.ofReal_mul, mul_assoc]
    · rcases (show n=0 ∨ n=1 by omega) with rfl | rfl <;> simp [v,f,vonMangoldtAtom]
  have hv : Summable v := by
    apply Summable.of_norm_bounded (GaloisForLFunctions.summable_log_nat_div_sq.mul_left (C*Real.exp (2*t)))
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [v]
    have h := continuousIntegerAtom_bound hb (by exact_mod_cast hn : (1:ℝ) ≤ n) t
    dsimp only [v]
    rw [Real.norm_eq_abs,abs_mul, abs_of_nonneg vonMangoldt_nonneg]
    calc _ ≤ Real.log n*((C*Real.exp (2*t))*(1/(n:ℝ)^2)) :=
              mul_le_mul vonMangoldt_le_log h (abs_nonneg _) (Real.log_natCast_nonneg n)
      _ = _ := by ring
  have hf : Summable f := (Complex.ofRealCLM.hasSum hv.hasSum).summable.congr he
  have hsplit := tsum_eq_ordinary_primes_add_proper_powers hf (fun n hn => by
    by_contra hp
    apply hn
    rw [← he]
    dsimp only [v]
    rw [vonMangoldt_eq_zero_iff.2 hp,zero_mul,Complex.ofReal_zero])
  have ht : (∑' n, f n) = ((∑' n, v n : ℝ):ℂ) := by
    rw [Complex.ofReal_tsum]; exact tsum_congr fun n => (he n).symm
  have hj : (∑' j, f (properPrimePowerIndex j)) =
      ((∑' j, vonMangoldtAtom (properPrimePowerIndex j)*Φ (t-Real.log (properPrimePowerIndex j)) : ℝ):ℂ) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr fun _ => (Complex.ofReal_mul ..).symm
  rw [ht, hj] at hsplit
  exact congrArg Complex.re hsplit

/-- The entire nonsquarefree divisor contribution has a finite late-time
limit, independently of the density subtracted inside its rows. -/
theorem riemannHypothesis_or_nonsquarefree_divisor_limit : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ G : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      Tendsto G atTop (𝓝 (-((negativeHalfLineLaplace (cx F) 0).re/2))) ∧
      ∀ A t : ℝ, Tendsto (fun N : ℕ => ∑ d ∈ range (N+1),
        if Squarefree d then 0 else ordinaryPrimeDivisorWeight d*centredMultipleRow Φ A d t)
          atTop (𝓝 (G t)) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hΦ,he,_,⟨C,_,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  obtain ⟨Ψ,hΨ,heΨ,hp⟩ := criticalState_tendsto_properPowerWave hW ht hF
  have hΨΦ : Ψ = Φ := (Continuous.ae_eq_iff_eq volume hΨ hΦ).mp (heΨ.symm.trans he)
  subst Ψ
  refine Or.inr ⟨W₀,F,Φ,_,hW,ht,hF,hΦ,he,hp.neg,fun A t => ?_⟩
  have h := tendsto_nonsquarefree_ordinaryPrimeDivisorWeight hb A t
  simpa only [mangoldt_atom_sum_split hb t, Pi.neg_apply,
    sub_add_eq_sub_sub, sub_self, zero_sub] using h

#print axioms riemannHypothesis_or_nonsquarefree_divisor_limit
#print axioms tendsto_nonsquarefree_ordinaryPrimeDivisorWeight
#print axioms ordinaryPrimeDivisorWeight_harmonic_limit
#print axioms tendsto_ordinaryPrimeDivisorWeight_centredMultipleRow
end GaloisForLFunctions.ExclusionOfTheCriticalState
