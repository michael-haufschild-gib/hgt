import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheCriticalStatesFormAnOrthogonalLadder
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheOnLineResolventOfAFiniteLayer
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.GammaAveragesOfTheOrdinaryPrimeError

/-!
# Ordinary primes on the third confined span

A negative Weil direction must couple both sides of one actual off-line quartet.
On three rungs the growing Euler charge and the constant prime-square charge can
be killed simultaneously. The remaining ordinary-prime transform is regular
around the real segment from −1 to 0 but still has a nonremovable singularity.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology Zeta23
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

open private centredZero_reflect_eq from
  GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheOnLineResolventOfAFiniteLayer

/-- Every strictly negative profile couples a right zero to its reflection.
If each product vanished, the heated zero sum would be nonnegative at every scale. -/
theorem exists_coupled_right_zero_of_bare_neg {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hneg : bareMixedEnergy F F < 0) :
    ∃ q : XiZeroCopy, 0 < (centredZero q).re ∧
      negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx F) (-centredZero q) ≠ 0 := by
  by_contra! h
  have off (q : XiZeroCopy) (hq : q ∉ onLineCopies) :
      negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx F) (-centredZero q) = 0 := by
    rcases lt_or_gt_of_ne (show (centredZero q).re ≠ 0 from hq) with hl | hr
    · have hr : 0 < (centredZero (xiZeroCopyReflectEquiv q)).re := by
        rw [centredZero_reflect_eq, neg_re]; exact neg_pos.mpr hl
      simpa only [centredZero_reflect_eq, neg_neg, mul_comm] using h _ hr
    · exact h q hr
  have ht : Tendsto (fun ε : ℝ => (∑' q, zeroNormTerm F ε q).re) (𝓝[>] 0)
      (𝓝 (bareMixedEnergy F F)) :=
    (continuous_re.tendsto _).comp (tendsto_heatedZeroPairing hF hF)
  apply hneg.not_ge
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [tsum_zeroNormTerm_eq_onLine_add (summable_heatedZeroPairing_of_domain hF hF hε)]
  have he (q : ↑onLineCopiesᶜ) : zeroNormTerm F ε q = 0 := by
    rw [zeroNormTerm, off q q.property, zero_mul]
  simp only [he, tsum_zero, add_zero, ofReal_re]
  exact tsum_nonneg fun q => mul_nonneg (onLineWeight_pos ε q).le (zeroValueMass_nonneg F q)

/-- At ratio zero the confined form is the bare form. The ladder diagonalizes it
with strictly negative entries, even when the full off-line divisor is infinite. -/
theorem IsCriticalLadder.bare_neg_of_nonzero {m : ℕ} {R : Fin (m+1) → ℝ}
    {Φ : Fin (m+1) → ℝ → ℝ} (hL : IsCriticalLadder m R Φ) {c : Fin (m+1) → ℝ}
    (hc : c ≠ 0) :
    let H := fun u => ∑ i, c i * Φ i u
    CriticalHalfLineEnergyDomain H ∧ bareMixedEnergy H H < 0 := by
  intro H
  let Z := fun u => 0 * Φ 0 u
  have hZ : CriticalHalfLineEnergyDomain Z := (hL.null 0).1.const_mul 0
  have ho (i) : criticalHalfLineExponentialPair (Φ i) Z = 0 := by
    rw [show Z = fun u => 0 * Φ 0 u from rfl, exponentialPair_const_mul, zero_mul]
  have hd : CriticalHalfLineEnergyDomain H := by
    simpa only [Z, zero_mul, zero_add, H] using
      criticalHalfLineEnergyDomain_add_sum hZ (fun i => (hL.null i).1) c Finset.univ
  refine ⟨hd, ?_⟩
  have e := fullEnergy_add_sum_nullVectors 0 hL.null hL.orth hZ ho c Finset.univ
  have h0 : criticalAliasCoefficient 0 = 0 := by rw [criticalAliasCoefficient_eq_div 0, div_zero]
  have eZ : criticalHalfLineFullEnergy 0 Z = 0 := by
    rw [show Z = fun u => 0 * Φ 0 u from rfl, criticalHalfLineFullEnergy_const_mul]; simp
  rw [eZ, h0] at e
  simp only [Z, zero_mul, zero_add, zero_sub, neg_mul, mul_neg, Finset.sum_neg_distrib] at e
  change criticalHalfLineFullEnergy 0 H = _ at e
  rw [← criticalHalfLineMixedEnergy_self 0 hd, criticalHalfLineMixedEnergy_eq_bare_add,
    h0, zero_mul, add_zero] at e
  rw [e, neg_lt_zero]
  have hdiag (i) : 0 < criticalAliasCoefficient (R i) * criticalHalfLineExponentialPair (Φ i) (Φ i) :=
    mul_pos (criticalAliasCoefficient_positive (hL.pos i))
      (exponentialPair_self_pos (hL.null i).1 (hL.null i).2.1)
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra! hz
    exact hc (funext hz)
  exact Finset.sum_pos' (fun j _ => mul_nonneg (sq_nonneg _) (hdiag j).le)
    ⟨i, Finset.mem_univ i, mul_pos (sq_pos_of_ne_zero hi) (hdiag i)⟩

/-- Any two prescribed real Laplace moments can be cancelled within three rungs. -/
private theorem exists_kill_two_moments {Φ : Fin 3 → ℝ → ℝ}
    (hΦ : ∀ i, CriticalHalfLineEnergyDomain (Φ i)) (s : Fin 2 → ℝ) (hs : ∀ j, -4 < s j) :
    ∃ c : Fin 3 → ℝ, c ≠ 0 ∧ ∀ j, negativeHalfLineLaplace
      (cx fun u => ∑ i, c i * Φ i u) (s j : ℂ) = 0 := by
  let A : Matrix (Fin 2) (Fin 3) ℝ := fun j i => ∫ u, Φ i u * Real.exp (s j * u)
  have hni : ¬ Function.Injective A.mulVecLin := by
    intro hin
    have h := LinearMap.finrank_le_finrank_of_injective hin
    simp at h
  obtain ⟨x, y, he, hxy⟩ := Function.not_injective_iff.mp hni
  let c := x-y
  have hc : c ≠ 0 := sub_ne_zero.mpr hxy
  have hk : A.mulVecLin c = 0 := by rw [show c = x-y from rfl, map_sub, he, sub_self]
  refine ⟨c, hc, fun j => ?_⟩
  rw [negativeHalfLineLaplace_ofReal, ← Complex.ofReal_zero, Complex.ofReal_inj]
  have hi (i : Fin 3) : Integrable fun u => Φ i u * Real.exp (s j * u) :=
    integrable_mul_rexp_of_domain (hΦ i) (hs j)
  have e : (fun u => (∑ i, c i * Φ i u) * Real.exp (s j * u)) =
      fun u => ∑ i, c i * (Φ i u * Real.exp (s j * u)) := by
    funext u; simp only [Finset.sum_mul, mul_assoc]
  rw [e, integral_finsetSum _ fun i _ => (hi i).const_mul _]
  simp_rw [integral_const_mul]
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, A, integral_const_mul,
    Pi.zero_apply, mul_comm] using congrFun hk j

/-- Double neutrality leaves an actual reflected zero pair in the same profile.
Its ordinary-prime head continues across the real wall at zero but cannot continue
through the whole left half-plane. -/
theorem IsCriticalLadder.exists_double_neutral_ordinary_prime_head {R : Fin 3 → ℝ}
    {Φ : Fin 3 → ℝ → ℝ} (hL : IsCriticalLadder 2 R Φ) :
    ∃ c : Fin 3 → ℝ, c ≠ 0 ∧
      let H := fun u => ∑ i, c i * Φ i u
      negativeHalfLineLaplace (cx H) (-(1/2)) = 0 ∧ negativeHalfLineLaplace (cx H) 0 = 0 ∧
      bareMixedEnergy H H < 0 ∧
      (∃ q : XiZeroCopy, 0 < (centredZero q).re ∧
        negativeHalfLineLaplace (cx H) (centredZero q) *
          negativeHalfLineLaplace (cx H) (-centredZero q) ≠ 0) ∧
      (∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (Metric.closedBall (-1) 1) ∧
        ∀ p : ℂ, -4 < p.re → p.re < -(1/2) → G p = ordinaryPrimeHead H p) ∧
      ¬ ∃ J : ℂ → ℂ, DifferentiableOn ℂ J {p : ℂ | p.re < 0} ∧
        EqOn J (ordinaryPrimeHead H) {p : ℂ | p.re < -(1/2)} := by
  let s : Fin 2 → ℝ := ![-(1/2), 0]
  obtain ⟨c,hc,hkill⟩ := exists_kill_two_moments (fun i => (hL.null i).1) s
    (fun j => by fin_cases j <;> norm_num [s])
  let H := fun u => ∑ i, c i * Φ i u
  have ha : negativeHalfLineLaplace (cx H) (-(1/2)) = 0 := by simpa [H,s] using hkill 0
  have hb : negativeHalfLineLaplace (cx H) 0 = 0 := by simpa [H,s] using hkill 1
  obtain ⟨hd,hn⟩ := hL.bare_neg_of_nonzero hc
  change CriticalHalfLineEnergyDomain H at hd
  change bareMixedEnergy H H < 0 at hn
  obtain ⟨q,hq,hp⟩ := exists_coupled_right_zero_of_bare_neg hd hn
  refine ⟨c,hc,ha,hb,hn,⟨q,hq,hp⟩,?_,?_⟩
  · obtain ⟨G,hG,hread⟩ := exists_analyticOnNhd_regular_ordinaryPrimeHead hd
    refine ⟨G,hG,fun p hp4 hp => ?_⟩
    simpa only [ha,hb,zero_div,add_zero,sub_zero] using hread p hp4 hp
  · rintro ⟨J,hJ,he⟩
    have hcont : ∃ K : ℂ → ℂ, DifferentiableOn ℂ K {p : ℂ | p.re < 0} ∧
        EqOn K (primeHead H) {p : ℂ | p.re < -(1/2)} := by
      refine ⟨J + properPowerHead H, hJ.add (differentiableOn_properPowerHead hd), fun p hp => ?_⟩
      exact (congrArg (· + properPowerHead H p) (he hp)).trans (primeHead_eq_prime_add_properPowerHead hd hp).symm
    have hv := (purePrimeHeadContinuation_profile_iff_vanish_leftZeros hd ha).mp hcont
    have hz := hv (xiZeroCopyReflectEquiv q) (by rw [centredZero_reflect_eq,neg_re]; exact neg_lt_zero.mpr hq)
    rw [centredZero_reflect_eq] at hz
    exact hp (mul_eq_zero_of_right _ hz)

#print axioms exists_coupled_right_zero_of_bare_neg
#print axioms IsCriticalLadder.bare_neg_of_nonzero
#print axioms IsCriticalLadder.exists_double_neutral_ordinary_prime_head

end GaloisForLFunctions.ExclusionOfTheCriticalState
