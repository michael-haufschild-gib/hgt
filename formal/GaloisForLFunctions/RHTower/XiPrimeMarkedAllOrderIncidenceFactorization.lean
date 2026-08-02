import GaloisForLFunctions.RHTower.XiPrimeMarkedPhysicalEndpointRVMQuarticIncidence
import GaloisForLFunctions.RHTower.PrimeArchReflectionPositiveHankelRH
import GaloisForLFunctions.RHTower.PrimeArchXiCompactThorinRH

/-!
# Route K all-order incidence factors through the Route P moment cone

For a self-adjoint Hilbert--Schmidt operator `T`, the sequence
`hsNormSq (T^(n+1))` is Hankel-positive.  Its polynomial quadratic tests are exact squared
Hilbert--Schmidt norms of finite odd-power probes.  Therefore matching every reflected source
moment, `2 hsNormSq (T^(n+1)) = normalizedPrimeArchMoment n`, proves RH before any Fredholm
determinant is formed and canonically supplies Route P's compact Markov carrier.

This isolates the genuine all-order boundary: finite-order Route K incidence can carry marked-prime
cycle provenance, but complete spectral incidence is already the compact positive moment problem.
-/

open scoped BigOperators InnerProductSpace Nat.Prime

namespace RHTower

noncomputable section

open ContinuousLinearMap

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isHilbertSchmidt_pow_succ
    (T : H →L[ℂ] H) (hT : T.IsHilbertSchmidt) (n : ℕ) :
    (T ^ (n + 1)).IsHilbertSchmidt := by
  rw [pow_succ, ContinuousLinearMap.mul_def]
  exact hT.comp_left (T ^ n)

theorem isSelfAdjoint_pow
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (n : ℕ) :
    IsSelfAdjoint (T ^ n) := by
  change star T = T at hT
  change star (T ^ n) = T ^ n
  rw [star_pow, hT]

theorem isHilbertSchmidt_finset_sum
    {κ : Type*} (s : Finset κ) (A : κ → H →L[ℂ] H)
    (hA : ∀ i ∈ s, (A i).IsHilbertSchmidt) :
    (∑ i ∈ s, A i).IsHilbertSchmidt := by
  refine Finset.sum_induction _ ContinuousLinearMap.IsHilbertSchmidt
    (fun S U hS hU => hS.add hU) isHilbertSchmidt_zero ?_
  intro i hi
  exact hA i hi

theorem hsInner_finset_sum_left
    {κ : Type*} (s : Finset κ) (A : κ → H →L[ℂ] H)
    (B : H →L[ℂ] H)
    (hA : ∀ i ∈ s, (A i).IsHilbertSchmidt)
    (hB : B.IsHilbertSchmidt) :
    hsInner (∑ i ∈ s, A i) B =
      ∑ i ∈ s, hsInner (A i) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hsInner]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        hsInner_add_left
          (hA a (Finset.mem_insert_self a s))
          (isHilbertSchmidt_finset_sum s A
            (fun i hi => hA i (Finset.mem_insert_of_mem hi)))
          hB,
        ih
          (fun i hi => hA i (Finset.mem_insert_of_mem hi))]

theorem hsInner_finset_sum_right
    {κ : Type*} (s : Finset κ) (A : κ → H →L[ℂ] H)
    (B : H →L[ℂ] H)
    (hA : ∀ i ∈ s, (A i).IsHilbertSchmidt)
    (hB : B.IsHilbertSchmidt) :
    hsInner B (∑ i ∈ s, A i) =
      ∑ i ∈ s, hsInner B (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hsInner]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        hsInner_add_right hB
          (hA a (Finset.mem_insert_self a s))
          (isHilbertSchmidt_finset_sum s A
            (fun i hi => hA i (Finset.mem_insert_of_mem hi))),
        ih
          (fun i hi => hA i (Finset.mem_insert_of_mem hi))]

theorem hsInner_odd_powers_eq_hsNormSq_power
    (T : H →L[ℂ] H) (hT : T.IsHilbertSchmidt)
    (hself : IsSelfAdjoint T) (i j : ℕ) :
    hsInner (T ^ (2 * i + 1)) (T ^ (2 * j + 1)) =
      (hsNormSq (T ^ (i + j + 1)) : ℂ) := by
  have hoddI := isHilbertSchmidt_pow_succ T hT (2 * i)
  have hoddJ := isHilbertSchmidt_pow_succ T hT (2 * j)
  have hpow := isHilbertSchmidt_pow_succ T hT (i + j)
  have hadjI := isSelfAdjoint_pow T hself (2 * i + 1)
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hadjI
  have htrace :
      hsInner (T ^ (2 * i + 1)) (T ^ (2 * j + 1)) =
        opTrace
          (ContinuousLinearMap.adjoint (T ^ (2 * i + 1)) ∘L
            T ^ (2 * j + 1)) := by
    symm
    simpa using opTrace_comp_eq_hsInner
      (ContinuousLinearMap.adjoint (T ^ (2 * i + 1)))
      (T ^ (2 * j + 1))
  rw [htrace, hadjI]
  have hcomp :
      (T ^ (2 * i + 1)) ∘L (T ^ (2 * j + 1)) =
        (T ^ (i + j + 1)) ^ 2 := by
    change T ^ (2 * i + 1) * T ^ (2 * j + 1) =
      (T ^ (i + j + 1)) ^ 2
    rw [← pow_add, ← pow_mul]
    congr 1
    omega
  rw [hcomp]
  have hpowSelf := isSelfAdjoint_pow T hself (i + j + 1)
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hpowSelf
  exact HTGeometry.opTrace_sq_eq_ofReal_hsNormSq hpow hpowSelf

def routeKOddPowerProbe
    (T : H →L[ℂ] H) (p : Polynomial ℝ) :
    H →L[ℂ] H :=
  ∑ n ∈ p.support,
    ((p.coeff n : ℝ) : ℂ) • T ^ (2 * n + 1)

theorem routeKOddPowerProbe_isHilbertSchmidt
    (T : H →L[ℂ] H) (hT : T.IsHilbertSchmidt)
    (p : Polynomial ℝ) :
    (routeKOddPowerProbe T p).IsHilbertSchmidt := by
  rw [routeKOddPowerProbe]
  refine Finset.sum_induction _ ContinuousLinearMap.IsHilbertSchmidt
    (fun S U hS hU => hS.add hU) isHilbertSchmidt_zero ?_
  intro n hn
  exact (isHilbertSchmidt_pow_succ T hT (2 * n)).smul _

theorem sum_toFn_smul_X_pow_eq (p : Polynomial ℝ) :
    (∑ i : Fin (p.natDegree + 1),
      Polynomial.toFn (p.natDegree + 1) p i •
        Polynomial.X ^ (i : ℕ)) = p := by
  let N := p.natDegree + 1
  let c : Fin N → ℝ := Polynomial.toFn N p
  have hp : Polynomial.ofFn N c = p :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
      (Nat.lt_succ_self _)
  change (∑ i : Fin N, c i • Polynomial.X ^ (i : ℕ)) = p
  calc
    (∑ i : Fin N, c i • Polynomial.X ^ (i : ℕ)) =
        ∑ i : Fin N, Polynomial.monomial (i : ℕ) (c i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Polynomial.smul_eq_C_mul,
            Polynomial.C_mul_X_pow_eq_monomial]
    _ = Polynomial.ofFn N c :=
      (Polynomial.ofFn_eq_sum_monomial c).symm
    _ = p := hp

def routeKOddPowerFinProbe
    (T : H →L[ℂ] H) (p : Polynomial ℝ) :
    H →L[ℂ] H :=
  ∑ i : Fin (p.natDegree + 1),
    ((Polynomial.toFn (p.natDegree + 1) p i : ℝ) : ℂ) •
      T ^ (2 * (i : ℕ) + 1)

theorem routeKOddPowerFinProbe_isHilbertSchmidt
    (T : H →L[ℂ] H) (hT : T.IsHilbertSchmidt)
    (p : Polynomial ℝ) :
    (routeKOddPowerFinProbe T p).IsHilbertSchmidt := by
  rw [routeKOddPowerFinProbe]
  apply isHilbertSchmidt_finset_sum
  intro i hi
  exact (isHilbertSchmidt_pow_succ T hT (2 * (i : ℕ))).smul _

theorem hsInner_routeKOddPowerFinProbe_self
    (T : H →L[ℂ] H) (hT : T.IsHilbertSchmidt)
    (hself : IsSelfAdjoint T) (p : Polynomial ℝ) :
    hsInner (routeKOddPowerFinProbe T p)
        (routeKOddPowerFinProbe T p) =
      ∑ i : Fin (p.natDegree + 1),
        ∑ j : Fin (p.natDegree + 1),
          ((Polynomial.toFn (p.natDegree + 1) p i : ℝ) : ℂ) *
            ((Polynomial.toFn (p.natDegree + 1) p j : ℝ) : ℂ) *
              (hsNormSq (T ^ ((i : ℕ) + (j : ℕ) + 1)) : ℂ) := by
  let N := p.natDegree + 1
  let c : Fin N → ℂ :=
    fun i => ((Polynomial.toFn N p i : ℝ) : ℂ)
  let A : Fin N → H →L[ℂ] H :=
    fun i => c i • T ^ (2 * (i : ℕ) + 1)
  have hA :
      ∀ i ∈ (Finset.univ : Finset (Fin N)),
        (A i).IsHilbertSchmidt := by
    intro i hi
    exact (isHilbertSchmidt_pow_succ T hT (2 * (i : ℕ))).smul _
  have hsum : (∑ i : Fin N, A i).IsHilbertSchmidt :=
    isHilbertSchmidt_finset_sum Finset.univ A hA
  change hsInner (∑ i : Fin N, A i) (∑ i : Fin N, A i) = _
  rw [hsInner_finset_sum_left Finset.univ A
    (∑ i : Fin N, A i) hA hsum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hsInner_smul_left]
  change star (c i) * hsInner
      (T ^ (2 * (i : ℕ) + 1)) (∑ j : Fin N, A j) = _
  rw [hsInner_finset_sum_right Finset.univ A
    (T ^ (2 * (i : ℕ) + 1)) hA
    (isHilbertSchmidt_pow_succ T hT (2 * (i : ℕ))),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hsInner_smul_right,
    hsInner_odd_powers_eq_hsNormSq_power T hT hself]
  simp [c, N]
  ring

theorem hsNormSq_routeKOddPowerFinProbe
    (T : H →L[ℂ] H) (hT : T.IsHilbertSchmidt)
    (hself : IsSelfAdjoint T) (p : Polynomial ℝ) :
    hsNormSq (routeKOddPowerFinProbe T p) =
      ∑ i : Fin (p.natDegree + 1),
        ∑ j : Fin (p.natDegree + 1),
          Polynomial.toFn (p.natDegree + 1) p i *
            Polynomial.toFn (p.natDegree + 1) p j *
              hsNormSq (T ^ ((i : ℕ) + (j : ℕ) + 1)) := by
  rw [← hsInner_self_re
    (routeKOddPowerFinProbe_isHilbertSchmidt T hT p),
    hsInner_routeKOddPowerFinProbe_self T hT hself]
  simp

theorem momentFunctional_pow_two_eq_hsNormSq_oddPowerProbe
    (T : H →L[ℂ] H) (hT : T.IsHilbertSchmidt)
    (hself : IsSelfAdjoint T) (m : ℕ → ℝ)
    (hmom : ∀ n, m n = hsNormSq (T ^ (n + 1)))
    (p : Polynomial ℝ) :
    HTGeometry.momentFunctional m (p ^ 2) =
      hsNormSq (routeKOddPowerFinProbe T p) := by
  let v : Fin (p.natDegree + 1) → ℝ :=
    Polynomial.toFn (p.natDegree + 1) p
  have hp :
      (∑ i : Fin (p.natDegree + 1),
        v i • Polynomial.X ^ (i : ℕ)) = p :=
    sum_toFn_smul_X_pow_eq p
  calc
    HTGeometry.momentFunctional m (p ^ 2) =
        HTGeometry.momentFunctional m
          ((∑ i : Fin (p.natDegree + 1),
            v i • Polynomial.X ^ (i : ℕ)) ^ 2) := by rw [hp]
    _ = ∑ i : Fin (p.natDegree + 1),
          ∑ j : Fin (p.natDegree + 1),
            v i * v j * m ((i : ℕ) + (j : ℕ)) :=
      HTGeometry.momentFunctional_sq_eq_hankelForm m v
    _ = hsNormSq (routeKOddPowerFinProbe T p) := by
      rw [hsNormSq_routeKOddPowerFinProbe T hT hself]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hmom]

theorem sequenceTraceHankelNonnegative_of_hsNormSq_powerMoments
    (T : H →L[ℂ] H) (hT : T.IsHilbertSchmidt)
    (hself : IsSelfAdjoint T) (m : ℕ → ℝ)
    (hmom : ∀ n, m n = hsNormSq (T ^ (n + 1))) :
    SequenceTraceHankelNonnegative m := by
  intro p
  rw [sequenceTraceHankel_eq_momentFunctional,
    momentFunctional_pow_two_eq_hsNormSq_oddPowerProbe
      T hT hself m hmom p]
  exact hsNormSq_nonneg _

theorem sequenceTraceHankel_const_mul
    (c : ℝ) (m : ℕ → ℝ) (p : Polynomial ℝ) :
    sequenceTraceHankel (fun n => c * m n) p =
      c * sequenceTraceHankel m p := by
  rw [sequenceTraceHankel, sequenceTraceHankel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem sequenceTraceHankelNonnegative_const_mul
    {c : ℝ} (hc : 0 ≤ c) {m : ℕ → ℝ}
    (hm : SequenceTraceHankelNonnegative m) :
    SequenceTraceHankelNonnegative (fun n => c * m n) := by
  intro p
  rw [sequenceTraceHankel_const_mul]
  exact mul_nonneg hc (hm p)

/-- Full reflected trace-energy incidence for one positive-half Route K operator.  Reflection
doubles every even trace and kills every odd trace. -/
def RouteKAllOrderReflectedEnergyIncidence
    (T : H →L[ℂ] H) : Prop :=
  T.IsHilbertSchmidt ∧ IsSelfAdjoint T ∧
    ∀ n : ℕ,
      2 * hsNormSq (T ^ (n + 1)) = normalizedPrimeArchMoment n

/-- **All-order frontier factorization.**  Any self-adjoint Hilbert--Schmidt Route K operator
matching the complete reflected source-energy tower proves RH before a Fredholm determinant is
formed.  Polynomial source-Hankel tests are squared Hilbert--Schmidt norms of odd-power probes. -/
theorem riemannHypothesis_of_routeKAllOrderReflectedEnergyIncidence
    (T : H →L[ℂ] H)
    (hinc : RouteKAllOrderReflectedEnergyIncidence T) :
    RiemannHypothesis := by
  rcases hinc with ⟨hT, hself, hmom⟩
  let halfMoment : ℕ → ℝ :=
    fun n => normalizedPrimeArchMoment n / 2
  have hhalf :
      ∀ n, halfMoment n = hsNormSq (T ^ (n + 1)) := by
    intro n
    have h := hmom n
    dsimp [halfMoment]
    linarith
  have hhalfPos : SequenceTraceHankelNonnegative halfMoment :=
    sequenceTraceHankelNonnegative_of_hsNormSq_powerMoments
      T hT hself halfMoment hhalf
  have hsource :
      SequenceTraceHankelNonnegative normalizedPrimeArchMoment := by
    have hscaled :=
      sequenceTraceHankelNonnegative_const_mul
        (show (0 : ℝ) ≤ 2 by norm_num) hhalfPos
    have heq :
        (fun n => (2 : ℝ) * halfMoment n) =
          normalizedPrimeArchMoment := by
      funext n
      dsimp [halfMoment]
      ring
    rw [heq] at hscaled
    exact hscaled
  apply riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
  intro p
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq,
    ← sequenceTraceHankel_eq_momentFunctional]
  exact hsource (p.map (Int.castRingHom ℝ))

/-- The remaining all-order Route K burden maps canonically to Route P: any such operator forces
the compact positive Markov carrier whose existence is Route P's exact endpoint. -/
theorem primeArchCompactMarkovGermRepresentation_of_routeKAllOrderIncidence
    (T : H →L[ℂ] H)
    (hinc : RouteKAllOrderReflectedEnergyIncidence T) :
    PrimeArchCompactMarkovGermRepresentation :=
  primeArchCompactMarkovGermRepresentation_of_riemannHypothesis
    (riemannHypothesis_of_routeKAllOrderReflectedEnergyIncidence T hinc)

end

end RHTower
