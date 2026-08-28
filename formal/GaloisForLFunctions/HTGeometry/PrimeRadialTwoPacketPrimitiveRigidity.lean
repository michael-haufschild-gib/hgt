import GaloisForLFunctions.HTGeometry.TwoPacketRationalPrimitiveDomainRigidity
import GaloisForLFunctions.HTGeometry.PrimeValuationProfileRankLaw
import GaloisForLFunctions.HTGeometry.PrimeProfileJetCommonKernel
import GaloisForLFunctions.HTGeometry.PrimeProfileSeparatedPacketExact
import GaloisForLFunctions.HTGeometry.DifferentialAdjoinFiniteSupport
import GaloisForLFunctions.HTGeometry.SpanRankMaximalSubfamily
import GaloisForLFunctions.HTGeometry.PrimeValuationProfileFieldClassification
import GaloisForLFunctions.HTGeometry.PrimePowerSupportInterfaceBridge
import Mathlib.Tactic

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open ArithmeticFunction Matrix

/-- Natural numbers whose every prime divisor lies in `S`. -/
def PrimeFactorsIn (S : Set Nat.Primes) (n : ℕ) : Prop :=
  n ≠ 0 ∧ ∀ p : Nat.Primes, (p : ℕ) ∣ n → p ∈ S

theorem primeFactorsIn_one (S : Set Nat.Primes) : PrimeFactorsIn S 1 := by
  refine ⟨one_ne_zero, ?_⟩
  intro p hp
  exact (p.2.not_dvd_one hp).elim

theorem primeFactorsIn_mul_iff (S : Set Nat.Primes) (a b : ℕ) :
    PrimeFactorsIn S (a * b) ↔ PrimeFactorsIn S a ∧ PrimeFactorsIn S b := by
  constructor
  · rintro ⟨hab, hprime⟩
    have ha : a ≠ 0 := fun h => hab (by rw [h, zero_mul])
    have hb : b ≠ 0 := fun h => hab (by rw [h, mul_zero])
    refine ⟨⟨ha, ?_⟩, ⟨hb, ?_⟩⟩
    · intro p hp
      exact hprime p (dvd_mul_of_dvd_left hp b)
    · intro p hp
      exact hprime p (dvd_mul_of_dvd_right hp a)
  · rintro ⟨⟨ha, hpa⟩, ⟨hb, hpb⟩⟩
    refine ⟨Nat.mul_ne_zero ha hb, ?_⟩
    intro p hp
    rcases p.2.dvd_mul.mp hp with h | h
    · exact hpa p h
    · exact hpb p h

/-- Retain coefficients whose prime factors all lie in `S`. -/
noncomputable def primePacketRestrict (S : Set Nat.Primes)
    (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ := by
  classical
  exact
    { toFun := fun n => if PrimeFactorsIn S n then f n else 0
      map_zero' := by simp [PrimeFactorsIn] }

@[simp]
theorem primePacketRestrict_apply_of_mem (S : Set Nat.Primes)
    (f : ArithmeticFunction ℂ) (n : ℕ) (hn : PrimeFactorsIn S n) :
    primePacketRestrict S f n = f n := by
  classical
  simp [primePacketRestrict, hn]

@[simp]
theorem primePacketRestrict_apply_of_not_mem (S : Set Nat.Primes)
    (f : ArithmeticFunction ℂ) (n : ℕ) (hn : ¬ PrimeFactorsIn S n) :
    primePacketRestrict S f n = 0 := by
  classical
  simp [primePacketRestrict, hn]

/-- Prime-packet restriction is a unital Dirichlet-convolution algebra map. -/
def primePacketRestrictAlgHom (S : Set Nat.Primes) :
    ArithmeticFunction ℂ →ₐ[ℂ] ArithmeticFunction ℂ := by
  classical
  let r : ArithmeticFunction ℂ →+* ArithmeticFunction ℂ :=
    { toFun := primePacketRestrict S
      map_one' := by
        ext n
        by_cases hn : n = 1
        · subst n
          simp [primePacketRestrict, primeFactorsIn_one]
        · simp [primePacketRestrict, ArithmeticFunction.one_apply, hn]
      map_mul' := by
        intro f g
        ext n
        by_cases hn : PrimeFactorsIn S n
        · rw [primePacketRestrict_apply_of_mem S (f * g) n hn,
            ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
          apply Finset.sum_congr rfl
          intro ab hab
          have hp : PrimeFactorsIn S ab.1 ∧ PrimeFactorsIn S ab.2 := by
            apply (primeFactorsIn_mul_iff S ab.1 ab.2).mp
            rw [(Nat.mem_divisorsAntidiagonal.mp hab).1]
            exact hn
          simp [primePacketRestrict, hp.1, hp.2]
        · rw [primePacketRestrict_apply_of_not_mem S (f * g) n hn,
            ArithmeticFunction.mul_apply]
          symm
          apply Finset.sum_eq_zero
          intro ab hab
          have hp : ¬ (PrimeFactorsIn S ab.1 ∧ PrimeFactorsIn S ab.2) := by
            intro h
            apply hn
            rw [← (Nat.mem_divisorsAntidiagonal.mp hab).1]
            exact (primeFactorsIn_mul_iff S ab.1 ab.2).mpr h
          rcases not_and_or.mp hp with h | h
          · simp [primePacketRestrict, h]
          · simp [primePacketRestrict, h]
      map_zero' := by
        ext n
        simp [primePacketRestrict]
      map_add' := by
        intro f g
        ext n
        by_cases hn : PrimeFactorsIn S n <;>
          simp [primePacketRestrict, hn] }
  exact
    { r with
      commutes' := by
        intro c
        ext n
        by_cases hn : n = 1
        · subst n
          simp [r, primePacketRestrict, primeFactorsIn_one]
        · change (if PrimeFactorsIn S n then
              (algebraMap ℂ (ArithmeticFunction ℂ) c) n else 0) =
            (algebraMap ℂ (ArithmeticFunction ℂ) c) n
          rw [Algebra.algebraMap_eq_smul_one, ArithmeticFunction.smul_map,
            ArithmeticFunction.one_apply, if_neg hn, smul_zero]
          simp }

@[simp]
theorem primePacketRestrictAlgHom_apply_of_mem (S : Set Nat.Primes)
    (f : ArithmeticFunction ℂ) (n : ℕ) (hn : PrimeFactorsIn S n) :
    primePacketRestrictAlgHom S f n = f n := by
  classical
  simp [primePacketRestrictAlgHom, primePacketRestrict, hn]

@[simp]
theorem primePacketRestrictAlgHom_apply_of_not_mem (S : Set Nat.Primes)
    (f : ArithmeticFunction ℂ) (n : ℕ) (hn : ¬ PrimeFactorsIn S n) :
    primePacketRestrictAlgHom S f n = 0 := by
  classical
  simp [primePacketRestrictAlgHom, primePacketRestrict, hn]

theorem primeFactorsIn_prime_pow_iff
    (S : Set Nat.Primes) (p : Nat.Primes) (e : ℕ) :
    PrimeFactorsIn S ((p : ℕ) ^ (e + 1)) ↔ p ∈ S := by
  constructor
  · intro h
    exact h.2 p (dvd_pow_self (p : ℕ) (Nat.succ_ne_zero e))
  · intro hp
    refine ⟨pow_ne_zero _ p.2.ne_zero, ?_⟩
    intro q hq
    have hqp : q = p := by
      apply Subtype.ext
      exact Nat.prime_eq_prime_of_dvd_pow q.2 p.2 hq
    simpa [hqp] using hp

theorem primePacketRestrictAlgHom_prime_pow_of_mem
    (S : Set Nat.Primes) (f : ArithmeticFunction ℂ)
    (p : Nat.Primes) (e : ℕ) (hp : p ∈ S) :
    primePacketRestrictAlgHom S f ((p : ℕ) ^ (e + 1)) =
      f ((p : ℕ) ^ (e + 1)) := by
  rw [primePacketRestrictAlgHom_apply_of_mem]
  exact (primeFactorsIn_prime_pow_iff S p e).2 hp

theorem primePacketRestrictAlgHom_prime_pow_of_not_mem
    (S : Set Nat.Primes) (f : ArithmeticFunction ℂ)
    (p : Nat.Primes) (e : ℕ) (hp : p ∉ S) :
    primePacketRestrictAlgHom S f ((p : ℕ) ^ (e + 1)) = 0 := by
  rw [primePacketRestrictAlgHom_apply_of_not_mem]
  exact fun h => hp ((primeFactorsIn_prime_pow_iff S p e).1 h)

/-- Prime-packet restriction commutes with the rotated logarithmic derivation. -/
theorem primePacketRestrictAlgHom_rotatedLog
    (S : Set Nat.Primes) (f : ArithmeticFunction ℂ) :
    primePacketRestrictAlgHom S (rotatedLogArithmeticDerivationComplex f) =
      rotatedLogArithmeticDerivationComplex (primePacketRestrictAlgHom S f) := by
  classical
  ext n
  by_cases hn : PrimeFactorsIn S n
  · simp [primePacketRestrictAlgHom_apply_of_mem, hn,
      rotatedLogArithmeticDerivationComplex, logWeight_apply,
      ArithmeticFunction.smul_map, smul_eq_mul]
  · simp [primePacketRestrictAlgHom_apply_of_not_mem, hn,
      rotatedLogArithmeticDerivationComplex, logWeight_apply,
      ArithmeticFunction.smul_map, smul_eq_mul]

/-- Restriction to a disjoint union is the sum of the two restrictions on a positive-prime-power
current. -/
theorem primePacketRestrictAlgHom_union_eq_add
    (S T : Set Nat.Primes) (hST : Disjoint S T)
    (f : ArithmeticFunction ℂ) (hf : SupportedOnPositivePrimePowers f) :
    primePacketRestrictAlgHom (S ∪ T) f =
      primePacketRestrictAlgHom S f + primePacketRestrictAlgHom T f := by
  classical
  ext n
  by_cases hfn : f n = 0
  · by_cases hU : PrimeFactorsIn (S ∪ T) n <;>
      by_cases hS : PrimeFactorsIn S n <;>
        by_cases hT : PrimeFactorsIn T n <;>
          simp [primePacketRestrictAlgHom, primePacketRestrict, hfn, hU, hS, hT]
  · obtain ⟨p, e, rfl⟩ := hf hfn
    change primePacketRestrictAlgHom (S ∪ T) f ((p : ℕ) ^ (e + 1)) =
      primePacketRestrictAlgHom S f ((p : ℕ) ^ (e + 1)) +
        primePacketRestrictAlgHom T f ((p : ℕ) ^ (e + 1))
    by_cases hpS : p ∈ S
    · have hpT : p ∉ T := Set.disjoint_left.mp hST hpS
      rw [primePacketRestrictAlgHom_prime_pow_of_mem _ _ _ _ (Set.mem_union_left T hpS),
        primePacketRestrictAlgHom_prime_pow_of_mem _ _ _ _ hpS,
        primePacketRestrictAlgHom_prime_pow_of_not_mem _ _ _ _ hpT, add_zero]
    · by_cases hpT : p ∈ T
      · rw [primePacketRestrictAlgHom_prime_pow_of_mem _ _ _ _ (Set.mem_union_right S hpT),
          primePacketRestrictAlgHom_prime_pow_of_not_mem _ _ _ _ hpS,
          primePacketRestrictAlgHom_prime_pow_of_mem _ _ _ _ hpT, zero_add]
      · have hpU : p ∉ S ∪ T := by simp [hpS, hpT]
        rw [primePacketRestrictAlgHom_prime_pow_of_not_mem _ _ _ _ hpU,
          primePacketRestrictAlgHom_prime_pow_of_not_mem _ _ _ _ hpS,
          primePacketRestrictAlgHom_prime_pow_of_not_mem _ _ _ _ hpT, add_zero]

/-- Finite clock-power columns masked to one infinite prime packet. -/
noncomputable def primePacketClockCoefficients
    (S : Set Nat.Primes) (e m : ℕ) : Fin (m + 1) → Nat.Primes → ℂ := by
  classical
  exact fun k p => if p ∈ S then
    ((((e + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^ (k : ℕ)) else 0

/-- Clock powers remain independent modulo finite prime support after restriction to any infinite
prime packet. -/
theorem primePacketClockCoefficients_tailIndependent
    (S : Set Nat.Primes) (hS : S.Infinite) (e m : ℕ) :
    TailCoefficientIndependent (primePacketClockCoefficients S e m) := by
  classical
  intro c hfinite
  let P : Polynomial ℂ :=
    ∑ k : Fin (m + 1), Polynomial.monomial (k : ℕ) (c k)
  let clock : Nat.Primes → ℂ := fun p =>
    ((e + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p
  have hscale : (((e + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero e
  have hclock : Function.Injective clock := by
    intro p q hpq
    apply rotatedPrimeLogClock_injective
    apply mul_left_cancel₀ hscale
    exact hpq
  let support : Set Nat.Primes :=
    {p | ∑ k, c k * primePacketClockCoefficients S e m k p ≠ 0}
  have hgood : (S \ support).Infinite := hS.sdiff hfinite
  have himage : (clock '' (S \ support)).Infinite :=
    hgood.image hclock.injOn
  have hroots : {z : ℂ | P.IsRoot z}.Infinite := by
    apply himage.mono
    intro z hz
    obtain ⟨p, hp, rfl⟩ := hz
    have hzero : ∑ k, c k * primePacketClockCoefficients S e m k p = 0 := by
      exact not_ne_iff.mp hp.2
    change Polynomial.evalRingHom (clock p) P = 0
    rw [show P = ∑ k : Fin (m + 1),
      Polynomial.monomial (k : ℕ) (c k) from rfl, map_sum]
    have heval (k : Fin (m + 1)) :
        Polynomial.evalRingHom (clock p) (Polynomial.monomial (k : ℕ) (c k)) =
          c k * clock p ^ (k : ℕ) :=
      Polynomial.eval_monomial
    simp_rw [heval]
    simpa only [clock, primePacketClockCoefficients, if_pos hp.1] using hzero
  have hP : P = 0 := Polynomial.eq_zero_of_infinite_isRoot P hroots
  funext k
  let coeffHom : Polynomial ℂ →+ ℂ :=
    { toFun := fun Q => Q.coeff (k : ℕ)
      map_zero' := Polynomial.coeff_zero (k : ℕ)
      map_add' := fun Q R => Polynomial.coeff_add Q R (k : ℕ) }
  have hk := congrArg coeffHom hP
  change coeffHom (∑ b : Fin (m + 1), Polynomial.monomial (b : ℕ) (c b)) = 0 at hk
  rw [map_sum] at hk
  change (∑ b : Fin (m + 1),
    (Polynomial.monomial (b : ℕ) (c b)).coeff (k : ℕ)) = 0 at hk
  rw [Finset.sum_eq_single k] at hk
  · simpa using hk
  · intro b hb hbk
    rw [Polynomial.coeff_monomial, if_neg]
    exact fun h => hbk (Fin.ext h)
  · simp

/-- Scalar prime-radial source restricted to one prime packet. -/
def primePacketRadialSource (S : Set Nat.Primes) (u : ℕ → ℂ) :
    ArithmeticFunction ℂ :=
  primePacketRestrictAlgHom S (scalarReplicatedPrimeProfile u)

@[simp]
theorem primePacketRadialSource_prime_pow_of_mem
    (S : Set Nat.Primes) (u : ℕ → ℂ) (p : Nat.Primes) (e : ℕ) :
    p ∈ S → primePacketRadialSource S u ((p : ℕ) ^ (e + 1)) = u e := by
  intro hp
  rw [primePacketRadialSource,
    primePacketRestrictAlgHom_prime_pow_of_mem _ _ _ _ hp]
  change primePowerCoordinateProfile (scalarReplicatedPrimeProfile u) (p, e) = u e
  exact primePowerCoordinateProfile_scalarReplicatedPrimeProfile u (p, e)

theorem primePacketRadialSource_prime_pow_of_not_mem
    (S : Set Nat.Primes) (u : ℕ → ℂ) (p : Nat.Primes) (e : ℕ) :
    p ∉ S → primePacketRadialSource S u ((p : ℕ) ^ (e + 1)) = 0 := by
  intro hp
  exact primePacketRestrictAlgHom_prime_pow_of_not_mem
    S (scalarReplicatedPrimeProfile u) p e hp

theorem primePacketRadialSource_supportedOnPositivePrimePowers
    (S : Set Nat.Primes) (u : ℕ → ℂ) :
    PrimeProfileSupportedOnPositivePrimePowers (primePacketRadialSource S u) := by
  intro n hn
  classical
  by_cases hpacket : PrimeFactorsIn S n
  · have hsource : scalarReplicatedPrimeProfile u n ≠ 0 := by
      simpa [primePacketRadialSource, primePacketRestrictAlgHom,
        primePacketRestrict, hpacket] using hn
    exact scalarReplicatedPrimeProfile_supportedOnPositivePrimePowers u hsource
  · exact (hn (primePacketRestrictAlgHom_apply_of_not_mem S _ n hpacket)).elim

theorem primeProfileJetRayCoefficient_primePacketRadialSource
    {d : ℕ} (S : Set Nat.Primes) (u : Fin d → ℕ → ℂ)
    (m : ℕ) (col : Fin d × Fin (m + 1)) (p : Nat.Primes) (e : ℕ) :
    primeProfileJetRayCoefficient (fun j => primePacketRadialSource S (u j))
        m col p e =
      ((e + 1 : ℕ) : ℂ) *
        (primePacketClockCoefficients S e m col.2 p * u col.1 e) := by
  classical
  change primeDeriv p.1
      (rotatedLogArithmeticJet col.2 (primePacketRadialSource S (u col.1)))
        ((p : ℕ) ^ e) = _
  rw [primeDeriv_rotatedLogArithmeticJet_apply_primePow]
  by_cases hp : p ∈ S
  · rw [primePacketRadialSource_prime_pow_of_mem _ _ _ _ hp]
    simp [primePacketClockCoefficients, hp]
  · rw [primePacketRadialSource_prime_pow_of_not_mem _ _ _ _ hp]
    simp [primePacketClockCoefficients, hp]

/-- One infinite prime packet retains every finite jet rectangle of a linearly independent radial
profile family. -/
theorem primePacketRadialSource_jetRayTailIndependent
    {d : ℕ} [Nonempty (Fin d)]
    (S : Set Nat.Primes) (hS : S.Infinite)
    (u : Fin d → ℕ → ℂ) (hu : LinearIndependent ℂ u) (m : ℕ) :
    PrimeProfileJetRayTailIndependent
      (fun j => primePacketRadialSource S (u j)) m := by
  classical
  obtain ⟨e, P, he, hPdet, hP⟩ :=
    exists_injective_evaluation_minor_of_linearIndependent_profiles u hu
  intro c hactive
  let rowCoefficient : Fin d → Fin (m + 1) → ℂ := fun r k =>
    ∑ s, c (s, k) * u s (e r)
  have hfactor (r : Fin d) (p : Nat.Primes) :
      (∑ col, c col *
        primeProfileJetRayCoefficient
          (fun j => primePacketRadialSource S (u j)) m col p (e r)) =
        ((e r + 1 : ℕ) : ℂ) *
          ∑ k, rowCoefficient r k * primePacketClockCoefficients S (e r) m k p := by
    simp_rw [primeProfileJetRayCoefficient_primePacketRadialSource]
    rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    change (∑ s, c (s, k) *
        (((e r + 1 : ℕ) : ℂ) *
          (primePacketClockCoefficients S (e r) m k p * u s (e r)))) =
      ((e r + 1 : ℕ) : ℂ) *
        ((∑ s, c (s, k) * u s (e r)) *
          primePacketClockCoefficients S (e r) m k p)
    calc
      _ = ∑ s, ((e r + 1 : ℕ) : ℂ) *
          ((c (s, k) * u s (e r)) *
            primePacketClockCoefficients S (e r) m k p) := by
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ = ((e r + 1 : ℕ) : ℂ) *
          ∑ s, (c (s, k) * u s (e r)) *
            primePacketClockCoefficients S (e r) m k p := by
        rw [Finset.mul_sum]
      _ = _ := by rw [← Finset.sum_mul]
  have hrow (r : Fin d) : rowCoefficient r = 0 := by
    apply primePacketClockCoefficients_tailIndependent S hS (e r) m
      (rowCoefficient r)
    apply hactive.subset
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    refine ⟨e r, ?_⟩
    rw [hfactor]
    exact mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero (e r)) hp
  have hPunit : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2 hPdet
  have hPinj : Function.Injective P.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hPunit
  funext col
  let v : Fin d → ℂ := fun s => c (s, col.2)
  have hv : P.mulVec v = 0 := by
    funext r
    have hr := congrFun (hrow r) col.2
    change ∑ s, P r s * v s = 0
    calc
      ∑ s, P r s * v s = ∑ s, c (s, col.2) * u s (e r) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [hP]
        simp only [v]
        ring
      _ = 0 := hr
  have hv0 : v = 0 := hPinj (by simpa using hv)
  exact congrFun hv0 col.1

/-- Two disjoint copies of a radial source family, indexed by a sum type. -/
def twoPrimePacketRadialSource
    {d : ℕ} (S T : Set Nat.Primes) (u : Fin d → ℕ → ℂ) :
    (Fin d ⊕ Fin d) → ArithmeticFunction ℂ :=
  Sum.elim (fun j => primePacketRadialSource S (u j))
    (fun j => primePacketRadialSource T (u j))

theorem twoPrimePacketRadialSource_supportedOnPositivePrimePowers
    {d : ℕ} (S T : Set Nat.Primes) (u : Fin d → ℕ → ℂ) :
    ∀ j, PrimeProfileSupportedOnPositivePrimePowers
      (twoPrimePacketRadialSource S T u j) := by
  intro j
  cases j with
  | inl j => exact primePacketRadialSource_supportedOnPositivePrimePowers S (u j)
  | inr j => exact primePacketRadialSource_supportedOnPositivePrimePowers T (u j)

/-- Two disjoint infinite prime packets jointly retain every finite radial jet rectangle. -/
theorem twoPrimePacketRadialSource_jetRayTailIndependent
    {d : ℕ} [Nonempty (Fin d)]
    (S T : Set Nat.Primes) (hS : S.Infinite) (hT : T.Infinite)
    (hST : Disjoint S T)
    (u : Fin d → ℕ → ℂ) (hu : LinearIndependent ℂ u) (m : ℕ) :
    PrimeProfileJetRayTailIndependent (twoPrimePacketRadialSource S T u) m := by
  classical
  intro c hactive
  let cL : Fin d × Fin (m + 1) → ℂ := fun col => c (Sum.inl col.1, col.2)
  let cR : Fin d × Fin (m + 1) → ℂ := fun col => c (Sum.inr col.1, col.2)
  have hleft : cL = 0 := by
    apply (primePacketRadialSource_jetRayTailIndependent S hS u hu m)
    apply hactive.subset
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    obtain ⟨e, he⟩ := hp
    have hpS : p ∈ S := by
      by_contra hpS
      apply he
      apply Finset.sum_eq_zero
      rintro ⟨j, k⟩ hk
      rw [primeProfileJetRayCoefficient_primePacketRadialSource]
      simp [primePacketClockCoefficients, hpS]
    have hpT : p ∉ T := Set.disjoint_left.mp hST hpS
    refine ⟨e, ?_⟩
    have hright : ∑ col : Fin d × Fin (m + 1),
        cR col * primeProfileJetRayCoefficient
          (fun j => primePacketRadialSource T (u j)) m col p e = 0 := by
      apply Finset.sum_eq_zero
      rintro ⟨j, k⟩ hk
      rw [primeProfileJetRayCoefficient_primePacketRadialSource]
      simp [primePacketClockCoefficients, hpT]
    rw [Fintype.sum_prod_type, Fintype.sum_sum_type]
    change (∑ j, ∑ k,
        cL (j, k) * primeProfileJetRayCoefficient
          (fun j => primePacketRadialSource S (u j)) m (j, k) p e) +
      (∑ j, ∑ k,
        cR (j, k) * primeProfileJetRayCoefficient
          (fun j => primePacketRadialSource T (u j)) m (j, k) p e) ≠ 0
    have hright' : (∑ j, ∑ k,
        cR (j, k) * primeProfileJetRayCoefficient
          (fun j => primePacketRadialSource T (u j)) m (j, k) p e) = 0 := by
      simpa only [Fintype.sum_prod_type] using hright
    rw [hright', add_zero]
    simpa only [Fintype.sum_prod_type] using he
  have hright : cR = 0 := by
    apply (primePacketRadialSource_jetRayTailIndependent T hT u hu m)
    apply hactive.subset
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    obtain ⟨e, he⟩ := hp
    have hpT : p ∈ T := by
      by_contra hpT
      apply he
      apply Finset.sum_eq_zero
      rintro ⟨j, k⟩ hk
      rw [primeProfileJetRayCoefficient_primePacketRadialSource]
      simp [primePacketClockCoefficients, hpT]
    have hpS : p ∉ S := Set.disjoint_right.mp hST hpT
    refine ⟨e, ?_⟩
    have hleftZero : ∑ col : Fin d × Fin (m + 1),
        cL col * primeProfileJetRayCoefficient
          (fun j => primePacketRadialSource S (u j)) m col p e = 0 := by
      apply Finset.sum_eq_zero
      rintro ⟨j, k⟩ hk
      rw [primeProfileJetRayCoefficient_primePacketRadialSource]
      simp [primePacketClockCoefficients, hpS]
    rw [Fintype.sum_prod_type, Fintype.sum_sum_type]
    change (∑ j, ∑ k,
        cL (j, k) * primeProfileJetRayCoefficient
          (fun j => primePacketRadialSource S (u j)) m (j, k) p e) +
      (∑ j, ∑ k,
        cR (j, k) * primeProfileJetRayCoefficient
          (fun j => primePacketRadialSource T (u j)) m (j, k) p e) ≠ 0
    have hleftZero' : (∑ j, ∑ k,
        cL (j, k) * primeProfileJetRayCoefficient
          (fun j => primePacketRadialSource S (u j)) m (j, k) p e) = 0 := by
      simpa only [Fintype.sum_prod_type] using hleftZero
    rw [hleftZero', zero_add]
    simpa only [Fintype.sum_prod_type] using he
  funext col
  rcases col with ⟨j, k⟩
  cases j with
  | inl j => simpa [cL] using congrFun hleft (j, k)
  | inr j => simpa [cR] using congrFun hright (j, k)

/-- Algebraic form of Lemma 4.1: every finite joint jet rectangle on two disjoint infinite prime
packets is algebraically independent over `ℂ`. -/
theorem twoPrimePacketRadialSource_jets_algebraicIndependent
    {d : ℕ} [Nonempty (Fin d)]
    (S T : Set Nat.Primes) (hS : S.Infinite) (hT : T.Infinite)
    (hST : Disjoint S T)
    (u : Fin d → ℕ → ℂ) (hu : LinearIndependent ℂ u) (m : ℕ) :
    AlgebraicIndependent ℂ
      (fun col : (Fin d ⊕ Fin d) × Fin (m + 1) =>
        algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (primeProfileJetSource (twoPrimePacketRadialSource S T u) m col)) := by
  classical
  let g := twoPrimePacketRadialSource S T u
  have hray : PrimeProfileJetRayTailIndependent g m :=
    twoPrimePacketRadialSource_jetRayTailIndependent S T hS hT hST u hu m
  have hpacket : ∀ (forbidden : Set Nat.Primes), forbidden.Finite →
      ∃ (q : ((Fin d ⊕ Fin d) × Fin (m + 1)) → Nat.Primes)
        (e : ((Fin d ⊕ Fin d) × Fin (m + 1)) → ℕ),
        Function.Injective q ∧
        (∀ row, q row ∉ forbidden) ∧
        (primeProfileJetPacketMatrix g m q e).det ≠ 0 := by
    intro forbidden hforbidden
    exact cofinitePrimeProfileJetPacket_at_of_rayTailIndependent
      g m hray forbidden hforbidden
  have hAI := algebraicIndependent_fractionPrimeProfileJets_of_cofinitePacketAt
    g (twoPrimePacketRadialSource_supportedOnPositivePrimePowers S T u) m hpacket
  exact hAI.restrictScalars
    (algebraMap ℂ finitePrimeCoefficientField).injective

theorem primePacketRestrictAlgHom_rotatedLogJet
    (S : Set Nat.Primes) (f : ArithmeticFunction ℂ) (k : ℕ) :
    primePacketRestrictAlgHom S (rotatedLogArithmeticJet k f) =
      rotatedLogArithmeticJet k (primePacketRestrictAlgHom S f) := by
  classical
  ext n
  by_cases hn : PrimeFactorsIn S n
  · simp [primePacketRestrictAlgHom_apply_of_mem, hn,
      rotatedLogArithmeticJet_apply]
  · simp [primePacketRestrictAlgHom_apply_of_not_mem, hn,
      rotatedLogArithmeticJet_apply]

theorem primeProfileRotatedLogJet_eq_rotatedLogArithmeticJet
    (k : ℕ) (f : ArithmeticFunction ℂ) :
    primeProfileRotatedLogJet k f = rotatedLogArithmeticJet k f := by
  ext n
  rfl

/-- Literal packet-restriction form of Lemma 4.1 `(PFR.17)`. -/
theorem primeRadial_two_disjoint_infinite_packets_jet_free
    {d : ℕ} [Nonempty (Fin d)]
    (S T : Set Nat.Primes) (hS : S.Infinite) (hT : T.Infinite)
    (hST : Disjoint S T)
    (u : Fin d → ℕ → ℂ) (hu : LinearIndependent ℂ u) (m : ℕ) :
    AlgebraicIndependent ℂ
      (fun col : (Fin d ⊕ Fin d) × Fin (m + 1) =>
        algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (Sum.elim
            (fun j => primePacketRestrictAlgHom S
              (rotatedLogArithmeticJet col.2 (scalarReplicatedPrimeProfile (u j))))
            (fun j => primePacketRestrictAlgHom T
              (rotatedLogArithmeticJet col.2 (scalarReplicatedPrimeProfile (u j)))) col.1)) := by
  have hAI := twoPrimePacketRadialSource_jets_algebraicIndependent
    S T hS hT hST u hu m
  convert hAI using 1
  funext col
  rcases col with ⟨j, k⟩
  cases j with
  | inl j =>
      simp [primeProfileJetSource, twoPrimePacketRadialSource,
        primePacketRadialSource, primePacketRestrictAlgHom_rotatedLogJet,
        primeProfileRotatedLogJet_eq_rotatedLogArithmeticJet]
  | inr j =>
      simp [primeProfileJetSource, twoPrimePacketRadialSource,
        primePacketRadialSource, primePacketRestrictAlgHom_rotatedLogJet,
        primeProfileRotatedLogJet_eq_rotatedLogArithmeticJet]

/-- Every member of a differential field generated by a finite family already belongs to an
ordinary rational field generated by one finite rectangular jet prefix. -/
theorem exists_finJetRectangle_of_mem_differentialAdjoin_range
    {C E : Type*} [Field C] [Field E] [Algebra C E] [Differential E]
    {d : ℕ} (x : Fin d → E) {z : E}
    (hz : z ∈ differentialAdjoin C (Set.range x)) :
    ∃ m : ℕ, z ∈ IntermediateField.adjoin C
      (Set.range (fun col : Fin d × Fin (m + 1) =>
        differentialJet col.2 (x col.1))) := by
  rw [differentialAdjoin] at hz
  obtain ⟨T, hT, hzT⟩ := IntermediateField.exists_finset_of_mem_adjoin hz
  classical
  have hwitness : ∀ w : {w // w ∈ T},
      ∃ j : Fin d, ∃ n : ℕ, differentialJet n (x j) = w.1 := by
    intro w
    obtain ⟨y, ⟨j, rfl⟩, n, hn⟩ := hT w.2
    exact ⟨j, n, hn⟩
  choose source order hsource using hwitness
  let orders : Finset ℕ := Finset.univ.image order
  let m : ℕ := orders.sup id
  refine ⟨m, ?_⟩
  have hle : IntermediateField.adjoin C (T : Set E) ≤
      IntermediateField.adjoin C
        (Set.range (fun col : Fin d × Fin (m + 1) =>
          differentialJet col.2 (x col.1))) := by
    apply IntermediateField.adjoin.mono C
    intro w hwT
    let wt : {w // w ∈ T} := ⟨w, hwT⟩
    have horderMem : order wt ∈ orders := by
      exact Finset.mem_image.mpr ⟨wt, Finset.mem_univ wt, rfl⟩
    have horderLe : order wt ≤ m := Finset.le_sup (f := id) horderMem
    refine ⟨(source wt, ⟨order wt, Nat.lt_succ_of_le horderLe⟩), ?_⟩
    exact hsource wt
  exact hle hzT

theorem rotatedLogArithmeticJet_supportedOnPositivePrimePowers
    (k : ℕ) (f : ArithmeticFunction ℂ) (hf : SupportedOnPositivePrimePowers f) :
    SupportedOnPositivePrimePowers (rotatedLogArithmeticJet k f) := by
  intro n hn
  have hfn : f n ≠ 0 := by
    intro hzero
    apply hn
    rw [rotatedLogArithmeticJet_apply, hzero, mul_zero]
  exact hf hfn

/-- Joint packet freeness in the coordinate ordering used by the abstract domain theorem. -/
theorem primeRadial_twoPacketRectangle_algebraicIndependent
    {d : ℕ} [Nonempty (Fin d)]
    (S T : Set Nat.Primes) (hS : S.Infinite) (hT : T.Infinite)
    (hST : Disjoint S T)
    (u : Fin d → ℕ → ℂ) (hu : LinearIndependent ℂ u) (m : ℕ) :
    AlgebraicIndependent ℂ
      (Sum.elim
      (fun col : Fin d × Fin (m + 1) =>
          algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (primePacketRestrictAlgHom S
              (rotatedLogArithmeticJet col.2
                (scalarReplicatedPrimeProfile (u col.1)))))
        (fun col : Fin d × Fin (m + 1) =>
          algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (primePacketRestrictAlgHom T
              (rotatedLogArithmeticJet col.2
                (scalarReplicatedPrimeProfile (u col.1)))))) := by
  let reindex :
      (Fin d × Fin (m + 1)) ⊕ (Fin d × Fin (m + 1)) →
        (Fin d ⊕ Fin d) × Fin (m + 1) :=
    (Equiv.sumProdDistrib (Fin d) (Fin d) (Fin (m + 1))).symm
  have hreindex : Function.Injective reindex :=
    (Equiv.sumProdDistrib (Fin d) (Fin d) (Fin (m + 1))).symm.injective
  have hAI := (primeRadial_two_disjoint_infinite_packets_jet_free
    S T hS hT hST u hu m).comp reindex hreindex
  convert hAI using 1
  funext col
  cases col <;> rfl

/-- Finite-family arithmetic form of Theorem 4.2: every positive-prime-power current in the
differential field of a linearly independent radial palette is a finite constant-coefficient jet
combination of that palette. -/
theorem finite_primeRadial_differentialField_current_eq_jetCombination
    {d : ℕ} [Nonempty (Fin d)]
    (S T : Set Nat.Primes) (hS : S.Infinite) (hT : T.Infinite)
    (hST : Disjoint S T)
    (u : Fin d → ℕ → ℂ) (hu : LinearIndependent ℂ u)
    (f : ArithmeticFunction ℂ) (hf : SupportedOnPositivePrimePowers f)
    (hfield : algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f ∈
      differentialAdjoin ℂ
        (Set.range (fun j : Fin d =>
          algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (scalarReplicatedPrimeProfile (u j))))) :
    ∃ (m : ℕ) (c : Fin d × Fin (m + 1) → ℂ),
      f = ∑ col, c col •
        rotatedLogArithmeticJet col.2 (scalarReplicatedPrimeProfile (u col.1)) := by
  classical
  let source : Fin d → arithmeticFunctionFractionField := fun j =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (scalarReplicatedPrimeProfile (u j))
  obtain ⟨m, hm⟩ :=
    exists_finJetRectangle_of_mem_differentialAdjoin_range source hfield
  let g : Fin d × Fin (m + 1) → ArithmeticFunction ℂ := fun col =>
    rotatedLogArithmeticJet col.2 (scalarReplicatedPrimeProfile (u col.1))
  let r₀ : ArithmeticFunction ℂ →ₐ[ℂ] arithmeticFunctionFractionField :=
    (IsScalarTower.toAlgHom ℂ (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField).comp (primePacketRestrictAlgHom S)
  let r₁ : ArithmeticFunction ℂ →ₐ[ℂ] arithmeticFunctionFractionField :=
    (IsScalarTower.toAlgHom ℂ (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField).comp (primePacketRestrictAlgHom T)
  let r₀₁ : ArithmeticFunction ℂ →ₐ[ℂ] arithmeticFunctionFractionField :=
    (IsScalarTower.toAlgHom ℂ (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField).comp (primePacketRestrictAlgHom (S ∪ T))
  let g₀ : Fin d × Fin (m + 1) → arithmeticFunctionFractionField := fun col => r₀ (g col)
  let g₁ : Fin d × Fin (m + 1) → arithmeticFunctionFractionField := fun col => r₁ (g col)
  have hpacket : AlgebraicIndependent ℂ (Sum.elim g₀ g₁) := by
    simpa [g₀, g₁, r₀, r₁, g] using
      primeRadial_twoPacketRectangle_algebraicIndependent S T hS hT hST u hu m
  have hg₀ : AlgebraicIndependent ℂ g₀ := by
    convert hpacket.comp
      (Sum.inl : (Fin d × Fin (m + 1)) →
        (Fin d × Fin (m + 1)) ⊕ (Fin d × Fin (m + 1)))
      Sum.inl_injective using 1
    funext col
    rfl
  have hgA : AlgebraicIndependent ℂ g :=
    AlgebraicIndependent.of_comp r₀ (by
      convert hg₀ using 1
      funext col
      rfl)
  have hg : AlgebraicIndependent ℂ
      (fun col => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (g col)) := by
    have hmap := hgA.map
      (f := IsScalarTower.toAlgHom ℂ (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField)
      (Set.injOn_of_injective
        (IsFractionRing.injective (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField))
    convert hmap using 1
    funext col
    rfl
  have hrectangle :
      (fun col : Fin d × Fin (m + 1) =>
        differentialJet col.2 (source col.1)) =
      (fun col => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (g col)) := by
    funext col
    exact differentialJet_algebraMap_rotatedLogArithmeticJet col.2
      (scalarReplicatedPrimeProfile (u col.1))
  rw [hrectangle] at hm
  obtain ⟨F, hF⟩ := exists_freeCoordinateEvalMap_eq_of_mem_adjoin
    (fun col => algebraMap (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField (g col)) hg hm
  have hsourceAdd (col : Fin d × Fin (m + 1)) :
      r₀₁ (g col) = g₀ col + g₁ col := by
    change algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (primePacketRestrictAlgHom (S ∪ T) (g col)) =
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (primePacketRestrictAlgHom S (g col)) +
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (primePacketRestrictAlgHom T (g col))
    rw [← map_add, primePacketRestrictAlgHom_union_eq_add S T hST]
    exact rotatedLogArithmeticJet_supportedOnPositivePrimePowers col.2 _
      (scalarReplicatedPrimeProfile_supportedOnPositivePrimePowers (u col.1))
  have hfAdd : r₀₁ f = r₀ f + r₁ f := by
    change algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (primePacketRestrictAlgHom (S ∪ T) f) =
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (primePacketRestrictAlgHom S f) +
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (primePacketRestrictAlgHom T f)
    rw [← map_add, primePacketRestrictAlgHom_union_eq_add S T hST f hf]
  obtain ⟨c, hc, _⟩ := twoPacketRationalFormation_domain_eq_linear
    g hg g₀ g₁ hpacket r₀ r₁ r₀₁ (fun _ => rfl) (fun _ => rfl)
      hsourceAdd F f hF hfAdd
  refine ⟨m, c, ?_⟩
  apply IsFractionRing.injective (ArithmeticFunction ℂ)
    arithmeticFunctionFractionField
  calc
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f =
        freeCoordinateEvalMap
          (fun col => algebraMap (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField (g col)) hg F := hF.symm
    _ = freeCoordinateEvalMap
          (fun col => algebraMap (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField (g col)) hg
          (freeCoordinateLinearForm ℂ (Fin d × Fin (m + 1)) c) := by rw [hc]
    _ = algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (∑ col, c col • g col) := by
        simp [freeCoordinateLinearForm, Algebra.smul_def,
          IsScalarTower.algebraMap_apply ℂ (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField]
    _ = algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (∑ col, c col • rotatedLogArithmeticJet col.2
            (scalarReplicatedPrimeProfile (u col.1))) := by rfl

noncomputable def evenPrimePacket : Set Nat.Primes :=
  Set.range (fun n : ℕ => Infinite.natEmbedding Nat.Primes (2 * n))

noncomputable def oddPrimePacket : Set Nat.Primes :=
  Set.range (fun n : ℕ => Infinite.natEmbedding Nat.Primes (2 * n + 1))

theorem evenPrimePacket_infinite : evenPrimePacket.Infinite := by
  apply Set.infinite_range_of_injective
  exact (Infinite.natEmbedding Nat.Primes).injective.comp (by
    intro a b h
    exact Nat.mul_left_cancel (by omega) h)

theorem oddPrimePacket_infinite : oddPrimePacket.Infinite := by
  apply Set.infinite_range_of_injective
  exact (Infinite.natEmbedding Nat.Primes).injective.comp (by
    intro a b h
    exact Nat.mul_left_cancel (by omega) (Nat.add_right_cancel h))

theorem evenPrimePacket_disjoint_oddPrimePacket :
    Disjoint evenPrimePacket oddPrimePacket := by
  apply Set.disjoint_left.mpr
  rintro p ⟨a, rfl⟩ ⟨b, hab⟩
  have h := (Infinite.natEmbedding Nat.Primes).injective hab
  have hmod := congrArg (fun n : ℕ => n % 2) h
  norm_num at hmod

/-- Differential field generated over `ℂ` by every radial profile in `W`. -/
def primeRadialDifferentialField (W : Submodule ℂ (ℕ → ℂ)) :
    IntermediateField ℂ arithmeticFunctionFractionField :=
  differentialAdjoin ℂ
    (Set.range (fun u : W =>
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (scalarReplicatedPrimeProfile (u : ℕ → ℂ))))

/-- A literal finite constant-coefficient jet representation by profiles in `W`. -/
def HasFinitePrimeRadialJetRepresentation
    (W : Submodule ℂ (ℕ → ℂ)) (f : ArithmeticFunction ℂ) : Prop :=
  ∃ (d m : ℕ) (u : Fin d → W) (c : Fin d × Fin (m + 1) → ℂ),
    f = ∑ col, c col •
      rotatedLogArithmeticJet col.2
        (scalarReplicatedPrimeProfile ((u col.1 : W) : ℕ → ℂ))

theorem scalarReplicatedPrimeProfile_mem_differentialAdjoin_of_mem_span
    {ι : Type*} (u : ι → ℕ → ℂ) {v : ℕ → ℂ}
    (hv : v ∈ Submodule.span ℂ (Set.range u)) :
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (scalarReplicatedPrimeProfile v) ∈
      differentialAdjoin ℂ
        (Set.range (fun i =>
          algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (scalarReplicatedPrimeProfile (u i)))) := by
  let K := differentialAdjoin ℂ
    (Set.range (fun i =>
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (scalarReplicatedPrimeProfile (u i))))
  refine Submodule.span_induction (p := fun v _ =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (scalarReplicatedPrimeProfile v) ∈ K) ?_ ?_ ?_ ?_ hv
  · rintro w ⟨i, rfl⟩
    have hgen : algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (scalarReplicatedPrimeProfile (u i)) ∈
        Set.range (fun i =>
          algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (scalarReplicatedPrimeProfile (u i))) := ⟨i, rfl⟩
    simpa only [differentialJet_zero] using
      differentialJet_mem_differentialAdjoin ℂ hgen 0
  · simp
  · intro x y _ _ hx hy
    simpa using K.add_mem hx hy
  · intro c x _ hx
    have hmul := K.mul_mem (K.algebraMap_mem c) hx
    change algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (scalarReplicatedPrimeProfile (c • x)) ∈ K
    rw [map_smul]
    simpa [Algebra.smul_def,
      IsScalarTower.algebraMap_apply ℂ (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField] using hmul

set_option maxHeartbeats 800000 in
/-- Forward inclusion in Theorem 4.2 for an arbitrary profile subspace. -/
theorem primeRadialDifferentialField_current_hasFiniteJetRepresentation
    (W : Submodule ℂ (ℕ → ℂ)) (f : ArithmeticFunction ℂ)
    (hf : SupportedOnPositivePrimePowers f)
    (hfield : algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f ∈
      primeRadialDifferentialField W) :
    HasFinitePrimeRadialJetRepresentation W f := by
  classical
  let source : W → arithmeticFunctionFractionField := fun u =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (scalarReplicatedPrimeProfile (u : ℕ → ℂ))
  obtain ⟨s, hs⟩ := mem_differentialAdjoin_range_exists_finset source hfield
  let κ := {u : W // u ∈ s}
  let v : κ → ℕ → ℂ := fun i => ((i.1 : W) : ℕ → ℂ)
  have hsRange : source '' (s : Set W) = Set.range (fun i : κ => source i.1) := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
  rw [hsRange] at hs
  obtain ⟨T, hTind, hTspan, _⟩ :=
    exists_maximal_linearIndepOn_finset (R := ℂ) (M := ℕ → ℂ) v
  let τ := {i : κ // i ∈ T}
  let bW : τ → W := fun i => i.1.1
  let b : τ → ℕ → ℂ := fun i => ((bW i : W) : ℕ → ℂ)
  have hb : LinearIndependent ℂ b := by
    exact hTind
  have hvspan (i : κ) : v i ∈ Submodule.span ℂ (Set.range b) := by
    obtain ⟨c, hc, hcv⟩ := hTspan i
    have hsets : v '' (T : Set κ) = Set.range b := by
      ext w
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨j, hj⟩, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨j.1, j.2, rfl⟩
    rw [hsets] at hcv
    have hinv := (Submodule.span ℂ (Set.range b)).smul_mem c⁻¹ hcv
    simpa [smul_smul, hc] using hinv
  let Kb := differentialAdjoin ℂ
    (Set.range (fun j : τ =>
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (scalarReplicatedPrimeProfile (b j))))
  have hle : differentialAdjoin ℂ (Set.range (fun i : κ => source i.1)) ≤ Kb := by
    apply GaloisForLFunctions.differentialAdjoin_le ℂ
    · rintro _ ⟨i, rfl⟩
      exact scalarReplicatedPrimeProfile_mem_differentialAdjoin_of_mem_span
        b (hvspan i)
    · exact derivationClosed_differentialAdjoin_of_constants ℂ
        arithmeticFunctionFractionField_deriv_algebraMap_complex _
  have hfieldB : algebraMap (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField f ∈ Kb := hle hs
  by_cases hT : T.Nonempty
  · letI : Nonempty τ := Finset.nonempty_coe_sort.mpr hT
    let e : τ ≃ Fin (Fintype.card τ) := Fintype.equivFin τ
    letI : Nonempty (Fin (Fintype.card τ)) :=
      ⟨e (Classical.choice (inferInstance : Nonempty τ))⟩
    let uW : Fin (Fintype.card τ) → W := fun j => bW (e.symm j)
    let u : Fin (Fintype.card τ) → ℕ → ℂ := fun j => ((uW j : W) : ℕ → ℂ)
    have hu : LinearIndependent ℂ u := by
      exact hb.comp e.symm e.symm.injective
    have hfieldFin : algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField f ∈
        differentialAdjoin ℂ
          (Set.range (fun j : Fin (Fintype.card τ) =>
            algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
              (scalarReplicatedPrimeProfile (u j)))) := by
      change algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField f ∈ Kb at hfieldB
      convert hfieldB using 1
      congr 1
      ext z
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨e.symm j, by simp [u, uW, b]⟩
      · rintro ⟨j, rfl⟩
        exact ⟨e j, by simp [u, uW, b]⟩
    obtain ⟨m, c, hfc⟩ :=
      finite_primeRadial_differentialField_current_eq_jetCombination
        evenPrimePacket oddPrimePacket evenPrimePacket_infinite
          oddPrimePacket_infinite evenPrimePacket_disjoint_oddPrimePacket
            u hu f hf hfieldFin
    exact ⟨Fintype.card τ, m, uW, c, hfc⟩
  · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    have hKb : Kb = (⊥ : IntermediateField ℂ arithmeticFunctionFractionField) := by
      have hrange : (Set.range (fun j : τ =>
          algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (scalarReplicatedPrimeProfile (b j)))) = ∅ := by
        ext z
        constructor
        · rintro ⟨j, rfl⟩
          exact (hT ⟨j.1, j.2⟩).elim
        · simp
      change differentialAdjoin ℂ
        (Set.range (fun j : τ =>
          algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (scalarReplicatedPrimeProfile (b j)))) = ⊥
      rw [hrange, differentialAdjoin]
      simp [differentialJetSet]
    rw [hKb, IntermediateField.mem_bot] at hfieldB
    obtain ⟨c, hc⟩ := hfieldB
    have hfconst : f = algebraMap ℂ (ArithmeticFunction ℂ) c := by
      apply IsFractionRing.injective (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField
      simpa only [IsScalarTower.algebraMap_apply ℂ (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField] using hc.symm
    have hc0 : c = 0 := by
      by_contra hc0
      have hf1 : f 1 ≠ 0 := by
        rw [hfconst, Algebra.algebraMap_eq_smul_one,
          ArithmeticFunction.smul_map, ArithmeticFunction.one_apply, if_pos rfl]
        simpa using hc0
      obtain ⟨p, e, hp⟩ := hf hf1
      have hpdiv : (p : ℕ) ∣ 1 := by
        rw [hp]
        exact dvd_pow_self (p : ℕ) (Nat.succ_ne_zero e)
      exact p.2.not_dvd_one hpdiv
    refine ⟨0, 0, Fin.elim0, (fun col => Fin.elim0 col.1), ?_⟩
    simp [hfconst, hc0]

theorem supportedOnPositivePrimePowers_add
    {f g : ArithmeticFunction ℂ}
    (hf : SupportedOnPositivePrimePowers f)
    (hg : SupportedOnPositivePrimePowers g) :
    SupportedOnPositivePrimePowers (f + g) := by
  intro n hn
  by_cases hfn : f n = 0
  · apply hg
    intro hgn
    apply hn
    simp [hfn, hgn]
  · exact hf hfn

theorem supportedOnPositivePrimePowers_smul
    (c : ℂ) {f : ArithmeticFunction ℂ}
    (hf : SupportedOnPositivePrimePowers f) :
    SupportedOnPositivePrimePowers (c • f) := by
  intro n hn
  apply hf
  intro hfn
  apply hn
  simp [ArithmeticFunction.smul_map, hfn]

theorem supportedOnPositivePrimePowers_sum
    {ι : Type*} (s : Finset ι) (f : ι → ArithmeticFunction ℂ)
    (hf : ∀ i ∈ s, SupportedOnPositivePrimePowers (f i)) :
    SupportedOnPositivePrimePowers (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using supportedOnPositivePrimePowers_zero
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact supportedOnPositivePrimePowers_add (hf i (by simp))
        (ih (fun j hj => hf j (by simp [hj])))

/-- Reverse inclusion in Theorem 4.2. -/
theorem primeRadialDifferentialField_current_of_hasFiniteJetRepresentation
    (W : Submodule ℂ (ℕ → ℂ)) (f : ArithmeticFunction ℂ)
    (hrep : HasFinitePrimeRadialJetRepresentation W f) :
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f ∈
        primeRadialDifferentialField W ∧
      SupportedOnPositivePrimePowers f := by
  classical
  obtain ⟨d, m, u, c, rfl⟩ := hrep
  let K := primeRadialDifferentialField W
  constructor
  · rw [map_sum]
    apply K.sum_mem
    intro col hcol
    have hsource : algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField
          (scalarReplicatedPrimeProfile ((u col.1 : W) : ℕ → ℂ)) ∈ K := by
      exact GaloisForLFunctions.subset_differentialAdjoin ℂ _
        ⟨u col.1, rfl⟩
    have hjet := differentialJet_mem_differentialAdjoin ℂ
      (s := Set.range (fun w : W =>
        algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (scalarReplicatedPrimeProfile ((w : W) : ℕ → ℂ))))
      ⟨u col.1, rfl⟩ (col.2 : ℕ)
    rw [differentialJet_algebraMap_rotatedLogArithmeticJet] at hjet
    have hmul := K.mul_mem (K.algebraMap_mem (c col)) hjet
    simpa [Algebra.smul_def,
      IsScalarTower.algebraMap_apply ℂ (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField] using hmul
  · apply supportedOnPositivePrimePowers_sum Finset.univ
      (fun col => c col • rotatedLogArithmeticJet col.2
        (scalarReplicatedPrimeProfile ((u col.1 : W) : ℕ → ℂ)))
    intro col hcol
    exact supportedOnPositivePrimePowers_smul (c col)
      (rotatedLogArithmeticJet_supportedOnPositivePrimePowers col.2 _
        (scalarReplicatedPrimeProfile_supportedOnPositivePrimePowers
          ((u col.1 : W) : ℕ → ℂ)))

/-- Theorem 4.2 `(PFR.18)`: the positive-prime-power sector of the radial differential field is
exactly the finite constant-coefficient span of source jets. -/
theorem primeRadial_differentialField_primitive_rigidity
    (W : Submodule ℂ (ℕ → ℂ)) (f : ArithmeticFunction ℂ) :
    (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f ∈
        primeRadialDifferentialField W ∧
      SupportedOnPositivePrimePowers f) ↔
    HasFinitePrimeRadialJetRepresentation W f := by
  constructor
  · rintro ⟨hfield, hf⟩
    exact primeRadialDifferentialField_current_hasFiniteJetRepresentation W f hf hfield
  · exact primeRadialDifferentialField_current_of_hasFiniteJetRepresentation W f

/-- Finite source jets are algebraically independent whenever their profile family is linearly
independent. -/
theorem finite_primeRadial_jets_algebraicIndependent
    {d : ℕ} [Nonempty (Fin d)]
    (u : Fin d → ℕ → ℂ) (hu : LinearIndependent ℂ u) (m : ℕ) :
    AlgebraicIndependent ℂ
      (fun col : Fin d × Fin (m + 1) =>
        algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (rotatedLogArithmeticJet col.2
            (scalarReplicatedPrimeProfile (u col.1)))) := by
  let g : Fin d × Fin (m + 1) → ArithmeticFunction ℂ := fun col =>
    rotatedLogArithmeticJet col.2 (scalarReplicatedPrimeProfile (u col.1))
  let r : ArithmeticFunction ℂ →ₐ[ℂ] arithmeticFunctionFractionField :=
    (IsScalarTower.toAlgHom ℂ (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField).comp
        (primePacketRestrictAlgHom evenPrimePacket)
  let g₀ : Fin d × Fin (m + 1) → arithmeticFunctionFractionField := fun col => r (g col)
  let g₁ : Fin d × Fin (m + 1) → arithmeticFunctionFractionField := fun col =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (primePacketRestrictAlgHom oddPrimePacket (g col))
  have hpacket : AlgebraicIndependent ℂ (Sum.elim g₀ g₁) := by
    simpa [g₀, g₁, r, g] using
      primeRadial_twoPacketRectangle_algebraicIndependent
        evenPrimePacket oddPrimePacket evenPrimePacket_infinite
          oddPrimePacket_infinite evenPrimePacket_disjoint_oddPrimePacket u hu m
  have hg₀ : AlgebraicIndependent ℂ g₀ := by
    convert hpacket.comp
      (Sum.inl : (Fin d × Fin (m + 1)) →
        (Fin d × Fin (m + 1)) ⊕ (Fin d × Fin (m + 1)))
      Sum.inl_injective using 1
    funext col
    rfl
  have hgA : AlgebraicIndependent ℂ g :=
    AlgebraicIndependent.of_comp r (by
      convert hg₀ using 1
      funext col
      rfl)
  have hmap := hgA.map
    (f := IsScalarTower.toAlgHom ℂ (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField)
    (Set.injOn_of_injective
      (IsFractionRing.injective (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField))
  convert hmap using 1
  funext col
  rfl

/-- Fixed-profile-basis uniqueness clause of Theorem 4.2, on every common finite jet rectangle. -/
theorem finite_primeRadial_jetCoefficients_unique
    {d : ℕ} [Nonempty (Fin d)]
    (u : Fin d → ℕ → ℂ) (hu : LinearIndependent ℂ u) (m : ℕ)
    (c e : Fin d × Fin (m + 1) → ℂ)
    (hce : (∑ col, c col • rotatedLogArithmeticJet col.2
        (scalarReplicatedPrimeProfile (u col.1))) =
      ∑ col, e col • rotatedLogArithmeticJet col.2
        (scalarReplicatedPrimeProfile (u col.1))) :
    c = e := by
  let g : Fin d × Fin (m + 1) → arithmeticFunctionFractionField := fun col =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (rotatedLogArithmeticJet col.2
        (scalarReplicatedPrimeProfile (u col.1)))
  have hg : AlgebraicIndependent ℂ g :=
    finite_primeRadial_jets_algebraicIndependent u hu m
  let eval := freeCoordinateEvalMap g hg
  have heval (a : Fin d × Fin (m + 1) → ℂ) :
      eval (freeCoordinateLinearForm ℂ (Fin d × Fin (m + 1)) a) =
        ∑ col, algebraMap ℂ arithmeticFunctionFractionField (a col) * g col := by
    simp [eval, freeCoordinateLinearForm]
  have hsum : (∑ col, algebraMap ℂ arithmeticFunctionFractionField (c col) * g col) =
      ∑ col, algebraMap ℂ arithmeticFunctionFractionField (e col) * g col := by
    simpa [g, Algebra.smul_def,
      IsScalarTower.algebraMap_apply ℂ (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField] using
      congrArg (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField) hce
  have hlinear : freeCoordinateLinearForm ℂ (Fin d × Fin (m + 1)) c =
      freeCoordinateLinearForm ℂ (Fin d × Fin (m + 1)) e := by
    apply eval.injective
    change eval (freeCoordinateLinearForm ℂ (Fin d × Fin (m + 1)) c) =
      eval (freeCoordinateLinearForm ℂ (Fin d × Fin (m + 1)) e)
    rw [heval c, heval e]
    exact hsum
  funext col
  apply (algebraMap ℂ
    (FreeCoordinateRationalField ℂ (Fin d × Fin (m + 1)))).injective
  calc
    algebraMap ℂ (FreeCoordinateRationalField ℂ (Fin d × Fin (m + 1))) (c col) =
        freeCoordinateDerivation ℂ (Fin d × Fin (m + 1)) col
          (freeCoordinateLinearForm ℂ (Fin d × Fin (m + 1)) c) := by
      rw [freeCoordinateDerivation_linearForm]
    _ = freeCoordinateDerivation ℂ (Fin d × Fin (m + 1)) col
          (freeCoordinateLinearForm ℂ (Fin d × Fin (m + 1)) e) := by rw [hlinear]
    _ = algebraMap ℂ (FreeCoordinateRationalField ℂ (Fin d × Fin (m + 1))) (e col) :=
      freeCoordinateDerivation_linearForm e col

/-- Corollary 5.1: finite rational differential formation from an independent radial palette
cannot return a new positive-prime-power current. -/
theorem finite_rational_formation_no_new_primeAdditive_current
    {d : ℕ} [Nonempty (Fin d)]
    (u : Fin d → ℕ → ℂ) (hu : LinearIndependent ℂ u)
    (f : ArithmeticFunction ℂ) (hf : SupportedOnPositivePrimePowers f)
    (hfield : algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f ∈
      differentialAdjoin ℂ
        (Set.range (fun j : Fin d =>
          algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (scalarReplicatedPrimeProfile (u j))))) :
    ∃ (m : ℕ) (c : Fin d × Fin (m + 1) → ℂ),
      f = ∑ col, c col •
        rotatedLogArithmeticJet col.2 (scalarReplicatedPrimeProfile (u col.1)) :=
  finite_primeRadial_differentialField_current_eq_jetCombination
    evenPrimePacket oddPrimePacket evenPrimePacket_infinite oddPrimePacket_infinite
      evenPrimePacket_disjoint_oddPrimePacket u hu f hf hfield

end

end GaloisForLFunctions.HTGeometry
