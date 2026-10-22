import GaloisForLFunctions.RHTower.Deninger.DeningerPrimePacketFiniteCyclotomicStage
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Frobenius-orbit evaluations span every finite Deninger packet mode

At a cyclotomic stage `n` coprime to `p`, the transverse Deninger packet is

`(ZMod n)ˣ / ⟨p⟩`.

For `j : ZMod n`, evaluation of the `j`-th root character at a unit `u` is the additive
character `exp(2πi j u / n)`.  Averaging this evaluation over the finite Frobenius subgroup
`⟨p⟩` makes it descend to the quotient.

The main theorem proves that these descended orbit evaluations span **every** complex-valued
function on the finite packet quotient.  Thus finite rational-cyclotomic evaluation data sees all
finite packet modes, including every mean-zero mode; it does not collapse to the valuation or
constant channel.

The proof is exact finite Fourier inversion.  First extend a function on `(ZMod n)ˣ` by zero to
`ZMod n`, expand it in the full additive Fourier basis, and then apply the Reynolds average over
the subgroup.  No cardinality comparison or non-canonical basis choice is used.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

/-- Additive root evaluation at a finite cyclotomic unit. -/
def deningerFiniteUnitEvaluation
    (n : ℕ) [NeZero n] (j : ZMod n) (u : (ZMod n)ˣ) : ℂ :=
  ZMod.stdAddChar (j * (u : ZMod n))

/-- Root evaluations indexed by all `j : ZMod n` span every function on the unit group.

This is Fourier inversion after extending the function by zero off `(ZMod n)ˣ`. -/
theorem deningerFiniteUnitEvaluation_span
    (n : ℕ) [NeZero n] (f : (ZMod n)ˣ → ℂ) :
    ∃ c : ZMod n → ℂ, ∀ u : (ZMod n)ˣ,
      f u = ∑ j : ZMod n, c j * deningerFiniteUnitEvaluation n j u := by
  let Φ : ZMod n → ℂ :=
    Function.extend ((↑) : (ZMod n)ˣ → ZMod n) f 0
  let Ψ : ZMod n → ℂ := ZMod.dft Φ
  refine ⟨fun j => (n : ℂ)⁻¹ * Ψ j, ?_⟩
  intro u
  have hΦ : Φ (u : ZMod n) = f u := by
    exact Units.val_injective.extend_apply f 0 u
  have hinv := ZMod.invDFT_apply (Ψ := Ψ) (k := (u : ZMod n))
  have hΨ : ZMod.dft.symm Ψ = Φ := by
    dsimp [Ψ]
    exact LinearEquiv.symm_apply_apply ZMod.dft Φ
  rw [hΨ, hΦ] at hinv
  rw [hinv]
  simp only [deningerFiniteUnitEvaluation, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Reynolds average of a root evaluation over a finite subgroup of cyclotomic units. -/
def deningerFiniteOrbitEvaluation
    (n : ℕ) [NeZero n] (H : Subgroup (ZMod n)ˣ)
    (j : ZMod n) (u : (ZMod n)ˣ) : ℂ := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  exact
    (Fintype.card H : ℂ)⁻¹ *
      ∑ h : H, deningerFiniteUnitEvaluation n j (u * h.1)

/-- Orbit evaluation is invariant under right multiplication by the averaging subgroup. -/
theorem deningerFiniteOrbitEvaluation_mul
    (n : ℕ) [NeZero n] (H : Subgroup (ZMod n)ˣ)
    (j : ZMod n) (u : (ZMod n)ˣ) (h₀ : H) :
    deningerFiniteOrbitEvaluation n H j (u * h₀.1) =
      deningerFiniteOrbitEvaluation n H j u := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  simp only [deningerFiniteOrbitEvaluation]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft h₀)
    (fun h : H => deningerFiniteUnitEvaluation n j ((u * h₀.1) * h.1))
    (fun h : H => deningerFiniteUnitEvaluation n j (u * h.1)) ?_
  intro h
  congr 1
  exact mul_assoc u h₀.1 h.1

/-- Reynolds-averaged root evaluations span every subgroup-invariant function. -/
theorem deningerFiniteOrbitEvaluation_span_invariant
    (n : ℕ) [NeZero n] (H : Subgroup (ZMod n)ˣ)
    (f : (ZMod n)ˣ → ℂ)
    (hf : ∀ (u : (ZMod n)ˣ) (h : H), f (u * h.1) = f u) :
    ∃ c : ZMod n → ℂ, ∀ u : (ZMod n)ˣ,
      f u = ∑ j : ZMod n,
        c j * deningerFiniteOrbitEvaluation n H j u := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  obtain ⟨c, hc⟩ := deningerFiniteUnitEvaluation_span n f
  refine ⟨c, ?_⟩
  intro u
  have hcardNat : Fintype.card H ≠ 0 := Fintype.card_ne_zero
  have hcard : (Fintype.card H : ℂ) ≠ 0 := by
    exact_mod_cast hcardNat
  calc
    f u =
        (Fintype.card H : ℂ)⁻¹ * ∑ h : H, f (u * h.1) := by
      simp_rw [hf u]
      simp [hcard]
    _ = (Fintype.card H : ℂ)⁻¹ *
        ∑ h : H, ∑ j : ZMod n,
          c j * deningerFiniteUnitEvaluation n j (u * h.1) := by
      congr 1
      apply Finset.sum_congr rfl
      intro h _
      exact hc (u * h.1)
    _ = ∑ j : ZMod n,
        c j * deningerFiniteOrbitEvaluation n H j u := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [deningerFiniteOrbitEvaluation]
      calc
        (Fintype.card H : ℂ)⁻¹ *
              ∑ h : H, c j * deningerFiniteUnitEvaluation n j (u * h.1) =
            ∑ h : H, (Fintype.card H : ℂ)⁻¹ *
              (c j * deningerFiniteUnitEvaluation n j (u * h.1)) := by
          rw [Finset.mul_sum]
        _ = ∑ h : H, (c j * (Fintype.card H : ℂ)⁻¹) *
              deningerFiniteUnitEvaluation n j (u * h.1) := by
          apply Finset.sum_congr rfl
          intro h _
          ring
        _ = c j * ((Fintype.card H : ℂ)⁻¹ *
              ∑ h : H, deningerFiniteUnitEvaluation n j (u * h.1)) := by
          rw [← Finset.mul_sum]
          ring

/-- Orbit evaluation descended to the finite quotient by the averaging subgroup. -/
def deningerFiniteOrbitEvaluationQuotient
    (n : ℕ) [NeZero n] (H : Subgroup (ZMod n)ˣ)
    (j : ZMod n) (q : (ZMod n)ˣ ⧸ H) : ℂ :=
  q.liftOn'
    (deningerFiniteOrbitEvaluation n H j)
    (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply] at hab
      let h : H := ⟨a⁻¹ * b, hab⟩
      have hab' : a * h.1 = b := by
        simp [h]
      rw [← hab']
      exact (deningerFiniteOrbitEvaluation_mul n H j a h).symm)

@[simp] theorem deningerFiniteOrbitEvaluationQuotient_mk
    (n : ℕ) [NeZero n] (H : Subgroup (ZMod n)ˣ)
    (j : ZMod n) (u : (ZMod n)ˣ) :
    deningerFiniteOrbitEvaluationQuotient n H j
        (QuotientGroup.mk u : (ZMod n)ˣ ⧸ H) =
      deningerFiniteOrbitEvaluation n H j u :=
  rfl

/-- Descended orbit evaluations span every function on the finite subgroup quotient. -/
theorem deningerFiniteOrbitEvaluationQuotient_span
    (n : ℕ) [NeZero n] (H : Subgroup (ZMod n)ˣ)
    (F : ((ZMod n)ˣ ⧸ H) → ℂ) :
    ∃ c : ZMod n → ℂ, ∀ q : (ZMod n)ˣ ⧸ H,
      F q = ∑ j : ZMod n,
        c j * deningerFiniteOrbitEvaluationQuotient n H j q := by
  let f : (ZMod n)ˣ → ℂ := fun u => F (QuotientGroup.mk u)
  have hf : ∀ (u : (ZMod n)ˣ) (h : H), f (u * h.1) = f u := by
    intro u h
    dsimp only [f]
    congr 1
    rw [QuotientGroup.mk_mul]
    rw [show (QuotientGroup.mk h.1 : (ZMod n)ˣ ⧸ H) = 1 from
      (QuotientGroup.eq_one_iff h.1).2 h.2]
    exact mul_one (QuotientGroup.mk u : (ZMod n)ˣ ⧸ H)
  obtain ⟨c, hc⟩ :=
    deningerFiniteOrbitEvaluation_span_invariant n H f hf
  refine ⟨c, ?_⟩
  intro q
  induction q using Quotient.inductionOn' with
  | _ u =>
      simpa only [f, deningerFiniteOrbitEvaluationQuotient_mk] using hc u

/-- Finite subgroup generated by arithmetic Frobenius `p mod n`. -/
def deningerFiniteFrobeniusSubgroup
    (p n : ℕ) [NeZero n] (hpn : p.Coprime n) :
    Subgroup (ZMod n)ˣ :=
  Subgroup.zpowers (ZMod.unitOfCoprime p hpn)

/-- Frobenius-orbit evaluation on the finite Deninger packet quotient. -/
def deningerFiniteFrobeniusOrbitEvaluation
    (p n : ℕ) [NeZero n] (hpn : p.Coprime n)
    (j : ZMod n)
    (q : (ZMod n)ˣ ⧸ deningerFiniteFrobeniusSubgroup p n hpn) : ℂ :=
  deningerFiniteOrbitEvaluationQuotient n
    (deningerFiniteFrobeniusSubgroup p n hpn) j q

/-- **Full finite packet visibility.** Frobenius-orbit root evaluations span the whole function
space on `(ZMod n)ˣ / ⟨p⟩`. -/
theorem deningerFiniteFrobeniusOrbitEvaluation_span
    (p n : ℕ) [NeZero n] (hpn : p.Coprime n)
    (F : ((ZMod n)ˣ ⧸ deningerFiniteFrobeniusSubgroup p n hpn) → ℂ) :
    ∃ c : ZMod n → ℂ,
      ∀ q : (ZMod n)ˣ ⧸ deningerFiniteFrobeniusSubgroup p n hpn,
        F q = ∑ j : ZMod n,
          c j * deningerFiniteFrobeniusOrbitEvaluation p n hpn j q :=
  deningerFiniteOrbitEvaluationQuotient_span n
    (deningerFiniteFrobeniusSubgroup p n hpn) F

/-- Canonical finite enumeration of the Frobenius packet quotient. -/
noncomputable instance deningerFiniteFrobeniusQuotientFintype
    (p n : ℕ) [NeZero n] (hpn : p.Coprime n) :
    Fintype ((ZMod n)ˣ ⧸ deningerFiniteFrobeniusSubgroup p n hpn) :=
  Fintype.ofFinite _

/-- **Mean-zero source visibility.**  On every nontrivial finite Frobenius packet quotient, a
finite linear combination of orbit root evaluations is nonzero but has total mass zero.

This is the finite-stage obstruction to replacing rational-cyclotomic source restriction by the
scalar packet average: source evaluations already contain a genuine transverse mode. -/
theorem deningerFiniteFrobeniusOrbitEvaluation_exists_zeroSum_nonzero
    (p n : ℕ) [NeZero n] (hpn : p.Coprime n)
    [Nontrivial ((ZMod n)ˣ ⧸ deningerFiniteFrobeniusSubgroup p n hpn)] :
    ∃ c : ZMod n → ℂ,
      (∑ q : (ZMod n)ˣ ⧸ deningerFiniteFrobeniusSubgroup p n hpn,
        ∑ j : ZMod n,
          c j * deningerFiniteFrobeniusOrbitEvaluation p n hpn j q) = 0 ∧
      ∃ q : (ZMod n)ˣ ⧸ deningerFiniteFrobeniusSubgroup p n hpn,
        (∑ j : ZMod n,
          c j * deningerFiniteFrobeniusOrbitEvaluation p n hpn j q) ≠ 0 := by
  classical
  let Q := (ZMod n)ˣ ⧸ deningerFiniteFrobeniusSubgroup p n hpn
  let q₀ : Q := Classical.choice inferInstance
  obtain ⟨q₁, hq₁⟩ : ∃ q₁ : Q, q₁ ≠ q₀ := exists_ne q₀
  let F : Q → ℂ := fun q =>
    (if q = q₀ then 1 else 0) - (if q = q₁ then 1 else 0)
  obtain ⟨c, hc⟩ :=
    deningerFiniteFrobeniusOrbitEvaluation_span p n hpn F
  refine ⟨c, ?_, q₀, ?_⟩
  · simp_rw [← hc]
    simp [F, Finset.sum_sub_distrib, eq_comm]
  · rw [← hc]
    simp [F, hq₁.symm]

/-- A finite noncyclic group remains nontrivial after quotienting by any cyclic subgroup. -/
theorem deningerQuotientZpowersNontrivial_of_not_isCyclic
    {G : Type*} [Group G] [Finite G] (a : G) (hG : ¬ IsCyclic G) :
    Nontrivial (G ⧸ Subgroup.zpowers a) := by
  rw [QuotientGroup.nontrivial_iff]
  intro htop
  exact hG (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨a, htop⟩)

/-- Uniform finite transverse detector: modulus `15` at `p = 2`, and modulus `8` at every odd
prime. -/
def deningerPrimeTransverseCyclotomicStage (p : Nat.Primes) : ℕ :=
  if (p : ℕ) = 2 then 15 else 8

instance deningerPrimeTransverseCyclotomicStageNeZero (p : Nat.Primes) :
    NeZero (deningerPrimeTransverseCyclotomicStage p) := by
  constructor
  unfold deningerPrimeTransverseCyclotomicStage
  split <;> norm_num

/-- The uniform transverse detector is prime to the residue characteristic. -/
theorem deningerPrimeTransverseCyclotomicStage_coprime (p : Nat.Primes) :
    (p : ℕ).Coprime (deningerPrimeTransverseCyclotomicStage p) := by
  by_cases hp : (p : ℕ) = 2
  · rw [deningerPrimeTransverseCyclotomicStage, if_pos hp, hp]
    norm_num
  · let l2 : {l : Nat.Primes // (l : ℕ) ≠ (p : ℕ)} :=
      ⟨⟨2, Nat.prime_two⟩, Ne.symm hp⟩
    rw [deningerPrimeTransverseCyclotomicStage, if_neg hp]
    convert deningerPrime_coprime_awayPrime_pow p l2 3 using 1
    norm_num [l2]

/-- Units modulo `15` are noncyclic. -/
theorem deningerUnitsModFifteen_not_isCyclic :
    ¬ IsCyclic (ZMod 15)ˣ := by
  simpa using ZMod.not_isCyclic_units_of_mul_coprime 3 5
    (by exact ⟨1, rfl⟩) (by norm_num)
    (by exact ⟨2, rfl⟩) (by norm_num) (by norm_num)

/-- The unit group at the uniform transverse detector is noncyclic for every prime. -/
theorem deningerPrimeTransverseCyclotomicStage_not_isCyclic
    (p : Nat.Primes) :
    ¬ IsCyclic (ZMod (deningerPrimeTransverseCyclotomicStage p))ˣ := by
  by_cases hp : (p : ℕ) = 2
  · rw [deningerPrimeTransverseCyclotomicStage, if_pos hp]
    exact deningerUnitsModFifteen_not_isCyclic
  · rw [deningerPrimeTransverseCyclotomicStage, if_neg hp]
    exact ZMod.not_isCyclic_units_eight

/-- Explicit nontrivial finite quotient detected inside every prime packet. -/
abbrev DeningerPrimeTransverseFinitePacket (p : Nat.Primes) :=
  (ZMod (deningerPrimeTransverseCyclotomicStage p))ˣ ⧸
    deningerFiniteFrobeniusSubgroup
      (p : ℕ) (deningerPrimeTransverseCyclotomicStage p)
      (deningerPrimeTransverseCyclotomicStage_coprime p)

/-- Every prime has an explicit nontrivial transverse finite packet. -/
noncomputable instance deningerPrimeTransverseFinitePacketNontrivial
    (p : Nat.Primes) :
    Nontrivial (DeningerPrimeTransverseFinitePacket p) :=
  deningerQuotientZpowersNontrivial_of_not_isCyclic
    (ZMod.unitOfCoprime (p : ℕ)
      (deningerPrimeTransverseCyclotomicStage_coprime p))
    (deningerPrimeTransverseCyclotomicStage_not_isCyclic p)

/-- **Uniform transverse source mode at every prime.**  At modulus `8` or `15`, according to `p`,
one finite linear combination of Frobenius-orbit root evaluations is nonzero and has zero total
mass on the finite packet quotient. -/
theorem deningerPrimeTransverseFinitePacket_exists_zeroSum_nonzero
    (p : Nat.Primes) :
    ∃ c : ZMod (deningerPrimeTransverseCyclotomicStage p) → ℂ,
      (∑ q : DeningerPrimeTransverseFinitePacket p,
        ∑ j : ZMod (deningerPrimeTransverseCyclotomicStage p),
          c j * deningerFiniteFrobeniusOrbitEvaluation
            (p : ℕ) (deningerPrimeTransverseCyclotomicStage p)
            (deningerPrimeTransverseCyclotomicStage_coprime p) j q) = 0 ∧
      ∃ q : DeningerPrimeTransverseFinitePacket p,
        (∑ j : ZMod (deningerPrimeTransverseCyclotomicStage p),
          c j * deningerFiniteFrobeniusOrbitEvaluation
            (p : ℕ) (deningerPrimeTransverseCyclotomicStage p)
            (deningerPrimeTransverseCyclotomicStage_coprime p) j q) ≠ 0 :=
  deningerFiniteFrobeniusOrbitEvaluation_exists_zeroSum_nonzero
    (p : ℕ) (deningerPrimeTransverseCyclotomicStage p)
      (deningerPrimeTransverseCyclotomicStage_coprime p)

/-- Equivalent invariant-function form of full finite packet visibility. -/
theorem deningerFiniteFrobeniusOrbitEvaluation_span_invariant
    (p n : ℕ) [NeZero n] (hpn : p.Coprime n)
    (f : (ZMod n)ˣ → ℂ)
    (hf : ∀ (u : (ZMod n)ˣ) (h : deningerFiniteFrobeniusSubgroup p n hpn),
      f (u * h.1) = f u) :
    ∃ c : ZMod n → ℂ, ∀ u : (ZMod n)ˣ,
      f u = ∑ j : ZMod n,
        c j * deningerFiniteOrbitEvaluation n
          (deningerFiniteFrobeniusSubgroup p n hpn) j u :=
  deningerFiniteOrbitEvaluation_span_invariant n
    (deningerFiniteFrobeniusSubgroup p n hpn) f hf

end

end RHTower
