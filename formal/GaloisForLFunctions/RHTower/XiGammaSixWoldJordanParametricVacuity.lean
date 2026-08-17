import GaloisForLFunctions.RHTower.XiGammaSixWoldJordanSingularSourceDescent

/-!
# Parametric vacuity of the Wold--Jordan actual-source descent

`XiGammaSixWoldJordanSingularSourceDescent` proves that the existence of a continuous reporter on
the Big--Witt singular one-leg graph agreeing with the literal Wold--Jordan energy on the genuine
normalized fixed-left rows is equivalent to `Re q = 1/2`, hence globally equivalent to RH.

This module isolates *what that equivalence actually uses*.  The finite Wold--Jordan energy
reporter is a `Finsupp.lsum` whose coefficient at an ordered edge `(p, r)` is
`thetaGammaSixWoldHorizontalCarrier p q ^ 2 = A q / p` with `A q` the Gamma-six harmonic weight.
So the reporter — and therefore the whole descent predicate — depends on the Xi copy `q` **only
through the single real scalar** `A q`.  Nothing else in the construction (Big--Witt rows, one-leg
trace, ambient admission, singular vector, Green--Stokes boundary calculus) sees `q` at all.

We make this precise by defining the descent predicate for a *free* real parameter `A`, proving

* `abstractPrimeReciprocalSourceDescends A ↔ A = 0` (Theorem `abstractPrimeReciprocalSourceDescends_iff`),
* `deningerBigWittWoldJordanActualSourceEnergyDescends q ↔ abstractPrimeReciprocalSourceDescends (A q)`,
* `¬ ∀ A : ℝ, abstractPrimeReciprocalSourceDescends A` (witness `A = 1`).

The consequence is a **no-go for the two-port secondary source character**: the sought canonical
source `2`-cell `H` with `∂H = P_{p,N} - P_{r,N} + exact`, together with a quadratic Stokes law
`W(∂H) = 0`, is to be produced from Big--Witt/Gamma/Green--Stokes naturality.  All of that data is
defined verbatim for every value of the free parameter `A`; hence any construction of `H` from it
would prove `abstractPrimeReciprocalSourceDescends A` for every `A`, which is false at `A = 1`.
Therefore no naturality-only construction of the two-port secondary source character exists, and
the RH-equivalence proved in the parent module is a pullback of an arithmetic-free scalar condition
along `q ↦ A q` — a receiver, never a producer.

Everything here is unconditional.
-/

open Complex Filter Function Set Topology
open scoped BigOperators

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-! ## A general prime-labelled energy reporter -/

/-- The finite energy reporter attached to an arbitrary real coefficient function of the *left*
prime label.  The literal Wold--Jordan reporter is the special case
`c p = thetaGammaSixWoldHorizontalCarrier p q ^ 2`. -/
def primeLabelledEnergyReporter (c : Nat.Primes → ℝ) :
    (DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ fun i => LinearMap.toSpanSingleton ℂ ℂ ((c i.1.1 : ℝ) : ℂ)

@[simp] theorem primeLabelledEnergyReporter_single
    (c : Nat.Primes → ℝ) (i : DeningerCalderonWittCrossPrimePacketIndex) (z : ℂ) :
    primeLabelledEnergyReporter c (Finsupp.single i z) = ((c i.1.1 : ℝ) : ℂ) * z := by
  classical
  simp [primeLabelledEnergyReporter, Finsupp.lsum_apply, LinearMap.toSpanSingleton, mul_comm]

/-- The literal Wold--Jordan energy reporter is the prime-labelled reporter of the carrier square. -/
theorem deningerBigWittCrossPairFiniteWoldJordanEnergyReporter_eq
    (q : XiZeroCopy) :
    deningerBigWittCrossPairFiniteWoldJordanEnergyReporter q =
      primeLabelledEnergyReporter (fun p => thetaGammaSixWoldHorizontalCarrier p q ^ 2) := by
  classical
  refine Finsupp.lhom_ext ?_
  intro i z
  rw [deningerBigWittCrossPairFiniteWoldJordanEnergyReporter_single,
    primeLabelledEnergyReporter_single]

/-- On a genuine trace-normalized fixed-left Big--Witt row the prime-labelled reporter returns the
coefficient at the row's left prime, for *every* coefficient function. -/
theorem primeLabelledEnergyReporter_woldFixedLeftRightEdgeNormalizedPacket
    (c : Nat.Primes → ℝ) (a n : ℕ) :
    primeLabelledEnergyReporter c
        (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n) =
      ((c (nthPrimeSubtype a) : ℝ) : ℂ) := by
  classical
  set M := deningerBigWittWoldFixedLeftRightEdgeMass a (n + 1) with hMdef
  have hM : (M : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (deningerBigWittWoldFixedLeftRightEdgeMass_pos a n))
  have hraw :
      primeLabelledEnergyReporter c
          (deningerBigWittWoldFixedLeftRightEdgeRawPacket a (n + 1)) =
        ((c (nthPrimeSubtype a) : ℝ) : ℂ) * (M : ℂ) := by
    rw [deningerBigWittWoldFixedLeftRightEdgeRawPacket, map_sum,
      deningerBigWittWoldFixedLeftRightEdgePrefix, Finset.sum_map]
    have hsum :
        (∑ k ∈ Finset.range (n + 1),
          primeLabelledEnergyReporter c
            (Finsupp.single (deningerBigWittWoldFixedLeftRightEdgeEmbedding a k)
              (deningerBigWittCrossPrimePacketRawCoefficient
                (deningerBigWittWoldFixedLeftRightEdgeEmbedding a k)))) =
        ∑ k ∈ Finset.range (n + 1),
          ((c (nthPrimeSubtype a) : ℝ) : ℂ) *
            (deningerBigWittWoldFixedLeftRightEdgeWeight a k : ℂ) := by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [primeLabelledEnergyReporter_single,
        deningerBigWittCrossPrimePacketRawCoefficient_woldFixedLeftRightEdge]
      rfl
    rw [hsum, ← Finset.mul_sum]
    rw [hMdef, deningerBigWittWoldFixedLeftRightEdgeMass]
    push_cast
    rfl
  rw [deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket, map_smul, hraw]
  change (M : ℂ)⁻¹ * (((c (nthPrimeSubtype a) : ℝ) : ℂ) * (M : ℂ)) = _
  field_simp

/-! ## The descent predicate for a free real parameter -/

/-- The Wold--Jordan actual-source descent predicate with the Gamma-six harmonic weight replaced by
a **free real parameter** `A`.  The prime-labelled energies are `A / p`, exactly the shape produced
by the carrier square, but with no Xi input whatsoever. -/
def AbstractPrimeReciprocalSourceDescends (A : ℝ) : Prop :=
  ∃ reporter : DeningerBigWittCrossPairSingularOneLegGraph →L[ℂ] ℂ,
    ∀ a n : ℕ,
      reporter (deningerBigWittCrossPairFiniteOneLegGraphAdmission
        (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n)) =
      primeLabelledEnergyReporter (fun p => A / (p : ℕ))
        (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n)

theorem abstractPrimeReciprocalSourceDescends_of_eq_zero
    {A : ℝ} (hA : A = 0) : AbstractPrimeReciprocalSourceDescends A := by
  refine ⟨0, ?_⟩
  intro a n
  rw [primeLabelledEnergyReporter_woldFixedLeftRightEdgeNormalizedPacket]
  simp [hA]

theorem abstractPrimeReciprocalSourceDescends_eq_zero
    {A : ℝ} (h : AbstractPrimeReciprocalSourceDescends A) : A = 0 := by
  rcases h with ⟨reporter, hreporter⟩
  have hlimit (a : ℕ) :
      ((A / (nthPrimeSubtype a : ℕ) : ℝ) : ℂ) =
        reporter deningerBigWittCrossPairOneLegGraphSingularVector := by
    have hreported : Tendsto
        (fun n => reporter (deningerBigWittCrossPairFiniteOneLegGraphAdmission
          (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n)))
        atTop (nhds (reporter deningerBigWittCrossPairOneLegGraphSingularVector)) :=
      (reporter.continuous.tendsto
        deningerBigWittCrossPairOneLegGraphSingularVector).comp
          (tendsto_deningerBigWittCrossPairFiniteOneLegGraphAdmission_woldFixedLeftRightEdgeNormalizedPacket a)
    have hreported' : Tendsto
        (fun _n : ℕ => ((A / (nthPrimeSubtype a : ℕ) : ℝ) : ℂ))
        atTop (nhds (reporter deningerBigWittCrossPairOneLegGraphSingularVector)) := by
      refine hreported.congr ?_
      intro n
      rw [hreporter, primeLabelledEnergyReporter_woldFixedLeftRightEdgeNormalizedPacket]
    exact tendsto_nhds_unique tendsto_const_nhds hreported'
  have hcomplex :
      ((A / (nthPrimeSubtype 0 : ℕ) : ℝ) : ℂ) = ((A / (nthPrimeSubtype 1 : ℕ) : ℝ) : ℂ) :=
    (hlimit 0).trans (hlimit 1).symm
  have hreal : A / (nthPrimeSubtype 0 : ℕ) = A / (nthPrimeSubtype 1 : ℕ) := by
    exact_mod_cast hcomplex
  have hp0 : (0 : ℝ) < (nthPrimeSubtype 0 : ℕ) := nthPrimeSubtype_pos 0
  have hp1 : (0 : ℝ) < (nthPrimeSubtype 1 : ℕ) := nthPrimeSubtype_pos 1
  have hlt : ((nthPrimeSubtype 0 : ℕ) : ℝ) < ((nthPrimeSubtype 1 : ℕ) : ℝ) := by
    exact_mod_cast nthPrimeSubtype_strictMono (by omega : (0 : ℕ) < 1)
  have key : A * ((nthPrimeSubtype 1 : ℕ) : ℝ) = A * ((nthPrimeSubtype 0 : ℕ) : ℝ) :=
    (div_eq_div_iff (ne_of_gt hp0) (ne_of_gt hp1)).mp hreal
  have hzero : A * (((nthPrimeSubtype 1 : ℕ) : ℝ) - ((nthPrimeSubtype 0 : ℕ) : ℝ)) = 0 := by
    rw [mul_sub, key, sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) (ne_of_gt hlt)

/-- **The descent predicate is a scalar condition on one free real parameter.** -/
theorem abstractPrimeReciprocalSourceDescends_iff (A : ℝ) :
    AbstractPrimeReciprocalSourceDescends A ↔ A = 0 :=
  ⟨abstractPrimeReciprocalSourceDescends_eq_zero,
    abstractPrimeReciprocalSourceDescends_of_eq_zero⟩

/-- **The parametric family is false**, with the explicit witness `A = 1`. -/
theorem not_abstractPrimeReciprocalSourceDescends_one :
    ¬ AbstractPrimeReciprocalSourceDescends 1 := by
  intro h
  have := abstractPrimeReciprocalSourceDescends_eq_zero h
  norm_num at this

theorem not_forall_abstractPrimeReciprocalSourceDescends :
    ¬ ∀ A : ℝ, AbstractPrimeReciprocalSourceDescends A := fun h =>
  not_abstractPrimeReciprocalSourceDescends_one (h 1)

/-! ## The Xi descent is the pullback of the parametric family -/

/-- **Parametric factorization.**  The genuine Wold--Jordan actual-source descent at a Xi copy `q`
is literally the free-parameter predicate evaluated at the Gamma-six harmonic weight `A q`. -/
theorem deningerBigWittWoldJordanActualSourceEnergyDescends_iff_abstract
    (q : XiZeroCopy) :
    DeningerBigWittWoldJordanActualSourceEnergyDescends q ↔
      AbstractPrimeReciprocalSourceDescends (xiGammaSixWoldJordanHarmonicWeight q) := by
  have hrep :
      deningerBigWittCrossPairFiniteWoldJordanEnergyReporter q =
        primeLabelledEnergyReporter
          (fun p => xiGammaSixWoldJordanHarmonicWeight q / (p : ℕ)) := by
    rw [deningerBigWittCrossPairFiniteWoldJordanEnergyReporter_eq]
    congr 1
    funext p
    exact thetaGammaSixWoldHorizontalCarrier_sq_eq_weight_div p q
  constructor
  · rintro ⟨reporter, hreporter⟩
    exact ⟨reporter, fun a n => by rw [hreporter, hrep]⟩
  · rintro ⟨reporter, hreporter⟩
    exact ⟨reporter, fun a n => by rw [hreporter, hrep]⟩

/-- **Only the scalar is seen.**  Two Xi copies with the same Gamma-six harmonic weight have the
same descent status; no other feature of the Xi divisor enters the construction. -/
theorem deningerBigWittWoldJordanActualSourceEnergyDescends_congr
    {q q' : XiZeroCopy}
    (h : xiGammaSixWoldJordanHarmonicWeight q = xiGammaSixWoldJordanHarmonicWeight q') :
    DeningerBigWittWoldJordanActualSourceEnergyDescends q ↔
      DeningerBigWittWoldJordanActualSourceEnergyDescends q' := by
  rw [deningerBigWittWoldJordanActualSourceEnergyDescends_iff_abstract,
    deningerBigWittWoldJordanActualSourceEnergyDescends_iff_abstract, h]

/-- **Vacuity of the two-port secondary source character.**

Read together with `deningerBigWittWoldJordanActualSourceEnergyDescends_iff_abstract`, this is the
no-go: every ingredient of the proposed construction (genuine Big--Witt rows, one-leg trace, ambient
and graph admission, the common singular vector, and the prime-labelled quadratic energy) is defined
for a free real parameter `A`, and the resulting descent statement is *false* for `A = 1`.  A
construction of the source `2`-cell from Big--Witt/Gamma/Green--Stokes naturality alone would
establish the parametric statement for every `A`; hence no such construction exists.

Consequently the RH-equivalence of the parent module is the pullback of the arithmetic-free scalar
condition `A = 0` along `q ↦ A q`, and carries no arithmetic content of its own. -/
theorem woldJordanSourceDescent_parametric_vacuity :
    (∀ A : ℝ, AbstractPrimeReciprocalSourceDescends A ↔ A = 0) ∧
      ¬ (∀ A : ℝ, AbstractPrimeReciprocalSourceDescends A) ∧
      (∀ q : XiZeroCopy,
        DeningerBigWittWoldJordanActualSourceEnergyDescends q ↔
          AbstractPrimeReciprocalSourceDescends (xiGammaSixWoldJordanHarmonicWeight q)) :=
  ⟨abstractPrimeReciprocalSourceDescends_iff,
    not_forall_abstractPrimeReciprocalSourceDescends,
    deningerBigWittWoldJordanActualSourceEnergyDescends_iff_abstract⟩

end

end RHTower.HedenmalmThetaSource
