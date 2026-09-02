import GaloisForLFunctions.RHTower.FZZCigarParityHigherGenusMellinCycleSelector
import GaloisForLFunctions.HTGeometry.FZZCigarWorldsheetDivisorGenusLock

/-!
# Literal worldsheet-genus continuation cannot produce the FZZ replica tangent

Mori--Sakai--Shigemori, arXiv:2509.21796v3, split the FZZ string-entanglement
response into a sphere vertex-operator term and an unresolved replica term.  Their
`n = 1 - delta` cover has analytically continued genus

`g(delta) = (1 - 1 / (k - 2)) delta`.

At every physical level `k > 3`, this has a strictly positive first derivative.  For
`0 < delta <= 1` its value lies strictly between zero and one, so it is not the genus of
any literal closed worldsheet.  More generally, every continuous natural-valued genus
family is locally constant at `delta = 0`; every complex observable factoring only through
that genus therefore has zero first derivative.

The obstruction applies to the exact FZZ divisor charge.  The corpus theorem from the
arbitrary-genus FZZ path integral identifies that charge with the loop exponent `2g - 2`,
whose formal continuation has derivative `2(1 - 1 / (k - 2)) > 0`, while its literal-genus
transport is first-order flat.

## RH-chain scope

This kills

`literal n-sheeted FZZ worldsheets`
`-> transported integer-genus divisor/homology-cycle observables`
`-> nonzero first replica-area tangent in the two-cycle passivity chamber`
`-> critical-line incidence -> RH`.

The fixed-genus two-cycle selector remains exact.  The sharp survivor is an analytic
continuation of full amplitudes or moduli that does not factor through literal integer genus;
the 2026 paper leaves precisely that continuation unresolved.

`[FZZ-P ROUTE-BRANCH KILL] [SOURCE-PURE] [PAPER-PROVED] [LEAN-PROVED]
[POSITIVE ANALYTIC-CONTINUATION SURVIVOR]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Formal genus slope of the `n = 1 - delta` worldsheet replica cover at level `k`. -/
def fzzWorldsheetReplicaFormalGenusSlope (k : ℝ) : ℝ :=
  1 - (k - 2)⁻¹

/-- Analytically continued replica genus used at first order around `delta = 0`. -/
def fzzWorldsheetReplicaFormalGenus (k delta : ℝ) : ℝ :=
  fzzWorldsheetReplicaFormalGenusSlope k * delta

theorem fzzWorldsheetReplicaFormalGenusSlope_pos
    {k : ℝ} (hk : 3 < k) :
    0 < fzzWorldsheetReplicaFormalGenusSlope k := by
  rw [fzzWorldsheetReplicaFormalGenusSlope]
  have hdenpos : 0 < k - 2 := by linarith
  have hdenone : 1 < k - 2 := by linarith
  exact sub_pos.mpr ((inv_lt_one₀ hdenpos).2 hdenone)

theorem fzzWorldsheetReplicaFormalGenusSlope_lt_one
    {k : ℝ} (hk : 3 < k) :
    fzzWorldsheetReplicaFormalGenusSlope k < 1 := by
  rw [fzzWorldsheetReplicaFormalGenusSlope]
  have hdenpos : 0 < k - 2 := by linarith
  have hinvpos : 0 < (k - 2)⁻¹ := inv_pos.mpr hdenpos
  linarith

theorem fzzWorldsheetReplicaFormalGenus_mem_openUnitInterval
    {k delta : ℝ} (hk : 3 < k) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    0 < fzzWorldsheetReplicaFormalGenus k delta ∧
      fzzWorldsheetReplicaFormalGenus k delta < 1 := by
  have hslope := fzzWorldsheetReplicaFormalGenusSlope_pos hk
  have hslopeOne := fzzWorldsheetReplicaFormalGenusSlope_lt_one hk
  constructor
  · rw [fzzWorldsheetReplicaFormalGenus]
    exact mul_pos hslope hdelta
  · rw [fzzWorldsheetReplicaFormalGenus]
    calc
      fzzWorldsheetReplicaFormalGenusSlope k * delta ≤
          fzzWorldsheetReplicaFormalGenusSlope k * 1 :=
        mul_le_mul_of_nonneg_left hdeltaOne hslope.le
      _ < 1 := by simpa using hslopeOne

/-- At every physical level, the analytically continued first-order genus is genuinely fractional
for a positive replica deficit at most one. -/
theorem not_exists_literalWorldsheetGenus_eq_formalGenus
    {k delta : ℝ} (hk : 3 < k) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    ¬ ∃ genus : ℕ, (genus : ℝ) = fzzWorldsheetReplicaFormalGenus k delta := by
  rintro ⟨genus, hgenus⟩
  have hbounds :=
    fzzWorldsheetReplicaFormalGenus_mem_openUnitInterval hk hdelta hdeltaOne
  have hgenusPos : 0 < (genus : ℝ) := by simpa [hgenus] using hbounds.1
  have hgenusNatPos : 0 < genus := by exact_mod_cast hgenusPos
  have hgenusOne : (1 : ℝ) ≤ genus := by exact_mod_cast hgenusNatPos
  rw [hgenus] at hgenusOne
  linarith

theorem hasDerivAt_fzzWorldsheetReplicaFormalGenus
    (k : ℝ) :
    HasDerivAt (fzzWorldsheetReplicaFormalGenus k)
      (fzzWorldsheetReplicaFormalGenusSlope k) 0 := by
  change HasDerivAt
    (fun delta : ℝ => fzzWorldsheetReplicaFormalGenusSlope k * delta)
    (fzzWorldsheetReplicaFormalGenusSlope k) 0
  simpa only [id_eq, mul_one] using
    (hasDerivAt_id (𝕜 := ℝ) 0).const_mul
      (fzzWorldsheetReplicaFormalGenusSlope k)

/-- Analytically continued loop/divisor charge `2g-2`. -/
def fzzWorldsheetReplicaFormalLoopExponent (k delta : ℝ) : ℝ :=
  2 * fzzWorldsheetReplicaFormalGenus k delta - 2

theorem hasDerivAt_fzzWorldsheetReplicaFormalLoopExponent
    (k : ℝ) :
    HasDerivAt (fzzWorldsheetReplicaFormalLoopExponent k)
      (2 * fzzWorldsheetReplicaFormalGenusSlope k) 0 := by
  change HasDerivAt
    (fun delta : ℝ => 2 * fzzWorldsheetReplicaFormalGenus k delta - 2)
    (2 * fzzWorldsheetReplicaFormalGenusSlope k) 0
  exact ((hasDerivAt_fzzWorldsheetReplicaFormalGenus k).const_mul 2).sub_const 2

/-- Any observable depending only on continuously transported literal genus is first-order flat. -/
theorem literalWorldsheetGenusObservable_hasDerivAt_zero
    (observable : ℕ → ℂ) (genus : ℝ → ℕ)
    (hcontinuous : ContinuousAt genus 0) :
    HasDerivAt (fun delta : ℝ => observable (genus delta)) 0 0 := by
  have hgenus : genus =ᶠ[nhds 0] fun _ => genus 0 := by
    have hsingleton : {genus 0} ∈ nhds (genus 0) := by
      rw [nhds_discrete]
      exact Set.mem_singleton _
    filter_upwards [hcontinuous hsingleton] with delta hdelta
    exact Set.mem_singleton_iff.mp hdelta
  have hobservable :
      (fun delta : ℝ => observable (genus delta)) =ᶠ[nhds 0]
        fun _ => observable (genus 0) :=
    hgenus.fun_comp observable
  exact (hasDerivAt_const (x := (0 : ℝ)) (c := observable (genus 0))).congr_of_eventuallyEq
    hobservable

/-- A literal-genus producer would obtain a nonzero first replica tangent from an observable of a
continuously varying natural-valued worldsheet genus. -/
def FZZLiteralWorldsheetGenusNonzeroReplicaProducer : Prop :=
  ∃ (genus : ℝ → ℕ) (observable : ℕ → ℂ) (tangent : ℂ),
    ContinuousAt genus 0 ∧ tangent ≠ 0 ∧
      HasDerivAt (fun delta : ℝ => observable (genus delta)) tangent 0

theorem not_FZZLiteralWorldsheetGenusNonzeroReplicaProducer :
    ¬ FZZLiteralWorldsheetGenusNonzeroReplicaProducer := by
  rintro ⟨genus, observable, tangent, hcontinuous, htangent, hderiv⟩
  have hzero := literalWorldsheetGenusObservable_hasDerivAt_zero
    observable genus hcontinuous
  exact htangent (hderiv.unique hzero)

/-- The formal replica-genus slope itself cannot be realized by a continuous literal genus. -/
def FZZWorldsheetReplicaFormalGenusTangentLiterallyRealizable (k : ℝ) : Prop :=
  ∃ genus : ℝ → ℕ, ContinuousAt genus 0 ∧
    HasDerivAt (fun delta : ℝ => ((genus delta : ℕ) : ℂ))
      (fzzWorldsheetReplicaFormalGenusSlope k : ℂ) 0

theorem not_fzzWorldsheetReplicaFormalGenusTangentLiterallyRealizable
    {k : ℝ} (hk : 3 < k) :
    ¬ FZZWorldsheetReplicaFormalGenusTangentLiterallyRealizable k := by
  rintro ⟨genus, hcontinuous, hderiv⟩
  have hzero := literalWorldsheetGenusObservable_hasDerivAt_zero
    (fun n : ℕ => (n : ℂ)) genus hcontinuous
  have hslopeC : (fzzWorldsheetReplicaFormalGenusSlope k : ℂ) = 0 :=
    hderiv.unique hzero
  have hslope : fzzWorldsheetReplicaFormalGenusSlope k = 0 := by
    exact_mod_cast hslopeC
  exact (ne_of_gt (fzzWorldsheetReplicaFormalGenusSlope_pos hk)) hslope

/-- Literal FZZ loop/divisor charge cannot realize the continued nonzero charge tangent. -/
def FZZWorldsheetReplicaFormalLoopTangentLiterallyRealizable (k : ℝ) : Prop :=
  ∃ genus : ℝ → ℕ, ContinuousAt genus 0 ∧
    HasDerivAt
      (fun delta : ℝ =>
        ((GaloisForLFunctions.HTGeometry.FZZCigar.worldsheetLoopExponent
          (genus delta) : ℤ) : ℂ))
      ((2 * fzzWorldsheetReplicaFormalGenusSlope k : ℝ) : ℂ) 0

theorem not_fzzWorldsheetReplicaFormalLoopTangentLiterallyRealizable
    {k : ℝ} (hk : 3 < k) :
    ¬ FZZWorldsheetReplicaFormalLoopTangentLiterallyRealizable k := by
  rintro ⟨genus, hcontinuous, hderiv⟩
  have hzero := literalWorldsheetGenusObservable_hasDerivAt_zero
    (fun genus : ℕ =>
      ((GaloisForLFunctions.HTGeometry.FZZCigar.worldsheetLoopExponent genus : ℤ) : ℂ))
    genus hcontinuous
  have htangent : ((2 * fzzWorldsheetReplicaFormalGenusSlope k : ℝ) : ℂ) = 0 :=
    hderiv.unique hzero
  have htangentReal : 2 * fzzWorldsheetReplicaFormalGenusSlope k = 0 := by
    exact_mod_cast htangent
  nlinarith [fzzWorldsheetReplicaFormalGenusSlope_pos hk]

/-- Closed certificate: the fixed-genus cycle selector survives, but no continuous transport of
literal integer genus can supply its nonzero first-order replica producer. -/
def FZZCigarParityWorldsheetReplicaGenusContinuationNoGo : Prop :=
  (∀ genus residualZeros spectralFlowZeros radiationPoles : ℕ,
    GaloisForLFunctions.HTGeometry.FZZCigar.FZZDivisorRealization
        genus residualZeros spectralFlowZeros radiationPoles →
      GaloisForLFunctions.HTGeometry.FZZCigar.fzzDivisorCharge
          residualZeros spectralFlowZeros radiationPoles =
        GaloisForLFunctions.HTGeometry.FZZCigar.worldsheetLoopExponent genus) ∧
  (∀ rho : ℂ,
    FZZHigherGenusCyclePairKreinSign 1
        (fzzCigarParityMellinTorusTwist rho) ↔ rho.re = 1 / 2) ∧
  (∀ k delta : ℝ, 3 < k → 0 < delta → delta ≤ 1 →
    ¬ ∃ genus : ℕ, (genus : ℝ) = fzzWorldsheetReplicaFormalGenus k delta) ∧
  (∀ k : ℝ, 3 < k →
    0 < fzzWorldsheetReplicaFormalGenusSlope k ∧
      HasDerivAt (fzzWorldsheetReplicaFormalGenus k)
        (fzzWorldsheetReplicaFormalGenusSlope k) 0 ∧
      HasDerivAt (fzzWorldsheetReplicaFormalLoopExponent k)
        (2 * fzzWorldsheetReplicaFormalGenusSlope k) 0 ∧
      ¬ FZZWorldsheetReplicaFormalGenusTangentLiterallyRealizable k ∧
      ¬ FZZWorldsheetReplicaFormalLoopTangentLiterallyRealizable k) ∧
  ¬ FZZLiteralWorldsheetGenusNonzeroReplicaProducer

theorem fzzCigarParity_worldsheetReplicaGenusContinuation_noGo :
    FZZCigarParityWorldsheetReplicaGenusContinuationNoGo := by
  refine ⟨?_, fzzCigarParityMellinCyclePairKreinSign_iff_re_eq_half, ?_, ?_,
    not_FZZLiteralWorldsheetGenusNonzeroReplicaProducer⟩
  · intro genus residualZeros spectralFlowZeros radiationPoles hrealized
    exact GaloisForLFunctions.HTGeometry.FZZCigar.fzzDivisorCharge_eq_worldsheetLoopExponent
      hrealized
  · intro k delta hk hdelta hdeltaOne
    exact not_exists_literalWorldsheetGenus_eq_formalGenus hk hdelta hdeltaOne
  intro k hk
  exact ⟨fzzWorldsheetReplicaFormalGenusSlope_pos hk,
    hasDerivAt_fzzWorldsheetReplicaFormalGenus k,
    hasDerivAt_fzzWorldsheetReplicaFormalLoopExponent k,
    not_fzzWorldsheetReplicaFormalGenusTangentLiterallyRealizable hk,
    not_fzzWorldsheetReplicaFormalLoopTangentLiterallyRealizable hk⟩

end

end RHTower
