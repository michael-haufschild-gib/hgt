import GaloisForLFunctions.HTGeometry.TemporalCharacterWallCrossingLaw
import GaloisForLFunctions.HTGeometry.ValuatedSpectralCharacterLaw

/-!
# Temporal wall crossing for every finite character of an arbitrary spectrum

The ambient energy-label type in this file is arbitrary. An observation
uses a finitely supported projective integer character, so only finitely many
analytic branches enter each theorem.

The character's exact filtration birth is proved equal to the order of its
summed analytic detuning series. Consequently every active character of
every analytic spectrum obeys the same unresolved/crossover/dephased
temporal wall-crossing law.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Analytic detuning paired with one finite-support projective character. -/
def projectiveCharacterResponse
    {I : Type*} (energy : I → ℂ → ℂ)
    (k : ProjectiveCharacter I) (g : ℂ) : ℂ :=
  ∑ i ∈ k.1.support, (k.1 i : ℂ) * energy i g

/-- Formal series of a projective-character detuning. -/
def projectiveCharacterSeries
    {I : Type*}
    (series : I → FormalMultilinearSeries ℂ ℂ ℂ)
    (k : ProjectiveCharacter I) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  ∑ i ∈ k.1.support, (k.1 i : ℂ) • series i

/-- Every finite projective combination of analytic energy branches is
analytic with the corresponding finite sum of formal series. -/
theorem hasFPowerSeriesAt_projectiveCharacterResponse
    {I : Type*} (energy : I → ℂ → ℂ)
    (series : I → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (k : ProjectiveCharacter I) :
    HasFPowerSeriesAt
      (projectiveCharacterResponse energy k)
      (projectiveCharacterSeries series k) 0 := by
  classical
  unfold projectiveCharacterResponse projectiveCharacterSeries
  induction k.1.support using Finset.induction_on with
  | empty =>
      simpa using
        (hasFPowerSeriesAt_const (𝕜 := ℂ) (E := ℂ)
          (c := (0 : ℂ)) (e := (0 : ℂ)))
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      simpa [Pi.smul_apply, smul_eq_mul] using
        ((henergy a).const_smul (c := (k.1 a : ℂ))).add ih

/-- Scalar Taylor coefficient of one spectral branch. -/
def spectralTaylorJet
    {I : Type*}
    (series : I → FormalMultilinearSeries ℂ ℂ ℂ)
    (n : ℕ) (i : I) : ℂ :=
  series i n (fun _ => 1)

/-- Pairing the summed character series at ones is exactly pairing the
branchwise scalar Taylor jets with that character. -/
theorem projectiveCharacterSeries_apply_one_eq_relationJet
    {I : Type*}
    (series : I → FormalMultilinearSeries ℂ ℂ ℂ)
    (k : ProjectiveCharacter I) (n : ℕ) :
    projectiveCharacterSeries series k n (fun _ => 1) =
      projectiveSpectralRelationJet (spectralTaylorJet series) n k := by
  classical
  change
    (∑ i ∈ k.1.support, (k.1 i : ℂ) • series i) n
        (fun _ => 1) =
      k.1.sum fun i m => (m : ℂ) * series i n (fun _ => 1)
  rw [Finsupp.sum]
  have hsum :
      (∑ i ∈ k.1.support, (k.1 i : ℂ) • series i) n =
        ∑ i ∈ k.1.support, ((k.1 i : ℂ) • series i) n := by
    induction k.1.support using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        change
          ((k.1 a : ℂ) • series a) n +
              (∑ i ∈ s, (k.1 i : ℂ) • series i) n =
            ((k.1 a : ℂ) • series a) n +
              ∑ i ∈ s, ((k.1 i : ℂ) • series i) n
        rw [ih]
  rw [hsum]
  let one : Fin n → ℂ := fun _ => 1
  change
    (∑ i ∈ k.1.support, ((k.1 i : ℂ) • series i) n) one =
      ∑ i ∈ k.1.support, (k.1 i : ℂ) * series i n one
  have happly :
      (∑ i ∈ k.1.support, ((k.1 i : ℂ) • series i) n) one =
        ∑ i ∈ k.1.support, (((k.1 i : ℂ) • series i) n) one := by
    induction k.1.support using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        change
          (((k.1 a : ℂ) • series a) n) one +
              (∑ i ∈ s, ((k.1 i : ℂ) • series i) n) one =
            (((k.1 a : ℂ) • series a) n) one +
              ∑ i ∈ s, (((k.1 i : ℂ) • series i) n) one
        rw [ih]
  rw [happly]
  apply Finset.sum_congr rfl
  intro i hi
  simp [smul_eq_mul]

/-- A one-dimensional formal series is nonzero exactly when one scalar
Taylor coefficient evaluated on the all-one direction is nonzero. -/
theorem formalMultilinearSeries_ne_zero_iff_exists_apply_one_ne
    (series : FormalMultilinearSeries ℂ ℂ ℂ) :
    series ≠ 0 ↔ ∃ n, series n (fun _ => 1) ≠ 0 := by
  constructor
  · intro hne
    by_contra hall
    push Not at hall
    apply hne
    ext n
    rw [← (series n).mkPiRing_apply_one_eq_self]
    simp [hall n]
  · rintro ⟨n, hn⟩ hzero
    exact hn (by simp [hzero])

/-- Character activity in the spectral-jet filtration is exactly
nonvanishing of its analytic relation series. -/
theorem spectralCharacterActive_iff_characterSeries_ne_zero
    {I : Type*}
    (series : I → FormalMultilinearSeries ℂ ℂ ℂ)
    (k : ProjectiveCharacter I) :
    SpectralCharacterActive (spectralTaylorJet series) k ↔
      projectiveCharacterSeries series k ≠ 0 := by
  rw [formalMultilinearSeries_ne_zero_iff_exists_apply_one_ne]
  unfold SpectralCharacterActive
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩
  · rwa [projectiveCharacterSeries_apply_one_eq_relationJet]
  · rwa [projectiveCharacterSeries_apply_one_eq_relationJet] at hn

/-- Exact filtration birth equals the analytic order of the character's
detuning series. -/
theorem spectralCharacterBirthOrder_eq_series_order
    {I : Type*}
    (series : I → FormalMultilinearSeries ℂ ℂ ℂ)
    (k : ProjectiveCharacter I)
    (hactive : SpectralCharacterActive (spectralTaylorJet series) k) :
    spectralCharacterBirthOrder (spectralTaylorJet series) k hactive =
      (projectiveCharacterSeries series k).order := by
  let p := projectiveCharacterSeries series k
  have hp : p ≠ 0 :=
    (spectralCharacterActive_iff_characterSeries_ne_zero series k).mp
      hactive
  have hpOrderApply : p p.order (fun _ => 1) ≠ 0 := by
    intro hzero
    apply FormalMultilinearSeries.apply_order_ne_zero hp
    rw [← (p p.order).mkPiRing_apply_one_eq_self]
    rw [hzero, ContinuousMultilinearMap.mkPiRing_zero]
  have hrelationOrder :
      projectiveSpectralRelationJet
          (spectralTaylorJet series) p.order k ≠ 0 := by
    rwa [← projectiveCharacterSeries_apply_one_eq_relationJet]
  have hle :
      spectralCharacterBirthOrder
          (spectralTaylorJet series) k hactive ≤ p.order :=
    Nat.find_min' hactive hrelationOrder
  apply le_antisymm hle
  by_contra hnot
  have hlt :
      spectralCharacterBirthOrder
          (spectralTaylorJet series) k hactive < p.order := by
    omega
  have hpzero :
      p (spectralCharacterBirthOrder
          (spectralTaylorJet series) k hactive) = 0 :=
    FormalMultilinearSeries.apply_eq_zero_of_lt_order hlt
  have hrelationZero :
      projectiveSpectralRelationJet
          (spectralTaylorJet series)
          (spectralCharacterBirthOrder
            (spectralTaylorJet series) k hactive) k = 0 := by
    rw [← projectiveCharacterSeries_apply_one_eq_relationJet]
    simp [p, hpzero]
  exact spectralRelationJet_birthOrder_ne_zero hactive hrelationZero

/-- **Every finite character of every analytic spectrum has universal wall
crossing.** The ambient spectral label type can be arbitrary. -/
theorem projectiveCharacter_wallCrossing
    {I : Type*} (energy : I → ℂ → ℂ)
    (series : I → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (k : ProjectiveCharacter I)
    (hactive : SpectralCharacterActive (spectralTaylorJet series) k)
    {τ : ℝ} (hτ : 0 < τ) :
    let b := spectralCharacterBirthOrder
      (spectralTaylorJet series) k hactive
    let response := projectiveCharacterResponse energy k
    (∀ r < b,
      Tendsto
        (fun g : ℝ => Real.sinc (τ * (‖response g‖ / g ^ r)))
        (𝓝[>] 0) (𝓝 1)) ∧
    Tendsto
      (fun g : ℝ => Real.sinc (τ * (‖response g‖ / g ^ b)))
      (𝓝[>] 0)
      (𝓝 (Real.sinc
        (τ * ‖analyticBirthUnit response
          (projectiveCharacterSeries series k) 0‖))) ∧
    (∀ r, b < r →
      Tendsto
        (fun g : ℝ => Real.sinc (τ * (‖response g‖ / g ^ r)))
        (𝓝[>] 0) (𝓝 0)) := by
  dsimp only
  have hf :=
    hasFPowerSeriesAt_projectiveCharacterResponse
      energy series henergy k
  have hseries :
      projectiveCharacterSeries series k ≠ 0 :=
    (spectralCharacterActive_iff_characterSeries_ne_zero series k).mp
      hactive
  have hresponse : AnalyticSectorActive
      (projectiveCharacterResponse energy k) :=
    by
      intro hzero
      exact hseries (hf.eq_zero_of_eventually hzero)
  have hwall :=
    analyticSectorReporter_wallCrossing hf hresponse hτ
  have hbirth :=
    spectralCharacterBirthOrder_eq_series_order series k hactive
  simpa [analyticBirthOrder, hbirth] using hwall

end

end GaloisForLFunctions.HTGeometry
