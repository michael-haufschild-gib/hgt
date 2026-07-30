import GaloisForLFunctions.RHTower.XiAperturePoissonFullApertureHilbertTransport
import GaloisForLFunctions.RHTower.XiApertureResponseCorrelationDet2

/-!
# Universal counterterm phase of the fused Xi aperture response

The unit aperture has one non-trace-class prime-harmonic channel, whose unique subtraction
coefficient is `6`.  Every deeper positive integral aperture is already trace class, so any
nonzero prime-harmonic subtraction destroys summability.  This gives one exact all-depth
renormalization law with a boundary jump from `6` to `0`.
-/

namespace RHTower

noncomputable section

/-- Unique prime-harmonic counterterm coefficient at a positive integral aperture. -/
def xiAperturePrimeFusedResponseBoundaryCounterterm (a : ℕ) : ℝ :=
  if a = 1 then 6 else 0

/-- **Fused-response counterterm phase universality.** After subtracting the unit background
only at aperture one, the all-prime fused gain is summable after a scalar harmonic subtraction
exactly for the canonical coefficient: `6` at aperture one and `0` at every deeper positive
integral aperture. -/
theorem summable_xiAperturePrimeFusedResponseGainSq_sub_boundary_sub_c_mul_iff
    {a : ℕ} (ha : 0 < a) (c : ℝ) :
    Summable (fun p : Nat.Primes ↦
      xiAperturePrimeFusedResponseGainSq a p -
        (if a = 1 then 1 else 0) -
        c * xiTransversePrimeApertureDiskNode 1 p) ↔
      c = xiAperturePrimeFusedResponseBoundaryCounterterm a := by
  by_cases ha1 : a = 1
  · subst a
    simpa [xiAperturePrimeFusedResponseBoundaryCounterterm,
      xiAperturePrimeFusedResponseGainSq_one] using
      summable_xiApertureOnePrimeFusedResponseGainSq_sub_one_sub_c_mul_iff c
  · have ha2 : 2 ≤ a := by omega
    have hgain : Summable (xiAperturePrimeFusedResponseGainSq a) :=
      summable_xiAperturePrimeFusedResponseGainSq_of_two_le ha2
    simp only [ha1, if_false, sub_zero,
      xiAperturePrimeFusedResponseBoundaryCounterterm]
    constructor
    · intro hren
      have hscaled : Summable (fun p : Nat.Primes ↦
          c * xiTransversePrimeApertureDiskNode 1 p) := by
        have hdiff := hgain.sub hren
        exact hdiff.congr (fun p => by ring)
      by_contra hc
      have hnodes : Summable (fun p : Nat.Primes ↦
          xiTransversePrimeApertureDiskNode 1 p) :=
        (summable_mul_left_iff hc).mp hscaled
      apply Nat.Primes.not_summable_one_div
      simpa [xiTransversePrimeApertureDiskNode_one_eq_inv, one_div] using hnodes
    · rintro rfl
      simpa using hgain

/-- **Exact-recovery/counterterm packet phase.** Exact cofinite prime-jet reconstruction supplies
the positivity needed by the scalar counterterm law in every channel. Thus an entire finite
aperture packet is exactly recoverable and canonically renormalizable precisely when its labels
are injective, nonzero, and every channel uses its unique boundary counterterm. -/
theorem
    xiTransversePrimeJetApertureCofiniteHilbertReconstruction_and_countertermPhase_iff
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (c : Fin N → ℝ) :
    XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m ∧
        (∀ j, Summable (fun p : Nat.Primes ↦
          xiAperturePrimeFusedResponseGainSq (shift j) p -
            (if shift j = 1 then 1 else 0) -
            c j * xiTransversePrimeApertureDiskNode 1 p)) ↔
      Function.Injective shift ∧
        ∀ j, shift j ≠ 0 ∧
          c j = xiAperturePrimeFusedResponseBoundaryCounterterm (shift j) := by
  rw [
    xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero]
  constructor
  · rintro ⟨⟨hinjective, hnonzero⟩, hsummable⟩
    refine ⟨hinjective, fun j => ⟨hnonzero j, ?_⟩⟩
    exact
      (summable_xiAperturePrimeFusedResponseGainSq_sub_boundary_sub_c_mul_iff
        (Nat.pos_of_ne_zero (hnonzero j)) (c j)).1 (hsummable j)
  · rintro ⟨hinjective, hphase⟩
    exact ⟨⟨hinjective, fun j => (hphase j).1⟩, fun j =>
      (summable_xiAperturePrimeFusedResponseGainSq_sub_boundary_sub_c_mul_iff
        (Nat.pos_of_ne_zero (hphase j).1) (c j)).2 (hphase j).2⟩

/-- **Exact trace-class packets have zero counterterm.** Adding unsubtracted trace-class gain to
the exact-recovery/counterterm packet phase removes the unit-aperture boundary. Consequently the
labels are injective and at least two, and the unique counterterm vanishes in every channel. -/
theorem
    xiTransversePrimeJetApertureCofiniteHilbertReconstruction_and_traceClassGain_and_countertermPhase_iff
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) (c : Fin N → ℝ) :
    XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m ∧
        (∀ j, Summable (xiAperturePrimeFusedResponseGainSq (shift j))) ∧
        (∀ j, Summable (fun p : Nat.Primes ↦
          xiAperturePrimeFusedResponseGainSq (shift j) p -
            (if shift j = 1 then 1 else 0) -
            c j * xiTransversePrimeApertureDiskNode 1 p)) ↔
      Function.Injective shift ∧ ∀ j, 2 ≤ shift j ∧ c j = 0 := by
  constructor
  · rintro ⟨hreconstruct, hgain, hrenormalized⟩
    have htrace :=
      (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_and_traceClassGain_iff
        shift m).1 ⟨hreconstruct, hgain⟩
    have hcounterterm :=
      (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_and_countertermPhase_iff
        shift m c).1 ⟨hreconstruct, hrenormalized⟩
    refine ⟨htrace.1, fun j => ⟨htrace.2 j, ?_⟩⟩
    have hne_one : shift j ≠ 1 :=
      Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) (htrace.2 j))
    simpa [xiAperturePrimeFusedResponseBoundaryCounterterm, hne_one] using
      (hcounterterm.2 j).2
  · rintro ⟨hinjective, hphase⟩
    have hrecoverGain :=
      (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_and_traceClassGain_iff
        shift m).2 ⟨hinjective, fun j => (hphase j).1⟩
    have hrecoverCounterterm :=
      (xiTransversePrimeJetApertureCofiniteHilbertReconstruction_and_countertermPhase_iff
        shift m c).2 ⟨hinjective, fun j => by
          have hne_zero : shift j ≠ 0 :=
            Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) (hphase j).1)
          have hne_one : shift j ≠ 1 :=
            Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) (hphase j).1)
          exact ⟨hne_zero, by
            simpa [xiAperturePrimeFusedResponseBoundaryCounterterm, hne_one] using
              (hphase j).2⟩⟩
    exact ⟨hrecoverGain.1, hrecoverGain.2, hrecoverCounterterm.2⟩

end

end RHTower
