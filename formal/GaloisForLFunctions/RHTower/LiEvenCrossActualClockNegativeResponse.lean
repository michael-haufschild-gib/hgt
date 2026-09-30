import GaloisForLFunctions.RHTower.LiEvenCrossActualClockTopFrequency
import GaloisForLFunctions.RHTower.LiClockFiniteTopSinePacket
import GaloisForLFunctions.RHTower.LiClockSineImaginaryEnvelope
import Mathlib.Topology.Algebra.Order.Field

/-!
# Off-line zeros force a negative actual clock response

Failure of RH isolates a finite nonempty maximal imaginary reciprocal-frequency packet,
including every analytic multiplicity copy. Simultaneous phase recurrence gives its exact
negative exponentially normalized limit; the strict frequency gap suppresses the complete
complement. The literal completed-source response therefore tends to minus infinity along
cofinal clocks. Eventual nonnegativity of that response implies RH.
-/

open scoped BigOperators Topology
open Filter
namespace RHTower
noncomputable section

private theorem actualResponse_split (Q : Set XiZeroCopy) [Fintype Q]
    [DecidablePred (· ∈ Q)] (t : ℝ) :
    liEvenCrossActualClockResponse t =
      (∑ q : Q, (liEvenCrossActualClockSineAtom t q.val).re) +
        (∑' q : XiZeroCopy, if q ∈ Q then 0 else liEvenCrossActualClockSineAtom t q).re := by
  classical
  rw [liEvenCrossActualClockResponse_eq_re_tsum_sine,
    ← (summable_liEvenCrossActualClockSineAtom t).tsum_subtype_add_tsum_subtype_compl Q,
    Complex.add_re, tsum_fintype]
  congr 1
  · exact map_sum Complex.reAddGroupHom _ _
  · congr 1
    rw [tsum_subtype]
    apply tsum_congr
    intro q
    by_cases hq : q ∈ Q <;> simp [Set.indicator, hq]

/-- Failure of RH forces an exact negative normalized limit along cofinal actual clocks. -/
theorem exists_liEvenCrossActualClock_negative_normalized_limit_of_not_rh
    (hnot : ¬RiemannHypothesis) :
    ∃ b : ℝ, 0 < b ∧ (liEvenCrossActualClockTopPacket b).Finite ∧
      (liEvenCrossActualClockTopPacket b).Nonempty ∧ ∃ t : ℕ → ℝ,
      (∀ n : ℕ, (n : ℝ) + 1 ≤ t n) ∧ Tendsto t atTop atTop ∧
      Tendsto (fun n => Real.exp (-b * t n) * liEvenCrossActualClockResponse (t n))
        atTop (𝓝 (-b * (Nat.card (liEvenCrossActualClockTopPacket b) : ℝ) / 2)) := by
  classical
  obtain ⟨b, hb, hQfin, hQnonempty, _, β, hβ0, hgap, hβ⟩ :=
    exists_liEvenCrossActualClockTopPacket_of_not_rh hnot
  let Q := liEvenCrossActualClockTopPacket b
  letI : Fintype Q := hQfin.fintype
  letI : Nonempty Q := hQnonempty.to_subtype
  let w : Q → ℂ := fun q => (xiSpectralPoint q.val)⁻¹
  have hw (q : Q) : |(w q).im| = b := q.property
  obtain ⟨t, ht, htcofinal, htop⟩ :=
    exists_liClockFiniteTopSinePacket_negative_limit w hb hw
  have hcompl :=
    (liEvenCrossActualClock_tendsto_normalized_complement_zero Q hβ0 hβ hgap).comp htcofinal
  have htail : Tendsto (fun n => Real.exp (-b*t n) *
      (∑' q : XiZeroCopy, if q ∈ Q then 0 else liEvenCrossActualClockSineAtom (t n) q).re)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] using
      Complex.continuous_re.continuousAt.tendsto.comp hcompl
  refine ⟨b, hb, hQfin, hQnonempty, t, ht, htcofinal, ?_⟩
  have hsum := htop.add htail
  have heq (n : ℕ) :
      Real.exp (-b*t n) * liEvenCrossActualClockResponse (t n) =
        Real.exp (-b*t n) * (∑ q : Q, (w q * Complex.sin ((t n : ℂ)*w q)).re) +
          Real.exp (-b*t n) *
            (∑' q : XiZeroCopy, if q ∈ Q then 0 else liEvenCrossActualClockSineAtom (t n) q).re := by
    rw [actualResponse_split Q (t n)]
    simp only [liEvenCrossActualClockSineAtom, w, mul_add]
  simpa only [← heq, add_zero, Nat.card_eq_fintype_card] using hsum


/-- If RH fails, the actual response tends to minus infinity along a cofinal clock sequence. -/
theorem exists_liEvenCrossActualClock_tendsto_atBot_of_not_rh
    (hnot : ¬RiemannHypothesis) :
    ∃ t : ℕ → ℝ, (∀ n : ℕ, (n : ℝ) + 1 ≤ t n) ∧
      Tendsto t atTop atTop ∧
      Tendsto (fun n => liEvenCrossActualClockResponse (t n)) atTop atBot := by
  classical
  obtain ⟨b, hb, hQfin, hQnonempty, t, ht, htcofinal, hlimit⟩ :=
    exists_liEvenCrossActualClock_negative_normalized_limit_of_not_rh hnot
  letI : Fintype (liEvenCrossActualClockTopPacket b) := hQfin.fintype
  letI : Nonempty (liEvenCrossActualClockTopPacket b) := hQnonempty.to_subtype
  have hcard : 0 < (Nat.card (liEvenCrossActualClockTopPacket b) : ℝ) := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_pos
  have hc : -b * (Nat.card (liEvenCrossActualClockTopPacket b) : ℝ) / 2 < 0 := by
    nlinarith [mul_pos hb hcard]
  have he := Real.tendsto_exp_atTop.comp (htcofinal.const_mul_atTop hb)
  have hp := hlimit.neg_mul_atTop hc he
  refine ⟨t, ht, htcofinal, hp.congr ?_⟩
  intro n
  calc
    (Real.exp (-b*t n)*liEvenCrossActualClockResponse (t n))*Real.exp (b*t n) =
        (Real.exp (-b*t n)*Real.exp (b*t n))*liEvenCrossActualClockResponse (t n) := by ring
    _ = liEvenCrossActualClockResponse (t n) := by
      rw [← Real.exp_add, show -b*t n+b*t n=0 by ring, Real.exp_zero, one_mul]

/-- Failure of RH forces arbitrarily negative responses beyond every real clock threshold. -/
theorem liEvenCrossActualClock_unbounded_below_cofinally_of_not_rh
    (hnot : ¬RiemannHypothesis) (M T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧ liEvenCrossActualClockResponse t < M := by
  obtain ⟨t, _, htcofinal, hresponse⟩ :=
    exists_liEvenCrossActualClock_tendsto_atBot_of_not_rh hnot
  obtain ⟨n, hnT, hnM⟩ :=
    ((htcofinal.eventually (eventually_ge_atTop T)).and
      (hresponse.eventually (eventually_lt_atBot M))).exists
  exact ⟨t n, hnT, hnM⟩

/-- Eventual nonnegativity of the literal completed-source response implies RH. -/
theorem riemannHypothesis_of_liEvenCrossActualClock_eventually_nonneg
    (h : ∀ᶠ t : ℝ in atTop, 0 ≤ liEvenCrossActualClockResponse t) :
    RiemannHypothesis := by
  by_contra hnot
  obtain ⟨t, _, htcofinal, hresponse⟩ :=
    exists_liEvenCrossActualClock_tendsto_atBot_of_not_rh hnot
  obtain ⟨n, hn0, hnneg⟩ :=
    ((htcofinal.eventually h).and
      (hresponse.eventually (eventually_lt_atBot (0 : ℝ)))).exists
  exact not_lt_of_ge hn0 hnneg

end
end RHTower
