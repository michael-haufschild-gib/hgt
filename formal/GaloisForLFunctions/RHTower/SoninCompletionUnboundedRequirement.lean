import GaloisForLFunctions.RHTower.SoninNoAperturePacketFloor

/-!
# What a completion must do to restore the floor

The unit-weight aperture packet channel has no lower bound.  Adding any counterterm that stays
uniformly bounded on the packet family therefore cannot restore one, whether or not the counterterm
depends on the packet.

Read backwards this is a requirement on the archimedean side: a completion that does produce a
lower floor on this family must itself be unbounded above along it, and must in fact exceed every
level at some packet.  The earlier no-gos ruled out counterterms depending on the aperture flag
alone; this rules out every bounded one.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- **No bounded counterterm restores the floor.**  A counterterm that is uniformly bounded on the
packet family leaves the channel unbounded below, even if it depends on the packet. -/
theorem not_exists_lower_bound_soninAperturePacketCurvature_add_bounded
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) (C : Finset ℕ → ℝ) (M₀ : ℝ) (hC : ∀ s, C s ≤ M₀) :
    ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ (opTrace (soninAperturePacketCurvature s a b c (soninCrossingClock a c)
            (one_lt_soninCrossingClock a c) (fun _ => 1))).re + C s := by
  rintro ⟨M, hM⟩
  refine not_exists_lower_bound_soninAperturePacketCurvature_re_opTrace a b c ha hb hab hbc q
    haq hqb ⟨M - M₀, fun s => ?_⟩
  have h := hM s
  have hCs := hC s
  linarith

/-- **A completion with a floor is unbounded above on the packet family.** -/
theorem not_bddAbove_of_lower_bound_completion
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) (C : Finset ℕ → ℝ)
    (hfloor : ∃ M : ℝ, ∀ s : Finset ℕ,
      M ≤ (opTrace (soninAperturePacketCurvature s a b c (soninCrossingClock a c)
          (one_lt_soninCrossingClock a c) (fun _ => 1))).re + C s) :
    ¬ ∃ M₀ : ℝ, ∀ s : Finset ℕ, C s ≤ M₀ := by
  rintro ⟨M₀, hC⟩
  exact not_exists_lower_bound_soninAperturePacketCurvature_add_bounded a b c ha hb hab hbc q
    haq hqb C M₀ hC hfloor

/-- The same requirement in witness form: the completion must exceed every level at some packet. -/
theorem exists_packet_le_completion_of_lower_bound
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) (C : Finset ℕ → ℝ)
    (hfloor : ∃ M : ℝ, ∀ s : Finset ℕ,
      M ≤ (opTrace (soninAperturePacketCurvature s a b c (soninCrossingClock a c)
          (one_lt_soninCrossingClock a c) (fun _ => 1))).re + C s)
    (L : ℝ) :
    ∃ s : Finset ℕ, L ≤ C s := by
  by_contra hcon
  push Not at hcon
  exact not_bddAbove_of_lower_bound_completion a b c ha hb hab hbc q haq hqb C hfloor
    ⟨L, fun s => (hcon s).le⟩

end RHTower
