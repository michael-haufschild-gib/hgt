import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.TopBlockFeasibility

/-!
# Non-strict inverse-content feasibility

Integrality at any inverse-content coordinate propagates around the cycle and
forces the weighted divisibility congruence. Consequently, a non-strict integer
threshold either gives a composition with a positive unrestricted final part,
or gives one fewer part with divisible total value. This includes the exact
boundary where the unrestricted remainder may be empty.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss
variable {s : ℕ} [NeZero s]

/-- Integrality propagates around the cyclic difference from any chosen coordinate. -/
theorem integral_of_cyclicDifference_at (p : ℤ) (a : ZMod s → ℚ) (u : ZMod s → ℤ)
    (ha : cyclicDifference (p : ℚ) a = fun h => (u h : ℚ))
    (r : ZMod s) (hr : ∃ z : ℤ, a r = z) (h : ZMod s) : ∃ z : ℤ, a h = z := by
  have he : cyclicDifference (p : ℚ) (fun j => a (j + r)) = fun j => (u (j + r) : ℚ) := by
    funext j
    have hh := congrFun ha (j + r)
    simpa only [cyclicDifference, add_right_comm j 1 r] using hh
  have h0 : ∃ z : ℤ, a (0 + r) = z := by simpa only [zero_add] using hr
  have hh := integral_of_cyclicDifference p (fun j => a (j + r))
    (fun j => u (j + r)) he h0 (h - r)
  simpa only [sub_add_cancel] using hh

/-- One integral inverse-content coordinate forces the weighted divisibility congruence. -/
theorem weighted_dvd_of_inverseContent_integral_at (p : ℕ) (hp : 2 ≤ p)
    (u : ZMod s → ℤ) (r : ZMod s)
    (hr : ∃ z : ℤ, inverseContent (p : ℚ) (fun h => (u h : ℚ)) r = z) :
    ((p : ℤ) ^ s - 1) ∣ cyclicWeighted (p : ℤ) u 0 := by
  let a := inverseContent (p : ℚ) (fun h => (u h : ℚ))
  have hpQ : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  have he : cyclicDifference (p : ℚ) a = fun h => (u h : ℚ) :=
    cyclicDifference_inverseContent _ (ne_of_gt (one_lt_pow₀ hpQ (NeZero.ne s))) _
  have hall (h : ZMod s) : ∃ z : ℤ, a h = z :=
    integral_of_cyclicDifference_at (p : ℤ) a u (by exact_mod_cast he) r hr h
  choose b hb using hall
  apply (exists_cyclicDifference_eq_iff p hp u).mp
  refine ⟨b, ?_⟩
  funext h
  have hh := congrFun he h
  simp only [cyclicDifference, hb] at hh
  exact_mod_cast hh

namespace DigitComposition
variable {p k : ℕ} {S : Finset (Digit p)}

/-- A non-strict threshold allows an empty final remainder exactly at the divisible boundary. -/
theorem nonempty_or_divisible_iff_inverseContent_ge (hp : 2 ≤ p) :
    (Nonempty (DigitComposition p s (k + 2) S) ∨
      (Nonempty (DigitComposition p s (k + 1) S) ∧ ((p : ℤ) ^ s - 1) ∣ digitValue p S)) ↔
    ∀ h : ZMod s, ((k + 1 : ℕ) : ℚ) ≤ inverseContent (p : ℚ)
      (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s)) S j : ℚ)) h := by
  constructor
  · rintro (hC | ⟨⟨C⟩, hN⟩)
    · exact fun h => ((nonempty_iff_inverseContent hp (k + 1) S).mp hC h).le
    · exact C.inverseContent_ge_length_of_total_divisible hp hN
  · intro hge
    by_cases hgt : ∀ h : ZMod s, ((k + 1 : ℕ) : ℚ) < inverseContent (p : ℚ)
        (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s)) S j : ℚ)) h
    · exact Or.inl ((nonempty_iff_inverseContent hp (k + 1) S).mpr hgt)
    · push Not at hgt
      obtain ⟨r, hr⟩ := hgt
      have he := le_antisymm hr (hge r)
      have hw := weighted_dvd_of_inverseContent_integral_at p hp
        (tokenContent (fun t : Digit p => (t.1 : ZMod s)) S) r
        ⟨((k + 1 : ℕ) : ℤ), by exact_mod_cast he⟩
      refine Or.inr ⟨(nonempty_iff_inverseContent hp k S).mpr ?_, ?_⟩
      · intro h
        have hh := hge h
        push_cast at hh
        linarith only [hh]
      · have hd := dvd_add (dvd_tokenValue_sub_weightedContent (s := s) p hp Prod.fst S) hw
        simpa only [digitValue, sub_add_cancel] using hd

end DigitComposition
end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.nonempty_or_divisible_iff_inverseContent_ge
