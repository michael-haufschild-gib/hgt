/-
# Concrete root-tower independence for the shipped Böttcher capstones

The abstract two-coordinate Kummer descent `KummerRootApplications.noRelation_pow_descent_both`
lifts any established `NoRelation K F G` to independence of every finite root of `F` from every
finite root of `G`.  Here it is instantiated at the CONCRETE inverse-Böttcher coordinates
`phiMero c₁, phiMero c₂` of the shipped disconnected-pair capstones:

* `q62_phiMero_linGap`   (linear norm gap `‖c₂‖ ≲ ‖c₁‖/600`, unconditional)
* `q62_phiMero_norm_gap` (quadratic norm gap / mixed `300·(max 2‖c₂‖)² ≤ ‖c₁‖`, unconditional)

giving: on the common far domain `U`, every `p`-th root of `φ_{c₁}` is algebraically independent
of every `q`-th root of `φ_{c₂}` over `K = ℂ(z)` — the full finite root tower of the ACTUAL
Böttcher coordinates in `meroField U`, not only the abstract field elements.  In particular every
`2^j`-th Böttcher root of one coordinate is independent of every `2^k`-th root of the other.

Axiom-clean.  No new q62 input; the Böttcher-lane files are untouched — this file only consumes the
two shipped capstones and the field-generic descent.
-/
import GaloisForLFunctions.KummerRootApplications
import GaloisForLFunctions.Bottcher.W4LinCapstone
import GaloisForLFunctions.Bottcher.MixedTowerData
import GaloisForLFunctions.Bottcher.Q62BothConnectedExposed

namespace Bottcher

/-- Domain-specific root lift for concrete inverse-Böttcher coordinates.  Any established
`NoRelation` between `phiMero c₁` and `phiMero c₂` on a common far domain lifts to every finite
root of both coordinates. -/
theorem q62_phiMero_roots_of_noRelation
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} {hU₁ : U ⊆ escapeOpen c₁} {hU₂ : U ⊆ escapeOpen c₂}
    (hNR :
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- **Linear-gap disconnected q62 — full finite root tower.**  For disconnected `c₁, c₂` with
`‖c₁‖ ≥ 1000`, `‖c₂‖ ≥ 2` and the linear gap `(√(2‖c₂‖)+1)² ≤ ‖c₁‖/300`, on the common far domain
`U` every `p`-th root `χ` of `φ_{c₁}` is algebraically independent over `ℂ(z)` of every `q`-th root
`η` of `φ_{c₂}`.  The base independence is `q62_phiMero_linGap`; the lift is the two-coordinate
Kummer descent. -/
theorem q62_phiMero_linGap_roots {c₁ c₂ : ℂ}
    (hc₁ : (0:ℂ) ∉ filledJulia c₁) (hc1000 : (1000:ℝ) ≤ ‖c₁‖)
    (hc₂ : (0:ℂ) ∉ filledJulia c₂) (hc₂2 : (2:ℝ) ≤ ‖c₂‖)
    (hsgap : (Real.sqrt (2 * ‖c₂‖) + 1) ^ 2 ≤ ‖c₁‖ / 300) :
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂),
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ {χ η : meroField U} {p q : ℕ},
        χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
        NoRelation (RatFunc ℂ) χ η := by
  obtain ⟨U, hUo, hUc, hUne, hUinf, hU₁, hU₂, hNR⟩ :=
    q62_phiMero_linGap hc₁ hc1000 hc₂ hc₂2 hsgap
  refine ⟨U, hUo, hUc, hUne, hUinf, hU₁, hU₂, ?_⟩
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- **Quadratic-gap / mixed disconnected q62 — full finite root tower.**  For disconnected `c₁`
with `‖c₁‖ ≥ 1000`, any nonexceptional `c₂ ∉ {0, -2}` and the quadratic gap
`300·(max 2 ‖c₂‖)² ≤ ‖c₁‖`, on the common far domain `U` every `p`-th root `χ` of `φ_{c₁}` is
algebraically independent over `ℂ(z)` of every `q`-th root `η` of `φ_{c₂}`.  The base independence
is `q62_phiMero_norm_gap` (which itself splits mixed/both-disconnected internally); the lift is the
two-coordinate Kummer descent. -/
theorem q62_phiMero_norm_gap_roots {c₁ c₂ : ℂ}
    (hc₁ : (0:ℂ) ∉ filledJulia c₁) (hc1000 : (1000:ℝ) ≤ ‖c₁‖)
    (hc₂0 : c₂ ≠ 0) (hc₂2 : c₂ ≠ -2)
    (hgap : 300 * (max 2 ‖c₂‖) ^ 2 ≤ ‖c₁‖) :
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂),
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ {χ η : meroField U} {p q : ℕ},
        χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
        NoRelation (RatFunc ℂ) χ η := by
  obtain ⟨U, hUo, hUc, hUne, hUinf, hU₁, hU₂, hNR⟩ :=
    q62_phiMero_norm_gap hc₁ hc1000 hc₂0 hc₂2 hgap
  refine ⟨U, hUo, hUc, hUne, hUinf, hU₁, hU₂, ?_⟩
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- **Mixed disconnected/connected q62 — full finite root tower, gap-free.**  For a far disconnected
`c₁` (`‖c₁‖ ≥ 1000`) and ANY connected `c₂ ∈ mandelbrot ∖ {0, -2}` — with NO norm-gap hypothesis —
on the common far domain `U` every `p`-th root `χ` of `φ_{c₁}` is algebraically independent over
`ℂ(z)` of every `q`-th root `η` of `φ_{c₂}`.  This covers the entire Mandelbrot set (minus the two
exceptional parameters) for the second coordinate, strictly broader than the mixed branch of
`q62_phiMero_norm_gap_roots` (which carries a redundant quadratic-gap argument).  The base
independence is `q62_phiMero_mixed_far` (mixed case needs no E–vS rigidity — the monodromy of the
disconnected `c₁` coordinate alone settles it); the lift is the two-coordinate Kummer descent. -/
theorem q62_phiMero_mixed_far_roots {c₁ c₂ : ℂ} (hc₁ : (0:ℂ) ∉ filledJulia c₁)
    (hc1000 : (1000:ℝ) ≤ ‖c₁‖)
    (hc₂M : c₂ ∈ mandelbrot) (hc₂0 : c₂ ≠ 0) (hc₂2 : c₂ ≠ -2) :
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂),
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ {χ η : meroField U} {p q : ℕ},
        χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
        NoRelation (RatFunc ℂ) χ η := by
  obtain ⟨U, hUo, hUc, hUne, hUinf, hU₁, hU₂, hNR⟩ :=
    q62_phiMero_mixed_far hc₁ hc1000 hc₂M hc₂0 hc₂2
  refine ⟨U, hUo, hUc, hUne, hUinf, hU₁, hU₂, ?_⟩
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- **Mixed q62, swapped orientation — full finite root tower, gap-free.**  The other orientation of
the mixed regime: `c₁ ∈ mandelbrot ∖ {0, -2}` connected and `c₂` far disconnected (`‖c₂‖ ≥ 1000`),
again with no norm gap.  On the common far domain `U` every `p`-th root of `φ_{c₁}` is algebraically
independent over `ℂ(z)` of every `q`-th root of `φ_{c₂}`.  Consumes `q62_phiMero_mixed_far_swapped`;
the lift is the two-coordinate Kummer descent. -/
theorem q62_phiMero_mixed_far_roots_swapped {c₁ c₂ : ℂ}
    (hc₁M : c₁ ∈ mandelbrot) (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2)
    (hc₂ : (0:ℂ) ∉ filledJulia c₂) (hc1000 : (1000:ℝ) ≤ ‖c₂‖) :
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂),
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ {χ η : meroField U} {p q : ℕ},
        χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
        NoRelation (RatFunc ℂ) χ η := by
  obtain ⟨U, hUo, hUc, hUne, hUinf, hU₁, hU₂, hNR⟩ :=
    q62_phiMero_mixed_far_swapped hc₁M hc₁0 hc₁2 hc₂ hc1000
  refine ⟨U, hUo, hUc, hUne, hUinf, hU₁, hU₂, ?_⟩
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

end Bottcher

namespace Bottcher

/-- **Linear-gap q62 in either orientation — full finite root tower.**
This consumes `q62_phiMero_linGap_either` and lifts the resulting Böttcher-coordinate independence to
all finite roots of both coordinates. -/
theorem q62_phiMero_linGap_either_roots {c₁ c₂ : ℂ}
    (hor :
      ((0:ℂ) ∉ filledJulia c₁ ∧ (1000:ℝ) ≤ ‖c₁‖ ∧
        (0:ℂ) ∉ filledJulia c₂ ∧ (2:ℝ) ≤ ‖c₂‖ ∧
        (Real.sqrt (2 * ‖c₂‖) + 1) ^ 2 ≤ ‖c₁‖ / 300) ∨
      ((0:ℂ) ∉ filledJulia c₁ ∧ (2:ℝ) ≤ ‖c₁‖ ∧
        (0:ℂ) ∉ filledJulia c₂ ∧ (1000:ℝ) ≤ ‖c₂‖ ∧
        (Real.sqrt (2 * ‖c₁‖) + 1) ^ 2 ≤ ‖c₂‖ / 300)) :
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂),
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ {χ η : meroField U} {p q : ℕ},
        χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
        NoRelation (RatFunc ℂ) χ η := by
  obtain ⟨U, hUo, hUc, hUne, hUinf, hU₁, hU₂, hNR⟩ := q62_phiMero_linGap_either hor
  refine ⟨U, hUo, hUc, hUne, hUinf, hU₁, hU₂, ?_⟩
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- **Quadratic-gap / mixed q62 in either orientation — full finite root tower.**
This consumes `q62_phiMero_norm_gap_either` and lifts the resulting Böttcher-coordinate independence
to all finite roots of both coordinates. -/
theorem q62_phiMero_norm_gap_either_roots {c₁ c₂ : ℂ}
    (hor :
      ((0:ℂ) ∉ filledJulia c₁ ∧ (1000:ℝ) ≤ ‖c₁‖ ∧ c₂ ≠ 0 ∧ c₂ ≠ -2 ∧
        300 * (max 2 ‖c₂‖) ^ 2 ≤ ‖c₁‖) ∨
      ((0:ℂ) ∉ filledJulia c₂ ∧ (1000:ℝ) ≤ ‖c₂‖ ∧ c₁ ≠ 0 ∧ c₁ ≠ -2 ∧
        300 * (max 2 ‖c₁‖) ^ 2 ≤ ‖c₂‖)) :
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂),
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ {χ η : meroField U} {p q : ℕ},
        χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
        NoRelation (RatFunc ℂ) χ η := by
  obtain ⟨U, hUo, hUc, hUne, hUinf, hU₁, hU₂, hNR⟩ := q62_phiMero_norm_gap_either hor
  refine ⟨U, hUo, hUc, hUne, hUinf, hU₁, hU₂, ?_⟩
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

end Bottcher

namespace Bottcher

/-- **Linear-gap q62, swapped orientation — full finite root tower.**
Direct swapped-orientation API for the finite-root tower over the linear-gap disconnected capstone. -/
theorem q62_phiMero_linGap_roots_swapped {c₁ c₂ : ℂ}
    (hc₁ : (0:ℂ) ∉ filledJulia c₁) (hc₁2 : (2:ℝ) ≤ ‖c₁‖)
    (hc₂ : (0:ℂ) ∉ filledJulia c₂) (hc1000 : (1000:ℝ) ≤ ‖c₂‖)
    (hsgap : (Real.sqrt (2 * ‖c₁‖) + 1) ^ 2 ≤ ‖c₂‖ / 300) :
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂),
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ {χ η : meroField U} {p q : ℕ},
        χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
        NoRelation (RatFunc ℂ) χ η := by
  obtain ⟨U, hUo, hUc, hUne, hUinf, hU₁, hU₂, hNR⟩ :=
    q62_phiMero_linGap_swapped hc₁ hc₁2 hc₂ hc1000 hsgap
  refine ⟨U, hUo, hUc, hUne, hUinf, hU₁, hU₂, ?_⟩
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

/-- **Quadratic-gap / mixed q62, swapped orientation — full finite root tower.**
Direct swapped-orientation API for finite roots over `q62_phiMero_norm_gap_swapped`. -/
theorem q62_phiMero_norm_gap_roots_swapped {c₁ c₂ : ℂ}
    (hc₂ : (0:ℂ) ∉ filledJulia c₂) (hc1000 : (1000:ℝ) ≤ ‖c₂‖)
    (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2)
    (hgap : 300 * (max 2 ‖c₁‖) ^ 2 ≤ ‖c₂‖) :
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂),
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ {χ η : meroField U} {p q : ℕ},
        χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
        NoRelation (RatFunc ℂ) χ η := by
  obtain ⟨U, hUo, hUc, hUne, hUinf, hU₁, hU₂, hNR⟩ :=
    q62_phiMero_norm_gap_swapped hc₂ hc1000 hc₁0 hc₁2 hgap
  refine ⟨U, hUo, hUc, hUne, hUinf, hU₁, hU₂, ?_⟩
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

end Bottcher

namespace Bottcher

/-- **Mixed disconnected/connected q62 in either orientation — full finite root tower.**
A single API for the gap-free mixed far regime: one parameter is far disconnected (`‖c‖ ≥ 1000`) and
the other is connected nonexceptional.  The conclusion lifts Böttcher-coordinate independence to all
finite roots of both coordinates. -/
theorem q62_phiMero_mixed_far_roots_either {c₁ c₂ : ℂ}
    (hor :
      ((0:ℂ) ∉ filledJulia c₁ ∧ (1000:ℝ) ≤ ‖c₁‖ ∧
        c₂ ∈ mandelbrot ∧ c₂ ≠ 0 ∧ c₂ ≠ -2) ∨
      (c₁ ∈ mandelbrot ∧ c₁ ≠ 0 ∧ c₁ ≠ -2 ∧
        (0:ℂ) ∉ filledJulia c₂ ∧ (1000:ℝ) ≤ ‖c₂‖)) :
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂),
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ {χ η : meroField U} {p q : ℕ},
        χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
        NoRelation (RatFunc ℂ) χ η := by
  rcases hor with hleft | hright
  · rcases hleft with ⟨hc₁, hc1000, hc₂M, hc₂0, hc₂2⟩
    exact q62_phiMero_mixed_far_roots hc₁ hc1000 hc₂M hc₂0 hc₂2
  · rcases hright with ⟨hc₁M, hc₁0, hc₁2, hc₂, hc1000⟩
    exact q62_phiMero_mixed_far_roots_swapped hc₁M hc₁0 hc₁2 hc₂ hc1000

end Bottcher

namespace Bottcher

/-- **Large-disconnected mixed-or-gap q62 — full finite root tower.**  If `c₁` is far disconnected
(`‖c₁‖ ≥ 1000`) and `c₂` is nonexceptional, then either connectedness of `c₂` or the quadratic
norm-gap condition gives a common far carrier on which every finite root of `φ_{c₁}` is
algebraically independent of every finite root of `φ_{c₂}` over `ℂ(z)`. -/
theorem q62_phiMero_large_disconnected_mixed_or_norm_gap_roots {c₁ c₂ : ℂ}
    (hc₁ : (0:ℂ) ∉ filledJulia c₁) (hc1000 : (1000:ℝ) ≤ ‖c₁‖)
    (hc₂0 : c₂ ≠ 0) (hc₂2 : c₂ ≠ -2)
    (hcase : c₂ ∈ mandelbrot ∨ 300 * (max 2 ‖c₂‖) ^ 2 ≤ ‖c₁‖) :
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂),
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ {χ η : meroField U} {p q : ℕ},
        χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
        NoRelation (RatFunc ℂ) χ η := by
  rcases hcase with hc₂M | hgap
  · exact q62_phiMero_mixed_far_roots hc₁ hc1000 hc₂M hc₂0 hc₂2
  · exact q62_phiMero_norm_gap_roots hc₁ hc1000 hc₂0 hc₂2 hgap

/-- **Swapped large-disconnected mixed-or-gap q62 — full finite root tower.**  The symmetric
orientation of `q62_phiMero_large_disconnected_mixed_or_norm_gap_roots`: `c₂` is the far
disconnected parameter, while the nonexceptional `c₁` is handled by either connectedness or the
quadratic norm-gap condition. -/
theorem q62_phiMero_large_disconnected_mixed_or_norm_gap_roots_swapped {c₁ c₂ : ℂ}
    (hc₂ : (0:ℂ) ∉ filledJulia c₂) (hc1000 : (1000:ℝ) ≤ ‖c₂‖)
    (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2)
    (hcase : c₁ ∈ mandelbrot ∨ 300 * (max 2 ‖c₁‖) ^ 2 ≤ ‖c₂‖) :
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂),
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ {χ η : meroField U} {p q : ℕ},
        χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
        NoRelation (RatFunc ℂ) χ η := by
  rcases hcase with hc₁M | hgap
  · exact q62_phiMero_mixed_far_roots_swapped hc₁M hc₁0 hc₁2 hc₂ hc1000
  · exact q62_phiMero_norm_gap_roots_swapped hc₂ hc1000 hc₁0 hc₁2 hgap

/-- **Either-orientation large-disconnected mixed-or-gap q62 — full finite root tower.**  A single
placement-free API for the strongest shipped large-disconnected root-tower discharge: one parameter
is far disconnected, the other is nonexceptional and is either connected or quadratically
norm-separated. -/
theorem q62_phiMero_large_disconnected_mixed_or_norm_gap_roots_either {c₁ c₂ : ℂ}
    (hor :
      ((0:ℂ) ∉ filledJulia c₁ ∧ (1000:ℝ) ≤ ‖c₁‖ ∧
        c₂ ≠ 0 ∧ c₂ ≠ -2 ∧
        (c₂ ∈ mandelbrot ∨ 300 * (max 2 ‖c₂‖) ^ 2 ≤ ‖c₁‖)) ∨
      ((0:ℂ) ∉ filledJulia c₂ ∧ (1000:ℝ) ≤ ‖c₂‖ ∧
        c₁ ≠ 0 ∧ c₁ ≠ -2 ∧
        (c₁ ∈ mandelbrot ∨ 300 * (max 2 ‖c₁‖) ^ 2 ≤ ‖c₂‖))) :
    ∃ (U : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
      (hUinf : U.Infinite) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂),
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ {χ η : meroField U} {p q : ℕ},
        χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
        NoRelation (RatFunc ℂ) χ η := by
  rcases hor with hleft | hright
  · rcases hleft with ⟨hc₁, hc1000, hc₂0, hc₂2, hcase⟩
    exact q62_phiMero_large_disconnected_mixed_or_norm_gap_roots
      hc₁ hc1000 hc₂0 hc₂2 hcase
  · rcases hright with ⟨hc₂, hc1000, hc₁0, hc₁2, hcase⟩
    exact q62_phiMero_large_disconnected_mixed_or_norm_gap_roots_swapped
      hc₂ hc1000 hc₁0 hc₁2 hcase

end Bottcher

namespace Bottcher

/-- **Both-connected q62 from open problem 6 — full finite root tower.**
On any connected meromorphic carrier `U`, the exposed-one-sided/smooth-piece connected capstone
`q62_phiMero_bothconnected_of_op6` lifts to all finite roots of both Böttcher coordinates. -/
theorem q62_phiMero_bothconnected_of_op6_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c₁ c₂ : ℂ} (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot)
    (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2) (hc₂0 : c₂ ≠ 0) (hc₂2 : c₂ ≠ -2)
    (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hexp : ExposedOneSided c₁ c₂ ∨ ExposedOneSided c₂ c₁)
    (hrig12 : SmoothPieceRigidity c₁ c₂) (hrig21 : SmoothPieceRigidity c₂ c₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR := q62_phiMero_bothconnected_of_op6 hUo hUc hUne hUinf
    hc₁M hc₂M hc₁0 hc₁2 hc₂0 hc₂2 hU₁ hU₂ hexp hrig12 hrig21
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

end Bottcher

namespace Bottcher

/-- **General exposed-one-sided q62 capstone — full finite root tower.**
This is the root-tower lift of `q62_phiMero_independence_of_exposed_oneSided`: once the connected
exposed-tip input and the disconnected monodromy inputs prove Böttcher-coordinate independence on a
carrier `U`, every finite root of one coordinate is independent of every finite root of the other. -/
theorem q62_phiMero_independence_of_exposed_oneSided_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2) (hc₂0 : c₂ ≠ 0) (hc₂2 : c₂ ≠ -2)
    (hmono₁ : c₁ ∉ mandelbrot →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (phiMero c₂ hU₂) = phiMero c₂ hU₂ ∧ σ ζ = ζ ∧
        σ (phiMero c₁ hU₁) = ζ * phiMero c₁ hU₁)
    (hmono₂ : c₂ ∉ mandelbrot →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (phiMero c₁ hU₁) = phiMero c₁ hU₁ ∧ σ ζ = ζ ∧
        σ (phiMero c₂ hU₂) = ζ * phiMero c₂ hU₂)
    (hexp : c₁ ∈ mandelbrot → c₂ ∈ mandelbrot → ExposedOneSided c₁ c₂)
    (hrig : c₁ ∈ mandelbrot → c₂ ∈ mandelbrot → SmoothPieceRigidity c₁ c₂) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR := q62_phiMero_independence_of_exposed_oneSided hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
    hc₁0 hc₁2 hc₂0 hc₂2 hmono₁ hmono₂ hexp hrig
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

end Bottcher

namespace Bottcher

/-- **Conditional q62 dispatcher — full finite root tower.**
This lifts `q62_phiMero_independence_conditional`: for any placement predicate `Disc`, once the two
monodromy inputs, the connected transcendence inputs, and the both-connected independence input
settle the Böttcher coordinates, all finite roots of both coordinates are independent. -/
theorem q62_phiMero_independence_conditional_roots
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (Disc : ℂ → Prop)
    (hmono₁ : Disc c₁ →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (phiMero c₂ hU₂) = phiMero c₂ hU₂ ∧ σ ζ = ζ ∧
        σ (phiMero c₁ hU₁) = ζ * phiMero c₁ hU₁)
    (hmono₂ : Disc c₂ →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[RatFunc ℂ] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧ σ (phiMero c₁ hU₁) = phiMero c₁ hU₁ ∧ σ ζ = ζ ∧
        σ (phiMero c₂ hU₂) = ζ * phiMero c₂ hU₂)
    (htrans₁ : ¬ Disc c₁ →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (htrans₂ : ¬ Disc c₂ →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hbothconn : ¬ Disc c₁ → ¬ Disc c₂ →
      haveI := isDomain_analyticSubring U hUo hUc hUne
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    ∀ {χ η : meroField U} {p q : ℕ},
      χ ^ p = phiMero c₁ hU₁ → η ^ q = phiMero c₂ hU₂ →
      NoRelation (RatFunc ℂ) χ η := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hNR := q62_phiMero_independence_conditional hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ Disc
    hmono₁ hmono₂ htrans₁ htrans₂ hbothconn
  intro χ η p q hχ hη
  exact KummerRootApplications.noRelation_pow_descent_both hχ hη hNR

end Bottcher
