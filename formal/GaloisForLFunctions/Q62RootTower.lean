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

namespace Bottcher

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
