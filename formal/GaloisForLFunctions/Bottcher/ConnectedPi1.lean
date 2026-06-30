/-
# Toward `π₁(escapeLevel c n) ≅ ℤ` and the connected-case winding divisibility (`hlift`, #22)

In the connected case (`c ∉ escapeLevel c n` for all `n`, i.e. the critical value never escapes) the
quadratic `f = z²+c` restricts to a genuine degree-`2` **covering map** of escape-level subtypes
`escapeLevel c (n+1) → escapeLevel c n` (`isCoveringMap_quadratic_escapeLevel`, this file, upgrading the
`IsCoveringMapOn` of `EscapeCovering`). This is the foundational object for the covering-`π₁` route to
the winding-divisibility hypothesis `hlift`:

* `f` connected double cover ⟹ its monodromy `π₁(escapeLevel c n) → ℤ/2` is onto ⟹ `image f∗ = ` the
  index-`2` (even) subgroup;
* `π₁(escapeLevel c n) ≅ ℤ` inductively (base `Pi1EscapeOpen`), with `f∗(gen) = 2·gen`;
* hence every `f∗[ℓ]` is even, so `(βlev_n)∗ ∘ f∗` lands in the squares of `π₁(ℂ*)` — exactly the
  `hlift` consumed by `exists_levelRoot_of_lift` / `exists_sqrt_pullback_of_lift`.

The covering map and the homeomorphism identifying its domain with `escapeLevel c (n+1)` are built here.
-/
import GaloisForLFunctions.Bottcher.EscapeCovering
import GaloisForLFunctions.Bottcher.CoveringPi1
import Mathlib.Analysis.Complex.CoveringMap

open Topology

namespace Bottcher

/-- **`f = z²+c` is a covering map of escape-level subtypes.** In the connected case
(`c ∉ escapeLevel c n`), `(escapeLevel c n).restrictPreimage (quadratic c)` — whose domain is
`↑((quadratic c) ⁻¹' escapeLevel c n) = ↑(escapeLevel c (n+1))` (`escapeLevel_succ_eq_preimage`) — is a
genuine `IsCoveringMap` onto `↑(escapeLevel c n)`. Upgrades `isCoveringMapOn_quadratic_escapeLevel`. -/
theorem isCoveringMap_quadratic_escapeLevel (c : ℂ) (n : ℕ) (hc : c ∉ escapeLevel c n) :
    IsCoveringMap ((escapeLevel c n).restrictPreimage (quadratic c)) :=
  (isCoveringMapOn_quadratic_escapeLevel c n hc).isCoveringMap_restrictPreimage

end Bottcher
