# Sub-Weyl flatness of functional-equation pairs

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Γ46
- **Statement:** For every ε>0, a strip zero ρ=β+iγ with |γ|≥9 satisfies |ζ(½+iγ)|≤Cε|γ|^(33/200+ε)(β−½)². A shallow off-line pair forces the same quadratic bound throughout a short interval around γ.

## Mathematical argument

The sub-Weyl strip profile bounds ζ to the right of ½ by Cη t^(33/200+η). The functional equation and the uniform moving-left-line bound |χ(½−d+it)|≤K t^d extend this to |σ−½|≤r with exponent 33/200+η+r. Choose positive η,r with η+r≤ε and r≤1/20. Conjugation covers negative heights; a disc of radius r about ½+iγ has |Im s| between |γ|−r and |γ|+r, hence is bounded by Cε|γ|^(33/200+ε).

For depth δ≤r/16, the symmetric-zero Taylor estimate gives |ζ(½+iγ)|≤96 Cε r⁻²|γ|^(33/200+ε)δ². For larger depths the central disc bound is absorbed by (16δ/r)². For 0<δ≤η≤r/16, Taylor expansion from one partner, using the other zero to bound its derivative, gives a uniform Oε(|γ|^(33/200+ε)η²) bound on |t−γ|≤η.

## Novelty and remaining wall

`TheDepthOfAnFEPairIsReadOnTheLine` supplies the quadratic mechanism with an O(|γ|²) height cost. `SubWeylZetaProfiles` and `SmoothAFEZetaChiUniformMovingLeftLine` supply unconditional analytic inputs. The new statement replaces that cost by the sub-Weyl power and removes the depth cutoff from the centre estimate. It does not establish the sign of the near-pair discriminant or exclude off-line pairs.

## Lean statements

Module: `ArithmeticDiscreteness/SubWeylFEPairFlatness.lean`.
Namespace: `GaloisForLFunctions.ArithmeticDiscreteness`.

- `exists_norm_zeta_center_le_subWeyl_depth_sq`: central bound for every depth.
- `exists_subWeyl_depth_ge_sqrt_center`: depth ≥ √(|ζ(½+iγ)|/(Cε|γ|^(33/200+ε))).
- `exists_norm_zeta_interval_le_subWeyl_depth_sq`: uniform bound on the short interval.

## Verification

[PROVED HERE] Direct check from `formal/`:

```text
lake --old env lean GaloisForLFunctions/ArithmeticDiscreteness/SubWeylFEPairFlatness.lean
```

All three theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. Module wired into the `ArithmeticDiscreteness` umbrella. Γ46 partially solved; the reality sign remains open.
