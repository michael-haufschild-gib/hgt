# F2 — the second-prime source-to-window correspondence

- **Stage:** 3-formalized
- **Goal:** Realize the prime-three window shift through the actual Lewis period, enabling the two-prime spectral separation used by the arithmetic orbit criteria.
- **Established [K]:** [Determinant-three cone identity and seven-branch Barnes law](f2-prime-three-barnes-hecke-identity.md).
- **Established [K]:** [Completed and resonant Lewis periods satisfy the global prime-three law](f2-global-prime-three-lewis-hecke.md).
- **Established [K]:** The same normalized Lewis period realizes `(T₃−Id)Φ_H=Φ_(F₃H)`, with `F₃H(u)=√3 H(u+log3)` and complete Weil similitude `Q(F₃H)=3Q(H)`.

## Source identity

For `P_w(a,b)=ζ₂(a|a,b;w)+ζ₂(b|a,b;w)`, positive `a,b`, `Re w>2`, the audited identity is

`P(3a,b)+P(a,3b)+P(a+b,3b)+P(a+2b,3b)`
`+P(3a,a+b)+P(3a,2a+b)+P(2a+b,a+2b)`
`=P(a,b)+3P(3a,3b)`.

These seven cones subdivide the four index-three sublattices of `ℤ²`. The two nontrivial fans have rays `(3,0),(1,1),(0,3)` and `(3,0),(2,1),(1,2),(0,3)`. Boundary rays have weight one and cone interiors weight two. A nonzero residue vector belongs to one index-three sublattice; a vector divisible by three belongs to all four. This yields the identity, equivalently an identity of their rational exponential kernels.

Homogeneity gives a seven-branch operator with eigenvalue `1+3·3^(−2s)` on the completed period. Its arguments are

`3a`, `a/3`, `(a+1)/3`, `(a+2)/3`, `3a/(a+1)`, `3a/(2a+1)`, `(2a+1)/(a+2)`.

The `a/3` branch leaves the original Mayer disc. Reciprocity replaces it by `3/a`, with combined weight `a^(−2s)`. For `1<a<7/6`, all reduced arguments lie in the original period segment. Multiply the local defect by `w−2`. Evaluation of the pole-cleared Mayer state is holomorphic for `Re w>0`; the defect vanishes in `Re w>2`, hence throughout that half-plane. Divide by `w−2` in the open strip `0<Re w<1`. The state equation identifies these disc values with the actual completed period `E_s`, where `w=2s`. Reciprocity restores the original `a/3` branch. All seven branch compositions and weights are real analytic on `a>0`, so vanishing on `(1,7/6)` extends to the whole positive line. At a resonance the zeta forcing vanishes and `E_s` equals the resonant period.

## Window correspondence

For `Φ_H(s,a)=tr(H)(2s)E_s(a)/E_s(1)`, translation of the Mellin integral gives

`tr(F₃H)(2s)=3·3^(−2s)tr(H)(2s)`, `F₃H(u)=√3 H(u+log3)`.

Linearity and the source eigen-equation give `(T₃−Id)Φ_H=Φ_(F₃H)`, alongside the audited prime-two identity. The shift maps stage `A` into `A+log3`; translation invariance and quadratic homogeneity of the complete Weil form give `Q(F₃H)=3Q(H)`. The pair of multipliers at `2,3` separates spectral parameters; this requires an actual second source action, not a prescribed diagonal operator. Neither eigenvalue law alone establishes positivity.

## Lean audit

Source: `MayerScattering/PrimeThreeWindowMellinBridge.lean`.

- `heckeWindowPullThree_mem`
- `tr_heckeWindowPullThree`
- `lewisHeckeT3_windowMellinPeriod`
- `weilQuad_heckeWindowPullThree`

Final individual `lake --old env lean` check passed without warnings. The source-intertwining and complete-form endpoints have only `propext`, `Classical.choice`, `Quot.sound` in their transitive axiom audits. Wired into `RenormalizedIntersectionTheory.lean`. No umbrella was compiled.
