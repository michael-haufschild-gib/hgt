# Unnormalized Xi divisor coefficients and transitions

- **ID:** unnormalized-xi-divisor-transitions
- **Stage:** 3-formalized
- **Type:** INTERFACE THEOREM
- **Source:** Arithmetic Local Divisor Geometry; exact finite canonical-product head
- **Statement:** The real local divisor polynomial, formed from critical copies and conjugate pairs without dividing by the central Xi value, represents every radius head exactly. Its coefficients are the canonically normalized even Taylor coefficients. Disjoint copy transitions obey exact polynomial multiplication and signed coefficient convolution, including central zeros and arbitrary multiplicity.

## Objects and exact statement

For a finite copy set `S`, let `S_crit` select real spectral copies and `S_up` select copies with positive spectral imaginary part. Define

`P_(t,S)(Y)=∏_(q∈S_crit)(Y+(Re z_q−t)²) · ∏_(q∈S_up) Q_(Re z_q−t,Im z_q)(Y)`.

Here `Q_(u,δ)(Y)=Y²+2(u²−δ²)Y+(u²+δ²)²`. For arbitrary `S`, this is the polynomial of its canonical symmetrized carrier `sliceTrunc S`; it does not count an unpaired lower copy independently. A radius head is already pairing-stable, so every original copy and multiplicity is retained there.

For `H={q:|z_q−t|≤R}`, the canonical finite head satisfies

`Q_(t,R)(x)=c_(t,R) P_(t,H)(x²)`.

The scalar is the existing canonical-product scalar and is real and strictly positive for `R≥0`. No division by `XiC t` appears. Thus, for every `k`,

`Q_(t,R)^(2k)(0)/(2k)! = c_(t,R) [Y^k]P_(t,H)`,

and every odd derivative vanishes. These identities are valid also at a central zero of any multiplicity.

For disjoint `S,T`, `P_(t,S∪T)=P_(t,S)P_(t,T)`. In particular, for arbitrary `S,T`,

`P_(t,S)=P_(t,S∩T) P_(t,S\T)`

and

`[Y^n]P_(t,S)=Σ_(i+j=n)[Y^i]P_(t,S∩T) [Y^j]P_(t,S\T)`.

No mixed sign is discarded. A central critical copy contributes exactly `Y`.

## Paper proof

The elementary identity

`Q_(u,δ)(y)=(y+(u+iδ)²)(y+(u−iδ)²)`

identifies each upper copy with its conjugate pair. Critical copies give the remaining real linear factors. The existing multiplicity-copy product decomposition `prod_sliceTrunc` therefore identifies `P_(t,S)` with the full product over `sliceTrunc S`.

Conjugation preserves `|z_q−t|` for real `t`, so a radius head is pairing-stable. Every lower copy is the image of its upper conjugate under the exact copy equivalence; real copies remain fixed in the critical part. Hence `sliceTrunc H=H`. Substitution in the existing canonical-head factorization gives the displayed source identity; its scalar positivity is an existing finite-head theorem.

Represent the resulting entire function by the complex polynomial `C(c)·expand_2(map_ℝ→ℂ P)`. Polynomial Taylor differentiation gives its `n`th coefficient after dividing the `n`th derivative at zero by `n!`. Expansion places coefficient `k` precisely at `2k` and gives zero at odd degrees. This proves the identities without any nonvanishing condition on the center.

Critical and upper filters distribute over union and preserve disjointness. Finite products therefore factor over a disjoint union. Apply this to `(S∩T) ∪ (S\T)=S`, whose pieces are disjoint. The polynomial multiplication formula gives the full coefficient convolution. Finally, evaluation at a real square is nonnegative factor by factor: critical factors are sums of squares and pair factors are `(x²+u²−δ²)²+4u²δ²`.

## Scope and prior work

The finite canonical head, its positive scalar, real-axis nonnegativity and radius-head symmetry are existing corpus inputs. `XiWardGlobalCapAndFiniteHeadArithmetic` also identifies the normalized head away from `XiC t=0`; `XiSliceHeatFiniteHeadReduction` contains normalized disjoint transitions. This interface retains the unnormalized polynomial through central zeros and exposes the exact real coefficients and signed transitions. It is not a new source sign theorem or a worldwide novelty claim.

## Formalization gates

- [x] Exact multiplicity and normalization audited on paper.
- [x] Existing canonical-head and transition inputs inspected.
- [x] `SourceLocalFactors.lean` plain module check and umbrella wiring.
- [x] Transitive axiom audit of source identity, even/odd coefficients and signed split.

`lake --old env lean GaloisForLFunctions/ArithmeticLocalDivisorGeometry/SourceLocalFactors.lean`
passed. Audits of `exists_pos_xiFiniteHead_normalization`, `xiFiniteHead_even_taylor`,
`xiFiniteHead_odd_taylor` and `localDivisorPolynomial_split_coeff` use only
`propext`, `Classical.choice` and `Quot.sound`. Temporary print commands were removed.

The arithmetic coefficient certificate remains open.
