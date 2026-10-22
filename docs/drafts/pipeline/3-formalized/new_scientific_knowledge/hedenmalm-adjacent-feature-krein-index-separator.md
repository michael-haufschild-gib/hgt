# Hedenmalm adjacent-feature Krein-index separator

- **ID:** `hedenmalm-adjacent-feature-krein-index-separator`
- **Stage:** `3-formalized/new_scientific_knowledge`
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [AXIOM-CLEAN] [NOT A DENSITY THEOREM]`
- **Parent:** `zeta23-beyond-bandwidth-one-proportion.md`

## Exact claim

For a point `z=x+iy` in the open critical strip, let

```text
e_t(z)=2/[1+(z-t)^2],
t=round(x),
v(z)=(e_t(z),e_(t+1)(z)).
```

Then

```text
det[v(z),v(conj z)]
 = -16 i y [1-y^2-(x-t)(x-t-1)]
   / product_(s in {t,t+1})
       ([1+(z-s)^2][1+(conj z-s)^2]).                 (AF1)
```

If `0<|y|<1/2`, the numerator is nonzero.  Indeed `u=x-t` lies in `[-1/2,1/2]`, and

```text
1-y^2-u(u-1)>0.                                       (AF2)
```

Hence `v(z)` and `v(conj z)` are linearly independent for every nonreal strip point, however
close it lies to the real axis.  Writing `v=xv+i yv` with real vectors, the reflected Weil block

```text
Q(z)=v(z)v(z)^T+v(conj z)v(conj z)^T
    =2[xv xv^T-yv yv^T]
```

satisfies

```text
det Q(z)=-4 det[xv,yv]^2<0.                            (AF3)
```

Thus its real symmetric signature is exactly `(1,1)`.  At `y=0`, `yv=0` and the same block is
positive semidefinite of rank at most one.  Adjacent fixed Hedenmalm features therefore distinguish
an off-line functional-equation pair from an on-line double by negative index even at
submicroscopic displacement.

## Why this is the surviving invariant

Anthropic's tight rank--trace extremizer replaces each off-line pair by a positive projection.
`(AF3)` proves that this projection is only a boundary limit: every actual nonreal pair has one
strictly negative direction.  Its negative eigenvalue tends to zero as `y->0`, so no continuous
trace/Frobenius correction gains a uniform constant.  Exact negative index survives and is forced
to be discontinuous at collision.

## Mandatory falsifiers and scope

1. Reporter centers are fixed before divisor evaluation; only nearest-integer routing chooses one
   adjacent pair from the countable source family.
2. Denominators must be proved nonzero on the whole open strip.
3. `(AF2)` must cover rounding ties and depths arbitrarily close to `1/2`.
4. No multiplicity or density conclusion follows from one pair block.  A proportion theorem needs
   a height-local arithmetic upper bound for negative index, or a source-native singular graph
   converting that index into quantitative budget.
5. Cauchy packets are constant on multiplicity fibres.  This claim separates a nonreal reflected
   pair from a coincident line multiple; it does not separate copies inside one multiple-zero
   fibre.

## Frontier audit

- Internal Cauchy-core theorem says multiplicity fibres are the exact density obstruction; it does
  not contradict `(AF1)`, whose two nodes are distinct whenever `y!=0`.
- Existing five-shift boundary rigidity proves magnitude-based uniform separation must be singular.
  `(AF3)` supplies the alternative discontinuous index channel predicted there.
- External Zeta-23 Lemma R uses only trace, Frobenius norm, integer on-line atoms, and an upper
  bound on positive index; its published tight model does not retain strict negative index of an
  actual reflected pair.
- Weil/screw-function literature treats positivity or operator limits, not this adjacent-feature
  finite signature factorization or a quantitative negative-index density budget.

## Gates

- [x] exact paper algebra `(AF1)`--`(AF3)`
- [x] collision and multiplicity hostile audit
- [x] Lean determinant factorization
- [x] Lean nonvanishing at nearest integer
- [x] Lean negative determinant/signature separator
- [x] umbrella wiring
- [x] targeted build and direct Lean check
- [x] forbidden-token scan
- [x] axiom audit (`propext`, `Classical.choice`, `Quot.sound` only)
- [x] full lint attempted; red only on unrelated pre-existing umbrella-reachability failures

Arithmetic negative-index/source budget remains a separate conjecture. It is not a gate for this
finite separator theorem and no density conclusion is claimed here.

## Lean declarations

Module `formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmAdjacentFeatureKreinIndexSeparator.lean`:

- `adjacentCriticalFeatureEvaluationDet_eq` proves `(AF1)`;
- `adjacentCriticalFeatureEvaluationDet_round_ne_zero` proves nearest-integer detection;
- `reflectedPairBlockDet_adjacentCriticalFeature_neg` proves `(AF3)`;
- `adjacentCriticalFeature_reflectedPair_indefinite` supplies explicit positive and negative
  quadratic witnesses;
- `reflectedPairBlockDet_adjacentCriticalFeature_eq_zero_of_im_eq_zero` proves critical-line
  degeneration;
- `reflectedPairBlockDet_adjacentCriticalFeature_xiRight_round_neg` specializes to every actual
  strict-right Xi copy.
