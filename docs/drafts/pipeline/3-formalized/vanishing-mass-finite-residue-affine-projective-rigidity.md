# Vanishing-mass finite-residue affine projective rigidity

- **ID:** `vanishing-mass-finite-residue-affine-projective-rigidity`
- **Stage:** 3-formalized
- **Type:** `THEOREM (Lean) / GENERAL HT SINGULARITY-CONSTRAINT LAW / NOVELTY UNVERIFIED`
- **Parent:** `../1-in-progress/vanishing-mass-finite-residue-projective-rigidity.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/VanishingMassResidueRigidity.lean`

## Theorem

Let `l` be a nontrivial asymptotic filter.  Let nonzero real masses `w_i` tend to zero, let
`epsilon_i,delta_i` be Boolean orientations, and suppose

```text
sign(delta_i) w_i = a sign(epsilon_i) w_i + q_i            (1)
```

eventually along `l`, where `a` is one real scalar and the correction sequence `q_i` has finite
range.  Then exactly one of the following holds:

```text
a = +1,  q_i = 0 eventually,  epsilon_i = delta_i eventually;
a = -1,  q_i = 0 eventually,  epsilon_i != delta_i eventually. (2)
```

More generally, if

```text
q_i = sum_j c_j n_j(i),
```

with finitely many coefficients `c_j` and each integer-valued order function `n_j` having finite
range, then `q` has finite range and the same conclusion follows.

## Mechanism

Rearranging `(1)` expresses `q_i` as a uniformly bounded signed coefficient times `w_i`, so
`q_i -> 0`.  A finite-range map into a `T1` space which converges to zero is eventually zero.
Cancelling the nonzero mass leaves an equality between two Boolean signs under the single scalar
`a`, forcing `a=+1` or `a=-1` globally and therefore the corresponding projective tail relation.

This is a positive maximal-class statement: every finite quantized residue correction is screened
by a vanishing mass palette, and the surviving asymptotic symmetry is exactly the global
projective sign.

## Universal prime-log specialization

The actual universal prime-log masses are positive and summable, hence tend to zero on the
cofinite prime filter.  The theorem therefore proves that any affine residue action with a finite
correction palette preserving those signed masses must relate the two prime orientations by
eventual equality or eventual opposition.  The conclusion is exactly
`PrimeOrientationTailPairDependent` through the existing projective-tail classification.

This does not yet prove that every differential-field re-expression induces a finite-range
correction.  That local-to-global differential-birational rigidity statement remains isolated in
the parent card.

## Physical lens

`[CONJECTURAL INTERPRETATION]` The masses behave as oscillator strengths tending to zero, while the
finite correction palette behaves as finitely many quantized winding charges from logarithmic
derivatives.  The theorem says that vanishing-strength channels asymptotically screen every fixed
finite charge palette; only a global `Z/2` superselection sector survives.  This interpretation is
a source of candidate laws, not part of the mathematical claim.

## RH route constraint

Any route that encodes prime data in this summable signed pole palette and changes carriers only by
one affine scalar plus finitely generated bounded logarithmic residue charges must preserve the
prime orientation tail up to global sign.  A route capable of independent asymptotic prime sign
surgery must therefore use an infinite correction palette, unbounded pole-order data, or a truly
non-affine singularity action.

## Formal declarations

- `eventually_eq_zero_of_finite_range_tendsto_zero`;
- `vanishingMass_finiteResidueCorrection_projective`;
- `tendsto_universalPrimeWeight_cofinite`;
- `finiteQuantizedResidueCorrection`;
- `finite_range_finiteQuantizedResidueCorrection`;
- `universalPrimeWeight_finiteResidueCorrection_projective`;
- `universalPrimeWeight_finiteQuantizedResidueCorrection_projective`.

## Gates

- [x] abstract vanishing-mass screening theorem formalized
- [x] finite quantized correction producer formalized
- [x] actual universal prime-log specialization formalized
- [x] targeted module build green
- [x] accepted-axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] repository formal lint gate passed
- [ ] exact scientific novelty and significance audit completed

## Status

`[FORMALIZED] [NOVELTY UNVERIFIED]` The theorem is unconditional at the asymptotic residue and
actual universal prime-mass levels.  It supplies a rigorously maximal affine finite-palette class,
but it is not yet the unrestricted differential-field classification.
