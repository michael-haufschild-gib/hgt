# Arbitrary-orientation affine Gamma products have one scaled alien charge

- **ID:** `oriented-arbitrary-scale-gamma-alien-charge-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean 4) / UNIVERSAL LAW 2 IN CORPUS EXHAUSTION
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Subsumes:** `incommensurable-gamma-orbit-free-quasianalyticity`,
  `gamma-reflection-charge-conjugation-doubling`
- **Statement:** A finite signed product of affine Euler Gamma factors with arbitrary nonzero real
  slopes is differentially algebraic exactly when its reflection-normalized scaled alien character
  vanishes; otherwise it is hypertranscendental. No rational commensurability assumption and no
  common orientation are required.

## 1. Datum and reflection normalization

Let

```text
G(s)=exp(alpha*s) product_(j=1)^d Gamma(lambda_j*s+mu_j)^m_j,
lambda_j in R\{0}, mu_j in C, m_j in Z.                    (1)
```

For each factor define positive normalized data

```text
L_j=abs(lambda_j),
nu_j=mu_j,       q_j=m_j       if lambda_j>0,
nu_j=1-mu_j,     q_j=-m_j      if lambda_j<0.              (2)
```

Euler reflection gives, for a negative slope,

```text
Gamma(lambda*s+mu)^m
 = (pi/sin(pi*(lambda*s+mu)))^m
   Gamma((-lambda)*s+(1-mu))^(-m).                         (3)
```

The sine factor in `(3)` is a nonzero meromorphic differentially algebraic gauge. Therefore

```text
G=A_DA * G_plus,
G_plus=exp(alpha*s) product_j Gamma(L_j*s+nu_j)^q_j,        (4)
```

and `G` is DA, respectively HT, exactly when `G_plus` is DA, respectively HT.

## 2. Oriented scaled alien character

For real `t!=0`, define

```text
R_G^or(t)=sum_(j: t/L_j in Z\{0})
  q_j L_j exp(-2*pi*i*(t/L_j)*nu_j).                       (5)
```

This is not the unreflected sum: orientation reversal conjugates the affine pole lattice by
`(lambda,mu,m) -> (-lambda,1-mu,-m)` before its contribution is evaluated. Slopes in distinct
rational commensurability classes have disjoint nonzero Borel singular lattices, so they cannot
cancel each other.

## 3. Universal classification

Exactly one branch occurs:

```text
R_G^or=0
  iff G_plus=C exp(beta*s) Q(s), Q in C(s)^x
  iff G is differentially algebraic over C(s);             (6)

R_G^or!=0
  iff G_plus is hypertranscendental over C(s)
  iff G is hypertranscendental over C(s).                  (7)
```

Thus arbitrary orientation and arbitrary scale rank commute at the classification level:
reflection first removes orientation into a DA gauge, while the scaled alien character then
separates every rational commensurability class. No third DA carrier appears at their intersection.

## 4. Proof

1. Apply Euler reflection `(3)` independently to every negative-slope factor. Integer powers of
   each sine gauge remain nonzero and DA, proving `(4)` and preservation of the DA/HT alternatives.
2. The positive arbitrary-scale theorem from
   `incommensurable-gamma-orbit-free-quasianalyticity.md` applies to `G_plus`. Its finite product of
   matching commuting shift differences sends the complete trigamma tail to `C(s)`.
3. Finite-shift peeling, using the Adamczewski--Dreyfus--Hardouin one-shift theorem, forces that tail
   into the rational or HT branch.
4. The scaled Borel-residue character is exactly `(5)`. Its vanishing is equivalent, class by class,
   to cancellation of every common-scale translation-orbit charge; nonvanishing excludes the
   rational branch.
5. Multiplication by the nonzero DA gauge in `(4)` preserves differential algebraicity and its
   complement. Equations `(6)--(7)` follow.

No numerical experiment or computed special case enters the proof.

## 5. Strict subsumption

- If every `lambda_j>0`, normalization is the identity and `(6)--(7)` recover the arbitrary-positive-
  scale alien-charge classifier.
- If all `abs(lambda_j)` are commensurable, `(5)` becomes the finite Fourier transform of the
  oriented common-scale orbit charge and recovers reflection charge conjugation plus the exact
  common-scale DA/HT phase law.
- Mixed signs and at least two incommensurable absolute scales are covered by neither predecessor
  alone.

## 6. Hostile attacks and exact boundary

1. **Reflection zeros do not invalidate the gauge.** The argument is in the meromorphic field;
   `pi/sin` is nonzero as a field element even though it has poles.
2. **Negative exponents are allowed.** DA elements form a field, so inverse sine gauges remain DA.
3. **Offsets are arbitrary complex numbers.** They enter only through reflection and the finite
   Fourier character; no reality condition is used.
4. **Zero slopes are excluded.** A zero-slope Gamma factor is constant (or undefined at a pole) and
   is not part of the affine-lattice mechanism.
5. **Complex nonreal slopes are not claimed.** Their singular lattices lie on different complex
   rays and require a complex-frequency carrier, not the real scaled character `(5)`.
6. **Infinite products are not claimed.** Finiteness is load-bearing for the commuting-shift word,
   the Borel residue sum, and DA-field gauge product.
7. **Charge is not total multiplicity.** Nonzero orbit charges may have zero total exponent; `(5)`
   retains offsets and all scaled singular frequencies.

The strongest positive survivor after these attacks is exactly `(6)--(7)`; weakening to a mere
noncancellation obstruction would discard the elementary normal form in the zero-charge branch.

## 7. Literature attack

Adjacent established results are substantial:

- Euler reflection and Gauss multiplication are classical (NIST DLMF §5.5).
- Bank--Kaufman extend Hoelder hypertranscendence, and Bank's 1980 canonical-product theorem treats
  the two-ray product `Gamma(z)Gamma(cz)`, including the reflection degeneration at `c=-1`.
- Adamczewski--Dreyfus--Hardouin prove the rational-or-HT dichotomy for Laurent solutions of rational
  linear shift equations (JAMS 34 (2021), DOI `10.1090/jams/960`).
- Resurgent Gamma/Bernoulli Borel singularities are classical; Sauzin gives a modern treatment.

Searches for arbitrary finite products `Gamma(lambda_j z+mu_j)^m_j`, mixed positive/negative
slopes, incommensurable affine Gamma products, and a complete reflection-normalized Borel-residue
classification located the two-factor ray theorem and broad parent machinery, but not `(5)--(7)`.
This is not proof of priority. The law remains `[NOVELTY UNVERIFIED]`, and its proof is a short but
strict synthesis of the two corpus predecessors.

## 8. Lean status

`formal/GaloisForLFunctions/HTGeometry/GammaOrientedAlienCharge.lean` formalizes the exact reusable
boundary:

- `OrientedAffineGammaFactor` and `PositiveAffineGammaFactor`;
- `OrientedAffineGammaFactor.positiveNormalization` with proved positive/negative formulas;
- `scaledGammaAlienChargeAt`, `ScaledGammaAlienChargeZero`, and
  `OrientedGammaAlienChargeZero`;
- `orientedGammaAlienCharge_shiftWord_classification`, joining reflection preservation to
  `alienCharge_shiftWord_classification`;
- `orientedGammaAlienCharge_shiftWord_exactClassification`, giving both exact iff statements when
  rationality and HT are disjoint.

The ADH one-shift theorem, scaled-Borel selector, and analytic reflection preservation remain named
hypotheses rather than hidden axioms. The project proves the normalization and universal assembly.

## Gates

- [x] two predecessor laws identified and strictly subsumed
- [x] negative-slope normalization proved
- [x] arbitrary commensurability rank retained
- [x] exact zero/nonnull classification proved on paper
- [x] hostile edge-case audit completed
- [x] preliminary exact literature audit completed
- [x] exact abstract theorem formalized in Lean
- [ ] independent full-text priority audit
- [ ] complex-slope extension or counterclassification
