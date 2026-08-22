# A geometric Källén--Lehmann spectrum gives a Gaussian field with hypertranscendental propagator

- **ID:** `q-geometric-generalized-free-field-hypertranscendence`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / `[BRIDGE]`
- **Scientific status:** `[PROVED FROM PUBLISHED PARENT THEOREMS]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `../../1-in-progress/wick-kolchin-interaction-spectrum.md`
- **Scope:** general positive spectral QFT; no RH or distinguished special-function input
- **Statement:** For every `0<a,b<1`, the compact positive spectral measure
  `(1-a) sum a^k delta_(b^k)` defines a generalized free field whose Euclidean momentum
  propagator is hypertranscendental as a germ at infinity, although every connected correlation
  function above order two vanishes.

## Theorem `[PROVED]`

Fix real numbers `a,b` with

```text
0 < a < 1,   0 < b < 1.                                    (1)
```

Define the positive mass-squared measure

```text
rho_(a,b) = (1-a) sum_(k>=0) a^k delta_(b^k).               (2)
```

Then:

1. `rho_(a,b)` is a probability measure supported in `[0,1]` and is an admissible positive,
   polynomially bounded Källén--Lehmann weight.
2. It defines a scalar generalized free Wightman field.  Its generating functional is Gaussian,
   and its truncated/connected `n`-point functions vanish for every `n != 2`.
3. Its normalized mass-resolvent response

   ```text
   R_(a,b)(z) = integral 1/(1-z t) d rho_(a,b)(t)            (3)
   ```

   is hypertranscendental over `C(z)`.
4. Its Euclidean momentum propagator

   ```text
   G_(a,b)(s) = integral 1/(s+t) d rho_(a,b)(t)              (4)
   ```

   is hypertranscendental over `C(s)` as a germ at infinity.

Consequently hypertranscendence of a positive QFT two-point spectral response does not imply
interaction, non-Gaussianity, nonzero higher connected correlators, chaos, or quantum gravity.

## Proof

### Positive spectral realization

The total mass is

```text
(1-a) sum_(k>=0) a^k = 1.                                  (5)
```

Every atom `b^k` lies in `(0,1]`, so `(2)` is finite, positive, compactly supported, and therefore
polynomially bounded.  The standard generalized-free-field construction applied to this
Källén--Lehmann weight gives a local scalar Wightman field.  By definition/equivalent
characterization of a generalized free field, its generating functional is Gaussian and its
connected functions vanish outside order two.

### Exact self-similarity constraint

For `|z|<1`, absolute convergence permits summation atom by atom:

```text
R_(a,b)(z)
  = (1-a) sum_(k>=0) a^k/(1-z b^k).                         (6)
```

Removing the `k=0` atom and reindexing the tail gives

```text
R_(a,b)(z)
  = (1-a)/(1-z) + a R_(a,b)(b z).                           (7)
```

This is a static fixed-measure constraint.  It is not a time evolution or an initial-value law.

### Linear `b`-difference equation

Let `rho f(z)=f(bz)` and put `r(z)=(1-a)/(1-z)`.  Equation `(7)` is

```text
(1-a rho) R = r.                                            (8)
```

The rational function `r` obeys

```text
((1-bz) rho - (1-z)) r = 0.                                (9)
```

Composing `(9)` with `(8)` gives a homogeneous linear `b`-difference equation of order at most
two over `C(z)` for `R`.

### Nonrationality

The series in `(6)` converges locally uniformly away from the distinct points `b^(-k)`.  At
`z=b^(-k)` its `k`th summand has a nonzero simple pole, while all other summands are regular there.
Thus `R` has infinitely many poles.  A rational function has only finitely many poles, so `R` is
not rational.

### Hypertranscendence

The main theorem of Adamczewski--Dreyfus--Hardouin states, in the `q`-difference case, that a
Puiseux Laurent-series solution of a homogeneous linear `q`-difference equation is either a
ramified rational function or hypertranscendental.  Here `q=b` is not a root of unity by `(1)`, and
`R` is an ordinary power series.  If it were ramified rational, invariance of its integer-power
expansion under the finite ramification monodromy would descend it to `C(z)`, contradicting the
infinite-pole argument.  Hence `R` is hypertranscendental for the Euler derivation `z d/dz`.

Over `C(z)`, algebraic differential dependence for `z d/dz` is equivalent to algebraic
differential dependence for `d/dz`: iterates of each derivation are triangular `C(z)`-linear
combinations of iterates of the other.  Therefore `R` is hypertranscendental in the ordinary
sense.

Finally,

```text
G_(a,b)(-1/z) = -z R_(a,b)(z).                              (10)
```

If `G` were differentially algebraic over `C(s)`, rational substitution `s=-1/z` and multiplication
by `-1/z` would make `R` differentially algebraic over `C(z)`.  This contradicts the preceding
paragraph, proving item 4.  `square`

## Anti-theatre and parent-theory verdict

This theorem is a clean physical realization but not candidate new scientific knowledge.

- The measure `(2)` and identity `(7)` are an elementary generalized `q`-logarithm construction.
- Positive Källén--Lehmann superpositions and generalized free fields are classical QFT.
- Gaussian factorization and vanishing higher connected functions are defining parent facts.
- The rational-or-hypertranscendental step is exactly the published difference-Galois theorem.

The useful residue is the no-go: hypertranscendence and interaction cannot be identified.  The
positive successor is the Wick-reduced relative Kolchin profile in the parent card.

## Boundary cases

1. If `a=0`, the measure has one atom and the response is rational.
2. If `b=1`, all atoms coincide and the response is rational.
3. If the geometric spectrum is truncated to finitely many atoms, the response is rational.  The
   HT law is an infinite-spectrum constraint, not a property of any fixed finite cutoff.
4. Compact mass support is not being used as evidence for interaction.  It is used precisely to
   place the example in the generalized-free/Gaussian class.
5. The theorem concerns the physical mass-resolvent/Euclidean propagator.  It does not claim that
   every spacetime restriction or every smeared Wightman distribution is HT in every coordinate.

## Literature gate

- M. Duetsch and K.-H. Rehren, *Generalized free fields and the AdS-CFT correspondence*,
  <https://arxiv.org/abs/math-ph/0209035>.
- B. Adamczewski, T. Dreyfus, and C. Hardouin, *Hypertranscendence and linear difference
  equations*, <https://arxiv.org/abs/1910.01874>.
- W. Zudilin, *On the irrationality of generalized q-logarithm*,
  <https://arxiv.org/abs/1601.02688>.
- E. Koelink and W. Van Assche, *Leonhard Euler and a q-analogue of the logarithm*,
  <https://arxiv.org/abs/0709.1788>.

## Lean boundary

The companion formalization target is the unconditional part not requiring the full published
difference-Galois theorem:

- the explicit moment formula;
- the positive atomic realization;
- the exact power-series self-similarity constraint;
- strict positivity of every finite Hankel determinant;
- escape from every fixed finite spectral width.

The actual HT conclusion must remain paper-proved until the Adamczewski--Dreyfus--Hardouin
`q`-difference dichotomy and the rational/Puiseux descent are formalized in Lean.

## Gates

- [x] exact measure and response stated
- [x] complete paper proof from published parent theorems
- [x] Gaussian/noninteraction no-go explicit
- [x] special functions and RH absent from the statement
- [x] parent-theory reduction recorded
- [ ] published difference-Galois theorem formalized in Lean
- [ ] full HT statement formalized in Lean
