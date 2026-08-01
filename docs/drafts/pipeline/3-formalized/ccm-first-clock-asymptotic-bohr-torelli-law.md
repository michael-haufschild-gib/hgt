# CCM first-clock asymptotic Bohr Torelli law

- **ID:** `ccm-first-clock-asymptotic-bohr-torelli-law`
- **Stage:** 3-formalized
- **Labels:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Source:** `CCMFirstClockAsymptoticBohrLaw`, full Bohr uniqueness/mean corpus, and
  multiplicity-exact `XiZeroCopy` divisor carrier.

## Exact claim

Put

```text
F(L) = L * ccmPublishedSourceSineCoefficient (L/2) (2*pi/L).
```

Call a continuous real Bohr almost-periodic function `P` an asymptotic compact model of `F` when
`F(L)-P(L) -> 0` as `L -> +infinity`.

1. `F` has an asymptotic compact model if and only if RH.
2. Such a model is unique.
3. On this fibre the unique model is

```text
P(L) = 2 * sum_q (1 - cos(omega_q L)) / omega_q^2,
omega_q = Re xiSpectralPoint(q),
```

where `q` runs through multiplicity copies.
4. For every nonzero real `lambda`, its complex Bohr coefficient is

```text
c_P(lambda)
  = - sum_q [ |omega_q| = |lambda| ] / omega_q^2.
```

Consequently

```text
-lambda^2 * c_P(lambda)
  = #{q : |omega_q| = |lambda|}.
```

The nonzero Bohr spectrum with these integral masses reconstructs the full real symmetric Xi
divisor, including multiplicity, and hence its normalized even canonical product.

## Dependency-closed paper proof

The existence equivalence and the explicit `O(L^-2)` comparison with the displayed screw series
are already proved in `ccm-first-clock-asymptotic-bohr-law.md`.

For uniqueness, let `P` and `Q` be two compact models. Their difference `D=P-Q` is continuous and
Bohr almost periodic, and `D(L)->0` at `+infinity`. If `D(t0)` were nonzero, choose
`epsilon < ||D(t0)||/3`. Relative density supplies an `epsilon`-almost-period `tau` in every
sufficiently far interval. Choose such a positive `tau` with `t0+tau` beyond the decay threshold.
Then

```text
||D(t0)|| <= ||D(t0)-D(t0+tau)|| + ||D(t0+tau)|| < 2*epsilon,
```

a contradiction. Thus `D=0`. Comparing any compact model with the explicit RH-side screw series
gives part 3.

For the coefficient formula, first take a finite set of indices. Euler's cosine identity and
orthogonality of Bohr characters give, for `lambda != 0`,

```text
c(lambda; sum_i a_i (1-cos(omega_i L)))
  = -(1/2) sum_i [omega_i=lambda] a_i
    -(1/2) sum_i [omega_i=-lambda] a_i.
```

For a nonnegative summable family `a`, finite subsums converge uniformly on the whole line because
`0 <= 1-cos(theta) <= 2`. The Bohr mean, and hence each Bohr coefficient, is 1-Lipschitz in uniform
norm. Passing through the directed finite-subset limit proves the same formula for the infinite
series. For `a_q=omega_q^-2`, RH makes every `omega_q` real and nonzero and makes the weight family
summable. Multiplication by two combines the two fibres into
`|omega_q|=|lambda|`. That fibre is finite: under RH it is contained in the union of the two finite
complex spectral-point fibres at `lambda` and `-lambda`. Every term in it equals `lambda^-2`, so
multiplying by `-lambda^2` gives its exact cardinality. Functional-equation symmetry restores both
signs from the absolute ordinate; `XiZeroCopy` already counts analytic multiplicity. The normalized
even genus-one canonical product is therefore fixed.

## Hostile audit

- This does not prove RH: existence of the compact model is exactly RH-equivalent.
- Generic `AP intersect C_0 = {0}` and coefficient extraction from an absolutely summable
  trigonometric series are classical; neither is claimed as novelty.
- Suzuki's divisor series already displays the zero frequencies. The candidate new residue is the
  source-specific statement that the **literal first CCM prime--Gamma clock**, without a supplied
  divisor in its hypothesis, has one and only one compact asymptotic germ and that this germ is a
  complete multiplicity-exact spectral invariant.
- The formula retains collisions and multiplicity and uses neither simplicity nor linear
  independence of ordinates.
- Zero frequency is excluded by the proved Xi spectral gap; no division by a possible zero
  ordinate occurs.

## Formalization gate

- [x] Generic `AP intersection C_0 = {0}` theorem.
- [x] Generic summable-screw Bohr coefficient theorem.
- [x] Xi fibre finiteness and quantization specialization.
- [x] Unique first-clock compact model and divisor reconstruction capstone.
- [x] Targeted `lake env lean`, axiom audit, final module build, and formal lint.
