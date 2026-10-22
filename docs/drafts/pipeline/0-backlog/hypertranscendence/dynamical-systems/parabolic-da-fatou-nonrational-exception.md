# Parabolic DA Fatou coordinates are not confined to Mobius maps

- **ID:** parabolic-da-fatou-nonrational-exception
- **Stage:** 0-backlog
- **Type:** GATEKEEPER THEOREM / COUNTERMODEL
- **Source:** Haiku after Turing parabolic trichotomy discussion, 2026-06-24
- **Priority:** HIGH for scoping any Fatou-coordinate HT conjecture

## Statement

The slogan "parabolic Fatou coordinate is DA only for Mobius/trivial degree-one maps" is false in the local
analytic-germ category.

There exists a non-rational algebraic parabolic germ `f` at `0` whose Fatou coordinate is rational, hence DA.
Thus any parabolic HT theorem must specify a finite-base/global category. It cannot classify DA exceptions by
Mobius maps alone.

## Promptability audit

No computation is used. The construction is the stripped normal form:

> Choose a DA Fatou coordinate `Phi` with a pole at the parabolic point, and define the germ by
> `Phi(f(z))=Phi(z)+1`.

Once stated this way, the example is direct. Its value is not depth; it blocks an overnarrow exceptional-locus
claim.

## Theorem `[PROVED HERE]`

Let

```text
Phi(z) = -1/z + z.
```

Define `f` near `0` by the branch satisfying

```text
Phi(f(z)) = Phi(z) + 1,    f(z) -> 0 as z -> 0.
```

Then:

1. `f` is an algebraic analytic germ at `0`;
2. `f(0)=0` and `f'(0)=1`, so `f` is parabolic;
3. `Phi` is a rational Fatou coordinate for `f`, hence DA;
4. `f` is not rational, and therefore not Mobius.

## Proof

Writing `w=f(z)`, the defining equation is

```text
-1/w + w = -1/z + z + 1.
```

Equivalently, with

```text
A(z)= -1/z + z + 1 = (z^2+z-1)/z,
```

the branch `w` satisfies

```text
w^2 - A(z) w - 1 = 0.
```

Thus `f` is algebraic over `C(z)`. Since `A(z) ~ -1/z` as `z -> 0`, one root tends to `0` and the other tends to
`infinity`; the root tending to `0` gives a single-valued analytic germ near `0`. Expanding the equation gives
`f(z)=z+z^2+O(z^3)`, hence `f(0)=0` and `f'(0)=1`, so the fixed point is parabolic.

The Fatou equation is true by construction:

```text
Phi(f(z)) = Phi(z)+1.
```

Since `Phi` is rational on a punctured neighborhood, it is DA.

It remains to show that `f` is not rational. A root of the quadratic is rational over `C(z)` iff the
discriminant

```text
Delta(z)=A(z)^2+4
        = ((z^2+z-1)^2 + 4z^2)/z^2
```

is a square in `C(z)`. This would require the polynomial

```text
N(z)=(z^2+z-1)^2+4z^2
    = z^4 + 2z^3 + 3z^2 - 2z + 1
```

to be a square in `C[z]`. It is not: if `N=(z^2+az+b)^2`, then `b^2=1` and `2a=2`, so `a=1`; the coefficient of
`z` would then be `2ab`, equal to `2` for `b=1` and `-2` for `b=-1`, but the constant and `z^2` coefficients
cannot both match in the `b=-1` case. Hence `N` is not a square, the algebraic branch is not rational, and `f`
is not Mobius. ∎

## Consequence

For rational maps of degree at least two, Becker--Bergweiler/Fernandes already proves that Abel/Fatou
coordinates are always HT. For local analytic or algebraic parabolic germs, the situation is different:
non-rational algebraic germs can have DA Fatou coordinates.

Therefore a fresh parabolic theorem cannot be stated as:

```text
Fatou coordinate DA iff the germ is Mobius.
```

The plausible boundary is instead something like:

```text
Fatou coordinate DA iff the germ is DA-conjugate, in an appropriate sectorial/global sense, to translation by
a DA Fatou coordinate with trivial analytic modulus.
```

That is a different and harder statement. The present card only supplies the countermodel that forces the
stronger scoping.

## Novelty and significance

This is an elementary local construction, so it is not a deep theorem. Its significance is diagnostic: it stops
the rational-map trichotomy from being extrapolated into the full local parabolic category with the wrong
exceptional set.

Grade: BRIDGE / gatekeeper for the parabolic-Fatou HT lane.

## Gates

- [x] 0 -> 1 in-progress: explicit countermodel and proof written.
- [ ] 1 -> 2 fully-proven: team audits branch analyticity and non-rationality argument.
- [ ] 2 -> 3 formalized: optional algebraic-curve/local-branch lemma.
- [ ] 3 -> 4 publication-ready: include as a warning in any parabolic trichotomy note.

## Log

- 2026-06-24 - Created by Haiku to correct the overnarrow "Mobius only" exceptional-locus language in the
  parabolic/Fatou discussion.

## 2026-06-24 strengthening -- a one-parameter algebraic non-rational DA-Fatou family

The countermodel is not isolated.

### Theorem `[PROVED HERE]`

For every `c in C*`, set

```text
Phi_c(z) = -1/z + c z.
```

Let `f_c` be the local branch at `0` determined by

```text
Phi_c(f_c(z)) = Phi_c(z) + 1,    f_c(z) -> 0 as z -> 0.
```

Then `f_c` is an algebraic analytic parabolic germ at `0`, `Phi_c` is a rational/DA Fatou coordinate for `f_c`,
and `f_c` is not rational.

### Proof

Writing `w=f_c(z)` and

```text
A_c(z)=Phi_c(z)+1=(-1/z)+c z+1=(c z^2+z-1)/z,
```

the equation `Phi_c(w)=Phi_c(z)+1` becomes

```text
c w^2 - A_c(z) w - 1 = 0.
```

Since `A_c(z) ~ -1/z`, one algebraic branch tends to `0` as `z -> 0`; this branch is analytic and satisfies

```text
f_c(z)=z+z^2+O(z^3),
```

so `f_c(0)=0` and `f_c'(0)=1`. The Fatou equation is built into the definition, and `Phi_c` is rational.

It remains to show that the algebraic branch is not rational. If `f_c` were rational, the discriminant

```text
Delta_c(z)=A_c(z)^2+4c
```

would be a square in `C(z)`. Equivalently,

```text
N_c(z)=(c z^2+z-1)^2+4c z^2
```

would be a square in `C[z]`. Suppose `N_c=(d z^2+a z+b)^2`. From the leading and constant coefficients,
`d=±c` and `b=±1`. The `z^3` coefficient of `N_c` is `2c`, so `d a=c`, hence `a=1` if `d=c` and `a=-1` if
`d=-c`. The `z` coefficient is `-2`, forcing respectively `b=-1` in the first case and `b=1` in the second.
In both cases the square's `z^2` coefficient is `1-2c`, while `N_c` has `z^2` coefficient `1+2c`. Since
`c != 0`, this is impossible. Thus `N_c` is not a square and `f_c` is not rational. ∎

### Consequence

There is a punctured one-parameter algebraic family of non-rational local parabolic germs with rational Fatou
coordinates. Therefore local non-rationality, algebraicity of the germ, and non-Mobius behavior are all too weak
to force Fatou-coordinate HT.

A viable parabolic HT theorem must use a stronger global finite-base condition, such as rational-map degree at
least two, or a genuinely analytic modulus condition that excludes these algebraic pullback-by-coordinate models.

## 2026-06-24 finite-jet strengthening cross-link

The one-parameter family above is strengthened in
`../2-fully-proven/parabolic-zero-residue-finite-jet-da-fatou-realization.md`.

There, every finite jet

```text
+z+z^2+z^3+a_4 z^4+...+a_N z^N
```

in the normalized zero-residue simple parabolic class is realized by an algebraic local parabolic germ whose
Fatou coordinate is rational. The proof is triangular: for `h=z+z^2+...`, the operator
`P -> P(h)-P(z)` sends `z^k` to `k z^(k+1)+higher`, so the polynomial part of the Fatou coordinate cancels any
finite residual after the forced zero-residue term.

Consequence: finite local parabolic jet data cannot support Fatou-coordinate HT. The live invariant must be
global, sectorial, or modulus-level.
