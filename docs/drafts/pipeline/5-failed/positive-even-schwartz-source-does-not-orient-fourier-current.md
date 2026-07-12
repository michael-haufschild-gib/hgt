# Positive even Schwartz sources do not orient Fourier logarithmic current

- **ID:** `positive-even-schwartz-source-does-not-orient-fourier-current`
- **Stage:** 5-failed
- **Type:** COUNTEREXAMPLE / ROUTE RETIREMENT
- **Scientific status:** `[PROVED COUNTEREXAMPLE] [SEARCH-LEVEL BRIDGE]`
- **Failed statement:** Positivity, evenness, Schwartz decay, and the resulting full raw-moment
  Hankel positivity of a source force nonpositive upper-half-plane logarithmic current for its
  Fourier transform.

## Counterexample

Fix `0<a<1/2` and let

```text
mu = delta_0 + a delta_1 + a delta_(-1).
```

Its Fourier transform is

```text
F(z) = 1 + 2a cos z.                                         (1)
```

Choose `y>0` with

```text
cosh y = 1/(2a).
```

Then

```text
F(pi+i y) = 1 - 2a cosh y = 0.                              (2)
```

The zero is simple because

```text
F'(pi+i y) = 2a i sinh y != 0.                               (3)
```

Now convolve `mu` with the centered Gaussian density

```text
g_epsilon(x) = c_epsilon exp(-x^2/(2 epsilon)),
```

where `epsilon>0`.  The resulting density

```text
w_epsilon(x) = g_epsilon(x)
             + a g_epsilon(x-1)
             + a g_epsilon(x+1)                              (4)
```

is strictly positive, even, and Schwartz.  Its Fourier transform is

```text
W_epsilon(z) = exp(-epsilon z^2/2) (1+2a cos z).              (5)
```

The Gaussian factor never vanishes, so `(2)` is still a simple nonreal zero of `W_epsilon`.
Approaching it from below in the centered coordinate makes

```text
Im(W_epsilon'/W_epsilon)
```

grow at a positive linear reciprocal-distance rate.  Thus the oriented current

```text
Im(W_epsilon'(z) conjugate(W_epsilon(z)))
```

is positive on points immediately below that zero.

## Strict log-concavity does not repair the route

The same family may be chosen strictly log-concave.  Factor `(4)` as

```text
w_epsilon(x) = g_epsilon(x) (1+b cosh(x/epsilon)),
b = 2a exp(-1/(2 epsilon)).                                  (6)
```

Writing `u=x/epsilon`, direct differentiation gives

```text
(log w_epsilon)''(x)
  = -1/epsilon
    + (1/epsilon^2)
      (b cosh u+b^2)/(1+b cosh u)^2.                         (7)
```

The last fraction is strictly below `1`, because

```text
(1+b cosh u)^2-(b cosh u+b^2)
  = 1+b cosh u+b^2 sinh(u)^2 > 0.                            (8)
```

Hence, for every `epsilon>1`,

```text
(log w_epsilon)''(x) < -(epsilon-1)/epsilon^2 < 0             (9)
```

uniformly in `x`.  Even uniform strong log-concavity, combined with strict positivity, evenness,
Schwartz decay, and all raw moment inequalities, does not orient the Fourier logarithmic current.

## Moment consequence

Every raw moment Hankel matrix of the positive density `(4)` is positive semidefinite.  Therefore
all of the following are insufficient to orient the Fourier logarithmic current:

1. positivity of every source weight;
2. evenness and Schwarz reality;
3. Schwartz decay and entire Fourier continuation;
4. positivity of every finite raw-moment Hankel matrix;
5. finite Taylor coefficients represented as moments of one positive source.
6. a uniform negative curvature floor for the logarithm of that source.

The counterexample does not address an inequality using the exact theta-cusp atom weights,
reflection formula, or a genuinely theta-specific global constraint.

## Retirement verdict

The Xi Taylor producer cannot be proved from qualitative positive-kernel or raw-moment structure.
It must use an exact property distinguishing `thetaCuspFullSource` from `(4)`.  Calling the source
positive, Schwartz, even, or moment-positive is not such a property.

## Gates

- [x] explicit positive even Schwartz density constructed
- [x] explicit simple nonreal Fourier zero proved
- [x] raw-moment Hankel positivity shown irrelevant
- [x] qualitative positive-source route retired
