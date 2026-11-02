# Exact spline quartets with bounded cone coupling

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** SC2; boundary of generic zero-side cone arguments.
- **Scope:** Abstract zero configurations, not the zeros of zeta.

## Exact theorem

For distinct primes `p,q` and `0<d<D`, put `F(z)=(sinh z/z)^8`. There is a
countable family `z_i` such that:

- Every point in the quartets `z_i, conj z_i, -z_i, -conj z_i` is distinct.
- `d<=Re z_i<D`, `Im z_i>=1`, and the real parts approach `D`.
- Every `F(z_i)` is nonzero; `sum_i |F(z_i)|<=2`.
- The base-atom height truncation embeds into `Fin floor(T)`; in particular,
  support is locally finite.
- `L(t)=sum_i F(z_i) exp(t z_i)` converges absolutely for every real `t`.
- `L(m log p+n log q)=0` whenever natural `m,n` are not both zero.

All multiplicities are one. Define the exact quartet kernel

`K(t)=L(t)+conj L(t)+L(-t)+conj L(-t)`.

The identities `F(-z)=F(z)` and `F(conj z)=conj F(z)` identify these four
terms with the prescribed coefficients of the four reflected atoms. The kernel
is real and even, and for all natural `m,n`,

`|K(m log p+n log q)-K(m log p)-K(n log q)+K(0)|<=20`.

Thus exact spline coefficients, integer multiplicities, linear height count,
and prime-clock separation permit bounded cone coupling at unattained positive
width. The prime-side explicit formula is not imposed by this construction.

## Proof

[Finite prescribed-coefficient interpolation](prescribed-spline-coefficients-interpolate-finite-cone-moments.md)
provides distinct heights in `[H,H+C_k]` realizing every target vector of norm
at most `epsilon_k*n_k/H^8` on a finite positive cone window. Along
`N_k=ceil(C_0*8^k)`, the node count, span, required height, and inverse residual
radius are bounded by a common `U*R^k`, uniformly for `d<=delta<=D`.
Baker separation supplies these geometric interpolation costs.

Set

`delta_k=D-(D-d)*2^(-k)`, `A_k=exp(-4^k)`, `H_k=(n_k/A_k)^(1/8)`.

Every geometrically bounded nonnegative threshold `Q_k` satisfies
`A_k*Q_k^8 -> 0`; hence `H_k` eventually exceeds the required height, span,
and cumulative node count. Likewise `2*A_k<=epsilon_k` eventually.
The uniform numerator bound gives each block coefficient norm at most
`B*n_k/H_k^8=B*A_k`. Choose one sufficiently late starting index `k_0` so
these bounds hold and `B*A_(k_0+j)<=2^(-j)`.

The first block has zero target. At each later level `delta_k`, divide the
previous prefix moment by `exp(delta_k*t)` and negate it. Previously sampled
frequencies have zero residual. For a newly sampled frequency,

`t>=N_(k-1)*min(log p,log q)`.

The previous prefix has total coefficient norm at most two and real levels
at most `delta_(k-1)`. Its normalized residual is therefore at most

`2*exp(-(delta_k-delta_(k-1))*t)`.

Choose `C_0>=1` with `((D-d)/2)*min(log p,log q)*C_0>=8`. The displayed
residual is then at most `2*A_k^2`, which is at most
`epsilon_k*n_k/H_k^8`. Exact finite interpolation adds the new block without
changing any earlier height. Recursion and prefix stability give one infinite
height family satisfying every finite cancellation identity.

The coefficient norm is summable, and multiplying by `exp(t z_i)` costs at
most `exp(|t|*D)`. Thus every real-time atomic series converges absolutely.
Each cone time eventually belongs to every subsequent window; all later
blocks individually have zero moment there. Regrouping into finite blocks
therefore gives `L(t)=0` at every positive cone time.

Strictly increasing real levels and distinct heights within each block give
distinct atoms. Nonempty blocks make the width cofinal in `D`. Cumulative
block rank is injective and smaller than the cumulative node count, which is
at most block height. Hence atoms below height `T` inject into `Fin floor(T)`.
The positive quadrant keeps all four reflected copies disjoint.

For `t>=0`, absolute convergence and `Re z_i>=d` give `|L(-t)|<=2`.
At positive cone times, `L(t)=0`, so `|K(t)|<=4`; also `|K(0)|<=8`.
The triangle inequality gives the coupling bound `4+4+4+8=20`.
If either exponent is zero, the coupling is identically zero.

## Formalization

Namespace `GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments`:

- `SplineSparseSupport.lean`:
  `exists_two_prime_prescribed_spline_nullseries`.
- `PrescribedSplineQuartets.lean`:
  `prescribedSplineQuartetKernel_eq`,
  `prescribedSplineQuartetAtom_injective`, and
  `exists_two_prime_prescribed_spline_cone_model`.
- `SplineWeilCoefficient.lean`: `cubicSpline_Wsummand` verifies the convention
  `Wsummand(B,B,1/2+z)=mult(1/2+z)*(sinh z/z)^8` for `z!=0`.

Direct `lake --old env lean` audits pass. Transitive axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. Umbrella imports are wired.

SC2 for actual zeta zeros remains open: this model does not satisfy an asserted
prime-side explicit formula or identify its support with zeta's divisor.
