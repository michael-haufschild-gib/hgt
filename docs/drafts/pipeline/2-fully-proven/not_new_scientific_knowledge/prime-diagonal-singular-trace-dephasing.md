# Prime-diagonal singular traces: Dixmier nullity and log-log dephasing

- **ID:** `prime-diagonal-singular-trace-dephasing`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM / non-Fock operator-ideal obstruction
- **Scientific status:** `[PROVED ON PAPER; NOVELTY UNVERIFIED]`
- **Source:** the prime Hilbert--Schmidt diagonal and functional-equation reflection
- **Statement:** The positive reflected product of prime diagonals should have zero ordinary
  Dixmier trace but a nonzero log-log-normalized residue independent of the spectral parameter.
  Keeping the nonadjoint phase should instead annihilate every nonzero height.  Thus neither
  singular-trace choice can see the zeta divisor.

## Operator

On `ell^2(Primes)` define

```text
D_s e_p=p^(-s)e_p,
tau(s)=1-conj(s).
```

For `Re(s)>1/2`, `D_s` is Hilbert--Schmidt.  Its two reflected quadratic products are

```text
D_s D_(tau(s))^* e_p=p^(-1)e_p,                       (1)

D_s D_(tau(s)) e_p=p^(-1-2 i Im(s))e_p.               (2)
```

The first is positive and loses all phase.  The second retains height but is not positive.

## Theorem

Let `p_n` be the `n`th prime and let `A=diag(1/p_n)`.

`[PROVED]` The following four statements hold.

1. `A` belongs to the separable part of both the weak trace ideal and the ordinary Dixmier ideal:

   ```text
   n mu_n(A)=n/p_n -> 0.
   ```

2. Its ordinary Dixmier means vanish:

   ```text
   (1/log N) sum_(n<=N) mu_n(A) -> 0.
   ```

3. The sharp prime normalization is instead double logarithmic:

   ```text
   (1/log log N) sum_(n<=N) mu_n(A) -> 1.
   ```

4. For every nonzero real `t`, the prime-ordered series

   ```text
   sum_p p^(-1-2it)
   ```

   converges, so its log-log-normalized spectral trace is zero.

Consequently the positive log-log singular residue of `(1)` is the constant `1` at every point of
the critical strip.  The canonical prime-basis log-log spectral mean of `(2)` is `0` at every
nonzero height.

### Proof of weak-ideal membership and the two normalizations

The prime number theorem in inverse form gives

```text
p_n ~ n log n.                                         (3)
```

Therefore

```text
n mu_n(A)=n/p_n ~ 1/log n -> 0.                        (4)
```

This places `A` in the order-continuous/separable part of the weak Schatten ideal
`L_(1,infinity)`.

Mertens' prime-harmonic theorem gives

```text
sum_(p<=X) 1/p=log log X+B_1+o(1).                    (5)
```

Putting `X=p_N` and using `(3)`,

```text
log log p_N=log log N+o(1),                            (6)
```

so

```text
S_N:=sum_(n<=N)mu_n(A)=log log N+B_1+o(1).             (7)
```

It follows immediately that

```text
S_N/log N -> 0,                                        (8)
S_N/log log N -> 1.                                    (9)
```

Equation `(8)` proves that `A` belongs to the order-continuous subideal
`M_(1,infinity)^0` of the ordinary Dixmier ideal.  Every ordinary Dixmier and Connes--Dixmier trace
therefore vanishes on `A`.

For a concave gauge equivalent at infinity to

```text
Psi(N)=log log N,
```

equation `(9)` places `A` in the Marcinkiewicz ideal `M_Psi` and makes it measurable for every
compatible generalized-limit trace.  With the normalization `Psi(N)~log log N`, all such positive
traces have value `1`.

### Proof of phase dephasing

Let `lambda=2t!=0`.  Ordered by increasing primes, partial summation writes

```text
sum_(p<=X) p^(-1-i lambda)
  = integral_(2-)^X y^(-1-i lambda) d pi(y).            (10)
```

The de la Vallee Poussin prime-number theorem

```text
pi(y)=Li(y)+O(y exp(-c sqrt(log y)))                   (11)
```

splits `(10)` into a main term and an absolutely convergent error.  After `u=log y`, the main term
is

```text
integral_(log 2)^(log X) exp(-i lambda u)/u du,         (12)
```

which converges by Dirichlet's test.  Integration by parts in the error leaves a majorant

```text
exp(-c sqrt(log y)) dy/y,
```

which is integrable.  Thus `(10)` has a finite limit.

Consequently

```text
(1/log log N) sum_(n<=N) p_n^(-1-2it) -> 0             (13)
```

for `t!=0`.  Equation `(13)` is the canonical arithmetic-basis spectral mean.  It also computes any
singular trace for which a Lidskii formula is known on this normal diagonal, but no blanket Lidskii
claim for every trace on `M_Psi` is needed here.

## Reflection dichotomy

At the self-dual point `Re(s)=1/2`, `(1)` is the positive square `D_s D_s^*`.  Off the line it is
still the reflected positive pairing.  In every case it is exactly `A`, so both its zero ordinary
Dixmier trace and its nonzero log-log trace are parameter-blind.

The nonadjoint pairing `(2)` retains the vertical phase but `(13)` kills every nonzero height.  Thus
singular-trace regularization has only two canonical outcomes:

```text
positive reflected pairing:  universal value 1,
phase-retaining pairing:      value 0 for every t!=0.  (14)
```

Neither outcome distinguishes a zeta zero from a nonzero point at the same height.

## Kill test

If these statements hold, singular traces do not supply an RH mechanism:

- positivity forces adjunction and produces a universal parameter-blind residue;
- retaining phase dephases every nonzero height, including every nontrivial zeta zero;
- changing from `log N` to `log log N` changes the effective spectral dimension but not this
  dichotomy.

The only remaining phase-sensitive linear trace is the unnormalized prime sum `sum_p p^(-s)`,
namely the prime zeta function.  On `Re(s)>1/2`, write

```text
H(s)=sum_(k>=2) P(k s)/k.
```

The tail is holomorphic there and

```text
log zeta(s)=P(s)+H(s).                                 (15)
```

The Hilbert--Carleman determinant is the zero-free factor

```text
det_2(I-D_s)=exp(-H(s)).                               (16)
```

Hence all zeta zeros in the Hilbert--Schmidt half-plane occur as logarithmic monodromy of the
missing first-order trace `P(s)`, not as zeros of the canonical determinant.  Restoring `P(s)`
restores the divisor itself; it does not supply a pre-divisor localization law.

## Parent and novelty boundary

The operator-ideal ingredients are standard: Dixmier traces on `M_(1,infinity)`, generalized traces
on Marcinkiewicz ideals, and Lidskii formulae for suitable normal operators.  The arithmetic inputs
are the prime number theorem, Mertens' theorem, and conditional convergence of the prime zeta
series on `Re(s)=1` away from `s=1`.

Exact searches did not locate the assembled dichotomy `(14)` for the functional-equation-reflected
prime diagonal.  Nevertheless `(3)`--`(13)` are direct consequences of those parent theorems.  The
result is scientifically useful as a route obstruction but remains `[NOVELTY UNVERIFIED]` pending a
broader audit; it must be downgraded if the exact prime-diagonal example is already standard.

### Parent references

- S. Lord, A. Sedaev, and F. Sukochev, *Dixmier traces as singular symmetric functionals and
  applications to measurable operators*, J. Functional Analysis 224 (2005),
  <https://arxiv.org/abs/math/0501131>.
- M. Goffeng and A. Usachev, *Dixmier traces and residues on weak operator ideals*, J. Math.
  Analysis and Applications 488 (2020), <https://arxiv.org/abs/1710.08260>.
- C.-E. Froberg, *On the prime zeta function*, BIT 8 (1968), 187--202.

## Gates

- [x] prove the weak-ideal and ordinary-Dixmier nullity claims
- [x] prove log-log measurability and value `1`
- [x] prove nonzero-height phase convergence
- [x] compare with Marcinkiewicz ideals and higher-order singular traces
- [ ] formalize only a substantive prime-asymptotic core available without axioms
- [ ] independent operator-ideal audit of the chosen `M_Psi` normalization
