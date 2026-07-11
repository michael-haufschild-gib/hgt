# The CCM compressed prime shifts faithfully carry the arithmetic complement

- **ID:** `ccm-compressed-prime-shift-arithmetic-complement-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** finite linear independence of distinct translations, unique factorization,
  and the signed-Gamma orbit-charge boundary law
- **Statement:** At every finite aperture, the distinct prime logarithms below the aperture define
  linearly independent compressed weighted shifts. Their operator span is a faithful copy of the
  prime-log space `V_N`; after quotienting the phase directions carried by the finite signed-Gamma
  completion, the resulting operator quotient is canonically the required arithmetic complement
  `A_N=V_N/(V_N intersection D)`.

## Weighted aperture shifts

Let

```text
H=L2(R,e^(-x)dx)
```

and, for `h in R`, define the bilateral weighted translation

```text
(S_h f)(x)=e^h f(x-h).                                      (1)
```

Then

```text
S_h S_k=S_(h+k),
||S_h||=e^(h/2).                                            (2)
```

For `A>0`, let `P_A` be restriction to `[0,A]`, followed by zero extension, and put

```text
T_(A,h)=P_A S_h P_A,       0<=h<A.                          (3)
```

These are exactly the compact-support weighted shifts appearing in
`critical-euler-weighted-shift-accretivity-law.md`.

## Finite-aperture faithfulness

`[PROVED]` If

```text
0<=h_1<...<h_r<A,                                           (4)
```

then

```text
T_(A,h_1),...,T_(A,h_r)                                    (5)
```

are linearly independent over `C`.

### Proof

Choose

```text
0<epsilon<min(A-h_r, h_2-h_1,...,h_r-h_(r-1)).             (6)
```

Take a nonzero `f` supported in `[0,epsilon]`. The vector `T_(A,h_j)f` is nonzero and supported in

```text
[h_j,h_j+epsilon].                                         (7)
```

The intervals in `(7)` are pairwise disjoint. Therefore

```text
sum_j c_j T_(A,h_j)=0                                      (8)
```

implies, after applying `(8)` to `f` and restricting successively to the intervals `(7)`, that
every `c_j=0`. This proves the theorem.

The endpoint restriction `h_r<A` is exact: compression of the shift by `A` has only a measure-zero
range. Cofinal cutoffs may always be chosen with `log N<A`, so no arithmetic direction is lost.

There is also a pointed cyclic strengthening before aperture compression. If `0!=f in H` has
compact support and `h_1,...,h_r` are distinct, then

```text
S_(h_1)f,...,S_(h_r)f                                    (8a)
```

are linearly independent. Indeed, compact support makes `f` integrable. Fourier transformation of
a relation among `(8a)` gives

```text
hat(f)(t) sum_j c_j e^(h_j)e^(-i h_j t)=0.                (8b)
```

The Fourier transform of `f` is not identically zero, so it is nonzero on a real interval. The
exponential polynomial in `(8b)` vanishes on that interval and hence identically; distinct
frequencies force every `c_j=0`.

Thus the arithmetic directions do not collapse even after evaluation on one nonzero compactly
supported cyclic vector. A hypothetical screw-kernel zero mode must therefore be a genuine
prime--archimedean cross-channel incidence after aperture restriction, not an internal linear
aliasing of distinct prime translations.

## Prime-log operator carrier

Fix `N<e^A` and put

```text
V_N=span_Q{log p:p<=N}.                                    (9)
```

Unique factorization gives

```text
dim_Q V_N=pi(N).                                           (10)
```

Define the `Q`-linear map

```text
J_(A,N):V_N -> span_C{T_(A,log p):p<=N}
```

on the prime-log basis by

```text
J_(A,N)(log p)=T_(A,log p).                               (11)
```

The finite-aperture theorem makes `(11)` injective. Thus the exact CCM weighted-shift operator has
not merely `pi(N)` formal labels but a faithful `pi(N)`-dimensional arithmetic operator carrier.
Prime powers are represented compatibly by the semigroup law in `(2)` before compression, and by
the same law after compression whenever the total shift remains below `A`.

## Exact Gamma-complement quotient

Let

```text
D_N=V_N intersection D,                                   (12)
```

where `D` is the rational phase space transported by a proposed finite signed positive-scale Gamma
completion. Put

```text
A_N=V_N/D_N.                                              (13)
```

Because `J_(A,N)` is injective, it induces a canonical isomorphism

```text
A_N
  ~= J_(A,N)(V_N)/J_(A,N)(D_N).                          (14)
```

The signed-Gamma orbit-charge theorem supplies the finite bound

```text
dim_Q D_N<=delta_beta+2m(n+1),
delta_beta in {0,1}.                                      (15)
```

Consequently

```text
dim_Q A_N
 >=pi(N)-delta_beta-2m(n+1).                              (16)
```

Equations `(14)`--`(16)` turn the Gamma obstruction into a positive carrier theorem: the missing
prime-character directions already live as an explicit quotient of the CCM compressed-shift
operator span.

## Exact arithmetic Krein block

The same carrier has a canonical indefinite factorization. On a compact-support aperture core let

```text
Q_A={n>=2:log n<A},
a_n=Lambda(n)/n>0,                                        (16a)
```

and define, for any `c>0`,

```text
(V_(+,A,c)f)_n=sqrt(a_n)(T_(A,log n)f+c f),
(V_(-,A,c)f)_n=sqrt(a_n)(T_(A,log n)f-c f)               (16b)
```

as vectors in the finite Hilbert direct sum indexed by `Q_A`. The parallelogram identity gives

```text
1/(2c)(||V_(+,A,c)f||^2-||V_(-,A,c)f||^2)
 =2 Re sum_(n in Q_A) a_n<T_(A,log n)f,f>.                (16c)
```

Hence the completed finite-aperture Hermitian form is exactly

```text
2 Re<T_A f,f>
 =2 Re<B_A f,f>
  +1/(2c)||V_(-,A,c)f||^2
  -1/(2c)||V_(+,A,c)f||^2.                               (16d)
```

This is a source-defined Krein decomposition: the prime coefficients, prime-power shifts, and
critical norms occur explicitly, and no Xi zero is used. After any positive/negative spectral
factorization of the Gamma-only form `2 Re<B_A ., .>`, positivity of `(16d)` is equivalent by the
Douglas lemma to a contraction from the combined positive feature map onto the combined negative
feature map. The negative map contains `V_(+,A,c)` and therefore contains the faithful quotient
`A_N` for every `N<e^A`.

Thus the positive object forced by the completed source is not a scalar inequality but a cofinal
family of contractions

```text
C_A : positive Gamma-prime features -> negative Gamma-prime features  (16e)
```

whose restriction remains faithful on the arithmetic quotient `(14)`. Constructing `(16e)` from
the Euler--Gamma incidence proves finite-aperture nonnegative birth; constructing it for every
aperture proves RH. Equation `(16d)` identifies the exact carrier of that construction without
assuming the desired positivity.

## Consequence for a successful CCM construction

Any factorization or index transport of the completed weighted-shift form that is faithful to the
actual finite-aperture operator must induce an injective map on the quotient `(14)`. By rank-nullity,
its arithmetic state space at cutoff `N` therefore has rational dimension at least

```text
dim_Q A_N.                                                (17)
```

This applies to a positive Gram factor, a de Branges Hamiltonian, a determinant state, a Weil-test
completion, or an aperture-index transport. The theorem does not say that large carrier dimension
implies positivity. It says positively what the CCM construction must preserve while proving the
no-negative-birth law:

```text
faithful compressed prime shifts
  + finite signed-Gamma phase carrier
  + the quotient A_N
  + index-preserving cofinal transport.                   (18)
```

The current weighted-shift realization clears the carrier-existence part of `(18)`. The remaining
RH theorem is a positive factorization of the Hermitian completed form that remains faithful on
this quotient.

## Novelty and significance verdict

Linear independence of finitely many compressed translations is elementary, and `(14)` is the
first isomorphism theorem. The result is a route bridge, not new scientific knowledge. Its value is
that the Gamma no-go is replaced by the exact operator quotient a successful CCM proof must carry.

## References

- `critical-euler-weighted-shift-accretivity-law.md`.
- `signed-archimedean-gamma-orbit-charge-phase-law.md`.
- `incommensurable-gamma-orbit-free-quasianalyticity.md`.

## Lean decision

The formal tree does not yet contain the weighted `L2` translation representation or the analytic
completed operator. Formalizing only finite linear independence would not certify the CCM source
factorization, so no Lean file is added at this stage.

## Gates

- [x] compressed weighted shifts proved linearly independent
- [x] prime translates proved independent on every nonzero compactly supported cyclic vector
- [x] prime-log space embedded faithfully in the operator span
- [x] signed-Gamma phase quotient identified exactly
- [x] arithmetic complement lower bound proved
- [x] exact prime Krein defect block constructed
- [ ] construct a positive factorization faithful on the quotient `A_N`
- [ ] preserve the aperture Morse index cofinally
- [ ] prove RH
