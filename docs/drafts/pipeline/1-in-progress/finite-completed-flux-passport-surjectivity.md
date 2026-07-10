# Finite Completed-Flux Passport Surjectivity

- **ID:** `finite-completed-flux-passport-surjectivity`
- **Stage:** 1-in-progress
- **Type:** THEOREM CANDIDATE / POSITIVE FINITE-PASSPORT CLASSIFICATION
- **Date:** 2026-07-11
- **Scientific status:** `[NOVELTY UNVERIFIED]`
- **Statement:** Every finite graded-real completed-flux passport at every prescribed finite packet
  of symmetry-disjoint off-critical quartets is realized by a real-even, exact-order-one,
  aperiodic entire function with a zero-free real axis; the next coefficient can simultaneously be
  prescribed outside the graded-real locus, so every selected FE/Schwarz partner pair separates at
  exactly the following order.

## Positive theorem under construction

Fix pairwise symmetry-disjoint points

`rho_j = sigma_j + i gamma_j`, `j=1,...,r`,

with `r>=1`, `0<sigma_j<1/2`, and `gamma_j>0`.  Fix `N_j>=0`.  For every `j` and every
`1<=n<=N_j`, prescribe a complex number `a_(j,n)` satisfying the graded-reality law

`a_(j,n) = (-1)^n conj(a_(j,n))`.                              (1)

The target is an entire function `X` such that:

1. `X(1-s)=X(s)` and `X(conj s)=conj(X(s))`;
2. `X` has exact order one and no nonzero period;
3. `X(t)!=0` for every real `t`;
4. every point in the quartet of `rho_j` is a simple zero;
5. for `c_j=1-rho_j` and `d_j=conj(rho_j)`, the residue-filled negative
   logarithmic-flux Taylor coefficients at both centers equal `-1` in degree zero and equal
   `a_(j,n)` in every degree `1<=n<=N_j`;
6. in degree `N_j+1`, the coefficient at `c_j` is

   `eta_j = i^(N_j+2)`,

   while the coefficient at `d_j` is `-eta_j`.

Thus the two partner germs have exactly the prescribed common finite passport and first separate
at the next coefficient.

## Why (1) is the exact passport space

For every FE- and Schwarz-symmetric entire function, the two partner coefficients obey

`coeff(d_j,n) = (-1)^n conj(coeff(c_j,n))`.                     (2)

Consequently a common coefficient is possible exactly when it satisfies (1).  For even `n`, this
is the real line; for odd `n`, it is the purely imaginary line.  The element
`eta_j=i^(N_j+2)` lies in the complementary real line: direct conjugation gives

`(-1)^(N_j+1) conj(eta_j) = -eta_j`.

The theorem therefore aims to prove surjectivity onto the entire finite admissible passport space,
not merely the existence of one flat passport.

## Construction

Use centered coordinates

`z=-i(s-1/2)`, `alpha_j=-i(rho_j-1/2)`,

and let `c'_j=-alpha_j`, `d'_j=-conj(alpha_j)`.  If `b_(j,n)` is the local `z`-coordinate flux
coefficient at `c'_j`, then the corresponding `s`-coordinate coefficient is

`a_(j,n)=(-i)^n b_(j,n)`.

Hence prescribe

`b_(j,n)=i^n a_(j,n)` for 1<=n<=N_j,

and `b_(j,N_j+1)=i^(N_j+1) eta_j`.  Define the finite logarithmic unit jet

`P_j(x) = - sum_(n=1)^(N_j+1) (b_(j,n)/n) x^n`,
`U_j(x) = exp(P_j(x))`.                                        (3)

Then

`-x d/dx log(x U_j(x)) = -1 + sum_(n=1)^(N_j+1) b_(j,n) x^n`.  (4)

Assign the three other local unit jets by the sign and Schwarz involutions.  Let

`A(z)=cosh(z-a_0)cosh(z+a_0)`

be the real-even order-one envelope from
`arbitrary-finite-quartet-passport-realization.md`.  At every orbit point `w`, prescribe the Taylor
class of

`epsilon_w x U_w(x)/A(w+x) mod x^(N_j+3)`,                    (5)

where the nonzero slopes `epsilon_w` are chosen compatibly with the two involutions.  Equivariant
Hermite CRT gives a real-even polynomial `B_0` satisfying (5) at every point, with degree below

`D=4 sum_j (N_j+3)`.

Let

`R(z)=prod_j ((z^2-alpha_j^2)(z^2-conj(alpha_j)^2))^(N_j+3)`.

Then `deg R=D`, `R(iy)>0` on the imaginary axis, and adding `L R` preserves every prescribed jet
through the separating coefficient.  Choosing `L` above the bounded real quotient
`-B_0(iy)/R(iy)` gives `B_L(iy)>0` for every real `y`.  Finally set

`F=A B_L`, `X(s)=F(-i(s-1/2))`.

Equation (5) gives the simple zeros and, by (4), the prescribed passport and exact next-order
separation.  Positivity of `A(iy)B_L(iy)` gives the zero-free real axis.  The envelope zero-lattice
argument from the arbitrary-location realization theorem gives exact order one and aperiodicity.

## Attack

- **Compatibility:** arbitrary complex common coefficients are not realizable; (1) is necessary by
  FE plus Schwarz and is built into the target.
- **Jet depth:** modulus `N_j+2` is insufficient for the separating coefficient.  Modulus
  `N_j+3` makes the induced flux correction start in degree `N_j+2`, preserving degrees through
  `N_j+1`.
- **Axis positivity:** arbitrary passports change `B_0`, but not the argument: real-evenness makes
  `B_0(iy)` real, while the strictly positive repair has strictly larger degree.
- **Full-germ separation:** this is now local and explicit; the coefficient in degree `N_j+1` is
  `eta_j` at one partner and `-eta_j` at the other.  The quasi-period argument is needed only for
  the independent aperiodicity guard.
- **Parent theory:** local logarithmic integration and finite Hermite CRT are classical.  The
  candidate content is the exact surjectivity statement with simultaneous off-line quartets,
  complete admissible passports, global axis positivity, exact order one, and aperiodicity.

## Lean interfaces

- `[FORMALIZATION]` `FiniteHermiteCRT.lean` supplies arbitrary finite Hermite interpolation and
  its sign/Schwarz-equivariant form.
- `[FORMALIZATION]` `SimultaneousFiniteJetFlatness.lean` supplies exact local correction orders and
  strict positivity of the packet polynomial on the imaginary axis.
- `[OPEN FORMAL INTERFACE]` Formalize the polynomial passport map
  `P |-> -1-X P'`, its coefficientwise surjectivity onto all finite passports with constant `-1`,
  and the exponential-unit identity (4).
- `[OPEN FORMAL INTERFACE]` Add a degree-bounded equivariant CRT representative and the global
  positive-domination lemma.

## Gates

- [x] 0 -> 1: exact admissible coefficient space, construction, depth count, and boundary attacks
  are explicit.
- [ ] 1 -> 2: independently audit the coordinate conversion, symmetry-assigned unit jets, and
  degree-bounded CRT step; then present the proof without open prose.
- [ ] 2 -> 3: formalize the passport map, degree control, positivity domination, and envelope.
- [ ] complete the literature and parent-theory audit before any scientific-novelty promotion.
