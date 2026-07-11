# Finite Completed-Flux Passport Surjectivity

- **ID:** `finite-completed-flux-passport-surjectivity`
- **Stage:** 2-fully-proven / needs independent audit
- **Type:** THEOREM (paper) / POSITIVE FINITE-PASSPORT CLASSIFICATION
- **Date:** 2026-07-11
- **Scientific status:** `[NOVELTY UNVERIFIED]`.  The local logarithmic integration and Hermite
  interpolation are classical; the exact global surjectivity statement has a complete proof here
  but has not passed the parent-theory and literature gates.
- **Statement:** Every finite graded-real completed-flux passport at every prescribed finite packet
  of symmetry-disjoint off-critical quartets is realized by a real-even, exact-order-one,
  aperiodic entire function with a zero-free real axis; the next coefficient can simultaneously be
  prescribed arbitrarily outside the graded-real locus, so every selected FE/Schwarz partner pair
  separates at exactly the following order.

## Positive theorem

Fix pairwise symmetry-disjoint points

`rho_j = sigma_j + i gamma_j`, `j=1,...,r`,

with `r>=1`, `0<sigma_j<1/2`, and `gamma_j>0`.  Fix `N_j>=0`.  For every `j` and every
`1<=n<=N_j`, prescribe a complex number `a_(j,n)` satisfying the graded-reality law

`a_(j,n) = (-1)^n conj(a_(j,n))`.                              (1)

Also prescribe an arbitrary transverse coefficient `eta_j` satisfying

`eta_j != (-1)^(N_j+1) conj(eta_j)`.                            (2)

There exists an entire function `X` such that:

1. `X(1-s)=X(s)` and `X(conj s)=conj(X(s))`;
2. `X` has exact order one and no nonzero period;
3. `X(t)!=0` for every real `t`;
4. every point in the quartet of `rho_j` is a simple zero;
5. for `c_j=1-rho_j` and `d_j=conj(rho_j)`, the residue-filled negative
   logarithmic-flux Taylor coefficients at both centers equal `-1` in degree zero and equal
   `a_(j,n)` in every degree `1<=n<=N_j`;
6. in degree `N_j+1`, the coefficient at `c_j` is `eta_j`, while the coefficient at `d_j` is

   `(-1)^(N_j+1) conj(eta_j)`.

Thus the two partner germs have exactly the prescribed common finite passport and first separate
at the next coefficient.

## Why (1) is the exact passport space

For every FE- and Schwarz-symmetric entire function, the two partner coefficients obey

`coeff(d_j,n) = (-1)^n conj(coeff(c_j,n))`.                     (3)

Consequently a common coefficient is possible exactly when it satisfies (1).  For even `n`, this
is the real line; for odd `n`, it is the purely imaginary line.  Condition (2) selects exactly the
complement of this fixed line.  This complement is nonempty in every degree: the canonical choice
`eta_j=i^(N_j+2)` satisfies

`(-1)^(N_j+1) conj(eta_j) = -eta_j`.

The theorem proves surjectivity onto the entire finite admissible passport space, strictly
strengthening the realization of one flat passport.

## Proof

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

Assign the three other local unit jets by the sign and Schwarz involutions:

`epsilon_(-w)=-epsilon_w`, `U_(-w)(x)=U_w(-x)`,

`epsilon_(conj w)=conj(epsilon_w)`,
`U_(conj w)(x)=conj(U_w(conj x))`.

Choose the initial slopes real and nonzero.  These rules are exactly the local Taylor rules for a
real-even function.  Let

`A(z)=cosh(z-a_0)cosh(z+a_0)`

be the real-even order-one envelope from
`arbitrary-finite-quartet-passport-realization.md`.  At every orbit point `w`, prescribe the Taylor
class of

`epsilon_w x U_w(x)/A(w+x) mod x^(N_j+3)`,                    (5)

where the nonzero slopes `epsilon_w` obey the displayed rules.  The target classes are therefore
fixed by both involutions.  Equivariant Hermite CRT gives a real-even, Schwarz-real polynomial
`B_0` satisfying (5) at every point, with degree below

`D=4 sum_j (N_j+3)`.

Let

`R(z)=prod_j ((z^2-alpha_j^2)(z^2-conj(alpha_j)^2))^(N_j+3)`.

Then `deg R=D`, `R(iy)>0` on the imaginary axis, and adding `L R` preserves every prescribed jet
through the separating coefficient.  Choosing `L` above the bounded real quotient
`-B_0(iy)/R(iy)` gives `B_L(iy)>0` for every real `y`.  Finally set

`F=A B_L`, `X(s)=F(-i(s-1/2))`.

Equation (5) gives

`F(w+x)=epsilon_w x U_w(x)+O(x^(N_j+3))`.

After division by the simple factor `x`, the unit error is `O(x^(N_j+2))`; logarithmic
differentiation and multiplication by `x` preserve all flux coefficients through degree
`N_j+1`.  Equation (4) therefore gives the prescribed passport and the exact next-order
separation.

For completeness, the coordinate conversion is as follows.  If `b_n` is the `z`-coordinate flux
coefficient, then the affine substitution `z=-i(s-1/2)` sends it to `(-i)^n b_n`.  At `c'_j` this
is `a_(j,n)`.  At the conjugate point `d'_j` it is

`(-i)^n conj(i^n a_(j,n)) = (-1)^n conj(a_(j,n))`.

This equals `a_(j,n)` through degree `N_j` by (1), and equals
`(-1)^(N_j+1)conj(eta_j)` in degree `N_j+1`, which differs from `eta_j` by (2).

Positivity of `A(iy)B_L(iy)` gives the zero-free real axis.  Multiplication of the exact-order-one
envelope by a nonzero polynomial preserves exact order one.  Finally, any period of `F` transports
the two vertical zero progressions of `A`.  Since `B_L` has only finitely many zeros, three
consecutive sufficiently remote transported zeros lie again in those two progressions; their real
parts force the period to be purely imaginary and their imaginary parts force it into `pi i Z`.
It is then a period of `A`, so it is a period of `B_L`.  The polynomial `B_L` is nonconstant because
it vanishes at every prescribed point, and hence has no nonzero period.  Thus `F`, and therefore
`X`, is aperiodic.  This completes the proof.

## Sharpness and boundary

- **Exact compatibility space:** FE plus Schwarz fix precisely the graded-real locus (1), the
  construction realizes every finite point of that locus, and every transverse next coefficient
  in its complement is simultaneously realizable.
- **Sharp jet depth:** modulus `N_j+3` makes the induced flux correction start in degree
  `N_j+2`, exactly preserving degrees through the chosen separator in degree `N_j+1`.
- **Axis positivity:** arbitrary passports change `B_0`, but not the argument: real-evenness makes
  `B_0(iy)` real, while the strictly positive repair has strictly larger degree.
- **Full-germ separation:** this is local and explicit; the coefficient in degree `N_j+1` is
  `eta_j` at one partner and its distinct forced transform
  `(-1)^(N_j+1)conj(eta_j)` at the other.  The quasi-period argument is needed only for the
  independent aperiodicity guard.
- **Parent theory:** local logarithmic integration and finite Hermite CRT are classical.  The
  candidate content is the exact surjectivity statement with simultaneous off-line quartets,
  complete admissible passports, global axis positivity, exact order one, and aperiodicity.

## Lean interfaces

- `[FORMALIZATION]` `FiniteHermiteCRT.lean` supplies arbitrary finite Hermite interpolation, its
  sign/Schwarz-equivariant form, and the strict degree bound below the product modulus.  The theorem
  `exists_real_even_polynomial_iterateDerivative_eval_eq_degree_lt_modulus` is the exact global
  interpolation interface used above.
- `[FORMALIZATION]` `SimultaneousFiniteJetFlatness.lean` supplies exact local correction orders and
  strict positivity of the packet polynomial on the imaginary axis.
- `[FORMALIZATION]` `FiniteFluxPassport.lean` formalizes the polynomial passport map
  `P |-> -1-X P'`, proves its surjectivity onto every polynomial passport with constant `-1`, and
  proves that `x exp(P(x))` is an entire simple-zero realization whose actual normalized
  logarithmic derivative equals that passport away from the removable center.
- `[OPEN FORMAL INTERFACE]` Formalize the global positive-domination lemma and the order-one envelope.

## Gates

- [x] 0 -> 1: exact admissible coefficient space, construction, depth count, and boundary attacks
  are explicit.
- [x] 1 -> 2: the coordinate conversion, symmetry-assigned unit jets, degree-bounded CRT,
  positivity repair, exact separator, exact order, and aperiodicity have complete proofs above.
- [ ] independent audit of the coordinate conversion and the global period argument.
- [ ] 2 -> 3: the passport map and degree-controlled equivariant CRT are formalized; formalize the
  global positivity domination and order-one envelope.
- [ ] complete the literature and parent-theory audit before any scientific-novelty promotion.
