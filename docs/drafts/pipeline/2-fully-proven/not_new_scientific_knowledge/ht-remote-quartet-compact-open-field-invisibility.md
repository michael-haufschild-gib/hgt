# HT remote-quartet compact-open field invisibility

- **ID:** `ht-remote-quartet-compact-open-field-invisibility`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) — `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general hypertranscendence; remote divisor surgery; multi-route finite-probe no-go
- **Statement:** Inside one exact order-one differential-translation field and the FE/Schwarz symmetry
  cage, construct off-critical quartets in the critical strip escaping vertically to infinity while
  preserving any finite jet passport and converging to an all-line HT carrier with every derivative
  on every compact.

## Remote-quartet theorem `[PROVED HERE]`

Fix `0<|delta|<1/2` and let

`rho_T=1/2+delta+iT`, `T>0`.

Let `A subset C` be finite and invariant under `s |-> 1-s` and conjugation, and let the finite jet
depth `nu:A -> N` be invariant.  Put `w=s-1/2` and

`H_A(s)=w^2 prod_(a in A)(s-a)^(2 nu(a))`.                     (1)

There are real numbers `c_T,d_T` such that

`P_T(s)=1+H_A(s)(c_T+d_T w^2)`                                (2)

has all the following properties as `T -> infinity`:

1. `P_T(1-s)=P_T(s)` and `P_T(conj s)=conj(P_T(s))`;
2. `P_T-1` vanishes to order at least `nu(a)` at every `a in A`;
3. `P_T` vanishes at the full off-critical quartet
   `{rho_T,1-rho_T,conj(rho_T),1-conj(rho_T)}`, contained in `0<Re(s)<1`;
4. `P_T -> 1` with every derivative uniformly on every compact subset of `C`;
5. every zero of `P_T` escapes every fixed compact set.

### Proof

The polynomial `H_A` is real-even about `1/2`, has even degree `D>=2`, and satisfies

`|H_A(rho_T)| asymp T^D`.

Write

`b_T=-1/H_A(rho_T)`, `u_T=(delta+iT)^2`.

Since

`Im(u_T)=2 delta T !=0`,

the real numbers

`d_T=Im(b_T)/Im(u_T)`,

`c_T=Re(b_T)-d_T Re(u_T)`

satisfy `c_T+d_T u_T=b_T`.  Hence `P_T(rho_T)=0`; the two symmetries give the other
three zeros.  Moreover,

`d_T=O(T^(-D-1))`, `c_T=O(T^(1-D))`.                           (3)

Both coefficients tend to zero.  Since `H_A` is fixed, (2)--(3) imply convergence to `1` with
every derivative on compacts.  The even exponents in (1) give the symmetries and the passport
vanishing.  Finally, a zero sequence remaining in a fixed compact would contradict uniform
convergence there to the nonzero constant `1`. `QED`

## HT same-field realization `[PROVED HERE]`

Choose any real `alpha>0` with `2 alpha-1 notin Z`, and let

`C_alpha(s)=1/(Gamma(alpha+i(s-1/2)) Gamma(alpha-i(s-1/2)))`

be the order-one, FE/Schwarz-symmetric hypertranscendental carrier proved in
`finite-order-symmetry-ht-rational-gauge-blindness.md`.  Define

`F_T=P_T C_alpha`.

Then:

1. every `F_T` is entire, order one, FE/Schwarz-symmetric, and hypertranscendental;
2. `F_T` and `C_alpha` have identical jets through order `nu(a)-1` on `A`;
3. `F_T -> C_alpha` with every derivative on compacts;
4. `C_alpha` has only critical-line zeros, while every `F_T` has the designated off-line quartet;
5. for every `T`, their complete differential-translation fields are exactly equal:

   `C(s)(D^n T_h F_T:h in C,n>=0)`

   ` = C(s)(D^n T_h C_alpha:h in C,n>=0)`.                    (4)

All assertions except (4) follow from the remote-quartet theorem and the carrier theorem.
For (4), use

`T_h F_T(s)=P_T(s+h)T_h C_alpha(s)`.

The nonzero factor `P_T(s+h)` and its inverse belong to `C(s)`, so each translated generator on
either side belongs to the other field.  Differentiation and translation preserve the equality.
`QED`

## Topological selector law `[PROVED HERE]`

Inside this single differential-translation field, the critical-line divisor predicate is not open
in the compact-open topology, even after order one, the two scalar symmetries, and an arbitrary
finite passport are fixed.

More precisely, let `Phi_1,...,Phi_k` be continuous real-valued functionals on the symmetric entire
function space, and assume `Phi_j(C_alpha)>0` for all `j`.  Then

`Phi_j(F_T)>0`, `1<=j<=k`,

for all sufficiently large `T`, although `F_T` has off-critical zeros.  This is immediate from
`F_T -> C_alpha`.  Thus no finite collection of strict compact-open-continuous tests can be a
sufficient RH-type selector on this HT class.

## Finite Li-prefix corollary `[PROVED HERE]`

For an FE-symmetric divisor avoiding `0,1`, define its generalized Li sums by symmetric pairing,

`lambda_n(F)=sum_rho [1-(1-1/rho)^n]`.

For `C_alpha`, every pair `rho=1/2+i gamma`, `1-rho=conj(rho)` contributes

`2-2 Re((1-1/rho)^n)>=0`,

because `|1-1/rho|=1`.  The paired series converges like `sum gamma^(-2)` and is strictly positive
for every `n>=1`.  Hence

`lambda_n(C_alpha)>0` for all `n>=1`.                           (5)

The extra zeros of `P_T` form a symmetry-invariant set of uniformly bounded cardinality and, by
the theorem, all escape to infinity.  For a pair `rho,1-rho`, the `1/rho` terms in the binomial
expansion cancel:

`[1-(1-1/rho)^n]+[1-(1-1/(1-rho))^n]=O(|rho|^(-2))`.

Therefore

`lambda_n(F_T)-lambda_n(C_alpha) -> 0`                         (6)

for every fixed `n`.  From (5)--(6), for every finite `N` there is `T_N` such that

`lambda_1(F_T),...,lambda_N(F_T)>0`

for `T>=T_N`, even though `F_T` violates the critical-line divisor predicate.  Thus finite Li
positivity cannot be promoted to an RH proof by adjoining the complete HT differential-translation
field, scalar symmetries, order, or a finite normalization passport.

## Pure-quartet variant and finite decaying tests

For route tests that are naturally written directly on the divisor, use the degree-four factor

`Q_T(s)=((w^2-(delta+iT)^2)(w^2-(delta-iT)^2))/(delta^2+T^2)^2`.

It is real-even, has exactly the designated quartet, satisfies `Q_T(1/2)=1`, and tends to `1` with
all derivatives on compacts.  Multiplication by `Q_T` again leaves the complete
differential-translation field equal.

Consequently, any finite packet of strict Weil/Connes explicit-formula inequalities whose
zero-side test transforms decay uniformly as `|Im rho| -> infinity` in the critical strip remains
true after the quartet is inserted, for sufficiently large `T`.  The same applies to finitely many
inverse-power spectral moments or decaying trace tests.  This statement is only about finite
packets; the full Weil positivity cone and a complete spectral measure are global objects and are
not preserved.

## Exact route map

1. **Li:** every finite positive prefix survives a remote off-line quartet; the full infinite Li
   criterion is not excluded.
2. **Weil / Connes explicit formula:** every finite strict packet with vertically decaying tests can
   survive; the full test-function cone is not excluded.
3. **de Branges:** every finite collection of strict point/jet/compact inequalities continuous in
   the compact-open topology can survive; the global Hermite--Biehler inequality is not excluded.
4. **Hilbert--Polya / spectral:** finitely many decaying traces or inverse moments can survive; an
   actual self-adjoint operator whose complete spectrum is the divisor is not preserved.
5. **Nyman--Beurling:** no complete conclusion is claimed.  Its exact Hilbert-space closure uses the
   Euler/Dirichlet realization, absent from this carrier.  Only implementations that replace the
   closure by finitely many compact-open-continuous probes fall under the topological selector law.

The common consequence is sharp: a successful route must use an all-order, nonlocal selector.  HT,
even with the full translation-differential field and the constraints above, cannot turn a finite
strict certificate into one.

## Novelty audit

The construction is elementary once rational-gauge field invariance and the reflected-gamma carrier
are available.  Remote-root compact convergence and finite-prefix continuity are standard.  The
multi-route synthesis is useful but does not clear the novelty gate; this is a bridge/no-go theorem,
not new scientific knowledge.

## Lean status

No complete Lean claim is made.  The full theorem includes the analytic reflected-gamma carrier,
its hypertranscendence import, compact-open convergence, and generalized Li sums.  Formalizing only
the polynomial coefficient estimates would be a partial anchor and would not justify stage 3.

## Open core

Closed explicitly by the two real coefficients `c_T,d_T` in (3).

## Gates

- [x] 0 -> 1: exact construction and open core isolated
- [x] 1 -> 2: complete unconditional paper proof and route corollaries
- [ ] 2 -> 3: complete unconditional theorem formalized in Lean
- [ ] 3 -> 4: publication-ready preprint

## Log

- 2026-07-11 -- Solved the symmetry-compatible remote interpolation problem with a two-dimensional
  real-even correction.  The full off-line quartet escapes vertically while all compact jets and
  every prescribed finite passport converge to the all-line HT carrier.
- 2026-07-11 -- Proved exact differential-translation field equality, finite Li-prefix positivity,
  and the finite continuous-selector law.  Classified the result as a bridge.
