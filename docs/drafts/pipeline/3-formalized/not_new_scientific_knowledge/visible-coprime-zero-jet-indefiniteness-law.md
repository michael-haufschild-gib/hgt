# Visible-coprime zero-jet orientation and indefiniteness law

- **ID:** `visible-coprime-zero-jet-indefiniteness-law`
- **Stage:** 3-formalized / not new scientific knowledge
- **Type:** THEOREM (paper) / NO-GO / BRIDGE
- **Scientific status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [REDISCOVERED PARENTS] [BRIDGE] [NOT RH]`
- **Source:** Möbius--Laplace renewal law / visible-lattice inversion / GCD-matrix inertia
- **Statement:** Primitive-lattice convolution gives an exact signed zero-orientation jet, but
  its coprimality kernel has Möbius inertia and therefore unbounded negative index; no positive
  divisor-stationary kernel can retain the critical-line zero.

## Goal

Test whether the exact Möbius--Laplace Lambert law can be squared over primitive dilation pairs
to produce a positive source for the missing half-power bound.  The answer is exact: primitive
convolution does detect horizontal zero orientation, but precisely through an indefinite kernel.
This closes positive GCD-kernel and finite-negative-index versions of the route.

Put

```text
Phi(x)=sum_(n>=1) mu(n) exp(-n x),    x>0.
```

## Exact visible-addition law

Absolute convergence and the Lambert identity give

```text
sum_(n>=1) Phi(n x)=exp(-x).                                  (V1)
```

For `r>=2` and `x_1,...,x_r>0`, define

```text
P_r(x_1,...,x_r)
 = sum_(gcd(a_1,...,a_r)=1) product_j Phi(a_j x_j).           (V2)
```

Every positive lattice point has a unique common gcd.  Hence

```text
sum_(d>=1) P_r(d x_1,...,d x_r)
 = product_j sum_(a_j>=1) Phi(a_j x_j)
 = product_j exp(-x_j)=exp(-(x_1+...+x_r)).                  (V3)
```

Möbius inversion along the common dilation gives the exact universal law

```text
P_r(x_1,...,x_r)
 = sum_(d>=1) mu(d) exp(-d(x_1+...+x_r))
 = Phi(x_1+...+x_r).                                        (V4)
```

For `r=2`,

```text
sum_((a,b)=1) Phi(a x) Phi(b y)=Phi(x+y).                    (V5)
```

This is a genuine nonlinear identity, but it is not a source estimate.

## Mellin symbol and zero radical

For `Re(s),Re(t)>1`, the primitive-lattice Mellin symbol is the classical identity

```text
K(s,t)=sum_((a,b)=1) a^(-s)b^(-t)
      =zeta(s)zeta(t)/zeta(s+t).                             (V6)
```

Thus every zeta-zero mode belongs to the radical of primitive convolution.  This is the exact
reason `(V5)` can hold in the presence of a hypothetical off-line zero: the nonlinear carrier
annihilates, rather than controls, the offending Mellin mode.

## Hermitian zero-jet orientation law

Let `rho` be a nontrivial zeta zero of multiplicity `m`, and put `beta=Re(rho)`.  Interpret
`1/zeta(u)` at `u=1` by its holomorphic continuation, whose value is zero.  Then

```text
J(rho)
 = (partial_s^m partial_t^m K)(rho,conj(rho))
 = |zeta^(m)(rho)|^2 / zeta(2 beta).                         (V7)
```

Indeed, every zeta derivative of order below `m` vanishes at `rho` and `conj(rho)`.  In the
two Leibniz expansions, any derivative falling on `1/zeta(s+t)` therefore leaves a lower zeta
derivative and vanishes.  The unique survivor differentiates each numerator factor exactly `m`
times, proving `(V7)`.

For `0<u<1`, the alternating eta series is positive and

```text
zeta(u)=eta(u)/(1-2^(1-u))<0.
```

For `u>1`, the positive Dirichlet series gives `zeta(u)>0`, while `1/zeta(1)=0`.  Since the
leading zero derivative is nonzero,

```text
sign J(rho)=sign(2 Re(rho)-1),                              (V8)
J(rho)=0  iff  Re(rho)=1/2.                                (V9)
```

This is an exact pointwise orientation law, not proof that the jet vanishes.

### Primitive Dirichlet-character form

Let `chi` be primitive modulo `q`, and let `chi_0(n)=|chi(n)|^2` be the principal character.
For `Re(s),Re(t)>1`,

```text
K_chi(s,t)
 =sum_((a,b)=1) chi(a)conj(chi(b))a^(-s)b^(-t)
 =L(s,chi)L(t,conj(chi))/L(s+t,chi_0).                      (V10)
```

If `rho` is a nontrivial zero of `L(s,chi)` of multiplicity `m`, coefficient conjugation makes
`conj(rho)` a zero of `L(t,conj(chi))` with the same multiplicity.  The same Leibniz argument gives

```text
J_chi(rho)
 = |L^(m)(rho,chi)|^2 / L(2 Re(rho),chi_0).                 (V11)
```

Since

```text
L(u,chi_0)=zeta(u) product_(p|q)(1-p^(-u)),                 (V12)
```

and every finite Euler factor is positive for real `u>0`, `(V8)`--`(V9)` hold unchanged.  This
includes real exceptional zeros; no simplicity assumption is used.

## Exact finite inertia law

Let `C_N` be the real `N x N` coprimality matrix

```text
C_N(i,j)=1 if gcd(i,j)=1, and 0 otherwise.                  (V13)
```

Let `E_N(i,d)=1` when `d|i` and zero otherwise.  Divisor Möbius inversion gives

```text
C_N=E_N diag(mu(1),...,mu(N)) E_N^T.                        (V14)
```

In numerical order, `E_N` is lower triangular with diagonal one, hence invertible.  Sylvester's
law of inertia proves

```text
n_+(C_N)=#{d<=N:mu(d)=+1},
n_0(C_N)=#{d<=N:mu(d)=0},
n_-(C_N)=#{d<=N:mu(d)=-1}.                                 (V15)
```

In particular the negative index is unbounded: every new prime supplies another `mu(p)=-1`
diagonal direction.  No correction of fixed finite rank can make all `C_N` positive semidefinite.

The same formula gives an exact spectral-flow law.  If `sig(A)=n_+(A)-n_-(A)`, then

```text
sig(C_N)=sum_(d<=N)mu(d)=M(N),                              (V15a)
sig(C_N)-sig(C_(N-1))=mu(N).                               (V15b)
```

Thus the prime number theorem is exactly `sig(C_N)=o(N)`, and the classical Littlewood
criterion rewrites RH as

```text
for every epsilon>0, sig(C_N)=O_epsilon(N^(1/2+epsilon)).   (V15c)
```

This is an exact `0`--`1` matrix encoding of Mertens cancellation, not an independent spectral
bound: factorization `(V14)` already contains every Möbius sign on its diagonal.

## Universal positive-kernel obstruction

For a real arithmetic sequence `c(d)`, consider the divisor-stationary kernel

```text
H_c(a,b)=sum_(d|gcd(a,b)) c(d).                             (V16)
```

On every initial finite interval its matrix factors as

```text
H_(c,N)=E_N diag(c(1),...,c(N)) E_N^T.                      (V17)
```

Consequently `H_(c,N)` is positive semidefinite for every `N` if and only if `c(d)>=0` for every
`d`.  Its Mellin symbol, wherever absolutely convergent, is

```text
sum_(a,b>=1) H_c(a,b)a^(-s)b^(-t)
 =zeta(s)zeta(t) C(s+t),
C(u)=sum_(d>=1)c(d)d^(-u).                                 (V18)
```

If the critical energy `C(1)` is finite and `c` is nonzero and nonnegative, then `C(1)>0`; if it
is infinite, no finite critical kernel value exists.  Therefore a nonzero positive
divisor-stationary kernel can neither have a finite zero at `s+t=1` nor reproduce `(V9)`.
The coprimality detector uses `c=mu` and `C=1/zeta`; its critical zero is purchased exactly by
the unbounded negative inertia `(V15)`.

## Positive diagonal completion destroys the detector

The obstruction is not confined to divisor-stationary corrections.  Let `W=(w_(a,b))` be any
Hermitian kernel supported on coprime pairs of integers greater than one, with some
`w_(a,b) != 0`.  Its diagonal is zero because `gcd(a,a)>1`.  If

```text
W + diag(d_1,d_2,...)
```

is positive semidefinite, every nonzero `2 x 2` coprime block forces

```text
d_a>=0, d_b>=0, d_a d_b >= |w_(a,b)|^2,                    (V19)
```

so in particular some `d_n>0` with `n>1`.  If the correction has a finite critical Dirichlet
symbol

```text
D(u)=sum_(n>=1)d_n n^(-u),                                  (V20)
```

Finite `D(1)` alone does **not** imply convergence of the logarithmically weighted boundary
moments: `d_n=1/(log n)^2` for `n>=2` has finite `sum d_n/n` and divergent
`sum d_n(log n)^2/n`.  The exact unconditional boundary statement is the dichotomy

```text
either D is not holomorphic at u=1,
or, for every m>=0 and Re(s)=1/2,
  (partial_s^m partial_t^m D(s+t))_(t=conj(s))
   =D^(2m)(1)
   =sum_(n>=1)d_n (log n)^(2m)/n > 0.                      (V21)
```

Indeed, if `D` is holomorphic at `1`, local Landau transfer for nonnegative Dirichlet
coefficients forces convergence at some abscissa strictly left of `1`; all critical logarithmic
moments then converge and termwise differentiation gives the second branch.  Thus any positive
diagonal completion capable of repairing even one nonzero coprime edge either has no analytic
critical jet at all or adds a strictly positive critical-line jet and destroys `(V9)`.  Analytic
positive completion and exact critical-line vanishing are incompatible before any asymptotic
estimate is attempted.

## Hostile verdict

`REDISCOVERED / BRIDGE`, not candidate new scientific knowledge.

1. Visible-lattice decomposition and `(V6)` are classical Möbius inversion.
2. GCD-matrix incidence factorizations, inertia, and positivity criteria are established parent
   theory.
3. The zero-jet, spectral-signature, and Dirichlet-character formulas are short consequences of those parents plus
   zero multiplicity.  Exact searches found no matching packaged statement, but packaging does
   not overcome routine derivability.
4. `(V9)` is a zero-location certificate, not a source theorem.  It measures orientation only
   after a zero is supplied.
5. Positivity cannot be added inside this representation: `(V15)`, `(V17)`, and `(V21)` are exact
   obstructions, not missing estimates.

## No-go closure

- **Exact killing theorem/mechanism:** Mellin zero modes lie in the radical of visible
  convolution; differentiating lifts the radical only into the indefinite coprimality form.
  Coprimality inertia is exactly Möbius sign inertia and has unbounded negative index.
- **Strongest positive survivor:** the universal zero-jet orientation law `(V7)`--`(V12)`, the
  exact spectral signature law `(V15a)`--`(V15c)`, and the
  exact positive-kernel/completion impossibility theorems `(V16)`--`(V21)`.
- **New insight:** a successful Möbius--Laplace source cannot be a positive GCD-stationary form,
  a finite-negative-index correction of coprimality, or a primitive-dilation norm.  It must use a
  source-defined nonstationary cancellation before positivity, or retain an infinite Krein
  cancellation with an independent sign-selection theorem.
- **Status:** dependency-closed paper proof and dependency-closed Lean formalization.  Parent
  mechanisms are known, so no novelty claim.  Formal leaves include the analytic zeta/Dirichlet
  zero jets, infinite Mellin symbol, arbitrary finite-rank obstruction, and corrected critical
  boundary dichotomy—not only matrix wrappers.

## Literature boundary

- Geoffrey B. Campbell, *Visible Point Vector Partition Identities for Hyperpyramid Lattices*,
  arXiv:2309.16094, records the general visible-lattice zeta quotient
  `product_j zeta(s_j)/zeta(sum_j s_j)`.
- Pentti Haukkanen and Jori K. Merikoski, *Inertia, positive definiteness and l_p norm of GCD and
  LCM matrices and their unitary analogs*, arXiv:1707.09473, develops incidence factorizations,
  inertia, and positivity through Sylvester congruence.
- The local Dirichlet `L`-function continuation, Euler product, and functional equation are
  standard; no claim of novelty is attached to `(V10)`--`(V12)`.

## Gates

- [x] internal Möbius--Laplace and heat-finite-part corpus audited
- [x] visible-lattice and GCD-matrix parent literature audited
- [x] visible-addition law paper-proved
- [x] zero-jet orientation law paper-proved, including multiplicity and complex characters
- [x] finite inertia and positive-kernel no-go paper-proved
- [x] exact coprimality spectral flow identified with the Mertens function
- [x] positive diagonal completion proved to destroy the critical zero jet
- [ ] source-defined nonstationary sign selector
- [ ] half-power Möbius--Laplace control
- [ ] RH

## Log

- 2026-07-22 — visible-addition conjecture derived, reduced to classical visible-lattice
  inversion, and rejected as a source because zeta-zero modes lie in its radical.
- 2026-07-22 — strongest survivor extracted: exact zero-jet orientation, Möbius inertia, and
  positive divisor-kernel impossibility.

## Lean status update (2026-08-23): Möbius incidence entry

`formal/GaloisForLFunctions/RHTower/MobiusCoprimeIncidence.lean` now formalizes the exact arithmetic entry behind the claimed incidence factorization: the Möbius sum over all common divisors of `a` and `b` is the integral `0`--`1` indicator of `Nat.Coprime a b`.  The positive-coordinate specialization is supplied in the same leaf, matching the natural indexing of a finite coprimality matrix.  This is derived directly from Mathlib's proved Möbius--zeta convolution identity, with no arithmetic hypothesis, axiom, or finite computation.

The leaf is wired into `GaloisForLFunctions/RHTower.lean`, direct-checked with `lake env lean`, and exact-target-built with `lake build GaloisForLFunctions.RHTower.MobiusCoprimeIncidence`.  Both declarations audit only to `[propext, Classical.choice, Quot.sound]`.

This closes the scalar incidence entry only.  The finite matrix congruence/inertia count, visible-addition summability, and the completed zeta/Dirichlet mixed-jet calculation remain to be formalized before this card can move to stage 3.

## Lean status update (2026-08-23): finite incidence factorization

`formal/GaloisForLFunctions/RHTower/MobiusCoprimeMatrixFactorization.lean` now promotes that entry identity to the literal finite matrix statement from `(V14)`.  On the exact coordinate type `{1,...,N}`, it defines the coprimality matrix, divisor-incidence matrix, and Möbius diagonal, then proves
`C_N = E_N * diagonal(mu) * E_N.transpose` entrywise.  Coordinate positivity and the bound by `N` are encoded in the finite index type, so the public factorization has no theorem hypotheses.

The leaf is wired into `GaloisForLFunctions/RHTower.lean`, direct-checked with `lake env lean`, and exact-target-built with `lake build GaloisForLFunctions.RHTower.MobiusCoprimeMatrixFactorization`.  The entry, product-entry, and full factorization declarations audit only to `[propext, Classical.choice, Quot.sound]`.

The next precise finite task is the congruence/inertia extraction from this factorization.  The analytic visible-addition and zeta/Dirichlet mixed-jet parts remain separate required work; the card stays at stage 2.

## Lean status update (2026-08-23): incidence invertibility

The same factorization leaf now proves that the divisor-incidence matrix is lower triangular in its natural positive-coordinate order, has unit diagonal and determinant exactly one, and is therefore a unit over the integers.  This closes the algebraic congruence prerequisite for transporting the Möbius diagonal’s sign data to the coprimality matrix; it is not merely an entrywise factorization.

The changed leaf was direct-checked and exact-target-built again as `GaloisForLFunctions.RHTower.MobiusCoprimeMatrixFactorization`.  Its new triangularity, determinant, and invertibility declarations audit only to `[propext, Classical.choice, Quot.sound]`.  The exact positive/null/negative inertia cardinalities and unbounded-negative-index conclusion remain the next finite-dimensional layer.

## Lean status update (2026-08-23): exact finite Möbius inertia

`formal/GaloisForLFunctions/RHTower/MobiusCoprimeInertia.lean` now closes the exact finite inertia law `(V15)`.  It complexifies the integral factorization, proves the complex incidence matrix and its transpose are units, identifies the coprimality matrix as an invertible Hermitian congruence of the real Möbius diagonal, and applies the corpus's proved Sylvester law.  The resulting unconditional declarations are exactly

```text
hermPosIndex C_N  = #{d in {1,...,N} : mu(d)= 1},
hermNullIndex C_N = #{d in {1,...,N} : mu(d)= 0},
hermNegIndex C_N  = #{d in {1,...,N} : mu(d)=-1}.
```

The leaf is wired into `GaloisForLFunctions/RHTower.lean`, direct-checked with `lake env lean`, and exact-target-built with `lake build GaloisForLFunctions.RHTower.MobiusCoprimeInertia`.  Its complex factorization, congruence, Hermitian, and three exact inertia declarations audit only to `[propext, Classical.choice, Quot.sound]`.

This completes the card's finite inertia identity, without a matrix-size computation or a spectral hypothesis.  Still required for stage 3: the visible-addition analytic identity, zeta/Dirichlet mixed zero-jet orientation, positive-kernel obstruction, diagonal-completion obstruction, and the unbounded-negative-index corollary.

## Lean status update (2026-08-23): unbounded negative index

`formal/GaloisForLFunctions/RHTower/MobiusCoprimeInertiaUnbounded.lean` now closes the final conclusion of `(V15)`: negative inertia is unbounded.  For every `k`, the first `k` primes are injected into the negative Möbius coordinates below the `k`th prime; `mu(p)=-1` then combines with the exact inertia theorem to produce a cutoff `N` whose coprimality matrix has negative index at least `k`.  The construction is symbolic and uses the corpus's proved ordered-prime equivalence, not finite prime enumeration.

The leaf is umbrella-wired, direct-checked, and exact-target-built with `lake build GaloisForLFunctions.RHTower.MobiusCoprimeInertiaUnbounded`.  Both declarations audit only to `[propext, Classical.choice, Quot.sound]`.

The entire finite incidence/inertia portion `(V13)`--`(V15)` is now Lean-complete.  Remaining stage-3 blockers are the analytic visible-addition/Mellin and mixed-zero-jet laws plus the two positive-kernel obstruction arguments.

## Lean status update (2026-08-23): exact Mertens signature flow

`formal/GaloisForLFunctions/RHTower/MobiusCoprimeSignatureFlow.lean` now closes `(V15a)`--`(V15b)`.  It defines the spectral signature as the integer difference of the already-proved Hermitian positive and negative indices, transports those subtype counts to the natural interval `Icc 1 N`, and reuses the corpus's Möbius sign-balance theorem.  The resulting unconditional identities are

```text
finiteMobiusCoprimeSignature N = sum_{1 <= d <= N} mu(d),
((finiteMobiusCoprimeSignature N : Int) : Real) = mertensM N,
finiteMobiusCoprimeSignature (N+1) - finiteMobiusCoprimeSignature N = mu(N+1).
```

The leaf is wired into `GaloisForLFunctions/RHTower.lean`, direct-checked with `lake env lean`, and exact-target-built with `lake build GaloisForLFunctions.RHTower.MobiusCoprimeSignatureFlow`.  All four new public theorem declarations audit only to `[propext, Classical.choice, Quot.sound]`.

This completes exact finite spectral flow without computation.  The card remains at stage 2: `(V15c)` still needs its exact RH-growth formulation, and the analytic visible-addition/Mellin, mixed-zero-jet, positive-kernel, and diagonal-completion parts remain required.

## Lean status update (2026-08-23): Littlewood signature criterion

`formal/GaloisForLFunctions/RHTower/MobiusCoprimeSignatureRH.lean` now closes `(V15c)` exactly.  It proves that the corpus's complex Mertens partial sum is the real Mertens function embedded in `Complex`, identifies its norm with the absolute coprimality-matrix signature, and transports the already-closed Littlewood criterion to the matrix statement

```text
(forall delta > 0, exists C >= 0, forall N,
  |sig(C_N)| <= C * (N+1)^(1/2+delta))
  iff RiemannHypothesis.
```

This equivalence is a closed theorem, not a theorem under RH or under an added Mertens premise.  The leaf is umbrella-wired, direct-checked, and exact-target-built with `lake build GaloisForLFunctions.RHTower.MobiusCoprimeSignatureRH`.  Its four public theorem declarations audit only to `[propext, Classical.choice, Quot.sound]`.

Thus `(V13)`--`(V15c)` are Lean-complete.  The card remains at stage 2 pending its analytic visible-addition/Mellin, mixed-zero-jet, universal positive-kernel, and diagonal-completion obstruction theorems.

## Lean status update (2026-08-23): universal divisor-stationary positivity

`formal/GaloisForLFunctions/RHTower/DivisorStationaryKernelPositivity.lean` now closes the finite-algebraic content of `(V16)`--`(V17)` for an arbitrary real arithmetic sequence `c`.  It defines the literal kernel

```text
H_c,N(a,b) = sum_{1 <= d <= N} if d|a and d|b then c(d) else 0,
```

proves its exact factorization `H_c,N = E_N diag(c) E_N.transpose`, transports integral incidence invertibility to `Real`, and proves both the fixed-cutoff and all-cutoff order laws

```text
H_c,N is PSD iff every c(d) on {1,...,N} is nonnegative,
(forall N, H_c,N is PSD) iff (forall d>0, c(d)>=0).
```

The leaf is umbrella-wired, direct-checked, and exact-target-built with `lake build GaloisForLFunctions.RHTower.DivisorStationaryKernelPositivity`.  Its five public theorem declarations audit only to `[propext, Classical.choice, Quot.sound]`.

The finite incidence/positivity obstruction is complete.  The card stays at stage 2 because the infinite Mellin-symbol identity and critical-energy conclusion `(V18)`, diagonal-completion jet `(V19)`--`(V21)`, and the earlier visible-addition/mixed-zero-jet analytic laws remain.

## Lean status update (2026-08-23): sharp diagonal-completion edge cost

`formal/GaloisForLFunctions/RHTower/PositiveDiagonalCompletionEdge.lean` now closes `(V19)` in a form stronger than the card's final existence statement.  For an arbitrary finite Hermitian matrix `W`, any two distinct zero-diagonal coordinates `a,b`, and any real diagonal correction `d`, positivity of `W + diag(d)` implies

```text
0 <= d(a),  0 <= d(b),  ‖W(a,b)‖^2 <= d(a)*d(b).
```

If `W(a,b) != 0`, both `d(a)` and `d(b)` are strictly positive.  The proof takes the exact two-coordinate principal submatrix, applies nonnegativity of its determinant, and uses Hermitian symmetry to identify the off-diagonal product with the squared complex norm.

The leaf is umbrella-wired, direct-checked, and exact-target-built with `lake build GaloisForLFunctions.RHTower.PositiveDiagonalCompletionEdge`.  Both public declarations audit only to `[propext, Classical.choice, Quot.sound]`.

The card remains at stage 2 pending `(V18)`, the infinite derivative/strict-positivity statement `(V20)`--`(V21)`, and the visible-addition/mixed-zero-jet analytic laws.

## Lean status update (2026-08-23): positive Dirichlet completion jets

`formal/GaloisForLFunctions/RHTower/PositiveDiagonalCompletionDirichletJet.lean` supplies the dependency-closed analytic core of `(V20)`--`(V21)`.  It first proves the reusable identity that the `(p,q)` mixed derivative of `F(s+t)` is `F^(p+q)(s+t)`.  It then packages a nonnegative Dirichlet coefficient family, convergence at an abscissa `sigma0`, and one strictly positive coefficient at some `n>1` as data.  For that data it proves:

```text
C(sigma0) > 0,
C^(2m)(sigma0+h) = sum_n d_n*(log n)^(2m)*n^(-(sigma0+h)) > 0  for h>0,
partial_s^m partial_t^m C(s+t) at t=conj(s)
  = sum_n d_n*(log n)^(2m)*n^(-2 Re(s)) > 0
  whenever sigma0 < 2 Re(s).
```

All convergence and positivity requirements are fields of the data object, so theorem declarations add no premises.  The leaf is umbrella-wired, direct-checked, and exact-target-built with `lake build GaloisForLFunctions.RHTower.PositiveDiagonalCompletionDirichletJet`.  Its nine public theorem declarations audit only to `[propext, Classical.choice, Quot.sound]`.

Lean also makes an important boundary distinction explicit: convergence of `sum d_n/n` alone does not imply convergence of `sum d_n*(log n)^(2m)/n`.  Thus the exact critical-line derivative in `(V21)` requires either convergence at an abscissa left of `1` (already covered by this leaf) or an analytic-continuation input from which Landau's theorem derives that margin.  The card remains at stage 2 until that boundary bridge, `(V18)`, and the earlier visible-addition/mixed-zero-jet laws are closed.

## Lean status update (2026-08-24): visible Mellin and all zeta/Dirichlet zero jets

`VisibleCoprimeMobiusLaplaceAddition.lean` and `VisibleCoprimeMellinSymbol.lean` close the exact
visible-addition and zeta Mellin identities `(V1)`--`(V6)`.  The dedicated
`VisibleCoprimeZetaZeroJet.lean` leaf then closes `(V7)`--`(V9)` at every actual Xi divisor,
including exact analytic multiplicity, Schwarz-conjugate leading jets, real-valuedness, strict
left/right chamber signs, and vanishing if and only if the divisor lies on the critical line.

`formal/GaloisForLFunctions/RHTower/VisibleCoprimeDirichletZeroJet.lean` now closes the complete
primitive-character extension `(V10)`--`(V12)`.  It proves the character-weighted visible-lattice
series from absolute convergence, the exact principal-character Euler factorization, a
pole-filled reciprocal at `s+t=1`, and global coefficient-conjugation symmetry for Dirichlet
`L`-functions by analytic continuation from `Re(s)>1`.  An actual open-strip zero is bundled as
data, its multiplicity is derived from `analyticOrderAt`, all lower jets are discharged, and the
mixed Hermitian jet satisfies the literal formula

```text
J_chi(rho) = |L^(m)(rho,chi)|^2 * principalDirichletInv(q, 2 Re(rho)).
```

The finite Euler correction is strictly positive for every positive real abscissa.  Consequently
the leaf proves, without GRH, simplicity, or a zero-location premise, that this jet is negative
left of `1/2`, zero exactly at `1/2`, and positive right of `1/2`; both sign implications are
packaged as equivalences.

All four leaves are wired into `GaloisForLFunctions/RHTower.lean`; only their exact leaf targets
were built.  Every newly introduced declaration in the Dirichlet leaf was audited and depends
only on `[propext, Classical.choice, Quot.sound]`.

Thus `(V1)`--`(V17)` and the interior-abscissa form of `(V20)`--`(V21)` are Lean-complete.  This
card remains at stage 2 only for the infinite divisor-stationary Mellin/critical-energy law
`(V18)` and the exact finite-critical-energy boundary bridge needed to state `(V21)` at its paper
hypotheses.

## Lean completion update (2026-08-24): V18, exact boundary dichotomy, and capstones

`formal/GaloisForLFunctions/RHTower/DivisorStationaryKernelMellinSymbol.lean` closes `(V18)` for
the literal infinite common-divisor kernel.  Under its bundled absolute-convergence data it proves
absolute summability of the two-variable Mellin series and the exact factorization

```text
M_c(s,t)=zeta(s) zeta(t) sum_d c(d)d^(-(s+t)).
```

For nonzero nonnegative coefficient data, the critical coefficient series is the strictly
positive zeroth logarithmic moment.  The same leaf formally refutes the former unqualified
boundary inference with the closed coefficient family `d_n=1/(log n)^2`: critical mass is finite
while the second logarithmic moment diverges.

`PositiveDiagonalCompletionCriticalBoundaryDichotomy.lean` supplies the corrected unconditional
`(V21)`.  If the positive Dirichlet series is analytic at `1`, local analyticity gives a closed
ball; the general Landau transfer theorem forces convergence at an abscissa left of `1`, hence all
critical logarithmic moments converge and every reflected even mixed jet is exactly its strictly
positive moment.  Otherwise the series is nonanalytic at `1`.  The counterexample is consequently
proved nonanalytic there.

Two final capstone leaves close claims outside the numbered display equations:

- `MobiusCoprimeSignatureAsymptoticFiniteRank.lean` proves the PNT limit
  `|sig(C_N)|/N -> 0` and the full arbitrary-correction rank law: if `C_N+R` is positive
  semidefinite, the range dimension of `R` is at least the negative inertia of `C_N`.  Unbounded
  Möbius negative inertia therefore rules out every uniformly fixed finite-rank correction family.
- `PositiveDiagonalCoprimeKernelRepairNoGo.lean` formalizes an infinite coprime-supported
  Hermitian kernel through all injective finite PSD sections.  It derives zero diagonal from
  coprime support, derives every correction coefficient `d_n>=0` from positivity, derives a
  strictly positive coefficient at `n>1` from an actual nonzero coprime edge, and applies the exact
  boundary dichotomy.  Thus the repair-to-critical-jet incompatibility is a single closed theorem,
  not an informal juxtaposition of `(V19)` and `(V21)`.

Every new leaf was direct-checked with `lake env lean`, exact-target-built only, and wired into
`GaloisForLFunctions/RHTower.lean` without building that umbrella.  Every new public declaration
audits only to `[propext, Classical.choice, Quot.sound]`.  With `(V1)`--`(V21)` and all stated
capstones formalized, this card is promoted to stage 3.
