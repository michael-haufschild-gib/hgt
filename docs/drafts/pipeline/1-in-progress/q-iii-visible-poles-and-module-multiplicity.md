# Q-III: visible poles and actual module multiplicity

- **ID:** q-iii-visible-poles-and-module-multiplicity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / source-identification audit
- **Parent:** [Q-III](q-iii-escape-state-classification.md)
- **Question:** Which uncancelled poles of the actual receiver transform are
  visible in its cofactor modules, and what relation connects their orders to
  joint generalized spectral multiplicities?

## Source evidence inspected

`RHTower/PMPowerDampedMobiusMellin.lean` proves the literal Fermi-source Mellin
identity on its initial convergence strip:

`M(F_epsilon)(s)=(1-2^(1-s))*zeta(s)/(s*zeta(s+epsilon))`.

`TheDampedMoebiusMellinQuotientIsHardyRightOfTheZeroAbscissa.lean` constructs its
pole-cleared continuation with `etaSlope`, `zetaResidueUnit`, and `invZeta`.
It proves Hardy bounds strictly to the right of the zero abscissa. These are
Fermi-source statements. Do not silently identify the Fermi and centered
divisor source presentations or their normalized modules.

The more relevant bridge already exists in AOT
`TheOffLineZerosObstructTheMoebiusReceiver.lean`, using THIM
`APaidReceiverContinuesTheDirichletSeriesAcrossItsAbscissa.lean`.
For each real repairing Wiener kernel `k`, it constructs an analytic `Phi`
on `Re(s)>1/2` and proves on `1/2<Re(s)<1` the exact cleared identity

`Z_epsilon(s) Phi(s) = (s+epsilon-1) zeta(s) K(s) - m zeta(s) Z_epsilon(s)`,

where `Z_epsilon(s)=(s+epsilon-1)zeta(s+epsilon)` is the residue-unit
continuation and `K` is the kernel L-series. This is a direct paid-receiver
argument. Its identity is presently internal to
`riemannZeta_mul_lSeries_eq_zero_of_repairs`; expose and reuse it for orders.

The newly drafted finite-module index counts joint generalized eigenspace
dimensions. It does not identify them with arithmetic zero orders. The
existing AOT index formula for the actual receiver is an above-width
empty-hull result; its below-width classification remains open.

The exact AOT definition `translatedOffLineZeroHull` already restricts to
zeros `rho` satisfying `zeta(rho-epsilon) != 0`.
`translatedOffLineZeroHull_subset_obstructionHull_moebius` proves these points
are obstructions via `mem_obstructionHull_moebius_of_zero`. Thus the basic
noncancellation gate is existing work, not a new discovery. Any extension here
must handle partial cancellation and exact multiplicity, then connect it to
the smaller hull of each actual cofactor module.

## Candidate refinement and unresolved steps

A denominator zero does not by itself specify a pole order of a quotient:
numerator zero orders must be subtracted. On the initial Fermi continuation,
away from the explicit scalar poles, the meromorphic order is the sum of
numerator orders minus the shifted denominator order. The eta factor is
nonzero in the open strip below real part one. Thus any proposed zero count
must first identify the uncancelled receiver divisor. No common-zero
configuration of zeta is asserted or assumed here.

Required work:

1. Extract the existing cleared analytic identity as a reusable theorem;
   preserve its actual centered receiver and source conventions.
2. Extend the existing noncancellation bridge to exact visible pole orders
   using meromorphic-order calculus. Account for partial cancellation without
   adding a nonvanishing premise.
3. Prove which pole data constrain the paid ideal and the closed module
   annihilator. Keep these two ideals separate.
4. Relate actual cofactor modules to this divisor, or find the precise
   obstruction and a positive replacement. Purely algebraic joint
   multiplicities do not supply that relation.

This card records a source-based lead, not a proved arithmetic classification.
No new analytic hypothesis or unproved interface is available as an input.

## Dependency-closed positive refinement on paper

Fix a translated zero `s0=rho-epsilon` with
`1/2+epsilon<Re(rho)<1`. Both `zeta(s)` and `K(s)` are analytic near `s0`.
The scalar `s+epsilon-1` is nonzero there. Rearranging the inspected cleared
identity gives the local analytic factorization

`zeta(s) K(s) = Z_epsilon(s) H(s)`,

where `H=(Phi+m*zeta)/(s+epsilon-1)` is analytic. Translation and multiplication
by the nonzero residue factor preserve the zero order of `zeta` at `rho`.
Additivity of analytic orders therefore proves, with infinity allowed,

`ord_(rho-epsilon)(K) + ord_(rho-epsilon)(zeta) >= ord_rho(zeta)`.

In particular every repairing kernel vanishes at `rho-epsilon` whenever the
denominator zero order is strictly greater than the numerator zero order.
For complex Wiener kernels apply the real-kernel factorization to real and
imaginary parts. This strictly extends the existing nonvanishing-numerator
criterion to partial cancellation. The same inequality gives the required
kernel jet order `max(ord_rho(zeta)-ord_(rho-epsilon)(zeta),0)`.

The argument uses the already proved paid-receiver continuation, not a new
source-growth premise. It identifies a lower constraint on the paid ideal;
it does not put these points into every actual module hull or prove the
requested reverse inclusion. Lean extraction, order calculus, and jet
consequences remain to be checked. General analytic order arithmetic is not
claimed as new; the target application is the exact actual repairing ideal.

## Lean drafts awaiting their first check

- `/tmp/qiii_cleared_continuation_body.lean`: exact extraction of the existing
  centered-receiver continuation argument, retaining its full strip identity.
- `/tmp/qiii_paid_kernel_zero_order_body.lean`: real-kernel order inequality,
  strict-order-loss vanishing, partial-cancellation Bohr obstruction, and
  nonpayment. The proof multiplies through by the nonzero residue factor,
  avoiding local division. Uses the existing translation-invariance and
  residue-unit order theorems.

These drafts have not passed Lean. Once checked, extract the continuation
helper into the existing AOT module and refactor its old value-at-zero proof
through that helper; do not retain two copies of the continuation argument.

The order draft now also combines real and imaginary parts using the minimum
order bound for sums. It states the complex paid-kernel inequality, defines
`visibleTranslatedZetaOrder`, and derives every lower kernel-jet vanishing
condition. All these additions remain unverified in Lean. No equality of the
paid ideal with this jet ideal, nor equality with the actual annihilator, is
claimed.

The dependency-closed paid-ideal refinement has its own card:
[Paid kernels cover visible shifted zero orders](../2-fully-proven/paid-kernels-cover-visible-shifted-zero-orders.md).
The present card retains the unresolved identification with actual module
spectra and multiplicities.
