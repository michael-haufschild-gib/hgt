# Finite prime jets classify the one-slot quotient, but not the all-orders constraint

- **ID:** pinned-affine-prime-jet-rigidity
- **Stage:** 3-formalized
- **Type:** finite-quotient classification / all-orders separation theorem
- **Status:** `[PROVED ON PAPER + LEAN]`

## Claim

Fix an order `k`, an arbitrary complex point `rho`, and `k` distinct positive labels `p_i`.  The
first `k` derivative coefficients of the prime germs

`p_i^(-rho) exp(-log(p_i) X)`

form a basis of the order-`k` local divisor-jet algebra.  More strongly, the one-slot descended
Fitting boundary

`PinnedAffineDefectQuotient k [X^k] -> C[X]/(X^k)`

is bijective.  Consequently every one-slot pinned-affine quotient class has a unique expression as
a linear combination of those `k` prime jets.

This reverses the earlier interpretation of finite-prime independence.  Independence is real, but
it does not distinguish prime data from an archimedean differential functional: every finite jet,
including every finite truncation of the derivation, is uniquely reproduced by a square prime
packet.

The distinction appears only when all orders are required simultaneously.  If a finite packet of
distinct positive prime-log characters agrees at every order with an eventually-zero differential
moment sequence, then both the prime amplitudes and the differential sequence vanish.  Hence the
finite prime sector and the finite-order differential sector have trivial intersection as fixed
all-orders sequences, although their every finite truncation agrees after a unique change of
coefficients.

The failure occurs immediately.  For every `k > 0`, the unique packet matching the derivation
moments in degrees `0,...,k-1` fails in degree `k`.  Indeed, the node polynomial

`Q_k(X)=prod_i (X+log p_i)`

vanishes at every prime frequency `-log p_i`, but `Q_k'(0)>0`.  If the packet also matched degree
`k`, weighted evaluation of `Q_k` would equal coefficient extraction `Q_k'(0)`, forcing the positive
number `Q_k'(0)` to be zero.  No asymptotic or infinite object is needed to locate the first defect.

The defect is computed exactly.  Writing `M_k` for the packet's first omitted moment,

`M_k - delta_(k,1) = -Q_k'(0) < 0`.

Thus every finite interpolation fails with the same real orientation.  Moreover, the order-`k`
packet cannot be extended to order `k+1` merely by appending one coefficient: the zeroth moment
would force the appended coefficient to vanish, leaving the strictly negative order-`k` defect
unrepaired.  At least one previously chosen coefficient must change.

## Proof

For frequencies `f_i=-log(p_i)` and nonzero weights `w_i=p_i^(-rho)`, the first `k` moments are the
weighted Vandermonde map

`a -> (sum_i a_i w_i f_i^j)_(j<k)`.

Distinct positive labels give distinct `f_i`, and every `w_i` is nonzero.  Vandermonde injectivity
and equal finite dimensions give a unique preimage for every coefficient vector.  Passing from
coefficient vectors to `C[X]/(X^k)` proves finite-jet bijectivity.

For the one-slot presentation, a matrix is one polynomial.  The commutator part of a pinned-affine
defect vanishes, while the remaining source, target, and local-ideal corrections are exactly the
multiples of `X^k`.  Thus the kernel of the descended Fitting boundary is precisely the subgroup
already divided out, and the boundary is bijective.

For all-orders separation, suppose the differential sequence vanishes from degree `d` onward.
The `k` equations in degrees `d,...,d+k-1` are a Vandermonde system for the rescaled amplitudes
`a_i f_i^d`.  All `f_i` are nonzero for labels greater than one, so every `a_i` vanishes.  The full
equality then forces the differential sequence itself to vanish.

## Attack and verdict

- `[BRIDGE]` Weighted Vandermonde bijectivity is standard finite-dimensional algebra.
- `[PROVED NATIVE CLASSIFICATION]` The pinned-affine subgroup is proved to be exactly the kernel of
  the one-slot Fitting boundary, so the new universal quotient is completely classified in this
  model.
- `[FALSIFIED ROUTE]` No fixed finite-order pinned-affine quotient can separate a prime source from
  an archimedean differential source.  Every target jet has a unique prime realization.
- `[PROVED FIXED CONSTRAINT]` Simultaneous compatibility at all orders restores separation: finite
  prime-exponential sequences and eventually-zero differential sequences intersect only at zero.
- `[PROVED SHARP BOUNDARY]` A square packet succeeds through exactly the finite quotient it spans
  and necessarily fails at the first omitted order.  The obstruction does not require the prime
  labels to be distinct; distinctness is needed only for uniqueness below the boundary.
- `[PROVED ORIENTATION]` The first omitted-order defect is the negative positive number
  `-Q_k'(0)`, not merely a nonzero complex scalar.
- `[PROVED INCOHERENCE]` Consecutive finite interpolants cannot be compatible under the natural
  restriction that forgets the new prime coordinate.
- `[NO FLOW]` The separating datum is one all-orders equality, not a cutoff family, limit, carrier,
  evolution parameter, or propagation rule.

## Formal theorem surface

- `oneSlotPolynomialDefect` and `fittingBoundaryClass_oneSlotPolynomial_eq` compute arbitrary
  polynomial sources exactly.
- `twoPrimeFirstJetPinnedAffineClass_eq_zero_iff` proves the first nonconstant two-label case.
- `finitePrimeDerivativeJetPinnedAffineClass_eq_zero_iff` proves arbitrary finite-prime
  independence inside the order-`k` quotient.
- `existsUnique_weightedFiniteMoments` proves weighted Vandermonde existence and uniqueness.
- `neg_log_nat_injective` discharges the distinct-frequency Prop from positive injective labels.
- `existsUnique_finitePrimeDerivativeJet_coeff` proves every finite coefficient vector has a unique
  prime-jet realization.
- `existsUnique_finitePrimeDerivativeJet_jetClass` upgrades this to the entire local divisor-jet
  algebra.
- `pinnedAffineBoundaryHom_oneSlot_injective`, `_surjective`, and `_bijective` classify the universal
  one-slot pinned-affine quotient exactly.
- `existsUnique_finitePrimeDerivativeJet_pinnedAffineClass` proves every finite quotient class has a
  unique representation by any fixed square packet of distinct positive prime germs.
- `finitePrimeMoments_eq_eventuallyZero_iff` proves the full all-orders intersection theorem.
- `negativeNodePolynomial_derivative_eval_zero_pos` supplies the positive polynomial witness.
- `no_finitePrimeMoments_eq_archimedeanDerivation_through_card` proves that `k` prime nodes cannot
  match the derivation through degree `k`, without a distinctness hypothesis.
- `finitePrimeDerivationInterpolation_nextOrderDefect_eq` computes the exact signed defect
  `-Q_k'(0)`.
- `finitePrimeDerivationInterpolation_nextOrderDefect_re_neg` proves its real part is strictly
  negative for positive prime labels.
- `no_finitePrimeDerivationInterpolation_coefficientPreserving_extension` proves that a matching
  order-`k` packet cannot be extended by appending a coefficient while preserving the old ones.
- `existsUnique_finitePrimeDerivationInterpolation_with_nextOrderDefect` combines finite
  Vandermonde existence and uniqueness with the exact signed node-polynomial obstruction.
- `no_finitePrimeMoments_eq_archimedeanDerivationMoment` is now a corollary for the derivation moment
  `delta_(n,1)`, rather than an isolated calculation.

The implementation is
`formal/GaloisForLFunctions/RHTower/PinnedAffinePrimeJetRigidity.lean` and is registered in the
`RHTower` umbrella.

## New open core

`[OPEN CORE]` The completed arithmetic datum must supply one coefficient sequence satisfying every
prime--archimedean weld relation simultaneously.  Any argument confined to a finite local quotient
is now proved incapable of distinguishing the two sectors.  More sharply, every separately solved
order-`k` packet acquires a nonzero defect at order `k`; choosing a new packet to repair that defect
must alter old coefficients and is precisely the cutoff-carrier construction forbidden by the
mission.

The next theorem must therefore state an order-independent compatibility law on a single arithmetic
source and show that functional-equation reflection turns its failure into a nonzero pinned-affine
class.  The coefficients must be fixed by the Euler--Gamma datum, not selected from a zero location
or solved anew at each truncation.

## Novelty and significance gates

- **NOVEL:** the new result is not finite Vandermonde algebra alone; it identifies the exact
  pinned-affine one-slot quotient, proves complete prime representability of every finite class, and
  locates the prime/archimedean distinction exclusively in cross-order compatibility.
- **SIGNIFICANT:** this kills the finite-jet attachment route and prevents treating finite-prime
  independence as an RH-facing survivor.  It specifies the minimum structure the next arithmetic
  theorem must use.
- **NON-TAUTOLOGICAL:** no xi zero, critical-line hypothesis, target location, cutoff, or limiting
  object occurs.

## Verification scope

The edited module compiles directly.  Its exact module target and axiom footprint are checked
separately; no root build or project-wide lint is required.
