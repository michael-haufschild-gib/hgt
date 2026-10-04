# TG C9.19a: critical arithmetic selection and the exact boundedness boundary

- **Stage:** 3-formalized
- **Route:** TG, actual signed arithmetic covariance
- **Original target:** unconditional Summable soninPrimePolarGridEnergy and RH completion
- **Candidate under test:** obtain a bounded physical selector from the exact LCM-idempotent arithmetic jet, then use it to control the polar-centered covariance.

## Corpus basis and fidelity

C9.12 proves the literal jet's complete LCM self-convolution is its negative,
and identifies the full two-coordinate incidence kernel. C9.11/C9.12 give
actual physical ground vectors B_n=soninGroundEntry a(log(n+2)) with
<B_i,B_j>=2a/max(i+2,j+2), not the Dirichlet divisor-overlap measure.
The fresh native-cancellation and jet-contraction deep searches are
nonpartial snapshots. Their source arguments give weighted covariance
identities and different-carrier orthogonality, but no bound for TG's native
energy. The prime-selection search was checked before Lean work.
No numerical experiments are used.

## Failure of the universal contraction and sharp survivor

For a>0 let D_n=B_n-B_(n+1). Literal covariance gives
 ||B_n||^2=2a/(n+2), ||D_n||^2=2a/((n+2)(n+3)).
Suppose a bounded linear T selects B_n according to a binary mask m(n).
Whenever the mask changes at n, T D_n is B_n or -B_(n+1). Consequently
 ||T||^2 >= n+2.
An infinitely changing mask therefore cannot have a bounded physical
extension. This concerns a proposed universal selection method, not the
specific native prime-polar discrepancy or its energy summability.

The strongest positive survivor is a complete boundedness classification:
there exists such a bounded T exactly when m is eventually constant.
Necessity is the preceding annular argument. For sufficiency set
 v_n=D_n/||D_n||^2. The exact physical pairing is
 <v_n,B_j>=1 for j<=n and 0 for j>n.
Thus the continuous coordinate functionals
 ell_0=<v_0,->, ell_n=<v_n-v_(n-1),-> (n>0)
satisfy ell_n(B_j)=delta_(n,j). If m is constant with value c past N,
 T=c I + sum_(n<N) (m(n)-c) B_n ell_n
is an explicit bounded finite-rank perturbation of c I that retains every
original ground vector. This proves the converse without changing carrier.

The actual prime mask changes at every odd prime p and its following even
composite p+1. Infinitely many primes force no bounded prime selector on
this physical grid. A fixed polar subtraction cannot repair a universal
linear Lipschitz estimate, since it cancels in source differences. This
last observation does not reject source-specific arithmetic cancellation.

## Frontier consequence

Do not substitute LCM algebraic idempotence, complete-period orthogonality,
or Dirichlet-measure prime independence for boundedness on the actual TG
carrier. The original single prime-polar source still needs its own signed
cross-label cancellation. No RH proof, energy bound, or route retirement
is claimed by this classification.

## Additional sharp boundary and arithmetic specialization

Contractive selection is possible exactly for masks constant on the entire
grid: any switch forces norm squared at least n+2, exceeding one. The zero
and identity maps realize both constant masks.

The prime-power mask actually exposed by the jet's divisor transform is
also excluded. Every tail contains a prime, and every tail contains a
multiple of six with two distinct prime factors. Thus that mask is not
eventually constant. This uses genuine arithmetic, not a surrogate mask.

## Verification

Closed 2026-10-04 in SoninGroundGridArithmeticSelection.lean. The final
production command lake --old env lean GaloisForLFunctions/RHTower/
SoninGroundGridArithmeticSelection.lean -o the corresponding .olean exits0
with empty diagnostics. All twelve public declarations have exactly
propext, Classical.choice and Quot.sound as foundations; no added axioms,
holes, numerical experiments or heartbeat increases. Umbrella wired;
index exits0 and all twelve public names are present. Global lint exits1
on fourteen unrelated unreachable modules, with no finding in this leaf.
Logs: /tmp/tg-c919-final.log, -axioms.log, -index.log, -lint.log.

Deep searches tg-c919-native-cancellation, tg-c919-jet-contraction and
tg-c919-selection are nonpartial source snapshots. Compiler refresh was
incomplete because the background indexer was running. Candidate lemmas,
source arguments and proposed ingredients were inspected; applicability
was resolved in Lean. No matching classification was found in these hits;
this is not an exhaustive novelty claim.

The universal LCM-to-physical-contraction candidate is retired in P5
(tg-universal-arithmetic-selector-contraction). TG and actual source energy
summability remain open. This result narrows the allowed mechanism; it
supplies no arithmetic energy bound.
