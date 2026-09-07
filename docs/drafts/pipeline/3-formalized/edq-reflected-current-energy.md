# EDQ reflected current as positive prefix energy

Stage: 3-formalized; dependency-closed paper proof and Lean verified.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH.
RH status: the real current has the exact orientation below. Its annihilation at every zero is not established.

Write r(s)=1-conjugate(s), alpha=2*Re(s)-1, and w_n=(n+1)^alpha. For the literal
modulus-p+1 jumps u_n at s, the reflected jumps are exactly v_n=w_n*u_n. Let
X_N=sum_(n<N)u_n and Y_N=sum_(n<N)v_n. For arbitrary real weights and complex jumps,
put Z_N=w_N*X_N-Y_N. Then

`Z_(n+1)-Z_n=(w_(n+1)-w_n)*X_(n+1)`.

Finite summation by parts, without any zero premise, therefore gives the full complex identity

`C(u,v,N)-C(v,u,N)=w_N*norm(X_N)^2-Y_N*conjugate(X_N)`
`                         -sum_(n<N)(w_(n+1)-w_n)*norm(X_(n+1))^2`.

No imaginary part or diagonal term has been dropped. At an actual nontrivial zero s,
the corpus bounds norm(X_N) by A_p(s)*(N+1)^(-Re(s)); hence the first terminal norm is at
most A_p(s)^2/(N+1). Both ordinary endpoints tend to zero. The previous variation-current
identity then identifies the full reflected arithmetic current with the real prefix-energy limit.

For alpha>0 the weights strictly increase, for alpha<0 they strictly decrease, and for
alpha=0 they are constant. Each squared prefix norm is nonnegative. For every actual
nontrivial modulus (p>0), X_1=1. Therefore the first energy term is exactly 2^alpha-1,
strictly positive or negative with alpha. All further terms have the same weak sign.
The terms have one sign, so convergence of their partial sums proves genuine summability.
The full complex current is exactly the real sum of these terms. Consequently it is real at zeros,
has the sign of Re(s)-1/2, and vanishes exactly on
the critical line. Its positive survivor is the literal source energy, not an assumed Hilbert model.

This does not establish that the full current vanishes at every zero. The imaginary endpoint
equation already proved only gives its imaginary part. An additional source identity or
comparison forcing the real energy to vanish is still necessary for RH. Functional-equation
covariance exchanges partners and reverses the current; it does not identify the two values.

Corpus inspected: EulerDeletionReflectedChronologicalCurrent, EulerDeletionQuasiShuffleSecondConvergence,
EulerDeletionQuasiShuffleSecondShadow, EulerDeletionReflectedLogarithmicGram, DirichletAbel.
The broader searches located SuzukiInverseNeumannLaplacian's prefix Gram and
RouteRBurnolReflectionPartnerCurrent's reciprocal orientation; their different source definitions
are not substituted for the literal deletion current.

The quantitative right-half floor is `2^(2*Re(s)-1)-1 <= Re(J_p(s))`; on the left half
the same expression is an upper bound. Both are strict in sign away from the line. For the
literal modulus-two channel (p=1), Lean identifies Mathlib's RiemannHypothesis exactly with
`forall rho : NontrivialZetaZero, reflectionCurrent 1 rho = 0`. This is a proved equivalence,
not a proof of the required universal vanishing statement.


## Formal certificate

Leaf: `formal/GaloisForLFunctions/RHTower/EulerDeletionReflectedCurrentEnergy.lean`
(274 lines; 17 public theorems, three public definitions, five private lemmas).
Namespace: `RHTower.DeletionReflectedEnergy`.

- `weighted_cross_identity`: arbitrary real weights and complex jumps, with the full complex boundary and prefix energy.
- `reflected_jump_eq_weight`, `source_energy_identity`: literal reflected arithmetic jumps and every finite source cutoff.
- `weighted_endpoint_bound`, `weighted_endpoint_tendsto`, `energy_tendsto_at_nontrivial_zero`: explicit inverse-linear amplified-endpoint bound and full complex energy limit at every actual nontrivial zero.
- `energyTerm_nonneg`, `energyTerm_nonpos`, `energyTerm_zero`: orientation of every term and exact nontrivial first prefix.
- `hasSum_energy_at_nontrivial_zero`, `reflectionCurrent_eq_energy`: genuine summability and the full complex current as a real signed source energy.
- `first_energy_le_current`, `current_le_first_energy`: quantitative first-step floor and ceiling.
- `current_re_pos_of_right`, `current_re_neg_of_left`, `reflectionCurrent_eq_zero_iff`: strict signs and exact critical-line characterization at every nontrivial zero.
- `riemannHypothesis_iff_modulus_two_current_zero`: the literal modulus-two current-vanishing condition is equivalent to Mathlib's original RH proposition.

Final scratch: `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_energy.lean`, exit 0, no diagnostics.
Final leaf audit: `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionReflectedCurrentEnergy`, exit 0. Only the new leaf rebuilt (4.2 seconds); dependencies cached/replayed. Umbrella import added; no full or umbrella build.
New-only axiom audit: `lake env lean /tmp/edq_energy_axioms.lean`, exit 0. All 20 public declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`; private lemmas are covered by that dependency closure. No added axioms, admissions, numerical premises, or external computation certificates.

Repository `scripts/formal_tools.py lint` ran once and passed, with existing file-size warnings.
The search index was refreshed once. Owned scratch Lean sources were removed after verification.
Logs remain under `/tmp/edq_energy` with `.api.log`, `.check.log`, `.build.log`, `.axioms.log`,
`.lint.log`, and `.index.log` suffixes. Scoped whitespace, links, exact wiring, and owned-process
checks passed.

RH remains unproved and unfalsified. The new positive survivor is the exact oriented source
energy. Its universal annihilation remains open; no reflection-covariance argument is silently
used to equate opposite current values. No route is retired.
