# Global rational orbit preservers are Laurent Adams maps

- **ID:** alst-global-rational-orbit-preservers-are-laurent-adams
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** Let `N_p,D_p : MvPolynomial Nat.Primes ℂ` be a rational coordinate family defined on the whole prime orbit and preserving it. No common finite invariant prime set is assumed. Then there are unique `n∈ℤ`, `b∈ℝ` with `N_p X_p^{(-n).toNat}=C(p^(−ib)) D_p X_p^{n.toNat}` for every prime `p`. Real or integer coefficients force `b=0`.

## Research consequence
The finite-prime classification does not address maps whose successive
coordinates introduce new primes. This would classify rational orbit
preservers in the full prime-variable algebra and eliminate that escape.

## Proposed mechanism
Each coordinate polynomial still has finite support. The logarithmic-residue
and entire-quotient arguments should therefore give a character in every
coordinate, with frequency an integer combination of finitely many prime
logarithms. Two output primes determine a common affine clock `t↦at+b`.
Thus `exp(a log p)` is rational for every prime `p`.

Three distinct output primes and the six-exponentials theorem force `a`
to be algebraic: if it were transcendental, `(1,a)` and the three prime
logarithms would satisfy the independence hypotheses, while all six
exponentials would be algebraic. Baker independence, applied separately to
the finite frequency support of each coordinate together with its output
prime, then forces `a` to be an integer and all off-prime exponents to vanish.
This replaces the finite-generation determinant trick.

## Corpus leads and gaps
- `SixExponentials.six_exponentials` and `SixExponentials.prime_logs_independent` provide the transcendence and independence inputs. The existing prime-power corollary handles nonreal exponents; a real transcendental clock needs a separate application.
- `RHTower.exp_primeLog_comb_eq_rat` exponentiates a finitely supported integer prime-log combination to a rational number.
- `Core.log_prime_nat_relation_eq` supplies frequency injectivity for polynomials in all prime variables.
- The local logarithmic and entire-quotient lemmas of the finite rational classification have no finite-prime-set premise.
- `MvPolynomial.exists_rename_eq_of_vars_subset_range` reduces each finite collection of global polynomials to one finite variable set. It can transfer the existing orbit evaluation, Bohr recovery, and entire-growth lemmas without assuming that set is invariant under the map.

Input axiom audits, the global frequency interface, the scalar theorem, and
classification assembly remain. No result from this card is proved or counted.
