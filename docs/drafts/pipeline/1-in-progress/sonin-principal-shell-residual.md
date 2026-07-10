# Sonin principal-shell residual

- **ID:** sonin-principal-shell-residual
- **Stage:** 1-in-progress
- **Type:** BRIDGE / CONJECTURAL RH ROUTE
- **Lean target:** `formal/GaloisForLFunctions/RHTower/SoninPrincipalShellResidual.lean`

## Statement

Let `Q_a` be the orthogonal projection onto the even physical-and-Fourier Sonin carrier and

`L_(a,p) = (1-Q_a)(U_p+U_p^(-1))Q_a`, `a>0`, `p>1`.

The canonical principal shell of the positive Gram operator `L_(a,p)^* L_(a,p)` is

`Sigma_(a,p) = (A_(pa)-A_a) + (R_(pa)-R_a)`,

the sum of its physical and Fourier cutoff shells. Define the principal-shell residual

`K_(a,p) = L_(a,p)^* L_(a,p) - Sigma_(a,p)`.

`[PROVED IN LEAN]` The existing exact Calkin shell law implies that `K_(a,p)` is compact. Both
terms are self-adjoint, hence `K_(a,p)` is self-adjoint. Consequently

`T_(a,p) = K_(a,p)^* K_(a,p) = K_(a,p)^2`

is a positive compact source operator.

## Schatten strengthening

`[PROVED ON PAPER; LEAN INFRASTRUCTURE OPEN]` The resolvent proof of the Sonin projection formula
contains a stronger ideal statement. The projection correction

`C_a = Q_a-(1-A_a-R_a)`

is a finite sum of bounded two-sided multiples of the mixed finite time-band blocks `A_a R_a`
and `R_a A_a`. These blocks are Hilbert--Schmidt integral operators: after Fourier conjugation
their kernels are the bounded Fourier kernel restricted to a finite rectangle. The
Hilbert--Schmidt ideal is two-sided, so `C_a` is Hilbert--Schmidt. Expanding every replacement of
`Q_a` by `1-A_a-R_a` in the Gram-shell calculation shows that `K_(a,p)` is Hilbert--Schmidt.
Therefore `T_(a,p)=K_(a,p)^*K_(a,p)` is trace class.

Mathlib does not currently expose general Hilbert--Schmidt or trace-class predicates for
continuous operators on arbitrary Hilbert spaces. The repository's `HilbertSchmidt.lean` treats
countable matrix kernels only. The remaining formalization obligation is therefore substantive:
construct the integral-kernel Hilbert--Schmidt ideal for the actual `L^2` operators and prove its
two-sided ideal and product-to-trace-class laws.

## All-prime assembly

`[CONJECTURE]` The all-prime object must begin after removal of the linear prime shell. The raw
positive Euler coefficient is `p^(-1/2)`, whose squared prime energy is `sum_p 1/p` and diverges,
exactly as the formal finite-family Calkin lower bound proves. The regularized prime-power tail

`{(p,k) : p prime, k>=2}`, with weight `p^(-k/2)`,

has square energy `sum_p sum_(k>=2) p^(-k)<infinity`. This is the operator-ideal counterpart of
the `det_2` cancellation of the linear Euler term. A viable all-prime Sonin residual should be a
Hilbert direct sum or convergent Hilbert--Schmidt series of the `K_(a,p)` weighted over this
prime-power tail, not the divergent raw sum over primes.

## RH interface

`[OPEN CORE]` Construct the source-built positive trace-class operator `T_Sonin`, then prove

`Tr(T_Sonin p(T_Sonin)^2) = Re(xiCentralTraceHankel p)`

for every real polynomial `p`. The existing Lean theorem
`xiCentralTraceHankelNonnegative_iff_riemannHypothesis` would then yield RH. No zero divisor may
be used in the construction of `T_Sonin`.

## Gates

- [x] Canonical principal shell and residual isolated.
- [x] Compactness, self-adjointness, and positivity of the squared residual formalized.
- [ ] General `L^2` Hilbert--Schmidt operator ideal formalized; residual certified in it.
- [ ] Regularized all-prime prime-power assembly constructed.
- [ ] Trace moments identified with `xiCentralTraceHankel` from source data.
- [ ] Regularized determinant or resolvent trace identified with Xi.

## Classification

- `[BRIDGE]` Compact/self-adjoint residual packaging follows directly from the existing Calkin
  shell theorem.
- `[SEARCH]` Finite-rectangle Fourier kernels are Hilbert--Schmidt and products of two
  Hilbert--Schmidt operators are trace class.
- `[NOVELTY UNVERIFIED]` The source-defined principal-shell subtraction, its prime-power
  regularization, and any Xi trace identification require a full parent-theory and literature
  audit after proof.
