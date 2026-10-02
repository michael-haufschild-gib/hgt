# SZ actual finite exponential remainder orbit

- ID: sz-finite-exponential-remainder-orbit
- Stage: 3-formalized
- Type: THEOREM (Lean)
- Route: SZ
- RH status: unresolved

## New theorem

Let B_a be the actual bounded Weil remainder and c_a the prescribed
Suzuki interval shift. Every iterate of H_a=B_a/c_a on the odd pole
source p=(p_+-p_-)/2 has a finite truncated-exponential representation
with endpoint budget

    V_n = C0^n * exp(a/2),  C0 = 2*(norm(kappa)+46).

Its L2 Fourier cofunction satisfies, almost everywhere off zero,

    norm(Fourier(H_a^n p)(xi)) <= V_n/(pi*abs(xi)).

For every R>0, the physical Fourier cutoff Q_R therefore satisfies

    norm(H_a^n p - Q_R(H_a^n p))^2 <= 2*V_n^2/(pi^2*R).

These root theorems require no conjectural premise. They concern the
actual complete prime operator, retaining all prime powers and the
terminal floor(exp(2a)) cutoff, and the actual crossed polar operator.
No regularity of the unknown Riesz response is assumed.

## Dependency-closed paper proof

The corpus atom theorem gives endpoint budget and Fourier decay for
z*1_[l,r]*exp(s*x). Inductive constructors record actual L2 zero, atoms,
addition, complex scalar multiplication, and budget enlargement. This
proves the envelope, integrability, and Fourier bound by induction.
Translations preserve the budget exactly. Interval projection intersects
each atom interval and decreases its budget; empty intersections vanish.

For any represented aperture vector of budget V, each pole charge is at
most 2*exp(a/2)*V. The crossed polar operator therefore has budget at most
4*exp(a)*V, with no aperture-length loss. Every prime transport is the
literal pair of projected translations. Their complete coefficient sum
is bounded using primeMassHalf_le_sqrt, giving 42*exp(a)*V. The scalar
term costs at most norm(kappa)*exp(a)*V. Thus B_a costs at most
(norm(kappa)+46)*exp(a)*V.

The audited prescribed-shift theorem exp(a)<=2*c_a cancels this aperture
factor. The odd pole source has budget exp(a/2). Natural-number induction
gives the stated actual orbit and its Fourier envelope.

Integrating the squared envelope on (R,infinity) gives
V_n^2/(pi^2*R). Reflection supplies the negative half-line. The exact
Plancherel cutoff identity joins both integrals and gives the physical
L2 truncation estimate. All iterates are literal L2 vectors, so the
integrability required to join the halves is automatic from their type.

## Verification

Modules: CCMFiniteExponentialRemainderOrbit (eighteen public theorems)
and CCMFiniteExponentialRemainderTail (two public theorems).
Final direct leaf audit35153 used `lake --old env lean <leaf> -o <leaf.olean>`
and exited0, without warnings. Tail scratch11198 and final leaf audit13836
also exited0 without warnings. Both root RHTower umbrella imports added;
no umbrella or full build run. All twenty public theorem axiom queries
passed in scratch52666, reporting only propext, Classical.choice and
Quot.sound. No added axioms or proof placeholders occur.

Post-wiring formal lint66480 exits1 on twelve unrelated unreachable
modules, listed in the SZ working log. Neither new leaf is reported.
Global lint is not green; unrelated work is preserved.

## Remaining hard connection

The full convolution/multiplier/compression identity and one-step actual
source norm estimate are now proved in P3:sz-actual-remainder-source-contraction.
That estimate must be iterated a growing number of times before the actual
Riesz equation yields bounded odd source energy. Signed Wronskian control,
shift removal, canonical normalization and RH remain unresolved.
