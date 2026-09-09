# SQB common theta forcing: native Gram reduction

Scratch, final source, named-leaf build, all 23 public-declaration axiom checks,
and formal lint passed. RH and normalized native occurrence remain unproved.

Lean module:
`formal/GaloisForLFunctions/RHTower/SelbergThetaCommonForcingGram.lean`.

## Mathematical result

Let A be the original native energy operator, and let

    U_q = centeredDomain(q),
    e_q = energy(q),
    F   = -(1/4) centered(nativePositive).

The already proved source equation is `A U_q=e_q U_q+F`. All vectors and images
below belong to the original native Hilbert space and operator graph. Define

    G(q,r) = <U_q,U_r>,
    m(q)   = <F,U_q>,
    B      = <F,F> = ||F||^2.

The complex inner product is conjugate-linear in its first argument. The new
unconditional native displacement identity is

    (e_r-conj(e_q)) G(q,r) = m(r)-conj(m(q)).                 (1)

Consequently, away from reflected energy collisions, the complete two-parameter
Gram entry is the divided difference on the right of (1). At a collision,
`e_r=conj(e_q)` implies `m(r)=conj(m(q))`; no division or confluent value is assumed.

The other blocks of the native augmented Gram are

    <U_q,A U_r>     = e_r G(q,r)+conj(m(q)),
    <A U_q,U_r>     = conj(e_q) G(q,r)+m(r),
    <A U_q,A U_r>   = conj(e_q)e_r G(q,r)
                     +conj(e_q)conj(m(q))+e_r m(r)+B.        (2)

In particular, the diagonal gives the exact source-flux identity

    Im m(q) = Im e_q ||U_q||^2.                             (3)

For any complex target z, put `R_z(q)=(A-z)U_q` and `d_q=e_q-z`. Its full Gram is

    <R_z(q),R_z(r)> = conj(d_q)d_r G(q,r)
                     +conj(d_q)conj(m(q))+d_r m(r)+B.        (4)

All source cross terms in (2) and (4) are retained.

For every finite index type, actual Xi copies q_i, and complex coefficients c_i,
the domain packet `V=sum_i c_i U_(q_i)` is constructed in the original operator
domain. Lean proves both exact energies:

    ||V||^2       = Re sum_(i,j) conj(c_i)c_j G(q_i,q_j),
    ||(A-z)V||^2  = Re sum_(i,j) conj(c_i)c_j <R_z(q_i),R_z(q_j)>.

Thus numerator and denominator of the normalized residual are measured in the
same native norm. Positivity of the denominator and a sequence driving their ratio
to zero are not asserted.

## Proof

Self-adjointness gives `<A U_q,U_r>=<U_q,A U_r>`. Substituting the existing common
forcing equation into both sides proves (1). Substitution into one or both slots
gives (2), and taking the imaginary diagonal part of (1) proves (3). Subtracting
the arbitrary target gives `R_z(q)=d_q U_q+F`, whose sesquilinear expansion is (4).
Linearity on the actual operator domain and finite sesquilinear expansion prove
the two packet formulas. No numerical input, extra axiom, or source-domain premise
enters these proofs.

## Consequence for the remaining mathematical task

For noncolliding energies, comparing the native augmented Gram with a proposed
source model now reduces to comparing one-variable source-pairing values m, the
fixed forcing mass B, and the energies. This is an actual reduction for the
constructed theta responses, not an abstract equal-Gram assumption.

The unresolved arithmetic calculation is m(q), or an estimate on the resulting
finite quadratic forms strong enough to produce vanishing normalized residuals.
The scalar pairing is not shown real. The centered responses are not shown
nonzero by this module. At reflected collisions (1) supplies compatibility, not
the missing Gram value. No occurrence or RH conclusion follows yet.

## Audit

- Scratch: `lake env lean /tmp/sqb38_common_gram.lean` passed.
- Final source: `lake env lean GaloisForLFunctions/RHTower/SelbergThetaCommonForcingGram.lean`
  passed without warnings; `/tmp/sqb38_source_check.log`.
- Preflight: only the named new leaf required rebuilding; `/tmp/sqb38_preflight.log`.
- Final named leaf: `lake build GaloisForLFunctions.RHTower.SelbergThetaCommonForcingGram --old`
  passed; `/tmp/sqb38_leaf_build.log`.
- Public axiom audit: `lake env lean /tmp/sqb38_axioms.lean` passed, exit 0;
  all 23 public definitions and theorems use only `propext`, `Classical.choice`,
  and `Quot.sound`. Log: `/tmp/sqb38_axioms.log`.
- Generated indexes refreshed and `scripts/formal_tools.py lint` passed;
  `/tmp/sqb38_index.log` and `/tmp/sqb38_lint.log`.
- Umbrella: imported once into `GaloisForLFunctions/RHTower.lean`; no umbrella build.
- Frontier map and universal-law ledger: unchanged by this work.
