# Universal relative centering fails on a residue matching

- **ID:** twin-prime-universal-relative-centering
- **Stage:** 5-failed
- **Type:** FALSIFIED; positive survivor fully formalized
- **Source:** [fixed-determinant uniformity](../1-in-progress/twin-prime-fixed-determinant-uniformity.md).
- **Statement:** The ambient-horizon rough-shift centering theorem cannot retain arbitrary bounded second rows and its claimed saving after normalization by the progression sample count.

## Exact failed claim

Replace `1/Y` by `l/Y` in the
[coupled-centering statement](../2-fully-proven/twin-prime-coupled-residue-centering.md),
keeping the `O_h(L^(-21/20))` error uniform in the modulus and every
unit-bounded second row. The claim already fails for the actual
Liouville first row, `h=4`, residue `r(z)=cz`, and all shift weights one.
This does not refute either two-actual-row affine cancellation conjecture.

## Exact killing mechanism

Take `a=4D+6`, `c=4D+2`, `l=ac`, `Y=l(K+1)`, and prime shifts
`D<p<=floor(6D/5)`. The frame `(a,1;c,1)` is primitive, reduced,
and has determinant four. The bounded row

`g_D(w)=lambda(w-4 floor((w mod l)/a))`

recovers the input Liouville sign on every selected edge:
`v mod l=cp` implies `(v+4p) mod l=ap` and
`lambda(v)g_D(v+4p)=1`.

The selected incidence is a partial matching. Each prime selects
exactly `K+1` input points. Therefore its relative correlation is
exactly `sum_p 1/p`, eventually at least `1/(20 log(2D))`.
Take `D=ceil(exp L)` and choose `K` large enough for the required
long-horizon condition. All shifts satisfy the required roughness,
while the relative mass is of order at least `1/L`, contradicting
the proposed `L^(-21/20)` bound. The same example allows the slopes
to be smaller than any fixed positive power of `Y/l` by increasing `K`.

## Strongest positive survivor

The [exact matching norm and prime-mass bound](../3-formalized/twin-prime-residue-matching-boundary.md)
prove both sides: every unit-bounded second row has absolute correlation
at most `(K+1) sum_p 1/p`, and the explicit row attains equality for
every `K`. The normalized value is independent of the horizon.
It is not `o(1/log(2D))` along any horizon schedule.

**New insight for this route:** retaining the determinant and progression
normalization is not sufficient if the second arithmetic row is replaced
by an arbitrary bounded function. Separated residue classes give that
function enough freedom to erase all cancellation. A successful relative
estimate must retain additional information about both actual rows or
use a shift regime that supplies the missing overlap.

**Paper/Lean status:** dependency-closed paper proof; six unconditional
capstones in `twin-prime/SemiprimeEnergy.lean`; leaf check passed;
all transitive axiom audits contain only `propext`, `Classical.choice`,
and `Quot.sound`. No analytic premise or limit increase was introduced.

**Novelty:** classical matching geometry and a proved PNT consequence;
no new number-theoretic knowledge claimed. The existing ambient-normalized
centering result, the actual-row conjectures, and the twin-prime goal
are unaffected by this rejection.

## Log

- 2026-10-23 — Closed only the universal relative-centering route,
  with its exact sharp positive survivor and full Lean audit.
