# Exact conditional centering and compensated interior progression bounds

- **ID:** BVI-INTERIOR-ORBIT-2026-10-18
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Problem 4 of `docs/reports/walls/bezout-wall1-programme.md`
- **Statement:** Classify the conditional mean of the two-endpoint-deleted interior sawtooth and bound its centered finite progression sums uniformly in both horizons.

## Mathematical statement

For positive integers d,e, put g=gcd(d,e), m=e/g and

    psi_e(n) = (n mod e)/e - (e-1)/(2e),
    J_e(n) = -psi_e(n) if e divides neither n nor n+1, and 0 otherwise,
    gamma(d,e) = 0 if g=1, and (e-g)/(2e^2) otherwise.

Then

    sum_{k<m} J_e(d-1+dk) = m gamma(d,e),
    0 <= gamma(d,e) <= 1/(2e),
    gamma(d,e)=0 iff g=1 or g=e.

For every integer a>=2, gamma(a,2a)=1/(8a)>0. In particular, deleting both
endpoint residues does not imply conditional mean zero.

For every finite L,T>=0, define

    w_{d,T}(k) = max(1/(d(k+1))-1/(T+1),0).

The centered prefix, harmonic, and compensated bounds are

    |sum_{k<L} (J_e(d-1+dk)-gamma(d,e))| <= m,
    |sum_{k<L} (J_e(d-1+dk)-gamma(d,e))/(d(k+1))| <= m/d,
    |sum_{k<L} w_{d,T}(k)(J_e(d-1+dk)-gamma(d,e))| <= m/d.

Finally, for every cutoff N and arbitrary real weights c, write

    Gamma_N,c(d) = sum_{1<=e<=N} c(e) gamma(d,e).

The literal existing BVI observable satisfies

    |sum_{k<L} w_{d,T}(k)
        (bezoutInteriorSawtoothSum N c (d-1+dk) - Gamma_N,c(d))|
      <= (1/d) sum_{1<=e<=N} |c(e)| (e/gcd(d,e)).

Every displayed bound holds at finite horizons; no full-period averaging
assumption is imposed on L or T. Positivity of the two input moduli is encoded
by `PNat` in the public Lean interface. No analytic input is assumed.

## Dependency-closed paper proof

**[PROVED HERE]** The progression residues modulo e form the fiber
g-1+gj, 0<=j<m. To see this, divide d and e by g; the reduced stride is
coprime to m, so multiplication by it, followed by translation, permutes
the residues modulo m.

The average of psi_e over this fiber is (g-1)/(2e). The successor endpoint
e-1 occurs exactly once, with psi_e=(e-1)/(2e). The predecessor endpoint
0 occurs exactly when g=1, with the opposite value. Deleting these endpoints
and negating the sawtooth gives zero when g=1, and

    -(g-1)/(2e) + (1/m)(e-1)/(2e) = (e-g)/(2e^2)

otherwise. This proves the mean, its bounds, and the complete zero
classification. Setting e=2d gives the positive doubled-modulus family.

The centered sequence has period m and zero sum on each complete period.
The sawtooth bound |psi_e|<1/2 gives |J_e-gamma|<=1. Removing all complete
periods from a finite prefix leaves fewer than m terms, proving its bound.

Abel summation against a nonnegative antitone weight w bounds the absolute
weighted sum by m*w(0). Both reciprocal and compensated weights have
w(0)<=1/d. This proves both horizon-independent estimates. The final
finite-cutoff theorem follows by the exact atom decomposition of
`bezoutInteriorSawtoothSum`, exchanging finite sums, and the triangle
inequality. All coefficient dependence is retained explicitly.

## Scope and research consequence

The finite fractional-atom gcd orbit mean is existing infrastructure:
`RHTower.cycleAverage_fracAtom` in `CausalMobiusThetaUniformCycle.lean`.
No novelty claim is made for residue permutations, general periodic
centering, or Abel summation. The audited object here is the actual
two-endpoint-deleted BVI interior atom and its finite compensated bound.
Corpus search found the prior infrastructure; semantic search had partial
coverage on the broader conditional-mean query. No global novelty claim.

Prime interior moduli always have zero conditional mean: their gcd with
the jump modulus is either one or the full modulus. The correction is
supported precisely on proper shared factors of composite interior moduli.
For actual weights mu(e)e^(-epsilon), the mean correction gains a reciprocal
power and is absolutely summable in e for every positive epsilon.

The error bound still grows with the divisor cutoff. It does **not** prove
problem 4's strict contraction, nor boundedness of the horizon-free interior
martingale. That prefix also has a separate affine correction, as established
in `pmBezoutInteriorPrefix_sub_bezoutInteriorSawtoothSum_eq_affine`.

## Lean certificate and verification

Module: `formal/GaloisForLFunctions/BezoutValuationIncidence/InteriorJumpOrbitCenteringAndCompensatedBounds.lean`.
Fourteen public declarations cover definitions, exact orbit mean, mean
bounds/classification, positive overlap family, prefix/harmonic/compensated
estimates, and the existing-observable bridge.

- Original-source `lake --old env lean -j 1` audit: session 44502, exit 0, no diagnostics. Fresh `.olean` and `.ilean` emitted from the original named module.
- Source diagnostics: `logs/bvi-interior-orbit-2026-10-18-source.txt`.
- All fourteen public declarations audited in session 87987, exit 0: exactly `propext`, `Classical.choice`, `Quot.sound`. Raw output: `logs/bvi-interior-orbit-2026-10-18-axioms.txt`.
- Source SHA-256: `a9c13b9d5842db83bf4b1784f9fd85331239c5ab71a07df7d1a2513e8571e961`.
- Umbrella import added; index session 96489 passed; owned whitespace check passed.
- Formal lint session 97873 exited 1. No finding names this leaf. Six unrelated findings concern concurrent CHMD leaves, two other BVI leaves, and the existing root `TransHorizonIncidenceMechanics.lean` placement. Full raw output: `logs/bvi-interior-orbit-2026-10-18-lint.txt`. Global lint is not claimed clean.
- Final index refresh and `lint --check-generated` ran sequentially in session 7780. Index passed; final lint retains the same six unrelated findings, with no generated-file freshness error. Evidence: `logs/bvi-interior-orbit-2026-10-18-final-index.txt` and `logs/bvi-interior-orbit-2026-10-18-final-lint.txt`.
- Final manifest verifies the source hash, fresh artifacts, all fourteen axiom closures, and exactly one umbrella import. Ten temporary files removed after archive; no owned process remains. Manifest: `logs/bvi-interior-orbit-2026-10-18-manifest.json`.

## Log

- 2026-10-18 — Paper proof closed; source assembled after scratch elaboration.
- 2026-10-18 — Original-source and all public axiom audits passed; promoted to stage 3. Full contraction remains on its separate in-progress card.
