# Route L: actual Burnol reciprocal-window incidence

- **ID:** L-C33
- **Date:** 2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM; actual source/reader comparison
- **Depends on:** [C32](../3-formalized/route-l-complete-transgression-physical-balance.md)
- **RH status:** unproved

The chain is complete original source → cyclic/fixed physical reader
agreement → original conormal vanishing → RH. C32 shows why a fixed
source does not force its complete distributional boundary to vanish:
the retained Gaussian has a nonzero anti-Fourier boundary. The missing
physical reader has not been identified with the annihilated tests.

## Actual incidence candidate

The existing Burnol sub-window source is a concrete even L²/Sonin
vector. Fourier transform sends it to the co-Poisson vector of the
reciprocal seed. For a window `[c,d]`, that seed is the indicator on
`[d^-1,c^-1]`, whereas the original seed is the reciprocal function on
`[c,d]`. The completed Mellin evaluations and the first nonzero Xi
conormal jets must be compared for these actual two vectors, with the
same divisor, aperture and multiplicity retained.

Conjecture to test: the actual Fourier pairing, including both window
ends and their nonzero conormal factors, supplies the unchanged-anchor
physical reciprocity missing from the abstract cyclic reader. Derive
the reciprocal vector's exact Mellin germ before inferring any equality.
An equation that only transports evaluation to `1-rho` or `1-conj(rho)`
is not yet agreement at the original point.

The existing reflection cover already retains invariant orbit sum,
unit-norm product and invariant squared character difference. The last
quantity is zero exactly on the critical line. Passing to invariant
data cannot be used as a proof that the original characters merge.

## Research and proof loop

Search actual reciprocal-window/Mellin pairing and source-adjunction
methods throughout the corpus. Broad recent arXiv probes start with
reciprocity and sewing. Test a complete paper argument against the
actual source definitions before new Lean. If the proposed pairing
only transports the conormal, identify and prove its strongest exact
positive comparison and use the remaining term to choose the next
source-balance conjecture.

## Exact comparison obtained from the literal seed

For `L>0`, set `f_L` to the existing original Sonin window vector on
`[exp(-L),1]`. Its Fourier image is the actual co-Poisson vector of the
indicator on `[1,exp(L)]`. The general co-Poisson Mellin theorem gives
the latter's uncompleted germ

`V_L(w) = zeta(w) (exp(L(1-w))-1)/(1-w)`.

The required absolute Mellin integrability on `0<Re(w)<1` follows by
splitting at one: the existing indicator-window decay profile bounds
the near part by `C t^(-Re(w))` and the far part by
`C t^(-Re(w)-1)`. The seed integral itself is the elementary integral of
`u^(-w)` on `[1,exp(L)]`. Both the general co-Poisson identity and the
special `[1,2]` version already exist in the corpus; only the exact
arbitrary-window application and its source/jet comparison are needed.

At each actual Xi divisor `rho`, with its exact multiplicity `m`,
Leibniz and the vanishing lower zeta jets leave

`V_L^(m)(rho) = (exp(L(1-rho))-1) zeta^(m)(rho)/(1-rho)`.

This coefficient is nonzero. The actual doubled-window jet quotient,
minus one, is therefore `exp(L(1-rho))`. The original source quotient
is already `exp(L rho)`. Half-density centering gives inverse
characters at the same original divisor, not equal characters. Their
squared-norm difference reproduces the fixed physical conormal radial
defect. Writing `G` for the Gamma completion, the literal completed
leading jets are

`J_L = G(rho) zeta^(m)(rho) (exp(L rho)-1)/rho`,

`K_L = G(rho) zeta^(m)(rho) (exp(L(1-rho))-1)/(1-rho)`.

Both are nonzero. The same original zeta jet and Gamma factor cancel
from their respective doubled-window quotients. No reflection of the
zeta argument is used to obtain the reciprocal vector's formula.

The complete scratch proof and targeted module build pass. The final
theorem substitutes the actual squared-norm difference into the complete
cross-prime incidence reader, retaining the original prime pair, zero
copy, depth and nonzero incidence witness. This proves the positive
actual-source comparison exposed by the failed cancellation conjecture.
It does not prove equality of radial readouts or agreement with the
cyclic reader. The physical defect is zero exactly on the critical line;
no vanishing assertion or equality of reciprocal characters is assumed.

## Search record so far

Two partial deep/method searches returned 20 candidates and 20 source
arguments each; all were inspected. Generation 823361, semantic
coverage 2196271/2337495, deadline/filter-and-judge/source-refresh
unfinished; no proposed proof ideas or ingredient sets. They locate
the actual reciprocal seed, source-domain admission, lower conormal
jets and completed nonzero jet. Generic adjunction and exactness hits
do not supply the source/reader equality.

Broad recent searches led to primary papers
[scale-dependent nonreciprocity](https://arxiv.org/abs/2609.08820),
[mechanical network reciprocity](https://arxiv.org/abs/2609.04169), and
[optical interleaving](https://arxiv.org/abs/2608.07054).
The optical abstract is empirical and supplies no proof mechanism.
The network paper's Theorem 6 and proof were read: imposed-drive
reciprocity is a compliance-weighted relation, with a common symmetric
operator and invertible terminal blocks required; equality of raw
transmission magnitudes does not follow. That distinction reinforces
the need to retain both actual conormal normalizations. No paper theorem
is used as an unproved Lean input. The nonreciprocity perspective's
abstract and initial HTML retrieval have been inspected; no specific
mathematical result from it has been adopted.

A third deep/method search tested whether source Fourier orthogonality
survives the conormal evaluation. All 20 candidate statements and 20
source arguments were inspected. Generation 824048, semantic coverage
2192666/2347598; deadline, filter-and-judge and source refresh remain
partial, with no proposed proof ideas or ingredient sets. Actual Burnol
Fourier parity projectors and their self-adjointness exist. Unitary
Gram invariance and common inverse-Cholesky comparison require their
own isometry or common-frame premises; none identifies the normalized
point-conormal reader with the source Hilbert metric.

The actual closed cosine source has exact first-live jet detection;
the existing literal zero-jet Riesz system indexes jets strictly below
that multiplicity. Its annihilation cannot be applied to the nonzero
leading jet. These source files were inspected directly after search.
The next source-balance test must retain the two actual normalization
factors while comparing the Fourier parity components through the
physical reader. Source orthogonality alone has not supplied that
comparison. The required physical equality is equality of squared
norms of the centered characters, not equality of their complex phases.

## Closed Lean result and audit

Module: `GaloisForLFunctions.RHTower.BurnolCoPoissonReciprocalWindowIncidence`.
Thirteen exported theorems, three internal lemmas and three actual-source
or literal-jet-quotient definitions. Wired into `RHTower.lean`.

- Full scratch check: exit 0, no diagnostics. Repository theorem bodies
  match the successful scratch exactly.
- Targeted `lake build GaloisForLFunctions.RHTower.BurnolCoPoissonReciprocalWindowIncidence`:
  exit 0; only the new leaf compiled, in 63 seconds. Existing dependency
  diagnostics were replayed; the new module emitted none.
- Thirteen exported `#print axioms` audits: only `propext`,
  `Classical.choice`, `Quot.sound`. These cover all three used internal
  lemmas transitively. No new axioms or unproved assumptions were added.
- Duplicate check: 19 declarations, zero collisions. Formal index
  regenerated; `scripts/formal_tools.py lint` passed.
- Scratch, build and axiom processes all terminated. No full or umbrella
  build, numerical experiment or committed change was used.

Positive survivor: exact Fourier-partner incidence, preserving the
original nonzero completed leading jet and physical radial defect.
Remaining mathematical obstacle: derive that defect's vanishing from
complete source balance. Next attack: the real polarized source pairing
that measures the radial difference, with both actual normalization
factors and all source corrections retained. Fourier Hilbert
orthogonality is not yet agreement of that physical pairing.
