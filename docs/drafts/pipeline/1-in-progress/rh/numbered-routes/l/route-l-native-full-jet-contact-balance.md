# Route L: original two-collar jet balance with critical contacts

- **ID:** RH-L-C69
- **Stage:** 1-in-progress
- **Target:** Complete original source agreement with the fixed Gamma/BV reader.
- **RH status:** UNPROVED

Chain: complete original source → fixed-reader agreement → conormal vanishing → RH.
C68 has verified both native critical currents' integrability, exact Xi-jet
masses and full causal-pairing contact identities. The next hard comparison
must retain these contributions in the original two-collar source equation.

## Source sign and paper target

Write `A_k` and `B_k` for the unchanged prime-anchored first and exchanged
collars at the original positive depth `m`, and write `L_k`, `LJ_k` for
their original logarithmic finite prefixes. Existing native recurrences give

`A_(k+1)=im*(log|x| A_k-E_k-L_k)`,

`B_(k+1)=-im*(log|x| B_k-EJ_k-LJ_k)`.

Here the Euler currents and prefixes are extended evenly from the positive
ray. Thus, with the complete boundary `K_k=Fourier(A_k)-B_k`, the Euler
combination in the raised boundary is `Fourier(E_k)+EJ_k`. A difference of
these currents would have the wrong sign for the actual source recurrence.

Conjecture: prove the original logarithmic collars integrable, then derive
the exact distributional raised-boundary equation with both finite prefixes
and both critical contacts. C68 identifies the first even contact with
`2*P(h_k)*delta_0`, the second with `2*P(Jh_k)*delta_0`. Fourier turns the
first into `2*P(h_k)*volume`; the second remains at zero. Both enter with
the signs forced by the displayed recurrence. Neither a scalar cancellation
nor a vanished complete source boundary is assumed.

Fixed degree-six source cyclicity is already proved independently. Its
physical agreement is equivalent to the reflected physical boundary being
zero at every original Xi copy. The new balance must be evaluated through
that actual comparison, preserving the prime cutoff, native depth,
multiplicity, nonzero Xi jet and horizontal anchor; it is not itself RH.

The complete scratch proof and named-module audit passed with default Lean
limits. The new leaf is wired into `RHTower.lean`. Formal lint passed.
Fixed-reader agreement remains unproved.

## Paper proof of logarithmic admission and the balance

Solve the first recurrence for `log|x| A_k`:
`log|x| A_k=(im)^(-1) A_(k+1)+E_k+L_k` almost everywhere.
The raised original collar is integrable by native source admission; C68
admits `E_k`; every term of the finite prefix is an admitted positive
integer dilation. The same argument uses `-im` on the second collar.
Since `m` is positive, both coefficients are invertible. This proves both
logarithmic admissions from the original equations without new decay premises.

For `φ` in Schwartz space write `φ_even=φ+Fourier²(φ)`. Splitting the
whole line into its two rays gives
`<even(E),φ>=<E,φ_even>_(positive)`.
C68 therefore gives
`<even(E_k),φ>=C_h(φ_even)+2*P(h_k)*φ(0)`, and the same formula for `Jh_k`.
Pair the two raised source recurrences with `Fourier(φ)` and `φ`, respectively,
and subtract. The result retains, inside the common factor `im`:

- the sum of the two logarithmic collar pairings;
- minus the sum of the two original causal pairings;
- minus the sum of the two logarithmic finite-prefix pairings;
- minus `2*P(h_k)*Fourier(φ)(0)+2*P(Jh_k)*φ(0)`.

Here `P(h_k)=Xi^(k)(i*(1/2-1/m))/m` and `P(Jh_k)=Xi^(k)(i/2)/m`.
All infinite pairings have the required admission from C67–C68. This is an
identity for the original complete boundary, not a claim that it vanishes.

## Whole-corpus candidate and method audit

Both searches below returned 20 candidate statements, 20 source-argument
records and one unverified ingredient group; every such record was read.
Neither returned a proof idea. Their partial source coverage and pending
compiler statuses do not certify whole-corpus absence or candidate validity.

- `route-l-native-contact-reader-transfer-search.json`: query generation
  882662, snapshot 882694, current 882706; 57,208 files, 47,568 Lean files,
  738,153 declarations, 44,729 compiler-pending files. Fourier pairing,
  periodized boundary coefficients and finite cutoff Ward splits were
  useful. The proposed group assumes `chainLiftObstruction h=0` and then
  invokes an unrelated Gaussian Fourier sector; it does not produce the
  native comparison. Gaussian fixed-test equalities and Ward codiagonal
  cancellation retain their narrower domains or other boundary components.
- `route-l-native-log-collar-balance-search.json`: query generation 882706,
  snapshot/current 882715; 57,210 files, 47,569 Lean files, 738,203
  declarations, 44,730 compiler-pending files. The Fourier multiplication
  formula requires actual integrability, supplied above. Parseval variants
  additionally require L2. `connesFourierLogMoment_eq` unfolds a definition;
  it does not admit the native logarithm. StrongLog boundary candidates
  require Meyer-cap or Poisson-range data. The proposed circle Fourier/L1-L2
  group does not identify the original source or fixed reader.
- `route-l-native-log-fourier-reader-search.json`: query generation 883465,
  snapshot 883473, current 883476; 57,213 files, 47,571 Lean files,
  738,617 declarations, 44,732 compiler-pending files. All 20 candidate
  statements and all 20 source-argument statements, proof excerpts and
  applicability records were inspected. Every returned applicability was
  unchecked and the records were source-only. The request was partial
  after interrupted retrieval and a reranking deadline. Its proposed group
  combines an admitted damped source Fourier/Mellin identity, a generic
  weighted Meyer identity, damping-two Green residues, and a truncated
  Poisson input. These are different domains; the residue-to-fixed-reader
  comparison remains an explicit obligation. Direct source inspection of
  `DeningerOriginalGreenBoundaryResidues.lean` confirms that the retained
  prime-harmonic residues are nonzero, not a vanishing producer.
- `route-l-native-mellin-contact-reader-search.json`: query generation
  883487, snapshot 883488, current 883489; 57,213 files, 47,571 Lean files,
  738,617 declarations, 44,732 compiler-pending files. All 20 candidate
  statements and all 20 source-argument statements, proof excerpts and
  available method assumptions were read. Partial retrieval/reranking
  again reached its deadline; applicability remained unchecked. The
  ingredient group combines a uniformly Lipschitz endpoint finite-part
  theorem with linear independence of Mellin jets. Direct inspection of
  `FirstEndpointMellinLaurentInterchange.lean` confirms the endpoint and
  parameter-uniform bounds must be supplied before residue interchange.
  Neither jet independence nor its source-quotient descent supplies them.
  A returned method describes
  `CCMMobiusThetaSourceResidueAnnihilatesMinimalBoundary` as proving
  annihilation, but the returned declaration is only its definition.
  This false positive was rejected. Skewness of a generalized jet pairing
  also supplies no equality of the required squared norms.
- `route-l-native-mellin-prefix-extraction-search.json`: hybrid query
  generation 883506, snapshot/current 883513; 57,213 files, 47,571 Lean
  files, 738,617 declarations, 44,732 compiler-pending files. All 20
  candidate statements and all 20 source-method statements, proof excerpts
  and available assumptions were read. Retrieval was partial; no ingredient
  group or proof idea returned. The actual inverse-zeta theorems apply in
  `Re(s)>1`; algebraic Mobius inversion alone supplies no integral
  interchange. The original preimage was returned as a definition. No
  native collar Mellin/prefix comparison was returned. An exhaustive source
  text search for the explicit Mobius-preimage/Mellin name combinations also
  found no match; this does not rule out a differently named theorem.

## Comparison attempts after the source balance

**A. Cancel the two contacts as one scalar.** This fails before any limit:
the two source-forced coefficients multiply different test functionals,
`Fourier(φ)(0)` and `φ(0)`, and the raised source signs give their sum inside
the subtracted contact. No identity cancelling these functionals on all
Schwartz tests has been derived. Positive survivor: the displayed complete
balance identifies both contributions and their signs separately.

**B. Identify a source Gamma endpoint with the fixed degree-six reader.**
Direct inspection of `DeningerAdiabaticGammaEndpoint.lean` shows its Gamma
boundary is the Fourier difference of the two source Gamma distributions.
`DeningerAdiabaticTransgression.lean` identifies the admitted flux with the
difference from the critical Mobius boundary. This is not a comparison
with the degree-six physical scalar. The other exact source construction,
`DeningerGammaSixActualGammaBoundaryLogTransgression.lean`, reconstructs a
logarithmic Wold weight from equal-depth `(2,3)` critical exteriors after a
forced half-density factor. Its original critical parameter is zero; no
identification with the unchanged divisor parameter follows. Neither
result can be substituted for the missing reader map.

**C. Transfer through original Green residues.** The returned damping-two
Green theorem retains the source, prime period and every boundary mode,
but its poles are original prime harmonics and its residues are nonzero.
It does not evaluate the native collar contact equation at an arbitrary
Xi divisor or at its exact multiplicity jet. The needed transfer must
first admit that spectral extraction with the actual contact prescription.
Fourier/Mellin reparametrization alone does not supply it.

The precise next target is a source-derived passage from the complete
native Schwartz-test balance to the unchanged multiplicity-exact physical
conormal reading. `DeningerBurnolConormalRadialTopBoundaryComparison.lean`
already identifies that reading with the difference of squared norms of
the two reflected nested-window characters. Its proof retains the nonzero
top Xi jet. This quadratic reading cannot be replaced by holomorphic
reflection of the native source Mellin parameter. Source admission for the
test passage, all contact/prefix terms, and the quadratic comparison still
have to be proved. No reader equality or norm equality is assumed.

**D. Original native Mellin extraction (next conjecture).** Test the
original collar at `s=m*rho` at sufficiently large native depths, so the
integer dilation series is admitted in `Re(s)>1` without moving `rho`.
The proposed first-collar formula is the source Mellin value times
`1/zeta(s)-sum_(n<p) mu(n)*n^(-s)`, with the zero-index convention retained.
Differentiate only after a common local integrable bound is established;
then extract the actual first nonzero Xi jet. For the second collar,
the exact exchange uses `s -> 1-s`, together with the native depth
correction. It cannot be replaced by `m*rho -> m*(1-rho)` without deriving
the intervening character. This would identify an actual source-to-spectral
passage, but the comparison of reflected squared norms would still remain.

## Broad recent literature audit

Single-word latest-first arXiv `gluing`, and broad `anomaly` search, screened
the displayed recent results. The gluing result page was truncated; this is
not an audit of all 50 results. No external result is a Lean dependency.

- Hubisz, Moradipasha, Singh, [arXiv:2609.10459v1](https://arxiv.org/html/2609.10459v1),
  September 9, 2026. Read the boundary-anomaly setup, fermion equations and
  normalization argument in §§2–4, and anomaly-flow mechanisms in §§6.1–6.3.
  Their Chern–Simons contribution moves anomalies between boundary supports
  with opposite signs; integrated cancellation alone does not control each
  boundary. Nonabelian charge structures can prevent this mechanism from
  working. Transfer tested: account for each source-forced contact before
  comparing total readouts. The paper changes the action or field content
  to accomplish cancellation. Those operations cannot be imported as an
  adjustable correction to the unchanged RH source. Its geometric and
  physical consistency assumptions do not establish the fixed reader.
- Brown, Gómez García, Jordan, Vancraeynest,
  [arXiv:2609.09308v1](https://arxiv.org/html/2609.09308v1), September 8, 2026.
  Read the defect/dual setup, §§3.1–3.2, Lemmas 4.3–4.4, Proposition 4.5
  and its proof, and the reconstruction/localization argument through
  Corollary 4.6 and the start of §4.2. Injectivity and explicit q-commutation
  establish the Ore localization; generation then gives the localized
  isomorphism. The defect becomes invertible only after localization and
  leaves a Weyl action. Transfer tested: construct the comparison on a
  precisely admitted source domain and retain its residual exchange.
  Neither localization nor a residual Weyl action supplies equality on the
  unlocalized complete native source. No quantum-group or semisimplicity
  assumptions were transferred. The HTML obscures diagram formulas; no
  complete audit of those diagrammatic identities is claimed.

## Formal result and verification

`formal/GaloisForLFunctions/RHTower/MobiusThetaNativeFullJetBalance.lean`
contains 232 lines. Its public API is:

- `mobiusThetaNativeCollarTail_log_integrable` (line 101);
- `mobiusThetaNativeSecondCollarTail_log_integrable` (line 110);
- `mobiusThetaNativeEvenTest` (line 119);
- `mobiusThetaNativeFullCollarBoundary_succ_contact` (line 203).

The three theorems are unconditional on the original source for all jet
orders, natural prime cutoffs, positive native depths and, in the boundary
identity, every Schwartz test. No domain, reader equality or zero-location
premise was added to these statements.

`lake env lean /tmp/MobiusThetaNativeFullJetBalance.lean` passed with exit 0
(session 36413). Initial failures were resolved using explicit function
arguments in integral rewrites, an explicit ray endpoint, and explicit
membership elimination. The leaf has only `set_option autoImplicit false`.

`lake build GaloisForLFunctions.RHTower.MobiusThetaNativeFullJetBalance`
passed with exit 0 (session 46064). The new leaf built in 6.0 seconds;
the target reported 12,624 dependency jobs. Log:
`/tmp/route-l-native-full-jet-balance-build.log`.
The import is at `formal/GaloisForLFunctions/RHTower.lean:6282`.
No umbrella or full build was run.

`scripts/formal_tools.py lint` passed with exit 0 (session 73854), with
existing large-file warnings. Log:
`/tmp/route-l-native-full-jet-balance-lint.log`.
A refreshed module-filtered lexical search returned all four public API
entries at their current source lines; its output contains no compiler
freshness metadata, so the named build remains the verification evidence.
All owned Lean and search processes reached terminal status; the final
process check found no owned Lean process left running.

The checked improvement is the full native source balance, not fixed-reader
agreement. The remaining original-parameter Mellin extraction and quadratic
conormal comparison are stated in D above.
