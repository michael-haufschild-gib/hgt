# Route L: complete critical Euler current by signed Abel assembly

- **ID:** RH-L-C68
- **Stage:** 1-in-progress
- **Target:** Full-source fixed Gamma/BV reader agreement.
- **RH status:** UNPROVED

Chain: complete original source → fixed-reader agreement → conormal vanishing → RH.
C67 verified the complete native jet connections and both damped Euler mass
limits. The critical scalar-pairing series is now identified on both original collars
with the complete regular current minus its exact origin contact. The fixed
Gamma/BV reader comparison remains open.

## Source conjecture and paper mechanism

For the unchanged all-exponential native source `h`, write `H(x)=h(log x)`.
The actual critical current is `E(h)(x)=-sum_n mu(n) log(n) H(nx)` on `x>0`.
Introduce its signed Abel atoms, without altering the original arithmetic:

`Q_n(x)=M(n)[log(n+1) H((n+1)x)-log(n) H(nx)]`.

Their finite sum equals the original finite logarithmic current plus its
original boundary `M(N) log(N) H(Nx)`. The boundary tends to zero. Split each
atom into `M(n) log(n)[H((n+1)x)-H(nx)]` and
`M(n)[log(n+1)-log(n)]H((n+1)x)`. The existing adjacent-dilation integral
estimate and `log(n+1)-log(n)<=1/n` give

`integral |Q_n| <= V(h) |M(n)| log(n)/n^2 + Pabs(h) |M(n)|/n^2`.

Both scalar majorants are summable by proved Mertens bounds. Therefore the
complete critical current is integrable. Integrating these admitted atoms,
then using the exact scalar logarithmic Möbius normalization, gives
`integral_(0,infinity) E(h)=P(h)`.

The scalar Mertens and Abel identities discovered in the PW Gamma module
contain no Gamma source assumption; they may be reused on their exact
statements. Its profile-specific estimates and Gamma mass value may not be
transferred. The native source constants and masses must be derived anew.

Formal target: this integrability and exact mass on both original native
collars, with `P(h_k)=Xi^(k)(i(1/2-1/m))/m` and
`P(Jh_k)=Xi^(k)(i/2)/m`. The integrability, exact-mass and critical-contact proofs passed together in
foreground scratch Lean at default limits (final session 91677, exit 0).
The named leaf audit also passed. Fixed-reader agreement is not established.


## Critical contact: second conjecture and direct paper proof

Let `f=M(h)` be the unchanged complete Möbius preimage. Its mass is zero
and its first absolute moment is finite. For every Schwartz test `phi`, the
original Euler term after subtracting `phi(0)` has norm integral at most

`seminorm(0,1,phi) * integral y*|f(y)| * Lambda(n)/n^2`.

This is summable. Change variables in each finite original term; its zero
mass makes the subtracted pairing equal to its original causal pairing.
The admitted infinite exchange therefore gives exactly

`sum_n CausalTerm(f,phi,n) = integral E(h)(x)*phi(x) dx - P(h)*phi(0)`.

This directly identifies the origin contact on the positive collar. A
separate point-support classification is unnecessary. The complete regular
current's admission is needed to separate its constant-test contribution.
Both native coefficients are the original Xi-jet masses stated above.
Both native specializations passed scratch Lean. No identification with the
fixed degree-six Gamma/BV reader follows solely from this identity.

## Corpus and method audit

Four completed deep whole-corpus searches were read in full: all 20
candidate statements, all 20 source-method statements and assumptions, and
the proposed group in each. All four are partial/source-only retrievals,
with complete inventory but no compiler admission claim.

- `route-l-critical-abel-admission-search.json`: generation 882417;
  snapshot/current 882419; 57,201 files, 47,564 Lean files, 738,063
  declarations, 44,724 compiler-pending files. The signed Gamma atom proof
  supplied the decomposition pattern. Only its purely arithmetic Mertens
  and Abel identities are reused; the native variation bound is proved
  from the actual all-exponential source. The proposed Laplace/pole/Suzuki
  group combines different input families and supplies no identification.
- `route-l-critical-current-mass-method-search.json`: generation and
  snapshot/current 882419, same counts. The actual adjacent-dilation FTC
  mass estimate and native moment admission are applicable. The proposed
  Hankel/Sonin/vacuum group does not establish critical native L1 admission.
- `route-l-critical-contact-support-search.json`: generation 882439;
  snapshot/current 882445; 57,202 files, 47,564 Lean files, 738,063
  declarations, 44,724 compiler-pending files. PointSupportVanishing requires
  actual annihilation of tests vanishing near zero. Connes jet independence
  requires the actual finite-jet functional to annihilate every test. Neither
  produces those premises. The proposed group confuses derivative support
  with evenness and has no native-current input. Definitions, unrelated
  wave/source equations and finite-jet parity formulas are not producers.
  Pivot: prove the contact directly by subtracting the test value inside
  the original arithmetic terms.


- `route-l-critical-subtracted-contact-search.json`: generation and
  snapshot/current 882493; 57,204 files, 47,565 Lean files, 738,070
  declarations, 44,725 compiler-pending files. All 20 statements and all
  20 source-method arguments were inspected. The proposed moment-dilation
  group combines an unrelated finite moment-model definition with the
  profile-specific Gamma mass theorem; it does not prove the actual
  subtracted-pairing exchange. The existing Deninger causal renormalization
  source was then read directly: its norm-of-integral bound alone is
  insufficient for interchange. The new proof establishes the stronger
  integral-of-norm bound before exchanging the full series and integral.


A fifth, mechanism-named hybrid search,
`route-l-critical-causal-method-search.json`, completed without truncation:
generation 882513; snapshot 882515/current 882516; 57,204 files, 47,565 Lean
files and 738,080 declarations, with 44,725 compiler-pending files. All 20
candidate statements and all 20 source-method arguments were inspected.
It recovers the actual causal split and summability theorem with explicit
Lipschitz and first-moment premises, which are derived on the native source
in the new proof. The unrelated Hardy resolvents and Neumann contractions
use different spaces and supply no fixed native Gamma/BV comparison. No
proof ideas or ingredient groups were returned.


A sixth deep search, `route-l-critical-fourier-contact-search.json`, was
partial/source-only: generation 882544; snapshot/current 882568; 57,205
files, 47,566 Lean files, 738,113 declarations and 44,726 compiler-pending
files. All 20 candidate statements, 20 source-method arguments and the
proposed group were inspected. The actual Fourier-of-Dirac theorem and L1
Fourier pairing theorem provide the convention and admission needed for the
next transport. The proposed group does not identify the two native readers:
its second theorem concerns the embedding of Schwartz functions. The FZZ
kernel equality assumes full Fourier covariance; neither that assumption
nor circle rigidity and unrelated finite Fourier identities can establish
native fixed Gamma/BV agreement.

## Broad recent literature audit

The latest-first single-word arXiv search `renormalization` and a broad
`sewing` search were used; the latter yielded no usable result. First-page
abstracts were screened, including plasma, tomography, Higgs, condensate
and percolation topics; no mathematical input was imported from them.

[Erman–Turgut, arXiv:2609.09068v1](https://arxiv.org/html/2609.09068v1),
September 8: read introduction, section 3.1, physical subtraction in 5.1,
and appendices C.5–C.7. Their contact coefficient uses a rescaled kernel and
an integrable bound; operator convergence also retains a nonzero finite
part. The tail estimate requires the actual kinetic dispersion and trace
structure. We have no such operator construction on the native source.
The transferable mechanism is to prove the retained tail and coefficient
on the original source. Here signed Abel assembly and a first-moment bound
supply that mechanism directly. Auxiliary Bessel/trace estimates were not
independently verified and are not used as proof inputs.

[He–Uhlemann–Vallarino, arXiv:2609.09303v1](https://arxiv.org/html/2609.09303v1),
September 8: read sections 2.1–2.3 through equation 44. Smooth coupling
variation forces interface terms before a sharp limit. Their local Ward
relation requires preserved supersymmetry, vanishing fermion variations
and the specified multiplet. The hypermultiplet argument identifies an
ambient coefficient after separating contact contributions; it does not
prove equality of complete distributions. No such supersymmetry data is
available here. The useful instruction for the native calculation is to
retain the origin term explicitly and identify its original coefficient.
No Ward identity or discarded contact is transferred.


## Next source comparison after the contact identity

For an even extension of each positive collar, testing against `phi` means
using `phi(x)+phi(-x)` on the positive ray. Thus the same proved positive-ray
contact contributes twice its coefficient. The actual Fourier convention
has `fourier_delta_zero : Fourier(delta_0)=volume.toTemperedDistribution`
(Mathlib, TemperedDistribution). Consequently the first collar's origin
contact becomes a constant distribution, while the second collar's contact
remains at the origin before Fourier transformation. They cannot be
cancelled as two scalar coefficients at a common point without an actual
transport identity. This observation is on paper only here; a complete
native two-collar Fourier contact equation and its comparison with the fixed
Gamma/BV reader remain to be established. All original prefix contributions
from the existing native jet recurrence must remain in that comparison.


## Formal result and remaining hard gate

`MobiusThetaNativeCriticalEuler.lean` supplies six public native theorems:
both complete critical currents are integrable, both have their exact
original Xi-jet masses, and both original causal pairing series equal the
complete regular-current pairing minus that mass times the test value at
zero. The proofs quantify over every original internal jet, every positive
native depth and every Schwartz test. No reader equality, RH, stationarity,
Poisson-range or positivity premise is introduced.

The scalar and analytic admissions used in the signed assembly are
proved from the corpus's original Mertens bound and native all-exponential
source. In the contact passage, a first-moment integral-of-norm estimate
justifies the infinite exchange. The original Möbius preimage has zero
mass; the complete Euler current retains its source mass. This explains
precisely why the regular current and the series of causal tests differ.

The module is wired into `RHTower.lean`; no umbrella build is requested.
The only setting is `autoImplicit false`. No heartbeat, recursion-depth or
transparency setting was raised. Named audit and lint results are recorded below. The target remains complete original source →
fixed-reader agreement → conormal vanishing → RH. The open mathematical
gate is now transporting these exact contacts with both original collars,
prime prefix and horizontal anchor to the independently fixed degree-six
Gamma/BV functional and proving that full comparison.


## Verification

- Foreground scratch: `lake env lean /tmp/MobiusThetaNativeCriticalEuler.lean`,
  final session 91677, exit 0; all six public native results and their
  private analytic proofs checked together.
- Named leaf audit: `lake build GaloisForLFunctions.RHTower.MobiusThetaNativeCriticalEuler`,
  session 86177, exit 0. The new leaf built in 121 seconds; Lake reported
  12,623 dependency jobs. Log: `/tmp/route-l-native-critical-euler-build.log`.
  No umbrella or full build was run.
- Source module has 514 lines, and exactly one umbrella import. Index
  generation completed, with all six public declarations present in
  `LEAN_API.md`.
- `scripts/formal_tools.py lint` ran once and exited 1. Its only error is
  the unrelated, currently unwired
  `GaloisForLFunctions.HTGeometry.InversePowerCancellation`; it reports no
  error for the new module. Existing large-file warnings remain.
- All six research commands, scratch Lean checks, the named build and
  index/lint processes completed. No owned Lean process remains.

The general STATUS entry on countable reconstruction now records the
stronger test-functional lesson, without introducing a route-specific rule.
The original Route L target remains open; this leaf closes the critical
regular-current/causal-pairing contact comparison, not fixed-reader agreement.
