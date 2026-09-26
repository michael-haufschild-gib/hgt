# Exact theta-tail signature under Fourier–Laplace transformation

- **ID:** RH-THETA-TAIL-EXACT-SIGNATURE-ROOT-20260926
- **Owner:** root
- **Stage:** 3-formalized
- **Type:** derived [BRIDGE]; mechanism visible before freezing
- **Result:** frozen C12 and separately frozen stronger C12+ proved
- **Mission status:** RH and the common source signature's sign remain open

## Exact result

Write Phi for the complete theta source and

`K(x,y) = integral_(s>0) (x+y+2s) Phi(x+s) Phi(y+s) ds`.

Write `X(w)` for its actual bilateral Laplace transform, `X1(w)=X'(w)`
for its first moment, and use the Hermitian Bezoutian

`B(w,v) = [X1(w) conj(X(v)) + X(w) conj(X1(v))] / [w+conj(v)]`.

For every real a, sigma>0, and finite r:

`negativeDimension_r(K on x>a) <=> negativeDimension_r(B on sigma+i*t, t real)`.

The same equivalence holds for the literal product-measure double Laplace
integral. A finite negative dimension means r finitely supported coefficient
packets whose every nonzero complex linear combination has strictly negative
kernel form. No sign hypothesis, RH assumption, truncation, or tolerance occurs.

Original C12 required sigma>1/2; its exact statement is the Euler-line
specialization. C12+ was frozen separately when the proof exposed that only
sigma>0 is needed. No conjecture was weakened.

## Dependency-closed paper proof

1. **Actual source sections.** In the Hilbert sum of two L2 spaces, let
   `F(x)(s)=1_(s>0)((x+s+1)Phi(x+s),(x+s-1)Phi(x+s))`.
   For `J=diag(1,-1)`, the existing literal identity gives
   `<F(y),J F(x)>=2K(x,y)`. All source terms remain.

2. **Explicit transformed sections.** For Re(w)>0 define the L2 vector
   `L(w)(s)=1_(s>0)e^(-ws)(X1(w)+X(w),X1(w)-X(w))`.
   Each channel belongs to L2 by the half-line exponential-square integral.
   For an arbitrary L2 pairing vector u and channel d=+1 or -1, integration
   in x of the absolute scalar integrand gives exactly
   `|u(s)| e^(-Re(w)s) * integral_R |(x+d)Phi(x)e^(wx)| dx`.
   The x-integral is finite by the proved full-source bilateral transform
   and first-moment integrability. The s-integral is finite by L2
   Cauchy–Schwarz. Scalar Fubini therefore proves, for every Hilbert vector u,
   `integral_R e^(wx)<u,F(x)> dx = <u,L(w)>`.
   This argument requires no unproved vector-valued integration assertion.

3. **Fourier uniqueness.** Weak analyticity of F on the source strip makes
   `f_sigma(x)=e^(sigma*x)<u,F(x)>` continuous; step 2 makes it L1.
   Its Fourier transform at t equals `<u,L(sigma-2*pi*i*t)>`.
   If u annihilates L on the vertical line, the transform is zero and is
   itself L1. Fourier inversion gives f_sigma=0. The exponential never
   vanishes, so u annihilates every F(x). The reverse follows directly from
   step 2. The Hilbert annihilator criterion identifies the two closed spans.

4. **Every real tail.** A scalar analytic pairing vanishing on x>a vanishes
   on the connected source strip by the accumulating-zero theorem. Thus
   every real tail of F has the same closed span as all real F sections.

5. **Every finite dimension.** Strict negativity on a finite coefficient
   unit sphere is open in its vector tuple, by compactness. A negative tuple
   in the closure of an algebraic span can therefore be approximated by a
   negative tuple in that span. Finite synthesis produces literal kernel
   packets. Hence equal closed spans preserve all finite negative dimensions
   of a bounded form. This general theorem needs neither completeness nor
   a Hermitian hypothesis on that form.

6. **Literal normalization.** The integrated two-channel difference gives
   `<L(v),J L(w)>=2B(w,v)`. Existing source Fubini identifies B with the
   literal double Laplace integral. Both kernels have the same factor 2;
   positive real scaling preserves each finite negative dimension. Steps
   3–5 prove C12+ and hence unchanged C12.

## Lean surface

- `HTGeometry/KernelClosedSpanInertia.lean`: generic finite-tuple density,
  equal-closed-span signature, positive kernel scaling; 12 theorem/lemma
  declarations and 3 definitions.
- `RHTower/ThetaTailLaplaceTotality.lean`: actual scalar Fubini, transformed
  sections, Fourier annihilator equivalence, all-tail totality, exact kernel
  identity; 22 theorem/lemma declarations and 3 definitions.
- `RHTower/ThetaTailLaplaceSignature.lean`: vertical-line, Euler-line, and
  literal-double-integral signature equivalences; 3 theorems.

All three leaves are wired exactly once. No new proof limit, forbidden
proof-debt declaration, numerical mathematical experiment, or git command.

## Novelty and right-problem audit

Existing `ThetaTailAnalyticLocality` transported dimensions between tails;
`ThetaTailFirstMomentDoubleLaplace` identified entries and supplied RH sign
receivers. C12 identifies the actual negative dimensions across these two
representations. Inspected corpus searches supplied the scalar Fourier and
finite-tuple mechanisms, but no existing actual-source signature theorem.
This is corpus-relative novelty, not a literature priority claim.

Search records: `/tmp/rh-c12-signature-search.json`,
`/tmp/rh-c12-laplace-totality.json`, `/tmp/rh-c12-density-method.json`;
flux/factorization/Stein searches also inspected. Laplace-totality and
finite-density searches completed without partial-stage errors; others
reported deadlines/disconnects. Compiler coverage was predominantly
source-only/pending/stale. Retrieved candidates were checked in Lean.

**Whole route:** transform and tail restriction hide no negative directions.
Moving to arbitrarily large positive sigma or arbitrarily distant real tails
cannot change the signature. This theorem does not bound it or prove it zero.
The next substantive obligation is the exact sign of the original two-channel
form on its actual closed source span. Further equivalent criteria alone
would not discharge that obligation. No primary sign conjecture is claimed.

## Verification

Complete combined scratch `/tmp/rh-c12-complete-signature.lean`: exit 0,
no warnings. All three final named leaf builds: exit 0, no new-leaf diagnostics.
Dependency builds replay existing unrelated warnings.

All 43 public declarations (37 theorems/lemmas, 6 definitions) pass the
scratch axiom audit: only `propext`, `Classical.choice`, `Quot.sound`; no
missing report. `/tmp/rh-c12-axioms.lean`, `/tmp/rh-c12-axioms.log`, and
`/tmp/rh-c12-axiom-names.txt` hold the exact audit surface.

Final index regeneration succeeds. `lint --check-generated` exits 1 only
for the unrelated unwired `RHTower.ThetaPowerFejerTransfer` module; no stale
index or own-leaf error remains. That module was not edited. Existing
large-file warnings remain. Logs: `/tmp/rh-c12-final-index.log` and
`/tmp/rh-c12-final-lint.log`; named builds:
`/tmp/rh-c12-build-density.log`, `/tmp/rh-c12-build-totality.log`,
`/tmp/rh-c12-build-signature.log`.

All owned Lean/build/search/index/lint jobs exited; final process scan
found none. Global goal remains active: no RH proof or falsification.
