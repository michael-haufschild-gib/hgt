# Route L: two-prime joint-jet source

- **ID:** L-C36
- **Date:** 2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM; actual joint source interpolation and its source-selection obstruction
- **Depends on:** [C34](route-l-real-polarized-source-balance.md), [C35](route-l-jet-kernel-fourier-transport.md)
- **Lean:** `formal/GaloisForLFunctions/RHTower/BurnolCoPoissonTwoPrimeJointJets.lean`
- **RH status:** unproved

The chain remains complete original Green/BV source → cyclic/fixed
physical reader agreement → conormal vanishing → RH. C34–C35 retain
normalization bias and a source component that leaves the original
leading-jet kernel under Fourier transport. C36 retains both measurements
and constructs their actual joint interpolation at a common aperture.
It does not identify an interpolant with the specified complete source.

## Closed source theorem

Keep arbitrary distinct original primes `p,q`, an unchanged actual Xi
divisor `rho`, and the exact first nonzero zeta derivative order `m`.
Let `f_L` be the literal logarithmic co-Poisson window and let
`J_L=ell(f_L)`, `K_L=ell(F(f_L))` be its actual Gamma-completed `m`-jets.
Then one of `L=log p` and `L=log q` has a nonsingular joint matrix for
`f_L,f_(2L)`. For any complex `u,v`, a literal combination
`f=c*f_L+d*f_(2L)` satisfies

`ell(f)=u`, `ell(F(f))=v`.

Both vectors already belong to the algebraic co-Poisson source at the
single aperture `A=exp(-2*(log p+log q))`, before closure. Every derivative
of order below `m` vanishes on both vectors. This theorem needs no
strict-right, simplicity, critical-line or source-incidence assumption.
The original zero, multiplicity and nonzero internal zeta jet are retained.

## Dependency-closed proof

The literal completed window formulas give

`J_(2L)=(exp(L*rho)+1)*J_L`,
`K_(2L)=(exp(L*(1-rho))+1)*K_L`.

Both `J_L` and `K_L` are nonzero, including their original common Gamma
factor and nonzero `m`-th zeta derivative. Hence

`D_L=J_L*K_(2L)-K_L*J_(2L)`
`   =J_L*K_L*(exp(L*(1-rho))-exp(L*rho))`.

An actual Xi divisor is nonreal, so `2*rho-1` is nonzero. Dividing the
last exponential difference by its nonzero factors shows that `D_L=0`
is equivalent to `rectangularWindowAmplitude L (2*rho-1)=0`. The existing
irrational-width rectangular-window theorem excludes a common zero for
`log p,log q`; their irrational ratio follows from prime factorization.
Thus at least one actual joint determinant is nonzero.

For that pair, the Cramer coefficients are exactly

`c=(u*K_(2L)-v*J_(2L))/D_L`,
`d=(v*J_L-u*K_L)/D_L`.

The proof admits these coefficients on the literal source. Original
subwindow profiles and reciprocal indicator-window profiles have weighted
absolute integrability throughout `0<Re(w)<1`. Almost-everywhere L²
addition and scalar multiplication therefore give linearity of the raw
completed Mellin integral on this finite span. Local equality with the
analytic completed window germs transports every finite derivative.
In particular, all lower jets vanish and the two `m`-jets are the displayed
Cramer readings. The aperture estimate admits both original windows and
both Fourier images in the same algebraic source.

This argument does not widen the general Sonin continuation/raw-integral
agreement theorem beyond its proved convergence half-strip. The required
full-strip admission is proved for these specific literal windows.

## Obstruction and positive survivor

Choosing `(u,v)=(1,0)` proves that Fourier unitarity cannot impose equal
absolute top-jet readings on every admitted source. This conclusion holds
at every actual Xi divisor, including any critical-line divisor; it is not
an off-line-zero contradiction. The strongest positive survivor is the
actual arbitrary joint interpolation theorem, with all lower jets and
common-aperture source membership retained.

A correction with readings `(0,J_L-K_L)` can preserve the original top
reading while equalizing the two corrected readings. That shortcut fails
the original-source comparison: it changes the retained Fourier reading
and provides no coherent original doubled-window or all-prime source
family. Exact interpolation does not select the complete Green/BV source.

The next target is a correction forced by that complete source that
preserves the original physical readings and aperture transport. Existing
actual dilation theorems retain reciprocal Mellin characters but send the
source to a smaller aperture. The co-Poisson quotient dilation theorem
leaves a Sonin aperture projection. Fixed-aperture invariance or isometry
must not be inserted as a premise.

## Corpus audit

Five deep searches used 150-second budgets. Every response's 20 candidate
lemmas and 20 source arguments were inspected, including available methods.
All responses reported partial coverage and background refresh; none is
an exhaustive absence claim.

1. `joint Mellin jet source interpolation two incommensurate prime logarithms Fourier determinant nonzero`:
   generation 872335, semantic coverage 1,996,945/2,351,398; deadline and
   filtering incomplete. Adopted the narrower rectangular-window pair
   nonvanishing mechanism, not conditional joint-observer covariance.
2. `injective pair exponential irrational periods complex parameter`:
   generation 872405, coverage 2,019,257/2,351,398; decomposition incomplete.
   Found another exponential-pair independence theorem; no duplicate proof
   was needed.
3. `joint kernel invariant involution quotient norm linear section dilation`:
   generation 872865; inventory 56,809 files complete, 706,128 ready methods,
   semantic indexing incomplete. The proposed ingredient set required
   compact joint boundedness below, which is unproved here and was not adopted.
4. `Mellin evaluation dilation invariant kernel quotient closure`:
   generation 872993, coverage 2,129,081/2,351,552; deadline and filtering
   incomplete. Located the actual Mellin character, Fourier inversion and
   source-aperture change in `BurnolSoninDilationMellin`,
   `BurnolCoPoissonSourceDilation`, and `BurnolCoPoissonQuotientDilationCollapse`.
5. `real source conjugate Mellin Fourier jet involution`:
   generation 873453, coverage 2,232,246/2,351,556; deadline and filtering
   incomplete. One source argument lacked a method record. Conjugation
   identities require the actual real-source condition. The existing real
   Hodge factorization distinguishes an unconditional source involution
   from a different transport compatibility equivalent to RH; the latter
   was not used as a premise.

## Broad recent-paper audit

Primary sources inspected through broad `interpolation`, `transport`,
and `lifting` searches:

- [Dimitrić–Vučković–Žigić, 2609.06258](https://arxiv.org/html/2609.06258v1),
  September 5: Theorem 3.4 interpolates supplied derivative bounds from
  suitably spaced orders, with parameter loss. It supplies no source balance.
- [Karakashian, 2609.10374](https://arxiv.org/html/2609.10374v1), September 9:
  Theorem 2 and Proposition 2 retain trace/jump costs when correcting local
  finite-element data. Method analogy: admit the common source frame and
  retain its correction costs.
- [Fahli–Galichon, 2609.06277](https://arxiv.org/html/2609.06277v1),
  September 5: section 2.4 requires a specified cost and an optimal coupling.
  No corresponding Burnol optimality law was constructed.
- [He–Le, 2609.08684](https://arxiv.org/html/2609.08684v1), September 8:
  Lemma 4.12 classifies lift defects through a connecting map; Proposition
  4.16 tests the residual defect class. This suggests separating interpolation
  from compatibility of a selected lift. No category-theoretic premise was imported.
- [Yovkochov et al., 2609.09827](https://arxiv.org/html/2609.09827v1),
  September 9: section III-A factors two-channel reconstruction into
  triangular matrices of determinant one. This gives invertibility,
  but no isometry follows from that factorization. No numerical experiment
  or empirical result was used in the proof.

## Verification

Foreground `lake env lean /tmp/route_l_joint_jet_c36.lean` passed with no
output. The exact proof bodies were promoted to the new module and wired
into `RHTower.lean`. The targeted final leaf build passed; only the new
leaf was compiled. Formal lint passed. No umbrella or full build was run.
The module contains 11 exported theorems, 7 internal lemmas and 2 source
definitions; declaration collision checking found no collisions.
