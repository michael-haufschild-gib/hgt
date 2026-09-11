# Route L: two-prime joint-jet source

- **ID:** L-C36
- **Date:** 2026-09-11
- **Stage:** 1-in-progress
- **Type:** CONJECTURE; actual joint source interpolation and Fourier transport
- **Depends on:** [C35](../3-formalized/route-l-jet-kernel-fourier-transport.md)
- **RH status:** unproved

The chain is complete original source → cyclic/fixed physical reader
agreement → conormal vanishing → RH. C34–C35 prove normalization bias
and a literal source witness that leaves the leading-jet kernel under
Fourier transport. They do not supply complete-source compensation.
The present attack retains both leading-jet measurements and tests
whether a joint source correction can preserve the relevant transport.

## Conjecture and paper mechanism

Keep distinct original primes `p,q`, the same actual Xi divisor `rho`,
and its first nonzero completed derivative order. For the literal
window `f_L`, write `J_L=ell(f_L)` and `K_L=ell(F(f_L))` as in C34.
C33's endpoint formulas imply

`D_L=J_L*K_(2L)-K_L*J_(2L)`
`   =J_L*K_L*(exp(L*(1-rho))-exp(L*rho))`.

All four normalization factors are nonzero. If both `D_(log p)` and
`D_(log q)` vanished, their exponential periods would first force
`Re(rho)=1/2`, then impose integer relations
`Im(rho)*log(p)=pi*m` and `Im(rho)*log(q)=pi*n`.
Independence of the two prime logarithms would force `Im(rho)=0`,
contradicting the corpus theorem that an actual Xi divisor is nonreal.
Thus at least one doubled-window pair should provide an invertible
two-by-two matrix of the two actual leading-jet measurements.

The positive target is arbitrary joint interpolation on a finite
combination of these literal windows, all admitted at one common
aperture. No strict-right, simplicity or critical-line hypothesis is
allowed in that target. A common-aperture proof must retain the actual
raw Mellin derivatives: the general bounded Sonin continuation evaluator
agrees with the raw integral only in its proved convergence half-strip,
whereas these particular co-Poisson windows have full-strip admission.
No continuation/raw identification will be assumed outside that domain.

After admission, test the complete paired correction and its Fourier
law. Joint interpolation alone cannot be called radial balance or
agreement with the cyclic source reader. If a correction erases either
normalization factor or its original physical character, fail and pivot.

## Current verification

Corpus search and the actual source/prime-period proof are in progress.
No new Lean theorem or RH conclusion is claimed yet.

## Full-strip source proof under audit

The explicit Cramer coefficients are
`c=(u*K_(2L)-v*J_(2L))/D_L` and
`d=(v*J_L-u*K_L)/D_L`. The candidate literal source is
`c*f_L+d*f_(2L)`, with Fourier image `c*F(f_L)+d*F(f_(2L))`.
All four windows are admitted in the algebraic co-Poisson source at
`A=exp(-2*(log p+log q))`. Weighted integrability of original subwindows
and reciprocal indicator windows holds throughout the open strip.
Consequently the raw completed integral is linear on this finite span;
local analytic germ equality then transports every finite derivative.
This avoids widening the general Sonin continuation/raw agreement theorem.

The proposed positive theorem gives arbitrary `(u,v)` at the unchanged
actual divisor and exact multiplicity. Its obstruction test uses `(1,0)`:
Fourier unitarity cannot enforce equal jet amplitudes on every admitted
source. This does not refute balance for the particular complete Green/BV
source; identifying that source and its physical readings remains open.

## Corpus and broad-paper audit

Three deep searches (150 seconds each) inspected all 20 candidate lemmas
and 20 source arguments/methods per response:

- `joint Mellin jet source interpolation two incommensurate prime logarithms Fourier determinant nonzero`:
  partial, generation 872335; semantic coverage 1,996,945/2,351,398;
  background refresh and deadline/filtering incomplete. Adopted the
  existing sharp rectangular-window pair nonvanishing mechanism, not a
  conditional joint observer or assumed source covariance.
- `injective pair exponential irrational periods complex parameter`:
  partial, generation 872405; semantic coverage 2,019,257/2,351,398;
  decomposition/refresh incomplete. Found a second exponential-pair
  independence theorem, but reused the narrower rectangular-window law.
- `joint kernel invariant involution quotient norm linear section dilation`:
  partial, generation 872865; inventory 56,809 files complete, semantic
  index incomplete, 706,128 ready methods. The proposed ingredient set
  combines kernel intersection with compact joint boundedness below;
  the latter is an unproved premise here and was not adopted. A joint
  kernel is an intersection, but that alone supplies no physical
  dilation law or source selection.

Primary sources inspected through broad `interpolation`, `transport`,
and `lifting` searches:

- [Dimitrić–Vučković–Žigić, 2609.06258](https://arxiv.org/html/2609.06258v1),
  September 5: Theorem 3.4 interpolates derivative bounds from suitably
  spaced orders, with parameter loss. Such bounds must already be
  supplied; this is no source-balance producer.
- [Karakashian, 2609.10374](https://arxiv.org/html/2609.10374v1), September 9:
  Theorem 2 and Proposition 2 retain trace/jump costs when correcting
  local finite-element data. Method analogy: admit the literal common
  source frame and retain correction costs.
- [Fahli–Galichon, 2609.06277](https://arxiv.org/html/2609.06277v1),
  September 5: section 2.4 uses a specified transport cost and optimal
  coupling. No corresponding Burnol optimality law was constructed.
- [He–Le, 2609.08684](https://arxiv.org/html/2609.08684v1), September 8:
  Lemma 4.12 classifies lift defects through a connecting map; Proposition
  4.16 tests the residual defect class. This suggests distinguishing
  solvable interpolation from compatibility of the selected lift.
  No triangulated-category assumptions were imported into Route L.
- [Yovkochov et al., 2609.09827](https://arxiv.org/html/2609.09827v1),
  September 9: section III-A factors two-channel reconstruction into
  triangular matrices of determinant one. Invertibility follows,
  whereas an isometry does not follow from that factorization. No
  empirical result or numerical experiment was used in this proof.

Scratch `/tmp/route_l_joint_jet_c36.lean` is undergoing a foreground Lean
check. The first check verified the API probes and doubled-jet formulas,
but found explicit-positivity and simplification obligations in the
remaining determinant proof. Those were corrected before adding the
full-strip source interpolation proof; final closure is not yet claimed.

Verification instruction: user stopped `#print axioms` checks. Continue
foreground scratch checks and the required targeted final leaf build; do
not run or add axiom-print audits.
