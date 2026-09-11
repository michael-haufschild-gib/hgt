# Route L: actual jet-kernel Fourier transport

- **ID:** L-C35
- **Date:** 2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM; literal source kernel witness and quantitative Fourier readout
- **Depends on:** [C34](../3-formalized/route-l-real-polarized-source-balance.md)
- **RH status:** unproved

The chain remains complete original source → cyclic/fixed physical reader
agreement → original conormal vanishing → RH. C34 closes the actual
normalization comparison and exposes a strict cost. It supplies no source
compensation. The next test is whether canonical minimum-norm interpolation
can provide that compensation without changing Fourier transport or the
original leading derivative.

## Conjecture, failure mechanism and positive target

Fix the actual window `f=f_L` and its cosine Fourier image `Ff` at the
unchanged right-half Xi divisor. The existing completed Mellin jet theorem
provides a bounded linear evaluator `ell` on the actual extended Sonin
space at this aperture. Its values are precisely the nonzero C34 factors
`ell(f)=J` and `ell(Ff)=K`. All lower derivatives vanish on the closed
co-Poisson source; none is substituted for this first nonzero derivative.

A proposed minimum-norm correction would replace the jet-one sources
`X=J^-1 f` and `Y=K^-1 Ff` by their common representative perpendicular
to `ker(ell)`. Equality of those representatives alone supplies no
Fourier covariance. Test the missing kernel invariance on the literal
source difference, without choosing a new vector or reflected zero.

Set `V=K f-J Ff`. Linearity and `F²=1` give the exact paper identities

`ell(V)=0`, `ell(FV)=K²-J²`.

C34 proves `exp(L*(2*Re(rho)-1))*|K|²<|J|²` on the strict right
half, hence `K²-J²` is nonzero there. Thus `V` is an explicit source
vector in the leading-jet kernel whose Fourier image leaves that kernel.
An orthogonal kernel projection cannot commute with Fourier there.
This tests the proposed correction directly; it is not an independent
proof that an off-line Xi divisor exists or that RH fails.

The positive survivor is the exact source-valued kernel witness, its
nonzero Fourier readout, and the quantitative lower bound

`(exp(L*(2*Re(rho)-1))-1)*|K|² < |ell(FV)|`.

The reverse triangle inequality gives
`|J|²-|K|² <= |K²-J²|`; combine it with C34's strict bound.
Both normalization factors, source aperture and the same divisor remain
in the statement. Both `V` and `FV` lie in the literal algebraic
co-Poisson source, before closure. No generic evaluator is assumed:
the proof uses the existing bounded completed-derivative evaluator on
the actual extended Sonin carrier and identifies its values on both
literal window sources.

All four theorems passed the complete scratch check with no diagnostics.
The exact checked bodies are in
`GaloisForLFunctions.RHTower.BurnolCoPoissonTopJetKernelFourierLeakage`,
with one source definition, and the module is wired into `RHTower`.
The targeted leaf build and complete axiom audit passed. No orthogonal
projection is adopted as the missing physical source comparison.

## Corpus and external methods checked

Two deep/method queries inspected all 20 candidate statements and all
20 returned source arguments each. The complete-boundary query was
partial because source refresh was running; its semantic snapshot was
complete at 1921517/1921517, generation 826737. Its generated Green-form
proposal points to `HedenmalmThetaActualStageGreenBalance`: inspection
shows a retained correction commutator, with eigenmode neutrality still
equivalent to a real spectral parameter. Its proposed Fourier/essential
boundary-layer combination provides no identification with the actual
Burnol conormal. The boundary-layer source is a separate explicit
exponential family, not the missing correction.

The interpolation query was partial at generation 830221, semantic
coverage 1921193/1946980, with no proof ideas. The proposed ingredient
set combines unrelated algebraic affine jets with generic kernel
projection. A closed kernel has an orthogonal projection, but that
existence theorem gives no commutation with Fourier. The actual bounded
completed-jet evaluator, extended-space Fourier invariance and Fourier
involution were located directly in the Lean corpus.

Broad arXiv searches used entropy and recurrence. The abstracts of
[entropy reduction in learning](https://arxiv.org/abs/2609.08054)
(September 7) and [recurrence-tensor clustering](https://arxiv.org/abs/2608.04157)
(August 4) supply no source comparison here.
[Entropy for singular flows](https://arxiv.org/abs/2609.00626)
(September 1), Theorems 1.1–1.2 and the beginning of Lemma 2.3's proof,
require a compact flow or geometric separation with uniform small-time
control and a compact set meeting every regular orbit. None of those
structures has been constructed for this source correction. No entropy
bound or external theorem is adopted as a Lean premise.

## Formal audit and remaining attack

The final targeted `lake build` compiled only this leaf (271 seconds;
existing dependencies cached). All four theorem names were audited
exactly once through `/tmp/route_l_jet_kernel_c35_axioms.lean`; every
entry depends only on `propext`, `Classical.choice` and `Quot.sound`.
Duplicate checking found five declarations and zero collisions. The
formal index was regenerated, the global formal lint gate passed, and
the repository bodies match the successful scratch exactly. No added
axioms, proof placeholders, numerical experiments or full/umbrella
builds were used.

The complete-source compensation law remains open. A stronger next
conjecture tests the joint pair of leading-jet readers at every Xi
divisor, including the critical line. C33's two doubled-window formulas
give the determinant
`J_L*K_(2L)-K_L*J_(2L) = J_L*K_L*(exp(L*(1-rho))-exp(L*rho))`.
For two distinct prime logarithms, simultaneous vanishing should force
`rho=1/2` using prime-logarithm independence, contradicting the already
proved nonzero imaginary part of an actual Xi divisor. This would give
an unconditional finite source frame for both readouts and test joint
interpolation without a strict-right hypothesis. This stronger statement
has not been formalized or audited; it must first undergo corpus search
and an actual common-aperture source proof. It is not an RH claim.
