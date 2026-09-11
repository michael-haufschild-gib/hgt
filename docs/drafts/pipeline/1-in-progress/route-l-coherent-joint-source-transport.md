# Route L: coherent joint-source transport

- **ID:** L-C37
- **Date:** 2026-09-11
- **Stage:** 1-in-progress
- **Type:** CONJECTURE; source-selected joint correction across apertures
- **Depends on:** [C36](../3-formalized/route-l-two-prime-joint-jet-source.md)
- **RH status:** unproved

The proof chain is complete original Green/BV source → cyclic/fixed
physical reader agreement → conormal vanishing → RH. C36 constructs
arbitrary joint original/Fourier top jets at an unchanged actual Xi divisor,
with every lower jet zero and literal common-aperture source admission.
The hard obligation is a correction forced by the complete source that
preserves its physical readings and coherent transport.

## First attack: coherent dilation filters

The actual normalized dilation has Mellin character `r^(w-1/2)`, and
Fourier transport inverts the dilation. A scalar filter symmetric under
inversion therefore multiplies the two leading-jet channels by the same
factor. Such a filter cannot alter their ratio while retaining both
nonzero readings. This is a paper-level failure of the proposed balanced
scalar correction, not a retirement of Route L. Any proof must admit the
actual filtered source and its exact multiplicity jets; formalization
must not stop at a generic scalar identity.

## Pivot: canonical joint correction and aperture cost

Retaining both measurements makes their joint kernel Fourier invariant.
C36 supplies actual joint surjectivity. Test whether orthogonal projection
off this joint kernel gives a canonical minimum-norm right inverse that
commutes with Fourier, at the original aperture. This would solve the
one-measurement kernel defect without assuming source incidence.

Then derive the actual comparison across apertures from normalized
source dilation. Its two channel characters are reciprocal; its source
aperture shrinks. The source-selected right inverse must retain this
metric cost. A fixed-aperture isometry, a uniform lower bound on the
minimum-energy profile, or equality with the physical reader cannot be
supplied as a premise. The main target is the actual joint correction
and the exact remaining aperture term, followed by an independent attack
on whether the complete Green/BV source compensates that term.

## Evidence in progress

Deep corpus search: `coherent correction Fourier dilation Mellin kernel
projection commutator aperture`, 150-second budget. Broad recent arXiv
queries: `reciprocity` and `compression`. No new Lean theorem is claimed.
