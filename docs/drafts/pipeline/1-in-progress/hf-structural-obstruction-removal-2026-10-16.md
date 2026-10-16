# HF: structural obstruction removal

Status: paper proof closed; Lean verification in progress. No verified
contribution claimed yet.

## Contract

Produce an unconditional structural theorem removing a substantive obstruction
in route HF. No improved estimate, RH equivalence, receiver, numerical
computation, external search, or novelty audit. Read Lean corpus and use its
research search. Preserve full multiplicity and original arithmetic source.

## Plan

1. Identify actual frontier from route entry and Lean declarations.
2. Conjecture exact structural laws; attack them against full corpus and their
   mathematical consequences; record failures and continue.
3. Complete a dependency-closed paper proof before formalization.
4. Formalize, audit leaf modules and standard axioms, wire umbrellas, run lint.

The requested update_plan tool is unavailable; this card records task state.

## Initial frontier

Original Meyer cohomology has global Xi synthesis, continuous full-Hasse
Hilbert admission, nondegenerate Paugam pairing, full-Jordan source Fredholm
calculus, genuine arithmetic convolution trace, original-source inverse
preservation, and finite native density. Positive Hodge compatibility remains
open. The route also names arithmetic cup/trace identification as unresolved.

## Conjecture ledger

1. Global Paugam skew-convolution trace: BRIDGE. Local full-jet identity and
   global summability already exist in `DeningerMeyerConvolutionPaugam` and
   `DeningerMeyerGlobalHassePaugamPairing`. Summing is not the requested advance.
2. Original-source upper/lower spectral splitting: OPEN, not selected. The
   Hilbert sign multiplier does not prove preservation of the all-weight
   source. Gaussian half-contours do not supply Gaussian removal.
3. Whole-source differential realization: SURVIVES PRELIMINARY ATTACK.
   The existing faithful Gaussian native map intertwines the original
   centered generator with the literal theta differential action on EVERY
   original Meyer class. Consequently its image lies in the native domain,
   is invariant under the actual differential action, and realizes every
   finite differential word without dropping any Jordan coordinate.

## Exact theorem and dependency-closed paper proof

Let Q be literal strong Meyer cohomology, A=-i(D-1/2) its centered generator,
P the existing faithful fixed-Gaussian native profile map, and R the actual
bounded native Green operator at i. Prove

    R P((A-i)q) = Pq,       thetaSpatialAction(Pq) = P(Aq)

for every q in Q. No spectral-location, simplicity, positivity, convergence,
or source-admission premise is added.

Write p(s)=-i(s-1/2), m for theta mass, and K(z)=XiC(z)/m. For an entire
input F and any Xi-free rectangle, put

    a_F = integral_boundary F(s)/xi(s),
    B_F(u) = integral_boundary F(s)/xi(s) dslope(xi,s,u),
    f_F(x) = -i integral_boundary F(s)/xi(s) cutQuotient(p(s),0,x).

All contour integrals have the existing normalized rectangle convention.
The already-proved charge cancellation makes f_F bounded and continuous.
Its exact theta moment is M_p(u)(f_F)=-p(u) B_F(u)/m.

The divided-difference identity, valid also at u=s, gives

    B_(pF)(u) = p(u) B_F(u) + i xi(u) a_F.

Indeed p(s)-p(u)=i(u-s), so the difference of integrands is
i F(s)/xi(s) (xi(u)-xi(s)); the entire F term integrates to zero.
Thus, with h_F=f_((p-i)F) and t_F=i a_F,

    M_z(h_F) = (z-i) M_z(f_F) - z t_F K(z).

At z=i this forces the native resolvent trace to equal t_F, since
i K(i) is nonzero (the existing imaginary regular parameter). The exact
native Green moment law then gives

    (i-z) [M_z(R h_F)-M_z(f_F)] = 0.

For real z, i-z is nonzero. Real theta moments separate bounded continuous
profiles: multiply the profile by the strictly positive theta density,
apply L1 Fourier uniqueness, then use continuity to turn almost-everywhere
equality into equality. Therefore R h_F=f_F.

Apply this identity to every upper/lower contour block. For any original
source g and positive Gaussian time epsilon, both the native series for g
and for (A-i)g are absolutely summable by the existing source theorem.
Mellin integration by parts gives M_((A-i)g)=(p-i)M_g; multiplication by the
Gaussian commutes with this scalar factor. Bounded linearity of R therefore
passes the identity through both full sums and then through the genuine
Poisson quotient. Take epsilon=1 to obtain R P((A-i)q)=Pq.

The existing Green equation now yields the pointwise differential identity,
both equal endpoint limits, and differentiability. The profile is already
BV, and its action equals another admitted BV profile, so it lies in the
literal native differential domain. Induction gives every finite scalar
shift word. P remains injective by the existing global Xi-synthesis theorem;
its already-proved arithmetic graph admission and full signed Weil identity
remain attached to the very same profiles.

Moreover A-i=-i(D+1/2). Xi has no zero at -1/2 by the existing unconditional
real-height zero-free theorem. The actual Xi cap and causal division
therefore give a source preimage for every forcing. The Green identity and
faithfulness make this source solution unique and identify its spatial
profile with R applied to the original forcing profile. Thus R preserves
the whole original-source image, not only a collection of finite packets.

This closes whole-range generator compatibility, not Gaussian removal,
positive Hodge compatibility, or RH.

## Verification

Lean implementation is in `PaperThetaMomentSeparation`,
`PaperThetaContourGenerator`, and `PaperThetaWholeMeyerGenerator`.
`PaperThetaMomentSeparation` and `PaperThetaContourGenerator` pass direct
`lake --old env lean -j 1` leaf audits, with no warnings. The combined
scratch audit exposed source-subtype coercions and a pointwise application
rewrite in the whole-source passage; corrected. Its direct leaf audit and
the final standard-axiom audit remain pending.

The exact-proposition search and exhaustive source-name search found no
existing whole-range native generator identity. Deep searches for the
earlier infinite interpolation candidate were partial and supplied no
applicable interpolation theorem; no conclusion depends on their coverage.
Serena's symbol tool ignores Lean files in this project; source reads and
patches are used after that explicit tool failure.
