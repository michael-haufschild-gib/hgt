# Hellinger--Beta/co-Poisson resonance transmutation

- **ID:** `hellinger-beta-copoisson-resonance-transmutation`
- **Stage:** 3 — formalized in Lean 4
- **Type:** EXACT SCALAR REPAIR NO-GO + VECTOR-COFACE SURVIVOR
- **Scientific status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:**
  - `../2-fully-proven/new_scientific_knowledge/suzuki/bv-copoisson-sharp-critical-half-weight-log-flux.md`;
  - `../4-publication-ready/riemann-hellinger-hodge-green-descent/main.tex`.
- **RH used:** no
- **Computation used:** no
- **Lean:** fully formalized unconditionally in
  `formal/GaloisForLFunctions/RHTower/BVCoPoissonHellingerBetaResonanceTransmutation.lean`

## Frontier and failed conjecture

Burnol's extended-property-S topology excludes the sharp critical co-Poisson
Mellin vector

\[
 F(s)=\frac{\eta(s-\tfrac12)}{s-\tfrac12}
\tag{1}
\]

because its reflected values are nonzero on every positive even and odd
Gamma-pole lattice.  The Hellinger--Hodge source constructed later supplies
the canonical scalar Beta column

\[
 H(s)=-B\!\left(s+\tfrac12,\tfrac32\right)
 =-\frac{\Gamma(s+\tfrac12)\Gamma(\tfrac32)}
          {\Gamma(s+2)}.
\tag{2}
\]

This suggests the exact conjecture

`[CONJECTURE] [SCALAR_HELLINGER_PROPERTY_S_REPAIR]`

> The scalar corrected vector \(M(s)=F(s)H(s)\) belongs to one of Burnol's
> even or odd extended-property-S classes after multiplication by a nonzero
> polynomial.

**Hostile verdict: `FALSE`.**  The Beta quotient cancels almost all old
integer Gamma poles but creates a common infinite half-integer pole lattice.
Thus scalar Hellinger completion transmutes the resonance; it does not remove
it.

## Exact transmutation theorem

Put

\[
 \chi_+(s)=\pi^{s-1/2}
   \frac{\Gamma((1-s)/2)}{\Gamma(s/2)},\qquad
 \chi_-(s)=i\pi^{s-1/2}
   \frac{\Gamma((2-s)/2)}{\Gamma((s+1)/2)}.
\tag{3}
\]

These are the even and odd Fourier reflection factors in Burnol's Mellin
normalization.  Define

\[
 E_\pm(s)=\chi_\pm(s)M(1-s).
\tag{4}
\]

`[LEAN-PROVED] [HELLINGER_BETA_COPOISSON_RESONANCE_TRANSMUTATION]`

1. For every \(n\ge1\), the zero of \(H(1-s)\) at \(s=1+2n\)
   cancels the simple pole of \(\chi_+\).  Only the initial integer pole
   \(s=1\) can remain.
2. For every \(n\ge1\), the zero of \(H(1-s)\) at \(s=2+2n\)
   cancels the simple pole of \(\chi_-\).  Only the initial integer pole
   \(s=2\) can remain.
3. Both \(E_+\) and \(E_-\) have a simple pole with nonzero residue at every
   point
   \[
                    s_n=\frac32+2n,\qquad n\ge0.
   \tag{5}
   \]
   More precisely, writing \(z_n=1-s_n=-\tfrac12-2n\),
   \[
   \operatorname*{Res}_{s=s_n} M(1-s)
    =\frac{\eta(-1-2n)}{-1-2n}
      \frac{\Gamma(\tfrac32)}
           {(2n)!\,\Gamma(\tfrac32-2n)}\ne0,
   \tag{6}
   \]
   and multiplication by either finite nonzero value
   \(\chi_\pm(s_n)\) preserves nonvanishing.
4. Consequently no nonzero polynomial can make either reflected scalar
   vector have only finitely many poles.  The scalar corrected vector is
   excluded from both extended-property-S parities.

## Proof

The Gamma function has simple poles at \(-m\), \(m\in\mathbb N_0\), with
residue \((-1)^m/m!\), and no zeros.  Its reciprocal is entire with simple
zeros at those points.

At \(s=1+2n\),

\[
 H(1-s)
 =-\frac{\Gamma(\tfrac32-s)\Gamma(\tfrac32)}
          {\Gamma(3-s)}.
\tag{7}
\]

For \(n\ge1\), the numerator is finite and nonzero because
\(\tfrac32-s=\tfrac12-2n\) is a half-integer, while
\(3-s=2-2n\) is a nonpositive integer.  Hence `(7)` has a simple zero.
The factor \(\chi_+\) has a simple pole there.  The existing critical-eta
nonvanishing theorem gives
\(F(1-s)=F(-2n)\ne0\).  Orders therefore cancel exactly.  At \(n=0\),
\(H(0)\ne0\), so no cancellation is asserted.  The odd calculation at
\(s=2+2n\) is identical: for \(n\ge1\), the denominator argument
\(3-s=1-2n\) is a nonpositive integer and the numerator argument
\(-\tfrac12-2n\) is not.

Now fix \(s_n=\tfrac32+2n\) and \(z_n=1-s_n\).  In the local variable
\(z=1-s\), the only singular factor of \(H(z)\) is
\(\Gamma(z+\tfrac12)\) at \(z+\tfrac12=-2n\).  Its residue is
\(1/(2n)!\).  The change of variable \(z=1-s\) reverses the residue sign,
which cancels the leading minus sign in `(2)`.  This gives the second factor
in `(6)`.

The remaining co-Poisson factor is

\[
 F(z_n)=\frac{\eta(-1-2n)}{-1-2n}.
\tag{8}
\]

Here
\(\eta(-1-2n)=(1-2^{2+2n})\zeta(-1-2n)\ne0\): the elementary factor is
nonzero, and the zeta functional equation reduces nonvanishing at the
negative odd integer to \(\zeta(2+2n)>0\).  Also
\(\Gamma(\tfrac32-2n)\ne0\).  Thus `(6)` is nonzero.

At \(s_n\), every Gamma argument in `(3)` is a nonintegral quarter-integer
or a positive quarter-integer.  Hence \(\chi_+(s_n)\) and
\(\chi_-(s_n)\) are finite and nonzero.  This proves item 3.

Finally the points `(5)` are pairwise distinct.  If multiplication by a
polynomial removed every pole outside a finite set, that polynomial would
vanish at all but finitely many \(s_n\).  A nonzero polynomial has only
finitely many roots.  This proves item 4.

## Hostile and rediscovery audit

- `[LOCAL-RESEARCH]` The parent sharp-flux card already proves exclusion of
  \(F\) from both property-S parities, logarithmic boundary flux \(1/4\),
  dense multiplier ideal, and compact-seed rigidity.  It explicitly asks
  for an archimedean correction before completion.
- `[LOCAL-RESEARCH]` The Hellinger--Hodge paper constructs `(2)` from the
  occupation source and proves its coface recurrence; it does not multiply
  `(1)` by `(2)` or audit Burnol pole lattices.
- `[LITERATURE]` Burnol's co-Poisson/property-S work classifies the required
  reflected Mellin behavior and the Sonine evaluator spaces.  It does not
  supply the specific Hellinger Beta correction `(2)`.
- Targeted searches for the exact eta--Beta product and its reflected pole
  lattice found no matching theorem.  Priority remains unverified.
- The theorem is not RH progress by itself.  It is a provider no-go and a
  representation discriminator.

Primary sources:

- J.-F. Burnol, *Entrelacement de co-Poisson*, Ann. Inst. Fourier 57 (2007),
  525--602, DOI `10.5802/aif.2268`.
- J.-F. Burnol, *Two complete and minimal systems associated with the zeros
  of the Riemann zeta function*, JTNB 16 (2004), 65--94,
  DOI `10.5802/jtnb.434`.
- L. Báez-Duarte, *A general strong Nyman--Beurling Criterion for the
  Riemann Hypothesis*, arXiv:`math/0505453`.

## Positive survivor and stronger conjecture

The killing mechanism is scalarization, not the Hellinger correction itself.
The Beta column obeys the source-forced shift law

\[
 H(s+1)=\frac{s+\tfrac12}{s+2}H(s).
\tag{9}
\]

An Euler polynomial cannot clear the new infinite lattice, but the coface
shift `(9)` acts on all of it simultaneously.  This yields the stronger
replacement:

`[CONJECTURE] [VECTOR_HELLINGER_COFACE_RESIDUE_BOUNDARY]`

> Before Haar orientation, the shifted two-channel Hellinger--Beta column
> carries the half-lattice residue family `(6)` into the image of the
> source Calderón--Witt incidence differential.  The reflected transform is
> therefore moderate as a vector-valued relative class even though every
> scalar orientation has the pole lattice `(5)`.

This is not killed by the scalar pole argument: it uses a source shift and a
relative vector class, neither a polynomial multiplier nor cancellation
after scalar trace.  It is falsifiable by computing one residue in the
degree-two packet quotient.  `[OPEN CORE]` Construct the coface action on the
actual vector-valued Gamma/co-Poisson transport and identify the class of the
residue at \(s=3/2\).  Nonzero quotient class kills the conjecture; exact
incidence boundary gives the first source-native mechanism capable of
entering Burnol's graph without assuming RH.

## Lean formalization

The scalar theorem and its positive Beta-recurrence survivor are formalized
without mathematical hypotheses beyond the explicit regular-point
conditions of the Gamma shift identity.  Main theorem:

- `hellingerBetaCoPoisson_resonanceTransmutation` — capstone packaging the
  recurrence, both old integer-pole cancellations, exact nonzero residues on
  the full common half-lattice, and both finite-exception polynomial no-go
  statements.

Supporting exact statements include:

- `hellingerHodgeBetaColumnComplex_add_one` and
  `hellingerHodgeBetaColumnComplex_real_add_one` — formula `(9)`;
- `hellingerBetaReflectedResidue_eq_card_formula` — formula `(6)` exactly in
  eta/factorial/Gamma form;
- `tendsto_hellingerBetaEvenReflectedMellin_oldPole` and
  `tendsto_hellingerBetaOddReflectedMellin_oldPole` — finite punctured limits
  at every old integer pole after the initial point;
- `hellingerBetaEvenIntegerCancellationValue_ne_zero` and
  `hellingerBetaOddIntegerCancellationValue_ne_zero` — exact nonzero
  cancellation values;
- `tendsto_hellingerBetaEvenReflectedMellin_residue` and
  `tendsto_hellingerBetaOddReflectedMellin_residue` — normalized limits at
  every point `(5)`;
- `hellingerBetaEvenReflectedResidue_ne_zero` and
  `hellingerBetaOddReflectedResidue_ne_zero` — nonvanishing in both parities;
- `polynomial_eq_zero_of_cancels_hellingerBeta_even_half_residues_off_finset`
  and
  `polynomial_eq_zero_of_cancels_hellingerBeta_odd_half_residues_off_finset`
  — exact “outside a finite set” form of item 4.

Verification:

- `lake env lean GaloisForLFunctions/RHTower/BVCoPoissonHellingerBetaResonanceTransmutation.lean`;
- `lake build GaloisForLFunctions.RHTower.BVCoPoissonHellingerBetaResonanceTransmutation`;
- `#print axioms` on the capstone and critical supporting theorems reports
  only `propext`, `Classical.choice`, and `Quot.sound`.

The fixed-cross-prime form of
`[VECTOR_HELLINGER_COFACE_RESIDUE_BOUNDARY]` is now falsified by
`hellinger-beta-calderon-witt-relative-residue-obstruction.md`: its residue
is ambient incidence but its admitted relative class vanishes exactly at
zero modular displacement.  Only a new off-diagonal, source-horizon-graded
graph differential remains viable.

## Gates

- [x] exact scalar conjecture stated
- [x] hostile falsity proof
- [x] positive survivor extracted
- [x] dependency-closed paper proof
- [x] internal parent-theory audit
- [x] preliminary primary-literature audit
- [x] exact Lean formalization
- [x] fixed-cross-prime vector coface residue computation — falsified;
  positive cofinal graph-boundary survivor extracted
