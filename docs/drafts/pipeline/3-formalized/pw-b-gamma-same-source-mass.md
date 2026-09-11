# PW-B complete spatial mass of the same-source forcing

- **ID:** PW-B-GAMMA-SAME-SOURCE-MASS-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** The complete same-source forcing has an everywhere absolutely convergent mass L-series. Its first nonzero coefficient is a finite strictly negative source mass. The spatially integrated defect is eventually nonzero as the real coefficient parameter grows, with a quantitative scaled L1 lower bound.

## Literal pairing and admission

Retain the source, both operators and every signed coefficient from the
[same-source current audit](pw-b-gamma-same-source-current.md).
Write `D_z(x)=H(R M_z)(x)-R E_z(x)` and
`B(z)=integral_0^infinity D_z(x) dx`. This is the unchanged Lebesgue
pairing on the complete positive ray; no physical spectral interpretation
of this pairing is assumed.

For each arithmetic index, take the actual difference between the
integrated original-response atom and the reflected-current atom.
Its norm integral is bounded by the sum of the original atom's joint
norm integral and the reflected-current atom's spatial norm integral.
Both complete majorant series converge for every complex z. Consequently
the full difference series passes through the spatial integral.
The already admitted joint response difference also satisfies Fubini.
Thus B is both the difference of the two complete current masses and
the joint integral of their literal response difference.

## Positive survivor and exact leading mass

The previous exact coefficient was
`c_n(x)=mu(n)*Q(x)*W_n(x)`, with W_0=W_1=0 and W_n(x)>0 for n>1,x>0.
Every c_n is globally integrable. Define `d_n=integral c_n(x) dx`.
The actual mass identity is

`B(z)=LSeries(d,z)`, absolutely convergent for every complex z.

The first two coefficients vanish. The prime-two coefficient is
`d_2=-A`, where

`A=integral_0^infinity norm(Q(x))*W_2(x) dx > 0`.

Finiteness follows from the actual admitted coefficient; strict positivity
follows from positivity at every positive source coordinate. No numerical
value is needed. The L-series leading-coefficient theorem now gives

`2^r*B(r) -> -A` as real r tends to infinity.

Hence B(r) is nonzero for every sufficiently large r, and equality of the
two complete current masses cannot hold at every complex parameter.
The integral norm inequality gives the stronger retained-source bound

`eventually r, A/2 < integral_0^infinity norm(2^r*D_r(x)) dx`.

This proves survival under the specified spatial pairing, which did not
follow from pointwise nonvanishing alone. It does not determine B(0),
D_0, or balance at particular spectral occurrences.

## Research and remaining proof chain

[Search records](../1-in-progress/pw-b-gamma-same-source-mass-searches.json)
retain three partial deep searches, a partial hybrid method search,
an eight-hit lexical fallback, and a failed deep Ward query.
The three deep results report pending coverage without a declaration
count; the hybrid inventory reports 723510 declarations. Generic adjoint,
Bessel and coefficient-gauge results did not supply a physical source
identification. The closed proof uses the actual full norm estimates,
product integration and the corpus L-series asymptotic theorem.

Broad date-ordered arXiv searches used `entrainment` and `echo`.
[Ruling out matter-induced bumps in black-hole effective potentials](https://arxiv.org/html/2609.09284v1)
(September 8) requires consistency between matter, geometry and the
perturbation operator. No transfer of those source conditions to this
arithmetic family has been established.
[Shadows and gravitational perturbations of black bounces](https://arxiv.org/abs/2609.09487)
(September 8, abstract inspected) supplies no arithmetic balance law.
No external premise enters Lean.

RH remains unproved. Chain: literal PW response -> FE partner imbalance
-> positive Deninger Ward transmutation -> independent source-forced
fixed-grade balance -> RH. This result closes the full spatial-cancellation
test for the current coefficient family. The missing mathematical steps
are the source's physical pairing/domain, actual Xi spectral identification,
and independent balance at those occurrences.

The next attack is the literal Mellin transform of the unreflected source.
The candidate formula is Gamma(s+1/2)/zeta(z+s), initially where
Re(s)>-1/2 and Re(z+s)>1. Its atom admission and full interchange must be
proved before using that parameter relation. Extending the actual source
transform toward the critical strip requires signed endpoint control;
reflected all-parameter L1 admission does not supply it.

## Lean audit

Module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekGammaMobiusSameSourceMass.lean`.
The complete scratch passed, including all 31 public declaration axiom
checks with only propext, Classical.choice and Quot.sound. Identical proof
bodies were promoted and the umbrella import was wired. The targeted final build passed, rebuilding only the new leaf in 239s;
dependencies were reused. No full or umbrella build ran.

Repository-wide lint did not pass: six unrelated active modules lack
umbrella reachability: RHTower.EulerDeletionSignatureWordExpansion,
Sieve.MenonHarmonicRamareLadderSwapped,
Sieve.MenonHarmonicRamareLadderSwappedVolume, and HTGeometry.WeightedMinimax
Alternation, Coefficient and Perturbation. The new PW-B leaf is not flagged.
The separate active work was preserved. Index, API and local-link results
are recorded in the attack ledger.
