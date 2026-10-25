# Bounded Meyer flow orbits live in critical top jets

- **ID:** bounded-meyer-flow-orbits-live-in-critical-top-jets
- **Stage:** 2-fully-proven
- **Type:** THEOREM (core classification); extensions awaiting Lean verification
- **Source:** Q-II; faithful Hilbert–Schmidt reserve and genuine full-Hasse flow.
- **Statement:** An actual Meyer source has bounded centered-flow orbit in Hilbert–Schmidt convolution norm exactly when its Xi jets vanish off the critical line and only the highest jet survives in each critical multiplicity block.
- **Status:** CORE FORMALIZED. The four-way orbit classification and fixed-source/global criteria passed actual-file check and all six axiom audits. Product, radical, nontriviality and reserve-flow extensions remain unverified. External novelty unverified.

## Exact theorem

For an actual strong logarithmic source `g`, write `T(g)` for its existing
full-Hasse convolution operator and `F_c(g)` for the existing centered source
flow. The following conditions are equivalent:

1. `sup_{c in R} ||T(F_c(g))||_HS < infinity`.
2. Every individual lower raw Xi-jet reading of `F_c(g)` is bounded over all
   real `c`; the bound may depend on the point and jet order.
3. All lower jets vanish at every off-line Xi point. At a critical point
   of multiplicity `m`, all orders strictly below `m-1` vanish.
4. `||T(F_c(g))||_HS = ||T(g)||_HS` for every real `c`.

These are statements about actual admitted sources, not arbitrary prescribed
infinite jet families. The genuine source quotient retains all these jets.

## Formalized bounded-orbit argument

Every actual convolution operator is Hilbert–Schmidt by its existing
resolvent factorization. Let `a_j` be the raw Mellin jet at a fixed Xi point
`rho` of multiplicity `m`. The proved confluent source flow law gives

`a_j(F_c g) = exp(c(rho-1/2)) sum_{i=0}^j choose(j,i)c^i a_(j-i)`.

This is `deningerMeyerStrongLogMellinJetLM_flow`, followed by the defining
centered scalar. No asymptotic interchange enters this finite formula.

**1 implies 2.** The first column of `T(F_c g)` contains the Hasse reading
`a_j(F_c g)/j!`. Each coordinate is bounded by the column norm, the column
norm by the operator norm, and the operator norm by the Hilbert–Schmidt
norm. Thus `|a_j(F_c g)|<=j! ||T(F_c g)||_HS`.

**2 implies 3 off the line.** Induct on `j`. Once the lower coefficients
vanish, the displayed flow formula is `exp(c(rho-1/2)) a_j`. If `a_j!=0`,
two-sided boundedness forces `Re rho=1/2`, by the existing bounded
eigenfunctional-orbit theorem. Therefore every `a_j` vanishes off the line.

**2 implies 3 on the line.** A bounded affine function `b+c a` on the real
line has `a=0`: otherwise `|c a|<=C+|b|` for every `c`, contradicted by
`c=(C+|b|+1)/|a|`. Induct on `j<m-1`. With all lower `a_k=0`, the `(j+1)`-st
flow reading is

`exp(c(rho-1/2)) (a_(j+1)+(j+1)c a_j)`.

The character has modulus one. Boundedness and the affine argument force
`(j+1)a_j=0`, hence `a_j=0`. This avoids any unproved general polynomial
growth lemma.

**3 implies 4.** For every lower jet, the flow now multiplies its value by
`exp(i c Im rho)`; this also holds off the line because those jets are zero.
The exact triangular convolution formula therefore gives, for every Hilbert
vector `x` and coordinate `q=(rho,j)`,

`(T(F_c g)x)_q = exp(i c Im rho) (T(g)x)_q`.

Every coordinate norm, hence every column norm, is unchanged. The admitted
Hilbert–Schmidt sum of squared column norms is unchanged. This uses equality
of summands, not an unproved uniform domination across Xi points.

**4 implies 1** with the finite bound `||T(g)||_HS`.

## Positive carrier and its product

The classes satisfying condition 3 form a complex linear subspace, stable
under arithmetic sharp and convolution. It consists of critical highest
local jets, including nilpotent jets at multiple critical zeros.

At a critical point of multiplicity one, multiplication retains ordinary
value multiplication. At multiplicity greater than one, the product of two
highest monomials has order `2(m-1)>=m`, hence vanishes in the actual quotient.
Distinct blocks have zero mixed product. Thus the multiple-critical part is
an annihilating square-zero ideal inside this bounded-orbit algebra.
Arithmetic sharp preserves each critical block and signs its highest jet by
`(-1)^(m-1)`. A nonzero highest class in a multiple critical block therefore
has zero sharp square but positive faithful Hilbert–Schmidt mass.

The carrier is nontrivial unconditionally: `exists_xiZeroCopy_re_eq_half`
supplies a critical point; the actual finite causal source isolating its
highest jet is nonprincipal. Full jet synthesis and the exact boundary
kernel certify this directly, regardless of that point's multiplicity.

Ordinary trace on this carrier sees exactly its simple-critical value part.
Its radical consists of the multiple-critical highest jets: the actual
simple-critical value class and its imaginary multiple separately probe the
real and imaginary value at each simple critical point, while every multiple
highest jet has zero value. This applies the proved value-only trace radical
law with explicit probes inside the bounded-orbit carrier. No existence of a
multiple zero is asserted.

## Global and fixed-source corollaries

All actual sources have bounded Hilbert–Schmidt centered-flow orbit exactly
when every Xi point is simple and critical. Necessity uses an actual source
with nonzero zeroth jet at any chosen point; condition 3 then forces that
point to be critical and its multiplicity to be one. Sufficiency is immediate
from condition 3.

The same equivalence already holds for the one existing compact source
`deningerMeyerXiAvoidingSource`, whose zeroth Mellin value is nonzero at every
Xi point. Thus replacing its known pointwise zeroth-orbit bound by a bound
on its full faithful Hilbert–Schmidt orbit strengthens the endpoint from RH
to RH plus simplicity. That stronger hypothesis must not be advertised as
an RH-only producer.

The faithful source/sharp reserve from
`../3-formalized/hilbert-schmidt-reserves-measure-the-arithmetic-adjoint-defect.md` is invariant
on this bounded-orbit carrier. Its invariance on every actual source is also
equivalent to simple critical zeros: it bounds each source operator's squared
HS norm, and the converse follows from the norm isometry above.

## Corpus audit and Lean obligations

- `DeningerMeyerXiSpectralInclusion`: exact raw jet flow formula.
- `DeningerMeyerHalfDensityFiniteXiJetVerticalDefect`: centered finite full-jet transport.
- `DeningerMeyerFaithfulConvolution`: first-column recovery and genuine boundary kernel.
- `HilbertSchmidtCompact.opNorm_le_hsNorm`: coordinate admission bound.
- `DeningerMeyerXiAvoidingCenteredOrbitCriterion`: bounded nonzero eigenfunctional
  forces imaginary exponent; fixed compact source avoids every Xi value zero.
- `XiRealCriticalPointSignLaw.exists_xiZeroCopy_re_eq_half`: unconditional nontriviality.
- Exact finite Hasse algebra: paper proof complete, Lean verification pending.

Searches located the preceding mechanisms but no full bounded-orbit critical-highest-jet
classification. The four-way equivalence and fixed-source/global criteria are now
formalized. Exact product/radical corollaries, unconditional nontriviality and
reserve-flow assertions still await verification.
The core source/jet bounds are drafted in
`ArithmeticCastelnuovoSeveri/MeyerHilbertSchmidtSource.lean` (actual-file certified); the four-way classification and
fixed-source/global criteria are drafted in
`ArithmeticCastelnuovoSeveri/MeyerBoundedCenteredOrbits.lean` (certified). The product,
trace-radical, and nontriviality endpoints are present in the actual
`ArithmeticCastelnuovoSeveri/MeyerCriticalTopAlgebra.lean` candidate, also unverified.
This jet-selected restricted carrier does not supply an independent all-source
RR/Bézout mechanism on the original scaling surface.

Direct `lake --old env lean` check **20136** passed with only `propext`,
`Classical.choice`, and `Quot.sound` in all six endpoint audits:

- `meyerHilbertOrbitBounded_iff_criticalTopJets`
- `meyerJetOrbitBounded_iff_criticalTopJets`
- `meyerHilbertOrbitIsometric_iff_criticalTopJets`
- `meyerXiAvoidingHilbertOrbitBounded_iff`
- `all_meyerHilbertOrbits_bounded_iff`
- `all_meyerHilbertOrbits_isometric_iff`

Temporary prints and the core scratch draft are removed; the core module is
wired and documented. This card remains in stage 2 until its remaining
algebra and reserve-flow extensions pass their own Lean checks.

The actual algebra module contains positive trace, radical-annihilation, and
unconditional nontriviality endpoints. Its inputs are the exact full-jet algebra
and bounded-orbit classification; its direct check and axiom audit are pending.
It also explicitly defines `meyerCriticalTopCohomologySubmodule`, with candidate
proofs of its representative criterion, sharp and convolution closure, and
nontriviality, so the paper's quotient-subspace assertion has its own Lean object.

## Exact reserve orbit law

Arithmetic sharp reverses centered flow: sharp(F_c g)=F_(-c)(sharp g), by the
Mellin character formula and injectivity. The faithful reserve is the mean
of the two squared HS norms. It is constant on a critical highest-jet orbit,
because both source and sharp are in that carrier. Conversely any finite
upper bound for the reserve bounds the first squared HS norm by twice that
constant, hence forces the same critical highest-jet condition. Therefore
reserve boundedness, reserve invariance, and critical highest-jet support are
equivalent for each actual source. Global invariance is exactly the faithful
cone RR condition, both equivalent to simple criticality. Actual candidate:
`ArithmeticCastelnuovoSeveri/MeyerHilbertReserveFlowRigidity.lean`, importing
`FaithfulHilbertSchmidtSourceReserves.lean`. Direct verification is pending;
the old scratch copy does not contain every subsequent correction.
