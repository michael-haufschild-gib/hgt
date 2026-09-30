# Multiplicity-exact hyperbolic blocks and index of the physical Fermi witness form

- **ID:** pm-fermi-multiplicity-hyperbolic-signature
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Route:** PM, alternating Nyman–Beurling physical witness signature
- **Novelty:** exact physical statement not found in scoped corpus/public searches; global absence from literature or training data cannot be certified

## Exact statement

Let `W` consist of continuous complex functions on `(0,1]` with integrable squared norm and

`integral_0^1 phi_a(t) conj(w(t)) dt = 0` for every `a>=1`,

where `phi_a(t)={1/(at)}-2{1/(2at)}`. Define

`q(u,v)=integral_0^(1/2) u conj(v) - (1/2) integral_0^1 u conj(v)`.

For every finite set `S` of actual zeta zeros in `1/2<Re rho<1`, let
`M(S)=sum_(rho in S) ord_rho(zeta)`, using analytic multiplicity. There are literal witnesses
`v_a^-`, `v_a^+`, one pair for every multiplicity slot, satisfying

`q(v_a^-,v_b^-)=-delta_ab`, `q(v_a^+,v_b^+)=delta_ab`, `q(v_a^-,v_b^+)=0`.

The extended total right-strip multiplicity equals `witnessNegIndex`. The intrinsic Lean
capstones have no hypothesis parameters:

- `exists_rightStripMultiplicity_hyperbolic (s : Finset rightStripZeros)`
- `rightStripMultiplicityCount_le_witnessNegIndex`
- `witnessNegIndex_eq_rightStripMultiplicityCount`

No RH, simplicity, source positivity, spectral completeness, or new axiom is assumed.

## Dependency-closed paper proof

1. The literal generator is bounded and supported on a finite interval, hence MellinRapid. Its
   source transform is an analytic prefactor times zeta away from `0` and `1`. At a right-strip
   zero of order `m`, all derivatives below `m` vanish. Mellin differentiation identifies them
   with orthogonality of `conj(log(t)^j t^(rho-1))`, `j<m`. Their squared norms are integrable
   because `Re rho>1/2`; continuity holds on `(0,1]`.
2. Put `c(s)=2^(-s)-1/2`. This is analytic and nonzero for `Re s<1`. Expand the conjugate jet of
   `t^(s-1)/c(s)` into the preceding log-power witnesses; call it `h_(rho,j)`.
3. Existing literal spurious witnesses `g_l` have neutral mutual pairing and pair with the
   unnormalized power witness by `c(s)/(s-d_l)`, where the nodes `d_l` are distinct and imaginary.
   Compactly supported cuts of `g_l` are MellinRapid. Differentiating both integrals defining `q`
   is therefore justified at every order. The product rule cancels `c` against its reciprocal:

   `q(g_l,h_(rho,j))=(-1)^j j! ((rho-d_l)^(-1))^(j+1)`.

4. Change Cauchy control nodes to `x_rho=-rho`, `t_l=-d_l`. The coupling columns are the corpus's
   confluent Cauchy columns multiplied by nonzero factors `(-1)^j j!`. Distinct zero nodes,
   injective imaginary spurious nodes and real-part separation give surjectivity of the existing
   complex Cauchy-jet control map. Thus finite spurious combinations `g_a` satisfy
   `q(g_a,h_b)=delta_ab` and `q(g_a,g_b)=0`.
5. For `Q_ab=q(h_a,h_b)`, define

   `v_a^r=h_a+(1/2) sum_b (r delta_ab-Q_ab) g_b`, for real `r`.

   Sesquilinearity and `conj(Q_ba)=Q_ab` give
   `q(v_a^r,v_b^s)=((r+s)/2) delta_ab`. Taking `r,s` in `{-1,1}` proves both signed blocks and their
   cross orthogonality.
6. Zeta is analytic on the punctured plane, which is connected, and is nonzero at `2`. Its
   analytic order is therefore finite at every right-strip zero. The packet index set has exactly
   `M(S)` elements. Reindex its negative block by `Fin M(S)` and apply the definition of negative
   index. Taking the supremum over all finite `S` proves the unconditional extended bound.
7. For a literal witness `w`, its conjugate correlation-Mellin transform is analytic on
   `Re s>0`. Conjugating its derivatives at each actual right-strip zero gives complex-linear
   coordinates `J_(rho,j)(w)` for every `j<ord_rho(zeta)`. Finite witness sums commute exactly
   with these coordinates by Mellin linearity and analytic differentiation.
8. If the coordinate packet vanishes, correlation has at least zeta's local analytic order
   at every possible left-defect pole. Multiplication by the analytic numerator prefactor and
   division by the nonzero-germ entire zeta denominator leave nonnegative meromorphic order.
   Existing unconditional removability then makes `w` dyadically self-similar, hence `q(w,w)=0`.
9. A coefficient sum in a negative orthonormal family has quadratic form `-sum |c_i|²`.
   Step 8 therefore makes its coordinate map injective. For a finite zero set, the coordinate
   target has dimension exactly the sum of multiplicities. For an infinite zero set, positivity
   of every finite multiplicity makes the extended count infinite. Both cases give the matching
   upper bound and exact equality, without assuming finiteness or simple zeros.

## What is new relative to the recorded PM frontier

PM-18 counted distinct zero locations. This theorem counts every analytic multiplicity slot and
constructs both signs simultaneously in the literal physical witness class. It closes the lower
bound half of PM-19b. Correlation jets and local pole cancellation also close the upper bound,
so PM-19b's exact multiplicity index is now formalized. Source-side nonnegative half-mass remains open.

## Prior-art comparison

Burnol's [On Fourier and Zeta(s)](https://empslocal.ex.ac.uk/people/staff/mrwatkin/zeta/burnol5.pdf),
Theorem 7.1, already relates zero multiplicity to orthogonality of jet vectors. Logarithmic admission
alone is not claimed new. Scoped public searches for Nyman–Beurling with dyadic forms, negative
index, inertia, indefinite signature and multiplicity found no exact matching hyperbolic theorem.
The public 2026 Weil-form inertia framework uses another form and another construction. The
candidate contribution is the exact literal Fermi pairing and hyperbolic completion, not generic
Hermitian linear algebra or the classical Nyman closure criterion.

## Lean and audit

- `FermiNymanLogarithmicWitness.lean`: all-order literal admission; targeted build and final direct audit passed.
- `FermiNymanConfluentCoupling.lean`: normalized confluent pairing; targeted build and final direct audit passed.
- `FermiNymanMultiplicitySignature.lean`: neutral duals, signed completion and intrinsic multiplicity capstones; targeted build and final direct audit passed.
- `FermiNymanCorrelationJets.lean`: local order cancellation and complex-linear correlation coordinates; targeted build and final direct audit passed.
- `FermiNymanMultiplicityIndex.lean`: intrinsic exact multiplicity index; targeted build and final direct audit passed.
- All five leaves wired into `RHTower.lean`; no full or umbrella build run.
- Axiom audits of admission, coupling, both lower capstones, local pole cancellation, coordinate linearity and intrinsic exact index equality passed: only `propext`, `Classical.choice`, `Quot.sound`.
- Generated indexes refreshed. Formal lint with `--check-generated` ran; no PM errors or admission-policy errors, but global gate failed on 15 unrelated concurrently added modules unreachable from `RHTower.lean`. Those write scopes were preserved. No claim that the global gate passed.

## Next conjecture

Exact algebraic rank of the literal dyadic difference `w(t/2)-w(t)`: negative families have
independent differences, while independent-difference families inject into correlation jets.
The paper proof is closed in `3-formalized/pm-dyadic-defect-rank.md`; Lean audit pending.
