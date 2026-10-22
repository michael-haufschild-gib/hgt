# CCM-FU anchored positive-kernel frontier

- **ID:** CCM-FU-APK1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route CCM-FU, literal third-grade completed prime--polar source
- **Statement:** The normalized CCM-FU Cesàro primitive is exactly one positive-kernel signed
  average of anchored completed-error increments, and its uniform boundedness is equivalent to the
  existing RH-bearing linear Cesàro bound.

## Goal

Replace reporter-side coercivity and separate prime/polar estimates by an exact source-native
coordinate for the open CCM-FU bound.  This is a bridge, not an RH proof: the remaining arithmetic
task is uniform signed control of the displayed anchored moment.

## Gates

- [x] 0 → 1 in-progress: literal source, fixed positive lower wall, no source substitution
- [x] 1 → 2 fully-proven: dependency-closed finite-interval paper proof below
- [x] 2 → 3 formalized: module
  `GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilThirdGradeCesaroAnchoredMoment`
- [ ] 3 → 4 publication-ready: integrate into a standalone CCM-FU paper

## Corpus-first audit

Searches were run with `scripts/formal_tools.py research` before conjecturing.  Corpus already had:

- the literal completed-error flux formula for the third-grade cumulative source;
- the second Abel/Cesàro RH criterion;
- the signed FU reporter and source-relative escaped boundary jet;
- unit-Riesz/Volterra transports and all-depth von Mangoldt--Gamma carriers;
- exact actual-head signed producers and the coherent quantile no-go.

No declaration or text match supplied the anchored identity below, its exact kernel mass, or the
equivalence of the literal linear bound with boundedness of this single signed moment.

Current Suzuki/CCM primary sources checked during the route audit formulate operator realizations,
screw-function criteria, and open cofinal convergence questions.  No matching anchored
third-grade Cesàro kernel formula was located.  This is an internal novelty result; no priority
claim is made without a dedicated external review.

## Conjecture / failure / pivot log

1. **Fixed signed-FU graph energy controls the source.** Falsified as a landing: the reporter symbol
   has an affine zero, so reporter coercivity cannot recover the low-frequency primitive without a
   source law.
2. **Midpoint codiagonal positivity controls the primitive.** Falsified: the exact codiagonal is
   completed-error self-energy, with the wrong inequality direction for an upper bound.
3. **Quantile or cellwise absolute transport.** Falsified: the canonical coherent chi-square
   reserve is strictly negative on every nonzero actual head; absolute transport pays the critical
   half-density.
4. **Unit-Riesz/prime-co-shift transfer.** Falsified as a direct proof: unconditional control is for
   `exp(-h/2) E(h)`, while inversion to the FU primitive restores `exp(h/2)`.  This is exactly the
   missing arithmetic cancellation.
5. **Pivot: integrate the already exact completed-error flux once, but retain its lower-wall
   coefficient.** This yields the theorem below.  The lower-wall term is not an extra debt: it is
   exactly the total mass of the positive kernel and therefore becomes an anchored error
   difference.

## Theorem

Let

\[
E(h)=\operatorname{criticalMellinCompletedError}(h),\qquad
q_b(h)=\operatorname{ccmGuinandWeilThirdGradeCumulativeMeasurable}(b,h),
\]

and

\[
Q_b(H)=\int_b^H q_b(s)\,ds,
\qquad
K_H(h)=\frac{96-64h/H}{h^4}.
\]

For `0 < b ≤ H`,

\[
\frac{Q_b(H)}{H}
=\int_b^H K_H(h)\bigl(E(b)-E(h)\bigr)\,dh. \tag{1}
\]

Moreover, for `b ≤ h ≤ H`,

\[
0<K_H(h),\qquad \frac{32}{h^4}\le K_H(h)\le\frac{96}{h^4}, \tag{2}
\]

and its exact mass is

\[
\int_b^H K_H(h)\,dh=\frac{32}{b^3}\left(1-\frac bH\right). \tag{3}
\]

Consequently, for every fixed `b>0`, the literal CCM-FU linear Cesàro bound is equivalent to

\[
\sup_{H>b}\left|
  \int_b^H K_H(h)\bigl(E(b)-E(h)\bigr)\,dh
\right|<\infty. \tag{4}
\]

## Paper proof

The corpus flux identity gives, on every finite physical window,

\[
q_b(s)=\frac{32E(b)}{b^3}-\frac{32E(s)}{s^3}
       -\int_b^s\frac{96E(h)}{h^4}\,dh. \tag{5}
\]

All terms are interval-integrable.  Integrating (5) in `s` and applying finite-interval integration
by parts to the last primitive gives

\[
\begin{aligned}
Q_b(H)
 &=\frac{32E(b)}{b^3}(H-b)
   -32\int_b^H\frac{E(h)}{h^3}\,dh
   -\int_b^H\int_b^s\frac{96E(h)}{h^4}\,dh\,ds\\
 &=\frac{32E(b)}{b^3}(H-b)
   +64\int_b^H\frac{E(h)}{h^3}\,dh
   -96H\int_b^H\frac{E(h)}{h^4}\,dh. \tag{6}
\end{aligned}
\]

Divide by positive `H` and combine the last two integrals:

\[
\frac{Q_b(H)}H
=\frac{32E(b)}{b^3}\left(1-\frac bH\right)
 -\int_b^H\frac{96-64h/H}{h^4}E(h)\,dh. \tag{7}
\]

Direct antiderivatives give (3).  Substituting (3) into the first term of (7) proves (1).  Since
`0<h/H≤1` on the physical window, the numerator of `K_H` lies in `[32,96]`, proving (2).

If `|Q_b(H)|≤C(H+1)`, (1) is uniformly bounded because
`(H+1)/H≤1+1/b` for `H>b`.  Conversely, a uniform bound `C` in (4), multiplied by `H`, gives
`|Q_b(H)|≤CH≤C(H+1)`.  This proves the equivalence.

## Scientific consequence

CCM-FU no longer lacks a lawful bridge between reporter geometry and the literal arithmetic
source.  Its open core is precisely boundedness of one anchored, positive-kernel, signed
completed-error moment.  Positivity belongs to the transport kernel, while cancellation remains
entirely in `E(b)-E(h)`; estimating positive and negative FU regions separately destroys exactly
the information needed for (4).

The kernel has only inverse-quartic decay, bounded below by `32/h^4`.  Therefore the corpus's
unconditional bound on `exp(-h/2)E(h)` cannot close (4): undoing the half-density produces an
exponential loss.  Any successful producer must act directly on anchored prime--polar increments
or produce a graph-dual estimate at this exact inverse-quartic grade.

## Lean certificate

Formal declarations:

- `ccmCesaroPrimitive_thirdGradeCumulative_eq_errorMoment`
- `integral_ccmGuinandWeilThirdGradeCesaroErrorKernel`
- `ccmCesaroPrimitive_thirdGradeCumulative_div_eq_anchoredErrorMoment`
- `ccmGuinandWeilThirdGradeCesaroErrorKernel_pos`
- `ccmGuinandWeilThirdGradeCesaroErrorKernel_bounds`
- `ccmGuinandWeilThirdGradeCesaroLinearBound_iff_anchoredMomentBound`
- `riemannHypothesis_of_ccmGuinandWeilThirdGradeCesaroAnchoredMomentBound`

The module is wired into `GaloisForLFunctions.RHTower`.  No axiom, `sorry`, computation, or
asymptotic premise is introduced.

## Log

- 2026-08-19 — corpus audit; four producer conjectures rejected at exact source mismatch.
- 2026-08-19 — anchored positive-kernel identity proved on paper and in Lean.
