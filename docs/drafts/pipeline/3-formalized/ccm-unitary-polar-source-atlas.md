# Unitary--polar source atlas for the complete Riemann divisor

- **ID:** UPSA-1
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** whole-corpus audit; `CCMRectangularFullObservableDivisorTomography`,
  `CCMFirstClockVolterra`, `SummableSpectrumScrewBohrCoefficients`
- **Statement:** Two explicit prime--Gamma source readouts reconstruct the complete centered Xi
  divisor with analytic multiplicity: Dirichlet poles recover the nonunitary/off-line sector, and
  the unique Bohr asymptote after subtracting that recovered sector recovers the unitary/critical
  sector.

## Goal

Public sentence: **growth records every nonunitary zero as a pole; recurrence records every unitary
zero as a quantized frequency; together the two source charts recover the whole divisor without
assuming where any zero lies.**

This removes the conditionality in the earlier first-clock Torelli law.  The literal first clock is
asymptotically almost periodic only under RH, but failure of almost periodicity is caused exactly by
the off-line sector.  That sector is independently and completely visible in the fixed-width
Dirichlet polar chart.  Subtracting its source-determined contribution leaves an unconditionally
almost-periodic critical signal.

## Claim labels

- `[CORPUS]` Fixed-width full observable continuation has simple poles exactly at shifted right
  Xi zeros and normalized residues equal analytic multiplicity.
- `[CORPUS]` Scaled literal first clock equals twice the real part of the complete rational Xi
  divisor for every physical aperture.
- `[CORPUS]` Summable nonnegative screw spectra are Bohr almost periodic; their Bohr coefficients
  aggregate collisions exactly; an almost-periodic function decaying at (+\infty) is zero.
- `[PAPER-PROVED]` The two-chart theorem below; exact proof is dependency-closed in this card.
- `[NOVELTY UNVERIFIED]` Priority of the combined source-specific atlas awaits exact literature
  audit.  Generic pole recovery, almost-periodic uniqueness, and coefficient extraction are not
  claimed new.

## Exact theorem

Write

\[
 z_q=(\rho_q-\tfrac12)(-i),\qquad
 K_T(z)=\frac{1-\cos(Tz)}{z^2-(2\pi/T)^2}.
\]

Let (Q_+\) be the divisor copies with \(\Re\rho_q>1/2\), and let

\[
 Q_0=\{q:\Im z_q=0\}
     =\{q:\Re\rho_q=1/2\}.
\]

For fixed (A>0\), let (a_A(n)\) be the complete rectangular logarithmic prime--Gamma source
coefficient and let (D_A(s)\) be its canonical meromorphic continuation to \(\Re s>1\).  Let

\[
 F(T)=T\,B_1(T)
\]

be the scaled literal first CCM source clock.  Define its polar-subtracted residual solely from the
pole data of (D_A\) by

\[
 F_0(T)=F(T)-4\Re\sum_{q\in Q_+}K_T(z_q),
\]

where a pole is repeated according to its normalized residue.

Then, unconditionally:

1. In \(\Re s>1\), (D_A\) has a simple pole at (p\) iff
   (p=1+(\rho-\tfrac12)\) for a right off-line Xi zero.  Its normalized residue is the analytic
   multiplicity of that zero.  Hence the polar chart reconstructs the complete off-line divisor:
   the right half directly and the left half by \(\rho\mapsto1-\rho\).
2. For every physical aperture,

   \[
   F_0(T)=2\Re\sum_{q\in Q_0}K_T(z_q).
   \]

3. The nonnegative critical screw series

   \[
   P_0(T)=2\sum_{q\in Q_0}\frac{1-\cos((\Re z_q)T)}{(\Re z_q)^2}
   \]

   converges uniformly, is continuous and Bohr almost periodic, and

   \[
   F_0(T)-P_0(T)\longrightarrow0\qquad(T\to+\infty).
   \]

   It is the unique continuous Bohr-almost-periodic asymptote of (F_0\).
4. For every \(\lambda\ne0\),

   \[
   \widehat P_0(\lambda)
     =-\frac{N_0(|\lambda|)}{\lambda^2},
   \]

   where (N_0(|\lambda|)\) is the exact number of critical divisor copies with
   \(|\Re z_q|=|\lambda|\).  Thus \(-\lambda^2\widehat P_0(\lambda)\) is an integer and recovers
   critical-line multiplicity without simplicity or rational-independence assumptions.
5. Polar support and normalized residues recover every off-line copy; Bohr support and quantized
   masses recover every critical copy.  Their disjoint union is the complete centered Xi divisor,
   hence determines its normalized even canonical product.

The theorem does not prove RH.  It makes RH the degenerate one-chart case: RH holds iff the polar
chart is empty, equivalently iff no subtraction is needed and the literal first clock itself has a
Bohr asymptote.

## Complete paper proof

### 1. Polar chart

For every fixed (A>0\), the corpus proves that (D_A\) is meromorphic on \(\Re s>1\), has
meromorphic order (-1\) precisely at

\[
 p_q=1+w_q,\qquad w_q=\rho_q-\tfrac12,qquad q\in Q_+,
\]

and is analytic elsewhere.  At (p_q\),

\[
 \operatorname{Res}_{p_q}D_A
  =2m_q\,A_A(w_q)^2,
\]

where (A_A(w_q)\ne0\).  Division by the explicit nonzero window factor returns (m_q\).  Pole
position returns (w_q=p_q-1\), hence \(\rho_q=p_q-1/2\) and
\(z_q=-iw_q\).  The functional equation sends every right copy to one left copy of the same
multiplicity and is an involution.  Therefore pole locations plus normalized residues determine
all and only the off-line divisor copies.  No zero was supplied to the reconstruction.

### 2. Exact divisor split

The first-clock kernel is even: (K_T(-z)=K_T(z)\).  Partition all Xi divisor copies by the sign of
\((iz_q).\Re=\Re\rho_q-1/2\).  Functional-equation reflection is a multiplicity-preserving
equivalence from the positive part to the negative part and sends (z_q\) to (-z_q\).  Absolute
summability of (K_T(z_q)\), already bounded by a constant times \(|z_q|^{-2}\), permits splitting
and reindexing the series.  Consequently

\[
 \sum_qK_T(z_q)
   =2\sum_{q\in Q_+}K_T(z_q)+\sum_{q\in Q_0}K_T(z_q).
\]

For (T\ge\pi/2\), the literal source identity gives

\[
 F(T)=2\Re\sum_qK_T(z_q).
\]

Subtracting the first term, reconstructed from the polar chart with its exact multiplicities,
proves the asserted identity for (F_0\).

### 3. Critical asymptote

For (q\in Q_0\), (z_q=\gamma_q\in\mathbb R\setminus\{0\}\).  The unconditional low-zero gap
gives \(|\gamma_q|>4\), and reciprocal-square summability of the full Xi divisor restricts to

\[
 \sum_{q\in Q_0}\gamma_q^{-2}<\infty.
\]

Thus the generic summable-spectrum theorem makes (P_0\) continuous and Bohr almost periodic.
For (T\ge2\pi\), put (u=2\pi/T\).  Direct subtraction gives, term by term,

\[
 0\le
 \frac{1-\cos(\gamma_qT)}{\gamma_q^2-u^2}
 -\frac{1-\cos(\gamma_qT)}{\gamma_q^2}
 \le\frac{2}{15}u^2\gamma_q^{-2}.
\]

Indeed (0\le1-\cos x\le2\), (u^2\le1\), \(\gamma_q^2>16\), and

\[
 \frac{1-\cos(\gamma_qT)}{\gamma_q^2-u^2}
 -\frac{1-\cos(\gamma_qT)}{\gamma_q^2}
 =\frac{(1-\cos(\gamma_qT))u^2}
        {\gamma_q^2(\gamma_q^2-u^2)}.
\]

Summing the nonnegative inequalities is legitimate by reciprocal-square domination and yields

\[
 0\le F_0(T)-P_0(T)
 \le\frac4{15}(2\pi/T)^2\sum_{q\in Q_0}\gamma_q^{-2}\to0.
\]

If (P\) is another continuous Bohr-almost-periodic asymptote, then (P-P_0\) is continuous,
Bohr almost periodic, and tends to zero at (+\infty\).  The generic rigidity theorem forces
(P-P_0=0\).  Hence (P_0\) is unique.

### 4. Quantized critical multiplicity

Uniform convergence allows the Bohr coefficient to pass through the critical screw series.  One
atom (2a(1-\cos\omega T)\) has coefficient (-a\) at \(\lambda=\omega\) and at
\(\lambda=-\omega\), and zero at every other nonzero frequency.  Collisions therefore add rather
than cancel.  At a fixed \(\lambda\ne0\), every contributing atom has
(a=1/\gamma_q^2=1/\lambda^2\), so

\[
 \widehat P_0(\lambda)
  =-\lambda^{-2}\#\{q\in Q_0:\gamma_q=\lambda\text{ or }-\gamma_q=\lambda\}.
\]

The fibre is finite because it is contained in the union of the two finite Xi spectral-point
fibres at \(\lambda\) and \(-\lambda\).  This proves the exact cardinal formula.

### 5. Completeness

Every divisor copy satisfies exactly one of \(\Re\rho>1/2\), \(\Re\rho=1/2\), or
\(\Re\rho<1/2\).  Steps 1 and 4 recover the first two sectors; reflection recovers the third.
Support points and their recovered integer copy counts are exactly the divisor with analytic
multiplicity.  A normalized genus-one/even canonical product is determined by that divisor, so the
two charts are complete.

## Hostile falsity and circularity audit

- **Not RH in disguise.**  No recurrence assumption is made.  Almost periodicity is proved only
  after the off-line sector, already recovered by a separate source observable, is subtracted.
- **No divisor smuggling.**  The subtraction uses (p_q-1\) and the integer normalized residue,
  both read from source-continuation poles.  The divisor notation is a proof coordinate, not an
  input to the reconstruction.
- **No loss from collisions.**  Polar residues recover analytic multiplicity at repeated poles;
  Bohr coefficients aggregate equal absolute critical frequencies with a fixed sign.
- **No hidden simplicity or independence.**  The index is the multiplicity-copy type; all sums
  and fibre counts retain repeated zeros.  Generic Bohr extraction allows arbitrary frequency
  relations.
- **No bounded-operator claim.**  Meromorphic continuation and exact asymptotic mean are singular,
  infinitary readouts.  Existing Rees and recurrence-instability no-gos therefore do not apply.
- **Scientific risk.**  The mathematical theorem may still be judged a synthesis of exact
  transforms rather than a new foundational result.  Promotion requires a literature audit of the
  source-specific two-chart completeness statement, not keyword novelty.

Verdict: `SURVIVES PRELIMINARY ATTACK` and `[PAPER-PROVED]`.

## Gates

- [x] 0 -> 1: exact source-pure statement, non-circular reconstruction, hostile attack
- [x] 1 -> 2: complete paper proof above; no open mathematical dependency
- [x] 2 -> 3: exact unconditional Lean theorem, targeted compile, lint, axiom audit
- [ ] 3 -> 4: literature audit, manuscript rewrite, antagonistic journal review

## Lean plan after paper closure

1. Define critical multiplicity-copy subtype and critical screw/rational series.
2. Prove the exact right/left/critical first-clock partition by absolute summability and reflection.
3. Generalize the existing RH-side one-atom bound to a critical-copy hypothesis and sum it.
4. Prove unconditional residual convergence, Bohr uniqueness, and coefficient/cardinality law.
5. Bundle these with existing polar support/residue theorems in one source-atlas capstone.

## Log

- 2026-08-01 — froze UPSA-1 after full-source polar/Bohr synthesis; closed paper proof and hostile
  circularity audit before Lean work.
- 2026-08-01 — exact Lean closure in
  `formal/GaloisForLFunctions/RHTower/CCMUnitaryPolarSourceAtlas.lean`: strict-right polar
  support/residue recovery, right/left/critical divisor partition, residual critical identity,
  unique Bohr asymptote, exact critical multiplicity recovery, multiplicity-preserving complete
  divisor equivalence, and normalized canonical-product reconstruction. Direct elaboration, final
  module build, umbrella reachability, lint, and axiom audits pass; capstones use only `propext`,
  `Classical.choice`, and `Quot.sound`.
