# Summable-compensator essential phase and reciprocal selection law

- **ID:** ULF-EFM-1
- **Stage:** 2-fully-proven
- **Type:** UNIVERSAL FORMATION / ESSENTIAL PROPERNESS / DUALITY SELECTION
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN-PROVED]
  [MECHANISM, NOT ROUTE] [ESSENTIAL QUOTIENT] [RECIPROCAL FIXED PHASE] [NOT RH]
- **Lean:** `HTGeometry.ConstitutiveEssentialFormationMechanics`

## 1. Higher mechanism

Exact equality is the wrong comparison for cofinal law formation.  Finite observers, local
counterterms, and summable reconstruction errors can change every finite chart without changing
whether total formation work is globally admitted.  The invariant object is therefore not a raw
formation ledger but its class modulo summable work.

For an index set `I` and real formation ledgers `a,b:I->R`, define

\[
 a\sim_{\mathrm{ess}}b
 \quad\Longleftrightarrow\quad
 \sum_{i\in I}|a_i-b_i|<\infty .
 \tag{EFM.1}
\]

This is the formation analogue of an essential operator class: finite and summable changes are
invisible, while a nonsummable cofinal change is a genuine phase event.

## 2. Essential-formation theorem

### Theorem 2.1 — quotient laws

Essential formation equivalence is an equivalence relation.  Moreover:

1. it preserves the global admitted phase,
   \[
   a\sim_{\mathrm{ess}}b
   \quad\Longrightarrow\quad
   \left(\sum_i|a_i|<\infty\iff\sum_i|b_i|<\infty\right);
   \tag{EFM.2}
   \]
2. every finite-support correction is essentially zero;
3. if `c` is summable, then `a=b+c` implies `a~ess b`.

#### Proof

Reflexivity follows from `a-a=0`; symmetry from `b-a=-(a-b)`; transitivity from

\[
 a-c=(a-b)+(b-c).
\]

Absolute summability is closed under negation and addition.  If `a-b` and `a` are summable, then
`b=a-(a-b)` is summable; the reverse direction is symmetric.  Finite-support functions are
absolutely summable.  The compensator statement is immediate from `a-b=c`.  QED.

This theorem explains a large class of no-go results at once: no finite cutoff repair, finite-rank
counterterm, or absolutely summable tail correction can move a formation across its admitted versus
escaping boundary.  Crossing that boundary requires a genuinely cofinal nonsummable event.

## 3. Prime interaction formation

The source-formation interaction theorem produces, for every prime `p` and exponent `sigma>0`,

\[
 a_\sigma(p)={4p^\sigma\over(1+p^\sigma)^2}.
 \tag{EFM.3}
\]

It satisfies

\[
 p^{-\sigma}\le a_\sigma(p)\le4p^{-\sigma},
 \qquad
 \sum_pa_\sigma(p)<\infty\iff\sigma>1.
 \tag{EFM.4}
\]

Thus exponent one is not introduced as a desired answer.  It is the formation/properness wall of
the literal prime interaction ledger.

## 4. Essential reciprocal selection

### Theorem 4.1 — fixed essential phase

For `0<sigma<2`,

\[
 \boxed{
 a_\sigma\sim_{\mathrm{ess}}a_{2-\sigma}
 \quad\Longleftrightarrow\quad
 \sigma=1.}
 \tag{EFM.5}
\]

#### Proof

If the difference is summable, Theorem 2.1 says `a_sigma` and `a_(2-sigma)` have the same
summability phase.  By `(EFM.4)`, this is

\[
 (\sigma>1)\iff(2-\sigma>1).
 \tag{EFM.6}
\]

Inside `0<sigma<2`, the two inequalities lie on opposite sides of one.  Their truth values agree
only when neither is strict, namely `sigma=1`.  Conversely, at `sigma=1` the two ledgers agree
pointwise.  QED.

### Corollary 4.2 — no summable compensator off criticality

If `0<sigma<2` and `sigma!=1`, there is no summable ledger `c` satisfying

\[
 a_\sigma(p)=a_{2-\sigma}(p)+c(p)
 \quad\text{for every prime }p.
 \tag{EFM.7}
\]

In particular, no finite-support correction can implement reciprocal matching away from the fixed
point.

### Theorem 4.3 — global bridge consumer

Let `A_sigma` be any source formation ledger.  Exact identification with the prime ledger is not
required.  If all three comparisons

\[
 a_\sigma\sim_{\mathrm{ess}}A_\sigma,
 \qquad
 A_\sigma\sim_{\mathrm{ess}}A_{2-\sigma},
 \qquad
 A_{2-\sigma}\sim_{\mathrm{ess}}a_{2-\sigma}
 \tag{EFM.8}
\]

hold for `0<sigma<2`, then `sigma=1`.

#### Proof

Transitivity of essential equivalence gives

\[
 a_\sigma\sim_{\mathrm{ess}}a_{2-\sigma}.
\]

Theorem 4.1 applies.  QED.

This is the exact global formation/properness consumer.  It tolerates finite and summable
renormalization on every leg.  Therefore the final producer need not manufacture an exact equality.

## 5. Formation–interaction field laws

Together with `ULF-ISDM-1`, the current field core is a mechanism with six laws:

1. **Formation:** a source creates local law cells with positive activation work.
2. **Interaction generation:** multiplication creates irreducible finite-support channels.
3. **Reconstruction:** the complete interaction packet reconstructs the marked product source.
4. **Passive conservation:** bounded-complexity observation moves, but does not destroy, work.
5. **Executor conservation:** lost coherent quantum Fisher information is four times hidden work.
6. **Essential selection:** a conservative reciprocal duality can identify formation classes only
   at the unique fixed properness phase.

This is a Frankenstein synthesis of source formation, Hoeffding interaction spectra, Hilbert
passivity, information geometry, summability ideals, properness, and duality.  None of those parent
languages alone supplies the coupled law.

## 6. Exact RH producer gate

Set

\[
 \sigma(s)=2\operatorname{Re}s.
 \tag{EFM.9}
\]

Functional-equation reflection `s -> 1-conj(s)` sends `sigma` to `2-sigma`.  The remaining global
producer theorem is therefore:

> **Global essential-duality formation theorem.** Construct, before zero specialization, a
> coefficient-faithful source formation ledger `A_s` and a source duality transport such that the
> two source-to-prime shadow errors and the reflected source-duality error in `(EFM.8)` all have
> summable work.

If this theorem applies to every spectral state producing a Xi zero, `(EFM.5)` forces
`sigma=1`, hence `Re(s)=1/2`.

This is strictly weaker than the repeatedly blocked demand for exact source equality or literal
null-homology.  It asks only that global duality mismatch have finite total formation work.  It is
also falsifiable: one nonsummable duality tail destroys the selection implication.

The producer theorem is not proved here.  Consequently this card is not an RH proof.

## 7. Hostile boundaries

1. The theorem selects a phase only after a pre-zero duality comparison is constructed.  Fitting
   that comparison from a Xi zero is circular.
2. Ordinary pointwise convergence to zero is insufficient; the mismatch must be absolutely
   summable.
3. A change of observer that does not preserve the source work ideal need not preserve the phase.
4. Compactness language is justified only after a route supplies an operator realization.  The
   theorem itself concerns summable ledgers, not arbitrary compact operators.
5. Essential equivalence forgets finite local data.  It cannot reconstruct exact coefficients
   without the full interaction packet retained in the underlying formation chart.
6. The critical exponent is selected by the joint formation-plus-duality law, not by summability
   or reflection alone.

## 8. Lean certificate

Lean proves, without project-added axioms:

- reflexivity, symmetry, and transitivity of essential formation equivalence;
- invariance of summability phase;
- inessentiality of finite-support corrections;
- reciprocal essential selection on `0<sigma<2`;
- impossibility of a summable reciprocal compensator off the fixed point.
- critical selection from any three-leg essential source bridge.

## Gates

- [x] route-independent mechanism stated
- [x] exact essential quotient and conservation phase
- [x] literal prime formation specialization
- [x] unique reciprocal fixed phase
- [x] finite/summable compensator no-go
- [x] Lean proof, no `sorry`, no added axioms
- [ ] global pre-zero essential-duality formation theorem
- [ ] coefficient-faithful landing on every Xi spectral state
- [ ] RH selection consequence
