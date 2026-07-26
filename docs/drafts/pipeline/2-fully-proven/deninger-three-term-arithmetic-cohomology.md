# Three-term arithmetic cohomology and transverse flow

- **ID:** `deninger-three-term-arithmetic-cohomology`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Parent:** `deninger-derived-mw-rational-witt-coefficient`
- **Statement:** Every three-term coefficient complex has canonical \(H^0,H^1,H^2\), and
  every commuting transverse generator descends canonically to all three groups.

## Goal

Separate formal cohomological algebra from the open arithmetic construction.  The theorem
applies to the derived rational-Witt coefficient complex once that complex is constructed.
It does not identify an analytic Xi quotient with arithmetic cohomology.

## Gates

- [x] 0 → 1 in-progress: source-pure statement and direct proof
- [x] 1 → 2 fully-proven: dependency-closed proof below
- [ ] 2 → 3 formalized: direct Lean check of
  `DeningerArithmeticThreeTermCohomology.lean`
- [ ] 3 → 4 publication-ready: integrated with coefficient construction

## Theorem

`[PROVED HERE] [DAC_THREE_TERM_COHOMOLOGY]`

Let \(R\) be a commutative ring and
\[
 A^0\xrightarrow{d^0}A^1\xrightarrow{d^1}A^2,\qquad d^1d^0=0             \tag{1}
\]
a complex of \(R\)-modules.  Define
\[
\begin{aligned}
 H^0(A)&=\ker d^0,\\
 H^1(A)&=\ker d^1/\operatorname{im}d^0,\\
 H^2(A)&=A^2/\operatorname{im}d^1.                                      \tag{2}
\end{aligned}
\]
These are well-defined because `(1)` gives
\(\operatorname{im}d^0\subseteq\ker d^1\).

Suppose \(\Theta_q:A^q\to A^q\) satisfy
\[
 d^0\Theta_0=\Theta_1d^0,\qquad
 d^1\Theta_1=\Theta_2d^1.                                                \tag{3}
\]
Then `(3)` implies:

1. \(\Theta_0(\ker d^0)\subseteq\ker d^0\);
2. \(\Theta_1(\ker d^1)\subseteq\ker d^1\);
3. \(\Theta_1(\operatorname{im}d^0)\subseteq\operatorname{im}d^0\);
4. \(\Theta_2(\operatorname{im}d^1)\subseteq\operatorname{im}d^1\).

Therefore \(\Theta\) induces canonical endomorphisms on all three modules in `(2)`.

## Proof

For \(x\in\ker d^0\),
\[
 d^0\Theta_0x=\Theta_1d^0x=0.
\]
For \(y\in\ker d^1\),
\[
 d^1\Theta_1y=\Theta_2d^1y=0.
\]
If \(y=d^0x\), then
\[
 \Theta_1y=\Theta_1d^0x=d^0\Theta_0x,
\]
so degree-one boundaries are preserved.  If \(z=d^1y\), then
\[
 \Theta_2z=\Theta_2d^1y=d^1\Theta_1y,
\]
so degree-two boundaries are preserved.  Universal properties of submodules and quotient
modules give the induced maps.  No further hypothesis is used.

## Arithmetic specialization

For the Deninger program, take \(A^\bullet\) to be the realified completed
Galois/residue/power descent of the unit-amalgamated Milnor--Witt cochain coefficient on the
rational-Witt character space.  Coherent power correspondences and their suspended
infinitesimal action should supply `(3)`.  Proving that this concrete \(A^\bullet\) exists
remains the source-construction conjecture; theorem `DAC_THREE_TERM_COHOMOLOGY` supplies its
exact cohomological output but does not assume it.

## Hostile audit

- This theorem does not prove \(H^0\simeq\mathbb C\), \(H^2\simeq\mathbb C(-1)\), or that
  \(H^1\) has zeta zeros as spectrum.  Those are later source and comparison theorems.
- Replacing \(A^\bullet\) by the existing entire-function Xi complex would produce a valid
  instance of `(2)` but would not construct arithmetic cohomology; it is only a comparison
  target.
- The transverse generator is a cochain endomorphism, not another cohomological differential.

## Log

- 2026-07-26 — paper proof completed; Lean module written, direct check deferred while other
  workspace tasks occupy Lean processes.
