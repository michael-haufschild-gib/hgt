# Coarse invariant-sheaf Rost--Schmid descent

- **ID:** `deninger-coarse-invariant-sheaf-rost-schmid-descent`
- **Stage:** 1-in-progress
- **Type:** SOURCE CONJECTURE
- **Label:** `DAC_COARSE_INVARIANT_SHEAF_ROST_SCHMID_DESCENT`
- **Parent:** `deninger-arithmetic-rost-schmid-signature-resolution`
- **Statement:** Deninger's degreewise invariant coefficient sheaf has a
  two-column generic/prime derived-section resolution whose reduced
  hypercohomology is the three-term arithmetic cohomology.

## Source lock

Let
\[
 \pi:\widetilde X=\check X(\mathbb C)\times\mathbb R_{>0}
 \longrightarrow
 X=\widetilde X/\mathbb Q_{>0}
\]
be Deninger's rational-Witt suspension.  For a
\(\mathbb Q_{>0}\)-equivariant leafwise dg algebra
\(\widetilde{\mathscr A}^{\bullet}\), define the coefficient on the coarse
quotient degreewise:
\[
 \boxed{\mathscr A_X^\bullet
   :=(\pi_*\widetilde{\mathscr A}^{\bullet})^{\mathbb Q_{>0}}.}       \tag{1}
\]
This follows Definition 10.1 of Deninger's 2024 paper.  No derived
invariants, bar construction, group-cohomology complex, or prime-indexed
descent differential occurs in `(1)`.

For the untwisted degree-zero part,
\(\widetilde{\mathscr A}^0=\mathcal R_{\widetilde X}\), formula `(1)`
recovers Deninger's
\[
 \mathcal R_X=(\pi_*\mathcal R_{\widetilde X})^{\mathbb Q_{>0}}.
\]
The local coefficient is the source-defined leafwise analytic
Tate--Milnor/MW refinement constructed in
`DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE`.  Deninger's
\(Q_0(1)\)-regulator is an edge input; its cover-invariant target is not
declared to be the whole arithmetic \(H^1\).

## Generic and prime columns

Let \(j:X_\eta\hookrightarrow X\) be the generic stratum and let
\(i_p:X_p\hookrightarrow X\) be the compact packet over \(p\).  Define
\[
 G^{0,\bullet}
   :=R\Gamma\!\left(X,j_*\mathscr A_{X_\eta}^{\bullet}\right),        \tag{2}
\]
\[
 G^{1,\bullet}
   :=R\Gamma\!\left(
      X,\prod_p' i_{p,*}\mathscr A_{X_p}^{\bullet}
      \right).                                                       \tag{3}
\]
The restricted product topology is induced by finite rational-Witt
correspondences.  Twisted Milnor--Witt residues give the horizontal map
\[
 \partial_{\mathrm{RS}}:
 G^{0,\bullet}\longrightarrow G^{1,\bullet}.                         \tag{4}
\]
Frobenius/Verschiebung act on `(1)` and `(4)` by equivariant sheaf maps.
Prime powers control the local trace of `(4)` but do not form another
cohomological direction.

## Conjecture

`[CONJECTURE] [DAC_COARSE_INVARIANT_SHEAF_ROST_SCHMID_DESCENT]`

There is a source-defined complete locally convex enhancement of `(1)` for
which:

1. **Internal amplitude.**  Both `(2)` and `(3)` admit functorial
   Hausdorff derived-section representatives in degrees \(0,1\).
2. **Localization triangle.**  The map `(4)` represents the finite-place
   localization triangle for \(\mathscr A_X^\bullet\).  After adjoining
   the real signature orientation, arithmetic cohomology is
   \[
   R\Gamma_{\mathrm{arith}}(X,\mathscr A)
   \simeq
   \operatorname{Tot}\!\left(
     G^{0,\bullet}\xrightarrow{\partial_{\mathrm{RS}}}G^{1,\bullet};
     \mathbb R(-1)[-2]\right).                                      \tag{5}
   \]
3. **Three-term form.**  Formula `(5)` is represented by
   \[
   L^0=G^{0,0},\qquad
   L^1=G^{1,0}\oplus G^{0,1},\qquad
   L^2=G^{1,1}\oplus\mathbb R(-1),                                  \tag{6}
   \]
   with no cohomology outside degrees \(0,1,2\).
4. **Endpoints.**  Deninger's Theorem 10.2 identifies
   \(H^0_{\mathrm{arith}}\cong\mathbb R\) with generator \(0\), while
   residue/signature reciprocity identifies
   \(H^2_{\mathrm{arith}}\cong\mathbb R(-1)\) with generator \(1\).
5. **Regulator edge.**  The source regulator
   \[
   \Gamma(X_0,\mathcal O^\times)\otimes Q_0
   \longrightarrow
   H^1(\widetilde X,Q_0(1))^{\widetilde G}
   \]
   maps naturally to the degree-one edge of `(5)`.
6. **Residual non-scalar flow.**  Translation in \(\log u\) acts on
   `(1)` and `(5)`.  Its action on reduced \(H^1\) is not obtained by
   taking invariants of the already-computed pure Milnor cohomology; it
   records the failure of global sections to be exact on the irreducible
   nonproper coarse quotient and can therefore be non-scalar.
7. **Cup and trace.**  Frobenius reciprocity for MW residues and the real
   signature map makes `(5)` multiplicative and gives
   \[
   H^i_{\mathrm{arith}}\widehat\otimes
   H^{2-i}_{\mathrm{arith}}\longrightarrow\mathbb R(-1).
   \]
8. **Prime trace.**  On the reduced Hausdorff cohomology, the local
   distributional Lefschetz term of the packet \(X_p\) is supported at
   \(k\log p\) with coefficient \(\log p\) and the MW orientation sign.

## Why this avoids the two no-go theorems

- `DAC_PURE_SUSPENSION_SCALAR_SPECTRUM_NO_GO` applies when final
  cohomology is obtained from locally pure cohomology by exact
  invariants.  Clause 6 explicitly forbids that comparison.
- `DAC_DIAGONAL_POWER_RELATION_LEIBNIZ` exposes higher Koszul syzygies in
  a prime-indexed action presentation.  Construction `(1)` has no such
  presentation; primes enter only through codimension-one localization.

## Construction program

1. Define \(\widetilde{\mathscr A}^{\bullet}\) on finite pro-Stein
   rational-Witt charts with its Galois, power, Tate, and MW operations.
2. Form `(1)` degreewise and prove it is a sheaf of complete locally
   convex dg algebras on Deninger's coarse quotient.
3. Construct a quotient-adapted acyclic chart basis and prove the
   internal amplitude in clause 1 without commuting cohomology with
   invariants.
4. Construct the sheaf-level MW residue square and prove the localization
   triangle in clause 2.
5. Construct the archimedean signature boundary and prove global
   finite-plus-infinite reciprocity.
6. Pass to maximal Hausdorff quotients and prove closedness of the reduced
   differentials.
7. Compute local prime fixed-point traces before comparing with any zeta
   divisor or Xi determinant.

## Falsifiers

- Any proof replacing
  \(R\Gamma(X,(\pi_*\widetilde{\mathscr A})^{\mathbb Q_{>0}})\) by
  \(R\Gamma(\widetilde X,\widetilde{\mathscr A})^{\mathbb Q_{>0}}\)
  without an independent theorem is invalid.
- If reduced \(H^1\) is scalar under the flow, it cannot contain the
  nontrivial zeta spectrum.
- If the internal coarse-sheaf amplitude exceeds one, `(6)` does not
  follow.
- If the topology or norm uses Xi zeros, Weil positivity, or RH, the
  construction is circular.
- If the prime trace lacks the exact \(\log p\) coefficient, the explicit
  formula is not recovered.

## Current status

- Deninger's invariant-sheaf definition and \(H^0=\mathbb R\):
  literature-proved.
- Equivariant Tate regulator and local pro-Stein coefficient:
  literature/paper-proved.
- Abstract two-column totalization and cup/flow descent:
  paper-proved; Lean written, direct check deferred during external build
  saturation.
- Coarse invariant-sheaf internal amplitude, sheaf-level localization
  triangle, reduced closed-range theorem, and local prime trace: open.

**Verdict:** `ACTIVE SOURCE CONJECTURE; FIRST GLOBAL ARITHMETIC
COHOMOLOGY GATE`.

## Log

- 2026-07-26 — Extracted from the failure of prime-indexed diagonal
  descent after checking Deninger's Definition 10.1, Theorem 10.2, and
  Section 12 regulator construction.
