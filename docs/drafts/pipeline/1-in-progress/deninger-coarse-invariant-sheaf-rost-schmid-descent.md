# Coarse invariant-sheaf Rost--Schmid descent

- **ID:** `deninger-coarse-invariant-sheaf-rost-schmid-descent`
- **Stage:** 1-in-progress
- **Type:** SOURCE CONJECTURE
- **Label:** `DAC_COARSE_INVARIANT_SHEAF_ROST_SCHMID_DESCENT`
- **Parent:** `deninger-arithmetic-rost-schmid-signature-resolution`
- **Statement:** Deninger's derived true-to-approximate coefficient on
  the coarse suspension has a two-column generic/prime resolution whose
  reduced hypercohomology is the three-term arithmetic cohomology.

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
This is Deninger's raw Definition 10.1.  No derived
invariants, bar construction, group-cohomology complex, or prime-indexed
descent differential occurs in `(1)`.

`DAC_COARSE_INVARIANT_SHEAF_EXISTENCE` proves that `(1)` is a genuine
dg-algebra sheaf, functorial for every commuting source operation.
This closes existence of the coarse coefficient.  It deliberately
does not commute fixed points with cohomology or derived colimits.

For the untwisted degree-zero part,
\(\widetilde{\mathscr A}^0=\mathcal R_{\widetilde X}\), formula `(1)`
recovers Deninger's
\[
 \mathcal R_X=(\pi_*\mathcal R_{\widetilde X})^{\mathbb Q_{>0}}.
\]
Raw `(1)` is not the missing arithmetic coefficient: on the generic
rational-Witt fibre, Kucharczyk--Scholze prove that its degree-two cup
product violates the Steinberg relation.  The corrected source is
\[
 \mathscr E_{\mathrm{Den}}
 =R\alpha_*\mathcal G                                             \tag{1a}
\]
as specified by `DAC_TRUE_TO_APPROXIMATE_DERIVED_COEFFICIENT`.
`DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE` constructs its
equivariant Tate--Milnor cover sheaf.  Its chartwise Milnor computation
is `DAC_CHARACTER_SHAPE_FORMALITY` plus
`DAC_ALGEBRAIC_CYCLOTOMIC_MILNOR_AMPLITUDE`; transferring that
calculation to the coarse suspension remains
`DAC_SHEAFIFIED_UNIT_AMALGAMATION_COMPARISON`.  Deninger's
\(Q_0(1)\)-regulator is an edge input; its cover-invariant target is
not declared to be the whole arithmetic \(H^1\).

## Generic and prime columns

Let \(j:X_\eta\hookrightarrow X\) be the generic stratum and let
\(i_p:X_p\hookrightarrow X\) be the compact packet over \(p\).  Define
\[
 G^{0,\bullet}
   :=R\Gamma\!\left(X,j_*\mathscr E_{\mathrm{Den},\eta}\right),       \tag{2}
\]
\[
 G^{1,\bullet}
   :=R\Gamma\!\left(
      X,\prod_p' i_{p,*}\mathscr E_{\mathrm{Den},p}
      \right).                                                       \tag{3}
\]
The restricted product topology is induced by finite rational-Witt
correspondences.  Milnor Rost--Schmid residues give the horizontal map
\[
 \partial_{\mathrm{RS}}:
 G^{0,\bullet}\longrightarrow G^{1,\bullet}.                         \tag{4}
\]
Frobenius/Verschiebung act on `(1)` and `(4)` by equivariant sheaf maps.
Prime powers control the local trace of `(4)` but do not form another
cohomological direction.

## Conjecture

`[CONJECTURE] [DAC_COARSE_INVARIANT_SHEAF_ROST_SCHMID_DESCENT]`

There is a source-defined complete locally convex sheafification of
`(1a)` for which:

1. **Mixed arithmetic topology.**  On logarithmic Kummer charts the
   enhancement restricts to
   `DAC_ADELIC_L1_L2_ROST_SCHMID_HODGE_COEFFICIENT`: \(L^1\) retains
   the product formula, real boundary, and residues, while \(L^2\)
   supplies positive local energy.  It is not the bare \(L^2\)
   completion.
2. **Internal amplitude.**  Both `(2)` and `(3)` admit functorial
   Hausdorff derived-section representatives in degrees \(0,1\).
3. **Localization triangle.**  The map `(4)` represents the finite-place
   localization triangle for \(\mathscr E_{\mathrm{Den}}\).  After adjoining
   the real signature orientation, arithmetic cohomology is
   \[
   R\Gamma_{\mathrm{arith}}(X,\mathscr E_{\mathrm{Den}})
   \simeq
   \operatorname{Tot}\!\left(
     G^{0,\bullet}\xrightarrow{\partial_{\mathrm{RS}}}G^{1,\bullet};
     \mathbb R(-1)[-2]\right).                                      \tag{5}
   \]
4. **Three-term form.**  Formula `(5)` is represented by
   \[
   L^0=G^{0,0},\qquad
   L^1=G^{1,0}\oplus G^{0,1},\qquad
   L^2=G^{1,1}\oplus\mathbb R(-1),                                  \tag{6}
   \]
   with no cohomology outside degrees \(0,1,2\).
5. **Endpoints.**  Deninger's Theorem 10.2 identifies
   \(H^0_{\mathrm{arith}}\cong\mathbb R\) with generator \(0\), while
   `DAC_REAL_ARAKELOV_DIVISOR_ENDPOINT` identifies the
   real-linearized residue/signature row cokernel
   \(H^2_{\mathrm{arith}}\cong\mathbb R(-1)\) with generator \(1\).
   The analytic comparison of this row with `(5)` is part of clause 3.
6. **Regulator edge.**  The source regulator
   \[
   \Gamma(X_0,\mathcal O^\times)\otimes Q_0
   \longrightarrow
   H^1(\widetilde X,Q_0(1))^{\widetilde G}
   \]
   maps naturally to the degree-one edge of `(5)`.
7. **Residual non-scalar flow.**  Translation in \(\log u\) acts on
   `(1a)` and `(5)`.  Its action on reduced \(H^1\) is not obtained by
   taking invariants of the already-computed pure Milnor cohomology; it
   lies in the full true-to-approximate correction and is defined
   intrinsically by the coarse-sheaf hypercohomology.
8. **Cup and trace.**  Frobenius reciprocity for Milnor residues and the real
   signature map makes `(5)` multiplicative and gives
   \[
   H^i_{\mathrm{arith}}\widehat\otimes
   H^{2-i}_{\mathrm{arith}}\longrightarrow\mathbb R(-1).
   \]
9. **Prime trace.**  On the reduced Hausdorff cohomology, the local
   distributional Lefschetz term of the packet \(X_p\) is supported at
   \(k\log p\) with coefficient \(\log p\) and the real orientation sign.

## Why this avoids the two no-go theorems

- `DAC_PURE_SUSPENSION_SCALAR_SPECTRUM_NO_GO` applies when final
  cohomology is obtained from locally pure cohomology by exact
  invariants.  Clause 7 explicitly forbids that comparison.
- `DAC_COARSE_STACK_EXACTNESS_SCALAR_SPECTRUM_NO_GO` remains a
  diagnostic: identifying underived coarse invariants with derived
  quotient descent would again force scalar \(H^1\).  Derived quotient
  descent is not used constructively.
- `DAC_DIAGONAL_POWER_RELATION_LEIBNIZ` exposes higher Koszul syzygies in
  a prime-indexed action presentation.  Construction `(1)` has no such
  presentation; primes enter only through codimension-one localization.

## Construction program

1. Define raw \(\widetilde{\mathscr A}^{\bullet}\) on finite pro-Stein
   rational-Witt charts with its Galois, power, and Tate operations.
2. Start with the already constructed equivariant Tate--Milnor sheaf,
   form `(1)` degreewise, and prove its coarse-suspension
   derived-section comparison as a complete locally convex
   \(E_\infty\)-coefficient.  Do not replace it by global chart
   cochains or a Postnikov truncation.
3. Construct the mixed adelic \(L^1/L^2\) Kummer topology and identify
   its place-component averages with normalized residue coordinates.
4. Prove
   `DAC_COFINITE_COARSE_ANALYTIC_DIVISOR_COMPARISON` on every actual
   preimage \(a^{-1}\operatorname{Spec}\mathbb Z[1/N]\), without a
   quotient-local slice and without commuting cohomology with
   invariants.  Compose with the proved split strict cofinite divisor
   row to obtain
   `DAC_ARITHMETIC_PROJECTION_LERAY_ROST_SCHMID_RESOLUTION`.
5. Identify local Frobenius homotopy cocycles directly in the Leray
   edge and the full middle hypercohomology of `(1a)`.
6. Use the minimal generated part of
   `DAC_FINITE_CORRESPONDENCE_ANALYTIC_REALIZATION`; use its
   dimension-one Rost--Schmid complex to identify the two columns.
7. Construct the sheaf-level Milnor residue square and prove the
   localization triangle in clause 3; add MW/signature only at the real
   boundary.
8. Construct the archimedean signature boundary and prove global
   finite-plus-infinite reciprocity.
9. Pass to maximal Hausdorff quotients and prove closedness of the reduced
   differentials.
10. Compute local prime fixed-point traces before comparing with any zeta
   divisor or Xi determinant.

## Falsifiers

- Any proof replacing
  \(R\Gamma(X,(\pi_*\widetilde{\mathscr A})^{\mathbb Q_{>0}})\) by
  \(R\Gamma(\widetilde X,\widetilde{\mathscr A})^{\mathbb Q_{>0}}\)
  without an independent theorem is invalid.
- Any proof using raw `(1)` without the Steinberg correction contradicts
  the computed generic degree-two cup product.
- If reduced \(H^1\) is scalar under the flow, it cannot contain the
  nontrivial zeta spectrum.
- If the internal coarse-sheaf amplitude exceeds one, `(6)` does not
  follow.
- If the topology or norm uses Xi zeros, Weil positivity, or RH, the
  construction is circular.
- If the topology is bare adelic \(L^2\), the product-formula condition
  is dense rather than closed and the construction is ruled out by
  `DAC_NAIVE_ADELIC_L2_KUMMER_COMPLETION_NO_GO`.
- If the prime trace lacks the exact \(\log p\) coefficient, the explicit
  formula is not recovered.

## Current status

- Deninger's invariant-sheaf definition and \(H^0=\mathbb R\):
  literature-proved.
- Equivariant Tate regulator and local pro-Stein coefficient:
  literature/paper-proved.
- Degreewise coarse invariant-sheaf existence and descent of commuting
  source operations: paper-proved.
- Abstract two-column totalization and cup/flow descent:
  paper-proved; Lean written, direct check deferred during external build
  saturation.
- Real-linearized Arakelov residue/signature endpoint:
  paper-proved; \(\mathbb Q\)-coordinate Lean source written.
- Generic rational Steinberg correction and local amplitude:
  paper-proved.
- Internal coarse amplitude, arithmetic-projection Leray resolution,
  sheaf-level localization triangle, mixed adelic coefficient,
  finite-correspondence analytic realization, reduced closed-range
  theorem, and local prime trace: open.

**Verdict:** `ACTIVE SOURCE CONJECTURE; FIRST GLOBAL ARITHMETIC
COHOMOLOGY GATE`.

## Log

- 2026-07-26 — Extracted from the failure of prime-indexed diagonal
  descent after checking Deninger's Definition 10.1, Theorem 10.2, and
  Section 12 regulator construction.
