# Diagonal arithmetic localization descent

- **ID:** `deninger-diagonal-arithmetic-localization-descent`
- **Stage:** 5-failed
- **Type:** RETIRED CONJECTURE / NO-GO
- **Label:** `DAC_DIAGONAL_ARITHMETIC_LOCALIZATION_DESCENT`
- **Parent:** `deninger-arithmetic-rost-schmid-signature-resolution`
- **Statement:** non-proper suspension descent and prime Rost--Schmid
  localization form one codimension-one differential.

## Retraction

This conjecture is false as a source model.  Deninger does not resolve the
non-proper \(\mathbb Q_{>0}\)-action by a prime-indexed bar differential.
Definition 10.1 of *Dynamical systems for arithmetic schemes* first forms the
degreewise invariant sheaf
\[
 \mathcal R_X=(\pi_*\mathcal R_{\widetilde X})^{\mathbb Q_{>0}}
\]
on the coarse quotient and then takes ordinary sheaf cohomology
\(H^\bullet(X,\mathcal R_X)\).  In Section 12 he explicitly uses
\[
 H^1(\widetilde X,Q_0(1))^{\widetilde G}
\]
only as a replacement for an expected quotient-space regulator target,
because the action is not properly discontinuous.  That cover-invariant
regulator group is not identified with the desired spectral
cohomology of the quotient.

The proposed prime relation module also has unavoidable factor-order
syzygies.  `DAC_DIAGONAL_POWER_RELATION_LEIBNIZ` proves
\[
 \Delta_{mn}=T_m\Delta_n+\Delta_mF_n,
\]
and for \(mn=nm\) the two factor orders give the Koszul syzygy
\[
 T_m\Delta_n+\Delta_mF_n
 =
 T_n\Delta_m+\Delta_nF_m.
\]
Thus a genuine free presentation needs higher relation cells.  Quotienting
those cells away by definition gives no proof that the resulting two-term
object computes Deninger's invariant sheaf.

The positive survivor is
`DAC_COARSE_INVARIANT_SHEAF_ROST_SCHMID_DESCENT`: form the invariant
coefficient sheaf before derived global sections, and use prime
Rost--Schmid localization as the sole horizontal codimension-one
differential.  Non-exactness of the coarse quotient remains inside sheaf
hypercohomology rather than becoming a separate group-action direction.

## Why the discarded model looked plausible

The local analytic Tate--Milnor complex has amplitude \([0,1]\).
Successively applying a one-dimensional non-proper descent complex and a
one-dimensional Rost--Schmid complex would allow total degree three.
Deninger's arithmetic curve requires degrees \(0,1,2\).

Exact invariant descent is also impossible:
`deninger-analytic-exact-weight-descent` and
`DAC_PURE_SUSPENSION_SCALAR_SPECTRUM_NO_GO` show that it collapses the
final flow to pure scalar weight.  Therefore the non-exact descent defect
must be the same codimension-one boundary that records prime packets.

## Source complexes

Use logarithmic transverse coordinate \(s=\log u\).  Let
\[
 C^{0,\bullet}
\]
be the complete nuclear cylinder--Mellin realization of the pro-Stein
analytic Tate--Milnor coefficient on the generic character cover.  It has
amplitude \([0,1]\).  Translation in \(s\) gives a strongly continuous
operator
\[
 (\tau_t f)(P,s)=f(P,s+t).                                          \tag{1}
\]

For every prime \(p\), let
\[
 C_p^{1,\bullet}
\]
be the amplitude-\([0,1]\) analytic coefficient on Deninger's compact
prime packet \(\Gamma_p\), with twisted MW residue
\[
 \partial_p^{MW}:C^{0,\bullet}\to C_p^{1,\bullet}.                  \tag{2}
\]
The diagonal suspension relation at \(p\) is
\[
 \Delta_p=\tau_{\log p}-F_p^*.                                     \tag{3}
\]
The Tate normalization is included in \(F_p^*\).

Let \(\mathcal R_{\mathrm{ar}}\) be the closed arithmetic relation module
obtained from the weighted restricted product of the images of the
\(\Delta_p\), modulo the closed Frobenius/Verschiebung relations forced
by composite power correspondences.  Its definition uses the
rational-Witt finite-correspondence topology, not the abstract discrete
group ring of \(\mathbb Q_{>0}\).

Set
\[
 C^{1,\bullet}
 =
 \mathcal R_{\mathrm{ar}}^\bullet
 \widehat\oplus
 \prod_p' C_p^{1,\bullet}.                                         \tag{4}
\]

## Retired conjecture

`[RETIRED] [DAC_DIAGONAL_ARITHMETIC_LOCALIZATION_DESCENT]`

The map
\[
 \partial_{\mathrm{ar}}:
 C^{0,\bullet}\longrightarrow C^{1,\bullet},\qquad
 x\longmapsto
 \left(
   [(\Delta_p x)_p],
   (\partial_p^{MW}x)_p
 \right)                                                            \tag{5}
\]
is a continuous cochain map with the following properties.

1. **Coarse sheaf comparison.**  There is a genuine analytic coefficient
   complex \(\mathscr A_{\mathrm{fin}}\) on Deninger's coarse
   rational-Witt suspension such that
   \[
   R\Gamma(X_W,\mathscr A_{\mathrm{fin}})
   \simeq
   \operatorname{Tot}
   (C^{0,\bullet}\xrightarrow{\partial_{\mathrm{ar}}}
    C^{1,\bullet}).                                                  \tag{6}
   \]
2. **Arithmetic dimension one.**  The quotient by composite-power
   relations in \(\mathcal R_{\mathrm{ar}}\) is exact; no independent
   prime--prime intersection term survives.  This is the
   finite-correspondence analogue of the length-one Rost--Schmid complex
   on a regular arithmetic curve.
3. **Regulator edge.**  Deninger's map
   \[
   \Gamma(X_0,\mathcal O^\times)\otimes Q_0
   \to H^1(\widetilde X,Q_0(1))^{\widetilde G}
   \]
   maps naturally into the degree-one edge of `(6)`.
4. **Residual flow.**  Translations \(\tau_t\) commute with `(5)` and
   induce the transverse flow on `(6)`.  The analytic relation module is
   not collapsed to the pure Milnor cohomology, so the induced generator
   need not be scalar.
5. **Prime localization.**  The distributional trace of the relation
   channel at \(p\) is supported at
   \[
   k\log p,\qquad k\ge1,
   \]
   with coefficient \(\log p\); the MW residue fixes the Lefschetz sign
   and orientation.
6. **Multiplicativity.**  Frobenius reciprocity makes `(5)` compatible
   with cup product and the arithmetic trace.

After adding the single archimedean signature orientation in total degree
two, `(6)` has the three-term representative
\[
 L^0=C^{0,0},                                                       \tag{7}
\]
\[
 L^1=C^{1,0}\oplus C^{0,1},                                        \tag{8}
\]
\[
 L^2=C^{1,1}\oplus\mathbb R(-1),                                   \tag{9}
\]
with the differential already formalized abstractly by
`DAC_TWO_COLUMN_SIGNATURE_TOTALIZATION`.

## Construction program

1. Define the nuclear cylinder--Mellin completion without Xi data.
2. Extend each finite rational-Witt correspondence continuously to that
   completion.
3. Present \(\mathcal R_{\mathrm{ar}}\) as the completed cokernel of the
   composite-power syzygies and prove independence of prime
   factorization.
4. Construct the sheaf map `(5)` locally on the coarse quotient and prove
   `(6)` by a two-level analytic hypercover.
5. Prove the MW residue/power commutative square and global finite-place
   reciprocity.
6. Compute the local trace of \(\Delta_p\) from the fixed points of
   \(F_p^k\), before any global spectral comparison.
7. Add the real signature boundary and apply the existing three-term
   totalization.

## Falsifiers

- If composite-power syzygies leave nonzero higher derived relations,
  arithmetic amplitude may exceed \([0,2]\).
- If `(6)` factors through exact invariants of local Milnor cohomology,
  the scalar-spectrum no-go kills the construction.
- If the chosen completion is defined using Xi zeros or an
  RH-equivalent norm, it is circular.
- If \(\Delta_p\) and \(\partial_p^{MW}\) do not satisfy a common
  Frobenius-reciprocity identity, cup product cannot descend.
- Prime trace support without the exact \(\log p\) coefficient does not
  recover the explicit formula.

## Current status

- Generic analytic coefficient and chartwise comparison: paper-proved.
- Power/residue operations: literature-proved abstractly.
- Algebraic two-column totalization, flow descent, and cup formulas:
  paper-proved; Lean written, direct check pending low system load.
- Arithmetic relation module, two-level coarse comparison, and local
  fixed-point trace: open.

**Verdict:** `FAILED AS A SOURCE MODEL; POSITIVE SURVIVOR IS COARSE
INVARIANT-SHEAF HYPERCOHOMOLOGY FOLLOWED BY ROST--SCHMID LOCALIZATION`.

## Log

- 2026-07-26 — Created as positive survivor of exact-invariant descent
  no-go.
- 2026-07-26 — Retired after checking Deninger's Definition 10.1 and
  Section 12.  Prime-indexed diagonal descent is neither his invariant-sheaf
  definition nor a two-term resolution: its factor-order Koszul syzygies
  require higher cells.  Extracted
  `DAC_COARSE_INVARIANT_SHEAF_ROST_SCHMID_DESCENT`.
