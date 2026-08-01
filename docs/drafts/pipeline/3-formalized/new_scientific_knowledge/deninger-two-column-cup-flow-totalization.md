# Two-column cup, trace, and flow totalization

- **ID:** `deninger-two-column-cup-flow-totalization`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Parent:** `deninger-arithmetic-rost-schmid-signature-resolution`
- **Statement:** Componentwise flow and local residue/signature adjunction
  identities assemble canonically into a three-term arithmetic flow with a
  degree-two cup--trace pairing.

## Goal

Identify exact local identities which global Rost--Schmid, Galois, and
real-signature descent must prove.  Once these identities hold, construction
of the source three-term flow and descended cup product is formal algebra,
not an additional conjecture.

## Gates

- [x] 0 → 1 in-progress: source-pure statement, attack, falsifiers
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: Lean constructors
  `deningerTwoColumnSignatureFlow` and
  `deningerTwoColumnCupPairing`
- [ ] 3 → 4 publication-ready: standalone theorem and Lean certificate

## Setup

Let
\[
\begin{matrix}
G^{0,0}&\xrightarrow{h_0}&G^{1,0}\\
\downarrow v_0&&\downarrow v_1\\
G^{0,1}&\xrightarrow{h_1}&G^{1,1}
\end{matrix}
\]
be a commuting square and let
\[
\sigma_{10}:G^{1,0}\to S,\qquad
\sigma_{01}:G^{0,1}\to S
\]
satisfy
\[
v_1h_0=h_1v_0,\qquad
\sigma_{10}h_0+\sigma_{01}v_0=0.                    \tag{1}
\]
The total complex is
\[
L^0=G^{0,0},\quad
L^1=G^{1,0}\oplus G^{0,1},\quad
L^2=G^{1,1}\oplus S
\]
with
\[
d^0a=(h_0a,v_0a),\qquad
d^1(c,b)=(v_1c-h_1b,\sigma_{10}c+\sigma_{01}b).     \tag{2}
\]

## Flow theorem

`[PROVED HERE] [DAC_TWO_COLUMN_FLOW_TOTALIZATION]`

Suppose endomorphisms
\[
\Theta_{00},\Theta_{10},\Theta_{01},\Theta_{11},\Theta_S
\]
commute with \(h_0,v_0,h_1,v_1,\sigma_{10},\sigma_{01}\).  Then the
componentwise maps
\[
\Theta_0=\Theta_{00},\quad
\Theta_1=\Theta_{10}\oplus\Theta_{01},\quad
\Theta_2=\Theta_{11}\oplus\Theta_S
\]
commute with `(2)` and define a flow on the three-term complex.

### Proof

Commutation with \(d^0\) is exactly the pair of identities for \(h_0,v_0\).
On the first component of \(d^1\), commutation follows from
\[
v_1\Theta_{10}c-h_1\Theta_{01}b
=\Theta_{11}(v_1c-h_1b).
\]
On the signature component it follows from
\[
\sigma_{10}\Theta_{10}c+\sigma_{01}\Theta_{01}b
=\Theta_S(\sigma_{10}c+\sigma_{01}b).
\]

## Cup--trace theorem

`[PROVED HERE] [DAC_TWO_COLUMN_CUP_TRACE_TOTALIZATION]`

Let
\[
T:G^{0,0}\times G^{1,1}\to R,\qquad
A:G^{0,0}\times S\to R,\qquad
X:G^{1,0}\times G^{0,1}\to R
\]
be bilinear.  Define
\[
\begin{aligned}
B_{02}(a,(z,s))&=T(a,z)+A(a,s),\\
B_{11}((c,b),(c',b'))&=X(c,b')-X(c',b).
\end{aligned}                                                   \tag{3}
\]
Assume the two local adjunction identities
\[
\begin{aligned}
-X(c,v_0a)+T(a,v_1c)+A(a,\sigma_{10}c)&=0,\\
 X(h_0a,b)-T(a,h_1b)+A(a,\sigma_{01}b)&=0.
\end{aligned}                                                   \tag{4}
\]
Then `(3)` is a chain-level degree-two cup--trace pairing:
\[
B_{11}(d^0a,y)+B_{02}(a,d^1y)=0,                                \tag{5}
\]
and \(B_{11}\) is alternating.

### Proof

For \(y=(c,b)\), the left side of `(5)` is
\[
\begin{aligned}
&X(h_0a,b)-X(c,v_0a)\\
&\quad+T(a,v_1c)-T(a,h_1b)
 +A(a,\sigma_{10}c)+A(a,\sigma_{01}b).
\end{aligned}
\]
This is the sum of the two zero expressions in `(4)`.
Skew-symmetry follows immediately by exchanging \((c,b)\) and
\((c',b')\) in `(3)`.

## Arithmetic meaning

- \(h_i\): prime-packet/Rost--Schmid residue;
- \(v_i\): internal derived Milnor coefficient differential;
- \(S=\mathbb R(-1)\): real orientation line;
- \(\sigma_{10},\sigma_{01}\): real signature boundary;
- \(T\): finite-place top trace;
- \(A\): archimedean orientation trace;
- \(X\): cross cup product.

Thus global construction reduces to proving `(1)`, flow naturality, and
the two reciprocity/adjunction identities `(4)` for the actual coefficient
\(R\alpha_*\mathbb R\).  Descent to \(H^0\times H^2\) and
\(H^1\times H^1\), together with the exact radical criterion for Poincaré
nondegeneracy, is already formalized in
`DeningerArithmeticThreeTermCupDescent.lean`.

## Hostile audit

- This theorem constructs no arithmetic sheaf and proves no acyclicity.
- Perfectness does not follow from `(4)`; it is equivalent to the already
  isolated endpoint separation and middle radical equalities.
- Orientation/signature gives a trace summand, not positivity.
- No Xi quotient, Gamma/CCM model, zero set, RH premise, or numerical
  computation occurs.

## Log

- 2026-07-26 — exact flow and cup--trace totalization proved on paper.

## Lean status

### Both theorems landed

`formal/GaloisForLFunctions/RHTower/DeningerArithmeticTwoColumnSignatureTotalization.lean`, over
the three-term complex/flow/cup framework of `DeningerArithmeticThreeTermCohomology.lean` and
`DeningerArithmeticThreeTermCupDescent.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerTwoColumnSignatureD0`, `deningerTwoColumnSignatureD1`,
  `deningerTwoColumnSignatureD1_comp_D0`, `deningerTwoColumnSignatureComplex` — the setup `(1)` and
  the total complex `(2)`: `L⁰ = G^{0,0}`, `L¹ = G^{1,0} ⊕ G^{0,1}`, `L² = G^{1,1} ⊕ S`, with
  `d⁰a = (h₀a, v₀a)` and `d¹(c,b) = (v₁c - h₁b, σ₁₀c + σ₀₁b)`, and `d¹d⁰ = 0` forced by exactly the
  two identities of `(1)`.
- `deningerTwoColumnProductEnd`, `deningerTwoColumnSignatureFlow` —
  **`DAC_TWO_COLUMN_FLOW_TOTALIZATION`**: five componentwise endomorphisms commuting with the two
  residues, the internal differential and the two signature boundaries assemble into a flow on the
  three-term complex; the two commutation obligations in each total degree are discharged exactly
  as the card's proof does.
- `deningerTwoColumnPair02`, `deningerTwoColumnPair11` — the endpoint and middle pairings `(3)`.
- `deningerTwoColumnCupPairing` — **`DAC_TWO_COLUMN_CUP_TRACE_TOTALIZATION`**: the two local
  adjunction identities `(4)` give the chain-level cup–trace identity `(5)`
  (`differential_adjoint`), and the middle pairing is alternating (`skew`).  Descent of this
  pairing to `H⁰ × H²` and `H¹ × H¹`, with the radical criterion for nondegeneracy, is the already
  formalized `DeningerArithmeticThreeTermCupDescent.lean`.

### Remaining

Nothing.  The card's own scope is exactly this formal algebra: it constructs no arithmetic sheaf,
proves no acyclicity, and does not claim perfectness — those obligations belong to the global
Rost–Schmid, Galois and real-signature descent cards that must supply `(1)`, flow naturality and
`(4)` for the actual coefficient.
