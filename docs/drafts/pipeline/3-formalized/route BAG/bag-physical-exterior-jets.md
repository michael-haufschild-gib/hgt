# BAG actual all-order physical exterior jets

- **Stage:** 3-formalized

01ax, 2026-10-06. Dependency-closed paper proof; complete scratch90088/log09
terminal0PASS. Production ChiCubicPhysicalExteriorDecay830lines/API2 audit52566emptyPASS.
Both public axiomprints58537 show only propext,Classical.choice,Quot.sound;
the combined next Gagliardo candidate failed separately. Index93916PASS,
umbrella importonce,scoped diffcheckPASS. Lint41440terminal1:362warnings and
six unrelated unreachable modules (FourierCompactSupportDensity,
Sieve.TwistedSelbergCoefficient,Sieve.TwistedSelbergFactorization,
SmoothHeightProfileMellin,HTGeometry.ResetMarkovExecution,
HTGeometry.ResetPathSingularity); no ownedleaf finding. Global lint not clean.
Two public statements: exterior_decay, selected_exterior_decay on the
literal bagCubicNormalizedPhysicalKernel. No analytic assumptions.

For all fixed natural j,n there is C>0, uniform in structural0<delta<1/2,
0<=h<=1, N>0 and positive(x,y) outside[1/4,4]^2, such that
 N^n*(1+x+y)^n*max(|partial_x^j H|,|partial_y^j H|)
 <= C*N^(j+1)*(1+x+y)^j/delta^(n-1).
In particular for every fixed j,m,k, selected delta=N^-3/4,h=1/logN gives
one C>0 and eventuallyN, uniformly on the positive exterior,
 N^k*(1+x+y)^m*max(|partial_x^j H_N|,|partial_y^j H_N|)<=C.
Both are universal results on structural parameter/spatial subtypes; no
uniform derivative budget or cancellation premise has been inserted.

Proof. Joint smoothness and compactness control all derivatives of
(alpha*P+beta)^j W(kP) after normalizing the polynomial by1+|y|.
Leibniz and actual normalized-slice L1 derivative bounds cost only
delta^-(n-1). Native repeated IBP bounds each complete oscillatory row.
Literal cube domination admits all pure x jets and all their derivatives;
dominated parameter differentiation identifies them with actual iteratedDeriv.
Fubini is justified before changing nested orders. Exact P- and Q-row phase
factorizations preserve all three slices, conjugation, W and reciprocal1/R.

For positive(x,y) outside[1/4,4]^2, choose one direction independent ofP,Q,R.
If a coordinate is large, use the larger coordinate. Otherwise one coordinate
is below1/4 while both are bounded. SinceP/R,Q/R lie in[1/2,2], the selected
gradient has modulus at least(1+x+y)/36 throughout the amplitude cube.
The polynomial coefficient bounds work in either direction. Actual outer
slice L1 budgets integrate the row estimate. Exact physical coordinate
symmetry supplies the second pure jet; no false mixed-derivative product
formula is used.

After selecting delta=N^-3/4, sufficiently high fixed n pays any prescribed
N power and position weight. One explicit n=4*(j+k+m+1) suffices; the theorem
is arbitrary-order localization, not a numerical optimization result.
All division cancellations retain positive scale proofs. No resource-limit
increases, numerical experiments or full/umbrella builds used.

Remaining mathematical obstruction: localized fractional Sobolev transfer
through the logarithmic coordinate change and exterior Jacobian admission,
then uniform Mellin tails and lower-growth arithmetic-source pairing.
Full original sharp-action and common-height self-return remain open.
RH not proved or falsified.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiCubicPhysicalExteriorDecay` | `bagCubicNormalizedPhysicalKernel_exterior_decay`, `bagCubicNormalizedPhysicalKernel_selected_exterior_decay` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
