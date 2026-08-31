# Suzuki quadratic-contact compensation width loss

- **ID:** SUZ-QCWL
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` (read-only) · shared HB/FZZ-P/PW-B/RBH Ward producer
- **Statement:** Eventual boundedness of the quadratic-contact residual `E_N^2 / C_N` forces only the quantitative Xi half-plane bound `Re rho ≤ 3/4`; the CCM continuation manufactured by this residual reaches exactly `Re u > -1/4`, not the RH endpoint `Re u > -1/2`.

## Goal

Kill quadratic (and subsequently every higher finite-contact) signed compensation as an endpoint-preserving repair of the shared four-route Ward producer.  Exact proof chain:

`E_N^2/C_N = O(1)` → `G_N = O(N^(1/4))` → `Q(log N) = O(N^(1/4))` → `Q(t) = O(exp(t/4))` → critical-Mellin continuation on `Re u > -1/4` → `XiZeroHalfPlaneBound (1/4)`.

Here `C_N` is Suzuki transition-core energy, `E_N` its aligned Gamma-completed energy, `G_N` Suzuki Green/completed lower-Hardy amplitude, and `Q` the critical Mellin Chebyshev resolvent.  Contact order one is the already formalized residual `E_N`, whose boundedness is equivalent to RH.  Quadratic contact loses one quarter-plane before divisor tomography.

## Gates

- [x] 0 → 1  in-progress: corpus-native statement, exact four-route chain, current-literature audit, proof architecture
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, targeted `lake build`, axiom audit
- [ ] 3 → 4  publication-ready: standalone theorem + proof + Lean certificate

## Corpus audit

- `SuzukiTransitionCoreAlignedGammaCompletion`: `G_N^2 ≤ E_N`, `C_N ≤ D N`, `E_N ≥ 0` eventually.
- `CCMUnitRieszSuzukiGreenProducerClassification`: completed outgoing charge equals Suzuki Green plus two uniformly bounded corrections; outgoing charge is `Q(log N)/2`.
- `CCMUnitRieszLogLatticeHandoff`: one logarithmic cell changes `Q` by at most `log 4 + 5`.
- `CCMUnitRieszResolventRHCriterion`: bounded `Q` manufactures the full `Re u > -1/2` critical-Mellin continuation.
- `CCMSourceDivisorEnergySpectrum`: holomorphy only above `alpha - 1/2` detects only `XiZeroHalfPlaneBound alpha`.

No corpus theorem propagates an exponential resolvent envelope through the CCM continuation, and no theorem identifies the quadratic aligned residual's lost quarter-plane.

## Literature audit (through 2026-08-31)

Suzuki's screw-function papers `arXiv:2206.03682`, `arXiv:2209.04658`, and `arXiv:2606.09096`, plus Matsumoto--Suzuki's M-function work, contain no transition-core/aligned-energy nonlinear compensation and no finite-contact-order abscissa law.  Searches for nonlinear screw renormalization, Chebyshev-resolvent power growth, and contact-order compensation found no matching theorem.  The claim is therefore internally and externally unrecorded, subject to final wording audit after proof closure.

## Paper proof `[PROVED HERE]`

Write `P_N := E_N^2/C_N`, with totalized division.  Assume `P_N ≤ B` eventually.

1. Eventual positivity of `C_N` follows from the corpus lower bound `N/104976 ≤ C_N`.  Since `E_N ≥ 0`, `P_N ≤ B` gives `E_N^2 ≤ B C_N`.
2. The aligned lower bound `G_N^2 ≤ E_N` gives `|G_N|^4 ≤ E_N^2`.  The transition-core linear upper bound `C_N ≤ D N` therefore gives `|G_N|^4 ≤ BD N`.  Two applications of the nonnegative square-root order law yield `|G_N| ≤ K N^(1/4)` for a fixed `K`.
3. For `N ≥ 2`, `G_N` is Suzuki Green at `log N`.  The completed outgoing charge is Green plus polar and archimedean corrections bounded uniformly in `N`, and it equals `Q(log N)/2`.  Absorbing constants into `K` gives `|Q(log N)| ≤ K N^(1/4)`.
4. On the logarithmic cell `N ≤ exp t ≤ N+1`, the exact lattice handoff gives `|Q(t)| ≤ |Q(log N)| + log 4 + 5`.  Since `N^(1/4) ≤ exp(t/4)`, a compact initial interval and constant absorption give a global envelope `|Q(t)| ≤ K' exp(t/4)` for `t ≥ 0`.
5. Set `R(t)` to the continuous ray representative of `Q` and `q(h):=R(h-1)`.  The tilted tail `exp(-h/4)q(h)` is bounded on `h>1`.  Hence
   `L(z)=exp(z) ∫_{1}^{∞} exp(-zh)q(h) dh`
   is holomorphic on `Re z>1/4` (rewrite it as the Laplace transform of the bounded tilted tail at `z-1/4`).
6. The existing absolutely-continuous integration-by-parts proof remains valid for every real `r>max(1/2,1/4)`.  Its boundary term now decays like `exp(-(r-1/4)t)`.  Thus the manufactured defect
   `A(u)=1/(u+1)-1-(u+1)((u+3/2)L(u+1/2)+2/3)`
   is holomorphic on `Re u>-1/4` and agrees with the regularized critical-Mellin defect on `Re u>0` by the identity theorem.
7. Rotate coordinates as in the corpus endpoint proof:
   `B(w)=-i(A(-1/2-iw)+GammaConnection(1/2-iw))`.
   Then `B` is holomorphic on `Im w>1/4` and agrees with `XiC'/XiC` on `Im w>1/2`.  The analytic identity `XiC'=B XiC` propagates over the connected half-plane `Im w>1/4`.  A zero of `XiC` there would make its logarithmic derivative have meromorphic order `-1`, contradicting analytic `B`.
8. For any Xi zero `rho`, its centered coordinate `z_rho` satisfies `Im z_rho=1/2-Re rho` and `XiC(z_rho)=0`.  If `Re rho>3/4`, evenness gives a zero at `-z_rho` with imaginary part `>1/4`, contradiction.  Hence `Re rho≤3/4`.

All steps use unconditional corpus theorems plus the displayed residual boundedness premise.  Lean target will package step 4–8 first as a general exponential-growth-to-width theorem, then discharge its premise from `P_N` in a Suzuki module.

## Hostile audit

- **Cancellation objection:** no sign is discarded before `G_N^2≤E_N`; subsequent quantities are nonnegative.
- **Division-by-zero objection:** `C_N` is eventually strictly positive by its linear lower bound.
- **Lattice-gap objection:** exact cell handoff is additive and the exponential envelope is monotone.
- **Endpoint objection:** `Re z>1/4` translates to `Re u>-1/4`, not `>-1/2`; no identity theorem enlarges an analytic domain.
- **Gamma obstruction:** `Im w>1/4` remains inside the Gamma connection's holomorphic half-plane.
- **Overclaim objection:** theorem proves the exact continuation delivered by the quadratic-growth argument.  Route-class kill is limited to endpoint preservation through this compensation/CCM-abscissa mechanism; it does not assert that the bounded residual is logically inequivalent to RH by every conceivable argument.

## No-go closure

- **Exact killing theorem/mechanism:** quadratic contact converts the RH-bearing amplitude into a fourth-power bound and spends `1/4` of Mellin abscissa; the generated analytic continuation stops at Xi width `1/4`.
- **Strongest positive survivor:** a new quantitative theorem `Q(t)=O(exp(alpha t)) ⇒ XiZeroHalfPlaneBound alpha`, specialized to the actual Suzuki quadratic residual at `alpha=1/4`.
- **New insight:** finite contact order is a zero-width dial, not free cancellation.  First contact is the unique order whose mechanical continuation reaches the RH endpoint.
- **Status:** dependency-closed paper proof and Lean formalization complete.  Generic theorem:
  `xiZeroHalfPlaneBound_of_criticalMellinChebyshevResolventSource_exponentialBound` in
  `CCMCriticalMellinResolventExponentialWidth.lean`.  Actual Suzuki capstone:
  `suzukiTransitionCore_linear_quadratic_contact_widthClassification` in
  `SuzukiTransitionCoreQuadraticContactWidthLoss.lean`.  Both targeted builds pass; all audited
  capstones use only `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-31 — conjecture C1 frozen from internal corpus; current-literature audit found no matching nonlinear contact-order law.
- 2026-08-31 — paper proof closed and formalized; targeted builds and axiom audit pass.  Quadratic contact is retired as an endpoint-preserving CCM mechanism; quarter-width survivor retained.
