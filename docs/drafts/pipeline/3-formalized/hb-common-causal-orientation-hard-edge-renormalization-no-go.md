# HB common-causal-orientation hard-edge renormalization no-go

- **ID:** HB-CCO-HER-NG
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · HB singular two-leg survivor
- **Statement:** Any response correction added identically to retarded and advanced `++`/`+-` Teukolsky resolvents is invisible to the full nonlinear Peierls causal cut; for order-one point-supported hard-edge corrections, causal reflection removes the `δ₀` charge and retains exactly twice the `δ₀′` charge.

## Goal

Kill HB chain

`common local/distributional hard-edge renormalization → radiative ++ extinction → clock-defect extinction → RH`.

This is pre-divisor and source-independent: no Xi zero or target coefficient enters correction.

## Gates

- [x] 0 → 1: exact corpus cut formula; point-support jet infrastructure; primary-literature audit
- [x] 1 → 2: dependency-closed proof below
- [x] 2 → 3: Lean capstone, targeted build, axiom audit, umbrella wiring
- [ ] 3 → 4: standalone preprint

## Theorem and proof

Write quadratic residuals as `q₊₋, q₊₊`. Corpus gives

`Cut = B(p,(R₊₋ʳ-R₊₋ᵃ)q₊₋) + B(m,(R₊₊ʳ-R₊₊ᵃ)q₊₊)`.

After arbitrary corrections `Kχʳ,Kχᵃ`, subtraction gives

`Cut_K-Cut = B(p,(K₊₋ʳ-K₊₋ᵃ)q₊₋) + B(m,(K₊₊ʳ-K₊₊ᵃ)q₊₊)`.

Hence common corrections `Kχʳ=Kχᵃ` vanish identically. They cannot create, remove, or tune any causal-cut zero. Under Peierls stationary-channel elimination every admissible `+-` correction is a causal self-pairing; the corrected full cut equals the original radiative term plus exactly the orientation-odd `++` correction.

For a point-supported distribution of scaling degree at most two on one transverse coordinate, Brunetti--Fredenhagen extension theory bounds ambiguity by `c₀δ₀+c₁δ₀′`. Equivalently, its action is `φ(0)c₀+φ′(0)c₁`. Causal reflection sends `φ(x)` to `φ(-x)`, preserving `φ(0)` and negating `φ′(0)`. Thus retarded minus advanced is exactly `2φ′(0)c₁`; `c₀` is invisible.

## No-go closure

- **Exact killing mechanism:** Peierls uses retarded-minus-advanced response; every common correction cancels before cokernel projection.
- **Strongest positive survivor:** local scaling-degree-two ambiguity has one visible coordinate only: orientation-odd derivative-delta boundary charge `c₁`; arbitrary `δ₀` threshold mass is gauge-invisible to the cut.
- **New insight:** HB cannot be rescued by choosing a common Hadamard/finite-part prescription, even if source-adapted and phase-odd. Live local route must derive an orientation-odd boundary first jet; otherwise dynamics must be genuinely nonlocal, sheet-changing, or singular beyond order one.
- **Status:** `[PROVED HERE] [LEAN-PROVED]`; theorem `RHTower.d4HBCommonCausalOrientationHardEdgeRenormalizationRouteKilled`; targeted build `8668/8668`; standard axioms only; umbrella wired. Corpus novelty search found no equivalent theorem. Literature contains generic scaling-degree extension and Peierls frameworks, not this theta-HB nonlinear causal-cut classification.

## Literature audit (through 2026-08)

- Brunetti--Fredenhagen, arXiv:math-ph/9903028, Thms. 5.2--5.3: finite-scaling-degree extensions and delta-jet ambiguity.
- Khavkine, arXiv:1402.1282: Peierls inverse from retarded/advanced Green operators under precise gauge/hyperbolicity conditions.
- Spiers--Pound--Moxon, arXiv:2305.19332: reduced second-order Teukolsky source is distributionally well-defined; singular source handling remains gauge/formulation dependent.
- Green--Hollands--Sberna--Toomani--Zimmerman, arXiv:2210.15935: QNM pole sum omits direct arc and zero-frequency tail, so causal discontinuity cannot be replaced by QNM-only data.

## Log

- 2026-09-02 — conjecture frozen and paper proof closed after hostile audit rejected extension-ambiguity-only argument.
