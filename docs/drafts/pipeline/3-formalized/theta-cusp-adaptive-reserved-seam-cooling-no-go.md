# Adaptive Reserved C5 Seam-Cooling No-Go

- **ID:** CLG-TTF-C5-adaptive-reserve-no-go
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** `rh-current-frontier-map.md`, Route CLG/TTF, fixed-action C5 far-tail direct-J burden
- **Statement:** For every physical centre `u`, the denominator-cleared adaptive-reserved compensation has fifth seam derivative `600 * κ(u)^2 * (F₃(u) + 2 * A(u) * F₂(u)) < 0`, where `κ(u)` is completed reflected-action seam curvature, `A` is first-atom scale, and `F₂,F₃` are likelihood source jets. Hence the proposed adaptive-reserved lower margin is negative on a punctured right seam neighbourhood and cannot prove far-tail direct-J globally.

## Goal

Kill or close the conjecture

`0 < c5CompletedAdaptiveReservedCompensationMargin u t`

for `0 < t < u` in the structural tail. Its intended RH chain was

adaptive reserved compensation → literal far-tail direct-J orientation → local/compact assembly → fixed-action seam → reflection-odd rank-four/Ptolemy wall → cofinal no-escape → CLG/TTF or Weil-polarization positivity → RH.

The result kills the first arrow and identifies the exact seam data a replacement must retain.

## Gates

- [x] 0 → 1 in-progress: exact physical statement, source-pure attack, RH passport fixed
- [x] 1 → 2 fully-proven: complete paper proof below, no open dependency
- [x] 2 → 3 formalized: Lean fifth-germ identity, local negativity, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone no-go theorem and replacement-route consequence

## Paper proof `[PROVED HERE]`

Fix a physical centre `u` and write, as functions of displacement `t`,

- `q` for completed reflected action, `a = q_t`, `b = q_tt`;
- `s = q_u`, `m = q_ut`;
- `c₀,n₀` for atom-only third displacement and second mixed-centre channels;
- `H = a(t m) - (a+t b)s`;
- `P₂ = a(t m+t² n₀) - (a+3t b+t²c₀)s`;
- `Z = 2A(u+t)F₂(u+t)+2A(u-t)F₂(u-t)`.

Let `r = exp(q)-1`, `v=t a`, and define the division-free cleared margin

`D = r * (5P₂ - (14+10v)H + 5t²aZ) - 8vH`.

For positive physical displacement, `q>0`, hence `r>0`, and exact field algebra gives

`D = r * c5CompletedAdaptiveReservedCompensationMargin`.

Put `κ=q_tt(0)>0`. Reflection parity gives `q(0)=a(0)=s(0)=m(0)=0`, while

`b(0)=κ`, `s_tt(0)=n₀(0)-2F₃(u)`, and `Z(0)=4A(u)F₂(u)`.

The cubic terms are therefore

- `H = O(t⁵)` (its cubic coefficient cancels exactly);
- `P₂ = 2κF₃(u)t³ + O(t⁵)`;
- `5t²aZ = 20κA(u)F₂(u)t³ + O(t⁵)`.

Also `r=(κ/2)t²+O(t⁴)` and `v=κt²+O(t⁴)`. Thus terms containing `H` do not contribute through order five, and

`D = 5κ²(F₃(u)+2A(u)F₂(u))t⁵ + O(t⁷)`.

Equivalently,

`D⁽⁵⁾(0)=600κ²(F₃(u)+2A(u)F₂(u))`.

Corpus theorem `two_mul_scale_mul_thetaCuspLikelihoodSourceLogPartitionJetTwo_lt_neg_jetThree` states

`2A(u)F₂(u) < -F₃(u)`,

so the parenthesis is strictly negative. Completed logarithmic curvature gives `κ>0`; hence `D⁽⁵⁾(0)<0`. Taylor's theorem yields `D(t)<0` for all sufficiently small `t>0`. Since `r(t)>0` there, the literal adaptive-reserved margin is also negative. This contradicts its proposed global positivity.

## No-go closure

- **Exact killing theorem/mechanism:** Adaptive lower-bounding replaces the exact highest mixed-centre jet by `Z`. At cubic order it deletes the strict cooling excess `-F₃-2AF₂>0`; that excess is precisely what cancels the lower-jet seam defect. The lower bound is therefore strictly adverse at the seam.
- **Strongest positive survivor:** Exact seam-defect classification `D⁽⁵⁾(0)=600κ²(F₃+2AF₂)<0`, together with the representation law that restoring the exact third likelihood channel cancels this fifth-order cleared obstruction.
- **New insight:** Any viable far-tail proof must preserve exact third-channel cooling excess through the collapsed seam. Universal adaptive reserve, even though pointwise favorable away from seam, cannot be inserted before seam cancellation. Next admissible route must use full completed compensation or a cancellation-preserving homotopy.
- **Status:** Internal corpus audit complete; no exact theorem found in corpus. External primary-literature audit found theta log-derivative convexity, Hermite–Hadamard refinements, total-positive Hankel transforms, and a 2026 theta-kernel/blockwise-positivity obstruction, but no fixed-action C5 adaptive-reserve seam classification. Paper proof and Lean formalization dependency-closed.

## Lean formalization

- Generic exact seam classification: `HTGeometry.c5AdaptiveReservedClearedExpression_seamJetClassification` in `GaloisForLFunctions.HTGeometry.AdaptiveReservedC5SeamDefect`.
- Physical fifth-germ identity and strict sign: `RHTower.iteratedDeriv_five_thetaCuspC5AdaptiveReservedClearedSeamGerm` and `RHTower.iteratedDeriv_five_thetaCuspC5AdaptiveReservedClearedSeamGerm_neg`.
- Literal punctured-neighbourhood failure: `RHTower.eventually_c5CompletedAdaptiveReservedCompensationMargin_neg`.
- Route-killing closed theorem: `RHTower.not_forall_c5CompletedAdaptiveReservedCompensationMargin_nonneg`.
- Verification: direct foreground Lean checks passed for both new modules; targeted build `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFixedActionC5AdaptiveReservedSeamNoGo` passed; exported theorem axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-29 — Adaptive-reserved positivity conjecture hostile-tested and falsified at seam; exact fifth-germ survivor proved on paper.
- 2026-08-29 — Generic and physical seam classifications, local negativity, exact literal-margin connector, and unconditional route-killing theorem formalized in Lean.
