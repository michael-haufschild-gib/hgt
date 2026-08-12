# Mass-shifted contact-order arithmetic-source transmutation

- **ID:** MS-COST
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 Exact open core
- **Statement:** At a positive flat canonical shifted-Xi face, first-order inverse-Hankel admission is exactly the monic Möbius coefficient tangent, hence every simple hard Gauss coordinate has zero first derivative; arithmetic forcing reappears in the first nonzero higher contact jet as the adaptive completed even `P^sharp` source.

## Goal

Replace the false absolute-terminal-mass/speed inference by a source-pure law valid at the singular
face itself.  The producer must use actual shifted-Xi moment differentiation and canonical
inverse-Hankel admission before reflection aggregation.  No fixed linear observer and no chosen
null orientation may enter.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Let `P_y` be degree-`n` monic inverse-Hankel admission, `V=∂_yP_y`, and suppose at `y=y₀`
its coefficient vector spans kernel of `(n+1)` Hankel block while leading `n` block is positive
definite.  Differentiated orthogonality and shifted-Xi moment ODE give, for `k<n`,

\[
 L(X^kV)=L(X^{k+2}P').
\]

If `a=[X^{n-1}]P`, define degree-lowered monic Möbius tangent

\[
 G_P=X^2P'-nXP+aP.
\]

Flat nullity gives `L(X^kG_P)=L(X^{k+2}P')`; head positivity gives `V=G_P`.  At a simple
root `x`, `V(x)=x²P'(x)`, so implicit differentiation gives `x'=-x²` and therefore
`(x⁻¹-y)'=0`.  Existing all-order Padé contact law predicts that first nonzero departure from this
frozen Möbius orbit occurs exactly at first unseen defect and lands in adaptive completed even
`P^sharp` source.

## No-go closure

- **Exact killing theorem/mechanism:** Previous inference “absolute terminal mass can vanish only by nonproper hard-root speed” confuses absolute `Γ` with relative `Γ/h_n`.  Worldline conservation controls `u' Γ/h_n`; at a flat face `h_n=0`, so `Γ→0` does not force `Γ/h_n→0` or speed escape.  Positive-chamber hypotheses also do not include singular face.
- **Strongest positive survivor:** Relative terminal mass is exact inverse mobility inside positive chamber.  At flat face source/atomic contact instead forces first-order hard-root freeze, shifting source information to higher contact order.
- **New insight:** Mobility loss and terminal-mass collapse are shadows of contact-order transmutation, not nonproper escape.  Correct route invariant is first nonzero temporal jet of adaptive completed source paired with absolute Padé residue/radical alternative.
- **Status:** Paper derivation of first-jet tangent under audit; all-order jet and adaptive even-source identities already exist separately in corpus.  Lean target is exact flat tangent, hard-root freeze, and a capstone linking freeze to singular producer law.

## Conjecture loop

1. **C1 — absolute mass extinction forces speed escape.** `[FALSIFIED]` Scale mismatch `Γ` versus `Γ/h_n`; flat norm is zero.
2. **C2 — flat source contact freezes hard coordinates to first order.** `[ACTIVE]` Attack by differentiated inverse-Hankel orthogonality and head-positive uniqueness.
3. **C3 — first nonzero higher jet is exactly completed adaptive even source.** `[ACTIVE]` Audit whether existing Padé-contact and singular-source modules already close all dependencies or whether coefficient-jet reconstruction remains.
4. **C4 — higher-jet source sign anchors hard-root level.** `[HOSTILE]` Expected false: derivative/level separation survives all finite contact orders unless absolute Padé atom is excluded or radical branch is used.

## Door passport

- **Door-1 source purity:** shifted-Xi reciprocal moment ODE; inverse-Hankel monic admission; Hankel flatness; adaptive completed `P^sharp` aggregate.
- **Door-2 proof target:** finite polynomial/Hankel algebra and differentiable root chain rule only.
- **Forbidden shortcuts:** no RH-equivalent positivity assumption, no numerical root tracking, no fixed reporter, no post-hoc null orientation, no generic speed compactness.

## Log

- 2026-08-12 — created in 1-in-progress after hostile scale audit falsified speed-escape interpretation.
