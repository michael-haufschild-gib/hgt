# HB reduced-Teukolsky Hermitian-dilation fidelity no-go

- **ID:** HB-REDUCED-TEUKOLSKY-HERMITIAN-DILATION-FIDELITY-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` HB angular-leakage survivor; corpus searches for reduced `2s` incidence, Hermitian dilation, support preservation, and determinant fidelity
- **Statement:** The actual reduced second-order chiral Teukolsky source admits a coefficient-faithful, finitely supported, Hilbert--Schmidt self-adjoint dilation on every Xi fibre, but that dilation preserves the source Hilbert--Carleman determinant exactly iff the fibre lies on the critical line; universal determinant fidelity is equivalent to RH.

## Goal

Kill multi-sector Hermitianization as a non-circular law forbidding the already-proved tilted angular leakage. Proof chain under test:

`reduced Einstein--Teukolsky 2s source -> doubled Hermitian angular carrier -> determinant/source-divisor fidelity -> source extinction -> HB/FZZ-P/PW-B/RBH Ward extinction -> RH`.

The theorem must separate free structure from RH-bearing structure. Hermiticity, finite modal support, Hilbert--Schmidt regularity, and exact recovery of the chiral source block are unconditional. Exact preservation of the holomorphic determinant is the missing selector and is itself equivalent to source extinction/RH.

## Gates

- [x] 0 → 1  in-progress: source-pure target, explicit one-mode kernel, exact RH chain, hostile alternatives stated
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `d4HBReducedTeukolskyHermitianDilationFidelityRouteKilled`, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

For the exact reduced same-grade coefficient

`c(q) = S_2s(amplitude,mixed,anti;q)`, 

put it into the rank-one modal kernel `K_q = c(q)e_00` on `ℕ`. Its chiral dilation is

`D(K_q) = [[0,K_q],[K_q^*,0]]`.

Existing dependency-closed kernel theory gives: `K_q` and `D(K_q)` are Hilbert--Schmidt; `D(K_q)` is self-adjoint; support only doubles the chirality label and stays over modal index zero; the positive chiral block is exactly `K_q`; and

`det₂(1-zD(K_q)) = det₂(1-zK_q)  iff  K_q=0`.

Rank-one faithfulness gives `K_q=0 iff c(q)=0`. Existing reduced-source incidence gives, for nonzero seed, `c(q)=0 iff Re(q)=1/2`, with universal extinction iff RH. Compose these equivalences and retain the source-sized quadratic-jet lower bound `||c(q)||²/2` for determinant mismatch.

## Paper proof

**[PROVED HERE]** Fix a nonzero Einstein seed and a divisor copy `q`. The rank-one kernel `K_q=c(q)e_00` has Hilbert--Schmidt mass `||K_q||²_HS=||c(q)||²` and support `{(0,0)}`. The block formula for `D(K_q)` makes it self-adjoint, retains `c(q)` in entry `((+,0),(-,0))`, and preserves finite modal support. The Hermitian-dilation second-jet theorem gives

`||c(q)||²/2 ≤ ||[z²]det₂(1-zD(K_q)) - [z²]det₂(1-zK_q)||`

and equality of the full entire determinants iff `K_q=0`. Evaluation at `(0,0)` shows `K_q=0 iff c(q)=0`. The proved reduced Teukolsky incidence theorem gives `c(q)≠0 iff Re(q)≠1/2`; hence determinant fidelity holds iff `Re(q)=1/2`, while every tilted fibre pays a strictly positive quadratic-jet mismatch. Quantifying over all Xi copies and using the proved universal source-extinction endpoint gives determinant fidelity on every fibre iff RH. No spectral computation, QNM completeness, positivity assumption, or divisorwise normalization occurs.

## Competing conjectures and hostile audit

- **C1 — one-sector self-adjointness directly absorbs complex tilted eigenvalue:** false; corpus residual identity proves nonzero leakage for every nonzero tilted source.
- **C2 — doubled Hermitian carrier forbids leakage:** false; coefficient-faithful chiral dilation exists for every complex source and is self-adjoint unconditionally.
- **C3 — locality/Hilbert--Schmidt regularity forbids C2:** false; rank-one source and dilation are finitely supported and Hilbert--Schmidt, with support preserved after adding only chirality.
- **C4 — determinant-faithful Hermitianization supplies missing selector:** proved circular. Fidelity is equivalent fibrewise to critical-line incidence and globally to RH.
- **Hostile source-zero check:** nonzero seed is quantified inside closed route certificate; wall fibres legitimately have zero reduced `2s` source.
- **Hostile gauge check:** no scalar gauge or division is used; mismatch appears in second Taylor coefficient, so equality of entire determinants cannot hide it.
- **Hostile support check:** carrier uses `ℕ`, not a one-point ambient type; source support is exactly one modal cell and dilation support remains in its doubled cell.

## Novelty audit

- Internal search found the general coefficient-faithful Hermitian dilation, its support/Hilbert--Schmidt laws, and its determinant second-jet obstruction, plus separate reduced Teukolsky `2s` incidence. It found no theorem composing them into the exact Xi-fibre critical-wall classification or the global RH-equivalent fidelity endpoint.
- Spiers--Pound--Moxon (arXiv:2305.19332) derive a second-order Teukolsky source, and Ma--Yang (arXiv:2401.15516) compute quadratic QNM excitation with angular mode coupling. Neither supplies a Hermitian-dilation determinant-fidelity theorem or Xi/RH classification.
- Bhat--Ghatak--Pamula (arXiv:2302.13873) study block operator moment dilations. The searched primary literature contains no result coupling the chiral dilation's Hilbert--Carleman second jet to the reduced Teukolsky source or RH.

## No-go closure

- **Exact killing theorem/mechanism:** `d4HBReducedTeukolskyHermitianDilationFidelityRouteKilled`: Hermitian, finite-support, Hilbert--Schmidt chiral dilation exists unconditionally, while determinant fidelity is exactly the critical-wall/RH condition.
- **Strongest positive survivor:** a successful angular law must forbid doubled chirality by genuine differential/elliptic domain or boundary geometry while remaining source-derived; abstract Hermiticity, modal locality, Hilbert--Schmidt regularity, and coefficient faithfulness do not suffice.
- **New insight:** angular leakage is not inconsistent with a conservative doubled theory. RH-bearing content begins precisely when that doubled theory is required to preserve the original holomorphic source determinant.
- **Status:** corpus and primary-literature audit complete; paper proof dependency-closed; formalized in `ThetaCuspHawkingHBReducedTeukolskyHermitianDilationFidelityNoGo.lean`; direct elaboration and targeted module build PASS; axiom audit only `propext`, `Classical.choice`, `Quot.sound`; formal lint has one unrelated concurrent `HTGeometry.ExtMiddleProduct` umbrella error.

## Log

- 2026-08-31 — C1--C3 falsified from corpus; C4 isolated and paper-proved as exact route kill.
- 2026-08-31 — Lean certificate completed, wired into `RHTower`, targeted build and axiom audit passed; card promoted to stage 3.
