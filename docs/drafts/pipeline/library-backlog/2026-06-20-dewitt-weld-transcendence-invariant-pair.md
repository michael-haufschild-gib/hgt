# Library ticket — proposal: classify native objects by the invariant-PAIR (σ-trdeg, ∂-trdeg)

**From:** DeWitt  **Date:** 2026-06-20  **Status:** PROPOSAL (charter-organizational; honestly graded below).
**Target:** a weld-section note + candidate cross-ref from door/00-index (do NOT edit directly — this requests it).

## The invariant
For an object f, the differentially-relevant invariant is the **differential transcendence degree growth**
  d_∂(n) = trdeg_{ℂ(s)} ℂ(s)(f, f', …, f^{(n)}).
- Differentially algebraic (DA) ⟺ d_∂ plateaus (at the minimal ADE order).
- Hypertranscendental (HT) ⟺ d_∂(n) = n+1 for ALL n (maximal growth, never plateaus).
This makes the probe's ONE-SIDEDNESS exact: "resist up to order n" = d_∂ maximal *so far*; certifying HT =
proving maximal growth for ALL n = a transcendence theorem, never a finite computation (Hölder for Γ).

The weld 𝓜⁺ has TWO axes (∂_s differential, σ_p / shift difference), so the native invariant is the PAIR
  ( d_σ , d_∂ )  =  (difference-transcendence degree , differential-transcendence degree).

## Classification of the seed objects [partly CONJECTURE]
- **Γ**: Γ(z+1)=z·Γ(z) is a 1st-order linear difference equation ⟹ d_σ FINITE (difference-algebraic).
  Hölder 1887 ⟹ d_∂ = ∞ (HT). **Pair = (finite, ∞).** The constraint is a DIFFERENCE equation; no flow.
- **ζ**: no algebraic difference equation in s [CONJECTURE — believed known: ζ is difference-transcendental]
  ⟹ d_σ = ∞; HT ⟹ d_∂ = ∞. **Pair = (∞, ∞).** Pinned NOT by a difference or differential relation but by
  the functional-equation REFLECTION s↔1−s — a discrete SYMMETRY (a third kind of constraint).
- **P(s)=Σ_p p^{−s}**: no clean difference equation ⟹ d_σ = ∞ (likely); d_∂ OPEN (see retraction ticket).

## What this organizes (the contribution)
1. **"Constraint not flow" becomes PLURAL and precise:** the constraint pinning a native object can be
   (i) a difference equation (Γ: σ-finite), (ii) a reflection/symmetry (ζ: functional equation), or
   (iii) none of the elementary ones — but NEVER a differential flow (all seed objects are ∂-∞).
2. **Certifiability is per-axis and one-sided each way:** an object is CATCHABLE on an axis iff it is
   ALGEBRAIC (finite trdeg) there — Γ is caught on the σ-axis at order 1; E2 is caught on the ∂-axis at
   order 3 (Chazy). TRANSCENDENCE on an axis (∞ trdeg) is never catchable by a probe — only by proof.
   So ζ, transcendental on BOTH algebraic axes, is catchable on neither; its only handle is the symmetry.
3. Pairs with Wheeler's 2-probe operational criterion (differential probe ↔ d_∂; shift probe ↔ d_σ),
   and explains the probe one-sidedness uniformly.

## HONEST novelty grade
The framework (σ-∂ / difference-differential transcendence degrees) is **Hardouin–Singer (known)**; Γ
difference-algebraic is classical; ζ HT and (believed) difference-transcendental are known. A specialist
would assemble this classification readily ⟹ **largely reduces-to-known**. The value is CHARTER-
ORGANIZATIONAL: the invariant-pair as the native classifier, the plural-constraint refinement of
"constraint not flow," and the per-axis one-sided certifiability picture. **Recommend:** accept as a
charter organizing note if useful; do NOT promote as a result. The genuinely OPEN cell is P(s)'s d_∂.
