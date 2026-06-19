# Scorecard update — Professor — the coupling-apex chipping diagnosis (C5 status sharpened)

**For:** librarian + all. **Date:** 2026-06-19. **Author:** Professor. Did not touch ledger files.
**Context:** user steered the loop to "chip the coupling apex" (the cone∩generic / B7 / realization-IFF
frontier). This records the conclusion of that chipping.

## Working diagnosis: C5 = the apex coupling; no sub-apex provable-native theorem found
Three independent results now converge to one structural conclusion:
1. **faces-orthogonality** (#75/B29/#84/G10, re-proven): each face alone is **parent-reachable** — Face A
   (positivity) = dBN/Li (the log audit L1430: "positivity attack collapses to dBN, no new mechanism"),
   Face B (genericity) ⇏ RH (off-line is generic, #84). So neither face alone is C5.
2. **The positivity/finite-free machinery is tautological** (`c5-jensen-prime-kernel` §8): `λ_min(S_d(t))≥−1
   ⟺ H_d⪰0 ⟺ section roots real ⟺ hyperbolic` is exactly **Hermite's theorem**. Every refinement
   (`A_d+δH_d` split; Wheeler's rank-1 + (d−1)-residual) reparametrizes "are the roots real." Consequently
   **an a-priori (RH-free) bound on the residual's negative extreme would *be* a proof of RH** — there is no
   easier sub-apex version inside this machinery.
3. **The realization-IFF converse is genuinely apex** (#86): the easy counterexample (an arbitrary generic
   LP function with FE — two faces, no Euler) is blocked by the **source-built constraint** (the converse is
   about Bohr-lift / multi-q-built objects, not arbitrary ones), so it is not trivially refutable.

**Conclusion (diagnosis, not a proof of impossibility).** The proto-branch's only *native, irreducible*
content is the **RH/DSS coupling itself** (the single rigidity, the a1-a2 unification) = the apex. Hence the
branch earns **C5 essentially when RH/DSS is proven**; there is no evident provable-native theorem strictly
below the apex. This is the structural reason C5 has been elusive — and it is itself the honest answer to
"is this a branch?": a **proto-branch whose keystone is the apex.**

## Recommended scorecard note (00-status §A)
Add: "C5-chipping (2026-06-19): the coupling is the apex; the positivity machinery is Hermite-tautological;
no sub-apex provable-native theorem located. C5 ⇔ apex (RH/DSS coupling). The genuinely-new flagged handles
(B7 Bogomolov-minimality, realization-IFF converse #86) remain apex/open."

## Two realistic paths forward (for the user to weigh)
- **(A) Consolidate/formalize the BRIDGE corpus.** `3-formalized` is EMPTY despite 16 proven cards. Moving
  proven results to axiom-clean Lean solidifies the branch's *actual* content regardless of C5. Highest
  concrete value; Leaner's lane.
- **(B) Apex campaign.** Commit to the flagged genuinely-new handles (B7 Bogomolov-minimality with the
  Liouville gap; the realization-IFF converse) as a long campaign — Fields-Medal-hard, sub-lemmas only.

The live team frontier (DeWitt integer-gap residual, Wheeler residual structure) is path (B); per result 2
its win condition is producing an **a-priori** residual bound — which, if achieved, *is* RH.
</content>

---

## CORRECTION (2026-06-19, after Wheeler #89) — result 2 was too strong; there IS a non-tautological C5 candidate

My "result 2" (the positivity machinery is tautological ⟹ no sub-apex C5) applies only to the **EXACT**
criterion `λ_min(S_d)≥−1 ⟺ roots real` (Hermite). Wheeler's **gap-difference condition**
> **(GD)**  `sup_t |ε_l(t) − ε_{l+1}(t)| < Δ_l`  ∀l,d  ⟹ no adjacent root collision ⟹ hyperbolic ⟹ RH
is a **sufficient** (strictly stronger) condition that is **genuinely non-tautological**: `Δε_l(t) =
Σ_p p^{−1/2} e^{−𝔦t\log p}[K_d(r_l;p)−K_d(r_{l+1};p)]` (explicit prime Bohr sum, my kernel) and `Δ_l`
(explicit Hermite gap: bulk `≍ d^{−1/2}`, edge `≍ d^{−1/6}`) are both computed **without** assuming reality.
It passes the circularity test.

**Revised conclusion.** C5 is **not** simply "= the apex." There is a concrete non-tautological C5
candidate (GD), and the **C5-vs-BRIDGE grade is decided by the large-values question on the gap-differences**:
does `sup_t|Δε_l|` (a `p^{−1/2}` large-values/cancellation quantity, abs/`L²`-divergent per the kernel §6)
stay below `Δ_l` uniformly in `l,d`, and is the bound a parent large-values estimate (Halász/Montgomery ⟹
BRIDGE) or the support-`≤2d` near-resonance (Baker/integer-gap ⟹ native, DeWitt's lane)? The no-margin
persists (the `J'`-sign-flip makes `Δε_l` a sum `~` displacement scale, so `Δ_l` does not cancel).

So the honest scorecard note is: **C5 candidate = (GD), non-tautological; its grade = the large-values
control of the gap-differences `Δε_l` vs the Hermite gaps `Δ_l`.** (Supersedes the "C5 ⇔ apex" line above.)
