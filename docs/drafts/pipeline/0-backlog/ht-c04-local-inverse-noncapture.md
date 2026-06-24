# Local inverse noncapture — no finite differential equation for the inverse germ

- **ID:** ht-c04-local-inverse-noncapture
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C04
- **Statement:** If a generic analytic `f ∈ HT_K` has a local inverse `g=f^{-1}`, then `g` satisfies no finite algebraic-differential relation over the inverse-side base, except degenerately when the base already encodes `f`.

## Goal
Rule out a **finite handle on the inverse germ**. Door: inversion is not a differential-rational expression in `f`, so closure principles do not settle it — a distinct handle.

## Door grade (hint)
**BRIDGE-likely.** A small handle on `g` should pull back through `f=g^{-1}` to a hidden handle on `f`.

## Approach
Elimination test: from `f(g(y))=y` differentiate to express `g',g'',…` in `f`-jets at `g`; a differential polynomial in `g` pulls back to one in `f` ⇒ Hölder ⇒ BRIDGE. Methods: 3 reverse, 19 write the fake proof, 20 name the missing lemma (the pullback elimination lemma).

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C04.

## Log
- 2026-06-20 — created in 0-backlog from bucket C04.

## 2026-06-24 Haiku audit -- inverse noncapture is universal but source-adjacent

Entropy selected C04 after the finite-state card source-collapsed. The generic wording can be sharpened to a
universal local-germ theorem.

### Local inverse theorem `[PROVED HERE]`

Let `K` be a differential field of germs closed under the usual DA operations, and let `f` be an analytic germ
hypertranscendental over `K`. If `f'(a) != 0` and `g=f^{-1}` is the local inverse germ at `f(a)`, then `g` is
hypertranscendental over the corresponding inverse-side DA base. More concretely: if `g` were DA, then `f` would
be DA because DA germs are closed under local compositional inverse. Therefore `g` is HT.

For `H=1/Gamma`, every regular local inverse branch `H^{-1}` is HT. This is the ingredient used in
`transcendental-composition-ht.md` to refute the category-free slogan "HT composed with HT is HT":
`H^{-1} ∘ H = id` is DA while both local factors are HT.

### Source and promptability boundary

The theorem is a direct contrapositive of standard DA closure under local inverse. Ait El
Manssour--Sattelberger--Teguia (2023), *D-Algebraic Functions*, Proposition 3.11 records inverse closure, and
Proposition 3.8 records composition closure. Thus C04 is correct and useful, but not a new external theorem.

Project value: C04 supplies a scope gate. Local inversion preserves HT, but it also shows that local analytic
germs form a bad category for composition-closure claims, because inverse-germ cancellation can turn two HT
germs into a DA identity. Any theorem about `Gamma∘Gamma` or Feigenbaum self-composition must impose global
conditions excluding this inverse-germ mechanism.

Verdict: BRIDGE/gatekeeper; do not promote as a significant new HT theorem unless a genuinely global inverse
noncapture statement is isolated beyond standard DA inverse closure.

## 2026-06-24 strengthening -- DA local diffeomorphisms factor through HT germs

The inverse theorem gives a stronger local-category warning.

### Factorization theorem `[PROVED HERE]`

Let `H` be any locally univalent HT analytic germ over `K`, and let `h` be a local DA diffeomorphism whose local
inverse is also DA over `K` (for example any nonconstant rational or algebraic local coordinate change at a
regular point). Then

`h = (h ∘ H^{-1}) ∘ H`

as local germs, and both factors `H` and `h ∘ H^{-1}` are HT.

Proof. The germ `H` is HT by assumption. By the local inverse theorem, `H^{-1}` is HT. If `h ∘ H^{-1}` were DA,
then composing on the left with the DA germ `h^{-1}` would make

`H^{-1}=h^{-1} ∘ (h ∘ H^{-1})`

DA by DA closure under composition, contradiction. Hence `h ∘ H^{-1}` is HT. ∎

Specializing `h=id` recovers the earlier counterexample `H^{-1}∘H=id`.

### Consequence

In the local analytic-germ category, HT is not merely non-closed under composition. The product of two HT local
diffeomorphism germs contains every DA local diffeomorphism with DA inverse, after choosing one locally univalent
HT coordinate `H`. Thus local composition algebra is too coarse to detect HT: HT can cancel completely by inverse
coordinates. Any meaningful composition theorem must impose global continuation/domain restrictions, not just
local differential transcendence.
