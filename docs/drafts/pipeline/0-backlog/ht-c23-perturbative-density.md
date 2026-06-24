# Perturbative HT density — small generic perturbations land in (and stay in) HT

- **ID:** ht-c23-perturbative-density
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C23
- **Statement:** Around any sufficiently regular function, arbitrarily small generic perturbations are HT; conversely, a generic small perturbation of an HT function remains HT.

## Goal
Establish **stability/instability of handles under perturbation**: exact algebraic-differential identities are fragile; HT is open under generic small noise. Door: a perturbative companion to the topological-largeness claim C22.

## Door grade (hint)
**Genuinely-new flavour.** Exact polynomial identities are non-generic; a tiny generic perturbation should destroy them without installing a new one.

## Approach
Show `{P(f)≡0}` has empty interior in the chosen norm (perturb one Taylor coefficient to break any fixed `P`); diagonalize over countably many `P`. Pair with mpmath experiments. Methods: 2 attack-as-false, 8 similar objects, 11 run experiments.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C23; C22 (topological), C24 (random).

## Log
- 2026-06-20 — created in 0-backlog from bucket C23.

## 2026-06-24 Haiku strengthening -- affine perturbation quotient geometry

### Promptability audit

No computation is useful here. The statement is forced once the normal form is exposed:

> The differentially algebraic elements over a base field form a differential subfield. What does that imply for
> finite-dimensional affine perturbation families modulo that subfield?

So this is a clean structural lemma and a reusable guardrail, not a claim of deep novelty.

### Theorem `[PROVED HERE / STANDARD]`

Let `K` be a differential field containing the constants `C`, let `E` be a differential field extension, and let

```text
D = { y in E : y is differentially algebraic over K }.
```

Then `D` is a differential subfield of `E`. Fix `G,H_1,...,H_n in E` and define the affine family

```text
F_lambda = G + sum_i lambda_i H_i,    lambda=(lambda_1,...,lambda_n) in C^n.
```

Let bars denote classes in the `C`-vector-space quotient `E/D`. Then the parameter set

```text
S = { lambda in C^n : F_lambda is DA over K }
```

is exactly the affine linear solution set

```text
bar(G) + sum_i lambda_i bar(H_i) = 0  in E/D.
```

Consequently:

1. `S` is either empty or an affine linear subspace of `C^n`.
2. If `bar(H_1),...,bar(H_n)` are linearly independent in `E/D`, then `S` has at most one point.
3. If `G` is DA and every nonzero `C`-linear combination of the `H_i` is HT, then `F_lambda` is HT for every
   nonzero `lambda`.

### Proof

By the standard closure properties of DA elements, `D` is a differential subfield of `E`. Therefore
`F_lambda` is DA over `K` iff `F_lambda in D`, which is equivalent to its class in `E/D` vanishing:

```text
bar(F_lambda)=bar(G)+sum_i lambda_i bar(H_i)=0.
```

This is a finite linear equation in the quotient vector space, so its solution set in `C^n` is empty or affine
linear. The independence and DA-center consequences are immediate. ∎

### Interpretation

Finite-dimensional additive perturbation spaces do not have mysterious DA exceptional sets. The DA locus is just
linear algebra modulo the DA subfield. In particular, once a perturbation direction is genuinely outside the DA
field, at most one point on that affine line can be DA; if the center is DA, that exceptional point is the center.

This explains why constructions such as

```text
P + lambda Q/Gamma
```

have a punctured affine line of HT functions: `Q/Gamma` is a nonzero class in `E/D`.

### Boundary

This is additive geometry only. It says nothing about nonlinear families whose parameters enter through
composition, analytic continuation, or functional equations. Those are exactly the places where Feigenbaum,
Bottcher, Abel/Fatou, and weld-style problems can still contain real mathematics.

### Source anchor

Ait El Manssour--Sattelberger--Teguia, *D-Algebraic Functions* (arXiv:2301.02512), records that DA functions form
a field and are closed under composition, inverse, and differentiation. The affine quotient statement above is the
linear-algebra consequence of that field property.
