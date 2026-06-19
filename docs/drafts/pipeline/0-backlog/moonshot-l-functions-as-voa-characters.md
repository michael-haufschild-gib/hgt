# MOONSHOT — L-functions are characters of vertex algebras; RH = unitarity of the VOA (an arithmetic moonshine)

- **ID:** moonshot-l-functions-as-voa-characters
- **Stage:** 0-backlog
- **Type:** MOONSHOT CONJECTURE (wild; ~10% true; far beyond SOTA)
- **Priority:** FIELDS MEDAL (+)
- **Source:** user directive 2026-06-19 (wild moonshots); the FE=modularity/theta link (`fe-fourier-quasicrystal`),
  the realization/fake-family filter (#81/#86), monstrous moonshine as the template.
- **The wild claim.** The Selberg class is the **representation category of a chiral algebra**; RH is its
  **unitarity**.

## The conjecture
> **Conjecture (arithmetic moonshine).** Each L-function `L(s,π)` in the Selberg class is the **graded
> character / one-point function** of a module over a **vertex operator algebra (VOA) `V`** (a 2D chiral CFT):
> `L(s,π) ↔ \mathrm{tr}_{M_π} q^{L_0−c/24}` under a precise `q↔s` dictionary (the Euler product = the VOA's
> **factorization/operator-product** structure, primes = the simple-current generators; the FE = the modular
> `S`-transform of the character).
> Then:
> - the **Selberg class with its Rankin–Selberg `⊗`** is the **modular tensor category** `\mathrm{Rep}(V)`;
> - **genuineness (Euler product, #81) = `M_π` is a genuine `V`-module** (not a fake non-modular character);
> - **RH ⟺ `V` is a UNITARY VOA** (positive-definite invariant form) ⟺ the character's zeros lie on the
>   self-dual line — the chiral-algebra positivity is the FE-polarization positivity (#137).

## Why ~10% plausible (not random)
- **Monstrous moonshine** is the proof-of-concept: a specific function (`j`) = a VOA character, with deep
  arithmetic — the leap is "all L-functions, systematically."
- The **FE = modular `S`-transform** is exact for ζ (theta/Jacobi); VOA characters are precisely the functions
  with such modular transforms.
- **Rankin–Selberg = `⊗`** (#29, banked) is literally the fusion/tensor of the conjectured `Rep(V)`.
- **Unitary VOA ⟺ positivity** is the standard CFT dictionary; matching it to RH=FE-positivity (#137) is the leap.
- Ties RH to **VOAs / modular tensor categories / moonshine** — far from analytic NT.

## Attack / what would confirm or refute
1. Pin the `q↔s` dictionary on ζ: is there a VOA whose character is `ξ` (or `Λ`)? (Candidate: a `bc`/`βγ`
   ghost system or a lattice VOA whose theta = the completing factor.)
2. Test `genuine ⟺ V-module` against a known fake (Davenport–Heilbronn / superzeta): is the fake a
   **non-modular** (non-VOA) character? (Predicts yes — the fake filter = modularity.)
3. **Refuted if** the FE-modular characters provably cannot be VOA characters (a central-charge/weight obstruction).
- Door: NATIVE if the VOA's chiral algebra is the joint `(σ_p,∂_s)` symmetry.

## Cross-references
- `fe-fourier-quasicrystal.md` (FE=modular), `../2-fully-proven/...rankin...` (#29, `⊗`),
  `bucket-realization-and-fake-family.md` (#81/#86, the genuineness filter = modularity).

## Log
- 2026-06-19 — Professor: filed as a moonshot (user directive). L-functions = VOA characters; Selberg class =
  Rep(V) modular tensor category; RH = VOA unitarity; genuineness = modularity. Arithmetic moonshine; the
  fake-filter-as-modularity is a near-term consistency test.
