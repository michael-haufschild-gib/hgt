# Library update request — INDEX + STATUS agent — new bucket X9 (archimedean generator) + 4 backlog cards

**For:** the agent that maintains `docs/drafts/door/00-index.md` and `docs/drafts/door/00-status.md`
(librarian). **Date:** 2026-06-19. **Edit-race avoidance:** I did not touch the ledger files; please apply.
**Action:** (A) register the **new bucket** `door/bucket-archimedean-generator.md` in `00-index.md`;
(B) add **4 new §C rows** to `00-status.md` for the new backlog cards; (C) bump the §D tally.

Numbers assumed from current ledger state: next bucket = **X9**; corank-seam-invariant is **#125**, so the
next §C rows are **#126–#129**. Adjust if the ledger advanced since.

---

## A. `00-index.md` — add the bucket to the cross-cutting table

Insert a new row in the **cross-cutting buckets** table (the `| Bucket | Scope | Serves | Work package |`
table, ~lines 38–46), **immediately after** the `[[bucket-the-seam-archimedean-obstruction]]` row (they
are obstruction↔generator duals and should sit together):

```
| [[bucket-archimedean-generator]] | promote the archimedean place from obstruction (X3) to **generator**: adjoin the derivation `∂_s=−Σ_p(log p)θ_p` (`x_p=p^{−s}`; `[∂_s,σ_p]=0`; irreducibly cross-prime) and build the parameterized `(σ,∂)` difference–differential Galois theory `𝓜⁺`, natural object = completed `Λ=Γ·ζ`; lead **falsifiable** bet: `∂_s`=the product-formula relation collapses ℚ-corank `∞→1`, so the missing single Frobenius `=∂_s` (#127); FE `s↔1−s` = internal `⊗`-duality, fixed locus `Re=½` (#128); `Γ=ζ-reg det ∂_s` (Kurokawa) and `ω=0 in 𝓜⁺ ⟺ ∂_s trace-class ⟺ HP ⟺ RH` (#129); first NATIVE/C5 candidate because `∂_s` does not axis-decouple | A1 ∧ A2 | `archimedean-generator-category.md`; `archimedean-corank-collapse.md`; `completed-lambda-internal-fe.md`; `gamma-regularized-det-omega.md` |
```

Optional one-clause cross-link in the existing `[[bucket-the-seam-archimedean-obstruction]]` scope cell:
append `; the constructive dual (adjoin `∂_s` as a generator) is [[bucket-archimedean-generator]] (#126–#129)`.

## B. `00-status.md` §C — add 4 rows (#126–#129)

```
| 126 | **archimedean generator — the category `𝓜⁺`**: adjoin the derivation `∂_s=−Σ_p(log p)θ_p` (`θ_p=x_p∂_{x_p}`, `x_p=p^{−s}`; eigenvalue `−(m·ℓ)` on `e_m`; `[∂_s,σ_p]=0`; cross-prime), define `𝓜⁺=(∂_s,{σ_p})`-modules, conjecture neutral Tannakian with parameterized Galois group `G_L⁺` and `1→G_L→G_L⁺→G_{∂_s}→1`; the apparatus for the archimedean place (Γ-factor, FE, time) the pure-difference theory cannot pose | [[bucket-archimedean-generator]] | CONJECTURE | FOUNDATIONAL |
| 127 | **archimedean corank collapse (lead bet)**: the product formula `∏_v|x|_v=1` in operator form **is** `∂_s=−Σ(log p)θ_p`; conjecture the enriched lattice `Λ⁺` has `corank=1`, so the seam gap `∞−1` reads "`∞` finite primes, `1` archimedean relation" and the **missing single Frobenius `=∂_s`**; falsifiable (collapse vs new infinite generator); Stieltjes test: `trdeg=1` in the `∂_s`-direction; `F_q` anchor `corank=1` | [[bucket-archimedean-generator]] / [[bucket-the-seam-archimedean-obstruction]] | CONJECTURE | FIELDS MEDAL |
| 128 | **completed `Λ` + internal FE**: `M_ζ` extends to `M_Λ∈𝓜⁺` with diagonal section the completed `Λ(s)=π^{−s/2}Γ(s/2)ζ(s)`, Γ = the archimedean Euler factor; the functional equation `s↔1−s` is an **internal `⊗`-autoequivalence/polarization** of `𝓜⁺` (not an import) with fixed locus the critical line `Re=½`; `F_q` recovery = the Γ-free Weil L-polynomial FE (#78) | [[bucket-archimedean-generator]] / [[G5-unitarity-gatekeeper]] | CONJECTURE | FOUNDATIONAL |
| 129 | **`Γ=ζ-reg det(∂_s)`; `ω=0 in 𝓜⁺ ⟺ RH`**: recast the seam's type-III/`ω≠0` diagnosis (#90/#98) constructively — the Γ-factor is the `ζ`-regularized determinant of `∂_s` (Kurokawa absolute zeta), and adjoining it trivializes the monoidality class: `ω=0 ⟺ ∂_s trace-class (F₁) ⟺ Hilbert–Pólya ⟺ RH`; test = compute `ω` in `𝓜⁺` vs `𝓜`, is `Γ` the trivializing cochain? | [[bucket-archimedean-generator]] / [[G4-multi-q-picard-vessiot-and-langlands-group]] | CONJECTURE | FIELDS MEDAL |
```

## C. §D tally / headline counts

- row count `125 → 129` (**+4**);
- **CONJECTURE / "stated conjectures"** count **+4** (all four new rows are conjectures); no change to
  proven / import / Lean / candidate / falsified counts.
- Optionally add to §B ("pick something to prove"): the **lead falsifiable bet #127** (archimedean corank
  collapse) as the highest-leverage new FIELDS-MEDAL item, and the foundational #126 as its prerequisite.

---

## D. Context / non-duplication (read before applying)

- **What this is.** A user-requested research direction: the branch is pure-difference (`σ_p` only) and
  structurally excises the archimedean place, then calls its absence "the seam"
  ([[bucket-the-seam-archimedean-obstruction]]). The new bucket **flips obstruction → generator**: adjoin
  the derivation `∂_s` and build the `(σ,∂)` difference–differential theory. New files (already created):
  - bucket `door/bucket-archimedean-generator.md`;
  - cards `pipeline/0-backlog/archimedean-generator-category.md`,
    `archimedean-corank-collapse.md`, `completed-lambda-internal-fe.md`, `gamma-regularized-det-omega.md`.
- **Non-duplication, flagged:**
  - vs `[[bucket-the-seam-archimedean-obstruction]]` (#90/#92/#98) — **complementary dual, not a
    duplicate.** That bucket *diagnoses* the archimedean place as an obstruction (type III, no trace,
    `ω≠0`); X9 *constructs* the generator (`∂_s`, `𝓜⁺`, `Γ=ζ-reg det ∂_s`) that would resolve it. X9's
    #129 re-poses #90's chain **constructively**; cross-link, do not merge.
  - vs `corank-seam-invariant` (#125) and `baker-for-stieltjes` — #127 supplies the **constructive `∂_s`
    resolution** of the same `∞−1` corank gap those state in difference language. Keep all three; #127 is
    the generator-side card.
  - vs `compute-omega-h2-gl.md` — #129 asks whether `𝓜⁺`/`Γ` **trivializes** the `ω` that card computes;
    references it, does not replace it.
  - The four cards have an internal dependency order (#126 foundational → #127/#128/#129 build on it);
    safe to list all in 0-backlog now.

## E. Pipeline state (FYI, no ledger action needed)

- All four cards are **0-backlog**, gate 0→1 not yet cleared. Lead/decision card = **#127** (corank
  collapse, falsifiable); foundational prerequisite = **#126** (the category). The bucket's open core
  names the attack order.
</content>
