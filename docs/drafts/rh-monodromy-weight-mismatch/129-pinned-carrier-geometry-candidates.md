# 129 — Pinned-carrier geometry candidates, cut by the lane's two instruments

- **Register:** SEARCH. Orientation. The candidate carriers below are from the literature (arXiv
  refs as cited); nothing about them is claimed as new here. The only load-bearing claims are the two
  **cuts**, which are backed by banked machine-checked theorems in this repo.
- **Purpose:** doc 128 §5 / charter §13 handed forward one question — *is there a space, other than
  the `s`-plane, where prime content and the ξ-divisor share a pinned carrier?* — under the rule
  (rule 7) that any zero-side obtained by analytic continuation, contour shift, a determinant set
  equal to `Ξ`, or propagation of `ζ` is disqualified as a flow in disguise. This document does not
  answer it; it **cuts** the candidate list with the lane's own instruments so the live target is
  exact.

## 1. The two instruments (banked, verifiable)

The lane has, machine-checked and axiom-clean, exactly the two tests a candidate carrier must face:

- **Negative cut — freeness is deck-invisibility** (`RelativeTorsor.lean`, doc 128). A reference
  frame that is *free* — a single-valued global root / a globally invertible comparison object —
  is a **coboundary**: it cancels in the deck cocycle (`relative_deckClass_eq`,
  `reference_own_deckClass_one`). It contributes **no** obstruction. Freeness and contribution are
  mutually exclusive.
- **Positive test — the ζ-free non-fake-defect criterion** (`FittingSeamBoundary.lean`, charter §13).
  On a torsion seam presentation `Rⁿ --A--> Rⁿ → Q` with `det A = Xᵐ`, a defect `Δ_p` has boundary
  class `tr(adj(A)·Δ_p) mod Xᵐ`; **fake** defects `Δ_p = A·H_p + Xᵐ·K_p` vanish
  (`fittingBoundaryClass_eq_zero_of_right_factor_mod_X_pow`), so a live divisor requires a
  **non-fake** defect `Δ_p ∉ A·End + (Xᵐ)`. Crucially the divisor here is `det A = Xᵐ` — **algebraic
  data, not ζ's zero set**. So "non-fake defect on an intrinsic presentation" is precisely a
  **ζ-free acceptance test**: a carrier passes iff it produces such an `A` from its own `∂_s` and
  `{σ_p}` structure, without importing ζ.

The negative cut says *free carriers produce no divisor*; the positive test says *a legitimate
divisor is a non-fake defect on an intrinsically-produced presentation*. Every candidate is scored by
these two.

## 2. The candidates and the cut

| Candidate (literature) | Support-sharing? | Cut by the two instruments |
|---|---|---|
| **Log-comb `𝓜⁺_log ⋊ ⟨σ_p⟩`**, `[D,σ_p]=(log p)σ_p` (ax+b / Mellin scaling structure) | **Yes, automatic** — `D` and `σ_p` share the log-support by construction | The `σ_p` shift `δ_{log n} ↦ δ_{log pn}` is the **regular action of the free monoid ℕ^×** — *free*. Negative cut ⟹ **deck-invisible**: `D − ρ` is invertible off the real log-spectrum `{log n}`, so the bare carrier has **no complex divisor**. The divisor cannot come from the free action; it needs a freeness-breaking quotient. |
| **Adèle-class / idèle scaling** `A_ℚ/ℚ^×`, `C_ℚ` (Connes, math/9811068) | Yes — primes are periodic orbits of length `log p`; scaling is `∂_{log}` | The quotient by `ℚ^×` **does** break freeness (compact quotient), so it escapes the negative cut — this is why the trace formula sees the zeros. But the meeting is **trace-level**, not germ-level: it gives `prime orbits ↔ spectral divisor`, not an intrinsic presentation `A` with `det A = Xᵐ` at a pinned `ρ`. Positive test **not yet** applicable — no pinned `J_m`. |
| **Semilocal Sonin / prolate** `S_λ(K_S) = {f : f|_{|x|<λ}=0, f̂|_{|x|<λ}=0}` (Connes–Consani–Moscovici, 2310.18423) | Yes — local fields, cutoff, scaling generator, `p`-place support all native | The Fourier-uncertainty **cutoff breaks freeness** at a **finite boundary**, `S` a finite set of places — this is the one candidate whose obstruction is **germ/boundary-level**, not trace-level. Positive test is **applicable in principle**: the boundary defect of `(∂_{log} − ρ, {σ_p})` on `S_λ(K_S)` is exactly the object to feed the non-fake criterion. **Strongest germ-level survivor.** |
| **Arithmetic / scaling site** (`ℕ^×`, `ℤ_max`; Connes–Consani) | Yes — Frobenius `σ_p ⊂ End(𝒪)` native | Freeness broken by the topos structure, but the **divisor side is conjectural**: the missing piece is a Weil cohomology making the zero-side a Lefschetz formula. Positive test cannot yet be run — there is no intrinsic `A`. |
| **Zeta spectral triples** (finite Euler perturbations, 2511.22755) | Finite prime content → operator perturbation | Finite-dimensional *pinned* flavor — a legitimate **finite obstruction laboratory** *iff* the divisor is defined by the finite obstruction itself. **Disqualified** the moment the final step is "the determinant converges to `Ξ`" — that is the ζ-flow in disguised spectral form (rule 7). |
| **Deninger foliated dynamics** (leafwise cohomology) | `primes = closed orbits`, `zeros = generator spectrum` | Conceptually the exact meeting shape, but **disqualified** whenever the foliation is built by fitting ζ's zero set. Counts only if the foliated space is arithmetic-first — currently not. |

## 3. The verdict, sharpened

The negative cut explains *why* the support-sharing log-comb (Candidate 3, the natural native carrier)
does **not** by itself carry a divisor: its `σ_p` action is free, hence deck-invisible — the same
mechanism that collapsed the relative torsor (doc 128). The divisor can appear **only after a quotient
or boundary breaks freeness**. Of the freeness-breaking quotients on offer, the adèle-class one gives
a **trace-level** meeting (Connes), the arithmetic site gives a **conjectural** one (missing Weil
cohomology), and only the **semilocal Sonin boundary complex** gives a candidate **germ-level**
(pinned, finite-boundary) obstruction. So the live target is exact:

> **The one lane-attemptable, ζ-free test:** build the boundary defect of `(∂_{log} − ρ, {σ_p})` on
> the Sonin space `S_λ(K_S)` as a seam presentation, and check whether its `σ_p`-defect is **non-fake**
> (`Δ_p ∉ A·End + (Xᵐ)`, `FittingSeamBoundary`) or fake (collapses, like every free reference so far).
> If non-fake **and** produced without importing ζ, it is the first genuine `{σ_p}`-graded pinned
> divisor. If fake, the Sonin boundary joins the collapse and the `s`-plane freeness extends to the
> adelic boundary too.

The germ-level divisor built intrinsically (no continuation, no `det = Ξ`) is the missing Weil
cohomology / Hilbert–Pólya apex — **known-open**, not to be faked. The lane does not claim it. What
the lane contributes is the pair of instruments that turn "which geometry?" into a decidable test:
*break freeness (else deck-invisible) and pass the non-fake criterion (else ζ-imported).*

## 4. Why no Lean module here

Rule 8: the carriers above are all in the literature and the log-comb relation `[D,σ_p]=(log p)σ_p`
is the known ax+b/Mellin structure — formalizing them and presenting it as progress would be theatre.
The two instruments this document applies are **already banked** (`RelativeTorsor`,
`FittingSeamBoundary`); they are the contribution. New Lean is warranted only when there is a
genuinely new object to certify — a Sonin-boundary seam presentation with a **non-fake** `σ_p`-defect
produced without ζ. Until such a defect exists, writing code would be certifying known geometry, not
research. The forward move is to construct that boundary defect and run it through the banked non-fake
criterion — the first step that is neither a walked route nor a flow.
