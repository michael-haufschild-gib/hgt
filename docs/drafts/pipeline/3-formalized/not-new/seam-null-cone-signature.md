# The signature of the seam supermetric is neutral, never Lorentzian

- **ID:** seam-null-cone-signature
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]`, axiom-clean. Pins the inertia signature of the polarized seam supermetric `Q` (a symmetric bilinear form carrying a compatible complex structure `J`, `J² = -1`, `Q(J·,J·)=Q`) against the three defining features of a Lorentzian metric.
- **Scope note:** pure linear algebra of a polarized form — a rigidity of `J`, no carrier, no flow. Extends and completes [[seam-supermetric-signature-answered]] (the tree's nondegenerate `polarized_negIndex_even`).

## The question
A metric is *Lorentzian* when it has (1) exactly one time direction, (2) a nondegenerate metric, and (3) a light cone. Does the seam supermetric `Q`?  Answer: **no.** One mechanism — `J` pairs every direction with its partner — settles all three, and each answer separates the seam from Lorentzian geometry.

## What is proved (`formal/GaloisForLFunctions/RHTower/SeamNullConeSignature.lean`)

**(1) One time direction — false.**
- `polarized_sigNeg_even` — the negative index (mathlib `sigNeg`, the count of time directions) is **even**, with **no nondegeneracy hypothesis** on `Q`. This strengthens the tree's `polarized_negIndex_even` (which required `Q.Nondegenerate`) and states the result through the standard inertia invariant.
  - Proof = the extension argument. `extend_Jinvariant_negdef`: a `J`-invariant negative-definite subspace `W` of dimension `< sigNeg` grows by a whole negative-definite `J`-plane — a maximal negdef subspace meets the (`J`-invariant, `orthogonal_Jinvariant`) `Q`-orthogonal complement of `W` in a nonzero `v` with `Q(v,v)<0`, and `span{v,Jv} ⊆ Wᗮ` adjoins `W` orthogonally (`negDef_sup`). The dimension count uses `finrank_add_finrank_orthogonal'`, which holds for degenerate forms. `build_even_negdef` iterates; parity then forces `sigNeg` even.
- `polarized_sigPos_even` — the positive index is even too (apply the theorem to `-Q`, polarized by the same `J` via `polarizedNeg`).
- `polarized_not_lorentzian` — `sigNeg ≠ 1`: a lone time direction is impossible.

**(2) Non-degeneracy — the radical is even.**
- `radical_finrank_even` — the radical `Q.orthogonal ⊤` is `J`-invariant (`orthogonal_Jinvariant` at `⊤`), hence even-dimensional. If the metric degenerates, it degenerates in `J`-pairs.

**(3) Light cones — the cone is fat.**
- `null_forces_isotropic_plane` — a single nonzero null vector `x` (`Q x x = 0`) drags its whole `J`-plane `span{x,Jx}` into the null cone as a **2-dimensional totally isotropic subspace** (`null_plane_totally_isotropic`, from `Q(a·x+b·Jx) = (a²+b²)·Q(x,x) = 0`). A Lorentzian form has Witt index `1` — its maximal totally isotropic subspace is a line — so the seam form, whenever it has any null vector, is not Lorentzian read from the light-cone side either.

**Capstone.** `polarized_inertia_triple_even` — the full inertia triple `(sigPos, sigNeg, dim radical)` is `(even, even, even)`. Neutral, never Lorentzian `(n−1, 1, 0)`.

## The structural content
Under a compatible complex structure every part of the metric — positive, negative, and degenerate directions, and the null cone — comes welded in `J`-pairs. The negative index even is the functional equation's conjugate-pairing of off-line zeros, obtained as a rigidity of `J` rather than propagated by any flow. The seam's supermetric is neutral `(2a,2b,2c)`: there is no single York-time axis, which is why the seam clock ([[seam-clock-selection]]) is not a lone time direction.

## Constraint, not flow
No carrier is built; `J` is a given compatible structure and the pairing is what it forces on the inertia cone. Concrete realization: the FE seam Krein index `κ₋ = k` (`SeamInertiaCharge.seamCarrier_exact_inertia`).

## Lean
- Module `formal/GaloisForLFunctions/RHTower/SeamNullConeSignature.lean`, in the `RHTower` umbrella.
- 6 exposed theorems, axiom-clean `{propext, Classical.choice, Quot.sound}`, `formal lint passed`.
- Housekeeping: removed a dead `import SeamSpectralFlow` from `SeamPolarizationWeld.lean`, replacing it with the narrow `import Mathlib.LinearAlgebra.BilinearForm.Orthogonal` (the analytic module was referenced only in a comment; this decouples the polarization algebra from the analytic tower).

## What it opens
- The neutral `(2a,2b,2c)` signature contrasts sharply with gravitational superspace's Lorentzian DeWitt supermetric — a native structural difference to push on: what plays the role of the conformal (York) mode when there is no distinguished time axis?
- The null cone carries `J`-planes (Witt index `≥ 2` whenever nonempty): the maximal totally isotropic subspace is itself even-dimensional and `J`-invariant — a further parity invariant to compute.
- Degenerate-`Q` regime is now in scope (nondegeneracy dropped): the interplay of the radical's `J`-pairs with the seam's actual degeneracy locus is the next object.
