# The polarization weld: a compatible complex structure forces the negative index even

- **ID:** hp-seam-polarization-weld
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — the `J`-weld (Sylvester's law of inertia for `J`-forms)
- **Source:** §4 of `../../rh-monodromy-weight-mismatch/123-constraint-reframe-catalog.md` (the
  polarization `J` = T2's weld); links `formal/GaloisForLFunctions/RHTower/OmegaComplexStructure.lean`
  (the polarization `J`) to `formal/GaloisForLFunctions/RHTower/SeamSpectralFlow.lean` (the negative
  index / definiteness face).
- **Statement:** For a nondegenerate symmetric real form `Q` carrying a compatible polarization `J`
  (`J² = -1`, `Q(Jx,Jy) = Q(x,y)`), the space splits `J`-invariantly and `Q`-orthogonally into a
  negative-definite `Nneg` and a positive-definite `Npos` (`polarized_signature_decomp`), and the
  **negative index `κ₋ = finrank Nneg` is even** (`polarized_negIndex_even`). The polarization forces
  off-line negativity to occur only in `J`-conjugate pairs — the functional equation's
  conjugate-pairing of zeros, obtained as a rigidity of the compatible complex structure.

## Goal

§4's flagship reframe says: "making the indefinite FE-form definite = choosing a compatible complex
structure `J` (a polarization)." `SeamSpectralFlow` built the index reduction (RH ⟺ definiteness `κ₋ = 0`)
but left the `J` itself unlinked — the polarization surface `OmegaComplexStructure` develops `J` and its
`Q`-interaction, but nothing tied `J` to the negative index. This card **builds that weld**: it proves
what a compatible `J` *does* to the index — it pins negativity into even-dimensional `J`-blocks, so
`κ₋` is even. mathlib has no signature/inertia theory; this is built from scratch.

## The Lean certificate (axiom-clean)

`GaloisForLFunctions/RHTower/SeamPolarizationWeld.lean` (25 declarations, all
`[propext, Classical.choice, Quot.sound]`, lint green, in the `RHTower` umbrella):

- **The pairing lever** — `polarized_negDef_plane` / `polarized_posDef_plane`: on the forced `J`-plane
  `span{x, J x}`, `Q = (a²+b²)·Q(x,x)`, so a single non-isotropic direction drags its `J`-partner into
  a whole definite two-plane. `polarized_plane_Jinvariant` (the plane is `J`-invariant),
  `Jinvariant_subspace_finrank_even` (a `J`-invariant subspace is even-dimensional — `J` restricts to a
  complex structure).
- **The Sylvester foundations** — `exists_self_ne_zero` (nondegenerate symmetric ⟹ non-isotropic
  vector), `orthogonal_Jinvariant` (the `Q`-orthogonal complement of a `J`-invariant subspace is
  `J`-invariant, via `J` skew-adjoint), `plane_restrict_nondegenerate`, `omegaRestrict`/`polarizedRestrict`
  (the polarization restricts to any `J`-invariant subspace — the recursion's inductive object), plus
  the assembly lemmas (`negDef_sup`, `isCompl_planeExtend`, `lift_sup`, `lift_inf`, `plane_orthogonal_zero`).
- **`polarized_signature_decomp`** — the signature decomposition: `V = Nneg ⊕ Npos`, `J`-invariant and
  `Q`-orthogonal, `Q` negative-definite on `Nneg`, positive-definite on `Npos`. Strong induction on
  `finrank`: peel a non-isotropic `J`-plane, recurse into its (`J`-invariant, nondegenerate) orthogonal
  complement, reassemble by the plane's sign.
- **`polarized_negIndex_even`** — the capstone: `κ₋ = finrank Nneg` is **even** (`Nneg` `J`-invariant),
  negative-definite, and maximal (any negative-definite subspace is disjoint from the positive-definite
  `Npos`, hence dimension `≤ finrank Nneg`).

## Approach

The whole weld turns on one computation the polarization surface already supplies
(`Q_apply_span_self_of_isSymm`): on `span{x, J x}`, `Q` is the Euclidean form scaled by `Q(x,x)`. So the
sign of `Q` is constant on each `J`-plane, and `J`-planes are `2`-dimensional. Sylvester's inertia
induction then decomposes the form into `J`-planes; the negative ones sum to `Nneg`, a `J`-invariant
(hence even) maximal negative subspace. No carrier or operator is constructed — the decomposition is a
structural property of the *given* polarized form, and the peeling operates on that fixed form (rule 7:
the invariant is what survives, not what is propagated).

## Verdict — dual gate

**DELIVERED (formalized):** the `J`-weld is proven and machine-checked, axiom-clean. §4's polarization
`J` is now linked to the negative index by theorems: a compatible `J` forces `κ₋` even. This closes the
front the `SeamSpectralFlow` card had left open ("the concrete `J ⟹ definite` link … the one weld still
to build").

**Graded as branch infrastructure (a mathlib-gap fill):** Sylvester's law of inertia is classical, and
its `J`-invariant refinement (Hodge-index parity) is known Hodge theory — mathematically reduce-to-known.
But it is **absent from mathlib** (no signature/inertia theory exists there), so the formalization is
genuine new infrastructure; and the *application* — welding `OmegaComplexStructure`'s `J` to the seam
Krein index and reading `κ₋` even as the FE conjugate-pairing — is the branch-native content. Significance
real: it makes the T2 polarization operational on the index prong, turning "off-line zeros pair up" from a
symmetry observation into a rigidity of the compatible complex structure.

**Where it points (not a terminus):** the decomposition gives, for a *given* polarization, `κ₋` even —
but the RH content is the **existence** of a positive polarization (`Npos = ⊤`, `κ₋ = 0`). The next moves:
(1) feed `polarized_negIndex_even` back to `SeamSpectralFlow` — an odd off-line count obstructs *any*
compatible polarization, sharpening the reduction; (2) the period-domain existence question on
`D_∞ = Sp_∞(ℝ)/U(∞)` (T2) — when does the arithmetic fix a *positive* `J`; (3) the complex/Hermitian
analogue over the actual FE Krein form (this card is the real-form model). The parity is the first
rigidity the polarization imposes; the positivity is the frontier.

## Log
- 2026-07-07 — created in 3-formalized: the `J`-weld built end-to-end (`SeamPolarizationWeld.lean`, 25
  decls, axiom-clean, lint green). Sylvester's law of inertia for `J`-forms formalized from scratch
  (mathlib gap); `polarized_signature_decomp` + `polarized_negIndex_even` prove a compatible `J` forces
  `κ₋` even — the FE conjugate-pairing as `J`-rigidity. Links `OmegaComplexStructure` (T2's `J`) to
  `SeamSpectralFlow`'s negative index; front-1 of the §4 follow-up closed.
