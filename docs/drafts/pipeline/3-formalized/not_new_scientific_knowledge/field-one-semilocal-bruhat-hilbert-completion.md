# Hilbert completion of semilocal Schwartz--Bruhat tensors

- **ID:** `field-one-semilocal-bruhat-hilbert-completion`
- **Stage:** 3-formalized
- **Type:** CONSTRUCTION / THEOREM (Lean)
- **Labels:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `field-one-semilocal-bruhat-l2-embedding`
- **Statement:** pull back the product-Haar \(L^2\) inner product along the faithful algebraic
  Schwartz--Bruhat realization; its abstract Hilbert completion is canonically isometrically
  equivalent to the closure of the algebraic image, and the Weyl action extends unitarily with
  exact ambient intertwining.

## Theorem

Let
\[
  J:\mathcal S(\mathbb R)\otimes_{\mathbb C}
       C_c^{\mathrm{lc}}(\mathbb A_f)
    \longrightarrow L^2(\mathbb R\times\mathbb A_f)
\]
be the injective pointwise-product realization. Give the source the pulled-back norm and inner
product. If \(H_{\mathrm{SB}}\) is its uniform/Hilbert completion, then
\[
  H_{\mathrm{SB}}
    \simeq_{\mathrm{iso}}
  \overline{\operatorname{range}J}
    \subseteq L^2(\mathbb R\times\mathbb A_f).
\]
The completed map is a linear isometry whose range is exactly the closed algebraic image.

Each algebraic Weyl automorphism preserves the pulled-back norm because \(J\) intertwines it
with the ambient \(L^2\) unitary. It therefore extends to a unitary
\(\widehat W_a\) on \(H_{\mathrm{SB}}\), satisfying
\[
  J^\wedge\widehat W_a=W_a^{L^2}J^\wedge,
  \qquad
  \widehat W_a\widehat W_b=\widehat W_{a+b}.
\]

This is the completed comparison to the generated closed subspace. It does **not** assert
\(\overline{\operatorname{range}J}=L^2\); full-product density and sheaf compatibility remain
separate obligations.

## Lean certificate

- **Module:** `GaloisForLFunctions.RHTower.FieldOneSemilocalBruhatHilbertCompletion`
- **Core definitions:** `FieldOneSemilocalBruhatHilbertCompletion`,
  `fieldOneSemilocalBruhatCompletionEquivClosedImage`,
  `fieldOneSemilocalBruhatCompletionToL2`,
  `fieldOneSemilocalBruhatCompletionWeylUnitary`
- **Core theorems:** `fieldOneSemilocalBruhatCompletionEquivClosedImage_coe`,
  `fieldOneSemilocalBruhatCompletionToL2_range`,
  `fieldOneSemilocalBruhatCompletionToL2_weyl`,
  `fieldOneSemilocalBruhatCompletionWeylUnitary_add_apply`
- **Audit:** direct cached `lake env lean` passed. Scratch `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`. Final targeted `lake build` remains reserved
  for final audit.

## Gates

- [x] 0 → 1: faithful algebraic \(L^2\) map and induced pre-Hilbert structure typed
- [x] 1 → 2: completion-to-closure equivalence and completed Weyl laws proved
- [x] 2 → 3: unconditional direct Lean check and axiom audit
- [ ] 3 → 4: publication-ready integration
