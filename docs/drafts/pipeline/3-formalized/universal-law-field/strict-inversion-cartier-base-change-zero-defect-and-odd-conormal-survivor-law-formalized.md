# Strict inversion/Cartier base change, zero defect, odd conormal — Lean certification

- **ID:** ULF-INV-1
- **Paper card:**
  `strict-inversion-cartier-base-change-zero-defect-and-odd-conormal-survivor-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveStrictInversionCartier`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

`inversion` is `LaurentPolynomial.invert`, the strict inversion `q ↦ q⁻¹` on `k[q,q⁻¹]`, and
`cartier` is `eval₂ id 1`, the Cartier specialization `q ↦ 1`, for an arbitrary commutative ring `k`.
`inversion_T`, `inversion_C`, `cartier_T`, `cartier_C` compute them on the generators.

### Theorem 2.1 — the strict square has no defect

`cartier_inversion` proves `ε(σ(p)) = ε(p)` for **every** `p ∈ k[q,q⁻¹]`, by Laurent induction on
monomials `C a · Tⁿ`.  The two `R`-module structures on `S = k` entering the base-change comparison
are therefore literally the same, which is the ring-level content of (IC.3)–(IC.4).

### Theorem 3.1 — the odd conormal survivor

- `inversion_sub_one` — the exact identity `σ(q − 1) = −q⁻¹(q − 1)` (IC.5);
- `inversion_mem_span` — hence `σ(I) ⊆ I` for `I = (q − 1)`;
- `inversion_conormal_odd` — `σ(q − 1) + (q − 1) = q⁻¹(q − 1)² ∈ I²`, which is exactly `σ(e) = −e`
  on `I/I²` (IC.7).

### Section 4 — the positive square

- `positiveDisplacement_eq` — `q + q⁻¹ − 2 = (q − 1)² q⁻¹` (IC.10), so the leading normal term is
  `e²`;
- `inversion_positiveDisplacement` — `σ` fixes it, so the odd orientation disappears after squaring
  (IC.11).

### Section 5 — multiplicative no-selection

`radialGain_isSquare` proves that for every prime-like positive `p` and **every** real `a` the gain
`p^{2a}` is the square of the positive real `p^a`.  A coefficient-relative law that calls a
multiplicative defect trivial merely because it has a positive square root therefore calls every
radius trivial, and Moore-cell fillability cannot select the critical radial origin.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveStrictInversionCartier.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveStrictInversionCartier
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

All checks passed with no warnings.  `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound`.  No project axiom, placeholder, hypothesis interface, or unresolved theorem premise is
used.

## Scope note

The derived equivalence (IC.4) and the identification `Tor₁(S,S) ≅ I/I² ≅ S` (IC.8) are not
certified: they are formal consequences of `ε ∘ σ = ε` and of the free resolution
`0 → R →(q−1) R → S → 0`, but the corpus has no derived-functor layer.  The certified statements are
exactly the ring-level inputs those derived statements consume, and they are what the elimination
argument of §6 uses.

## Exact field consequence

Two candidate mechanisms for a source-normal dagger landing are eliminated unconditionally: the
strict inversion/Cartier square has no comparison defect at all, and every multiplicative radial
gain is already a positive square, so square-root fillability is radius-blind.  The only algebraic
survivor is the odd conormal orientation, which any successful construction must compare against a
doctrine that is not already this strict square.
