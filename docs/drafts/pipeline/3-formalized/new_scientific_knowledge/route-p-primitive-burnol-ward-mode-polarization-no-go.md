# Route P Ward-mode polarization no-go

- **ID:** `route-p-primitive-burnol-ward-mode-polarization-no-go`
- **Stage:** 3-formalized
- **Type:** FALSIFIED with exact rigidity classification
- **Label:** `P-G198`
- **Source:** P-G197 Ward--Herglotz tangent, P-G182 cubic conormal Gram, P-G168 mixed Hardy jet
- **Statement:** P-G197's positive one-mode Herglotz tangents cannot be polarized entrywise across
  distinct zero modes. On two positive real modes the natural polarization is positive
  semidefinite exactly when the modes coincide; its determinant is otherwise a strict negative
  square.

## Conjecture loop

P-G197 exposes every resolved zero column as a positive summand of an actual Xi aperture tangent.
`C198-A` asked whether polarizing that tangent across zero labels would directly produce the
cross-zero matrix needed by W-H184. This would have bypassed the missing coefficient-faithful
landing.

At a common positive real external node `x`, mode rate `a_i` has scalar response
`2/(x+a_i)`. The natural left/right polarization is therefore

```text
M_ij = (1/x) [1/(x+a_i) + 1/(x+a_j)].
```

Each diagonal is exactly the corresponding P-G197 one-mode Herglotz tangent. But on two modes
`a,b`, Lean proves

```text
det M = -[(1/(x+a)-1/(x+b))/x]^2.                 (P-G198.1)
```

For `x>0` and `a!=b`, this determinant is strictly negative. In the positive chamber,

```text
M >= 0  iff  a=b.                                (P-G198.2)
```

Thus positivity of every one-mode tangent does not matrix-amplify over distinct mode labels.

## Exact positive survivor

P-G197 must be read as a positive frame-operator decomposition on the common external-node Hardy
carrier, not as a positive kernel on the zero-label set. Distinct zero modes must remain separate
resolved columns in that common carrier. Their cross-zero cubic Gram can only be formed after a
common generator/derivative operation: differentiating `1/(w+lambda)` gives the squared resolvent,
whose Hardy/radial Gram has cubic Cauchy order.

This locates the missing structure more precisely. W-H184 cannot come from entrywise polarization
of the Ward response. It needs a source-controlled graph norm for the noncommuting generator that
acts on all resolved columns before their Gram is taken. P-G196 supplies the required nonzero
commutator anomaly; P-G186 and P-G182 already realize source and target cubic columns as radial
generator modes. The remaining theorem is a coefficient-faithful polar--Gamma graph-norm
contraction, not another Pick-kernel positivity statement.

## Hostile novelty audit

P-G168 already proves an abstract mixed Hardy jet equals the cubic Hellinger kernel, so repeating
that derivative calculation would be theatre. Corpus search found no cross-mode Ward polarization,
negative-square determinant, or PSD coincidence classification. P-G198 is new because it tests the
specific tempting amplification of P-G197 and completely classifies its two-mode positive locus.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/RoutePPrimitiveBurnolWardModePolarizationNoGo.lean
```

Capstones:

- `xiWardCrossModeHerglotzPolarization_diag_eq_mode`;
- `det_xiWardCrossModeHerglotzPolarization_two`;
- `not_posSemidef_xiWardCrossModeHerglotzPolarization_two`;
- `xiWardCrossModeHerglotzPolarization_two_posSemidef_iff`.

Verification:

- `/tmp/pg198.lean`: `lake env lean /tmp/pg198.lean` passed cleanly;
- repository source check passed cleanly;
- exact leaf build passed; no umbrella/full build run;
- `/tmp/pg198_audit.lean`: capstones depend only on `propext`, `Classical.choice`, `Quot.sound`;
- forbidden-declaration scan clean;
- umbrella import wired without building umbrella.

## Gates

- [x] natural cross-mode polarization defined
- [x] agreement with every one-mode P-G197 diagonal proved
- [x] exact two-mode determinant computed
- [x] PSD locus classified in positive chamber
- [x] direct cross-mode amplification retired
- [x] identify common generator graph norm linking P-G197 resolved columns to P-G182 conormals
  (P-G199)
- [ ] prove coefficient-faithful primitive-source graph-norm contraction
- [ ] instantiate W-H184 and prove unconditional RH
