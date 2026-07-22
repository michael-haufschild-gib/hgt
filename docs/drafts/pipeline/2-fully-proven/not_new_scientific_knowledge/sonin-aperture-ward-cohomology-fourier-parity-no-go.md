# Sonin aperture Ward cohomology and Fourier-parity no-go

- **ID:** `sonin-aperture-ward-cohomology-fourier-parity-no-go`
- **Stage:** 2-fully-proven
- **Type:** THEOREM, `[FORMAL CLOSURE] [READER-CLASS NO-GO] [SUZUKI ANTI-LOOP]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH] [NOT A WHOLE-LANE NO-GO]`
- **Lean status:** every displayed mathematical assertion below is formalized without project
  axioms in `SoninApertureWardPotential.lean` and
  `SoninApertureFourierParityNoGo.lean`.

## Theorem

Let `Q_a` be exact even Sonin projection, `L_(a,b)=Q_a-Q_b`, and

```text
D_r=U_r+U_r^*,
Z_(a,b,c;r)=L_(a,b)D_rL_(b,c),
Kappa_(a,b,c;r)=Delta_(a,c;r)-Delta_(a,b;r)-Delta_(b,c;r).
```

For `0<o<a<b<c<r*o`, trace-class aperture curvature obeys operator Bianchi identity

```text
Kappa_(o,b,c)+Kappa_(o,a,b)
 =Kappa_(o,a,c)+Kappa_(a,b,c).                           (1)
```

Since

```text
Re Tr Kappa_(a,b,c)=-||Z_(a,b,c;r)||_HS^2,              (2)
```

its transition energies obey exact quadrilateral conservation

```text
||Z_(o,b,c)||_HS^2+||Z_(o,a,b)||_HS^2
 =||Z_(o,a,c)||_HS^2+||Z_(a,b,c)||_HS^2.                (3)
```

Define base-aperture Ward potential

```text
B_o(a,b)=||Z_(o,a,b;r)||_HS^2.                           (4)
```

Then scalar curvature is globally exact on every ordered aperture chamber:

```text
B_o(a,b)+B_o(b,c)-B_o(a,c)=||Z_(a,b,c;r)||_HS^2,
Re Tr Kappa_(a,b,c)+delta B_o(a,b,c)=0.                 (5)
```

Changing base `o` to `p` is only vertex gauge. With

```text
V_(o,p)(x)=||Z_(o,p,x;r)||_HS^2,
```

one has

```text
B_o(a,b)-B_p(a,b)=V_(o,p)(b)-V_(o,p)(a).                (6)
```

Thus no nonzero scalar cohomology class remains in aperture curvature.

Now let `J` be cosine Fourier involution. Exact carrier geometry gives

```text
JQ_a=Q_aJ,
JD_r=D_rJ,
JZ=ZJ,
J(Z+Z^*)=(Z+Z^*)J.                                     (7)
```

By contrast, forward-minus-inverse bilateral aperture holonomy

```text
H_(a,r)=U_r Q_a U_r^*-U_r^* Q_a U_r                   (8)
```

is Fourier-odd:

```text
J H_(a,r) J=-H_(a,r).                                   (9)
```

Let `Phi` be any complex-linear operator reader invariant under Fourier conjugation:

```text
Phi(JTJ)=Phi(T).                                        (10)
```

Then

```text
Phi(H_(a,r))=0.                                         (11)
```

Moreover the canonical Ward energy is

```text
||[Z+Z^*,L_(a,b)]||_HS^2=2||Z||_HS^2.                  (12)
```

Equations `(11)`--`(12)` give exact no-go equivalence

```text
Phi(H_(a,r))=||[Z+Z^*,L_(a,b)]||_HS^2
 iff Z=0
 iff Kappa_(a,b,c;r)=0.                                (13)
```

## Proof

Equation `(1)` is expansion of curvature as two-coboundary. Apply ordinary trace using the
Schatten-1 aperture theorem, take real parts, and substitute `(2)` to obtain `(3)`. Rearrangement
gives `(5)`. Applying `(3)` to quadruple `o<p<a<b` gives `(6)`.

The physical and Fourier cutoffs exchange under `J`, so their common kernel and orthogonal
complement are both invariant. Uniqueness of orthogonal projection gives `JQ_a=Q_aJ`. Fourier
reflection swaps `U_r` and `U_r^*`, proving `(7)` and `(9)`. From `(9)`--`(10)`, linearity gives
`Phi(H)=Phi(-H)=-Phi(H)`, hence `(11)` over `C`. Finally `(12)` is exact Ward transgression and
Hilbert--Schmidt faithfulness; combine it with `(11)` to obtain `(13)`.

## Suzuki verdict delivered by this theorem

This is class-complete for **Fourier-invariant complex-linear relative-trace readers**:

```text
invariant linear trace + bilateral holonomy -> identically zero orientation.
```

Therefore the proposed invariant relative finite-part identification between bilateral
Burnol/co-Poisson orientation and positive aperture Ward energy is impossible except on flat
triples. Aperture curvature can be cancelled, but that cancellation is gauge and contains no RH
orientation.

This does not prove RH, disprove RH, or kill every Suzuki construction. It leaves exactly a
fibre-pointed reader that is not invariant at one fixed fibre: Fourier reflection must exchange
the fibres `w` and `1-conj(w)`. Corpus example is co-Poisson Berezin diagonal. Its same-point sign
on annihilator characters remains RH-bearing open core.

## Lean correspondence

- `(1)`:
  `evenSoninApertureRestrictionCurvature_bianchi`;
- `(3)`:
  `hsNormSq_evenSoninApertureSuccessiveLayerTransition_bianchi`;
- `(5)`:
  `evenSoninApertureWardPotential_coboundary` and
  `re_opTrace_apertureCurvature_add_WardPotential_coboundary_eq_zero`;
- `(6)`:
  `evenSoninApertureWardPotential_base_change`;
- `(7)`:
  `evenFourierTransform_evenCentralSoninProjection`,
  `evenFourierTransform_evenDilationSum`, and the two aperture commutator theorems;
- `(9)`:
  `evenSoninBilateralApertureHolonomy_fourier_odd`;
- `(11)`:
  `reflectionInvariantLinearReader_evenSoninBilateralApertureHolonomy_eq_zero`;
- `(13)`:
  `reflectionInvariantLinearReader_holonomy_eq_apertureWardEnergy_iff_flat`.

## Gates

- [x] operator Bianchi identity
- [x] exact quadrilateral energy conservation
- [x] explicit Ward potential and curvature coboundary
- [x] exact base-gauge transformation
- [x] Fourier-evenness of symmetric aperture/Ward channel
- [x] Fourier-oddness of bilateral aperture holonomy
- [x] invariant-linear-reader annihilation
- [x] exact invariant-trace/Ward-energy flatness iff
- [x] formalize all claims in Lean
- [ ] construct or refute fibre-pointed co-Poisson source sign
- [ ] compose surviving source theorem to RH
