# HB: fixed original horizon branch and full compactified wave

- **Stage:** formalized in Lean 4.
- **RH:** unproved. Full forced joint continuation and physical left pairing remain open.
- **Result:** one frequency-independent C² regularity class, after removing the original horizon phase, selects the original Gauss branch throughout the nonreal strip reaching all fundamental Xi QNMs. The entire original metric wave has an exact compactified expression retaining its modular angular Laplacian.

## Exact result

For the original compact radial coordinate `b=sech(t)^2`, define
`OriginalHorizonC2 w U` to mean that `b^(-w/2) U(b)` has a genuine C² extension
across `b=0`, agreeing with the original expression on a positive-side germ.
The extension is used because totalized powers at zero do not supply the
correct limiting value.

`originalHorizonC2_modes_iff` proves, for any angular parameter and coefficients,
with `Im w≠0` and `Re w>-2`:

```text
OriginalHorizonC2(w, A*H(w)+B*H(-w))  iff  B=0.
```

Here H is the actual existing Gauss solution of the original BM radial
operator. This is an exact classification of the displayed two-branch family,
not yet a representation theorem for every local homogeneous solution.
`allXi_fundamental_original_horizon_domain` supplies this classification and
the actual original radial equation at both fundamental QNMs for every Xi copy,
without additional regularity, nonresonance, endpoint, or RH assumptions.

For an arbitrary full angular-dependent profile V with the stated actual
radial and angular differentiability, restore `U(t,z)=b(t)^(w/2)V(b(t),z)`.
`compactHorizonField_original_wave` proves

```text
fieldWave(w,U) = -b^(w/2)*b*P_w V,
P_w V = 4b(1-b)V_bb + [4(w+1)-(4w+6)b]V_b
        + Delta_H V - w(w+1)V.
```

Both radial derivatives and the angular Laplacian are actual derivatives of
V. No angular eigenfunction, spectral parameter replacement, or assigned jet
is used in this full-field identity. Its exact horizon trace is
`4(w+1)V_b(0)+Delta_H V(0)-w(w+1)V(0)`.

## Dependency-closed proof

1. Let a have `Re a<2`, `a≠0,1`. On the positive axis the actual second
   derivative of `b^a` is `a(a-1)b^(a-2)`. If a C² extension g existed, its
   second derivative would be continuous at zero. Since `Re(2-a)>0`, the
   product `g''(b)b^(2-a)` would tend to zero from the right. Equality of
   positive-side germs also identifies their actual derivative germs, so the
   same product is constantly `a(a-1)` near zero. Uniqueness of limits gives
   a contradiction. Dividing a proposed extension by a nonvanishing C²
   multiplier proves that such a multiplier cannot hide this failure.
2. Every actual Gauss factor is analytic on the unit disk, including at
   terminating parameters, by the previously proved radius lower bound.
   Its real restriction is C² at zero and its value there is exactly one.
   Algebra of positive-base complex powers gives
   `b^(-w/2)(A H(w,b)+B H(-w,b))=A F_w(b)+B b^(-w)F_(-w)(b)`.
   For nonreal w in `Re w>-2`, exponent `-w` satisfies step 1. If B is nonzero,
   subtract the admitted original factor and divide by B to obtain the
   forbidden extension. Conversely B=0 gives the actual Gauss extension.
3. The previously proved strict Xi strip and nonzero real spectral coordinate
   put both fundamental QNM frequencies in `Im w≠0`, `|Re w|<2`. Apply step 2
   with the actual Xi angular coordinate. Reuse the proved continued original
   Gauss radial equation to supply the equation component of the capstone.
4. The original coordinate has actual derivatives
   `b'=2*radialUnit*b` and `b''=2*b*(3*radialUnit²-1)`, with
   `radialUnit²=1-b`. Differentiate the original complex-power dressing and
   the full V twice, then compose through this coordinate. Local derivative
   equality identifies the second derivative of the actual restored field.
   The angular Laplacian commutes with the scalar radial dressing by its
   proved differentiated product rule. Substitution and exact algebra give
   the full displayed P_w. Evaluation at b=0 yields the stated trace law.

## Formal modules

- `HTGeometry.ComplexPowerC2Boundary`
- `RHTower.ThetaCuspHawkingBMOriginalHorizonDomain`
- `RHTower.ThetaCuspHawkingBMCompactHorizonWave`
- `RHTower.ThetaCuspHawkingBMFundamentalHorizonDomain`

## Validation

Four canonical leaves, 284 source lines, and 13 new public theorems passed
individual foreground `lake build <module>` audits. The isolated audit reused
4080 existing dependency oleans and produced exactly four new oleans. All four
installed sources and eight installed olean/ilean artifacts were byte-verified
against that audit. A scratch-only axiom audit of the 13 new public theorems
reported only `propext`, `Classical.choice`, and `Quot.sound`. No new leaf
reported a warning. Both umbrellas are wired without being built.

The corpus index was refreshed once. `python3 scripts/formal_tools.py lint
--check-generated` passed, with existing large-file warnings only. No full or
umbrella build, numerical experiment, or computational proof certificate was
used.

## Remaining operator construction

This fixes the radial branch criterion and proves the actual full differential
expression. It does not construct a closed joint Banach operator domain,
prove its Fredholm property, supply the full source-dependent inverse, or
identify that inverse with the original causal response. The modular cusp
condition, outer endpoint, and complete source must all be retained in that
construction. The existing complete source L²-meromorphic germ is available.
The scalar two-branch classification is not a replacement for those full
joint assertions.

A direct next step is the actual horizon Wronskian and source-dependent
boundary map for P_w, followed by a jointly controlled inverse with the
original modular cusp condition. The physical advanced/adjoint left-source
projection, spin-two/AIME identification, and independent Hawking-clock
extinction remain open. No numerical experiment or computational proof
certificate is used.
