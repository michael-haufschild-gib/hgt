# The CCM Evans Gram requires a determinant-line lift to carry Morse charge

- **ID:** `ccm-evans-gram-requires-determinant-line-lift`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** exterior algebra, Fredholm determinant lines, spectral flow, and
  `ccm-rational-residual-finite-evans-matrix-law.md`

## Statement

On any aperture stratum where the real-characteristic multiplicity `d_a` is constant, let

```text
M_a:F_a->Y_a:=R_(L_a) direct_sum C^3,
dim F_a=d_a,
dim Y_a=d_a+3.                                             (1)
```

The top exterior power

```text
P_a=wedge^(d_a)M_a
 in det(F_a)^* tensor wedge^(d_a)Y_a                       (2)
```

is a Pluecker vector, and

```text
||P_a||^2=det(M_a^*M_a),                                  (3)
P_a=0 iff ker M_a!=0 iff ker G_a!=0.                       (4)
```

However, `P_a` is not a scalar determinant-line section: `wedge^(d_a)Y_a` has dimension
`binomial(d_a+3,d_a)>1`. Consequently `(2)` has no canonical sign or phase, and the Gram determinant
in `(3)` forgets the orientation of a kernel crossing.

Therefore pointwise kernel equivalence does not yet transport the aperture Morse charge. A
successful quantized CCM construction must additionally supply a source-defined identification

```text
finite Evans presentation
  -> intrinsic Fredholm determinant line of the restricted Weil family,       (5)
```

compatible with the self-adjoint crossing form. Only after `(5)` is constructed do oriented zeros
compute spectral flow and the change of

```text
kappa(a)=Tr 1_(-infinity,0)(A_a).                         (6)
```

## Proof

For a linear map from a `d`-dimensional Hermitian space into a Hermitian space, the squared norm of
its top exterior power is the Gram determinant of the images of any orthonormal basis. This proves
`(3)`. The exterior power vanishes exactly when those images are linearly dependent, and the exact
finite Evans reduction identifies that kernel with `ker G_a`, proving `(4)`.

Since the target in `(1)` has dimension `d_a+3`, its `d_a`-th exterior power is not a line. Changing
the three-dimensional complement to `range M_a`, or changing a basis of that complement, changes
any scalar extracted from `P_a`. Squaring its norm removes those choices but also removes crossing
orientation. Thus neither `P_a` nor `det(M_a^*M_a)` canonically determines the spectral-flow sign.

For a continuous self-adjoint Fredholm family, the intrinsic determinant line and its crossing-form
orientation do carry spectral flow. Hence an isomorphism `(5)` compatible with the kernel and
cokernel orientations is precisely the additional datum required to transfer the integer charge.
`QED`

## Positive CCM carrier law

The exact direct route has three distinct obligations:

```text
kernel obligation:
  det(M_a^*M_a)>0 at every aperture,

presentation obligation:
  identify the rectangular Evans complex with the intrinsic Fredholm complex,

quantized transport obligation:
  orient the resulting determinant line from the exact prime--Gamma source
  and prove zero spectral flow from the small-aperture chamber.                (7)
```

A sequence of nonnegative Gram determinants, finite spectral agreements, or normalized scalar
determinants does not compute the aperture charge unless it also supplies the determinant-line
identification and crossing orientation in `(7)`.

The required positive object is therefore not an arbitrary sign assigned to a finite matrix. It is
a canonical prime--Gamma trivialization of the Fredholm determinant line, compatible with aperture
enlargement, the logarithmic Dirichlet reconstruction, the rational residual, and the three anchor
channels.

Those three channels are canonically graded, not anonymous. Reflection splits the exact map into an
even block with mean and constant-affine channels and an odd block with the slope channel. This is
proved in `ccm-parity-split-evans-gram-law.md` and supplies a natural source-compatible candidate
for the stabilization in a determinant-line comparison. It does not by itself identify those three
target lines with the actual cokernel.

Suzuki's deficiency-index line does not close this comparison at zero shift. It is constructed from
`A_a-lambda I>0` with `lambda<inf spec A_a`; choosing `lambda=0` for every aperture is already RH,
and even a cofinal choice `lambda(a)->0` below the floor proves RH by no evacuation. Therefore the
required lift must be an unshifted indefinite/Fredholm construction, not the positive shifted line.
This is proved in `ccm-suzuki-deficiency-line-zero-shift-floor-equivalence.md`.

Nor can one insert a spectral parameter into the existing screw-variable `L2` Evans matrix without
additional work. Suzuki's generalized derivative problem lives on `H(S_(a,mu))`, which is
explicitly not a subspace of `L2`; the two forced repairs are proved in
`ccm-spectral-parameter-evans-completion-carrier-law.md`.

`[PROVED SUBSEQUENT ESCAPE]` The actual restricted-Weil eigenfunction remains in `L2(-a,a)` and
obeys the supported multiplier equation directly. Factoring `W_a-lambda` in that variable removes
the mean and affine channels and produces a square map

```text
N_(a,lambda):F_(a,lambda)->R_(a,lambda).
```

Its determinant is already a section of a genuine determinant line and its kernel is exactly
`ker(A_a-lambda I)`. Thus the rectangular comparison `(5)` is not compulsory for the direct
restricted-Weil route. The remaining obligation is to trivialize the square determinant line
across characteristic-stratum changes and prove nonvanishing for `lambda<=0`. This is proved in
`ccm-restricted-weil-square-evans-determinant-law.md`.

## Scope and classification

Equations `(3)`--`(4)` and the determinant-line/spectral-flow correspondence are standard. The
application identifies a missing carrier but is not new scientific knowledge. The finite inertia
and congruence layer is already formalized in `RHTower/SeamSpectralFlow.lean`; the analytic Fredholm
complex and the comparison `(5)` are absent from Lean, so no wrapper is added.

## Gates

- [x] Evans Gram determinant identified as a squared Pluecker norm
- [x] kernel zero set identified exactly
- [x] false scalar orientation of the rectangular Evans map excluded
- [x] determinant-line comparison isolated as the required quantized carrier
- [x] three excess target channels canonically graded as two even plus one odd
- [x] positive shifted Suzuki determinant-line shortcut proved RH-equivalent at zero shift
- [x] spectral-parameter Evans shortcut reduced to a completed-domain carrier alternative
- [x] eigenfunction-variable square Evans determinant constructed
- [ ] construct the finite Evans-to-Fredholm complex quasi-isomorphism
- [ ] transport the prime--Gamma source orientation through that quasi-isomorphism
- [ ] prove zero spectral flow through all apertures
- [ ] RH
