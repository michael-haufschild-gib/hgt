# The CCM Evans Gram requires a determinant-line lift to carry Morse charge

> **2026-07-22 domain correction.** This card concerns the raw `L2` screw Evans complex. Its
> determinant-line lift does not detect completion-corona zero modes without an additional
> regularity theorem. The square eigenfunction-variable Evans line is completion-safe; see
> `suzuki-completed-zero-mode-corona-seam-law.md`.

- **ID:** `ccm-evans-gram-requires-determinant-line-lift`
- **Stage:** 3-formalized (paper proof; Lean certificate alongside)
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

## Lean status

**Formalized unconditionally, 2026-08-15**, in
`formal/GaloisForLFunctions/RHTower/CCMEvansDeterminantLine.lean`, on new reusable infrastructure
`formal/GaloisForLFunctions/HTGeometry/ComplexGramPlucker.lean`.  The earlier decision ("the
analytic Fredholm complex and the comparison `(5)` are absent from Lean, so no wrapper is added")
measured the wrong thing: `(3)`, `(4)` and the whole obstruction are finite linear algebra over `ℂ`,
and none of them needs the analytic complex.

- `hermFeatureMinor`, `hermFeatureWedge`, `hermFeatureGram`, `hermPluckerNormSq`, `finiteHermDual`,
  `hermFeatureWedgeDual` — the maximal coordinate minors, the top exterior power, the Hermitian Gram
  matrix, and the exterior dual pairing.
- **`det_hermFeatureGram_eq_pluckerNormSq`** — equation `(3)`: complex Cauchy–Binet, absent from
  mathlib.  The Gram determinant equals `∑_s |minor_s|²`, that is, the squared norm of the top
  exterior power in the induced coordinate basis of the exterior power.  The proof pairs the
  exterior dual wedge of the Hermitian row functionals against the feature wedge, expands in the
  exterior basis, and uses that the dual wedge reads each basis vector as the conjugate of the
  matching minor.
- **`det_hermFeatureGram_ne_zero_iff`**, **`hermFeatureWedge_eq_zero_iff`**,
  **`det_evansGram_ne_zero_iff`**, **`evansPlucker_eq_zero_iff`** — equation `(4)`: the Pluecker
  vector vanishes exactly when the presentation has a kernel, and so does the Gram determinant.  The
  Gram half is proved directly from the Hermitian energy identity
  `∑_i conj(c_i)(G c)_i = ∑_k |∑_j c_j v_j(k)|²`, so no exterior-power independence lemma is needed.
- `det_evansGram_eq_nonneg_real`, `hermPluckerNormSq_nonneg` — the Gram determinant is a nonnegative
  real.
- **`finrank_exteriorPower_evansExcessTarget`**, **`one_lt_finrank_exteriorPower_evansExcessTarget`**,
  **`not_nonempty_linearEquiv_exteriorPower_evansExcessTarget`** — the obstruction of the paragraph
  after `(4)`: `dim ⋀^{d} Y = binomial(d+3, d) > 1` at every positive `d`, so `⋀^{d} Y` is not a
  line and admits no linear isomorphism with the scalars.  `P_a` is therefore not a section of a
  determinant line.
- **`evansPlucker_update_neg`**, **`hermPluckerNormSq_update_neg`**, **`det_evansGram_update_neg`** —
  "squaring its norm removes crossing orientation", as a theorem: reversing the sign of one source
  vector reverses the Pluecker vector and leaves the Gram determinant unchanged.
- **`exists_scalar_extraction_disagreement`** — "changing a basis of the complement changes any
  scalar extracted from `P_a`", in its sharpest form: at every kernel-free presentation there are two
  scalar extractions of `P_a`, one nonzero and one vanishing.  A scalar read off the rectangular
  Pluecker vector therefore does not detect the kernel, while the Gram determinant does.

All statements are unconditional: `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]`.

Not formalized, and imported rather than proved here: the exact finite Evans reduction identifying
`ker M_a` with `ker G_a`, which is the content of `ccm-rational-residual-finite-evans-matrix-law.md`;
and the analytic Fredholm determinant line with its crossing form, which is the missing carrier the
card names.
