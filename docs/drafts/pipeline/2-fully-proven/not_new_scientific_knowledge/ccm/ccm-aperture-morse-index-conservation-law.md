# The CCM aperture Morse charge is monotone and RH is its conservation law

- **ID:** `ccm-aperture-morse-index-conservation-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** the Weil criterion, Yoshida's localization theorem, and Suzuki's continuity
  and compact generalized-eigenvalue formulations
- **Statement:** The negative Morse index of the exact restricted Weil form is a finite,
  nondecreasing integer under aperture enlargement. It starts at zero, and RH is exactly the law
  that this aperture charge remains zero. In the derivative variable, the equivalent kernel is
  that of the screw operator extended to Suzuki's completed space, not automatically the raw
  compact operator on `L2_0`.

> **2026-07-22 domain correction.** The original version silently replaced Suzuki's completed
> derivative space `H(S_(a,mu))` by `L2_0(-a,a)`. Suzuki explicitly states that the former is not
> contained in the latter. All raw-`L2` equivalences below are corrected accordingly; see
> `suzuki-completed-zero-mode-corona-seam-law.md` for the exact intersection theorem.

## Exact aperture charge

For `a>0`, let `QW_a` be the closed Weil form on `L2(-a,a)` and define

```text
kappa(a)
 =sup{dim V:
      V subset D(QW_a) is a linear subspace and
      QW_a(v,v)<0 for every 0!=v in V}.                       (1)
```

Suzuki's associated self-adjoint operator `A_a` has discrete spectrum, is bounded below, and has
only `+infinity` as an accumulation point. Hence

```text
kappa(a)=Tr 1_(-infinity,0)(A_a)<infinity.                    (2)
```

This is the exact finite-aperture Morse charge, not a finite-prime approximation to an unknown
global operator.

## Monotone quantization theorem

`[PROVED]` If `0<a<=b`, then

```text
kappa(a)<=kappa(b).                                           (3)
```

### Proof

Zero extension gives an isometric linear inclusion

```text
E_(a,b):D(QW_a)->D(QW_b)                                      (4)
```

and preserves the global Weil pairing:

```text
QW_b(E_(a,b)v,E_(a,b)w)=QW_a(v,w).                            (5)
```

Therefore the image of every negative-definite subspace for `QW_a` is a negative-definite
subspace of the same dimension for `QW_b`. Taking the supremum proves `(3)`.

Since Suzuki--Yoshida prove that the lowest restricted eigenvalue is positive for all sufficiently
small `a`, one has

```text
kappa(a)=0 for all sufficiently small a.                      (6)
```

Thus `kappa` is an integer-valued one-way aperture charge: once it becomes nonzero it can never be
repaired by going to larger aperture.

## Conservation theorem

The following are equivalent:

```text
(i)   RH;
(ii)  kappa(a)=0 for every a>0;
(iii) QW_a>=0 for every a>0;
(iv)  QW_a is nondegenerate for every a>0;
(v)   ker(Gtilde_a)=0 on H(S_(a,mu)) for every a>0.             (7)
```

Here `mu<inf spec(A_a)` and `Gtilde_a` is Suzuki's bounded extension of the raw compact
continuous-kernel screw operator to `H(S_(a,mu))`.

### Proof

The equivalence `(i)<->(iii)` is the localized Weil criterion. Equations `(1)`--`(2)` give
`(ii)<->(iii)`. Suzuki records Yoshida's nondegeneracy criterion `(i)<->(iv)`. Finally, for
`v in H01(-a,a)` and `u=Dv in L2_0(-a,a)`, Suzuki proves

```text
QW_a(v,v)=<G_a u,u>.                                         (8)
```

His generalized eigenvalue formulation identifies a zero eigenvalue of the restricted Weil
operator with a nonzero kernel vector of `Gtilde_a` on the completed derivative space, giving
`(iv)<->(v)`.

For the canonical injection `j_a:L2_0->H(S_(a,mu))`, one only has

```text
j_a(ker G_a)=ker(Gtilde_a) intersect j_a(L2_0).             (7a)
```

Thus RH implies raw screw injectivity at every aperture, but the converse additionally requires
the regularity statement `ker(Gtilde_a) subset j_a(L2_0)` or a direct exclusion of the completion
corona.

There is also a direct first-crossing proof of the nontrivial direction. Let `lambda_0(a)` be the
lowest eigenvalue. It is positive for small `a` and continuous in `a`. If RH is false, localized
Weil positivity fails, so `lambda_0(b)<0` for some `b`. Continuity forces an aperture `a_*<b` with

```text
lambda_0(a_*)=0,                                             (9)
```

which is precisely a nonzero vector in `ker(Gtilde_(a_*))` on the Suzuki completion. Hence
excluding a completed finite-aperture zero mode for every `a` prevents the first negative spectral
birth and proves RH. Excluding only raw `L2` screw null vectors does not address a possible corona
mode.

## Positive CCM reformulation

The exact global CCM route is therefore

```text
weighted all-prime incidence + archimedean completion
  -> ker(Gtilde_a)=0 on H(S_(a,mu)) for every finite aperture a
  -> kappa(a)=0 is conserved
  -> QW_a>=0 for every a
  -> RH.                                                     (10)
```

This is stronger operationally than asking an error term to vanish. The carrier is the integer
`kappa(a)`, and the load-bearing theorem is injectivity of the completed extension of a
source-defined continuous-kernel operator. The raw integral operator is compact on `L2`; its
extension acts on the larger Suzuki space. The logarithmic boundary layer cannot blur the Morse
charge: a negative eigenvalue of arbitrarily small magnitude still changes `kappa` by an integer
and then persists at all larger apertures.

The same theorem also says exactly what a cofinal finite-prime implementation must transport. It
must preserve the inertia of the **true** restricted form, or equivalently prove that the Fredholm
kernel never acquires a zero mode. Real zeros of an auxiliary determinant, fixed-depth prolate
Rayleigh bounds, or a scalar lower error do not compute this charge unless they exhaust the full
kernel.

## Relation to the existing index corpus

`seam-spectral-flow-index.md` formalizes the abstract statement that definiteness is negative-index
zero and is invariant under congruence. The present theorem supplies the missing exact CCM
specialization:

```text
seam negative index          <-> abstract divisor charge,
kappa(a)                          <-> finite-aperture analytic charge,
ker(Gtilde_a)=0 for every a       <-> charge conservation through the aperture filtration. (11)
```

`euler-pick-inertia-offline-zero-count.md` supplies a second exact realization of the transverse
charge in the Euler-convergent region. A genuinely source-native CCM proof may therefore seek an
index-preserving incidence transform between the Euler Pick system and `G_a`; merely observing that
both indices vanish iff RH is not such a transform.

`[PROVED SUBSEQUENT TRANSPORT]` The global screw kernel supplies that index transport after cofinal
exhaustion. Its Krein--Langer negative index is exactly the total right-half off-line zero
multiplicity, while continuous-kernel exhaustion identifies that index with `sup_a kappa(a)`.
The shifted-Xi inner denominator has the same cofinal model-space dimension. Thus

```text
sup_a kappa(a)
 =right-half off-line zero multiplicity
 =sup_(omega>0)dim K(B_omega).
```

The proof is in `ccm-aperture-morse-hardymodel-index-exhaustion-law.md`.

## Scientific status

The ingredients are classical min--max monotonicity, Yoshida's localized Weil criterion, and
Suzuki's continuity and generalized eigenvalue theorems. The quantized-conservation formulation is
the correct route interface but does not clear the novelty gate.

## References

- M. Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096, Theorems 1.1 and
  1.3 and Section 8.
- H. Yoshida, localized nondegeneracy criterion for Weil's quadratic form, as cited by Suzuki.

## Lean status

**Superseded, 2026-08-03.**  Formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/CCMApertureMorseCharge.lean`.  `RHTower/SeamSpectralFlow.lean` is
matrix-level Krein nonnegativity and does **not** overlap: nothing is duplicated.

The previous decision listed "zero extension of the closed Weil forms" as missing analytic content.
That is a representation artefact: taking the aperture domains as *submodules of one fixed space*
makes `(4)`--`(5)` literal inclusion `D a ≤ D b`, with no isometry to construct and no form-preservation
to check.

- `HasNegDefSubspaceOfDim`, `morseCharge` — definition `(1)`, the achievable negative dimensions and
  their supremum.
- **`HasNegDefSubspaceOfDim.mono`** and **`morseCharge_mono`** — equations `(3)`--`(5)`: every
  negative-definite subspace of a smaller aperture is one of the larger aperture, of the same
  dimension, so the charge is monotone.  The set-level statement carries no hypotheses at all; the
  `sSup` version needs only `BddAbove`, which is what `(2)` supplies analytically.
- **`hasNegDefSubspaceOfDim_one`** and **`negDefDims_eq_zero_iff_nonneg`** — equations
  `(ii) ↔ (iii)`: the charge vanishes exactly when the form is nonnegative.  The nontrivial direction
  builds an explicit one-dimensional negative subspace from a single negative vector; homogeneity of
  the form is the only structure used.
- **`morseCharge_eq_zero_of_nonneg`** — equation `(6)`, the small-aperture anchor.
- **`exists_crossing_of_pos_of_neg`** — equation `(9)`, the first-crossing step: a continuous
  aperture-indexed bottom eigenvalue positive at a small aperture and negative at a larger one
  vanishes in between.  This is the intermediate value theorem, and it is what identifies the first
  negative spectral birth with a zero mode.

All statements are unconditional: `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]`.

Not formalized, and genuinely external: the discreteness/boundedness-below of `spec(A_a)` giving
finiteness `(2)`; Yoshida's localized Weil criterion `(i) ↔ (iii)` and nondegeneracy criterion
`(i) ↔ (iv)`; Suzuki's identity `(8)` and the completed-space generalized eigenvalue equivalence
`(iv) ↔ (v)` together with the corona statement `(7a)`; and continuity of `lambda_0` in the aperture,
which is the hypothesis `exists_crossing_of_pos_of_neg` consumes.

## Gates

- [x] exact finite aperture charge defined
- [x] finiteness proved from compact resolvent
- [x] aperture monotonicity proved
- [x] small-aperture anchor recorded
- [x] RH, charge conservation, nondegeneracy, and completed screw injectivity identified
- [x] first-zero-mode crossing isolated
- [x] cofinal aperture charge identified with the full Hardy off-line model-space index
- [x] raw-`L2`/completed-space mismatch corrected
- [x] Lean: charge definition and monotonicity `(3)`--`(5)` unconditional
- [x] Lean: charge vanishing identified with form nonnegativity `(ii)` ↔ `(iii)`
- [x] Lean: small-aperture anchor `(6)` and first-crossing zero mode `(9)` unconditional
- [ ] construct a source-defined proof of `ker(Gtilde_a)=0` for every `a`
