# Calibrated fracture incidence has one kernel and one cokernel

- **ID:** `calibrated-fracture-incidence-kernel-cokernel`
- **Stage:** 3-formalized
- **Type:** FORMAL ALGEBRAIC BRIDGE / POINTED EFFECTIVITY / EXACT INCIDENCE FIBRE
- **Scientific status:** `[UNCONDITIONALLY LEAN-FORMALIZED] [PARENT HOMOLOGICAL ALGEBRA]`
  `[ARCHITECTURAL CONSEQUENCE FOR HT] [NOT AN RH RESULT]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/FacetRestrictionEmbedding.lean`
- **Parents:**
  - `distributive-coordinate-facet-effectivity.md`
  - `relative-boundary-effectivity-conservativity.md`
- **Successor:** `polarized-fracture-incidence-trichotomy.md`
- **Statement:** After a finite fracture packet has a common representative, a prescribed source
  calibration has an exact obstruction in the cokernel of the residual-gauge calibration and an
  exact ambiguity in its kernel.  Existence and noncanonicity are therefore the two cohomological
  sides of one calibration map.

## Setup

Let `J_i<=M` be quotient channels indexed by a finite set `s`, and put

```text
K_s=intersection_(i in s) J_i.                            (1)
```

Suppose `a in M` represents a compatible observation packet `x_i in M/J_i`.  Every other common
representative is of the form `a+k` with `k in K_s`.  Let

```text
c:M->N
```

be a linear source calibration and let `n in N` be the prescribed calibrated value.

## Exact defect and ambiguity `[PROVED + LEAN]`

Define

```text
omega_c(x,n)=[n-c(a)] in N/c(K_s).                        (2)
```

Lean proves that `(2)` is independent of the chosen common representative `a`.  It then proves

```text
there exists b representing every x_i with c(b)=n
  iff omega_c(x,n)=0.                                     (3)
```

If calibrated representatives exist, any two differ by

```text
K_s intersection ker(c).                                 (4)
```

Thus the pointed incidence fibre has the complete linear profile

```text
existence obstruction = coker(c restricted to K_s),
residual automorphism = ker(c restricted to K_s).         (5)
```

Equivalently, `(5)` is the cohomology of the two-term calibration complex

```text
K_s --c--> N.                                             (6)
```

## Exact positive reconstruction theorem `[PROVED + LEAN]`

Assume the channel family is distributive, so pairwise compatibility produces an ambient common
representative.  If

```text
c(K_s)=N,
K_s intersection ker(c)=0,                               (7)
```

then every pairwise-compatible packet and every prescribed calibration value have exactly one
common representative.

This supplies the positive theorem paired with two no-gos:

```text
[NO-GO] compatible local data automatically realize an arbitrary source pointing;
[POSITIVE] the exact obstruction is omega_c in the cokernel in (2).

[NO-GO] adding a calibration automatically makes the lift canonical;
[POSITIVE] the exact residual ambiguity is the kernel in (4).
```

Surjectivity and separation are independent requirements.  A proof that checks only uniqueness
does not construct an effective point; a proof that checks only existence does not make the source
canonical.

## Relation to existing formal results

`DifferenceDifferential.lean` already proves that complete difference boundaries leave precisely
the joint-fixed gauge and that a calibration is injective exactly when it separates this gauge.
The present theorem adds the missing existence half for an arbitrary finite fracture packet:
prescribed pointing is possible exactly when the new cokernel class `(2)` vanishes.

`ClockDescentAnomaly.lean` already identifies a nonempty integration fibre as a kernel torsor.  The
present theorem identifies the obstruction before nonemptiness and couples that torsor to finite
local quotient observations.

## HT and RH boundary

The kernel--cokernel theorem is parent linear algebra, not new science.  Its HT consequence is
architectural: the linearized source-effectivity object is not merely a Cech obstruction group.
It is the two-term incidence complex `(6)`, whose cokernel detects failure of effectivity and whose
kernel detects boundary-condition ambiguity.

`[CONJECTURE; NOT AN RH RESULT]` Different RH proof chains may map the same source-calibration
complex to Hermitian, spectral, bornological, or integral targets.  This becomes content only after
the source constructs the common complex and the realization maps without using the Xi divisor.

## Lean declarations

- `calibratedFractureDefect`
- `calibratedFractureDefect_eq_of_commonRepresentatives`
- `exists_calibratedFamilyRepresentative_iff_defect_eq_zero`
- `calibratedFamilyRepresentative_sub_mem_inf_inf_ker`
- `calibratedFamilyRepresentative_eq_of_inf_inf_ker_eq_bot`
- `existsUnique_calibratedFamilyRepresentative`

## Verification

- The module's cached object file already existed, so no build was run.
- The touched source passed direct `lake env lean` verification against cached imports.
- No `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration was introduced.

## Gates

- [x] common-representative torsor identified
- [x] calibration defect quotient defined
- [x] independence from base representative proved
- [x] calibrated existence iff defect vanishing proved
- [x] residual calibrated ambiguity computed
- [x] unique pointed reconstruction under surjectivity and separation proved
- [x] every no-go paired with an exact positive receiver
- [x] theorem demoted to parent algebra rather than advertised as new science
