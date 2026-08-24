# The scaled Gamma Borel-residue character detects every multiplication cancellation

- **ID:** `scaled-gamma-borel-residue-character-completeness`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / GENERAL HYPERTRANSCENDENCE LANDSCAPE
- **Scientific status:** `[PROVED] [BRIDGE]`
- **Statement:** For an arbitrary finite signed product of positive-scale affine Gamma factors, the
  polar Borel residues of its formal second logarithmic derivative define a scaled residue character.
  This character vanishes identically exactly when every rational commensurability class cancels by
  Gauss multiplication and Gamma recurrence, equivalently when the product is
  exponential--rational. Every nontrivial reduced product is therefore forced to carry a nonzero
  scaled Borel-residue character even when no common shift exists.

## 1. Signed products and their Borel polar part

Let

```text
G(s)=exp(alpha s) product_(j=1)^d Gamma(lambda_j s+mu_j)^m_j,
lambda_j>0,  m_j in Z\{0},                                 (1)
```

and put

```text
Psi=G'/G,
Tau=Psi'=sum_j m_j lambda_j^2 psi'(lambda_j s+mu_j).       (2)
```

The formal trigamma expansion is

```text
hat psi'(z)=1/z+1/(2z^2)+sum_(n>=1) B_(2n) z^(-2n-1).      (3)
```

Use the formal Borel transform normalized by

```text
B(s^(-n-1))=xi^n/n!.                                      (4)
```

Since

```text
sum_(n>=1) B_(2n) xi^(2n)/(2n)!
 =xi/(exp xi-1)-1+xi/2,                                   (5)
```

scaling by `lambda_j` and translating by `mu_j/lambda_j` give, modulo an entire function of `xi`,

```text
B hat Tau(xi)
 ==sum_j m_j exp(-(mu_j/lambda_j)xi)
       xi/(exp(xi/lambda_j)-1).                            (6)
```

Only the displayed terms contribute finite Borel singularities.

## 2. Explicit scaled residue character

At

```text
xi=2 pi i k lambda_j,  k in Z\{0},                         (7)
```

the `j`th summand in `(6)` has residue

```text
2 pi i k m_j lambda_j^2 exp(-2 pi i k mu_j).              (8)
```

For real `t!=0`, define

```text
R_G(t)=sum_(j: t/lambda_j in Z\{0})
          m_j lambda_j exp(-2 pi i (t/lambda_j)mu_j),      (9)
```

with the empty sum equal to zero. Then

```text
Res_(xi=2 pi i t) B hat Tau(xi)=2 pi i t R_G(t).           (10)
```

The finitely supported-on-lattices function `R_G` is the **scaled Gamma Borel-residue character**.
It is intrinsic to `Tau`: multiplying `G` by a nonzero exponential or rational function changes the
Borel transform only by an entire function and leaves `(9)` unchanged.

## 3. Separation by rational commensurability class

Partition the indices by

```text
j~k iff lambda_j/lambda_k in Q_(>0).                       (11)
```

If two indices lie in different classes, their nonzero singular lattices are disjoint:

```text
lambda_j Z\{0} intersection lambda_k Z\{0}=empty.          (12)
```

Indeed a common nonzero point would make `lambda_j/lambda_k` rational. Hence residues from different
commensurability classes never cancel. The character `(9)` is the disjoint union of the characters
of the individual classes.

## 4. One class is the Fourier transform of orbit charge

Fix one class. Choose `H>0` such that

```text
n_j=H lambda_j in N_(>0)                                  (13)
```

for every factor in the class. Gauss multiplication and Gamma recurrence give the common-scale
normal form

```text
G_class(s)=C exp(beta s) R(s)
  product_(c=1)^q Gamma((s+b_c)/H)^M_c,                    (14)
```

where `R in C(s)^x`, the `b_c` are distinct modulo `H Z`, and the nonzero integers `M_c` are the
shift-orbit charges.

The operations leading to `(14)` multiply by exponential--rational functions and therefore preserve
the Borel polar residues. For `t=r/H`, `r in Z\{0}`, formula `(9)` becomes

```text
R_G(r/H)=1/H sum_(c=1)^q M_c exp(-2 pi i r b_c/H).         (15)
```

Thus the restriction of `R_G` to the common singular lattice is the nonconstant Fourier transform
of the finite atomic orbit-charge measure

```text
nu=sum_c M_c delta_(b_c/H mod Z).                          (16)
```

## 5. Completeness theorem

`[PROVED]`

```text
R_G(t)=0 for every t!=0
  iff every orbit charge in every commensurability class vanishes
  iff G(s)=C exp(beta s) R(s),  R in C(s)^x.               (17)
```

### Proof

If every orbit charge vanishes, `(14)` is exponential--rational in each class, so `Tau` is rational
and its Borel transform has no finite singularity. Hence `R_G=0`.

Conversely, suppose `R_G=0`. Section 3 reduces the question to one commensurability class. Put

```text
zeta_c=exp(-2 pi i b_c/H).                                 (18)
```

The `zeta_c` are pairwise distinct. Equation `(15)` gives

```text
sum_c M_c zeta_c^r=0,  r=1,...,q.                          (19)
```

The matrix `(zeta_c^r)_(1<=r,c<=q)` is a Vandermonde matrix multiplied by the invertible diagonal
`diag(zeta_c)`. It is invertible. Therefore every `M_c=0`. Applying this to every class proves
`(17)`.

## 6. Positive law

The theorem does not merely say that a reduction fails. It identifies what every unreduced product
must possess:

> **Scaled alien-charge law.** Every finite signed affine Gamma product is uniquely separated into
> an exponential--rational part and a nonzero scaled Borel-residue character supported on disjoint
> rational commensurability classes. The character is the Fourier transform of the canonical
> shift-orbit charge in each class.

This is the orbit-free continuation of the discrete-residue law. A common shift is a proof device
inside one class, not part of the invariant itself.

## 7. How the charge selects the HT carrier

`R_G!=0` proves that the formal trigamma tail is nonzero and resurgently charged. It does not by
itself prove hypertranscendence, because differentially algebraic resurgent series can also possess
Borel poles.

The proved arbitrary-scale classification in
`../needs-audit/incommensurable-gamma-orbit-free-quasianalyticity.md` supplies the independent
dichotomy: the product of the finitely many matching shift differences sends `hat Tau` to `C(s)`,
so finite-shift peeling forces `hat Tau` to be rational or HT. The present character then selects
the branch exactly: `R_G!=0` excludes rationality and therefore forces HT. Thus the positive roles
are separate and complete: this card detects the intrinsic charge; the peeling theorem identifies
the two possible carriers.

## 8. Parent and novelty audit

`[BRIDGE]`

- Formula `(5)` is the classical Bernoulli generating function.
- Scaling and translation in the formal Borel plane are classical.
- Gauss multiplication and Gamma recurrence give `(14)`.
- Fourier/Vandermonde uniqueness for a finite atomic measure proves completeness.

Preliminary exact searches did not locate the character `(9)` or equivalence `(17)` in this form,
but the proof is a short synthesis of these parent mechanisms. It is classified as a proved bridge,
not new scientific knowledge.

## 9. Lean status

On 2026-08-23, the complete theorem was formalized in
`formal/GaloisForLFunctions/HTGeometry/ScaledGammaExponentialRational.lean`, on top of the exact
Borel-residue and canonical-orbit infrastructure in
`ScaledGammaBorelResidue.lean` and `ScaledGammaNaturalOrbitCompleteness.lean`.

The formalization constructs the genuine global meromorphic product, its exponential--rational
subgroup, exact Gauss/recurrence gauges for every rational-commensurability class, and a canonical
residual affine-Gamma divisor family. It proves native divisor rigidity: distinct canonical pole
progressions intersect only finitely, while any surviving multiplicity supplies infinitely many
isolated Gamma poles that cannot occur in a rational function times an exponential.

`scaledGammaAlienChargeZero_iff_exponentialRationalMero` is the unconditional equivalence `(17)`.
`scaledGammaBorelResidueCharacter_exponentialRational_capstone` combines the exact residue limit
`(10)`, character vanishing, canonical orbit-charge cancellation, and literal
exponential--rationality in one closed theorem. The module is wired into
`GaloisForLFunctions.HTGeometry`.

Exact source check and targeted module build pass. Axiom audits of the affine divisor rigidity,
canonical collision theorem, exact equivalence, and final capstone report only `propext`,
`Classical.choice`, and `Quot.sound`.

## Gates

- [x] Borel polar part computed
- [x] scaled residue character defined explicitly
- [x] commensurability classes separated
- [x] character identified with orbit-charge Fourier transform
- [x] vanishing classification proved
- [x] positive carrier law stated
- [x] HT overclaim explicitly excluded
- [x] parent-theory gate applied; classified BRIDGE
- [x] complete unconditional Lean formalization
