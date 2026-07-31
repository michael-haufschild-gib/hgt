# Meromorphic pole-jet finite certificate law

- **ID:** meromorphic-pole-jet-finite-certificate-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) · STRUCTURAL BRIDGE
- **Status:** `[PROVED HERE] [LEAN-VERIFIED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Differential transcendence of a meromorphic function is equivalent to the
  existence, at every finite ADE complexity, of one nonzero finite determinant made from Laurent
  coefficients of its differential monomials at any chosen pole.

## Setup

Let \(f\) be meromorphic on a connected domain \(U\subseteq\mathbb C\), and fix a pole
\(a\in U\).  For integers \(r,D,E\geq0\), define the finite column set
\[
 \mathcal C_{r,D,E}
 =\{(q,\alpha):0\leq q\leq E,\ 
 \alpha=(\alpha_0,\ldots,\alpha_r)\in\mathbb N^{r+1},\ |\alpha|\leq D\}.
\]
The column function indexed by \((q,\alpha)\) is
\[
 F_{q,\alpha}(z)=z^q\prod_{j=0}^{r}\bigl(f^{(j)}(z)\bigr)^{\alpha_j}.
\]
For every Laurent index \(\ell\in\mathbb Z\), put
\[
 M_{r,D,E}(\ell,(q,\alpha))
 =[t^\ell]F_{q,\alpha}(a+t).
\]

## Theorem — finite pole-jet certificate

The following are equivalent.

1. \(f\) is hypertranscendental over \(\mathbb C(z)\).
2. For every \(r,D,E\), the columns of the infinite Laurent matrix \(M_{r,D,E}\) are linearly
   independent over \(\mathbb C\).
3. For every \(r,D,E\), there are
   \(N=|\mathcal C_{r,D,E}|\) Laurent indices
   \(\ell_1,\ldots,\ell_N\) such that
   \[
   \boxed{
   \det\left(M_{r,D,E}(\ell_i,c)\right)_{
      1\leq i\leq N,\ c\in\mathcal C_{r,D,E}}\neq0.
   }
   \]

The same equivalence holds if rows are drawn from Laurent coefficients at any nonempty family of
poles, rather than at one fixed pole.

## Proof

A polynomial ADE over \(\mathbb C(z)\) can be cleared of denominators and written
\[
 \sum_{(q,\alpha)\in\mathcal C_{r,D,E}}
 c_{q,\alpha}F_{q,\alpha}(z)=0
\]
for some finite \(r,D,E\) and a nonzero coefficient vector \(c\).  Thus hypertranscendence is
equivalent to linear independence of every finite family \((F_{q,\alpha})\).

The Laurent expansion at \(a\) is injective on meromorphic functions: if all coefficients of a
meromorphic function vanish, it vanishes on a punctured neighborhood of \(a\), hence on \(U\) by
the identity theorem.  Therefore a coefficient vector lies in the kernel of the Laurent matrix
exactly when it gives a global ADE relation.  This proves \((1)\iff(2)\).

For a matrix with \(N\) columns, column independence is equivalent to the existence of an
invertible \(N\times N\) row minor.  Indeed, the descending intersection of the kernels of all
finite row truncations stabilizes in the finite-dimensional coefficient space; if the full
kernel is zero, some finite truncation already has zero kernel, and an \(N\)-row submatrix has
nonzero determinant.  This proves \((2)\iff(3)\). \(\square\)

## Specialization to \(\psi\!\circ\!\Gamma\)

For
\[
 f(z)=\psi(\Gamma z),
\]
the poles
\[
 a=z_{n,m},\qquad \Gamma(z_{n,m})=-m,
\]
give a two-index family of certificate rows.  The exact values from
`../new_scientific_knowledge/digamma-gamma-factorial-pole-cluster-law.md` begin with
\[
 z_{n,m}=-n-\frac{(-1)^n}{n!m}
 +\frac{\psi(n+1)}{(n!)^2m^2}+O(m^{-3}),
\]
\[
 \operatorname{Res}_{z=z_{n,m}}f(z)
 =\frac{(-1)^n}{n!m^2}
 -\frac{2\psi(n+1)}{(n!)^2m^3}+O(m^{-4}).
\]
All higher Laurent rows are algebraic expressions in the jets of \(\Gamma\) at \(z_{n,m}\) and
the universal Laurent coefficients of \(\psi\) at \(-m\).  Consequently, the full HT question
has a positive finite-value form:
\[
 \boxed{
 \forall r,D,E\ \exists\text{ a finite inverse-Gamma pole-jet minor with nonzero determinant}.
 }
\]

## Classification

The equivalence is a direct synthesis of the identity theorem, Laurent uniqueness, and
finite-dimensional linear algebra.  It is therefore a structural bridge, not new scientific
knowledge.  Its value is that it makes every bounded ADE claim decidable by one finite determinant
and identifies the exact entries supplied by the factorial pole-cluster law.

## Lean formalization — unconditional, axiom-clean

Three new modules, all `lake build` green and `#print axioms`-clean
(`propext`, `Classical.choice`, `Quot.sound` only).  Nothing is carried as a hypothesis interface:
the Laurent-coefficient functional and the determinant criterion are both constructed.

### `formal/GaloisForLFunctions/HTGeometry/LinearIndependentMinorCertificate.lean`

The determinant criterion, for an arbitrary coordinate space over a field.

| Declaration | Statement |
|---|---|
| `coordinateMinor v φ` | the square matrix `(v j (φ i))` of a column family read along a selection `φ` of coordinates |
| `linearIndependent_of_coordinateMinor_det_ne_zero` | one nonvanishing minor forces independence |
| `exists_coordinateMinor_det_ne_zero_fin` | a linearly independent `Fin n`-family admits a nonvanishing minor; induction adding one column at a time, the bordered determinant with free last row being a linear functional whose last coefficient is the previous minor |
| `exists_coordinateMinor_det_ne_zero` | the same for any finite index type |
| `linearIndependent_iff_forall_finset_exists_coordinateMinor_det_ne_zero` | independence over an arbitrary index type is decided by the finite minors |

This is the `(2) ⟺ (3)` half of the theorem, and is absent from mathlib
(`Matrix.rank` exists, but no minor characterisation of column independence).

### `formal/GaloisForLFunctions/HTGeometry/MeromorphicLaurentCoefficient.lean`

The missing Laurent infrastructure.  Mathlib has `MeromorphicAt` and analytic orders but no Laurent
coefficient functional for meromorphic functions.

| Declaration | Statement |
|---|---|
| `laurentShift f a k` | the clearing shift `t ↦ t ^ k * f (a + t)` |
| `laurentCoeff f a ℓ` | the `ℓ`-th Laurent coefficient, defined as the eventual value along `k → ∞` of the shifted Taylor coefficients — canonical, no choice of clearing exponent |
| `taylorCoeffZero_pow_mul` | multiplying by `t ^ j` shifts Taylor indices by `j` (one Leibniz expansion); the `k`-independence |
| `meromorphicAt_iff_exists_analyticAt_laurentShift` | meromorphy is exactly the existence of a clearing exponent |
| `laurentCoeff_eq_taylorCoeffZero` | evaluation through any admissible `k` |
| `laurentCoeff_sum` | `ℂ`-linearity on finite families meromorphic at `a` |
| `eventuallyEq_zero_nhdsNE_iff_forall_laurentCoeff_eq_zero` | **injectivity of the Laurent transform**: the coefficients vanish exactly when the function vanishes on a punctured neighbourhood |

The last item is the formal content of "the Laurent expansion is injective on meromorphic
functions" used in the paper proof; it is proved from `analyticOrderAt` and the vanishing of all
iterated derivatives, not assumed.

### `formal/GaloisForLFunctions/HTGeometry/MeromorphicPoleJetCertificate.lean`

The theorem itself.

| Declaration | Statement |
|---|---|
| `jetVector f n z` | `(z, f z, f' z, …, f⁽ⁿ⁾ z)`, in the variable order of `DifferentiallyAlgebraic` |
| `jetMonomial f n m` | the differential monomial `z ^ m₀ * ∏ⱼ (f⁽ʲ⁾ z) ^ mⱼ₊₁` — the card's `F_{q,α}` |
| `jetLaurentRow f a n m` | its row of Laurent coefficients at `a` — the card's matrix `M` |
| `DifferentiallyAlgebraicNear` / `HypertranscendentalNear` | the ADE notions read on a punctured neighbourhood of `a`, where the derivatives of a meromorphic function are honest |
| `meromorphicAt_jetMonomial` | every differential monomial of a function meromorphic at `a` is meromorphic at `a` |
| `eventuallyEq_zero_iff_forall_jetLaurentRow` | a finite linear relation among monomials holds near `a` exactly when it holds among their Laurent rows |
| `hypertranscendentalNear_iff_forall_linearIndependent_jetLaurentRow` | **`(1) ⟺ (2)`** |
| `hypertranscendentalNear_iff_forall_exists_jetLaurentMinor_det_ne_zero` | **`(1) ⟺ (3)`**, the finite determinant certificate |
| `hypertranscendentalNear_iff_forall_bounded_exists_jetLaurentMinor_det_ne_zero` | the same in the card's bounded shape `(r, D, E)`, via `BoundedJetExponent` and `exists_boundedJetExponent` |
| `hypertranscendental_of_forall_exists_jetLaurentMinor_det_ne_zero` | the certificate at a single point implies `Hypertranscendental f` in the global corpus sense |
| `differentiallyAlgebraicNear_iff_of_isPreconnected` | **pole independence**: on a preconnected set of meromorphy the local notion, hence the certificate, does not depend on the chosen point — the card's "any nonempty family of poles" clause |

Two points of fidelity worth recording.

1. The Lean statement of `(2)` and `(3)` quantifies over *every* finite family of differential
   monomials rather than over the truncations `C_{r,D,E}`.  This is equivalent — linear independence
   of a family is linear independence of every finite subfamily, and every finite family is bounded
   (`exists_boundedJetExponent`) — and the card's exact bounded shape is recorded separately as
   `hypertranscendentalNear_iff_forall_bounded_exists_jetLaurentMinor_det_ne_zero`.
2. The ADE relation is taken on the punctured-neighbourhood filter rather than pointwise on all of
   `ℂ`.  This is forced: the pointwise reading is sensitive to the junk values that `deriv` and
   division assign at poles (`z · (1/z) − 1` is the zero function off the origin but takes the value
   `−1` at it).  The global corpus notion is recovered in the useful direction by
   `differentiallyAlgebraicNear_of_differentiallyAlgebraic`, so the certificate still proves
   `Hypertranscendental f`.

## Gates

- [x] 0 → 1: coefficient matrix and ADE bounds defined
- [x] 1 → 2: equivalence and finite-minor proof complete
- [x] 2 → 3: formal Laurent infrastructure and determinant criterion built and proved
  unconditionally; `lake build GaloisForLFunctions.HTGeometry.MeromorphicPoleJetCertificate` green,
  `#print axioms` clean on every theorem listed above
- [ ] 3 → 4: include only as a supporting lemma in a publication (no standalone pre-print: the
  result is classified as not new scientific knowledge)

## Log

- 2026-07-31 — formalized in Lean 4.  Built the two missing pieces named by the 2 → 3 gate
  (a Laurent-coefficient functional for meromorphic functions, and the minor characterisation of
  linear independence), then assembled the full equivalence, the bounded-complexity form, the
  bridge to the corpus's global `Hypertranscendental`, and pole independence on preconnected
  domains.  Moved to `3-formalized/not_new_scientific_knowledge`.
