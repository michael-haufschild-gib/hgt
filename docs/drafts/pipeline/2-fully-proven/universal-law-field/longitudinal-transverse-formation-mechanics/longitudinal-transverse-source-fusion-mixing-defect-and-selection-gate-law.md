# Longitudinal--transverse source fusion, mixing defect, and selection-gate law

- **ID:** ULF-LTFM-2
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / CROSS-ORGAN FUSION AND EXACT NO-GO
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL] [THREE-ORGAN FUSION]`
  `[EXACT CONSERVATION] [JOINT RECONSTRUCTION] [SELECTION GATE] [LEAN PENDING] [NOT RH]`

## 1. Abstract split source

Let `X` be a complex topological vector space, let

\[
 c:X\to\mathbb C,\qquad e:\mathbb C\to X
\]

be continuous linear maps with `c e=id`.  The codiagonal `c` is the longitudinal observer and
`e` is its marked section.  Define

\[
 r(x)=x-e(c(x)). \tag{LTF.1}
\]

Then

\[
 \boxed{c(r(x))=0,\qquad x=r(x)+e(c(x)).} \tag{LTF.2}
\]

Thus the source is reconstructed jointly from its scalar longitudinal response and its zero-mass
transverse radical.

For a continuous linear intervention `T:X->X`, define its mixing defect

\[
 \mathfrak m_T(x)=c(T(r(x))). \tag{LTF.3}
\]

### Theorem 1.1 -- exact intervention conservation and classification

For every `x`,

\[
 \boxed{c(Tx)=\mathfrak m_T(x)+c(T(e(c(x)))).} \tag{LTF.4}
\]

Moreover, the following are equivalent:

1. `mathfrak m_T(x)=0` for every `x`;
2. `T` preserves the zero-mass radical: `c(y)=0` implies `c(Ty)=0`.

If these conditions hold and one scalar `a` satisfies

\[
 c(T(e(z)))=az\qquad(z\in\mathbb C), \tag{LTF.5}
\]

then

\[
 \boxed{c(Tx)=a\,c(x).} \tag{LTF.6}
\]

### Proof

Equation `(LTF.2)` follows from `ce=id`.  Apply `T` and then `c` to the second equality to obtain
`(LTF.4)`.  If the radical is preserved, `(LTF.3)` vanishes.  Conversely, if the defect vanishes,
then for `c(y)=0` one has `r(y)=y`, hence `c(Ty)=0`.  Substitute `(LTF.5)` into `(LTF.4)` to obtain
`(LTF.6)`. QED.

The theorem identifies the exact missing mechanism: a transverse construction can affect a
longitudinal divisor only through a nonzero mixing defect.

## 2. Literal complete-shell realization

For the complete high-exponent Riemann resolution, let

\[
 X=\ell^1(\mathbb N;\mathbb C),\qquad
 c(x)=\sum_jx_j,
\]

with point section `e(z)=z delta_0`.  Existing source theorems construct, for every `K` and every
`s` with `Re(s)>0`, a canonical vector `h_K(s) in X` satisfying

\[
 \boxed{c(h_K(s))=1.} \tag{LTF.7}
\]

Its coordinates are the normalized complete-resolution multipliers: the head reciprocal dilation
and all subsequent largest-exponent shell differences.  The series is absolutely summable, and
the codiagonal is norm one.

Let `U` be any scalar response and form

\[
 \mathcal X_U(s)=U(s)h_K(s). \tag{LTF.8}
\]

### Theorem 2.1 -- literal source fusion and pole-unit landing

For every admitted `s`,

\[
 \boxed{c(\mathcal X_U(s))=U(s).} \tag{LTF.9}
\]

Consequently, for admitted `epsilon` and `epsilon w`,

\[
 \boxed{
 \frac{c(\mathcal X_U(\epsilon w))}{c(\mathcal X_U(\epsilon))}
 =\frac{U(\epsilon w)}{U(\epsilon)}
 =C_\epsilon(w).} \tag{LTF.10}
\]

If `q(s) in ker c` is any transverse perturbation, replacing `mathcal X_U(s)` by
`mathcal X_U(s)+q(s)` leaves `(LTF.9)` and `(LTF.10)` unchanged.

### Proof

Linearity and `(LTF.7)` give `c(Uh)=U c(h)=U`.  Apply this at both endpoints of the scale
intervention.  A transverse perturbation is killed by `c`. QED.

## 3. Genuine three-organ fusion

The theorem is not a restatement inside one route.

1. **Arithmetic/incidence organ:** largest-exponent coefficient channels form the complete source
   resolution.
2. **Completion/topology organ:** absolute summability selects `ell^1`, where the codiagonal is a
   bounded quotient with a bounded section; the corresponding Hilbert codiagonal is nonclosable.
3. **Analytic/probability organ:** codiagonal fusion lands exactly on the pole-unit scale cocycle,
   whose correction ghosts reconstruct its regular germ and generate its moment/phase/Hankel
   shadows.

The joint reconstruction law is

\[
 \boxed{\mathcal X_U(s)=r(\mathcal X_U(s))+e(U(s)).} \tag{LTF.11}
\]

The conservation law `(LTF.4)` determines exactly which interventions can transfer information
between the transverse source resolution and the longitudinal analytic divisor.

## 4. Fourth-organ prediction and exact no-go

The predicted fourth organ is intervention geometry.  Every candidate source operation `T` has a
canonical observable `mathfrak m_T`.  This gives a sharp dichotomy:

- `mathfrak m_T=0`: the operation is block-triangular, preserves the radical, and can only rescale
  the longitudinal response by its predeclared section action;
- `mathfrak m_T!=0`: transverse source information is genuinely converted into longitudinal
  analytic response.

Hence no family of normalized shell operations, probability laws, phase packets, Hankel tests, or
radical-preserving completions can select the common Riemann divisor.  They can reconstruct and
test the normalized resolution, but `(LTF.6)` proves that they cannot generate a new divisor law.

This is stronger than saying that one observer is lossy.  It classifies the entire no-mixing
intervention algebra.

## 5. RH selection consequence

For the Euler-shell specialization, the common longitudinal factor carries the zeta/Xi divisor,
while the high-shell normalized channels are zero-free transversely.  Therefore a final RH
mechanism must construct, before divisor specialization, an admitted intervention `T` such that

\[
 \boxed{\mathfrak m_T\ne0} \tag{LTF.12}
\]

and whose longitudinal output obeys the reflected fixed-locus law.  Proving only a property of
the normalized channel vector, or only a scalar action on the marked section, is ruled out by
`(LTF.6)`.

This theorem does not produce that mixed intervention and does not prove RH.  It replaces the
vague request for a source-native selector by a typed mechanism-level obligation: generate and
control a nonzero longitudinal--transverse mixing defect.

## 6. Hostile scope

1. The split itself is classical linear algebra; the content is its exact literal source landing
   and its selection obstruction.
2. Choosing an arbitrary `T` with nonzero mixing is theatre.  The intervention must be generated
   by pre-zero source operations and must obey the same composition laws as the source.
3. Nonzero mixing is necessary, not sufficient, for RH.  Reflection orientation and analytic
   admission remain additional laws.
4. Scalar normalization always has zero mixing defect.
5. The theorem preserves the Banach/Hilbert completion distinction; it does not regularize the
   known nonclosable Hilbert codiagonal.

## 7. Formalization boundary

Lean module:

`formal/GaloisForLFunctions/HTGeometry/LongitudinalTransverseFormationMechanics.lean`.

It should certify the abstract split, mixing conservation, radical-preservation equivalence,
scalar no-mixing classification, literal complete-resolution codiagonal landing, scale-response
identity, and transverse-perturbation blindness.

## Gates

- [x] abstract conservation and classification proved
- [x] literal complete-resolution instantiation proved
- [x] pole-unit response landing proved
- [x] joint reconstruction proved
- [x] fourth-organ intervention defect predicted
- [x] exact no-mixing selection obstruction proved
- [ ] Lean certification and Stage-3 promotion
- [ ] source-generated nonzero mixed intervention
- [ ] reflected analytic admission and RH consequence

## Log

- 2026-08-11 -- extracted after the pole-unit fusion law met the already-formal complete-shell
  partition of unity: normalization separates the common divisor from the transverse source, and
  only a mixed intervention can reconnect them.
