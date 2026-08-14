# Functional-reflection positive envelope, polarization untwisting, and faithful-receiver trilemma

- **ID:** ULF-CRSM-4
- **Stage:** 2-fully-proven
- **Type:** FROZEN CONJECTURE -> HOSTILE CLASSIFICATION THEOREM
- **Status:** `[PAPER-PROVED] [BRIDGE] [PARENT KREIN C*-ALGEBRA]`
- **Parent card:** `../../../../2-fully-proven/universal-law-field/constitutive-reflection-space-mechanics/split-star-formation-positive-profile-and-functional-fixedness-neutrality-law.md`

## Public sentence

Functional reflection can be used as the algebraic adjoint or retained as a symmetry of a positive
adjoint, but a nontrivial reflection cannot do both jobs in a faithful positive realization.

## 1. Exact frontier

The parent theorem proves that every direct `*`-homomorphic formation preserves star-isotropy.  A
nonfixed reflected atom `e_x` with

\[
 e_x^*=e_{\sigma x},\qquad e_{\sigma x}e_x=0
\]

is therefore killed by every `C*` receiver, before or after any direct `*`-formation.  The unresolved
question is not whether one atom is killed, but what the complete positive receiver of the whole
functional-reflection algebra is and whether changing the involution can retain the lost orbit.

### Internal corpus boundary

- `ConstitutivePositiveProfileFormation.lean` proves receiver-profile conservation and hereditary
  star-isotropy.
- `RHTower/XiPositiveReflectionRadical.lean` proves the route-specific positive-radical reduction.
- `RHTower/CCMRationalAdelicCompletedXiFixedCoronaPolarization.lean` contains a concrete Hodge
  untwisting.
- `RHTower/EulerPrimitiveJointDepthKreinXiLanding.lean` contains a concrete fundamental symmetry.
- No universal-law theorem classifies the full receiver radical or positive spectrum of a finite
  functional-reflection algebra, or compares it with the untwisted positive dagger.

### External parent mathematics

The proposed *machinery* is not new.

- Kawamura, *Algebra with indefinite involution and its representation in Krein space*,
  [arXiv:math/0610059](https://arxiv.org/abs/math/0610059), replaces an indefinite involution by a
  positive one and derives Krein representations from a `Z/2` dynamical system.
- Bannangkoon--Bertozzini--Lewkeeratiyutkul, *Spectral Theory on Commutative Krein C*-algebras*,
  [arXiv:1409.1329](https://arxiv.org/abs/1409.1329), defines a fundamental symmetry `J`, the
  positive involution `dagger = J o star`, and the even/odd decomposition.
- Nieuviarts, *Signature change by an isomorphism of spectral triples*,
  [arXiv:2402.05839](https://arxiv.org/abs/2402.05839), relates twists, Krein products, parity, and
  signature change through one implementing unitary.

Thus “invent Krein geometry” is `[REDISCOVERED]`.  The surviving claim is the exact universal
positive-envelope classification below and its consequence for constitutive selection.

## 2. Frozen conjecture

Let `X` be a finite set and `sigma:X->X` an involution.  On

\[
 A_X=\mathbb C^X
\]

use pointwise multiplication and define

\[
 f^\dagger(x)=\overline{f(x)},\qquad
 f^{*_{\sigma}}(x)=\overline{f(\sigma x)}.
 \tag{FPE.1}
\]

Write

\[
 F=X^\sigma=\{x:\sigma x=x\},\qquad
 q:A_X\longrightarrow\mathbb C^F,\qquad q(f)=f|_F.
 \tag{FPE.2}
\]

> **Conjecture.** The restriction `q` is the universal positive receiver of
> `(A_X,*_sigma)`: every `*`-homomorphism from `(A_X,*_sigma)` to a `C*`-algebra factors uniquely
> through `q`.  Its universal positive radical is exactly `ker q`.  A faithful positive receiver
> exists iff `sigma=id`.  Replacing `*_sigma` by `dagger` restores a faithful positive receiver on
> all of `X`, but functional reflection then survives only as a separate involutive
> `dagger`-automorphism and supplies no fixed-point selection.

This is falsifiable already on one two-cycle.

## 3. Hostile attack

### Attack A -- a noncommutative receiver might retain a two-cycle

It cannot.  For the point atom `e_x`,

\[
 e_x^{*_{\sigma}}e_x=e_{\sigma x}e_x=0
\]

when `sigma x != x`.  In every `C*`-algebra, `a^*a=0` implies `a=0`; hence every receiver kills
`e_x`, independent of receiver commutativity.

### Attack B -- the receiver might lose more than the nonfixed atoms

It need not.  Restriction to `F` is itself a surjective `*`-homomorphism into the finite-dimensional
`C*`-algebra `C^F`.  Therefore every element nonzero on `F` survives this receiver.

### Attack C -- untwisting might itself select the fixed locus

It does not.  Under `dagger`, every atom is a nonzero selfadjoint projection and the identity
representation is faithful.  The map `Jf=f o sigma` is a `dagger`-automorphism permuting all atoms.
Untwisting retains the reflection action but removes its positive erasure.

### Verdict

The conjecture survives.  The proof is finite and dependency-closed below.  The surrounding Krein
framework is `[REDISCOVERED]`; the exact receiver classification is `[BRIDGE]` and new to the HGT
universal-law corpus.

## 4. Classification theorem

### Theorem 4.1 -- functional-reflection positive-envelope law

Let `X`, `sigma`, `A_X`, `F`, and `q` be as above.

1. `*_sigma` is a conjugate-linear involutive anti-automorphism, and

   \[
   f^{*_{\sigma}}=J(f^\dagger),\qquad Jf=f\circ\sigma.
   \tag{FPE.3}
   \]

2. `q:(A_X,*_sigma)->(C^F,dagger)` is a surjective unital `*`-homomorphism.
3. For every unital `*`-homomorphism `pi:(A_X,*_sigma)->B` into a `C*`-algebra,

   \[
   \ker q\subseteq\ker\pi.
   \tag{FPE.4}
   \]

   Hence there is a unique unital `*`-homomorphism `bar pi:C^F->B` with

   \[
   \pi=\bar\pi\,q.
   \tag{FPE.5}
   \]

4. The intersection of the kernels of all positive receivers is exactly

   \[
   \boxed{J_+(A_X,*_\sigma)=\ker q
   =\{f:f|_F=0\}.}
   \tag{FPE.6}
   \]

5. The positive characters are exactly the evaluations at fixed points.  Thus the positive
   spectrum is `F`, not the orbit space `X/sigma`.
6. A faithful positive receiver exists iff `sigma=id_X`.
7. With the untwisted dagger, `A_X` is the finite-dimensional `C*`-algebra `C^X`, its identity
   receiver is faithful, and `J` is an involutive dagger automorphism.  Every nonfixed pair survives.

### Proof

For `(1)`, commutativity gives

\[
 (fg)^{*_{\sigma}}(x)
 =\overline{f(\sigma x)g(\sigma x)}
 =g^{*_{\sigma}}(x)f^{*_{\sigma}}(x),
\]

and involutivity of `sigma` gives

\[
 (f^{*_{\sigma}})^{*_{\sigma}}(x)
 =\overline{\overline{f(\sigma^2x)}}=f(x).
\]

Equation `(FPE.3)` is the definition.

For `(2)`, restriction is visibly unital, linear, multiplicative, and surjective by extension by
zero outside `F`.  If `x in F`, then

\[
 q(f^{*_{\sigma}})(x)=\overline{f(\sigma x)}
 =\overline{f(x)}=q(f)^\dagger(x),
\]

so it preserves star.

For `(3)`, let `e_x` be the characteristic function of `{x}`.  If `x notin F`, then

\[
 e_x^{*_{\sigma}}=e_{\sigma x},\qquad
 e_x^{*_{\sigma}}e_x=0.
\]

Therefore

\[
 \pi(e_x)^*\pi(e_x)=\pi(e_x^{*_{\sigma}}e_x)=0,
\]

and the `C*` identity gives `pi(e_x)=0`.  Every `f in ker q` has the finite expansion

\[
 f=\sum_{x\notin F}f(x)e_x,
\]

so `pi(f)=0`; this proves `(FPE.4)`.  Since `q` is surjective, the ordinary quotient universal
property gives a unique unital algebra homomorphism `bar pi` satisfying `(FPE.5)`.  It preserves
star because `q` and `pi` do and `q` is surjective.

For `(4)`, `(FPE.4)` puts `ker q` inside every receiver kernel.  Conversely, `q` itself is a
positive receiver, so an element outside `ker q` survives.  Hence the intersection is exactly
`ker q`.

For `(5)`, every character factors through `C^F`.  The coordinate idempotents in `C^F` are pairwise
orthogonal and sum to one.  A unital algebra homomorphism to `C` sends each to an idempotent, hence
to `0` or `1`, and sends exactly one to `1`.  It is therefore evaluation at one fixed point.
If `F` is empty, a unital map from the zero algebra `C^F` to nonzero `C` cannot exist, so both sets
of characters are empty.  Conversely every fixed-point evaluation preserves `*_sigma`.

For `(6)`, if `sigma` has a nonfixed point, every positive receiver kills the nonzero atom `e_x`,
so none is faithful.  If every point is fixed, `*_sigma=dagger` and the identity representation of
`C^X` is faithful.

For `(7)`, pointwise conjugation makes `C^X` a finite-dimensional commutative `C*`-algebra.  Direct
substitution shows

\[
 J(fg)=J(f)J(g),\quad J(f^\dagger)=J(f)^\dagger,\quad J^2=id,
\]

and `J(e_x)=e_{sigma x}`.  The identity receiver retains every atom.  QED.

## 5. Exact trilemma

For a nontrivial finite involution, the following cannot coexist:

1. functional reflection is identified with the algebraic adjoint `*_sigma`;
2. the realization is positive in a `C*` receiver;
3. every source atom is retained faithfully.

Keeping `(1)` and `(2)` forces the quotient `C^X -> C^F`.  Keeping `(2)` and `(3)` requires the
untwisted dagger and leaves functional reflection as the neutral symmetry `J`.  No common recovery
or direct `*`-formation changes this classification, by the parent receiver-profile theorem.

## 6. Four-organ consequence

| organ | exact consequence |
|---|---|
| functional equation | `sigma` is an involutive action on source packets |
| algebraic reflection | identifying `sigma` with star makes nonfixed atoms star-isotropic |
| positive representation | universal receiver is restriction to the fixed locus |
| topology/spectrum | positive spectrum collapses from `X` to `Fix(sigma)` |

The fourth line is a prediction forced by the first three, not an extra route input.

## 7. Representation lesson and exact open core

Positivity is not an intrinsic scalar test on an unmarked functional-equation algebra.  It depends
on which involution is declared physical adjoint.  The missing constitutive mechanism must therefore
do more than construct a positive receiver:

> it must produce, transport, and constrain the polarization relating functional reflection to the
> positive dagger.

The next exact question is whether local source-produced positive untwistings transport coherently
through formation.  Any additive mismatch of chosen untwistings is automatically suspect as a
coboundary; a field law must identify the restricted space of admissible positive polarizations and
prove a gauge-invariant obstruction or properness theorem there.  This open problem is kept in the
Stage-1 field programme and is not part of Theorem 4.1.

## 8. Sharp boundaries

1. Finiteness is used for the atom expansion.  Infinite locally compact variants require a chosen
   function algebra and completion.
2. The theorem classifies direct `*`-homomorphisms.  Relative, derived, non-`*`, or law-changing
   comparisons are deliberately outside scope.
3. Fundamental symmetries need not be unique in general Krein `C*`-algebras.  Here `J` is fixed by
   the marked source involution `sigma`.
4. The fixed-locus quotient is selection by erasure, not a faithful proof of absence of nonfixed
   source packets.
5. Untwisting is conservative but not selective.
6. No `Xi` zero, RH statement, or source-canonical global polarization is constructed.

## 9. Promotion gate

- [x] internal corpus audit
- [x] external parent audit
- [x] exact conjecture frozen
- [x] hostile attacks A--C
- [x] dependency-closed paper proof drafted
- [x] hostile reread of factorization and empty-fixed-locus edge case
- [x] promote to Stage 2 after reread
- [x] formalize exact classification in Lean

## 10. Lean certification

The exact classification is certified in
`formal/GaloisForLFunctions/HTGeometry/ConstitutiveFunctionalReflectionPositiveEnvelope.lean`.
Lean proves the twisted-star algebra, fixed-locus restriction, atom erasure in arbitrary positive
`C*` receivers, unique factorization, exact receiver radical, positive-character classification,
faithful-receiver trilemma, and positive-dagger untwisting.  The module is wired into
`GaloisForLFunctions.HTGeometry.UniversalLawField`.
