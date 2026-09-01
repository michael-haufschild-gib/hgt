# Vacuum-index cancellation and determinant-family torsion

- **ID:** ULF-CIT-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / NO-GO WITH POSITIVE SURVIVOR
- **Statement:** Composing an index-zero analytic Fredholm pencil with an injective one-defect
  shift preserves index `-1` at every parameter while retaining every characteristic value in a
  matched effective kernel--cokernel defect and in the determinant section.

## 1. Big-picture interpretation

The fixed source winding and the Xi divisor occupy different categorical degrees. Pointwise
Fredholm index is a signed group-completed shadow. The Xi divisor is torsion of an analytic family.
Putting them into one operator does not make the first control the second: characteristic modes
are balanced before numerical index is taken.

For the corpus this is decisive. The theta source already supplies one fixed Hilbert--Schmidt
operator `B` with

`det_2(I + z B) = XiC(z) / XiC(0)`

and exact algebraic multiplicity. Adding the unilateral source vacuum cannot turn this determinant
identity into an RH proof.

## 2. Corpus audit

Searches with `scripts/formal_tools.py research` covered Fredholm composition, balanced defects,
source determinant zeros, effective defect pairs, analytic local multiplicity, and determinant
lines.

- `HedenmalmThetaSourceDeterminantIdentity` proves the global determinant identity.
- `HedenmalmThetaSourceDeterminantMultiplicity` identifies analytic order with the maximal
  generalized eigenspace of the fixed source inverse.
- `HedenmalmThetaKakutaniBalancedIndexNoGo` proves reflection-balanced escape has zero signed index.
- `ConstitutiveBalancedDefectZeroIndex` proves arbitrary balanced defect size is invisible after
  signed group completion.
- No corpus theorem stated the canonical cokernel exact sequence for composition with an injective
  one-defect operator.

External determinant-line, analytic-index, and Fredholm-complex theories already provide the
general technology. The new content here is the exact consequence for the corpus's already-fixed
theta/Xi pencil and the resulting retirement of ALCI-3.

## 3. The algebraic exact sequence

### Theorem 3.1 [PROVED HERE]

Let `X,Y,Z` be complex vector spaces, `A : X -> Y` and `S : Y -> Z` linear, and suppose `S` is
injective. There is a canonical exact sequence

`0 -> coker A --S_bar--> coker(S A) --pi--> coker S -> 0`,

and `ker(S A) = ker A`.

Here

- `S_bar(y + ran A) = S y + ran(S A)`;
- `pi(z + ran(S A)) = z + ran S`.

#### Proof

`S_bar` is well-defined because `S(ran A) = ran(S A)`. If `S_bar(y + ran A)=0`, then
`S y = S(Ax)` for some `x`; injectivity of `S` gives `y=Ax`, so `S_bar` is injective.

`pi` is well-defined because `ran(S A) <= ran S`, and it is surjective. Its kernel consists of
classes represented by `z=S y`; each equals `S_bar(y + ran A)`. Thus
`ker pi = ran S_bar`, proving exactness. Finally `S(Ax)=0` iff `Ax=0` because `S` is injective, so
the kernels agree. QED.

### Corollary 3.2 [PROVED HERE]

Assume the ranges are closed and the three cokernels and relevant kernels are finite-dimensional.
Then

`dim coker(S A) = dim coker A + dim coker S`

and

`ind(S A) = ind A + ind S`.

#### Proof

Dimension is additive in the short exact sequence. Subtract it from
`dim ker(S A)=dim ker A`. QED.

## 4. One-defect vacuum cancellation

### Theorem 4.1 [PROVED HERE]

Let `H` be a complex Hilbert space, let `S : H -> H` be an isometric unilateral shift with
`dim coker S = 1`, let `B` be compact, and put `A_z = I + z B`. Then for every `z`:

1. `A_z` and `S A_z` are Fredholm with closed range;
2. `ind A_z = 0` and `ind(S A_z) = -1`;
3. writing `g_z = dim ker A_z`,
   `dim ker(S A_z)=g_z` and `dim coker(S A_z)=1+g_z`;
4. `A_z` is noninvertible exactly when the effective defect of `S A_z` is strictly larger than
   the vacuum pair `(0, C)`.

#### Proof

`A_z` is a compact perturbation of the identity, hence Fredholm of index zero. The isometry `S`
has closed range, is injective, and has one-dimensional cokernel. Its restriction to any closed
subspace is an isomorphism onto a closed subspace, so `S A_z` has closed range. Apply Corollary 3.2.
Since `ind A_z=0`, `dim coker A_z=dim ker A_z=g_z`. The last claim is the Fredholm alternative.
QED.

## 5. Theta/Xi consequence

### Theorem 5.1 [PROVED HERE]

Let `B` be the fixed corpus theta source inverse and `S` a unilateral one-defect shift. Define
`Omega_z = S (I + z B)`. Then

`ind Omega_z = -1`

for every complex `z`, including every zero of `XiC`. Moreover:

- `XiC(z)=0` iff `ker Omega_z` is nonzero;
- at such a point the cokernel dimension grows by the same geometric multiplicity;
- analytic order of `XiC` is retained by the generalized root space/determinant section, even
  though pointwise index sees only the zero difference of geometric defects.

#### Proof

The corpus proves `det_2(I+zB)=XiC(z)/XiC(0)` and `XiC(0) != 0`. Its Fredholm-alternative theorem
identifies determinant zeros with nonzero eigenmodes of `B`, hence with noninvertibility of
`I+zB`. Theorem 4.1 gives every index and defect-dimension statement. The corpus's determinant
multiplicity theorem identifies analytic order with the maximal generalized eigenspace. QED.

## 6. Exact no-go and positive survivor

ALCI-3 proposed

`coker Omega ~= vacuum + Xi_negative + escape`

while keeping `Omega` injective. For `Omega_z=S(I+zB)`, injectivity is exactly nonvanishing of Xi;
it cannot be obtained from the fixed index. At a zero, the omitted `ker(I+zB)` cancels the extra
cokernel in numerical index. Therefore the equation `-1=-(1+k)` is not an index theorem but RH
inserted as injectivity.

The positive survivor is the **effective family defect**:

- pointwise ordered pair `(ker A_z, coker A_z)` retains geometric defect;
- the analytic root complex retains algebraic multiplicity;
- the determinant-line section retains its divisor;
- Green/Krein data may orient this torsion relative to the real locus.

Any viable completion theorem must act on this family-level object and prove a source-native
support/properness restriction. Ordinary Fredholm index, any invariant factoring through it, and a
vacuum cokernel count cannot do so.

## 7. RH relevance and boundary

This theorem does not prove RH. It removes a false closure architecture and narrows the only viable
completion-index class:

1. index must retain analytic-family torsion before signed cancellation;
2. it must distinguish real-locus torsion from off-real conjugate torsion;
3. it must be constructed from the literal theta/prime--Gamma source before divisor selection;
4. it must prove no birth or escape of off-real torsion under completion.

Determinant lines, Gohberg--Sigal multiplicity, spectral flow, Maslov index, and Pontryagin inertia
are candidate readers. None is a producer without clause 3 and the properness theorem in clause 4.

## 8. Formalization status

Paper proof is dependency-closed. No Lean file was written or built because current task phase
explicitly restricts work to Lean-corpus audit. Exact formalization target is Theorem 3.1 plus the
finite-dimensional dimension corollary; the theta consequence should reuse the already-formalized
determinant identity rather than duplicate it.

## Log

- 2026-09-01 — proved after the source determinant audit falsified pointwise arithmetic Levinson
  closure.
