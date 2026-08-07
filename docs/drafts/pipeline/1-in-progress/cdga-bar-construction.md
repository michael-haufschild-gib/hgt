# The bar construction of an augmented commutative differential graded algebra

- **ID:** `cdga-bar-construction`
- **Stage:** 1-in-progress
- **Type:** INFRASTRUCTURE
- **Parents:** `cdga-module-derived-tensor-layer`,
  `deninger-derived-rank-quotient-universal-property`,
  `deninger-selective-positive-cell-h0-preservation`,
  `deninger-character-shape-formality`

## Why

Three deninger cards record the same remaining gap in the same words: "the `E_∞` coherence, the bar
construction and its spectral sequence".  The corpus's substitute for `E_∞` is the commutative
differential graded model, which is now complete — free algebras on degree-one generators, relative
tensor products of algebras over a base, semi-free resolutions, flatness and derived base change.
The bar construction is the one object of that model still missing, and it is what the cards use to
pass from the underived shadow to the connectivity statements.

## What is to be built

Let `A` be a unital commutative differential graded algebra over `R` with an augmentation
`ε : A → R`, and let `Ā = ker ε` be the augmentation ideal.  Assume `A` connected, that is `Ā`
concentrated in degrees `≥ 1`, so that the shift `sĀ` with `(sĀ)^n = Ā^{n+1}` stays in
nonnegative degrees.  The bar construction is

    B(A) = ⨁_{k ≥ 0} (sĀ)^{⊗ k}

with the differential `d = d_int + d_bar`, where `d_int` is the internal differential of `Ā` with the
sign of the shift and `d_bar` multiplies adjacent factors.

## Steps

1. **The augmentation ideal as a non-unital algebra.**  `augIdealCarrier` and `augIdealModule` are
   built; what is missing is the multiplication `Ā^a → Ā^b → Ā^{a+b}` and its bilinearity,
   associativity, graded commutativity and Leibniz rule.  `[LANDED]`
2. **The shift of the ideal**, `(sĀ)^n = Ā^{n+1}`, with the induced differential and the sign.
3. **The iterated tensor power** `(sĀ)^{⊗k}`, by recursion on `k` using the corpus's
   `TensorCarrier`, which is already a product over the decompositions of the degree and therefore
   the direct sum in each degree.
4. **The total object** `⨁_k (sĀ)^{⊗k}` in each degree.
5. **The two differentials** and `d² = 0`.
6. **The augmentation and the counit**, and the comparison `B(A) → R`.

## Status

Steps 1--3 landed; axiom audit for every declaration below is `propext, Classical.choice, Quot.sound`
or less.

- `formal/GaloisForLFunctions/HTGeometry/CDGAAugmentationIdealAlgebra.lean` — `augIdealMul` with
  bilinearity, `augIdealMul_assoc`, `augIdealMul_comm`, `augIdealMul_leibniz`: **the augmentation
  ideal is a commutative differential graded algebra without a unit.**
- `formal/GaloisForLFunctions/HTGeometry/CDGAGroundModule.lean` — `zeroComplexModule`: **a cochain
  complex is a differential graded module with zero action**, over any algebra.  This is the device
  that makes the whole module layer — in particular the tensor product with its Koszul sign —
  available for plain complexes, without building a second tensor product.  The first attempt went
  through modules over `groundCDGA` with the scalar action in degree zero; that forces a transport
  along `0 + b = n` into every axiom, and the zero action avoids all of it while giving the same
  tensor product, since `tensorD` never reads the action.
- `formal/GaloisForLFunctions/HTGeometry/CDGACochain.lean` — `Cochain`, a complex packaged with its
  instances so that complexes can be produced by recursion (the `DGStage` pattern);
  `Cochain.tensor`, **the tensor product of complexes**, whose differential squares to zero for
  free; `Cochain.ground`; `augIdealShift`, **the shift of the augmentation ideal**, degree `n` being
  degree `n + 1` of the ideal with the differential negated; and `barPower`, **the `k`-fold tensor
  power of the shifted ideal**, by recursion on `k`.

## Step 5: the bar differential

The bar differential maps `(sĀ)^{⊗(k+1)} → (sĀ)^{⊗k}` and *raises* the total degree by one, since
multiplying two shifted elements of degrees `a` and `b` gives an element of `Ā` in degree
`a + b + 2`, which is degree `a + b + 1` after the shift.  Written recursively on the number of
factors it has two parts, and both are now within reach.

- The tail part, `id ⊗ d_bar`, is a degree-one map on the *right* factor with the Koszul sign of the
  degree of the left one.  **Landed**: `formal/GaloisForLFunctions/HTGeometry/CDGATensorDegOne.lean`
  — `tensorLeftDegOne`, `tensorRightDegOne` and their linear forms, the generalisation of the two
  half-differentials of a tensor product from a differential to an arbitrary degree-one family.
- The head part multiplies the outer factor with the first factor of the inner tensor product.  It
  looked as though this needed a graded associator for `TensorCarrier`, which the corpus does not
  have and which would need the distribution of a tensor product over a finite product of
  decompositions.  It does not: `TensorCarrier` is a *product over decompositions*, so the component
  of the result at a decomposition `(c, e)` is a finite sum over `a + a' = c - 1` of terms obtained
  by projecting the inner factor at `(a', e)` — projection out of the second factor of a tensor
  product is `TensorProduct.map id (proj _)`, which is linear — and then applying mathlib's ordinary
  `TensorProduct.assoc` followed by the multiplication in the first two slots.  No graded associator
  is needed.

Both pieces of step 5's head are now landed as well.

- `formal/GaloisForLFunctions/HTGeometry/CDGABarMul.lean` — `augIdealShiftMulₗ`,
  `augIdealShiftMulTensor`: **the multiplication of two shifted elements**, of shifted degrees `a`
  and `a'`, landing in shifted degree `a + a' + 1`, as a bilinear map and out of the tensor product.
- `formal/GaloisForLFunctions/HTGeometry/CDGABarHead.lean` — `BarSplit` with its `Fintype`
  instance, `barHeadTerm` and **`barHead`**: the head of the bar differential, the finite sum over
  the splits `a + a' + 1 = c` of "project the inner factor at `(a', e)`, reassociate with the
  ordinary associator of tensor products, multiply the first two slots".

The head is linear by construction — each term is a composition of projections, the associator and
the multiplication, and it is the *composition* that is transported along the degree identification,
not its value — and the bar differential itself is assembled:

- `formal/GaloisForLFunctions/HTGeometry/CDGABarDifferential.lean` — **`barD`**: on `k + 1` factors,
  the head plus the bar differential of the last `k` tensored with the identity, carrying the Koszul
  sign of the first factor; on one factor there is no adjacent pair, so it is zero.

One Lean point worth keeping: the two summands of the recursive step have syntactically different
source types, `TensorCarrier sĀ (barPower (k+1))` and `TensorCarrier sĀ (TensorCarrier sĀ
(barPower k))`.  They are definitionally equal, but instance resolution for `HAdd` runs at reducible
transparency and does not see it; ascribing both summands to the same type with `show … from` is what
lets the sum elaborate.

Step 6 is landed too, in the same module: `BarCarrier`, **the bar construction** — in each degree
the direct sum over the number of factors of the tensor powers of the shifted ideal —
`barTotalComponent`, the component of the total differential on the `k`-fold power (the internal
differential, which keeps the number of factors, plus the bar differential, which lowers it by one),
`barTotalD`, and `barTotalD_of`, its value on a single factor.

What remains is `d² = 0`.  Writing the recursive step as `barD (k+1) = H_k + R(barD k)`, with `H` the
head and `R` the right-factor degree-one construction, the square expands into four terms:

    H ∘ H  +  H ∘ R(barD)  +  R(barD) ∘ H  +  R(barD) ∘ R(barD)

* The last term is **discharged**: `tensorRightDegOne_comp` in
  `formal/GaloisForLFunctions/HTGeometry/CDGATensorDegOne.lean` shows that two degree-one maps on the
  right factor compose *without* a sign — the two Koszul signs are the same and cancel — so the term
  vanishes exactly by the inductive hypothesis `barD (k-1) (b+1) ∘ barD k b = 0`.
* **The shifted multiplication needed a sign, and did not have one.**  Working the cancellation out
  showed the construction as first built was wrong: with `μ(sa, sb) = s(ab)` the two bracketings of
  three factors are *equal*, so the two terms add rather than cancel and `d²` is not zero.  The
  correct shifted product carries the sign of the shifted degree of its first factor,
  `μ(sa, sb) = (-1)^{|sa|} s(ab)`; then the two bracketings differ by exactly `-(-1)^{|sa|}`, which
  is the sign the tail contributes.  `augIdealShiftMulOf` and **`augIdealShiftMulOf_assoc`** in
  `CDGABarMul.lean` carry the sign and prove that identity.  Keeping the target degree a parameter
  with an equation, rather than fixing it as `a + a' + 1`, is what lets associativity be stated at
  all — otherwise the two sides sit in `(p+q+1)+r+1+1` and `p+(q+r+1)+1+1`, which are equal but not
  definitionally so.
* The first three cancel against each other, and **the cancellation itself is now proved**.
  `formal/GaloisForLFunctions/HTGeometry/CDGABarCancel.lean` defines the two composites
  `barMulFirstTwo` and `barMulLastTwo` — multiply the first two of three adjacent shifted factors
  then the result with the third, against multiply the last two then the first with the result — and
  **`barMul_cancel`** proves that the first plus `(-1)^p` times the second is zero, for an arbitrary
  element of the triple tensor, not only for a pure one.  On a pure tensor it is
  `augIdealShiftMulOf_cancel`; the general case is three nested inductions, since the middle factors
  are themselves tensor products.

  The reindexing is built too:
  `formal/GaloisForLFunctions/HTGeometry/CDGABarSquare.lean` has `BarTriple`, the triples of degrees
  the two multiplications consume, the two reindexings `barTripleOfFirst` and `barTripleOfSecond`
  with both round trips, and `barTele`, the component of the argument both halves read with its
  three shifted factors separated.  `barHeadTermₗ` was also rebuilt to multiply straight into the
  target degree, so no transport along an identification of degrees appears anywhere.

  Both identifications are **proved**, in the same module: `barProj_comm_mul` — the projection of the
  innermost factor commutes past a multiplication of the outer two, which is the only thing
  separating the head applied twice from the first bracketing — then `barHead_first_comp` and
  `barHead_second_comp`.  The second needs no commutation at all: the tail multiplies exactly where
  the telescope's projections already are.  `barTriple_cancel` puts them together with
  `barMul_cancel`: every triple of degrees the two multiplications consume contributes one term to
  each half, both applied to the same component of the argument, and the two add to zero.

  `barHead_head_outer` expands the head-applied-twice half at one outer split into a sum of first
  bracketings over the splits of its first part.

`barHead_tail_outer` expands the other half the same way.  The tail's defining equation only applies
when the degree it reads is a successor, and that degree is a *sum* sitting in a dependent position;
neither `set` nor `rw` can move it, because the subtype's proof depends on it.  The case analysis
therefore goes on the summands — first on the trailing degree, then on the split's second part — and
each branch makes the sum a successor definitionally, so nothing has to be moved at all.

`barHead_sq_add` then reindexes the two double sums onto each other with `Finset.sum_nbij'`, using
the two triple bijections composed, and cancels them term by term with `barTriple_cancel`.
`barHead_sq` is the same as an identity of maps, and **`barD_two_sq` is `d² = 0` for the bar
differential on three factors** — the first case with content, since on two factors the tail is zero.

## Status of `d² = 0`

**Proved for three factors** (`barD_two_sq`), and every ingredient of the general statement is proved.
Writing the inductive step as `barD (k+1) = H_k + R(barD k)`, the square has four terms and each has
its reason:

| term | proved by |
|---|---|
| `H ∘ H` and `H ∘ R(H)` | `barHead_sq` — stated for an arbitrary coefficient family, so it applies at every `k` |
| `H ∘ R(R(barD))` and `R(barD) ∘ H` | `barHead_comm_tail_apply` in `CDGABarComm.lean` |
| `R(barD) ∘ R(barD)` | `tensorRightDegOne_comp` together with the inductive hypothesis |

`CDGABarComm.lean` builds the second of the two classical cancellations from scratch: `barMulTail`,
the map that multiplies the first two factors and acts on the third; `barMulTail_first` and
`barMulTail_second`, which show both orders compose to it; `barMulTail_cancel`, which cancels them
because the two Koszul signs differ by exactly one — the multiplication raises the degree of the slot
the outer sign reads; and `barHead_tailtail_term`, `barHead_tail_term`,
`barHead_comm_tail_apply`, which identify the two halves componentwise and cancel them.
`tensorRightDegOne_add_map` splits a tail into its own head and tail, and `barD_succ_split` and
`barTailFamily` fix the spelling the split needs.

What is left is the induction itself.  It is blocked on nothing mathematical: `(barPower (k+1)).carrier`
and `TensorCarrier S (barPower k).carrier` are *definitionally* equal but not syntactically so, and
Lean elaborates the two summands of the inductive step against the two different spellings, so the
`HAdd` instance for their sum is not found and the rewrite that splits the tail does not fire.  The
fix is to force one spelling through the whole step — `barTailFamily` does it for the tail; the head
and the outer differential need the same treatment.

Everything the statement quantifies over is defined, and one of the four terms is proved.
