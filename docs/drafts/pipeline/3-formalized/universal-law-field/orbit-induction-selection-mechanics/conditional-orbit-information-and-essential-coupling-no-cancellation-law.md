# Conditional-orbit information and essential-coupling no-cancellation law

- **ID:** ULF-OISM-3
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parents:** ULF-OISM-1 and ULF-OISM-2
- **Statement:** Correlated orbit formation cannot cancel information production while each fresh
  conditional law retains positive separation: path Jeffreys work is the exact sum of conditional
  innovations.  On the operator side, compact or Schatten cross-orbit couplings cannot cancel an
  induced essential class, alter its Calkin norm, or repair non-Fredholmness.  Any successful
  global repair must carry a noncompact opposite quotient class or force conditional innovations
  to become summable.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [ROUTE-INDEPENDENT]
  [CORRELATION-ROBUST INFORMATION PROPERNESS] [CALKIN REPAIR CLASSIFICATION]
  [GLOBAL COUPLING GATE] [LEAN-PROVED] [NOT RH]

## 1. Correlated path formation

Let `X_1,...,X_n` be standard Borel spaces and let `P_n,Q_n` be probability laws on
`X_1 x ... x X_n`.  Choose regular conditional laws

```text
P_i(. | x_<i),   Q_i(. | x_<i)
```

for the `i`-th coordinate given its past.  Define directed conditional innovations

```text
k_i^P = integral D_KL(P_i(.|h) || Q_i(.|h)) dP_<i(h),
k_i^Q = integral D_KL(Q_i(.|h) || P_i(.|h)) dQ_<i(h).
```

Extended value `+infinity` is allowed.

### Theorem 1.1 -- exact conditional-orbit conservation

The full path divergence decomposes exactly:

\[
 \boxed{
 D_{\rm KL}(P_n\Vert Q_n)=\sum_{i=1}^n k_i^P,
 \qquad
 D_{\rm KL}(Q_n\Vert P_n)=\sum_{i=1}^n k_i^Q.}
\tag{COI.1}
\]

Consequently

\[
 \boxed{
 J(P_n,Q_n)=\sum_{i=1}^n(k_i^P+k_i^Q).}
\tag{COI.2}
\]

#### Proof

Apply the relative-entropy chain rule to the split

```text
(X_1,...,X_n) = (X_1,...,X_(n-1)) x X_n.
```

It gives the divergence of the past plus expected conditional divergence of the final coordinate.
Iterate to the first coordinate.  The same argument with `P_n,Q_n` exchanged proves the reverse
identity.  Adding gives `(COI.2)`.  Standard Borelness supplies regular conditional laws; the
extended chain rule covers singular histories. QED.

### Corollary 1.2 -- correlation cannot cancel fresh information

If numbers `c_i>=0` satisfy

```text
k_i^P+k_i^Q >= c_i,
```

then

\[
 \boxed{J(P_n,Q_n)\ge\sum_{i=1}^n c_i.}
\tag{COI.3}
\]

Hence:

1. a uniform conditional gap `c_i>=c>0` gives `J(P_n,Q_n)>=nc`;
2. if `sum_i c_i=infinity`, cofinal path work diverges;
3. bounded cofinal path work forces summability of all actual conditional innovations.

Independence is therefore unnecessary for information properness.  Correlation can evade linear
amplification only by making later conditional distinctions decay; it cannot contribute a negative
KL cancellation.

## 2. Common recovery remains neutral on correlated histories

Let `M_n` be one Markov kernel from the full source path to an auxiliary recovery path, used
identically under `P_n` and `Q_n`.  Put

```text
Ptilde_n = P_n tensor M_n,
Qtilde_n = Q_n tensor M_n.
```

### Theorem 2.1 -- correlated common-recovery isometry

\[
 \boxed{
 D_{\rm KL}(\widetilde P_n\Vert\widetilde Q_n)
 =D_{\rm KL}(P_n\Vert Q_n),
 \qquad
 J(\widetilde P_n,\widetilde Q_n)=J(P_n,Q_n).}
\tag{COI.4}
\]

#### Proof

The split chain rule gives base divergence plus the expected conditional divergence
`D_KL(M_n(.|x)||M_n(.|x))=0`.  Repeat in the reverse direction. QED.

Thus neither correlation nor common recovery supplies the missing negative information current.
Every escape must occur by decay/summability of conditional innovations or by a genuinely lossy
observer whose hidden fibre term is retained elsewhere.

## 3. Essential operator coupling

Let `A:H->K` be a bounded operator between Hilbert spaces, and let `R:H->K` be compact.  Write
`q(A)` for the class modulo compact operators and

```text
||A||_ess = inf_C compact ||A-C||.
```

### Theorem 3.1 -- compact global repair is impossible

\[
 \boxed{
 q(A+R)=q(A),
 \qquad
 \|A+R\|_{\rm ess}=\|A\|_{\rm ess}.}
\tag{COI.5}
\]

Moreover:

1. `A+R` is compact exactly when `A` is compact;
2. `A+R` is Fredholm exactly when `A` is Fredholm;
3. when Fredholm, their indices agree.

#### Proof

The compact operators form a closed two-sided ideal, so `q(R)=0` and `(COI.5)` follows.  The first
item is immediate.  The second and third are Atkinson stability of Fredholmness and index under
compact perturbation; applying the same statement to `(A+R)+(-R)=A` gives both directions. QED.

### Corollary 3.2 -- induced essential defects require essential repairs

Let

```text
A = Ind_a(D)
```

be a weighted orbit induction with compact nonzero local block `D`.  If
`limsup_i |a_i| = alpha > 0`, ULF-OISM-2 gives

\[
 \|A\|_{\rm ess}=\alpha\|D\|>0.
\tag{COI.6}
\]

No compact, trace-class, Schatten, finite-rank, or norm-limit-of-finite-rank cross-orbit coupling
can make `A` compact or alter `(COI.6)`.  No such coupling can repair a non-Fredholm induced
formation.

If a bounded repair `R` does make `A+R` compact, then necessarily

\[
 \boxed{
 q(R)=-q(A),
 \qquad
 \|R\|_{\rm ess}\ge\|A\|_{\rm ess}.}
\tag{COI.7}
\]

The first identity follows by applying `q`; the norm bound follows from the quotient norm.  A
successful repair must therefore be globally essential and have at least the original essential
size.  “Small off-diagonal correction” is categorically the wrong class.

## 4. Positive completion cannot hide a compact repair

Let `A:H->K` be bounded and `R:H->K` compact.  Expanding the Gram difference gives

\[
 (A+R)^*(A+R)-A^*A=A^*R+R^*A+R^*R.
\tag{COI.8}
\]

Every term on the right is compact.  Hence

\[
 \boxed{
 q((A+R)^*(A+R))=q(A^*A).}
\tag{COI.9}
\]

For a homogeneous nonzero compact local block induced over an infinite orbit,

\[
 \|q(A^*A)\|=\|D\|^2.
\tag{COI.10}
\]

Thus positive Gram completion erases polar phase but does not make a compact cross-orbit repair
visible in the essential class.  Any cancellation must occur before positive completion through a
noncompact opposite Calkin class.

## 5. Joint no-cancellation theorem

### Theorem 5.1

Consider one source orbit represented simultaneously by:

1. correlated path pairs `(P_n,Q_n)`;
2. an induced operator defect `A=Ind_a(D)` with `D` compact nonzero;
3. one common recovery kernel on each finite history;
4. a compact cross-orbit operator correction `R`.

Assume

```text
sum_i (k_i^P+k_i^Q) = infinity,
limsup_i |a_i| > 0.
```

Then:

\[
 \boxed{
 J(\widetilde P_n,\widetilde Q_n)\longrightarrow\infty,
 \qquad
 \|A+R\|_{\rm ess}
 =\bigl(\limsup_i|a_i|\bigr)\|D\|>0.}
\tag{COI.11}
\]

No correlations, common recoveries, or compact cross-couplings can neutralize either global
obstruction.

#### Proof

The information conclusion is Theorems 1.1 and 2.1 plus monotone divergence of the conditional
innovation sum.  The operator conclusion is ULF-OISM-2 and Theorem 3.1. QED.

## 6. Consequence for field design

The next source mechanism has only two viable shapes:

1. **decay:** prove conditional information innovations are summable and orbit amplitudes tend to
   zero, accepting loss of uniform recovery/closed range; or
2. **essential cancellation:** construct a source-native noncompact cross-orbit coupling with
   exact quotient class `-q(A)` and a matching signed conditional-information transgression.

The first does not select neutrality.  The second is the genuine open field problem.  It cannot be
replaced by another finite-rank correction, trace-class counterterm, positive Gram, or common
recovery kernel.

## 7. Hostile scope

1. Conditional KL terms are nonnegative, but their size may decay through correlations; no uniform
   lower bound is automatic.
2. A noncompact off-diagonal operator can cancel an essential class.  This theorem says such a
   repair is necessary, not that it exists or is source-canonical.
3. Signed currents outside relative entropy may cancel.  They require a separate conservation law
   before positive completion.
4. Fredholm stability uses compact corrections; domain-changing unbounded perturbations are not
   covered.
5. No RH implication is claimed.  A literal source must produce the conditional lower bounds and
   essential operator class before specialization.

## 8. Lean status

Fully formalized, unconditionally: see the Lean certificate below.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.BoundedFredholmStability`, `GaloisForLFunctions.HTGeometry.ConditionalOrbitInformationRepair`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.BoundedFredholmStability` (reusable bounded Fredholm theory:
Grushin bordering, openness/local constancy of the index, finite-rank approximation of compacts, Riesz
theory for `1 + C`, Atkinson stability and index invariance under compact perturbation) and
`GaloisForLFunctions.HTGeometry.ConditionalOrbitInformationRepair` (the card).  Corpus inputs: mathlib
`klDiv_compProd_eq_add`, `klDiv_compProd_left`, `Measure.condKernel`, `Kernel.measurableSet_absolutelyContinuous`,
`compactOperator`; corpus `klDiv_compProd_right`, `rectEssentialNorm`, `rectEssentialNorm_weightedInduction`
(ULF-OISM-2), `gram_weightedInduction`, `IsBoundedFredholm`, `isCompactOperator_adjoint_rectangular`,
`isCompactOperator_of_memRectSchattenClass`.

| Claim | Lean declaration |
|-|-|
| path space `X₁ × ⋯ × X_n` of standard Borel coordinates; consistent laws; regular conditional laws `P_i(·|x_<i)` | `PathSpace`, `PathSpace.instStandardBorelSpace`, `IsConsistentPathLaw`, `pathConditional`, `path_disintegrate` |
| directed innovations `k_i^P = ∫ KL(P_i(·|h) ‖ Q_i(·|h)) dP_<i(h)`, extended value `∞` allowed | `pathInnovation`; extended chain term without absolute continuity `klDiv_compProd_eq_lintegral`, `pathInnovation_eq_klDiv` |
| Theorem 1.1, (COI.1) `KL(P_n‖Q_n) = Σ k_i^P` (and the reverse with `P,Q` exchanged) | `klDiv_path_eq_sum` (applied to `(P,Q)` and `(Q,P)`) |
| (COI.2) `J(P_n,Q_n) = Σ (k_i^P + k_i^Q)` | `pathJeffreys`, `pathJeffreys_eq_sum` |
| Corollary 1.2, (COI.3) `J ≥ Σ c_i` | `sum_le_pathJeffreys` |
| Corollary 1.2 (1) uniform gap ⇒ `J ≥ n c` | `nsmul_le_pathJeffreys` |
| Corollary 1.2 (2) `Σ c_i = ∞` ⇒ cofinal work diverges | `tendsto_pathJeffreys_top` |
| Corollary 1.2 (3) bounded work ⇒ summable innovations | `tsum_innovation_le_of_pathJeffreys_le`, `tsum_innovation_ne_top_of_pathJeffreys_le` |
| Theorem 2.1, (COI.4) common recovery `P̃ = P ⊗ M`: `KL` and `J` unchanged | `commonRecovery_pathDivergence` |
| §3 Calkin class `q(A)`, `‖A‖_ess = inf ‖A - C‖ = ‖q(A)‖` | `CalkinQuotient`, `calkinClass`, `calkinClass_eq_iff`, `calkinClass_eq_zero_iff`, `norm_calkinClass` |
| Theorem 3.1, (COI.5) `q(A+R) = q(A)`, `‖A+R‖_ess = ‖A‖_ess` | `calkinClass_add_compact`, `rectEssentialNorm_add_compact` |
| Theorem 3.1 (1)–(3): compactness, Fredholmness (both directions) and index preserved | `isCompactOperator_add_compact_iff`, `isFredholmOp_add_compact_iff`, `fredholmIndex_add_compact`, packaged `compactRepair_invariants`; Atkinson layer `IsFredholmOp.add_compact`, `isFredholmOp_one_add_compact`, `IsCompactOperator.exists_finiteRank_approx`, `IsFredholmOp.exists_stable`, `isFredholmOp_of_grushin`, `IsFredholmOp.exists_bordering` |
| Hilbert cokernel `(range)ᗮ` vs quotient cokernel (ULF-OISM-2's Fredholm notion) | `isBoundedFredholm_iff_isFredholmOp` |
| Corollary 3.2, (COI.6) `‖Ind_a(D) + R‖_ess = limsup|aᵢ|‖D‖ > 0`, never compact | `weightedInduction_add_compact_essential` |
| Corollary 3.2: trace-class, Schatten, finite-rank, norm-limit-of-finite-rank couplings | `compactRepair_invariants_of_memRectSchattenClass`, `isCompactOperator_of_finiteDimensional_range`, `isCompactOperator_of_tendsto_finiteRank` |
| Corollary 3.2: no compact coupling repairs a non-Fredholm induced formation | `not_isBoundedFredholm_weightedInduction_add_compact` |
| (COI.7) `A+R` compact ⇒ `q(R) = -q(A)`, `‖R‖_ess ≥ ‖A‖_ess` (proved with equality) | `calkinClass_repair`, `rectEssentialNorm_le_of_repair`; induced case `weightedInduction_repair` |
| (COI.8) `(A+R)*(A+R) - A*A = A*R + R*A + R*R` | `gram_add_sub_gram` |
| (COI.9) `q((A+R)*(A+R)) = q(A*A)` | `calkinClass_gram_add_compact` |
| (COI.10) homogeneous induced compact block over an infinite orbit: `‖q(A*A)‖ = ‖D‖²` (general constant modulus `c`: `c²‖D‖²`) | `tailSup_eq_of_norm_eq`, `norm_calkinClass_gram_weightedInduction`, `norm_calkinClass_gram_weightedInduction_homogeneous` |
| Theorem 5.1, (COI.11) `J(P̃_n, Q̃_n) → ∞` and `‖A+R‖_ess = limsup|aᵢ|‖D‖ > 0` | `conditionalOrbit_essentialCoupling_noCancellation` |

`limsup_i |a_i|` is the corpus `tailSup a` (infimum over finite sets of the supremum outside them).  §6
(field-design consequence) and §7 (hostile scope) carry no Lean obligation and are not claimed.

## Log

- 2026-10-04 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
