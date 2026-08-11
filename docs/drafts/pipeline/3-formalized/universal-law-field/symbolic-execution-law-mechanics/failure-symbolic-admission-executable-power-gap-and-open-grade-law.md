# Failure symbolic admission, executable-power gap, and open-grade law

- **ID:** ULF-SELM-1
- **Stage:** 3-formalized
- **Type:** THEOREM (paper; Lean target below)
- **Source:** `../../../1-in-progress/universal-law-field/symbolic-execution-law-mechanics/symbolic-execution-law-mechanics-field-programme.md`
- **Statement:** Weighted execution always implies failure-kernel-local admission; the one-kernel
  system has no gap, while the triangle has a symbolic-but-nonexecutable repair in every positive
  even grade, all sharing one positive normalized observer and one closed parity observation while
  exact grade escapes.

## 1. Setup

Let `I` be a finite set and let `H` be a finite family of finite subsets of `I`.  Think of each
`K in H` as one inclusion-minimal failure kernel.  A **weight** is a function

\[
 a:I\longrightarrow\mathbb N.
\]

For `m in N`, define symbolic or local admission by

\[
 \operatorname{Local}_H(m,a)
 \quad\Longleftrightarrow\quad
 m\le \sum_{i\in K}a_i\qquad\text{for every }K\in H.
 \tag{SE1.1}
\]

Define executable admission by

\[
 \operatorname{Exec}_H(m,a)
 \quad\Longleftrightarrow\quad
 \exists (b_j)_{j\in\operatorname{Fin}(m)}:
 \begin{cases}
   \operatorname{Local}_H(1,b_j)&\text{for every }j,\\
   \sum_j b_j(i)\le a_i&\text{for every }i.
 \end{cases}
 \tag{SE1.2}
\]

The coordinate slack in `(SE1.2)` represents multiplication by an arbitrary surplus monomial.
Thus for a clutter cover ideal, `(SE1.1)` is the exponent condition for the symbolic/intersection
power and `(SE1.2)` is the exponent condition for the ordinary power.  The theorem below is stated
purely in the exponent language and requires no polynomial-ring infrastructure.

## 2. General execution law

### Theorem 2.1 -- executable implies local

For every finite `I`, failure family `H`, grade `m`, and weight `a`,

\[
 \operatorname{Exec}_H(m,a)\Longrightarrow\operatorname{Local}_H(m,a).
 \tag{SE1.3}
\]

#### Proof

Choose grade-one pieces `b_j` as in `(SE1.2)` and fix `K in H`.  Since every `b_j` is locally
admitted at grade one,

\[
 1\le\sum_{i\in K}b_j(i).
\]

Sum this inequality over the `m` indices `j`, interchange the two finite sums, and use coordinate
domination:

\[
 m=\sum_j1
 \le\sum_j\sum_{i\in K}b_j(i)
 =\sum_{i\in K}\sum_jb_j(i)
 \le\sum_{i\in K}a_i.
\]

This is `(SE1.1)`.  QED.

## 3. A sharp gap-free calibration

Let `I` contain one point `star` and let `H_unit={{star}}`.

### Theorem 3.1 -- one kernel has exact symbolic execution

For every grade `m` and weight `a`,

\[
 \operatorname{Local}_{H_{\mathrm{unit}}}(m,a)
 \Longleftrightarrow
 \operatorname{Exec}_{H_{\mathrm{unit}}}(m,a).
 \tag{SE1.4}
\]

#### Proof

The reverse implication is Theorem 2.1.  For the forward implication, local admission says
`m<=a(star)`.  For every `j in Fin(m)`, take the grade-one piece `b_j(star)=1`.  It is locally
admitted because its weight on the only kernel is one, and the sum of all pieces at `star` is
exactly `m<=a(star)`.  Hence `(SE1.2)` holds.  QED.

This example proves that a symbolic--execution gap is interaction data, not an artifact of the
definitions.

## 4. Triangle collective defect

Set `I=Fin(3)` and

\[
 H_\triangle=\{\{0,1\},\{1,2\},\{0,2\}\}.
 \tag{SE1.5}
\]

For `n in N`, define the constant weight

\[
 a_n(0)=a_n(1)=a_n(2)=n.
 \tag{SE1.6}
\]

### Lemma 4.1 -- every grade-one triangle repair costs at least two

If `Local_triangle(1,b)`, then

\[
 b(0)+b(1)+b(2)\ge2.
 \tag{SE1.7}
\]

#### Proof

The three kernel inequalities are

\[
 b_0+b_1\ge1,\qquad b_1+b_2\ge1,\qquad b_0+b_2\ge1.
\]

Adding gives `2(b_0+b_1+b_2)>=3`.  Since the total is integral, it is at least two.  QED.

### Theorem 4.2 -- persistent symbolic--ordinary gap

For every `n>0`,

\[
 \operatorname{Local}_{H_\triangle}(2n,a_n)
 \quad\text{and}\quad
 \neg\operatorname{Exec}_{H_\triangle}(2n,a_n).
 \tag{SE1.8}
\]

#### Proof

Every triangle kernel has two vertices, so its `a_n`-weight is `n+n=2n`.  This proves local
admission.

Suppose an executable decomposition `(b_j)_{j in Fin(2n)}` existed.  By Lemma 4.1, every piece has
total weight at least two.  Hence

\[
 4n=\sum_{j\in\operatorname{Fin}(2n)}2
 \le\sum_j\sum_{i\in\operatorname{Fin}(3)}b_j(i).
 \tag{SE1.9}
\]

Interchanging sums and using coordinate domination gives

\[
 \sum_j\sum_i b_j(i)
 =\sum_i\sum_jb_j(i)
 \le\sum_i a_n(i)=3n.
 \tag{SE1.10}
\]

Thus `4n<=3n`, impossible for `n>0`.  QED.

For the classical triangle cover ideal

\[
 J=(x_0x_1,x_1x_2,x_0x_2),
\]

the exponent statement reads

\[
 (x_0x_1x_2)^n\in J^{(2n)}\setminus J^{2n}.
 \tag{SE1.11}
\]

Equation `(SE1.11)` is an interpretation of the proved exponent theorem, not an additional
dependency of it.

## 5. Positive observer closure and open grade

For `n>0`, observe only the normalized rational profile and grade parity:

\[
 \mathcal O(n)=
 \left(\left(\frac{a_n(i)}{2n}\right)_{i\in\operatorname{Fin}(3)},
 [2n]_2\right).
 \tag{SE1.12}
\]

### Theorem 5.1 -- closed relaxed observation, open execution history

For every `n>0`,

\[
 \mathcal O(n)=((1/2,1/2,1/2),0),
 \tag{SE1.13}
\]

yet `a_n` is not executable at its marked grade `2n`.  Moreover the exact grades are unbounded:

\[
 \forall N\in\mathbb N\ \exists n>0:\quad N<2n.
 \tag{SE1.14}
\]

#### Proof

For `n>0`, cancellation in `Q` gives `n/(2n)=1/2` in every coordinate, and every even number has
zero class modulo two.  Nonexecution is Theorem 4.2.  For `(SE1.14)`, choose `n=N+1`; then
`N<2(N+1)`.  QED.

Thus one fixed positive observer state and one closed parity observer can hide an unbounded graded
family of locally legal but nonexecutable histories.  This is an exact calibration of
“closed observer projection with open lifted history.”  No dynamical recurrence theorem is
claimed.

## 6. Mechanism consequences

1. **Local legality and execution are different compositions.**  Theorem 2.1 gives only the
   inclusion `Exec subset Local`; reversing it is an integrality/effectivity theorem.
2. **Positive relaxation can be permanently non-effective.**  Clearing every denominator of the
   constant profile `(1/2,1/2,1/2)` produces the whole family `(SE1.8)`, never an executable repair
   at matching grade.
3. **Persistent grade is not primitive complexity.**  The classical triangle vertex-cover algebra
   is generated in degree two; the family is repeated low-degree defect, not unbounded primitive
   arity and not hypertranscendence.
4. **Parity closure loses work.**  Grade modulo two closes identically while exact grade escapes.
5. **Effectivity requires structure.**  The one-kernel system has equality, while the triangle
   fails.  The missing condition is interaction rigidity such as integer decomposition,
   unimodularity, or MFMC—not another scalar invariant.

## 7. Hostile scope

1. The theorem concerns finite failure families and nonnegative integral weights.
2. It does not construct failure kernels from any arithmetic source; ULF-FKT-1 supplies only the
   finite abstract kernelization law.
3. It does not prove a symbolic-power theorem for arbitrary ideals.  Polynomial terminology is a
   dictionary for squarefree cover ideals.
4. It does not identify persistent defect with hypertranscendence, curvature, physics, or RH.
5. The normalized observer in Section 5 is deliberately lossy and does not claim every positive
   observer behaves this way.
6. No reflexive update from primitive defect to a new legal context is built here.
7. Finite squarefree symbolic Rees algebras are classically finitely generated.  Any cofinal or
   differential nonfinite-generation claim needs a separate theorem.

## 8. Parent boundary

Weighted covers and symbolic vertex-cover algebras are classical:

- Herzog--Hibi--Trung, <https://arxiv.org/abs/math/0512423>;
- Herzog--Hibi--Trung, <https://arxiv.org/abs/math/0703577>;
- Gu--Ha--O'Rourke--Skelton, <https://arxiv.org/abs/1805.03428>.

The exact contribution here is the dependency-closed Universal Law Field calibration linking:

\[
 \text{failure kernels}
 \to\text{symbolic local admission}
 \to\text{ordinary execution}
 \to\text{positive observer closure/open grade}.
\]

No external priority claim is made.

## 9. Lean certification

Formalized in

`formal/GaloisForLFunctions/HTGeometry/ConstitutiveSymbolicExecutionGap.lean`

with no project axioms, `sorry`, `admit`, `opaque`, `unsafe`, or computation-based proof.  The
module certifies:

1. `WeightedLocalRepair` and `WeightedExecutableRepair`;
2. executable implies local;
3. exact one-kernel equality;
4. triangle grade-one cost lower bound;
5. triangle local admission and nonexecution for every `n>0`;
6. constant normalized rational/parity observer and unbounded grade;
7. one closed capstone imported by `HTGeometry.UniversalLawField`.

Direct foreground elaboration passes.  Axiom prints for the principal implication, one-kernel
classification, triangle nonexecution, observer constancy, and closed capstone report only
`propext`, `Classical.choice`, and `Quot.sound`.  The module is imported by
`HTGeometry.UniversalLawField`; its final foreground umbrella build passes with 11,599 jobs.
Repository lint reaches the target without a target error; its nonzero global exit is caused only
by pre-existing unreachable modules in unrelated `RHTower` and `HTGeometry` work.

## Log

- 2026-08-10 — paper proof closed after the expanded frontier audit and external symbolic-Rees
  collision check.
- 2026-08-10 — Lean certification closed; direct elaboration, axiom audit, target lint, and final
  Universal Law Field umbrella build pass.
- 2026-08-11 -- Lean surface audited complete against the card; promoted to stage 3.
