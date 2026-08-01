# Suzuki wall-field anti-diagonal Gram lift

- **ID:** `suzuki-wall-field-antidiagonal-gram-lift`
- **Stage:** 2 — fully proved on paper
- **Type:** HERMITIAN LIFT / FE-REFLECTED FAR-SOURCE WELD / ROOTED-DEBT CONNECTOR
- **Scientific status:** `[PAPER-PROVED] [SOURCE-SPECIFIC]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:** `suzuki-critical-wall-field-square-root-weld.md`,
  `suzuki-marked-secant-midpoint-lorentz-completion.md`,
  `suzuki-wall-field-projective-density-separation-law.md`
- **RH used:** no
- **Computation used:** no

## Actual frontier attacked

Corpus has two exact pieces but no bridge between them:

1. marked affine-secant symmetric block owes sharp rooted rate `d^2` before it can be positive;
2. critical wall field has complex bilinear square equal to far delayed-hinge numerator.

Treating wall-field square as scalar Gram diagonal fails because it carries complex phase.  Treating
far hinge as independent positive atom also fails.  Open frontier is an FE-reflected Hermitian
carrier that preserves full far phase while exposing positive diagonal mass able to pay rooted debt.

## Theorem A: reflected stationary wall kernel `[PAPER-PROVED]`

For `n=p^(e+1)` and

```text
omega_e(t)=b_e exp(i t log(n)/2),
b_e^2=Lambda(n)/sqrt(n)>0,
```

define two-height kernel

```text
K_e(t,u)=omega_e(t) conjugate(omega_e(u)).
```

Exact laws are:

```text
conjugate(omega_e(-t)) = omega_e(t),
K_e(t,u) = Lambda(n)/sqrt(n) exp(i (t-u) log(n)/2),
K_e(t,t)  = Lambda(n)/sqrt(n),
K_e(t,-t) = Lambda(n)/sqrt(n) exp(i t log n),
```

and `conjugate(K_e(u,t))=K_e(t,u)`.

### Proof

Bare amplitude `b_e` is real and wall phase is `exp(i t log(n)/2)`.  Conjugating at `-t` changes
`-i(-t)` back to `it`, proving reflection.  Multiplication gives

```text
b_e^2 exp(i t log(n)/2) exp(-i u log(n)/2)
 = b_e^2 exp(i(t-u)log(n)/2).
```

Parent square-root weld gives `b_e^2=Lambda(n)/sqrt(n)`.  Set `u=t` and `u=-t` for diagonal and
anti-diagonal formulas.  Conjugating and swapping variables proves Hermitian symmetry.  No
division or limit is used.  Square-root weld also gives

```text
farJump_e(t)=-i K_e(t,-t)/t^2,
```

including full prime-power delay phase.

## Theorem B: arbitrary finite-packet positivity `[PAPER-PROVED]`

For heights `t_1,...,t_N`, matrix `M_ij=K_e(t_i,t_j)` is Gram matrix of conjugated wall features:

```text
M_ij = inner(conjugate(omega_e(t_i)), conjugate(omega_e(t_j))).
```

Consequently for every complex packet `c`,

```text
sum_(i,j) conjugate(c_i) M_ij c_j
 = |sum_i conjugate(c_i) omega_e(t_i)|^2 >= 0.
```

Thus every finite section is Hermitian positive semidefinite and rank at most one; nonzero
diagonal makes every nonempty section rank exactly one.

### Proof

Complex inner product is conjugate-linear in first slot, hence
`inner(conj omega_i,conj omega_j)=omega_i conj omega_j=M_ij`.  Gram positivity gives quadratic
identity and nonnegativity.  This proves finite-height claim, not all-prime summability.

## Theorem C: exact rooted-debt completion `[PAPER-PROVED]`

Let `S_(m,d)` be marked-secant symmetric Lorentz form and `b_e` bare wall amplitude.  Exact local
completion is

```text
S_(m,d)((b_e r,b_e s),(b_e r,b_e s)) + d^2 (b_e s)^2
  = Lambda(n)/sqrt(n) (r-m s)^2 >= 0.
```

This identifies positive wall-kernel diagonal as exact prime-power currency for sharp `d^2`
completion, while anti-diagonal retains full far phase.

### Proof

Parent midpoint theorem gives

```text
S_(m,d)((R,S),(R,S))+d^2 S^2=(R-mS)^2.
```

Substitute `(R,S)=(b_e r,b_e s)`, factor `b_e^2`, and use
`b_e^2=Lambda(n)/sqrt(n)>0`.  Right side is nonnegative.  Coefficient is exactly diagonal
`K_e(t,t)` and is independent of height, whereas far phase remains anti-diagonal.

## Hostile audit

1. **Reflection passed.**  Exact conjugation formula proved; anti-diagonal is wall-field bilinear
   square with no phase loss.
2. **Finite-packet PSD passed.**  Whole finite matrix identified with Gram, not only minors.
3. **Phase passed.**  Anti-diagonal retains `exp(i t log n)` exactly.
4. **Projective boundary retained.**  Common density cancels after normalized characteristic
   division; theorem lives in division-free determinant line.
5. **Mass test blocks naive globalization.**  Unrestricted all-prime diagonal mass diverges;
   theorem is prime-power local and finite-height-packet.  Global assembly needs compensation or
   renormalized summation.
6. **Positivity type separated.**  Anti-diagonal values need not be nonnegative.  PSD belongs to
   independent two-height kernel; reflected restriction is phase-bearing observable.
7. **Ward remains open.**  Local completion does not prove global compensation or RH.

Verdict: `SURVIVES HOSTILE ATTACK`.

## Representation correction

Prior obstruction said complex bilinear square `omega_e(t)^2` cannot be a norm square.  Correct,
but incomplete: it is not a Gram **diagonal**.  Exact lift is

```text
positive diagonal K_e(t,t) = rooted completion mass,
FE-reflected anti-diagonal K_e(t,-t) = far source phase.
```

One Hermitian block now carries both quantities without forcing either into wrong positivity type.

## Novelty audit

- Rank-one character kernels and Gram positivity are classical `[BRIDGE]`.
- Audited Suzuki source does not state wall-field lift above.
- Audited Livsic/determinantal sources support general projective representation only; they do not
  identify prime-power Gamma wall field, FE-reflected anti-diagonal, or exact `d^2` completion.
- Corpus search found square-root weld, projective density, and midpoint debt separately but no
  theorem joining positive diagonal and far anti-diagonal in one wall kernel.
- Candidate novelty is source-specific three-way weld, not general rank-one positivity.
  Independent priority audit remains required.

## Remaining RH core if successful

### `SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY` `[CONJECTURE]`

Construct actual division-free rectangular Ward kernel whose local prime-power blocks are `K_e`,
whose reflection anti-diagonal gives far hinge, and whose diagonal rooted coordinate pays marked
halfgap debt before projective division.  Prove compensated global kernel positive and identify its
Weil quadratic form.  This assembly—not local rank-one positivity—is RH-bearing step.

## Gates

- [x] actual corpus frontier identified
- [x] exact conjecture and falsifiers stated
- [x] paper proof
- [x] internal/external novelty audit
- [x] unconditional Lean formalization
- [ ] global reflected Ward assembly
- [ ] RH

### Lean progress — Theorem B's rank claim FORMALIZED

Audit of the numbered statements against `RHTower/SuzukiWallFieldAntidiagonalGramLift.lean`.
Theorem A (reflection, difference character, diagonal, anti-diagonal, Hermitian symmetry, far-jump)
and Theorem C (rooted completion identity and its nonnegativity) each had a declaration. Theorem B
did not: `..._posSemidef` proved positive semidefiniteness through `Matrix.posSemidef_gram`, but the
card's two further assertions — the **explicit packet square** `(83)` and **rank at most one, rank
exactly one on a nonempty section** — had none. Both are now proved, [PROVED HERE], standard axioms
`[propext, Classical.choice, Quot.sound]`, no new warnings:

- `suzukiCriticalEntryWallBareAmplitude_pos` : `b_e > 0` (its square is the strictly positive
  far-hinge weight; the earlier corpus lemma covered only `e = 0`).
- `suzukiCriticalWallField_ne_zero` : `omega_e(t) ≠ 0` — positive amplitude times a nonvanishing
  exponential.
- `suzukiCriticalWallFieldGramMatrix_eq_vecMulVec` : the finite section is the outer product
  `omega ⊗ conj omega`.
- `suzukiCriticalWallFieldGramMatrix_rank_le_one` : rank ≤ 1, via `Matrix.rank_vecMulVec_le`.
- `suzukiCriticalWallFieldGramMatrix_dotProduct_mulVec` : `star c ⬝ᵥ M *ᵥ c =
  ‖∑ᵢ conj(cᵢ) omega_e(tᵢ)‖²` — the card's displayed quadratic identity, from which PSD is
  immediate (proof: double-sum expansion, `Finset.sum_mul_sum` factorization, `Complex.mul_conj'`).
- `suzukiCriticalWallFieldGramMatrix_rank_eq_one` : for `N > 0` the rank is exactly one — the range
  of `mulVecLin` is not `⊥` because the diagonal entry `omega_e(t₀) * conj omega_e(t₀)` is nonzero.

This is again the scalar-law-vs-operator-claim pattern: the per-vector positivity was formalized
and the matrix-level rank quantification was not. Gate 2 → 3 now holds with the rank claim included.
