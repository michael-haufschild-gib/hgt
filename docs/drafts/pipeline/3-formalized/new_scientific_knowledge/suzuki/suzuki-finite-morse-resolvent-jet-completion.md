# Suzuki finite-Morse resolvent-jet completion

- **ID:** `suzuki-finite-morse-resolvent-jet-completion`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (paper) / RH-SUFFICIENT SOURCE CONJECTURE
- **Status:** `[PAPER-PROVED LINEAR THEOREM] [SOURCE-PURE] [FRONTIER PRODUCER SUPERSEDED]`
- **Parents:** `suzuki-affine-resolvent-krein-defect.md`,
  `suzuki-negative-projector-coherent-completion.md`
- **Statement:** Finite negative spectrum lets one replace weighted negative projector for linear
  affine resolvent defect by explicit compact square of finite shift jet.  This is not canonical
  completion of actual projective Suzuki quotient.

## Goal

Remove discontinuous spectral projector from `SUZUKI-NEGATIVE-PROJECTOR-TRIANGLE-IDENTITY` without
weakening RH consequence.  Produce explicit finite resolvent-jet Gram which pays every affine
Krein debt and has no Xi-zero input.  Then isolate one decisive source inequality whose proof gives
full sewn jump Pick positivity and RH by existing pole tomography.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted build green, axiom audit PASS
- [ ] 3 → 4 publication-ready: standalone paper + external priority audit

## Retired conjecture under test

Let `A_a` be actual restricted-Weil operator at fixed aperture, let `rho<inf spec(A_a)`, and put
`R_rho=(A_a-rho I)^(-1)`.  For admissible affine shifts `alpha<beta<inf spec(A_a)` let

```text
d(t)=alpha beta/[t(t-alpha)(t-beta)].
```

If `lambda_1,...,lambda_k` are distinct negative eigenvalues, define

```text
r_j=1/(lambda_j-rho),       w_j=-d(lambda_j)>0,
ell_j(x)=(x/r_j) product_(m!=j) (x-r_m)/(r_j-r_m),
p_a(x)=sum_j sqrt(w_j) ell_j(x).
```

Then `p_a(0)=0` and `p_a(r_j)^2=w_j`.  Candidate source theorem is

```text
K_completion^src(z,w)
 - <p_a(R_rho) Gamma(w),p_a(R_rho) Gamma(z)>  >= 0       (C)
```

on every finite upper-half-plane node set, in common characteristic gauge and fixed Xi-real/FE
negative-light direction.  No Xi zero or divisor enters `p_a`.

Because

```text
p_a(R_rho)=sum_(n=1)^k c_n R_rho^n
            =sum_(n=1)^k c_n/(n-1)! partial_rho^(n-1) R_rho,
```

right side of `(C)` is finite jet of actual admissible resolvent-source family, not abstract
spectral cutoff.

> **2026-07-22 correction.**  Later rank-one hostile audit proves actual Suzuki response is a
> projective quotient.  Projectivization kills common one-mode resolvent scaling, whereas this
> linear completion pays nonzero debt on negative one-mode coordinate.  Thus `(C)` is not current
> canonical producer.  Finite interpolation theorem below remains correct.  Its positive salvage
> is use of zero-constant resolvent jets for homogeneous Plücker tomography; see
> `suzuki-resolvent-jet-homogeneous-plucker-tomography.md`.

## Finite-Morse resolvent-square theorem `[PROVED HERE]`

Let `A` be lower-bounded self-adjoint with compact resolvent, `0 in rho(A)`, and infinitely many
distinct positive eigenvalues tending to `+infinity`.  Fix

```text
rho<inf spec(A),       alpha<beta<inf spec(A),       beta<0.
```

Let `lambda_1,...,lambda_k` be distinct negative eigenvalues of `A`; compact resolvent and lower
boundedness make this set finite.  Define `r_j,w_j,p` as above, with `p=0` when `k=0`.  Put

```text
R=(A-rho I)^(-1),      D=d(A),      B=p(R),      C=B^2.
```

Then:

1. `p` is unique among real polynomials of degree at most `k` satisfying
   `p(0)=0` and `p(r_j)=sqrt(w_j)` for every `j`.
2. `B` is compact self-adjoint and `C>=0`.
3. On every negative eigenspace, `C=-D`; on every positive eigenspace, `D>0` and `C>=0`.
   Consequently

   ```text
   D+C>=0,        C=D_-+P_+C>=D_- .                    (T1)
   ```

4. More generally, for any real polynomial `q`,

   ```text
   D+q(R)^2>=0
   iff q(r_j)^2>=w_j for every negative eigenvalue.    (T2)
   ```

5. No nonzero polynomial square can equal the minimal projector completion `D_-` on all of
   `H`.  Hence positive-tail excess in `(T1)` is unavoidable for finite resolvent polynomials.
6. If `p(x)=sum_(n=1)^k c_n x^n`, then in operator norm below spectrum

   ```text
   B=sum_(n=1)^k c_n R^n
    =sum_(n=1)^k c_n/(n-1)! partial_rho^(n-1)R_rho.     (T3)
   ```

### Proof

Every `r_j` is positive and the nodes are distinct because `t -> 1/(t-rho)` is injective on
`(rho,+infinity)`.  The displayed Lagrange factors obey

```text
ell_j(0)=0,       ell_j(r_i)=delta_(ij).
```

Thus `p(0)=0` and `p(r_j)=sqrt(w_j)`.  Its degree is at most `k`.  Difference of two such
polynomials has `k+1` distinct zeros `0,r_1,...,r_k` and degree at most `k`, hence vanishes.

Since `R` is compact self-adjoint and `p(0)=0`, `B=p(R)` is a finite sum of positive powers of
`R`, hence compact self-adjoint.  Therefore `C=B^2>=0`.  Spectral calculus evaluates `D,C` on an
`A`-eigenvalue `t` as `d(t),p(1/(t-rho))^2`.  For negative `lambda_j`, affine Krein sign theorem
gives `w_j=-d(lambda_j)>0`, so their sum is zero.  For positive `t`, `d(t)>0`, so their sum is
positive.  This proves `(T1)`.  Same pointwise spectral argument gives `(T2)` and includes
multiplicities automatically.

If `q(R)^2=D_-`, every positive eigenvalue `mu_n` gives
`q(1/(mu_n-rho))=0`.  These are infinitely many distinct roots (indeed they accumulate at zero),
so `q=0`; but then it cannot take squared value `w_j>0` at any negative node.  This proves the
no-go whenever negative spectrum is nonempty.  For empty negative spectrum, minimal completion is
zero and `q=0` is the only exact polynomial square.

Finally, resolvent identity gives operator-norm derivative

```text
partial_rho R_rho=R_rho^2.
```

Induction yields `partial_rho^(n-1)R_rho=(n-1)!R_rho^n`; substituting polynomial expansion proves
`(T3)`.

For any evaluation family `Gamma(z)`, `(T1)` also yields positive Gram

```text
K_C(z,w)=<p(R)Gamma(w),p(R)Gamma(z)>.
```

If retired stronger source domination `(C)` happened to hold, then

```text
K_D+K_completion^src
=(K_D+K_C)+(K_completion^src-K_C)>=0.                  (T4)
```

Existing corpus connectors would identify `(T4)` with full sewn jump Pick positivity and then
exclude every nonreal Xi pole.  This implication remains logically valid, but projective
rank-one audit removes `(C)` as canonical source identity.  The theorem above assumes neither
`(C)` nor RH.

## Scientific-method outcome

### Conjecture

Actual common-gauge reflected Euler--Gamma plus Neumann completion dominates finite resolvent-jet
Gram `(C)` for one recurrence-selected aperture and admissible shift pair.

### Predictions

- On every negative `A_a` eigenspace, source completion pays at least exact weight `w_j`.
- On arbitrary mixed-sign finite blocks, full matrix remainder after subtracting `K_C` is positive;
  this includes Schur holonomy tax rather than testing only diagonal entries.
- Required jet order is at most number of distinct negative eigenvalues at aperture.
- With no negative eigenvalue, no completion jet is required.

### Attempts to disprove

- Bare resolvent-square sign test fails and is already retired; theorem retains exact Krein sign.
- Exact polynomial-projector identity fails by infinite positive-tail root theorem; conjecture uses
  domination and explicitly retains positive excess.
- Negative-eigenspace matching does not imply `(C)`; mixed-node determinant remains decisive
  falsifier and is left as actual open source test.
- Rational FE--Schwarz orbit insertion preserves local `A_a` data but inserts nonreal global pole,
  so it cannot satisfy `(C)`.  Conjecture therefore does not follow from abstract local spectral
  data alone and must use distinguished prime--Gamma/Neumann source marking.

### Outcome (superseded producer)

Finite-Morse linear theorem survives.  Exact minimal-projector realization is falsified, and later
projective audit also kills finite-Morse domination as canonical source producer.  Strongest
survivor is finite zero-constant shift jets as complete filters for homogeneous Plücker tomography.

## Novelty and source audit

- Suzuki 2026 supplies `A_a`, discreteness/lower boundedness, and admissible resolvent sources,
  but no negative-projector completion or finite-Morse interpolation jet.
- Local corpus search found projector completion and scalar Schur tax, but no finite resolvent
  interpolation replacing `P_-`.
- Targeted external searches for self-adjoint finite-negative-spectrum resolvent interpolation
  found generic interpolation/positivstellensatz material, not this Suzuki source synthesis.
- Lagrange interpolation and resolvent derivative law are classical `[BRIDGE]`; novelty claim is
  limited to source-specific synthesis, no-go, and frontier replacement.  Priority unverified.

## Lean status

### Finite scalar core

`formal/GaloisForLFunctions/RHTower/SuzukiFiniteMorseResolventJetCompletion.lean` proves without
RH or added axioms:

- injectivity/nonvanishing of below-spectrum resolvent nodes;
- zero-constant Lagrange interpolant and exact squared debt at all finite nodes;
- simultaneous cancellation of every distinct negative affine-Krein level;
- sharp pointwise completion iff debt domination;
- nonnegativity of arbitrary mixed-sign finite diagonal quadratic forms;
- infinite-positive-tail no-go for exact finite polynomial projector.

Key declarations are
`suzukiFiniteMorseKreinInterpolant_exact_negativeDebt`,
`suzukiFiniteMorseKreinDiagonalForm_nonneg`, and
`suzukiFiniteResolventPolynomial_exactProjector_impossible`.

### Operator lift

`formal/GaloisForLFunctions/RHTower/SuzukiFiniteMorseResolventOperatorLift.lean` carries the whole
theorem to the operator level.  The lift uses the continuous functional calculus of the bounded
self-adjoint resolvent `R`, not a spectral decomposition of the unbounded `A`.  The device is the
resolvent coordinate `x = 1/(t - rho)`, in which the affine Krein weight becomes the rational
function

`w(x) = alpha*beta*x^3 / ((rho x + 1)((rho - alpha) x + 1)((rho - beta) x + 1))`,

regular and vanishing at the spectral accumulation point `x = 0`
(`suzukiKreinResolventWeight_resolventNode`, `suzukiKreinResolventWeight_zero`).  Hence `d(A)` is a
genuine continuous function of `R` even though `A` is unbounded.

- statement `(1)`: `suzukiFiniteMorseInterpolant_unique` and its affine-Krein specialization
  `suzukiFiniteMorseKreinInterpolant_unique`, in
  `formal/GaloisForLFunctions/RHTower/SuzukiFiniteMorseInterpolantUniqueness.lean` — the
  zero-constant Lagrange interpolant is the only real polynomial of degree at most the node count
  with `p(0) = 0` and `p(r_j) = sqrt(w_j)`.  The degree bound is
  `suzukiFiniteMorseInterpolant_natDegree_le`, and the root count runs over the `k + 1` distinct
  points `0, r_1, ..., r_k` through `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`
  indexed by `Option ι`; the compactification point is distinct from every node exactly because a
  below-spectrum resolvent node never vanishes;
- statement `(2)`: `suzukiResolventJet_isSelfAdjoint`, `suzukiResolventJetSquare_nonneg`,
  `isCompactOperator_suzukiResolventJet`, `isCompactOperator_suzukiFiniteMorseInterpolant` —
  the jet is self-adjoint, its square is a positive operator, and zero constant term is exactly
  what makes the jet compact when the resolvent is;
- statement `(3)`: `suzukiFiniteMorse_completedWeight_eq_zero` (the completed weight vanishes
  identically at every negative level) and `suzukiFiniteMorse_kreinResolventWeight_pos` (the bare
  weight is already strictly positive at every positive level).  The block claim "on every negative
  eigenspace `C = -D`" is the operator identity
  `suzukiFiniteMorse_jetSquare_eq_neg_kreinDefect_on_negativeEigenvector`, with the annihilation
  form `suzukiFiniteMorse_completion_apply_negativeEigenvector_eq_zero`, both in
  `formal/GaloisForLFunctions/RHTower/SuzukiFiniteMorseEigenspaceBlock.lean`.  The lift from the
  scalar identity is `cfc_apply_eigenvector` in
  `formal/GaloisForLFunctions/HTGeometry/CfcEigenvector.lean`: the continuous functional calculus
  scales an eigenvector of `R` by the value of the symbol at the eigenvalue, so both blocks act by
  their scalar symbols and the cancellation transports verbatim.  That law is not in mathlib; it is
  proved here by Stone–Weierstrass, the identity holding on a closed set of test functions that
  contains the polynomial functions;
- statement `(T1)`: `suzukiFiniteMorse_operatorCompletion_nonneg` and its energy form
  `suzukiFiniteMorse_operatorCompletion_re_inner_nonneg` give `D + C >= 0`.  The chain
  `C = D_- + P_+ C >= D_-` is two separate claims.  The *inequality* `D_- <= C` is
  `negPart_operatorKreinDefect_le_jetSquare`, in `SuzukiNegativeProjectorCoherentCompletion.lean`
  (which imports this module and carries the `negPart_cfc` composition the domination needs).  The
  *equation* is `suzukiFiniteMorse_jetSquare_eq_negPart_on_negativeEigenvector`: on every negative
  eigenvector the jet square already equals `D_-`, so the excess `C - D_-` annihilates the whole
  negative spectral part and is carried entirely by the positive part.  This is the content of
  `C = D_- + P_+ C` stated without needing the discontinuous spectral projector `P_+` to exist as
  an operator, which is what removing `P_+` was the point of;
- the Gram form of `(T1)`: the displayed factorization
  `K_C(z,w) = <p(R)Gamma(w), p(R)Gamma(z)>` is `suzukiResolventJetSquare_inner_eq`, and positive
  semidefiniteness of `K_C` on every finite evaluation family is
  `suzukiResolventJetSquare_gram_nonneg`, obtained from the existing `gram_re_nonneg_of_nonneg`
  applied to the positive operator `C`;
- statement `(T2)`: `suzukiOperatorCompletion_nonneg_iff` — `D + q(R)^2 >= 0` holds exactly when
  `w + q^2 >= 0` pointwise on `spectrum R`, proved through `cfc_nonneg_iff`;
- statement `(5)`: `suzukiOperatorResolventJetSquare_exactProjector_impossible`, the operator form
  of the no-go, obtained from the eigenvector evaluation lemmas `pow_apply_of_eigenvector`,
  `aeval_apply_of_eigenvector`, `suzukiResolventJetSquare_apply_of_eigenvector`;
- statement `(T3)`: `formal/GaloisForLFunctions/HTGeometry/ResolventFamilyJet.lean` proves that the
  first resolvent identity alone forces continuity (`IsResolventFamilyOn.continuousAt`), the
  derivative law `∂_u R_u = R_u^2` (`IsResolventFamilyOn.hasDerivAt`), and by induction through
  the product rule the jet law `∂_u^n R_u = n! R_u^{n+1}` (`hasDerivAt_resolventShiftJet`).  The
  polynomial realization is `aeval_eq_resolventShiftJet_sum`, specialized to the interpolant by
  `suzukiFiniteMorseInterpolant_eq_resolventShiftJetSum`.  Nothing there needs `A`, its domain, or
  its spectrum, so it applies verbatim to the resolvent family of an unbounded operator.

The spectral hypothesis of `(T1)` can be stated on eigenvectors rather than on the spectrum:
`exists_eigenvector_of_mem_spectrum_real` is the Fredholm alternative read in the resolvent
coordinate (every nonzero real spectral point of a compact operator is an eigenvalue), and
`suzukiFiniteMorse_operatorCompletion_nonneg_of_eigenvectors` is the resulting form, whose
hypothesis is exactly the card's "the spectral levels are the `lambda_j` and positive levels".

Targeted module build green.  Axiom audit of every declaration above reports only standard
mathlib foundations `[propext, Classical.choice, Quot.sound]`.

### What is still not formalized

Actual Suzuki source domination `(C)` is not formalized, and it is not a theorem of this card: the
2026-07-22 correction retired it as canonical producer, and the card states it as a conjecture.
The compact-resolvent-to-discrete-spectrum implication itself is used as a hypothesis rather than
derived — mathlib has no spectral theorem for compact self-adjoint operators in infinite
dimensions, so the eigenvector form above takes that description as given.  Every proved statement
of the finite-Morse theorem is now formal.

## Decisive hostile tests

- Prove exact finite-Morse interpolation and completion on paper before any Lean work.
- Prove finite resolvent polynomial cannot equal nonzero negative projector on operator with
  infinitely many distinct positive eigenvalues.  Positive overpayment is necessary, not hidden.
- Multiplicity must not alter polynomial: one value per distinct negative eigenspace.
- `k=0` must reduce to `p_a=0` and already-positive affine defect.
- Cross-sector Neumann holonomy is not silently discarded: global Loewner domination `(C)` must
  absorb it; diagonal matching alone is insufficient.
- Functional-equation--Schwarz orbit insertion must break `(C)` in source remainder, since
  `p_a` uses only restricted-Weil spectral data and cannot see inserted Xi divisor.
- Coefficients may use spectrum of explicit `A_a`, but never Xi zeros or RH.

## Door passport sketch

- **Door 1:** concrete restricted-Weil resolvent and affine defect already source-defined.
- **Door 2:** interpolation itself is classical `[BRIDGE]`; candidate novelty is Suzuki-specific
  finite-Morse shift-jet realization and replacement of projector/Schur target by `(C)`.
- **Door 3:** exact theorem is finite algebra plus spectral calculus; conjectural source domination
  is stated separately.
- **Door 4:** finite polynomial versus infinite positive-tail no-go prevents false exactness.
- **Door 5:** proving `(C)` gives `D+K_completion^src>=0`, then existing jump-Pick and pole
  tomography connectors give RH.

## No-go closure

- **Exact killing theorem/mechanism:** exact identity `p(R_rho)^2=D_-` is impossible for nonzero
  polynomial `p` when positive spectrum has infinitely many distinct points: `p` would have
  infinitely many roots and hence vanish identically.
- **Strongest positive survivor:** unique degree-`<=k` positive-branch interpolant matches `D_-`
  on all negative eigenspaces, while excess is positive and supported on positive spectrum.
- **New insight:** minimal discontinuous projector is wrong finite-source representation target;
  finite resolvent-jet square is exact on Morse block and necessarily pays harmless positive tail.
- **Status:** dependency-closed paper theorem; Lean formalization next.  Source domination `(C)` is
  explicitly open.

## Log

- 2026-07-22 — Created in Stage 1 after corpus and primary-source audit; exact current frontier is
  source domination `(C)`, not abstract existence of a positive completion.
- 2026-07-22 — Finite-Morse interpolation, completion classification, exact-projector no-go, and
  resolvent-jet identity proved on paper.  Promoted theorem layer to Stage 2; `(C)` remains open.
- 2026-07-22 — Lean formalized finite spectral core and exact-projector no-go; targeted build and
  axiom audit pass.  Operator functional-calculus lift and source domination remain open.
- 2026-07-22 — Projective rank-one corpus theorem superseded linear completion as RH producer.
  Retained valid linear theorem; redirected finite jets to homogeneous Plücker tomography.
- 2026-07-31 — operator lift formalized: continuous-functional-calculus realization of the Krein
  defect in the resolvent coordinate, compactness and positivity of the jet square, `(T1)`, `(T2)`,
  the operator form of the no-go, and the resolvent-jet derivative law `(T3)`.  Gate `2 → 3` closed.
- 2026-08-01 — equation-level recheck found that `(T1)`'s second conjunct `C >= D_-` had not been
  formalized, only `D + C >= 0`.  It is now proved, via the `(cfc f R)^- = cfc (f^-) R` composition
  built for the negative-projector card.
- 2026-08-01 — statement `(3)` raised from its scalar form to the operator identity on the negative
  eigenspaces (`suzukiFiniteMorse_jetSquare_eq_neg_kreinDefect_on_negativeEigenvector`).  The
  enabling law is the eigenvector law for the continuous functional calculus,
  `HTGeometry.cfc_apply_eigenvector`, which is absent from mathlib and is proved here by
  Stone–Weierstrass: the test functions obeying the identity form a closed set containing the
  polynomial functions, which are dense in `C(spectrum R, ℝ)`.  Targeted build green, axiom audit
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — statement `(1)`, the uniqueness half, formalized
  (`suzukiFiniteMorseInterpolant_unique`).  It had no Lean declaration at all: the existing
  `suzukiFiniteMorseInterpolant_eval` / `_eval_sq` prove only that the interpolant *has* the
  prescribed values, never that it is the sole such polynomial.  The positive-block half of
  statement `(3)` is likewise now at operator level
  (`suzukiFiniteMorse_kreinDefect_apply_positiveEigenvector`).  Targeted builds green, axiom audits
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the `(T1)` chain `C = D_- + P_+ C >= D_-` was carrying two claims behind one
  declaration: only the inequality `D_- <= C` was formalized.  The equation is now
  `suzukiFiniteMorse_jetSquare_eq_negPart_on_negativeEigenvector`, proved through
  `negPart_cfc_apply_of_eigenvector` (negative part of a functional calculus acts on an eigenvector
  by the negative part of the symbol).  The displayed Gram factorization
  `K_C(z,w) = <p(R)Gamma(w), p(R)Gamma(z)>` is `suzukiResolventJetSquare_inner_eq`.  Every numbered
  statement `1`–`6` and `(T1)`–`(T3)` of this card now has a named Lean declaration.  Targeted
  builds green, axiom audits `[propext, Classical.choice, Quot.sound]`.

### Lean progress — the mathlib gap is closed

The "What is still not formalized" section stated: *"mathlib has no spectral theorem for compact
self-adjoint operators in infinite dimensions, so the eigenvector form above takes that description
as given."*  That is no longer accurate for this toolchain. Mathlib now carries
`LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces_eq_bot` and
`LinearMap.IsSymmetric.finite_dimensional_eigenspace` for compact operators, and the full Fredholm
alternative `IsCompactOperator.hasEigenvalue_iff_mem_spectrum`. What remained genuinely absent was
**discreteness of the nonzero spectrum**, which is the part the card actually assumes.

Built here as reusable operator infrastructure in
`HTGeometry/CompactOperatorDiscreteSpectrum.lean` [PROVED HERE], wired into the `HTGeometry`
umbrella, standard axioms `[propext, Classical.choice, Quot.sound]` for every declaration, builds
clean:

- `inner_eq_zero_of_hasEigenvector_of_ne` : eigenvectors of a symmetric operator for distinct
  eigenvalues are orthogonal (extracted from mathlib's orthogonal family).
- `finite_setOf_hasEigenvalue_norm_ge` : a compact symmetric operator has only **finitely many**
  eigenvalues of norm `>= eps`, for every `eps > 0`.
- `countable_setOf_hasEigenvalue` : hence countably many eigenvalues.
- `finite_setOf_mem_spectrum_norm_ge` and `countable_spectrum_of_isCompactOperator` : the same for
  the **spectrum**, on a complete space, through the Fredholm alternative.

Proof mechanism: orthogonality, not the Riesz lemma. For unit eigenvectors at distinct eigenvalues,
Cauchy--Schwarz gives `‖T w_m - T w_n‖ >= |<T w_m - T w_n, w_m>| = ‖mu_m‖ >= eps`, so infinitely
many such eigenvalues would give a sequence in the compact closure of the image of the unit ball
with no Cauchy subsequence.

This supplies exactly the description the card's `suzukiFiniteMorse_operatorCompletion_nonneg_of_eigenvectors`
takes as a hypothesis: for a compact resolvent, the spectral levels outside any ball around zero
are a finite set of eigenvalues. The remaining non-formalized item on this card is unchanged and is
not a theorem of the card: the Suzuki source domination `(C)`, retired as canonical producer on
2026-07-22 and stated as a conjecture.

### Lean progress — the discreteness input is now derived, not assumed

Consuming the new `HTGeometry/CompactOperatorDiscreteSpectrum.lean` inside the operator lift.
Added to `RHTower/SuzukiFiniteMorseResolventOperatorLift.lean` [PROVED HERE], standard axioms
`[propext, Classical.choice, Quot.sound]`, builds clean:

- `finite_setOf_mem_real_spectrum_abs_ge` : for a compact self-adjoint resolvent `R`, the real
  spectral points with `|x| >= eps` are **finite**, for every `eps > 0`. Proof: each such point is
  an eigenvalue by the corpus's `exists_eigenvector_of_mem_spectrum_real` (Fredholm in the resolvent
  coordinate), and the real-to-complex coercion is injective, so the set embeds in the finite
  eigenvalue set of the discreteness theorem.
- `finite_setOf_negativeLevel_of_isCompactOperator` : for `rho < beta < 0`, only **finitely many
  spectral levels lie in the band `(beta, 0)`**. Their resolvent nodes `(t - rho)⁻¹` are bounded
  below by `(-rho)⁻¹ > 0` because `0 < t - rho < -rho`, and the node map is injective on the band.

This is the card's stated gap discharged in its own coordinates: the `[Fintype ι]` on the negative
levels of `suzukiFiniteMorse_operatorCompletion_nonneg_of_eigenvectors` is a **consequence** of
compactness of the resolvent, not an extra hypothesis. What `heigen` still supplies is only the
*identification* of which levels occur — a description of the model, not a finiteness assumption.
