# Markovian return recovery and complexity reflection law

- **ID:** `markovian-return-recovery-complexity-reflection-law`
- **Stage:** 3 -- formalized in Lean 4
- **Type:** theorem / open-system recurrence rigidity / robust circuit incidence
- **Parent:** `autonomous-return-complexity-reflection-law.md`
- **Status:** `[LEAN-PROVED] [FRONTIER ADVANCE] [CLASSICAL CORE] [EXTERNAL PRIORITY OPEN]`
- **Date:** 2026-08-13

## Public sentence

A full autonomous Markovian quantum channel cannot return without refunding every earlier loss.
An approximate full-channel return supplies an explicit recovery channel at every intermediate time
and reflects every unitary-circuit complexity shell across the return.  An exact return forces the
entire semigroup to be unitary: genuine dissipation and exact full-channel recurrence are mutually
exclusive.

## Setup

Let `K=C^D`, and let `(Lambda_t)_(t>=0)` be a quantum dynamical semigroup on `End(K)`:

\[
 \Lambda_0=\operatorname{id},
 \qquad
 \Lambda_{s+t}=\Lambda_s\circ\Lambda_t,
 \tag{1}
\]

where every `Lambda_t` is completely positive and trace preserving.  Continuity is not needed for
the quantitative statements below.

Use unhalved diamond distance

\[
 d_\diamond(\Phi,\Psi)=\|\Phi-\Psi\|_\diamond.             \tag{2}
\]

Fix a proposed full-channel return time `R>0` and define

\[
 \delta_R=d_\diamond(\Lambda_R,\operatorname{id}).         \tag{3}
\]

Let `G` be a finite inverse-closed dictionary of unitary channels.  For a word `w`, write
`mathcal W_w` for its unitary channel and define

\[
 C_\epsilon^\diamond(\Phi)
 =\min\{|w|:d_\diamond(\mathcal W_w,\Phi)\le\epsilon\}.     \tag{4}
\]

For each exact length `ell`, define normalized circuit incidence

\[
 I_{\ell,\epsilon}^\diamond(\Phi)
 ={1\over |G|^\ell}
 \left|\{w\in G^\ell:
 d_\diamond(\mathcal W_w,\Phi)\le\epsilon\}\right|.       \tag{5}
\]

## Theorem A -- every intermediate channel has the return segment as a recovery

For every `0<=t<=R`,

\[
 \boxed{
 \Lambda_{R-t}\circ\Lambda_t
 =\Lambda_t\circ\Lambda_{R-t}=\Lambda_R,}                 \tag{6}
\]

and hence

\[
 \boxed{
 \|\Lambda_{R-t}\circ\Lambda_t-\operatorname{id}\|_\diamond
 =\delta_R.}                                               \tag{7}
\]

Thus `Lambda_(R-t)` is one explicit `delta_R`-recovery channel for `Lambda_t`, simultaneously at
every intermediate time.

Moreover, for every operator `X` on `K` tensored with an arbitrary ancilla,

\[
 \boxed{
 \|(\Lambda_t\otimes\operatorname{id})(X)\|_1
 \ge (1-\delta_R)\|X\|_1.}                               \tag{8}
\]

In particular, an approximate full-channel return permits at most `delta_R` relative loss of any
ancilla-assisted trace-distance distinguishability anywhere in the return cycle.

### Proof

Equation (6) is the semigroup law.  Equation (7) is (3).  Complete positivity and trace
preservation make `Lambda_(R-t)` completely contractive in trace norm, so

\[
 \|(\Lambda_t\otimes\operatorname{id})(X)\|_1
 \ge\|(\Lambda_R\otimes\operatorname{id})(X)\|_1.
\]

The reverse triangle inequality and (3) give

\[
 \|(\Lambda_R\otimes\operatorname{id})(X)\|_1
 \ge\|X\|_1-
 \|((\Lambda_R-\operatorname{id})\otimes\operatorname{id})(X)\|_1
 \ge(1-\delta_R)\|X\|_1.
\]

This proves (8).  QED.

## Theorem B -- robust circuit-complexity reflection for open dynamics

For every `0<=t<=R` and every `epsilon>=0`,

\[
 \boxed{
 C_{\epsilon+\delta_R}^\diamond(\Lambda_{R-t})
 \le C_\epsilon^\diamond(\Lambda_t),
 \qquad
 C_{\epsilon+\delta_R}^\diamond(\Lambda_t)
 \le C_\epsilon^\diamond(\Lambda_{R-t}).}                \tag{9}
\]

At every exact word length,

\[
 \boxed{
 I_{\ell,\epsilon}^\diamond(\Lambda_t)
 \le I_{\ell,\epsilon+\delta_R}^\diamond(\Lambda_{R-t}),
 \qquad
 I_{\ell,\epsilon}^\diamond(\Lambda_{R-t})
 \le I_{\ell,\epsilon+\delta_R}^\diamond(\Lambda_t).}  \tag{10}
\]

Therefore every nonnegative length partition function

\[
 Z_{b,\epsilon}^\diamond(\Phi)
 =\sum_{\ell\ge0}b_\ell I_{\ell,\epsilon}^\diamond(\Phi) \tag{11}
\]

obeys the same two radius-interlacing inequalities.  This includes the geometric Abel profile
`b_ell=a^ell`.

### Proof

Suppose a unitary word channel `mathcal W` satisfies

\[
 \|\mathcal W-\Lambda_t\|_\diamond\le\epsilon.
\]

Composition by a channel is diamond-contracting, so (6) gives

\[
 \begin{aligned}
 \|\Lambda_{R-t}\circ\mathcal W-\operatorname{id}\|_\diamond
 &\le
 \|\Lambda_{R-t}\circ\mathcal W-
   \Lambda_{R-t}\circ\Lambda_t\|_\diamond
 +\|\Lambda_R-\operatorname{id}\|_\diamond\\
 &\le\epsilon+\delta_R.                                  \tag{12}
 \end{aligned}
\]

Postcomposition by the inverse unitary channel is a diamond isometry.  Applying it to both maps in
(12) yields

\[
 \|\Lambda_{R-t}-\mathcal W^{-1}\|_\diamond
 \le\epsilon+\delta_R.                                  \tag{13}
\]

Word inversion is a length-preserving bijection because the dictionary is inverse closed.  Thus
every word counted near `Lambda_t` injects, by inversion, into the enlarged shell near
`Lambda_(R-t)`.  This proves the first inequalities in (9)--(10).  Interchange `t` and `R-t` for
the second inequalities.  Nonnegative summation proves the partition-function statement.  QED.

## Corollary C -- exact Markovian recurrence is unitary and palindromic

If `delta_R=0`, then for every `0<=t<=R`, `Lambda_(R-t)` is a CPTP two-sided inverse of `Lambda_t`.
A finite-dimensional CPTP automorphism with a CPTP inverse is a unitary conjugation.  Consequently,
for every `t` there is a unitary `U_t`, unique up to phase, such that

\[
 \Lambda_t(X)=U_tXU_t^*,
 \qquad
 \Lambda_{t+R}=\Lambda_t.                                 \tag{14}
\]

Thus the channels themselves form a periodic one-parameter group of unitary conjugations.  Under
the standard continuity premise for a quantum dynamical semigroup, their projective unitary
representatives have the usual continuous Hamiltonian lift.

Equations (9)--(11) become exact equalities under `t mapsto R-t`.  Hence no genuinely dissipative
finite-dimensional quantum dynamical semigroup has a nonzero exact recurrence of the full channel.

The classification of CPTP maps with positive/CPTP inverse as unitary channels is classical.  The
new candidate composition is the simultaneous recovery law (7)--(8) with shellwise robust circuit
reflection (9)--(11); priority remains open.

## Conjecture--failure--proof loop

### C0 -- an open Markovian channel can dissipate and later exactly recur

Label: `[FALSIFIED]` by Corollary C.

Exact return makes every earlier segment CPTP-invertible by the remaining segment.  The semigroup
is unitary on the full channel space.

### C1 -- approximate recurrence constrains only the endpoint

Label: `[FALSIFIED]` by Theorem A.

The remaining physical evolution is a uniform recovery map at every intermediate time, and (8)
forbids larger distinguishability loss anywhere in the cycle.

### C2 -- open dynamics destroys recurrence reflection of complexity

Label: `[FALSIFIED FOR UNITARY-CIRCUIT COST]` by Theorem B.

The intermediate channels need not themselves be assumed unitary.  Semigroup composition,
contractivity, and inverse words suffice for robust reflection.

### C3 -- Markovian recurrence reflection proves Brown growth

Label: `[FALSIFIED]`.

The law transfers whatever complexity is present between the two sides of a return.  It neither
forces first-cut growth nor supplies a recurrence time.

## Hostile audit

1. **Unconditional scope:** every finite-dimensional CPTP semigroup, every full-channel diamond
   return defect, every inverse-closed unitary gate dictionary.
2. **No hidden reversibility premise:** approximate Theorems A--B do not assume any `Lambda_t` is
   unitary or invertible.
3. **Full-channel qualification is load-bearing:** recurrence of one stationary state does not make
   an open channel reversible.  The norm in (3) quantifies recurrence of the entire channel.
4. **Markovian qualification is load-bearing:** non-Markovian dynamics can lose information to an
   environment and later receive it back; the system maps need not form a CPTP semigroup.
5. **No Brown ramp:** first-cut undistortion for ordinary static local Hamiltonians is unchanged.
6. **Novelty:** CPTP-inverse rigidity and reversible/decoherence-free semigroup structure are
   classical.  Targeted searches did not locate the quantitative all-intermediate recovery plus
   shellwise circuit-reflection package.  This is separation evidence only, not priority proof.
7. **Physics meaning:** an observed full-channel recurrence distinguishes reversible memory from
   Markovian dissipation.  No black-hole, gravity, or thermodynamic-limit claim is made.

## External boundary

- Nayak and Sen, *Invertible Quantum Operations and Perfect Encryption of Quantum States*
  (`quant-ph/0605041`), characterize quantum operations with quantum-operation inverses.  This is
  the classical input behind Corollary C.
- Quantum-dynamical-semigroup/decoherence theory classically splits reversible and stable sectors.
  The present theorem does not claim that decomposition as new.
- Research on non-Markovian information backflow concerns families outside the semigroup premise;
  it is not contradicted by Corollary C.

## Formalization status

Lean is deliberately deferred during the shared corpus refactor.  No Lean process was started.
Later formalization should separate abstract contractive semigroup recovery, diamond-norm channel
composition, inverse-word shell injection, and the imported finite-dimensional CPTP-inverse
classification.

## Lean progress -- Theorems A and B, the metric core

`formal/GaloisForLFunctions/HTGeometry/ReturnRecoveryReflection.lean` (new, umbrella-wired,
axiom-clean) proves the reflection content of Theorems A and B in the exact generality the paper
proof uses: a monoid with a metric in which left composition contracts and right composition by a
dictionary element is an isometry.  Diamond distance on channels is one instance, but no
channel-specific structure is needed and none is assumed.

| Card item | Declaration |
|---|---|
| left composition by a channel contracts the metric -- complete positivity plus trace preservation | `LeftContracting` |
| **`(13)`**: `‖S − G⁻¹‖ ≤ ε + δ` whenever `‖S·T − id‖ ≤ δ` and `‖G − T‖ ≤ ε` | `dist_reflect_le`, `exists_reflected_word` |
| **`(9)`**: hence the two complexities interlace at radius shift `δ` | same, applied to a minimising word |
| **`(10)`**: at each exact length the reflection is injective, so the incidence counts interlace | `card_reflect_le` |
| **`(8)`**: if the return factors through a norm contraction, every intermediate stage keeps at least `1 − δ` of any norm | `norm_le_of_contraction_return` |

`(11)`, the partition-function form, is `card_reflect_le` summed against any nonnegative weight, so
it needs no separate argument.

### What remains

`(6)` itself -- the semigroup law `Λ_{R−t} ∘ Λ_t = Λ_R` -- is a hypothesis of the theorems above
rather than a proved input, because it *is* the definition of a dynamical semigroup; and the
identification of the abstract metric monoid with completely positive trace-preserving maps under
diamond distance, together with the exact-return rigidity statement that a genuinely dissipative
semigroup cannot return exactly.  The latter needs a Lean theory of the diamond norm, which is
absent from mathlib and from this corpus.

## Lean progress -- the card is now closed (2026-08-19)

The two items listed above as remaining are done.  `(6)` is no longer a hypothesis but a theorem
about a `DynamicalSemigroup`, and the abstract metric monoid is now *identified* with completely
positive trace-preserving maps under the diamond distance: the diamond distance is constructed,
proved to be a metric, and proved to satisfy exactly the two hypotheses the reflection law
consumes.  Corollary C is proved outright, so no classical input is imported.

### The trace-norm layer

| Card item | Declaration | Module |
|---|---|---|
| the nuclear norm of a Hermitian matrix is `∑\|λ_i\|` | `finiteMatrixNuclearNorm_isHermitian` | `HTGeometry/HermitianTraceNorm` |
| the trace of a functional-calculus image | `trace_cfc_re`, `trace_re_eq_sum_eigenvalues` | same |
| a positive matrix has nuclear norm its trace | `finiteMatrixNuclearNorm_posSemidef` | same |
| **duality**: a Hermitian contraction pairs at most as strongly as the nuclear norm | `IsHermContraction`, `re_trace_mul_le_nuclearNorm` | same |
| **duality, attainment**: the sign of the spectrum realises it | `exists_isHermContraction_re_trace_eq` | same |
| **the triangle inequality on Hermitian matrices** | `finiteMatrixNuclearNorm_add_le` | same |
| the Jordan decomposition `A = A₊ − A₋` with `‖A‖₁ = tr A₊ + tr A₋` | `hermPos`, `hermNeg`, `hermPos_sub_hermNeg`, `trace_hermPos_add_trace_hermNeg` | `HTGeometry/PositiveTraceContraction` |
| **a positive trace-preserving map contracts `‖·‖₁` on Hermitian matrices** | `finiteMatrixNuclearNorm_apply_le` | same |
| the block/ancilla dictionary and the amplification calculus | `blockMat`, `blockMat_mul`, `blockMat_trace`, `amplify_blockMat`, `trace_amplify` | `HTGeometry/AncillaBlockMatrix` |
| the Hermitian dilation `[[0,X],[Xᴴ,0]]` and `‖dil X‖₁ = 2‖X‖₁` | `hermDilation2`, `finiteMatrixNuclearNorm_hermDilation2` | `HTGeometry/PositiveMapTraceNormContraction` |
| **a positive linear map is star preserving** | `positiveLinear_map_conjTranspose` | same |
| **a two-positive trace-preserving map contracts `‖·‖₁` of *every* matrix** | `nuclearNorm_apply_le_of_twoPositive` | same |
| the triangle inequality and the reverse triangle inequality in full generality | `finiteMatrixNuclearNorm_add_le'`, `_sub_le'`, `_sub_le_sub` | same |

### The channel layer: the diamond distance is a metric on the monoid of channels

`HTGeometry/QuantumChannelDiamond.lean`.

| Card item | Declaration |
|---|---|
| a channel: linear, completely positive, trace preserving | `QuantumChannel` |
| channels compose, and form a monoid | `Monoid (QuantumChannel n)` |
| a channel is positive, and every ancilla amplification is a positive trace-preserving map | `QuantumChannel.positive`, `isPositiveTP_amplify_anc` |
| **every amplification of a channel is again two-positive** | `amplify_amplify`, `twoPositive_amplify` |
| **a channel contracts the trace norm at every ancilla level** | `nuclearNorm_amplify_le` |
| **`(2)`**: the diamond distance, as the sup over the trace-norm unit ball | `diamondDist` |
| it is bounded by two and attained on a nonempty set | `diamondDistSet_bddAbove`, `diamondDistSet_nonempty` |
| **the diamond distance is a genuine metric on channels** | `MetricSpace (QuantumChannel n)` |
| **`‖(Φ−Ψ)(X)‖₁ ≤ d_◇(Φ,Ψ)·‖X‖₁`** | `nuclearNorm_sub_le_diamondDist_mul` |
| **left composition contracts** -- the `LeftContracting` hypothesis | `leftContracting_quantumChannel` |
| unitary channels, and their inverses | `unitaryChannel`, `unitaryChannel_mul_star`, `star_unitaryChannel_mul` |
| **right composition by a unitary channel is a diamond isometry** | `diamondDist_mul_unitaryChannel` |

`eq_of_dist_eq_zero` is proved through `IsPositiveTP.eq_of_eqOn_density`: a positive
trace-preserving map is determined by its action on states, because every positive matrix is a
non-negative multiple of a state and every matrix is a complex combination of Hermitian ones.

### Theorems A and B for a dynamical semigroup

`HTGeometry/MarkovianReturnRecovery.lean`.

| Card item | Declaration |
|---|---|
| a quantum dynamical semigroup | `DynamicalSemigroup` |
| **`(6)`**: `Λ_{R−t} ∘ Λ_t = Λ_t ∘ Λ_{R−t} = Λ_R` -- now a theorem, not a hypothesis | `recovery_left`, `recovery_right` |
| **`(7)`**: the recovery defect of the pair is exactly the return defect | `dist_recovery_eq` |
| **`(8)`**: `(1 − δ_R)‖X‖₁ ≤ ‖(Λ_t ⊗ id)(X)‖₁` for **every** matrix `X` and every ancilla | `one_sub_defect_mul_nuclearNorm_le` |
| a finite inverse-closed dictionary of unitary channels | `UnitaryDictionary` |
| right composition by a dictionary word is a diamond isometry | `UnitaryDictionary.dist_mul_word` |
| **`(9)`**: complexity reflection at radius shift `δ_R` | `dist_reflect_word`, `DynamicalSemigroup.dist_reflect_word` |
| **`(10)`**: incidence-count interlacing at each exact length | `card_reflect_word`, `DynamicalSemigroup.card_reflect_word` |
| **`(11)`**: any non-negative length weighting interlaces | `sum_weighted_le` |

### Corollary C, proved rather than imported

The classification of completely positive trace-preserving maps with completely positive inverse
is built from scratch.  Four modules.

`HTGeometry/CompletelyPositiveSchwarz.lean`:

| Card item | Declaration |
|---|---|
| the quadratic form of a two-by-two block matrix | `blockVec2`, `dotProduct_blockMat_two` |
| **`[[A,Bᴴ],[B,1]] ⪰ 0 ⟹ BᴴB ≤ A`** | `sub_conjTranspose_mul_posSemidef` |
| `[[XᴴX, Xᴴ],[X,1]] = CᴴC ⪰ 0` | `posSemidef_schwarzBlock` |
| a completely positive linear map, and its positivity | `IsCP`, `IsCP.pos`, `IsCP.map_conjTranspose` |
| **the Kadison--Schwarz inequality** `Θ(X)ᴴΘ(X) ≤ Θ(XᴴX)` | `IsCP.schwarz` |

`HTGeometry/UnitalCPInverseRigidity.lean`:

| Card item | Declaration |
|---|---|
| a positive map is monotone for the Loewner order | `IsCP.monotone` |
| **Schwarz equality** for two mutually inverse unital completely positive maps | `IsCP.schwarz_eq` |
| **multiplicativity**, by polarising in `A+B` and `A+iB` | `IsCP.map_mul_of_inverse` |

`HTGeometry/MatrixStarAutomorphismInner.lean`:

| Card item | Declaration |
|---|---|
| moving a matrix across the pairing conjugates it | `star_mulVec_dotProduct` |
| the unit is the sum of the diagonal matrix units | `one_eq_sum_diagonal_single` |
| **an injective unital star endomorphism of a matrix algebra is a unitary conjugation** | `exists_unitary_conjugation_of_starAlgHom` |

`HTGeometry/ChannelInverseRigidity.lean`:

| Card item | Declaration |
|---|---|
| a positive matrix is dominated by its trace times the unit | `posSemidef_le_trace_smul_one` |
| a linear functional vanishing on positive matrices vanishes | `linear_eq_zero_of_eqOn_posSemidef` |
| a matrix pairing with the trace like the unit is the unit | `eq_one_of_trace_mul_eq` |
| **`Φ(1)` is nonsingular** when `Φ` is onto | `QuantumChannel.det_map_one_ne_zero` |
| **Corollary C**: a channel with a channel inverse is `X ↦ W X Wᴴ` with `W` unitary | `QuantumChannel.exists_unitary_of_channel_inverse` |

`HTGeometry/MarkovianExactReturn.lean` runs it back through the semigroup:

| Card item | Declaration |
|---|---|
| a vanishing return defect is an exact return -- this is where the metric (not pseudometric) matters | `ch_eq_one_of_dist_eq_zero` |
| **exact return makes every intermediate channel invertible** | `inverse_of_exact_return` |
| **`(14)`**: every `Λ_t` is a unitary conjugation | `exists_unitary_of_exact_return` |
| **`(14)`**: and the semigroup is periodic, `Λ_{t+R} = Λ_t` | `periodic_of_exact_return` |
| **`(9)`--`(10)` become equalities under `t ↦ R−t`** | `card_reflect_eq` |

The normalisation is the step that makes the classification unconditional: `P = Φ(1)` is positive
definite because `X ↦ ⟨v, Φ(X)v⟩` is a positive linear functional and a positive matrix is
dominated by its trace times the unit, so a functional annihilating the unit annihilates
everything -- while `Φ` is onto.  Conjugating by `P^{-1/2}` makes `Φ` unital without disturbing
complete positivity or invertibility, Kadison--Schwarz is then saturated in both directions, the
normalised map is a star automorphism, hence inner, and trace preservation forces the remaining
positive factor to be one.

Axiom audit: every displayed declaration depends only on `propext`, `Classical.choice`,
`Quot.sound`.

### Nothing remains

`(6)`--`(11)` and Corollary C are all Lean theorems about arbitrary finite-dimensional quantum
dynamical semigroups, arbitrary ancillas, and arbitrary finite inverse-closed unitary
dictionaries.  The card moves to stage 3.
