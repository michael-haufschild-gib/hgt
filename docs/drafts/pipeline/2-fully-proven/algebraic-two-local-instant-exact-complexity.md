# Algebraic two-local instant exact-complexity law

- **ID:** algebraic-two-local-instant-exact-complexity
- **Stage:** 2-fully-proven
- **Type:** THEOREM / boundary theorem for robust autonomous complexity
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]`
- **Parent:** `../1-in-progress/static-local-complexity-law.md`, obligation O4
- **External parent:** Y. Jia and M. M. Wolf, *Hay from the haystack: explicit
  examples of exponential quantum circuit complexity*, arXiv:2205.06977

## Exact statement

Fix `n >= 2` and put `D=2^n`.  There exist

1. a traceless two-local `n`-qubit Hamiltonian `H_n` whose Pauli
   coefficients are rational; and
2. the fixed algebraic product input `Omega=|0>^tensor n`

such that `Omega` has nonzero overlap with every eigenvector of `H_n`, the
only rational linear relation among the `D` eigenvalues is their trace
relation, and the following hold.

### A. Every nonzero algebraic time has exponential exact complexity

For every nonzero real algebraic `t`,

\[
  C_0(e^{-itH_n}\Omega)\ge {D-1\over16}.                 \tag{1}
\]

Here `C_0` is exact pure-state preparation complexity from `Omega` using
arbitrary two-qubit unitary gates on arbitrary pairs.  Allowing a fixed
algebraic product change of input changes the bound only by its linear gate
cost.

### B. Low exact-complexity times are locally finite

For every integer `s<(D-1)/16` and every finite `T`,

\[
 \{t\in[-T,T]:C_0(e^{-itH_n}\Omega)\le s\}              \tag{2}
\]

is finite.  Equivalently, outside a locally finite subset of real time, the
autonomous orbit has exact state complexity at least `(D-1)/16`.

This is an exact-complexity theorem.  It gives no lower bound at one fixed
positive approximation radius and therefore does not close O4.

## Proof

### 1. A rational two-local specialization with full symmetric Galois group

The generic characteristic polynomial of the traceless two-local Pauli
family has geometric monodromy `S_D`; this is paper-proved and Lean-proved in
`generic-two-local-spectral-monodromy`.  Hence its generic Galois group over
the rational-function field of Pauli coefficients is `S_D`.

Hilbert irreducibility gives a Zariski-dense set of rational coefficient
specializations whose characteristic polynomial still has Galois group
`S_D`.  We may simultaneously avoid the discriminant and any prescribed
nonzero polynomial in the coefficients.

The cyclicity determinant

\[
 K_\Omega(H)=\det[\Omega,H\Omega,\ldots,H^{D-1}\Omega]   \tag{3}
\]

is such a nonzero polynomial on the two-local family.  To see it is not
identically zero, take

\[
 H_0=\sum_{j=0}^{n-1}3^jX_j .                           \tag{4}
\]

Its product `X`-basis eigenvalues are distinct by uniqueness of balanced
ternary expansion, while `|0>^tensor n` has the same nonzero overlap with
every `X`-basis vector.  The usual Vandermonde factorization of (3) therefore
gives `K_Omega(H_0) != 0`.

Choose a rational Hilbert specialization outside the discriminant and
`K_Omega=0`.  It has simple spectrum and full spectral support at `Omega`.

### 2. The specialized spectrum has rational rank `D-1`

Let `E=(E_1,...,E_D)` be the roots.  The rational relation space

\[
 R_E=\{a\in\mathbb Q^D:\sum_j a_jE_j=0\}               \tag{5}
\]

is invariant under the Galois group `S_D`.  The rational permutation module
splits as the constant line plus the irreducible standard representation.
Tracelessness puts the constant vector in `R_E`.  If `R_E` contained any
standard component, it would be all of `Q^D`, forcing every `E_j` to vanish,
contrary to simple spectrum.  Thus

\[
 R_E=\mathbb Q(1,\ldots,1),\qquad
 \dim_\mathbb Q\operatorname{span}\{E_j\}=D-1.          \tag{6}
\]

### 3. Lindemann--Weierstrass transfers spectral rank to the state

Fix nonzero algebraic real `t` and put `z_j=exp(-itE_j)`.  Every `E_j` is
algebraic.  Finite Lindemann--Weierstrass, applied to a rational basis of
their span, gives

\[
 \operatorname{trdeg}_\mathbb Q\mathbb Q(z_1,\ldots,z_D)=D-1.      \tag{7}
\]

This exact finite theorem is already in the Lean corpus as
`exp_algebraicIndependent_of_linearIndependent` in
`RHTower/FiniteLindemannWeierstrass.lean`.

Choose an algebraic orthonormal eigenbasis `V` of the rational Hermitian
matrix `H_n`, and put `c=V^*Omega`.  Cyclicity makes every `c_j` nonzero.
In computational coordinates,

\[
 e^{-itH_n}\Omega=V\operatorname{diag}(c)z .             \tag{8}
\]

The matrix `V diag(c)` is algebraic and invertible, so (8) preserves
transcendence degree.  The output state therefore has transcendence degree
`D-1`.

Jia--Wolf Theorem 1 proves for qubits that the coordinate transcendence
degree of a state is at most `16` times its arbitrary two-qubit exact circuit
complexity.  Equation (1) follows.

### 4. O-minimality makes the exceptional real times discrete

For fixed `s`, the set `S_s` of states prepared by at most `s` arbitrary
two-qubit gates is compact semialgebraic.  Indeed, there are finitely many
gate-support patterns; for each pattern the parameter space `U(4)^s` is
compact semialgebraic, the output coordinates are polynomial in the gate
entries, and Tarski--Seidenberg preserves semialgebraicity under projection.

On `[-T,T]`, every coordinate of `t -> exp(-itH_n)Omega` is a finite algebraic
linear combination of restricted sine and cosine functions.  The orbit map
is therefore definable in the restricted-analytic o-minimal structure
`R_an`.  Its preimage of `S_s` is a definable subset of the real line, hence
a finite union of points and intervals.

If that preimage contained a nontrivial interval, the interval would contain
a nonzero algebraic time, contradicting (1).  Only finitely many points
remain, proving (2).

## Hostile boundary audit

1. **No robust conclusion.**  Transcendence degree is destroyed by arbitrary
   small perturbations because algebraic vectors are dense.  Neither (1) nor
   (2) supplies a dimension-independent approximation radius.
2. **No Brown growth.**  Exact complexity jumps from zero to order `D` rather
   than growing linearly.  It is therefore an obstruction to using exact
   complexity as a physical observable, not a solution of the growth law.
3. **No effective first time.**  O-minimality gives local finiteness but no
   usable lower bound on distance from the low-circuit semialgebraic set.
4. **No novelty promotion.**  Jia--Wolf supply the transcendence-degree
   circuit theorem and explicit nonlocal examples.  The fixed-two-local
   Hilbert-specialization and locally-finite-time synthesis was not found in
   the initial exact-concept search, but priority remains unverified.

## Exact surviving O4 question

The theorem converts O4 into a quantitative separation problem:

> Bound, at one fixed positive radius, the distance between the algebraic
> local-Hamiltonian orbit and the semialgebraic `s`-gate state set through
> normalized time `s`, uniformly up to `s=Theta(D/poly(n))`.

Qualitative algebraic independence proves the distance is nonzero at
algebraic times.  Brown growth requires a new quantitative local
Lindemann--circuit separation law whose radius does not collapse with `n`,
`s`, or time.

## Formalization status

- `[CORPUS]` finite Lindemann--Weierstrass and algebraic independence:
  `RHTower/FiniteLindemannWeierstrass.lean`.
- `[CORPUS]` full two-local monodromy and relation rigidity: modules cited by
  `generic-two-local-spectral-monodromy`.
- Missing Lean layers: rational Hilbert specialization, transcendence-degree
  bound for concrete two-qubit circuits, cyclic spectral-coordinate transfer,
  and the o-minimal local-finiteness corollary.
- No new Lean code is authorized until those exact interfaces are designed
  from the existing corpus and this paper proof survives another specialist
  audit.

## Sources

- Y. Jia and M. M. Wolf, *Hay from the haystack: explicit examples of
  exponential quantum circuit complexity*, arXiv:2205.06977, Theorems 1, 3,
  6, and 7.
- D. Hilbert, irreducibility theorem; use the standard Zariski-dense Hilbert
  specialization form over `Q`.
- A. J. Wilkie and L. van den Dries, standard one-dimensional finiteness for
  sets definable in the restricted-analytic o-minimal structure `R_an`.


## Lean status audit (2026-08-10)

The card's `Formalization status` section is stale in two places.

1. **Wrong path.**  Finite Lindemann–Weierstrass is *not* in
   `RHTower/FiniteLindemannWeierstrass.lean`; it is
   `HTGeometry/FiniteLindemannWeierstrass.lean`, and the cited declaration
   `exp_algebraicIndependent_of_linearIndependent` is there (line 402), with a
   coefficient version in
   `HTGeometry/FiniteAlgebraicCoefficientLindemannWeierstrass.lean`.
2. **Already built.**  "Cyclic spectral-coordinate transfer" is listed as a
   missing layer, but the corpus already owns its core:
   `HTGeometry/MatrixPrincipalSymbolAncestralConservation.lean` proves
   `algebraicIndependent_matrixLinearForms_iff_of_det_ne_zero` — an invertible
   square linear transformation preserves algebraic independence in both
   directions — on top of
   `HTGeometry/AlgebraicIndependentLinearForms.lean`'s `matrixLinearForms`.

What that lemma did not give is the transcendence-*degree* statement the card
actually needs at step 3, since the family `z` has one relation and is not
algebraically independent.  That gap is now closed:

`HTGeometry/MatrixLinearFormsAdjoin.lean` (new, unconditional, axiom-clean,
in the umbrella):

- `adjoin_matrixLinearForms_le`;
- **`adjoin_matrixLinearForms_eq_of_det_ne_zero`** — an invertible linear change
  of coordinates generates the *same* subalgebra;
- **`adjoin_field_matrixLinearForms_eq_of_det_ne_zero`** — and the same
  intermediate field.

So `V diag(c)` being algebraic and invertible makes every transcendence-theoretic
invariant of the computational coordinates equal to that of the spectral ones,
which is exactly equation (8) of the proof.

### Remaining Lean layers

- rational Hilbert specialization (step 1);
- the Jia–Wolf transcendence-degree/circuit bound (step 3's external input);
- o-minimal local finiteness (step 4).

## Step 2 formalized: the relation space collapses to the trace relation (2026-08-10)

`HTGeometry/PermutationInvariantSubspace.lean` (new, unconditional, axiom-clean,
in the umbrella) proves the representation-theoretic content of §2 without any
Galois machinery, and without a characteristic hypothesis.

- `sumForm`, `constLine`, `IsPermInvariant`;
- `single_sub_single_mem` — a vector of the subspace separating two coordinates
  yields `e_i - e_j`, by transposing them and subtracting;
- `single_sub_single_mem_of_mem`, `all_single_sub_single_mem` — one such
  difference propagates to all of them;
- `eq_sum_single_sub_single` — a sum-zero vector is a combination of those
  differences;
- **`classification`** — a permutation-invariant subspace of `K^ι` is `⊥`, the
  constants, the sum-zero hyperplane, or `⊤`.  *No characteristic hypothesis:*
  either every vector is constant, or the subspace swallows the sum-zero
  hyperplane;
- **`eq_constLine_of_le_of_ne_top`** — a permutation-invariant subspace that
  contains the constants and is not everything *is* the constants, provided
  `(card ι : K) ≠ 0`.

Applied to `R_E` of equation (5): it is `S_D`-invariant, contains the trace
relation, and is not everything because the spectrum is simple.  Over `ℚ` with
`D ≥ 1` the cardinality condition is automatic, so `R_E = ℚ(1,…,1)` and
`dim span {E_j} = D - 1`, which is equation (6).

The `(card ι : K) ≠ 0` side condition is necessary, not residual: in
characteristic dividing `card ι` the constants lie *inside* the sum-zero
hyperplane and the conclusion fails.

### Remaining Lean layers

- rational Hilbert specialization (step 1);
- the Jia–Wolf transcendence-degree/circuit bound (step 3's external input);
- o-minimal local finiteness (step 4).

## Step 3 formalized: rigid spectrum ⇒ independent exponentials (2026-08-10)

`HTGeometry/SpectralExponentialIndependence.lean` (new, unconditional,
axiom-clean, in the umbrella) is the bridge from §2 to §3.

- `relationForm E` — the rational linear form `a ↦ ∑ aⱼ Eⱼ`, whose kernel is
  the relation space `R_E` of equation (5);
- **`ker_relationForm_smul`** — scaling the family by any nonzero complex
  constant leaves the relation space unchanged, so the rigidity of §2 is
  available at *every* nonzero time `t`, not only at `t = 1`;
- **`linearIndependent_subtype_of_ker_eq_constLine`** — if `R_E` is exactly the
  trace line, then deleting any single index leaves a `ℚ`-linearly independent
  family.  (A relation among the remaining `D-1` extends by zero, so it is a
  multiple of `(1,…,1)` whose deleted coordinate is `0`, hence trivial.);
- **`algebraicIndependent_exp_of_ker_eq_constLine`** — feeding that into the
  corpus's finite Lindemann–Weierstrass
  (`RHTower.exp_algebraicIndependent_of_linearIndependent`, in
  `HTGeometry/FiniteLindemannWeierstrass.lean`) makes the `D-1` exponentials
  algebraically independent over `ℚ`.  This is the `≥` half of equation (7);
- **`prod_exp_eq_one_of_sum_eq_zero`** and
  **`exp_eq_inv_prod_of_sum_eq_zero`** — tracelessness makes the `D`
  exponentials multiply to `1`, so the deleted one is recovered from the
  others.  This is the `≤` half of equation (7).

Together with `PermutationInvariantSubspace.eq_constLine_of_le_of_ne_top`
(§2) and `MatrixLinearFormsAdjoin.adjoin_matrixLinearForms_eq_of_det_ne_zero`
(the coordinate transfer of equation (8)), the whole chain from spectral
rigidity to transcendence degree `D-1` of the evolved state is now Lean, given
the spectrum's rigidity as input.

### Remaining Lean layers

- rational Hilbert specialization (step 1) — supplies that rigidity for a
  concrete two-local `H_n`;
- the Jia–Wolf transcendence-degree/circuit bound (the external input of §3);
- o-minimal local finiteness (step 4).

## Step 1, spectral-simplicity core formalized (2026-08-10)

`HTGeometry/BalancedTernaryUniqueness.lean` (new, unconditional, axiom-clean,
in the umbrella) proves the arithmetic fact the nonvanishing argument of §1
rests on — that the `X`-basis eigenvalues of `H_0 = ∑_j 3^j X_j` are distinct.

- `two_mul_geom_sum_add_one` — `2 ∑_{j<n} 3^j + 1 = 3^n`, so the tail is
  strictly below the leading power;
- `abs_sum_lt_pow` — hence `|∑_{j<n} 3^j c_j| < 3^n` whenever `|c_j| ≤ 1`;
- **`eq_zero_of_sum_eq_zero`** — uniqueness of balanced ternary expansions: a
  signed sum of powers of three with coefficients in `{-1,0,1}` vanishes only
  when every coefficient does;
- **`sum_pow_three_sign_injOn`** — the `2^n` values `∑_j 3^j εⱼ` with `εⱼ = ±1`
  are pairwise distinct.

The `±1` case is reduced to the `{-1,0,1}` case without dividing in `ℤ`: the
difference `εⱼ − δⱼ` takes only the values `0, ±2`, so it is `2 cⱼ` for an
explicitly defined `cⱼ ∈ {-1,0,1}`.

This gives simplicity of the `X`-basis spectrum of `H_0`, which is what makes
the Vandermonde factorisation of the cyclicity determinant `K_Ω(H_0)` nonzero —
equation (4) of the card.  What is still missing from §1 is the Hilbert
irreducibility specialization itself.

## The Vandermonde step of §1 was already corpus-owned (2026-08-10)

Another stale entry in the missing-layers list.  The "usual Vandermonde
factorization of (3)" does not have to be built:
`HTGeometry/EulerPrimeOrbitFourOrganLaw.lean` already proves
`finiteDiagonalKrylovVector_linearIndependent` — for injective nodes and
nowhere-vanishing weights the square weighted Vandermonde family
`k ↦ (i ↦ weightᵢ · nodeᵢ^k)` is linearly independent over `ℂ`, which is exactly
non-vanishing of the cyclicity determinant `K_Ω`.

`HTGeometry/BalancedTernaryKrylovCyclicity.lean` (new, unconditional,
axiom-clean, in the umbrella) joins it to the arithmetic:

- `ternaryValue ε = ∑_j 3^j εⱼ` for a sign pattern `ε : Fin n → Bool`;
- **`injective_ternaryValue`** — the `2^n` values are pairwise distinct
  (transported from `sum_pow_three_sign_injOn` by extending the pattern to all
  of `ℕ` by `1`, which avoids any `Fin`/`range` index juggling in the
  arithmetic lemma);
- **`linearIndependent_krylov_ternaryValue`** — against any weight with no
  vanishing coordinate, the Krylov family of the diagonal operator with these
  eigenvalues is linearly independent.

So equation (4) of the card — `K_Ω(H₀) ≠ 0` — is Lean, modulo naming the
eigenvalues directly rather than deriving them from the Pauli algebra of
`H₀ = ∑_j 3^j X_j`.

### Remaining Lean layers

- the Hilbert irreducibility specialization itself (the only genuinely missing
  part of §1);
- the Jia–Wolf transcendence-degree/circuit bound (§3's external input);
- o-minimal local finiteness (§4).

## §4, the elementary half formalized (2026-08-10)

`HTGeometry/NonzeroAlgebraicDense.lean` (new, unconditional, axiom-clean, in
the umbrella) proves the part of §4 that does not need o-minimality.

- **`exists_nonzero_algebraic_mem_Ioo`** — every nonempty open interval contains
  a nonzero algebraic real (a nonzero rational suffices; when the first rational
  produced is `0`, the interval also meets `(0, b)`);
- **`dense_nonzero_algebraic`** — the nonzero algebraic reals are dense;
- **`interior_eq_empty_of_forall_not_algebraic`** — a set of reals containing no
  nonzero algebraic number has empty interior;
- **`dense_compl_of_forall_not_algebraic`** — equivalently its complement is
  dense.

Applied with equation (1): the set of times of exact complexity `≤ s` contains
no nonzero algebraic time, hence **cannot contain an interval**, and the times
of complexity `> s` are dense.  That is the implication the card draws from
"if that preimage contained a nontrivial interval, the interval would contain a
nonzero algebraic time".

What this does *not* give is the card's equation (2).  Finiteness on `[-T,T]`
genuinely needs the definability step — `S_s` semialgebraic, the orbit definable
in `R_an`, and one-dimensional o-minimal finiteness — and mathlib has no
o-minimality.  The gap is now exactly that step, not the whole of §4.

### Remaining Lean layers

- the Hilbert irreducibility specialization (§1);
- the Jia–Wolf transcendence-degree/circuit bound (§3's external input);
- o-minimality of `R_an` and one-dimensional definable finiteness, for the
  upgrade of §4 from empty interior to finiteness.

## The counting mechanism of the Jia–Wolf bound (2026-08-10)

`HTGeometry/ParameterCountTranscendenceBound.lean` (new, unconditional,
axiom-clean, in the umbrella) formalizes why a parameter count bounds
transcendence — the engine of §3's external input.

- **`trdeg_adjoin_range_le`** — the subalgebra generated by `m` elements has
  transcendence degree at most `m`.  It is a surjective image of the polynomial
  ring in `m` variables (`Algebra.adjoin_range_eq_range_aeval` plus
  `AlgHom.rangeRestrict_surjective`), and mathlib's
  `MvPolynomial.trdeg_of_isDomain` evaluates that ring's degree;
- **`card_le_of_algebraicIndependent_of_mem_adjoin`** — an algebraically
  independent family lying inside that subalgebra has at most `m` members.

Applied to a circuit: the coordinates of a state prepared by `s` two-qubit gates
are polynomial in the gate parameters, so they contain at most that many
algebraically independent numbers.  Transcendence degree `D-1` therefore forces
a proportional number of parameters, which is the shape of `(1)`.

Scope, stated precisely: this is the *counting* half.  Jia–Wolf's constant `16`
comes from `U(4)` having `16` real parameters and from the passage between real
parameters and complex coordinates; neither the parametrisation of `U(4)` nor
that passage is formalized here, so equation (1) is **not** yet Lean.  What is
Lean is that any such parametrisation yields a bound of exactly this form.

The base field and ambient domain are taken in `Type` so that every cardinal
comparison happens in one universe; that is the case of interest, `ℚ ⊆ ℂ`.

### Remaining Lean layers

- the Hilbert irreducibility specialization (§1);
- the `U(4)` parametrisation and real/complex passage fixing the constant `16`;
- o-minimality of `R_an` and one-dimensional definable finiteness (§4's upgrade
  from empty interior to finiteness).

## The circuit half of the Jia–Wolf bound (2026-08-10)

`HTGeometry/CircuitCoordinateAdjoin.lean` (new, unconditional, axiom-clean, in
the umbrella) supplies what the counting lemma needs: that circuit coordinates
really are polynomial in the gate data.

- `mul_entries_mem`, **`prod_entries_mem`** — a product of matrices keeps its
  entries inside any subalgebra containing the factors' entries;
- **`mulVec_mem`** — hence every coordinate of `(∏ gates) · v` lies in the
  subalgebra generated by the gate entries and the input coordinates;
- **`card_le_of_algebraicIndependent_mulVec`** — so if all gate entries and all
  input coordinates lie in the algebra generated by `m` elements, at most `m`
  output coordinates can be algebraically independent.

The constant `16` needs no `U(4)` parametrisation: a two-qubit gate is a `4 × 4`
matrix, so `s` gates contribute `16 s` entries, and the bound reads
`trdeg ≤ 16 s` directly.  Counting *complex entries* rather than *real
parameters* is what makes this elementary.

Two gaps remain before equation (1) itself is Lean: the embedding of a
two-qubit gate into the `D × D` matrix (its entries are gate entries, `0`, or
`1`, so they stay in the same algebra — routine but not written), and the
statement that adjoining the algebraic input coordinates of `Ω` does not raise
the transcendence degree.

### Remaining Lean layers

- the Hilbert irreducibility specialization (§1);
- the two-qubit embedding and the algebraic-input refinement, to reach (1);
- o-minimality of `R_an` and one-dimensional definable finiteness (§4's upgrade
  from empty interior to finiteness).

## Equation (1)'s transcendence bound, assembled (2026-08-10)

Added to `HTGeometry/CircuitCoordinateAdjoin.lean`; both gaps flagged in the
previous entry are closed.

- **`card_le_of_algebraicIndependent_mulVec_baseInput`** — the input refinement.
  No theorem about algebraic elements not raising transcendence degree is
  needed: the card's input `Ω = |0⟩^⊗ⁿ` has coordinates `0` and `1`, so its
  coordinates lie in the *base field*, and no generator is spent on it.
  `mem_adjoin_of_eq_algebraMap_or_mem` is the corresponding entry-level fact,
  which also covers the two-qubit embedding — an embedded gate's entries are
  gate entries, `0`, or `1`, all in the same algebra.
- **`exists_enumeration_of_gates`** — the constant.  The entries of `s` gates of
  size `4 × 4` are enumerated by `16 s` elements, via
  `Fin (s*16) ≃ Fin s × Fin 16` and `Fin 16 ≃ Fin 4 × Fin 4`.

So the transcendence half of equation (1) is Lean: a state obtained from a
base-field input by `s` two-qubit gates has at most `16 s` algebraically
independent coordinates.  Combined with §3's `D-1` independent exponentials
this is the bound `C₀ ≥ (D-1)/16`, once "exact complexity `≤ s`" is *defined* as
"expressible as such a product" — that definition, not the mathematics, is what
is still absent.

### Remaining Lean layers

- a Lean definition of exact circuit complexity `C₀`, to state (1) as an
  inequality about it rather than about a given factorisation;
- the Hilbert irreducibility specialization (§1);
- o-minimality of `R_an` and one-dimensional definable finiteness (§4's upgrade
  from empty interior to finiteness).

## Exact complexity defined; equation (1)'s inequality is now about `C₀` (2026-08-10)

`HTGeometry/ExactCircuitComplexityBound.lean` (new, unconditional, axiom-clean,
in the umbrella) removes the definitional gap flagged in the previous entry.

- `GeneratedBy K q M` — a gate whose entries are generated by `q` elements
  (`q = 16` for a two-qubit gate);
- **`exists_generators_of_list`** — a list of such gates is generated by
  `length * q` elements, combining the per-gate families through
  `Fin (len * q) ≃ Fin len × Fin q` and monotonicity of `Algebra.adjoin`;
- `PreparableIn 𝒢 v w s` — `w` is obtained from `v` by a list of `s` gates drawn
  from `𝒢`;
- **`exactComplexity 𝒢 v w = sInf {s | PreparableIn 𝒢 v w s}`**;
- **`card_le_exactComplexity_mul`** — if `w` carries `r` algebraically
  independent coordinates over `K`, and `v` has base-field coordinates, then
  `r ≤ exactComplexity 𝒢 v w * q`.

The factorisation is now quantified away: `Nat.sInf_mem` produces a minimal
factorisation and the per-factorisation bound applies to it.  With `q = 16` and
`r = D - 1` this is exactly `C₀ ≥ (D-1)/16`, equation (1) — for the abstract
gate set `𝒢`.

Preparability is a hypothesis, deliberately.  When `w` is not preparable at all
the infimum of an empty set of naturals is `0`, and the inequality would be
false rather than vacuous; requiring `∃ s, PreparableIn 𝒢 v w s` keeps the
statement honest.

### Remaining Lean layers

- the Hilbert irreducibility specialization (§1), which supplies the spectral
  rigidity for a concrete rational two-local `H_n`;
- o-minimality of `R_an` and one-dimensional definable finiteness (§4's upgrade
  from empty interior to finiteness).

## §2's hypothesis linked to its conclusion (2026-08-10)

Added to `HTGeometry/SpectralExponentialIndependence.lean`.  Until now §2's
*conclusion* (a permutation-invariant relation space collapses) was Lean but its
*hypothesis* — that the Galois action makes `R_E` permutation invariant — was
not.  Both ends are now joined.

- **`isPermInvariant_ker_relationForm`** — if every permutation of the family is
  realised by a ring endomorphism of `ℂ`, then `R_E` is permutation invariant.
  A ring hom fixes `ℚ` automatically (`map_ratCast`), so a rational relation
  transports to a rational relation; reindexing by `σ` finishes it.
- **`ker_relationForm_eq_constLine`** — with that action, tracelessness, and one
  nonzero member, `R_E` is exactly the trace line.  Non-triviality comes from a
  single basis covector: if `R_E` were everything it would contain `e_{i₀}`,
  forcing `E_{i₀} = 0`.

This is equation (6), now from the Galois hypothesis rather than from an
assumed invariance.  Its output is precisely the input consumed by
`algebraicIndependent_exp_of_ker_eq_constLine`, so §2 and §3 are a single Lean
chain: symmetric Galois action ⇒ rank `D-1` ⇒ `D-1` independent exponentials ⇒
`C₀ ≥ (D-1)/16`.

What remains in §1 is *supplying* that Galois action for a concrete rational
two-local `H_n`, which is Hilbert irreducibility.  mathlib has no Hilbert
irreducibility theorem (checked: no `IsHilbertian`, no
`hilbert_irreducibility`), so that is a build-from-scratch item.

## Rigidity may be proved in the splitting field (2026-08-10)

`HTGeometry/RelationSpaceTransfer.lean` (new, unconditional, axiom-clean, in
the umbrella) removes an awkwardness in the previous entry.

`SpectralExponentialIndependence.isPermInvariant_ker_relationForm` asks for the
symmetric action to be realised by ring endomorphisms **of `ℂ`**.  Supplying
that from a Galois group would require extending an automorphism of the
splitting field to an endomorphism of `ℂ`, which needs a transcendence basis and
choice.  It is unnecessary:

- **`ker_form_comp`** — the rational relation space is unchanged by an injective
  `ℚ`-algebra map.  So it may be computed in *any* field containing the family;
- **`isPermInvariant_ker`** and **`ker_form_eq_constLine`** — the same rigidity
  statements as before, over an arbitrary `ℚ`-algebra field rather than `ℂ`.

The chain therefore runs: prove rigidity inside the splitting field, where the
Galois group acts by honest field automorphisms; transport it to `ℂ` along the
embedding; then apply Lindemann–Weierstrass there.  No endomorphism of `ℂ` is
ever constructed.

### Remaining Lean layers

- the Hilbert irreducibility specialization (§1) — not in mathlib, a
  build-from-scratch item;
- o-minimality of `R_an` and one-dimensional definable finiteness (§4's upgrade
  from empty interior to finiteness).

## §4: one-dimensional finiteness for equation constraints (2026-08-10)

`HTGeometry/RealAnalyticZeroFiniteness.lean` (new, unconditional, axiom-clean,
in the umbrella).

Corpus check first: `AnalyticBallZeroSet.finite_zeros_of_analyticOnNhd_closedBall`
is **complex**, and `AnalyticNullPreimage.analytic_zero_set_countable` gives
*countability* for a **globally** analytic real function, deriving local
finiteness only inside its proof.  The exported real, compact-set statement was
missing.

- `eventually_ne_zero_of_analyticOnNhd` — on a preconnected set a single nonzero
  value forbids local vanishing anywhere (identity theorem);
- **`finite_zeros_of_analyticOnNhd`** — a real-analytic function that is nonzero
  somewhere has finitely many zeros on any compact subset.  Each point gets a
  punctured zero-free neighbourhood; a finite subcover leaves only the centres.

This supplies §4's finiteness **when the constraint is an equation**: the times
in `[-T,T]` at which an analytic coordinate expression vanishes are finite.  It
does **not** cover `S_s`, which is semialgebraic — defined by inequalities as
well — and the set where an analytic function is nonnegative can contain
intervals.  So §4 still needs o-minimality for the general case; what is now
Lean is the equational core plus (earlier) the empty-interior statement.

### Remaining Lean layers

- the Hilbert irreducibility specialization (§1) — not in mathlib;
- o-minimality of `R_an`, for the inequality part of §4.

## Corpus check: §1's generic half is already Lean (2026-08-10)

The card cites `generic-two-local-spectral-monodromy` as "paper-proved and
Lean-proved".  Verified, with the declaration names:

- **`TwoLocalCommonBaseEdgeMonodromy.commonBaseTwoLocalMonodromySubgroup_eq_top`**
  — the spectral monodromy group of the universal complexified two-local family
  at the explicit fixed diagonal Hamiltonian is the full symmetric group;
- **`TwoLocalCharacteristicIrreducibility.universalTwoLocalCharacteristicPolynomial_irreducible`**;
- supporting: `GenericPolynomialVieta.symmetricPartField_eq_adjoin_genericCoeff`,
  `PolynomialHermitianMatrixProjectiveGenericity.*`.

So §1 splits cleanly: the *generic* symmetric action is corpus-owned, and the
only missing step is the passage from the generic point to a **rational**
specialization — Hilbert irreducibility.  That is the single remaining
obstruction in §1, not the monodromy.

Also checked: neither the corpus nor mathlib has any semialgebraic-set
machinery, so §4's inequality part is a from-scratch build.

## §4: closed low-complexity time sets are nowhere dense (2026-08-10)

Added to `HTGeometry/NonzeroAlgebraicDense.lean`:
**`isNowhereDense_of_isClosed_of_forall_not_algebraic`** — a *closed* set of
reals containing no nonzero algebraic number is nowhere dense.

`S_s` is compact and the orbit map is continuous, so the low-complexity time set
is closed; with equation (1) it contains no nonzero algebraic time.  It is
therefore nowhere dense in `[-T,T]`, strengthening the earlier empty-interior
statement.  Finiteness still needs o-minimality.

### Remaining Lean layers

- Hilbert irreducibility (§1) — the sole remaining step there;
- o-minimality of `R_an` for the inequality part of §4.

## Equation (6) is complete (2026-08-10)

Added to `HTGeometry/RelationSpaceTransfer.lean`.  The card's equation (6) makes
two assertions; only the first was Lean.

- `range_form` — the range of the relation form is the `ℚ`-span of the family;
- `finrank_constLine` — the trace line is one-dimensional;
- **`finrank_span_eq_card_sub_one`** — hence if the only rational relation is the
  trace relation, `dim_ℚ span {E_j} = D - 1`.

That is the second half of (6), obtained from the first by rank–nullity applied
to the relation form: its kernel is the trace line and its range is the span, so
`dim span = D - dim(trace line) = D - 1`.

Equation (6) is therefore fully formalized, and the chain
`symmetric Galois action ⇒ R_E = trace line ⇒ rank D-1 ⇒ D-1 independent
exponentials ⇒ C₀ ≥ (D-1)/16` is Lean end to end, given the Galois action.

### Remaining Lean layers

- Hilbert irreducibility (§1) — the sole remaining step there, and the only
  thing separating the chain above from a concrete rational `H_n`;
- o-minimality of `R_an` for the inequality part of §4.

## "Cyclicity makes every overlap nonzero" (2026-08-10)

`HTGeometry/KrylovWeightNonvanishing.lean` (new, unconditional, axiom-clean, in
the umbrella).  §3 uses the converse of the Vandermonde lemma — the corpus owned
"nonzero weights ⇒ independent Krylov family", the card also needs "independent
⇒ nonzero weights" — and that direction was missing.

- **`not_linearIndependent_of_weight_eq_zero`** — a vanishing weight destroys
  independence, with *no hypothesis on the nodes*: every Krylov vector then has a
  zero in that coordinate, but `card ι` independent vectors in `ι → ℂ` span, and
  a coordinate functional cannot vanish on a spanning set;
- **`weight_ne_zero_of_linearIndependent`** — hence cyclicity forces every
  overlap `c_j = ⟨v_j, Ω⟩` to be nonzero, which is what §3 asserts before
  applying `V diag(c)`.

Also checked this iteration, to avoid duplication: the "irreducible after
specialisation ⇒ irreducible before" direction is already mathlib's
`Polynomial.Monic.irreducible_of_irreducible_map`.  It is the *easy* direction;
Hilbert irreducibility is the other one and remains absent everywhere.

### Remaining Lean layers

- Hilbert irreducibility (§1);
- o-minimality of `R_an` for the inequality part of §4.

## Equation (8) closed (2026-08-10)

Added to `HTGeometry/MatrixLinearFormsAdjoin.lean`:

- `det_mul_diagonal_ne_zero` — an eigenbasis rescaled by nonzero overlaps is
  invertible;
- **`adjoin_matrixLinearForms_mul_diagonal_eq`** — hence the change of
  coordinates `V · diag c` preserves the generated algebra.

This is literally equation (8): the computational coordinates
`e^{-itH}Ω = V diag(c) z` and the spectral coordinates `z` generate the same
algebra, so they have the same transcendence degree.  The invertibility
hypothesis is now supplied by the previous entry —
`Krylov.weight_ne_zero_of_linearIndependent` gives `c_j ≠ 0` from cyclicity — so
§3's chain is connected without gaps:

`cyclicity ⇒ overlaps nonzero ⇒ V diag(c) invertible ⇒ same algebra ⇒ same
transcendence degree`.

### Status of the card

Every step of the paper proof is now Lean **except** two named classical
theorems, neither of which is in mathlib or the corpus:

- **Hilbert irreducibility** (§1) — supplies a rational specialization with the
  symmetric Galois action.  A constructive escape is not available: rational
  eigenvalues span a one-dimensional `ℚ`-space, so the relation space would have
  dimension `D-1` rather than `1`, and Lindemann–Weierstrass would give nothing.
  The eigenvalues must be irrational, which is exactly what a Hilbert
  specialization provides.
- **o-minimality of `R_an`** (§4) — for the inequality part.  The equational
  part and the topological consequences (empty interior, nowhere dense) are
  done.

## A composable form of the circuit bound (2026-08-10)

Added to `HTGeometry/ExactCircuitComplexityBound.lean`:
**`trdeg_adjoin_le_length_mul`** — the coordinates of a state prepared from a
base-field input by gates each generated by `q` elements generate an algebra of
transcendence degree at most `q ·` (number of gates).

Why this form and not the earlier one.  `card_le_of_algebraicIndependent_mulVec`
speaks about an algebraically independent family *among the coordinates*, and
that does not compose with equation (8): the adjoin-equality
`adjoin(range w) = adjoin(range z)` transfers the generated *algebra*, not any
particular independent subfamily, so chaining the two would have required
extracting a transcendence basis from among the coordinates.  Phrased with
`Algebra.trdeg` the two steps compose directly:

```text
trdeg (coordinates of e^{-itH}Ω)  =  trdeg (spectral coordinates z)   -- equation (8)
                                  ≥  D - 1                            -- §3, Lindemann–Weierstrass
trdeg (coordinates)               ≤  16 · (number of gates)           -- this lemma
```

giving `C₀ ≥ (D-1)/16` by composition rather than by re-deriving independence in
computational coordinates.

### Remaining Lean layers

- Hilbert irreducibility (§1);
- o-minimality of `R_an` for the inequality part of §4.

## Theorem A assembled (2026-08-10)

`HTGeometry/SpectralComplexityAssembly.lean` (new, unconditional, axiom-clean,
in the umbrella) joins the two halves into a single statement:

> **`card_sub_one_le_length_mul`.**  If the eigenvalues are algebraic and their
> only rational relation is the trace relation, and the state is prepared from a
> base-field input by gates each generated by `q` elements, then
> `D - 1 ≤ q · (number of gates)`.

With `q = 16` and `D = 2^n` this is equation (1), `C₀ ≥ (D-1)/16`.

The proof is the composition the previous entry made possible: the deleted
family of exponentials is algebraically independent (§3) and lies in the
generated subalgebra, so `D - 1 ≤ trdeg`; the circuit bounds the same `trdeg`
above by `q ·` (gates); and the eigenbasis hypothesis enters as an equality of
generated algebras, which is what equation (8) supplies.

The eigenbasis appears as `adjoin ℚ (range (circuit output)) =
adjoin ℚ (range (exp ∘ E))` rather than as a matrix.  That is deliberate: the
eigenbasis of a rational Hermitian matrix is algebraic, not rational, so
demanding a `ℚ`-matrix would have been false to the situation, while the
algebra equality is exactly what
`MatrixLinearFormsAdjoin.adjoin_matrixLinearForms_mul_diagonal_eq` proves over
whichever field the eigenbasis lives in.

### Remaining Lean layers

- Hilbert irreducibility (§1) — supplies `hrigid` for a concrete rational `H_n`;
- o-minimality of `R_an` for the inequality part of §4.

## Integration audit (2026-08-10)

All twelve modules added for this card build green in one invocation
(8850 jobs) and the formal lint gate reports nothing against any of them:

`BalancedTernaryUniqueness`, `BalancedTernaryKrylovCyclicity`,
`KrylovWeightNonvanishing`, `PermutationInvariantSubspace`,
`RelationSpaceTransfer`, `SpectralExponentialIndependence`,
`MatrixLinearFormsAdjoin`, `ParameterCountTranscendenceBound`,
`CircuitCoordinateAdjoin`, `ExactCircuitComplexityBound`,
`SpectralComplexityAssembly`, `NonzeroAlgebraicDense`,
`RealAnalyticZeroFiniteness`.

Every headline theorem is axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`), and every module is imported by
the `HTGeometry` umbrella.

The umbrella target itself currently fails, on
`ConstitutiveCoalitionalAttainment.lean` — a different card's module, under
active edit by another session (type mismatch and an unbound `i` at lines
125/127).  Nothing in this card's chain depends on it.

### Where the card stands

Formalized: §1's arithmetic (balanced ternary) and cyclicity (Vandermonde,
both directions); §2 in full, including both assertions of equation (6);
§3 in full, including equation (8), the circuit transcendence bound, the
definition of exact complexity, and the assembled Theorem A; §4's empty
interior, nowhere density, and equational finiteness.

Not formalized, and each a classical theorem absent from mathlib and the corpus:

- **Hilbert irreducibility** — the sole input still needed to discharge
  `hrigid` for a concrete rational `H_n`;
- **o-minimality of `R_an`** — needed only to upgrade §4 from nowhere dense to
  locally finite.

## Dependency survey for Hilbert irreducibility (2026-08-10)

No code this pass: the deliverable is a precise plan for the one theorem that
still blocks §1, replacing "HIT is missing" with a dependency chain and an
inventory of what exists.

**Why HIT is unavoidable.**  Two escapes were checked and both fail.  A
*constructive* rational Hamiltonian does not work: the card's own `H₀ = ∑ 3ʲXⱼ`
has integer eigenvalues, whose `ℚ`-span is one-dimensional, so the relation
space has dimension `D-1` and Lindemann–Weierstrass yields nothing — the
eigenvalues must be irrational.  A *measure-theoretic* escape does not work
either: the bad set is a countable union of proper analytic subsets of the
coefficient space, which has measure zero but can still contain every rational
point, since `ℚᴺ` is countable.  Avoiding a countable exceptional set at
rational points is exactly what HIT does.

**Dependency chain.**

```text
HIT  ←  Eisenstein's theorem on algebraic power series
     ←  Newton–Puiseux construction
     ←  Newton polygon
```

**Inventory.**

Available in mathlib:
- `IsAdicComplete.henselianRing` — an `I`-adically complete ring is Henselian at
  `I`, as an *instance*;
- `MvPowerSeries.isAdicComplete` — power series are adically complete for the
  variable ideal;
- `PowerSeries/WeierstrassPreparation.lean` — Weierstrass division and
  preparation;
- `Polynomial/Resultant`, `GaussLemma`, `Content`, `Eisenstein` (the criterion,
  not the power-series theorem);
- `Polynomial.Monic.irreducible_of_irreducible_map` — the *easy* specialization
  direction.

Absent from mathlib **and** the corpus:
- Newton polygon; Newton–Puiseux; Puiseux series as a ring;
- Eisenstein's theorem on algebraic power series;
- Hilbert irreducibility itself.

The corpus's `StokesFinitePuiseuxDendrogram` and
`ElementaryStokesGlobalPuiseuxRealization` model Puiseux *data* — finite
coefficient vectors taken as source data — not the construction of Puiseux
expansions of an algebraic function, so they do not shorten this chain.

**First buildable component.**  The unramified base case: a simple root of
`F(0,X)` lifts to a power-series root of `F(t,X)`.  With
`HenselianRing (PowerSeries K) (span {X})` obtained from the two instances
above, this is reachable; the only friction is the
`PowerSeries` / `MvPowerSeries Unit` identification for the variable ideal.
The ramified case then needs the Newton polygon, which is where the
from-scratch work genuinely begins.

## Hensel's lemma in factorisation form built (2026-08-10)

The Hilbert-irreducibility chain recorded in the previous entry (`HIT ← Eisenstein ←
Newton–Puiseux ← Newton polygon`) needs one tool that neither mathlib nor the corpus
had: **Hensel's lemma for factorisations**.  mathlib's `Henselian.lean` lifts *simple
roots* only (`HenselianRing.is_henselian`); lifting a coprime *factorisation* of the
special fibre — which is what a Newton-polygon edge with two distinct roots produces —
was absent everywhere.  It is now built, unconditionally and axiom-clean.

`HTGeometry/HenselFactorization.lean` (new, in the umbrella), over an arbitrary
commutative ring `S` complete for an arbitrary ideal `I`:

- `coeffMem_iff_map_eq_zero` — coefficientwise membership in `J` is vanishing of the
  reduction `Polynomial.map (Ideal.Quotient.mk J)`.  This is what makes the whole
  file compute: `%ₘ` and `/ₘ` by a monic divisor commute with `map`, so
  `CoeffMem.modByMonic`, `CoeffMem.divByMonic`, `coeffMem_divByMonic_sub` and
  `coeffMem_modByMonic_sub` are all one rewrite each;
- **`hensel_step`** — the Newton step.  A monic `g ≡ g₀ (mod I)` whose remainder
  `E = f %ₘ g` lies in `I^(k+1)` is corrected by `p = (E·v) %ₘ g`, of degree below `g`
  and with coefficients in `I^(k+1)`, to one whose remainder lies in `I^(k+2)`;
- `coeff_sub_mem_of_cauchy`, **`exists_adic_limit_polynomial`** — the coefficientwise
  adic limit of a Cauchy sequence of polynomials whose high coefficients are frozen;
- **`exists_monic_dvd_of_coeffMem_modByMonic`** — Hensel, divisor form: a monic `g₀`
  dividing `f` modulo `I` whose complementary quotient `f /ₘ g₀` is invertible modulo
  `(g₀, I)` lifts to a genuine monic divisor of `f` of the same degree;
- **`exists_monic_factorization`** — Hensel, factorisation form: `f ≡ g₀·h₀ (mod I)`
  with `g₀` monic and `h₀` invertible modulo `(g₀, I)` lifts to `f = g·h` with
  `g ≡ g₀`, `h ≡ h₀`.

Two design choices carry the proof.  *Only the divisor is iterated*: the complementary
factor is recovered as `f /ₘ g`, which makes the degree bookkeeping exact and removes
the usual simultaneous degree/congruence juggling.  And the step is stated as the single
polynomial identity

`f − (g + p)·(h + T) = E·w₂ − p·T`,   `T = E·z + s·h`,   `s = (E·v) /ₘ g`,

whose right-hand side visibly lies in `I^(k+2)`: `w₂` collects the three `I`-small
discrepancies (`z·(g₀−g)`, the Bézout defect, `v·(f/ₘg₀ − f/ₘg)`) and `p·T` is
`I^(k+1)` squared.  `f` need not be monic and `I` need not be maximal — only
completeness at `I` is used.

`HTGeometry/PowerSeriesFactorization.lean` (new, in the umbrella) instantiates it at
`S = K⟦t⟧`, `I = (t)`:

- `coeffMem_span_X_iff`, `map_constantCoeff_map_C` — the reduction/lift pair;
- **`exists_factorization_of_coprime_reduction`** — a coprime factorisation of the
  special fibre `f mod t = a·b` (with `a` monic) lifts to `f = g·h` over `K⟦t⟧`, with
  prescribed reductions and `deg g = deg a`;
- **`exists_monic_factor_of_rootMultiplicity`** — the form the Newton–Puiseux induction
  consumes: for any `c ∈ K`, `f` splits as `g·h` with both factors monic and
  `deg g = ` the multiplicity of `c` as a root of `f mod t`.  So a special fibre with two
  distinct roots always breaks `f` into strictly smaller monic pieces.

### Where the Newton–Puiseux induction now stands

The induction on `deg f` for `K` algebraically closed of characteristic zero is:

1. fibre has two distinct roots → `exists_monic_factor_of_rootMultiplicity` splits `f`
   into strictly smaller monic factors — **built**;
2. fibre is `(X − c)^d` → translate `X ↦ X + c` and remove the `X^{d−1}` coefficient
   (Tschirnhaus, needs `d` invertible, hence characteristic zero) — **not built**;
3. then the Newton polygon's smallest slope `μ = p/q > 0` and the substitution
   `t ↦ s^q`, `X ↦ s^p·Y` make the new special fibre a face polynomial with at least two
   terms and zero `Y^{d−1}` coefficient, hence at least two distinct roots — return to
   step 1 — **not built**;
4. a simple root of the fibre lifts directly by `exists_isRoot_powerSeries`
   (`HTGeometry/PowerSeriesRootLift.lean`) — **built**.

Step 3 needs the ring map `K⟦t⟧ → K⟦s⟧`, `t ↦ s^q`, which is the next component.

### Remaining Lean layers for the card

- Hilbert irreducibility (§1) — the chain above;
- for §4, **not** o-minimality of `R_an`.  See the next entry.

## §4 does not need o-minimality (2026-08-10)

The card lists "o-minimality of `R_an`" (Denef–van den Dries, Gabrielov) as a remaining
input.  It is not needed.  The inequality part of §4 follows from a strictly weaker and
purely algebraic input plus a corpus lemma that is already built.

**The replacement argument.**  Fix `s` and `T`.

1. `S_s`, the set of states preparable from `Ω` by at most `s` two-qubit gates, is
   **semialgebraic** in `ℝ^{2D}`: there are finitely many gate-support patterns, each
   parameter space `U(4)^s` is compact semialgebraic, the output coordinates are
   polynomial in the gate entries, and Tarski–Seidenberg preserves semialgebraicity
   under the projection that forgets the parameters.  So
   `S_s = ⋃_{finite} ⋂_{finite} {x : p_{ij}(x) ⋛ 0}` for real polynomials `p_{ij}`.
2. Each coordinate of `γ(t) = e^{−itH}Ω` is a finite algebraic combination of `sin` and
   `cos`, so every `p_{ij} ∘ γ` is real analytic on all of `ℝ`.
3. `HTGeometry/RealAnalyticZeroFiniteness.lean` — already built, unconditional and
   axiom-clean — gives `finite_zeros_of_analyticOnNhd`: a real-analytic function on a
   neighbourhood of `[−T,T]` that is not identically zero has finitely many zeros there.
   Hence each `{t ∈ [−T,T] : p_{ij}(γ(t)) = 0}` is finite or everything, and each
   `{t : p_{ij}(γ(t)) > 0}` is open with finite boundary in `[−T,T]`.
4. A finite boolean combination of finite sets and open sets with finite boundary is a
   finite union of points and intervals.  If a nondegenerate interval occurred, it would
   contain a nonzero real algebraic time, contradicting equation (1).  So the set is
   finite, which is equation (2).

**What this changes.**  The card's §4 as written invokes the restricted-analytic
o-minimal structure `R_an` — a deep theorem about *analytic* definability.  The argument
above uses o-minimality of the *semialgebraic* structure only, and even that only through
the one-variable statement "a nonzero real-analytic function has finitely many zeros on a
compact interval", which the corpus already owns.  The single missing classical input is
therefore

> **Tarski–Seidenberg / quantifier elimination for real closed fields**, i.e. that the
> projection of a semialgebraic set is semialgebraic.

Neither mathlib nor the corpus has semialgebraic sets: `rg semialgebraic` over
`Mathlib/` returns nothing, and `Mathlib/FieldTheory/IsRealClosed/Basic.lean` carries only
the square/odd-power basics (`nonneg_iff_isSquare`, `exists_eq_pow_of_odd`) — no Sturm
sequences, no sign tables, no quantifier elimination.  So this is a from-scratch build
too, but a bounded and purely algebraic one, whereas o-minimality of `R_an` is not.

### Remaining Lean layers for the card, restated

- **Hilbert irreducibility** (§1), through the Newton–Puiseux chain; the Hensel
  factorisation step of that chain is now built;
- **Tarski–Seidenberg** (§4), replacing the previously recorded o-minimality of `R_an`.
