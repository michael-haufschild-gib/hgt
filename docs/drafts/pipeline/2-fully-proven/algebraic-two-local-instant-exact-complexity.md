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

## Newton–Puiseux proved in Lean (2026-08-10)

The second link of the Hilbert-irreducibility chain is closed.  Neither mathlib nor the
corpus had Puiseux series, the Newton polygon, or the Newton–Puiseux theorem; all three
are now built, unconditionally and axiom-clean, and wired into the `HTGeometry` umbrella.

> **`HTGeometry/NewtonPuiseuxRoot.lean` — `exists_isRoot_map_expand`.**  Let `K` be
> algebraically closed of characteristic zero.  Every monic `f ∈ K⟦t⟧[X]` of positive
> degree has a root in `K⟦t⟧` after a ramification `t = s^N`:
> `∃ N ≠ 0, ∃ y : K⟦s⟧, (f.map (PowerSeries.expand N).toRingHom).IsRoot y`.

Ramification is `PowerSeries.expand`, which mathlib already supplies
(`RingTheory/PowerSeries/Expand.lean`, `expand_mul`, `coeff_expand`, `order_expand`), so
"root in the Puiseux field" needs no new field construction: it is a power-series root of
the expanded polynomial, and expansions compose.

Supporting modules, all new:

- **`HTGeometry/NewtonSlopeTransform.lean`** — the slope substitution `t = s^q`,
  `X = s^p·Y`, divided by `s^{p·d}`.  `shiftPow` divides a power series by `X^k`;
  `newtonTransform` assembles the substituted polynomial; `monic_newtonTransform` keeps
  monicity and degree; `coeff_map_constantCoeff_newtonTransform` identifies the special
  fibre of the transform as the *edge polynomial*, coefficientwise
  `coeff (p(d−i)) (expand q aᵢ)`; **`isRoot_map_expand_of_isRoot_newtonTransform`** turns a
  root of the transform into the root `s^p·y` of the expanded polynomial; and
  **`map_expand_newtonTransform`** shows a further ramification of a transform is again a
  transform, `newtonTransform f (Np) (Nq)` — this is what lets a recursive call's own
  ramification be pulled back through the substitution.
- **`HTGeometry/NewtonMinimalSlope.lean`** — **`exists_newton_slope`**: for `f` with
  special fibre `X^d` and some vanishing coefficient below the top, there are `p, q ≥ 1`
  with `X^{p(d−i)} ∣ expand q aᵢ` for every `i`, sharply at one index.  The minimum is
  selected in `ℚ` by `Finset.exists_min_image` and immediately cross-multiplied back to
  `ℕ`, so no rational arithmetic survives into the statement.
- **`HTGeometry/TschirnhausShift.lean`** — `hasseDeriv_natDegree_sub_one` computes the
  Hasse derivative of order `d−1` of a monic polynomial (it is linear: constant term the
  second coefficient, slope the degree), whence
  `taylor_coeff_natDegree_sub_one` and **`exists_taylor_coeff_eq_zero`**: in
  characteristic zero a translation removes the second coefficient, and the translation is
  no larger than that coefficient, so a special fibre `X^d` survives the shift.
- `HTGeometry/PowerSeriesFactorization.lean`, `HTGeometry/HenselFactorization.lean`,
  `HTGeometry/PowerSeriesRootLift.lean` — the previous entry.

**The induction.**  On the degree `d`.  Let `F = f mod t`, monic of degree `d`, and let `c`
be a root of `F` (`K` is algebraically closed) of multiplicity `m`.

*If `m < d`*, `exists_monic_factor_of_rootMultiplicity` splits `f = g·h` with `g` monic of
degree `m ∈ [1, d)`; recurse on `g`.

*If `m = d`*, then `F = (X − c)^d`.  Translate by `c` and apply the Tschirnhaus shift: the
fibre becomes `X^d` and the second coefficient vanishes.  If the polynomial is now `X^d`,
the root is `0`.  Otherwise take the minimal Newton slope and transform.  The transformed
fibre `G` is monic of degree `d`, still has vanishing second coefficient, and is *not*
`X^d` (sharpness at the minimising index).  If `G` were `(Y − c′)^d` its second
coefficient would be `−d·c′`, forcing `c′ = 0` in characteristic zero and hence `G = Y^d` —
contradiction.  So every root of `G` has multiplicity below `d`, and the first case applies
to the transform, giving a factor of degree in `[1, d)`; recurse on it, pull the recursive
ramification back through `map_expand_newtonTransform`, and push the root out through the
substitution and the two translations.

Characteristic zero enters exactly once — in the Tschirnhaus shift and in the
`−d·c′ = 0 ⇒ c′ = 0` step — and algebraic closedness exactly twice, to produce a root of
each special fibre.

### Where the Hilbert-irreducibility chain now stands

```text
HIT  ←  Eisenstein's theorem on algebraic power series   ← NOT BUILT
     ←  Newton–Puiseux                                   ← BUILT (this entry)
     ←  Newton polygon                                   ← BUILT (this entry)
     ←  Hensel factorisation                             ← BUILT (previous entry)
```

The remaining mathematical content is the arithmetic half: Eisenstein's theorem (the
Puiseux coefficients of an algebraic power series have a common denominator) and then
Hilbert irreducibility itself.

### Remaining Lean layers for the card

- Hilbert irreducibility (§1): Eisenstein's theorem, then HIT;
- Tarski–Seidenberg (§4), as re-scoped two entries above.

## Newton's lemma without a simple root (2026-08-10)

The next link of the Hilbert-irreducibility chain is Eisenstein's theorem on algebraic
power series — the statement that the Puiseux coefficients of an algebraic power series
have geometrically bounded denominators.  Its proof is a Newton iteration in which the
derivative is *not* a unit, so the tool it needs is Hensel's lemma in the
`|F(y₀)| < |F′(y₀)|²` form.  mathlib has only the simple-root form
(`HenselianRing.is_henselian`, monic polynomial, unit derivative); the general form was
absent from mathlib and the corpus.  It is now built.

`HTGeometry/HenselDefectRoot.lean` (new, in the umbrella, axiom-clean):

> **`exists_isRoot_of_sq_dvd`.**  Let `S` be complete for an ideal `I`, `F ∈ S[X]`, and
> `y₀ ∈ S` with `d = F′(y₀)` and `F(y₀) = d² · ε` for some `ε ∈ I`.  Then `F` has a root
> `y₀ + d·z` with `z ∈ I`.
>
> **`isRoot_unique_of_sq_dvd`.**  Over a domain that root is unique: two roots of the shape
> `y₀ + d z` with `z ∈ I` and `d ≠ 0` coincide.

No monicity, no unit, no simple root, and the ideal is arbitrary.  The proof does not
iterate: substituting `y = y₀ + d·Z` makes every Taylor term beyond the linear one carry
`d²`, so the substituted polynomial is `d²` times

`H(Z) = ε + Z + (higher terms)`,

whose reduction modulo `I` is exactly `Z` — the degeneracy has been absorbed into the
substitution.  `H` is never monic, which is why the divisor form
`exists_monic_dvd_of_coeffMem_modByMonic` (built two entries above, and deliberately stated
without assuming `f` monic) is what applies to it, with the linear divisor `Z - z₀`.

Supporting declarations, all reusable:

- `shiftScale F y₀ h` — the polynomial `Z ↦ F(y₀ + h·Z)`, with `coeff_shiftScale`
  (`= (taylor y₀ F).coeff k · hᵏ`) and `eval_shiftScale`;
- `rychlikQuotient` and `C_sq_mul_rychlikQuotient` — the division of `shiftScale F y₀ d` by
  `d²`, valid exactly under `F(y₀) = d²ε` and `d = F′(y₀)`;
- `eval_divByMonic_X_sub_C` — the quotient by `X − a` at `a` is the derivative at `a`;
- `exists_eval_add_eq` — the Taylor expansion to second order,
  `F(a+h) = F(a) + F′(a)h + h²B`;
- `polyShiftPow`, `shiftPow_X_pow_mul` — coefficientwise division of a polynomial over a
  power-series ring by `Xᵏ`;
- **`exists_isRoot_of_defect`** — the `K⟦t⟧` specialisation, now a corollary: if
  `F′(y₀) = t^r · unit` and `t^{2r+1} ∣ F(y₀)`, then `F` has a root congruent to `y₀`
  modulo `t^{r+1}`.

`shiftPow` and `constantCoeff_eval`/`mem_span_X_iff` were generalised in place from a field
to an arbitrary commutative ring, so nothing is duplicated.

### Why this is the right next tool for Eisenstein

Over a discrete valuation ring `A` with fraction field `K`, let `y ∈ K⟦t⟧` be a root of a
monic `F ∈ A[t][X]` and let `r` be the `t`-order of `F′(y)`.  Rescaling `t ↦ c t`
(`PowerSeries.rescale`) turns `y` into `w = y(ct)`, a root of `G = F(ct, X)`, and for `c`
divisible by a high enough power of the uniformiser the truncation `w₀` of `w` below degree
`2r+1` lies in `A⟦t⟧` and satisfies `G(w₀) = G′(w₀)² · ε` with `ε` in the variable ideal.
`exists_isRoot_of_sq_dvd` then produces a root of `G` in `A⟦t⟧`, and
`isRoot_unique_of_sq_dvd` identifies it with `w`, i.e. `c^n a_n ∈ A` for all `n` — which is
Eisenstein's theorem.  The remaining work is the valuation bookkeeping that makes the
`d² ε` hypothesis hold for large `v(c)`.

### Remaining Lean layers for the card

- Hilbert irreducibility (§1): Eisenstein (valuation bookkeeping + assembly over the
  finitely many bad primes), then HIT itself;
- Tarski–Seidenberg (§4).

## Eisenstein: the recursion and the denominator calculus (2026-08-10)

Two more links of the Hilbert-irreducibility chain, both new and both axiom-clean.

### The recursion

`HTGeometry/EisensteinRecursion.lean` — **`coeff_deriv_mul_coeff_eq`**:

> If `F.eval y = 0` over a power-series ring and `(F′(y))_j = 0` for all `j < r`, then for every
> `n > r`
>
> `(F′(y))_r · y_n = − (F(y_{<n}))_{n+r}`,
>
> where `y_{<n} = truncPS n y` is the truncation of `y` below degree `n`.

The right-hand side involves only `y_0, …, y_{n−1}`, so this *is* the recursion that computes an
algebraic power series, and the only denominator it introduces per step is the single fixed element
`(F′(y))_r`.  The proof is the second-order Taylor expansion at the truncation
(`exists_eval_add_eq`, built in the previous entry): with `y = y_{<n} + η` and `Xⁿ ∣ η`, the
quadratic remainder is divisible by `X^{2n}` and invisible in degree `n + r` exactly when `n > r`;
the linear term is `∑_{j ≥ n} (F′(y_{<n}))_{n+r−j} y_j`, and `F′(y_{<n})` agrees with `F′(y)` below
degree `n`, whose coefficients below `r` vanish — leaving the single term `j = n`.  No monicity, no
field, no domain.

### The denominator calculus

`HTGeometry/CoeffDenominatorBound.lean` — the bookkeeping the induction runs on.  For a subring
`A` of a field `K` and `q ∈ A`:

- `IsPowMul A q β x` — `x = q^β · a` for some `a ∈ A`, with `add`, `sum`, **`mul`** (gains add),
  `mul_left`, `mono`, and `isPowMul_zero_iff_mem`;
- **`CoeffBnd A q κ β f`** — `q^{κN} · f_N ∈ q^β · A` for every `N`: denominators grow at most
  geometrically, *with a gain* `q^β`; with `add`, `neg`, **`mul`** (`β + γ`), **`pow`** (`i·β`),
  `coeffBnd_of_coeff_mem`, and `truncPS`.

The gain is the whole point.  Each step of the recursion loses one factor of `(F′(y))_r`; a term of
`F(y_{<n})` that is a product of two or more bounded factors gains `2β ≥ 2`, so it pays for that
loss, while a term linear in `y_{<n}` gains only `β` and is instead paid for by the strict drop of
the index (`j ≤ n − 1` against `n`), and the constant term is paid for by `n` being large.  That
three-way split — `F(w) = F(0) + F′(0)·w + w²·(…)`, which `exists_eval_add_eq` supplies at `w = 0`
— is exactly how the induction will be organised.

### Remaining Lean layers for the card

- Eisenstein's theorem itself: the parameter choice (`κ`, the gain `β`, the cut `N₀`) and the strong
  induction on `n` using the two modules above, then the assembly over the finitely many bad primes;
- Hilbert irreducibility on top of it;
- Tarski–Seidenberg (§4).

## Eisenstein's theorem proved at a simple root (2026-08-10)

`HTGeometry/EisensteinSimpleRoot.lean` (new, in the umbrella, axiom-clean) closes the
unramified case of Eisenstein's theorem on algebraic power series.

> **`exists_coeffBnd_of_isRoot`.**  Let `A` be a subring of a field `K` whose fraction
> field is `K`, let `F` be a polynomial whose coefficients are power series with
> coefficients in `A`, and let `y ∈ K⟦t⟧` be a root of `F` with `y₀ = 0` and `(F′(y))₀ ≠ 0`.
> Then there is a nonzero `q ∈ A` with
>
> `q^{2N} · y_N ∈ q · A`   for every `N`,
>
> i.e. the denominators of the coefficients of `y` grow at most geometrically.

The scaling element is constructed, not assumed: `q` is `(F′(y))₀` times whatever clears
the denominators of `(F′(y))₀`, `y₁` and `y₂`.

**The mechanism.**  The recursion `(F′(y))₀ · y_n = −(F(y_{<n}))_n` loses one factor of
`(F′(y))₀` per step, and the split `F(w) = F₀ + F₁·w + w²·Q(w)` (with `Q = F.divX.divX`,
`eval_split`) pays for it three different ways — which is exactly why a single crude
"ring of bounded denominators" argument cannot work:

- `F₀` sits in `A`, and the normalisation `q^{2n}` is a large power once `n ≥ 3`;
- `F₁·w` is **linear** in `w`, and pays through the strict drop of the index: `w` is the
  truncation below degree `n`, so every surviving coefficient sits at index `≤ n − 1`,
  worth one factor `q²`;
- `w²·Q(w)` is **quadratic**, and pays through the gain: two bounded factors gain `q²`
  (`CoeffBnd.mul`).

The exponent `2` is forced: the index drop must be worth at least the loss `q¹`, and the
gain must beat it too.  With gain `1` and exponent `2` all three mechanisms clear, and the
base cases reduce to `y₀ ∈ qA` (automatic after translating `y₀` to zero) plus two
denominators.

Added to `HTGeometry/CoeffDenominatorBound.lean`: `CoeffBnd.mono`, `CoeffBnd.sum`, and
**`CoeffBnd.eval`** — evaluating a polynomial with `A`-coefficients at a bounded series is
bounded.

### What remains for full Eisenstein

1. **The ramified reduction** `r ≥ 1 → r = 0`.  All the pieces exist: the substitution
   `y = y₀ + t^{r+1}z` followed by division by `t^{2r+1}` (`shiftScale`, `polyShiftPow` in
   `HenselDefectRoot.lean`) turns `F` into a polynomial `H` with `H = α + u′Z + O(t)`, so
   `H′(z)` has **nonzero constant term** — the defect is removed exactly as in Newton's
   lemma, and `EisensteinSimpleRoot` then applies to `z`.  `H`'s coefficients have a single
   fixed denominator, cleared by replacing `H` with `D·H` (the recursion does not need
   monicity).
2. **The translation** making `y₀ = 0`, which needs `y₀ ∈ A` — automatic for `A`
   integrally closed and `F` monic, since `y₀` is a root of the monic reduction.
3. **The global assembly** over the finitely many bad primes.

### Remaining Lean layers for the card

- Eisenstein: items 1–3 above; then Hilbert irreducibility;
- Tarski–Seidenberg (§4).

## The ramified case of Eisenstein reduces to the simple one (2026-08-10)

`HTGeometry/EisensteinDefectReduction.lean` (new, in the umbrella, axiom-clean) removes the
defect from an algebraic power series, reducing Eisenstein's theorem to the unramified case
proved in the previous entry.

Definitions (over a field, no subring, no integrality):

- `defectRoot r y := shiftPow (r+1) (y − truncPS (2r+1) y)` — the `z` in
  `y = y₀ + t^{r+1}·z`, with `X_pow_mul_defectRoot` establishing that equation;
- `defectPoly r F y := polyShiftPow (2r+1) (shiftScale F y₀ (X^{r+1}))` — the polynomial
  `F(y₀ + t^{r+1}·Z)` divided by `t^{2r+1}`.

> **`isRoot_defectPoly_and_constantCoeff_deriv_ne_zero`.**  If `F.eval y = 0`, `(F′(y))_j = 0`
> for `j < r`, and `(F′(y))_r ≠ 0`, then
>
> `(defectPoly r F y).eval (defectRoot r y) = 0`  and
> `((defectPoly r F y)′ (defectRoot r y))_0 ≠ 0`.
>
> **`constantCoeff_defectRoot`.**  For `r ≥ 1` the reduced root has vanishing constant term.

So `z` is a root with a *simple* derivative and the normalisation `z₀ = 0` that
`EisensteinSimpleRoot.exists_coeffBnd_of_isRoot` requires — the two halves fit together.

The mechanism is the same defect removal as in Newton's lemma: `F′(y₀) = t^r·u` with `u` of
nonzero constant term (because `y₀ ≡ y` to order `2r+1`, so `F′(y₀) ≡ F′(y)` there), and
`t^{2r+1} ∣ F(y₀)` (because `F(y) = 0` and `y₀ ≡ y`).  Dividing the substituted polynomial by
`t^{2r+1}` leaves `H` with `H₁ = u` and every `H_k`, `k ≥ 2`, of zero constant term, so its
reduction at `t = 0` is the linear polynomial `α + ū·Z` and `H′(z)` has constant term `ū ≠ 0`.

### Remaining Lean layers for the card

- **Integrality transport** for the reduction: `defectPoly`'s coefficients lie in `A` once
  `F`'s do and the first `2r+1` coefficients of `y` do — after rescaling the root by a
  common denominator `D`, which replaces `F` by `D^{deg F}·F(X/D)`.  Note
  `CoeffBnd A q 0 0 f` is exactly "all coefficients of `f` lie in `A`", so the existing
  `CoeffBnd.mul`/`.eval` already give the closure properties needed; what is missing is
  `shiftPow` and `hasseDeriv` preservation.
- then the assembly of full Eisenstein, and the global statement over the finitely many bad
  primes;
- Hilbert irreducibility;
- Tarski–Seidenberg (§4).

## Eisenstein's theorem, ramified case, proved (2026-08-10)

The reduction of the previous entry is now assembled into the theorem itself.

> **`EisensteinDefectReduction.exists_coeff_mem_of_isRoot_of_pos_defect`.**  Let `A` be a
> subring of a field `K` whose fraction field is `K`, let `F` be a polynomial whose
> coefficients are power series with coefficients in `A`, and let `y ∈ K⟦t⟧` be a root of `F`
> whose derivative `F′(y)` vanishes to order exactly `r ≥ 1`.  If the first `2r+1`
> coefficients of `y` lie in `A`, then there is a nonzero `q ∈ A` with
>
> `q^{2N} · y_N ∈ A`  for every `N`.

That is Eisenstein's theorem on algebraic power series in the ramified case.  Together with
`EisensteinSimpleRoot.exists_coeffBnd_of_isRoot` (the case `r = 0`) the analytic content is
complete; what is left is bookkeeping, not mathematics.

Supporting results added:

- `coeffMem_defectPoly` — the reduced polynomial keeps its coefficients in `A`, because only
  the first `2r+1` coefficients of `y` enter it (through `Polynomial.taylor` at the
  truncation);
- in `CoeffDenominatorBound.lean`: `coeffBnd_zero_zero_iff` (with exponent and gain both
  zero, `CoeffBnd` says exactly "all coefficients lie in `A`", so the existing
  `CoeffBnd.mul`/`.eval` supply the closure properties for free), `coeffMem_shiftPow`,
  `coeffMem_X_pow_mul`, `coeffMem_hasseDeriv`.

The transfer of the bound from the reduced root back to `y` is the index shift
`y = y₀ + t^{r+1}·z`: below degree `r+1` the shifted part contributes nothing, above it the
gain `q¹` of the reduced bound plus the fixed factor `q^{2(r+1)}` more than absorbs the
normalisation.

### Remaining Lean layers for the card

- **Uniform statement**: fold the `r = 0` case in (it needs only the translation
  `y ↦ y − y₀`, which is `Polynomial.taylor`, with `y₀ ∈ A` supplied by the same hypothesis),
  and drop the hypothesis "first `2r+1` coefficients in `A`" by rescaling the root by their
  common denominator — which replaces `F` by `D^{deg F}·F(X/D)`;
- the global statement over the finitely many bad primes;
- Hilbert irreducibility;
- Tarski–Seidenberg (§4).

## Eisenstein: uniform statement (2026-08-10)

`HTGeometry/EisensteinUniform.lean` (new, in the umbrella, axiom-clean) joins the two cases.

> **`exists_coeff_mem_of_isRoot`.**  Let `A` be a subring of a field `K` whose fraction field
> is `K`, let `F` have power-series coefficients in `A`, and let `y ∈ K⟦t⟧` be a root of `F`
> whose derivative `F′(y)` vanishes to order exactly `r` (any `r ≥ 0`).  If the first `2r+1`
> coefficients of `y` lie in `A`, then there is a nonzero `q ∈ A` with
>
> `q^{2N} · y_N ∈ A`  for every `N`.

The case `r = 0` is `exists_coeff_mem_of_isRoot_of_zero_defect`: the root is translated by its
own constant term (`Polynomial.taylor`), which is legitimate precisely because that constant
term lies in `A`, and then the normalised simple-root theorem applies.  Supporting:
`eval_taylor`, `derivative_taylor` (translation commutes with differentiation),
`coeffMem_taylor`.

### The one bookkeeping step left in Eisenstein

Dropping the hypothesis "the first `2r+1` coefficients of `y` lie in `A`".  The route is
`Polynomial.scaleRoots`, which mathlib supplies: with `D` the product of the finitely many
denominators of `y_0, …, y_{2r}` (built from the fraction-field hypothesis), `C D · y` is a
root of `F.scaleRoots (C D)`, whose coefficients `F_i · (C D)^{m−i}` are again in `A`, and

- `Polynomial.scaleRoots_eval₂_mul` gives the root statement;
- `derivative (F.scaleRoots s) = (derivative F).scaleRoots s` holds coefficientwise whenever
  `natDegree (derivative F) = natDegree F − 1`, i.e. in characteristic zero, so the derivative
  data transports with the nonzero scalar `s^{m−1}` — which changes neither the order of
  vanishing nor the nonvanishing at `r`.

The conclusion then carries the expected fixed extra factor: `∃ q d ≠ 0 in A`,
`d · q^{2N} · y_N ∈ A` — the standard form of Eisenstein's theorem.

### Remaining Lean layers for the card

- the `scaleRoots` step above; then the global statement over the finitely many bad primes;
- Hilbert irreducibility;
- Tarski–Seidenberg (§4).

## Eisenstein's theorem on algebraic power series — complete (2026-08-10)

`HTGeometry/EisensteinScaling.lean` (new, in the umbrella, axiom-clean) removes the last
hypothesis.  The theorem now reads, with **no condition on the root beyond being a root**:

> **`exists_coeff_mem_of_isRoot_of_frac`.**  Let `A` be a subring of a field `K` whose
> fraction field is `K`, let `F` be a polynomial whose coefficients are power series with
> coefficients in `A`, and let `y ∈ K⟦t⟧` satisfy `F.eval y = 0` with `F′(y)` vanishing to
> order exactly `r` (any `r ≥ 0`).  Then there are nonzero `q, D ∈ A` with
>
> `D · q^{2N} · y_N ∈ A`  for every `N`.

That is Eisenstein's theorem in its classical form: the denominators of an algebraic power
series grow at most geometrically.  Neither mathlib nor the corpus had it.

**The trick that avoids a characteristic hypothesis.**  The finitely many coefficients
`y_0, …, y_{2r}` are cleared by one `D ∈ A` (`exists_common_denominator`, a product over
`Finset.range`).  One then has a choice: scale the *root* or scale the *polynomial*.  Scaling
the root — `Polynomial.scaleRoots` — needs `deg (derivative F) = deg F − 1` to transport the
derivative data, hence characteristic zero and a degree side condition.  Scaling the
polynomial by the constant `(C D)^{deg F}` needs neither: multiplying by a nonzero constant
changes neither the roots nor the order of vanishing of the derivative, and
`coeffMem_C_pow_mul_eval` shows `(C D)^m · P.eval w ∈ A` whenever `P` has `A`-coefficients,
`D·w` is `A`-integral, and `m ≥ deg P` — because `(C D)^m = (C D)^{m−j}·(C D)^j` splits the
scalar across the `j`-th monomial.

Supporting: `coeffMem_mul`, `coeffMem_pow`, `coeffMem_C_pow`, `coeffMem_C_pow_mul_taylor`,
`coeffMem_C_pow_mul_defectPoly`, `exists_common_denominator`, and the two case theorems
`exists_coeff_mem_of_isRoot_of_zero_defect_of_frac` / `..._of_pos_defect_of_frac`.

### Where the Hilbert-irreducibility chain stands

```text
HIT  ←  Eisenstein's theorem on algebraic power series   ← BUILT (this entry)
     ←  Newton–Puiseux                                   ← BUILT
     ←  Newton polygon                                   ← BUILT
     ←  Hensel factorisation / Newton–Rychlik            ← BUILT
```

Every input below HIT is now formalized.  What remains is HIT itself: the specialisation
argument that uses the geometric denominator bound to force a branch that takes rational
values at infinitely many integers to be a rational function.

### Remaining Lean layers for the card

- Hilbert irreducibility, on top of the finished chain;
- Tarski–Seidenberg (§4).

## §4 needs neither o-minimality nor Tarski–Seidenberg (2026-08-10)

The card's §4 invokes o-minimality of `R_an`; an earlier entry above reduced that to
Tarski–Seidenberg.  **Both are unnecessary.**  The local finiteness of the exceptional times
follows from the parameter count that already carries §3, together with the corpus's
real-analytic zero finiteness.  Two new modules, both axiom-clean and in the umbrella, prove it.

### The mechanism

The `s`-gate state set is the image of a polynomial parametrisation with `m` real parameters.
One does not need to know that this image is semialgebraic — it is enough to have **one
polynomial** vanishing identically on it and not vanishing along the orbit.

`HTGeometry/ImageSeparatingPolynomial.lean`:

- **`exists_ne_zero_aeval_eq_zero`** — more polynomials than variables are algebraically
  dependent: for `Φ : Fin r → MvPolynomial (Fin m) K` with `m < r` there is `h ≠ 0` with
  `aeval Φ h = 0`.  This is `card_le_of_algebraicIndependent_of_mem_adjoin` (built for §3 of
  this card) applied inside the polynomial ring itself, where `adjoin (range X) = ⊤`;
- `aeval_eq_zero_of_aeval_eq_zero` — such an `h` vanishes at every point of the image, over
  any target algebra;
- **`exists_separating_polynomial`** — if the point `P` has algebraically independent
  coordinates and `m < r`, that same `h` satisfies `aeval P h ≠ 0`.  So one polynomial
  separates `P` from the whole image.

`HTGeometry/AnalyticImageFiniteness.lean`:

- `analyticOnNhd_aeval` — a polynomial in real-analytic functions is real-analytic;
- **`finite_meets_image`** — a real-analytic curve `γ : ℝ → ℝ^r` passing through a point with
  algebraically independent coordinates meets `{aeval u Φ : u ∈ ℝ^m}` only finitely often on
  any compact set, whenever `m < r`.

The proof is three lines of mathematics: compose the separating polynomial with the curve; the
result is real-analytic and nonzero at `t₀`; its zeros on a compact set are finite
(`RealAnalyticZeroFiniteness.finite_zeros_of_analyticOnNhd`); and every intersection is such a
zero.

### What this does for the card

Equation (2) — the local finiteness of low-complexity times — is now within reach with **no
external classical input at all**.  Instantiating `finite_meets_image` with

- `r = 2D` (the real coordinates of the state), `m = 16s` (the gate parameters),
- `γ` the orbit `t ↦ e^{−itH}Ω`, whose coordinates are finite algebraic combinations of `sin`
  and `cos` and so real-analytic,
- `t₀` any nonzero algebraic time, where §3 gives `D − 1` algebraically independent
  coordinates,

gives finiteness on `[−T, T]` as soon as `16s < D − 1`, which is exactly the hypothesis of
equation (2).  The remaining work is instantiation — the orbit's analyticity and the
identification of the `s`-gate set as a polynomial image — not new mathematics.

### Remaining Lean layers for the card

- §4: instantiate `finite_meets_image` at the orbit (analyticity of `t ↦ e^{−itH}Ω`, the gate
  map as a polynomial parametrisation).  **No o-minimality, no Tarski–Seidenberg.**
- §1: Hilbert irreducibility, the sole remaining classical input, now resting on a finished
  chain (Hensel → Newton polygon → Newton–Puiseux → Eisenstein, all built).

## §4's equation (2) assembled at corpus level (2026-08-10)

`HTGeometry/OrbitExceptionalTimes.lean` (new, in the umbrella, axiom-clean) turns the
separating-polynomial mechanism into the exceptional-time statement itself.

- `analyticOnNhd_cos_mul`, `analyticOnNhd_sin_mul`, **`analyticOnNhd_trigSum`** — a finite
  trigonometric sum `∑ⱼ (aⱼ cos(λⱼ t) + bⱼ sin(λⱼ t))` is real-analytic on all of `ℝ`;
- **`finite_meets_iUnion_images`** — a real-analytic curve through an algebraically independent
  point meets a *finite union* of polynomial images, each with fewer parameters than
  coordinates, only finitely often on a compact set (one image per gate-support pattern);
- **`finite_exceptional_times`** — the two combined, for a trigonometric orbit.

### The subfamily correction

The first version of the separating-polynomial theorem required *all* `r` coordinates to be
algebraically independent — which the card's orbit does **not** satisfy: only `D − 1` of the
`2D` real coordinates are independent (the others are constrained).  The theorems are therefore
also proved in subfamily form, and those are the applicable ones:

- `ImageSeparatingPolynomial.exists_separating_polynomial_subfamily` — it suffices that `k > m`
  of the coordinates, selected by any `σ : Fin k → Fin r`, be algebraically independent; the
  separating polynomial is then `rename σ` of one in `k` variables;
- `AnalyticImageFiniteness.finite_meets_image_subfamily`,
  `OrbitExceptionalTimes.finite_meets_iUnion_images_subfamily`,
  **`OrbitExceptionalTimes.finite_exceptional_times_subfamily`**.

With `k = D − 1` (the independent exponentials of §3), `r = 2D` and `m = 16s`, the hypothesis
`m < k` is exactly `16s < D − 1`, which is the hypothesis of equation (2).

*(Elaboration note for future work: passing the point family implicitly makes Lean attempt a
non-pattern higher-order unification `?P (σ i) ≡ γ (σ i) t₀` and time out; supply
`(P := fun i => γ i t₀)` explicitly.)*

### Remaining Lean layers for the card

- §4: the last identification — that the coordinates of `e^{−itH}Ω` are trigonometric sums
  (real and imaginary parts of `∑ⱼ wⱼ e^{−itEⱼ}`) and that the `s`-gate set is the union of
  finitely many polynomial images.  Mechanical; no classical input.
- §1: Hilbert irreducibility, resting on the finished chain
  (Hensel → Newton polygon → Newton–Puiseux → Eisenstein, all built).

## The spectral orbit is a trigonometric orbit (2026-08-10)

`HTGeometry/SpectralOrbitTrigForm.lean` (new, in the umbrella, axiom-clean) closes the last
identification for §4.

- `re_mul_exp_neg_mul_I` — `Re(w · e^{−iθ}) = Re w · cos θ + Im w · sin θ`;
- **`re_sum_exp`** — hence `Re(∑ⱼ wⱼ e^{−i Eⱼ t}) = ∑ⱼ (Re wⱼ · cos(Eⱼ t) + Im wⱼ · sin(Eⱼ t))`:
  every coordinate of a spectral orbit is a finite trigonometric sum;
- `im_eq_re_neg_I_mul` — `Im z = Re(−i z)`, so an *imaginary* coordinate is again of the form
  `Re(∑ⱼ wⱼ' e^{−i Eⱼ t})` with `wⱼ' = −i wⱼ`.  One statement therefore covers all `2D` real
  coordinates of a `D`-dimensional complex state, with no case split and no `Fin (2D)` index
  bookkeeping;
- **`finite_exceptional_times_of_spectralOrbit`** — for `w : Fin r → Fin n → ℂ` and real `E`, if
  `k` of the coordinates `Re(∑ⱼ w_{ij} e^{−i Eⱼ t₀})` are algebraically independent over `ℚ` and
  each of finitely many polynomial parametrisations has fewer than `k` parameters, the set of
  `t` in any compact set at which the orbit lies in one of those images is **finite**.

That is equation (2) of the card, in corpus form.  Instantiating it needs only `r = 2D`,
`k = D − 1`, `m = 16s`, `E` the spectrum, and `w` the eigenbasis times the overlaps — the
hypothesis `m < k` being exactly `16s < D − 1`.

### Where the card stands

- §1's arithmetic, §2 in full, §3 in full including equation (8) and Theorem A: **built**.
- §4: empty interior, nowhere density, analytic zero finiteness, the separating-polynomial
  mechanism, the finite-union statement, and now the trigonometric form of the orbit: **built**.
  No o-minimality, no Tarski–Seidenberg, no semialgebraic geometry anywhere.
- The single remaining classical input for the whole card is **Hilbert irreducibility** (§1),
  and its entire dependency chain — Hensel factorisation, Newton–Rychlik, Newton polygon,
  Newton–Puiseux, Eisenstein's theorem on algebraic power series — is now formalized,
  unconditionally and axiom-clean.

## Newton–Puiseux upgraded to the splitting form (2026-08-10)

`HTGeometry/NewtonPuiseuxSplitting.lean` (new, in the umbrella, axiom-clean):

> **`exists_prod_X_sub_C_map_expand`.**  Over an algebraically closed field of characteristic
> zero, a monic `f ∈ K⟦t⟧[X]` of degree `d` satisfies, after a single ramification `t = s^N`,
>
> `f.map (expand N) = ∏_{i < d} (X − C yᵢ)`   for some `y : Fin d → K⟦s⟧`.

Not just *a* root — all `d` of them.  The induction divides out one root supplied by
`exists_isRoot_map_expand`, applies the hypothesis to the monic quotient of degree `d − 1`, and
composes the two ramifications; composition is exactly `expand (N₂N₁) = expand N₂ ∘ expand N₁`.

The conclusion is an explicit product rather than `Polynomial.Splits` because the latter needs
the coefficient ring to be a field, and `K⟦t⟧` is not.

**Why this is the next thing HIT needs.**  Every argument that specialises `T` to a rational
value must know that *every* root of the specialised polynomial is the value of one of the
finitely many branches.  The splitting form is that statement at the formal level; what remains
to make it usable at a rational `t₀` is p-adic convergence of the branches, which is exactly
what Eisenstein's bound `D·q^{2n}·yₙ ∈ ℤ` provides: the series converges for `v_p(t₀) > 2 v_p(q)`.

### Remaining Lean layers for the card

- §1, Hilbert irreducibility: p-adic evaluation of a branch (the series has bounded denominators,
  so it converges on a disc and its value is a root of the specialised polynomial), then the
  ramification/specialisation argument;
- §4: instantiation only — `finite_exceptional_times_of_spectralOrbit` is the statement, and the
  gate map as a finite union of polynomial parametrisations is the last identification.

## A circuit is a polynomial parametrisation (2026-08-10)

`HTGeometry/PolynomialCircuitParametrisation.lean` (new, in the umbrella, axiom-clean) supplies
the last structural ingredient of §4: the states a circuit can prepare lie inside the image of a
*fixed* polynomial map, so `finite_meets_image` applies to them.

- `aeval_mulVec` — evaluating the entries commutes with matrix-vector multiplication;
- `aeval_matrix_prod` — and with products of matrices *taken in order*.  Matrix multiplication is
  not commutative, so the product must be a `List.prod`, not a `Finset.prod`; the proof is
  `List.prod_hom` for `AlgHom.mapMatrix`;
- `aeval_circuit` — the two combined: the output coordinates of a gate sequence are the evaluation
  of fixed polynomials at the gate entries;
- `paramIndex`, `genericMatrix`, `paramOf` — one indeterminate per matrix entry, and the parameter
  tuple carrying a given real gate sequence;
- **`map_aeval_genericMatrix`**, **`circuit_mem_image`** — every real gate sequence is an
  evaluation of the generic one, so the prepared state is `aeval (paramOf s n M)` of the fixed
  generic coordinates.

No unitarity is imposed anywhere: constraints only shrink the parameter set, and the argument needs
the reachable states to lie *inside* a polynomial image, not to fill it.  With `s` gates on an
`n`-dimensional space the parameter count is `s · n²` — for two-qubit gates acting on `n = D`, the
gate matrices are supported on four rows and columns, so the honest count is `16s` complex, `32s`
real, both `< D − 1` in the regime of equation (2).

### Remaining Lean layers for the card

- §4: only the arithmetic of assembling these pieces into equation (2) as the card states it
  (real/imaginary split of the complex circuit, and the constant `16`);
- §1: Hilbert irreducibility — p-adic evaluation of a Puiseux branch, then the specialisation
  argument.  Everything below it (Hensel, Newton polygon, Newton–Puiseux with splitting,
  Eisenstein) is built.

## §4 equation (2) proved end to end (2026-08-10)

`HTGeometry/CircuitExceptionalTimes.lean` (new, in the umbrella, axiom-clean) joins the two
halves into the exceptional-time theorem itself.

> **`finite_circuit_exceptional_times`.**  Let the orbit's coordinates be trigonometric sums
> `γᵢ(t) = ∑ⱼ (aᵢⱼ cos(λⱼ t) + bᵢⱼ sin(λⱼ t))`, let `k` of them (selected by `σ`) be
> algebraically independent over `ℚ` at one time `t₀`, and let the gate parameter count satisfy
> `s · r² < k`.  Then for every compact `S ⊆ ℝ`,
>
> `{t ∈ S | ∃ real gates M : Fin s → Matrix (Fin r) (Fin r) ℝ,  γ(t) = (∏ Mₖ) · v}`
>
> is **finite**, for any fixed rational input vector `v`.

That is equation (2) of the card: outside a finite set of times, the orbit is not reachable by a
depth-`s` circuit.  `circuitCoords` and `aeval_circuitCoords` are the bridge — the prepared state
is the evaluation of fixed polynomials at the gate entries — and
`finite_meets_image_subfamily` supplies the finiteness.

**No external classical input anywhere in §4.**  Not o-minimality of `R_an`, not
Tarski–Seidenberg, not semialgebraic geometry.  The entire mechanism is: more polynomials than
variables are algebraically dependent (`ImageSeparatingPolynomial`), so one polynomial separates
an independent point from the image; composing it with the orbit gives a nonzero real-analytic
function; and a nonzero real-analytic function has finitely many zeros on a compact set
(`RealAnalyticZeroFiniteness`).

### Where the card stands

| Part | Status |
|---|---|
| §1 arithmetic (balanced ternary, cyclicity) | built |
| §2 relation-space collapse, equation (6) | built |
| §3 independence of exponentials, equation (8), Theorem A | built |
| §4 empty interior, nowhere density | built |
| §4 equation (2), local finiteness | **built (this entry)** |
| §1 Hilbert irreducibility | the sole remaining classical input |

Everything below Hilbert irreducibility — Hensel factorisation, Newton–Rychlik, Newton polygon,
Newton–Puiseux (root and splitting forms), Eisenstein's theorem on algebraic power series — is
formalized, unconditionally and axiom-clean.  What remains for §1 is the p-adic evaluation of a
Puiseux branch and the specialisation argument built on it.

## The formal-to-arithmetic bridge: p-adic evaluation of a branch (2026-08-10)

`HTGeometry/PadicPowerSeriesEvaluation.lean` (new, in the umbrella, axiom-clean) is the first
component of §1's remaining input.

mathlib already has evaluation of power series at a topologically nilpotent element as a *ring
homomorphism* (`PowerSeries.eval₂Hom`, in `RingTheory/PowerSeries/Evaluation.lean`), for a
complete separated **linearly topologized** target.  The one missing ingredient was that `ℤ_p` is
linearly topologized — mathlib has that instance only for the discrete topology and for
`WithIdeal`-adic topologies, not for `PadicInt`'s metric topology.  Note the target must be `ℤ_p`,
not `ℚ_p`: a field has no basis of neighbourhoods of zero consisting of ideals, so `ℚ_p` is *not*
linearly topologized.

- **`hasBasis_nhds_zero_span_pow`** — the closed balls around zero in `ℤ_p` are exactly the ideals
  `(p^n)`, so those ideals are a neighbourhood basis;
- **`isLinearTopology_padicInt`** — hence `IsLinearTopology ℤ_[p] ℤ_[p]`;
- `hasEval_of_norm_lt_one` — an element of norm below one is topologically nilpotent;
- **`padicEval`** — evaluation `PowerSeries ℤ →+* ℤ_[p]` at any such element, a ring
  homomorphism;
- **`isRoot_padicEval`** — a formal root specialises: if `g.eval z = 0` for `g` a polynomial with
  power-series coefficients over `ℤ` and `z ∈ ℤ⟦t⟧`, then
  `(g.map (padicEval a)).eval (padicEval a z) = 0`.

**Why this is the shape that works.**  Eisenstein's theorem gives `D·q^{2n}·yₙ ∈ ℤ`, so
`z := D · rescale (q²) y` has *integer* coefficients, and `y` is recovered from `z` by scaling.
Under the same scaling the defining polynomial `f ∈ ℤ[t][X]` becomes
`g(t, X) = D^d · f(q² t, X/D)`, again with integer coefficients and monic in `X`.  So the whole
branch datum lives in `ℤ⟦t⟧`, exactly where `padicEval` applies — and a rational `t₀` with
`v_p(t₀) > 2 v_p(q)` is an admissible evaluation point.

### Remaining Lean layers for the card

- §1: the scaling step above (Eisenstein's output into `ℤ⟦t⟧` form), then the specialisation
  argument — ramification at a branch point forces a rational root to come from an unramified
  branch, which is where Hilbert irreducibility is finally concluded;
- §4: complete.

## The branch datum put into integral form (2026-08-10)

`HTGeometry/EisensteinIntegralForm.lean` (new, in the umbrella, axiom-clean) connects Eisenstein's
bound to the domain of `padicEval`.

- `scaledRoot D q y := C D * rescale (q²) y` — coefficients `D · q^{2N} · y_N`
  (`coeff_scaledRoot`), which Eisenstein places in the base ring (`coeffMem_scaledRoot`);
- `scaledPoly D q f := (f.map (rescale (q²))).scaleRoots (C D)` — the matching
  `D^{deg f} · f(q² t, X/D)`, integral whenever `f` is (`coeffMem_scaledPoly`);
- **`eval_scaledPoly`** — the rescaled branch is a root of the rescaled polynomial.  Both
  operations are library ones (`PowerSeries.rescale` for the variable,
  `Polynomial.scaleRoots` for the root); the content is that they match up, via
  `Polynomial.scaleRoots_eval₂_mul` at the identity homomorphism;
- **`exists_map_eq_of_coeff_mem_range`**, **`exists_polyMap_eq_of_coeff_mem_range`** — a power
  series, or a polynomial with power-series coefficients, whose coefficients lie in the range of a
  ring homomorphism is the image of one over the source.  This is what moves the branch datum from
  `ℚ⟦t⟧` with integral coefficients to genuine `ℤ⟦t⟧`.

The chain from a formal branch to a `p`-adic root is now complete as a sequence of proved steps:

```text
f.eval y = 0 over ℚ⟦t⟧
  → Eisenstein: D q^{2N} y_N ∈ ℤ                        (EisensteinScaling)
  → scaledPoly / scaledRoot: integral root equation      (this entry)
  → lift along ℤ ↪ ℚ: the datum lives in ℤ⟦t⟧            (this entry)
  → padicEval at ‖a‖ < 1: a root in ℤ_p                  (PadicPowerSeriesEvaluation)
```

### Remaining Lean layers for the card

- §1: assembling the four steps above into one statement, then the specialisation argument
  (ramification at a branch point forces a rational root to come from an unramified branch) —
  the last mathematical content of Hilbert irreducibility;
- §4: complete.

## From a rational branch to a p-adic root — assembled (2026-08-10)

`HTGeometry/IntegralBranchSpecialisation.lean` (new, in the umbrella, axiom-clean) joins the four
steps into single statements.

- `hfrac_int_range` — every rational is cleared into `ℤ` by its denominator, so `ℚ` is the fraction
  field of `(Int.castRingHom ℚ).range` in the sense Eisenstein requires;
- **`exists_integral_root_form`** — a power-series root of a polynomial with integral coefficients
  over `ℚ⟦t⟧`, whose derivative does not vanish identically at the root, has an *integral model*:
  there are `g : ℤ⟦t⟧[X]` and `z : ℤ⟦t⟧` with `g.eval z = 0`.  The transfer is by injectivity of
  `PowerSeries.map` along `ℤ ↪ ℚ`;
- **`exists_padic_root_of_branch`** — hence for every prime `p` and every `a ∈ ℤ_p` with `‖a‖ < 1`,
  the specialised polynomial `g.map (padicEval p a)` has the root `padicEval p a z` in `ℤ_p`.

So the formal branches of an algebraic function are not merely formal: they take values, and those
values are roots of the specialised polynomial.  That is precisely the arithmetic input a
specialisation argument consumes.

### Remaining Lean layers for the card

- §1: the specialisation argument itself.  With branch values in hand, the remaining content of
  Hilbert irreducibility is the ramification step — at a branch point of ramification index `e > 1`,
  choosing `v_p(t − b)` coprime to `e` forces any root of the specialised polynomial that comes
  from that branch to generate a ramified extension of `ℚ_p`, hence to be irrational.  The inputs
  still to build are: the ramified Puiseux branch as a series in `t^{1/e}` (available from
  `NewtonPuiseuxSplitting` after `expand`), and the valuation bookkeeping in `ℚ_p`.
- §4: complete.

## The valuation half of the ramification step (2026-08-21)

`HTGeometry/PadicRamifiedSpecialisation.lean` (new, umbrella-wired, axiom-clean) supplies the local
arithmetic of §1's specialisation argument.

| Card item | Declaration |
|---|---|
| the valuation of an `e`-th power is divisible by `e` | `dvd_valuation_pow` |
| **no `e`-th root of a `p`-adic number of indivisible valuation** | `not_pow_eq_of_not_dvd_valuation`, `not_pow_eq_ppow` |
| coprimality is the usable form of indivisibility | `not_dvd_of_coprime` |
| the specialised polynomial has no `p`-adic root once every root determines an `e`-th root of the parameter | `no_padic_root_of_ramified_branch` |
| hence no rational root | `no_rational_root_of_ramified_branch` |
| `e·v(y) = k·v(π)` from the norm identity | `valuation_eq_of_norm_pow_eq`, `not_norm_pow_eq` |
| **the branch value is irrational**: a branch `y = c·s^k·u` of ramification index `e` over a parameter of valuation coprime to `e`, with unit leading coefficient and unit factor, takes no value in `ℚ_p` | `not_padic_branch_value` |

`not_padic_branch_value` is the form the card actually needs, and it deliberately avoids Galois
theory of `ℚ_p((s))/ℚ_p((t))`: it does not show that the root *generates* the ramified extension,
only that its **norm** is forced into `p^{ℤ/e} \ p^ℤ`.  The only inputs are multiplicativity of the
norm on an extension field and the isometry of the embedding, so no theory of the spectral norm, of
ramification indices, or of valuation rings of extensions is used.

### Remaining Lean layers for the card

- §1: with the local half in place, HIT still needs its **global** half — the Puiseux branch of a
  branch point presented as `y = c·s^k·u` with `s^e = t - b`, `gcd(k, e) = 1`, `c` a unit, and the
  identification of the branch's ramification index.  `exists_prod_X_sub_C_map_expand`
  (`NewtonPuiseuxSplitting`) gives the splitting after one ramification `t = s^N`; what is missing is
  the *primitivity* bookkeeping that extracts the exact index `e | N` of one branch and its leading
  exponent `k` coprime to `e`.  After that, the specialisation `t - b = p^m·(unit)` with
  `gcd(m, e) = 1` and `not_padic_branch_value` rule out a rational root, which is the
  no-rational-root case of Hilbert irreducibility.
- §1: the step from "no rational root of the specialisation" to "the specialised Galois group is
  `S_D`" needs the same argument on the resolvents.  Note that §2 does **not** need the full
  symmetric group: for any 2-transitive `G` the permutation module `ℚ^D` is the trivial line plus an
  irreducible standard summand, which is all `(6)` uses.
- §4: complete.

## The Dumas no-root criterion (2026-08-21)

The ramification step does not need Puiseux branches at all when the specialised polynomial is
presented by its coefficients: the Newton condition on the coefficients already forces the root
valuation, and `ℚ_p` has integral value group.  Added to
`HTGeometry/PadicRamifiedSpecialisation.lean`:

| Card item | Declaration |
|---|---|
| **the Dumas criterion, no-root form**: `‖a_i‖^e < ‖a_0‖^{e-i}` for `0 < i < e` and `e ∤ v(a_0)` leave no root in `ℚ_p` | `no_padic_root_of_dumas` |
| the same for a monic polynomial | `no_padic_root_of_dumas_poly` |
| **hence no rational root** | `no_rational_root_of_dumas` |

The proof is the trichotomy of `‖y‖^e` against `‖a_0‖`.  Above it, every term of
`y^e = -∑_{i<e} a_i y^i` is strictly smaller than `‖y‖^e`; below it, every term of
`a_0 = -(y^e + ∑_{0<i<e} a_i y^i)` is strictly smaller than `‖a_0‖`; and at equality
`e·v(y) = v(a_0)`, contradicting indivisibility.  Only the ultrametric inequality
(`IsUltrametricDist.norm_add_le_max`, `norm_sum_le_of_forall_le_of_nonneg`) and the finite `sup'`
are used -- no Newton polygon, no valuation ring, no extension field.

This is the sharper of the two local forms: `not_padic_branch_value` needs the branch presented
as `c·s^k·u` inside an extension, whereas `no_padic_root_of_dumas` needs only the coefficients of
the specialised polynomial, which is exactly what a specialisation produces.

## §1's missing bridge, and an elementary algebraic route to it (2026-08-22)

**Status correction.**  The Lean-status entries above are stale on two counts.

1. **Hilbert irreducibility is closed.**  `HTGeometry.HilbertIrreducibility.hilbert_irreducibility`
   (one variable) and **`gal_card_of_specialisation`** (monic `f ∈ (ℚ[Y₁..Y_m])[T]` of degree `D`,
   separable, with `Nat.card Gal = D!` over `FractionRing`, and any nonzero `g`, gives `y ∈ ℚ^m`
   with `g(y) ≠ 0` and `Nat.card (f.map (eval y)).Gal = D!`) are unconditional and axiom-clean.  The
   p-adic ramification route recorded above is *provably insufficient* and must not be reopened;
   `PadicRamifiedSpecialisation` survives only as an independent local asset.
   `gal_card_of_specialisation` is exactly §1's "Hilbert irreducibility gives a Zariski-dense set of
   rational specializations whose characteristic polynomial still has Galois group `S_D`, avoiding
   the discriminant and `K_Ω`".
2. **What is actually missing is its hypothesis**: `Nat.card Gal = D!` for the *generic* two-local
   characteristic polynomial over `ℚ(Y)`.  The parent card
   `../3-formalized/new_scientific_knowledge/ht/generic-two-local-spectral-monodromy.md` is fully
   formalized, but its Lean conclusion is about **balanced integer** relations (no rational
   resonance), obtained from *topological* monodromy
   (`commonBaseTwoLocalMonodromySubgroup_eq_top`).  The step "geometric monodromy `S_D` ⟹ Galois
   group `S_D`" is Riemann existence and is **not** formalized.

**A route that avoids Riemann existence entirely.**  Work over `ℚ(i)`.  Split the two-local
parameters as `Y = (Y_sub, Y_rest)` where `Y_sub` = the diagonal terms (`Z_i`, `Z_iZ_j`) together
with a *single* transverse coefficient `u = u_i`, and `Y_rest` = every other transverse/off-diagonal
coefficient.

*Step 1 — the sub-family factors exactly.*  With only `u_i` transverse, the Hamiltonian is
block-diagonal in the `D/2` hypercube pairs `{x, x ⊕ e_i}`, so

  `f_sub = ∏_z (X² − (d_x + d_{x'})X + d_x d_{x'} − u²)`,   `z ∈ {±1}^{n-1}`,

with `δ_z = d_x − d_{x'} = 2(a_i + ∑_{k≠i} z_k b_{ik})` and block discriminant
`disc_z = δ_z² + 4u² = 4(A_z² + u²)`, `A_z = a_i + ∑_k z_k b_{ik}`.

*Step 2 — Kummer independence, and it is elementary.*  Over `ℚ(i)`,
`A_z² + u² = (A_z + iu)(A_z − iu)`, a product of **two distinct degree-one irreducibles** of the
polynomial ring, and the `2·2^{n-1}` factors so produced are pairwise distinct because the linear
forms `A_z` are.  Hence for every nonempty `S`, `∏_{z ∈ S} disc_z` has some irreducible factor to
odd multiplicity and is **not** a square.  By Kummer theory the `√disc_z` are independent, so

  `Gal(f_sub / ℚ(i)(Y_sub)) = (ℤ/2)^{D/2}`,

realized as the group generated by the individual hypercube-pair transpositions.

*Step 3 — transport to the full family through a field extension, not a specialisation.*  Put
`F = ℚ(i)(Y_sub, w)` with new indeterminates `w` indexed by `Y_rest`, and send
`Y_rest_j ↦ t·w_j`, `Y_sub ↦ Y_sub` into `F[[t]]`.  This is **injective** (expand a relation in
powers of `t`: each coefficient is a form in `w`), so it extends to a field embedding
`ℚ(i)(Y) ↪ E := Frac F[[t]]` and therefore `Gal(f/E) ↪ Gal(f/ℚ(i)(Y))` — the direction that costs
nothing, unlike a specialisation.  Modulo `t`, `f` is `f_sub`, whose `D/2` quadratic factors are
pairwise coprime (the `d_x` are distinct), so one-variable Hensel over the complete DVR `F[[t]]`
lifts the factorisation.  A lifted discriminant is a **unit** with constant term `disc_z`, and a
unit of `F[[t]]` is a square exactly when its constant term is a square in `F`; the same for any
product over a subset.  So Step 2's independence survives verbatim and
`Gal(f / E) ⊇ (ℤ/2)^{D/2}` contains every hypercube-pair transposition.

*Step 4 — generation.*  Ranging over `i` gives every hypercube edge transposition, and
`closure_hypercubeEdgeSwaps` (already in the corpus) says those generate `S_D`.  Hence
`Nat.card (Gal f) = D!` over `ℚ(i)(Y)`, hence over `ℚ(Y)`, which is `gal_card_of_specialisation`'s
hypothesis.

**Why the obvious shortcuts fail** (recorded so they are not retried).
* A *single* rational point cannot be found by avoiding the countably many rational hypersurfaces
  `Z(Q_k)`, one per balanced character: countably many hypersurfaces can cover `ℚ^m`.  This is
  exactly why §1 needs Hilbert irreducibility rather than the corpus's full-measure genericity.
* "One good specialisation forces the generic group" is the *easy* direction only for
  irreducibility of the resolvent, and no explicit `S_{2^n}` Hamiltonian is available; the direction
  actually needed, `Gal(specialised) ↪ Gal(generic)`, is Dedekind's theorem and is not in the
  corpus.  Step 3 replaces it by a genuine field embedding, which needs nothing.
* Over a local field with algebraically closed residue field the Galois group is cyclic, so no
  single completion can give `S_D`; the transpositions must be collected from several places, or —
  as in Steps 1–3 — from one place where the residue polynomial itself already has a large
  elementary abelian group.

### Bricks built for the route (2026-08-22)

Two new modules, both axiom-clean and wired into `GaloisForLFunctions.HTGeometry`.

`HTGeometry/SquareInQuadraticExtension.lean` (`Algebra` language) —
`isSquare_or_isSquare_mul_of_notMem`, `isSquare_or_isSquare_mul_of_isSquare_algebraMap`,
`not_isSquare_algebraMap`.

`HTGeometry/QuadraticTowerSquareClasses.lean` (704 lines) — **the multiquadratic Kummer machinery,
which mathlib does not have**, phrased entirely with `Subfield L` and elements of `L`:

| Step 2's needs | Declaration |
|---|---|
| one quadratic step creates only the square class of `r*r` | `isSq_or_isSq_mul_of_span` |
| `K(r) = K + K·r` when `r ∉ K`, `r*r ∈ K` | `mem_closure_insert_iff` |
| uniqueness of the coordinates, i.e. `{1, r}` is a `K`-basis | `span_unique` |
| the tower and its square-class statement | `QuadraticTower`, `exists_twist_isSq`, `notMem_of_independent` |
| the same with the tower data as bounded hypotheses | `exists_twist_isSq_of_partial`, `notMem_of_partial` |
| the concrete tower `M_j = F₀(ρ₀,…,ρ_{j−1})` built from Kummer independence alone | `radicalStage`, `span_radicalStage_of_independent`, `independentTower` |
| conjugation `x + y r ↦ x − y r` as a ring, then algebra, automorphism | `quadConj`, `quadConjEquiv`, `quadConjAlgEquiv` |
| it exchanges the two roots `(s ± r)/2` of the adjoined quadratic, which are distinct | `quadConj_rootPlus`, `quadConj_rootMinus`, `rootPlus_ne_rootMinus` |

The load-bearing design point is the *partial* form of the induction: `span` at step `j` can only
be proved after knowing `ρ_j ∉ M_j`, which itself follows from the square-class statement one stage
lower, so the two must be built by a single strong induction — the structure-field form alone is
circular.

Remaining on this route: feed `quadConjAlgEquiv` to `Polynomial.Gal.restrict` (taking `L` to be the
splitting field of the sub-family polynomial, so the top of the tower *is* `L` and no
isomorphism-extension theorem is needed), read the transposition off with
`Polynomial.Gal.restrict_smul`, and conclude `Nat.card Gal = D !` from
`Polynomial.Gal.galActionHom_injective` plus `closure_hypercubeEdgeSwaps`; then Step 3's Hensel
lift and Step 1's block decomposition.

### Step 3 simplified: simple-root lifting replaces Hensel factorisation (2026-08-22)

The deformation step does **not** need Hensel *factorisation* into quadratics.  Take
`F' =` the splitting field of `f_sub` over `F` (the multiquadratic field of the block
discriminants).  Modulo `t`, the deformed polynomial `g` is `f_sub`, which has `D` **distinct**
roots `(s_z ± ρ_z)/2` already in `F'`.  So every residue root is *simple*, and ordinary
simple-root Hensel lifting over `F'[[t]]` splits `g` completely there.

Uniqueness of the lift is what carries the Galois action: an automorphism `σ ∈ Gal(F'/F)` extends
coefficientwise to `PowerSeries F'` and fixes `g` (whose coefficients lie in `F[[t]]`), so it
sends the lift of a residue root to the lift of `σ` of that residue root.  Hence the block flip
`σ_{z₀}` acts on the roots of `g` exactly as the transposition of the `z₀`-block, and `Gal(g/E)`
contains it.

Two more modules, both axiom-clean and wired:

| Need | Declaration | Module |
|---|---|---|
| a squarefree non-unit of a UFD is not a square in the fraction field (this is the Kummer-independence criterion for the explicit discriminants) | `isSquare_of_isSquare_algebraMap`, `not_isSquare_algebraMap_of_squarefree` | `HTGeometry/SquarefreeNotSquareInFractionField.lean` |
| simple-root Hensel lifting over `PowerSeries R`, **with uniqueness** | `exists_isRoot_powerSeries_of_isUnit_deriv`, `existsUnique_isRoot_powerSeries_of_isUnit_deriv`, `isRoot_map_powerSeries` | `HTGeometry/PowerSeriesSimpleRootLift.lean` |

The existence half is `HenselDefectRoot.exists_isRoot_of_defect` at defect `r = 0` (the corpus
already owns `IsAdicComplete (span {X}) (PowerSeries R)`), and uniqueness is
`isRoot_unique_of_sq_dvd`.

Also built: `HTGeometry/GalPermutationRealization.lean` —
`mem_range_galActionHom_of_algEquiv`, `galActionHom_surjective_of_closure`,
`card_gal_eq_factorial_of_closure`, `card_gal_eq_factorial_of_swaps`: the interface turning
"enough root permutations are realized by field automorphisms" into `Nat.card p.Gal = D !`, via
`Polynomial.Gal.galActionHom_injective` and `Gal.galActionHom_restrict`.

### Remaining on this route

1. The explicit block decomposition of the two-local family under a single transverse coupling, and
   the identification of the block discriminants as `4(A_z² + u²)`.
2. Squarefreeness of `∏_{z ∈ S} (A_z + iu)(A_z − iu)` in `ℚ(i)[Y_sub]` for nonempty `S` — the
   linear forms `A_z ± iu` are `2·2^{n−1}` distinct degree-one irreducibles.
3. The injective substitution `Y_rest_j ↦ t·w_j` and the resulting field embedding.
4. The assembly: `exists_algEquiv_neg_index` → coefficientwise extension → root labels via the
   unique Hensel lifts → `mem_range_galActionHom_of_algEquiv` → `closure_hypercubeEdgeSwaps` →
   `card_gal_eq_factorial_of_closure`.

### The root-labelling obstruction, and how to remove it (2026-08-22)

Steps 1–3 give, for each site `i`, a perfect matching of transpositions inside `Gal(f/K)`.  Their
union must generate `S_D`, and for that the matchings have to be compared — but each site's
construction runs in its **own** local field, so a priori each supplies its own bijection
`hypercube vertices ≃ roots`, and `n` perfect matchings under unrelated relabellings need not span
a connected graph.  This is exactly the base-point/path problem that the topological proof solves
by carrying labelled root packets along paths (`LabeledPolynomialMatrixPath`).

Three ways out were examined and rejected:

* **Transitivity alone is not enough.**  `universalTwoLocalCharacteristicPolynomial_irreducible`
  gives a transitive `Gal`.  A transitive group containing a transposition has its transposition
  graph `Gal`-invariant, so its components form a block system; a transposition's two points always
  lie in one block.  Concluding `S_D` needs **primitivity**, which is not available.
* **Conjugating the transposition around by transitivity** only reproduces the same block system.
* **A place where every block degenerates at once** does not exist: `disc_z ∝ A_z² + u²` cannot
  vanish for all `z` simultaneously, since the `A_z` are distinct linear forms.

**The fix: put every root in one ring.**  Keep all `n` transverse couplings as independent
variables and never specialise them.  Over `F = ℚ(i)(Y_diag)` the multivariable power series ring
`F[[u_1,…,u_n]]` is complete local with residue field `F`, and modulo `(u)` the characteristic
polynomial is the *diagonal* one `∏_x (X − d_x)`, whose `D` roots are **distinct**.  Simple-root
Hensel lifting therefore places all `D` roots of `f` in `F[[u_1,…,u_n]]` itself, canonically
labelled by

  `r_x ≡ d_x  mod (u_1,…,u_n)`.

That labelling is intrinsic — no path, no base point, and the same for every site.

The site-`i` analysis then runs in the *larger* ring `F'_i[[u_j : j ≠ i]]`, where `F'_i` is the
multiquadratic extension of `F((u_i))` generated by the block discriminants `√(A_z² + u_i²)`.  It
contains `F[[u_1,…,u_n]]` (a power series in all the `u` is a power series in `u_{≠i}` with
coefficients in `F[[u_i]] ⊆ F((u_i))`), so it contains the very same `r_x`.  Modulo `(u_{≠i})` the
characteristic polynomial is block-diagonal in direction `i`, its residue roots `(s_z ± ρ_z)/2` are
simple in `F'_i`, and `r_x`, `r_{x⊕e_i}` are precisely the two lifts over the block `z` — because a
further reduction modulo `u_i` returns `d_x` and `d_{x⊕e_i}`.  The block flip of
`Gal(F'_i/F((u_i)))`, extended coefficientwise to `F'_i[[u_{≠i}]]`, therefore swaps `r_x` with
`r_{x⊕e_i}` and fixes every other root.

So all `n` matchings are matchings of the *same* labelled root set, their union is the hypercube
graph, and `closure_hypercubeEdgeSwaps` finishes.  The remaining Lean work is the multivariable
Hensel bookkeeping (`MvPowerSeries` or the iterated one-variable form already available in
`PowerSeriesSimpleRootLift`) and the explicit block/discriminant computation.

### Two more bricks (2026-08-22)

`HTGeometry/QuadraticTowerSquareClasses.lean` also carries `quadratic_eq_prod_linear`
(`X² − sX + p = (X − (s+r)/2)(X − (s−r)/2)` when `r² = s² − 4p`) and `quadratic_roots_ne`.

`HTGeometry/BlockDiagonalCharpolyQuadratic.lean` (new, axiom-clean, wired) supplies the
block-decomposition side:

| Need | Declaration |
|---|---|
| **the characteristic polynomial of a block-diagonal matrix is the product over blocks** (mathlib has this for `det`, not for `charpoly`) | `charpoly_blockDiagonal` |
| the symmetric block `!![α, u; u, β]`, its trace and determinant | `symmTwo`, `trace_symmTwo`, `det_symmTwo` |
| its characteristic polynomial `X² − (α+β)X + (αβ − u²)` | `charpoly_symmTwo` |
| its discriminant `(α − β)² + 4u²` | `discrim_symmTwo` |

With these, "the two-local family with a single transverse coupling at site `i` is block-diagonal in
the hypercube pairs, with block discriminants `(d_x − d_{x⊕eᵢ})² + 4uᵢ²`" is a reindexing
(`Matrix.charpoly_reindex` along `Config ≃ pairs × Bool`) plus `charpoly_blockDiagonal`.

### Steps 1 and 2 are built (2026-08-22)

Two further modules, both axiom-clean and wired.

`HTGeometry/HypercubeSingleTransverseBlocks.lean` — **Step 1**, in a form independent of the
particular diagonal energies:

| Card item | Declaration |
|---|---|
| arbitrary diagonal energies plus a single transverse flip at coordinate `0` | `singleTransverseHam` |
| the `Fin 2 × environment` reindexing of the cube | `cubeSplit`, `boolToggle_zero_cons` |
| **it is block-diagonal**, block `z` coupling `Fin.cons false z` with `Fin.cons true z` | `reindex_singleTransverseHam` |
| **its characteristic polynomial is the product of the block quadratics** `X² − (d₀+d₁)X + (d₀d₁ − u²)` | `charpoly_singleTransverseHam` |

A general site `i` reduces to site `0` by a relabelling of `Fin n → Bool`, which
`Matrix.charpoly_reindex` absorbs.

`HTGeometry/SumOfTwoSquaresNotSquare.lean` — **Step 2**, and it turned out to need no multivariate
irreducibility at all:

| Card item | Declaration |
|---|---|
| a product of distinct monic linear factors is squarefree and a non-unit, hence not a square in `K(X)` | `not_isSquare_ratFunc_prod_X_sub_C` |
| `(X + c)² + w² = (X − (−c + Iw))(X − (−c − Iw))` over a field containing `√(−1)` | `sq_add_sq_eq_prod_linear` |
| **the independence statement**: with the `c_z` pairwise distinct and `c_z − c_{z'} ≠ 2Iw` (which at `z = z'` is `Iw ≠ 0`), `∏_z ((X + c_z)² + w²)` is not a square in `K(X)` | `not_isSquare_prod_sq_add_sq` |

The whole Kummer independence is therefore a **one-variable separability** computation
(`Polynomial.separable_prod_X_sub_C_iff` plus `Separable.squarefree`), applied in the single
variable `a_i` with the remaining parameters in the coefficient field.  The separation hypothesis
`c_z − c_{z'} ≠ 2Iw` is automatic in the application, where the `c_z` lie in the span of the `b`'s
and `w` involves the independent variable `u`.

Remaining: the deformation (put all `D` roots in `F[[u_1,…,u_n]]` by iterated simple-root lifting,
labelled by `r_x ≡ d_x`), the coefficientwise extension of the block flip, and the final assembly
into `card_gal_eq_factorial_of_closure`.

### Step 3's mechanism is built (2026-08-22)

Three further modules complete the deformation mechanism; only the concrete gluing to the two-local
family remains.

`HTGeometry/MonicDistinctRootFactorization.lean` — `eq_prod_X_sub_C_of_monic_of_injective_roots`:
over any integral domain, a monic polynomial of degree `d` with `d` distinct roots is the product
of the corresponding linear factors.  This is what turns "the `D` residue roots lift" into "the
deformed polynomial splits, with root set indexed by the residue roots".

`HTGeometry/PowerSeriesSimpleRootLift.lean` (extended) — **the equivariance of the lift**:

| Card item | Declaration |
|---|---|
| a coefficientwise automorphism fixing `G` sends the lift of `y₀` to the lift of `φ y₀` | `map_lift_eq` |
| hence, if `φ` permutes the `d` residue roots by `π`, it permutes the lifts by the same `π` | `map_lift_eq_of_perm` |

Uniqueness of the Hensel lift is exactly what makes this work: both `φ(lift y₀)` and `lift(φ y₀)`
are roots congruent to `φ y₀`, so they coincide.

`HTGeometry/QuadraticRootFlip.lean` — the residue side:

| Card item | Declaration |
|---|---|
| the two roots `(s_z ± ρ_z)/2` of the `z`-th block | `quadRoot`, `quadRoot_true`, `quadRoot_false` |
| the product of the block quadratics splits into those linear factors | `prod_quadratic_eq_prod_quadRoot` |
| **an automorphism fixing every `s_z`, fixing `ρ_z` for `z ≠ z₀` and negating `ρ_{z₀}` acts as `Equiv.swap (z₀, true) (z₀, false)`** | `map_quadRoot_of_flip` |

Composing `map_quadRoot_of_flip` with `map_lift_eq_of_perm` gives: the block flip permutes the
*deformed* roots by the transposition of the `z₀` pair.  What is left is the concrete gluing —
identifying the two-local characteristic polynomial with the deformed object over
`F[[u_1,…,u_n]]`, reading the hypercube labels off the second reduction, and feeding the resulting
transpositions to `closure_hypercubeEdgeSwaps` and `card_gal_eq_factorial_of_closure`.

### The Laurent-series carrier of the flip (2026-08-22)

`HTGeometry/LaurentSeriesCoefficientAutomorphism.lean` (new, axiom-clean, wired) supplies the field
in which the deformed polynomial splits and the automorphism that acts on it.

| Card item | Declaration |
|---|---|
| a coefficientwise automorphism of `PowerSeries L` | `psRingEquiv` |
| a ring automorphism of a domain preserves the nonzero divisors | `map_nonZeroDivisors_of_ringEquiv` |
| **its extension to the Laurent series field** `LaurentSeries L`, which is the fraction field of `PowerSeries L` | `laurentRingEquiv` |
| the two agree on power series | `laurentRingEquiv_algebraMap` |
| **it fixes every series whose coefficients come from a subfield that `φ` fixes** — this is what makes it an *algebra* automorphism over the base | `laurentRingEquiv_fix_of_comp` |

`LaurentSeries L` is used rather than an abstract `FractionRing` because mathlib already carries
`IsFractionRing (PowerSeries K) (LaurentSeries K)` and the field instance, so the extension is
`IsLocalization.ringEquivOfRingEquiv` with no further plumbing.

## CORRECTION: the root-labelling fix recorded above does not work (2026-08-22, later)

The entry "The root-labelling obstruction, and how to remove it" proposed keeping all `n` transverse
couplings as independent variables so that every root lies in `F[[u_1,…,u_n]]`, labelled by
`r_x ≡ d_x mod (u)`, with the site-`i` analysis running in the larger ring `F'_i[[u_{≠i}]]`.
**That containment fails**, and the reason is structural rather than technical.

The site-`i` flips exist only because the block discriminants `δ_z² + 4u_i²` are **non-squares**.
Over `F(u_i)` they are (`not_isSquare_prod_sq_add_sq`).  But `F[[u_1,…,u_n]] ⊆ F((u_i))[[u_{≠i}]]`,
not `F(u_i)[[u_{≠i}]]` — and over `F((u_i))` the discriminant `δ_z² + 4u_i²` has constant term
`δ_z²`, a square, so Hensel makes it a square and **the flip disappears**.  Making `u_i` small is
exactly what destroys the ramification.

Forcing odd valuation instead requires tuning `δ_{z₀} = ±2i u_i`, i.e. tuning the diagonal parameter
`a_i`; then in the total degeneration `d_{x₀} = d_{x₀⊕eᵢ}`, so the base point depends on `(i, z₀)`
and the labellings again differ.  Comparing two base points is comparing two valuations, which is
monodromy along a connecting curve — the very thing being computed.

**What this leaves.**  Mathlib *does* have Jordan's theorem:
`Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem` — a **primitive** subgroup of
`Equiv.Perm α` containing a swap is everything.  So the labelling problem evaporates if primitivity
is available: **one** transposition from **one** site suffices, and all nineteen modules above
deliver that transposition.  The card's remaining mathematical content is therefore exactly:

> **primitivity of `Gal(f/K)` on the roots** — equivalently, `K(θ)/K` has no proper intermediate
> field, equivalently the degree-`D` eigenvalue cover has no intermediate cover.

Three routes to primitivity were examined and none is cheap: `of_prime_card` fails since `D = 2^n`;
the `(ℤ/2)^{D/2}` subgroup from one site only forces the block size to be even (a transposition's
two points always lie in one block, and blocks are unions of its orbits); and deducing it from the
corpus's *topological* monodromy is the Riemann-existence bridge again.  Recorded so the failed
route is not retried.

## Primitivity is NOT the remaining content: the labelling can be fixed by a chain of deformations (2026-08-22, later still)

The correction above concluded that "the card's remaining mathematical content is exactly primitivity
of `Gal(f/K)`".  That is too pessimistic.  **Primitivity is not needed at all**, because a transitive
group generated by transpositions along a *connected* graph is already the full symmetric group
(`closure_hypercubeEdgeSwaps`), and the labelling obstruction dissolves in a different arrangement:
deform **one variable at a time** instead of putting all transverse couplings into one power-series
ring.

### The arrangement

For `S ⊆ [n]` let `f_S` be the characteristic polynomial of
`D(a,b) + ∑_{j ∈ S} u_j X_j` over `K_S = ℚ(i)(a, b, (u_j)_{j∈S})`.  Then:

* `f_∅ = ∏_x (X − d_x)` is separable, and its roots are canonically labelled by `x ∈ {0,1}^n`.
* For `S' = S ∪ {k}`, `f_{S'} ≡ f_S` modulo `u_k`, and `f_S` is separable; so **every root of
  `f_{S'}` is the unique Hensel lift of a root of `f_S`** in `M_S[[u_k]]`, where `M_S` is the
  splitting field of `f_S` over `K_S`.  This is one-variable Hensel lifting — no multivariate
  completion is needed.
* A coefficientwise automorphism of `M_S[[u_k]]` induced by `σ ∈ Gal(f_S/K_S)` fixes
  `K_{S'} = K_S(u_k)`, so it restricts to an element of `Gal(f_{S'}/K_{S'})`, and by uniqueness of
  the lift it **permutes the lifted roots by exactly the same permutation**.  The two corpus modules
  that do this are already built and axiom-clean: `PowerSeriesSimpleRootLift.map_lift_eq_of_perm`
  and `LaurentSeriesCoefficientAutomorphism.laurentRingEquiv_fix_of_comp`.

Iterating from `S = {i}` up to `S = [n]`, one variable at a time, embeds
`Gal(f_{\{i\}}/K_{\{i\}})` into `Gal(f_{[n]}/K_{[n]})` **compatibly with the labelling by `x`**,
because at every step the labelling is "reduce modulo the new variable", and the composite of all
the reductions is the `d_x` labelling of `f_∅`.

### Why the earlier obstruction does not apply

The failed arrangement put every transverse variable into one power-series ring, so `u_i` became
"small" and `δ_z² + 4u_i²` acquired the square constant term `δ_z²`, killing the flip.  Here `u_i`
never becomes small: at the step that produces the site-`i` transpositions, `u_i` is a **variable of
the base field** `K_{\{i\}}`, over which `δ_z² + 4u_i²` is a genuine non-square
(`not_isSquare_prod_sq_add_sq`), and only the *other* couplings are deformed away.

### What this leaves

The site-`i` transpositions in the `d_x` labelling — already delivered by the nineteen modules
listed above (`HypercubeSingleTransverseBlocks`, `SumOfTwoSquaresNotSquare`, `QuadraticRootFlip`,
`GalPermutationRealization`) — plus the deformation chain, plus `closure_hypercubeEdgeSwaps`.  No
primitivity, no Jordan's theorem, no Riemann existence.

### Bricks for the deformation route (2026-08-22, continued)

Four more modules, all unconditional, axiom-clean and umbrella-wired.

| Card item | Declaration | Module |
|---|---|---|
| **mathlib gap**: splitting one variable off a multivariate power series ring, `A⟦u_S⟧ ≅ (A⟦u_{S∖{k}}⟧)⟦u_k⟧` | `optionCons`, `optionSplit`, `optionJoin`, `MvPowerSeries.optionEquivLeft`, `constantCoeff_optionSplit` | `MvPowerSeriesOptionSplit` |
| a simple root is determined by its residue — no completeness, only the second-order Taylor factorisation | `isRoot_unique_of_residue`, `isRoot_unique_mvPowerSeries` | `ResidueRootUniqueness` |
| one-variable deformation with a labelled root family, and its equivariance | `eval_derivative_ne_zero_of_separable`, `exists_powerSeriesRootFamily` | `PowerSeriesRootFamilyTransfer` |
| **every block transposition is realized** by a base algebra automorphism of the multiquadratic splitting field | `exists_algEquiv_swap_quadRoot` | `BlockFlipRealization` |

`MvPowerSeries.optionEquivLeft` is the piece that makes the labelling *order-independent*: whichever
order the deformation variables are introduced in, the resulting root lies in the same multivariate
power series ring, and `isRoot_unique_mvPowerSeries` says a root there is determined by its constant
coefficient.  That is exactly the comparison the "CORRECTION" section above found missing.

### Remaining on this route

1. the branch convention: choose `ρ_z` with `u = 0` value `d(1z) − d(0z)`, so that
   `quadRoot s ρ (z, b)` degenerates to `d(bz)` and the block transposition is the hypercube edge
   swap at the chosen site, in the `d_x` labelling;
2. the deformation of the remaining transverse couplings, one variable at a time, transporting each
   block transposition by `exists_powerSeriesRootFamily`;
3. the comparison of the resulting labellings inside `A⟦u_1,…,u_n⟧` via `optionEquivLeft` and
   `isRoot_unique_mvPowerSeries`;
4. `closure_hypercubeEdgeSwaps` and `card_gal_eq_factorial_of_closure`, then
   `gal_card_of_specialisation`.

### The labelling anchor is built (2026-08-22, later)

Five more modules complete the infrastructure the deformation route needs; all unconditional,
axiom-clean and umbrella-wired.

| Card item | Declaration | Module |
|---|---|---|
| a power series whose constant term is a nonzero square has a square root **with prescribed branch** — the choice that makes `quadRoot` degenerate to the right unperturbed level | `exists_powerSeries_sqrt_branch` | `PowerSeriesSqrtBranch` |
| one-variable deformation over a **residue ring** rather than a field: the derivative at a root is the product of the differences, and its residue is nonzero exactly when the residues of the roots are distinct | `eval_derivative_prod_X_sub_C`, `exists_powerSeriesRootFamily_of_residue` | `ResidueRootFamilyTransfer` |
| a transverse coupling in an **arbitrary** direction: relabelling moves the direction, so the block decomposition follows from the direction-zero case | `singleDirectionHam`, `cubeRelabel`, `reindex_singleDirectionHam`, `charpoly_singleDirectionHam` | `SingleDirectionTransverse` |
| **every hypercube edge swap in the transverse direction is realized**, on the original labelling of the cube | `directionRoot`, `swap_boolToggle_mem_realizedPermSubgroup` | `DirectionEdgeSwaps` |
| variable reindexing, the no-variable case, `MvPowerSeries σ A` is a domain, and **the canonical labelled root family**: a monic polynomial whose constant term splits with distinct roots splits over `A⟦u_σ⟧` with roots labelled by their constant coefficients | `mvRenameEquiv`, `mvPowerSeriesEmptyEquiv`, `isDomain_mvPowerSeries`, `eq_prod_X_sub_C_of_monic_of_injective_family`, `exists_mvPowerSeriesRootFamily` | `MvPowerSeriesRootFamily` |

`exists_mvPowerSeriesRootFamily` is the anchor: it is proved by splitting off one variable at a time
(`MvPowerSeries.optionEquivLeft`) and lifting with the residue-ring Hensel step, and
`isRoot_unique_mvPowerSeries` says the result does not depend on the order.  Every deformation route
must therefore produce the *same* labelled family, which is exactly what the earlier "CORRECTION"
section found missing.

### Remaining on this route

1. the two-local family over a general commutative ring (the corpus's `hypercubeTwoLocalMatrix` is
   `ℂ`-specific) and its degeneration to `singleDirectionHam` when the other transverse couplings
   vanish;
2. placing the direction-`i` picture inside `A⟦u_1,…,u_n⟧` — the square roots are power series in
   `u_i` by `exists_powerSeries_sqrt_branch`, so the roots are, and `isRoot_unique_mvPowerSeries`
   identifies them with the canonical family;
3. `closure_hypercubeEdgeSwaps` with `card_gal_eq_factorial_of_rootFamily`, then
   `gal_card_of_specialisation`.

### Block splitting of the variable set (2026-08-22, later still)

`MvPowerSeriesSumSplit` adds the mathlib gap the deformation actually needs:
`MvPowerSeries.sumEquiv : A⟦u_{σ ⊕ τ}⟧ ≃+* (A⟦u_σ⟧)⟦u_τ⟧`, splitting the variables into the block
kept in the base and the block deformed away, in one step rather than one variable at a time
(`sumCons`, `sumSplit`, `sumJoin`, `constantCoeff_sumSplit`).  With it the direction-`i` picture —
base `A(u_i)`, deformation `u_{≠i}` — sits inside the same ring as the canonical labelled family,
which is what `isRoot_unique_mvPowerSeries` compares.

### The Galois assembly is Lean-closed; what is left is the instantiation (2026-08-22, final entry of the session)

Eight more modules.  All unconditional, axiom-clean, umbrella-wired.

| Card item | Declaration | Module |
|---|---|---|
| the two-local family over an arbitrary commutative ring, and **switching off every transverse coupling but one** | `transverseFamilyHam`, `transverseFamilyHam_eq_singleDirection`, `twoLocalDiagonal`, `twoLocalHam` | `TwoLocalGenericFamily` |
| **a permutation realized in an auxiliary field descends to the field generated by the roots**; two labelled generating families with the same image are isomorphic; transport of a realized permutation | `exists_algEquiv_of_embedding`, `exists_algEquiv_of_matching_embeddings`, `realized_of_algEquiv_transport` | `SplittingFieldPermTransport` |
| **hypercube edge swaps ⟹ symmetric Galois group**, and the generation lemma for an adjoined family | `card_gal_eq_factorial_of_cubeSwaps`, `adjoin_range_corestrict_eq_top` | `CubeSwapGaloisAssembly` |
| descent along a base field extension (`ℚ(i)` back to `ℚ`) | `card_gal_eq_factorial_of_cubeSwaps_baseExtension` | `GalBaseDescent` |
| the universal transverse family, its reduction at zero couplings, and **the canonical labelled root family** | `universalTransverseHam`, `universalCharpoly_residue`, `exists_canonicalRootFamily` | `TwoLocalCanonicalRoots` |
| **Kummer independence in the form the block quadratics produce it**: no nonempty product of `δ_z² + 4u²` is a square in `A(u)` when the detunings are pairwise distinct and never opposite | `not_isSquare_prod_sq_add_four_sq` | `BlockDiscriminantIndependence` |
| the canonical labelled family is **equivariant** | `map_mvRootFamily_of_perm` | `MvPowerSeriesRootFamily` |
| block splitting of the variable set | `MvPowerSeries.sumEquiv` | `MvPowerSeriesSumSplit` |

So the chain

```text
per-direction flip  →  edge swaps in the canonical labelling  →  closure_hypercubeEdgeSwaps
   →  card_gal_eq_factorial_of_cubeSwaps  →  descent to ℚ  →  gal_card_of_specialisation
```

is Lean-complete **except for one link**: exhibiting, for each direction `i`, the auxiliary field and
the embedding that `exists_algEquiv_of_embedding` consumes.  Concretely what remains is:

1. `L_i := IntermediateField.adjoin (RatFunc A) (Set.range ρ)` inside `LaurentSeries A`, where
   `ρ_z` is the power-series square root of `δ_z² + 4u²` with constant term `δ_z`
   (`exists_powerSeries_sqrt_branch`).  Its flip comes from `exists_algEquiv_swap_quadRoot` with
   `not_isSquare_prod_sq_add_four_sq` as the independence hypothesis.
2. The three fraction fields and the ring maps between them:
   `Ω₀ = Frac(A⟦u⟧)`, `Ω_i = Frac(A⟦u_{≠i}⟧ over L_i)`, and the comparison ring
   `MvPowerSeries {j ≠ i} (LaurentSeries A)`, which receives both.  The identification of the two
   root families there is `isRoot_unique_mvPowerSeries`, and their residues agree because both are
   roots of the direction-`i` characteristic polynomial in `A⟦u_i⟧` with constant term `d x`
   (`isRoot_unique_of_residue`).
3. `E := adjoin K (range Θ)` inside `Ω₀`, `E_i := adjoin K (range Θ^{(i)})` inside `Ω_i`, matched by
   `exists_algEquiv_of_matching_embeddings`; then `realized_of_algEquiv_transport` moves each flip to
   `E`, and `card_gal_eq_factorial_of_cubeSwaps` finishes.

This is fraction-field and algebra-tower plumbing, not new mathematics: every mathematical step in
the route is already a theorem in the tree.
