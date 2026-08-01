# Universal permanent specialization of the differential fiber symbol

- **ID:** ten-proofs-cross-corpus-bridge-audit
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** OpenAI `ten-proofs`, commit `6fefffdbab0dfa726fcfde6cefae23aa7a1888f3`
- **Statement:** `[PAPER-PROVED]` The complex cast of the local falling-factorial symbol `permSymbolPoly μ` is the specialization of `PermanentRollout.permanent r` obtained by sending its matrix variable `(i,j)` to the complex cast of `(descPochhammer ℤ (μ j))` evaluated at `X i`; consequently every local injective antidiagonal fiber weight is the evaluation of that universal permanent specialization.

## Goal

Expose the local differential fiber invariant as an exact specialization of the universal permanent
polynomial imported with the Permanent certificate.  This gives a standard polynomial carrier for
the local value and a type-correct bridge through which universal-permanent identities can be
transported without replacing the local symbol or assuming its nonvanishing.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Let

`P_r(X) = ∑_{π : Perm(Fin r)} ∏_{j : Fin r} X_(π j,j)`

be `PermanentRollout.permanent r`, and let

`Q_μ(x) = ∑_{π : Perm(Fin r)} ∏_{j : Fin r} (x_(π j))_(μ j)`

be the complex cast of the local `permSymbolPoly μ`, where `(x)_m` is the descending Pochhammer
polynomial.  Substitute `X_(i,j) := (x_i)_(μ j)` in `P_r`.

## Complete paper proof

`[PROVED HERE]` By `PermanentRollout.permanent_aeval_eq_matrix_permanent`, evaluating `P_r` at a
matrix `A` of polynomials gives `Matrix.permanent A`.  For

`A_(i,j) := map(ℤ→ℂ) ((descPochhammer ℤ (μ j)) evaluated at X_i)`,

the definition of `Matrix.permanent` expands this value to

`∑_π ∏_j A_(π j,j) = ∑_π ∏_j map(ℤ→ℂ) ((descPochhammer ℤ (μ j)) evaluated at X_(π j))`.

Ring-homomorphism preservation of finite sums and products identifies the right side with
`map(ℤ→ℂ) (permSymbolPoly μ)`.  This proves the polynomial identity with no hypotheses.

Now evaluate both sides at any integer scale tuple `s`, cast into `ℂ`.  Polynomial evaluation and
coefficient casting commute, so the common value is

`∑_π ∏_j (descFactorial (s (π j)) (μ j) : ℂ)`.

Under injectivity of `s` and the order bounds `∀ i j, μ j ≤ s i`, local
`fiber_perm_single` identifies the integer antidiagonal fiber weight with the same sum before
casting.  Applying `ℤ → ℂ` proves the claimed fiber-value bridge.  Every dependency is either a
definition, a ring-homomorphism law, `PermanentRollout.permanent_aeval_eq_matrix_permanent`, or
`fiber_perm_single`; no open implication remains.

## Exhaustive cross-corpus disposition

| Imported proof | Exact local overlap | Verdict |
|---|---|---|
| `CompactnessAndDegeneracy` | Generic exponential-integrability helpers already proved locally; no local extremal-graph interface | `REDISCOVERED` helpers; no discharge |
| `ConnesRigidity` | No local property-(T), cocycle, or Connes-rigidity carrier; local Connes work concerns trace-formula geometry | Type-incompatible |
| `EhrhartVolumeInequality` | No local `normalizedVolume`/`interiorLatticePoints` consumer | Type-incompatible |
| `GapCVP` | No local promise-problem, Turing reduction, or CVP interface | Type-incompatible |
| `MetricCodes` | Its Boolean Hamming distance is definitionally the Mathlib distance used by sign chambers | Trivial restatement; no non-trivial discharge |
| `MulticolorTriangleRamsey` | No local labeled-graph/Ramsey interface | Type-incompatible |
| `NonSoficGroup` | No local sofic approximation or finite-presentation interface | Type-incompatible |
| `Permanent` | Local falling-factorial permanent symbol and fiber equality | `[BRIDGE]`; exact survivor proved above |
| `QuantumParallelRepetition` | Density-matrix carriers are equivalent, but local operational channels are iterates on fixed state space, not tensor-power games | Representation bridge only; no valid theorem transfer |
| `SpherePacking` | No local packing-density or Cohn--Elkies interface | Type-incompatible |

Declaration-name audit covered 30,838 unique upstream names against 83,822 unique names in the two
local areas.  Twenty-six unqualified names overlapped; after removing structure-field noise, every
substantive match is classified in the table or is an already-local generic lemma (`sinh_le_mul_cosh`,
`integrable_exp_neg_mul_abs`, `integrable_abs_pow_mul_exp_neg_mul_abs`).  Exact headline namespace
search returned no pre-existing local consumer.  Repository absence establishes only local novelty,
not scientific novelty; the surviving identity is classified `[BRIDGE]`.

## Hostile audit

- A shared word such as compactness, rigidity, metric, positivity, spectrum, reflection, or volume
  is not evidence of a bridge.
- A theorem obtained by supplying an arbitrary existing local hypothesis is not a discharge.
- An equality transport is non-trivial only when it removes a genuine interface boundary or yields
  a conclusion not already available under equivalent or weaker assumptions.
- Repository absence alone does not establish scientific novelty.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** Nine proof families have no type-compatible local consumer;
  Hamming and density-matrix matches do not change a theorem after normalization.
- **Strongest positive survivor:** Universal-permanent specialization and its local fiber-value
  corollary.
- **New insight:** Local differential fiber nonvanishing is carried by a specialization of the
  universal matrix permanent, not merely an ad hoc permutation sum.
- **Status:** internal audit complete; paper proof dependency-closed; Lean formalization pending.

## Log

- 2026-08-01 — created in `1-in-progress`; upstream commit and three acceptance modes frozen.
- 2026-08-01 — all ten proof families audited; permanent specialization survives hostile review.
- 2026-08-01 — complete paper proof closed; promoted to `2-fully-proven` as `[BRIDGE]`, scientific novelty not claimed.
