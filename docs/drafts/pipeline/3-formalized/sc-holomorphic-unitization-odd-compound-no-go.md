# SC holomorphic identity-unitization odd-compound no-go

- **ID:** SC-HUCPN
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** read-only `rh-current-frontier-map.md` · route SC `LAND COMP`; corpus theorems `preDivisorRiggedPrimeHolomorphicReservoirMatrix_det`, `hasDerivAt_primeGammaCofinalBocksteinCoefficient_zero`, and compact-open holomorphic jet transport
- **Statement:** Canonical additive identity unitization of the coefficient-faithful holomorphic SC reservoir has a sign-definite full odd exterior-compound gap, with a fixed strictly positive first-three-prime cubic witness, so its determinants cannot converge compact-open to normalized centered Xi.

## Goal

Attack the first genuine additive escape left by the scalar-factor and matrix-equivalence no-goes.
The identity counterterm is canonical because it is full-rank at the wall and normalizes every
finite determinant to one at the origin.  Decide whether this central unitization can be the missing
SC Xi determinant.

## Gates

- [x] 0 → 1  in-progress: source-pure conjecture, hostile escape audit, corpus and literature search
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `not_tendstoLocallyUniformly_normalizedXiC_of_holomorphicUnitization`, exact leaf build green, scoped axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper and independent novelty review

## Corpus baseline

For packet dimension `n=m+2`, the exact complex SC reservoir is

`M_m(z) = (I - 11ᵀ) diag(B_0(z),…,B_{n-1}(z))`,

where each `B_j` is entire, odd, vanishes at the wall, and has strictly negative first central jet
`-2 a_p log p`.  The new candidate is the literal unitized determinant

`U_m(z)=det(I+M_m(z))`.

Unlike every previously excluded multiplicative correction, `U_m(0)=1`; moving prime-log zeros of
`det M_m` are no longer automatically zeros of `U_m`.  This is therefore a genuinely new additive
branch, not another reformulation of scalar normalization.

## Conjecture loop and result

1. **C1 — central normalization.** `U_m(0)=1` for every packet.
2. **C2 — cubic exterior compound.** The proposed third-jet obstruction is valid, but proof exposed
   a stronger invariant: for every diagonal vector `b`,
   `det(I + (I-11ᵀ)diag(b)) = Σ_S (1-|S|)∏_{i∈S}b_i`.
3. **C3 — full odd-compound obstruction.** At positive real transverse input every Bockstein
   coordinate is strictly negative.  Under `z ↦ -z`, every even subset cancels; every odd subset
   is nonnegative; the first three-prime subset is strictly positive and persists in every packet.
   Hence `U_m(1)-U_m(-1)` has a packet-independent positive lower witness.  Compact-open
   convergence implies pointwise convergence at `±1`, while normalized centered Xi is even.
   Contradiction. **[PROVED HERE]**

## Hostile audit

- A scalar or left/right matrix factor cannot help: already excluded by the moving-divisor theorem.
- Identity unitization does remove the old divisor argument; the new obstruction is independent and
  occurs in the third exterior compound.
- Symmetrizing `U_m(z)U_m(-z)` cancels the odd jet and is not covered.  More general additive
  counterterms can also cancel it.  Therefore the conclusion must not claim all additive coupling
  fails.
- Exact survivor: viable additive SC landing must cancel the source-derived third exterior compound
  cofinally while preserving the center unit, then satisfy every higher odd-compound cancellation.

## Attack

Use the principal-minor expansion of `det(I+X M)`.  Every principal restriction of the reservoir is
again `I-11ᵀ` on the restricted coordinate type, so its determinant is exactly `1-|S|`; multiplying
by the restricted diagonal gives the subset formula above.  Coefficient faithfulness identifies
the actual holomorphic matrices at `z=±1` with the real matrices for `b` and `-b`.  The odd part is
therefore an exact finite sum, not an asymptotic Taylor remainder.  Termwise sign and the fixed
three-coordinate embedding provide the positive cofinal witness.  Pointwise evaluation of the
assumed compact-open limit and Xi evenness finish the contradiction.

## Lean artifact

- Module: `GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicUnitizationOddCompoundNoGo`
- Exact algebra:
  - `realReservoirDiagonalMatrix_submatrix_det`
  - `unitizedRealReservoirDeterminant_eq_sum_powerset`
  - `unitizedRealReservoirDeterminant_sub_neg_eq_odd_powerset`
  - `realReservoirTripleWitness_le_odd_gap`
- Source bridge and normalization:
  - `preDivisorRiggedPrimeHolomorphicUnitizedDeterminant_zero`
  - `differentiable_preDivisorRiggedPrimeHolomorphicUnitizedDeterminant`
  - `preDivisorRiggedPrimeHolomorphicUnitizedDeterminant_ofReal`
  - `preDivisorRiggedPrimeUnitizedOddWitness_le_unitized_real_gap`
- Capstone:
  - `not_tendstoLocallyUniformly_normalizedXiC_of_holomorphicUnitization`
- Verification:
  - `lake env lean GaloisForLFunctions/RHTower/SourceHorizontalHolomorphicUnitizationOddCompoundNoGo.lean` — PASS
  - `lake build GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicUnitizationOddCompoundNoGo` — PASS (`Built ...`, 77s)
  - scoped `#print axioms` — only `propext`, `Classical.choice`, `Quot.sound`
  - forbidden declaration scan and scoped diff check — PASS
  - repository lint reaches the new module through `RHTower.lean`; global lint remains red only on unrelated concurrently unwired modules

## Literature audit (as of 2026-08-28)

- Principal-minor expansions, Fredholm finite-section determinants, and perturbation determinant
  trace formulas are classical; no novelty is claimed for those general identities.
- Bornemann, *On the Numerical Evaluation of Fredholm Determinants* (2008), treats convergence of
  finite determinant approximations for suitable kernels.
- Gesztesy--Zinchenko, *Symmetrized Perturbation Determinants and Applications to Boundary Data Maps
  and Krein-Type Resolvent Formulas* (2010), treats symmetrized perturbation determinants and trace
  formulas.
- No located source states the SC reservoir cubic-parity obstruction or its cofinal additive
  cancellation consequence. **Novelty status:** `[NOVELTY UNVERIFIED]`.

## Door passport

- **Unconditional source:** ordinary-prime enumeration, exact activation-Fisher density, exact
  holomorphic Gamma-Bocksteins, universal shared reservoir.
- **No RH leakage:** target uses only unconditional Xi evenness and `XiC(0) ≠ 0`.
- **Hard burden removed:** canonical full-rank identity unitization, the first genuine
  additive determinant surviving earlier no-goes.
- **Positive survivor:** a landing must introduce coefficient-faithful odd-compound counterterms,
  beginning at exterior order three; central normalization alone is insufficient.

## Log

- 2026-08-28 — created after mandatory corpus search, hostile audit, and current primary-literature
  search. Frontier map left read-only.
- 2026-08-28 — cubic conjecture strengthened to the exact full odd-compound law; paper proof closed,
  formalized unconditionally in Lean, wired into `RHTower.lean`, exact leaf build and scoped axiom
  audit passed. Frontier map remained read-only.
