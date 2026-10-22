# FZZ-P all-grade finite-counterterm no-go

- **ID:** fzz-p-all-grade-finite-counterterm-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** rh-current-frontier-map.md · FZZ-P source-first Ward-equivariance burden
- **Statement:** Literal all-grade FZZ parity reflection cannot be made locally `L¹` by any counterterm family whose pole order is bounded uniformly in grade.

## Goal

Kill one complete FZZ-P producer class in the chain

`literal FZZ parity-delay source → all-grade same-source FE reflection → finite-renormalizable local source action → Deninger Ward equivariance → RH`.

The target is source-pure: the reflected densities are forced by the corpus theorem
`FZZCigarParityLocalFEReflectionData.all_nat_grades`, and no zeta zero or RH statement occurs in
the obstruction.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4 publication-ready: standalone theorem + proof + Lean certificate + Door-2

## Corpus and literature provenance

- **[CORPUS]** For `t > 0`, `fzzCigarParityDelay t = 1 / (exp t + 1)`.
- **[CORPUS]** Two local reflected grades force reciprocal delay, the unique scalar weight, and all
  natural grades. Grade `n` has reflected density
  `R_n(t) = (t⁻¹)^(n+1) / (exp t + 1)`.
- **[CORPUS]** A positive finite residue `t^d f(t) → R > 0`, `d ≥ 1`, implies that `f` is not
  locally `L¹` on any right neighborhood of zero
  (`not_integrableOn_Ioo_of_tendsto_natPow_mul_pos`).
- **[LITERATURE, audited 2026-08-30]** FZZ correlator duality and reflection amplitudes
  ([Hikida–Schomerus](https://arxiv.org/abs/0805.3931)), oscillator / wound-string duality
  ([Giveon–Itzhaki–Kutasov](https://arxiv.org/abs/1603.05822)), and cigar density-of-states
  realizations ([Ikhlef–Jacobsen–Saleur](https://arxiv.org/abs/1109.1119)) are known. Search found no
  theorem classifying finite local counterterms for this literal Fermi source simultaneously in every
  Mellin grade. General Taylor-principal-part and Mellin endpoint facts are classical; novelty claim
  is only the exact source-derived all-grade classification and its route consequence.

## Heavy conjecturing loop

1. **Failed candidate A:** naked forced scalar weight is nonintegrable. Rejected: the transformed
   source is exponentially small, so naked-weight divergence does not obstruct the physical density.
2. **Candidate B:** grade-one reflected density is logarithmically nonintegrable because
   `t R_0(t) → 1/2`. Correct but too narrow: a single logarithmic counterterm removes that endpoint.
3. **[CONJECTURE C, PROVED HERE]** Any counterterm family with one uniform finite pole bound fails at some grade.
   This attacks the full all-grade reflection output and distinguishes finite renormalizability from
   an unbounded counterterm tower.

## Theorem and proof

Let `C_n : (0,∞) → ℝ` be counterterms. Say they have uniform pole order at most `N` when, for every
`n`, `t^N C_n(t)` tends to a finite real limit as `t → 0+`.

> **All-grade finite-counterterm no-go.** For every `C` and `N`, grade `N` has
> `R_N - C_N ∉ L¹((0, ε))` for every `ε > 0`. Hence no all-grade counterterm family has a uniform
> finite pole bound.

**Proof `[PROVED HERE]`.** The regular Fermi germ satisfies
`(exp t + 1)⁻¹ → 1/2` as `t → 0+`. If `t^N C_N(t) → L`, then

`t^(N+1) (R_N(t) - C_N(t)) = 1/(exp t + 1) - t · (t^N C_N(t)) → 1/2`.

Because `N+1 ≥ 1` and the residue is positive, the corpus positive-residue theorem implies
`R_N-C_N` is not locally `L¹` on any right neighborhood. This contradicts the grade-`N`
renormalization clause. No dependency remains. ∎

## Sharp positive survivor

The obstruction is exact grade by grade. If `R_n-C` is locally `L¹`, the same argument shows
`t^n C(t)` cannot have a finite limit, so the counterterm depth is strictly greater than `n`.
Conversely define

`C_n^♯(t) = (t⁻¹^(n+1) - 1)/(exp t + 1)`.

Then `R_n-C_n^♯ = 1/(exp t+1)`, which is continuous and locally `L¹`, while

`t^(n+1) C_n^♯(t) = (1-t^(n+1))/(exp t+1) → 1/2`.

Thus minimal pole depth is exactly `n+1`. Any all-grade locally `L¹` family has unbounded pole
depth. This is stronger and more exact than the initial expected Taylor-principal-part survivor:
one canonical analytic-coefficient subtraction already witnesses sharpness.

## Hostile audit and no-go boundary

- Grade-dependent counterterms with unbounded pole depth are not killed.
- Distributional / Hadamard finite-part completion is not literal local `L¹` and is not killed.
- Nonlocal or channel-coupled responses are not killed.
- Thus the exact target is a fixed finite local counterterm space, not every singular FZZ-P law.

## No-go closure

- **Exact killing theorem/mechanism:** the positive grade-`N` residue `1/2` survives every
  counterterm with one common pole bound `N`, forcing nonintegrability.
- **Strongest positive survivor:** exact classification: grade `n` requires and admits minimal pole
  depth `n+1`; therefore all-grade local reflection has unbounded counterterm complexity.
- **New insight:** all-grade FZZ covariance has unbounded ultraviolet counterterm complexity. A
  finite-type local source action cannot carry the missing Ward-equivariant reflection.
- **Status:** formalized in
  `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingFZZParityAllGradeFiniteCountertermNoGo`.
  Closed route theorem `not_fzzCigarParityUniformFiniteCountertermProducer`; sharp survivor theorem
  `exists_fzzCigarParity_exactCountertermDepth_everyGrade`. Direct-file check and targeted module
  build green; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`; umbrella
  wired.

## Open core

**[OPEN CORE CLOSED]** Exact per-grade sharpness and closed all-grade no-go are proved on paper.

## Log

- 2026-08-30 — Created directly in Stage 1 after corpus reconstruction and hostile literature audit.
- 2026-08-30 — Conjecture C proved; exact minimal depth `n+1` classified; promoted to Stage 2.
- 2026-08-30 — Closed no-go and sharp survivor formalized in Lean; targeted build and axiom audit
  green; promoted to Stage 3.
