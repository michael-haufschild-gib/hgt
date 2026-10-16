# Prime-pivot dual-spectrum constraint for Γ-site Lee–Yang chains

- **ID:** `lee-yang-prime-pivot-dual-spectrum`
- **Stage:** 3-formalized (2026-10-17)
- **Type:** CONJECTURE / proposed producer obstruction
- **Source:** `rh-current-frontier-map.md` W1C; MUST-820/852 and the Γ-site chain
- **Statement:** At a prime pivot `M=N+2`, a ferromagnetic Γ-site chain whose complete spectrum stays in the frozen Riemann–Siegel dual alphabet `ℕ ∪ M/ℕ` has active wall indices `n=k+2` forming a strict divisibility chain; hence at most `⌊log₂ M⌋` active walls.

## Goal

Classify the exact arithmetic frequency support of an unconditional real-rooted producer at a prime pivot. This rules out a dense positive-wall realization of the full Riemann–Siegel main sum; signed walls would need exact cancellation of specific nondual terms.

## Gates

- [x] 0 → 1: precise source, falsifiable constraint, attack via two-wall configurations.
- [x] 1 → 2: dependency-closed paper proof of exact support classification.
- [x] 2 → 3: Lean theorem, direct `lake env lean` final audit, umbrella (2026-10-17).
- [ ] 3 → 4: publication-ready independent result.

## Approach

Set `M=N+2` and `n_k=k+2`. For a spin set `S`, its Γ-site field frequency is `log q(S)`, where `q(S)=∏_{i∈S}(i+2)/(i+1)`. If only the walls `a<b` flip, the two complementary spin sets contribute `q=n_b/n_a` and `M/q`. Their weights are `c_a c_b>0`. Thus both occur in the positive partition spectrum. At prime `M`, `2≤n_a<n_b<M`, and `n_b/n_a∈ℕ∪ M/ℕ` iff `n_a∣n_b`: the second alternative would give `n_b∣M n_a`, and coprimality with `M` then gives `n_b∣n_a`, impossible. All pairs of active wall indices therefore divide in order. Conversely, ordered divisibility makes every interval product integral, so every spin-set frequency is an integer or `M` divided by an integer. Each strict divisibility step at least doubles the index; thus active wall count is logarithmic.

**Attack:** Check whether finite positive coefficients at colliding rational frequencies can cancel (they cannot); check odd/even wall parity and endpoint intervals in the converse; check prime-pivot density is relevant to the moving Riemann–Siegel phase. Signed couplings may cancel frequency collisions, so the claim is scoped to nonnegative couplings.

## Paper proof

Let `W` be the set of wall indices with `c_k>0`. A spin configuration is a subset `S` of minus-spin sites. Its coefficient is `w(S)=∏_{k∈∂S}c_k`, with `∂S` the set of adjacent sign changes. Thus `w(S)>0` precisely when `∂S⊆W`. Its field monomial is `exp(-it log q(S))` and `q(S)=∏_{i∈S}(i+2)/(i+1)>0`. Equal frequencies add positive weights, so the actual Fourier spectrum is exactly `{q(S):∂S⊆W}`; there is no cancellation.

For any `a<b` in `W`, choose `S={a+1,…,b}`. Its only walls are `a,b`, and telescoping gives `q(S)=(b+2)/(a+2)=B/A`. If `B/A∈ℕ∪ M/ℕ`, either `A∣B`, or `B∣MA`. Since `M` is prime and `B<M`, `gcd(B,M)=1`; in the second case Euclid gives `B∣A`, contradicting `A<B`. Hence `A∣B` for every ordered pair in `W`.

Conversely, suppose the active indices `n_k=k+2` form an ordered divisibility chain. If `S` does not contain the last site, decompose it into maximal consecutive intervals. Each interval is either an initial prefix, with field product `n_b`, or an internal interval between two active walls `a<b`, with field product `n_b/n_a∈ℕ`. Thus `q(S)∈ℕ`. If `S` contains the last site, its complement does not, and the complete field product telescopes to `M`; hence `q(S)=M/q(Sᶜ)∈M/ℕ`. Every positive-weight configuration therefore belongs to the dual alphabet.

If there are `r` active walls, their ordered indices obey `2≤n₁`, `2n_j≤n_{j+1}` and `n_r<M`. Induction gives `2^r≤n_r<M`. This logarithmic wall budget is sharp up to the endpoint: choose powers of two below `M`.

The proof is source-side: it uses positive fugacities and the actual Γ-site fields, no Xi zero or RH premise. It excludes **exact** dual-alphabet support for dense positive Γ chains, not an approximation whose extra frequencies disappear in a limit. Signed fugacities escape the positivity argument only through exact collision cancellation.

## Next conjecture: signed escape has algebraic codimension

For any nondividing active pair `a<b` at prime pivot `M`, let `C_{b/a}(c)` be the Fourier coefficient of the exact chain partition function at `log(b/a)` as a polynomial in **independent real fugacities** `c_k`. Then `C_{b/a}` is a nonzero polynomial: its `c_a c_b` monomial comes from the single minus interval `(a,b]`, with coefficient `1`, plus possibly the complementary configuration when `(b/a)^2=M`. At prime `M` and `2≤a<b<M`, that equality is impossible because it would require `b²=M a²`. Other wall configurations have different fugacity monomials. Hence the signed couplings that remove this specific nondual frequency lie on a proper algebraic hypersurface. Full signed escape requires simultaneous satisfaction of every such collision equation.

**Attack:** A fixed algebraic exceptional set can contain special structured couplings; codimension alone gives no lower bound on the Xi approximation error. The coefficient claim is about independent fugacity variables, not arbitrary parameterized families where monomials cease to be independent. The specific two-wall monomial remains unique after grouping field frequencies, which must be proved from the spin expansion.

**[OPEN CORE]** Prove the exact Fourier coefficient polynomial formula and formalize the nonzero mixed coefficient. Then test whether simultaneous equations force sparse support, or admit a genuinely arithmetic signed cancellation family.

**[OPEN CORE]** Formalize the complete spin partition, its frequency support, and the converse classification. The exact partition-to-transfer identity and wall-count bound also need Lean proof.

## Log

- 2026-10-10 — corpus-first W1C and two-wall search. Existing card asserts ferromagnetic rational pollution but not its prime-pivot dual-alphabet classification; exact search found no named declaration. External literature check omitted at user request. Paper proof closed above. No Lean result claimed yet.
- 2026-10-10 — second conjecture: generic signed chains retain nondual leakage. Source-side monomial argument closes paper nonzero polynomial assertion; exact signed solutions remain open.
- 2026-10-10 — Lean arithmetic core in `RHTower/LeeYangPrimePivotDualSpectrum.lean`: Γ-site ratio telescoping, exact prime-pivot two-wall criterion, and pairwise divisibility equivalence. Direct check passed; full spin-partition theorem and signed polynomial remain open.
- 2026-10-10 — Added source-level theorem `primePivot_spinSpectrum_forces_divisibility_chain`: any permitted spin-word spectrum contained in the dual alphabet forces the active wall labels to divide in order. Its proof constructs the interval word with exactly the two chosen walls. Final direct `lake env lean` and `lake build --old` of the leaf passed. Eight public theorems have only `propext`, `Classical.choice`, and `Quot.sound` axioms. Index refreshed; `git diff --check` passed. Global lint still fails on fourteen other agents' unwired modules; this leaf is wired and absent from the errors.

## Anti-theatre audit

The arithmetic classification is exact source knowledge, but the integer-anchored positive chain was already excluded as an Xi producer by its forced early zero. This theorem does not by itself move the live RH producer frontier; classify it as `BRIDGE`, not a proof advance. The surviving use is for modified Γ-site or graph constructions where the early-zero law does not apply. The next cycle must attack a live source bound (RW/CTF/PA) or prove that a modified source genuinely avoids the prior first-zero obstruction. Avoid further formal wrappers around the same dead anchored chain.

## Lean status (2026-10-17) — both paper theorems formalized

`RHTower/LeeYangPrimePivotSpinPartitionSpectrum.lean` closes every proven claim:
- `chainPair_eq_spinSum`, `chainZ_eq_spinSum`: the transfer recursion is the spin partition
  `Z = Σ_S (∏_{walls} c_k) ∏_{i∈S} u_i` (partition-to-transfer identity);
- `gammaChainZ_eq_frequencySum`: `Z(t) = Σ_λ C_λ e^{-iλt}` over spin-word frequencies `log q(S)`;
- `expSum_coeff_eq_zero` (Dedekind independence of the characters `t ↦ e^{-iλt}`) and
  `gammaChain_expSum_coeff_eq`: every exponential-sum representation has the fiber sums as
  coefficients; `gammaChain_spectrum_iff`: with `c ≥ 0` the spectrum is exactly
  `{log q(S) : ∂S ⊆ W}` (no cancellation);
- `gammaSpinWordRatio_eq_nat_of_wall_dvd` (block decomposition: integral frequency base) and
  `gammaSpinWord_mem_dualAlphabet_of_divisibility_chain` (converse, via the complement word);
- `primePivot_spinSpectrum_dual_iff_divisibility_chain`, `gammaChain_primePivot_dualSpectrum_iff`:
  spectrum ⊆ dual alphabet ⟺ ordered divisibility chain;
- `two_pow_card_le_of_divisibility_chain`, `gammaChain_primePivot_dualSpectrum_wall_budget`
  (`2^r ≤ N+1 < M`, `r ≤ ⌊log₂(M-1)⌋`), `exists_divisibility_chain_card_eq_log` (sharp: powers of two);
- signed fugacities: `gammaChainCoeffPoly`, `eval_gammaChainCoeffPoly` (it evaluates to the Fourier
  coefficient), `gammaChainCoeffPoly_coeff_twoWall` (coefficient of `X_j X_k` is exactly `1`, using
  that a word is determined by its walls and first spin and that `M (j+2)² = (k+2)²` is impossible),
  `gammaChainCoeffPoly_twoWall_ne_zero` (nonzero polynomial; the frequency is nondual when
  `j+2 ∤ k+2`).

Audit: `lake env lean` clean; `#print axioms` on all 14 main theorems gives only `propext,
Classical.choice, Quot.sound`.  Appended to `GaloisForLFunctions/RHTower.lean`.  The remaining
`[OPEN CORE]` items (simultaneous signed collision equations) are open research questions, not
proven claims of this card.  Card moved to `3-formalized`.
