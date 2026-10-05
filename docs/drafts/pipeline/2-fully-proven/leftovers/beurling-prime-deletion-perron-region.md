# Prime-deletion Beurling systems: the Perron region for [α,β] with β < ½

- **ID:** MC-BEURLING-DELETION-PERRON
- **Stage:** 2-fully-proven (conditional on RH; a paper theorem, so not formalizable under the unconditional Lean rule)
- **Type:** THEOREM (paper)
- **Source:** MC conjecture loop, cycles 129 and 136 (`1-in-progress/mc-conjecture-loop-2026-09-28.md`)
- **Statement:** Assume RH. For every `½ < α < 4/5` and every `β₀(α) < β < ½`, where `β₀(α) = 3α/(α+4)` for `α ≤ 2/3` and `β₀(α) = 1/(3−α)` for `α ≥ 2/3`, there is an [α,β]-system, i.e. a discrete Beurling system with `ψ(x) = x + O_ε(x^{α+ε})`, `N(x) = ax + O_ε(x^{β+ε})`, neither exponent improvable.

## Relation to the literature
- **Notation.** Broucke–Debruyne–Révész, *Some examples of well-behaved Beurling number systems*, Trans. AMS 378 (2025) 477–501, [arXiv 2309.01567](https://arxiv.org/abs/2309.01567), writes [α,β] with α for the primes and β for the integers.
- **Their results.**
  - Thm 1.1: all α ∈ [0,1), β ∈ [½,1), unconditionally.
  - Thm 1.3, under RH: [½,β] for every β < ½, and [α,β] for `½ < α < 2/3`, `2α/(α+2) ≤ β < ½`.
  - Remark 5.3(1): the double-prime variant gives nothing new for `2/3 ≤ α < 4/5`, because `2α/(α+2) ≥ ½` there.
  - Remark 5.3(2) leaves improvements "with more advanced technology than Dirichlet's hyperbola method" open.
- **New here.** The first convolution `ℕ ⋆ μ_S` is controlled by Perron's formula instead of the hyperbola method.
  - Since `(2α−1)(α−2) < 0`, we have `1/(3−α) < 2α/(α+2)` on `(½,1)`; both curves meet at `(½, 2/5)`.
  - This extends region III down to `β > 1/(3−α)` and across `2/3 ≤ α < 4/5`, where BDR has no systems with `β < ½`.
- **Lower bound.** For the deletion system itself, the corpus's formal DMU floor (loop cycle 89, `not_isBigO_qFreeCount_of_leading_chebyshev`) gives integer exponent `≥ α/2`. Its exact exponent therefore lies in `[α/2, 1/(3−α)]`.
- **The gap.** Closing the gap needs square-root cancellation in `Σ_{m∈N_S} μ_S(m) ψ(x/m)` (ψ the sawtooth). This is the deletion analogue of the squarefree error problem: conjecturally `x^{¼}`; under RH `x^{11/35}` is the best known.

## Inputs from BDR §5 (under RH)
For `½ < α < 4/5` there is a multiset `P_S` of classical primes, each occurring at most twice, with `π_S(x) = F(x) + O(1) ∼ Li(x^α)`. Let `P_D ⊂ P_S` be the primes occurring twice. Then:
1. On every half-plane `Re s ≥ α/2 + ε`: `log ζ_S(s) = log ζ(s+1−α) + O_ε(√log(|t|+2))`. Under RH this gives `ζ_S(s)^{±1} ≪_ε |t|^ε` there. Also:
   - `ζ_S` has a pole at `s = α` (the pole of `ζ(s+1−α)`);
   - `ζ_S` has no zeros with `Re s ≥ α/2+ε`, since the zeros of `ζ(s+1−α)` lie on `Re s = α − ½ < α/2`.
2. `π_D(x) ≪ x^{α/2}`, so `ζ_D` is bounded on `Re s ≥ α/2 + ε`.

(For `α < 2/3` the error-measure variant without `P_D` gives the same inputs.)

## Proof
**Step 1: the deletion system.**
- Let `P' = ℙ ∪ P_D ∖ P_S` as multisets. Every prime has multiplicity `1 + [p ∈ P_D] − mult_{P_S}(p) ∈ {0,1}`, so `P' = ℙ ∖ supp P_S`.
- Its integers `N'` are ordinary integers, each with multiplicity at most 1.
- `ζ_{P'} = ζ·ζ_D/ζ_S`, and its only singularity in `Re s ≥ α/2+ε` is a simple pole at `s = 1`. The pole of `ζ_S` at `α` is a zero of `ζ_{P'}`.

**Step 2: Perron.**
- The coefficients are 0/1 on the integers. Truncated Perron (Titchmarsh Lemma 3.12), with `c = 1 + 1/log x` and `2 ≤ T ≤ x`, gives
  `N'(x) = (1/2πi)∫_{c−iT}^{c+iT} ζ_{P'}(s)x^s ds/s + O(x log x/T + 1)`.
- Shift to `σ₀ = α/2 + ε`. Under RH (Lindelöf, plus the functional equation left of ½): `|ζ(σ+it)| ≪ |t|^{max(½−σ,0)+ε}` for `σ₀ ≤ σ ≤ c`, `|t| ≥ 1`. Together with input 2 and `|1/ζ_S| ≪ |t|^ε`:
  - residue at `s = 1`: `a x`, with `a = ζ_D(1)/ζ_S(1)`;
  - horizontal segments: `≪ T^{3ε}(xT^{−1} + x^{σ₀}T^{−½−σ₀})`;
  - vertical line: `≪ x^{σ₀}T^{½−σ₀+3ε}`.
- Take `T = x^{(1−σ₀)/(3/2−σ₀)}`. Then `N'(x) = ax + O_ε(x^{1/(3−2σ₀)+4ε}) = ax + O_ε(x^{1/(3−α)+5ε})`.

**Step 3: fixing β.**
- Apply BDR Lemma 5.1 with `N = N'` (`γ = 1/(3−α)+5ε`), `L = ℕ^{1/β}` (`b = 1`, `δ = 0`), `h ≡ 1`. This needs `γ < β`, which holds for small ε.
- The system `P_{α,β} = P' ∪ ℙ^{1/β}` then has `N_{α,β}(x) = aζ(1/β)x + ζ_{P'}(β)x^β + O(x^{β/(1−γ+β)})`, where `β/(1−γ+β) < β`.
- The coefficient `ζ_{P'}(β) = ζ(β)ζ_D(β)/ζ_S(β)` is nonzero:
  - `ζ(β) < 0`;
  - `ζ_D(β) > 0` is a convergent positive product;
  - `ζ_S(β) ≠ 0`, since `β > α/2` lies in the region where `log ζ_S` is defined.
- So the integers are β-well-behaved and not better.

**Step 4: primes.**
- `ψ_{α,β}(x) = ψ(x) + ψ_D(x) + β^{−1}ψ(x^β) − ψ_S(x)`.
- Under RH, `ψ_S(x) = x^α/α + O(x^{α−½+ε})`, so `ψ_{α,β}(x) − x = −x^α/α + O(x^{½+ε})`.
- Since `½ < α`, the primes are α-well-behaved and not better. ∎

## Refinement for α < 2/3: sawtooth decomposition (cycle 137)
Let `S' = supp P_S` (distinct primes), so that `1/ζ_{S'} = ζ_D/ζ_S`, `ζ_{S'} = ζ_S/ζ_D`, and `1_{N'} = 1 ⋆ μ_{S'}`.
- **Inputs.** By the inputs above: `ζ_{S'}^{±1} ≪ |t|^ε` on `Re s ≥ α/2+ε`; `M_{S'}(x) ≪ x^{α/2+ε}` (BDR's Perron argument); and `|μ_{S'}|` has Dirichlet series `ζ_{S'}(s)/ζ_{S'}(2s)`.
- **Decomposition.** With `ψ(y) = y − ⌊y⌋ − ½`:
  `N'(x) = x/ζ_{S'}(1) − R(x) + O(x^{α/2+ε})`, where `R(x) = Σ_{m≤x} μ_{S'}(m) ψ(x/m)`.
  Split `m` into dyadic ranges `m ~ M` with a smooth partition `W(m/M)`.
- **(i) Small `M ≤ x^{1/(1+α)}`.** Trivially `≪ N_{S'}(2M) ≪ M^{α+ε}`, which is `≤ x^{α/(1+α)+ε}`.
- **(ii) Large `M`.** On each interval where `⌊x/m⌋ = k`, `ψ(x/m)` is monotone with variation `≤ 1`. Abel summation against `M_{S'}` gives `≪ M^{α/2+ε}` per interval, and there are `≍ x/M` intervals, so `≪ x M^{α/2−1+ε}`.
- **(iii) Middle `M`.** Use Vaaler's trigonometric approximation `ψ_H` of `ψ`, whose error is dominated by a nonnegative trigonometric polynomial with constant term `(2H+2)^{−1}`. Every resulting sum has the form `Σ_m b(m)W(m/M)e(hx/m)` with `b = μ_{S'}` or `|μ_{S'}|`.
  - By Mellin inversion on `Re s = α/2+ε`, such a sum is `∫ B(s) I_c(s) M^s ds`, where `B ∈ {1/ζ_{S'}, ζ_{S'}(s)/ζ_{S'}(2s)}` is `≪ |t|^ε` and `I_c(s) = ∫W(u)e(c/u)u^{s−1}du`, `c = hx/M ≥ 1`.
  - Stationary phase: `|I_c| ≪ c^{−½}` for `t ∈ [πc/2, 4πc]` and `≪_A (|t|+c)^{−A}` otherwise. The pole of `ζ_{S'}` at `α` has residue `I_c(α) ≪_A c^{−A}`.
  - Hence each sum is `≪ M^{α/2−½}(hx)^{½+ε}`, and `R_M ≪ x^{½+ε}H^{½}M^{α/2−½} + M^{α+ε}/H`.
  - Take `H = M^{(α+1)/3}x^{−1/3}` (valid for `M ≥ x^{1/(1+α)}`): `R_M ≪ M^{(2α−1)/3}x^{1/3+ε}`, which is increasing in `M`.
- **Balance.** (ii) and (iii) meet at `M* = x^{4/(α+4)}` with value `x^{3α/(α+4)}`. Since `3α/(α+4) > α/(1+α)` for `α > ½`, we get `N'(x) = x/ζ_{S'}(1) + O(x^{3α/(α+4)+ε})`.
- **Comparison.** `3α/(α+4) < 1/(3−α)` iff `(3α−2)(α−2) > 0`, i.e. iff `α < 2/3`; the two bounds meet at `(2/3, 3/7)`. As `α → ½⁺` the refined bound tends to `1/3`, against `2/5` from both Perron and BDR. `3α/(α+4) < ½` iff `α < 4/5`.
- **Status.** The deletion exponent lies in `[α/2, β₀(α)]`. The lower end `α/2` is the square-root (random-model) value and is the formal DMU floor.

## Meaning for route MC
The deletion system is Möbius-inverted: `1_{N'} = 1 ⋆ μ_S`. Its integer error is a Möbius–sawtooth sum over the deleted system, and the only analytic input is `1/ζ_S ≪ |t|^ε` left of the critical line of `ζ_S`. This is the Beurling mirror of cycle 131's uniform Abel bound. The result is ζ-blind for RH: it is conditional on RH and describes systems built from ℕ.

## Log
- 2026-09-29: cycle 137 adds the sawtooth refinement `3α/(α+4)` for `α < 2/3`.
- 2026-09-29: proved on paper (loop cycle 136) after the BDR audit of cycle 129. No follow-up to BDR Theorem 1.3 found (web search 2026-09-29).
