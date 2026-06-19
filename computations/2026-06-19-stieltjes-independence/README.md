# Stieltjes-constant independence experiment (2026-06-19)

**Purpose.** Technique-⑤ experiment for `docs/drafts/pipeline/1-in-progress/omega-splits-wild-kernel-freeness.md` §Ω: probe *which level* of `{γ_n}` (Stieltjes constants = exponential-period regulators, A5) independence is robust vs marginal — to reveal the nature of DSS-cross.

**Method.** `stieltjes_exp.py`, mpmath dps=240, integer-relation search via `mp.pslq`, `maxcoeff=1e12`.
- `γ_n = mp.stieltjes(n)`, `γ_0` = Euler–Mascheroni.
- companions: `π²`, `ζ(3),ζ(5),ζ(7)`, `log 2π = −2ζ'(0)`, `logA` (Glaisher; `ζ'(−1)=1/12−logA`, an exponential/non-period companion).

**Result (`result.txt`) — all four probes PSLQ-NULL (no relation within the bound):**
| probe | set | verdict |
|---|---|---|
| A — linear floor | `{1, γ_0..γ_12}` | independent |
| C — DSS-cross | `{1, γ_0..γ_5, π², ζ(3,5,7), log2π, logA}` | no cross-relation |
| B — algebraic (apex level) | deg≤2 monomials of `{γ_0,γ_1,γ_2}` + motivic | no relation |
| B′ — product structure | `γ_0²` vs `{1,γ_0..γ_4, π², ζ(3),ζ(5), log2π, logA}` | not reducible (consistent with *free*) |

**Reading.** Independence is **robust at every probed level** — no relation hides within reach (coeffs `<10¹²`, dps 240). **Supports** (does not prove) `K` free / DSS-cross; consistent with the Borel-analog picture (empirically free; the proof is the algebraic-independence apex, same class as `{ζ(odd)}` independence).

**Caveats.** PSLQ-null at a finite coefficient bound is **evidence, not proof**. A relation with larger coefficients or higher degree is not excluded. (A)/(C) overlap the team's prior PSLQ; (B)/(B′) — the algebraic/product level — are the new part.

**Next probes (designed, not yet run):** extend (B) to degree ≤3 and `maxcoeff≥10^{18}`; add the prime-side handle `{log p}` (technique ②) for the *full* DSS-cross; compute the Borel-singularity lattice of the `E_1`/digamma family (technique ③, the resonance-genericity test).
