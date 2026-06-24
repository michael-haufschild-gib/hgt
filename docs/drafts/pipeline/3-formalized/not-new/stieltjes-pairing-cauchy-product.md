# Stieltjes pairing Cauchy product

- **ID:** stieltjes-pairing-cauchy-product
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/stieltjes-log-weld.md` §2
- **Statement:** For formal series `F(u)=sum_j c_j/j! u^j` and `G(u)=1+sum_n a_n u^(n+1)`, the coefficient of `F(u)G(u)` at degree `N` is the isolated top term `c_N/N!` plus the lower Cauchy-product sum.

## Goal
This banks the exact formal-power-series coefficient identity used in the Stieltjes-log weld. It does not formalize analytic continuation, actual Stieltjes constants, Dirichlet-polynomial independence, the no-isolation theorem, or any transcendence claim.

## Paper Proof
The coefficient of degree `N` in a product is the Cauchy sum
`sum_{j+k=N} F_j G_k`. Here `G_0=1`, and for `k=n+1>0`, `G_k=a_n`.

The term with `j=N,k=0` contributes `c_N/N!`. The remaining terms have `j<N`, `k=N-j`, hence `n=N-j-1`, and contribute
`(c_j/j!) a_{N-j-1}`. Substituting `a_n=(-1)^n gamma_n/n!` gives the displayed Stieltjes pairing formula.

## Gates
- [x] 0 -> 1  in-progress: formal Cauchy-product identity extracted.
- [x] 1 -> 2  fully-proven: paper proof above, by the coefficient formula for a product of formal power series.
- [x] 2 -> 3  formalized: Lean theorem `stieltjes_pairing_cauchy_j` in `formal/GaloisForLFunctions/StieltjesWeld.lean`; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the coefficient lemma in the Stieltjes-log weld note.

## Log
- 2026-06-19 — Leaner split this exact Cauchy-product lemma from `stieltjes-log-weld`. The parent card remains in `2-fully-proven` because the no-isolation, graded log-polynomial, and analytic independence layers are not fully Lean-formalized.
