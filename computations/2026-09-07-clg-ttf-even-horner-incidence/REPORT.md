# CLG/TTF compact determinant: bounded Horner incidence preparation

**Purpose:** Replace an oversized monolithic determinant check with symbolic identities in original modular coordinates and a graded Horner substitution. These are candidate expressions for independent Lean proofs, not assumed arithmetic or sign results.

**Execution:** Runpod `root@157.157.221.29:27094`, 16 workers for independent relative-shear grades. The raw-coordinate and Horner table preparation took approximately 0.524 seconds. `generate.py` retains every term of the stronger corrected raw determinant. `prepare_horner.py` renders bounded coefficient proof candidates from those tables. Outputs and generation logs were downloaded.

## Exact candidate decomposition

Starting with the archived full raw determinant and head polynomial, replace the earlier slope correction by `Q(3Q−6/19)` and normalize by `100^12`. The raw polynomial has 2460 terms and gap degree twenty.

Write it as `Σ_(n=0)^20 a^n R_n(u,w)`. Under `w=u(1+v/4)`, every monomial has even total `u,w` degree, giving `R_n(u,u(1+v/4))=P_n(u²,v)`. Each separate gap-grade table has at most 280 terms.

With `A(r,t)=191/10−12r/5+t(1/10+16r/15)`, set `H_21=0` and `H_n=P_n+A H_(n+1)`. Each `H_n` is further grouped by drift degree. Since `A=(191/10+t/10)+r(−12/5+16t/15)`, each coefficient step has only a linear multiplier and at most 329 displayed terms in its output coefficient. `H_0` has 5368 terms, the size of the existing positive unit-polynomial candidate.

## Artifacts and verification boundary

- `output/incidence.json`: complete raw, gap-grade, relative-shear and Horner tables.
- `generation-log.json`: table sizes, runtime and worker count.
- `output/horner-generation-log.json`: bounds on each coefficient-table size.
- `prepare_landing.py` and `output/landing-generation-log.json`: existing block-grading and final coefficient-incidence candidates.
- `output/*.lean`: emitted symbolic proof candidates.

All twenty-one gap-grade identities, every Horner step, all twelve drift-graded block identities and the final coefficientwise landing in the positive polynomial are Lean-checked. The original-coordinate determinant identity still requires a successful proof. Its monolithic attempts exceeded practical memory limits and were stopped. No equality or positivity follows merely from table generation. The [incidence checkpoint](../../../1-in-progress/clg-ttf-even-compact-incidence/STATUS.md) records the authoritative checked boundary and the needed smaller decomposition.

These runs prepared predictable algebraic expressions; they were not scientific experiments addressing an uncertain mathematical outcome. Further coefficient-generation runs are stopped under the user's computation restriction. All existing outputs are downloaded and the owned remote working directory is removed. Subsequent work uses these expressions only as candidates for symbolic Lean proofs.
