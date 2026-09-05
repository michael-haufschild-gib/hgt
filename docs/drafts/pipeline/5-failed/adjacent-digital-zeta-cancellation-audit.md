# Adjacent digital coefficients: zeta cancellation audit

**Result:** rejected as a new zero-selecting mechanism. No RH implication.

Corpus Prouhet/Thue–Morse sources suggested nonperiodic coefficients as a possible escape from
finite congruence patterns. The concrete test was adjacent Thue–Morse Dirichlet series.

Write `epsilon_n=1-2t_n`, with `t_n` the binary digit-parity bit, and

`A(s)=sum_(n>=1) epsilon_(n-1)/n^s`, `B(s)=sum_(n>=1) epsilon_n/n^s`.

The published two-column zeta identity becomes

`(2^s+1)(zeta(s)-A(s))/2 + (2^s-1)(zeta(s)-B(s))/2 = 2^s*zeta(s)`.

Centering cancels zeta identically, leaving

`(2^s+1)A(s)+(2^s-1)B(s)=0`.

This holds throughout the absolute-convergence half-plane, without a zero assumption. It is
already the adjacent-series relation in Lemma 1 and the proof of Theorem 1 of
[Tóth, Integers 22 (2022), A98](https://math.colgate.edu/~integers/w98/w98.pdf).
Specializing the continued identity at a zeta zero supplies no new relation.

**Second pass:** changing the two letter values adds constant multiples of zeta back into the
columns; it does not make this centered identity zero-specific. **NO POSITIVE SALVAGE FOUND**:
the surviving adjacent-series law is published, not new mathematics to formalize again.

Corpus verification used `research 'Prouhet'`, `research 'ThueMorse shift'`, and `rg`. The literal
even/odd sign laws were read in `RHTower/ThueMorseMellinFlatness.lean:182–194`. No completed-kernel
construction was adopted. This rejection concerns this adjacent linear identity; it makes no
claim about every digital source. No computation or new production Lean module was used.
