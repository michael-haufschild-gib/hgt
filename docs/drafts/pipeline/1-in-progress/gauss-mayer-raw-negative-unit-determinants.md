# Raw negative-unit determinants despite divergent Mayer operators

- **Stage:** 1-in-progress
- **Type:** Conjecture
- **Parent:** [successor response](../3-formalized/gauss-mayer-negative-unit-pole-cancellation.md).

## Target

For every `Re w>0`, the Fredholm determinants of the genuine finite-branch
operators `L_N(w)=Σ_{n=1}^N B_n(w)` should satisfy

`det(I+L_N(w)) → D(w,−1)`.

These are determinants of finite-branch operators, not finite Cauchy matrix
sections. The raw operators diverge when `0<Re w<1`; the proposed determinant
convergence would be a stronger positive survivor of that obstruction.

## Exact finite identity to audit

Put `f_w(z)=1−(1+z)^(−w)`, `h_N(z)=(N+1+z)^(−w)`,
`a_N=Σ_{n=1}^N n^(−w)`, and `R_N=L_N−a_NP`.
The source telescope gives `(I+L_N)f_w=1−h_N` and `f_w(0)=0`.
For `N≥1`, `|h_N(0)|<1`, so set `b_N=a_N/(1−h_N(0))`. Then

`(I+L_N)(I−b_N f_w⊗ev₀) = I+R_N+b_N(h_N−h_N(0))⊗ev₀`.

The right shear is nilpotent of order two and has determinant one.
The constant part of its residual cancels exactly. The existing Hilbert
rank-one update can prove determinant equality directly: take
`u=−b_N Qf_w`, `x=−b_N Q(1−h_N)`, and the actual evaluation functional `q`.
Then `u+L_N^H u=x`, `q(u)=0`, `q(x)=−a_N`. The regularized determinant
factor `exp(a_N)` cancels the diagonal correction `exp(−a_N)`.

The proved principal-power difference bound gives
`‖h_N−h_N(0)‖≤(5/2)|w|M(w+1)(N+1)^(−Re w−1)`.
Since `|a_N|≤N` and eventually `|1−h_N(0)|≥1/2`, the residual is
`O(N^(−Re w))`. Also `R_N→R` in operator norm.

The checked `MayerTrace.norm_remainder_monomial` bounds each remainder on
`(z−1)^j` by
`[2j M(w)+(5/2)|w|M(w+1)] n^(−Re w−1)`.
Summing in `n` bounds all `R_N` uniformly. Rescaling by `(6/5)^(−j)`
and using boundedness of `j(8/9)^j` gives the same geometric rate `15/16`
as the actual Cauchy coefficient functionals. The residual rank-one matrix
has this uniform decay too. Operator convergence supplies entrywise
convergence; the proved uniform geometric finite-section error then gives
Fredholm convergence by a three-term estimate. This supplies the paper
mechanism beyond operator-norm convergence alone.

## Obligations

Prove the finite-branch determinant construction, the uniform nuclear matrix
bounds, the determinant-one shear identity, and convergence to the actual
source determinant. Operator-norm convergence alone does not justify
Fredholm determinant convergence. Corpus and paper audits remain incomplete;
no Lean certificate or literature-priority claim is made.
