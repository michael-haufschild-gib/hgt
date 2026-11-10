# Universal moving branch for analytic prime smoothing

- **ID:** B130-analytic-prime-smoothing-rigidity
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** [Quadratic residue scaling](../3-formalized/quadratic-residue-collapse-with-a-nonpolynomial-joint-limit.md).

## Target

Let `Φ` be analytic on a disc of radius greater than one, with
`Φ(0)=1`, `Φ(1)=-1`, and `|Φ(x)|=1` for real `0≤x≤1`.
Write `Φ(z)-1=Σ_{k≥1}a_k z^k`, and let `m` be the first nonzero
coefficient index. For the actual prime phases `v_p(t)=Φ(p^(-t))`,
conjecture the exact small-parameter branch law

`U(t,s)=A_t(s)(s-(1-mt))^(-a_m)`, `A_t(1-mt)≠0`.

The phase condition forces `a_m` to be nonzero and purely imaginary.
Consequently no such nonconstant smoothing family has an actual joint
holomorphic endpoint regularization. The conjectural universal scaling
profile is

`U(t,1+tw)/t² → ζ(2)exp(-Σ_{k≥1}a_k log(w+k))`, `Re w>-m`.

## Open proof obligations

Certify uniform analytic Taylor remainders for the full phase class,
the exact prime-logarithm decomposition, and the locally uniform limit.
The endpoint residue order alone cannot detect the predicted obstruction.
No paper proof or Lean theorem for this general class. B130 remains open.
