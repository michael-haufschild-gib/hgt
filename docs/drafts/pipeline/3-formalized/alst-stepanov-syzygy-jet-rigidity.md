# Exact Stepanov jets from polynomial syzygies

- **ID:** alst-stepanov-syzygy-jet-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** For an Euler derivation `D`, `h=Σ_i f_i ψ_q(g_i)`, and an Adams fixed point `u`,
  `D^k h(u)=Σ_{j=0}^k binom(k,j) q^(k−j)(1−q)^j D^(k−j)(Σ_i D^j(f_i)g_i)(u)`.

## Mathematical purpose
Determine the exact jets of the Stepanov construction before applying a norm
amplifier. The identity holds for arbitrary integer polynomial families;
it assumes no vanishing or smallness input. Vanishing of the coefficient
moment polynomials below `r` gives exact Euler jets below `r` on the full
fixed grid.

## Evidence and novelty question
`StepanovsConstructionOnTheTorsion.lean` proves divisibility of the first
derivative by `ℓ` under `Σ_i (∂_j f_i)g_i=0`, then uses norm smallness to force
zero. Its amplifier theorem does not assume `Σ_i f_i g_i=0`. Differentiating
that additional polynomial identity forces the missing second-factor
syzygy, hence exact vanishing already follows in the combined setup.

Polynomial syzygies and pointwise vanishing on the fixed grid must be
distinguished: differentiating the former gives additional identities;
pointwise vanishing alone gives none. The first-jet identity is
`D h(u)=q D(Σ_i f_i g_i)(u)+(1−q)Σ_i D(f_i)(u)g_i(u)`.

## Proof route
On a product, let `A` differentiate the first factor and `B` the second.
After Adams substitution the Euler action is `A+qB`; at a fixed point,
write this as `q(A+B)+(1−q)A`. The two operators commute. Their binomial
expansion gives the displayed identity and makes every possible
archimedean vanishing input explicit.

## Gates
- [x] Corpus novelty audit: existing first-derivative divisibility and generic iterated Leibniz rules do not give the all-order Stepanov transfer identity.
- [x] Complete paper proof, including mixed Euler words and boundary cases.
- [x] Lean formalization and transitive axiom audit.

This concerns exact torsion vanishing; arithmetic length still prices the
order, and the construction contains no zeta-specific input.

## Transfer mechanism
For `M_g(f)=fg`, set `T_q(U)=qDU+(1−q)UD`. Left and right composition commute,
so `T_q^k` has the claimed binomial expansion. Leibniz gives
`T_q(M_g)=M_gD+qM_Dg`, and `T_q` commutes with right composition by `D`.
This recurrence is precisely the recurrence for `D^k(fψ_q(g))` after
evaluation at a fixed point. It proves the scalar identity for arbitrary
families, before imposing any polynomial syzygies.

## Mixed words and ordinary multiplicity
Write `E_L` for an ordered word of coordinate Euler derivations. Suppose
`Σ E_L(f_i)g_i=0` as a polynomial whenever `|L|<r`. Both differentiated
families `(E_j f,g)` and `(f,E_j g)` satisfy the same condition below `r−1`:
append `j` to the first word for the former; differentiate its moment and
subtract the moment with `j` prepended for the latter. The identity
`E_j h_q(f,g)=h_q(E_j f,g)+q h_q(f,E_j g)` then proves vanishing of every
Euler word below `r` at every fixed point, by induction on word length.

At a point where `u_i≠0`, multiplication by `X_i` cannot hide an Euler jet.
Induct on the order using
`E_j(X_iF)=δ_ij X_iF+X_i E_jF`; subtract the lower-order `X_iF` term and
cancel `u_i` in order zero. Since `E_iF=X_i∂_iF`, induction now converts
Euler vanishing into ordinary uniform vanishing. A nonzero auxiliary
therefore still has total degree at least `r` and arithmetic length at least
`2^r` by `ExactVanishingCostsTheDegree`.

The first ordinary derivative vanishes under the two polynomial identities
`Σ f_i g_i=0` and `Σ (∂_j f_i)g_i=0`, without smallness. The original norm
amplifier remains meaningful under the second identity alone. Pointwise
identities cannot be differentiated and do not imply these conclusions.

All identities allow `q=0,1`, zero derivative order, empty families, and
empty coordinate types. No factorial, `q`, or `1−q` is divided out. The
ordinary-jet conversion explicitly requires nonzero point coordinates.

## Lean statements
- `StepanovJetTransfer.lean`: the binomial endomorphism identity and its Leibniz recurrence.
- `TheEulerJetsOfStepanovsAuxiliary.lean`: `aeval_euler_pow_stepanov`, `aeval_euler_pow_stepanov_of_lowerMoments`, and `aeval_pderiv_stepanov_eq_zero_of_syzygies`.
- `PolynomialSyzygiesForceTheMixedJets.lean`: `vanishesToOrder_stepanov_of_syzygies` and `two_pow_le_length_stepanov_of_syzygies`.

All displayed conclusions have kernel-checked proofs. Transitive axiom
audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
All three new modules passed final plain `lake --old env lean` checks.
The transfer, its mixed-jet consequence, and the correction to the amplifier
interpretation form one contribution.
