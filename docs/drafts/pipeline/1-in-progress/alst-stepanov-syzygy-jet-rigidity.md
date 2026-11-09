# Exact Stepanov jets from polynomial syzygies

- **ID:** alst-stepanov-syzygy-jet-rigidity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** For an Euler derivation `D`, `h=Σ_i f_i ψ_q(g_i)`, and an Adams fixed point `u`,
  `D^k h(u)=Σ_{j=0}^k binom(k,j) q^(k−j)(1−q)^j D^(k−j)(Σ_i D^j(f_i)g_i)(u)`.

## Mathematical purpose
Determine the exact jets of the Stepanov construction before applying a norm
amplifier. The identity is proposed for arbitrary integer polynomial families;
it does not assume a vanishing or smallness input. If the coefficient moment
polynomials `Σ_i D^j(f_i)g_i` vanish for `j<r`, it would give exact Euler jets
of order below `r` on the full fixed grid.

## Evidence and novelty question
`StepanovsConstructionOnTheTorsion.lean` proves divisibility of the first
derivative by `ℓ` under `Σ_i (∂_j f_i)g_i=0`, then uses norm smallness to force
zero. Its amplifier theorem does not assume `Σ_i f_i g_i=0`, although the
module narrative discusses both identities together. Differentiating that
additional identity suggests exact vanishing already follows in the combined
setup. The precise all-order formula and its consequences need a corpus and
Lean audit before changing that narrative.

Polynomial syzygies and pointwise vanishing on the fixed grid must be
distinguished: differentiating the former gives additional identities;
pointwise vanishing alone gives none. The proposed first-jet identity is
`D h(u)=q D(Σ_i f_i g_i)(u)+(1−q)Σ_i D(f_i)(u)g_i(u)`.

## Proof route
On a product, let `A` differentiate the first factor and `B` the second.
After Adams substitution the Euler action is `A+qB`; at a fixed point,
write this as `q(A+B)+(1−q)A`. The two operators commute. Their binomial
expansion gives the displayed identity and makes every possible
archimedean vanishing input explicit.

## Gates
- [x] Corpus novelty audit: existing first-derivative divisibility and generic iterated Leibniz rules do not give the all-order Stepanov transfer identity.
- [ ] Complete paper proof, including mixed Euler words and boundary cases.
- [ ] Lean formalization and transitive axiom audit.

No jet-rigidity result is counted as proved. This concerns exact torsion
vanishing; arithmetic length still prices the order, and the construction
contains no zeta-specific input.

## Transfer mechanism
For `M_g(f)=fg`, set `T_q(U)=qDU+(1−q)UD`. Left and right composition commute,
so `T_q^k` has the claimed binomial expansion. Leibniz gives
`T_q(M_g)=M_gD+qM_Dg`, and `T_q` commutes with right composition by `D`.
This recurrence is precisely the recurrence for `D^k(fψ_q(g))` after
evaluation at a fixed point. It proves the scalar identity for arbitrary
families, before imposing any polynomial syzygies.
