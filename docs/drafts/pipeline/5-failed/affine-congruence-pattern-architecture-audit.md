# Affine congruence patterns: architecture audit

**Stage:** failed as a novel architecture. **RH status:** no implication. **Novelty status:** the first source
construction reduces to the existing periodic L-series class; it is not a qualifying architecture.

## Concrete proposal and first conjecture

The same-integer divisibility audit leaves neighboring integers outside its product-independence
statement. A concrete extension is to retain a finite family of bits

`b_j(n) = [q_j divides a_j*n+c_j]`

and apply an arbitrary complex-valued function `Phi` to the whole bit vector before forming the
Dirichlet series. Slopes and offsets are fixed natural numbers; moduli are positive integers.
This includes finite neighboring-integer products and arbitrary finite nonlinear Boolean rules.

**First conjecture:** this finite nonlinear extension escapes scalar congruence L-series.
**Failure:** if `M` is the product of the moduli, every bit and therefore every `Phi`-observable
depends only on `n mod M`. Consequently the entire construction is one function on `ZMod M`.
Mathlib's existing `ZMod.LFunction_eq_LSeries` identifies its Dirichlet series, for `Re(s)>1`,
with the finite Hurwitz-zeta combination defining `ZMod.LFunction`. Nonlinearity in a finite
bit vector does not escape that existing source class.

This rejects this proposed finite construction as a new architecture. It does not prove that all
uses of translations, all nonlinear operations on analytic functions, growing moduli, or ordered
infinite histories have the same reduction.

## Positive-survivor audit

The strongest representation statement available here is an exact theorem for every finite affine
congruence observable, including arbitrary nonlinear `Phi`, non-coprime moduli, and non-invertible
slopes. No independence hypothesis is needed. Since `q_j` divides `M`, reducing `n` modulo `M`
preserves each congruence. Defining `Theta(r)=Phi(b_j(r.val))` therefore gives

`f(n)=Theta(n mod M)`

and, in the absolute-convergence half-plane,

`sum_(n>=1) f(n)*n^(-s) = M^(-s) sum_(r mod M) Theta(r)*hurwitzZeta(r/M,s)`.

The zero residue uses mathlib's periodic Hurwitz convention. This is existing periodic-L-series
mathematics applied to the proposed arithmetic construction, not a new RH theorem. A scratch proof
checks the coefficient reduction and invokes the already-proved analytic theorem.

**Second pass:** dropping coprimality, allowing zero or non-invertible slopes, overlapping the
congruences, and allowing arbitrary nonlinear `Phi` still leaves exactly the same finite residue
representation. None produces a new invariant or replacement source law beyond that existing
periodic-function representation. **NO POSITIVE SALVAGE FOUND** in the sense of a new nontrivial
mathematical survivor. The useful output is a verified source-class collision, not a renamed known
fact promoted as a research theorem. No new production Lean module is warranted for this reduction.

## Evidence and verification

- Corpus search: `nonlinear` outside `RHTower`, `Gamma`, and `Spectral`, all 85 capped results
  across 66 matching modules; this is a declaration screen, not inspection of every proof.
- Source inspections: `ConstitutiveReciprocalFusionTopology`, `ConstitutiveMutationalGenesis`,
  `Sieve/ShiftedCongruenceCount`, `EulerDeletionCoprimeWordPeriodicity`, and mathlib's
  `NumberTheory/LSeries/ZMod.lean` through its non-completed L-function definition and comparison.
- Exact further queries: `shifted divisibility`, `periodic Hurwitz`, `residue reconstruction`,
  `deletion shift`, `periodic series`, `PeriodicLSeriesRightAsymptotics`; each paired with `rg`.
- Existing analytic source: [mathlib periodic L-functions documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/ZMod.html).

`lake env lean /tmp/hgt-affine-congruence-wJNNDv/NormalForm.lean` passed. The scratch defines the
product period, the actual affine congruence observable, and its `ZMod` representation. It proves
`residue_reconstruction`, `full_affine_pattern_is_periodic_LSeries`, and
`full_affine_pattern_hurwitz_normal_form`. Selected `#print axioms` reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. The proof uses congruence transport and the existing
analytic identity; no computed instance or extra postulate enters.

All Lean processes started for this check are terminal. No production module, umbrella edit,
build, or numerical experiment was needed. The result records an exact collision with established
mathematics; it does not certify any RH-producing theorem.
