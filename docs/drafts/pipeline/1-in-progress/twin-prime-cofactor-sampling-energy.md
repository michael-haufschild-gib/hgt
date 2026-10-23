# Cofactor sampling in the marked determinant energy

- **ID:** twin-prime-cofactor-sampling-energy
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [marked root-average paper deduction](../2-fully-proven/twin-prime-mark-preserving-root-average.md)
- **Statement:** Retain the natural density of a divisibility condition
  on the common cofactor in the signed determinant energy.

## Exact candidate

Fix `δ>0`, a polynomial frequency exponent `C>0`, and a smooth real
cutoff `η` supported on `[1,4]`. For each desired `D>0`, conjecture
that some fixed `K` has the following property.

Put `L=log X`, `Z=exp(L^(24/100))`, and
`a_i=1/10+i/(10(K+2))` for `1≤i≤K+1`. Let
`P_i={p prime:exp(L^a_i)<p≤exp(2L^a_i)}` and
`V_i=Σ_{p∈P_i}1/p`. The first `K` groups supply selected products
`a=p_1...p_K`; the last group supplies a prime `d∈P_(K+1)`.
All groups are disjoint for sufficiently large `X`.

Let `U=V=X^(1/10)`, `c_V(n)=Σ_{ℓ|n,ℓ>V}Λ(ℓ)`, and
`R_Z(n)=1_{P^-(n)>Z}`. For dyadic blocks with `MN≍X`,
`M,N≥X^δ`, restrict `m∈(M,2M]∩(U,∞)` and
`n∈(N,2N]∩(V,∞)`. Set, for real `|v|≤X^C`,

`α_m=μ(m)R_Z(m)m^(iv)`, `β_n=c_V(n)R_Z(n)n^(iv)`,

`A_h=Σ_{a,m,n:mn+2=ah} η(a/Y)(∏_{i≤K}V_i^(-1))α_mβ_n`.

The conjecture is the uniform estimate

`Σ_{h≥1,d|h}|A_h|² ≪_{D,δ,C,η} XY/(d L^D)`

for every nonempty label block `a∈[Y,4Y]` and every
`d∈P_(K+1)`, once `X` is sufficiently large. `K` is fixed
before `X`; its choice may depend on the displayed fixed parameters.

**[OPEN CORE]** The factor `1/d` must survive the signed energy
estimate. Restricting the nonnegative sum in the known full-energy
bound gives only `O(XY L^(-D))`.

## Why this is the next question

**Subsequent correction.** This pointwise estimate is no longer
needed for the partial-layer application below. The
[aggregation proof](../2-fully-proven/twin-prime-partially-consumed-mark-energy.md)
sums consumed selections before Cauchy--Schwarz, converting them
into a bounded weight depending on the modulus and cofactor.
It proves the contribution retaining sufficiently many marking
groups using the existing energy theorem. The pointwise sampling
claim itself remains unproved; fully consumed layers remain open.

The completed marked estimate assumes that root moduli avoid every
marking prime. To remove that assumption, retain the exact split of
a root divisor between the selected label and its cofactor. If
`q` is squarefree and `gcd(a,h)=1`, then

`1_{q|ah}=Σ_{d|a,d|q}1_{q/d|h}`.

Exactly one summand is nonzero when `q|ah`, namely
`d=gcd(a,q)`. After dropping `gcd(a,h)=1`, the excess terms have
a square of a marking prime dividing `ah`; their multiplicity
is at most `2^K`. The previously proved square-divisibility error
therefore still controls them for fixed `K`.

Fix a subset of the marking groups and a selected product `d`
from them. Write `a=da'`. The root modulus becomes `q=dr`, and
the remaining root restriction is `r|h`. The coefficient at `h`
is a remaining-group cofactor coefficient evaluated at `dh`:

`A_h^(d)=C_d A'_(dh)`, `Y'=Y/d`.

The normalization `C_d` is a product of fixed `V_i^(-1)`, hence
bounded in terms of the number of groups. The smooth cutoff is
exactly `η(a'/Y')`; it introduces no new frequency scale.

If sufficiently many marking groups remain, their source energy
gives only

`E_0^(d)≪XY/d · L^(-D)`.

The elementary weighted-energy proof, keeping the smaller number
`O(Y/d)` of labels and the original cofactor length `H≍X/Y`, gives

`E_2^(d)≪XY/d² · L^17`.

After physical endpoints and the finite modulus inequality, this
costs `X d^(-3/4)L^((21-D)/4)`. Summing `d^(-3/4)` over selected
primes cannot be absorbed by any fixed logarithmic precision.

The conjectured sampling factor instead gives
`E_0^(d)≪XY/d² · L^(-D)`, hence a modulus cost
`X d^(-1)L^((21-D)/4)`. The reciprocal prime sum is bounded.
This identifies the missing density precisely; it is not a request
for a uniform bound with an unaccounted modulus factor.

This diagnoses the loss in that particular order of summation.
It does not prove that the density estimate is necessary. Also,
the exact candidate above concerns one consumed prime from the
last group; a product of consumed primes would require a further
extension. No such extension follows merely by writing `d` for
the product.

## Falsification points and limits

1. The claim concerns the actual Type II coefficients above.
   Arbitrary coefficients or arbitrary residue-class restrictions
   are not included in its statement.
2. In the squared sum, `d|h` is equivalent to `mn≡-2 mod d`,
   because every retained label `a` is coprime to `d`. It is an
   edge condition in the determinant model. Equidistribution of
   the root alone does not prove that arbitrary edge restrictions
   preserve the operator estimate.
3. Character orthogonality followed by a uniform absolute energy
   bound loses the desired density: it averages `φ(d)` terms with
   coefficient `1/φ(d)`, giving no `1/d`. The source's major arcs
   only use logarithmic character conductors; polynomial Mellin
   frequencies do not enlarge that conductor range.
4. Even this candidate would handle only layers with enough free
   marking groups. If the modulus consumes all selected marks,
   the remaining positive energy has no averaging over labels.
   The source theorem does not cover that endpoint. Do not erase
   the Möbius sign there by an unsupported positive-energy bound.
5. Neither this conjecture nor its partial-layer consequence
   removes the weights on prime outputs. Twin-prime infinitude
   remains a separate unmet target.

## Preliminary verdict and novelty

**Verdict: BRIDGE.** Exact strengthening beyond the audited source
interface; not claimed new scientific knowledge. The density factor
has not been proved. Current corpus and primary-source searches
have not located this exact uniform sampling theorem. These searches
are not an absence certificate. Proof selection has changed because
the aggregate application can be proved without this strengthening.

Related corpus searches located the untwisted
`RHTower.Sieve.sum_moebius_isBigO_vinogradovKorobov`, but not the
needed uniform character-conductor or sampled-energy estimate.
That declaration is a search lead, not a substitute for either input.

## Gates

- [x] Exact conjecture and its consequence for consumed-mark layers.
- [ ] Exact corpus and current-literature attack completed.
- [ ] Dependency-closed paper proof, including the `1/d` factor.
- [ ] Unconditional Lean proof.
- [ ] Fully consumed layers and removal of the marks.

## Log

- 2026-10-23 — Derived the exact divisor split and the failed
  `d^(-3/4)` summation from the existing energy bound. Isolated
  the missing cofactor-sampling density. No added Lean premise,
  analytic theorem, or twin-prime result claimed.
- 2026-10-23 — Corrected the claimed necessity of pointwise
  sampling. Aggregating consumed selections first closes the
  partial-layer application from the existing determinant energy.
  The one-prime candidate is retained as an open strengthening,
  not as the current bottleneck or a proved result.
