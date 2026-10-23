# Goldbach signed-affine dispersion audit

- **ID:** goldbach-signed-affine-dispersion-audit
- **Stage:** 1-in-progress
- **Type:** CANDIDATE / external proof audit
- **Parent:** [unconditional Goldbach](goldbach-unconditional-2026-10-23.md)
- **Statement:** Audit and, where possible, repair the claimed signed-affine
  prime-pair lower bound before importing any part into Lean.

## Source and acceptance boundary

Juan Moreno Borrallo, [A Parity-Sensitive Liouville Decomposition for Binary Prime Correlations](https://www.researchgate.net/publication/403749879_A_Formalization-Oriented_Finite-Ledger_Framework_for_Spectral_Dispersion_in_Chen-Type_Additive_Prime_Problems),
DOI `10.13140/RG.2.2.17276.30082`. The page labels the preprint May 2026
and its full-text upload July 17, 2026. It claims a uniform prime-pair lower
bound and eventual Goldbach. This is an unverified claim, not an accepted
dependency. Even a repaired eventual theorem would leave the exact initial
range required by the user's all-target goal.

The search index exposed the statement of Lemma 13.19, equations (216)–(222),
and its use in the retained spectral estimate (239). The full local proof
and complete ancestry have not yet been retrieved. The direct download
returned HTTP 403; the web page exceeded the fetch-size limit. These are
retrieval limitations, not mathematical verdicts.
The `agent-browser` command is unavailable; the computer-use service reports
no browser providers. No browser session or external communication was created.

## Gates

- [x] Record exact first issue and a mathematically valid replacement.
- [ ] Check the actual generated weight class and the proof of Lemma 13.19.
- [ ] Check every use of the Fourier cutoff after its replacement.
- [ ] Audit the centered dispersion estimate and all imported estimates.
- [ ] Complete dependency-closed paper proof of the actual arithmetic result.
- [ ] Formalize that result without extra analytic assumptions.

## Fixed cutoff: derivative bounds alone are insufficient

The inspected statement assumes, uniformly over its cells, periodic smooth
weights with each fixed derivative norm `M_j(X)=X^o(1)`. It specifies
`K(X)=exp(sqrt(log X))` and claims a Fourier truncation error `O_B(X^(-B))`
for every fixed `B>0`.

Here is an explicit counterexample to that **derivative-only implication**.
Let `k(X)=floor(K(X))+1` and `Ψ_X(y)=cos(2π k(X)y)`. Every fixed-order
derivative has norm at most `(2π k(X))^j`, which is `X^o(1)`.
All Fourier coefficients at integer frequencies `|k|≤K(X)` vanish, but
`Ψ_X(0)=1`. Thus even an error tending to zero does not follow from those
derivative bounds at that cutoff. This is a symbolic family, not a numerical
experiment.

The source additionally refers to weights produced by its own completion.
The example has **not** been shown to belong to that narrower class.
Consequently the finding rejects the derivative-only justification, not
the specialized lemma under every possible additional property of those
weights, and certainly not Goldbach itself. Check for stronger regularity
or controlled cutoffs in the construction before making a broader claim.

## Positive replacement: an adaptive subpower cutoff

**Paper theorem.** Let `{Ψ_{X,t}}` be a family of smooth periodic functions,
where `t` ranges over the cells present at scale `X`. Assume that, for every
fixed nonnegative integer `j`,

`M_j(X)=sup_t (||Ψ_{X,t}^{(j)}||_1+||Ψ_{X,t}^{(j)}||_∞)=X^o(1)`.

There is one integer cutoff `K_*(X)=X^o(1)`, tending to infinity, such that
for every fixed `B>0` the Fourier truncation error at `K_*(X)` is
`O_B(X^(-B))`, uniformly in `t` and the point on the circle. The full Fourier
coefficient `ℓ¹` norm remains `X^o(1)`. No prescribed subpower cutoff works
for every such family; the cutoff must depend on the derivative profiles.

**Dependency-closed paper proof.** For each integer `m≥2`, choose `X_m`
so large that `M_j(X)≤X^(1/4)` for every `0≤j≤m²` and every `X≥X_m`.
This is possible because only finitely many fixed derivative orders occur.
Choose the thresholds strictly increasing and at least `exp(m²)`.
For `X≥X_2`, let `m(X)` be the largest `m` with `X_m≤X`, and put

`K_*(X)=ceil(X^(1/m(X)))`.

Then `m(X)→∞`, `m(X)≤sqrt(log X)`, and
`log K_*(X)/log X→0`. Also `K_*(X)→∞`.

For `r=m(X)²`, repeated integration by parts gives

`|hat Ψ(k)| ≤ M_r(X)/(2π|k|)^r` for `k≠0`.

Summing the two tails beyond the integer `K_*`, and comparing with an
integral, bounds the uniform error by

`[2/((2π)^r(r-1))] M_r(X) K_*(X)^(1-r)
 ≤ X^(1/4+1/m(X)-m(X)) ≤ X^(1-m(X))`.

For any fixed `B`, the last expression is at most `X^(-B)` once
`m(X)≥B+1`. The argument chooses a derivative order increasing with `X`
only **after** the diagonal thresholds control all those orders; it does
not treat fixed-order constants as uniform in an uncontrolled growing order.
Absolute convergence and the equality to the smooth function follow from
the order-two Fourier bound. The same order-two estimate gives
`∑_k |hat Ψ(k)| ≤ M_0(X)+C M_2(X)=X^o(1)`.

## What this repairs, and what remains open

This replacement retains a subpower frequency range and arbitrary polynomial
accuracy. If subsequent estimates use only these properties and the
coefficient norm, this particular cutoff issue can be repaired without
changing a fixed exponent margin. That compatibility is still unproved.

The replacement theorem is a general smooth-Fourier diagonal argument;
no novelty beyond that standard mechanism is claimed. Paper status: proved
above. Lean status: not formalized. In particular, no abstract smoothness
interface has been inserted as an assumption for an arithmetic theorem.

The claimed dispersion route remains active. This is **not** a retired
no-go card: the literal cutoff is unsupported by the displayed regularity,
but an admissible replacement exists at the analytic level. Full arithmetic
verification, and the user's all-target Goldbach theorem, remain open.

## External distribution input checked separately

Read Lichtman's [Theorem 1.7 and Proposition 3.1](https://arxiv.org/html/2309.08522v1).
The large-residue theorem really is uniform for one common integer residue
`0<|a|<x^(1+ε)` and gives the level below `153/256` with the Kim–Sarnak
exponent. Thus large target size alone is **not** a reason to reject this
input. Proposition 3.1 also requires triply well-factorable modulus weights,
a Siegel–Walfisz first coefficient with rough support, and
`x^ε≤N≤x^(1/3+ε)` for the shorter variable.

Lichtman's discussion explicitly distinguishes modified linear-sieve weights
from triply well-factorable weights. The arithmetic audit must therefore
check Borrallo's coefficient-class transfer (Theorem 4.7 and Proposition 4.12),
not just match the numerical distribution exponent. That transfer has not
yet been verified. The local corpus's lexical `Lichtman` query returned
no declarations; this is not a completeness statement about the corpus.

## Short fibres: the displayed cofactor inference fails

The indexed text of Lemma 10.4 and the beginning of Proposition 10.5 were
retrieved on 2026-10-23 from the same preprint's
[alternate indexed page](https://www.researchgate.net/publication/403749879_An_Exact_Spectral_Dispersion_Framework_Beyond_the_Classical_Parity_Barrier_in_Sieve_Theory_Exact_Spectral_Dispersion_and_Applications_to_Goldbach_and_Polignac_Conjectures).
The source uses the short orientation `A≤X^(1/2+o(1))`, marks the least
prime in its strict Buchstab tail, and treats `A/P≤log^B X` as forcing a
unit or prime cofactor. Proposition 10.5 starts with that restricted family.

**Independent size audit.** From `p≳A/log^B X` and `n≍X`, the valid bound is

`u=n/p ≲ (X/A) log^B X`.

Writing `A=X^α`, this is `u≤X^(1-α+o(1))`. The available upper bound
`α≤1/2+o(1)` cannot turn it into `u≤X^(1/2+o(1))`.
Likewise, a modulus `b₁≍B=X/A` belongs to the long orientation; it cannot
be treated as at most `X^(1/2+o(1))` without another restriction or switch.
The proof of Lemma 10.4 uses both unsupported upper bounds.

The correct roughness argument excludes two cofactor primes only when
`u<z²`. A sufficient condition is `p>n/z²`; using only the subunit bound
requires `A>X^(1-2β+δ)` for some fixed positive margin `δ`. This does not
cover the full short orientation. Relabeling the least prime as the largest
does not fix this inference: it changes the strict first-prime selection,
and even the largest prime of a balanced triprime can be below `sqrt(n)`.

**Explicit one-form family.** Take arbitrarily large odd primes `p`. By
Bertrand's theorem choose primes `2p<q<4p` and `4p<r<8p`. Choose
`k∈{1,2}` with `p∤qr+2k`; at least one works because their difference is
two. Put

`n=pqr`, `a=p+2`, `b=qr+2k`, `T=ab-n=2qr+2kp+4k`.

Then `T` is positive and even, `ab-T=n`, `gcd(b,T)=gcd(b,n)=1`, and
`p∤T`. The first affine form is primitive. At scale `X=n`, its variable
sizes are `A=p=X^(1/3+o(1))`, `B=qr=X^(2/3+o(1))`, with `AB=X`.
The marked least prime has `P=p` and `A/P=1`. For every fixed
`1/4<β<1/3`, eventually `p>X^β`, so `n` is squarefree and `X^β`-rough.
Nevertheless its cofactor is `qr`, a product of two distinct primes;
also `qr>sqrt(n)` because `qr>p`.

This family refutes the claimed implication from the listed one-form
sizes and roughness conditions. It does **not** establish a nonzero
counterexample after every two-form support and local-state restriction in
the source. Such an additional exclusion would need a proof; it is not
supplied by the size argument above. The finding is a gap in that argument,
not a disproof of Goldbach or of every possible repaired dispersion method.

**Exact positive replacement, paper proof.** For positive integers `n,z`
with `z≥2`, `n<z⁴`, and all prime factors of `n` at least `z`, let `p≥z`
be a prime divisor and set `u=n/p`. Then `u<z³`, since `u≥z³` would imply
`n=pu≥z⁴`. Every prime factor of `u` divides `n`, hence is at least `z`.
Three factors counted with multiplicity would give `u≥z³`. Thus `u` is
one, a prime, or a product of two primes. Squarefreeness makes the two
primes distinct. The sharper condition `n<p z²` excludes the last case;
conversely that case forces `n≥p z²`. This is the precise missing branch
and its size boundary. It is elementary factor counting, not new scientific
knowledge. Lean status: not formalized; the arithmetic route remains active.

## Second Vaughan step: the affine slope belongs in the modulus

The full first regime of Proposition 10.5 was subsequently retrieved.
It combines `u | ab₁-T` with a divisor `d | (ab₁-T)/u`, then invokes
Theorem 4.3 using only `ud≤X^(1/2-η₁)`. That theorem, checked directly,
requires the complete progression modulus at the scale of its
rough-Möbius argument to be at most `X^(1/2-η)`.

**Exact substitution.** Work on a primitive state, so `gcd(b₁,ud)=1`.
The first condition fixes `a≡r (mod ud)` for one residue `r`.
The second rough-Möbius argument is `h=b₂a-T` (a fixed sign changes
neither conclusion). Writing `a=r+ud k` gives exactly

`h=b₂r-T+b₂ud k`.

Thus the progression for `h` has modulus `b₂ud`, not `ud`. The modulus
already contains `b₂` when `u=d=1`. With `b₂≍B=X/A` and the short
orientation `A≤X^(1/2+o(1))`, the full modulus is at least
`X^(1/2-o(1))`. This is outside Theorem 4.3's fixed-margin range for
every positive `u,d`, eventually. Freezing `b₂` does not remove its
factor from that theorem's product-level condition.

Primitive gcd reduction does not erase this obstruction. On a primitive
second form, `gcd(b₂,T)=1`, so `gcd(b₂r-T,b₂)=1`. Any common divisor of
the residue and `b₂ud` must therefore divide `ud` and is coprime to
`b₂`. Removing it leaves the factor `b₂` in the progression step; the
new argument scale can only decrease.

The equivalence above is exact, not just a sufficient congruence. Indeed
the set `{b(r+mk)-T : k∈ℤ}` consists precisely of the integers congruent
to `br-T` modulo `bm`; its translation periods are exactly the multiples
of `bm`. This remains true when either factor is zero. The complete
paper proof and completed Lean audit are on the
[conductor card](../3-formalized/not_new_scientific_knowledge/goldbach-affine-progression-conductor.md).

This invalidates the displayed direct application of Theorem 4.3.
It does not exclude a different estimate averaging the long coefficient
`b₂` together with `u,d`, with the actual residues and coefficient weights
retained. Such an estimate is a missing analytic input; the source's
fixed-state invocation does not supply it. This is the leading repair
obligation, preceding the more elaborate spectral closure.

The unit-cofactor branch cannot be removed as a rare geometric endpoint:
whenever the first affine value is prime of size `X`, its marked prime is
that value and `u=1`, giving `A/P≤X^(-1/2+o(1))`. The short-fibre repair
therefore includes a full prime-first correlation problem.

The normalization also matters. The collision bound has outer factor
`A` and about `B²` weighted pairs. A uniform per-pair error
`O(X/log^K X)` gives a squared bound of size `A B² X/log^K X`, whereas
the target is `X²/log^K X=A²B²/log^K X`. A polynomial factor `X/A=B`
cannot be absorbed by choosing another fixed logarithmic exponent.
One needs a bound at the physical `a`-length scale, or a correctly
weighted aggregate estimate with equivalent strength.

## Attempted replacement by short-progression cancellation

The exact local source `RHTower/Sieve/MRFibreReduction.lean` takes
`havg : AveragedShortInterval ...` as an input. Its retrieved successors
in `OmegaSpectralFibre.lean` and `FibreWindowBridge.lean` still require
unproved-for-this-purpose spectral majorants and limiting bounds. Their
source statements were read; none is imported as an unconditional
Goldbach input.

Read Fei Wei's [Theorems 1.3 and 3.1](https://arxiv.org/pdf/2101.10134).
The quantitative statement requires `s log H≤(log N)^(1/32)/2` and
averages over starting points and residue classes. It therefore cannot be
applied at `N≍X` to the polynomial modulus `s=b₂ud`, nor does its
averaged conclusion select every target `T`. This rejects that direct
transfer, not the published theorem or stronger possible estimates.
The required polynomially rough, correctly centered, long-modulus
estimate remains unproved.

## Cauchy centering: exact obligation, still unresolved

Proposition 9.4 retains the complete sum over `b₁,b₂` after Cauchy, with
outer factor `A(log X)^C`. Thus the abbreviated equation (82) alone is
not evidence that the pair multiplicity was lost. The theorem replaces
raw correlations by centered ones; that replacement is the remaining
obligation.

For any finite complex matrix `F` and orthogonal projection `P` on its row
space, exact algebra gives

`F*F = F*(I-P)F + F*PF`.

Consequently `||Fβ||²` contains both the residual and projected squared
norms. A bilinear form `⟨α,Fβ⟩` is controlled by the residual Gram matrix
when `Pα=0`, or after its projected contribution has separately been
subtracted and accounted for. Merely replacing each raw correlation by
that correlation minus a proposed Euler-density average does not prove
either condition. The matrix formed by those averages must be matched to
the actual projection, or the discrepancy and surviving quadratic term
must be estimated. This is a standard algebraic audit criterion, not a new
analytic theorem or a counterexample to the source's arithmetic family.

Theorem 4.3 was also read: its rough-Möbius progression estimate explicitly
subtracts a mean over reduced classes. A nonzero unsifted rough mean does
not by itself contradict that statement. The local corpus query on
centering returned correlation identities in other settings, not a checked
unconditional estimate for this arithmetic remainder.

## Continuation

1. Read the full proof and exact generated-weight construction around
   Lemmas 13.18–13.19, including equation (223).
2. Track every occurrence of `K_Ψ` through the Kloostermanization and
   spectral bounds. Determine whether replacing it by `K_*` preserves them.
3. Independently check the asserted local Plancherel map and its multiplicity
   bound in Lemma 13.11; mere relabeling does not automatically preserve norm.
4. Check the zero-frequency subtraction and coefficient support before
   attempting any Lean transfer of the claimed prime lower bound.
5. Check the modified-sieve coefficient transfer against the precise
   factorability and variable-size conditions in Lichtman's Proposition 3.1.
6. Restore the semiprime-cofactor short-fibre branch and keep its actual
   long modulus. Check whether Proposition 10.5's second Vaughan step can
   cover it with the required coefficient norms and without circular use
   of the terminal estimates.
7. Identify the precise pre-Cauchy projection, compute its residual Gram
   matrix, and retain any difference from the asserted local density.
8. Replace the invalid second-Type-I invocation by a genuine estimate
   for moduli `b₂ud`, including its average over collision parameters.
   Do not hide the factor `b₂` in a frozen coefficient.

## Batch audit

- No proof of Goldbach or new scientific theorem has been obtained.
- The source review found unsupported cutoff, cofactor-size, and
  second-Type-I transfer steps. The last has an exact Lean certificate
  for the full modulus and its translation periods. These are audit
  findings and known support mathematics, not a claimed frontier advance.
- The new conductor leaf passed one direct compile and all three declaration
  axiom checks. The unchanged parity leaf was not recompiled; no umbrella
  was built.
- Repository-wide lint returned errors outside Goldbach: five missing
  umbrella reachability edges, three research leaves at the package root,
  and three stale generated indexes. No Goldbach error was reported.
  The indexes were regenerated after the check; global lint is not claimed
  green. Concurrent unrelated research files were not modified.
- Keep the arithmetic audit active; do not replace its missing signed
  estimate with an assumed interface or equate its eventual conclusion
  with the user's all-target goal.
