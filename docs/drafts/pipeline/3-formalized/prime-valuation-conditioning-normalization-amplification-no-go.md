# Prime-valuation conditioning normalization amplification no-go

- **ID:** `prime-valuation-conditioning-normalization-amplification-no-go`
- **Stage:** 3-formalized
- **Type:** SOURCE-NORMALIZATION NO-GO / THIRD-COMPLETION CORRECTION
- **Scientific status:** `[PAPER PROOF COMPLETE] [STANDARD PROBABILITY CORE]`
  `[CANDIDATE-NEW CORPUS CONSEQUENCE] [NOT RH]`
- **Parents:**
  - `prime-valuation-kakutani-polar-third-completion.md`;
  - `prime-sieve-wold-gamma-bv-relative-character.md`;
  - `../1-in-progress/source-effective-polar-kummer-conormal-purity.md`.
- **Statement:** The unnormalized prime-sieve restrictions have telescoping total variation, but
  their source-normalized conditional states do not.  Consecutive normalized states are separated
  by exactly \(1/p\), every finite state is at maximal total-variation distance from the atomic
  weak limit, and the normalized net is not total-variation Cauchy.  Therefore the summable
  unnormalized defect \(a_P/p\) cannot control a regulator of the normalized conormal blow-up
  without a genuinely new cancellation theorem.

## 1. Source valuation law and its two normalizations

Let
\[
 \Omega=\prod_p\mathbb N_0,\qquad
 \mu_0=\bigotimes_p\mu_p,\qquad
 \mu_p(k)=(1-p^{-1})p^{-k}.
\]
For a finite prime set \(P\), put
\[
 A_P=\{\mathbf k:k_p=0\text{ for every }p\in P\},\qquad
 a_P=\mu_0(A_P)=\prod_{p\in P}(1-p^{-1}).
\]
There are two different source objects:
\[
 \lambda_P=1_{A_P}\mu_0,\qquad
 \nu_P=\frac{\lambda_P}{a_P}=\mu_0(\,\cdot\mid A_P).
\]
The first is the unnormalized vanishing conormal coefficient.  The second is the source-normal
blow-up which retains unit mass.

Use the probability convention
\[
 d_{\rm TV}(\alpha,\beta)=\sup_B|\alpha(B)-\beta(B)|.
\]

## 2. Exact normalization-amplification theorem

`[PROVED HERE]`

For finite prime sets \(P\subseteq Q\),
\[
 \boxed{\quad
 d_{\rm TV}(\nu_P,\nu_Q)
 =1-\frac{a_Q}{a_P}
 =1-\prod_{q\in Q\setminus P}(1-q^{-1}).
 \quad}                                                     \tag{1}
\]
In particular, if \(p\notin P\),
\[
 d_{\rm TV}(\nu_P,\nu_{P\cup\{p\}})=\frac1p.              \tag{2}
\]
By contrast,
\[
 \|\lambda_P-\lambda_Q\|_{\rm TV}
 =a_P-a_Q,                                                 \tag{3}
\]
and along every prime exhaustion the increments in `(3)` telescope to one.

### Proof

Under \(\nu_P\), the event \(A_Q\) has probability
\[
 \nu_P(A_Q)=\frac{\mu_0(A_Q)}{\mu_0(A_P)}=\frac{a_Q}{a_P},
\]
and
\[
 \nu_Q=\nu_P(\,\cdot\mid A_Q).
\]
For any probability \(\nu\) and event \(B\) of probability \(b>0\),
\[
 d_{\rm TV}\bigl(\nu,\nu(\,\cdot\mid B)\bigr)=1-b.
\]
The lower bound is obtained by testing \(B\).  For the upper bound, write the two measures on
\(B\) and \(B^c\); their signed difference has positive mass \(1-b\) on \(B\) and negative mass
\(1-b\) on \(B^c\).  Substitution of \(B=A_Q\) proves `(1)`, and `(2)` follows from
\(a_{P\cup\{p\}}/a_P=1-p^{-1}\).  Since \(\lambda_Q\leq\lambda_P\), the total mass of their
difference is \(a_P-a_Q\), proving `(3)`.

## 3. Weak atomic limit is maximally far in strong variation

On cylinder functions,
\[
 \nu_P\longrightarrow\delta_{\mathbf0}
\]
as \(P\) exhausts the primes.  Nevertheless, for every finite \(P\),
\[
 \boxed{\quad d_{\rm TV}(\nu_P,\delta_{\mathbf0})=1.\quad} \tag{4}
\]

Indeed,
\[
 \nu_P(\{\mathbf0\})
 =\prod_{q\notin P}(1-q^{-1})=0
\]
by Euler's divergence of \(\sum_q q^{-1}\), whereas
\(\delta_{\mathbf0}(\{\mathbf0\})=1\).

The normalized net is not total-variation Cauchy.  Given finite \(P\) and
\(0<\varepsilon<1\), choose finite \(Q\supset P\) with
\(a_Q/a_P<\varepsilon\).  Equation `(1)` gives
\[
 d_{\rm TV}(\nu_P,\nu_Q)>1-\varepsilon.                   \tag{5}
\]

Thus the boundary conditioning is a weak/cylinder convergence only.  It does not construct a
strongly convergent normalized state.

## 4. Consequence for the proposed contractive polar transgression

The nested sieve proves summability of the **unnormalized** source size
\[
 \frac{a_P}{p}
 +
 \sup_{|t|\le r}|\log\Phi_P(t/p)|.
\]
The open contractive-transgression proposal attempted to use this as a bound for increments of a
regulator attached to the **normalized** blow-up \(a_P^{-1}J(E_Pp_a)\).

Equations `(1)`--`(5)` show that this inference is invalid.  Division by \(a_P\) amplifies the
canonical singular transition from \(a_P/p\) to \(1/p\), and the latter is not summable over
primes.  The estimate
\[
 \|h_{P\cup\{p\}}-h_P\|_{L^1+L^2}
 \lesssim
 \frac{a_P}{p}
 +
 \sup_{|t|\le r}|\log\Phi_P(t/p)|
\]
may still be postulated as an RH-bearing cancellation theorem, but it is not supplied or made
plausible by convergence of the nested unnormalized relative character.  Proving it would require
new source structure which cancels normalization amplification.

This matches the independently proved Kummer leakage law:

```text
valuation conditioning:
  weak cylinder convergence to the boundary atom,
  no total-variation convergence;

finite coherent Kummer regulators:
  L2 convergence to the archimedean leakage vector,
  no L1 convergence.
```

Both are the same escape of normalized mass to prime infinity.

## 5. Positive survivor

The source-normal conormal cannot be realized by an ordinary strong limit of normalized states or
by a single-valued closed first-trace regulator.  The surviving third-completion architecture is
a singular relative object retaining all three pieces:

1. the coarse/weak endpoint;
2. the vanishing scale \(a_P\) and its normal direction;
3. the presentation maps whose normalized strong variation diverges.

A Rees, mapping-cone, local-cohomology, or equivalent derived boundary object may retain these
pieces.  Merely conditioning, taking a GNS limit, or applying a contractive functor to the
unnormalized total variation cannot.

The next RH-bearing theorem must therefore control a source-defined normal/Bockstein class after
normalization amplification.  It must not ask an ordinary normalized state net to be strongly
Cauchy, and it must not use \(a_P/p\) as though normalization had preserved that increment.

## 6. Hostile audit

1. The probability identity `(1)` is standard and carries no novelty claim.
2. Weak convergence to \(\delta_{\mathbf0}\) remains correct; `(4)` distinguishes topology rather
   than contradicting it.
3. The theorem does not disprove every possible polar transgression.  It disproves derivation of
   normalized strong control from the unnormalized telescoping bound.
4. A deliberately rescaled blow-up metric can restore small increments, but its nondegeneracy and
   ability to reject coherent off-line radial escape would then require independent proof.
5. Kakutani singularity of bulk radial sectors does not repair `(4)`; the boundary atom is singular
   to every finite conditioned bulk state.

## Novelty and literature boundary

Conditional probability, total variation, and weak-versus-strong convergence are parent
mathematics.  Targeted searches found rare-event conditioning, Doob transforms, total-variation
conditional limit theorems, and product-measure distance formulas.  They did not locate the exact
Wold/BV consequence: the same factor \(a_P\) whose unnormalized prime-sieve loss telescopes is the
normalizing mass of the conormal boundary state, and normalization changes the proposed
\(a_P/p\) control to the nonsummable \(1/p\) law.  Candidate novelty is restricted to this
source-specific no-go and its third-completion correction.

## Gates

- [x] exact conditional product states identified
- [x] pairwise total-variation formula proved
- [x] one-prime normalization amplification proved
- [x] maximal distance from the weak atomic endpoint proved
- [x] non-Cauchy theorem proved
- [x] contractive-transgression inference corrected
- [x] positive singular-relative survivor stated
- [ ] independent probability/operator-algebra specialist audit
- [ ] Lean formalization
- [ ] explicit relative/Rees source transgression
- [ ] RH

## Log

- 2026-07-29 — Hostile audit separated unnormalized prime-sieve variation from normalized
  conormal conditioning.  Proved exact total-variation amplification, maximal strong distance
  from the cylinder-limit atom, and non-Cauchy behavior.  Retired use of \(a_P/p\) as automatic
  control of normalized polar regulators.

## 2026-08-07 — the abstract core is formalized

The card's §2 rests on one general fact, stated there as "for any probability `ν` and event `B` of
probability `b > 0`, `d_TV(ν, ν(·|B)) = 1 - b`". That fact is now Lean, unconditionally and without
any decomposition theory, in `HTGeometry/ConditioningTotalVariation.lean`
(`lake build` green, 1702 jobs, axioms `[propext, Classical.choice, Quot.sound]`):

- `abs_toReal_cond_sub_le` — for every test set `A`, measurable or not,
  `|ν(A|B) - ν(A)| ≤ 1 - ν(B)`.
- `abs_toReal_cond_sub_self` — testing `B` itself attains the bound.

Together these say the supremum defining the total-variation distance equals `1 - ν(B)` exactly,
which is the card's boxed identity in the only form the argument uses. The proof is elementary
measure algebra: `A ⊆ (B ∩ A) ∪ Bᶜ` bounds the loss outside `B`, and `μ(B ∩ A) ≤ μ(B)` bounds the
inflation inside it, so no Jordan decomposition and no total-variation definition are needed. The
test set is not required to be measurable, which is slightly stronger than the card states.

**Still on paper.** Everything specific to the prime valuation source — the product measure
`μ₀ = ⨂_p μ_p` on `∏_p ℕ₀`, the cylinder events `A_P`, and hence identities (1), (2), (3) as
statements about `ν_P` — is not formalized. That needs an infinite product measure over the primes,
which the corpus does not have. What is formalized is the mechanism that makes the no-go work: the
normalized states are displaced by the *complementary mass*, which does not telescope, whereas the
unnormalized ones are displaced by the *mass difference*, which does. The card stays at stage 2.

## 2026-08-07 (second pass) — the amplification contrast itself is now abstract Lean

The first pass formalized only the single-step displacement. The card's actual mechanism is a
*contrast* between two nested-family behaviours, and that contrast is now Lean in full generality —
still with no product measure, since nesting is all the argument uses.

For a probability measure `μ` and nested measurable events `C ⊆ B` of positive mass:

- `abs_toReal_cond_sub_cond_le`, `abs_toReal_cond_sub_cond_self` — the normalized states are
  displaced by exactly the complementary **ratio**,
  `d_TV(μ(·|B), μ(·|C)) = 1 - μ C / μ B`, which is the card's identity (1). The proof is the
  single-step lemma applied to the measure `μ(·|B)`, using `cond_cond_eq_cond_inter` to see
  `μ(·|B)(·|C) = μ(·|C)` for nested events.
- `toReal_restrict_sub_restrict_le`, `toReal_restrict_sub_restrict_self` — the unnormalized
  restrictions are displaced by exactly the **mass difference** `μ B - μ C`, the card's identity (3).

Identity (2) is the specialization `μ C / μ B = 1 - 1/p`, immediate once the sieve measures exist.

The contrast is the whole no-go: mass differences telescope along a decreasing family, ratios do not.
Both halves are now unconditional Lean, so what remains genuinely unformalized is only the
construction of `μ₀ = ⨂_p μ_p` and its cylinder events — not the mechanism. The card stays at
stage 2.

## 2026-08-07 (third pass) — the product sector exists; identities (1), (2), (3) are Lean

The blocker recorded twice above — "needs an infinite product measure over the primes, which the
corpus does not have" — was wrong about mathlib: `MeasureTheory.Measure.infinitePi` builds the product
of a family of probability measures over an arbitrary index type, with `infinitePi_pi` giving the mass
of a finite cylinder. Combined with `ProbabilityTheory.geometricMeasure`, the sector is constructible.

New module `HTGeometry/PrimeValuationSector.lean` (`lake build` green, 2995 jobs, axioms
`[propext, Classical.choice, Quot.sound]`, in the umbrella):

- `primeValuationLaw p = geometricMeasure (1 - 1/p)` — the card's `μ_p(k) = (1 - 1/p) p^{-k}`, since
  mathlib's `geometricPMFReal q k = (1-q)^k q`.
- `primeValuationMeasure = Measure.infinitePi primeValuationLaw` on `∏_p ℕ`, a probability measure.
- `primeValuationCylinder P` — the event `A_P` that every prime in `P` has valuation zero.
- `primeValuationMeasure_cylinder` — **`μ₀(A_P) = sieveDensity P`**, identifying the card's `a_P`
  with the corpus's existing finite-variation sieve density from `PrimeSieveDensityTelescope`.
- `abs_toReal_cond_primeValuation_le` — identity **(1)**: the normalized states `ν_P`, `ν_Q` are
  displaced by `1 - a_Q / a_P`.
- `abs_toReal_cond_primeValuation_insert_le` — identity **(2)**: adjoining one prime displaces by
  exactly `1/p`, using the corpus's `sieveDensity_insert`.
- `toReal_restrict_primeValuation_le` — identity **(3)**: the unnormalized restrictions move by
  `a_P - a_Q`, the quantity that telescopes (`tsum_sieveDensity_div_prime`, already in the corpus).

So the no-go is now formalized on its own object rather than only in the abstract: the same nested
family gives normalized displacement `1/p`, which sums to infinity over the primes, and unnormalized
displacement `a_P - a_Q`, which telescopes to one. Stage advanced to 3-formalized.

What is still not formalized is the weak-limit half of §3 (maximal distance to the atomic limit) and
the failure of Cauchyness, which need the limit state rather than the finite ones.

## 2026-08-07 (fourth pass) — §3 as well: maximal distance to the atomic limit

The gap left at the end of the third pass is closed for its main clause.

- `primeValuationMeasure_zeroValuation` — **the sector is atomless at the all-zero valuation.** The
  point lies in every cylinder, so its mass is below `sieveDensity (sievePrefix e n)` for every `n`,
  and the corpus's `tendsto_sieveDensity_sievePrefix` squeezes that to zero. No new arithmetic: the
  divergence of `∑ 1/p` enters only through the existing telescoping result.
- `cond_primeValuation_zeroValuation` — hence every normalized state `ν_P` gives the all-zero point
  mass zero.
- `abs_toReal_cond_sub_dirac_zeroValuation` — testing that single point separates `ν_P` from the
  atomic weak limit by exactly `1`, the maximum possible total-variation distance, **at every finite
  stage**.

So all of §2 and the headline of §3 are now Lean on the actual sector. The weak convergence statement
itself (that `ν_P → δ_0` weakly, on cylinder functions) is not formalized; what is formalized is the
strong-variation half, which is the half the no-go uses.

`lake build` green (2995 jobs), axioms `[propext, Classical.choice, Quot.sound]`.

## 2026-08-07 (fifth pass) — the sieve weights are event probabilities of the sector

Three additions close the identification between §1's source objects and the corpus's existing sieve
layer.

- `primeValuationLaw_compl_zero` — `μ_p({0}ᶜ) = 1/p`. Together with
  `primeValuationMeasure_cylinder` this says the restarted Euler sieve weight
  `w_{N,n} = D_{N,n} / p_{N+n}` is the mass of a genuine event of the sector: *the first `n` tail
  primes have valuation zero and the next one divides*. The corpus proves `∑_n w_{N,n} = 1`
  analytically; that identity is now visible as the statement that this first-divisor index is almost
  surely defined.
- `iInter_primeValuationCylinder` — along a full enumeration the cylinders shrink exactly to the
  all-zero valuation, so the sieve's surviving set is a single point.
- `ae_exists_valuation_ne_zero` — **almost surely some prime divides**, the probabilistic content of
  the sieve's unit total variation.

`lake build` green (2995 jobs), axioms `[propext, Classical.choice, Quot.sound]`.

### Parent card status

`prime-valuation-kakutani-polar-third-completion` still has "full product-measure/Kakutani
formalization" open, and it is not reachable by the same route: **mathlib has no Kakutani dichotomy
and no Hellinger machinery** (its `Kakutani` files are Riesz–Markov–Kakutani, unrelated). Closing that
gate needs either a general Kakutani proof or a bespoke strong law for independent
non-identically-distributed variables — mathlib's `strong_law_ae` is iid only. Recorded rather than
attempted, since that card is flagged `[NOT RH]`.

### Pass — independence is the reason the sector works

`HTGeometry/PrimeValuationSector.lean`, two additions:

- `iIndepFun_primeValuation` — **the valuations at distinct primes are independent random
  variables** under `primeValuationMeasure`. Instantiates mathlib's
  `ProbabilityTheory.iIndepFun_infinitePi` at the identity family. This is the probabilistic content
  of the Euler product, and it is what makes every cylinder mass factor into local terms: the
  formula `primeValuationMeasure_cylinder = ofReal (sieveDensity P)` is no longer a computation but
  a consequence of independence plus the two local masses `μ_p{0} = 1 − 1/p`, `μ_p{0}ᶜ = 1/p`.
- `primeValuationMeasure_dividedCylinder` — every prime of a finite set `P` divides with probability
  `∏_{p ∈ P} 1/p`, i.e. the density of the multiples of `∏ P`. The complementary cylinder to
  `primeValuationCylinder`, and the second of the two arithmetic densities the sector reproduces.

`lake build GaloisForLFunctions.HTGeometry.PrimeValuationSector` green (3008 jobs), axioms
`[propext, Classical.choice, Quot.sound]` for both.

`RHTower/RouteRFirstDivisorPartition.lean` now also has its cached olean
(`lake build` green, 11307 jobs; `primeValuationMeasure_iUnion_firstDivisorEvent` and
`pairwise_disjoint_firstDivisorEvent` axiom-clean), so the whole first-divisor layer —
event masses, pairwise disjointness, total mass one — is built and reachable from the umbrella.
