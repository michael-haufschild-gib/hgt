# Prime-valuation conditioning normalization amplification no-go

- **ID:** `prime-valuation-conditioning-normalization-amplification-no-go`
- **Stage:** 2-fully-proven
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
