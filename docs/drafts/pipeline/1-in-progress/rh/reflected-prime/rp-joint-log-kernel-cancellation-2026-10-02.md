# RP-55: joint logarithmic kernel cancellation

Status: active hard-frontier trial; no theorem claimed.
Route RP, unconditional RH. RP-54 made no frontier progress. Hard gaps:
positive-damping native negative work, signed high-LCM control, both
history debts. This trial retains both terms of the finite log-forcing
identity before taking any norms or passing to an infinite ray.

Notation follows RP-54: U is the literal unit head, H the complete native
Mobius head, R its quotient-log-weighted head. First test: reindex prime
forcing in both coefficient variables and check whether the resulting
bilinear kernel contains any cancellation beyond the original H^2.
If it does not, identify an additional source identity that changes that
kernel, rather than formalizing the reconstruction identity alone.

## First test: complete recombination is the original square

For x>=1 put A_d=mu(d)*sqrt(d)*U(x/d), 1<=d<=floor(x).
Finite convolution and symmetry in d,e give

  H(x)*R(x) = (1/2)*sum_(d,e) A_d*A_e*log(x^2/(d*e)),
  H(x)*sum_(n<=x) Lambda(n)*sqrt(n)*H(x/n)
    = -(1/2)*sum_(d,e) A_d*A_e*log(d*e).

Subtracting these two complete forms leaves

  log(x)*sum_(d,e) A_d*A_e = log(x)*H(x)^2.

Thus recombination alone does not expose a smaller signed remainder.
The proposed gain is identically zero before taking a norm. This is a
diagnosis of the attempted estimate, not a no-go for Route RP.

## Second test: use the literal unit-source differential equation

On every open interval between integer source events,

  d/dx (sqrt(d)*U(x/d))
    = primeFreeDivisorDefect(floor(x/d))/(2*sqrt(x)).

The same finite Mobius reconstruction collapses the summed numerator to
F(x)=psiDefect(floor(x)); hence H'(x)=F(x)/(2*sqrt(x)). The head is
continuous at each event, so finite integration by parts retains

  (2+epsilon)*integral_1^X H(x)^2*x^(-3-epsilon) dx
    = integral_1^X H(x)*F(x)*x^(-5/2-epsilon) dx
      - H(X)^2*X^(-2-epsilon).

Differentiating both coefficient variables produces F(x)^2. Integrating
through its jumps retains the same signed prejump term involving
F(n-1)*(Lambda(n)-1) recorded in RP-49. Ordinary integer entries remain;
prime-power positivity alone does not control their signed work.
The derivative test therefore does not furnish a new source estimate.
No identity or conditional receiver is being added to Lean.

## Third test: common-prime extraction in the chronological term

Expanding F(n-1)*Lambda(n) produces the ordered positive prime-power pair
sum, alongside the full ordinary-integer centering. Two von Mangoldt
labels with nontrivial gcd are powers of the same prime. For s=1+epsilon
and epsilon>=0, their full ordered contribution has the paper sum

  sum_p (log p)^2 * sum_(b>=2) (b-1)*p^(-b*s)
    = sum_p (log p)^2*p^(-2*s)/(1-p^(-s))^2.

This is summable already at s=1 by comparison with
sum_(n>=2) (log n)^2/n^2. Thus common-prime extraction does not touch the
unpaid distinct-prime correlation. It is not legitimate to drop all
proper powers: different-prime pairs containing a proper power are still
present. Nor can the ordinary-integer centering be dropped. Existing
chronological and midpoint balances pay jump corrections but provide the
wrong inequality direction (a lower bound on work) for the needed upper
energy estimate. No new bound for the remaining ordered sum was found.

## Reciprocal-phase and finite decomposition checks

The exact unsigned-source decomposition retains square births, the
terminal modular primitive, and the smooth component. RP-36 already
records the literal quotient-one cell

  A_M(d)=mu(d)*(2*gamma-1)*(sqrt(M)-sqrt(d)), M/2<d<=M.

Its period-one modular ramp is zero but its smooth part is not. Hence an
estimate restricted to nonzero reciprocal phases cannot control the
complete signed head. This previous obstruction was revalidated rather
than re-formalized. The existing uniform profile remainder is an unsigned
estimate and supplies no bound for the full high-LCM signed pair sum.

Read the exact finite Heath--Brown identity as another possible source
of arithmetic cancellation. It retains the truncation defect and removes
it only below its proved multiplicative support threshold. Its finite
identity supplies no estimate for the chronological state sampled at
the product cutoff. Bounding that state first would assume the desired
critical control. No unconditional critical estimate was inferred from
the identity or from an RH-conditional Chebyshev theorem returned by
search.

## Outcome and next attack

No frontier inequality, unconditional RH result, or new Lean certificate
was obtained. The recombination gain was proved to be identically zero
on paper; differential transport returned the known unpaid signed term.
This is not a retirement of RP. All four hard gaps remain open.

Next trial: apply finite bilinear dispersion to the complete short
quadratic source, retaining its smooth terminal cell and the original
maximum-index cutoff. The substantive obligation is cancellation in the
signed off-diagonal term. A coefficient identity, a product-only Selberg
sum, or a separately assumed source norm will not be counted as payment.

## Search evidence

Four owned research commands exited0. Candidate declarations, source
arguments, proof ideas, and proposed ingredient sets were inspected.
All relevant retrieved Lean evidence was source-only. Semantic coverage
was unmeasured and background refresh incomplete; no generated recipe
was treated as a proof.

- Joint97002: partial=false, no errors/unfinished stages; query1191235,
  coverage1191244/current1191253,64652files,zero pending. Older-coverage
  and semantic-unavailable warnings. The proposed fixed-core recipe
  does not control the native moving-cutoff kernel.
- Source50687: partial=false, no errors/unfinished stages; query1191278,
  coverage1191295/current1191298,64656files,zero pending. Its coprime
  column identity retains signed psiDefect at every supported quotient.
- Prejump76444: partial=true, semantic_retrieval unfinished after worker
  disconnect/cancellation; query1191301,coverage/current1191311,
  64656files,zero pending. Useful chronological identities were read;
  the proposed Chebyshev power-bound recipe assumes RH.
- Phase44080: partial=false, no errors/unfinished stages; query1191349,
  coverage1191362/current1191364,64659files,zero pending. Generic divisor
  cancellation and a different Fisher carrier do not estimate this form.

One guessed regularity filename did not exist; the actual
DivisorContinuousHeadRegularity was located before reading. No Lean
source changed, no Lean build ran, and prior successful audits were not
repeated. No subagents, numerical experiments, resource overrides,
commits, or pushes.

Cleanup: all owned processes terminal; four temporary research JSONs
removed. Scoped whitespace check passed. Goal remains active.
