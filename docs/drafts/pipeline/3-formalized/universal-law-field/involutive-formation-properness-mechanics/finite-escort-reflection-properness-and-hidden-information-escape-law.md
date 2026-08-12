# Finite escort reflection properness and hidden-information escape law

- **ID:** ULF-IFPM-1
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM / FOUR-ORGAN FUSION / GLOBAL PROPERNESS
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [NOT RH]`

## 1. Setup

Let `I` be a finite nonempty set.  Let `w_i>0`, `sum_i w_i=1`, and let `r_i in R`.  Define

\[
 Z(t)=\sum_iw_ie^{tr_i},\qquad
 p_t(i)=\frac{w_ie^{tr_i}}{Z(t)},
 \tag{EFR.1}
\]

\[
 m(t)=\sum_i p_t(i)r_i,
 \qquad
 v(t)=\sum_i p_t(i)(r_i-m(t))^2.
 \tag{EFR.2}
\]

The functional-equation action is parameter reflection `rho(t)=-t`.  Define directed and symmetric
finite information works by

\[
 K(s,t)=\sum_i p_s(i)\log\frac{p_s(i)}{p_t(i)},
 \qquad
 J(s,t)=K(s,t)+K(t,s).
 \tag{EFR.3}
\]

Put `J_ref(t)=J(t,-t)`.

## 2. Exact response generator

### Theorem 2.1

For every real `t`,

\[
 \boxed{m'(t)=v(t)\ge0.}
 \tag{EFR.4}
\]

If `r` is nonconstant, then `v(t)>0` for every `t`, hence `m` is strictly increasing.

### Proof

Differentiate the quotient in `(EFR.1)`:

\[
 m'(t)=\frac{(\sum_iw_ir_i^2e^{tr_i})Z(t)
                 -(\sum_iw_ir_ie^{tr_i})^2}{Z(t)^2}.
\]

Expanding `(EFR.2)` and using `sum_i p_t(i)=1` gives the same expression.  Every summand in
`v(t)` is nonnegative.  If `r_i!=r_j`, at least one of `r_i-m(t)` and `r_j-m(t)` is nonzero; its
strictly positive probability gives `v(t)>0`. QED.

## 3. Exact reflected information work

### Theorem 3.1

For every `s,t`,

\[
 \boxed{
 K(s,t)=(s-t)m(s)+\log Z(t)-\log Z(s),}
 \tag{EFR.5}
\]

\[
 \boxed{
 J(s,t)=(s-t)(m(s)-m(t)).}
 \tag{EFR.6}
\]

In particular,

\[
 \boxed{J_{ref}(t)=2t(m(t)-m(-t)).}
 \tag{EFR.7}
\]

### Proof

The likelihood ratio is

\[
 \log\frac{p_s(i)}{p_t(i)}
 =(s-t)r_i+\log Z(t)-\log Z(s).
\]

Take its `p_s` expectation to get `(EFR.5)`.  Add the two orientations; partition terms cancel,
giving `(EFR.6)` and then `(EFR.7)`. QED.

## 4. Complete-amplification properness

### Theorem 4.1

For `t>=1`,

\[
 \boxed{J_{ref}(t)\ge tJ_{ref}(1).}
 \tag{EFR.8}
\]

Consequently,

\[
 \boxed{
 \bigl(\exists C\;\forall k\in\mathbb N,\ J_{ref}(k)\le C\bigr)
 \iff r\text{ is constant}.}
 \tag{EFR.9}
\]

### Proof

Monotonicity of `m` gives

\[
 m(t)\ge m(1),\qquad m(-t)\le m(-1)qquad(t\ge1).
\]

Insert these inequalities into `(EFR.7)` to obtain `(EFR.8)`.  If `r` is nonconstant, strict
monotonicity gives `J_ref(1)>0`, so `(EFR.8)` makes the integer orbit unbounded.  If `r` is constant,
all `p_t` coincide and every work vanishes. QED.

## 5. Common-recovery lift

Let `kappa` be any parameter-independent Markov recovery kernel.  Form the packet law

\[
 P_t=p_t\otimes\kappa.
\]

The common-kernel KL isometry from ULF-PFM gives

\[
 \boxed{D(P_s\|P_t)=D(p_s\|p_t),\qquad
        J(P_s,P_t)=J(p_s,p_t).}
 \tag{EFR.10}
\]

Hence `(EFR.9)` survives every common recovery lift exactly.  Recovery is information-neutral, not
properness-neutral.

## 6. Fourth-organ prediction: hidden-information escape

Let `O_k` be any observed reflected work with `O_k<=C`, and define

\[
 L_k=J_{ref}(k)-O_k.
\]

### Corollary 6.1

For every integer `k>=1`,

\[
 \boxed{L_k\ge kJ_{ref}(1)-C.}
 \tag{EFR.11}
\]

If `r` is nonconstant, the right side tends to infinity.  Therefore a bounded recurrent observer
cannot be sufficient for the complete reflected family off the fixed locus.  Exact data processing
localizes the missing work in its conditional fibre.

Lean proves the stronger order-theoretic form: for every bounded-above observer sequence and every
nonconstant score, the hidden-loss sequence has no uniform upper bound.

### Proof

Subtract `O_k<=C` from `(EFR.8)`.  If observer were sufficient, directed KL and hence Jeffreys work
would be preserved, forcing `O_k=J_ref(k)`, contradicting boundedness. QED.

## 7. Hostile audit

1. Likelihood-ratio exponential families and their divergence formulas are classical information
   geometry; see Nielsen, arXiv:2207.03745, and Nagaoka, arXiv:1701.06119.
2. The theorem is not claimed as new scalar analysis.  Its field contribution is the exact fusion
   of reflection, common recovery, amplification, properness, and observer-fibre escape.
3. Strict positivity at one tilt is insufficient without complete amplification.
4. Common recovery preserves the work; arbitrary lossy observation need not.
5. Finite strict positivity uses full support.  With zero weights, “constant” must be replaced by
   constant on active support.
6. No RH coordinate or source uniform bound is assumed.

## 8. Gates

- [x] derivative/variance identity
- [x] exact KL and Jeffreys formulas
- [x] bounded complete orbit iff constant score
- [x] common-recovery information neutrality
- [x] fourth-organ hidden-loss prediction
- [x] Lean formalization and umbrella audit
- [ ] literal arithmetic source realization
