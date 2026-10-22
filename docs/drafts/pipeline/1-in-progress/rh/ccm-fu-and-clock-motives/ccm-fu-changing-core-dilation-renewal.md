# CCM-FU: changing-core dilation renewal

- **Stage:** 1-in-progress; global reserve propagation remains open. The source laws below are [formalized](../../../3-formalized/ccm-fu-changing-core-pair-reserves.md).
- **Goal:** Uniform signed reserve through exhaustive prime processing, then the every-cutoff Abel bound and RH.
- **Parent:** [exact successor extension](ccm-fu-exact-successor-extension.md).

## Closed source calculation

Let G_P be the literal continuous processed head and W_P(Y) its complete
inverse-cube dilation pairing. The exact prime update is
G_(P+p)(x)=G_P(x)-sqrt(p)G_P(x/p). Absolute convergence permits expanding
both factors of W. Substitution x=p*t in the two copied terms gives

W_(P+p)(Y)=(1+1/p)W_P(Y)-sqrt(p)/p^2 W_P(pY)-sqrt(p)W_P(Y/p).

The factor sqrt(p)/p^2 is p^(-3/2). Both copies and their common shift
remain present. This is a physical source identity, not a probabilistic
model or an estimate assuming a successful prime order.

For each fixed nonempty P, the proved contour residue plus integrable
boundary gives B_P with |W_P(Y)|<=B_P for every Y>=1. Consequently

|W_(P+p)(Y)+sqrt(p)W_P(Y/p)|<=3B_P

for every unprocessed prime p and every Y>=1. Division by sqrt(p) gives
an error tending to zero uniformly over the entire next-dilation ray.
The leading profile is the actual W_P evaluated at the ratio Y/p.
This distinguishes comparable-prime interactions from the previously
proved distant-prime limit with the enlarged core held fixed.

## Hard remaining comparison

This two-scale law must still be related to simultaneous finite-cutoff
successor admission and a reserve through all processed cores. Its B_P
is core-dependent. It supplies no common bound through exhaustion and
no every-cutoff RH conclusion. No experiment is needed: the displayed
identity and error estimate have a direct analytic derivation.

## Closed constructive even-core branch

For nonempty even P, the proved actual residue is strictly negative.
Thus W_P(lambda)<=-2c on some full tail lambda>=L. The same uniform
renewal estimate gives W_(P+p)(Y)>=c sqrt(p) when p is sufficiently
large and Y>=L*p. Restricting the next prime to [L*p,(L+1)*p] keeps its
coefficient release at order 1/p. This dominates the first merger's
possible cost of order p^(-3/2), giving a positive net pair reserve and
returning the processed core to even cardinality. The prime interval
theorem supplies such pairs beyond any prescribed lower cutoff.

Lean proves the complete pair reserve, even cardinality of the enlarged
core, and the resulting quadratic reserve for actual energies at every
sufficiently large cutoff for each selected pair. The same identity also
proves the opposite comparison near ratio one: sufficiently large
comparable prime pairs have a positive net cost of order 1/p, larger than
the first prime's possible release of order p^(-3/2).

The inverse use of this ratio window now proves that every sufficiently
large prescribed prime r has a reserve-producing partner p<r. The prime
interval theorem selects p between r/(L+1) and r/L. This universal
prescribed-prime statement, its actual-energy transfer, and the uniform
complete pair profile are [formalized](../../../3-formalized/ccm-fu-prescribed-prime-pair-reserves.md).

The constants and onset depend on the current core. Repeating existence
of these pairs still does not ensure inclusion of every prime or a common
physical cutoff threshold. The first merger can temporarily increase
energy, and a pair's final Q comparison does not bound every alternative
successor in Psi. Exhaustion, intermediate payment and the uniform
every-cutoff comparison remain the hard source obligations.
