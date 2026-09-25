# Frozen protocol: sign of the complete EDQ reciprocal flux

Classification: [BRIDGE] structural diagnostic, not a primary RH conjecture.
Read `docs/meta/scientific-method.md` before freezing. No result enters Lean.

## Question and frozen prediction

Can the full divisor flux be treated as a nonnegative source quantity?
The candidate is `reciprocalFlux(N)>=0` for every positive N. Its first
nonzero instance is positive: R(2)=(pi^2-8)/32. Individual directed kernels
are nonpositive, but their Möbius-weighted sum plus the exact mean correction
has no established sign. The motivation is a possible positive quadratic
interpretation of the complete primitive flux; evidence is limited and no
realization is assumed.

Parameter-free finite prediction: R(N)>=0 for EVERY N=1,...,512. Report
all cutoffs; do not select a favorable subsequence, fit a constant, or change
the range after seeing results. N=1 is exactly zero by its empty primitive.
Classify other cases as positive, negative, or unresolved from the full-series
enclosures, with a separate floating-point sensitivity margin 1e-8.

A separated negative enclosure reverses the prediction and directs proof
work away from treating this flux as a positive source on its own. If no
negative enclosure occurs, only this finite test survives; investigate an
actual sign identity before making any uniform claim. Neither outcome proves
or falsifies RH, the full energy ceiling, or cofinal subpower growth.

## Exact complete-series method

Let P_e(k)=(k mod e)*((k mod e)-e)/(2e),
K(d,e)=sum_(j>=1)P_e(dj)/(dj)^2, and c_N=(M(N)-H_mobius(N))/2.
The paper identity on the active EDQ card gives
R(N)=sum_(d,e<=N)mu(d)mu(e)K(d,e)+c_N.
The d=e entry is exactly zero. The complete-prefix recurrence adds the two
directed entries involving N, retaining both coefficient signs.

For each e use period e in j:
K(d,e)=d^(-2)*sum_(r=1..e)P_e(dr)*W(e,r),
where W(e,r)=sum_(m>=0)1/(r+me)^2. Fix S=512 complete blocks. With
a=r+Se, monotone integral comparison gives

```
sum_(m<S)1/(r+me)^2 + 1/(e*a) <= W(e,r)
 <= sum_(m<S)1/(r+me)^2 + 1/(e*a) + 1/a^2.
```

Since P_e<=0, reverse the weight endpoints when producing each kernel
interval. Propagate signed interval endpoints through every cutoff.
This retains all infinite tails; it is not a finite time-window flux.

## Controls, execution and archives

- Exact integer sieve for mu and integer modular numerators; longdouble sums.
- Check the N=2 closed expression falls inside its kernel enclosure.
- Check all diagonal and divisibility-zero kernel entries are exactly zero.
- Independently evaluate the literal time-indexed U_N(k)*g_N(k)/k^2 for
  N=2,7,31 through T=262144. Compute U directly from residues and g by
  divisor increments. Bound its complete omitted tail by
  `B_N*sum_(d<=N)|mu(d)|/[d^2*floor(T/d)]`,
  `B_N=sum_(d<=N)|mu(d)|*d/8`. Require overlap with the kernel enclosure.
- Check recurrence against direct finite quadratic summation at 31,127,512.
- Record every cutoff, both complete kernel-bound matrices, all controls,
  runtime, Python/NumPy versions and longdouble precision.
- Run only on the authorized RunPod, eight processes, native thread pools
  limited to one per process, with a 120-second foreground timeout.
- Hash frozen inputs before upload; verify remotely. Download outputs,
  verify hashes, write report, remove only owned remote files and processes.

Analytic tail bounds and floating-point sensitivity are reported separately.
These are not certified interval arithmetic or Lean numerical proofs.
