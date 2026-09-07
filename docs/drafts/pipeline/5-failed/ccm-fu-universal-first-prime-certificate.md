# CCM-FU: universal first-prime geometric certification is false

- **Stage:** 5-failed
- **Type:** unconditional actual-source obstruction with formal quantitative survivor
- **Parent:** [reserve-extension induction](../1-in-progress/ccm-fu-reserve-extension-induction.md).
- **Boundary:** Complete certified paths, negative-support extension from certified states,
  the two-prime energy ceiling, PE4, SD1 and RH remain open.

## Closed obstruction

Write `Phi(P)=Q_P+2sqrt(G_P D_P)` and `B=Q_empty`. For every real L,
all sufficiently large primes p satisfy, at cutoff M=12p,

`Phi({p})-B > L*p`.

In particular arbitrarily large primes give `Q_{p}<=B<Phi({p})`.
The ordinary energy contraction remains true; universal first-prime
geometric certification is false. Replacing G by B only increases the
geometric allowance, since `G<=Q_{p}<=B`, so that sufficient estimate fails
as well. The stored passes through1024 remain finite observations at their
stated cutoffs. No numerical computation enters these proofs.

## Analytic quotient-twelve overshoot

Let `c=log(2*pi)/2-gamma-1/4`, the proved uniform unsigned-channel mean.
Analytic estimates give

`c<=37/400`, `K_1(12)>=0.323`,
`(c+1/2000)*sqrt(12)<=K_1(12)`.

The harmonic half-correction at16 gives `gamma>=0.5768`. The twelve-term
Taylor lower bound for `exp(1.838)`, together with `pi<3.1416`, gives
`log(2*pi)<1.838`, hence the displayed upper bound for c.

The exact divisor defect at11 is bounded below by1.175. Its logarithms
are controlled by the established bounds for log2, log3 and log5, the
analytic inequality for log(8/7), and `2^8*5<=11^3`. The cutoff-eleven
channel box gives `K_1(11)>=0.15`; the successor identity and
`sqrt(12)-sqrt(11)>=0.1473` then give `K_1(12)>=0.323`.
Finally `sqrt(12)<=3.465` proves the strict coefficient margin.

At M=12p, exact homothety gives `K_p(M)=sqrt(p)*K_1(12)`.
The uniform mean error with epsilon1/4000 therefore makes the first
retained head at most `-sqrt(M)/4000` once p is large enough.
Keeping this head in the complete defect sum gives `D_{p}>=p/2000000`.

## Positive survivor: the complete energy scales

One constant b>0 and one threshold give, at every subsequent prime p,

`G_{p} >= b*p^2-136130*p`,
`p/2000000 <= D_{p} <= 122018*p`,
`0 <= B-Q_{p} <= 14112*p`.

Every source coordinate remains included. The upper defect bound is the
proved adjacent-cutoff bound, with quotients12 and13. The exact first-prime
release is twice the unsigned overlap. Its child channel vanishes for d>12;
on the remaining twelve cofactors, `mu(d)^2<=1` and `K_d<=7sqrt(M)` give
the displayed linear reserve ceiling. The already proved prime2 quadratic
release supplies `B>=b*p^2` for one b>0, independently of the selected p.
The identity `G+D=Q_{p}` then gives the good-energy lower bound.

Thus the complete defect has linear order, the good energy has quadratic
order, and the released reserve has only a linear upper bound. The
quadratic upper bound for good energy follows from `G<=Q_{p}<=B<=722M^2`.
For `K=abs(L)+14113`, enlarge the prime threshold until
`b*p>=2000000*K^2+136130`. The displayed inequalities force
`sqrt(G D)>=K*p`, hence `Phi({p})-B>L*p`.

This is a quantitative source-level obstruction, not an arbitrary-cube
example or a failure of the actual energy ceiling. A complete adaptive
argument must select its admissible first primes or retain sharper actual
signed overlaps; it cannot certify every initial prime through this radius.
No universal comparison for later already-certified fields follows here.

The [exact-overlap recovery](../3-formalized/ccm-fu-exact-overlap-recovery.md)
proves a stronger positive property of this same infinite family: at12p,
every sufficiently large prime p allows **every** available second prime
under the original diagonal, despite failing the geometric certificate.
All original four-cofactor blocks contract. The proof uses the new global
unsigned ceiling `3sqrt(M)/5`, the exact mean, and analytic quotient-twelve
bounds. Thus failure of this sufficient certificate need not signal even
one inadmissible next prime. Complete adaptive iteration remains open.

## Lean certificate

`formal/GaloisForLFunctions/RHTower/MobiusDivisorFirstPrimeCertificateObstruction.lean`,
namespace `RHTower`:

- `divisorUnsignedDilationChannel_twelve_mean_overshoot`.
- `exists_firstPrime_twelve_energy_balance`.
- `exists_firstPrime_twelve_geometric_excess`.
- `exists_firstPrime_contracting_energy_failed_certificate`.

Both the obstruction and the quantitative positive survivor have closed
analytic paper proofs and Lean proofs. No source experiment was run for
this conclusion; the old table served only to locate the quotient profile.

Scratch and exact leaf checks passed using `lake env lean`. Only this new
leaf olean was emitted. Its four public declarations were axiom-audited
once, all using only `propext`, `Classical.choice` and `Quot.sound`.
The module is wired into `RHTower`; the research index is refreshed and
formal lint passed. No full, umbrella or dependency build ran, and the
previously encountered stale-dependency Lake audit was not repeated.
All owned Lean processes terminated and scratch/audit/log files were removed.
The frontier map was not edited.
