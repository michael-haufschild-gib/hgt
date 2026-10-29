# Remove the finite head from the actual Haar Weil payment

- **ID:** acs-low-haar-head-payment
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Route:** ACS: full-source effectivity → Hodge index → RH.
- **Target:** Prove nonnegativity of `roughWeil (haarSectionProfile d X)`
  for every signed coefficient family d and every horizon X, including
  the finite low-index head.

## Current evidence

`exists_haarTail_roughWeil_floor` proves a uniform mass floor above one
fixed lower index. Its proof pays the full actual prime sum and both pole
moments, but its coarse outgoing-row constant leaves the head untreated.

`exists_uniform_finite_head_for_haar_prime` now approximates the entire
prime diagonal by a literal finite coefficient head, within ε times the
original complete-profile Gamma energy. The corresponding nonfirst mixed
source retains any complete Gamma share below one after a head.
Neither theorem pays the remaining head or its interaction with the tail.

## Concrete diagonal payment

First discharge the actual diagonal at every index, including index one.
For adjacent widths u,v, put w=u+v, M=uv/w and let E(s) be Gamma energy
per unit mass of an interval indicator of width s. Quadratic polarization
gives the exact normalized balanced energy E(u)+E(v)−E(w).

The corpus supplies the exact interval exterior kernel, elementary bounds
on its antiderivative, and polynomial bounds on its first moment. These
give

`Gamma(h)/M + 2*gammaHardyPhaseRate(0)
 ≥ 1−gamma_E−log(2*pi*M)−w^2/16−5*w^3/192`.

For the actual pairs, w≤log(2) and M≤w/4. Centering both exponential
weights bounds the actual pole by `−haarMass(a)^2/2`. The prime diagonal
of one Haar atom is exactly zero. The
[formalized diagonal proof](../3-formalized/acs-every-haar-cell-positive.md)
gives `roughWeil(haarProfile a)≥haarMass(a)/10` for every a≥1, including
the first cell. Both exact Lean file checks passed. Positivity of arbitrary
signed sums still requires the cross-pair terms; this card remains open.

## Checked arithmetic reserve on the entire head and tail

[Divisor squares and their uniform mass floor](../3-formalized/acs-haar-prime-ground-state.md)
retain every actual prime edge. With n_a=2a+1, the exact incoming charge is
`(log(n_a)−Lambda(n_a))*M_a`, because the odd root one is absent. Completing
each edge square gives

`D_X(d)=sum_a [log(n_a)*M_a+O_X(a)]*d_a²−haarPrimeEnergy(d,X)
       =Q_X(d)+sum_a Lambda(n_a)*M_a*d_a²
       ≥ (log(2)/12)*sum_a M_a*d_a²`.

Here Q_X is the original nonnegative divisor-square sum and O_X is the
exact outgoing charge with inverse-square multiplier budget. Both direct
Lean module checks passed. No arithmetic head is removed in this floor.
It does not prove the parent Weil sign: the original Gamma/central-mass
and retained arithmetic terms still require a joint comparison with this exact diagonal.

[Pole payment](../3-formalized/acs-haar-prime-defect-pays-poles.md) now has a
clean direct Lean check. For every signed section and every horizon,
`P≥−7mass/144`, `D_X+P≥D_X/8`, and `D_X+P≥mass/144`.
Both original pole moments and every low-index coefficient remain.
Centering at the common boundary gives exact first distance moment M*w/2;
the two exponential functionals then have summable normalized squares.
This pays the poles from the actual arithmetic defect without removing a head.

## Checked signed Gamma interaction

[The full off-diagonal Gamma bound](../3-formalized/acs-haar-gamma-off-diagonal-mass.md)
now gives, for every signed section and horizon,

`abs(Gamma(h)−sum_a d_a² Gamma(H_a))
 ≤ haarGammaBoundaryCost(d,X)
 ≤ exp(1/2)*sum_a logCellWidth(a)*d_a²
 ≤ 16 exp(1/2)*integral h²`.

Both signs of each mean-zero pair are paid by the actual positive
rectangle remainders. Disjoint target intervals spend each row remainder
once; exact finite assembly keeps the original Gamma normalization.
The three source files passed clean direct Lean checks. No low index or
touching pair is omitted. This removes logarithmic growth from the entire
signed Gamma interaction; its ordinary-mass cost still needs joint payment
with the full divisor-square defect and central mass.

## Investigation

Seek a direct shared Gamma–prime payment on all actual Haar cells, keeping
the now-paid original poles. Retain the full divisor-square defect when
comparing with its exact logarithmic/outgoing potential; its scalar floor
alone discards useful arithmetic energy. The sharp bound `P≥−7mass/144`
is available without spending a Gamma share. The exact boundary cost now
controls the full signed Gamma error in ordinary mass. The required
all-head joint inequality remains open. An all-head conclusion
must preserve cross terms, not combine separate diagonal inequalities.

One candidate joint comparison uses the actual divisor-square generator.
With `n_a=2a+1`, investigate the coordinates `u_a=sqrt(n_a)*d_a`
and weight `pi_a=M_a/n_a`. The proposed edge expression is
`Lambda(m)*pi_b*(u_a−u_b)^2` when `n_a*m=n_b`.
The comparison model has geometric prime parameter `q=1/p`; the existing
critical `primeBlaschkeParameter=1/sqrt(p)` is a different parameter.
`HTGeometry.HardyNumberSpectrum` supplies a basis for general `q`.
The exact mass change and any outgoing boundary completion must be proved
before using that model to pay the original Gamma boundary cost. This is
an investigation of the full signed head inequality, not a proved bridge.

No all-head positivity claim is established. No numerical experiment,
web search, novelty check, or axiom check is authorized. If this target
fails, record its precise obstruction and extract the strongest actual
positive payment before retiring it.

Even a successful all-Haar theorem leaves first-prime coarse/detail
mixing and the coarse signed source open; it would remove one actual
finite-head cost, not close full ACS.
