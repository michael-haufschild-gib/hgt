# Route L: actual residual of damped paired prime Green sources

- **ID:** L-C41
- **Date:** 2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM / literal damped source, strict contraction, complete finite boundary
- **Depends on:** C38 paired source, C39 fixed Sonin transport, [C40 original-Meyer compact escape](../3-formalized/route-l-cofinal-green-source-limit.md)
- **RH status:** unproved

Chain: complete original Green/BV source → fixed-reader agreement →
conormal vanishing → RH. C40 excludes a coefficient-preserving limit of
exact cofinal prime-kernel sources in the original Meyer topology. It does
not apply automatically to damped approximate kernels. The next attack
must derive their residual and its full normalization before passing to a
source limit or claiming a physical boundary cancellation.

## Verified literal finite-source algebra

Use the original log translation `T_c g(t)=g(t-c)` and weighted reflection
`Jg(t)=exp(-t)g(-t)`. For `L=log(p)>0` and real damping `a`, put
`D_(L,a)=Id-exp(-aL)T_(-L)` and `E_(L,a)=D_(L,a) J D_(L,a) J`.
The existing exact J/translation law gives
`J D_(L,a) J=Id-exp(-(a+1)L)T_L`.
Thus its literal Mellin multiplier is
`A_(L,a)(s)=(1-exp(-(a+s)L))(1-exp(-(a+1-s)L))`.
For `a>=0` and an actual Xi coordinate, both factors are nonzero; the
multiplier is reflection invariant. This follows from open-strip placement,
not RH.

At the ORIGINAL prime circle, translation by either sign of L acts as the
identity. Therefore the COMPLETE periodization is
`Per_L(E_(L,a)g)=r_(L,a) Per_L(g)`, where
`r_(L,a)=(1-exp(-aL))(1-exp(-(a+1)L))`.
Its first variation at a=0 is `L(1-exp(-L))`, positive; this derivative
is a paper calculation, not a theorem included in this Lean module. For a finite
commuting product with one occurrence of p removed, the same identity
holds with the entire remaining source as g. Repeated prime depths retain
the corresponding power of the residual factor.

After normalizing by the actual Xi evaluation, the exact recursion is
`Per_L(g_(P,a))/M(g_(P,a))(rho)`
`= [r_(L,a)/A_(L,a)(rho)] * Per_L(g_(P\p,a))/M(g_(P\p,a))(rho)`.
The prefactor tends to zero, but the remaining normalized source moves with
the cutoff. Its growth is the mathematical obstacle; a fixed finite-source
continuity argument cannot prove the cofinal residual tends to zero.

The infinite Euler expression `1/[zeta(a+s)zeta(a+1-s)]` is only a candidate
chamber representation until its literal product convergence and source
admission are proved. Do not claim that a meromorphic continuation is an
original-Meyer source limit. Do not replace the original physical reader by
a newly normalized limiting diagnostic.

## Prior source checks

- C38 proves the undamped paired defect and the weighted J/translation law.
- `DeningerTomographyNonstrict.lean` has exact periodization of translated
  sources; `deningerPeriodizationSum_periodic` and the linear periodization
  map supply the required fixed-period identities.
- `Sieve/DampedEulerCorrection.lean` defines a relative damped Euler factor;
  its norm estimate is a different normalization, not the needed source law.
- `SoninCofinalMobiusGammaXiIncidence.lean` transports actual Möbius Fisher
  data through singular cofinal Sonin corners at fixed Euler points. Its
  `fixedEulerCofinalDamping` diverges to compensate a collapsing coordinate;
  it is not this vanishing damping parameter.
- Deep/method report `/tmp/route_l_cofinal_c40_abel_residual_deep.json`,
  generation 874835, semantic 2352929/2353624, partial. All 20 candidates and
  20 source arguments inspected; no generated ingredient premise adopted.

The complete 383-line module is
`formal/GaloisForLFunctions/RHTower/Deninger/DeningerDampedPrimeCircleContraction.lean`.
It proves the source operator and its weighted reflection mate, exact Mellin
multiplier, full original periodization residual, strict normalized
contraction, explicit Gaussian powers, and convergence in the original
smooth-circle topology. At every finite normalized stage the literal Xi
reading equals one and the COMPLETE original Gamma/flux discrepancy is
nonzero. The latter follows from the retained zeroth Xi jet and the exact
Poisson-class characterization of full Gamma/flux cancellation; it does
not assert a uniform boundary lower bound or a fixed Sonin-image limit.



## Strict contraction theorem and actual source powers

For every `a>=0`, `L>0` and actual Xi point `rho`, the normalized residual
is strictly contractive: `|r_(L,a)/A_(L,a)(rho)|<1`. Put
`q=exp(-aL)`, `x=exp(-L Re(rho))`, `y=exp(-L(1-Re(rho)))`.
`q` lies in `(0,1]`, `x,y` lie in `(0,1)`, and `xy=exp(-L)`. The reverse triangle inequality
bounds `|A_(L,a)(rho)|` below by `(1-qx)(1-qy)`, whereas
`r_(L,a)=(1-q)(1-qxy)`. Their difference is exactly
`q(1-x)(1-y)>0`. Thus the contraction is unconditional throughout the
open strip and has an explicit positive margin.

Repeating one original prime factor k times, with no other moving factors,
gives the exact normalized periodization `(r/A)^k` times the original
normalized periodization. This tends to zero in the actual prime-circle
space, while the Xi reading remains one. The actual family, its circle convergence, and its nonzero complete
Gamma/flux discrepancy are formalized. Transport of the damped full Xi
field through the fixed Sonin graph remains a separate comparison. In a cofinal
multi-prime family, the remaining operators can amplify other circle
components; the one-prime contraction does not by itself control that
moving remainder. That comparison is the next substantive obstacle.


## Source, method and broad-paper audit (2026-09-11)

Two 150-second deep/method searches inspected all 20 candidate lemmas and
20 source arguments per report. Generations 874984 and 875003; semantic
coverage 2353860/2353927 and 2353405/2353995. Both partial: runtime deadline,
filter/judge, and background source refresh. No generated proof ideas or
ingredient sets were returned. Concrete periodicity and Mellin/flow laws
were checked from source and then used in scratch. A contraction hypothesis
or an RH-equivalent variance bound from a search hit is not a producer.

Broad arXiv queries used damping, transfer, localization, cascade, cocycle
and amplification. Sources and applicability were checked directly:

- [Bärlin, nonlocalised damping, 30 April 2026](https://arxiv.org/html/2604.27877v1):
  the characteristic/Duhamel argument retains its lower-order forcing;
  its high-frequency gap and hyperbolicity are assumptions. It provides a
  useful reminder to control the full moving remainder, not a spectral-gap
  premise for this source.
- [Gharibian–Hecht–Rudolph, 8 September 2026](https://arxiv.org/html/2609.09033v1),
  Section 3.2: the polynomial `(1+T_l(2u-1))/2` stays bounded on `[0,1]`
  while its evaluation at a negative point grows. Its factorization
  `u Q_l(u)^2` controls a separate representation cost. This suggests
  looking for a fixed source evaluation that amplifies outside the
  controlled measurement range. The RH source identification and its
  topology must still be proved; the paper's pseudo-density is not our
  physical reader. The companion Lean repository is linked in the paper.
- [Chattopadhyay–Joardar, 23 June 2026](https://arxiv.org/abs/2606.24728):
  metric-dimension bounds for cocycle-twisted groupoid algebras have no
  established identification with the present original source.
- [Psaltis, 31 July 2026](https://arxiv.org/abs/2608.00176): absorbing Markov
  cascades concern stochastic transition data; the signed paired source
  does not acquire those hypotheses. No numerical method was run.
- [Hadfield, 7 September 2026](https://arxiv.org/abs/2609.07090) and
  [Khalil, 11 August 2026](https://arxiv.org/abs/2608.10571): quantum
  compression complexity and sensor selection supply no source comparison.

## Full-source growth and next source comparison

[Fixed negative Mellin amplification](route-l-damped-negative-mellin-escape.md)
now proves uniform growth of the whole damped finite prime product,
including varying damping tending to zero, and excludes its original-Meyer
limit. The next actual weaker source and its original boundary comparison
are recorded on that card.


## Verification

Final scratch `lake env lean /tmp/route_l_damped_c41.lean` passed with no
errors or warnings. The file is byte-identical to the new module:
383 lines, 18 public theorems, two private lemmas and eight definitions.
The final audit `lake build GaloisForLFunctions.RHTower.Deninger.DeningerDampedPrimeCircleContraction`
passed; only the new leaf was built (135 seconds, 11943 dependency-graph
jobs). One umbrella import, 26 public declarations and zero cross-module
name collisions were verified. Index refresh and global lint passed.
No full/umbrella build, numerical experiment, axiom-print command, added
axiom or proof placeholder was used. All C41-owned Lean/research processes
finished. RH and the original complete source-to-fixed-reader comparison
remain open.
