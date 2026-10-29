# Every individual complete Haar cell has positive original Weil energy

- **ID:** acs-every-haar-cell-positive
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** ACS: full-source effectivity → Hodge index → RH.
- **Parent:** [finite Haar head payment](../1-in-progress/acs-low-haar-head-payment.md)
- **Statement:** For every integer a≥1, `roughWeil (haarProfile a) ≥ haarMass a / 10`.

## Goal and scope

Remove the arithmetic cutoff from the actual one-cell diagonal. Existing
signed-section effectivity applies only above a fixed lower index. This
result includes index one, retains the actual Gamma term, central mass,
entire prime series and both exponential poles. It does not prove positivity
of a signed combination of distinct Haar cells: their cross terms remain.

## Gates

- [x] Source and statement fixed; no analytic input assumed.
- [x] Dependency-closed paper proof below, `[PROVED HERE]`.
- [x] Both exact Lean files passed direct `lake --old env lean` checks.

No axiom checks, numerical experiments, web search or novelty checks.

## Paper proof

Write `k(t)=exp(-t/2)/(1-exp(-2t))`, `Omega(s)=integral_s^infinity k(t) dt`
and `C(s)` for the Gamma energy of an interval indicator of width s.
The checked exterior-kernel identity gives

`C(s)=2s Omega(s)+2 integral_0^s t k(t) dt`.

The corpus proves the elementary bounds, for 0<s≤1,

`-log(s/4)/2+pi/4-s/4 ≤ Omega(s)
 ≤ -log(s/4)/2+s^2/96+pi/4-s/4+5s^3/384`,

and

`s/2+s^2/8-s^3/48 ≤ integral_0^s t k(t) dt ≤ s/2+s^2/8`.

The latter follow also from the sharper checked first-moment polynomial
bounds. Thus

`1-log(s/4)+pi/2-s/4-s^2/24 ≤ C(s)/s
 ≤ 1-log(s/4)+pi/2-s/4+s^2/48+5s^3/192`.

For the actual adjacent cell widths u,v, set w=u+v and M=uv/w.
Their balanced profile is h=(v/w)1_left−(u/w)1_right. Quadratic
polarization, keeping the energy of the union, gives exactly

`Gamma(h)/M=C(u)/u+C(v)/v−C(w)/w`.

The union is the complete cell at index a translated by log 2. Inserting
the interval bounds cancels the linear terms. Since u²+v²≤w²,

`Gamma(h)/M ≥ 1-log(M/4)+pi/2-w^2/16-5w^3/192`.

Gauss's checked quarter-digamma identity gives

`2 gammaHardyPhaseRate(0)=−3log2−gamma_E−pi/2−log pi`.

Consequently the actual archimedean form satisfies

`Gamma(h)/M+2 gammaHardyPhaseRate(0)
 ≥1−gamma_E−log(2*pi*M)−w^2/16−5w^3/192`.

For every a≥1, w=log(1+1/a)≤log2<7/10 and 4M≤w, so M≤7/40.
The checked bounds gamma_E<3/5 and pi<22/7 give 2*pi*M≤11/10;
`log x≤x−1` therefore gives log(2*pi*M)≤1/10. Also w²,w³≤1.
Hence the last display exceeds 1/5. The original Gamma energy pays its
entire central mass with a remaining floor M/5.

For the pole, let s=sqrt(2a), t=sqrt(2a+2). Exact zero mean and the
identity integral |h|=2M permit centering each exponential weight at the
midpoint of its range. Therefore

`|integral h(x)exp(x/2) dx| ≤ M(t−s)`,

`|integral h(x)exp(-x/2) dx| ≤ M(1/s−1/t)`.

Since s≤t≤3s/2,

`(t−s)(1/s−1/t)=(t−s)^2/(s*t)≤1/4`.

The actual pole product is consequently at least −M²/2. This retains
both exponential moments, rather than deleting the adverse one.

Finally the exact prime incidence for one Haar atom requires
`(2a+1)m=2a+1`. This is impossible for every m≥2, and the coefficients
at m=0,1 vanish. Thus its entire actual prime energy is zero. Combining
the archimedean and polar estimates gives

`roughWeil(h) ≥ M/5−M^2/2 ≥ (1/5−7/80)M =9M/80 ≥ M/10`.

Every step applies to every a≥1. `[PROVED HERE]`

## Lean implementation

- `ArithmeticCastelnuovoSeveri/TheGammaEnergyOfABalancedPair.lean`:
  exact interval cost, matching finite-part bounds, adjacent union and
  exact balanced polarization.
- `ArithmeticCastelnuovoSeveri/EveryHaarCellHasPositiveWeilEnergy.lean`:
  normalized Gamma identity, actual archimedean floor, centered pole
  payment, prime diagonal vanishing and `haarProfile_roughWeil_ge`.

Both modules passed direct Lean checks. The first module's missing olean
was built only for the second module's import. The second module's olean
was subsequently built only for `TheHaarArithmeticReservePaysBothPoles`.
Both modules are wired into their owning umbrella, which was not compiled.
No axiom checks were run.

The all-head signed theorem and full ACS remain open. Individual positive
diagonals do not imply that a matrix of mixed Weil pairings is nonnegative.
