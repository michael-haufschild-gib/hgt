# All-cross Witt determinant: quadratic cancellation transmutes into negative quartic torsion

- **ID:** `ULF-ACW-1`
- **Stage:** 3-formalized
- **Type:** unconditional fusion/conservation theorem
- **Lean:** `GaloisForLFunctions.RHTower.AllCrossWittDeterminantGhostTransmutation`; verified

## 1. Big-picture interpretation

The corpus's all-cross-prime compensator was read through one quadratic ghost: diagonal physical
energy and off-diagonal energy cancel. The full determinant says something stronger and different.
The cancelled quadratic quantity is not destroyed. Nonadditivity of the Teichmüller lift moves it
up the completion tower. For an antisymmetric source, ghosts one, two, and three vanish, while the
first surviving ghost is a negative quartic interaction.

This is a completion mechanism, not static two-operation coherence: additive cancellation of the
source legs changes the multiplicative determinant divisor and creates a higher-order negative
channel. It gives a literal source-generated denominator of the type forced abstractly by
ULF-CIT-2.

## 2. Corpus audit before the theorem

Search used `scripts/formal_tools.py research` for higher ghosts of
`deningerBigWittCrossPairAllSource`, Teichmüller cross effects, quartic survival, and cross-pair
determinants.

- `DeningerGammaSixBigWittStokesSource` defines
  `Delta(x,y)=T(x)+T(y)-T(x+y)` and proves its first ghost vanishes.
- `DeningerBigWittFrobeniusCrossPairCoherentCompensator` proves only the second-ghost identity,
  its cancellation after Frobenius, and the diagonal/off-diagonal decomposition.
- `DeningerBigWittRing` proves `ghost_k(T(x))=x^k` for every positive `k`.
- `XiPrimeTwoThreeSeamRigidity` proves `|C_2(rho)|<|C_3(rho)|` off the critical line and equality
  of the two fixed charges only on it.
- `SourcePairPositiveQuarticGradedRealification` independently shows that preservation of lower
  signed traces can leave a quartic realness charge. It is a divisor-fed finite receiver; no
  source-side relation to the all-cross Witt determinant was present.

Corpus search found no third/fourth/all-degree ghost theorem for the existing all-cross source.
General big-Witt/ghost and characteristic-determinant technology is standard; the exact all-cross
transmutation and prime-seam specialization below are the new corpus result.

## 3. Universal all-depth law

Let `A` be a commutative `Q`-algebra. Let finite families `(ell_e)_(e in E)` and
`(r_f)_(f in F)` lie in `A`. In the big-Witt ring define

`X = sum_(e,f) Delta(ell_e,r_f)`,

where `Delta(x,y)=T(x)+T(y)-T(x+y)`.

Write power moments

`L_j=sum_e ell_e^j`, `R_j=sum_f r_f^j`.

### Theorem ACW-1 (all-depth cross-effect ghost)

For every `k>=1`,

`ghost_k(X) = - sum_(j=1)^(k-1) binom(k,j) L_j R_(k-j)`.

#### Proof

Ghosts are additive and `ghost_k(T(x))=x^k`. Therefore

`ghost_k(X)=sum_(e,f)(ell_e^k+r_f^k-(ell_e+r_f)^k)`.

The binomial theorem cancels the two endpoint powers, leaving the negative sum of mixed monomials.
Finite distributivity factors the `j`th left and `(k-j)`th right moments. QED.

### Corollary ACW-2 (low-degree transmutation)

If `L_1=R_1=0`, then

`ghost_1(X)=ghost_2(X)=ghost_3(X)=0`

and

`ghost_4(X)=-6 L_2 R_2`.

Thus the existing quadratic cancellation is the first face of an exact all-depth law. It does not
make the Big-Witt class zero.

## 4. Determinant identity

Under the power-series realization of the big-Witt additive group,

`series(Delta(x,y))=(1-xz)(1-yz)/(1-(x+y)z)`.

Hence

`series(X)=product_(e,f) ((1-ell_e z)(1-r_f z))/(1-(ell_e+r_f)z)`.

This exhibits the new divisor directly:

- marginal source legs give numerator zeros;
- additive cross-sums `ell_e+r_f` give denominator poles;
- the negative divisor is generated before scalar ghost evaluation.

The law is therefore a genuine addition--multiplication completion fusion. The denominator is not
chosen from a target divisor.

## 5. Antisymmetric ordered-edge source

Take an oriented finite edge set closed under reversal, with

`ell_(reverse e)=-ell_e`, `r_(reverse e)=-r_e`.

Every odd `L_j` and `R_j` vanishes. ACW-1 gives:

1. every odd ghost of `X` vanishes;
2. `ghost_2(X)=0`;
3. `ghost_4(X)=-6L_2R_2` is the first possible survivor.

For one two-orientation cell `E=F={+,-}` with legs `+/- ell` and `+/- r`,

`series(X)=((1-ell^2 z^2)^2 (1-r^2 z^2)^2) /
  ((1-(ell+r)^2 z^2)(1-(ell-r)^2 z^2))`

and

`ghost_4(X)=-24 ell^2 r^2`.

The rational determinant is nontrivial whenever `ell*r != 0`, although its first three ghosts
vanish.

## 6. Exact prime-seam specialization

For two distinct primes `p,q`, put

`d=a_p-a_q`, `ell=d/(pq)`, `r=conj(d)`.

These are exactly the two orientations in the corpus's
`deningerBigWittCrossPairLeftLeg/RightLeg`. Therefore

`ghost_4(X_(p,q)) = -24 |d|^4/(p^2 q^2) <= 0`,

with equality exactly when `a_p=a_q`.

For the fixed primes `2,3` and canonical seam charges `C_p(rho)`,

`ghost_4(X_(2,3)(rho)) = -(2/3)|C_2(rho)-C_3(rho)|^4`.

By `XiPrimeTwoThreeSeamRigidity`,

`ghost_4(X_(2,3)(rho))=0 iff Re(rho)=1/2`.

This is an unconditional source-defined quartic wall law for every complex `rho`; restricting it
to Xi support gives another exact RH receiver, but no divisor data was used to construct it.

## 7. Joint reconstruction / conservation identity

The finite all-cross determinant simultaneously reconstructs:

1. marginal numerator divisors from the left and right source legs;
2. the negative interaction divisor from every additive cross-sum;
3. every higher ghost from the two moment towers via ACW-1.

Quadratic physical cancellation is therefore conserved as higher interaction torsion. At the
smallest nontrivial antisymmetric stage it becomes a strict negative quartic. This supplies the
counterchannel type predicted by ULF-CIT-2 without fitting a meromorphic denominator.

## 8. What it changes and what remains open

This theorem kills the interpretation that the off-diagonal compensator annihilates physical
information. It redistributes that information through the determinant's higher ghosts and
cross-sum poles.

It does not prove RH. Closure now has a concrete object and a concrete task:

1. form the cofinal all-depth cross-effect determinant from literal prime--Gamma/source legs;
2. prove a source-normalized meromorphic/entire properness theorem for its cross-sum divisor;
3. identify its derived determinant torsion with the existing theta determinant before divisor
   specialization;
4. use the strict off-wall quartic as a contracting coefficient, proving torsion support lies on
   the neutral-grade locus.

The first three low ghosts no longer justify discarding the object. Its full determinant is the
candidate completion counterchannel.
