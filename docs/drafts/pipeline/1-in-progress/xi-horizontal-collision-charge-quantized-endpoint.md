# Xi horizontal collision charge: quantized endpoint and replication gap

- **ID:** `xi-horizontal-collision-charge-quantized-endpoint`
- **Stage:** 1-in-progress
- **Type:** FRANKENSTEIN BRIDGE / PRODUCER SPECIFICATION
- **Status:** `[PAPER-PROVED ENDPOINT] [LEAN-PROVED] [AXIOM-AUDITED] [NOT RH]`
- **Target:**
  `formal/GaloisForLFunctions/RHTower/XiHorizontalCollisionChargeEndpoint.lean`,
  `formal/GaloisForLFunctions/RHTower/XiHorizontalCollisionTwoPrimeCesaroCarrier.lean`,
  `formal/GaloisForLFunctions/RHTower/XiHorizontalCollisionPrimeCayleyInformationLoss.lean`

## Conjecture loop

### C1 — a zero-density estimate for horizontal charge proves RH

`[FALSIFIED]` Let `N(T)` be total Xi divisor multiplicity, `N_0(T)` its critical-line part, and
`O(T)` horizontal collision charge.  Even if `O(T)=o(N(T))`, the inequality

```text
N_0(T) >= N(T) - O(T)
```

proves only `N_0(T)/N(T) -> 1`.  A fixed reflected off-line pair contributes a persistent even
charge while still satisfying `O(T)=o(N(T))`.  Monotonicity and integrality do not remove that
finite defect.

### C2 — quantization lowers the required source estimate to a strict two-unit bound

`[PAPER-PROVED] [LEAN-PROVED]` For the finite positive-height strip divisor `S_T`, put

```text
m_rho = ord_rho(Xi),
H_rho = sum_{z in S_T, Im z = Im rho} m_z,
O(T)  = sum_{rho in S_T} m_rho (H_rho - m_rho).
```

Equivalently, after grouping by ordinates,

```text
O(T) = sum_gamma H_gamma^2 - sum_{rho in S_T} m_rho^2.
```

Every off-line point is accompanied by the distinct point `1-conj(rho)` at the same ordinate and
with the same positive order.  Hence its summand is at least `m_rho`, and

```text
N(T) - N_0(T) <= O(T).
```

The existing strip identity gives

```text
N(T) - N_0(T) = 2 sum_{Re rho > 1/2} m_rho.
```

Thus any off-line zero forces `2 <= O(T)` for every later window.  Conversely RH makes every
height fibre contain its unique critical-line point, so `H_rho=m_rho` and `O(T)=0`.  Therefore

```text
RH <-> forall T, O(T)=0
   <-> forall T, O(T)<2
   <-> forall n : Nat, O(n)<2
   <- O(T)<2 on any cofinal family
   <- eventually O(T)<2.
```

The last equivalence is the useful source endpoint: no limiting argument and no simplicity
assumption are needed.

### C3 — positive charge automatically amplifies to positive density

`[FAILED AS A CORPUS HANDOFF; OPEN AS A NEW SOURCE THEOREM]` The alternative route would be a
literal Xi-divisor replication
law

```text
O(T0)>0 -> exists c>0, eventually c*N(T) <= O(T).
```

No current corpus theorem supplies it.  Prime-semigroup, Wold, Gamma-six, and moment-neutral
amplifiers replicate source carriers or index blocks, not new Xi divisor points.  Treating those
copies as zeros would be a coefficient-faithfulness error.  Standard zero-density bounds also do
not convert one exceptional zero into positive density.

### C4 — finite prime-phase recurrence plus zero transfer supplies C3

`[FALSIFIED]` The corpus's locally uniform zero-transfer theorem is exact, but its recurrent input
is only proved for `depthThreeDirichletFactor`.  Finite Euler/Bohr phase recurrence controls a
truncated Dirichlet factor; it does not give locally uniform recurrence of the full zeta germ on a
circle surrounding an off-line zero.  Voronin universality cannot fill this gap because its target
must be nonvanishing on the compact set.  The full positive-lower-density self-approximation

```text
sup_(s in K) |zeta(s+i tau)-zeta(s)| < epsilon
```

is Bagchi strong recurrence, already equivalent to RH.  Thus importing full self-recurrence would
be circular; deriving a strictly charge-specific recurrence from a literal prime/Gamma remainder
law remains a legitimate but currently unproved producer.  Sources: Bagchi,
[Acta Math. Hungar. 50 (1987), 227--240](https://real-j.mtak.hu/7474/1/MTA_ActaMathHung_50.pdf),
and the effective Voronin theorem of
[Lamzouri--Lester--Radziwill](https://arxiv.org/abs/1611.10325).

### C5 — two fixed prime characters resolve every horizontal fibre without losing coefficients

`[PAPER-PROVED] [LEAN-PROVED] [AXIOM-AUDITED]` A single prime phase can alias two ordinates. The
pair of prime clocks at `2` and `3` is globally injective because `log 2 / log 3` is irrational.
For each strip zero `rho`, retain local order, both line-reflection orientations, both prime
labels, and independent prime-power depths:

```text
P_T(a,b) = sum_rho m_rho
  [chi_2(rho) chi_2(1-conj rho)]^a
  [chi_3(rho) chi_3(1-conj rho)]^b.
```

Reflected character product is exactly unit phase `exp(i (2 Im rho) log p)`. Grouping pencil by
ordinates gives coefficient `H_gamma`, and two-dimensional Cesaro orthogonality proves

```text
(1/N^2) sum_(a,b<N) |P_T(a,b)|^2  -->  sum_gamma H_gamma^2.
```

After subtracting local square census, limit is exactly `O(T)`. Hence

```text
RH <-> for every T, centered source excess --> 0,
```

and any eventual absolute upper bound `C_T<2` for that excess proves RH. This is first
coefficient-faithful prime-labelled carrier for complete horizontal collision charge. It remains
divisor-indexed: remaining producer must estimate its energy from a prime--Gamma law before
specializing to Xi divisor. Triangle/Cauchy estimates give total-mass-scale bounds and cannot
approach absolute two-unit threshold.

### C6 — collision charge is exactly source-horizontal information lost under reflection quotient

`[PAPER-PROVED] [LEAN-PROVED] [AXIOM-AUDITED]` Add to C5's same prime-labelled pencil the unit
Cayley phase of the actual BV/Wold source-horizontal rate `2 Re(rho)-1`. At Cayley depth zero this
is definitionally C5's reflected `(2,3)` carrier. Inside one fixed ordinate fibre, Cayley
injectivity separates every distinct Xi point. Therefore the iterated mean-square laws are

```text
prime-depth average at fixed Cayley depth c
  --> sum_gamma |sum_(Im rho=gamma) m_rho Cayley(rate_rho)^c|^2,

Cayley-depth average of that resolved energy
  --> sum_rho m_rho^2.
```

Depth zero is `sum_gamma H_gamma^2`. Hence information loss between quotient depth zero and full
source-horizontal resolution converges exactly to

```text
sum_gamma H_gamma^2 - sum_rho m_rho^2 = O(T).
```

This is coefficient-faithful and non-equivariant before scalarization: prime labels, local
multiplicity, both reflection orientations, and signed horizontal rate remain on one carrier.
It proves RH equivalent to zero asymptotic information loss, and any eventual absolute loss bound
below two proves RH. It does not yet prove that bound; it removes ambiguity about which two
transports a producer must compare.

### C7 — Ward--Green normalization cancels Cayley spectral collapse

`[OWN CONJECTURE LEAN-PROVED] [AXIOM-AUDITED]` Put `x=2 Re(rho)-1`. Exact Cayley algebra gives

```text
|Cayley(x)-Cayley(-x)|^2 = 16 x^2/(1+x^2)^2.
```

The Ward transverse Green weight is `4/x^2` off line and zero on line. Their product is therefore

```text
64/(1+x^2)^2 > 16                         (|x|<1),
0                                         (x=0).
```

Thus the singular Green normalization does not merely rescale an old detector: it removes the
entire submicroscopic collapse while preserving the exact critical-line kernel. Summed with local
multiplicity squares, the resulting finite-window energy dominates `16 O_reflection(T)`. Any
uniform source bound below `32` proves RH. Remaining issue at C7 alone was source realization:
ordinary fixed-feature diagonal trace also charges critical-line zeros.

### C8 — exterior prime/Cayley carrier removes the critical-line tax

`[OWN CONJECTURE LEAN-PROVED] [AXIOM-AUDITED]` Combine C7 with the adjacent Hedenmalm exterior
determinant and retain both fixed orientations `t+1` and `t-1`, where `t` is nearest integer to
centered height. Divide each determinant by the transverse spectral coordinate before taking its
norm square. Numerator and coordinate both reverse under critical-line reflection, so the two
orientations do not annihilate; on-line coefficients remain exactly zero. Existing adjacent-
feature algebra yields the pointwise quantum

```text
4(96/145)^2 <= |D_+(rho)/y_rho|^2 + |D_-(rho)/y_rho|^2
```

for every off-line divisor point, uniformly as `y_rho -> 0`. Both `D_+` and `D_-` are proved
literally equal to exterior squares of critical-feature Cauchy tests, whose polarizations have the
explicit four-term absolute-Euler prime--Gamma source formula.

For every finite divisor packet `S`, the new literal carrier retains analytic multiplicity,
prime labels `2,3`, both reflected Burnol-character factors, both adjacent exterior orientations,
and Cayley depth. Exact iterated Cesaro laws prove

```text
two-prime depth average at fixed c  --> exact ordinate-fibre energy,
Cayley-depth average                --> sum_(rho in S) m_rho^2 E_ext(rho).
```

Therefore packet energy dominates `4(96/145)^2` times the complete off-line multiplicity-square
census. RH is equivalent to zero dephased energy for every finite packet, and any eventual packet
bound strictly below `4(96/145)^2` proves RH. This is the first current carrier that simultaneously
removes the critical-line tax, defeats submicroscopic collapse, retains multiplicity squares,
and has literal prime labels before scalarization.

Open producer is now narrower: derive the strict sub-quantum bound from the four-leg prime--Gamma
source expression itself. The determinant of the global source matrix is insufficient because
Cauchy--Binet adds cross-zero minors; the required estimate must apply to the dephased local
exterior carrier proved here.

## Paper proof details

For `rho in S_T`, the exact-height finset contains `rho`; positivity of analytic order gives
`m_rho>0`.  Its critical-line reflection belongs to the same exact-height finset.  If `rho` is
off-line the two points are distinct, reflection preserves order, and therefore
`2*m_rho <= H_rho`.  It follows that `m_rho <= m_rho*(H_rho-m_rho)`.  Summing over off-line points
proves the deficit domination.

For the quadratic identity, `m_rho<=H_rho` gives

```text
m_rho(H_rho-m_rho)+m_rho^2=m_rho H_rho.
```

Summing and grouping the last expression by `gamma=Im rho` yields `sum_gamma H_gamma^2`.

If a right-half box contains a zero, its reflected pair contributes at least two to the off-line
mass, hence to `O(T)`.  This contradicts `O(T)<2`.  Natural cutoffs are cofinal in every finite
height box.  Under RH, the existing horizontal-fibre theorem gives `H_rho=m_rho` pointwise, so all
summands vanish.

## Exact open producer

Prove from a literal prime/Gamma/source identity, without assuming divisor reality, either

```text
O(T) < 2 on one cofinal family of cutoffs
```

or, equivalently for the fixed-prime carrier, an eventual bound

```text
centered_two_prime_energy(T,N) <= C_T < 2
```

for every cutoff in a cofinal family; alternatively prove C3 replication dichotomy by a
charge-specific source recurrence strictly weaker in premise than zeta self-approximation. An
estimate `O(T)=o(N(T))` is not enough.

## Lean realization

`XiHorizontalCollisionChargeEndpoint.lean` proves unconditionally:

- ordered-pair normal form for `O(T)`;
- `O(T)=sum H_gamma^2-sum m_rho^2`;
- evenness and monotonicity of `O(T)`;
- exact divisor splitting and `N(T)-O(T)<=N_0(T)`;
- off-line mass `<=O(T)` and off-line mass `=2` times right-half mass;
- `RH <-> forall T, O(T)<2 <-> forall T, O(T)=0`;
- natural, arbitrary cofinal, and eventual strict-two endpoints.

`XiHorizontalCollisionTwoPrimeCesaroCarrier.lean` proves unconditionally:

- generic finite two-phase Cesaro mean-square orthogonality;
- exact Burnol-character/reflected-phase identity for every positive prime label;
- global injectivity of fixed `(2,3)` phase pair on ordinates;
- exact coefficient-preserving grouping of source pencil by horizontal fibres;
- convergence of centered source energy to `O(T)`;
- RH equivalence with zero source-excess limits and with eventual absolute bounds below two.

`XiHorizontalCollisionPrimeCayleyInformationLoss.lean` proves unconditionally:

- source-rate Cayley phase has unit norm and separates same-ordinate Xi points;
- Cayley depth zero is exactly the earlier two-prime source pencil;
- two prime clocks land at fixed-depth horizontal-fibre energy;
- Cayley-depth Cesaro averaging lands at local multiplicity-square energy;
- quotient-minus-resolved information loss converges exactly to `O(T)`;
- zero-loss and eventual strict-two loss criteria are equivalent to RH.

`XiHorizontalCollisionWardGreenCayleyQuantum.lean` proves unconditionally:

- exact reflected-Cayley gap and its Ward--Green cancellation law;
- strict uniform quantum above `16` for each off-line copy and zero on line;
- finite-window energy domination of `16` times reflection self-intersection charge;
- absolute energy threshold `32` implies RH.

`XiHorizontalCollisionWardGreenExteriorSourceCarrier.lean` proves unconditionally:

- both normalized adjacent determinants are literal critical-feature Cauchy exterior channels;
- local two-orientation energy is exactly four times transverse exterior energy;
- pointwise uniform off-line quantum `4(96/145)^2` and exact on-line zero;
- finite packet domination of the multiplicity-square off-line census;
- exact literal `(2,3)` prime-source dephasing and exact Cayley resolution;
- strict sub-quantum source bound implies RH;
- RH iff every finite dephased packet energy tends to zero.

Direct `lake env lean`, exact leaf builds, and `#print axioms` audits pass. Audited
theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] C1 falsified with explicit persistent-even-defect model
- [x] C2 paper proof dependency-closed
- [x] C2 Lean formalization, exact leaf build, and axiom audit
- [x] C3 existing-corpus replication handoff falsified
- [x] C4 finite-phase/self-recurrence shortcut classified
- [x] C5 coefficient-faithful two-prime divisor-source carrier and exact energy limit
- [x] C6 same-carrier source-Cayley resolution and exact information-loss identity
- [x] C7 Ward--Green cancellation of submicroscopic Cayley collapse
- [x] C8 dephased exterior prime/Cayley carrier with zero critical-line tax
- [ ] four-leg prime--Gamma estimate forcing dephased packet energy below `4(96/145)^2`
