# Receiving charge in the complete form at critical overlap

- **ID:** Q6-CHARGE
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-0311/fable.md`, §7
- **Statement:** Evaluate complete Weil energy and its polarized conductor-complement pairing on harmonic-neutral coherent prime-charge families and their coprime conductor fibres at `c=2K(log N)^(1/8)`.

“Checked” below means an individual Lean check, standard-only transitive axioms,
and umbrella integration. Final plain audits remain pending for modules built
as dependencies. “Source” means written Lean awaiting verification.

## Normalizations

Put `B_Q=Σ_(p≤Q) log p/p`, `S_Q=Σ_(p≤Q)1/p`, `s=t/B_Q`, and
`F_Q(n)=s Σ_(p≤Q)(1_(p|n)−1/p)`. Subtract its exact harmonic mean on `[1,N]`
to obtain `F_(Q,N)`. Raw input is `x(n)=F_(Q,N)(n)/√n`; physical input is
`v=x/√log N`. Generator charge is exactly `t`; adjunction mass is `t²/B_Q`.
Raw and physical complete energies differ by `log N`.

The classification must retain Gamma, affine, shell, pole, overlap and finite
horizon terms. Small input alone does not determine a complete-form pairing.

## Checked polynomial-horizon energy

For finite prime support `P` and `F_b=Σ_P b_p(1_(p|n)−1/p)`,

`J_N(F_b,F_d)=Σ_P b_p d_p (log p/p) H_(⌊N/p⌋)`.

A Mangoldt edge changes one prime incidence; reindexing by that prime cancels
the cofactor logarithms. Constant subtraction preserves every jump. For the
coherent family,

`J_N(F_(Q,N))−t² log N/B_Q=−t²/2+(t/B_Q)²R_(Q,N)`,

`R_(Q,N)=Σ_(p≤Q)(log p/p)(H_(⌊N/p⌋)−log N+B_p)−½Σ_(p≤Q)(log p/p)²`,

with `|R_(Q,N)|≤C B_Q` uniformly for `N≥Q`. Divisibility counting bounds the
ordinary and harmonic incidence squares by `N V_Q` and `H_N V_Q`, where
`V_Q=(t/B_Q)²(4S_Q²+2S_Q)`. Here `B_Q~log Q` and `S_Q` grows more slowly
than every positive power of `log Q`.

For a nonnegative `C²` atom supported on `[0,1]` with positive square mass,
the exact neutral complete decomposition gives

`|Ecomplete(packet F)−J_N(F)|≤A c² H(F)+B c³(log N+1)O(F)/N`,

where `H(F)=ΣF²/n`, `O(F)=ΣF²`. Pole-error is exactly zero; all other
complete-form corrections are included in this bound.

Thus, for `Q=X^a`, `N=X^d`, `0<a≤d`, and each fixed `K>0`:

- raw complete energy tends to `t²(d/a−1/2)`;
- physical complete energy, raw input square, physical input square and adjunction mass tend to zero;
- generator charge remains exactly `t`;
- affine successor energy and shell diagonal separately tend to zero in raw coordinates.

The positive raw limit comes from prime dilation. Its affine and shell costs
are `O(c(log N+1)V_Q)`, with affine energy at most four shell diagonals.

Main checked modules: `PrimeIncidenceDilationEnergy`, `PrimeIncidenceDilationPairing`,
`FiniteHorizonPrimeCharge`, `PrimeChargeBoundaryCorrection`, `PrimeChargeMoments`,
`CompleteFormMoments`, `PrimeChargeScaleLimits`, `PrimeChargePolynomialScales`,
`PrimeChargeCompleteEnergy`, `PrimeChargeAffinePayment`.

## Checked signed complementary receiver

The exact dilation operator is
`D_N=diag(log n+ψ₁(⌊N/n⌋))−fullPrimeMatrix N`. Its conductor-packet row is
the adjunction packet plus `completedPrimeDilationTail`. The conductor
complement kills the entire adjunction packet; harmonic centering preserves
the tail.

For coherent coefficients,

`|T_(Q,N)(n)−(t/B_Q)max(log Q+log n−log N,0)|≤(|t|/B_Q)(C+ω_Q(n))`.

The quotient-floor loss is at most `log 2`; the low-prime tower remainder
and high-prime excess over prime Mertens mass are uniformly bounded. The
physical ramp error satisfies

`‖T/√(n log N)−ramp/√(n log N)‖≤2|t|(C+1+S_Q)/B_Q`,

uniformly for `log N≥1`. Polarization of the complete moment bound gives
normalized mixed-error square `O(c⁶(log N+1)V_Q)`. Hence the literal complete
pairing has this projected ramp profile against every unit complementary
receiver at each fixed polynomial cutoff/horizon ratio.

Concrete witness: `Q=X²`, `N=X⁴⁰`,
`g=1_(X³⁹,X⁴⁰]−κ1_(X³⁸,X³⁹]`, with `κ` the ratio of the two harmonic
window masses. Put `z=packet(g)/√log N` and `r=z−P_(conductorSubspace Q N)z`.
Then `Σg/n=0` exactly, and

`‖Pz‖²≤128Q³(1+|κ|)²/((X³⁸+1)²(log N)²)`.

Endpoint cancellation of the harmonic conductor finite parts yields

`κ→1`, `‖r‖²→1/20`, `X‖Pz‖→0`, `⟨Wφ(c)v,r⟩→t/80`.

On the two windows the ramp is linear; neutrality removes its constant part.
Its tower-error pairing is `O((|t|/B_Q)(1+|κ|)(H_N/log N)(C+S_Q))`.

The receiver's own complete energy satisfies `Ecomplete(r)/log N→1/20`.
Bounded variation controls its neutral prime form, and the complete correction
is `o((log N)²)` before physical normalization. Consequently

`Ecomplete(v)Ecomplete(r)−⟨Wv,r⟩²→6239t²/6400`.

For `t≠0`, the complete form is eventually positive on this entire
source–receiver plane. A nonzero mixed limit therefore does **not** exclude
all energy-based Schur arguments. No exact projection-variance formula for
the whole ramp is established or used.

Main checked modules: `PrimeChargeDilationRow`, `PrimeTowerTailMass`,
`PrimeChargeMixedLimits`, `PrimeChargeTailPairing`, `PrimeChargeComplementReceiver`,
`PrimeChargeSignedReceiver`, `PrimeChargeRampProfile`, `PrimeChargeComplementProfile`,
`PrimeChargeWindowEnergy`, `PrimeChargeReceiverEnergy`, `PrimeChargeSchur`.

## Coprime receiving fibres

Exclude primes dividing a fixed positive mode `m`. Multiplication by `e_m`
precedes global harmonic centering. Reversing that order changes the base-mode
charge. The corpus's `exists_fibre_charge_vanishing_energy` gives the exact
receiving coordinate `t e_m` with small adjunction and physical input.

For retained primes coprime to `m`, the exact product identity is

`J_N(e_mF_b)=Σ_P b_p²(log p/p)Σ_(n≤N/p)e_m(n)²/n`
`+Σ_(kn≤N)Λ(k)/(kn) F_b(n)²(e_m(kn)−e_m(n))²`.

The harmonic Gram discrepancy is at most `2m²`; every base-mode upward square
row is at most `C_m=m(log m+tameDifferent m)`. Thus

`|J_N(e_mF_b)−J_N(F_b)|≤2m²Σ_P b_p²log p/p+C_m H(F_b)`.

The raw and physical complete-energy limits are respectively `t²(d/a−1/2)`
and zero. All complete mixed corrections vanish against unit neutral receivers
at fixed polynomial ratios. These facts are checked in
`FixedConductorDilationRows`, `CoprimePrimeChargeDilation`, `CoprimePrimeChargeMoments`,
`CoprimePrimeChargeScales`, `CoprimePrimeChargeDilationScales`,
`CoprimePrimeChargeCompleteEnergy`, `CoprimePrimeChargeMixedLimits`.

The checked tail identity is `T(e_mF)=e_mT(F)+F T(e_m)`, unchanged by centering.
The fixed-mode tail has square at most
`2 sourceBound(m)²+2 primeActivityMass(m) C_m`
(`CoprimePrimeChargeTail`). Its multiplication by the small prime input is the
vanishing remainder. Removing primes dividing `m` changes the scalar tail by
at most `m|t/B_(m,Q)|`.

`CoprimePrimeChargeWindows` checks endpoint cancellation, mode-square window
comparison and projection bound
`128m²Q³(1+|κ|)²/((A+1)²(log N)²)`.
`CoprimePrimeChargeLogWindows` checks the logarithmic mode-product window
bound. `CoprimePrimeChargeWindowScales` checks receiver square `1/20`,
vanishing projection mass, and exact conductor-complement membership,
with standard-only transitive axioms. The remaining terminal chain is
source awaiting checks: `CoprimePrimeChargeTailMass`, `CoprimePrimeChargeTailNorms`,
`CoprimePrimeChargeTailPairing`, `CoprimePrimeChargeTailLimits`,
`CoprimePrimeChargeTailVectors`, `CoprimePrimeChargeSignedReceiver`.
It targets `‖r_l‖²→1/20` and `⟨Wv_m,r_l⟩→δ_ml t/80`, with the receiver
projected off any fixed common cutoff `R X²` containing the source fibre.

For two coprime receiving modes, the mixed leading energy is
`δ_ml J_N(F_b,F_d)`, with error at most

`2mlΣ_P |b_p d_p|log p/p+(C_m H(F_b)+C_l H(F_d))/2`.

`CoprimePrimeChargePairing` checks this bound with standard-only transitive axioms;
integrated.

Common exclusion by a positive multiple `M` gives exact simultaneous coordinates:
for `m,l|M`, `⟨G(e_mF_b),e_l⟩period=δ_mlΣ_p b_p log p/p`.
`PrimeFibreCoordinates` and `CommonPrimeFibrePackets` are checked, including
global harmonic neutrality and the entire simultaneous coordinate vector.
For a finite prescribed vector `(t_m)`,
the common packet has prospective raw limit `Σ_m t_m²(d/a−1/2)`, vanishing
physical energy, and adjunction at most
`|S|Σ_m(2(log m+tameDifferent m)+1)t_m²/B_(M,Q)`.
The remaining source modules are `CommonPrimeFibreMoments`,
`CommonPrimeFibreAdjunction`, `CommonPrimeFibreDilation`, `CommonPrimeFibreCompleteEnergy`.

Common exclusion differs from each original fibre by the fixed prime set
`{p|M:p∤m}` once `Q≥M`. Its exact profile is `(B_m/B_M)` times the original
fibre minus `(t/B_M)` times that fixed incidence packet. Centering is linear;
the correction's full critical output tends to zero. This gives the proposed
simultaneous signed law `⟨Wv,r_l⟩→t_l/80`, zero for absent modes.
`CommonPrimeFibreRestriction`, `CommonPrimeFibreCentering` and
`CommonPrimeFibreSignedReceiver` contain the dependency-closed paper assembly
and Lean source; checks pending. `SimultaneousCompleteReceivingLaw` specializes
to the tilted spline and common exclusion `R!` for arbitrary charges in modes
`1,…,R`; its exact-coordinate, energy and signed-limit assembly is unchecked.

## Cutoff dependence and complete cancellation

At `Q=N`, finite Ramanujan inversion makes the conductor span the whole horizon;
its complement is zero. The physical energy still tends to zero, with raw
limit `t²/2`. `PrimeChargeFullHorizon` contains the complement statement;
check pending. The terminal witness above has raw limit `39t²/2` and nonzero
complementary pairing. Thus charge and small physical energy alone do not
specify a complementary response.

Infinite overlap resolves every fixed conductor: completed conductor energy
`E_m(c)` is nonnegative and tends to zero. For the tilted spline it is
`O_m(c⁻⁷)` once `c≥m`. At critical overlap each fixed conductor's full output
norm tends to zero. Finite fixed-cutoff packets inherit this cancellation,
including horizon-dependent bounded coefficients and exact harmonic centering.
The general smooth-atom residual bound also tends to zero at critical overlap.

Checked: `FixedConductorCriticalCancellation`, `FixedPacketCriticalCancellation`,
`FixedConductorCompleteCancellation`, `PrimeChargeCompleteCancellation`,
`CoprimePrimeChargeCancellation`. The latter chooses a large cutoff first,
then a horizon threshold: exact charge coexists with adjunction, physical
input square, full output norm and absolute physical energy below any prescribed
tolerance on every subsequent horizon.

For fixed coefficients and cutoff, the sharper tilted-spline law is

`c_N⁷ Ecomplete(v_centered)→Σ_(m≠1) J(m)a_m²`,
`Ecomplete(x_centered)/c_N→Σ_(m≠1)J(m)a_m²/R`,

where `c_N⁸/log N→R>0` and `J(m)>0`. Centering deletes conductor one and its
critical polar genus. Every nonzero nonpolar fixed packet has eventually
positive, divergent raw energy (`FixedChargeJordanLimit`, checked).

## Positive charge-cost classification

For finite nonempty prime support `P⊆[1,N]`, define
`C_(P,N)=Σ_P(log p/p)/H_(⌊N/p⌋)`. At exact charge `q=Σ_P b_p log p/p`,

`J_N(F_b)=q²/C_(P,N)+J_N(F_(b−b*))`,
`b*_p=q/(C_(P,N)H_(⌊N/p⌋))`.

The minimizer is unique on `P`; harmonic centering preserves both charge and
minimum. This is checked in `PrimeIncidenceReceivingCapacity` and `PrimeChargeCapacity`.

Finite coherent prefixes at `Q_i=X^a_i`, horizon `X^d`, have complete raw limit
`Σ_ij t_i t_j K_d(a_i,a_j)`, where
`K_d(a,b)=d/max(a,b)−min(a,b)/(2max(a,b))`.
For integer `0<a_i≤d`, this is exactly

`Σ_(k<d)(d−k−1/2)f_k²`, `f_k=Σ_(i:k<a_i)t_i/a_i`,

and total charge is `Σ_(k<d)f_k`. Every weight is positive; zero energy means
all `f_k=0`. Hence nonzero charge costs positive energy on each fixed scale grid.
`PrimeChargePrefixPairing`, `PrimeChargePrefixComplete`, `PrimeChargeCombinations`
and `PrimeChargeScaleForm` are checked.

An exactly charged difference of prefixes with limiting band `X^a<p≤X^b`
has energy `t²[d−(a+b)/2]/(b−a)`. Disjoint limiting bands pair diagonally.
Assigning charge `t/M` to `M` terminal dyadic bands gives raw limit `3t²/(2M)`.
Finite inputs are exactly charged prefix differences; band support is limiting.
`PrimeChargeBands`, `PrimeChargeBandDistributions`, `PrimeChargeDyadicBands` are checked.

Choosing the bands first and the horizon second gives arbitrarily small raw
input square, adjunction and absolute raw complete energy at any fixed charge,
on arbitrarily large horizons. No fixed linear combination of those costs
bounds charge (`PrimeChargeRawObstruction`, checked).
`PrimeChargeConsequences` contains the concrete tilted-spline specialization
and the physical-cost obstruction; check pending.

The continuum form suggested by the finite grids is
`∫₀¹(1−u)f(u)²du=∫₀¹uT′(u)²du`, `T(u)=∫_(1−u)^1 f(v)dv`.
Its continuum and finite-fibre extensions are unformalized.

## Uniform horizon frontier

The current complete mixed comparison covers fixed polynomial ratios.
No all-horizon mixed classification is established.

For self-energy, exact quadratic transposition gives
`overlap−nonratio=−overlap+2(overlap−downward)`.
The following ingredients are checked:

- `PrimeChargeNearMean` and `PrimeChargeNearGram`: the near form keeps the exact nonpolar divisor mean `Σa_m²σ₁(m)/φ(m)` and the polar coefficient; boundary costs are `c⁵/N+c³Q⁴/(N log N)` times input square.
- `PrimeChargeOverlap`: overlap is its logarithmic near Gram plus a remainder bounded by `C c²√((1+log c)/log N)‖v‖²`.
- `PrimeChargeQuadraticChannels`: exact transposition, center and separated-cross bounds are combined without dropping any scalar term.
- `PrimeChargePhysicalChannels`: the exact prime identity and floor/Mertens scalar correction are transferred to physical coordinates.
- `PrimeChargeDivisorMean`: the coherent nonpolar divisor mean is exactly `s²Σ_(p≤Q)(p+1)/p²≤(3/2)s²S_Q`.
- `PrimeChargePoleCoefficient`: `|H_N a_1−t|≤8|t|Q/(NB_Q)≤8|t|/B_Q`.
- `PrimeChargeUniformCoefficients`: `|a_1|≤(|t|+8|t|/B_Q)/log N`, `Σ_(m≠1)(1+log m)a_m²≤s²(S_Q+B_Q)`, and `‖v‖²≤52s²S_Q` uniformly for `N≥Q≥2`.
- `PrimeChargeSmallPacketEnergy`: the complete residual costs `K[(c/log N)(Σ|a_m|m²)²+(c⁵log N/N)(Σ|a_m|m⁵)²]` plus the polarized harmonic Gram error; the nonpolar completed diagonal is at most `(|selfφ(1)|+3)s²(S_Q+B_Q)`.

All completed energies are nonnegative and satisfy
`E_m(c)≤|selfφ(1)|+2log m+3` for `c≥1`.
Thus the remaining polar diagonal costs only `(|selfφ(1)|+3)a_1²`.
`PrimeChargeCompletedDiagonal` checks the full diagonal bound and
`Σa_m²≤a_pole_bound²+s²S_Q`, with standard-only transitive axioms.
`PrimeChargeUniformFiniteBounds` checks exact physical pole orthogonality and
the small-cutoff bound under the same frame and near-radius conditions,
with `D=|selfφ(1)|+3`, `P=(|t|+8|t|/B)/log N`:

`|Ephysical|≤D[P²+s²(S+B)]`
`+[K(Q⁵c/log N+Q¹¹c⁵log N/N)+9D(1+log Q)²/log N](P²+s²S)`.

`PrimeChargeIntermediateBounds` checks the coherent norm, divisor mean
and polar coefficient in every quadratic channel, the physical prime bound
`0≤J_N(F)/log N≤2t²/B_Q`, and the physical moment comparison, with standard-only
transitive axioms.
`PrimeChargeUniformGeometry` checks the uniform frame, radius and sampling
conditions with standard-only transitive axioms. `PrimeChargeUniformScales`
checks the independent cutoff/horizon decay laws, including the overlap-scaled
polar coefficient, with standard-only transitive axioms.
`PrimeChargeDenseCutoffEnergy` and `PrimeChargeSmallCutoffEnergy` check
the dense and smallest-cutoff limits with standard-only transitive axioms.
`PrimeChargeIntermediateEnergy` checks the remaining regime limit with
standard-only transitive axioms.
`PrimeChargeIntermediateDomination` checks the middle-range cost separation;
`PrimeChargeUniformHorizonEnergy` checks the independent cutoff/horizon
limit with standard-only transitive axioms: physical complete energy tends
to zero whenever both cutoff and horizon diverge.

The uniform physical-energy proof splits at `Q⁶⁴=N` and
`Q=(log N)^(1/32)`, with `L=log N`, `B=B_Q`, `S=S_Q`:

- `N≤Q⁶⁴`: checked moment comparison and prime-scale limits give decay.
- `Q≤L^(1/32)`: the complete conductor residual, nonnegative diagonal and Gram error give decay. Cauchy–Schwarz gives `(Σ|a_m|m^k)²≤Q^(2k+1)Σa_m²`.
- Intermediate range: `log L≤32log Q`; both scalar diagonal and divisor-mean overlap cost `O_t(S/B)`. Other quadratic channels retain negative powers of `L` or `N`.

The middle-range assembly separates the error as

`|Ephysical−J/L|≤R_N W_Q+S_N V_Q+A(cP)²`,

where `V_Q=(t/B_Q)²S_Q`, `W_Q=(1+log Q)V_Q`, `R_N` converges to a finite
constant, and `S_N→0`. Both cutoff masses and `cP` tend to zero by checked
scale limits. Finite domination, all three regime limits and their assembly are checked.
Quadratic transposition does not apply to arbitrary complementary receivers.
The reduced-jet, coherent pole-cancellation and sharp near-collar bounds in the
corpus do not yet supply the required uniform upward nonratio remainder here.
A proposed replacement splits rows at `exp(√log N)` and primes at a power of
`log N`: short rows require a prime-progression upper bound; long rows require
a weighted affine-incidence covariance bound, with exceptional primes dividing
`kh′−k′h`. Neither required bound has yet been established for the literal kernel.
Bounding those exceptional primes individually loses a factor `log N`.
A proposed improvement averages the prime multiplier first: a progression
upper bound could replace that loss by `Σ_(p>R)1/p²`, permitting
`R=(log N)^(5/16)`. Checked sieve ingredients give unit CRT remainders,
absolute truncated coefficient mass at most `Y⁶`, and prime-deleted
reciprocal divisor mass at least `(log Y)/8−7/8` for deleted prime `p≥8`
(`BezoutValuationIncidence/Sieve`). `PrimeProgressionFinite` checks
`π(X;p,a)≤Y+16(X/p)/log Y+Y⁶` when `log Y≥14`.
`ProgressionTruncationScales` and `PrimeProgressionUpper` check
`π(X;p,a)≤1026X/(p log X)` for all sufficiently large prime moduli and `X≥p²`.
`WeightedPrimeProgressions` checks
`Σ_(H≤k≤X, prime k, k≡a mod p)log k/k≤(1026/p)(1+log X−log H)` for `p²≤H≤X`,
with standard-only transitive axioms. `KernelVariation` checks
`|ρ(a/B)ρ(b/B)/B|+Var_[A,B](ρ(a/n)ρ(b/n)/n)≤(2M²+2MK)/A`
for a compact kernel bounded by `M` with Lipschitz constant `K`.
`ResidueCovariance` and `WeightedResidueCovariance` check the exact coprime
and equal-prime period means and their weighted inverse-endpoint error,
with standard-only transitive axioms. `LogarithmicKernelVariation` checks
scale-independent Jacobian/logarithm variation and initial-segment truncation.
`LiteralUpwardKernelVariation` identifies both actual logarithmic kernels
and checks variation at most `2K+4M`, retaining both horizon cutoffs,
with standard-only transitive axioms.
Exact normalization of the upward matrix, prime-progression averaging and
complete-row assembly remain open. The rows with multiplier below `Q²` occupy a terminal
harmonic width `O((log Q+log c)/log N)` and need a separate bound.

## Gates

- [x] Explicit families, critical overlap and literal receivers identified.
- [ ] Dependency-closed full paper classification.
- [ ] Full Lean classification and consequences; final plain checks and transitive axiom audit.
