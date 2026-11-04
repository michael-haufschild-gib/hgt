# Receiving charge in the complete form at critical overlap

- **ID:** Q6-CHARGE
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-0311/fable.md`, §7
- **Statement:** Evaluate the complete Weil energy and its polarized conductor-complement pairing on harmonic-neutral coherent prime-charge families and their coprime conductor fibres at `c=2K(log N)^(1/8)`.

## Normalizations

Let `B_Q=Σ_(p≤Q) log p/p`, `s=t/B_Q`, and
`F_Q(n)=s Σ_(p≤Q)(1_(p|n)−1/p)`. Subtract its exact harmonic mean on `[1,N]`
to obtain `F_(Q,N)`. Raw input is `x(n)=F_(Q,N)(n)/√n`; physical input is
`v=x/√log N`. The generator charge is exactly `t`; adjunction mass is `t²/B_Q`.
Raw and physical complete energies differ by the factor `log N`.

Required classification retains every Gamma, affine, shell, pole, overlap and
finite-horizon term. A small-input theorem alone does not answer it.

## Checked scalar energy

For a finite prime set `P` and `F_b=Σ_P b_p(1_(p|n)−1/p)`,

`J_N(F_b,F_d)=Σ_P b_p d_p (log p/p) H_(⌊N/p⌋)`.

A Mangoldt edge changes only one prime incidence. Reindexing its source and
target sums by multiples of that prime cancels the cofactor logarithms.
Constant subtraction preserves every jump; disjoint prime bands pair to zero.

With `w_p=log p/p`, triangular summation gives

`J_N(F_(Q,N))−(t²/B_Q)log N = −t²/2+(t/B_Q)²R_(Q,N)`,

where
`R_(Q,N)=Σ_(p≤Q) w_p(H_(⌊N/p⌋)−log N+B_p)−½Σ_(p≤Q)w_p²`.
The floor-harmonic and prime Mertens remainders imply `|R_(Q,N)|≤C B_Q`
uniformly for `N≥Q`. Thus the exact boundary tends to `−t²/2`.

Write `S_Q=Σ_(p≤Q)1/p`. Divisibility counting yields ordinary and harmonic
second moments of the centered prime-divisor count bounded by
`N(4S_Q²+2S_Q)` and `H_N(4S_Q²+2S_Q)`. Since `S_Q=O(log log Q)` and
`B_Q~log Q`, the coherent moments tend to zero at fixed polynomial scales.

For every nonnegative `C²` atom supported on `[0,1]` with positive square mass,
the exact complete decomposition gives, for harmonic-neutral `F`,

`|Ecomplete(packet F)−J_N(F)|≤A c² H(F)+B c³(log N+1)O(F)/N`,

where `H(F)=Σ F²/n` and `O(F)=Σ F²`. This retains all terms: pole-error is
exactly zero; the scalar diagonal, far-cross, centre and near-overlap terms
have the displayed moment control; shell degree bounds both affine energy
and the signed affine-minus-shell term.

Consequently, for `Q=X^a`, `N=X^d`, `0<a≤d`, at every fixed `K>0`,

- raw complete energy tends to `t²(d/a−1/2)`;
- physical complete energy, raw input square, physical input square and
  adjunction mass tend to zero;
- generator charge remains exactly `t`.

The shell diagonal and affine successor energy separately tend to zero even
in the raw normalization: shell costs `O(c(log N+1)(t/B_Q)²(4S_Q²+2S_Q))`,
and affine energy is at most four shell diagonals. The positive raw limit
comes from prime dilation, not affine payment or cancellation of large
affine and shell terms. `PrimeChargeAffinePayment` proves these separate
limits; checked with standard-only transitive axioms and integrated.

Checked Lean, standard-only transitive axioms, integrated:
`PrimeIncidenceDilationEnergy`, `PrimeIncidenceDilationPairing`,
`FiniteHorizonPrimeCharge`, `PrimeChargeBoundaryCorrection`, `PrimeChargeMoments`,
`NearOverlapMoments`, `CompleteFormMoments`, `PrimeChargeScaleLimits`,
`PrimeChargePolynomialScales`, `PrimeChargeCompleteEnergy`.

## Signed complementary receiver

The exact dilation operator is
`D_N=diag(log n+ψ₁(⌊N/n⌋))−fullPrimeMatrix N`.
On a conductor packet its row equals the adjunction-diagonal packet plus
`completedPrimeDilationTail`. Orthogonality to the conductor span removes the
entire adjunction packet. Harmonic centering leaves the tail unchanged.

For coherent coefficients, the completed tail satisfies

`|T_(Q,N)(n)−(t/B_Q) max(log Q+log n−log N,0)|`
`≤(|t|/B_Q)(C+ω_Q(n))`,

and `|T_(Q,N)(n)|≤(|t|/B_Q) primeActivityMass Q`.
The quotient-floor loss is at most `log 2`. Low-prime tower remainders sum to
`primeActivityMass Y−mertensSum Y`, uniformly bounded; high-prime activity
exceeds its prime Mertens mass by at most eight.

Polarization of the complete quadratic remainder gives, for unit neutral `G`,

`R(F,G)²≤(1+A c²+B c³(log N+1))`
`·[A c²H(F)+B c³(log N+1)O(F)/N]`.

For coherent `F`, its normalized square is
`O(c⁶(log N+1)(t/B_Q)²(4S_Q²+2S_Q))`, tending to zero at critical overlap
and fixed polynomial ratios. This compares the literal complete matrix with
its dilation row against every bounded neutral receiver.

Concrete witness: `Q=X²`, `N=X⁴⁰`. Set
`g=1_(X³⁹,X⁴⁰]−κ·1_(X³⁸,X³⁹]`, with `κ` the ratio of their harmonic masses.
Then `Σg/n=0` exactly. Put `z=packet(g)/√log N`, and
`r=z−P_(conductorSubspace Q N)z`.

The finite projection bound is checked:

`‖Pz‖²≤128 Q³(1+|κ|)²/((X³⁸+1)²(log N)²)`.

It follows from the lower conductor frame and the nonpolar window coordinate
bound `8m(1+|κ|)/(X³⁸+1)`; torsion finite parts cancel between endpoints.
The receiver norm, projection transport and full complete-pairing limits
are checked:

`‖r‖²→1/20`, `⟨T/√(n log N),r⟩→t/80`,
`⟨Wφ(c)v,r⟩→t/80`.

On the two windows the ramp is linear. Neutrality removes its constant part;
harmonic logarithmic moments give the signed limit. The tower-error pairing
is bounded by `( |t|/B_Q)(1+|κ|)(H_N/log N)(C+S_Q)→0`.
Projection changes the pairing by at most `3|t|‖Pz‖→0`.

Checked and integrated: `CompleteFormMixedMoments`, `DilationPacketOperator`,
`PrimeChargeDilationRow`, `PrimeTowerTailMass`, `PrimeChargeWindows`, `PrimeChargeWindowScales`,
`PrimeChargeTailPairing`.
`PrimeChargeMixedLimits` and `PrimeChargeComplementReceiver` also pass their
individual checks and transitive axiom audits and are integrated.
`PrimeChargeSignedReceiver` passes its check and standard-only transitive
axiom audit and is integrated.
No exact projection-variance formula for the
whole ramp is established or used.

The second harmonic incidence moment strengthens the ramp comparison to
`‖T/√(n log N)−ramp/√(n log N)‖≤2|t|(C+1+S_Q)/B_Q`.
This tends to zero uniformly over all horizons with `log N≥1`.
`PrimeChargeRampProfile` passes its check and standard-only transitive axiom
audit; integrated.
`PrimeChargeComplementProfile` transfers this profile to the literal complete
pairing against every unit complementary receiver at fixed polynomial ratios;
its individual check and standard-only transitive axiom audit pass; integrated.

## Coprime fibres

The checked corpus theorem `exists_fibre_charge_vanishing_energy` supplies
harmonic-neutral coefficients on `{1}∪{mp:p≤Q,p∤m}` with exact output coordinate
`t e_m` and vanishing adjunction, physical input and residual output.
`packetMean_fibre_retains` proves the exact coordinate by coprime period
factorization. Multiply the uncentered prime packet by `e_m` before removing
its global harmonic pole; the reverse order changes the base-mode charge.

For a weight invariant under multiplication by every retained prime,

`Σ_(kn≤N) Λ(k)/(kn) h(n) ΔF_b ΔF_d`
`=Σ_P b_p d_p(log p/p) Σ_(n≤N/p)h(n)/n`.

For a coprime mode `e_m`, prime jumps and base-mode jumps have disjoint support:

`J_N(e_m F_b)=Σ_P b_p²(log p/p)Σ_(n≤N/p)e_m(n)²/n`
`+Σ_(kn≤N)Λ(k)/(kn) F_b(n)²(e_m(kn)−e_m(n))²`.

The complete-period square-energy identity bounds every base-mode upward row
by `m(log m+tameDifferent m)`. The harmonic Gram discrepancy is at most
`2m²`. Hence

`|J_N(e_mF_b)−J_N(F_b)|≤2m²Σ_P b_p²log p/p`
`+m(log m+tameDifferent m)H(F_b)`.

Both errors vanish on coherent polynomial families. Multiplication by the
bounded fixed mode preserves the reciprocal-prime moment gain; harmonic
centering contracts harmonic square and costs at most four in ordinary square.

For two base modes coprime to the retained primes, the mixed leading term is
`δ_ml J_N(F_b,F_d)`. Its error is at most
`2ml Σ_P |b_p d_p|log p/p + (C_m H(F_b)+C_l H(F_d))/2`,
where `C_m=m(log m+tameDifferent m)`. The first term is the harmonic period-Gram
discrepancy; `2|xy|≤x²+y²` pays the mixed base-mode remainder.
`CoprimePrimeChargePairing` contains this bound; check pending.

Excluding primes dividing a common multiple `M` gives exact simultaneous
coordinates: for `m,l∣M`, `⟨G(e_m F_b),e_l⟩period=δ_ml Σ_p b_p log p/p`.
The nonconstant prime rows have zero mean by coprime period factorization.
`PrimeFibreCoordinates` proves this identity; individual plain check and
standard-only transitive axiom audit pass; integrated.

The weighted product rule also gives the exact receiving-tail decomposition
`T(e_mF)=e_m T(F)+F T(e_m)` for coprime prime incidence. The fixed-mode tail
has square at most
`2 sourceBound(m)²+2 primeActivityMass(m)·m(log m+tameDifferent m)`.
Harmonic centering leaves both sides unchanged. This separates the transported
prime charge from a remainder paid by the small prime input.

`CommonPrimeFibrePackets` synthesizes a finite prescribed receiving vector
using this common exclusion, followed by one global harmonic centering;
`CommonPrimeFibreMoments` preserves its reciprocal-prime moment gain.
Checks pending. The finite energy assembly uses the mixed period-Gram
diagonal and the scalar incidence limit with normalizer `B_(M,Q)`.
`CommonPrimeFibreDilation` contains the resulting limit
`J_N→(Σ_m t_m²)(d/a−1/2)` at `Q=X^a`, `N=X^d`; check pending.
`CommonPrimeFibreCompleteEnergy` contains its complete-form transfer and
vanishing physical energy; check pending.
`CommonPrimeFibreAdjunction` bounds the finite receiving vector's adjunction
by `|S|Σ_m(2(log m+tameDifferent m)+1)t_m²/B_(M,Q)`; check pending.

The weighted identity `WeightedPrimeIncidenceEnergy` and exact quadratic
and mixed product laws `PrimeIncidenceProductEnergy` pass individual checks
and standard-only transitive axiom audits; integrated.
`FixedConductorDilationRows` proves the uniform upward square-row bound;
checked with standard-only transitive axioms and integrated.
`CoprimePrimeChargeDilation` proves the weighted finite fibre energy and
its scalar discrepancy bound; checked with standard-only transitive axioms
and integrated.
`CoprimePrimeChargeMoments` proves the ordinary and harmonic moment bounds
before and after exact centering; checked with standard-only transitive axioms
and integrated.
`CoprimePrimeChargeScales` proves the common-normalizer comparison and
vanishing sublogarithmic moment costs; checked with standard-only transitive
axioms and integrated.
`CoprimePrimeChargeDilationScales` proves the exact raw fibre limit
`t²(d/a−1/2)` after harmonic centering; checked with standard-only transitive
axioms and integrated.
`CoprimePrimeChargeCompleteEnergy` transfers the raw limit to the literal
complete form and proves vanishing physical energy, input and adjunction;
checked with standard-only transitive axioms and integrated.
Written, checks pending:
`CoprimePrimeChargeWindows`, `CoprimePrimeChargeLogWindows`,
`CoprimePrimeChargeWindowScales`, `CoprimePrimeChargeTail`, `CoprimePrimeChargeTailMass`,
`CoprimePrimeChargeTailPairing`, `CoprimePrimeChargeTailLimits`, `CoprimePrimeChargeTailNorms`,
`CoprimePrimeChargeTailVectors`, `CoprimePrimeChargeSignedReceiver`,
`CoprimePrimeChargeMixedLimits`. These include the full raw limit
`t²(d/a−1/2)`, vanishing physical complete energy and adjunction, and the
fixed-mode terminal projection bound and the diagonal signed complement law
`⟨Wv_m,r_l⟩→δ_ml t/80`. Finite-fibre polarization remains to be assembled;
the fibre modules remain unchecked.

`CompleteFormMomentCosts` proves the common scalar/fibre mixed moment bounds,
checked with standard-only transitive axioms and integrated.

The terminal fibre contrast may be projected off the common cutoff `R X²`
for any fixed positive `R`; its predicted square limit remains `1/20`.
Deleting the primes dividing `m` changes every tail row by at most
`m|t/B_(m,Q)|`, since each omitted prime tower has mass at most one.
Increasing-weight Abel summation bounds the centered conductor-product ramp
pairing by `8ml(1+|κ|)log Q`; this isolates the scalar diagonal in each fibre.

## Cutoff dependence

The hypotheses of Q6 do not force a nontrivial conductor complement.
`exists_horizon_normalizedRamanujan_expansion` gives an exact expansion of
every horizon vector in conductors through `N`; for `N≥2` their normalized
span is the whole horizon. Thus the `Q=N` charge family has a zero complement,
whereas the proposed `Q=X²`, `N=X⁴⁰` witness has nonzero complementary pairing.
`PrimeChargeFullHorizon` contains the full-horizon complement consequence;
its check remains pending.
Both families have vanishing physical complete energy; their raw limits
are respectively `t²/2` and `39t²/2`.

## Receiver energy and the Schur implication

The nonzero mixed limit alone does not exclude energy arguments: the
receiver's own energy may grow. For the terminal contrast, the target is
`Ecomplete(r_X)/log N→1/20`. The corpus theorem
`abs_atomicWeilForm_profile_sub_le` bounds its neutral prime form by
`(log 8+5)H_N Var_N(g)²`; the contrast has `Var_N(g)≤2(1+|κ|)`.
The Mertens diagonal is `log N·H(g)+O(H(g))`. Thus
`J_N(g)=log N·H(g)+O(log N)`, while the complete remainder is
`O(c³ log N)=o((log N)²)`. `BoundedVariationDilationEnergy` passes its check
and standard-only transitive axiom audit and is integrated.
`PrimeChargeWindowEnergy` proves the complete correction and normalized
contrast limit, checked with standard-only transitive axioms and integrated.
`CompleteFormNormCosts` contains the neutral polynomial operator cost and
its energy-difference consequence, checked with standard-only axioms and
integrated. `PrimeChargeReceiverEnergy` proves `X‖Pz‖→0` and transports the
contrast limit to the exact complement. Its check and standard-only transitive
axiom audit pass; integrated.

Together with the mixed limit, the energy accounting gives the positive
Schur determinant limit
`Ecomplete(v_X)Ecomplete(r_X)−⟨Wv_X,r_X⟩²→6239t²/6400`.
`PrimeChargeSchur` contains this limit and eventual positivity on the whole
two-dimensional source–receiver span for `t≠0`; its individual check and
standard-only transitive axiom audit pass; integrated. No claim that all
energy-based Schur arguments fail follows from the charge obstruction.

## Positive classification and implications still to prove

For a finite nonempty prime set `P⊆[1,N]`, the exact dilation receiving
capacity is `C_(P,N)=Σ_P (log p/p)/H_(⌊N/p⌋)`. Completing squares gives
`J_N(F_b)=q²/C_(P,N)+J_N(F_(b−b*))`, where `q=Σ_P b_p log p/p`
and `b*_p=q/(C_(P,N)H_(⌊N/p⌋))`. The minimizer has charge `q` and energy
`q²/C_(P,N)` exactly. `PrimeIncidenceReceivingCapacity` proves this
finite classification, checked with standard-only transitive axioms and integrated.
Equality is characterized exactly by the minimizing coefficient vector on `P`.
`PrimeChargeCapacity` identifies this charge with `packetMean(GF)` and
preserves the exact minimum under harmonic pole removal. Its check and
standard-only transitive axiom audit pass; integrated.

Prefix polarization gives
`K(θ,η)=[min(θ,η)−min(θ,η)²/2]/(θη)`.
Exactly charged prefix differences with limiting band `X^a<p≤X^b`, horizon
`X^d`, have complete energy limit `t²[d−(a+b)/2]/(b−a)`. Disjoint limiting
bands pair diagonally. Assigning charge `t/M` to `M` dyadic terminal bands
gives energy limit `3t²/(2M)` with total charge `t`.
The proposed continuum extension is the prime-scale charge-distribution form
`∫₀¹(1−u)f(u)²du`, tensored with the period Gram of fixed conductor fibres.
Writing `T(u)=∫_(1−u)^1f(v)dv` gives `∫₀¹uT′(u)²du`; total charge is `T(1)`.
The continuum representation and finite-fibre assembly remain unformalized.
For integer exponents the proposed exact finite representation is
`E_limit=Σ_(k<d)(d−k−1/2)f_k²`,
`f_k=Σ_(i:k<a_i)t_i/a_i`, and total charge is `Σ_(k<d)f_k`.
Every weight is positive; the form vanishes exactly when every `f_k` vanishes.
Thus nonzero charge has positive energy on each fixed finite scale grid,
while the dyadic sequence has no uniform positive charge cost.
`PrimeChargeScaleForm` proves this representation and rigidity; individual plain
check and standard-only transitive axiom audit pass; integrated.
`PrimeChargePrefixPairing` proves the exact dilation prefix kernel, checked
with standard-only transitive axioms and integrated. `PrimeChargePrefixComplete`
proves its complete-form transfer, also checked with standard-only transitive
axioms and integrated.
`PrimeChargeCombinations` assembles arbitrary finite coherent prefixes in
one neutral packet, retaining total charge exactly and evaluating its full
energy by the symmetric kernel `d/max(a,b)−min(a,b)/(2max(a,b))`.
Its raw input norm and adjunction mass also tend to zero; checked with
standard-only transitive axioms and integrated.
The supporting `CompleteFormLinearAlgebra` passes its check and standard-only
transitive axiom audit and is integrated.
`PrimeChargeBands` specializes this kernel to an exactly charged difference
of prefixes, with energy limit `t²[d−(a+b)/2]/(b−a)`; checked with
standard-only transitive axioms and integrated.
`PrimeChargeBandDistributions` gives the diagonal complete-energy form on
arbitrary finite disjoint prime bands, exact total charge, harmonic neutrality
and vanishing raw input and adjunction; checked with standard-only transitive
axioms and integrated. The finite packets are charged prefix differences;
their band support is a limiting statement.
`PrimeChargeDyadicBands` specializes to `M` terminal dyadic bands and obtains
complete raw energy `3t²/(2M)` at exact total charge `t`; checked with
standard-only transitive axioms and integrated.
Choosing `M` first and then the polynomial scale gives arbitrarily small
raw complete energy, raw input square and adjunction at any prescribed
charge and arbitrarily large horizons. `PrimeChargeRawObstruction` contains
this existence theorem and the failure of every fixed linear charge bound
by these three raw costs; individual plain check and standard-only transitive
axiom audit pass; integrated.

`PrimeChargeConsequences.lean` contains the concrete tilted-spline specialization
and the failure of control by adjunction plus physical input and physical
complete energy; checks pending. This is only one implication, not closure of Q6.

The current complete-form comparison covers fixed polynomial cutoff/horizon
ratios. The corpus bound
`completedConductorEnergy_le_logarithmic_uniform≤|selfφ(1)|+2log m+3`
for `c≥1` does not yet give a uniform packet comparison for every `N≥Q`.
No all-horizon extension is claimed.

Infinite overlap also resolves each fixed conductor:
`CompletedShell.tendsto_completedConductorEnergy_atTop` gives `E_m(c)→0`.
Thus the all-horizon analysis must retain the completed conductor energies
when the prime cutoff lies below overlap; the polynomial dilation limit
alone does not describe that regime.

For the tilted spline, `ConductorOverlapDecay` gives `E_m(c)≤C_m/c⁷`
once `c≥m`. The checked critical low-packet residual budget bounds each
fixed column's squared residual by `(log N)^(1/4) E_m(c)`, which tends to
zero at critical overlap. Together with bounded normalized mode norms,
this gives `‖W(c_N)e_(m,N)‖→0`. `FixedConductorCriticalCancellation` passes
its individual check and standard-only transitive axiom audit; integrated. It supplies
a nontrivial cancellation regime even when the conductor complement is
nonzero; finite fixed-cutoff packets inherit it by linearity.
`FixedPacketCriticalCancellation` proves the finite-packet assembly, including
bounded horizon-dependent coefficients and exact harmonic centering; checked
with standard-only transitive axioms and integrated.
`PrimeChargeCompleteCancellation` contains the coherent charge specialization;
individual plain check and standard-only transitive axiom audit pass; integrated.
`CoprimePrimeChargeCancellation` proves the fixed-mode analogue; individual
plain check and standard-only transitive axiom audit pass; integrated.
The last theorem chooses a large cutoff first, then a larger horizon threshold:
exact charge `t` coexists with adjunction, physical input square, complete
output norm and absolute complete physical energy all below any prescribed
positive tolerance on every subsequent horizon.
For a base mode `m|M`, common prime exclusion differs from its own fibre
only by the fixed prime set `{p|M : p∤m}` once `Q≥M`.
The common profile equals `(B_m/B_M)` times the original coherent fibre,
minus `(t/B_M)` times this fixed finite incidence packet.
`CommonPrimeFibreRestriction` contains the exact identities; check pending.
Harmonic centering is linear, so the same finite correction holds for the
physical vectors (`CommonPrimeFibreCentering`). Its full critical output
tends to zero. Thus a simultaneous prescribed receiving vector has complete
pairing `t_l/80` with its mode-`l` terminal receiver in the common conductor
complement, and zero in every absent mode. The dependency-closed paper
argument and Lean source are in `CommonPrimeFibreSignedReceiver`; checks pending.
For fixed coefficients `a` and fixed cutoff, the sharper energy law is
`c_N⁷ Ecomplete(v_centered)→Σ_(m≠1) J(m)a_m²`, where `J(m)>0` is the
tilted-spline Jordan coefficient. Harmonic centering tends coefficientwise
to deletion of conductor one, removing the critical polar genus term.
`FixedChargeJordanLimit` contains this consequence of the corpus's exact
critical conductor Gram limit, the raw law `Ecomplete(x)/c_N→(Σ J(m)a_m²)/R`,
and eventual positivity and raw-energy divergence for every nonzero nonpolar
packet; individual plain check and standard-only transitive axiom audit pass;
integrated.
For a general admissible smooth atom, the corpus residual bound
`O_m(c⁵/log N+c¹⁰(log N/N)²+c³/√log N)` also tends to zero at critical overlap.
`FixedConductorCompleteCancellation` contains this atom-independent
fixed-conductor cancellation; individual check and standard-only transitive
axiom audit pass; integrated.

For quadratic energy the exact identity `overlap−nonratio =
−overlap+2(overlap−downward)` eliminates the upward channel
(`overlap_sub_nonRatio_inner_eq`). The divisor-mean near-Gram bound and
quadratic terminal cancellation are available for the intermediate cutoff
range. Their coherent-packet specialization, including the small polar
centering coefficient, is not yet assembled. This quadratic reduction
does not apply to arbitrary complementary mixed pairings.

The proposed uniform physical-energy proof splits at `Q⁶⁴=N` and
`Q=(log N)^(1/32)`. Write `L=log N`, `B=B_Q`, `S=S_Q`.
For `N≤Q⁶⁴`, the checked moment comparison gives a decaying cost
`O_t(L^(3/8)S²/B²)`. For `Q≤L^(1/32)`, the logarithm-free conductor
Gram bound gives errors `O_t(L^(−11/16)+L²/N+L^(−7/8)log L)`, while
the completed diagonal costs `O_t(1/B)`.
In the intervening range, `log L≤32log Q`; both the divisor-mean overlap
and scalar diagonal cost `O_t(S/B)`, and the quadratic
near-row, center and separated-cross terms retain negative powers of `L`.
`PrimeChargeSmallPacketEnergy` sums the logarithm-free conductor residual
with the exact moments `Σ|a_m|m²` and `Σ|a_m|m⁵`, then retains the polarized
harmonic Gram error. It also bounds the coherent nonpolar completed
diagonal by `(|selfφ(1)|+3)(t/B_Q)²(S_Q+B_Q)`, uniformly in overlap
and horizon. Its source is pending verification.
The completed energies are nonnegative, including conductor one, and
their logarithmic upper bound is uniform in `c≥1`. Consequently the
remaining polar diagonal costs at most `(|selfφ(1)|+3)a_1²`; no growing
overlap factor is needed in the small-cutoff diagonal.
`PrimeChargeCompletedDiagonal` contains this full diagonal bound and the
coefficient-square bound `Σa_m²≤a_pole_bound²+(t/B_Q)²S_Q`; check pending.
The relevant public center and cross bounds are
`abs_fullWeilCenterMatrix_self_inner_le_of_mem_conductorSubspace` and
`abs_separatedCrossErrorMatrix_inner_le_of_mem_conductorSubspace`.
The near-Gram and subkernel bounds pass; uniform assembly remains open.
`PrimeChargeOverlap` separates the overlap exactly into its logarithmic
near Gram and a remainder bounded by
`C c²√((1+log c)/L)‖u‖²`. This weaker remainder bound already decays at
critical overlap; it uses the public near-band square estimate directly.
Individual check and standard-only transitive axiom audit pass; integrated.
`PrimeChargeQuadraticChannels` combines this overlap bound with the exact
quadratic transposition, the center bound and the separated-cross bound;
individual check and standard-only transitive axiom audit pass; integrated.
The scalar diagonal remains literal.
`PrimeChargePhysicalChannels` transfers the exact prime identity and scalar
diagonal bound to physical coordinates; individual plain check and
standard-only transitive axiom audit pass; integrated.

Swapping conductor and lag sums isolates the exact polar near-mean term
`a_1² Σ_h nearWeightMass(h)`. Abel cancellation bounds the remainder by
`C(1+log c)Σ_(m≠1) a_m² σ_1(m)/φ(m)`, preserving each coefficient's
divisor mean. `PrimeChargeNearMean` proves this refinement; individual check
and standard-only transitive axiom audit pass; integrated.
`PrimeChargeNearGram` propagates it through linearization and the periodic
oscillation error: the near-Gram form costs
`C[(c⁵/N+c³Q⁴/(N log N))‖u‖² + (1+log c)(Σ_(m≠1)a_m²σ₁(m)/φ(m)+c a₁²)/log N]`.
Individual check and standard-only transitive axiom audit pass; integrated.
The polar coefficient remains explicit.
For the coherent coefficients the nonpolar divisor mean is exactly
`(t/B_Q)² Σ_(p≤Q)(p+1)/p²≤(3/2)(t/B_Q)² S_Q`.
`PrimeChargeDivisorMean` proves this identity and bound; individual check
and standard-only transitive axiom audit pass; integrated.
`PrimeChargeUniformCoefficients` bounds the exact polar coefficient by
`(|t|+8|t|/B_Q)/log N` and the nonpolar logarithmic coefficient square by
`(t/B_Q)²(S_Q+B_Q)`. The physical square has the uniform bound
`52(t/B_Q)²S_Q` for all `N≥Q≥2`; harmonic projection and the conductor
sampling bound preserve the reciprocal-prime gain. Individual check and
standard-only transitive axiom audit pass; integrated.

The centering coefficient itself satisfies
`|H_N a_1−t|≤8|t|Q/(N B_Q)≤8|t|/B_Q` for all `N≥Q≥2`.
Indeed `H_N a_1=(t/B_Q)Σ_p(H_N−H_(⌊N/p⌋))/p`; the two floor-harmonic
remainders cost at most `8/N` per prime. `PrimeChargePoleCoefficient`
proves this uniform identity and bound; individual plain check and
standard-only transitive axiom audit pass; integrated.

The corpus provides a sharper near-Gamma input:
`sum_collarRowNear_sq_le_sharp` bounds the square-mean logarithmic multiplier
by `130m/φ(m)`, with finite-period boundary error. The reduced-jet and exact
coherent-pole cancellation theorems in
`TheReducedDivisorJetCostsItsDivisorMean` and `TheJetPoleComponentCancelsThePole`
retain the charge in those channels. Their uniform transfer to these charge
families, including the upward nonratio channel, remains open here.

## Gates

- [x] Explicit families, critical overlap and literal receivers identified.
- [ ] Dependency-closed full paper classification.
- [ ] Full Lean classification and consequences; individual checks and transitive axiom audit.
