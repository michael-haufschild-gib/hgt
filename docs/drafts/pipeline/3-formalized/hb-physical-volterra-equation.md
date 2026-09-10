# HB: the physical causal time equation

Stage: 3-formalized. The original physical causal response satisfies the bounded time equation almost everywhere on the whole real time line. The exact leaf build and new-theorem axiom audit passed. The [native original-space Bochner equation](hb-native-time-integral-identification.md) is also formalized. [Native/physical response equality](hb-native-causal-equality.md) is now proved almost everywhere. Complete-current cancellation and RH remain open. Frontier map read only.

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Exact proved statement

Let `U=causalJointForcedResponse q branch a`, `F=causalCuspSourceVector q branch a`, `J=jointEmbedding`, `B=J J.adjoint` and `P2 f(t)=integral_0^t (t-u) f(u) du`. The new theorem proves, almost everywhere on the original real time line,

```
B U+(I-B)P2 U=B P2 F.
```

The existing physical construction supplies weighted time-L2 admission, causal support, absolute Bochner Laplace convergence and the actual original operator equation

```
A Uhat+(w^2-1) Uhat=Fhat,
Uhat in domain(A), A=jointEnergyOperator=B^(-1),
Re(w)>causalResponseShift(q)+1.
```

No norm continuity of this physical representative is assumed.

## Paper proof

1. Extend all damped functions by zero off the positive ray. Write `K_w(t)=1_(t>0) exp(-wt)`. For `Re(w)>0`, the actual complex exponential integral gives `K_w in L1` and `integral K_w=w^(-1)`.
2. Directly restricting the convolution integral to `0<u<t` proves `K_w*K_w=1_(t>0)t exp(-wt)`. Hence the latter kernel is L1 and has integral `w^(-2)`, by the existing Bochner convolution theorems. This derives the polynomial weight from the elementary exponential kernel.
3. Scalar multiplication and the exponential addition law identify the convolution of this kernel with the damped datum as `1_(t>0)exp(-wt)P2 f(t)`. Thus any datum with an absolutely convergent Laplace integral has an absolutely convergent double-primitive Laplace integral, equal to `w^(-2) fhat(w)`. The construction does not require a continuous datum.
4. On the actual operator domain, `B(A v)=v`: use the range definition of the original Friedrichs inverse and its proved action on a covariance value. Apply B to the physical operator equation. Its exact result is `Uhat+(w^2-1)B Uhat=B Fhat`.
5. For `D=B U+(I-B)P2 U-B P2 F`, bounded-operator integral interchange and step 3 show `Dhat=0` throughout the same physical right half-plane. Each damped term is L1. Fix the line `Re(w)=causalResponseShift(q)+2`.
6. For each Hilbert vector v, the Fourier transform of the scalar damped probe `inner(v,D(t))` vanishes, using the corpus's actual `fourierIntegral_rayDamp`. The proved scalar L1 Fourier uniqueness theorem makes that probe zero almost everywhere. To remove the probes without assuming a globally separable Hilbert space, pair the integral of the damped vector over each finite-measure set against every v. All these pairings vanish, so each set integral is zero. `Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero` then gives vector vanishing almost everywhere. Nonvanishing of the damping removes it.
7. The original causal support makes the response and its double primitive zero before time zero, almost everywhere for the response and everywhere for the primitive. The source has the same support. This extends the time equation from the positive ray to the whole original time line, with time zero irrelevant to the measure.

Every parameter, principal amplitude, cutoff commutator and original measure is inherited from the constructed physical source and operator. No response-identification premise is introduced.

## Completed response comparison and next hard step

The [applied covariance-energy uniqueness proof](hb-native-causal-equality.md) now subtracts the two original equations and proves the native/physical time-class equality. Local integrability follows from existing admission theorems. A first-moment decomposition makes the double primitive continuous; integrating the equation twice gives a classical homogeneous equation with zero initial data. Contractivity and dense range of the actual embedding force its conserved energy, velocity and original difference to vanish.

The full physical-current cancellation remains open. The next target is transferring the identified response into the complete finite-domain current and evaluating all its physical boundary terms before taking their limits.

## Search and method check

Broad corpus searches `Volterra` and `quadratic conservation` (the latter OR), and deep Laplace/convolution and energy-uniqueness searches were inspected in declaration, candidate, source-method, proof-idea and ingredient-set views. The convolution and scalar Fourier-injectivity ingredients were checked against the installed toolchain. Retrieval remained partial: the broad energy snapshot inventoried 56,304 files, with 48 compiled snapshots and most compiler metadata pending; the deep energy request ended at its budget with coverage pending. Generated ingredient groups are proposals, not proofs. The scalar `sturmEnergy_const` and Klein–Gordon inner-product differentiation supply methods for the next uniqueness step, not its application to these fields.

Own broad arXiv searches used `coercivity` and `transmutation`. [Jin–Ma–Zuazua, revised 27 June 2026](https://arxiv.org/html/2601.03616v2), sections 2.1–2.2, represents diffusion through a Gaussian average of a factored wave evolution. This suggests testing a positive first-order realization if the direct covariance-energy argument fails; its wave/domain assumptions still require proof for the actual joint operator. [Adarsha–Chakraborty–Bhattacharyya, revised 7 September 2026](https://arxiv.org/abs/2608.10594) derives compact-star growth times with accretion, evaporation and feeding; its stated result supplies no identity for this source pairing. Neither paper is a premise of the Lean proof.

## Lean and audit

[ThetaCuspHawkingBMPhysicalVolterraEquation.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMPhysicalVolterraEquation.lean) contains one public theorem, `causalJointForcedResponse_bochner_covariance_equation`, for every original Xi occurrence, branch and amplitude. Its mathematical hypotheses are the existing constructed objects; no source-equation, response-identification or growth premise is supplied.

The full candidate passed `lake env lean`. Final `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalVolterraEquation` passed in the isolated cached leaf environment: two jobs, 31 seconds reported build time. One harmless private-helper unused-section-variable warning remains. Only the new public theorem was checked with `#print axioms`; the result is exactly `propext`, `Classical.choice`, `Quot.sound`. The source and all five build artifacts were installed byte for byte. Its import is wired into `RHTower.lean`; no umbrella or dependency build ran.

Repository-wide `scripts/formal_tools.py lint` passes; existing large-file warnings remain. Report links were checked. Frontier map and universal-law ledger remain unchanged. No numerical computation, full build, umbrella build, Git command or launcher ran.
