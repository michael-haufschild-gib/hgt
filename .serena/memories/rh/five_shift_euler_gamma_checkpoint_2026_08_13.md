# Five-shift Euler–Gamma checkpoint (2026-08-13)

Axiom-clean Lean formalization now proves a five-shift prime-gap separator
P_r(a)=x(1-x)(x-e^{-6r/5})(x-e^{-2r})(x-e^{-21r/10}), x=e^{-2ar}.
It is positive for 0<a<=1/2, zero at a=0, nonpositive at a=log n (n>=2), and has two exact Gamma-tail moment cancellations.

Paired inverse-square feature has uniform scale-one lower bound 1/81 and an exact multiplicity-aware Weil–Krein reflection-difference landing. Finite receiver:
three_quarters_line_of_fiveShiftEulerGammaPairedCharge; it needs 81 E <= N/8.

Critical Hedenmalm feature has exact kernel 2/(1+(z-t)^2), decomposed into lower/upper Cauchy poles. Full holomorphic Weil polarization is formally equal to four absolute-Euler prime–Gamma source terms (same-orientation terms fold via XiC'/XiC oddness).

No-go survivors:
- normalized feature cannot land continuously at critical boundary;
- legal rectangular window preserves a nonnegative global Hermitian charge, zero iff RH;
- coefficient-faithful windowed holomorphic Weil source is identically zero;
- Hermitian/source pointwise identification is equivalent to RH.

Open core: height-local Hermitian/rank-trace source current and unconditional dyadic arithmetic estimate 81 E_T <= N(T,2T)/8. Holomorphic source decomposition alone is not Euclidean pair-difference energy.

Relevant modules:
formal/GaloisForLFunctions/RHTower/XiWardFiveShift*.lean
formal/GaloisForLFunctions/RHTower/HedenmalmCriticalFeatureKernel.lean
formal/GaloisForLFunctions/RHTower/HedenmalmCriticalFeaturePrimeGammaDecomposition.lean

Guardrail: fiveShiftCriticalEvaluationEnergyCurrent_vonMangoldt_nonpos has incompatible strip/Euler premises for n>=2; valid implication but not a usable Euler sampling theorem.