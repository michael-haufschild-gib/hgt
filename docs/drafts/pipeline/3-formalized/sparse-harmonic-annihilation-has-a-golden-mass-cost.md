# Sparse harmonic annihilation has a golden mass cost

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); contribution 21
- **Obstacles:** B13, B112; positive annihilation of finite vertical zero patterns.
- **Statement:** For a positive two-prime Dirichlet polynomial with constant coefficient one, accuracy at the first and fourth harmonic ordinates forces tail mass at least `(sqrt(5)-1)(1-epsilon)`. For every real abscissa and `0<=epsilon<=1`, a positive polynomial attains equality at a positive ordinate spacing.
- **Novelty:** The corpus already has the sharp consecutive-harmonic packet bound. This result concerns a sparse pair of harmonics and its exact accuracy frontier. The certificate, phase classification, and extremizers count together.

## Proof

Put `phi=(1+sqrt(5))/2`. For every real `x`,
`8x^4-8x^2+4x+1+5phi/2 = 8(x+phi/2)^2((x-phi/2)^2+(phi-1)/2)`.
The identity follows by expansion and `phi^2=phi+1`. Its second factor is strictly positive since `phi>1`. The double-angle formula gives `cos(4theta)=8cos(theta)^4-8cos(theta)^2+1`. Thus `F(theta)=5phi/2+4cos(theta)+cos(4theta)>=0`, with equality exactly when `cos(theta)=-phi/2`.

For each nonconstant monomial, let `L_d` be its logarithmic frequency and let `w_d>0` be its coefficient times `exp(-beta L_d)`. Put `H=sum w_d`. The real part of the evaluation at `beta+i k gamma` is `1+sum w_d cos(k gamma L_d)`. Consequently
`sum w_d F(gamma L_d) = (5phi/2)H+4 Re P(beta+i gamma)+Re P(beta+4i gamma)-5`.
Nonnegativity gives the universal joint evaluation inequality. If both evaluation norms are at most `epsilon`, their real parts are at most `epsilon`, so `H>=2/phi*(1-epsilon)=(sqrt(5)-1)(1-epsilon)`. If both evaluations vanish, equality holds exactly when every supported phase satisfies `cos(gamma L_d)=-phi/2`.

For sharpness, take `P=1+(1-epsilon)/phi*(X_beta^2+X_beta^3)`, where `X_beta` is the scaled prime-two monomial. Its coefficients are nonnegative for `epsilon<=1`, and its constant coefficient is one. At spacing `gamma=2pi/(5 log 2)>0`, put `u=exp(-2pi i/5)`. Then `u^5=1`, `u^3=conj(u^2)`, and `Re(u^2)=cos(4pi/5)=-cos(pi/5)=-phi/2`. Hence `u^2+u^3=-phi`. Also `(u^4)^2+(u^4)^3=u^3+u^2=-phi`. Both required evaluations therefore equal `epsilon`, and `H=2(1-epsilon)/phi`. For `epsilon>=0`, their norms equal `epsilon`.

## Lean certificate

Modules under `formal/GaloisForLFunctions/ArithmeticPositiveDuality/`:

- `SparseHarmonicAnnihilatorMass.lean`: `sparseHarmonic_mass_energy`, `sparseHarmonic_joint_evaluation_bound`, `sparseHarmonic_accuracy_mass_bound`, and `sparseHarmonic_mass_eq_iff`.
- `SharpSparseHarmonicAnnihilation.lean`: `sparseHarmonicAnnihilator_at_harmonic`, `exists_sharp_sparse_harmonic_accuracy`, and `sparse_harmonic_accuracy_frontier`.

Both modules passed `lake --old env lean` checking; the final frontier passed a direct audit. Transitive axioms are only `propext`, `Classical.choice`, and `Quot.sound`. Both imports are wired into the programme umbrella. No frequency cutoff, RH, or abscissa-law premise occurs.
