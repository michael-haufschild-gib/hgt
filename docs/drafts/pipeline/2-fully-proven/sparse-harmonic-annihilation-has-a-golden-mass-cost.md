# Sparse harmonic annihilation has a golden mass cost

- **Stage:** 2-fully-proven; Lean formalization in progress
- **Type:** THEOREM on paper; not yet counted
- **Obstacles:** B13, B112; positive annihilation of finite vertical zero patterns.
- **Statement:** For a positive two-prime Dirichlet polynomial with constant coefficient one, accuracy at the first and fourth harmonic ordinates forces tail mass at least `(sqrt(5)-1)(1-epsilon)`. For every real abscissa and `0<=epsilon<=1`, a positive polynomial attains equality at a positive ordinate spacing.
- **Novelty:** The corpus already has the sharp consecutive-harmonic packet bound. The proposed result concerns a sparse pair of harmonics and its exact accuracy frontier; it is not counted yet.

## Proof

Put `phi=(1+sqrt(5))/2`. For every real `x`,
`8x^4-8x^2+4x+1+5phi/2 = 8(x+phi/2)^2((x-phi/2)^2+(phi-1)/2)`.
The identity follows by expansion and `phi^2=phi+1`. Its second factor is strictly positive since `phi>1`. The double-angle formula gives `cos(4theta)=8cos(theta)^4-8cos(theta)^2+1`. Thus `F(theta)=5phi/2+4cos(theta)+cos(4theta)>=0`, with equality exactly when `cos(theta)=-phi/2`.

For each nonconstant monomial, let `L_d` be its logarithmic frequency and let `w_d>0` be its coefficient times `exp(-beta L_d)`. Put `H=sum w_d`. The real part of the evaluation at `beta+i k gamma` is `1+sum w_d cos(k gamma L_d)`. Consequently
`sum w_d F(gamma L_d) = (5phi/2)H+4 Re P(beta+i gamma)+Re P(beta+4i gamma)-5`.
Nonnegativity gives the universal joint evaluation inequality. If both evaluation norms are at most `epsilon`, their real parts are at most `epsilon`, so `H>=2/phi*(1-epsilon)=(sqrt(5)-1)(1-epsilon)`. If both evaluations vanish, equality holds exactly when every supported phase satisfies `cos(gamma L_d)=-phi/2`.

For sharpness, take `P=1+(1-epsilon)/phi*(X_beta^2+X_beta^3)`, where `X_beta` is the scaled prime-two monomial. Its coefficients are nonnegative for `epsilon<=1`, and its constant coefficient is one. At spacing `gamma=2pi/(5 log 2)>0`, put `u=exp(-2pi i/5)`. Then `u^5=1`, `u^3=conj(u^2)`, and `Re(u^2)=cos(4pi/5)=-cos(pi/5)=-phi/2`. Hence `u^2+u^3=-phi`. Also `(u^4)^2+(u^4)^3=u^3+u^2=-phi`. Both required evaluations therefore equal `epsilon`, and `H=2(1-epsilon)/phi`. For `epsilon>=0`, their norms equal `epsilon`.

## Formalization gate

The positive certificate, universal evaluation inequality, equality support, and sharp accuracy frontier count together. All mathematical dependencies are explicit above; Lean and transitive-axiom checks remain.
