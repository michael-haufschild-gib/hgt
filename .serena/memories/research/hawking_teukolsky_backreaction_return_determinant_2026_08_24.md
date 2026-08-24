Implemented `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTeukolskyBackreactionReturnDeterminant.lean`; imported from `formal/GaloisForLFunctions/RHTower.lean`. No git.

Exact source-faithful results:
- Birmingham--Mokhtari d=4 Kodama--Ishibashi scalar/vector gravitational potentials specialized with Hodge-paired Q.
- At M=0 both paired sectors share exact Gamma-product gravitational boundary Jost.
- Xi divisor descendants: simple gravitational Jost zeros, inverse Green simple poles, both QNM branches.
- Exact first mass-coordinate potential split: d/dx(B_S-B_V)|0 = 12/(Q+2).
- On physical theta continuum Q=1/4+xi^2, split =48/(9+4xi^2)>0. Normalized horizon absorption square times split is nonnegative; negative radial cubic chamber excluded.
- Teukolsky-Starobinsky branch difference C(omega+)-C(omega-)=24 i M xi, shadow odd but nonzero at every Xi divisor for M !=0: bare helicity phase no-go.
- Genuine finite/jet Evans return determinant R=J_ret(z)J0(tau z)-J0(z)J_ret(tau z), shadow odd.
- At plus divisor QNM, R=J_ret(z)*nonzero companion; R!=0 iff returned channel nonzero.
- QNM pole velocity factorization R=-v_M*(dJ/domega)*companion.
- For J_ret=horizonPhase*J0+crossSource, arbitrary multiplicative phase cancels at QNM; R!=0 iff crossSource!=0.
- Projective Cayley numerator/denominator are swapped by shadow; quotient S=(1+R)/(1-R) satisfies S(tau)=S^-1.
- S nontrivial in every Xi sector iff cross source excites every Xi sector.

Important correction: earlier scratch claim of sign-changing mass split was wrong. Exact TeX gives scalar derivative 3(2-Q)/(Q+2), vector derivative -3, difference +12/(Q+2).

Remaining OPEN CORE:
Derive actual J_ret/crossSource from second-order Einstein/Teukolsky nonlinear source and horizon mass/spin history. Need full optical resolution including QNM residues plus direct large-frequency arc (AdS) and branch cut/continuum (asymptotically flat). Literature does not provide positive QNM completeness. Do not pretend KMS/passivity supplies this.

Verification:
- targeted Lean compile passed clean.
- targeted olean passed.
- axiom audit for all new theorems: only propext, Classical.choice, Quot.sound.
- temp Lean/PDF/source files removed.
- no umbrella build or lint rerun; prior session already found unrelated umbrella lint omissions.