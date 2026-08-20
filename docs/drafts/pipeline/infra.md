The main missing point: HLS is not merely the super-Poincaré commutation relations. It proves that those relations are the only possible nontrivial graded extensions under scattering-theory assumptions.

Current Lean work formalizes examples of the allowed answer. It does not derive exclusivity.

What full formalization needs:

1. **Physical state space**

   - Hilbert space decomposed into vacuum, one-particle, and multiparticle sectors.
   - Bosonic/fermionic statistics.
   - One-particle states classified by mass, momentum, spin, and particle type.
   - Positive-energy representations and finite particle multiplicity below each mass.

2. **Actual Poincaré/Lorentz action**

   - Unitary representation of \(\mathrm{Spin}^+(1,3)\ltimes\mathbb R^{1,3}\).
   - Self-adjoint generators \(P_\mu,M_{\mu\nu}\) with common invariant domains.
   - Mass-shell spectral condition and \(P_0\ge0\).
   - Weyl-spinor transformation law
     \[
     [M_{\mu\nu},Q^I_\alpha]
       =(\sigma_{\mu\nu})_\alpha{}^\beta Q^I_\beta,
     \qquad [P_\mu,Q^I_\alpha]=0.
     \]

   A \(2\times2\) matrix identity resembling this is insufficient; it must be an operator identity in a Poincaré representation.

3. **Scattering operator**

   - A unitary \(S\)-matrix on asymptotic scattering states.
   - Poincaré invariance of \(S\).
   - Symmetry generators must commute with \(S\).
   - Generators must act additively on multiparticle states, with the correct graded signs.

   HLS explicitly defines its generators through commutation with \(S\) and additive action on incoming multiparticle states. It also requires them to connect only equal-mass particle types. [Original HLS paper](https://courses.physics.ucsd.edu/2014/Fall/physics215a/project/susy-HLS.pdf)

4. **Nontrivial scattering and analyticity**

   - Elastic amplitudes as functions of Mandelstam \(s,t\).
   - Analyticity near the physical region, except normal thresholds.
   - Actual occurrence of scattering between generic particle states.
   - Distributional regularity of symmetry-generator kernels in momentum space.

   These conditions do the no-go work. Without them, exotic higher-spin or momentum-dependent symmetries survive. Coleman–Mandula lists the assumptions explicitly. [Original Coleman–Mandula paper](https://www.physics.mcgill.ca/~keshav/675/colemanmandula.pdf)

5. **Massive-sector restrictions**

   - Finite number of particle types per mass multiplet.
   - No vacuum degeneracy or spontaneous symmetry breaking.
   - No obstructive infrared behavior.
   - Usually a massive sector or mass gap for the standard HLS conclusion.

   HLS warns that massless theories, infrared problems, vacuum degeneracy, and infinite particle towers fall outside that conclusion. [Original HLS paper](https://courses.physics.ucsd.edu/2014/Fall/physics215a/project/susy-HLS.pdf)

6. **Classification proof**

   Lean would then need to prove:

   - translation-invariant odd generators form a finite-dimensional Lorentz representation;
   - spin-statistics forces them to carry half-integral Lorentz type;
   - positivity of \(\{Q,Q^\dagger\}\) eliminates all types except rank-one Weyl spinors;
   - Lorentz covariance forces
     \[
     \{Q^I_\alpha,\bar Q^J_{\dot\beta}\}
       =2\delta^{IJ}\sigma^\mu_{\alpha\dot\beta}P_\mu;
     \]
   - the same-chirality bracket can contain only antisymmetric scalar central charges:
     \[
     \{Q^I_\alpha,Q^J_\beta\}
       =\varepsilon_{\alpha\beta}Z^{IJ};
     \]
   - graded Jacobi identities force \(Z^{IJ}\) to be central and constrain internal-symmetry action;
   - no additional bosonic or fermionic spacetime generators remain.

Why assumptions cannot simply be removed: take \(S=1\). Then every unitary transformation commutes with \(S\), producing vastly more symmetries than super-Poincaré. The classification is false unconditionally.

Therefore:

- The proposed \(N=2\) Weyl/central-charge module formalizes an **allowed HLS algebra**.
- A physical HLS theorem requires the entire scattering/Poincaré infrastructure above.
- Under the strict “no hypotheses” rule, full HLS classification is impossible unless we construct one explicit scattering model and prove everything for that model—which would be an example, not the HLS theorem.