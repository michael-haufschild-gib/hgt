# HC15: HB source-faithful branch covariance no-go (2026-08-28)

Formal module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSourceFaithfulBranchCovarianceNoGo.lean`
Formalized card: `docs/drafts/pipeline/3-formalized/hb-source-faithful-branch-covariance-no-go.md`
Failed-route card: `docs/drafts/pipeline/5-failed/hb-two-branch-source-faithful-schwarz-covariance-no-go.md`

For every nonzero amplitude, canonical plus source at `reflect q` equals canonical minus source at `q` iff `Re(q)=1/2`. Therefore for arbitrary complex field space, arbitrary bilinear quadratic residual, and arbitrary branch families, literal source fidelity plus branch swap forces criticality. Global source fidelity plus branch covariance implies RH. No symmetry, cyclicity, Peierls pairing, propagator, radial basis, or square-root representation is used.

Combined theorem `hbXiPeierls_tilted_sourceFaithful_noGo_and_realClosure_ge_four` proves that off wall the two-branch realization is impossible while every FE+Schwarz closed packet containing the physical weight has card at least four. Strongest survivor: minimal physical continuation must use the complete four-sector FE-Schwarz real-closure packet and an orbit-level landing.

Verification: direct `lake env lean` passed; target-only build passed (11892 jobs after shared replay); four endpoint axiom prints only `[propext, Classical.choice, Quot.sound]`; forbidden-token scan clean; umbrella wired. Global lint failure was unrelated pre-existing umbrella reachability errors.

Next HC16 direction: construct the four-sector orbit Peierls landing; determine exact orbit sum/classification rather than retrying individual-fibre incidence.