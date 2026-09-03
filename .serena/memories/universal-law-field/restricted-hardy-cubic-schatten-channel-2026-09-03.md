# Restricted Hardy cubic Schatten channel (2026-09-03)

Active route: `restricted-prime-gamma-toeplitz-polar-defect.md`.

Exact paper theorem added to `ULF-RUCRI-001`: for an orthogonal projection `P`, unitary `U` with `[P,U] in S2`, `R=U*PU`, `Delta=R-P`, and `T=Delta^3`,
```
||T||_1 = ||(1-P)UP||_3^3 + ||(1-P)U*P||_3^3
        = ||[P,U]||_3^3.
```
Proof: relative to `P H directSum (1-P)H`, `Delta^2=diag(1-A,C)`; those blocks are the two Hankel seam energies. Functional calculus gives the trace norm identity.

For bounded real multiplication generator `phi`, `U=exp(i M_phi)`, Duhamel gives
```
[P,U] = integral exp((1-t)X)[P,X]exp(tX) dt, X=iM_phi,
||T||_1 <= ||[P,M_phi]||_3^3 = 2||(1-P)M_phi P||_3^3.
```
So exponentiation is non-amplifying at S3; missing theorem is additive-current Hankel S3 control plus genuine S3 completion.

Hostile lock: diagonal coefficient cubes do not dominate Hankel S3 mass with constant one. For the finite Hankel matrix `A=[[1,1],[1,0]]`, `Tr|A|^3=2 sqrt 5 > 3`, while weighted separate coefficient cubes are `1+2=3`. Full cyclic cross-frequency Gram is mandatory.

Further firewall: existing Route-P base Cauchy source Gram is prime-depth-labelled; target conormal Gram is zero-labelled. Corpus theorem `routePPrimitiveBaseCauchyTraceCapacityLaw_iff_riemannHypothesis` proves their global trace domination is already terminal RH capacity. It cannot be reused as upstream producer. Trace of source Gram also sees only diagonal, whereas S3 mass of a summed Hankel operator contains cyclic triple products.

Required next object: finite-stage coefficient-faithful factorization of the anomaly-subtracted additive boundary Hankel operator itself through a full source cyclic Gram before completion, with S3 contractivity. Post-completion prime-Gram/zero-Gram comparison is circular. Related memories: `mem:universal-law-field/restricted-prime-gamma-toeplitz-polar-defect-2026-09-02`, `mem:prime-hodge-singular-residue-clock-2026-09-03`.