# P real-axis boundary — own research facts

- The existing critical-Laplace graph admits literal lower-half, four-level
  source reports, but its real-axis theta coefficient has prime square mass
  `4 log(p)^4 / p`; no continuous graph reader realizes even degree zero.
- New formal result:
  `PrimeLogThetaRealAxisClosableReaderNoGo.lean` proves that a complex-linear
  partial reader on this same graph, agreeing with all literal one-prime
  real-axis values, cannot simultaneously be closable and have dense domain.
  The result applies before any Xi quotient or scalar normalization.
- New reusable infrastructure:
  `DenseClosedComplexScalarRigidity.lean` proves that every closable,
  densely-defined complex scalar `LinearPMap` from a complex Banach space has
  a continuous full-domain extension.  This closes the previously open
  complex, rather than merely real, scalar case.
- Consequence for whole route: replacing the missing P morphism by an
  unbounded scalar reader, or by finitely many such coordinate readers, is
  impossible on `Graph(cl primeLogCriticalLaplaceSynthesis)`.  The surviving
  construction must alter topology before completion or use a genuinely
  non-scalar/infinite boundary object with a separately proved Xi-adic
  incidence law.  No Gamma or weighted-port module in the corpus currently
  supplies that incidence law.
- Literature audit: broad recent Calderón/boundary searches found weighted
  boundary spaces in PDE, but no theorem supplying the required arithmetic,
  coefficient-faithful Xi transport.  They do not advance P without a new
  source-to-boundary incidence construction.
