# Actual rough Markov clamp and local energy localization

- **ID:** rough-markov-clamp-domain
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Statement:** Construct the [0,1] clamp inside the physical L² primitive domain,
  localize its additive derivative energy exactly, and prove contraction of the
  entire admitted compact-source form.

For G(t)=c+primitive q(t), put T(a)=min(max(a,0),1). Candidate construction:

    q_clip = (modulusVelocity q c − modulusVelocity q (c−1))/2.

The scalar identity T(a)=(|a|−|a−1|+1)/2 suggests

    T(c)+primitive q_clip(t)=T(G(t))
    q_clip(t)=q(t) 1_{0<G(t)<1} a.e.

The second formula needs the already proved zero-level derivative law at BOTH
thresholds. It would identify the exact removed local Dirichlet energy and
give contraction of every path budget, congestion, jump energy and compact
source mass. Modulus preserves local derivative energy, whereas clamping
removes energy outside the band; this is a new domain-closure obligation.
No differentiability, integrability or Markov-admission premise may be assumed.

Potential equality frontier for the positive compact-source kernel: graph
energy is unchanged iff the state is constant throughout the nonzero source
or all its source values lie in [0,1]. Prove or correct this classification
on paper before formalization. Source-mass equality is a separate condition.

Query `Sobolev clamp truncation Markov primitive actual velocity graph contraction`
in the BiScaleUncertainty corpus completed without partial stages or errors.
All 20 candidate lemmas and 20 source arguments were inspected: actual modulus,
rough primitives, finite admission and graph comparison are available, but no
matching clamp realization or derivative localization was found. Snapshot is
older than the current index, semantic coverage unmeasured, background refresh
incomplete. Repeat focused source/parent-theory audit before implementation.
No external novelty claim. Unproved and not counted.
