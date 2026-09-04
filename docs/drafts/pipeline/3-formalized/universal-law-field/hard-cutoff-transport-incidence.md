# Hard-cutoff transport: commuting scale motion, exact birth incidence

- ID: ULF-HCTI-001
- Stage: 3-formalized; exact Lean proofs verified, not an RH estimate.
- Type: [BRIDGE], scoped obstruction to one proposed hypocoercive realization; not an RH bound.
- Parent: ULF-MHBR-001-PHYS. Required RH edge remains cofinal upper bounds on unchanged C_N(r).

## Interpretation and audit

The proposed extra motion was integer cutoff transport coupled to prime dilation.
Its extra coordinate is not automatically a new mixing direction: the combined transfers
still form one commutative multiplicative action. Integer births, in contrast, carry exact
divisibility incidence. This distinguishes an actual interaction from a second coordinate name.

Checked corpus: `GibbsDilationSeam.dilate_comm`, `GibbsScaleContraction`,
`GibbsAntiscaleFirstTraceFrame`, `GibbsCriticalDissipationAntiscaleResonance`,
`MobiusLaplaceCriticalDilationNoGo`, `MobiusGammaXiMarkedClockBoundaryRateDecoupling`.
Research searches: hard cutoff Gibbs insertion; floor dilation successor difference;
divisibility cutoff increment; dilation successor intertwining; hypocoercivity commutative kernel.
Existing untruncated dilation commutation is not being presented as new mathematics.

[LITERATURE] Fang--Lu--Tong, https://arxiv.org/html/2404.11503, conditions 5--8:
transport must move dissipative-kernel directions into damped directions quantitatively.
Their result does not prove this property for arithmetic cutoffs.
[LOCAL-RESEARCH] The recurrence manuscript's completed-time-then-size order does not exchange
the two limits; it cannot supply this quantitative property either.

## Exact statement

For F : N x R -> R define

    (T_p F)(N,x)=F(N div p,p x),
    (D_p F)=F+T_p F,       (B_p F)=F-T_p F,
    (Delta F)(N,x)=F(N+1,x)-F(N,x).

1. T_p T_q=T_(pq)=T_q T_p, including the literal floor.
2. D_p B_q=B_q D_p. In particular B_q preserves any exact D_p-null history.
   This is only a statement about these unnormalized constant-coefficient operators.
3. Delta T_p F(N,x)=T_p Delta F(N,x) if p divides N+1, and zero otherwise.
4. If p>=2 and F(0,x)=0, then D_p F=0 implies F=0.
5. For K>=0,

    F(N,x)=sum_(j<K) (-1)^j (D_p F)(N div p^j,p^j x)
            +(-1)^K F(N div p^K,p^K x).

   If p^K>N and F(0,.)=0 the terminal term vanishes. This is finite reconstruction,
   not a cutoff-uniform estimate: the number of seam terms grows with cutoff.
6. This loss is real even for a single fixed p>=2. The explicit zero-boundary history

       F_p(N,x)=0 if N=0; otherwise (-1)^floor(log_p N)(floor(log_p N)+1)

   satisfies |D_p F_p(N,x)|<=1 everywhere, but |F_p(p^K,x)|=K+1.
   Thus bounded seams and algebraic injectivity alone do not uniformly bound histories.
   This history is a counterexample to a generic transfer estimate, not a model of mu.

## Complete proof

1. Euclidean division gives (N div p) div q=N div(pq), and multiplication of
   scales gives q(px)=(pq)x. This also covers zero using natural division conventions.
2. Expand both sides. Each is F-T_q F+T_p F-T_p T_q F; apply (1).
   If D_p F=0, the right side B_q(0) is zero.
3. Natural successor division is
   (N+1) div p=N div p + (if p divides N+1 then 1 else 0).
   Substitute this identity in the difference. No limiting argument is used.
4. Strong induction on N, with the assertion quantified over every real x.
   N=0 is the zero boundary condition. For N>0, N div p<N; the induction
   hypothesis at px gives T_p F(N,x)=0. D_p F(N,x)=0 then gives F(N,x)=0.
5. K=0 is immediate. Expand the last term using F=D_p F-T_p F.
   Use (1) to identify the new last term and (-1)^(K+1)=-(-1)^K.
   Induction proves the formula. Natural division is zero when its numerator
   is smaller than its denominator, proving the boundary-vanishing assertion.
6. If 0<N<p, the quotient is zero and floor(log_p N)=0, so the seam equals 1.
   If N>=p, set L=floor(log_p(N div p)); then floor(log_p N)=L+1.
   The two history values sum to (-1)^(L+1)(L+2)+(-1)^L(L+1)=(-1)^(L+1).
   At N=0 both terms vanish. The absolute seam is therefore 0 or 1.
   Finally floor(log_p(p^K))=K gives the stated growing amplitude.

## Hostile verdict and positive survivor

[FALSIFIED] The claim that adding the hard cutoff automatically makes the prime
transfers noncommute. The exact floors do not break commutation.
[BRIDGE] The positive survivor is the explicit birth-incidence law and finite
seam reconstruction with an explicit logarithmically growing, unit-seam history,
separating algebraic injectivity from a uniform analytic bound.
There is no claim that nonzero global null histories exist under the physical zero boundary;
statement (4) proves they do not. Near-null behavior and its rate remain separate questions.

This does NOT retire hypocoercivity with additional source-derived operators, variable Gibbs
hazards, adjoints or boundary conditions. Nor does it show these additions suffice. The next
candidate must quantify an actual noncommuting action on the unchanged arithmetic source;
divisibility incidence alone is not cancellation (STATUS CANNOT-291).

[OPEN CORE] No estimate for the signed reconstructed seams in the Gamma--Hankel norm,
no bound on C_N(r), and no unconditional RH proof is supplied here.

## Lean certificate

`formal/GaloisForLFunctions/RHTower/GibbsHardCutoffTransport.lean`, namespace
`RHTower.GibbsGas`: `hardCutoffTransfer_comm`, `hardCutoffSameSign_signedInsertion`,
`hardCutoffBirth_transfer`, `hardCutoffBirth_transfer_commutator`,
`hardCutoffSameSign_zero_boundary_injective`, `hardCutoffSameSign_reconstruction`,
`hardCutoffSameSign_reconstruction_of_lt`,
`exists_hardCutoff_unit_seam_logarithmic_escape`, `not_hardCutoff_unit_seam_uniform_bound`.
Exact proof bodies checked together in `/tmp/hgt_hard_cutoff_transport.lean` with
`lake env lean`: exit 0, no warnings. Axiom audit: only
`propext`, `Classical.choice`, `Quot.sound`. RHTower import wired; no umbrella build.
Repository-wide `formal_tools.py lint` was run without build: it reports six unrelated
unwired HTGeometry physics modules, not proof debt or an error in this leaf. Full-project
lint is therefore not green; those concurrently owned modules were left untouched.
