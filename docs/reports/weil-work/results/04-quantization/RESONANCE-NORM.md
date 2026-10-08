# T23: critical resonance energy and the failed B² receiver

Paper status: dependency-closed. Lean status: PROVED. WP04 and P22 remain OPEN.
Verdict: the uniform bounded-resonance conjecture is FALSE; the exact finite-band
norm and pole/variance decomposition are a BRIDGE from existing source energy.
Independent scientific novelty is not established.

Final direct audits passed for WeilWorkQuantizationResonanceEnergy and
WeilWorkQuantizationResonanceMean, using `lake --old env lean` on each leaf.
All fifteen new declarations and their dependencies use only propext,
Classical.choice and Quot.sound. Both imports are wired exactly once; all sixty
quantization leaves are reachable. Complete audit: resonance-norm-lean-audit.txt.
Authoritative lint exited 1 on nine unrelated unreachable modules, with no
quantization error. No full or umbrella build was run.

## Exact statement

Fix an arbitrary `hW : WeilPositiveFull lam`. Write a(n) for the actual forward
Dirichlet-exponential coefficient, β for `sourceCompletion hW 1`, and

    r(n) = quantizationFrequencyResidue lam (−2 log n) 1,  n≥1,
    r_c(n) = r(n) − exp(−log n/2)c,
    E_c(N) = Σ_{1≤n≤N} |r_c(n)|²,
    L_{c,N}(p) = Σ_{1≤n≤N} p(n)r_c(n).

There are source-determined K>0 and V≥0 such that K=|β|²+V,
E_0(N)/log N→K and E_β(N)/log N→V. For every complex c, finite N and p,

    |L_{c,N}(p)|² ≤ E_c(N) Σ_{1≤n≤N}|p(n)|².

Equality holds for p(n)=conj(r_c(n)): its response is E_c(N), and its coefficient
energy is E_c(N). Thus E_c(N) is the exact squared finite-band norm, including
the zero-energy case. In particular E_0(N)→∞. No finite C bounds all original
responses by C times coefficient energy. When E_0(N)>0, the normalized witness
conj(r(n))/E_0(N) has response 1 and energy 1/E_0(N)→0.

The distinct frequencies −2 log n have orthogonal Cesàro means: each off-diagonal
term is an exponential of nonzero frequency, whose integral divided by T tends
to zero by its explicit antiderivative. Consequently coefficient energy is the
squared B² seminorm of these finite exponential polynomials. The normalized
resonance functional therefore has no bounded B² extension. This concerns the
normalized residue functional. It does not assert unboundedness of the actual
radial contour operator: that also requires a nonzero limit of the universal
main radial kernel, not proved here from the kernel definition alone.

## Closed proof

The exact resonance equation is log n+(−2 log n)/2=log 1. Uniqueness and
`quantizationFrequencyResidue_eq` give r(n)=exp(−log n/2)a(n). The source
coefficient equality is `forwardCoeff_eq_sourceCoeff`, with sourceCoeff defined
as dirichletExp(lamLog lam). Hence

    |r_c(n)|² = exp(−log n)|a(n)−c|² = |a(n)−c|²/n.

All equalities hold for n≥1, so summation identifies E_0 and E_β exactly with the
two energies in `exists_forwardCoeff_energy_variance`. That theorem, with hW as
its only source premise, supplies K,V and their relation. Its strict K>0 uses
β≠0, already proved from bigG nonvanishing and exponential nonvanishing.

The finite norm inequality follows by the triangle inequality and real
Cauchy–Schwarz applied to |p(n)| and |r_c(n)|. For the displayed conjugate
witness, each product equals the nonnegative real |r_c(n)|², and conjugation
preserves norms. If E_c(N)=0 all rows vanish; otherwise division by its square
root gives a unit-energy maximizer. Since log N→∞ and E_0(N)/log N→K>0,
E_0(N)→∞. A bound C would, on the unnormalized witness, imply E_0(N)²≤CE_0(N),
contradicting E_0(N)>max(C,0). The normalized witness follows by division.
No claim that V=0 follows: even V=0 would only give E_β=o(log N), not boundedness.

## Parent audit and scope

The source energy limit and variance decomposition already exist in
WeilWorkSingularArithmeticForwardEnergyLimit/ForwardVariance. Finite Hilbert
duality is classical. Følner, *On the dual spaces of the Besicovitch almost
periodic spaces* (1954), treats Bp completions and their duals:
[primary paper](https://gymarkiv.sdu.dk/MFM/kdvs/mfm%2020-29/mfm-29-1.pdf).
The source-specific consequence is an audited obstruction to the proposed P22
receiver, not a new general duality theorem or a proof of P22's failure.

Olsen's [local Dirichlet Hilbert-space results](https://arxiv.org/pdf/1011.3370)
assume finite coefficient Hilbert norm and concern local boundary intervals.
They do not pay this diverging critical row's global operator bound. The
[2026 finite-prime composition-operator norm paper](https://arxiv.org/html/2608.26041v1)
studies different operators and does not supply a bound for this canonical
source contour. No analogy is used as a premise.

## Next conjecture after the obstruction

P22 still survives. A successful receiver must retain the particular source
approximation error or use a stronger topology. Subtracting the pole row alone
removes |β|² log N but leaves V log N; even vanishing V would not bound the row.
Next inspect whether the actual phase admits approximants whose signed contour
errors vanish, with their bandwidth and B² accuracy chosen jointly. [OPEN CORE]
Produce such joint approximation from the original hW identity, without assuming
periodicity, a representation, or the desired arithmetic rigidity.
