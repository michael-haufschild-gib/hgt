# Hidden grade duality of source phase work versus prime-seam energy

- **ID:** stc-source-work-grade-duality
- **Stage:** 3-formalized
- **Type:** exact source-scalarization non-identification theorem
- **Routes:** STC, RHist, Gamma-six/Sonin source lift
- **Status:** [PROVED ON PAPER] [FORMALIZED IN LEAN] [NOT AN RH PROOF]

## Two actual source observables

For a real centered horizontal grade 0<t<1, the complete-source/Sonin phase work in FrankensteinSourceTailSoninPhaseWork.lean has the pre-divisor scalar profile

    W(t)=c t²(1-t²)/(1+t²)²,   c=(log 2)²/4.          (1)

At a Xi-divisor copy its exact value is W(t), with t=primeDepthBVWoldXiCenteredRate. This card studies the same source profile on the full open grade interval without asserting that zeros occur at any chosen grade.

The canonical STC all-prime seam has reciprocal-prime one-particle energy, independent of vertical height,

    E(t)=sum_p (log p)²/p² (p^t+p^(-t)-2)
        =4 sum_p (log p)²/p² sinh²(t log p/2).         (2)

The identity is already formalized primewise in XiPrimeSeamReflectionEnergy.lean; convergence for t<1 and the cofinal pair-energy limit 2E(t) are in XiPrimeSeamPairAsymptotics.lean. Thus E(t) is the positive coefficient read by the Calkin lower bound, whereas W(t) is the scalar returned by the existing complete-source/Sonin diagonal.

## Theorem: exact grade involution and lost seam information

Put s=t² and define

    J(s)=(1-s)/(1+3s),       h(s)=s(1-s)/(1+s)².     (3)

For 0<s<1, J(s) also lies in (0,1), J(J(s))=s, and h(J(s))=h(s). The only fixed point is s=1/3. Indeed

    1-J(s)=4s/(1+3s),     1+J(s)=2(1+s)/(1+3s),

which gives h(J(s))=h(s); substituting once more gives the involution. Fixed-point algebra is (3s-1)(s+1)=0. Therefore the two grades

    t and t*=sqrt[(1-t²)/(1+3t²)]                    (4)

have exactly the same work W whenever 0<t<1, while t*=t only at t=1/sqrt(3).

By (2), E(t) is **strictly increasing** on (0,1): each prime summand is strictly increasing, and all sums are finite. Hence E(t*) differs from E(t) whenever t differs from 1/sqrt(3). There is no function Φ, linear or nonlinear, satisfying E(t)=Φ(W(t)) for every pre-divisor grade 0<t<1. The complete-source phase work by itself has folded together two physically different seam energies.

The mismatch becomes unbounded at the two ends of this duality. As t→0+, t*→1-, E(t)→0 and E(t*)→+∞, while W(t*)=W(t)→0. The E limits follow by dominated convergence on any compact substrip and monotone convergence at the outer edge, where the limiting prime series dominates a positive multiple of sum_p 1/p. Thus even a comparison E≤Φ(W) with Φ bounded near zero fails uniformly over the full strip.

## Sharp outer-edge transport cost

Let δ=1-t↓0 and F(δ)=sum_p (log p)² p^(-1-δ). Equation (2) gives the exact decomposition

    E(1-δ)=F(δ)-2F(1)+F(2-δ).                        (5)

The Euler product and the pole of ζ at 1 give F(δ)=δ^(-2)+O(1): the second derivative of log ζ(1+δ) is δ^(-2)+O(1), while the prime-power correction is analytic at δ=0. The independent [prime-height fibre theorem](stc-prime-boundary-height-fibers.md) records this argument. From (1),

    W(1-δ)~[(log 2)²/8] δ,
    E(1-δ)~δ^(-2),
    E(1-δ)/W(1-δ)~[8/(log 2)²] δ^(-3).              (6)

So any grade-uniform multiplicative bridge from this scalar work to seam energy needs at least a cubic singular gain at the outer strip edge. Equation (6) is a scale obstruction, not a prohibition on a Xi-zero-specific nonuniform or singular transport.

## Consequence and scope

This kills the conjecture that the already proved positive complete-source/Sonin work alone controls the all-prime STC seam or its Calkin coefficient. Its hidden Möbius grade involution loses information before any analytic estimate. The signed complete-source tail still retains the oriented grade, and the full prime carrier retains still more information; the theorem does not rule out a coupled, non-scalar source law using them. Such a law must be derived independently and must keep the arithmetic vertical phase through its Sonin landing. Neither the work identity nor this no-go proves RH.

An attempted all-prime square budget from the existing work diagonal also fails for a precise reason. The normalized prime Bockstein in FrankensteinSourceTailSoninGaussianWronskianBridge.lean equals the same source Wronskian at every prime; summing those normalized squares would be infinite whenever t≠0, but the diagonal theorem supplies a **single scalar limit**, not a summed mass bound. The raw Bockstein keeps prime decay, yet PrimeGammaCofinalBocksteinSchattenWall.lean proves its fixed square-summability still admits off-line |t|<1/2. Neither side provides the missing source-derived seam bound by itself.

There is an exact positive survivor: the **chronological grade slope** resolves the two branches of work. Differentiating (1) gives

    W'(t)=2c t(1-3t²)/(1+t²)³.                        (7)

For 0<t<1 its sign is positive below t=1/sqrt(3), zero at that grade, and negative above it. Since W rises then falls strictly, the pair (W(t), sign W'(t)) determines t uniquely on (0,1), whereas W(t) alone does not. Any source realization of this repair must retain the derivative through the complete-source/Sonin limit; merely differentiating the already scalarized endpoint would assume the missing interchange. Even a successful branch label would reconstruct the grade, not supply the required seam Calkin bound.

## Audit

- Exact source-work closed form: FrankensteinSourceTailSoninPhaseWork.lean.
- Exact seam square density, convergence, and pair-energy limit: XiPrimeSeamReflectionEnergy.lean and XiPrimeSeamPairAsymptotics.lean.
- [STCSourceWorkGradeDuality.lean](../../../../formal/GaloisForLFunctions/RHTower/STCSourceWorkGradeDuality.lean) formalizes the rational involution, work invariance, and factorization of the actual complete-source/Sonin work through that profile. Its leaf passed `lake env lean` and is wired into the RHTower umbrella without an umbrella build. Strict seam-energy monotonicity, edge asymptotics, and the no-factor-through-work consequence remain paper-only.
- Deep corpus searches for a direct source-work/seam-energy bridge were partial and found the two components but no exact duality comparison. No external priority claim is made.

## Log

- 2026-09-27: duality, strict monotonicity, both edge limits, outer-edge asymptotics (5)–(6), slope (7) and the Bockstein budget no-go formalized unconditionally (`STCSourceWorkGradeDuality.lean`, `STCSourceWorkSeamEnergy.lean`); certificate `stc-source-work-grade-duality-formalized.md`; moved to stage 3.
