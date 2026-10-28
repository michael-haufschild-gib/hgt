# Fable review: the RH programme read as one problem

Status: 28 October 2026, corpus commit `389e3f1d10` plus the working tree. Evidence: the five review documents, the programme list, and corpus searches with inspection of Lean statements and module docstrings. No builds, no audits. **[L]** integrated Lean, **[S]** working source, **[E]** external claim, **(inference)** my conclusion. Research record: [working log](../../../logs/fable-review-2810-research-2026-10-28.md).

Companions: [frontier map](../rh-current-frontier-map.md) · [killed routes](../rh-killed-routes.md) · [route obstacles](route-obstacles.md) · [walls](walls-ledger.md) · [unification](route-unification-ledger.md).

## 0. The one-paragraph reading

The corpus has turned RH into a single inequality and proved that there is no way around it. Every one of the 31 routes and 17 candidates is an exact receiver; the receivers differ only in coordinates. The one unproved producer is the sign of the signed prime source at the critical scale, read against the derivative of a test: by the ordered Chebyshev identity the off-diagonal of the complete Weil form is
\[
W(f,g)=-\int_0^\infty\big(e^h-\psi(e^h)-c\big)\,q'_{f,g}(h)\,dh-\Gamma_{\rm tail}(f,g),
\]
and the selection theorem says that no inequality blind to the difference between \(\Lambda\) and its sign twins can ever reach an RH-complete family. So the three walls are one wall seen from three sides: Wall 1 asks for the inequality, Wall 3 asks in which topology it survives, Wall 14 asks what structure could force it. The corpus's deepest discoveries are not routes but *measurements of the wall*: the selective margin is exactly \(2\log 2\); narrow positivity ends at a quarter of the Robin–Euler point; the atomic receiver reaches width \((\log\log N)^{1+\varepsilon}/N\) and stops there for a quasi-analyticity reason; the cross-level prime coupling is almost periodic and can never be paid as a summable cost; finite off-line support is a proper stratum, equivalent to five different bounded quantities, and strictly harder than both a zero-free strip and the Lindelöf hypothesis; the census of critical zeros sits at the pair-correlation threshold with an exactly computed budget for 75%.

The answers below follow from this reading. Short form: (1) no circumvention is possible, but the wall can be attacked as a *structure* rather than as an *estimate*; (2) every wildly different approach relocates the selective sign, and the only approach that converts a weaker statement into RH is an effective finiteness theorem; (3) finitely many off-line zeros is a Lindelöf-strength statement with one dynamical formulation worth pursuing; (4) quasi-RH with any fixed constant has no internal producer, and the value \(7/8\) is set by an external mean-value input the corpus does not own; (5) 75% on the line is, by the corpus's own calibration, exactly the parity barrier for prime pairs, so it needs either a parity-breaking averaged input or a higher-order inertia certificate; (6) three questions; (7) the field the walls are asking for is a Krein–Toeplitz theory of Hermitian kernels on the multiplicative group of positive rationals, with the Hodge defect as negative index.

## 1. What the corpus has established, in prose

### 1.1 The receivers are complete

For every route the RH endpoint is a proved equivalence [L]: critical energy, coprime cross-work, cumulative energy, the one-sided count \(\psi(x)-x\le C\sqrt x\log^2x\), Abel moments, history floors, Möbius half-power cancellation in every dictionary, theta and heat signs, Jensen/Laguerre signs, Ward caps, Li/Cayley-ladder sign, Suzuki first variation, Haar approximation, Robin/Nicolas, Hodge index of the scaling surface, Hecke invariance of the collided form, section counts with Riemann–Roch and Bézout, canonical energy \(\mathcal E_{\rm crit}\le Q_*\), atomic positivity at widths \((\log\log N)^\alpha/N\) for every \(\alpha>1\). Nothing in the frontier is a missing dictionary. This matters for what follows: a new idea that ends in a new equivalence is not progress.

### 1.2 The producer is selective and its size is known

The selection theorem [L] (`atomicPositiveAt_iff`): a bounded weight \(|\lambda|\le\Lambda\) is eventually positive on an overlapping atomic family at some root iff RH holds and \(\lambda=\Lambda\) on \(n\ge2\). Hence every proof must use a property \(\Lambda\) has and every sign twin lacks. The corpus has identified what that property is at the level of the explicit formula: the pole product \(A(f)B(g)\), the only term growing across scales, is cancelled by the prime main term \(e^h\) in \(e^h-\psi(e^h)\). For the Liouville twin the prime sum is \(\approx-e^h\) and for characters \(o(e^h)\). Pole cancellation is the arithmetic signature of \(\zeta\): it is holomorphy of \(\xi\) in the strip, not the functional equation (over-regular Beurling systems with off-line zeros exist [L]; the functional equation forbids decaying count errors [L]).

The size of the selective input is measured [L]: on the pole hyperplane \(\sum x_n/\sqrt n=0\) the prime form of \(\zeta\) has gap exactly \(2\log2\) (the Poincaré constant of the multiplicative walk), the Liouville twin has gap \(0\), every sign gauge has gap \(\le2\log2\), and the first excitation is conductor \(2\). This margin buys positivity at widths up to \(K_\star\approx0.108\) of the atom spacing [S], a quarter of the Robin–Euler point where the Markov form must go negative [L]; beyond that point the atomic sign is a Markov gap on the pole complement plus one affine scalar [S].

### 1.3 The strata, as proved

The chain below is the corpus's most valuable organizing fact, and it is in Lean:
\[
\mathrm{RH}\iff\mathcal E_{\rm crit}\le Q_*\ \Longrightarrow\ \mathcal E_{\rm crit}<\infty\iff\text{finite off-line support}\ \Longrightarrow\ \text{zeros approach the line}\ \Longrightarrow\ \mathrm{LH}\ \wedge\ \Theta<1 .
\]
Finite off-line support is equivalent [L/S] to: a bounded integer-log spline index; bounded damped source work; vanishing dyadic work increments; a subtracted prime lag bounded on one side; uniformly bounded cosine-shift defects; uniformly bounded nonreal zero counts of the heat flow \(H_t\) as \(t\downarrow0\); bounded horizontal collision charges of windows; a finite Hodge defect of the scaling surface. The Index Exit adds the identity \(\sum_{s>t}C(s)=2(D+E)\) between the total collision mass of the heat flow after time \(t\) and the Hodge defect \(D\) [S], and RH is \(D<2\). "Zeros approach the line" (for every \(h>0\) only finitely many zeros with \(|\beta-\tfrac12|>h\)) is unconditionally equivalent to LH together with finiteness of the nonreal zeros of every cosine shift \(\cos(hD)\Xi\) [L].

### 1.4 The structural facts that are new

Relative to the literature as I know it, these corpus results are new mathematics, not reformulations:

- the selection theorem and the exact margin \(2\log2\) with the Robin–Euler ceiling \(\log N-\gamma\) [L];
- the dyadic multiresolution of the complete source with prime two as the unilateral shift, and the split of the cross-level coupling into pole (rank two, removable), Gamma (\(\pi4^{-(d-1)}\), summable), touching (bounded) and Chebyshev (almost periodic, never summable) [L/S];
- the uniform finite-index chain for every prime layer except the first [S], with the exact divergence \(\sum_p\log p/\sqrt p\) marking where twin-blind payment ends;
- the Denjoy–Carleman receivers and their quasi-analytic boundary at \(\alpha=1\) [L] (inference for the boundary);
- the canonical energy \(\mathcal E_{\rm crit}\) with its finiteness and RH thresholds and the quadratic cost of index [S];
- the coalescence blind spot: at bandwidth one no functional of the summed Gram and the zero count can certify more than \(2/3\), and the two routes to \(3/4\) with the exact budget \(1/18\) at bandwidth \(4/3\) [L];
- the functional-equation count-fluctuation theorem and the Beurling counterexamples [L];
- the Gamma boundary rigidity (norm \(\pi/2\), never attained, no uniform relative reserve) [S].

## 2. Question 1: a mechanism that circumvents or destroys a wall

### 2.1 Circumvention is impossible; this is a theorem

Any route that ends in a positivity statement on an RH-complete family meets the selection theorem. Any route that ends in a growth statement (strip, lag, Abel moment, Mertens) meets the same thing in another currency, because the strip dictionaries are exact and the Liouville twin satisfies every twin-blind estimate. There is no fourth wall and no way between the three: Wall 3 is where the selective margin must be carried (from narrow widths to overlap), and Wall 14 is where it must come from. "Circumventing the walls" would mean proving RH by an inequality true for the Liouville twin, which the corpus has shown is impossible.

### 2.2 What destroying a wall means

To destroy Wall 1 is to produce one parity-breaking estimate at the critical scale. The inventory of parity-breaking mechanisms known in mathematics is short, and the corpus has tested most of them:

| Mechanism | Breaks parity by | Reach | Corpus status |
|---|---|---|---|
| Holomorphy of \(\xi\) and the simple pole | pole cancellation \(e^h-\psi(e^h)\) | de la Vallée Poussin and Vinogradov–Korobov regions; no fixed strip | the organizing identity; VK formalized [L] |
| Reality of Hardy's \(Z\), Laguerre–Pólya structure | functional equation of degree one | real-rootedness receivers; automatic hyperbolicity only at high degree | LA, WD, HCF, TH; KR-JPR |
| Cohomological finiteness plus Rankin tensor powers (Deligne) | the \(L\)-function is a polynomial | RH over \(\mathbb F_q\) | ACS/HF; Wall 14.37: over \(\mathbb Z\) the count is RH |
| Bilinear (Type II) sums | second multiplicative structure | primes in thin sets, no square-root precision | Vaughan dictionaries: a uniform power saving is a strip |
| Landau positivity of \(\zeta_K\), Deuring–Heilbronn repulsion | nonnegative coefficients of a product | at most one exceptional real zero | not in the corpus |
| Spectral positivity (Selberg, Kuznetsov) | self-adjointness of the Laplacian | eigenvalue gaps, Kloosterman cancellation on average | KR-AUT, KR-SEL: \(\zeta\) zeros are scattering poles |
| Diophantine incommensurability of \(\{\log p\}\) | Baker-type independence | removes aliasing, \(+10^{-8}\) in the census | IGP, BGG |
| Pair correlation of zeros (Montgomery) | zeros repel at \(|\alpha|\le1\) | proportions, not individual zeros | Zeta23 census, unconditional \(F(\alpha)\) on \((0,1)\) [L] |

Only the third row reaches square-root precision, and only because the global object is finite-dimensional. That is the whole content of Wall 14 over \(\mathbb Z\).

### 2.3 Three attacks on the wall as a structure

I see no estimate that the corpus has missed. I see three ways to change what is being estimated.

**M1. Pole repulsion, read as Deuring–Heilbronn.** The classical zero-free region is the pole at \(s=1\) repelling zeros, with the repulsion weakened by the archimedean growth \(\log t\). In atomic coordinates this is literally the corpus's picture: the pole vector \(x_n=n^{-1/2}\) is the one hyperbolic direction, its complement is the harmonic hyperplane, and the prime form's ceiling \(\log N-\gamma\) is the Robin–Euler constant while the selective margin \(2\log2\) is bounded. A fixed strip is a height-uniform pole repulsion; the margin is its finite-horizon shadow. The Deuring–Heilbronn phenomenon is the only mechanism in the literature that produces "finitely many exceptions" statements, and it works through an explicit formula with a *positive kernel* and an exceptional zero of the opposite sign. Nothing in the corpus has tried to let an off-line zero play the exceptional role: a zero \(\rho_0=\beta_0+i\gamma_0\) with \(\beta_0>\tfrac12\) contributes \(x^{\rho_0}\) to every explicit-formula reading and must be paid by the pole product and the other zeros. The corpus's quadratic cost law (index \(k\) costs \(\mathcal E_{\rm crit}\ge50k^2-3k/2\)) is a repulsion statement among off-line zeros: each new quartet costs more than the last. What is missing is the same statement with an *arithmetic* ceiling, and I do not see one. Verdict: M1 clarifies Walls 1.0 and 1.18 as one object; it does not supply the uniform estimate.

**M2. The Hodge defect as Krein–Langer index.** The signed Weil Gårding bound gives finite negative index at every aperture [L], and finite off-line support is uniformly bounded index. Krein–Langer theory classifies Hermitian kernels on \(\mathbb Z\) with \(\kappa\) negative squares: a positive measure on the circle plus \(\kappa\) reflected pairs of points off the circle. Along the orbit of one Hecke translation the Weil form is a Toeplitz form whose symbol is the zero measure pushed to the circle by \(\gamma\mapsto\gamma\log p\) (unification ledger, inference), so the off-line zeros are exactly the off-circle Krein–Langer points. This converts the finite-support stratum from an inequality into a structure theorem (see §4), and it gives the right notion of convergence for Wall 3: Pontryagin spaces of bounded index, not \(L^2\). The corpus already has Krein and Pontryagin modules and the one-prime Stepanov module; the missing step is to make the Krein–Langer decomposition the *definition* of the finite-support stratum and to compute its index from the prime side.

**M3. Multivariable Toeplitz positivity on the Bohr torus.** The explicit-formula kernel is a function on the group \(\mathbb Q_+^\times\cong\mathbb Z^{(\infty)}\): \(K(r)=\) pole term \(-\) prime term \(-\) archimedean term at the rational point \(r=n/m\). Its Fourier coefficients on the dual, the Bohr torus \(\mathbb T^\infty\), are \(\sum_\rho r^{\rho-1/2}\). RH is the statement that the Bohr lift of the zero divisor \(\gamma\mapsto(p^{i\gamma})_p\) lands on the torus, equivalently that \(K\) is positive definite on \(\mathbb Q_+^\times\) with the diagonal regularized by atom width (the atomic receivers are exactly this regularization). Positivity on each cyclic subgroup \(p^{\mathbb Z}\) is one-prime Toeplitz positivity; the corpus has proved that one grid aliases while two grids decide (HCF), and that one prime suffices for the strip and RH criteria. So the content of RH is a local-to-global principle on the lattice: positivity on finitely many coordinate circles versus positivity on \(\mathbb T^\infty\). This is a known hard subject (multivariable Fejér–Riesz fails; Dritschel-type sums of squares exist only for strictly positive symbols), and it is where the corpus's "signed Chebyshev cross-level work" lives. Verdict: M3 is the right language for Wall 3.32 and gives a clean research object (§7); it is not an estimate.

### 2.4 Verdict on Question 1

No new estimate. The honest opportunity is to stop treating the finite negative index as a defect to be bounded and start treating it as a Krein–Langer invariant to be computed from primes, and to put the cross-level prime coupling where it belongs, in multivariable Toeplitz theory on the Hecke lattice. Both are reorganizations, both are new theorems to prove, and both pass the selectivity test by construction (twins have infinite index).

## 3. Question 2: a wildly different approach

### 3.1 What has not been tried

Set against the literature, the corpus's coverage is close to complete: Weil positivity in every coordinate system, Nyman–Beurling, Li, Jensen/Laguerre–Pólya, heat flow, Lee–Yang, Hilbert–Pólya realizations, Lax–Phillips, Deninger, Connes–Consani, de Branges, Robin/Nicolas, Farey, Riesz and Hardy–Littlewood criteria, Speiser, universality and recurrence, Beurling systems, finite-field calibration, mollifiers, pair correlation. Not tried: Turán's partial-sum approach (dead since Montgomery's theorem that partial sums have zeros right of \(\operatorname{Re}s=1\)); Deuring–Heilbronn (above); random multiplicative models (twin-blind by construction); model-theoretic or o-minimal definability (no handle on zeros); arithmetic topology. None of these carries a parity-breaking input at square-root precision.

### 3.2 Two genuinely different endgames

**E1. Effective finiteness closes RH by computation.** The finite-support stratum is treated in the corpus as an intermediate. It is not, if effective: every receiver of finite support with an explicit height horizon \(T_0\) states that all zeros above \(T_0\) are on the line, and RH below \(T_0\) is verified numerically to heights far beyond any horizon the heat flow produces at fixed \(t\). The corpus's horizons are already effective (\(2\pi e^{(27/40+\varepsilon)/t}\) for \(0<t\le1/8\)). This is the only known route on which a weaker statement becomes RH without further analysis: a \(t\)-uniform horizon is not an intermediate result, it is the proof. The whole difficulty is that the horizon grows like \(e^{c/t}\), and the corpus's reality-horizon mechanism (Lindelöf chords for \(\mu(\sigma)\)) cannot remove the \(1/t\).

**E2. The window picture.** At height \(t\), the approximate functional equation makes \(\xi\) a Dirichlet polynomial of length \(\sqrt{t/2\pi}\) in the Bohr variables, with about \(\log t\) zeros per unit window. RH on a window is a statement about the zeros of a trigonometric polynomial of \(\sqrt t\) frequencies restricted to the Bohr curve \(t\mapsto(p^{-it})_p\). Bombieri–Hejhal showed that for linear combinations of \(L\)-functions with the same functional equation the zeros lie on the line asymptotically under RH and spacing hypotheses; the corpus's W1C candidate names the Bohr-torus Lee–Yang lift as its natural landing. A theory that located zeros of such polynomials on the Bohr curve from the structure of the curve (Kronecker density plus the functional equation) would be new. It would still have to be selective: the Liouville twin has no functional equation of this form, so the mechanism is not twin-blind. I rate this as the one genuinely different *landscape*; I do not see its first theorem.

### 3.3 A different object: the prime point process at window scale

The atomic receivers say RH is equivalent to positivity of \(W\) on families of atoms at the integers \(n\le N\) with width \((\log\log N)^{1+\varepsilon}/N\): windows of length \((\log\log N)^{1+\varepsilon}\) around each integer, far below the average prime gap \(\log N\). On such a family the prime form reads the positions of individual primes against the archimedean kernel. So RH is a statement about the point process of primes at a scale where each window holds at most one prime: the positions of primes are "positive definite relative to the Gamma kernel". This reformulation is in the corpus implicitly; stated this way it suggests importing the theory of point processes with repulsion (determinantal and Pfaffian processes, rigidity), where positive-definiteness of pair kernels is the defining property. I do not know a theorem there that is selective.

### 3.4 Verdict on Question 2

Every different approach relocates the selective sign; none avoids it. The one approach that changes the logical shape of the problem is E1, effective finiteness, and it is the subject of the next question.

## 4. Question 3: only finitely many off-line zeros

### 4.1 Status in Lean

Finite off-line support is equivalent [L/S] to each of: \(\mathcal E_{\rm crit}<\infty\); bounded spline index on every finite set of log shifts; the subtracted lag \(\psi(x)-x+\operatorname{Re}\sum_{q\in S}x^q/q\) bounded on one side for some finite \(S\); uniformly bounded cosine-shift defects; \(\sup_{t>0}N_{\rm nonreal}(H_t)<\infty\); bounded horizontal collision charges of windows; finite Hodge defect. It implies "zeros approach the line", hence LH and \(\Theta<1\), hence Möbius and prime power savings in short windows [L]. It is RH with finitely many exceptions, strictly stronger than quasi-RH and than Lindelöf; by Landau's one-sided principle its one-sided lag form is equivalent to its two-sided form.

### 4.2 Hardness

The stratum sits above both QRH and LH. Every analytic method that produces density statements (Ingham, Huxley, Guth–Maynard, all formalized [L]) gives \(N(\sigma,T)=o(T)\) for \(\sigma>\tfrac12\) and never finiteness; the gap between "density zero" and "finite" is the gap between almost all and all, and no known mechanism crosses it except Deuring–Heilbronn for real zeros. So there is no cheap opportunity. There are three structural ones.

### 4.3 Opportunities

**(a) The collision calculus.** The Index Exit identity \(\sum_{s>t}C(s)=2(D+E)\) [S] says: the number of off-line zeros is the number of collisions of the de Bruijn–Newman flow over all positive time. Collisions occur only for \(t\le\Lambda\) (the de Bruijn–Newman constant, \(\Lambda\ge0\) by the infinitely many nonreal zeros at negative time [L], \(\Lambda\le0.2\) in the literature; all zeros real for \(t\ge1/8\) in the corpus normalization [L]). The nonreal count \(N(t)\) is finite for every \(t>0\) and antitone [L]. The question is \(\sup_t N(t)<\infty\). The corpus's horizon gives \(N(t)\le e^{c/t}\); any sub-exponential bound \(N(t)\le e^{o(1/t)}\) would be new mathematics (it would say that off-line zeros are sparser than the Gaussian smoothing scale), and a bound polynomial in \(1/t\) would mean the collision times \(t_k=\delta_k^2/2\) (for isolated pairs the displacement squared decreases linearly, `riemannHeat_upper_energy_le`) accumulate at \(0\) only polynomially. Finite support is \(\sum_k1<\infty\). The dynamical formulation is the only one in which the off-line zeros are counted by events rather than by sizes, and the only one with an effective endgame (§3.2).

**(b) The Krein–Langer decomposition along one prime.** By M2, finite support is the statement that the dyadic Chebyshev sequence \(d\mapsto W(f,T_{d\log2}g)\) has finitely many negative squares uniformly in \(f,g\); Krein–Langer says such a sequence is positive-definite plus finitely many hyperbolic exponentials, which is exactly the subtracted-lag receiver. The new content would be a structure theorem *with an estimate of \(\kappa\)*, and the corpus already has the estimate in energy form: \(\kappa\le\mathcal E_{\rm crit}/Q_*\)-type bounds from the quadratic cost. So finite support reduces to bounding \(\mathcal E_{\rm crit}\), the damped second moment of the centered prime error at the critical scale. That is the WL route's energy, and it is \(\ge\)QRH. No shortcut, but a single clean target.

**(c) Repulsion with the pole as agent.** M1 above. An off-line zero at height \(\gamma_0\) and displacement \(\delta\) contributes \(2x^{1/2}\cos(\gamma_0\log x)x^{\delta}\) to \(\psi(x)-x\); the explicit formula with a positive kernel concentrated at scale \(\gamma_0\) in the test variable must pay this against the pole and the other zeros. Deuring–Heilbronn in Heath-Brown's form makes exactly such a computation for a Siegel zero. I do not know whether an off-line zero of \(\zeta\) can be made to repel, but this is the one classical mechanism that outputs "finite exceptions", and the corpus has not tried it.

### 4.4 Verdict on Question 3

No mechanism gives finiteness short of a Lindelöf-strength input. The opportunity is to make finiteness effective in the heat-flow formulation, because there and only there a finiteness theorem is a proof of RH.

## 5. Question 4: quasi-RH with better constants

### 5.1 Status in Lean

Every fixed strip has an exact dictionary [L]: \(\Theta\le1-\theta\) is equivalent to the escaped-Möbius rate, the all-test Hecke-defect cap, the dyadic defect rate \(1-2\theta\), \(\operatorname{Re}\xi'/\xi\ge0\) on \(\operatorname{Re}s>1-\theta\), the quotient-head exponent at any power cutoff, the finite-contact Suzuki exponent, the Möbius-divisor Abel exponent; \(\Theta<1\) is equivalent to a uniform Vaughan power saving; a strip of width \(1/k\) is a power saving \(1/k^2\) in the smoothed \(k\)-free count [L]; and the strip \(\Theta\le\tfrac12+x_0\) is the nonnegativity of about \((\tfrac12-x_0)\log t\) derivatives per height of \(\xi(\tfrac12+x+it)\xi(\tfrac12-x+it)\) at \(x_0\) [L]. Unconditionally the corpus has Vinogradov–Korobov in several forms, the zero-free region for \(|\operatorname{Im}s|<4\), and the Guth–Maynard density exponent \(30/13\) under its large-value estimate [L]. No producer of any fixed strip exists in the corpus.

The external claim [E] is Dirichlet zero-freeness for \(\operatorname{Re}s>7/8\). The intake (279 modules) formalizes the zero detector as the \(L\)-series of a truncated Möbius twist, Lemmas 3.3, 4.1, 4.2, 4.5, 6.2, Propositions 4.6 and 5.1, and the exponent arithmetic consolidating \(q^{7(1-\sigma)/3}T^{2(1-\sigma)}\) and \((qT)^{30(1-\sigma)/13}\) into \(2(qT)^{7(1-\sigma)/3}\). The analytic anchor is proved only for \(\operatorname{Re}s>1\); the continuation and contour step is unformalized. The collision no-go [L] shows a fibre-separated CGL packet cannot carry horizontal reflection charge (reflection preserves ordinates, so two reflected rows collapse) and that the Proposition 4.6 envelope has floor \(288\) against the collision quantum \(2\): the method cannot reach the RH endpoint, whatever the strip.

### 5.2 Where \(7/8\) comes from and what would move it

The corpus owns none of the inputs that set the constant. The constant is fixed by the family mean value the detector is tested against and by the density exponent (the formalized consolidation uses exactly the \(7/3\) and \(30/13\) exponents). Improving the constant means improving the large-value estimate for the detector polynomial in the family; the corpus formalizes Guth–Maynard's corollaries [L] but has no sharper large-value theorem. I will not speculate on the internal exponent balance of a manuscript I have not read.

### 5.3 Opportunities

1. **Finish the capstone as import, not research.** The continuation step is the only gap; once closed, the dictionaries cascade for \(\zeta\) at \(\theta=1/8\): \(\psi(x)-x\ll x^{7/8+\varepsilon}\), \(M(x)\ll x^{7/8+\varepsilon}\), the escaped-Möbius rate, the \(8\)-free count saving \(1/64\), a uniform Vaughan saving \(n^{7/8}\), \(\operatorname{Re}\xi'/\xi\ge0\) on \(\operatorname{Re}s>7/8\), and nonnegativity of the first \((\tfrac18+\varepsilon)\log t\) off-centre derivatives at \(x_0=3/8\). Each is a finite instantiation.
2. **A strip receiver at atomic widths.** The RH receiver lives at widths \((\log\log N)^{1+\varepsilon}/N\); the strip dictionaries live in Möbius and Vaughan currencies. Missing is the natural bridge: an atomic receiver for \(\Theta\le1-\theta\) at widths \(N^{-(1-2\theta)}\)-type, i.e. positivity of the Weil form on atoms whose width grows with the allowed displacement. The off-centre derivative criterion is the height-side version. With it, a strip becomes a positivity statement on *wide* atoms, where the prime form's bottom spectrum (the adjunction energies \(E_m=\gamma+\log m+d(m)\) [S]) is explicit, and one could test whether the known arithmetic modes already certify some strip. I expect not, but it would locate the first place where the Robin–Euler ceiling, not the archimedean growth, is the obstruction.
3. **Better constants.** Any improvement of \(7/8\) by the external method is a large-value problem for Dirichlet polynomials over a character family; the corpus could contribute the formalized large-sieve and dispersion tools (BVI, Guth–Maynard box), nothing more.

### 5.4 Verdict on Question 4

Internally no. The quasi-RH stratum has no producer in the corpus and the strip dictionaries are already exact. The constant \(7/8\) belongs to an external mean-value input; improved values would come from improved large-value estimates in that family, which is standard analytic number theory and not where the corpus's strengths lie.

## 6. Question 5: at least 75% of zeros on the line

### 6.1 Status in Lean

Imported Alpöge–Furman (`Zeta23`): at least \(2/3\), and \(HD(1)=0.6725007\ldots\) with the Montgomery–Taylor window, of zeros simple and on the line; the corpus extends to \(0.67250071\) [L], \(4/5\) of ordinates critical [L], off-line copies \(\le1-HD(1)\), and \(3/4\) of copies within \(4/\log T\) of the line (near, not on) [L]. The mechanism is a Sylvester inertia inequality on the evaluation Gram \(\hat A=P+Q\): the \(c=2\) rank–trace form has capacity \(2-\kappa\), \(\kappa\) the normalized Frobenius norm computed from Montgomery's \(F(\alpha)\) on \(|\alpha|\le1\), which the corpus has unconditionally [L]. At bandwidth \(\lambda=1\), \(\kappa=4/3\) and the coalescence blind spot is exact: a double critical zero and a coalesced off-line pair give the same Gram, so no functional of \((N,\operatorname{tr}\hat A,\|\hat A\|_F^2)\) certifies beyond \(2/3\) [L].

Two routes to \(3/4\) are formalized as conditional theorems [L]:

- **Zero side.** The joint \((c=2,c=3)\) functional equals \(((7-3\kappa)/4)N=\tfrac34N\) at \(\kappa=4/3\); a zero-side spectral slack of \((\tfrac34-H(\lambda))N\), \(H(\lambda)\to\tfrac1{12}\) as \(\lambda\to1^-\), gives \(3/4\). The slack is the on-line Parseval excess \(\|P\|_F^2-2\operatorname{tr}P+\operatorname{rank}P\) plus the negative-part credit \(2\operatorname{tr}Q_-\), positive iff some off-line pair contributes a genuine negative square on the probe window.
- **Prime side.** At bandwidth \(4/3\) (\(X=(T/2\pi)^{4/3}\)), the diagonal and archimedean part of \(\|\hat A\|_F^2\) is unconditionally \(43/36\) of the normalization, the prime–pole cross term is \(O(T^{5/6}\log^2T)\), and \(3/4\) follows iff the prime surplus (off-diagonal prime pairs, sum frequencies, grid end correction) is at most \(1/18\) of the normalization (`SurplusFourThirds`). In form-factor language the surplus ratio is \((2/\lambda^2)\int_1^\lambda(\lambda-\alpha)(F(\alpha)-\alpha)\,d\alpha\); Hardy–Littlewood (\(F\equiv1\)) gives \(-1/144\) and \(13/16\); a uniform bound \(F\le\Upsilon\) on \([1,4/3]\) certifies \(7/8-\Upsilon/16\); \(3/4\) iff \(\Upsilon\le2\) [L].

### 6.2 The arithmetic content of 75% (inference)

The weight \(\lambda-\alpha\) in the surplus is largest at \(\alpha=1\): primes near \(T\) with *bounded* shifts. The form factor on \([1,4/3]\) is the Hardy–Littlewood correlation of primes at shifts from \(O(1)\) up to \(n^{1/4}\), and the bounded shifts carry most of the weight. For a bounded shift the only unconditional upper bounds are sieve bounds with a constant \(\Upsilon\) in Hardy–Littlewood units; the best known is about \(3.4\) (Wu, from memory, not corpus-verified), and the parity barrier forbids any sieve from going below \(2\). Inserting \(\Upsilon=3.4\) in the corpus's calibration gives \(0.6625\), below the \(2/3\) already known by the \(|\alpha|\le1\) route; \(\Upsilon=10/3\) recovers \(2/3\); \(\Upsilon=2\) is exactly \(3/4\). So, in the corpus's own calibration, **75% on the line is the parity barrier for prime pairs at bounded shifts.** This is a sharp and, I think, new placement of the \(3/4\) problem: it is not a better mollifier, it is twin primes on average with the sieve constant at parity.

### 6.3 Opportunities

1. **Higher-order inertia from unconditional \(n\)-level correlations.** The \(2/3\) theorem uses only the second moment \(\|\hat A\|_F^2\). The next invariants are \(\operatorname{tr}\hat A^3,\operatorname{tr}\hat A^4\), whose prime-side inputs are the \(3\)- and \(4\)-level correlations of zeros at sub-threshold support. The corpus proved the pair correlation unconditionally for complex ordinates; the same method (entire test functions, explicit formula, diagonal only) should give the \(n\)-level correlations at supports \(\sum|\alpha_j|<1\) unconditionally. Whether a higher inertia inequality certifies more than \(HD(1)\) is a finite computation on block models (the corpus has the block-data machinery). This is the one route to the census that does not meet the parity barrier, because it stays below the threshold on the prime side.
2. **Mixed certificates.** The IGP slack (\(+10^{-8}\)) and the ordinate census (\(4/5\)) show that incommensurability and distinctness add. A certificate mixing distinct-count, simple-count and near-line information with the Montgomery–Taylor window has not been optimized as one semidefinite programme; the corpus's exchange-rate laws make it a finite problem. Expect small gains, not \(3/4\).
3. **The mollifier route** (Levinson–Conrey, \(2/5\to5/12\) on the line) is parity-neutral and independent; the hybrid "Hermitianized mollified moments" (walls Q3) is the natural second main term. Under RH it is \(19/27\) (Bui–Heath-Brown); unconditionally nothing is formalized.

### 6.4 Verdict on Question 5

Not by the prime side without breaking parity on average over shifts of size up to \(n^{1/4}\), which is Hardy–Littlewood strength. The zero-side higher-inertia route is the only one with unconditional inputs in reach, and its ceiling is unknown. Target \(0.70\) before \(0.75\).

## 7. Question 6: the three questions

The corpus's own priorities (Q1 selective positivity past Robin–Euler, Q2 first-layer compactness, Q3 a second main term for the census) are the right strata. I would sharpen each into a question with a finite first step and a Lean-ready receiver.

**Q-I (the sign). Selective Toeplitz positivity at bounded overlap, one generator, prime two.** Fix a smooth profile and the pole-complement coordinates. For overlap ratio \(\rho\in(1,1.2)\) and \(N\le10^6\), compute the dyadic Toeplitz matrices \((W(f_j,T_{(k-j)\log2}f_k))_{j,k}\) of the complete source on the pole complement, with the pole removed by \(\sum_jc_j2^{-j/2}=0\), the Gamma coupling \(\pi4^{-(k-j-1)}\) and the touching cost explicit, and the Chebyshev coupling read from \(\psi(2^dx)-2^dx\). Locate where positivity first fails and which lags carry the failure. Then prove the sign at that overlap from the Chebyshev identity using only Brun–Titchmarsh and the prime number theorem in short intervals. Why this question: it is the first point past the Robin–Euler threshold, the arithmetic enters only through \(\psi\) on bounded windows around the integers \(n\le N\), and the selectivity test is built in (the Liouville twin must fail at the same overlap). Receiver: `TheHodgeIndexIsAGapOnThePoleComplementAndOneScalar`.

**Q-II (finite support). A \(t\)-uniform collision bound for the heat flow.** Prove \(N_{\rm nonreal}(H_t)\le e^{o(1/t)}\) as \(t\downarrow0\), then polynomial, then bounded. The receiver is `finite_nonreal_zeros_iff_exists_nonrealZeroCount_le` and the Index Exit identity; the tools are the energy transition law (displacements decrease by \(2t\)), the KKL horizon with its Lindelöf chords, and the quadratic cost law. Why this question: it is the only formulation of finite support in which the obstacle is a dynamical count, not an arithmetic sum, and it is the only route whose success is effective and therefore closes RH by computation.

**Q-III (the census). Unconditional \(n\)-level correlations below threshold and the higher inertia certificate.** Prove the \(3\)- and \(4\)-level correlation sums of \(\zeta\) zeros for test functions with Fourier support in \(\sum|\alpha_j|<1\), with complex ordinates, by the corpus's pair-correlation method; then determine the best proportion certified by inertia inequalities using \(\operatorname{tr}\hat A^k\), \(k\le4\), on the block models. Why this question: it is the one census route with unconditional inputs, it does not touch the parity barrier, and its answer is a number.

I would not list a fourth. The quasi-RH stratum has no internal producer, and the structural programmes (M2, M3) are the subject of the next section rather than questions with a first step.

## 8. Question 7: the field the walls are asking for

### 8.1 What the walls demand

Wall 1 demands a positivity theorem that sees multiplicativity (selectivity). Wall 3 demands a notion of convergence under which indefinite forms with bounded negative index are closed. Wall 14 demands a construction whose output is a positive-definite kernel. All three are statements about one kind of object: a Hermitian kernel on a group, with a finite number of negative squares, covariant under a semigroup of translations. Mathematics has a theory of exactly this on \(\mathbb Z\) and \(\mathbb R\) (Krein–Langer, Pontryagin spaces, Toeplitz and Hankel operators, Nevanlinna classes), and almost none of it on the group that matters here.

### 8.2 The field: Hecke-covariant Krein–Toeplitz theory

**Point of view.** RH is a property of a kernel, not of a function. The kernel is the explicit-formula pairing \(K_\Lambda\) on the multiplicative group of positive rationals \(\mathbb Q_+^\times\cong\mathbb Z^{(\infty)}\) (one coordinate per prime), with the archimedean term as a regularization at the identity. Its spectral measure is the zero divisor lifted to the Bohr torus \(\mathbb T^\infty\) by \(\gamma\mapsto(p^{i\gamma})_p\). On-line zeros are mass on the torus; off-line zeros are reflected pairs of points off the torus, the negative squares of the kernel. The pole is the single hyperbolic direction. The primes act by translation, and the Hecke semigroup is the structure group.

**Objects.** The Hecke lattice and its Bohr dual; Hermitian kernels on it with finitely many negative squares and their Pontryagin GNS spaces; the explicit-formula kernel and its deformations (aperture, heat, cosine shift, damping, twists by gauges \(\omega\)); the energy functionals that price negative squares (\(\mathcal E_{\rm crit}\), source work, collision mass); the one-prime restrictions (Toeplitz forms with symbol the pushed zero measure) and the finite-prime sublattices; the twin orbit \(\{\omega\Lambda\}\) as the control family.

**Language.** Positive-definiteness on discrete groups (Bochner, Herglotz), negative index and Krein–Langer decompositions, Toeplitz and Hankel symbols, multivariable Fejér–Riesz and sums of squares on the torus, Poincaré and Gårding inequalities for the multiplicative walk, Sylvester inertia of evaluation Grams, Denjoy–Carleman regularity of test profiles.

**Foundational principles.**

1. *Selectivity.* Every theorem of the field must be false for the Liouville twin; the twin orbit is a built-in test family, and a statement that survives all twins is a dictionary, not a theorem.
2. *Index is energy.* Negative squares are not errors; each costs a quantum and the cost is superlinear. The finite-index stratum is a structure theorem with a price list.
3. *The pole is the only hyperbolic direction.* Gamma pays every detail; the pole couples levels hyperbolically and is removable by one linear condition; what remains is prime coupling, almost periodic, never small.
4. *Locality fails, one prime decides.* Positivity on a single coordinate circle does not imply positivity on the torus, yet one prime's Toeplitz form already decides RH. The content of the field is the local-to-global law on the lattice.
5. *Regularization has a quasi-analytic boundary.* The identity must be regularized by atom width, and compactly supported profiles exist only below Gevrey class one; the receivers end exactly there.

**Criteria the field must fulfill.**

- Over \(\mathbb F_q\) it must reduce to Weil: the lattice is \(\mathbb Z\), the symbol is the Frobenius spectrum, positivity is the Hasse–Weil bound and the Cayley ladder, and the local-to-global law is the square-root count (all formalized in the corpus).
- Its first theorem must be selective at a scale beyond the Robin–Euler point.
- It must contain the finite-support stratum as a Krein–Langer structure theorem with an arithmetic estimate of the index.
- It must contain the census as an inertia theorem of kernels, with higher moments as higher inertia.
- It must have a transfer theorem: a topology on tests in which bounded-index kernels form a closed set and the atomic receivers are limits.

**Research topics.**

1. Krein–Langer on \(\mathbb Q_+^\times\) with Hecke covariance: classification of kernels with \(\kappa\) negative squares and translation structure; the arithmetic index formula.
2. Multiplicative Poincaré inequalities: the walk with constant \(2\log2\) at all scales and all overlaps; the spectral theory of the prime form beyond its bottom spectrum (adjunction energies \(E_m\)).
3. Local-to-global on the lattice: how many primes certify positivity at height \(T\), and the exact aliasing law (one grid hides a pair, two decide).
4. Inertia theory of explicit-formula Grams: higher moments, \(n\)-level inputs, exchange rates, the coalescence blind spot in general.
5. Deformation theory: aperture, heat and cosine flows as index-nonincreasing semigroups; the collision calculus; effective horizons.
6. The arithmetic Stepanov problem: auxiliary sections on the Hecke lattice from a source other than a lattice of the spectrum; what replaces \(x^q-x\).
7. Transfer: Pontryagin-space limits of atomic families; the Denjoy–Carleman boundary as a theorem about the field's test class.

### 8.3 Why this is the right field and not another

The corpus has already built most of its objects (SMAP, SAHT, AID, ALG, RAPT, SSHA, the Krein and Pontryagin modules, the Toeplitz ladders, the inertia census) without naming the field. What it lacks is the organizing principle that converts the three walls into three structure theorems about one kernel. The field's test of success is the one the corpus already applies: a theorem that the Liouville twin fails.

## 9. What I would change

- Stop opening routes. The receiver inventory is complete; a new equivalence is not progress.
- Treat finite negative index as an invariant to compute, not a defect to bound (M2), and the cross-level prime coupling as a multivariable Toeplitz problem (M3).
- Pursue effective finiteness through the heat flow (Q-II) because it is the only intermediate stratum with an endgame.
- Pursue the census through unconditional higher correlations (Q-III), and record that \(3/4\) by the prime side is the parity barrier.
- Keep the selectivity battery as the acceptance test for everything.

## Appendix: Lean declarations relied on

Selection and margin: `SelectiveMultiscaleArithmeticPositivity/PositivityAtEveryRootSelectsTheVonMangoldtWeight` (`atomicPositiveAt_iff`), `TheSelectiveMarginIsTwoLogTwo` (`isGreatest_zeta_hyperplaneGap`, `hasHyperplaneGap_zero_of_mul_self_eq_one`), `RenormalizedArithmeticPotentialTheory/TheSpectralGapOfThePrimeFormIsTwoLogTwo` (`eventually_atomicWeilForm_le_two_log_two`). Couplings: `SeparatedLevelsCoupleThroughTheChebyshevError`, `ArithmeticIndexDescent/TheOrderedWeilSourceIsACenteredChebyshevDefect`. Strata: `ArithmeticOrientationGeometry/TheIndexExit` (`index_exit_first_rung_tfae`, `zetaZeroAbscissa_lt_one_of_finite_rightZeros`, `riemannHypothesis_iff_encard_rightZeros_lt_two`), `RHTower/FiniteOffLineConverse`, `RHTower/DeBruijnNonrealCountRightLimit`, `RHTower/KiKimLeeFiniteness`, `RHTower/DeBruijnNewmanNonnegative`, `RHTower/KiKimLeeInteriorLindelofHorizon`, `RHTower/DeBruijnNewmanEnergyTransition`, `RHTower/XiSliceEventualPositivityFiniteOffLine` (`zerosApproachLine_of_finiteOffLine`), `RHTower/LindelofCosineFiniteDefectDepth` (`lindelofCriticalLine_of_zerosApproachLine`), `RHTower/LindelofOpenImpliesCriticalLine`, `ArithmeticIndexDescent/TheWorkAndIndexHaveTheSameFiniteStratum`. Strips: `RHTower/QuasiRHQuotientHeadAndFiniteContactAbscissaLaw`, `RHTower/KFreeExponentialLadder` (`zeroFree_strip_iff_kFree`), `RHTower/XiSliceOffCentreCoeffWindow` (`exists_strip_iff_offCentre_low_order`), `RHTower/ZetaZeroDensityThirtyThirteenths`, `RHTower/MontgomeryIsolatedDensityConditional`, `RHTower/ChenGuptaLiAnalyticAnchor`, `RHTower/ChenGuptaLiZeroDensityExponents`, `RHTower/ChenGuptaLiHorizontalCollisionNoGo`. Census: `IncommensurableGaborPinching/CriticalLineZeroProportion`, `RHTower/Zeta23CriticalOrdinateCensus`, `RHTower/ZetaThreeQuartersOfSurplus` (`SurplusFourThirds`), `RHTower/ZetaThreeQuartersOfPrimeSurplus`, `ArithmeticCastelnuovoSeveri/BreakingTheCoalescenceBlindSpotAndThreeQuarters`, `ArithmeticCastelnuovoSeveri/TheTwoThirdsConstantIsPairCorrelation`, `ArithmeticCastelnuovoSeveri/CoalescentSurplusAndTransThresholdProportionLaws`, `TransThresholdPairCorrelation/CoalescentSieveAnatomyAndModelCalibration`, `RHTower/MontgomeryPairCorrelationUniform`, `RHTower/SpeiserDeficitTwoThirds`. Structure: `ArithmeticCorrespondencePositivity/SparseAnnihilatorsAndTheStepanovMechanism`, `ArithmeticLorentzianGeometry/RHIsReflectionPositivityOfTheCayleyLadder`, `RHTower/RiemannFunctionalEquationForcesCountFluctuation`, `ArithmeticPositiveDuality/BeurlingRiemannFunctionalEquationRigidity`, `SpacingScaleHarmonicAnalysis/TheMarkovFormFailsInsideTheSeparatedRegime`.
