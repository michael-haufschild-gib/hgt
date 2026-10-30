# Research frontier: work, open problems and next questions

Status: 30 October 2026, corpus `00540e1855` plus working tree. **RH remains open.**

**The corpus in one paragraph.** The Lean corpus proves the classical state of the art and goes past it:

- the Guth–Maynard large-values theorem;
- Vinogradov–Korobov with explicit constant;
- at least \(0.6725\) of zeros simple and critical, and at least \(4/5\) of zero ordinates carrying a critical zero;
- \(0\le\Lambda<1/8\).

It also proves complete Weil positivity on atomic families at every fixed overlap, and it computes the decisive invariants exactly:

- Weil-kernel index = Hodge defect = number of right zeros;
- Hecke-state positivity threshold \(=1/2\);
- typical gauge exponent \(=1/2\).

It has turned RH into exact receivers in every coordinate system it studies, about 2,400 declarations named as RH equivalences. It proves why these receivers cannot be fed by soft means:

- no monotone extension of positivity;
- producers are blind at square-root precision;
- gauge-invariant data stop at \(3/4\).

The result is a sharp diagnosis. A crossing input must be critical, square-root precise and gauge-selective at once, and nothing in the corpus is all three.

Companions: [route report](route-obstacles.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md) · [frontier map](../rh-current-frontier-map.md). [Working log](../../../logs/review-3010-rev3-deep-research-2026-10-30.md). Labels: [Lean] declaration read via the corpus search; [map] frontier map; (inference) this review. No builds were run.

## 2.1 Work that is "just work"

Each item has a working mechanism in the corpus and a proved smaller instance. None promises a sign beyond its stated range.

**Complete Weil matrix below the critical curve.**

- **A1.** Extend complete positivity, including the growing conductors \(m\le c\) and the full complement, from fixed \(c\) to the reserve range \(c\le(\log N)^{1/8-\varepsilon}\). Ingredients:
  - the explicit complete defect reserve with polynomial overlap cost (`tiltedUnitSpline_complete_defect_reserve_explicit`);
  - the conductor-scale floor (constant above the overlap scale, \(c^{-7}\) below);
  - the polynomial residual.

  The work is loss-free bookkeeping on the \(\approx c\) near-degenerate conductors.
- **A2.** Raise the uniform-in-\(c\) packet exponent from \(A<1/48\) to the growing-packet exponent \(1/40\), then toward \(1/8\).
- **A3.** Formalize the Steklov full-index exhaustion for the SRT tower branch [map].

**Moments and heat.**

- **A4.** Theta Hankel ranks nine, ten, …, by the seam-split piece certificates that settled rank eight (`ThetaCuspOddFourRankEight`). At each rank, state the result as center-flux domination via `thetaCuspNativeTailHankelForm_eq_square_sub_flux`.
- **A5.** LA/WD: absorb the \(C\log X\) outer vertical energy in localized heat dissipation and sum the local estimates at each fixed \(t>0\). The output is a better numerical upper bound on \(\Lambda\) below \(1/8\).
- **A6.** HCF: grid signs at each finite degree on the \(\log2\) and \(\log3\) grids.

**Fixed-aperture and fixed-support positivity.**

- **A7.** RW/EWU/OWU: further fixed-radius floors and odd witnesses past radii \(181/500\) and \(23/40\).
- **A8.** ACT: larger-shift absorption of fixed-support reflected-prime collars.
- **A9.** SZ: uniform-in-packet assembly of the two-Gram identity on finite prime-power packets.
- **A10.** CHMD/AIP: Gamma graph payments; Schur payment on fixed blocks; first-prime, coarse and polar Haar costs.

**Geometry and selection bookkeeping.**

- **A11.** ACS: census and displacement Gram estimates at fixed degree; quotient-measure and unfolding formalization for the automorphic branch [map].
- **A12.** Selection: exact thresholds \(c_0(\omega)\) for further finite flip families; extend the Liouville selector to complex unimodular gauges with bounded harmonic sums.
- **A13.** PW-B: remove the `XiZeroCopy` indexing from the native two-response action, i.e. restate it on source data.

**Classical layer.**

- **A14.** Push the simple-critical proportion past \(0.6725\) with the incommensurable Gabor pinching and Montgomery–Taylor machinery.
- **A15.** Sharpen zero-density exponents inside the formalized Guth–Maynard framework; refine the \(4/5\) ordinate census at better critical proportions.

## 2.2 Open mathematical obstacles

Nobody knows how to produce these. Strength tags: [QRH] zero-free strip, [LH] Lindelöf, [FS] finitely many off-line zeros, [RH].

| # | Obstacle | Strength | Precise corpus form |
|---|---|---|---|
| **B1** | **Critical positivity of the complete Weil matrix** | [RH] | Positivity on \(E(c_N)\log N\asymp1\). For the tilted spline the curve has exponent \(1/7\); the receiver is \(\alpha>1/4\) (`tiltedUnitSpline_overlap_window`). Margin, reserve and synthesis error are one Fourier tail, so no fixed-relative-loss estimate crosses. |
| **B2** | **A positive ground state of the full arithmetic generator** | [RH] | The odd Markov form is never subcritical; folded supersolutions are excluded; the restricted ground energy tends to \(0\). Needed: a positive (super)solution of the nonlocal prime-jump generator. |
| **B3** | **Rank-uniform theta/Jensen positivity** | [RH] | Center-flux domination \(B_v(x)\le\int_{y>x}|G_v|^2\) for every finite section, uniformly in rank. Equivalently \(\Lambda=0\) on the heat side. |
| **B4** | **Finite Krein index** | [FS] ⇒ [LH] | \(\kappa(K_\zeta)<\infty\): all zeros above some height critical. A Gårding-type finite index exists at each aperture; the open part is uniformity in aperture. |
| **B5** | **A square-root producer over \(\mathbb Z\)** | [RH] | An integral auxiliary construction with polynomial support cost at \(x^{1/2}\). Adams jets cost \(2^{qr}\) (sharp), factorial ratios \(2\log2\); every producer law holds for \(\Lambda+\varepsilon n^{-\eta}\). |
| **B6** | **Type-II dispersion below the quadratic horizon** | [QRH] and up | Coherent prime blocks admit no Type-II dispersion below the quadratic horizon; every short-window or balanced saving is a zero-free strip (BVI). This is the parity problem in exact form. |
| **B7** | **The exponent at the trivial gauge point** | [RH] | \(\theta_\mu(0)=1/2\). The typical value is \(1/2\), but \(0\) is never better than typical, and gauge-invariant certificates stop at \(3/4\). |
| **B8** | **Uniform selection at growing resolution** | Part of B1 | Pole-keeping twins need overlap \(\asymp p^{1/7}\). Selection and criticality must be achieved on the same schedule. |
| **B9** | **Hecke invariance of the collided polarization** | [RH] | Weil form = collided form; the scaling defect is already a Hecke similitude, but the collided form's invariance is the sign. |
| **B10** | **An independent positive realization of \(\Xi\)** | [RH] | Operator, lossless medium, ferromagnet or quasinormal-mode system whose spectral data equal \(\Xi\)'s zeros without zero indexing. CCM leaves an anticommutator term; Deninger's complete carriers have bounded generators. |
| **B11** | **The classical conjectures** | [LH], [QRH] | Lindelöf, the density hypothesis, a fixed zero-free strip. In the corpus Lindelöf follows from finite index (B4) and from no current estimate. |

(inference) B1–B3 and B9–B10 are the critical-sign family, B4–B6 and B11 the precision family, B7–B8 the selection family. At their endpoints all three families are one statement (route-unification ledger §2).

## 2.3 The three questions to answer next

**Q1. Is the Weil-kernel index finite?**

Equivalently: are all zeros above some height on the line [Lean: finite index ⟺ finite off-line support; `lindelof_of_negIndex_zetaKernel_lt_top`]?

- **Why this question.** It is the weakest structural target that implies an open conjecture of first rank (Lindelöf).
- **It asks for a count, not a sign.** The index is an integer, lower semicontinuous, and closed under pointwise limits of kernels (HKT: bounded index is closed under pointwise convergence). Integrality and compactness act on such quantities; they do not act on margins.
- **Index at infinity.** By Krein–Langer, finite index means PSD minus finite rank. A Persson-type principle locates the index at infinity: it suffices to prove positivity, or a Gårding inequality with a compact error, only for tests living at large height or large aperture.
- **Concrete subquestions:**
  - Is the per-aperture finite index of the restricted Weil form bounded uniformly in the aperture?
  - Is the heat collision mass, which counts the index, bounded as \(t\downarrow0\)?
  - Does some nonblind prime tower carry an index ceiling from ring structure?

**Q2. What is the scaling limit of the complete Weil matrix on its critical curve?**

Rescale the matrix by \(E(c_N)\) with \(E(c_N)\log N\to\kappa\) and ask whether it converges, in the strong resolvent sense on the conductor coordinates, to an explicit limit operator \(\mathcal W_\kappa\).

- **Why this question.** Positivity on the curve is RH (B1), but the curve is also where the three error sources are equal. The limit isolates the content: the pole, the \(\approx c\) near-degenerate conductors with \(E_m\asymp c^{-7}\), and the archimedean weight.
- **If the limit is universal** (independent of the zeros), RH on the curve becomes the positivity of one explicit operator plus a convergence theorem. That is a finite, checkable mathematical object.
- **If it is not universal**, the limit is a new canonical encoding of the zeros at the exact critical scale, and its non-universality identifies which conductor block carries the off-line information.
- Either outcome converts the critical curve from an inferred heuristic into a theorem.

**Q3. Is \(2^{qr}\) a universal law for integral auxiliary constructions over \(\mathbb Z\)?**

The corpus proves sharply that vanishing to order \(r\) on the Adams fixed locus costs support \(2^{qr}\), and that factorial ratios stop at precision \(2\log2\).

- **The question.** Does every integral vanishing condition that implies square-root precision pay exponential support? This includes non-jet conditions: simultaneous vanishing of Ramanujan sums across many conductors, cyclotomic-norm conditions, conditions on the gauge torus away from \(0\).
- **"Yes"** is a deep no-go: Stepanov's method has no characteristic-zero form, and the precision family must be crossed by geometry (an infinite-genus Hodge theorem), not by auxiliary functions.
- **"No"** produces the first square-root producer over \(\mathbb Z\), the missing input of every P-route.
- The question is posed in the corpus's own language (Adams operations, the gauge torus, cyclotomic norms \(\ge1\)), so its answer is reachable by the methods that proved the \(2^{qr}\) law.

## 2.4 A wildly different route

The corpus's universality laws show that analytic, spectral, moment, sieve, heat, operator and physical-model certificates all collapse onto the same receivers (route report §2). (inference) A route that faces different walls must import a mechanism the corpus does not contain. Searches for measure rigidity, entropy rigidity under \(\times p\) actions and \(q\)-de Rham/Habiro structures return nothing relevant [corpus search].

**Proposal: arithmetic measure rigidity for the multiplicative action on the adelic solenoid.**

- **Mechanism.** Higher-rank measure rigidity (Furstenberg, Rudolph, Host, Einsiedler–Katok–Lindenstrauss): a probability measure on \(\widehat{\mathbb Q}\) or \(\mathbb A_{\mathbb Q}/\mathbb Q^\times\) that is invariant under multiplication by two multiplicatively independent integers and has positive entropy is Haar. In arithmetic quantum unique ergodicity (Lindenstrauss, Bourgain–Lindenstrauss), Hecke recurrence produces the positive entropy, and rigidity converts that qualitative input into an exact identification.
- **Why it faces different walls.**
  - The central step is not positivity of a quadratic form, so Σ does not appear as a margin.
  - It is not a count, so Π does not appear as an exponent.
  - It is an amplifier: qualitative positive entropy becomes exact algebraicity. This is the role the tensor-power trick plays over \(\mathbb F_q\) and the one the corpus proves missing over \(\mathbb Z\).
  - The corpus shows that two-prime lattices already carry the full Weil-kernel index (HKT) and that \(\log 6\) is the decoupling length of \(2\) and \(3\) (BSU). Higher-rank multiplicative structure contains the complete information, which is exactly what rigidity needs.
- **What it must supply:**
  1. A positive measure attached to a hypothetical off-line zero, e.g. a weak limit of normalized \(|f_\rho|^2\) for scaling-flow eigenfunctions with growth \(e^{t(\operatorname{Re}\rho-1/2)}\).
  2. Its invariance, or quasi-invariance with computable cocycle, under the \(\times p\) actions.
  3. Positive entropy from Hecke recurrence.
  4. A contradiction with the rigidity classification.
- **Risks (inference).**
  - Step 1 is where positivity enters: Σ returns if the construction needs a sign of the Weil form.
  - Step 3 must use the Euler product, or the argument would also apply to twins: Γ returns if the measure is gauge-blind.
  - The route is worth pursuing because steps 2 and 4 are theorems in other contexts and nothing in the corpus rules out steps 1 and 3.

No second route outside the three walls is visible in the corpus.

## 2.5 Breakthrough opportunities on Weil positivity

Each item below is a mechanism that creates positivity from structure, not a new receiver, a better constant or a lower bound.

**O1. Reflection positivity from locality.**

- The corpus proves that RH is reflection positivity of the Cayley ladder, that the sign is a gauge-fixing, and that the successor connection is the archimedean gauge field (ArithmeticLorentzianGeometry).
- In constructive field theory, reflection positivity is not estimated. It follows from locality: an action of the form \(A_++\theta A_++\sum_i\theta(F_i)F_i\) on a reflection-symmetric lattice is reflection positive (Osterwalder–Seiler, chessboard estimates). It holds at criticality, with no gap.
- **The opportunity:** a nearest-neighbour action on the multiplicative lattice, with the functional equation \(s\mapsto1-s\) as reflection and the successor as gauge field, whose transfer matrix is the Cayley ladder.
- Positivity then comes from the form of the action. The arithmetic content is the identification of the transfer matrix, an identity rather than an inequality.

**O2. Disconjugacy instead of coercivity.**

- The native theta fibre form is a square plus a null Lagrangian: \(\sum v_iv_jh_{i+j}=|G_v|^2+B_v'\) (`ThetaCuspCenterTailSquareFlux`). This is the structure of the second variation in the calculus of variations.
- There, positivity at the critical boundary is decided by the absence of conjugate points: Jacobi's theorem, a global Riccati solution, Weierstrass field of extremals. It is decided by comparison (Sturm), not by margins. Disconjugacy is the natural language of criticality: a critical form is exactly one with a positive solution that is not \(L^2\).
- **The opportunity:** a Riccati transformation of the arithmetic Markov form, with the null-Lagrangian freedom used to choose the flux \(B_v\). RH becomes "no conjugate point on \((0,\infty)\)", and a Sturm comparison with an explicit disconjugate equation would prove it.
- The excluded folded supersolutions (ACT) are one comparison family. The full nonlocal Riccati equation is not.

**O3. Positivity as a matrix coefficient.**

- The corpus proves:
  - the critical line is the positivity threshold of the integer successor on \(\mathrm{Aff}(\mathbb Q)\);
  - the Bost–Connes temperature is the Hecke exponent;
  - the integer successor forces the Hecke weight;
  - RH iff some positive-definite function on \(\mathrm{Aff}(\mathbb Q)\) restricts to Weil's correlation on dilations.
- A matrix coefficient \(\langle\pi(g)v,v\rangle\) of a unitary representation is positive definite for free.
- **The opportunity:** construct the representation arithmetically, as the GNS representation of a KMS\(_1\) state of a Hecke algebra at the critical temperature extended to the successor, and prove that its restriction to dilations is Weil's correlation.
- The corpus's classification says the admissible extensions are indexed by the critical zeros. The construction has to produce one extension from arithmetic alone. That is a construction problem, not an estimate.

**O4. The index at infinity.**

- Krein–Langer theory makes finite index equivalent to "PSD minus finite rank", and index is closed under pointwise limits (HKT).
- A Persson-type principle (the essential bottom is determined at infinity) together with a positive supersolution only outside a compact set gives finite index (Q1). Foster–Lyapunov drift and Agmon-type ground-state comparisons are the standard tools.
- This trades the global sign for a sign at large height plus a finite-dimensional compact part, which integrality and certified computation can handle (fixed-overlap positivity, fixed-aperture floors).

**O5. Effectivity counting on the scaling surface.**

- The scaling surface carries a theta \(h^0\) with Riemann–Roch proved independently of the sign (`arithH0_riemannRoch`), and its Hodge defect is the right-zero count.
- In the Castelnuovo–Severi/Bombieri proof over \(\mathbb F_q\), the Hodge index follows from a counting statement: \(h^0(nD)=o(n^2)\) for a degree-zero class.
- **The opportunity:** prove subquadratic growth of theta \(h^0\) on degree-zero classes. This is a dimension count of theta sections, a lattice-point problem, not a sign.
- Infinite genus (no radical) is the obstacle to be faced, and it appears here as the growth of the error term in Riemann–Roch.

**O6. Stability preservers.**

- Euler products of Lorentzian local factors are Lorentzian; the prime ladder is not; Ramanujan and Lorentzian meet only at the Weil bound (ALG).
- Borcea–Brändén classify the linear operators that preserve stability (real-rootedness). Pólya–Schur multiplier sequences are the one-variable case.
- **The opportunity:** a completion operator, built from \(\Gamma\) and the functional equation, that is a stability preserver and maps Lorentzian truncated Euler products to approximants of \(\Xi\).
- Positivity would be inherited from the local factors by a structural closure theorem. The task is to find the operator, a classification question.

## 2.6 Does crossing the walls need a new field?

(inference, ideation constrained by the corpus)

**Yes.** Over \(\mathbb F_q\) the three properties come from one object, the Frobenius graph on \(C\times C\), inside one theory, intersection theory on a surface of finite genus. The corpus has built the \(\mathbb Z\)-analogues of the surface, the intersection form, the Hecke correspondences and the count. It proves that the finite-genus mechanisms fail: no radical, Adams jets cost \(2^{qr}\), no Frobenius among self-maps. The missing theory is an intersection theory in which infinite genus is normal and positivity holds at criticality.

**What the field would be about.** Positivity theorems for intersection forms on arithmetic objects of infinite genus, exactly at their critical threshold, with dimensions measured relative to a symmetry rather than counted. A working name: **equivariant \(L^2\)-arithmetic Hodge theory**.

**What it is like.** Its closest model is \(L^2\)-cohomology with von Neumann dimension (Atiyah's \(L^2\)-index theorem, Lück's approximation theorem). Infinite-dimensional cohomology with a group action acquires a finite dimension per unit volume. Finite quotients approximate it: normalized finite Betti numbers converge to \(L^2\)-Betti numbers. The corpus already contains both halves:

- **The density half.** Zero-density theorems (formalized Guth–Maynard; \(\ge4/5\) critical ordinates) say the off-line part has density zero: zero "von Neumann dimension" per unit height.
- **The faithfulness half.** A faithful trace kills a projection of trace zero. The off-line spectral projection would vanish if it lay in an algebra with a faithful trace computing that density.

The corpus also proves why faithfulness is not free. The relevant equivariance, Hecke invariance of the collided polarization, is RH (`riemannHypothesis_iff_collided_hecke_invariant`). (inference) In this language, RH is the statement that the off-line part, already of density zero, is equivariant. The field's central theorem would be an equivariance principle for arithmetic spectral projections.

**Criteria for the field to be real rather than a reformulation.**

1. **An intrinsic object.** A von Neumann algebra \(\mathcal M\) generated by the scaling flow and the Hecke correspondences on the scaling surface's \(H^1\), defined from \(\mathbb Z\) without reference to zeros, with a semifinite normal trace \(\tau\).
2. **Finite density.** \(H^1\) has finite \(\tau\)-dimension per unit log-height. The Riemann–von Mangoldt density \((2\pi)^{-1}\log T\) is the expected value.
3. **A Hodge index theorem relative to \(\tau\),** reducing to Weil's over \(\mathbb F_q\), where the genus is the \(\tau\)-dimension of a finite-dimensional space.
4. **An approximation theorem.** Truncated complete Weil matrices at horizon \(N\) approximate the \(\tau\)-signature, like Lück's theorem; this is the missing amplifier.
5. **Selectivity built in.** \(\mathcal M\) and \(\tau\) must not exist, or must differ, for gauge twins. The pole, i.e. the simple-pole class, and the finite part \(-L'/L(1)\) must enter its definition.

**Questions it would ask.**

- Is the negative spectral projection of the Weil form affiliated with \(\mathcal M\)? This is the selection face, Γ4.
- Does an Atiyah-type rationality or integrality hold for \(\tau\)-dimensions of kernels of operators in the arithmetic Hecke algebra?
- Is there a renormalized genus, a \(\tau\)-dimension of \(H^1\) per window, for which a height-local Castelnuovo inequality holds with a constant growing subexponentially in the window?
- What replaces the characteristic-\(p\) vanishing derivative of Frobenius: is there a derivation on \(\mathcal M\) that kills the Hecke correspondences the way \(d(x^p)=0\) kills Frobenius?
- At the critical temperature \(\beta=1\), is the Bost–Connes KMS state the trace \(\tau\), and does criticality of the odd Markov form correspond to a phase transition of \(\mathcal M\)?

**Tools.**

- Von Neumann algebras and semifinite traces; \(L^2\)-invariants, Atiyah and Lück approximation.
- Krein and Pontryagin spaces (the index is already exact: HKT/AKLT).
- Dirichlet forms, Martin boundaries and ground-state transforms (RAPT, ACT).
- Reflection positivity and lattice gauge theory (ALG).
- Measure rigidity and entropy (§2.4).
- Lorentzian polynomials and stability preservers (ALG, O6).
- Arakelov intersection theory and theta Riemann–Roch (ACS, AOG).

**Objects.** The scaling surface of \(\mathbb Z\) and its intersection Gram; the gauge torus and its trivial point; the multiplicative random walk and its pole ground state; prime towers and two-prime lattices; Adams operations; the conductor spectrum \(E_m(c)\); the critical curve; the collided polarization; KMS states of the Hecke algebra.

**Language.** Criticality index; renormalized genus; equivariant signature; selection class (the set of gauges an invariant distinguishes); precision class (the perturbations \(n^{-\eta}\) it detects); deciding input; Hodge defect; collision mass; resolution threshold.

**Mechanisms it would need to provide.**

- **Positivity at zero margin:** Hodge index, reflection positivity or disconjugacy, instead of coercivity.
- **Precision from equivariance:** faithfulness of a trace, instead of auxiliary functions.
- **Amplification from approximation:** finite-horizon signatures converging to the \(\tau\)-signature, instead of tensor powers.
- **Selection from the definition of the algebra:** the pole and the Euler product as structure, instead of as test data.
