# Biarithmetic Gauge Geometry (BGG)

Namespace `GaloisForLFunctions.BiarithmeticGaugeGeometry`; umbrella `BiarithmeticGaugeGeometry.lean`.

**Question.** Every multiplicative operator on $\mathbb N_{\ge1}$ (diagonal weights, ratio shifts $n\mapsto mn$, prime Hecke towers,
product kernels) is unitarily intertwined across the prime gauge torus $\Omega_{\mathcal P}=\prod_pS^1$: it cannot tell the Euler vacuum
($\zeta$) from the Liouville vacuum ($\lambda$, $\zeta(2s)/\zeta(s)$) or a Kronecker shift $p^{i\gamma}$. And completed Bochner–Hadamard
positive systems admit rational surgeries that leave the integer log-lattice. Which non-commuting $(+1,\times p)$ gauge
geometry breaks prime-torus symmetry *selectively at the Euler vacuum*, survives Hadamard deformations in higher degree,
removes lattice-truncation surplus on polar-neutral states, and rotates additive torsion without collapsing onto the
Poisson pole?

**Basic invariant:** the **successor gauge connection** $A_\omega(n)=\overline{\chi_\omega(n)}\chi_\omega(n+1)$, whose holonomy across shortcuts
$n\mapsto pn$ measures the failure of $+1$ and $\times p$ to commute. **Principle:** every multiplicative positivity law must be
paired with an explicit gauge-fixing connection, and every broken two-sided symmetry replaced by its exact chiral survivor.

---

## 1. Place in the research

Four corpus routes end at structural obstructions BGG addresses: (1) unitary gauge blindness of multiplicative operators;
(2) degree-4 height-coupled systems are not scalar-rigid; (3) the reflected archimedean diagonal on $\{\log n\}$ grows
linearly and lattice truncation breaks translation invariance; (4) monomial $\mathbb Z^2$ theta dilations factor and fix the pole.

| Programme | Interface |
|---|---|
| ArithmeticEffectivityTheory | Complementary twin: counting/effectivity vs gauge connections |
| StripBochnerWeilForcing | `CompletedPositiveSystem`, polar sums, real-anchor law |
| ArithmeticCorrespondencePositivity | `HeightCoupledSystem`, `coupledQuartetSymSquare`; BGG refutes `CoupledRigid` and isolates the central ceiling |
| ArithmeticPolarization | Coupled rigidity would exclude zeros; BGG proves non-rigidity and the chiral survivor |
| ArithmeticOrientationTheory | `archPairKernel`, `archReflectedDiagWeight` |
| ArithmeticCorrelationGeometry | Gauge torus, Kronecker flows; cell holonomy growth |
| BiarithmeticGeometry, BezoutValuationIncidence, SignedSuccessorArithmetic | Successor/dilation curvature |

---

## 2. Why

1. **Multiplicative positivity alone never isolates $\zeta$.** $(U_\omega\psi)(n)=\chi_\omega(n)\psi(n)$ is unitary, preserves cutoffs and diagonal
   weights, intertwines ratio shifts; at real sign gauges (Liouville) it intertwines product kernels too.
2. **Catalan $\{1,2,3,4\}$ is the minimal gauge-fixing plaquette.** Flatness of $A_\omega$ on $[1,N]$ forces $\omega(p)=1$ for $p\le N+1$; the
   links $A_\omega(2),A_\omega(3)$ reconstruct $\omega(2),\omega(3)$. Mimicking Liouville along the Kronecker line ($2^{i\gamma}\approx3^{i\gamma}\approx-1$) is
   repelled: $(1+\cos(\gamma\log2))+(1+\cos(\gamma\log3))\ge\frac1{50}e^{-|\gamma|}$ (parity $2^a\ne3^b$, no Baker).
3. **Higher-degree Bochner–Hadamard forcing is chiral.** At a critical zero $\xi(\tfrac12+i\gamma)=0$, the outward splitting multiplier
   $W_\beta=((s-\tfrac12)^2+\beta^2)/(s-\tfrac12)^2$ is Bochner-positive and stays in `HeightCoupledSystem 2 1 1 γ`, lowering the central order
   by 2: `CoupledRigid γ` is false. Inward collapse ($+2$) is not Bochner-positive; off-critical quartet contraction raises
   it by $+4$. The surviving invariant is the one-sided **central vanishing ceiling** $\operatorname{ord}_{1/2}\Lambda\le\operatorname{ord}_{1/2}\Lambda_\gamma$.
4. **Log-cells heal truncation.** Over all pairs $[2,X]^2$ the linear archimedean growth is a rank-one polar square, vanishing on
   the polar-neutral hyperplane; cells $I_n=[\log n,\log(n+1))$ subdivide $\log m$-shifts exactly ($\sum_{r<m}w_{am+r}=w_a$).

---

## 3. Objects and language

| Concept | Realization | Lean |
|---|---|---|
| Prime gauge torus; vacua | phases $\omega(p)$; Euler, Liouville, Kronecker | `PrimeGauge`, `eulerGauge`, `liouvilleGauge`, `kroneckerGauge` |
| Gauge character, twist | $\chi_\omega$; $(U_\omega\psi)(n)$ | `gaugeChar`, `gaugeTwist`, `twistedLatticeForm` |
| Successor connection | $A_\omega(n)$ | `succConn` |
| Critical splitting / inward collapse | $W_\beta$, $W_\beta^{-1}$ | `criticalSplitMultiplier`, `inwardCollapseMultiplier` |
| Central ceiling | $\operatorname{ord}_{1/2}\Lambda\le\operatorname{ord}_{1/2}\Lambda_\gamma$ on the coupled class | `CentralVanishingCeiling` |
| Lattice decay | $O(2^{-\sigma})$ derivative decay of Dirichlet log-lattice series | `HasDirichletLatticeDecay` |
| Log-cells, Sobolev energy | widths $w_n$; $\sum k(c_{k+1}-c_k)^2$ | `logCellWidth`, `continuumCellShiftCorr`, `biarithmeticSobolevEnergy` |
| Torsion rotation, bi-torsion contrast | $u\mapsto2u$ on $(\mathbb Z/q)^\times$; $\Delta_{q_1,q_2}=\varphi(q_2)c_{q_1}-\varphi(q_1)c_{q_2}$ | `torsionMulEquiv`, `biTorsionContrast` |
| Positive deformation | $-F'/F+\zeta_\gamma'/\zeta_\gamma=$ Laplace of $\nu\ge0$ | — |

---

## 4. Mechanisms

1. **Unitary intertwining vs Catalan holonomy** (blindness of multiplicative forms; reconstruction from two successor links).
2. **Determinant elimination**: $(\log3)\delta_2-(\log2)\delta_3$ eliminates $\gamma$, reducing to $|2^{|u_3|}-3^{|u_2|}|\ge1$; with $N$ primes, Siegel's lemma +
   unique factorization give stretched-exponential repulsion $\exp(-c|\gamma|^{1/(N-1)})$.
3. **Chiral Bochner splitting**: $\Re(-W_\beta'/W_\beta)$ is the Laplace–cosine transform of $2e^{-(\sigma-1/2)t}(1-\cos\beta t)\ge0$; $W_\beta^{-1}$ violates the
   real-anchor law; both $W_\beta$ and quartet symmetric squares decay like $\sigma^{-3}$, escaping lattice decay.
4. **Landau–Wronskian principle**: entire $\Lambda,\Lambda_0$ with $\Lambda_0'/\Lambda_0-\Lambda'/\Lambda=\mathcal L\nu+E$ ($\nu\ge0$) share their divisor right of the abscissa; a
   positive jump there is a real zero of $\Lambda_0$ of higher order.
5. **Abel–Gram law**: across a vertical line at/right of the abscissa, divisor jumps are Abel limits of $\mathcal L\nu$ and form an even
   PD function on $(\mathbb R,+)$; finite support gives trigonometric inequalities (critical conservation).
6. **Abel residue quantization**: the residue $(\sigma-\tfrac12)\mathcal L\nu(\sigma)$ equals the central drop, an even integer.
7. **Polar-neutral rank-one cancellation + Euclidean cell subdivision** with $m$-uniform Sobolev remainder.
8. **Fixed-point-free torsion rotation**; Ramanujan sums mean zero with Parseval energy $q\varphi(q)$; the bi-torsion contrast kills $n=0$.

---

## 5. Pillar theorems

1. **Prime-torus blindness vs Catalan rigidity** (`nonneg_realSign_latticeForm_iff`, `succConn_flat_iff_primes_eq_one`, `catalan_holonomy_two`).
2. **Diophantine repulsion**, two and $N$ primes (`liouville_kronecker_repulsion_ge`, `multiPrime_repulsion`).
3. **`CoupledRigid` is false; chiral deformation law** (`not_forall_coupledRigid`, `not_isEvenPosDef_inwardCollapseMultiplier`,
   `coupledQuartet_escapes_dirichletLattice`).
4. **Central vanishing ceiling implies RH** (`riemannHypothesis_of_forall_centralVanishingCeiling`); it transfers to cofactors
   $\Lambda=(2\xi)^k\Lambda_G$ (`centralOrder_factor_le_of_ceiling`) — e.g. would bound $\operatorname{ord}_{1/2}L(s,\mathrm{sym}^2u)$ for Maass forms (not formalized).
5. **Rational classification**: rigid at every ξ-zero-free height line; rational ceiling at $\gamma\ne0$ ⇔ no off-critical zero at $\gamma$
   (`lattice_real_anchor`, `rationalDeformation_real_anchor`).
6. **Positive prime-mass deformations are rigid off the line**; positive ceiling ⇔ no off-critical zero at $\gamma$; RH ⇔ every positive
   deformation is trivial or strictly lowers the centre (`positiveDeformation_offLine_rigid`, `positiveCoupledRigid_iff`,
   `riemannHypothesis_iff_forall_positiveChiral`).
7. **Square-root deficit law and strong multiplicity one**: exceeding the central order forces removal of prime mass of square-root
   size; zero-residue deficit + kept centre ⇒ $F=K\zeta_\gamma$ (`centralExcess_forces_squareRoot_deficit`, `latticeMember_eq_of_negligible_deficit`).
8. **Landau–Wronskian and $\zeta^d$ rigidity; Abel–Gram boundary capacity $(\kappa-d)/2$** (`landauWronskian_orders_and_anchor`,
   `zetaPowDeformation_trivial`, `zetaPowDeformation_boundary_law`).
9. **Critical conservation**: each net created critical zero costs two central orders (`centralDrop_ge_two_mul_created_sub_destroyed`).
10. **Square-root quantization**: prime mass added at the $\sqrt x$ scale comes in even integer units $\le2\operatorname{ord}_{1/2+i\gamma}\xi$, zero at zero-free
    ordinates (`tendsto_abel_excess_eq_centralDrop`, `tendsto_surplus_residue_eq_centralDrop`).
11. **Polar-neutral collapse and cell subdivision** (`reflectedDiag_add_offDiagPolar_eq_neg_levy`, `continuumCellShiftCorr_eq_spine_add_remainder`).
12. **Torsion rotation and bi-torsion contrast** (`dyadic_torsion_rotation_fixed_point_free`, `biTorsionContrast_zero`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| A clever positive diagonal/product kernel on $[1,X]$ separates $\zeta$ from $\lambda$ | Real sign gauges intertwine them unitarily |
| `CompletedPositiveSystem 1 1` rigid ⇒ height-coupled class rigid | False at infinitely many Hardy ordinates |
| Critical zeros move freely both ways | Inward collapse is not Bochner-positive: chiral |
| Rational quartet contractions keep Dirichlet-series structure | They decay like $\sigma^{-3}$, escaping the lattice |
| The linear reflected diagonal is an irreducible obstruction | Rank-one polar square; vanishes on polar-neutral states |
| Discretizing shifts onto $[1,X]$ smears boundaries | Log-cells subdivide exactly; remainder $m$-uniform |
| Monomial $\mathbb Z^2$ dilations give 2D coupling | They factor and fix $(0,0)$ |
| Positive deformations can add prime mass freely | At $\sqrt x$ scale it is quantized by the central drop |

---

## 7. Open problems

1. **Central vanishing ceiling** beyond rational and positive deformations: transcendental multipliers with infinitely many
   singularities (needs a lattice sieve beyond finite polar sums); which Hadamard multipliers preserve both the coupled class
   and log-lattice support.
2. **Polar-neutral Sobolev vs divisibility spine**: explicit polar-neutral profiles whose prime spine dominates
   $\mathcal E_{\rm Sob}^{1/2}$ and the Lévy cost.
3. **Polynomial (Baker-strength) repulsion** $|\gamma|^{-C}$ from a growing prime set.
4. **Non-separable bi-torsion theta operators** on $\mathbb Z^2$ cancelling the $(0,0)$ and axis poles.
5. **Deficits with nonzero Abel residue**: the remaining case of strong multiplicity one.

## 8. Tools to build

Multi-prime Bézout holonomy plaquettes ($p^a-q^b=\pm1,\pm2$); lattice-preserving height-coupled classes
(`DirichletLatticeCoupledSystem`); optimized polar-neutral Sobolev families; Mellin–Poisson duality for
$\Delta_{q_1,q_2}$-weighted theta kernels.

## 9. Contribution standard

State how the construction transforms under $U_\omega$ and why it separates Euler from Liouville; test statements on the coupled
class against $W_\beta$ (must hold) and off-critical quartet contraction (must obstruct), and state whether discrete
$\{\log n\}$ support is used; account for off-diagonal polar terms and cell remainders exactly; record the chiral survivor of
every broken symmetry.
