# Arithmetic Defect Rigidity (ADR)

Namespace `GaloisForLFunctions.ArithmeticDefectRigidity`; umbrella `ArithmeticDefectRigidity.lean`.

**Question.** Which failures of critical arithmetic estimates survive normalization, localization and
passage to infinity — and which relations of the actual source restrict an escaping defect strongly
enough to control the signed quantity an established receiver consumes?

The working receiver is the centred damped Möbius receiver at $0<\varepsilon<\tfrac12$. ADR separates its
energy from the much larger positive forcing, keeps the receiver as a signed Gram difference, locates the
forcing in the cofactor tail, pays the forcing by an explicit power subtraction defined by the source's own
pole trace, and extracts limits (energy quantiles; common cofactor Gram limits carrying a cyclic critical
Wiener module) that retain signed data. Each result constrains what an escaping state can be.

**Open core: exclusion.** None of this bounds receiver energy. A source estimate excluding every escaping
state for a cofinal family of dampings would give RH through the critical-energy receiver.

---

## 1. Place in the research

The corpus has exact receivers; compensation theory proves normalized receiver profiles escape every fixed
window. ADR asks what survives that escape: a pointwise limit can be zero with total energy one; a cofactor
identity can become homogeneous on fixed cells while its forcing grows; a successor label can act as the
identity in the chosen norm.

| Programme | Relationship |
|---|---|
| ArithmeticCompensationTheory | Normalized profiles, origin costs, escape |
| ArithmeticContinuationAndCriticalEnergy | Receiver, inversion identity, dilation calculus, incomplete fibres |
| BezoutValuationIncidence | VK estimate, successor covariance, Vaughan Grams |
| TransHorizonIncidenceMechanics | Smooth-power expansion, Mellin cells, first-moment identity |
| ArithmeticOrientationTheory | Critical Wiener algebra, paid ideals, hulls; cofactor limits are Wiener modules |
| SignedSuccessorArithmetic | Successor counts; transfer must beat fixed-successor collapse |
| SignedArithmeticEnergyIncidence | Compact negativity vs escape |
| ArithmeticOrientationGeometry, ArithmeticCastelnuovoSeveri | Geometric carriers must preserve the adverse mode and its cost |

---

## 2. Objects and language

At damping $\varepsilon$: $c_\varepsilon(n)=\sum_{d\mid n}\mu(d)d^{-\varepsilon}$, $m_\varepsilon=\zeta(1+\varepsilon)^{-1}$, receiver prefix
$A(n)=\sum_{j\le n}(c_\varepsilon(j)-m_\varepsilon)$, pronic pairing $\langle u,v\rangle_T=\sum_{n\le T}u(n)v(n)/(n(n+1))$, energy
$E_T=\|A\|_T^2$. **Inversion identity**: $\rho(n)=n-m_\varepsilon\sum_{j\le n}j^{-\varepsilon}\lfloor n/j\rfloor=A(n)+D(n)$,
$D(n)=\sum_{2\le j\le n}j^{-\varepsilon}A(\lfloor n/j\rfloor)$.

| Object | Meaning | Lean |
|---|---|---|
| Forcing energy | $F_T=\|\rho\|_T^2\ge b_\varepsilon T^{1-2\varepsilon}$ | `forcingEnergy` |
| Signed Gram | $P=\langle A,\rho\rangle$, $G=\|D\|^2$, $Q=\langle\rho,D\rangle$ | `receiverForcingPairing`, `cofactorEnergy`, `forcingCofactorPairing` |
| Cofactor tail | $D-D_{\le J}$ | `cofactorTail` |
| Forcing power / remainder | $c_\varepsilon n^{1-\varepsilon}$, $c_\varepsilon=-m_\varepsilon\zeta(1-\varepsilon)/(1-\varepsilon)>0$; $R=\rho-c_\varepsilon n^{1-\varepsilon}$ | `forcingPower`, `forcingRemainder` |
| Renormalized cofactor | $\tilde D=D-c_\varepsilon n^{1-\varepsilon}$; operator on the pole-trace domain | `renormalizedCofactor`, `poleTraceDomain`, `renormalizedCofactorOperator` |
| Pole trace | $\mathcal L(v)$ = Mellin pairing at $1-\varepsilon$ | `traceDilation` |
| Energy quantile | first crossing of $rE_T$ | `receiverEnergyQuantile`, `quantileCofactorWork` |
| Cofactor Gram | $K_T(j,k)=\langle D_jA,D_kA\rangle_T/E_T$, $D_jv(n)=v(\lfloor n/j\rfloor)$ | `cofactorGram`, `ActualCofactorLimit` |
| Eta cofactor sum | $H_\varepsilon v=\sum_{j\le n}(-1)^{j+1}j^{-\varepsilon}v(\lfloor n/j\rfloor)$ | — |
| Cell word | successor translations + floor dilations; boundary cost $B(w)$ | `CellWord` |

**Words.** *Escape*: $E_T\to\infty$; *admission*: bounded. *Defect state*: a proposed carrier of escaping energy
with its operations, signed covariances, scales and forcing (no interface asserting exclusion is supplied).
Distinctions: data vs estimate; reconstruction vs bounded output; uniqueness vs coercivity; relative vs
absolute smallness; a limiting Gram can lose its small signed coordinate; divisor support loses multiplicity.

---

## 3. Mechanisms

### Scales and signed geometry
1. **Forcing dominates the receiver.** $E_T\le C_\varepsilon e^{-\kappa\sigma(T)/270}F_T$ (VK); $F_T/E_T\to\infty$ whether or
   not $E_T$ diverges; no common scalar normalization keeps both visible. Source-selective: the unsigned majorant
   has constant ratio.
2. **Receiver = Gram tangent.** $F+G-2Q=E$, $0\le FG-Q^2=EF-P^2$; determinant$/F^2\to0$ while distance$/E=1$: rank or
   positivity of the limiting Gram loses the receiver.
3. **The cofactor tail carries the forcing**, also on a moving window $J_T=\lfloor\log(F_T/E_T)\rfloor\to\infty$;
   fixed-label limits lose the whole forcing.

### Successors and words
4. **Fixed successors disappear on escape** ($\|A(\cdot+k)-A\|^2\le k^2$); with VK, recentred $o(k^{1-\varepsilon})$.
5. **Words have boundary budgets**: normalized displacement $\le B(w)^2/E_T$, forcing work $\le B(w)L_\varepsilon$; new
   horizon cells paid uniformly.

### Paid renormalization and the pole trace
6. **Power subtraction pays the forcing.** $\|R\|_T\le B_\varepsilon$ at every horizon; $A+\tilde D=R$; on escape the
   inversion is homogeneous and the renormalized pairing is **antipodal**, $(\tilde P/E+1)^2\le B^2/E$.
   Trace-free form: $H_\varepsilon=(I-2^{1-\varepsilon}D_2)S$ kills the pole exactly, $\|H_\varepsilon A\|_T\le B$, symbol
   $(1-2^{1-\varepsilon-s})\zeta(s+\varepsilon)$. Euler laws at 2 and 3 together ⇔ the renormalized inversion law.
7. **Finite forcing mass** $\to L_\varepsilon=-\zeta'/\zeta(1+\varepsilon)$: pays bounded cell errors, not $\langle A,\rho\rangle$.
8. **Absolute pole trace.** $\mathcal L(A)=c_\varepsilon>0$; dilations preserve the domain with weight $j^{-(1-\varepsilon)}$;
   packets cost harmonic sums.
9. **Bounded commutator** $[\tilde D,D_p]$, norm $\le|\mathcal L(v)|$ uniformly in $p,T$; vanishes on escape.
10. **Residual + trace determine the row**; $\ker(I+\tilde D)=\mathbb Rq_\varepsilon$; the unestimated term is the Möbius floor
    inverse of $R$.
11. **Symbol of $\tilde D$.** On power rows $(I+\tilde D)n^s=\zeta(s+\varepsilon)n^s$ modulo admitted rows; for $\Re s\ge\tfrac12$
    $\tilde Dv\approx-v$ iff $\zeta(s+\varepsilon)=0$. On $\log^kn\cdot n^s$ rows $I+\tilde D$ is the Leibniz matrix of
    $\zeta^{(i)}(s+\varepsilon)$: eigenspace dimension $=\operatorname{ord}_{s+\varepsilon}\zeta$, additive over exponent sets. Mellin
    residues: power-like solutions force $\zeta(s+\varepsilon)=0$ at every exponent present.

### Extraction
12. **Energy quantiles** keep mass $(s-r)\pm1/E$ and antipodal work $W/E\to-(s-r)$.
13. **Common cofactor limit.** One subsequence (along any cofinal family) makes every $K_T(j,k)$ converge: PSD,
    $|K(j,k)|\le1/\sqrt{jk}$, packet contraction $Q(pa)\le Q(a)/p$, scaled diagonals $pK(p,p)\in[0,1]$ antitone;
    admission ⇒ unique kernel; the kernel family is a singleton or has continuum cardinality; nonuniqueness
    forces escape.
14. **Wiener module.** Every limit has a cyclic Hilbert realization with $\|V_p\|\le p^{-1/2}$, a contractive
    $\mathcal W_{1/2}$-representation, nonempty hull; on escape $\emptyset\ne\text{hull}\subseteq\text{obstructionHull}(\mu_\varepsilon)$;
    contracted modules $K_p(j,k)=K(pj,pk)/K(p,p)$ with annihilator $I:\delta_p$.
15. **Module structure.** Admitted modules are faithful, infinite-dimensional, full Bohr hull: a
    finite-dimensional or non-faithful actual module forces escape. Annihilator quotient finite or continuum;
    finite index = joint character multiplicities; rank-one characters are augmentation or $\eta(p)p^{-s}$,
    $s\ge\tfrac12$ (magnitudes forced, signs/exponents not tied to zeros); at row level tiedness is automatic.
    Hulls are conjugation-symmetric.
16. **Unit transport.** Möbius and Liouville modules are unit-equivalent.
17. **Origin boundaries.** Escape records realize every positive origin mass $c$: shifted Gram $K+c/\max(j,k)$
    (faithful), raw $(K+c)/(1+c)$ — shifted, not actual zero-origin limits.

### Countermodels
18. White noise satisfies the compactness laws with a unique antipodal extension; prime-deleted white noise
    violates horizon order; the augmentation model has hull outside every half-plane point. Gram laws do not
    classify the source.

---

## 4. Pillar theorems

1. **Scale separation** (`tendsto_forcingEnergy_div_receiver_atTop`, `no_common_scalar_normalization`).
2. **Gram tangent** (`gram_distance_div_receiverEnergy_eq_one`).
3. **Paid renormalization and antipodality** (`admits_or_renormalized_inversion_is_homogeneous`,
   `renormalizedCofactorVariation_sq_le`).
4. **Pole trace and commutator** (`actualPoleTrace_eq_forcingPowerCoefficient`, `admits_or_moving_cofactor_commutator_vanishes`).
5. **Symbol / index of $\tilde D$** (`powerRow_renormalizedInversion_bounded_iff`, `powerLogRows_global_renormalizedInversion_iff_order`).
6. **Common limit and Wiener module** (`exists_cofactorGram_limit`, `admits_or_moduleHull_subset_obstructionHull`).
7. **Faithfulness dichotomy** (`faithful_or_receiver_escapes`, `receiver_escapes_of_finiteDimensional`).

---

## 5. Traps

- Pointwise disappearance of forcing does not justify discarding its global pairing.
- Power subtraction on the actual row is not a bounded operator on arbitrary rows.
- Finite forcing mass controls bounded cell errors, not the receiver prefix.
- Vanishing $E_T/F_T$ allows $E_T\to\infty$.
- A PSD or rank-one limiting Gram can lose the critical distance coordinate.
- Fixed words lose successor selectivity under energy normalization.
- Termwise absolute cofactor control has the half-damping threshold.
- Entrywise convergence does not justify a moving cutoff or infinite cofactor sum.
- A nonzero common Gram module is not evidence of escape (it exists when admitted).
- Antipodality and Gram laws hold for white noise; source realization is essential.
- Shifted origin-reset rows are not unshifted actual limits.
- $h=D+R$ with $D,R\ge0$ gives no upper bound forcing $D=0$.

---

## 6. Open problems

1. **Joint extraction**: one carrier holding fixed covariances, quantile signed work and the moving cofactor
   tail, without exchanging an infinite sum and a limit. Via $H_\varepsilon$ the tail is bounded by consecutive
   dilation differences $\|D_jA-D_{j+1}A\|$: a **dilation-regularity** question.
2. **Exclusion / source selectivity**: an independent estimate excluding $\tilde Du\approx-u$ for escape states.
   Rows obeying two dilation laws with $O(1)$ errors and the inversion law exist exactly at zeros; the gap is
   that escape states need not satisfy polynomial $D_2,D_3$ laws with absolute errors.
3. **Module classification**: is hull = obstructionHull; are rank-one signs/exponents tied to zeros; exclude
   finite-dimensional escape modules by a source law.
4. **Mixed Bézout/Vaughan covariance**: summable signed gain after centring.
5. **Successor dynamics**: moving words acting nontrivially at the escape scale with proved boundary cost.
6. **Operator domains**: domain invariance and critical-norm bounds for the full renormalized operator.
7. **Shared allocation** across overlapping carriers and one Gamma/polar reserve; **anti-collapse** of actual
   divisor packets with multiplicity.

## 7. Tools to build

A dilation-regularity estimate for consecutive cofactor dilates; a source law forcing polynomial
$D_2,D_3$ relations on escape states; a module invariant finer than the annihilator hull.

## 8. Contribution criteria

A full no-escape theorem extracts a nonzero state from any divergent receiver, retains the signed and moving
data, and excludes it by an independent source relation for a cofinal damping family; or proves a direct
energy estimate. A contribution states the source property used and countermodels excluded, the signed
residual and its norm, treatment of moving support, overlap, boundary and multiplicity, and the consuming
receiver. Keep horizon, damping, cutoff, location and scale quantifiers visible; charge overlaps, new cells,
boundaries and the Gamma/polar reserve once; allow diffuse escape (no fixed bad packet, no assumed gap).
