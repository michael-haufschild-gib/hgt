# Arithmetic Positive Duality (APD)

Namespace `GaloisForLFunctions.ArithmeticPositiveDuality`; umbrella `ArithmeticPositiveDuality.lean`.

**Question.** The explicit formula is a Poisson summation between two measures: the prime measure (positive
because $\Lambda\ge0$) and the zero measure (positive exactly under RH). Everything the corpus has *forced* about
$\zeta$ has one shape: positivity + an exact self-dual identity + an integer ⇒ rigidity. What is the complete
rigidity and capacity theory of positive arithmetic distributions under Poisson self-duality and integer
quantization? What can positivity on the prime side force on the zero side, how much zero charge can each
positive structure carry, and which structure carries none?

APD is the rigidity theory of **positive Poisson pairs** $(\mu,\hat\mu)$: one side with arithmetic support
($\pm\log n$, lattices, $S$-unit groups), the other a spectrum. Objects: positive-definite functions on groups of
finite rank and their Fourier measures on tori. Mechanism: the **spectral gap identity** (an exact sum of
nonnegative terms equals a computable constant; integrality or self-duality turns it into rigidity).
Measurement: **capacity** — the zero charge a positive structure can carry and the integer that pays for it.

**Inserted vs intrinsic charge.** Inserted charge is created by deforming a positive system; the pole pays for
it exactly. Intrinsic charge is the zero set of $\zeta$ itself; no pole count reaches it. RH = intrinsic off-line
charge of $\zeta$ is zero.

---

## 1. Place in the research

The walls are three readings of one sentence: *what forces the actual source to be blind to off-line zeros?*
Over $\mathbb F_q$ the answer is one object (intersection theory with integer pairing, finite rank, positivity
from sections, a base with nonnegative tensor-power traces). Over $\mathbb Z$ the corpus has the pairing, the
Lefschetz/adjunction identities, the signature law and the maximal blind carrier; the missing ingredient is a
structure, not an estimate.

**Exhausted mechanism classes:**

| Class | Exhausting theorem |
|---|---|
| Quadratic positivity on a sharp-stable convolution ideal | lies in the maximal blind ideal (ACS) |
| Quadratic positivity on a scale-shift-invariant test space | blind |
| Finite harmonic coupling by a nonnegative cosine polynomial | Fejér barrier; interior gain only from growth input (MPG) |
| Multi-channel positive certificates | direct sum of one-channel problems, one per rational fibre |
| Height-coupled positivity in completed positive systems | boundary capacity + a $1/\log T$ collar with $\le\kappa^2$ exceptions (SBWF) |
| Integer quantization in dlVP coupling | no budget below the first quantum at the critical line |
| Pole order on positive relative deformations | index–pole conservation; pays inserted charge only (RHTower) |
| Positive relative deformations of $\xi$ at pole order one | none: $E=c\xi$ (SBWF) |
| Positive functionals on the affine group $\operatorname{Aff}(\mathbb Q)$ | induced from the dilations; the successor reads only the continuous dilation spectrum |
| Finitely many linear readings | cannot supply Bézout (ACS) |

**Four instances of one law.** Forcing: boundary forcing (MPG: $\zeta(1+it)\ne0$) and theta forcing (a positive
measure with Riemann's self-dual theta law is the integer comb; on Beurling systems the FE forces $\zeta$).
Capacity: boundary capacity ($\lfloor k/2\rfloor$ zeros per pole of order $k$) and relative conservation (Weil-index
increment = pole increment + critical traffic). **Open core:** the third forcing instance in the strip — a law
bounding intrinsic charge, whose integer is not pole charge and whose gain does not scale with its cost.

| Programme | Interface |
|---|---|
| MultiplicativePositivityGeometry | Rank-one height side: boundary divisor, Fejér barrier, growth law, boundary capacity |
| StripBochnerWeilForcing | Strip side: completed positive systems, collective capacity, gauge collapse, pole-order-one rigidity |
| `RHTower` deformations | Pole-order-two strays, refunded quartets, index conservation |
| ArithmeticOrientationGeometry | Scale side: orientation = PD of orbit correlation; spline two-prime orbit decides RH |
| ArithmeticCastelnuovoSeveri | Maximal blind ideal, Meyer source, golden datum |
| BiarithmeticGeometry, SignedSuccessorArithmetic | Successor and affine action |
| ArithmeticDefectRigidity, ArithmeticContinuationAndCriticalEnergy | Limits: cofactor modules, escape states |
| ScaleSignedIncidenceCriticality | A finite box of $\mathbb Z^2$ is a bounded-aperture condition |
| TransThresholdPairCorrelation | Signed close-prime-pair surplus: a prime-side coefficient the zero side cannot see |

---

## 2. Why

**The explicit formula is a Poisson pair.** For even $g$, $\sum_\rho\hat g(\gamma_\rho)=\hat g(i/2)+\hat g(-i/2)-\sum\Lambda(n)n^{-1/2}(g(\log n)+g(-\log n))+$
(archimedean). Left: zero measure $\mu_Z$; right: prime measure $\mu_P\ge0$. RH ⇔ $\mu_Z\ge0$; in Bochner form, every
spectral kernel $y\mapsto W(\tau_y(f\star\tilde f))$ is the characteristic function of a positive measure.

**The two positivities are Fourier dual.** Height variable: $u\mapsto\Re(-\zeta'/\zeta)(\sigma+iu)$ is PD (known, MPG). Scale
variable: $t\mapsto\Re W(f,f(\cdot-t))$ is PD iff $|\hat f|^2\mu_Z\ge0$ (the theorem, AOG). The prime-free gap $|x|<\log2$ lies
on the known side, so gap rigidity on the Weil pair yields density statements, not lattice support.

**Forcing is rigidity**: an exact identity with sides of different regularity, a sum of nonnegative terms against a
computable constant, then quantization (integer PD functions are sign characters; the Fejér tent transform
$\operatorname{sinc}(\pi\xi)^2$ vanishes exactly on $\mathbb Z\setminus\{0\}$). Weil's theorem for curves is the calibration:
the trace sequence is PD on $\mathbb Z$ with integer mass $2g$.

**Capacity is counted by the pole** on the boundary and for inserted charge (trace condition at $x=1$; each removed
critical pair refunds one unit; pole order two buys a real off-line pair or a refunded quartet; pole order one
admits nothing). **Intrinsic charge is not**: the bookkeeping gives only lower bounds on $\zeta$'s index.

**Rank helps on the zero side only.** Height rank adds nothing per channel; scale rank one is blind (Wolff), scale
rank two decides RH.

**Amplification is depth-homogeneous over $\mathbb Z$.** Harmonic twists, Følner coupling, family averages and
tensor powers gain on depth exactly as fast as they pay in arithmetic length. Over $\mathbb F_q$ Deligne escapes
through a base with nonnegative even tensor powers and a fixed loss.

---

## 3. Objects and language

| Object | Meaning | Lean |
|---|---|---|
| Poisson pair; gap; tent | $\int\mathcal Fg\,d\mu=\int g\,d\nu$; $(-a,a)\setminus\{0\}$ massless; $\max(0,1-|x|)$ | `IsTentSelfDual`, `tentAt`, `diracComb` |
| Prime measure | $\tfrac12\sum\Lambda(n)n^{-1-x}(\delta_{\log n}+\delta_{-\log n})$ | `primeMeasure` |
| Positive-definite function | on $\mathbb Z^\iota$, on a group, even real | `IsPosDefOnLattice`, `IsPosDefOnGroup`, `IsEvenPosDef` |
| Fourier measure, Kronecker line | measure on the torus; $t\mapsto(\gamma_it)_i$ | `fourierCoeff`, `kroneckerLine` |
| Certificate fibre; channels | modes in $\mathbb Z\omega$; $\mathbb Q$-independent frequencies | `fibreCoeff`, `channelFreq` |
| Sign character | $\chi:H\to\{\pm1\}$ extended by zero | `IsSignCharacter`, `extendByZero` |
| Quantum budget | $b(\eta)=(\sqrt A+\sqrt{G\eta})^2/B$ | `quantumBudget` |
| Completed positive system | PD in heights on $\Re s>1$; order-one $\Lambda$ with FE | `CompletedPositiveSystem` (SBWF) |
| Relative deformation, refund | reflection-antisymmetric correction of $\zeta$'s log measure | `poleIncrement`, `indexIncrement`, `refundTransform` (RHTower) |
| Affine group of $\mathbb Q$ | $x\mapsto ax+b$; dilations, successor; Hecke state $(nd)^{-s}1[db\in\mathbb Z]$ | `AffineGroupQ`, `dilation`, `successor` |
| Prime torus, Kronecker line in it | spectrum of $\mathbb Q_{>0}$; $x\mapsto(x\log p/2\pi)_p$ | `archPoint` |
| GNS space | Hilbert space, representation, cyclic vector of a PD function | — |
| Critical-jet topology | coarsest topology making critical Meyer jets continuous | `criticalJetTopology` |

**Words.** *Positive side / spectral side*; *forcing* (vanishing on the spectral side); *capacity*; *receiver*
(RH-equivalent reformulation, never its own input); *dominated vs oscillatory payment*; *depth-homogeneous*.

---

## 4. Mechanisms

1. **Spectral gap identity**: pair a Poisson identity with a nonnegative test supported in the dual gap.
2. **Zero set of the tent transform** puts a positive measure on the lattice.
3. **Gram quantization**: integer PD with $\varphi(0)=1$ ⇔ sign character of a subgroup.
4. **Bohr projection** of a certificate onto resonant fibres; nonnegativity survives.
5. **Product extremals** $Q_1(\gamma_1t)Q_2(\gamma_2t)$ for independent channels.
6. **Fejér means on lattices** + Prokhorov ⇒ Herglotz–Bochner on $\mathbb Z^\iota$; restriction = Kronecker push-forward.
7. **Induction from a subgroup**: Gram forms split per coset.
8. **Budget arithmetic**: an integer below one is zero, an even integer below two is zero.
9. **Følner capacity** and Hadamard zero-pair series in completed systems.
10. **Trace bookkeeping** and **refund rigidity** (Landau continuation under $s\mapsto1-s$).
11. **Affine spectral calculus.** Translations act on archimedean dilation eigenvectors by one constant per
    frequency and never mix them with the continuous part ⇒ successor = blind constant + successor of the
    continuous part; atomic dilation parts admit only boxes of blind extensions; every $L^2$ wave (any nonzero
    absolutely continuous dilation part) has a visible, nonconstant successor; GNS orbits extend to real scales.

---

## 5. Pillar theorems

1. **Theta rigidity**: a positive measure on $[1,\infty)$ with Riemann's theta law is $c\sum\delta_k$; a degree-one Beurling
   system with the completed FE is $\zeta$ (`measure_eq_of_measureTheta_relation`, `beurlingSystem_rigidity_of_completed_functional_equation`).
2. **Poisson rigidity**: positive self-dual measure with unit gap ⇔ multiple of the Dirac comb; the unit gap is sharp;
   one-sided gap gives only density (`tentSelfDual_iff_eq_smul_diracComb`, `exists_tentSelfDual_not_comb`, `measure_Icc_le_of_poissonPair`).
3. **Integer classification** on every abelian group; isolation forces $1_{\{0\}}$ iff no 2-torsion (`intValued_posDef_iff_signCharacter`).
4. **Herglotz–Bochner** on $\mathbb Z^\iota$ and on $\mathbb Q_{>0}$ (prime torus) (`isPosDefOnLattice_iff`, `isPosDefOnGroup_posUnits_iff`).
5. **Fibre barrier and independent channels**: the barrier of a certificate is that of its fibre; joint barrier is
   the product (`multiFrequency_purchase_le_fibre_fejer`, `twoChannel_joint_barrier_attained`).
6. **Two-prime orbit is a Bochner problem on $T^2$** (`riemannHypothesis_iff_exists_torusMeasure`) — a receiver.
7. **Quantum budget**: no budget below the first quantum at $\Re s=\tfrac12$, parity included (`fejer_quantumBudget_half`).
8. **Topology of the blind ideal**: closed in the natural Fréchet topology; dense in the critical-jet topology,
   closed there iff RH (`isClosed_meyerTraceBoundedIdeal`, `isClosed_criticalJet_iff`).
9. **Weil over $\mathbb F_q$ = PD on $\mathbb Z$**; golden datum fails on every group (`curve_rh_tfae`, `not_exists_posDef_golden`).
10. **Positivity on both sides** of the explicit formula (`positive_duality_of_the_explicit_formula`).
11. **Affine laws.** Restriction–induction: affine positivity is induced from dilations (`exists_isPosDefOnGroup_extension_iff`);
    the integer successor forces the Hecke weight $(nd)^{-1/2}$, extremals are twisted Haar states, threshold $s\ge\tfrac12$ is
    the critical line, Bost–Connes temperature $\beta$ forces $(nd)^{-\beta/2}$ (`integer_successor_hecke_weight`,
    `isPosDefOnGroup_heckeState_iff`, `bc_successor_hecke_exponent`, `heckeExtremal_iff`); archimedean PD functions live on the
    Kronecker line while arithmetic successors force Kronecker-null spectra (`spectralMeasure_eq_map_archPoint`,
    `integer_successor_kronecker_null`); Weil's correlation admits only blind successors, its extensions indexed by the
    zeros (`weil_successor_blind`, `weil_extension_classification`); any nonzero AC dilation part has a visible extension
    (`exists_nonblind_affine_extension_of_ac_part_ne_zero`).

**Foundations from siblings**: boundary forcing and capacity (MPG `boundary_forcing_law`, `total_zero_mass_le`); completed-system
capacity, gauge collapse, pole-order-one rigidity (SBWF `collective_half_pole_interior_forcing`,
`simple_pole_nonneg_laplace_refund_rigidity`); inserted charge and index–pole conservation (RHTower
`lambdaPositive_refunded_complex_stray`, `indexIncrement_eq`, `absolute_inequality_fails`); maximality (ACS `isGreatest_meyerSharpPositiveIdeal`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| FE + positivity has many models | At degree one on Beurling systems only $\zeta$ |
| Hamburger uses only the FE | Remainder holomorphic on the strip with quadratic decay is part of the statement |
| The FE is a self-duality of the Weil pair | It is of the integer measure; on the Weil pair positivity and gap sit on the same side |
| Any gap gives a lattice | Only the unit gap |
| Coupling heights/primes buys more per zero | Fibre barrier; completed systems give boundary capacity only |
| Rank-two positivity is progress | The two-prime Bochner problem is a receiver |
| A non-commutative carrier adds positivity | Affine positivity is induced from dilations |
| Prescribing the integer successor constrains Weil's correlation | It excludes it (Hecke decay, Kronecker-null spectra) |
| Closedness of the blind ideal is a critical property | Critical data make it dense |
| Pole order bounds off-line zeros | Counts inserted charge exactly, intrinsic not at all |
| A complex off-line quartet needs pole order three | Two suffices after one refund |
| A larger amplification gives a rate | Every tested amplification is depth-homogeneous |
| Integer point counts force RH over $\mathbb F_q$ | Golden datum |

---

## 7. Open problems

1. **The third forcing instance in the strip**: an exact identity on the Weil pair with a quantization step bounding
   **intrinsic** charge. Candidate integers: torsion orders, finite affine quotients, Hecke-cycle lattices, the Hodge
   defect with its pole-plane budget.
2. **Oscillatory capacity**: a positive structure measuring oscillatory payment of $\zeta$'s own zeros, with the
   conservation identity as its relative case.
3. **Coupled scale positivity** beyond point-stable carriers (Rankin–Selberg sources, cones without convolution
   closure); for point-stable carriers positivity forces isotropy, not vanishing.
4. **A base over $\operatorname{Spec}\mathbb Z$**: a self-dual system with nonnegative even tensor powers and computable pole part.
   Multiplicative-only constructions are expected to fail on over-regular Beurling countermodels.
5. **Depth homogeneity as a law** for each amplification class, with positive survivors.
6. **Successor coordinates**: classify dilation parts compatible with $1_{\mathbb Z}$; AC parts are seen, atoms are not —
   whether singular continuous dilation spectra are seen.
7. **Rank-$r$ realization** of PD profiles by integral (Beurling) systems.
8. **Positive crystalline measures beyond degree one**; equality case of completed capacity (even $\kappa$).
9. **Spectral readings of limits**: escape states of cofactor modules as horizon Grams of
   $G(s)=\zeta(s)(1/\zeta(s+\varepsilon)-1/\zeta(1+\varepsilon))/s$.
10. **Signed additive prime correlations** at the square-root threshold (TTPC).

## 8. Tools to build

Oscillatory capacity calculus (dominated vs oscillatory payment kept apart); coupled scale positivity with matching
maximality theorems; base constructions over $\operatorname{Spec}\mathbb Z$; spectral readings of limits; Bochner–Schwartz for the Weil
distribution beyond characteristic functions.

## 9. Contribution standard

Unconditional; name positive side, spectral side, gap and integer; say whether the integer counts inserted or
intrinsic charge and how its depth gain scales with arithmetic cost; state an identity, classification, sharp
barrier, capacity or rigidity law (not a new RH equivalent); report on the battery — curves (reproduce Weil), golden
datum (fail), Beurling countermodels, pole-order-two strays and refunded quartets (separate from $\zeta$), pole-order-one
rigidity (reproduce); record the positive survivor of every no-go. Positivity on one side is known, on the other is
the theorem; rigidity before estimates; calibrate over $\mathbb F_q$.
