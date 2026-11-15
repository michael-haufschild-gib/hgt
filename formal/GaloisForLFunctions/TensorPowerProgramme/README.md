# The Tensor-Power Programme Ω (TPP)

Namespace `GaloisForLFunctions.TensorPowerProgramme`; umbrella `TensorPowerProgramme.lean`; 12 modules.
Specification: §2.22 of [the review-1511 obstacles summary](../../../docs/reports/review-1511/obstacles-summary.md).

*Deligne's tensor-power argument, carried to `Spec ℤ`: what it needs, where it breaks, and which
object would make it run.*

## 1. Motivation

Deligne's proof of the Riemann hypothesis over finite fields is the only argument of its shape that
has proved an RH. For a sheaf `F` on a curve `U` over `𝔽_q` with real traces, a polarization of
weight `w` and large monodromy it has four steps:

1. **Pointwise data.** At every closed point `x` the Frobenius has eigenvalues `α_{x,i}`.
2. **Free positivity.** The traces of `F^{⊗2k}` are `t_x^{2k} ≥ 0`, so the Euler product of
   `F^{⊗2k}` has nonnegative coefficients and converges up to its first real singularity.
3. **A pole law uniform in `k`.** The `L`-function of `F^{⊗2k}` is rational, its poles come only
   from `H²_c`, the coinvariants of the geometric monodromy; with large monodromy these are spanned
   by products of the polarization, of weight exactly `kw + 2`. The first pole sits at a place fixed
   in advance, whatever the eigenvalues are.
4. **The limit.** One Euler factor is dominated by the whole product, so `|α_x|^{2k} ≤ q_x^{kw+1}`
   for every `k`, and `k → ∞` gives `|α_x| ≤ q_x^{w/2}`.

The corpus already owns the receiver, the bookkeeping and several pieces. RH is equivalent to a
bound of the prime-trace moments `Σ_{p≤N} log p (2 Re S(log p))^{2k} = O(N^{1+A})` with `A`
independent of `k` (`SurfaceOfSpecZ.riemannHypothesis_iff_moments_primeTraces`): positivity is
free and the uniformity is RH. Frames, towers, levers and walls are a proved calculus
(FamilyContinuationTheory, ExponentDynamicsOfTheCriticalStrip). Products of the spectrum alone are
depth-homogeneous and gain nothing (ArithmeticKunnethTheory, layer 1). A family sees its members of
positive mass through the moments of its full traces (InfiniteRankPurityTheory).

What the corpus does not have is step 3 over `ℤ`: a base whose tensor powers have a pole law
fixed in advance, and in which the zeros of `ζ` are local parameters. TPP is the programme of that
step. It asks what the pole law is made of, proves where it is missing, prices every substitute
the corpus has (the frames of the cubic probe, the Möbius sign, the completions), and writes the
missing object as a list of axioms. Under the working prior of the report — no shortcut, every
question at its least favourable answer — each stage still ends in a theorem: a calibration, a
price law, a ruler no-go, a pencil or the axiom list of the object RH needs, a completion or a cost
theorem, a transport or an intrinsic floor.

## 2. The argument in the frame calculus

A **frame** `(c, k)` transports a zero of real part `β` to a zero of a correction at `kβ − c`.
With a top bound `b` for the correction (its Euler product converges and does not vanish on
`Re > b`) it gives the one-step bound `β ≤ (c + b)/k`; a coupled tower of frames gives the centre
`c/(k − 1)`, and every bound is `max(σ₀, centre)` with `σ₀` the estimate floor
(`FamilyContinuationTheory.abscissa_le_max_fixedPoint_of_tower`).

The `k`-th tensor power of a datum moves an eigenvalue of depth `δ` to depth `kδ`, i.e. a zero
at `β` to `kβ − (k − 1)/2`. It is the frame `((k − 1)/2, k)`: with the top bound `1` it gives
`½ + 1/(2k)`, its tower centre is `½`. Three lines of frames organize the programme:

| Line | Price `c` at period `k` | One step (`b = 1`) | Tower centre | Source |
|---|---|---|---|---|
| Deligne | `(k − 1)/2` | `½ + 1/(2k)` | `½` | tensor powers with a pole law |
| Sign | `k/2` | `½ + 1/k` | `k/(2(k − 1)) → ½` | short Möbius-signed Gauss monomials, priced by Stickelberger |
| Completion | `2k/3 − 1` | `2/3` | `2/3 − 1/(3(k − 1)) → 2/3` | Gauss pairings completed factor by factor |

The sign line lies exactly half a unit above the Deligne line: the Möbius sign costs `½` at some
place (`ExponentDynamicsOfTheCriticalStrip.Stickelberger.half_lt_stickelbergerPrice_div`), and the
cost disappears in the limit. The completion line meets the sign line at `k = 6`, the frame
`(3, 6)` of the cubic probe and the wall `3/5` of every tower of Gauss pairings
(`three_fifths_le_towerValue_pairings`). Beyond `k = 6` completion, not the sign, is the
obstruction of the producer.

## 3. Objects

| Object | Meaning |
|---|---|
| Euler datum over a base | points `x` with norms `N(x) > 1`; at each point local parameters `α_{x,i}`, closed under conjugation, so the level traces `t_x(n) = Σ_i α_{x,i}^n` are real |
| Depth, width | `δ(α) = log‖α‖ / log N(x) − w/2` for weight `w`; the width `W` is the supremum of the depths |
| Tensor-power moments | `D_{2k}(s) = Σ_x Σ_n log N(x) · t_x(n)^{2k} · N(x)^{−ns}`, nonnegative coefficients; the moment exponent `a_k` is its abscissa; for `ζ` in Lean `MomentBound k a`, `momentExponent k` over `SurfaceOfSpecZ.primeTraceMoment` |
| Pole law | `a_k ≤ 2k·(w/2) + A` for all `k` with `A` independent of `k`: the content of step 3 |
| Edge | the part of the `2k`-th tensor power that fixes `a_k`: tuples of parameters whose product survives the averaging over the base |
| Polarization pair | `α` and `N(x)^w/α` (functional equation); their tensor has the known size `N(x)^w` |
| Conjugation pair | `α` and `ᾱ`; their tensor has the unknown size `‖α‖²`. Purity is the coincidence of the two pairings |
| Flow datum | Frobenius at `x` is `N(x)^D` for one operator `D`: the motive of the zeros `⊕ ℤ(−ρ)` over `Spec ℤ`. Its geometric monodromy is trivial |
| Flow datum (Lean) | `flowTrace z b n = Σ_i b_i n^{z_i}`, moments `flowMomentTerm z b k σ n = Λ(n) |t(n)|^{2k} n^{−σ}` |
| Abelian base | every local system a sum of characters (Dirichlet and Hecke twists, Jacobi-sum characters, the archimedean family); in Lean `IsAbelianBase N λ ev`: norms, von Mangoldt weights, characters with conjugation = inversion, linear independence, and the prime number theorem of each character |
| Twisted datum (Lean) | `twistTrace` `t(x) = Σ_i b_i χ_i(x) N(x)^{z_i}`, moments `twistMomentTerm` |
| Tuples (Lean) | `tupleMode` `Σ z_{a_j}`, `tupleWeight` `Π b_{a_j}`, `tupleChar` `Π χ_{a_j}`; pairs `pairMode` `Z_{a,a'}`, `pairWeight` `B_{a,a'}`, `pairChar` `χ_a χ_{a'}⁻¹`; edge residues `edgeResidue`, `twistEdgeResidue` |
| Adams power (Lean) | `adamsTrace α m n x = Σ_i (α_{x,i}^{mn} + α_{x,i}^{−mn})`: moves modulus `N^δ` to `N^{mδ}`; its Rankin–Selberg square `adamsSquareCoeff`; frequencies `levelFreq` `(n+1) log N(x)`; `AdamsPoleLaw`: every square continues to `Re s > 1` |
| Pencil through `ζ` (N1) | a base with real level traces, the Deligne pole law for all even tensor powers, and `ζ` as the fibre at a prime point; in Lean `PencilThroughZeta`, with `zetaCycle` the one test whose Lefschetz numbers read the zero width at every prime |
| Levers of the lines (Lean) | `deligneLever k` `b ↦ ((k−1)/2 + b)/k`, `signLever k` `b ↦ (k/2 + b)/k`, `completionCentre k` `(2k/3 − 1)/(k − 1)` |
| Sign-line completion (N2) | a joint completion of a Möbius-signed monomial of period `k ≥ 7` priced `c = k/2` |
| Exact transport (N3) | zeros of `ζ` forced into a period-`k` family with no estimate floor and constants uniform in `k` |
| Angle base of `ℚ(ω)` (Lean) | points `(v, m)` for the prime powers `v^{m+1}`, norm `N(v)^{m+1}`, weight `log N(v)`, characters `j ∈ ℤ` acting by `ψ₆(v)^{j(m+1)}` with `ψ₆` the sextic Grössencharacter: `angleNorm`, `angleLam`, `angleEv` |
| Signature of a Gauss pairing (Lean) | the orders `m_i ≥ 3` of the nonquadratic characters of a Möbius-signed tuple, closed by the involution when their number is even; weight `Σ (1/2 − 1/m_i)` (`signatureWeight`). Euclidean signatures: `(3, 3, 3)`, `(2, 3, 6)`, `(2, 4, 4)` |

## 4. Language

- **Ruler**: a criterion that reads the width exactly and produces no bound. **Lever**: a map `T` on
  exponents with `θ ≤ b ⇒ θ ≤ T b`. **Wall**: the fixed point a family of levers cannot pass.
- **Price** of a frame: `c`; the **half unit** is the gap `½` between the sign line and the
  Deligne line.
- **Top bound**: the abscissa right of which a correction has a convergent Euler product and no
  zeros. Tempered members have top bound `1` for free; a dilation has the Deligne frame with top
  `(k + 1)/2` and is a ruler.
- **Arithmetic fibre**: a member of a family with Dirichlet series, Euler product and functional
  equation. **Geometry**: a monodromy acting on the zeros of the members.

## 5. Mechanisms

1. **Free positivity, Rankin domination.** For real traces `t^{2k} ≥ 0`; a nonnegative Euler
   product that converges dominates each of its factors. A pole law turns this into
   `‖α_x‖ ≤ N(x)^{w/2 + A/(2k)}` for every `k` (ArithmeticKunnethTheory `tensor_moment_bound_iff`,
   InfiniteRankPurityTheory `norm_le_of_amortized_levelSums`).
2. **The ruler law.** For every datum `2kW ≤ a_k ≤ 2kW + a₀`, `a₀` the abscissa of the base, so
   `a_k/(2k) → W`. The tensor-power trick is a ruler plus a pole law; the pole law is its whole
   content.
3. **What a pole law is made of.** Over `𝔽_q`: rationality (the trace formula), poles only from
   coinvariants (`H⁰_c = 0` on an affine base), coinvariants of a large monodromy spanned by
   polarization tensors, and the known weight of the polarization. Monodromy alone does not suffice:
   an impure Frobenius has a lift with full `SL₂` image (`goldenFrobenius_has_split_lift`).
4. **Two pairings at the edge.** Under abelian monodromy the conjugation pair `α ⊗ ᾱ` survives the
   averaging, and the edge of every even tensor power carries `‖α‖^{2k}`: the pole law is the
   conclusion. Under symplectic monodromy only polarization pairs survive and the edge has the
   weight fixed by the functional equation. Over `Spec ℤ` the two pairings are `ρ ↦ ρ̄` and
   `ρ ↦ 1 − ρ`; RH is their coincidence (GaloisTheoryOfZeros).
5. **Frames are tensor powers with a price.** A frame `(c, k)` is a `k`-th tensor power whose
   correction is completed at the cost `c`; `c − (k − 1)/2` is what the completion pays above
   the polarization.
6. **Diagnosis over `Spec ℤ`.** The motive of the zeros is a flow datum: all Frobenii are
   simultaneously diagonal, the geometric monodromy is trivial, every tuple of zeros contributes
   to the edge and nothing cancels. The zeros have to vary in a family with monodromy.
7. **Coinvariants are everything, nothing cancels.** For a flow datum the `k`-th tensor moment is
   `Σ_{a,a'} B_{a,a'} (−ζ'/ζ)(σ − Z_{a,a'})` over pairs of `k`-tuples of modes; each tuple carries
   its own shifted pole. At the edge `σ = 1 + 2kW` the surviving pairs are the conjugation pairs
   of top tuples, and the residue is `Σ_w ‖Σ_{Σ z_a = w} Π b_a‖²`, a sum of squares that the
   top mode of largest imaginary part makes positive. On an abelian base the characters only
   split the squares further (`Σ ‖Σ_{(Σ z_a, χ_a) = κ} Π b_a‖²`); positivity is the linear
   independence of characters, and the analytic input is the prime number theorem of each
   character (a pole only for the trivial one, no zero on `Re s = 1`).
8. **Polarization fixes the edge.** For a polarized datum (`α ↔ α⁻¹`) the Rankin–Selberg square of
   the `m`-th Adams power has nonnegative coefficients; if it continues analytically to `Re s > 1`,
   Landau's theorem makes it converge there, and one point of the base gives `|α|^m ≤ N(x)` for
   every `m`: purity. In rank two `p_m² = p_{2m} + 2`: the square is the next Adams power plus the
   two polarization pairs `α^m ⊗ α^{−m}`, of weight `det = 1` whatever `α` is, so the pole law
   reduces to the continuation of the Adams series themselves — the constituents. For
   `GL₂`-automorphic data they are differences of symmetric-power log-derivatives (the classical
   route from functoriality to Ramanujan); for flow data they are the shifted modes.
9. **The top bound one is temperedness.** For a polarized base the top bound `1` of every Adams
   power holds exactly when the parameters are unitary: tempered members get it for free, and a
   family that has it for all powers is tempered. Uniformity in the period is never a by-product.
10. **A pencil is RH, its source is the content.** With `ζ` as the fibre at a prime `p`, the pole
   law and Landau give `|W(T_{p^n} g, g)| ≤ C p^{n/k}` for the one cycle `g` of `ζ`, so
   `p^w ≤ p^{1/k}` for every `k`. Conversely, under RH one prime alone is a pencil. The axiom list
   is therefore equivalent to RH; what N1 must add is a source of the pole law that does not know
   the parameters — the continuation of constituents that are `L`-functions of other objects.
11. **One Deligne frame suffices, the sign needs all periods.** A Deligne lever excludes every
   exponent right of `½`; a sign lever only those right of `k/(2(k − 1))`; the completion
   centres increase to `2/3` and the Gauss levers stop at `3/5`.
12. **The sign line is Euclidean.** A Gauss pairing of period `k` costs at least `k` times the
   weight of its signature, and Möbius parity makes the signature that of a sphere orbifold with an
   odd number of cone points; for three points the weight is `½` plus the normalized area of the
   triangle. The weight is `½` exactly at the Euclidean signatures and at least `7/10` otherwise.
   So the Gauss family never prices below the sign line, meets it only at the crystallographic
   periods `3, 4, 6`, and pays at least `k/5` above it at every hyperbolic signature.
13. **The prime number theorem is the whole abelian input.** Independence of the characters
   follows from the pole of the trivial character (`linearIndependent_of_pnt`), and for a number
   field the series of each character is `−L'/L` of its Euler product
   (`neg_deriv_div_eq_primePowerSeries`). An abelian base is the list of `L`-functions with a pole
   only at the trivial character and no zero on `Re s = 1`.

## 6. Questions

| # | Question | Answer, or what remains |
|---|---|---|
| Q1 (Ω1) | **Calibration.** Which inputs does the pole law need; does monodromy enter already over `𝔽_q`? | The pole law is the analytic continuation of the constituents' series; positivity converts it into convergence (`norm_eq_one_of_adamsPoleLaw`); in rank two the Adams powers are the constituents (`norm_eq_one_of_adams_continue`). On the Kummer/Fermat calibration curves no monodromy and no tensor power is needed: their eigenvalues are Jacobi sums, and purity is the identity of the two pairings (`conj_jacobiSum`, `jacobiSum_mul_jacobiSum_inv_eq_card`, `norm_jacobiSum_sq`); the same eigenvalues sit `p`-adically on the sign line (`stickelbergerPrice_jacobiTriple`): purity does not remove the sign cost. Monodromy enters only for non-CM families, where the trace formula supplies the constituents (ArithmeticKunnethTheory); over `ℤ` functoriality would. |
| Q2 (Ω2) | **Price ledger.** | Proved: the half unit at every period, one-step values `½ + 1/(2k)`, `½ + 1/k`, `2/3`; completion centres increase strictly to `2/3` (`signPrice_sub_delignePrice`, `deligneLever_one`, `signLever_one`, `completionStep_one`, `completionCentre_strictMono`, `tendsto_completionCentre`). |
| Q3 (Ω3) | **Diagnosis over `Spec ℤ`.** | Proved. For `ζ`: `2kw ≤ a_k ≤ 1 + 2kw`, `a_k/(2k) → w`, and the pole law at any weight `w₀` is `w ≤ w₀` (`two_mul_width_le_momentExponent`, `momentExponent_le`, `tendsto_momentExponent_div`, `exists_momentPoleLaw_iff`). For every finite configuration the exponent is exactly `1 + 2kW` and nothing cancels at the edge (`summable_flowMomentTerm_iff`, `edgeResidue_pos`). |
| Q4 (Ω4) | **Pencil.** Heat pencil, twist families, Fermat/Kummer family; else the axiom list of N1. | Heat: arithmetic only at `τ = 0` (ZeroConfigurationGeometry `exists_dirichlet_iff`). Twists: abelian, a ruler (`summable_dirichletMomentTerm_iff`). Kummer and Hecke: Jacobi-sum characters and Grössencharacters, abelian; the angle characters `ψ₆^j` of `ℚ(ω)` form an abelian base (`isAbelianBase_angle`), so their tensor moments are rulers (`summable_angleMomentTerm_iff`); the transport of `ζ` into them is Q6. Axiom list: `PencilThroughZeta`, with `riemannHypothesis_of_pencil` and `riemannHypothesis_iff_nonempty_pencil`: the list is RH; N1 is a source of its pole law (mechanism 10). |
| Q5 (Ω5) | **Frame track.** A sign-line completion at period `k ≥ 7`. | Open for completions outside the Gauss family (stage 2–3 of §7). The Gauss family never prices below the sign line, `c ≥ k/2` (`half_period_le_pairingC`); it meets it only at the periods `3, 4, 6` (`period_mem_of_pairingC_eq_half`), whose signatures are Euclidean (`signatureWeight_dichotomy`); every hyperbolic signature pays at least `k/5` above it, sharp at `(2, 5, 10)` (`euclidean_of_pairingC_lt`, `exists_zmod_eleven_pairing`). So no Gauss pairing is a sign lever at period `5` or at any period `k ≥ 7` (`half_period_lt_pairingC`), and no Gauss pairing beats the sign lever of its period (`signCentre_le_coupledBarrier`). One valid sign lever of period `k` gives `Θ ≤ k/(2(k−1))`; sign levers at all large periods give RH (`riemannHypothesis_of_signLevers`). The Stickelberger price of the `A₂` coefficients (stage 1) is not computed. |
| Q6 (Ω6) | **Exact transport.** Continuation of the cubic probe to the centre of `(3, 6)` by identities. | Open; the dual series of the probe (stage 1) is not written. |
| Q7 (Ω7) | **Uniformity.** | The top bound `1` for all Adams powers is temperedness (`adamsPoleLaw_iff`). Open: conductor growth of order-`k` completions. |
| Q8 (Ω8) | **Assembly.** | Proved for levers: one valid Deligne lever, or valid sign levers at all large periods, give RH (`riemannHypothesis_of_deligneLever`, `riemannHypothesis_of_signLevers`). |
| Q9 | **Refutation.** Does every Euler–FE family through `ζ` have finite monodromy on its zeros; does every transport have an intrinsic floor? | Reformulated by `riemannHypothesis_iff_nonempty_pencil`: pencils exist iff RH (one prime is a pencil under RH), so no theorem about the existence of pencils can refute the route; a refutation must concern the sources of the pole law. In the abelian class the source is the conclusion (`exists_twistPoleLaw_iff`, `exists_poleLaw_iff`); Euler–FE deformations of `ζ` in the Hamburger class are rigid (EulerFETransportTheory `beurlingSystem_rigidity_of_decaying_defect`). Open: sources beyond abelian ones, and intrinsic floors of transports. |

## 7. The programme to close

Deligne's four steps over `ℤ`: pointwise data, free positivity and the limit are in the corpus; the
pole law is the programme. Three objects are missing:

- **N1** a pencil whose pole law has a source that does not know the parameters;
- **N2** a joint completion of a Möbius-signed monomial on the sign line at period `k ≥ 7`;
- **N3** an exact transport from `ζ` without estimate floor, uniform in the period.

| Stage | Statement | Status | A failure proves |
|---|---|---|---|
| 1 | Tools: Hecke characters of `ℚ(ω)` with infinity type as an abelian base; the dual series of the cubic probe; the Stickelberger price of the `A₂` coefficients | angle base built (`isAbelianBase_angle`); dual series and `A₂` price open | — |
| 2 | N2 at `k = 7`: one valid sign lever of period `7` gives `Θ ≤ 7/12` | open outside the Gauss family; inside it the cost theorem holds (`half_period_lt_pairingC`): every Gauss pairing of period `7` costs more than `7/2` | a cost theorem at period `7`: every completion costs more than `7/2`, and `3/5` is the wall of the Gauss family, not only of the completion class |
| 3 | N2 at all large periods, with constants uniform in the period (Q7) | open | conductor growth of order-`k` completions: an intrinsic floor above `½` (Q9) |
| 4 | N1: a base with non-abelian monodromy, `ζ` as a fibre at a prime point, constituents that are `L`-functions of other objects | open | finite or abelian monodromy on the zeros of every Euler–FE family through `ζ`; with the rigidity of Euler–FE data (`beurlingSystem_rigidity_of_decaying_defect`) this says that `ζ` lies in no family |
| 5 | Assembly | proved: `riemannHypothesis_of_signLevers`, `riemannHypothesis_of_deligneLever`, `riemannHypothesis_of_pencil` | — |

Stage 4 alone suffices and stage 3 alone suffices. Stage 2 is the first place where the programme
produces an exponent, and it presupposes estimates down to `7/12` (the estimate ladder of the cubic
probe). The pole law for `ζ` is a ruler at every weight (`exists_momentPoleLaw_iff`), so no
argument that produces it from the moments of `ζ` alone can succeed: the source is a second
object.

## 8. Tools

**From the corpus.** Frame and tower calculus with walls and mixed towers
(`pairingStep`, `towerValue`, `wall`); Stickelberger valuations and prices of Gauss sums
(`norm_gaussSum_extremalChar_pow`, `stickelbergerPrice_eq_half_mul`); the prime-trace receiver and
the width law at the primes (`riemannHypothesis_iff_moments_primeTraces`,
`zetaZeroWidth_le_iff_bddBelow_primeDegrees`); amortization over families
(`member_norm_le_of_family_moments`); `SL₂` invariants and the golden countermodel
(ArithmeticKunnethTheory); the heat monodromy and its comparison with the arithmetic group
(GaloisTheoryOfZeros); the cubic probe, its correction and rung (`correctionAbscissa_eq`).

**Built here.**
- Tensor moments of flow data and of abelian bases: coinvariant expansion, edge residue as a sum of
  squares, exact base loss (`flowMomentTerm`, `IsAbelianBase`, `twistMomentTerm`).
- The Rankin–Landau step for polarized bases at the level of analytic continuation, with Adams powers
  as the amplifier (`AdamsPoleLaw`, `adamsSquareCoeff`, `levelFreq`).
- The axioms of a pencil through `ζ` and their reduction to the one-cycle law at a prime
  (`PencilThroughZeta`, `zetaCycle`).
- The levers of the three lines and their assembly into RH criteria.
- The analytic package of an abelian base from `L`-functions: independence from the prime number
  theorem (`IsAbelianBase.of_pnt`), the Euler logarithm of a number field and its derivative
  (`eulerLog`, `primePowerSeries`), and the angle base of `ℚ(ω)` (`isAbelianBase_angle`).
- The signature weight of a Gauss pairing and its Euclidean–hyperbolic dichotomy
  (`signatureWeight`, `pair_signature`, `triple_signature`).

**To build (stage 1 of §7).**
- The dual series of the cubic probe (Q6).
- The Stickelberger price of the `A₂` coefficients (Q5).

## 9. Traps

| Trap | Truth |
|---|---|
| Positivity of even tensor powers forces purity | Golden data have positive even-tensor Euler coefficients and are impure (ArithmeticKunnethTheory) |
| Large monodromy forces purity | An impure Frobenius has a split lift with full `SL₂` image; the pole law is the input |
| The pole law needs the moments to converge | It needs only analytic continuation: positivity (Landau) converts continuation into convergence |
| Tensor powers of `ζ` amplify the depth | Products of the spectrum are homogeneous: gain equals depth times length |
| A family proves the purity of its members | Only members of positive mass, through moments of the full traces; without a measure, the closed strip |
| The heat pencil is a pencil | Only its fibre at `τ = 0` has a Dirichlet series; arithmetic group and heat monodromy agree on finite windows only |
| Twist families are a base | They are abelian: every even tensor moment has base loss exactly one and its edge is a positive sum of squares over conjugation pairs (`summable_dirichletMomentTerm_iff`) |
| Characters can cancel the edge | Distinct characters are linearly independent; the edge residue is a sum of squares that never vanishes |
| The Möbius sign is the obstruction | The sign line has wall `½`; completion caps the producer at `3/5` |
| A dilation transports zeros at the Deligne price | It has the Deligne frame with top `(k + 1)/2`: a ruler |
| Composing frames lowers the centre | Composite centres are convex combinations of the centres |
| Exact transport is a lever | The cubic correction moves bounds between `ζ` and the rung without loss: a ruler until the rung family has a seed |
| A Gauss completion reaches the sign line at a large period | Only at the periods `3, 4, 6`: the Euclidean signatures `(3, 3, 3)`, `(2, 3, 6)`, `(2, 4, 4)`; every other signature costs at least `7k/10` |

## 10. Pillar theorems

| Theorem | Lean |
|---|---|
| Flow data have base loss exactly one; coinvariants are shifted `−ζ'/ζ`; the edge residue is a positive sum of squares; the pole law is the width | `summable_flowMomentTerm_iff`, `ofReal_tsum_flowMomentTerm`, `edgeResidue_pos`, `exists_poleLaw_iff` |
| The prime-trace moments of `ζ` read the width with base loss at most one; the pole law at any weight is the width | `two_mul_width_le_momentExponent`, `momentExponent_le`, `tendsto_momentExponent_div`, `exists_momentPoleLaw_iff` |
| The calibration eigenvalues are pure by the identity of their two pairings and sit on the sign line | `norm_jacobiSum_sq`, `stickelbergerPrice_jacobiTriple` |
| Abelian bases are rulers; Dirichlet twists of any modulus form an abelian base | `summable_twistMomentTerm_iff`, `exists_twistPoleLaw_iff`, `isAbelianBase_dirichlet`, `summable_dirichletMomentTerm_iff` |
| Polarized bases whose Adams squares continue to `Re s > 1` are pure; in rank two the Adams series suffice | `norm_eq_one_of_adamsPoleLaw`, `norm_eq_one_of_adams_continue` |
| The top bound one for all Adams powers is temperedness | `adamsPoleLaw_iff` |
| A pencil through `ζ` proves RH, and exists iff RH | `riemannHypothesis_of_pencil`, `riemannHypothesis_iff_nonempty_pencil` |
| The three lines: half unit, one-step values, completion centres to `2/3`; one Deligne lever or sign levers at all large periods give RH | `signPrice_sub_delignePrice`, `excluded_deligneLever`, `excluded_signLever`, `tendsto_completionCentre`, `riemannHypothesis_of_deligneLever`, `riemannHypothesis_of_signLevers` |
| The prime number theorem of the characters gives their independence; the logarithmic derivative of a number-field Euler product is its prime-power series; the angle characters of `ℚ(ω)` form an abelian base | `linearIndependent_of_pnt`, `IsAbelianBase.of_pnt`, `neg_deriv_div_eq_primePowerSeries`, `isAbelianBase_angle`, `summable_angleMomentTerm_iff` |
| Gauss pairings and the sign line: `c ≥ k/2`, equality only at `k ∈ {3, 4, 6}`, Euclidean signatures or excess at least `k/5`, sharp | `half_period_le_pairingC`, `period_mem_of_pairingC_eq_half`, `signatureWeight_dichotomy`, `euclidean_of_coupledBarrier_lt`, `exists_zmod_eleven_pairing` |

All results are unconditional; the reductions to RH name their hypothesis as an object of the
programme (a lever, a pencil).

## 11. Context

| Neighbour | Interface |
|---|---|
| ArithmeticKunnethTheory | closes layer 1 (products of the spectrum); TPP is layer 3, families over a base; uses its `SL₂` invariants and golden countermodels |
| InfiniteRankPurityTheory, InfiniteRankWeilTheory | amortization, fixed parts, self-improvement at infinite rank: the Rankin step at a point |
| SurfaceOfSpecZ | the tensor-power trick over `ℤ` and the width law at the primes |
| FamilyContinuationTheory, ExponentDynamicsOfTheCriticalStrip | frames, towers, walls, Stickelberger prices, the sign line, the cubic probe and its rung |
| GaloisTheoryOfZeros | the two involutions `ρ ↦ ρ̄`, `ρ ↦ 1 − ρ`; heat monodromy and the arithmetic group |
| ZeroConfigurationGeometry | the heat pencil has a Dirichlet series only at `τ = 0`; Ramanujan as reality of an Euler column |
| ArithmeticCastelnuovoSeveri | Kummer calibration curves; the one-cycle law `zeta_exists_universal_lefschetz_growth` behind `zetaCycle` |
| HTGeometry | Landau's theorem for general Dirichlet series, the step from continuation to convergence |
| ZeroForcingCalculus | the covering-lever criterion used by the assembly |
| EulerFETransportTheory | rigidity of Euler–FE data with the functional equation of `ζ` |
| AbsoluteGeometryOfSpecZ (`𝔽₁`) | receives the axiom list of N1 as its specification |

## 12. Success criteria

The programme closes RH if stage 3 or stage 4 of §7 succeeds; it is complete as a field when every
question of §6 has a Lean answer — the theorem asked for, or the failure theorem of §7 with its
strongest positive survivor — and the stage-1 tools exist.

A contribution to TPP

- is unconditional Lean, with no premise that carries the mathematics;
- moves one question of §6 or one stage of §7, or builds a tool that a later stage uses;
- works with tensor powers, frames, pole laws, edges or pencils — not with products of the spectrum
  alone, which ArithmeticKunnethTheory has closed;
- states no "RH ⇒ X"; reductions "X ⇒ RH" only when `X` is a named object of the programme (a pole
  law, a pencil, a completion, a transport);
- is not a finite computation;
- records, when it is a no-go, the positive statement the obstruction exposes.
