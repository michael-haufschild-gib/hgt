# Endpoint Hausdorff aggregate negative-mass law

- **ID:** `endpoint-hausdorff-cofinal-ward-square-law`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE] RH route; source-pure cofinal estimate`
- **Source:** endpoint-calibrated source--temperature master theorem
- **Statement:** `[CONJECTURE]` The canonical endpoint-normalized Hausdorff--Bernstein systems
  lie in the exact zero phase of their monotone total-negative-mass order parameter.  Equivalently,
  a source identity forces cofinal decay; degree-elevation rigidity then forces exact positivity
  at every finite degree.

## Goal

Put \(s_n=R_*^{-n}\mu_n\), and let

\[
a_{M,i}=\ell_s\!\left(\binom MiX^i(1-X)^{M-i}\right),
\qquad
\eta_M=\sum_{i=0}^M(a_{M,i})^-.
\]

Prove the remaining condition

\[
\mathsf E_*:\qquad
\exists M_j\to\infty,\quad \eta_{M_j}\to0.
\]

The formal master theorem proves

\[
0\le\eta_M\le\eta_{M+1},\qquad
\mathsf E_*\Longleftrightarrow
[\forall M\ge1,\ \eta_M=0]
\Longleftrightarrow\mathrm{RH}.
\]

It also proves the positive phase dichotomy

\[
\neg\mathrm{RH}
\Longleftrightarrow
\exists M_0\ge1\ \forall M\ge M_0,
\qquad 0<\eta_{M_0}\le\eta_M.
\]

The cofinal formulation is therefore a scalar compression, not a weaker positivity condition.
It is equivalent to the common-quadrant condition

\[
\mathsf Q_*:\qquad
\exists M\ \forall k,r\ge M,\quad D^*_{k,r}\ge0.
\]

because both are equivalent to RH.  Only an unconditional source-side proof that the monotone
order parameter is in its zero phase counts as progress.  A bound obtained from assumed Hankel,
Hausdorff, KMS, or RH positivity is circular.

## Competing moves

1. `[CONJECTURE] Exact Ward zero-phase identity.`  Express the complete degree-`M` Bernstein mass
   vector through the theta cusp density and use the all-order Liouville/Witten Ward identities to
   prove its total negative mass is exactly zero.
2. `[CONJECTURE] Cofinal upper collapse.`  Construct explicit source-side bounds
   `eta_(M_j) <= e_j -> 0`.  Monotonicity makes this an exact theorem in disguise: it forces every
   earlier and then every finite-degree defect to vanish.
3. `[CONJECTURE] Bernstein/Gibbs comparison.`  Bound `eta_M` by a completed prime--Gamma Gibbs or
   transfer-operator partition whose source representation is subexponential on one cofinal
   schedule.  The comparison must be an exact source/divisor identity, not assumed passivity.
4. `[BRIDGE / LIKELY DEAD] Finite verified-height dominance.`  A verified critical-line prefix can
   force additional finite positivity, but cannot prove the cofinal tail and is not the main route.

## Hard attacks

- Positive theta density alone does not orient nonlinear cumulants; the low-order cumulant formulas
  already contain forced negative terms.
- A generic Hamburger/Hausdorff representation is equivalent to the desired positivity and cannot
  be used as input.
- Reflection-positive Hankel machinery transports positivity but does not create the arithmetic
  sign.
- Any finite rectangle can be defeated by a sufficiently remote off-line quartet; the required
  estimate must force the aggregate negative mass to vanish cofinally.
- The Ward transform fails if its boundary term is an uncontrolled copy of `eta_M`.  A merely
  positive asymptotic error cannot establish the zero phase; a cofinal error tending to zero would
  already prove exact vanishing by monotonicity.

## Physics-lane audit

The current formal tree supplies four distinct layers which must not be conflated.

1. **Unconditional quantitative layer.**  The endpoint quartet estimates give
   
   \[
   \mathcal E_\perp<\frac1{150000},\qquad
   \mathcal E_\perp\le \frac1{84}\mathcal M_2,
   \]
   
   together with the self-localized cubic bound in the off-line endpoint charge.  These are real
   estimate gains, but no positive gap separates a remote off-line quartet from zero charge.
2. **Monotone source-phase layer.**  The endpoint-normalized Bernstein masses satisfy

   \[
   \mathrm{RH}\Longleftrightarrow
   \exists M_j\to\infty,\quad\sum_i(a_{M_j,i})^-\to0.
   \]

   Degree elevation gives `eta_M <= eta_(M+1)`, so the displayed condition is equivalent to
   `eta_M = 0` for every degree.  False RH is the complementary persistent-gap phase.  This is the
   smallest scalar source-side order parameter in the route, but not a weakened sign theorem.
3. **Exact detector layer.**  The faithful projective partition
   
   \[
   Z_N(\beta)=\sum_{j<N}w_j e^{\beta\delta_j},
   \qquad w_j>0,
   \quad \delta_j=\left|\Re\rho_j-\frac12\right|,
   \]
   
   is monotone in both coordinates.  Along every cofinal size/cooling schedule its normalized
   logarithm has the exact limit

   \[
   \frac{\log Z_{N_j}(\beta_j)}{\beta_j}\longrightarrow\delta_*.
   \]

   Thus RH is equivalent to subexponential growth along any one such section; boundedness is a
   strictly stronger presentation of the same endpoint.  This is the correct positive thermal
   carrier, not a finite-temperature sign test.
4. **Prime-source realization layer.**  Finite prime-log Hermitian Gibbs responses now converge
   jointly as cutoff and inverse temperature tend to infinity, locally uniformly on the upper
   half-plane and in every holomorphic jet.  The uniform input is the spectral gap `log 2` and the
   finite dyadic prime mass.  This constructs a cofinal prime carrier but does not yet couple it to
   the Xi projective partition.

The minimal missing theorem is therefore positive and source-specific:

`[CONJECTURE]` **Source Bernstein zero-phase law.**  Derive directly from the completed
prime--Gamma/theta source either exact identities `eta_M=0` for every `M`, or a cofinal degree
schedule `M_j` and explicit bounds `e_j -> 0` such that

\[
\eta_{M_j}\le e_j.
\]

By monotonicity, the cofinal version already forces exact zero at every degree and hence RH.

An equivalent thermodynamic target remains useful when it admits a source comparison:

`[CONJECTURE]` **Cofinal source--divisor Gibbs subexponential domination.**  Construct from the
completed prime--Gamma source a cofinal schedule `(N_j,beta_j)` and explicit source values `B_j`
such that, for every `epsilon > 0`, eventually

\[
Z_{N_j}(\beta_j)\le B_j\le e^{\varepsilon\beta_j},
\]

with the first inequality proved by an exact source/divisor value relation rather than by assumed
RH, passivity, reflection positivity, Hausdorff positivity, or thermal moment closure.  This is
the weakest exact thermodynamic endpoint supplied by the present architecture and would
immediately imply RH through the free-energy radius law.

The same endpoint has another sparse source formulation.  For any chosen infinite
degree set `D`, it is enough to prove trace--Hankel nonnegativity only for monic integer
polynomials Eisenstein at `2` whose exact degrees lie in `D`.  Every positive-degree test is
irreducible, and the fixed congruence chamber remains positivity-complete.  Thus a viable Ward
construction may choose a convenient sparse schedule, for example powers of two, and target only
the probes

\[
X^d+2+4Np,\qquad X^d+2-4Np,
\]

without recovering the omitted degrees or coefficients.  The positive obligation is not the
full polynomial cone: it is one source-generated irreducible chamber on one cofinal degree ray.

The Born--Witten/Morse--Fisher lane supplies a separate finite-degree source estimate: every
linear trace--Hankel test follows from rational enclosures for `exp(-pi)` and the first nine moments
of one positive incomplete-Gamma density.  Those enclosures remain unproved, and even their proof
would close only the first nonconstant Hankel block, not the cofinal Hausdorff tail.

## Gates

- [x] 0 → 1 in-progress: exact cofinal target, source-pure candidates, and circularity firewall stated
- [x] prove and formalize Bernstein degree-elevation monotonicity, cofinal zero-rigidity, and the
      false-RH persistent-gap phase law
- [ ] derive a source-pure representation of the full degree-`M` Bernstein mass vector
- [ ] prove an explicit aggregate bound `eta_M <= e_M` along one cofinal schedule with `e_M -> 0`
- [ ] construct or rule out a source-pure comparison from the joint prime-log Gibbs limit to one
      cofinal Xi projective cold section
- [ ] alternatively, prove one sparse Eisenstein source-Hankel chamber or one subexponential
      projective thermal section without RH-equivalent assumptions
- [ ] 1 → 2 fully-proven: complete paper proof with no open dependency
- [ ] 2 → 3 formalized: unconditional Lean theorem, targeted build, axiom and lint gates
- [ ] 3 → 4 publication-ready: integrate the proof into the master paper
