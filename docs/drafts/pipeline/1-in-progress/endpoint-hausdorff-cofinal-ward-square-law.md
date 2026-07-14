# Endpoint Hausdorff aggregate negative-mass law

- **ID:** `endpoint-hausdorff-cofinal-ward-square-law`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE] RH route; source-pure cofinal estimate`
- **Source:** endpoint-calibrated source--temperature master theorem
- **Statement:** `[CONJECTURE]` The canonical endpoint-normalized Hausdorff--Bernstein systems
  admit a cofinal theta-source estimate whose total negative mass tends to zero.  Pointwise
  positivity of any selected system is not required.

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
\mathsf E_*\Longleftrightarrow\mathrm{RH}.
\]

This target is strictly weaker than the common-quadrant condition

\[
\mathsf Q_*:\qquad
\exists M\ \forall k,r\ge M,\quad D^*_{k,r}\ge0.
\]

Indeed \(\mathsf Q_*\) forces positivity on a principal ideal, whereas \(\mathsf E_*\) permits
negative Bernstein masses at every selected degree.  Only an unconditional source-side estimate
for \(\eta_M\) counts as progress.  A bound obtained from assumed Hankel, Hausdorff, KMS, or RH
positivity is circular.

## Competing moves

1. `[CONJECTURE] Aggregate Ward transform.`  Express the complete degree-`M` Bernstein mass vector
   through the theta cusp density and use the all-order Liouville/Witten Ward identities to bound
   the sum of its negative parts, without orienting each component.
2. `[CONJECTURE] Positive-part source coupling.`  Construct a source-side positive atomic system
   whose coordinatewise distance from the canonical signed Bernstein approximation is bounded by
   a scalar defect tending to zero.  The defect must be estimated before invoking moment closure.
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
- The Ward transform fails if its boundary term is an uncontrolled copy of `eta_M` or if its
  error remains bounded away from zero.

## Physics-lane audit

The current formal tree supplies four distinct layers which must not be conflated.

1. **Unconditional quantitative layer.**  The endpoint quartet estimates give
   
   \[
   \mathcal E_\perp<\frac1{150000},\qquad
   \mathcal E_\perp\le \frac1{84}\mathcal M_2,
   \]
   
   together with the self-localized cubic bound in the off-line endpoint charge.  These are real
   estimate gains, but no positive gap separates a remote off-line quartet from zero charge.
2. **Aggregate source-defect layer.**  The endpoint-normalized Bernstein masses satisfy

   \[
   \mathrm{RH}\Longleftrightarrow
   \exists M_j\to\infty,\quad\sum_i(a_{M_j,i})^-\to0.
   \]

   This is strictly weaker than selected-diagonal positivity and the common deep quadrant.  It is
   now the smallest source-side target in the route.
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

`[CONJECTURE]` **Cofinal source Bernstein-defect decay.**  Derive directly from the completed
prime--Gamma/theta source a cofinal degree schedule `M_j` and explicit bounds `e_j -> 0` such that

\[
\eta_{M_j}\le e_j.
\]

This alone implies RH.  It allows negative masses at every selected degree and is therefore
strictly weaker than a cofinal sign theorem.

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
- [ ] derive a source-pure representation of the full degree-`M` Bernstein mass vector
- [ ] prove an explicit aggregate bound `eta_M <= e_M` along one cofinal schedule with `e_M -> 0`
- [ ] construct or rule out a source-pure comparison from the joint prime-log Gibbs limit to one
      cofinal Xi projective cold section
- [ ] alternatively, prove one sparse Eisenstein source-Hankel chamber or one subexponential
      projective thermal section without RH-equivalent assumptions
- [ ] 1 → 2 fully-proven: complete paper proof with no open dependency
- [ ] 2 → 3 formalized: unconditional Lean theorem, targeted build, axiom and lint gates
- [ ] 3 → 4 publication-ready: integrate the proof into the master paper
