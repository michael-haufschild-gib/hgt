# 30 Second-Step Conjectures for Hypertranscendental Functions

**Working title:** *Hypertranscendence as constraint, not flow.*
**Standing object:** a function \(f\in \mathcal{HT}_K(D)\), usually with \(K=\mathbb C(x)\), unless a conjecture explicitly adds analytic, meromorphic, local-inverse, or probabilistic hypotheses.

## Reading rule used here

The uploaded hypertranscendence note treats a hypertranscendental function as one with **no finite algebraic-differential handle**: no nonzero differential polynomial over the base field vanishes on \(f\). It also warns that this does **not** imply “no equations at all,” does **not** decide special values, does **not** imply analytic pathology, and is always relative to the base field.

So the conjectures below are deliberately **not presented as theorems**. They are research seeds for a second step. Each one asks whether the absence of a finite algebraic-differential handle plausibly extends to some other kind of finite handle. The conjectures are framed mainly as **absence claims** because, under the user’s constraint, new knowledge should be about what the object plausibly *does not have*, not about a positive flow law it secretly obeys.

I use **generic** in the disciplined sense: “typical after a topology, measure, model-theoretic genericity notion, or construction protocol is chosen in the second research step.” Without such a qualifier, many of the conjectures would be too strong, because known hypertranscendental functions can still satisfy functional, difference, integral, or infinite-order equations.

## Anti-duplication rule

The 30 conjectures below are separated by **different possible handles**: shift, binary functional law, composition, inverse, integral equation, transform, coefficients, Padé pattern, asymptotic scale, singularity skeleton, monodromy, special values, cross-point values, zero incidence, finite data, state-space realization, rewrite grammar, definability, automorphism orbit, finite-cover descent, moduli, topology, perturbation, random construction, operator rank, approximate complexity, boundary behavior, minimal-counterexample logic, resurgence data, and base enrichment. None is meant as a mere rephrasing of another.

---

## C01 — Shift-lattice nonclosure

**Conjecture.** For a generic hypertranscendental \(f\), there is no nonzero finite algebraic **difference-differential** relation of the form
\[
P\bigl(x, f(x), f'(x),\ldots, f^{(r)}(x), f(x+h), f'(x+h),\ldots, f^{(r)}(x+mh)\bigr)\equiv 0
\]
for any fixed nonzero shift \(h\) in the chosen base context and any finite \(m,r\).

**Absent handle.** A finite translation/recurrence rule tying a finite derivative tower at \(x\) to finite derivative towers at shifted points.

**Why it has prior likelihood.** A shift law is not excluded by hypertranscendence itself, but it is another finite symbolic handle. The second-step test should attack this as false by examining Gamma-like counterexamples and then asking whether the conjecture survives only as a generic statement.

**Methods applied.** 2 attack as false; 10 test extreme cases; 22 compare nearby false statements.

---

## C02 — Algebraic addition-theorem absence

**Conjecture.** For a generic hypertranscendental \(f\), there is no algebraic addition theorem: no nonzero polynomial relation involving finitely many jets of
\[
f(x),\quad f(y),\quad f(x+y)
\]
vanishes identically in two independent variables \((x,y)\).

**Absent handle.** A binary group-law rule that compresses the function into values at fewer arguments.

**Why it has prior likelihood.** Classical special functions with addition theorems are often governed by finite algebraic or differential structure. Hypertranscendence blocks only one-variable finite differential handles, so this is a distinct functional-handle conjecture.

**Methods applied.** 1 split into subclaims; 3 reverse; 21 build a dependency chain.

---

## C03 — Algebraic self-iteration nonclosure

**Conjecture.** Whenever composition is meaningful, a generic hypertranscendental \(f\) has no finite algebraic law closing the sequence
\[
f,\ f\circ f,\ f^{\circ 3},\ldots.
\]
In particular, no finite set of algebraic equations over \(K\) should force \(f^{\circ n}\) to be algebraic over earlier iterates and their finite jets.

**Absent handle.** A finite dynamical closure rule for the self-composition orbit of \(f\).

**Why it has prior likelihood.** Iteration is not differentiation. Still, a closed algebraic iteration law would act like a finite machine that predicts infinitely many later objects from finitely many earlier ones.

**Methods applied.** 4 change viewpoint; 5 make it visual; 6 ask what action is happening.

---

## C04 — Local inverse noncapture

**Conjecture.** If a generic analytic hypertranscendental \(f\) has a local inverse \(g=f^{-1}\), then \(g\) is not captured by any finite algebraic-differential relation over the corresponding inverse-side base field, except in degenerate cases where the chosen base already encodes \(f\).

**Absent handle.** A finite differential equation for the inverse germ.

**Why it has prior likelihood.** Inversion is not a finite differential-rational expression in \(f\), so known closure principles do not settle it automatically. But if the inverse had a small handle, one would try to pull it back through \(f\) and look for a hidden handle on \(f\).

**Methods applied.** 3 reverse; 19 write the fake proof; 20 name the missing lemma.

---

## C05 — Finite-kernel integral noncapture

**Conjecture.** A generic hypertranscendental \(f\) is not the solution of a finite algebraic integral equation with a differentially algebraic kernel, for example an equation built from finitely many expressions of the type
\[
\int_a^x K_i(x,t,f(t),f'(t),\ldots,f^{(r)}(t))\,dt
\]
combined algebraically over \(K\).

**Absent handle.** A finite integral machine that reconstructs \(f\) from a DA kernel and finitely many integral operations.

**Why it has prior likelihood.** Hypertranscendence does not forbid integral equations. The conjecture says that, generically, integral structure should not collapse to a finite algebraic kernel.

**Methods applied.** 6 ask what action is happening; 14 weaken the conjecture; 18 look for the right theorem.

---

## C06 — Transform-domain noncapture

**Conjecture.** When a standard transform \(T(f)\)—Laplace, Mellin, Borel, Fourier, or a local variant—is defined, a generic hypertranscendental input should not transform into a differentially algebraic output unless the transform kernel or domain has encoded special information about \(f\).

**Absent handle.** A finite algebraic-differential handle appearing only after changing domains.

**Why it has prior likelihood.** Transform methods often turn differential equations into algebraic or recurrence data. A generic HT object should resist becoming finite-handle merely by moving to a dual variable.

**Methods applied.** 4 change viewpoint; 17 change representation; 22 compare nearby false statements.

---

## C07 — Coefficient-recurrence escape

**Conjecture.** For a generic analytic hypertranscendental \(f(x)=\sum_{n\ge0}a_n(x-a)^n\), the coefficient sequence \((a_n)\) satisfies no finite-width algebraic recurrence over the base constants, even nonlinear ones such as
\[
Q(n,a_n,a_{n+1},\ldots,a_{n+r})=0
\]
for a fixed finite \(r\) and nonzero polynomial \(Q\).

**Absent handle.** A finite recurrence grammar for the Taylor coefficients.

**Why it has prior likelihood.** D-finite functions correspond to strong coefficient recurrences, but this conjecture goes beyond linear holonomic recurrences and asks whether all bounded-window algebraic recurrences are generically absent.

**Methods applied.** 9 test small cases; 17 change representation; 18 look for the right theorem.

---

## C08 — Padé and continued-fraction nonstabilization

**Conjecture.** For a generic analytic hypertranscendental \(f\), Padé approximants, continued fractions, or rational-interpolation tables do not eventually settle into a finite algebraic pattern, periodicity, or bounded-rank law.

**Absent handle.** A finite approximation pattern that gives exact symbolic compression at all later orders.

**Why it has prior likelihood.** Rational approximants are visual and computational probes of hidden algebraic structure. Stabilization would suggest an unannounced finite handle.

**Methods applied.** 5 make it visual; 11 run experiments; 23 classify boundary cases.

---

## C09 — Asymptotic-scale nontermination

**Conjecture.** If \(f\) admits an asymptotic expansion in a chosen differentially algebraic scale, then for generic hypertranscendental \(f\) no finite initial segment of that expansion determines the tail by algebraic-differential rules internal to the same scale.

**Absent handle.** A finite asymptotic code that recursively generates the remaining expansion.

**Why it has prior likelihood.** Hypertranscendence says no finite derivative tower collapses algebraically. This conjecture translates that suspicion into asymptotic representation, where collapse can hide in tails rather than derivatives.

**Methods applied.** 7 strip to essentials; 13 find a monotone quantity; 17 change representation.

---

## C10 — Singularity-skeleton nonfiniteness

**Conjecture.** For a generic meromorphic or analytically continuable hypertranscendental \(f\), the singular set is not governed by a finite algebraic skeleton such as a finite union of algebraic loci, a finite arithmetic lattice, or a finite orbit under algebraic maps, unless such structure is separately imposed.

**Absent handle.** A finite geometric map of all singularities.

**Why it has prior likelihood.** Hypertranscendence does not imply analytic pathology, so this must be tested carefully. The conjecture is only that finite singularity geometry is not generically compatible with having no finite algebraic-differential handle.

**Methods applied.** 5 make it visual; 10 test extreme cases; 23 classify boundary cases.

---

## C11 — Monodromy finite-type absence

**Conjecture.** For a generic analytically continuable hypertranscendental \(f\), analytic continuation does not produce a finite algebraic monodromy object: not a finite branch cover, not a finite permutation representation, and not a finite-dimensional algebraic monodromy group that captures all branches.

**Absent handle.** A finite topological/algebraic monodromy controller.

**Why it has prior likelihood.** Algebraic and many classical differential-algebraic functions often have controlled continuation. A generic HT function may have continuation, but should not have finite monodromy compression without extra structure.

**Methods applied.** 4 change viewpoint; 5 make it visual; 12 find an invariant.

---

## C12 — Generic special-value independence

**Conjecture.** Although hypertranscendence alone says little about individual values, for a generic point \(a\) and generic hypertranscendental \(f\), the finite jet values
\[
f(a), f'(a),\ldots,f^{(n)}(a)
\]
are algebraically independent over the chosen constant field, for every finite \(n\).

**Absent handle.** A specialization trap where function-level freedom collapses at most points.

**Why it has prior likelihood.** The uploaded note explicitly warns that function-level algebraic independence need not imply value-level independence. This conjecture turns that warning into a second-step generic hypothesis rather than a deduction.

**Methods applied.** 1 split into subclaims; 2 attack as false; 14 weaken the conjecture.

---

## C13 — Cross-point jet independence

**Conjecture.** For distinct generic points \(a_1,\ldots,a_m\), the collection of finite jets
\[
\{f^{(j)}(a_i):1\le i\le m,\ 0\le j\le n_i\}
\]
has no algebraic relations over the constants beyond forced coincidences or relations imposed by the base field.

**Absent handle.** A finite algebraic web connecting independent observation sites.

**Why it has prior likelihood.** This is not just a special-value claim. It asks whether separate points remain algebraically uncoordinated, mirroring the absence of finite differential coordination in the function variable.

**Methods applied.** 1 split into subclaims; 8 look for similar objects; 21 build a dependency chain.

---

## C14 — Zero-incidence nonlaw

**Conjecture.** For a generic hypertranscendental \(f\), the zero sets of \(f,f',f'',\ldots\) do not satisfy any finite algebraic incidence law, such as a fixed algebraic rule forcing zeros of one derivative order to determine zeros of another.

**Absent handle.** A finite geometric law for where derivative towers vanish.

**Why it has prior likelihood.** Differential equations often impose strong zero interlacing, multiplicity, or critical-point restrictions. Hypertranscendence removes the finite ODE source of such restrictions, so a generic absence conjecture is natural.

**Methods applied.** 5 make it visual; 10 test extreme cases; 23 classify boundary cases.

---

## C15 — Finite sampling nonidentifiability

**Conjecture.** No finite set of sampled values and finite jets can certify hypertranscendence or reconstruct a generic HT function up to any finite algebraic-differential equivalence class. Every finite observation pattern compatible with smoothness or analyticity should be extendable both toward DA-looking and HT-looking functions.

**Absent handle.** A finite empirical certificate for an infinite negative property.

**Why it has prior likelihood.** Hypertranscendence is an identity-level universal negation over all finite differential polynomials. Finite samples cannot see all identities.

**Methods applied.** 7 strip to essentials; 9 test small cases; 16 use a minimal counterexample.

---

## C16 — Finite-state realization absence

**Conjecture.** A generic hypertranscendental \(f\) cannot be realized as the output of a finite-dimensional algebraic state-space system with differentially algebraic coefficients, hidden states, and inputs, unless elimination fails because the system has secretly smuggled in \(f\)-level data.

**Absent handle.** A finite hidden-state machine generating \(f\).

**Why it has prior likelihood.** A finite algebraic state-space model is a control-theoretic disguise for finite differential constraints. The second step should formalize the elimination lemma needed to convert this into a forbidden relation.

**Methods applied.** 4 change viewpoint; 17 change representation; 20 name the missing lemma.

---

## C17 — Finite rewrite-system absence

**Conjecture.** The derivative tower of a generic hypertranscendental \(f\) is not generated by any finite symbolic rewrite system whose rules use only algebraic operations, differentiation, substitution, and differentially algebraic side functions.

**Absent handle.** A finite grammar for all derivatives and transformations of \(f\).

**Why it has prior likelihood.** Hypertranscendence makes each finite jet algebraically free over previous finite information. A rewrite grammar would be another finite mechanism imposing long-range predictability.

**Methods applied.** 6 ask what action is happening; 7 strip to essentials; 17 change representation.

---

## C18 — Model-theoretic orthogonality to DA structure

**Conjecture.** In a saturated differential field, the generic type of a hypertranscendental function is orthogonal to finite-dimensional differentially algebraic varieties and to the constant field, except for relations explicitly added to the base.

**Absent handle.** A definable finite-to-finite correspondence between the HT generic and DA/constant structure.

**Why it has prior likelihood.** The differential ideal of relations is zero, so the HT generic resembles a differential indeterminate. Orthogonality is a stronger model-theoretic version of “no hidden finite DA coordinates.”

**Methods applied.** 15 strengthen the conjecture; 17 change representation; 18 look for the right theorem.

---

## C19 — Differential-Galois orbit noncollapse

**Conjecture.** In a universal differential extension fixing \(K\), the orbit of a generic hypertranscendental \(f\) under differential-field automorphisms does not collapse to a finite-dimensional algebraic quotient. Any stabilizer visible through finite algebraic data is trivial or base-imposed.

**Absent handle.** A finite algebraic symmetry quotient that classifies \(f\).

**Why it has prior likelihood.** Symmetry quotients often reveal hidden equations. If \(f\) has no finite differential equation, its automorphism orbit should remain too large for finite algebraic quotienting.

**Methods applied.** 12 find an invariant; 15 strengthen the conjecture; 18 look for the right theorem.

---

## C20 — Finite-cover descent failure

**Conjecture.** A generic local HT germ does not become differentially algebraic after pullback to a finite algebraic cover of the independent variable. Equivalently, finite ramified changes of coordinate should not create a finite algebraic-differential handle.

**Absent handle.** A hidden finite cover on which the function simplifies.

**Why it has prior likelihood.** Algebraic functions often simplify on finite covers. HT should resist this descent/pullback trick unless the cover is chosen with special knowledge of \(f\).

**Methods applied.** 3 reverse; 14 weaken the conjecture; 18 look for the right theorem.

---

## C21 — Finite moduli nonrepresentability

**Conjecture.** Generic hypertranscendental functions cannot be parameterized, even up to natural DA transformations, by points of any finite-dimensional algebraic or differentially algebraic moduli space.

**Absent handle.** A finite parameter list classifying the object.

**Why it has prior likelihood.** The full derivative tower has no finite algebraic collapse. A finite moduli representation would be a global compression of the same kind, but at the level of classification rather than equation-solving.

**Methods applied.** 7 strip to essentials; 17 change representation; 21 build a dependency chain.

---

## C22 — Topological largeness of HT

**Conjecture.** In a suitable function space with a countably specified base field and topology, the HT functions form a residual or dense \(G_\delta\)-like set, while functions with finite algebraic-differential handles form a thin union of closed nowhere-dense conditions.

**Absent handle.** Topological typicality of finite differential algebraic constraints.

**Why it has prior likelihood.** Each candidate differential-polynomial identity looks like a closed exceptional condition. The second step is to choose a topology and handle coefficient-cardinality issues carefully.

**Methods applied.** 8 look for similar objects; 11 run experiments; 18 look for the right theorem.

---

## C23 — Perturbative HT density

**Conjecture.** Around any sufficiently regular function, arbitrarily small generic perturbations produce hypertranscendental functions; conversely, a generic small perturbation of an HT function remains HT.

**Absent handle.** Stability of finite algebraic-differential relations under arbitrary small generic noise.

**Why it has prior likelihood.** Exact polynomial identities are fragile. A tiny generic perturbation should destroy them, while not installing a new identity.

**Methods applied.** 2 attack as false; 8 look for similar objects; 11 run experiments.

---

## C24 — Random-series almost-sure escape

**Conjecture.** A random analytic function with independently distributed continuous coefficients is hypertranscendental almost surely and, more strongly, almost surely avoids every finite symbolic handle from any prechosen countable menu of difference, recurrence, transform, and algebraic-functional relations.

**Absent handle.** Probability-positive occurrence of finite exact laws.

**Why it has prior likelihood.** A nonzero polynomial identity usually cuts out a measure-zero condition on random coefficients. The second step is to make the countability and convergence assumptions precise.

**Methods applied.** 8 look for similar objects; 11 run experiments; 17 change representation.

---

## C25 — Operator-rank noncompression

**Conjecture.** The derivative tower \((f^{(n)})_{n\ge0}\) of a generic HT function is not contained in any finite-rank module over rings of differentially algebraic operators; associated Wronskian-, Hankel-, or Krylov-type rank tests should not become eventually bounded for structural reasons.

**Absent handle.** A finite-dimensional linear/operator space containing the infinite jet tower.

**Why it has prior likelihood.** D-finite functions are finite-dimensional under differentiation. HT already rules that out in the simplest setting; this conjecture asks whether broader operator-rank compressions are also generically absent.

**Methods applied.** 12 find an invariant; 13 find a monotone quantity; 17 change representation.

---

## C26 — Approximate differential-complexity divergence

**Conjecture.** Fix a norm on a compact subdomain and bound the degree/order/height of differential polynomials over \(K\). For a generic HT function, the minimal complexity of a differential polynomial that approximates \(f\) to tolerance \(\varepsilon\) tends to infinity as \(\varepsilon\to0\), with no eventual bounded template.

**Absent handle.** A finite approximate algebraic-differential model that becomes exact in the limit without increasing complexity.

**Why it has prior likelihood.** Exact HT forbids zero residual at fixed complexity. The conjecture asks for a quantitative, monotone version suitable for experiments and falsification.

**Methods applied.** 11 run experiments; 13 find a monotone quantity; 14 weaken the conjecture.

---

## C27 — Boundary nonlocality between DA and HT

**Conjecture.** No finite-order contact between \(f\) and a differentially algebraic function—matching values and derivatives up to any fixed finite order at finitely many points—forces a hypertranscendental \(f\) to cross into the DA class. The DA/HT boundary is global and identity-level, not finite-local.

**Absent handle.** A finite local boundary certificate distinguishing DA from HT.

**Why it has prior likelihood.** Hypertranscendence is the absence of an identity, not a finite jet condition. This conjecture turns boundary cases into a research object.

**Methods applied.** 10 test extreme cases; 16 use a minimal counterexample; 23 classify boundary cases.

---

## C28 — Minimal higher-handle counterexample collapse

**Conjecture.** Suppose a generic-looking HT function satisfies one of the proposed extra finite-handle relations—shift, integral, transform, addition, or finite-state. A minimal-complexity counterexample should either be genuinely exceptional or should collapse, after elimination, into a forbidden finite differential-polynomial relation.

**Absent handle.** A minimal extra relation that remains independent of differential algebra.

**Why it has prior likelihood.** This is a meta-conjecture for the second research step: if an apparent new handle exists, try to shrink it until it either exposes a true exceptional family or produces the missing differential polynomial.

**Methods applied.** 16 use a minimal counterexample; 19 write the fake proof; 20 name the missing lemma.

---

## C29 — Resurgence and Stokes-data nonclosure

**Conjecture.** For a resurgent or multisummable hypertranscendental function, the alien derivatives, Stokes constants, and connection data should not satisfy a finite algebraic-differential closure relation over the original base unless resurgence structure was independently imposed.

**Absent handle.** A finite algebraic controller of analytic continuation data beyond ordinary derivatives.

**Why it has prior likelihood.** Resurgence can encode hidden equations outside finite ordinary differential algebra. The conjecture asks whether a generic HT object also avoids finite closure at this higher analytic-data level.

**Methods applied.** 4 change viewpoint; 15 strengthen the conjecture; 22 compare nearby false statements.

---

## C30 — Base-enrichment resistance

**Conjecture.** Enlarging the base field by finitely many differentially algebraic functions, algebraic extensions, constants, or finite-cover coordinate changes should not make a generic \(f\in\mathcal{HT}_K\) differentially algebraic. Any base enlargement that destroys hypertranscendence must already include a differentially transcendental object nontrivially encoding \(f\).

**Absent handle.** A small harmless-looking base extension that secretly captures \(f\).

**Why it has prior likelihood.** Hypertranscendence is relative to the base, so this is a boundary conjecture about how much the base must be enriched before the property collapses. It asks the second step to separate innocent enrichments from extensions that import the object itself.

**Methods applied.** 3 reverse; 18 look for the right theorem; 23 classify boundary cases.

---

# Scientific-method coverage map

Every item from `scientific-method.md` is used at least once.

| # | Method | Conjectures where applied |
|---:|---|---|
| 1 | Split it into subclaims | C02, C12, C13 |
| 2 | Attack it as false | C01, C12, C23 |
| 3 | Reverse it | C02, C04, C20, C30 |
| 4 | Change the viewpoint | C03, C06, C11, C16, C29 |
| 5 | Make it visual | C03, C08, C10, C11, C14 |
| 6 | Ask what action is happening | C03, C05, C17 |
| 7 | Strip it to essentials | C09, C15, C17, C21 |
| 8 | Look for similar objects | C13, C22, C23, C24 |
| 9 | Test small cases | C07, C15 |
| 10 | Test extreme cases | C01, C10, C14, C27 |
| 11 | Run experiments | C08, C22, C23, C24, C26 |
| 12 | Find an invariant | C11, C19, C25 |
| 13 | Find a monotone quantity | C09, C25, C26 |
| 14 | Weaken the conjecture | C05, C12, C20, C26 |
| 15 | Strengthen the conjecture | C18, C19, C29 |
| 16 | Use a minimal counterexample | C15, C27, C28 |
| 17 | Change representation | C06, C07, C09, C16, C17, C18, C21, C24, C25 |
| 18 | Look for the right theorem | C05, C07, C18, C19, C20, C22, C30 |
| 19 | Write the fake proof | C04, C28 |
| 20 | Name the missing lemma | C04, C16, C28 |
| 21 | Build a dependency chain | C02, C13, C21 |
| 22 | Compare nearby false statements | C01, C06, C29 |
| 23 | Classify boundary cases | C08, C10, C14, C27, C30 |

---

# Suggested second-step scrutiny plan

1. **Separate universal from generic.** First try to refute each conjecture as a universal statement. If a known HT function violates it, downgrade it to a generic, almost-sure, residual, or “outside named exceptional families” version.
2. **Choose a base field and function category.** Each conjecture must specify whether \(f\) is smooth, analytic, meromorphic, resurgent, local, global, real, or complex.
3. **Name the missing elimination lemma.** For each proposed extra handle, ask: “Would this relation imply a nonzero differential polynomial in \(f\)?” If yes, it may be provable. If no, it is a genuinely new research direction.
4. **Build counterexample banks.** Gamma-like functional equations, random analytic functions, compactly supported smooth functions, lacunary series, and functions with prescribed special values should be tested early.
5. **Keep the constraint pure.** Do not infer growth, chaos, noncomputability, singularity density, or value transcendence from HT alone. Those are only conjectural overlays unless independently proved.
