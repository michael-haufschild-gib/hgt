# Reframing: a working guide

How breakthroughs get made by changing the frame rather than by extending the computation — the moves, the procedure for finding one, and the historical cases they were extracted from.

---

## Part 1. The moves

Seven operations. Most documented reframings are one of these applied to a new subject.

### 1. Change the arena

Keep the object, change the space it lives on.

**Trigger:** a pathology that is a property of your description rather than of the thing described. Multivaluedness, non-uniqueness, "only defined locally."

**Test:** name the smallest space on which the problem disappears, then study that space instead.

*Riemann surfaces. Space of couplings. Deformation space. Parameter space.*

### 2. Swap primitive and derived

Whatever you have been deriving, assume it. Whatever you have been assuming, derive it.

**Trigger:** a derived result that is cleaner, more invariant, or more empirically direct than the axioms producing it.

*Minkowski made the transformation group primitive and geometry derived. Einstein made invariance primitive and dynamics derived. Carathéodory made adiabatic inaccessibility primitive and entropy derived.*

### 3. Re-assign the dictionary, keep the formalism

Change what a symbol refers to. Change nothing else.

**Trigger:** a formalism that works while its interpretation strains — quantities that are "effective," "formal," or "not to be taken literally."

Cheap to attempt, almost never attempted. Ownership of a formalism makes its intended reading feel necessary.

*Born reading |ψ|² as probability instead of charge density.*

### 4. Vary one structural parameter of a failed construction

A beautiful construction that fails empirically is usually a correct construction with one wrong input. Identify the inputs and vary them one at a time before discarding.

**Trigger:** an elegant dead theory. Especially one killed by a single specific objection.

*Weyl's gauge theory: ℝ⁺ → U(1). Euclid: drop the parallel postulate. Dirac: take the square root of the Klein–Gordon operator.*

### 5. Prove the correspondence you keep using informally

If you repeatedly match items between two catalogs by hand, the pairing is a theorem. Where the pairing breaks is the interesting part.

**Trigger:** the phrase "the analogue of" appearing in your own work more than twice.

*Noether: symmetries ↔ conservation laws. Kolmogorov: probability ↔ measure theory. Langlands. The Kleinian-group/rational-map dictionary.*

### 6. Represent one level inside another

Encode the meta-level in the object level; or replace "study X" with "study the maps into X," then "the maps out of X."

**Trigger:** statements *about* your system that you cannot state *in* it; or an object that resists direct analysis but has tractable morphisms.

*Gödel numbering. Cayley's theorem. Linear representations. Yoneda.*

### 7. Promote the nuisance to the structure

The parameter you are trying to eliminate becomes a coordinate. Differentiate with respect to it.

**Trigger:** anything you routinely cancel, subtract, normalize away, or apologize for.

*The cutoff becomes the RG flow parameter. The obstruction to gluing local solutions becomes a cohomology class. The error term becomes the main term. The failure of a construction to be canonical becomes the torsor it lives in.*

---

## Part 2. What to do when stuck

### Prerequisite

Reframing is not an alternative to grinding; it is what grinding is for. Every case in Part 3 came after years of technical intimacy, and every reframe was triggered by something specific the grinding had made the person sensitive to. If you have not computed enough examples to be *annoyed* by something, you are not stuck in the sense that admits a reframe. You are stuck in the sense that admits more computation.

### Step 1: locate the irritant

The reliable trigger is irritation. Find the thing you keep apologizing for, working around, or handling separately.

| Symptom | Likely meaning |
|---|---|
| A case you always treat separately | It is the general case in disguise, or your definition is wrong |
| A quantity that appears and cancels | It has meaning; name it and give it a home |
| A choice you make, then prove doesn't matter | The choices form a space; the independence is a group action |
| A hypothesis you carry but never use | Delete it and see what survives |
| A normalization you keep re-fixing | It is a section of a bundle you have not named |
| "After identifying…", "up to the obvious…" | Everything after that phrase is unexamined |
| An estimate that is always tight | The inequality is an equality about something else |

### Step 2: run the interrogation

Write out answers. Literally, in text, not in your head.

- **Where does my proof know that X?** Take a hypothesis; find the line that uses it. No line → remove the hypothesis. One line → that line is the actual content.
- **What group acts here, and what is invariant?** Then: is my object a function of the invariants alone? If not, my object is the wrong object.
- **On what space is this canonical?** If a construction depends on a choice, its honest domain is the space of choices.
- **What is the moduli count?** Dimension of the family of hypothesized objects vs. dimension of the space containing them. This alone is Sullivan's proof.
- **What am I trying to remove?** Keep it. Differentiate with respect to it.
- **Which mature theory has my primitives?** Write the translation table in two columns, including the rows where it fails. The failed rows are the research programme.
- **What is the dual / the base / the total space / the classifying object?**
- **Can I state my theorem without the words I invented?** If not, the invented words may be hiding the content.
- **What would this look like with the answer assumed?** Work backwards from the conclusion and meet in the middle; the gap is smaller than it looks from one side.

### Step 3: attack the frame itself

- Re-derive the standard theory from scratch without consulting sources. Where your reconstruction differs from the received one is where the received version made unforced choices.
- Rewrite the problem in three notations, one deliberately bad. Notation encodes which operations are considered easy; changing it changes which moves look natural.
- Explain it to someone in an adjacent field and record which of your standard phrases they refuse to accept. Those are the load-bearing conventions.
- Read the original papers, not the modern treatments. Modern treatments have already chosen the frame; you want the joint where the choice was made.
- Maintain an explicit dictionary between your field and its structural twin, listing theorems that have **not** yet crossed. Sullivan's theorem sat in that gap for twenty-five years.

### Failure modes

- **Reframing without technical control produces philosophy, not theorems.** Minkowski could name the invariant form because he could compute with it.
- **Most reframes fail and should be discarded within a day.** Cheapness matters more than plausibility. Run twenty, not one.
- **The builder of a formalism resists its reinterpretation** — including when the builder is you. Lorentz kept local time auxiliary; Planck thought the quantum was a formal device; Schrödinger fought Born; Einstein called Minkowski's version superfluous erudition, then needed it. Attempt the semantic re-assignment on your own constructions first.

---

## Part 3. The cases

### Galois (1832) — solvability by radicals

**Problem.** Which polynomial equations are solvable in radicals? Abel had shown the general quintic is not; nobody knew why, or which particular equations were.

**Already available.** Lagrange's and Ruffini's analysis of how symmetric functions of the roots behave under permutation.

**The move.** Stop manipulating the roots. Catalogue the permutations of the roots that preserve every rational relation among them — computable from the coefficients, whereas the roots are not. Solvability becomes a property of that group's internal structure (a chain of normal subgroups with abelian quotients).

**Move type:** 1, 6. Replaced an inaccessible object with the group acting on it.

### Riemann (1851) — algebraic functions and their integrals

**Problem.** Multivalued functions like √z and the integrals of algebraic functions required cuts, sheets, and case-by-case bookkeeping. No general theory.

**Already available.** Cauchy's complex analysis; Puiseux on branch points.

**The move.** "Multivalued" is a statement about the plane, not about the function. Build the surface on which the function is genuinely single-valued, and study the surface. Genus and connectivity enter analysis; Abel's theorem becomes topology.

**Move type:** 1. The pathology was evidence the domain was wrong.

### Minkowski (1908) — the structure of special relativity

**Problem.** Relativity was a set of transformation rules with no picture. Extending it — to gravity, to general covariance — had no handhold.

**Already available.** Every equation of Einstein's 1905 paper.

**The move.** Take the Lorentz transformations as data and ask the inverse question: which quadratic form do they preserve? Answer: x²+y²+z²−c²t². Promote that form to the metric of the actual arena. Four-dimensional geometry with indefinite signature.

**Move type:** 2, 1. Group primitive, geometry derived — and it is what made general relativity writable.

### Noether (1918) — conservation laws in general relativity

**Problem.** Energy conservation in general relativity was behaving strangely; Hilbert and Klein could not make it come out as an ordinary conservation law.

**Already available.** A century of variational calculus; thirty years of Lie's continuous groups. Individual pairings known case by case (time translation ↔ energy, space translation ↔ momentum).

**The move.** Ask whether the case-by-case pairing is a theorem. It is: every continuous symmetry of an action yields a conserved current. Then notice the anomaly — *local* symmetries do not fit, and instead produce identities among the field equations. That second theorem is why GR's energy conservation looked broken. It wasn't.

**Move type:** 5. The failure case of the correspondence was the more valuable half.

### Born (1926) — what the wavefunction is

**Problem.** Schrödinger's equation predicted correctly but nobody knew what ψ was. Schrödinger read |ψ|² as a smeared charge density, which fails for scattering: the wave packet spreads and the electron does not.

**Already available.** The entire formalism, months old.

**The move.** Change one symbol's referent: |ψ|² is a probability density. Not one line of mathematics changed.

**Move type:** 3. He received the Nobel almost thirty years later for the reinterpretation alone.

### Fock, London, Weyl (1927–29) — gauge invariance

**Problem.** Weyl's 1918 unification of gravity and electromagnetism used a local scale factor e^{λ(x)}. Einstein killed it in one objection: atomic spectra would depend on a rod's history. The construction was elegant and dead.

**Already available.** Weyl's whole differential-geometric apparatus — connection, curvature, the identification of F with curvature.

**The move.** Change exactly one input: the structure group, from ℝ⁺ to U(1), using the phase of the newly available complex wavefunction. Everything downstream survives. The potential is a connection, F its curvature, charge conservation a Noether current. Road to Yang–Mills and the Standard Model.

**Move type:** 4. The construction was right; one parameter was wrong.

### Gödel (1931) — the consistency of formal systems

**Problem.** Hilbert's programme: prove arithmetic complete and consistent by finitary means. Nobody could see how a formal system could be made to say anything about formal systems.

**Already available.** Primitive recursive functions; formalized proof; Cantor's diagonal argument (which had nothing in arithmetic to bite on).

**The move.** Encode formulas and proofs as integers, computably and injectively, so that "p is a proof of s" becomes an arithmetic relation among numbers. Arithmetic can now discuss its own syntax; diagonalization now has a surface. The incompleteness theorems follow more from the encoding than from any new analysis.

**Move type:** 6. Meta-level embedded in object level.

### Kolmogorov (1933) — foundations of probability

**Problem.** Probability had no foundation. Paradoxes over conditioning; no way to handle infinite sequences of random variables rigorously; stochastic processes unformalizable.

**Already available.** Lebesgue measure, abstract measure spaces, Radon–Nikodym — complete and mature.

**The move.** Write the dictionary. Probability = measure of total mass 1. Random variable = measurable function. Expectation = integral. Independence = product condition. Conditioning = sub-σ-algebra. Almost no new analysis invented; martingales, stochastic processes and eventually Itô calculus became possible immediately.

**Move type:** 5. Find the mature theory whose primitives match yours.

### Wilson (1971) — critical phenomena and the meaning of renormalization

**Problem.** Two separate scandals. Renormalization in QFT was an unexplained recipe for subtracting infinities. And in statistical mechanics, critical exponents were *universal* across chemically unrelated systems, with no reason why.

**Already available.** Gell-Mann–Low RG equations (1954); Kadanoff's block-spin picture (1966).

**The move.** Promote the cutoff — the nuisance everyone wanted to remove — to the time parameter of a dynamical system on the space of all couplings. A theory becomes a point; changing scale becomes a flow; critical behaviour becomes a fixed point; universality becomes the small number of relevant (unstable) directions; the infinities become an artifact of insisting the cutoff go to infinity. Both scandals dissolve.

**Move type:** 7, 1. Same formalism, entirely different picture of what it meant.

### Sullivan (1985) — no wandering domains

**Problem.** Fatou's question, open sixty years: can a rational map have a Fatou component whose forward orbit never repeats? Its existence would have made classification of the Fatou set hopeless.

**Already available.** The measurable Riemann mapping theorem (Ahlfors–Bers, ~1960); Ahlfors' finiteness theorem for Kleinian groups.

**The move.** Recognize rational maps and Kleinian groups as two faces of one conformal dynamical subject, so Ahlfors' argument transfers. Then: a wandering domain would support an infinite-dimensional family of quasiconformal deformations of the map — but degree-*d* rational maps form a finite-dimensional space. Contradiction. The ingredients were twenty-five years old; the dictionary was the discovery.

**Move type:** 5, 1. Hypothetical object → deformation family → dimension count.

### Douady–Hubbard (1982) — connectivity of the Mandelbrot set

**Problem.** Is M connected? A question about the parameter plane, with no apparent handle.

**Already available.** Böttcher coordinates — the canonical conjugacy of each polynomial to z² near infinity — known since 1904.

**The move.** Each parameter carries a canonical construction in its own dynamical plane. Evaluate that construction at the canonical point: the critical value. This produces an explicit conformal isomorphism from the complement of M to the complement of the closed disc, so M is connected. A parameter-space question answered in the dynamical plane.

**Move type:** 1, 6. When a family carries a canonical fibrewise construction, evaluating it at a canonical fibrewise point gives a map on the base.

---

## Appendix: the pattern across cases

- The reframe always came *after* technical saturation, never instead of it.
- The most common single move is **change the arena** (1), and the most underused is **re-assign the dictionary** (3), because it costs nothing and feels illegitimate.
- The person who built the machinery usually resisted the reinterpretation.
- Two of these (Gödel, Wilson) resolved problems by showing the difficulty was an artifact of an assumption nobody had noticed making — the assumption that a system cannot discuss itself, and the assumption that the cutoff must go to infinity. Ask what your field's unnoticed assumption is.