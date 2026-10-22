# Gamma-six trace-ideal/Sonin strict-lift obstruction

- **ID:** `deninger-gamma-six-trace-ideal-sonin-strict-lift-obstruction`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) / ROUTE-L NO-GO WITH POSITIVE SURVIVOR
- **Source:** Route L resolved Green source annihilator; complete Gamma-six weak-trace shell
- **Statement:** every trace-ideal-preserving comparison from the literal Gamma-six Wold coface
  to the fixed Sonin physical receiver has a canonical Calkin defect bounded below by the exact
  reflected Stokes curvature; exact comparison exists precisely at neutral horizontal grade.

## Goal

Decide whether relative cyclic homology, joint torsion, a Connes--Karoubi character, or any other
comparison invariant under trace-class correction can supply Route L's missing strict square.
The test uses the already constructed complete Gamma-six source operator and its literal Wold
coface, not a finite source atom or a quotient chosen to kill that atom.

This theorem does not prove RH. It proves that a source-natural comparison preserving the complete
trace-class remainder cannot be constructed uniformly in horizontal grade. Any surviving Route L
producer must be divisor-selective and must use a new multi-place law strong enough to cancel a
nonzero Calkin class at actual Xi divisor points.

## Exact objects

Let

\[
 T_6:\ell^2(\mathbb N)\longrightarrow
 \ell^2(\mathbb N;H_{\Gamma,6})
\]

be the complete corrected Gamma-six shell source and let \(W_6\) be its literal rectangular Wold
compression. Put

\[
 B_6^{\mathrm{src}}=W_6(T_6)-\frac16T_6.                 \tag{1}
\]

The complete-source Green--Stokes theorem proves

\[
 B_6^{\mathrm{src}}\in\mathcal L^1
   \bigl(\ell^2,\ell^2(H_{\Gamma,6})\bigr).                \tag{2}
\]

For real horizontal grade \(a\), let \(C_6^{\mathrm{phys}}(a)\) be the already fixed aperture-one
Sonin commutator built from the ordered \((2,3)\) Stokes curvatures. Its Calkin classification and
quantitative shell estimate are

\[
 C_6^{\mathrm{phys}}(a)\in\mathcal K
   \quad\Longleftrightarrow\quad a=0,                     \tag{3}
\]

and

\[
 \frac{|\Delta_{23}(a)|}{\sqrt6}
 \leq \|C_6^{\mathrm{phys}}(a)\|_{\mathrm{ess}}.           \tag{4}
\]

A **trace-ideal comparison** is a complex-linear map

\[
 F:\mathcal B\bigl(\ell^2,\ell^2(H_{\Gamma,6})\bigr)
   \longrightarrow \mathcal B(H_{\mathrm{Sonin}})
\]

such that

\[
 S\in\mathcal L^1\quad\Longrightarrow\quad F(S)\in\mathcal K. \tag{5}
\]

No continuity, boundedness of \(F\), cyclic trace, determinant, positivity, or divisor premise is
used. Define its strict-square defect by

\[
 \mathfrak D_F(a)=C_6^{\mathrm{phys}}(a)-F(B_6^{\mathrm{src}}). \tag{6}
\]

## Theorem and proof

`[PROVED HERE] [DAC_DENINGER_GAMMA_SIX_TRACE_IDEAL_SONIN_STRICT_LIFT_OBSTRUCTION]`

For every trace-ideal comparison \(F\) and every \(a\in\mathbb R\),

\[
 \boxed{
 \|\mathfrak D_F(a)\|_{\mathrm{ess}}
   =\|C_6^{\mathrm{phys}}(a)\|_{\mathrm{ess}}
   \geq {|\Delta_{23}(a)|\over\sqrt6}.}                   \tag{7}
\]

Consequently

\[
 \boxed{
 \exists F\text{ satisfying (5) and }\mathfrak D_F(a)=0
   \quad\Longleftrightarrow\quad a=0.}                    \tag{8}
\]

**Proof.** By `(2)` and `(5)`, \(K_F=F(B_6^{\mathrm{src}})\) is compact. Essential norm is
invariant under compact perturbation. Indeed the triangle inequality in the Calkin seminorm gives

\[
 \|C_6^{\mathrm{phys}}(a)-K_F\|_{\mathrm{ess}}
 \leq \|C_6^{\mathrm{phys}}(a)\|_{\mathrm{ess}}
      +\|-K_F\|_{\mathrm{ess}}
 =\|C_6^{\mathrm{phys}}(a)\|_{\mathrm{ess}},
\]

while writing

\[
 C_6^{\mathrm{phys}}(a)
  =(C_6^{\mathrm{phys}}(a)-K_F)+K_F
\]

gives the reverse inequality. This proves equality in `(7)`; `(4)` supplies its lower bound.

If \(\mathfrak D_F(a)=0\), then \(C_6^{\mathrm{phys}}(a)=K_F\) is compact, so `(3)` gives
\(a=0\). Conversely, at \(a=0\) the physical receiver is literally zero. The zero linear map is
a trace-ideal comparison and has zero strict-square defect. This proves `(8)`. \(\square\)

## Conjecture / proof-or-failure loop

### C1 -- relative cyclic homology absorbs the source character defect

`[FALSIFIED]`. The Connes--Karoubi multiplicative character agrees with the determinant invariant
after the canonical comparison, and joint torsion depends only on operator images modulo trace
class. These multiplicative invariants are not themselves linear chain maps. Any linearized
comparison constructed from them which preserves trace-class correction satisfies `(5)` and
therefore cannot alter the Calkin class in `(7)`. Kaad--Nest's operator-theoretic tame symbol
computes joint torsion locally; it does not provide a non-trace-class physical correction.

### C2 -- a Dixmier/singular trace annihilates the Wold coface and supplies strict descent

`[FALSIFIED]`. The source coface is already ordinary trace class, so every singular trace kills it.
The fixed physical receiver remains noncompact at every nonneutral grade. The corpus's modular
Gibbs classification independently proves that the physical normal weight becomes cyclic only at
the singular neutral wall.

### C3 -- arbitrary trace-class correction to a comparison can repair the square

`[FALSIFIED BY (7)]`. The entire correction disappears in the Calkin seminorm. Failure is not a
choice of representative or a missing cyclic-homology model.

### C4 -- construct the comparison only on the actual Xi divisor locus

`[SURVIVES; EXACT OPEN CORE]`. A fibrewise comparison may still preserve the complete trace-class
subobject and close the square at every actual Xi divisor. The theorem proves that such a
comparison cannot extend to a grade-uniform exact family away from the divisor equation: its
existence at a fibre already forces that fibre's grade to be neutral. It must therefore be
divisor-selective and use a new nonlocal multi-place consequence of `Xi(rho)=0`; otherwise existing
density, singular-corona, and finite Calkin recovery theorems erase the retained coefficient or
reproduce `(7)`. Constructing that divisor-selective lift is the remaining Route L frontier.

## No-go closure

- **Exact killing theorem/mechanism:** compact-perturbation invariance of the fixed physical
  Calkin class, applied to the literal trace-class Gamma-six Wold coface.
- **Strongest positive survivor:** the comparison obstruction
  \([\mathfrak D_F(a)]_{\mathrm{Calkin}}=[C_6^{\mathrm{phys}}(a)]_{\mathrm{Calkin}}\), with the
  quantitative lower bound `(7)` and exact zero classification `(8)`.
- **New insight:** Route L's missing square cannot be a grade-uniform functor on the trace-ideal
  quotient or a trace-class-invariant secondary character. It must be constructed only after the
  actual Xi divisor equation is available, preserve the trace ideal fibrewise, and turn that
  divisor equation into compactness. This separates the needed theorem from all ordinary
  relative-cyclic, joint-torsion, and Dixmier-trace packages.
- **Status:** paper proof and Lean formalization dependency-closed in
  `RHTower/Deninger/DeningerGammaSixTraceIdealSoninStrictLiftObstruction.lean`. Direct leaf check and
  targeted leaf build pass. Both capstones depend only on `propext`, `Classical.choice`, and
  `Quot.sound`.

## Novelty audit

Primary literature supplies parent ingredients, not `(7)`:

- [Kaad--Nest, *Tate tame symbol and the joint torsion of commuting operators*](https://arxiv.org/abs/1408.3851)
  identifies analytic joint torsion with local tame-symbol data.
- [Migler, *Joint torsion equals the determinant invariant*](https://arxiv.org/abs/1403.4882)
  proves trace-class-quotient invariance and Steinberg relations.
- [Kaad, *Comparison of secondary invariants of algebraic K-theory*](https://arxiv.org/abs/0804.1589)
  compares the Connes--Karoubi character with the determinant invariant through relative cyclic
  homology.
- [Lord--Sedaev--Sukochev, *Dixmier Traces as Singular Symmetric Functionals*](https://arxiv.org/abs/math/0501131)
  classifies the logarithmic weak-trace quotient detected by singular traces.

No located source couples those invariants to the complete Gamma-six shell coface and the fixed
Sonin \((2,3)\) receiver, nor proves the exact source-specific obstruction `(7)`. This is a
search-noncollision statement, not an external priority certificate.

## Gates

- [x] 0 → 1 in-progress: exact source and target fixed; source purity and falsifiers stated
- [x] 1 → 2 fully-proven: complete paper proof, no open dependency
- [x] 2 → 3 formalized: unconditional Lean theorem, direct check, targeted leaf build, axiom audit
- [ ] 3 → 4 publication-ready
- [ ] construct surviving singular divisor-selective multi-place lift
- [ ] prove RH

## Log

- 2026-08-15 -- Relative cyclic, joint-torsion, and Dixmier-trace proposals audited and killed.
  Exact Calkin obstruction and neutral-grade classification proved.
- 2026-08-15 -- Lean module direct-check and targeted build pass; module wired into `RHTower.lean`.
  Axiom audit is clean. Global no-build lint sees the module through the umbrella but remains red on
  seven unrelated concurrently unwired modules.
