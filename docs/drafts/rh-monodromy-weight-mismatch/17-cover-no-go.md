# 17 — The Cover No-Go: Compositional Rigidity Closes the Construction Hunt

**Register: SEARCH**, with a paper-proved no-go (§2–3) and one named open core (§5).
Resolves #116 (14-parity-stratum §4.4 survivor 2): the hunt for a quadrant-ramified
cover detector terminates in a THEOREM that no polynomial/rational/entire-with-poles
cover exists beyond the FE descent, and the sole surviving possibility is isolated as
a compositional-rigidity question about Ξ that is native to the hgt program.

## 0. What a cover detector must be

Doc 14 §4.1: parity is forced at RAMIFICATION points of factorizations of the function
itself. A cover π forces `2 ∣ ord_{u₀}(F)` only if F = G ∘ π with π 2-ramified AT u₀
(then ord = e·ord(G∘-image)). So a detector for a MOVABLE off-line point requires a
FAMILY of factorizations of ξ — equivalently, for degree 2, a family of involutions σ
with ξ ∘ σ = ξ fixing the hypothetical zero. The question is: what factorizations
does ξ admit at all?

## 1. Honesty first: the u-plane object is classical (novelty-ledger correction)

xiDescent(u) = ξ(1/2 + √u) is, up to normalization, the CLASSICAL Ξ₁ function
(Riemann's Ξ read in the variable z²; Pólya–Jensen's guise, in which RH = "all zeros
on the negative real axis"). The STATEMENT of `rh_iff_xiDescent_ne_zero_slitPlane` is
classically known in this form. What is new in this lane and stays new: the
machine-checked construction (Painlevé route, branch-free descent identity), the
2^k-graded ladder/deck calculus on it, and the ledger. The OBJECT is classical; the
OBSTRUCTION LANGUAGE on it is ours. Recorded so the novelty audit of doc 14/§12 stays
exact.

## 2. The affine no-go `[PROVED HERE — paper]`

**Theorem.** The compositional symmetry group {σ affine : ξ ∘ σ = ξ} is exactly
{id, s ↦ 1−s}. Consequently the FE descent is the UNIQUE factorization of ξ through a
degree-2 polynomial cover, and there is none through a degree-2 rational cover.

*Proof.* Let σ(s) = as + b with ξ∘σ = ξ. σ permutes the zero set Z ⊂ {0 < Re < 1}.
(i) Taking zeros γ_n → +i∞: Re(σ(1/2 + iγ_n)) bounded forces Im a = 0, so a ∈ ℝ.
(ii) σ and σ⁻¹ both inject Z into Z; the counting function N(T) ~ (T/2π)·log T then
forces |a|·1 ≥ 1 and ≤ 1 by symmetry: a = ±1.
(iii) a = 1, b ≠ 0: if Re b ≠ 0, iterates push Z out of the strip — impossible. If b
purely imaginary, Z is invariant under vertical translation: Z is then a union of
translates of the (finite, by discreteness in the compact cell strip×period) zero set
of one period cell, so N(T) grows LINEARLY — contradicting N(T) ~ T log T. So b = 0.
(iv) a = −1: compose with the FE involution τ(s) = 1−s: τσ is the translation
s ↦ s + (1−b); by (iii) it is the identity, so b = 1 and σ = τ. ∎

Degree-2 polynomial covers π correspond exactly to their deck involutions (affine);
degree-2 rational non-polynomial covers have Möbius deck involutions with a finite
pole p, and ξ∘σ = ξ would put an essential singularity of ξ at p — impossible. ∎

**Reading.** The FE is not just *a* symmetry of ξ — it is the ONLY compositional
symmetry in the affine/Möbius sector. The 14 §4.1 audit verdict ("FE covers are base
case only") is now a uniqueness theorem: there was never a second cover to find here.

## 3. The higher-degree and rational no-go `[PROVED HERE — paper, promotion checks flagged]`

Let ξ = G ∘ π nonconstant with π rational or polynomial, deg π = d ≥ 2.

- If G has finitely many zeros, ξ would have finitely many — false. So G has zeros
  w_n → ∂(domain).
- π rational with a finite pole p: values near ∞ are attained near p, so zero-fibers
  accumulate at the FINITE point p — but Z is discrete. Hence π is a polynomial and
  w_n → ∞.
- π polynomial, |w| → ∞: the d preimages of w spread along d asymptotic directions
  (the d-th roots, scaled |w|^{1/d} → ∞). Zero-fibers lie in Z ⊂ horizontal strip:
  only directions ±(real axis) are available, so d ≤ 2; and d = 2 forces the deck
  involution into §2, which pins it to the FE. ∎

`[Promotion checks: the two classical inputs — N(T) ~ (T/2π) log T (Riemann–von
Mangoldt) and the asymptotic fiber-direction expansion for polynomials — both
standard; the strip-confinement of Z is banked (xi_eq_zero_iff + zero-free region
facts).]`

**Corollary (u-plane form).** xiDescent = Ξ₁-normalization admits NO factorization
through any polynomial or rational cover of degree ≥ 2 at all: its zeros hug a SINGLE
asymptotic direction (the negative axis), and even d = 2 needs two opposite fiber
directions. The FE cover is spent in the descent, exactly as doc 14 predicted.

## 4. What survives: only the transcendental sector, and only in one shape

Pólya's composition theorem: if G ∘ π is of finite order with π transcendental entire,
then G has order 0 (and growth composition constrains the pair). ξ has order 1;
xiDescent has order 1/2. So the only unclosed factorizations are

  xiDescent = G ∘ π,  G entire of order 0 with infinitely many zeros,
  π transcendental entire of order ≤ 1/2 whose zero-fibers all lie asymptotically
  along the negative real axis.

The direction argument does NOT kill this: order-1/2 functions with one singular
tract along a ray exist and have exactly the right fiber geometry (cos√(−u)-type:
fibers (arccos w + 2πn)² lie on a ray). The question is whether Ξ actually admits
such a decomposition.

## 5. The open core: Ritt rigidity of Ξ `[OPEN CORE — hgt-native]`

> **(RittΞ)** The Riemann Ξ function (equivalently xiDescent) is compositionally
> PRIME in the transcendental sector: xiDescent = G ∘ π with π entire forces π
> affine or the assertion fails.

- If (RittΞ) holds: #116's construction hunt is FULLY closed — no cover detector of
  any compositional type exists; the parity burden lies entirely with the
  conservation front (OC1′), completing the concentration begun in doc 14.
- If (RittΞ) fails: the witnessing π is a NEW hidden symmetry of ζ — an object of
  the first magnitude, and (by §0) a genuine off-line parity detector at its
  ramification points.

Either branch is a major result; the conjecture is decision-complete for #116. Note
what this question IS: compositional rigidity of a seed object of the hgt program —
the exact analogue, in the composition monoid, of the differential rigidity
(hypertranscendence) that founds the branch. It drops out of the RH lane INTO the
lab's core mission: a new gatekeeper for 𝓜⁺, attackable with Nevanlinna theory —
which mathlib now carries (ValueDistribution, JensenFormula; cf. #123). Known
adjacent territory: Ritt's theorems (polynomial case, closed above independently),
Gross–Yang on factorization of entire functions of finite order. `[CHECK C11, at
promotion: literature on factorization/pseudo-primeness of Ξ specifically — the
classical factorization literature (Gross, Yang, Urabe) studied E-functions and
order-restricted classes; whether Ξ's pseudo-primeness is on record must be verified
before claiming (RittΞ) open.]`

## 6. Board consequences

- **#116 terminalizes**: construction refuted in the polynomial/rational/entire-with-
  poles sectors (theorem); survivor isolated as (RittΞ). No further cover hunting.
- **The parity front's two survivors (14 §4.4) reduce to: conservation (OC1′,
  doc 16) as the ACTIVE lane, plus (RittΞ) as a named open core** whose refutation
  branch would reopen covers.
- (RittΞ) itself is a candidate pipeline card for the hgt main line (compositional
  gatekeeper), independent of RH: it advances the branch whichever way it falls.
