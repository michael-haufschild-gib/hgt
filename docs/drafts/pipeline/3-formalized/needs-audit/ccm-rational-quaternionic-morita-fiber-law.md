# Quaternionic sign-reflection on the rational CCM Morita fiber

- **ID:** `ccm-rational-quaternionic-morita-fiber-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), novelty needs audit
- **Source:** `kreal-quaternionic-ccm-cokernel` · rational Morita construction lane
- **Statement:** the canonical CCM fiber \(\ell^2(\mathbb Q^\times)\) has a no-doubling
  quaternionic sign-reflection whose covariance detects the sign grading of
  \(\mathbb Q^\times\).

## Goal

Construct Deninger's odd \(K_{\mathbb R}\) coefficient operator directly on Hilbert data already
present in CCM's rational Morita equivalence, before matrix algebra and ordinary trace erase its
quaternionic square.

## Setup

CCM use the canonical splitting
\[
  \mathbb A_{\mathbb Q}^{\times}/\mathbb Q^\times=C_{\mathbb Q}
\]
and the fundamental domain
\(\Delta_{\mathbb Q}=\widehat{\mathbb Z}^{\,*}\times\mathbb R_+^*\).
Their fiber is canonically
\[
  \mathcal H_b=\ell^2(\mathbb Q^\times),\qquad b\in\Delta_{\mathbb Q}.
\]
For \(k\in\mathbb Q^\times\), use the left regular convention
\[
  (L_k f)(q)=f(k^{-1}q).
\]

Define the conjugate-linear sign-reflection
\[
  (\mathcal J f)(q)=\operatorname{sgn}(q)\,
    \overline{f(-q)}.                                      \tag{1}
\]

## Theorem

`[PROVED HERE]` The operator \(\mathcal J\) has the following properties.

1. It is additive and conjugate-linear.
2. It is antiunitary on \(\ell^2(\mathbb Q^\times)\).
3. It is quaternionic:
   \[
     \mathcal J^2=-1.                                     \tag{2}
   \]
4. It is covariant for rational scaling:
   \[
     \mathcal J L_k=\operatorname{sgn}(k)L_k\mathcal J.   \tag{3}
   \]
5. For a multiplication operator \(M_\phi\),
   \[
     \mathcal J M_\phi \mathcal J^{-1}
       =M_{\phi^{\mathcal J}},\qquad
     \phi^{\mathcal J}(q)=\overline{\phi(-q)}.             \tag{4}
   \]
6. For CCM's monomial matrix
   \[
     M_b(x,y)=f_k(xb),\qquad k=xy^{-1},
   \]
   antiunitary conjugation has kernel
   \[
     (\operatorname{Ad}_{\mathcal J}M_b)(x,y)
       =\operatorname{sgn}(x)\operatorname{sgn}(y)
          \overline{M_b(-x,-y)}
       =\operatorname{sgn}(k)\overline{f_k(-xb)}.          \tag{5}
   \]
   Thus it preserves the restricted groupoid representation and is independent of \(b\).
7. Passing to endomorphisms erases the quaternionic central sign:
   \[
     \operatorname{Ad}_{\mathcal J}^2(T)=T.               \tag{6}
   \]

No copy of \(\ell^2(\mathbb Q^\times)\) is added; the pair \(q,-q\) is already present in the
single CCM fiber.

## Proof

Additivity and conjugate-linearity follow directly from (1).  Since negation permutes
\(\mathbb Q^\times\) and \(|\operatorname{sgn}(q)|=1\),
\[
  \|\mathcal Jf\|_2^2
    =\sum_q|f(-q)|^2
    =\|f\|_2^2.
\]
Surjectivity follows from (2), so \(\mathcal J\) is antiunitary.

Using \(\operatorname{sgn}(-q)=-\operatorname{sgn}(q)\),
\[
\begin{aligned}
  (\mathcal J^2f)(q)
   &=\operatorname{sgn}(q)\,
     \overline{\operatorname{sgn}(-q)\overline{f(q)}}\\
   &=-\operatorname{sgn}(q)^2f(q)=-f(q),
\end{aligned}
\]
which proves (2).

For (3),
\[
\begin{aligned}
  (\mathcal JL_kf)(q)
   &=\operatorname{sgn}(q)\overline{f(-k^{-1}q)},\\
  (L_k\mathcal Jf)(q)
   &=\operatorname{sgn}(k^{-1}q)\overline{f(-k^{-1}q)}
     =\operatorname{sgn}(k)\operatorname{sgn}(q)
        \overline{f(-k^{-1}q)}.
\end{aligned}
\]
Because \(\operatorname{sgn}(k)^2=1\), these are related as claimed.

Since \(\mathcal J^{-1}=-\mathcal J\), direct substitution gives (4).  Applying the same
substitution to a matrix kernel gives
\[
  (\operatorname{Ad}_{\mathcal J}T)(x,y)
   =\operatorname{sgn}(x)\operatorname{sgn}(y)
      \overline{T(-x,-y)}.
\]
For a CCM monomial, \((-x)(-y)^{-1}=xy^{-1}=k\) and
\(\operatorname{sgn}(x)\operatorname{sgn}(y)=\operatorname{sgn}(k)\), proving (5).
Finally,
\[
  \operatorname{Ad}_{\mathcal J}^2(T)
   =\mathcal J^2T\mathcal J^{-2}
   =(-1)T(-1)^{-1}=T,
\]
proving (6).

## Hostile interpretation

`[NO-GO]` The theorem does **not** by itself make the CCM trace-class algebra
\(K_{\mathbb R}\)-odd.  Ordinary endomorphism algebra and Morita trace pair the quaternionic
module with its dual, so the central \(-1\) cancels exactly as in (6).  Applying ordinary cyclic
homology after \(\operatorname{End}(\mathcal H_b)\) can therefore recover at most a Real
involution.

## Strongest positive survivor

`[NEW]` The missing sign is already present, without doubling, on CCM's rational Morita
**bimodule**, but is destroyed by the ordinary endomorphism/trace passage.  A successful lift must
enhance the *relative restriction correspondence* before this passage and retain one unpaired
copy of \(\mathcal H_b\).  Concretely, the next target is Real/quaternionic cyclic homology with
coefficients in the sign-reflection Morita bimodule, together with a comparison theorem showing
that forgetting the coefficient structure is the single CCM relative realization.

This replaces the earlier unconstrained search for an order-four anti-map on the trace-class
algebra by a specific source operator and a specific descent problem.

## Novelty audit

- CCM give the canonical rational fiber and matrix Morita map, but do not equip the fiber with
  (1) or retain quaternionic data through their cyclic trace.
- Deninger specifies the required \(K_{\mathbb R}\) square but does not connect it to the CCM
  Morita fiber.
- Moutuou's Real graded Brauer theory and Kaledin's cyclic homology with coefficients provide
  established categorical homes for Real Morita data and cyclic coefficients.
- Exact searches for the sign-reflection formula together with CCM, Deninger, or arithmetic
  cyclic cohomology found no prior construction.

The elementary operator identities are not individually claimed as novel.  The identified
placement of the quaternionic structure on the pre-trace CCM Morita bimodule is labelled new
pending expert review.

Lean module:
`GaloisForLFunctions.RHTower.CCMRationalQuaternionicMoritaFiber`.

Formal capstones:

- `ccmRationalQuaternionicReflection_sq`;
- `ccmRationalQuaternionicReflection_leftScale`;
- `ccmRationalKernelRealStructure_sq`;
- `ccmRationalKernelRealStructure_monomial`;
- `ccmRationalQuaternionicReflectionₛₗ`.

## Gates

- [x] 0 → 1 in-progress: source-pure rational CCM datum and no-doubling test
- [x] 1 → 2 fully-proven: complete proof above; no open dependency
- [x] 2 → 3 formalized: leaf build green; axiom audit contains only Lean foundational axioms;
  formal lint passes
- [ ] 3 → 4 publication-ready: external expert novelty review and full CCM notation audit

## Sources

- Connes--Consani--Marcolli, *The Weil proof and the geometry of the adeles class space*,
  arXiv:math/0703392, especially the rational Morita map and
  \(M_b(x,y)=f_{xy^{-1}}(xb)\).
- Christopher Deninger, *There is no "Weil-"cohomology theory with real coefficients for
  arithmetic curves*, arXiv:2204.02714.
- D. Kaledin, *Cyclic homology with coefficients*, arXiv:math/0702068.
- El-kaïoum M. Moutuou, *Graded Brauer groups of a groupoid with involution*,
  arXiv:1202.2057.

## Log

- 2026-07-25 — proved after the graded-adjoint attack isolated the need for an intrinsic
  no-doubling quaternionic carrier.  No numerical evidence and no RH assumption used.
- 2026-07-25 — formalized in `CCMRationalQuaternionicMoritaFiber.lean`; minimal
  `lake env lean GaloisForLFunctions/RHTower/CCMRationalQuaternionicMoritaFiber.lean` passed;
  final `lake build GaloisForLFunctions.RHTower.CCMRationalQuaternionicMoritaFiber` passed;
  formal lint passed.
