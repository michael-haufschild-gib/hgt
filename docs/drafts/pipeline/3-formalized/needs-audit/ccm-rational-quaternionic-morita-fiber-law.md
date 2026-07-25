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
7. Passing to endomorphisms turns the central square into a Real involution:
   \[
     \operatorname{Ad}_{\mathcal J}^2(T)=T.               \tag{6}
   \]
8. This involution retains the quaternionic Brauer type through its fixed algebra:
   \[
     \operatorname{Ad}_{\mathcal J}(T)=T
       \quad\Longleftrightarrow\quad
     T\mathcal J=\mathcal JT.                              \tag{7}
   \]
9. On rational crossed-product monomial coefficients, the induced twist
   \[
     (\alpha_k\phi)(x)
       =\operatorname{sgn}(k)\overline{\phi(-x)}
   \]
   is conjugate-linear, involutive, and multiplicative:
   \[
     \alpha_{k\ell}(\phi\star_k\psi)
       =(\alpha_k\phi)\star_k(\alpha_\ell\psi),\qquad
     (\phi\star_k\psi)(x)=\phi(x)\psi(k^{-1}x).             \tag{8}
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

Write the involution as
\(\sigma_{\mathbb H}(T)=-\mathcal JT\mathcal J\), using
\(\mathcal J^{-1}=-\mathcal J\). If \(T\mathcal J=\mathcal JT\), then
\[
  \sigma_{\mathbb H}(T)
    =-\mathcal JT\mathcal J
    =-T\mathcal J^2=T.
\]
Conversely, if \(-\mathcal JT\mathcal J=T\), compose with \(\mathcal J\) and use
\(\mathcal J^2=-1\) to obtain \(\mathcal JT=T\mathcal J\). This proves (7). The same
calculation proves that \(\sigma_{\mathbb H}\) is conjugate-linear, unital, and multiplicative.

For monomial coefficients, involutivity follows from
\(\operatorname{sgn}(k)^2=1\) and applying conjugation and negation twice. Moreover,
\[
\begin{aligned}
  \alpha_{k\ell}(\phi\star_k\psi)(x)
   &=\operatorname{sgn}(k)\operatorname{sgn}(\ell)\,
     \overline{\phi(-x)\psi(-k^{-1}x)}\\
   &=(\alpha_k\phi)(x)(\alpha_\ell\psi)(k^{-1}x),
\end{aligned}
\]
which proves (8).

## Hostile interpretation

`[NO-GO]` The theorem does **not** by itself construct the analytic CCM cyclic cokernel or its
twisted derived \(\operatorname{Tor}\). Ordinary complex Morita trace forgets the fixed algebra
in (7), so it still cannot produce Deninger's odd \(K_{\mathbb R}\)-object.

`[CORRECTION]` The earlier reading of (6) as complete erasure was too strong. Moutuou proves
that for \(J^2=-1\), the Real structure \(T\mapsto-JTJ\) has fixed algebra equal to the compact
quaternionic-linear operators. It represents the non-split quaternionic Real Brauer type.

## Strongest positive survivor

`[NEW]` The missing sign is already present, without doubling, on CCM's rational Morita
**bimodule**, and the induced operator algebra retains it as non-split Real Brauer type. A
successful lift must enhance the relative restriction correspondence and carry this type through
closed cyclic cokernel and derived \(\operatorname{Tor}\). Concretely, next target is a
Real-Brauer-twisted cyclic realization whose forgetful complex is the single CCM realization.

This replaces both the unconstrained order-four search and the unnecessarily restrictive
"unpaired coefficient" requirement by a specific source operator, fixed algebra, and descent
problem.

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

Lean modules:

- `GaloisForLFunctions.RHTower.CCMRationalQuaternionicMoritaFiber`;
- `GaloisForLFunctions.RHTower.CCMRationalMoritaHilbertQuaternionic`;
- `GaloisForLFunctions.RHTower.CCMRationalRealCrossedProduct`;
- `GaloisForLFunctions.RHTower.CCMRationalKRealBrauerBridge`.

Formal capstones:

- `ccmRationalMoritaHilbertReflectionFunction_memℓp`;
- `ccmRationalMoritaHilbertReflection_sq`;
- `ccmRationalMoritaHilbertReflection_norm`;
- `ccmRationalMoritaHilbertQuaternionicIsometry`;
- `ccmRationalQuaternionicReflection_sq`;
- `ccmRationalQuaternionicReflection_leftScale`;
- `ccmRationalKernelRealStructure_sq`;
- `ccmRationalKernelRealStructure_monomial`;
- `ccmRationalQuaternionicReflectionₛₗ`;
- `ccmRationalEndomorphismRealStructure_sq`;
- `ccmRationalEndomorphismRealStructure_comp`;
- `ccmRationalEndomorphismRealStructure_fixed_iff`;
- `ccmRationalEndomorphismRealStructureₛₗ`;
- `ccmRationalMonomialRealTwist_sq`;
- `ccmRationalMonomialRealTwist_product`;
- `ccmRationalMoritaKRealOdd`;
- `ccmRationalEndomorphismKRealEven`;
- `ccmRationalEndomorphismKRealEven_fixed_iff`;
- `ccmRationalLeftScaleKRealMorphism`.

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
- 2026-07-25 — corrected the endomorphism-erasure interpretation after auditing Real graded
  Brauer classification. Added and formalized the fixed-algebra law and the full finite-support
  crossed-product Real involution. Both cached leaf builds passed; axiom audit contains only
  `propext`, `Classical.choice`, and `Quot.sound`; formal lint passed.
- 2026-07-25 — connected quaternionic source and Real endomorphism algebra to the generic
  \(K_{\mathbb R}\) interface in `CCMRationalKRealBrauerBridge.lean`. Minimal Lean check and
  cached leaf build passed; capstone axiom audit contains only `propext`,
  `Classical.choice`, and `Quot.sound`.
- 2026-07-25 — upgraded the algebraic function-space reflection to the actual CCM Hilbert
  fiber `lp (fun _ : CCMRationalUnit => ℂ) 2`. Formalized square \(-1\), norm preservation,
  and the resulting conjugate-linear isometric equivalence without adding a second fiber.
  Minimal `lake env lean` and final cached leaf `lake build` passed; all five audited
  capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.
