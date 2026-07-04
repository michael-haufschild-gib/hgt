# 23 — The Section Stability Theorem (SPUR-R): Identities, Bricks, and the Theorem-M Engine

**Register: SEARCH** (proved bricks marked [PROVED HERE] with derivations below or
numerically verified to ≥ 40 digits; citations delegate-sourced — spot-check at
promotion). Task #135. Target: for g real entire, genus 0, only real zeros, and
P = (x−τ)(x−τ̄) with τ = a+bi, b > 0, the Jensen sections J^d of f = Pg satisfy
Z_c(J^d_f) = 2 for d ≥ d₀ (exactly one non-real pair — no spurious pairs), and
Z_c = 0 when P is real-rooted.

## 1. The identity stack [PROVED HERE; one-line derivations]

With γ(m) = m-th Maclaurin datum (γ = m!·coefficient), J^d_f(x) = Σ_j C(d,j)γ_j xʲ:

- **(one-step)** γ_{(·−τ)g}(m) = −τγ_g(m) + mγ_g(m−1), hence
  J^d_{(·−τ)g} = −τJ^d_g + dx·J^{d−1}_g.
- **(three-term)** J^d_{Pg} = |τ|²J^d_g − 2ad·x·J^{d−1}_g + d(d−1)x²·J^{d−2}_g.
- **(Appell)** (J^d_f)' = d·J^{d−1}_{f'}; and J^{d+1}_f = J^d_f + x·J^d_{f'}.
- **(polar chain)** (d+1)J^d_f = (d+1)J^{d+1}_f − x(J^{d+1}_f)' — consecutive
  sections are POLAR DERIVATIVES of each other at pole 0. [Delegate: not in print;
  only (J^{d,n})' = d·J^{d−1,n+1} is standard.]
- **(generating)** Σ_d J^d_f(x) u^d/d! = e^u f(xu).

## 2. Proved bricks

**(a) Universal rescaling + visibility [PROVED HERE].** C(d,j)/dʲ ≤ 1/j! with
pointwise convergence and a Cauchy-estimate majorant give J^d_f(z/d) → f(z) locally
uniformly for EVERY entire f. Hurwitz: the pair survives into J^d for d ≥ d₀
(non-real for every finite d), so Z_c(J^d_{Pg}) ≥ 2 for d ≥ d₀. The recentered
application (doc 20) needs no separate argument.

**(b) Control direction [KNOWN].** P real-rooted ⟹ Pg ∈ LP ⟹ all sections
hyperbolic (Jensen's theorem). Z_c = 0.

**(c) Pointwise Turán for the chain [PROVED HERE].** For fixed real x,
u ↦ e^u g(xu) ∈ LP(u) (affine substitution + product), and its γ-sequence in u is
exactly (J^m_g(x))_m. The classical Laguerre inequality on LP then gives

> J^m_g(x)² ≥ J^{m−1}_g(x)·J^{m+1}_g(x)  for all real x and all m,

hence T(x) := d·A_{d−1}² − (d−1)·A_{d−2}A_d ≥ 0 everywhere (A_m := J^m_g).

**(d) One-sided interlacing, two-sided breakdown [PROVED HERE + measured].** By the
polar chain and Laguerre's polar-derivative theorem, consecutive sections of g
interlace when g's zeros are one-sided of the expansion point (pole 0 outside the
zero hull). Recentering INTO the zero field breaks it (measured: PI FAIL on the
recentered carrier) — the interlacing chain is not the two-sided tool.

**(e) (HBJ) — the half-plane theorem [KNOWN via Levin; delegate-verified shape].**
{(d)_k} is the multiplier sequence of (1+x)^d; Levin's angle theorem (Distribution
of Zeros, p. 342–343; via Craven–Csordas 1983) says nonnegative multiplier
sequences preserve zeros in any angle of opening ≤ π with vertex 0 — the closed
upper half-plane is such an angle. (·−τ)g has all zeros in ĈLUHP (τ ∈ ℂ⁺, rest
real), so ALL sections J^d_{(·−τ)g} have zeros in the closed UHP; measured: strictly
upper (24/24, three τ, two carriers), and real zeros are excluded directly (a real
zero would force A_d and xA_{d−1} to vanish simultaneously). General half-planes are
NOT preserved (Craven–Csordas Thm 3.3: angles are sharp) — the vertex-at-0 case is
exactly ours. NOTE: the Borcea–Brändén symbol of the Jensen operator computes to
Σ_j C(d,j)(d)_j xʲy^{d−j} = the homogenization of a LAGUERRE polynomial (reverse of
Σ C(d,i)xⁱ/i! = L_d(−x)) — real stable — an independent one-line stability-preserver
proof route [delegate: no published source applies BB to Jensen polynomials].

**Failed intermediates (recorded per protocol):** the half-step ℂ̄⁻-stability claim
was FALSE (sign error: c_kα_k < 0 in both one-sided orientations, so the ratio map
is Pick; probe refuted it before the doc did), and the count-conjecture PJ/PK was
superseded by the stronger (HBJ).

## 3. The theorem-m engine [structural transfer]

The lab's founding preprint (theorem-m: "Unconditional hyperbolicity of the critical
Laguerre family") proves hyperbolicity of a deformed family by: hyperbolic anchor +
coefficientwise deformation + SIGN TRANSFER at the anchor's critical points, with
amplitude control from an energy monotonicity (E = C² + C'²). Transferring that
skeleton to the pair deformation collapses beautifully — at every critical point c
of the anchor A_d (A_d'(c) = 0), the polar chain gives EXACT collapse:

> **A_{d−1}(c) = A_d(c)**,  A_{d−2}(c) = A_d(c) + c²A_d''(c)/(d(d−1)),

hence [verified 41 digits on the pod]

> **(CPI)  J^d_{Pg}(c) = q_d(c)·A_d(c) + c⁴·A_d''(c),
>  q_d(c) = |τ|² − 2adc + d(d−1)c²,**

and q_d is POSITIVE DEFINITE on ℝ exactly when d > 1 + a²/b². Sign transfer: at
every critical point where q_d(c)|A_d(c)| > c⁴|A_d''(c)|, the section J^d_{Pg}
copies the sign of A_d; each preserved sign alternation forces a real zero between
consecutive critical points, so the non-real count is controlled by the failure
structure. [CORRECTED in doc 24 §3: strict failure FORCES the flipped sign, which
still alternates; the right bound is Z_c ≤ 2 + T with T = #copy↔flip transitions,
and T = 1 + evenness gives Z_c ≤ 2.]

The curvature term opposes the amplitude at every extremum (A·A'' ≤ 0 there), so
the needed input is a lower bound on extremal amplitudes against the local
frequency — precisely theorem-m's energy object, now for the section chain.

## 4. The residual, named

> **(AMP) [OPEN]:** for d ≥ d₀, the transfer inequality q_d(c)|A_d(c)| > c⁴|A_d''(c)|
> holds at all but at most ONE critical point of A_d, the exception localized at the
> pair. Candidate energy: E_d = A_d² + w_d(x)A_d'² with w_d from the polar chain
> (theorem-m's E = C² + C'² is the Kummer-equation case); the chain's pointwise
> Turán (§2c) is the algebraic half of the estimate.

[SUPERSEDED: the (AMP) attack (doc 24) refuted the all-but-one form — the far flip
block is permanent — and re-cut the residual as (AMP-mono): the margin sequence
crosses 1 exactly once. See doc 24 §5.]

Status: (SPUR-R) = bricks (a),(b),(e) [done] + (CPI) [done] + (AMP-mono) [open]. With
(AMP), the DISC reader (doc 20) is provably exact on LP×pair carriers, and the
measured finite instance (#136: the truncation's off-line zero read correctly at
d = 4, 6, 8; domination provably failing there, as banked transport forces) sits on
theorem legs. Next: hunt w_d via the generating identity — e^u g(xu) turns the chain
into ONE two-variable object, and theorem-m's energy argument is an ODE statement;
the u-direction supplies the missing differential equation.

---
**STATUS 2026-07-05 (tasks #135/#138/#139 verdict — doc 79):** RETIRED as a route. The
reader-exactness this theorem targets is **superseded** by the Rouché+EM counting spine
(`enclosed_count_eq_of_close` + `completed_domination_of_em`, axiom-clean, Spur-independent
island — doc 79 §1), which delivers exact off-line-pair counting from DOMINATION alone,
where SPUR-R needs the carrier's zero-geometry ((F1)–(F3), measured-only). Core is SOUND not
false (winding formula + `Z_c=2` verified, doc 79 §3); Lean form honest-complete
(`AMPReaderInput` hypothesis-typed). Open core (S-mono)+(Lemma R) isolated as a standalone
entire-function conjecture, not a #130 blocker.
