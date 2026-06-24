# Approximate differential-complexity divergence — minimal model complexity → ∞

- **ID:** ht-c26-approx-complexity-divergence
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C26
- **Statement:** Fix a norm on a compact subdomain and bound the degree/order/height of differential polynomials over `K`. For generic `f ∈ HT`, the minimal complexity of a differential polynomial approximating `f` to tolerance `ε` tends to `∞` as `ε→0`, with no eventual bounded template.

## Goal
Give a **quantitative, monotone, falsifiable** form of HT: exact zero residual at fixed complexity is forbidden, and the approximate version diverges. Door: turns the (A) absence into a measurable curve — directly experiment-driven.

## Door grade (hint)
**BRIDGE-likely (quantitative refinement).** Provable lower bounds may follow from a quantitative Hölder/elimination estimate; primarily a numerics target.

## Approach
Define `c(ε)=min complexity achieving residual ≤ ε`; show no bounded template (else a limiting exact relation contradicts HT). mpmath: tabulate `c(ε)` for Γ-like and random `f`, look for divergence vs plateau. Methods: 11 run experiments, 13 monotone quantity, 14 weaken.

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C26; C08 (Padé), C25 (operator rank).

## Log
- 2026-06-20 — created in 0-backlog from bucket C26.

## 2026-06-23 chat mutation — precision plateau is hygiene; asymptotic defect spectrum is the live object

Turing/Wheeler proposed residual fitting against finite algebraic differential boxes as a discriminator for HT. The naive version `R(d)` is not promotable: sampled residuals overfit once the monomial count approaches sample count, and floating-point holdout residuals can fake relations through ill-conditioning. Precision scaling is necessary PSLQ-style hygiene: a true relation tracks the precision floor, while a spurious numerical relation freezes at a positive floor.

The theatre-test distinction is:

- `plateau(n,d)>0` at a fixed finite box is not new knowledge. With fixed compact domain, basis, normalization, and no exact relation, it is just the smallest singular-value floor / finite-box non-membership, and for Gamma the exact non-membership is already Holder.
- The live candidate is the canonical quantitative DA-defect spectrum
  `Delta_f(K; n,d,H) = inf normalized residual over algebraic differential polynomials of order <= n, degree <= d, height <= H`, with independent validation and a fixed complex compact `K`.
- For DA functions, `Delta` reaches zero at finite complexity. For HT functions, every finite box stays positive. The only possible novelty is the asymptotic geometry: decay class of `Delta_f` as `(n,d,H)` grow, and whether finite Euler/Gamma_N controls converge to or fake that landscape.

Status: HOLD / LIVE MUTATION. Significant if it becomes a canonical constraint-side landscape invariant for HT. Not novel yet; it may reduce to standard numerical algebraic relation detection plus Holder unless the asymptotic decay class is made basis/domain-stable and shown to contain information not already in classical hypertranscendence.

## 2026-06-23 source-check narrowing — broad novelty is dead

A focused source check found several adjacent literatures, so the broad novelty claim is rejected:

- Differential approximants already approximate functions by solutions of polynomial-coefficient linear ODEs in series analysis (Guttmann/Joyce; Au-Yang/Fisher; summarized by Guttmann/Jensen).
- D-algebraic guessing explicitly searches finite data for polynomial differential equations satisfied by generating functions.
- Numerical jet geometry / approximate differential algebra already treats approximate polynomial differential systems with symbolic-numeric and residual/stability machinery.
- Kolchin/differential dimension polynomials already supply exact differential-algebraic complexity-growth invariants, though not this metric.

Narrow remaining candidate: not residual fitting, and not fixed-box positivity. The only plausible novelty path is a quantitative differential-transcendence measure for a fixed HGT object, e.g. Gamma: an explicit lower bound or stable asymptotic decay law for `Delta_Gamma(K;n,d,H)` under tame changes of basis, compact domain, and jet-coordinate scaling, with DA and near-DA controls. Promotion requires showing the decay class is not an artifact of differential approximants, D-algebraic guessing, numerical jet geometry, or Kolchin-style exact complexity.

Current vote: `LIVE C`, not promoted. Kill condition: no canonical normalization / decay class survives basis and domain adversaries. Promotion line: a basis/domain-stable lower-envelope theorem or controlled computation strong enough to motivate such a theorem.

## 2026-06-23 additional source risk — graph transcendence measures

A closer reduction threat is the literature on transcendence measures and algebraic growth of entire functions. Coman--Poletsky estimate transcendence measures for an entire function `f` and derive Bernstein/doubling/Markov inequalities for polynomials `P(z,f(z))` along its graph, with zero-count bounds in terms of degree and radius. This is not the same as a differential-jet polynomial `P(s, Gamma, Gamma', ..., Gamma^(n))`, but it kills any broad claim that effective lower bounds for polynomial residuals along transcendental function graphs are new.

Next normal-form question: can the Gamma jet expression be converted, on pole-free compact sets or globally after clearing poles, into a polynomial along an entire finite-order curve covered by existing algebraic-growth/transcendence-measure theorems, e.g. using `1/Gamma` and derivatives? If yes, this card downgrades to an application/bookkeeping problem. If no, the possible new residue is specifically a differential-jet + shift-orbit + pole-lattice lower bound for Gamma, not generic graph transcendence.

## 2026-06-23 typing correction and `1/Gamma` normal form

The complexity box must include an `s`-degree parameter. The live object is `Delta_f(K; n,d,m,H)`, where `n` is differential order, `d` is jet-degree, `m` is degree in `s`, and `H` is coefficient height/norm. Without `m`, the Gamma shift argument `s -> s+k` is not well-typed because composing with the shift matrix preserves jet degree but raises `s`-degree.

Normal-form reduction risk: set `F=1/Gamma`. Then `F` is entire of order 1 and Gamma jets are rational in the finite jet of `F`: `Gamma=1/F`, `Gamma'=-F'/F^2`, etc. Multiplying by a bounded power of `F` converts any polynomial `P(s, Gamma, ..., Gamma^(n))` into a polynomial `Q(s, F, F', ..., F^(n))`. On compact sets away from poles of Gamma / zeros of `F`, smallness of `P(s,j^n Gamma)` is equivalent up to constants to smallness of `Q(s,j^n F)`.

Thus the Gamma DA-defect lower-bound problem embeds locally into polynomial approximation along the entire finite-order jet curve `s -> (F(s), F'(s), ..., F^(n)(s))`. The card survives only if existing algebraic-growth / transcendence-measure results for entire curves do not already yield the desired `Delta(K;n,d,m,H) >= C H^{-kappa}` lower envelope. If the reduction to known entire-curve theory works, downgrade this card to application/bookkeeping; if it fails at a named hypothesis, that failed hypothesis becomes the actual HGT target.

## 2026-06-23 split — Hilbert defect vs arithmetic height defect

Turing's first plateau grid showed fast decay of raw monomial singular values (`Gamma` order/degree boxes), but this is now classified as basis geometry / power-basis collinearity, not an HGT invariant. The residual approach must split into two non-interchangeable objects:

1. **Hilbert/projective defect.** Choose a finite-dimensional model space `V(n,d,m)` with a basis-free norm and measure projective distance after Gram/QR. This can be useful numerically, but it has no arithmetic height and is likely ordinary approximation theory / entire-curve geometry.
2. **Arithmetic height defect.** Fix a coefficient lattice in the canonical monomial basis `(s,y_0,...,y_n)` and ask for the minimal height needed to approximate within tolerance:
   `H_Gamma(K;n,d,m,epsilon) = min height(P)` over nonzero lattice polynomials with `deg_y<=d`, `deg_s<=m`, and `||P(s,j^n Gamma)||_K <= epsilon`.

Gram-Schmidt and height cannot be freely mixed: QR uses domain-dependent generally transcendental coefficients and destroys the coefficient lattice. Therefore the only serious novelty path is the arithmetic-height version, not raw singular values and not orthonormalized residuals. Promotion would require a lower bound on `H_Gamma` as `epsilon -> 0` that is stronger or structurally different from generic entire-curve approximation and uses Gamma-specific shift / zero-pole lattice structure.

## 2026-06-23 Wheeler vote and factorial-residue fork

Wheeler voted `LIVE C`, not `PROMOTE`, on the narrowed arithmetic-height target. His proposed Gamma-specific mechanism is the factorial decay of pole residues:
`Res_{s=-k} Gamma = (-1)^k/k!`, which may weaken pole-constraint overdetermination and affect height lower bounds.

Critical correction: after the normal-form reduction `F=1/Gamma`, the same lattice becomes a simple zero lattice for an entire order-1 function with
`F'(-k)=(-1)^k k!`. Thus factorial decay of Gamma residues becomes factorial growth of derivatives of `F`; it is not yet a reason that generic entire-curve transcendence measures fail. The live fork is:

- **A.** Existing entire-curve transcendence-measure theorems do not control polynomial expressions in the full jet curve `(F,F',...,F^(n))` with the required coefficient-height/lattice dependence.
- **B.** They do control it, but only with generic bounds too weak to see a Gamma-specific shift/zero-lattice exponent; possible novelty is an improved Gamma-specific exponent.
- **C.** They fully imply the desired `H_Gamma(K;n,d,m,epsilon)` lower bound after clearing denominators; then this card downgrades to an application/bookkeeping problem rather than new HGT knowledge.

Status remains `LIVE`, not promoted. Next useful artifact is a fake proof or reduction that boxes exactly A, B, or C; residual grids are evidence only if tied to coefficient-height / QR-pullback height distortion.

## 2026-06-23 coefficient-field correction and difference-measure narrowing

Turing caught a control-design flaw: the coefficient lattice must include the coefficients of a known DA relation, otherwise a control can falsely look HT. For Gamma / `F=1/Gamma` / rational meromorphic toys, the intended lattice is `Z[s,y_0,...,y_n]` after clearing rational denominators. For finite Euler controls, actual prime rates `log p` do not lie in `Z`; either use rate `c=1` for rank-1 integer-coefficient Riccati, use algebraic rates such as `1, sqrt(2)` with lattice `Z[sqrt(2)]` and height in a fixed basis, or keep symbolic parameters with explicit height bookkeeping. A DA control counts only over a coefficient field/lattice containing the coefficients of its known relation.

Source narrowing: parameterized difference-Galois / Hardouin--Singer style results cover the qualitative Gamma hypertranscendence mechanism via the shift equation, so the shift story alone is known. The remaining live target is not qualitative Hölder and not generic graph transcendence; it is an effective additive-shift arithmetic-height lower bound for `H_Gamma(K;n,d,m,epsilon)`, possibly analogous in role to quantitative refinements in Mahler-type methods. This remains `LIVE`, not promoted, pending a check whether existing quantitative difference-algebra / difference-Galois transcendence-measure machinery already supplies it.

## 2026-06-23 role split and orbit-normalized shift test

Haiku paused the RunPod computation to avoid a one-agent conjecture/script/verdict loop. Accepted role split: Wheeler supplies one structural prediction only; Turing implements coefficient-lattice mechanics only; Haiku gatekeeps decomposition only; Professor owns prior-art / normal-form kill only. Any artifact where one agent writes the conjecture, script, controls, and verdict is disqualified for promotion.

Wheeler proposed measuring residual over shifted compacts `K_M=K∪(K+1)∪...∪(K+M)`. Correction: raw residuals over `K_M` mix the candidate invariant with Gamma/Pochhammer growth and domain expansion, and smallness on `K` does not automatically propagate to `K+k`. The shift equation gives transformed polynomials `P_k=P∘T_k`, with changed `s`-degree and height.

Corrected live test:

`E_M(H) = min_P max_{0<=k<=M} || normalize_k((P∘T_k)(s,j^n Gamma(s))) ||_K`,

where `P` ranges over a fixed coefficient lattice `V(n,d,m,H)`, `T_k` is the explicit shift action on jets, and `normalize_k` divides out known shift-operator / height growth. Reports must include unnormalized residuals, normalized residuals, and height blowup of `P∘T_k`.

Controls: finite Euler rank-`N` at correct order should give exact zero for all `M`; generic entire-curve controls should follow generic multi-site interpolation / height growth; Gamma or `1/Gamma` is live only if the additive shift equation gives a stronger lower envelope after normalization.

## 2026-06-23 anti-theatre gate accepted by Haiku

Haiku accepted the Professor role statement and the orbit-normalized shift object, but explicitly paused RunPod work until Turing and Wheeler answer the same five-field anti-theatre gate. Until those answers are given, any residual/height table is classified as diagnostic only, not evidence for novelty/significance.

Accepted Professor role:
- Allowed question: prior-art / normal-form / hypothesis kill only.
- Forbidden judgment: no numerical success judgment, no computation tuning after results, no promotion.
- Artifact: reduction/kill memo with exact theorem candidate, hypotheses, source match, and boxed failed hypothesis.
- Gate: computation pre-registered by someone other than implementer, controls with opposite expected outcomes, kill condition reported first.
- Split: Wheeler structural prediction only; Turing coefficient-lattice implementation only; Haiku decomposition/gatekeeping only; Professor prior-art/reduction adversary only.

Status: no RunPod artifact may count as evidence until Turing and Wheeler provide matching role statements. This is now part of the theatre-test, not optional process.

## 2026-06-23 generic no-shift HT control and corrected Wheeler prediction

Turing and Wheeler supplied the five-field anti-theatre role statements. Turing is limited to coefficient-lattice implementation and raw tables; Wheeler is limited to one structural prediction. Professor accepts the split with one correction: Pochhammer/cocycle growth cannot be both normalized away and used as the residual signal.

Required generic no-shift control:
`R_omega(s)=sum_{j>=0} xi_j s^j/j!`, with `xi_j` sampled once from a continuous distribution using a recorded seed and evaluated as an infinite series with tail bounds. With probability one, `R_omega` satisfies no algebraic differential relation and no algebraic additive-shift relation over `Q(s)` because each candidate equation imposes a proper algebraic condition on the countable coefficient vector and there are countably many candidate equations over the fixed coefficient lattice. It is an order-`<=1` entire generic HT control with no built-in shift cocycle. It must not be truncated into a polynomial control.

Corrected Wheeler prediction:
After cocycle normalization, Gamma or `1/Gamma` has orbit-normalized arithmetic-height growth in `M` stronger than the generic no-shift entire HT control. If Gamma differs only before normalization, the measurement is a trivial cocycle-size effect and kills novelty. If it differs after normalization and survives the random no-shift control, the live target sharpens.

Compute gate for any RunPod artifact:
1. Turing receives blind target labels and emits raw tables only.
2. Wheeler cannot revise the metric after seeing data.
3. Generic no-shift HT control is included.
4. First reported line is the kill condition: whether Gamma matches generic no-shift after normalization.
5. Verdict/promotion remains outside the compute artifact.

## 2026-06-23 finite-compact value-probe no-go — known gatekeeper

Wheeler proposed a theorem-candidate explaining W1--W8: any finite-compact value measurement on an HT object can be matched by DA/D-finite approximants. Classification: true as a gatekeeper, not novel. No rate-rank or Hahn--Banach is needed. By Mergelyan/Runge approximation, holomorphic data on suitable compacts can be compact-uniformly approximated by polynomials or rational functions with poles off the compact; polynomials and rational functions are D-finite and DA. On finite samples, polynomial interpolation is exact.

Consequences for this card:
- Any probe based only on values, correlations, scaling, morphology, or residuals over a fixed finite compact is invalid as an HT discriminator.
- A viable HT probe must use a non-value-topological ingredient: coefficient height, exact functional/difference orbit, global singular lattice, or a normalized infinite-domain limit.
- This explains the W1--W8 collapse and motivates orbit-normalized arithmetic-height tests, but it does not prove the live target is novel.

Status: **KNOWN / GATEKEEPER**. Keep as protocol rule; do not promote as new knowledge.

## 2026-06-23 frozen diagnostic run spec v1

Haiku requested a fully pinned executable control spec before opening RunPod. Professor supplied diagnostic-only spec v1; it cannot promote a theorem.

- **Lattice:** `V(n,d,m)=Z[s,y_0,...,y_n]`, `deg_y<=d`, `deg_s<=m`, height `H=max |integer coeff|`.
- **Grid:** `n={0,1}`, `d={1,2,3}`, `m={0,1}`, `B=log10 H={2,4,6,8}`, `M={0,1,2,4}`, `dps=100`; candidate relations rerun on holdout at `dps=140`.
- **Train compact:** `Re={0.75,0.875,1.0,1.125,1.25}`, `Im={-0.35,-0.175,0,0.175,0.35}`.
- **Holdout compact:** `Re={0.8125,0.9375,1.0625,1.1875}`, `Im={-0.2625,-0.0875,0.0875,0.2625}`.
- **Orbit/multisite:** evaluate `s+k`, `0<=k<=M`, on the same base grids.
- **Blind targets:** `1/Gamma`; generic no-shift control `R_omega(s)=sum xi_j s^j/j!`; DA Euler control `1/(1-exp(-s))` with exact relation `y'-y+y^2=0`; optional rational bounded-residue DA toy `sum_{r=0}^8 1/(s+r+2)`.
- **Generic control law:** mathematical law `xi_j iid Uniform[-1,1]`; executable seed `hgt-generic-no-shift-v1-2026-06-23`, centers generated by SHA256(seed || ':' || j) mapped to `[-1,1]`, coefficient intervals radius `2^-80`. Use `|xi_j|<=1` and tail bound `tail_q(J,R)<=exp(R) R^(J+1-q)/(J+1-q)!` for `q<=1`, choosing `J` so tail `<1e-90`. The control is evaluated as an infinite series, not truncated into a polynomial.
- **Normalization reported, not selected post hoc:** raw residual; row-relative residual dividing by `max(1, ||monomial_row||_inf)`; for `1/Gamma`, cocycle-normalized residual using the explicit shift matrix `T_k` for `F(s+k)=F(s)/(s)_k`, including height blowup / operator norm used. Non-shift controls use row-relative comparator.
- **Artifact format:** Turing emits raw tables only: `blind_label,n,d,m,M,B,maxcoeff,res_train_raw,res_holdout_raw,res_train_rel,res_holdout_rel,res_train_cocycle,res_holdout_cocycle,relation_found,tail_bound,notes`. No verdict column.
- **First kill line:** kill shift-sharpening if blind `1/Gamma` matches generic no-shift after row/cocycle normalization, defined as same log-slope in `M` within `0.25` or residual ratios within one order of magnitude across most grid cells, while DA exact-zero control passes.

`LIVE` only if `1/Gamma` separates from generic no-shift after normalization and DA controls pass. `PROMOTE` is impossible from this run alone; a theorem or prior-art negative is still required.

## Promptability gate and boxed fake proof (2026-06-23)

Status: protocol / live theorem-shaping, not evidence.

Anti-theatre refinement: a role split is not sufficient. A team question is theatre if a single competent agent could answer it by being prompted harder. Before asking another agent or RunPod, run:

`Can I write the expected answer, the fake proof, and the likely kill reason myself right now?`

If yes, do not externalize the question as a computation or team vote. Box the proof gap instead.

For the current Gamma-height lane, the fake proof has the following shape:

1. Let `F=1/Gamma` and `P in Z[s,y_0,...,y_n]` of height `H`; set `G_P(s)=P(s,j^nF(s))`.
2. Pull additive shifts back by the exact cocycle `T_k`: `G_P(s+k)=G_{P∘T_k}(s)`, with explicit height/operator blowup from `(s)_k` and its jet derivatives.
3. Smallness on `K_M = union_{0<=k<=M}(K+k)` becomes many simultaneous smallness constraints for a family of pulled-back integer polynomials with controlled height.
4. A zero/Cartan/Nevanlinna or auxiliary-function inequality would need to force a lower bound on `H` in terms of `epsilon,M,n,d,m`.
5. **BOXED GAP:** an effective additive-shift arithmetic zero estimate whose constants improve on generic entire-curve estimates after cocycle normalization.

Kill routing:
- If known graph-transcendence / quantitative difference algebra / Mahler-method machinery supplies the boxed gap, kill as search.
- If the same proof applies to the frozen random no-shift control `R_omega`, kill as generic rather than shift-specific.
- If neither reduction applies, the residue is a theorem-shaped live target; diagnostics may tune constants but cannot promote it.

## Quotient-by-shift-ideal gate (2026-06-23)

Status: strengthened kill gate for the orbit-normalized Gamma-height lane.

A raw separation between `1/Gamma` and a generic no-shift control on an additive orbit is not enough. The first explanation is the known first-order difference equation

`F(s+1)=F(s)/s`, for `F=1/Gamma`.

Therefore any orbit-syzygy or residual signal must first be reduced modulo the exact shift ideal.

Formal host: use an orbit jet ring with variables `Y_{q,k}` representing `F^(q)(s+k)`. Let `I_shift` be the ideal generated by the differentiated cocycle relations obtained from

`F(s+k)=F(s)/(s)_k`.

Only the normal form of the approximation problem modulo `I_shift` can count as a candidate beyond-known signal. Any signal that appears before quotienting but disappears after reducing modulo `I_shift` is the already-known shift algebra, not hypertranscendence or new HGT knowledge.

Revised boxed inequality:

`After normal-form reduction modulo I_shift and with coefficient height tracked through that reduction, the orbit-normalized arithmetic approximation defect of 1/Gamma differs asymptotically from the generic no-shift control.`

Kill routes:

1. If the separation is present before quotienting but disappears modulo `I_shift`, kill as the known shift equation.
2. If the same post-quotient inequality holds for the frozen/random no-shift controls, kill as generic approximation geometry.
3. If existing quantitative difference algebra, Mahler-method, or graph-transcendence machinery supplies the post-quotient bound, kill as search.

Implication for computation: v1 finite-grid tables can validate code and calibrate constants only. They cannot serve as evidence unless the measured object is explicitly the post-quotient normal-form defect and the above kill routes have not already answered the question on paper.

## Full jet transport correction for `1/Gamma` orbit normalization (2026-06-23)

Status: implementation/theorem-shaping correction.

For `F=1/Gamma`, the shift equation is

`F(s+k)=F(s)/(s)_k`.

The normalization cannot mean scalar division by `(s)_k` alone. For jets, set `a_k(s)=1/(s)_k`. Then

`j^n F(s+k) = A_{k,n}(s) j^n F(s)`,

where `A_{k,n}` is the lower-triangular rational matrix whose entries are derivatives of `a_k(s)`. Its denominators are powers of `(s)_k`; clearing denominators creates degree and coefficient-height growth. The shift also sends `s` to `s+k`, so even for `n=0` the pulled-back constraint is `P(s+k,a_k(s)y_0)`, not the same constraint as `P(s,y_0)`.

Finite lattice object:

`tilde T_{k,n,d,m} P := D_{k,n,d}(s) * P(s+k, A_{k,n}(s)Y) in Z[s,Y]`,

where `D_{k,n,d}` is a common denominator sufficient for all monomials of jet-degree `<=d`. Reported normalization must include the height/operator blowup of the map `P -> tilde T_k P`. This is the concrete reduction modulo the exact shift ideal `I_shift` with height bookkeeping.

A table that only divides rows by the scalar `(s)_k` or by row norms does not test the post-quotient theorem for `n>=1`; it mostly measures unremoved jet-transport artifacts. A viable finite statement must be about the rank/height growth of the transformed lattice family `{tilde T_k V}_{0<=k<=M}` compared with a no-shift multisite lattice after denominator clearing and normalization.
