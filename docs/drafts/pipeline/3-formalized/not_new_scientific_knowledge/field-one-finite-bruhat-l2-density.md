# Density of finite-adele Bruhat--Schwartz functions in Haar L²

- **ID:** `field-one-finite-bruhat-l2-density`
- **Stage:** 3-formalized
- **Type:** ANALYTIC THEOREM (Lean)
- **Labels:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `field-one-finite-adele-compact-open-basis`
- **Statement:** compactly supported locally constant complex functions on
  rational finite adeles have dense image in additive Haar \(L^2\).

## Theorem

For measurable \(s\subseteq\mathbb A_f\) of finite Haar measure and
\(\varepsilon>0\), Haar regularity supplies compact \(K\subseteq s\) and
open \(U\supseteq s\), each with measure defect below
\(\varepsilon/2\).  Compact-open interpolation gives
\(K\subseteq C\subseteq U\), hence
\[
  \mu(C\mathbin{\triangle}s)<\varepsilon.
\]
The function \(c\,1_C\) is locally constant and compactly supported, so it
is a Bruhat--Schwartz function.  The exact \(L^2\) indicator-distance
identity then approximates \(c\,1_s\) by such vectors.  Standard
\(L^p\)-induction from finite-measure indicators proves
\[
 \overline{\operatorname{im}
   (\mathcal S(\mathbb A_f)\longrightarrow L^2(\mathbb A_f,\mu_f))}
 =L^2(\mathbb A_f,\mu_f).
\]

This closes finite-place density only.  It does not identify independently
completed tensor products, prove separated-product density on
\(\mathbb R\times\mathbb A_f\), construct a global sheaf/cohomology theory,
or imply RH.

## Lean certificate

- **Module:** `GaloisForLFunctions.RHTower.FieldOneFiniteBruhatL2Density`
- **Core theorems:**
  `fieldOneFiniteAdele_exists_compactOpen_symmDiff_lt`,
  `fieldOneFiniteAdeleCompactOpenBruhatToL2_eq_indicator`,
  `fieldOneFiniteAdele_indicatorConstLp_mem_bruhatClosure`,
  `fieldOneFiniteBruhatToL2Linear_denseRange`
- **Audit:** direct cached `lake env lean` passed. Scratch `#print axioms`
  reports only `propext`, `Classical.choice`, and `Quot.sound`. Final
  targeted `lake build` remains reserved for final audit.

## Gates

- [x] 0 → 1: compact-open symmetric-difference approximation
- [x] 1 → 2: indicator realization and `Lp.induction` density proof
- [x] 2 → 3: unconditional direct Lean check and axiom audit
- [ ] 3 → 4: publication-ready integration
