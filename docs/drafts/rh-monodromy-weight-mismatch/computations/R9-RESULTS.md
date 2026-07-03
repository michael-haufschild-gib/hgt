# R9 — mirror-identity verification (2026-07-03) — [MEASURED, 30 digits]

Pre-registered in 16-pinning-and-emission.md §3 (predictions P0–P2); scripts
`mirror_test.py`, `mirror_diag.py` (pod, python3.13 + mpmath, dps 30). Family
f_k = (1−ik)/2·L(s,χ) + (1+ik)/2·L(s,χ̄), χ mod 5 with χ(2) = i, L via Hurwitz zeta.

- **P0 PASS (and κ closed form VERIFIED):** with κ = (√(10−2√5) − 2)/(√5 − 1)
  = 0.284079043840412296…, the banked certified zero ρ = 0.808517182456637386
  + 85.6993484853775922i satisfies |f_κ(ρ)| = 3.5e-17. The closed form (removed
  from doc 14 as unverified recall) is now measurement-backed.
- **P2 initial run FAILED — root-finder artifact, not the identity:** Muller from the
  predicted mirror seed (0.1765…, 85.7059…) at k' converged to f_{k'}'s OTHER zero
  near that height (0.7943…, 85.6929…), the smoothly-continued trajectory zero.
- **Mirror identity CONFIRMED (diagnostic, exact-algebra route):** the pencil is
  LINEAR in (c,d), so the unique member vanishing at any point s₀ is computable in
  closed form: r(s₀) = −L(s₀,χ̄)/L(s₀,χ). At both reflected candidates 1−ρ(k₁) and
  1−conj ρ(k₁) (k₁ = κ+0.03): |r| = 1 to 3e-29 and the corresponding k equals the
  Möbius prediction k' = tan(2·arctan κ − arctan k₁) = 0.25454485509721718687550805096
  with imaginary part 8.5e-30. Root numbers measured: ε(χ) = 0.8506508083520399…
  + 0.5257311121191336…i, |ε| = 1 to 1e-30; ε(χ̄) = conj ε(χ) at these points.
- **Trajectory data (new):** box-84 zero moves SMOOTHLY: β(κ) = 0.80852,
  β(κ+0.03) = 0.82354, β(κ−0.05) = 0.78479 — measured velocity dβ/dk ≈ 0.50, no
  mirror kink (correct: trajectory identity applies only to zeros passing through
  on-line simple points; pre-existing off-line zeros carry SEPARATE mirror partners
  in the left half-strip).
- **New object (opened): the INCIDENCE MAP** r(s) := −L(s,χ̄)/L(s,χ), meromorphic;
  the entire pencil's zero dynamics is its level-set geometry (zeros of f_k = level
  curve r(s) = r(k); k-circle = |r| = 1 fiber system; FE fiber and mirror involution
  = symmetries of r). The measured R3/R5 defect dynamics is the value distribution
  of ONE meromorphic function.
