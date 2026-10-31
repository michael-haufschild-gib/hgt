# Arithmetic Coupling Theory (ACoT) programme

- **ID:** acot
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-3110/obstacles-summary.md §2.7 (also Q2, 2.5.2, 2.6.1, 2.6.2, A16)
- **Statement:** build arithmetic coupling theory: coupling calculus, stability, completeness,
  incidence identities, rigidity/noncrossing, F_q calibration.

## Goal
Answer the six §2.7 questions with unconditional Lean theorems; folder
`formal/GaloisForLFunctions/ArithmeticCouplingTheory/`, umbrella `ArithmeticCouplingTheory.lean`,
README foundational (no ledger).

## Gates
- [x] 0 → 1  README draft written
- [ ] Part A coupling calculus (Künneth, polarization, characters, antidiagonal)
- [ ] Part B stability (local HU const 3; density transfer; RH ⇔ bounded coupling; rate = width)
- [ ] Part C completeness (mixed differences see the same zeros; coupling form index = κ)
- [ ] Part D incidence (Mertens polarization identity; incidence packets; affine CRT energy)
- [ ] Part E rigidity → noncrossing
- [ ] Part F curve calibration (bounded curve coupling ⇔ unitary; golden fails)
- [ ] single two-prime lattice coupling (minimal S = {p,q})

## Approach (paper facts derived 2026-10-31)
- Antidiagonal: Hermitian K ⇒ C(u,u⁻¹) = 2(K(1) − Re K(u)). Two coprime two-prime lattices have dense
  logs ⇒ (x,−x) approximable ⇒ sup_{|x|≤L}|Re Φ(x) − Φ(0)| ≤ ½ sup_{box} |C|. Lossless, no Baker.
- Local HU (Skof-type) on T_L = {|x|,|y|,|x+y| ≤ L}: φ = ψ − (x/L)ψ(L); halving on [−L/2,L/2],
  shift by L on outer halves ⇒ S ≤ S/2 + 3M/2 ⇒ |φ| ≤ 3M.
- Rate: use triangle box so both directions have the same height ⇒ coupling rate = zero width.
- Mixed difference f' = (T_u−1)(T_v−1)f: FT multiplier (e^{iuγ}−1)(e^{ivγ}−1) ≠ 0 at non-real γ ⇒
  seenRightZeros f' = seenRightZeros f ⇒ orientation index law gives index κ.
- Mertens polarization: P_N(F) = Σ_{n≤N} F(n)²/n (ψ₁(N/n) + log n) − J_N(F), ψ₁(x)=Σ_{k≤x}Λ(k)/k,
  since Σ_k Λ(k)/k Σ_{kn≤N} F(kn)²/n = Σ_m F(m)² log m / m (Σ_{k|m}Λ = log).
- Incidence jumps: F_b(p^j n) − F_b(n) = b_p [p∤n]; non-prime-power k contribute 0 (Λ = 0).
- Curve: K(n) = Σ β_j^n, C(a,b) = Σ(β^a−1)(β^b−1); antidiagonal (a,−a) exact ⇒ bounded ⇔ |β|=1.

## Log
- 2026-10-31 — created; README draft.
