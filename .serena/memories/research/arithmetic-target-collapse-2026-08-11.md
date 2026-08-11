# Collapse principle + exact arithmetic open core (step 29)

`RHTower/XiResolventArithmeticTarget.lean` — 6 theorems, [propext, Classical.choice, Quot.sound].

## Resolution of "find an arithmetic bound M(X) = o(X⁻⁴)"
It is a THEOREM that no such bound exists short of RH: `riemannHypothesis_of_mass_eventually_le`
(collapse principle) — any g with M ≤ g eventually and (X+1)⁴g → 0 implies RH (then M ≡ 0). The
assignment's solution space = proofs of RH. Quartic rigidity closes the estimate route formally.

## The exact open core (sharpest frontier statement of the program)
- `tsum_norm_sq_xiResolventPoint_eq` : Σ'‖u_q‖² = Re R₁(X) + 2M(X)  (termwise Pythagoras).
- `moment_one_re_le_tsum_norm_sq` : Re R₁ ≤ Σ'‖u‖² unconditionally (one side free).
- `riemannHypothesis_iff_tsum_norm_sq_eq_moment_one_re` : **RH ⟺ Σ'‖u_q‖² = Re R₁(X)** —
  geometry (ℓ²/GNS side) = arithmetic (second moment) at any one shift.
- `hasDerivAt_xiResolventMoment_zero` : R₁ = −dR₀/dX; R₀(x²) = logDeriv ξ(1/2+x)/x (corpus).
- `riemannHypothesis_of_tsum_norm_sq_eventually_le` : Σ'‖u‖² ≤ Re R₁ + g, (X+1)⁴g → 0 ⇒ RH.

## Wall analysis (why each arithmetic route fails, quantitatively)
1. PNTPlus zero-free region: improves constants only; the X-exponent is termwise.
2. Any b-decay hypothesis (even |b| ≤ C/γ^{1+δ} for all zeros): X⁴M → Σ4(γb)² finite, not 0.
   o(X⁻⁴) ⟺ charge = 0 ⟺ RH exactly.
3. σ-blindness: reindexing by the line-conjugation involution turns every twisted double sum
   Σ_{q,r}f(A_q+Ā_r) into the plain one; e.g. (1/2π)∫|φ(X+it)|²dt = Σ_{q,r}1/(A_q+Ā_r+2X) =
   plain double sum. The ℓ²-mass is σ-DIAGONAL; no bilinear arithmetic observable reaches it.
4. Diagonal extraction = Bohr mean of F_X(t) = Σu_q e^{iγ_q t} (4M = mean|F|² − 4R₁ modulo
   ordinate collisions); Landau's formula makes it arithmetic-adjacent; unconditional errors =
   pair-correlation wall (Route E correlations wall).
5. Herglotz/Stieltjes reformulation of φ = Lagarias ξ'/ξ positivity criterion [REDISCOVERED].

## Remaining live mechanisms for the diagonal
(i) ordinate-separation through the pair-correlation wall; (ii) operator/GNS realization
computing Σ'‖u‖² (standing socket, Deninger/Hedenmalm/Burnol lanes). See card steps 27–29.
