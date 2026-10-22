# Route MC through the Weil cone: formal spectral theory and the three remaining open statements

- **Stage:** 1-in-progress (synthesis card, 2026-10-01, MC loop cycles 195–225)
- **Type:** MAP. It records where route MC stands after the cone's spectral theory became formal.

## Reduction
- Route MC asks for half-power Möbius cancellation for μ. On the cone:
  - every full-cone producer `lam ∈ W` has half-power Möbius cancellation for its own Möbius function (MUST-649);
  - by the corpus, `Λ ∈ W ⟺ RH`.
- So MC for μ is exactly the statement `Λ ∈ W`. The Möbius side adds no condition (cycle 211). MC ⟺ W-membership holds only because of Λ's reflection structure (cycle 215, countermodel `lam = 0`).

## What is formal for every producer (standard axioms)
| Object | Result | MUST |
|---|---|---|
| Herglotz bridge | `Re Φ_lam ≥ 0` on `Re s > ½`; boundary measure `μ_lam`; Poisson representation | 639, 640 |
| Deviation | `D_{lam−Λ}` has residue `ord ξ` at every point of `Re s > ½` | 650 |
| Deficit law | `liminf (2N_off⁺+R⁺)/T ≥ sup\|w(n)\|/(4πn)` | 643, 645 |
| Growth | Lindelöf for `F_lam` and `1/F_lam` on `Re s ≥ ½+δ`; horizontal modulus law | 646, 647 |
| Local mass | `μ_lam([t−1,t+1]) ≤ C log(\|t\|+3)` | 648 |
| PNT | exact `O(√x)` smoothed error, constant `W_lam(f⋆f̃)` | 652 |
| Wiener | mean square of the PNT error → `Σ\|f̂(a)\|⁴μ_lam{a}²` | 654 |
| Bohr spectrum | the frequency-`a` mean of the PNT error → `−\|f̂(a)\|²μ_lam{a}` | 658 |
| Counting | Poisson-smoothed `μ_lam`-count = ζ zero count + `O(1)` (exact identity) | 656 |
| Rigidity | `Λ ∈ W` and `o(√x)` Cesàro window deviation ⇒ `lam = Λ`; `μ_Λ{a} = ord_{½+ia}ξ` | 655 |
| Representation | `W_lam(f⋆g̃) = ∫f̂·conj(ĝ)dμ_lam` | 658 |

## The three open statements (each walled; see the loop card rows)
1. **Existence (PBAP).** Is `W ≠ ∅` unconditionally?
   - Every construction below `ε = ½` needs Euler-product information (216; HF L261/L262).
   - The continuity method is circular at a positive threshold (217).
   - Survivor: `ε* ≤ Θ − ½`.
2. **Uniqueness (Step A).** `∫\|F_lam(½+it)\|²w ≤ (R²+o(1))∫w log t` for every producer.
   - Equivalently (L228, MUST-603), mean-square excess `o(T)`.
   - Formal object: the modulus law (MUST-647) with damping `exp(−∫log(1+η²/x²)dμ)`.
   - Variational form: ζ's measure maximizes the weighted damping (210, ζ value `c/sinh c`).
3. **Detection (PBAP ⇒ RH).**
   - Needs pointwise recurrence of a non-absolutely-convergent Dirichlet series below its abscissa (214, Bagchi wall).
   - The deviation must carry every off-line zero (MUST-650).

## Discipline for the next cycles
- Fixed-abscissa growth laws cannot see uniqueness (205). Work at `σ − ½ ≍ 1/log T`.
- Mean-square arguments are sign-blind (MC walls). Atom information is the only integrality handle: Wiener (654), Bohr (658), window rigidity (655).
- Do not re-propose: deficit-law reformulations, MC ⇒ W converses, random or weighted Euler products for `PBAP_ε`, or continuity-method openness.
