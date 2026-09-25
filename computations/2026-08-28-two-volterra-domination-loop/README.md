# Two-Volterra domination loop — numerical batteries (2026-08-28)

Companion computations for the cards `1-in-progress/source-contraction-two-volterra-domination.md`
and `1-in-progress/theta-krein-pick-congruence.md` (cycle log there; Serena memory
`research/two_volterra_domination_loop_2026_08_28`). mpmath on the 128-core pod; all quantities
are the literal corpus objects (xiCent = xi(1/2+·), tilt channels, Bezoutian form).

- `loop1.py` — cycle-1 falsification battery. Results (recorded on the cards): even+positive+
  strictly-log-concave kernel with explicit rank-3 negative packet (C1 killed); FE-symmetrized
  single atom has an off-axis zero pair (C2′ killed); causal and even-symmetrized truncations
  indefinite for all N ≤ 10 (no truncation ladder).
- `loop2.py` / `loop2b.py` (+ `loop2b.json`) — cycle-5 Laguerre/slice battery at dps 60:
  L₁ = Ξ′²−ΞΞ″ and L₂ = ΞΞ⁗−4Ξ′Ξ‴+3Ξ″² have ZERO violations on τ ∈ [0.2, 120] (normalized
  minima 0.044 at τ=0.2 and 0.082 at τ=12.65); pointwise-normalized L₁ shows NO dip at the
  classical Lehmer pair window τ ∈ [7004.9, 7005.2] (min 0.365 vs 0.378 baseline) — the
  close-pair failure mode is invisible to pointwise wall jets. dps-30 4th-derivative stencils
  produce spurious L₂ negatives (h⁴ precision loss) — always use dps ≥ 60 with the 7-point
  stencils in `loop2b.py`.
- `loop2c.py` — verification of the exact wall-normal expansion
  `Re(ξc′·conj ξc)(ε+iτ) = ε·L₁(τ) + ε³·L₂(τ)/6 + O(ε⁵)`
  (residuals scale as ε⁴ to 3 significant figures across ε ∈ {0.02, 0.05, 0.1}); equivalently
  `1−|λ_c(ε+iτ)|² = (4c/|tilt₊(iτ)|²)(εL₁ + ε³L₂/6 + O(ε⁵))`: the contraction jets of the
  two-Volterra channels at the lossless wall are the classical Laguerre hierarchy. Slice
  contraction (`u > 0`) held at every sampled point, consistent with the Sondow–Dumitrescu/
  Jensen receiver (corpus: `strictMonoOn_norm_XiC_horizontal_of_halfPlaneBound`).
