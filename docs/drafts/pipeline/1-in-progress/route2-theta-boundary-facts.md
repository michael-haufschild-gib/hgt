# Route 2 fact log (theta renewal loop at the natural boundary)

Facts and no-gos only. [P] paper, [L] Lean, [X] refuted.

- F1 [P] 1+K(λ)=Ξ(2iλ)/((a−λ)D(−λ)); D(−λ) zero-free on Re λ≤a. Step 2's stop test is met by using Ξ linearly; the boundary representation is rational-cusp card eq. (8). Step 2 is a rotation of Riemann's integral, not new content.
- F2 [P] K(iy) is unimodular; |K|−1 ≈ 2Re(η+S)=∫_ℝ W(t)sinh(xt)cos(yt)dt (W odd, W(t)sinh(xt) even analytic on |Im t|<π/2). HB (|K|>1 off-axis) would give RH but the ledger's infinite Pick index kills it.
- F3 [P] R₂ ⟺ a_{2m}=a_m; H_p ⟺ a_{pm}=a_m; all p ⟺ a constant.
- F4 [P] R₂ is Mellin-diagonal: 𝓜[Q(·+1)]=−(1−2^{1−s})𝓜[Q]. No zero count can depend on it. Route 2 claim (ii) [X] as mechanism.
- F5 [P] One-sided gauge k+b·k(·+log p), p odd, keeps R₂, has strip off-line zeros, breaks FE.
- F6 [P] R₂ + θ-inversion + 2-periodicity ⟹ F(1+iε)=O(ε^{−1/2}e^{−π/4ε}): exact cancellation 2=4^{1/2}. R₂ = zero-charge cusp regularity; with weak holomorphy ⟹ F=cθ.
- F7 [P] V=θ·ℝ[h], h=λ(1−λ): FE, integer spectrum, same source strip, real; prescribed off-line strip zeros. FE+integer spectrum+source analyticity do not force RH.
- F8 [P] Fixed points of r↦4r mod 2 are the cusps with q∈{1,3}; local series ζ and ζ·(ω̄+(1−ω̄)3^{−s}); the extra factor's zeros are on Re s=½ ⟺ |G|²=q.
- F9 [L] `thetaGroupDeformation_offLine_strip_zero`: θ₃(1+t₁h+t₂h²) — two-periodic, exact θ-inversion, even source, transform XiC+t₁Ξ₁+t₂Ξ₂ — vanishes at some 0<Im z₀<½ for real t. FE + integer spectrum + source strip ⇏ RH.
- F10 [L] `norm_cusp_one_le_of_primeTwo`: R₂ + inversion ⟹ ‖F(1+i/y)‖ ≤ 2M√y e^{−πy/4}; `thetaGroupDeformation_primeTwo_iff`: R₂ ⟺ t₁=t₂=0. R₂ is exactly the zero-charge-cusp regularity separating ξ from the family.
- F11 [P] Consequence: route 2's arithmetic input (FE+R₂) is complete but rigid (a single point); the only separating datum from FE-countermodels is cusp-1 regularity, which in Mellin terms is η=(1−2^{1−s})ζ entire — again diagonal. No non-diagonal mechanism exists in the route as proposed.
- F12 [P] Q_s=Σk^{−s}e^{−iπk²r} is a common eigenvector of the transfer operators of r↦n²r (eigenvalue n^{−s}); the common eigenvectors are exactly Σχ(k)k^{−s}e_{k²}, χ completely multiplicative (Helson family, off-line zeros possible). ζ(s)=finite part of Q_s at the fixed point 0. No mechanism.
- F13 [X] Route 2 mechanism closed from both sides: r-space (other session, 5X/theta-dyadic-boundary-winding-rigidity) and s-space/modular (3F/route2-prime-two-cusp-rigidity). Open core = a non-Mellin-diagonal index map; none known.
- F14 [L] Cusp-charge law: Ξ₁ = transform of θ₃h has (Ξ₁ u).re < 0 and ‖Ξ(u)‖ ≤ C u^{−1/4}‖Ξ₁(u)‖ for u ≥ U (`cuspCharge_law`). Mechanism: exact saddle on Im x = −β at the pole cusp 1; far field capped at R₀/3 by the Farey reduction.
- F15 [L] ξ is critical in the positive exactly-Γ_θ-modular weight-½ class: ∀ε ∃0<s<ε, source of θ₃(1+sh) real and >0 on ℝ, transform Ξ+sΞ₁ vanishes at 0<Im z<½ (`thetaGroup_modular_criticality`). Kernel positivity + exact modularity + evenness + integer spectrum do not confine zeros even infinitesimally.
- F16 [P] Consequence for steps 2–3: any winding/zero-count invariant on this class that detects RH is discontinuous at ξ along the charge direction; the only datum separating ξ from its critical neighbours is zero charge at cusp 1 (F10), which is Mellin-diagonal (F4).
- F17 [L] Hardy rigidity on the charge line: ∀s≠0, Ξ+sΞ₁ has finitely many real and infinitely many nonreal zeros; s=0 has infinitely many real zeros (`chargeLine_hardy_rigidity`, `XiC_real_zeroSet_infinite`). On the line: infinitely many real zeros ⟺ s=0 ⟺ R₂.
- F18 [L] Hardy characterization: for P ∈ ℝ[X]∖0, the transform of θ₃P(h) has infinitely many real zeros ⟺ deg P = 0 (`formXi_real_zeros_infinite_iff`); deg P ≥ 1 ⇒ finitely many real, infinitely many nonreal zeros. Within the full space of real weakly holomorphic weight-½ Γ_θ forms regular at ∞, Hardy's theorem singles out ξ.
- F19 [L] Route step 4 (level specificity): for every complex L ≠ 0, Ξ = L has finitely many real and infinitely many nonreal solutions (`XiC_level_specificity`; generic `levelSet_infinite_of_growth_decay`). Affine form: for (P,L) ≠ (0,0), transform of θ₃P(h) equals L at infinitely many real points ⟺ L = 0 and deg P = 0 (`formXi_level_real_infinite_iff`). Hardy's property picks out cΞ in θ₃·ℝ[h] ⊕ ℂ; any route-2 counting argument must use the level 0 and the cusp-1 regularity of ξ, i.e. RH-specific data.
