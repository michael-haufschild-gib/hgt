# De Branges sampling of the pre-contact Weil spaces

- **ID:** precontact-de-branges-sampling-mimic
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-0511 §2.1, A49.
- **Statement:** Let `H_a` be the exact Weil Hilbert space below the onset, `E` its Hermite–Biehler function, and
  `S_φ = φE^# − E`. Then `S_φ ∈ H_a` for at most one unimodular `φ`, and for every other `φ` the normalized kernels at the
  real zeros of `S_φ` form a Hilbert basis, so `‖x‖² = Σ_{S_φ(t)=0} |F_x(t)|²/K(t,t)`. Placed on the critical line, the atoms
  `1/K(t,t)` have finite Lorentzian mass and reproduce the zeta image on every smooth window below the onset. They obey
  `Σ_{t∈[x,y]} 1/K(t,t) ≤ [θ(y−x)/(2π) + A] log(T/2π)` near `T`, with `A`, `T₀` independent of `φ`. Conversely a positive
  on-line mimic on an aperture forces positivity of the window.
- **Lean:** `GaloisForLFunctions/CanonicalSystemOfTheWindowTower/AUnitaryWithCompactDefectHasCompleteEigenvectors.lean`,
  `ThePrecontactWeilSpacesHaveSamplingBases.lean`, `TheSamplingAtomsArePositiveMimicsOfZeta.lean`; standard axioms only.

## Proof

1. **Boundary unitaries.** Zero-moving `ker eval_i → ker eval_{−i}` extends by `v_i/‖v_i‖ ↦ φ v_{−i}/‖v_{−i}‖` to a unitary `V_φ`
   with `(z−i)F_{V_φ x} = (z+i)F_x + c(x)S_φ`.
2. **Compact defect.** `V_φ − 1` is rank one plus `T`, where `(z−i)F_{Tx} = 2iF_{Px}` and `P` projects onto `ker eval_i`.
   In the form norm, `∫ω|F_{Tx}|² ≤ sup(ω/|ξ−i|²)·4∫|F_{Px}|²`, since `ω` grows logarithmically. So `T` is dominated by the
   compact embedding of the form domain into `L²`.
3. **Spectral theorem.** `V + V⁻¹ − 2` and `i(V − V⁻¹)` are commuting compact self-adjoint operators, so they have a common
   eigenvector in every nonzero closed reducing subspace. Hence `V_φ` has complete eigenvectors.
4. **`E ∉ H_a`.** If `F_y = E`, then `y ∈ ker eval_{−i}` and `b = U⁻¹y` has `F_b = (z−i)K(i,·)`. So `y = b + 2iv_i` with `b ⊥ v_i`,
   and `‖y‖² = ‖b‖² + 4‖v_i‖²`, contradicting `‖y‖ = ‖b‖`. Since `φ₂S_{φ₁} − φ₁S_{φ₂} = (φ₁−φ₂)E`, at most one `S_φ` lies in `H_a`.
5. **Eigenvectors are kernels.** `V_φx = μx` gives `(μ−1)(z−t)F_x = c(x)S_φ` with real `t = i(μ+1)/(μ−1)`. The case `μ = 1` is
   excluded by step 4, and `c(x) = 0` forces `x = 0`. Christoffel–Darboux at `t` gives `conj E(t)·S_φ(z) = 2i‖v_i‖²(z−t)K(t,z)`, so
   `x ∝ v_t`. The same formula gives `K(t,t') = 0` for distinct zeros.
6. **Lorentzian mass.** `u = e^{−s}1_{[0,b]}` lies in the form domain, because `ω|û|² = O((1+|ξ|)^{−3/2})`. Its transform satisfies
   `|F_u(t)|² ≥ (1−e^{−b})²/(1+t²)` on all of `ℝ`, so Parseval for `u` bounds `Σ 1/(K(t,t)(1+t²))`.
7. **Mimic.** On smooth windows `‖x_f‖² = W(f,f)` and `F_{x_f} = paperFT f`, so the sampling formula is the mimic identity. The count
   is `zeta_positive_mimic_weighted_count_of_smooth`, whose hypothesis was weakened to smooth windows.
