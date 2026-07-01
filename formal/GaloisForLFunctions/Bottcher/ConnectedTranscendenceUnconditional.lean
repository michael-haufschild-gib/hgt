/-
# GAP 4 CLOSED — unconditional connected-case transcendence for `c ∈ mandelbrot ∖ {0, -2}`

The final assembly. A polynomial relation `P(z, φ_c(z)) = 0` on `U ⊆ escapeOpen c`:
1. propagates to the branch `β` on the whole preconnected basin (identity theorem,
   `eval₂_relation_propagate` + `isPreconnected_compl_filledJulia`);
2. substitutes `z = ψ(w)` (`BasinGlobalInverse`): `P(ψ(w), w) = 0` on the exterior;
3. **swaps variables** (`swapPoly` / `swap_eval₂`): with `t = 1/w`, `ψ(1/t) = h(t)/t`, clearing
   `t^{J+K}` produces a polynomial relation `R(t, h(t)) = 0` for the full-disk model `h` on the
   punctured ball, extended over `0` by the identity theorem; `R ≠ 0` forces `P ≠ 0` to fail
   backwards (a vanishing swap kills every coefficient of `P`), and `natDegree R = 0` dies on the
   infinite ball — so `R` is a genuine relation;
4. contradicts `h_no_relation` (the disk model is transcendental over `ℂ(t)`, powered by the proven
   natural boundary).

The exclusions are exact: `φ₀(z) = z` and `φ₋₂` (Chebyshev/Zhukovsky) are genuinely algebraic.
-/
import GaloisForLFunctions.Bottcher.DiskModelNoRelation
import GaloisForLFunctions.Bottcher.DiskModelGlobal
import GaloisForLFunctions.Bottcher.BasinConnected
import GaloisForLFunctions.Bottcher.TranscendenceReduction
open Polynomial Filter Topology Metric Complex Set
namespace Bottcher
noncomputable section

/-- The variable swap: `P ∈ ℂ[z][Y]` (coefficients in `z`, variable `Y ↦ φ`) becomes
`R ∈ ℂ[t][Y']` (coefficients in `t = 1/w`, variable `Y' ↦ h`), via
`z = h(t)/t`, `φ = w = 1/t`, cleared by `t^{J+K}`. -/
def swapPoly (P : (Polynomial ℂ)[X]) (J K : ℕ) : (Polynomial ℂ)[X] :=
  ∑ i ∈ P.support, ∑ k ∈ (P.coeff i).support,
    Polynomial.C (Polynomial.C ((P.coeff i).coeff k) * Polynomial.X ^ (J - i + (K - k))) *
      Polynomial.X ^ k

theorem swap_eval₂ (P : (Polynomial ℂ)[X]) {J K : ℕ} (hJ : P.natDegree ≤ J)
    (hK : ∀ i, (P.coeff i).natDegree ≤ K)
    {t : ℂ} (ht : t ≠ 0) (y : ℂ) :
    (swapPoly P J K).eval₂ (evalRingHom t) y
      = t ^ (J + K) * P.eval₂ (evalRingHom (y / t)) (1 / t) := by
  rw [swapPoly, eval₂_finsetSum]
  rw [show P.eval₂ (evalRingHom (y / t)) (1 / t)
      = ∑ i ∈ P.support, (P.coeff i).eval (y / t) * (1 / t) ^ i from by
    rw [eval₂_eq_sum, Polynomial.sum_def]; rfl]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [eval₂_finsetSum]
  rw [show (P.coeff i).eval (y / t) = ∑ k ∈ (P.coeff i).support,
      ((P.coeff i).coeff k) * (y / t) ^ k from by
    rw [eval_eq_sum, Polynomial.sum_def]]
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [eval₂_mul, eval₂_C, eval₂_X_pow]
  simp only [coe_evalRingHom, eval_mul, eval_C, eval_pow, eval_X]
  have hiJ : i ≤ J := le_trans (le_natDegree_of_ne_zero (mem_support_iff.mp hi)) hJ
  have hkK : k ≤ K := le_trans (le_natDegree_of_ne_zero (mem_support_iff.mp hk)) (hK i)
  have hpow : t ^ (J + K) = t ^ (J - i + (K - k)) * (t ^ i * t ^ k) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [hpow, div_pow, div_pow, one_pow]
  have htk : (t:ℂ) ^ k ≠ 0 := pow_ne_zero _ ht
  have hti : (t:ℂ) ^ i ≠ 0 := pow_ne_zero _ ht
  field_simp

/-- **No polynomial relation for the Böttcher coordinate** on any nonempty open `U ⊆ escapeOpen c`,
for `c ∈ mandelbrot ∖ {0,-2}`: propagate to the basin, invert to the exterior, swap to the disk
model, and hit the natural boundary. -/
theorem no_phi_relation_of_mem_mandelbrot {c : ℂ} (hcM : c ∈ mandelbrot)
    (hc0 : c ≠ 0) (hc2 : c ≠ -2) {U : Set ℂ}
    (hUo : IsOpen U) (hUne : U.Nonempty) (hU : U ⊆ escapeOpen c)
    (P : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0)
    (hrel : Set.EqOn (fun z => P.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z)) 0 U) :
    False := by
  obtain ⟨h, β, ψ, hhd, hhe, hfe, hh0, hbridge, hβan, hβesc, hψan, hψmem, hβψ, hψβ⟩ :=
    exists_full_disk_model_of_mem_mandelbrot c hcM
  obtain ⟨z₀, hz₀U⟩ := hUne
  have hz₀basin : z₀ ∈ (filledJulia c)ᶜ := escapeOpen_subset_compl_filledJulia c (hU hz₀U)
  have hloc : ∀ᶠ z in 𝓝 z₀, P.eval₂ (Polynomial.evalRingHom z) (β z) = 0 := by
    filter_upwards [hUo.mem_nhds hz₀U] with z hzU
    rw [hβesc z (hU hzU)]
    exact hrel hzU
  have hbasinrel := eval₂_relation_propagate (isPreconnected_compl_filledJulia c) hβan P
    hz₀basin hloc
  have hpsirel : ∀ w : ℂ, 1 < ‖w‖ → P.eval₂ (Polynomial.evalRingHom (ψ w)) w = 0 := by
    intro w hw
    have h1 := hbasinrel (hψmem w hw)
    simp only [Pi.zero_apply] at h1
    rw [hβψ w hw] at h1
    exact h1
  set J := P.natDegree with hJdef
  set K := P.support.sup (fun i => (P.coeff i).natDegree) with hKdef
  have hK : ∀ i, (P.coeff i).natDegree ≤ K := by
    intro i
    by_cases hi : i ∈ P.support
    · exact Finset.le_sup (f := fun j => (P.coeff j).natDegree) hi
    · rw [Polynomial.notMem_support_iff.mp hi]; simp
  set R := swapPoly P J K with hRdef
  have hRrel' : ∀ t : ℂ, t ≠ 0 → t ∈ ball (0:ℂ) 1 →
      R.eval₂ (Polynomial.evalRingHom t) (h t) = 0 := by
    intro t ht0 htb
    have ht1 : ‖t‖ < 1 := mem_ball_zero_iff.mp htb
    have htn : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    have hw : 1 < ‖(1:ℂ)/t‖ := by
      rw [one_div, norm_inv]
      exact (lt_inv_comm₀ one_pos htn).mpr (by simpa using ht1)
    rw [hRdef, swap_eval₂ P le_rfl hK ht0 (h t)]
    have hht : h t / t = ψ (1 / t) := by
      rw [hbridge t ht0 ht1]
      field_simp
    rw [hht, hpsirel (1/t) hw, mul_zero]
  -- extend across 0 by the identity theorem on the ball
  have hhalf : (1/2 : ℂ) ∈ ball (0:ℂ) 1 := by rw [mem_ball_zero_iff]; norm_num
  have hlochalf : ∀ᶠ t in 𝓝 (1/2 : ℂ), R.eval₂ (Polynomial.evalRingHom t) (h t) = 0 := by
    have hball : ball (1/2 : ℂ) (1/4) ∈ 𝓝 (1/2 : ℂ) :=
      isOpen_ball.mem_nhds (mem_ball_self (by norm_num))
    filter_upwards [hball] with t ht
    have hd : ‖t - 1/2‖ < 1/4 := by rw [← dist_eq_norm]; exact mem_ball.mp ht
    have hn2 : ‖(1/2 : ℂ)‖ = 1/2 := by norm_num
    have hup : ‖t‖ < 1 := by
      have h1 : ‖t‖ ≤ ‖(1/2 : ℂ)‖ + ‖t - 1/2‖ := by
        calc ‖t‖ = ‖(1/2 : ℂ) + (t - 1/2)‖ := by ring_nf
          _ ≤ ‖(1/2 : ℂ)‖ + ‖t - 1/2‖ := norm_add_le _ _
      rw [hn2] at h1
      linarith
    have hlow : t ≠ 0 := by
      intro hcon
      rw [hcon] at hd
      simp only [zero_sub, norm_neg] at hd
      rw [hn2] at hd
      norm_num at hd
    exact hRrel' t hlow (mem_ball_zero_iff.mpr hup)
  have hRrel : ∀ t ∈ ball (0:ℂ) 1, R.eval₂ (Polynomial.evalRingHom t) (h t) = 0 := by
    have hEq := eval₂_relation_propagate (convex_ball (0:ℂ) 1).isPreconnected
      (hhd.analyticOnNhd isOpen_ball) R hhalf hlochalf
    intro t ht
    exact hEq ht
  -- R ≠ 0
  have hR0 : R ≠ 0 := by
    intro hR0'
    apply hP0
    have hzero : ∀ (z t : ℂ), t ≠ 0 → P.eval₂ (Polynomial.evalRingHom z) (1/t) = 0 := by
      intro z t ht0
      have hkey := swap_eval₂ P le_rfl hK ht0 (z * t)
      rw [← hRdef, hR0', Polynomial.eval₂_zero] at hkey
      have hzt : z * t / t = z := mul_div_cancel_right₀ z ht0
      rw [hzt] at hkey
      have hpow : (t : ℂ) ^ (J + K) ≠ 0 := pow_ne_zero _ ht0
      exact (mul_eq_zero.mp hkey.symm).resolve_left hpow
    have hfib : ∀ z : ℂ, P.map (Polynomial.evalRingHom z) = 0 := by
      intro z
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply Set.Infinite.mono (s := {x : ℂ | x ≠ 0})
      · intro x hx
        have hx0 : (x : ℂ) ≠ 0 := hx
        have := hzero z x⁻¹ (inv_ne_zero hx0)
        rw [one_div, inv_inv] at this
        show (P.map (Polynomial.evalRingHom z)).IsRoot x
        rw [Polynomial.IsRoot, Polynomial.eval_map]
        exact this
      · have h2 := (Set.finite_singleton (0:ℂ)).infinite_compl
        have hset : {x : ℂ | x ≠ 0} = ({0} : Set ℂ)ᶜ := by
          ext x; simp [Set.mem_compl_iff]
        rw [hset]
        exact h2
    apply Polynomial.ext
    intro i
    rw [Polynomial.coeff_zero]
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_univ.mono
    intro z _
    have := congrArg (fun q => Polynomial.coeff q i) (hfib z)
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this
    exact this
  rcases Nat.eq_zero_or_pos R.natDegree with hdeg0 | hdegpos
  · obtain ⟨r₀, hr₀⟩ := Polynomial.natDegree_eq_zero.mp hdeg0
    have hr₀ne : r₀ ≠ 0 := by
      intro hcon
      rw [hcon, map_zero] at hr₀
      exact hR0 hr₀.symm
    have hballinf : (Metric.ball (0:ℂ) 1).Infinite := by
      have hpre : IsPreconnected (Metric.ball (0:ℂ) 1) := (convex_ball (0:ℂ) 1).isPreconnected
      exact hpre.infinite_of_nontrivial ⟨0, mem_ball_self one_pos, (1/2 : ℂ), by
        rw [mem_ball_zero_iff]; norm_num, by norm_num⟩
    have : r₀ = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply hballinf.mono
      intro t ht
      have := hRrel t ht
      rw [← hr₀, Polynomial.eval₂_C] at this
      exact this
    exact hr₀ne this
  · exact h_no_relation hc0 hc2 hhd hhe hfe hh0 R hdegpos hRrel

/-- **GAP 4 CLOSED: connected-case transcendence, unconditional for `c ∈ mandelbrot ∖ {0,-2}`.** -/
theorem phiMero_transcendental_of_mem_mandelbrot {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c : ℂ} (hcM : c ∈ mandelbrot) (hc0 : c ≠ 0) (hc2 : c ≠ -2) (hU : U ⊆ escapeOpen c) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_no_function_relation hUo hUc hUne hUinf c hU
  intro q hq0 hqrel
  exact no_phi_relation_of_mem_mandelbrot hcM hc0 hc2 hUo hUne hU q hq0 hqrel

end
end Bottcher
