import GaloisForLFunctions.RHTower.VerticalProgressionResonance

/-!
# The twisted mollified first moment along a vertical progression

Let `φ ∈ C^∞` be supported in `[1, 2]`, `α > 0`, `β, γ ∈ ℝ`, `0 < θ ≤ ½`, and mollify with
`M_N`, `N = ⌊T^θ⌋`. Then (`tendsto_firstMoment_sub_bumpSum_div`)

`(Σ_ℓ φ(ℓ/T) e(ℓγ) ζ(½ + i(αℓ + β)) M_N(½ + i(αℓ + β)) − Σ_ℓ φ(ℓ/T) e(ℓγ)) / T → 0`,

and consequently the mean is `∫ φ` if `γ ∈ ℤ` and `0` otherwise (`tendsto_firstMoment_div_int`,
`tendsto_firstMoment_div_of_not_int`). This is the Bohr-twisted form of Li–Radziwiłł, Prop. 3.

**Proof.** Expand with the long smoothed series of length `X = T^{21/16}`; the error is
`≪ T · T/X · √N = o(T)`. The term `n = 1` is `a(1) L_T(γ)` with `a(1) → 1`. For `n ≥ 2` write
`u_n = γ − α log n/2π`:
* if `u_n` is at distance `≥ T^{−31/32}` from `ℤ`, summation by parts `k = 140` times gives
  `L_T(u_n) ≪ T^{1 − 140/32}`, which beats the polynomial size of `Σ |a(n)| n^{−1/2}`;
* the resonant `n` are grouped by the integer `j` they approach; each `j` carries at most
  `1 + 2eε₀ρ_j` of them, near `ρ_j = e^{2π(γ−j)/α}`. With `d(n) ≪ n^{1/100}`:
  - `n ≤ R₀`: finitely many fixed `n`, each with `a(n) → 0`;
  - `R₀ < n ≤ T^{15/16}`: at most two `n` per `j`, summing to `≪ R₀^{−49/100}` (geometric in `j`);
  - `T^{15/16} < n ≤ Z = T^{θ + 21/16 + 1/100}`: `≪ T^{−(15/16)(49/100)} + T^{−31/32} Z^{51/100}`;
  - `n > Z`: the power decay of the cutoff, `|a(n)| ≤ N K (NX/n)^{400}`.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower.VerticalAP

noncomputable section

/-! ## Bounded derivatives of a compactly supported bump -/

theorem iteratedDeriv_eq_zero_of_not_mem {φ : ℝ → ℂ} (hsupp : Function.support φ ⊆ Icc 1 2)
    (k : ℕ) {y : ℝ} (hy : y ∉ Icc 1 2) : iteratedDeriv k φ y = 0 := by
  have hopen : IsOpen (Icc (1 : ℝ) 2)ᶜ := isClosed_Icc.isOpen_compl
  have hev : φ =ᶠ[nhds y] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds hy] with z hz
    by_contra h
    exact hz (hsupp h)
  rw [hev.iteratedDeriv_eq]
  simp

theorem exists_bound_iteratedDeriv {φ : ℝ → ℂ} (hφ : ∀ k : ℕ, ContDiff ℝ k φ)
    (hsupp : Function.support φ ⊆ Icc 1 2) (k : ℕ) :
    ∃ M : ℝ, ∀ y, ‖iteratedDeriv k φ y‖ ≤ M := by
  have hc : Continuous (iteratedDeriv k φ) := (hφ k).continuous_iteratedDeriv k le_rfl
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc.continuousOn (s := Icc 1 2))
  refine ⟨max C 0, fun y => ?_⟩
  by_cases hy : y ∈ Icc (1 : ℝ) 2
  · exact (hC y hy).trans (le_max_left _ _)
  · rw [iteratedDeriv_eq_zero_of_not_mem hsupp k hy, norm_zero]; exact le_max_right _ _

theorem exists_bound_bump {φ : ℝ → ℂ} (hφ : ∀ k : ℕ, ContDiff ℝ k φ)
    (hsupp : Function.support φ ⊆ Icc 1 2) : ∃ M : ℝ, ∀ y, ‖φ y‖ ≤ M := by
  obtain ⟨M, hM⟩ := exists_bound_iteratedDeriv hφ hsupp 0
  exact ⟨M, fun y => by simpa using hM y⟩

/-! ## Parameters -/

/-- The mollifier length `N = ⌊T^θ⌋`. -/
def molLen (θ T : ℝ) : ℕ := ⌊T ^ θ⌋₊

/-- The length of the smoothed Dirichlet series, `X = T^{21/16}`. -/
def dirLen (T : ℝ) : ℝ := T ^ (21 / 16 : ℝ)

theorem molLen_le {θ T : ℝ} (hT : 0 ≤ T) : (molLen θ T : ℝ) ≤ T ^ θ :=
  Nat.floor_le (Real.rpow_nonneg hT θ)

theorem tendsto_molLen {θ : ℝ} (hθ : 0 < θ) : Tendsto (molLen θ) atTop atTop :=
  tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop hθ)

theorem tendsto_dirLen : Tendsto dirLen atTop atTop := tendsto_rpow_atTop (by norm_num)

/-- `T^p → 0` for `p < 0`. -/
theorem tendsto_rpow_of_neg {p : ℝ} (hp : p < 0) :
    Tendsto (fun T : ℝ => T ^ p) atTop (𝓝 0) := by
  have := tendsto_rpow_neg_atTop (y := -p) (by linarith)
  simpa using this

/-! ## Sums over resonant integers in three ranges -/

/-- `|a(n)| n^{−1/2} ≤ C_d n^{−49/100}` from `d(n) ≤ C_d n^{1/100}`. -/
theorem norm_mollCoeff_mul_rpow_le (N : ℕ) {X : ℝ} (hX : 0 < X) {n : ℕ} (hn : 1 ≤ n) :
    ‖mollCoeff N X n‖ * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      Sieve.divisorBoundConst (1 / 100) * (n : ℝ) ^ (-(49 / 100 : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd := Sieve.card_divisors_le_rpow (ε := 1 / 100) (by norm_num) (n := n) (by omega)
  calc ‖mollCoeff N X n‖ * (n : ℝ) ^ (-(1 / 2 : ℝ))
      ≤ (Sieve.divisorBoundConst (1 / 100) * (n : ℝ) ^ (1 / 100 : ℝ)) *
          (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right ((norm_mollCoeff_le_card_divisors N hX hn).trans hd)
          (by positivity)
    _ = Sieve.divisorBoundConst (1 / 100) * (n : ℝ) ^ (-(49 / 100 : ℝ)) := by
        rw [mul_assoc, ← Real.rpow_add hnR]
        norm_num

/-- **Middle range.** Resonant `n ∈ (R₀, Y]` with `2e·ε₀·eY ≤ 1` contribute at most
`2 C e^a (R₀/e)^{−a} s/(s − 1)`, `s = e^{2πa/α}`. -/
theorem sum_resonant_middle_le {α γ δ : ℝ} (hα : 0 < α) (hδ0 : 0 ≤ δ)
    (hε : 2 * Real.pi * δ / α ≤ 1) {R₀ Y : ℝ} (hR₀ : 0 < R₀)
    (hY : 2 * Real.exp 1 * (2 * Real.pi * δ / α) * (Real.exp 1 * Y) ≤ 1)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n ∧ R₀ < n ∧ (n : ℝ) ≤ Y ∧
      ∃ j : ℤ, |resFreq α γ n - j| < δ)
    (f : ℕ → ℝ) {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hf : ∀ n ∈ S, f n ≤ C * (n : ℝ) ^ (-a)) :
    ∑ n ∈ S, f n ≤ 2 * C * Real.exp a *
      ((R₀ / Real.exp 1) ^ (-a) * (Real.exp (2 * Real.pi * a / α) /
        (Real.exp (2 * Real.pi * a / α) - 1))) := by
  have hsum := sum_resonant_le hα hδ0 hε S (fun n hn => (hS n hn).1)
    (fun n hn => (hS n hn).2.2.2) f hC ha.le hf
  refine hsum.trans ?_
  set ε₀ : ℝ := 2 * Real.pi * δ / α with hε₀
  have hε₀0 : 0 ≤ ε₀ := by positivity
  set J := S.image fun n => round (resFreq α γ n) with hJ
  have hbounds : ∀ j ∈ J, R₀ / Real.exp 1 ≤ resCentre α γ j ∧
      resCentre α γ j ≤ Real.exp 1 * Y := by
    intro j hj
    rw [hJ, Finset.mem_image] at hj
    obtain ⟨n, hn, rfl⟩ := hj
    obtain ⟨h1, hR, hYn, hres⟩ := hS n hn
    obtain ⟨b1, b2⟩ := resCentre_round_bounds hα h1 hres
    have he1 : Real.exp (-ε₀) ≥ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have he2 : Real.exp ε₀ ≤ Real.exp 1 := Real.exp_le_exp.mpr hε
    constructor
    · have : R₀ / Real.exp 1 ≤ (n : ℝ) * Real.exp (-ε₀) := by
        rw [div_eq_mul_inv, ← Real.exp_neg]
        exact mul_le_mul hR.le he1 (Real.exp_pos _).le (by positivity)
      linarith
    · have : (n : ℝ) * Real.exp ε₀ ≤ Real.exp 1 * Y := by
        rw [mul_comm]
        exact mul_le_mul he2 hYn (by positivity) (Real.exp_pos _).le
      linarith
  have hterm : ∀ j ∈ J, C * Real.exp a * resCentre α γ j ^ (-a) *
      (1 + 2 * Real.exp 1 * ε₀ * resCentre α γ j) ≤
      2 * C * Real.exp a * (Real.exp (-(2 * Real.pi * a * γ / α)) *
        Real.exp (2 * Real.pi * a / α) ^ j) := by
    intro j hj
    obtain ⟨_, hhi⟩ := hbounds j hj
    rw [← resCentre_rpow_neg]
    have h2 : 1 + 2 * Real.exp 1 * ε₀ * resCentre α γ j ≤ 2 := by
      have : 2 * Real.exp 1 * ε₀ * resCentre α γ j ≤ 2 * Real.exp 1 * ε₀ * (Real.exp 1 * Y) :=
        mul_le_mul_of_nonneg_left hhi (by positivity)
      linarith
    have hρ := resCentre_pos α γ j
    calc C * Real.exp a * resCentre α γ j ^ (-a) * (1 + 2 * Real.exp 1 * ε₀ * resCentre α γ j)
        ≤ C * Real.exp a * resCentre α γ j ^ (-a) * 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 * C * Real.exp a * resCentre α γ j ^ (-a) := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hs : 1 < Real.exp (2 * Real.pi * a / α) := Real.one_lt_exp_iff.mpr (by positivity)
  refine sum_geometric_le_of_le hs (by positivity) J fun j hj => ?_
  rw [← resCentre_rpow_neg]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (hbounds j hj).1 (by linarith)

/-- **Upper range.** Resonant `n ∈ (Y, Z]` contribute at most
`C e^a ((Y/e)^{−a} s/(s − 1) + 2e ε₀ (eZ)^{1−a} s'/(s' − 1))`, `s' = e^{2π(1−a)/α}`. -/
theorem sum_resonant_upper_le {α γ δ : ℝ} (hα : 0 < α) (hδ0 : 0 ≤ δ)
    (hε : 2 * Real.pi * δ / α ≤ 1) {Y Z : ℝ} (hY : 0 < Y) (hYZ : Y ≤ Z)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n ∧ Y < n ∧ (n : ℝ) ≤ Z ∧
      ∃ j : ℤ, |resFreq α γ n - j| < δ)
    (f : ℕ → ℝ) {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (ha1 : a < 1)
    (hf : ∀ n ∈ S, f n ≤ C * (n : ℝ) ^ (-a)) :
    ∑ n ∈ S, f n ≤ C * Real.exp a *
      ((Y / Real.exp 1) ^ (-a) * (Real.exp (2 * Real.pi * a / α) /
          (Real.exp (2 * Real.pi * a / α) - 1)) +
        2 * Real.exp 1 * (2 * Real.pi * δ / α) * ((Real.exp 1 * Z) ^ (1 - a) *
          (Real.exp (2 * Real.pi * (1 - a) / α) / (Real.exp (2 * Real.pi * (1 - a) / α) - 1)))) := by
  have hsum := sum_resonant_le hα hδ0 hε S (fun n hn => (hS n hn).1)
    (fun n hn => (hS n hn).2.2.2) f hC ha.le hf
  refine hsum.trans ?_
  set ε₀ : ℝ := 2 * Real.pi * δ / α with hε₀
  have hε₀0 : 0 ≤ ε₀ := by positivity
  set J := S.image fun n => round (resFreq α γ n) with hJ
  have hbounds : ∀ j ∈ J, Y / Real.exp 1 ≤ resCentre α γ j ∧
      resCentre α γ j ≤ Real.exp 1 * Z := by
    intro j hj
    rw [hJ, Finset.mem_image] at hj
    obtain ⟨n, hn, rfl⟩ := hj
    obtain ⟨h1, hYn, hZn, hres⟩ := hS n hn
    obtain ⟨b1, b2⟩ := resCentre_round_bounds hα h1 hres
    have he1 : Real.exp (-ε₀) ≥ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have he2 : Real.exp ε₀ ≤ Real.exp 1 := Real.exp_le_exp.mpr hε
    constructor
    · have : Y / Real.exp 1 ≤ (n : ℝ) * Real.exp (-ε₀) := by
        rw [div_eq_mul_inv, ← Real.exp_neg]
        exact mul_le_mul hYn.le he1 (Real.exp_pos _).le (by positivity)
      linarith
    · have : (n : ℝ) * Real.exp ε₀ ≤ Real.exp 1 * Z := by
        rw [mul_comm]
        exact mul_le_mul he2 hZn (by positivity) (Real.exp_pos _).le
      linarith
  have hsplit : ∀ j ∈ J, C * Real.exp a * resCentre α γ j ^ (-a) *
      (1 + 2 * Real.exp 1 * ε₀ * resCentre α γ j) =
      C * Real.exp a * (Real.exp (-(2 * Real.pi * a * γ / α)) *
        Real.exp (2 * Real.pi * a / α) ^ j) +
      C * Real.exp a * (2 * Real.exp 1 * ε₀) * (Real.exp (2 * Real.pi * (1 - a) * γ / α) *
        Real.exp (2 * Real.pi * (1 - a) / α) ^ (-j)) := by
    intro j _
    rw [← resCentre_rpow_neg, ← resCentre_rpow]
    have hρ := resCentre_pos α γ j
    have : resCentre α γ j ^ (-a) * resCentre α γ j = resCentre α γ j ^ (1 - a) := by
      rw [show (1 - a) = -a + 1 by ring, Real.rpow_add hρ, Real.rpow_one]
    rw [← this]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hs : 1 < Real.exp (2 * Real.pi * a / α) := Real.one_lt_exp_iff.mpr (by positivity)
  have h1a : 0 < 1 - a := by linarith
  have hs' : 1 < Real.exp (2 * Real.pi * (1 - a) / α) := Real.one_lt_exp_iff.mpr (by positivity)
  have h1 := sum_geometric_le_of_le hs (Q := (Y / Real.exp 1) ^ (-a)) (by positivity) J
    (fun j hj => by
      rw [← resCentre_rpow_neg]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (hbounds j hj).1 (by linarith))
  have hZ0 : 0 ≤ Real.exp 1 * Z := by have := hY.trans_le hYZ; positivity
  have h2 := sum_geometric_neg_le_of_le hs' (Q := (Real.exp 1 * Z) ^ (1 - a)) (by positivity) J
    (fun j hj => by
      rw [← resCentre_rpow]
      exact Real.rpow_le_rpow (resCentre_pos α γ j).le (hbounds j hj).2 (by linarith))
  have hC' : 0 ≤ C * Real.exp a := by positivity
  calc _ = C * Real.exp a * ∑ j ∈ J, Real.exp (-(2 * Real.pi * a * γ / α)) *
          Real.exp (2 * Real.pi * a / α) ^ j +
        C * Real.exp a * (2 * Real.exp 1 * ε₀) * ∑ j ∈ J, Real.exp (2 * Real.pi * (1 - a) * γ / α) *
          Real.exp (2 * Real.pi * (1 - a) / α) ^ (-j) := by
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ C * Real.exp a * ((Y / Real.exp 1) ^ (-a) * (Real.exp (2 * Real.pi * a / α) /
          (Real.exp (2 * Real.pi * a / α) - 1))) +
        C * Real.exp a * (2 * Real.exp 1 * ε₀) * ((Real.exp 1 * Z) ^ (1 - a) *
          (Real.exp (2 * Real.pi * (1 - a) / α) / (Real.exp (2 * Real.pi * (1 - a) / α) - 1))) := by
        gcongr
    _ = _ := by ring

/-- **Tail.** If `f(n) ≤ W n^{−(A + 1/2)}` on a finite set of `n > Z ≥ 1` with `A ≥ 3/2`, then
`Σ f ≤ W Z^{−(A − 3/2)} Σ_n n^{−2}`. -/
theorem sum_tail_le {Z W A : ℝ} (hZ : 1 ≤ Z) (hW : 0 ≤ W) (hA : 3 / 2 ≤ A) (S : Finset ℕ)
    (hS : ∀ n ∈ S, Z < n) (f : ℕ → ℝ) (hf : ∀ n ∈ S, f n ≤ W * (n : ℝ) ^ (-(A + 1 / 2))) :
    ∑ n ∈ S, f n ≤ W * Z ^ (-(A - 3 / 2)) * ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ) := by
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hterm : ∀ n ∈ S, f n ≤ W * Z ^ (-(A - 3 / 2)) * (n : ℝ) ^ (-2 : ℝ) := by
    intro n hn
    have hnZ := hS n hn
    have hn0 : (0 : ℝ) < n := by linarith
    refine (hf n hn).trans ?_
    rw [show -(A + 1 / 2) = -(A - 3 / 2) + (-2) by ring, Real.rpow_add hn0, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hW) (by positivity)
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hnZ.le (by linarith)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact hsum.sum_le_tsum S (fun n _ => by positivity)

open Classical in
/-- The resonant mass `Q(T) = Σ_{n ≥ 2, dist(u_n, ℤ) < T^{−31/32}} |a(n)| n^{−1/2}`. -/
def resonantMass (α γ θ T : ℝ) : ℝ :=
  ∑' m : ℕ, if (∃ j : ℤ, |resFreq α γ (m + 2) - j| < T ^ (-(31 / 32 : ℝ))) then
    ‖mollCoeff (molLen θ T) (dirLen T) (m + 2)‖ * ((m + 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) else 0

theorem resonantMass_nonneg (α γ θ T : ℝ) : 0 ≤ resonantMass α γ θ T := by
  classical
  unfold resonantMass
  exact tsum_nonneg fun m => by split_ifs <;> positivity

end

end RHTower.VerticalAP
