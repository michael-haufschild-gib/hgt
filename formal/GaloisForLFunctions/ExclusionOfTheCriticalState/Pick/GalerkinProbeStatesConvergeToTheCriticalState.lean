import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.TheConfinedPickMatricesDecideTheCriticalRatio

/-!
# Galerkin probe states converge to the critical state

Off RH the critical state `F` is the null vector of the confined form `Q_{W₀}`, and below the second
critical ratio `R₂ > W₀` there is no negative plane. This is a spectral gap: on the `W₈`-complement of
`F`, `Q_{R₂} ≥ 0` (`fullEnergy_nonneg_of_orth_criticalState`), so `Q_{W₀}(X) ≥ (a(W₀) − a(R₂)) W₈(X)`
there. Splitting a profile `G` of mass `W₈(G) = W₈(F)` as `αF + X` gives

  `min_{s = ±1} W₈(G − sF) ≤ 2 Q_{W₀}(G) / (a(W₀) − a(R₂))`   (`exists_sign_exponentialMass_sub_le`).

**Galerkin convergence** (`criticalState_probe_galerkin`). For a ratio `R ↓ W₀` the integer Pick
blocks of `Q_R` eventually carry a negative vector (`confinedPick_blocks_approximate_criticalRatio`);
its probe sum, normalized to mass `W₈(F)`, has `Q_{W₀} ≤ (a(W₀) − a(R)) W₈(F)`. Hence for every `ε > 0`
and all large `N` a combination `P` of the probes `e_7, …, e_{N+6}` has `W₈(P − F) ≤ ε` and
`Q_{W₀}(P − F) ≤ ε`; the second bound holds because adding a multiple of `F` leaves `Q_{W₀}` unchanged.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory

local notation "W8" => criticalHalfLineExponentialPair

/-- The confinement coefficient `a(R) = a(1)/R` is strictly decreasing. -/
theorem criticalAliasCoefficient_lt {R S : ℝ} (hR : 0 < R) (hRS : R < S) :
    criticalAliasCoefficient S < criticalAliasCoefficient R := by
  rw [criticalAliasCoefficient_eq_div R, criticalAliasCoefficient_eq_div S]
  exact div_lt_div_of_pos_left (criticalAliasCoefficient_positive one_pos) hR hRS

/-- The confined energy changes with the ratio through the confinement only. -/
theorem fullEnergy_change_ratio (R S : ℝ) {X : ℝ → ℝ} (hX : CriticalHalfLineEnergyDomain X) :
    criticalHalfLineFullEnergy R X = criticalHalfLineFullEnergy S X +
      (criticalAliasCoefficient R - criticalAliasCoefficient S) * W8 X X := by
  rw [← criticalHalfLineMixedEnergy_self R hX, ← criticalHalfLineMixedEnergy_self S hX,
    criticalHalfLineMixedEnergy_change_ratio R S hX hX]

theorem probeSum_smul_coeff {N : ℕ} (p c : Fin N → ℝ) (r u : ℝ) :
    probeSum p (fun k => r * c k) u = r * probeSum p c u := by
  simp only [probeSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- For `X` `W₈`-orthogonal to a null vector `Φ` of `Q_S`:
`Q_R(sΦ + tX) = t² Q_R(X) + s² (a(R) − a(S)) W₈(Φ)`. -/
theorem fullEnergy_smul_add_smul_nullVector (R : ℝ) {S : ℝ} {Φ : ℝ → ℝ}
    (hΦ : IsConfinedNullVector S Φ) {X : ℝ → ℝ} (hX : CriticalHalfLineEnergyDomain X)
    (horth : W8 Φ X = 0) (s t : ℝ) :
    criticalHalfLineFullEnergy R (fun u => s * Φ u + t * X u) =
      t ^ 2 * criticalHalfLineFullEnergy R X +
        s ^ 2 * ((criticalAliasCoefficient R - criticalAliasCoefficient S) * W8 Φ Φ) := by
  have h := fullEnergy_add_sum_nullVectors R (ι := Unit) (S := fun _ => S) (Φ := fun _ => Φ)
    (fun _ => hΦ) (fun i j hij => absurd (Subsingleton.elim i j) hij) (hX.const_mul t)
    (fun _ => by rw [exponentialPair_const_mul, horth, mul_zero]) (fun _ => s) Finset.univ
  simp only [Finset.univ_unique, Finset.sum_singleton, criticalHalfLineFullEnergy_const_mul] at h
  rw [← h]
  congr 1
  funext u
  ring

/-- **The spectral gap at the critical state.** Without a negative plane at `R₂ > W₀`, the confined
form `Q_{R₂}` is nonnegative on the `W₈`-complement of the critical state. -/
theorem fullEnergy_nonneg_of_orth_criticalState {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) {R₂ : ℝ} (hR₂ : W₀ < R₂)
    (hnot : ∀ G₁ G₂ : ℝ → ℝ, ¬ IsNegativePlane R₂ G₁ G₂) {X : ℝ → ℝ}
    (hX : CriticalHalfLineEnergyDomain X) (horth : W8 F X = 0) :
    0 ≤ criticalHalfLineFullEnergy R₂ X := by
  by_contra hneg
  push Not at hneg
  have hnull := isConfinedNullVector_of_groundState hW ht hF
  have hm := exponentialPair_self_pos hnull.1 hnull.2.1
  have ha := criticalAliasCoefficient_lt hW hR₂
  have hK : (criticalAliasCoefficient R₂ - criticalAliasCoefficient W₀) * W8 F F < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hm
  refine hnot F X ⟨hnull.1, hX, fun s t hst => ?_⟩
  rw [fullEnergy_smul_add_smul_nullVector R₂ hnull hX horth s t]
  have hs2 := mul_nonneg (sq_nonneg s) (neg_nonneg.mpr hK.le)
  have ht2 := mul_nonneg (sq_nonneg t) (neg_nonneg.mpr hneg.le)
  rcases eq_or_ne t 0 with rfl | ht0
  · have hs : s ≠ 0 := by rintro rfl; exact hst rfl
    have := mul_neg_of_pos_of_neg (lt_of_le_of_ne (sq_nonneg s) (Ne.symm (pow_ne_zero 2 hs))) hK
    nlinarith
  · have := mul_neg_of_pos_of_neg (lt_of_le_of_ne (sq_nonneg t) (Ne.symm (pow_ne_zero 2 ht0))) hneg
    nlinarith

/-- **Distance to the critical state is controlled by the energy.** A profile `G` of mass `W₈(F)` is
within `2 Q_{W₀}(G)/(a(W₀) − a(R₂))` of `F` or of `−F`. -/
theorem exists_sign_exponentialMass_sub_le {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) {R₂ : ℝ} (hR₂ : W₀ < R₂)
    (hnot : ∀ G₁ G₂ : ℝ → ℝ, ¬ IsNegativePlane R₂ G₁ G₂) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) (hGm : W8 G G = W8 F F) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ W8 (fun u => G u - s * F u) (fun u => G u - s * F u) ≤
      2 * criticalHalfLineFullEnergy W₀ G /
        (criticalAliasCoefficient W₀ - criticalAliasCoefficient R₂) := by
  have hnull := isConfinedNullVector_of_groundState hW ht hF
  have hD := hnull.1
  have hm : 0 < W8 F F := exponentialPair_self_pos hD hnull.2.1
  have hδ : 0 < criticalAliasCoefficient W₀ - criticalAliasCoefficient R₂ := by
    have := criticalAliasCoefficient_lt hW hR₂; linarith
  obtain ⟨m, hm_def⟩ : ∃ m, m = W8 F F := ⟨_, rfl⟩
  obtain ⟨δ, hδ_def⟩ : ∃ δ, δ = criticalAliasCoefficient W₀ - criticalAliasCoefficient R₂ :=
    ⟨_, rfl⟩
  rw [← hm_def] at hm hGm
  rw [← hδ_def] at hδ ⊢
  -- split `G = αF + X` with `X ⟂ F`
  obtain ⟨α, hα_def⟩ : ∃ α, α = W8 F G / m := ⟨_, rfl⟩
  obtain ⟨X, hX_def⟩ : ∃ X : ℝ → ℝ, X = fun u => G u + (-α) * F u := ⟨_, rfl⟩
  have hX : CriticalHalfLineEnergyDomain X := by rw [hX_def]; exact hG.add_const_mul hD (-α)
  have horth : W8 F X = 0 := by
    rw [hX_def, exponentialPair_add_const_mul hD hG hD, ← hm_def, hα_def, neg_mul,
      div_mul_cancel₀ _ hm.ne', add_neg_cancel]
  have horth' : W8 X F = 0 := by rw [exponentialPair_comm]; exact horth
  -- the energy of `G` is that of its orthogonal part, bounded below by the gap
  have hQ : criticalHalfLineFullEnergy W₀ G = criticalHalfLineFullEnergy W₀ X := by
    have h := fullEnergy_smul_add_smul_nullVector W₀ hnull hX horth α 1
    have e : (fun u => α * F u + 1 * X u) = G := by funext u; simp only [hX_def]; ring
    rw [e, sub_self, zero_mul, mul_zero, add_zero, one_pow, one_mul] at h
    exact h
  have hgap := fullEnergy_nonneg_of_orth_criticalState hW ht hF hR₂ hnot hX horth
  have hXQ : δ * W8 X X ≤ criticalHalfLineFullEnergy W₀ G := by
    rw [hQ, fullEnergy_change_ratio W₀ R₂ hX, ← hδ_def]
    linarith
  -- Pythagoras along `F`
  have hexp : ∀ c : ℝ, W8 (fun u => X u + c * F u) (fun u => X u + c * F u) =
      W8 X X + c ^ 2 * m := by
    intro c
    have hY := hX.add_const_mul hD c
    rw [exponentialPair_add_const_mul hY hX hD c, exponentialPair_comm (fun u => X u + c * F u) X,
      exponentialPair_add_const_mul hX hX hD c, exponentialPair_comm (fun u => X u + c * F u) F,
      exponentialPair_add_const_mul hD hX hD c, horth, horth', ← hm_def]
    ring
  have hGmass : W8 X X + α ^ 2 * m = m := by
    rw [← hexp α, ← hGm]
    have e : (fun u => X u + α * F u) = G := by funext u; simp only [hX_def]; ring
    rw [e]
  have hα : α ^ 2 ≤ 1 := by
    have hXX : 0 ≤ W8 X X := by
      rw [criticalHalfLineExponentialPair_self]
      exact integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    nlinarith
  have hαabs : |α| ≤ 1 := (sq_le_one_iff_abs_le_one α).mp hα
  have h1 : (1 - |α|) ^ 2 * m ≤ W8 X X := by
    have h0 : (1 - |α|) ^ 2 ≤ 1 - α ^ 2 := by
      rw [← sq_abs α]; nlinarith [abs_nonneg α]
    have := mul_le_mul_of_nonneg_right h0 hm.le
    nlinarith
  have key : ∀ s : ℝ, (α - s) ^ 2 = (1 - |α|) ^ 2 →
      W8 (fun u => G u - s * F u) (fun u => G u - s * F u) ≤
        2 * criticalHalfLineFullEnergy W₀ G / δ := by
    intro s hs
    have hdiff : (fun u => G u - s * F u) = fun u => X u + (α - s) * F u := by
      funext u; simp only [hX_def]; ring
    rw [hdiff, hexp (α - s), hs, le_div_iff₀ hδ]
    nlinarith [mul_le_mul_of_nonneg_left h1 hδ.le]
  rcases le_or_gt 0 α with h | h
  · exact ⟨1, Or.inl rfl, key 1 (by rw [abs_of_nonneg h]; ring)⟩
  · exact ⟨-1, Or.inr rfl, key (-1) (by rw [abs_of_neg h]; ring)⟩

/-- Adding a multiple of the critical state does not change the critical energy. -/
theorem fullEnergy_add_const_mul_criticalState {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    (c : ℝ) :
    criticalHalfLineFullEnergy W₀ (fun u => G u + c * F u) = criticalHalfLineFullEnergy W₀ G := by
  have hnull := isConfinedNullVector_of_groundState hW ht hF
  rw [criticalHalfLineFullEnergy_add_const_mul W₀ hG hnull.1 c, criticalHalfLineMixedEnergy_comm,
    hnull.2.2 G hG, criticalHalfLineFullEnergy_groundState_eq_zero hW ht hF]
  ring

/-- **Galerkin approximation on probe spans converges to the critical state.** For every `ε > 0` and
all large `N` some combination `P` of the integer probes `e_7, …, e_{N+6}` has
`W₈(P − F) ≤ ε` and `Q_{W₀}(P − F) ≤ ε`: convergence in the energy norm `Q_{W₀} + W₈`. -/
theorem criticalState_probe_galerkin {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ c : Fin N → ℝ,
      W8 (fun u => probeSum (fun k : Fin N => (k : ℝ) + 7) c u - F u)
        (fun u => probeSum (fun k : Fin N => (k : ℝ) + 7) c u - F u) ≤ ε ∧
      criticalHalfLineFullEnergy W₀ (fun u => probeSum (fun k : Fin N => (k : ℝ) + 7) c u - F u) ≤ ε := by
  obtain ⟨R₂, hR₂, hnot, -, -⟩ := criticalState_secondCriticalState hW ht hF
  have hnot₂ : ∀ G₁ G₂ : ℝ → ℝ, ¬ IsNegativePlane R₂ G₁ G₂ := hnot R₂ (hW.trans hR₂) le_rfl
  have hnull := isConfinedNullVector_of_groundState hW ht hF
  have hm : 0 < W8 F F := exponentialPair_self_pos hnull.1 hnull.2.1
  have hδ : 0 < criticalAliasCoefficient W₀ - criticalAliasCoefficient R₂ := by
    have := criticalAliasCoefficient_lt hW hR₂; linarith
  have ha₀ : 0 < criticalAliasCoefficient W₀ := criticalAliasCoefficient_positive hW
  obtain ⟨m, hm_def⟩ : ∃ m, m = W8 F F := ⟨_, rfl⟩
  obtain ⟨δ, hδ_def⟩ : ∃ δ, δ = criticalAliasCoefficient W₀ - criticalAliasCoefficient R₂ :=
    ⟨_, rfl⟩
  obtain ⟨a₀, ha₀_def⟩ : ∃ a, a = criticalAliasCoefficient W₀ := ⟨_, rfl⟩
  rw [← hm_def] at hm
  rw [← hδ_def] at hδ
  rw [← ha₀_def] at ha₀
  -- a working tolerance with `ε₁ ≤ ε` and `ε₁ δ/4 ≤ ε`
  obtain ⟨ε₁, hε₁_def⟩ : ∃ e, e = min ε (4 * ε / δ) := ⟨_, rfl⟩
  have hε₁ : 0 < ε₁ := by rw [hε₁_def]; exact lt_min hε (div_pos (mul_pos four_pos hε) hδ)
  have hε₁ε : ε₁ ≤ ε := by rw [hε₁_def]; exact min_le_left _ _
  have hε₁δ : ε₁ * δ / 4 ≤ ε := by
    have h : ε₁ ≤ 4 * ε / δ := by rw [hε₁_def]; exact min_le_right _ _
    rw [le_div_iff₀ hδ] at h
    linarith
  -- a ratio `R > W₀` with `m (a(W₀) − a(R)) ≤ εδ/4`
  obtain ⟨η, hη_def⟩ : ∃ η, η = ε₁ * δ / (4 * m * a₀) := ⟨_, rfl⟩
  have hη : 0 < η := by
    rw [hη_def]; exact div_pos (mul_pos hε₁ hδ) (mul_pos (mul_pos four_pos hm) ha₀)
  obtain ⟨R, hR_def⟩ : ∃ R, R = W₀ * (1 + η) := ⟨_, rfl⟩
  have hR : W₀ < R := by rw [hR_def]; nlinarith [mul_pos hW hη]
  have hRpos : 0 < R := hW.trans hR
  have hgapR : m * (a₀ - criticalAliasCoefficient R) ≤ ε₁ * δ / 4 := by
    have hW0 : W₀ ≠ 0 := hW.ne'
    have h1η : (1 + η) ≠ 0 := (by linarith : (0 : ℝ) < 1 + η).ne'
    have e : a₀ - criticalAliasCoefficient R = a₀ * η / (1 + η) := by
      rw [hR_def, ha₀_def, criticalAliasCoefficient_eq_div W₀,
        criticalAliasCoefficient_eq_div (W₀ * (1 + η))]
      field_simp
      ring
    rw [e]
    have h1 : a₀ * η / (1 + η) ≤ a₀ * η := div_le_self (mul_pos ha₀ hη).le (by linarith)
    have hm0 : m ≠ 0 := hm.ne'
    have ha0 : a₀ ≠ 0 := ha₀.ne'
    have h2 : m * (a₀ * η) = ε₁ * δ / 4 := by rw [hη_def]; field_simp
    calc m * (a₀ * η / (1 + η)) ≤ m * (a₀ * η) := mul_le_mul_of_nonneg_left h1 hm.le
      _ = ε₁ * δ / 4 := h2
  -- a negative integer Pick vector at ratio `R`
  obtain ⟨N₀, hN₀⟩ := (confinedPick_blocks_approximate_criticalRatio ht hRpos).2 hR
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨c, hc⟩ := hN₀ N hN
  have hp : ∀ k : Fin N, (4 : ℝ) < (k : ℝ) + 7 := fun k => by
    linarith [Nat.cast_nonneg (α := ℝ) (k : ℕ)]
  obtain ⟨P, hP_def⟩ : ∃ P : ℝ → ℝ, P = probeSum (fun k : Fin N => (k : ℝ) + 7) c := ⟨_, rfl⟩
  have hP : CriticalHalfLineEnergyDomain P := by
    rw [hP_def]
    exact criticalHalfLineEnergyDomain_finsetSum _ (fun k => criticalHalfLineEnergyDomain_probe (hp k)) c
  have hPQ : criticalHalfLineFullEnergy R P < 0 := by
    have h := confinedPickForm_eq_fullEnergy R c
    rw [← hP_def] at h
    linarith
  have hPm : 0 < W8 P P :=
    exponentialPair_self_pos hP (integral_sq_pos_of_fullEnergy_neg hRpos hP hPQ).ne'
  have hW0 : W8 P P ≠ 0 := hPm.ne'
  -- normalize to the mass of `F`
  obtain ⟨κ, hκ_def⟩ : ∃ κ, κ = Real.sqrt (m / W8 P P) := ⟨_, rfl⟩
  have hκ : κ ^ 2 = m / W8 P P := by rw [hκ_def]; exact Real.sq_sqrt (div_nonneg hm.le hPm.le)
  have hG : CriticalHalfLineEnergyDomain (fun u => κ * P u) := hP.const_mul κ
  have hGm : W8 (fun u => κ * P u) (fun u => κ * P u) = W8 F F := by
    rw [exponentialPair_const_mul, exponentialPair_comm, exponentialPair_const_mul, ← mul_assoc,
      ← sq, hκ, div_mul_cancel₀ _ hW0, hm_def]
  have hGQ : criticalHalfLineFullEnergy W₀ (fun u => κ * P u) ≤ ε₁ * δ / 4 := by
    rw [criticalHalfLineFullEnergy_const_mul, fullEnergy_change_ratio W₀ R hP, hκ, ← ha₀_def]
    have hdiv : m / W8 P P * (criticalHalfLineFullEnergy R P +
        (a₀ - criticalAliasCoefficient R) * W8 P P) ≤
        m / W8 P P * ((a₀ - criticalAliasCoefficient R) * W8 P P) :=
      mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hm.le hPm.le)
    have he : m / W8 P P * ((a₀ - criticalAliasCoefficient R) * W8 P P) =
        m * (a₀ - criticalAliasCoefficient R) := by
      rw [mul_comm (a₀ - _) (W8 P P), ← mul_assoc, div_mul_cancel₀ _ hW0]
    linarith
  -- the spectral gap turns small energy into closeness
  obtain ⟨s, hs, hdist⟩ := exists_sign_exponentialMass_sub_le hW ht hF hR₂ hnot₂ hG hGm
  rw [← hδ_def] at hdist
  have hεδ := mul_pos hε₁ hδ
  have hdist' : W8 (fun u => κ * P u - s * F u) (fun u => κ * P u - s * F u) ≤ ε₁ := by
    refine hdist.trans ?_
    rw [div_le_iff₀ hδ]
    linarith
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hsum : (fun u => probeSum (fun k : Fin N => (k : ℝ) + 7) (fun k => s * κ * c k) u - F u) =
      fun u => s * (κ * P u - s * F u) := by
    funext u
    rw [probeSum_smul_coeff, ← hP_def]
    linear_combination (F u) * hs2
  refine ⟨fun k => s * κ * c k, ?_, ?_⟩
  · rw [hsum, exponentialPair_const_mul, exponentialPair_comm, exponentialPair_const_mul,
      ← mul_assoc, hs2, one_mul]
    exact hdist'.trans hε₁ε
  · rw [hsum, criticalHalfLineFullEnergy_const_mul, show s ^ 2 = 1 by rw [sq]; exact hs2, one_mul,
      show (fun u => κ * P u - s * F u) = fun u => κ * P u + (-s) * F u by funext u; ring,
      fullEnergy_add_const_mul_criticalState hW ht hF hG (-s)]
    linarith

/-- **Galerkin form of the critical state.** Off RH the critical state is the limit, in `W₈` and in the
critical energy, of combinations of the integer probes on growing blocks. -/
theorem riemannHypothesis_or_probe_galerkin :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧ IsCriticalHalfLineGroundState W₀ F ∧
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ c : Fin N → ℝ,
        W8 (fun u => probeSum (fun k : Fin N => (k : ℝ) + 7) c u - F u)
          (fun u => probeSum (fun k : Fin N => (k : ℝ) + 7) c u - F u) ≤ ε ∧
        criticalHalfLineFullEnergy W₀ (fun u => probeSum (fun k : Fin N => (k : ℝ) + 7) c u - F u) ≤
          ε := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl h
  · exact Or.inr ⟨W₀, F, hW, hF, fun ε hε => criticalState_probe_galerkin hW ht hF hε⟩

#print axioms riemannHypothesis_or_probe_galerkin

end GaloisForLFunctions.ExclusionOfTheCriticalState
