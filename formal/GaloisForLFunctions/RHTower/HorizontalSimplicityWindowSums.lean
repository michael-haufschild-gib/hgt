import GaloisForLFunctions.RHTower.HorizontalSimplicityDeficitThmD

/-!
# Window sums over a zero configuration

`zeroWindowSum Z f a b = Σ_{ρ ∈ 𝒵, a < γ ≤ b} f(ρ)` over the distinct zeros.  It is additive in the
window (`windowSum_add`).  Two instances are used:

* the off-line moment `offMoment Z a b = Σ_{β > ½} (β − ½)` (`offMoment_eq_windowSum`);
* the logarithmic off-line moment `logMoment Z a b = Σ_{β > ½} (β − ½) · max(log(γ/2π), 0)`.

The count `NisoH Z δ` of horizontally isolated simple critical zeros is additive as well
(`NisoH_add`).
-/

open Zeta23 Finset

namespace RHTower

noncomputable section

/-- `Σ_{ρ ∈ 𝒵, a < γ ≤ b} f(ρ)` over the distinct zeros. -/
def zeroWindowSum (Z : ZeroConfig) (f : ℂ → ℝ) (a b : ℝ) : ℝ :=
  ∑ ρ ∈ (Z.window_finite a b).toFinset, f ρ

/-- The off-line weight `(β − ½)⁺`. -/
def offWeight (ρ : ℂ) : ℝ := if 1 / 2 < ρ.re then ρ.re - 1 / 2 else 0

/-- The logarithmic off-line moment `Σ (β − ½)⁺ max(log(γ/2π), 0)`. -/
def logMoment (Z : ZeroConfig) (a b : ℝ) : ℝ :=
  zeroWindowSum Z (fun ρ => offWeight ρ * max (l ρ.im) 0) a b

theorem windowSum_add (Z : ZeroConfig) (f : ℂ → ℝ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    zeroWindowSum Z f a c = zeroWindowSum Z f a b + zeroWindowSum Z f b c := by
  classical
  unfold zeroWindowSum
  rw [← Finset.sum_union]
  · congr 1
    ext ρ
    simp only [Set.Finite.mem_toFinset, Finset.mem_union]
    rw [Assembly.window_union Z hab hbc, Set.mem_union]
  · rw [Finset.disjoint_left]
    intro ρ h1 h2
    rw [Set.Finite.mem_toFinset] at h1 h2
    exact Set.disjoint_left.mp (Assembly.window_disjoint Z a b c) h1 h2

theorem windowSum_nonneg (Z : ZeroConfig) {f : ℂ → ℝ} (hf : ∀ ρ, 0 ≤ f ρ) (a b : ℝ) :
    0 ≤ zeroWindowSum Z f a b :=
  Finset.sum_nonneg fun ρ _ => hf ρ

theorem windowSum_mono (Z : ZeroConfig) {f g : ℂ → ℝ} {a b : ℝ}
    (hfg : ∀ ρ ∈ Z.window a b, f ρ ≤ g ρ) : zeroWindowSum Z f a b ≤ zeroWindowSum Z g a b :=
  Finset.sum_le_sum fun ρ hρ => hfg ρ ((Set.Finite.mem_toFinset _).mp hρ)

/-- A window sum of terms at most `K` is at most `K · N(a, b)`. -/
theorem windowSum_le_mul_N (Z : ZeroConfig) {f : ℂ → ℝ} {K : ℝ} (hK : 0 ≤ K) {a b : ℝ}
    (hf : ∀ ρ ∈ Z.window a b, f ρ ≤ K) : zeroWindowSum Z f a b ≤ K * (Z.N a b : ℝ) := by
  have h1 : zeroWindowSum Z f a b ≤ ∑ ρ ∈ (Z.window_finite a b).toFinset, K :=
    Finset.sum_le_sum fun ρ hρ => hf ρ ((Set.Finite.mem_toFinset _).mp hρ)
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : ((Z.window_finite a b).toFinset.card : ℝ) ≤ (Z.N a b : ℝ) := by
    have e : (Z.window_finite a b).toFinset.card = Z.Nd a b := by
      rw [ZeroConfig.Nd, Set.ncard_eq_toFinset_card _ (Z.window_finite a b)]
    rw [e]
    exact_mod_cast Z.Nd_le_N a b
  nlinarith

theorem offWeight_nonneg (ρ : ℂ) : 0 ≤ offWeight ρ := by
  unfold offWeight
  split_ifs with h
  · linarith
  · exact le_rfl

theorem offWeight_le_half {Z : ZeroConfig} {ρ : ℂ} (hρ : ρ ∈ Z.carrier) : offWeight ρ ≤ 1 / 2 := by
  unfold offWeight
  split_ifs with h
  · linarith [(Z.strip ρ hρ).2]
  · norm_num

theorem offMoment_eq_windowSum (Z : ZeroConfig) (a b : ℝ) :
    offMoment Z a b = zeroWindowSum Z offWeight a b := by
  classical
  unfold offMoment zeroWindowSum
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  unfold offWeight
  split_ifs <;> rfl

theorem offMoment_add (Z : ZeroConfig) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    offMoment Z a c = offMoment Z a b + offMoment Z b c := by
  simp only [offMoment_eq_windowSum]
  exact windowSum_add Z _ hab hbc

theorem offMoment_le_half_N (Z : ZeroConfig) (a b : ℝ) :
    offMoment Z a b ≤ 1 / 2 * (Z.N a b : ℝ) := by
  rw [offMoment_eq_windowSum]
  exact windowSum_le_mul_N Z (by norm_num) fun ρ hρ => offWeight_le_half hρ.1

theorem logMoment_nonneg (Z : ZeroConfig) (a b : ℝ) : 0 ≤ logMoment Z a b :=
  windowSum_nonneg Z (fun ρ => mul_nonneg (offWeight_nonneg ρ) (le_max_right _ _)) a b

theorem logMoment_add (Z : ZeroConfig) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    logMoment Z a c = logMoment Z a b + logMoment Z b c :=
  windowSum_add Z _ hab hbc

/-- On `(T, T₂]` the logarithmic moment dominates `log(T/2π)` times the moment. -/
theorem mul_offMoment_le_logMoment (Z : ZeroConfig) {T T₂ : ℝ} (hT : 0 < T) :
    l T * offMoment Z T T₂ ≤ logMoment Z T T₂ := by
  rw [offMoment_eq_windowSum, zeroWindowSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have hρ' := (Set.Finite.mem_toFinset _).mp hρ
  have hlT : l T ≤ max (l ρ.im) 0 := by
    refine le_trans ?_ (le_max_left _ _)
    unfold l
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_right hρ'.2.1.le (by positivity)
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left hlT (offWeight_nonneg ρ)

/-- Up to height `T` the logarithmic moment is at most `max(log(T/2π), 0)` times the moment. -/
theorem logMoment_le_mul_offMoment (Z : ZeroConfig) {T₁ T : ℝ} (hT₁ : 0 ≤ T₁) :
    logMoment Z T₁ T ≤ max (l T) 0 * offMoment Z T₁ T := by
  rw [offMoment_eq_windowSum, logMoment, zeroWindowSum, zeroWindowSum, Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have hρ' := (Set.Finite.mem_toFinset _).mp hρ
  have hl : max (l ρ.im) 0 ≤ max (l T) 0 := by
    apply max_le_max_right
    unfold l
    apply Real.log_le_log (div_pos (by linarith [hρ'.2.1]) (by positivity))
    exact div_le_div_of_nonneg_right hρ'.2.2 (by positivity)
  rw [mul_comm (max (l T) 0)]
  exact mul_le_mul_of_nonneg_left hl (offWeight_nonneg ρ)

/-- Interval additivity of the horizontally isolated simple critical count. -/
theorem NisoH_add (Z : ZeroConfig) (δ : ℝ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    NisoH Z δ a c = NisoH Z δ a b + NisoH Z δ b c := by
  unfold NisoH
  rw [Assembly.window_union Z hab hbc, Set.union_inter_distrib_right,
    Set.union_inter_distrib_right, Set.union_inter_distrib_right,
    Set.ncard_union_eq ((((Assembly.window_disjoint Z a b c).mono Set.inter_subset_left
      Set.inter_subset_left).mono Set.inter_subset_left Set.inter_subset_left).mono
      Set.inter_subset_left Set.inter_subset_left)
    ((((Z.window_finite a b).subset Set.inter_subset_left).subset Set.inter_subset_left).subset
      Set.inter_subset_left)
    ((((Z.window_finite b c).subset Set.inter_subset_left).subset Set.inter_subset_left).subset
      Set.inter_subset_left)]

end

end RHTower
