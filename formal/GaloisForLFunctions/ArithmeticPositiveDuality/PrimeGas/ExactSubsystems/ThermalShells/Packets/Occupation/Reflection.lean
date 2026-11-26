import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation.Energy

/-! # Critical composition from reflected many-prime occupation counts -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation

open Filter Topology Set Real

/-- A positive count binomial law is the reflection of another precisely when their
single-draw probabilities are complementary. Its all-upper atom already forces this. -/
theorem bin_reflect_iff {m : ℕ} (hm : 0 < m) {p q : ℝ} (hp : 0 ≤ p) (hq : q ≤ 1) :
    (∀ j ≤ m, bin m j p = bin m (m-j) q) ↔ p=1-q := by
  constructor
  · intro h
    have he := h m le_rfl
    simp only [bin,Nat.sub_self,Nat.sub_zero,Nat.choose_self,Nat.choose_zero,Nat.cast_one,
      pow_zero,one_mul,mul_one] at he
    exact (pow_left_inj₀ hp (sub_nonneg.mpr hq) hm.ne').mp he
  · rintro rfl j hj
    simp only [bin,Nat.choose_symm hj,Nat.sub_sub_self hj,sub_sub_cancel]
    ring

private theorem complementary_iff (D : ℝ) {k : ℝ} (hk : 0 < k) (b g : ℝ) :
    upperProbability D k b = 1-upperProbability D k g ↔ odds D k b*odds D k g=1 := by
  have hb := add_pos zero_lt_one (odds_pos D hk b)
  have hg := add_pos zero_lt_one (odds_pos D hk g)
  have comp : 1-upperProbability D k g = 1/(1+odds D k g) := by
    unfold upperProbability; field_simp
  rw [comp,upperProbability,div_eq_div_iff hb.ne' hg.ne']
  constructor <;> intro h <;> linarith only [h]

/-- Reflection of the full limiting upper-count distribution detects norm preservation,
including zero separation between the two inverse temperatures. -/
theorem split_isometric_iff_reflected_counts {c d D : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D)
    {m : ℕ} (hm : 0 < m) (s : ℂ) (a : ℝ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      ∀ j ≤ m, Tendsto (fun h =>
        read c d D 1 (2*s.re-a) m {j} h-read c d D 1 (2*s.re+a) m {m-j} h) criticalApproach (𝓝 0) := by
  letI := criticalApproach_neBot
  let b := 2*s.re-a
  let g := 2*s.re+a
  let p := upperProbability D 1 b
  let q := upperProbability D 1 g
  have same (j : ℕ) : Tendsto (fun h => read c d D 1 b m {j} h-read c d D 1 g m {m-j} h)
      criticalApproach (𝓝 0) ↔ bin m j p = bin m (m-j) q := by
    have H := (cell_limit hc hcd hD zero_lt_one b m j).sub (cell_limit hc hcd hD zero_lt_one g m (m-j))
    constructor
    · intro h
      exact sub_eq_zero.mp (tendsto_nhds_unique H h)
    · intro h
      simpa only [show bin m j (upperProbability D 1 b)-bin m (m-j) (upperProbability D 1 g)=0 from sub_eq_zero.mpr h] using H
  have hp : 0 ≤ p := div_nonneg (odds_pos D zero_lt_one b).le (add_pos zero_lt_one (odds_pos D zero_lt_one b)).le
  have hq : q ≤ 1 := (div_le_one (add_pos zero_lt_one (odds_pos D zero_lt_one g))).mpr (by linarith)
  have refl : (∀ j ≤ m, bin m j p=bin m (m-j) q) ↔ s.re=1/2 := by
    rw [bin_reflect_iff hm hp hq,show p=1-q ↔ _ from complementary_iff D zero_lt_one b g]
    simp only [odds,one_mul,← exp_add,exp_eq_one_iff]
    rw [show (1-b)*D+(1-g)*D = (2-4*s.re)*D by dsimp [b,g]; ring,mul_eq_zero,or_iff_left hD.ne']
    constructor <;> intro h <;> linarith only [h]
  rw [split_isometric_iff,← refl]
  exact ⟨fun he j hj => (same j).mpr (he j hj),fun he j hj => (same j).mp (he j hj)⟩

#print axioms bin_reflect_iff
#print axioms split_isometric_iff_reflected_counts

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation
