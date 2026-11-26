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
    simp [bin] at he
    exact (pow_left_inj₀ hp (sub_nonneg.mpr hq) hm.ne').mp he
  · rintro rfl j hj
    simp only [bin,Nat.choose_symm hj,Nat.sub_sub_self hj,sub_sub_cancel]
    ring

private theorem complementary_iff (D : ℝ) {k : ℝ} (hk : 0 < k) (b g : ℝ) :
    upperProbability D k b = 1-upperProbability D k g ↔ odds D k b*odds D k g=1 := by
  have hb := add_pos zero_lt_one (odds_pos D hk b)
  have hg := add_pos zero_lt_one (odds_pos D hk g)
  have comp : 1-upperProbability D k g = 1/(1+odds D k g) := by
    unfold upperProbability
    field_simp [hg.ne']
    ring
  rw [comp,upperProbability,div_eq_div_iff hb.ne' hg.ne']
  constructor <;> intro h <;> linear_combination h

private theorem difference_limit {α : Type*} {l : Filter α} [l.NeBot] {u v : α → ℝ} {x y : ℝ}
    (hu : Tendsto u l (𝓝 x)) (hv : Tendsto v l (𝓝 y)) :
    Tendsto (fun h => u h-v h) l (𝓝 0) ↔ x=y := by
  have H := hu.sub hv
  exact ⟨fun h => sub_eq_zero.mp (tendsto_nhds_unique H h),fun h => (sub_eq_zero.mpr h) ▸ H⟩

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
      criticalApproach (𝓝 0) ↔ bin m j p = bin m (m-j) q :=
    difference_limit (cell_limit hc hcd hD zero_lt_one b m j) (cell_limit hc hcd hD zero_lt_one g m (m-j))
  have hp : 0 ≤ p := div_nonneg (odds_pos D zero_lt_one b).le (add_pos zero_lt_one (odds_pos D zero_lt_one b)).le
  have hq : q ≤ 1 := (div_le_one (add_pos zero_lt_one (odds_pos D zero_lt_one g))).mpr (by linarith)
  have refl : (∀ j ≤ m, bin m j p=bin m (m-j) q) ↔ s.re=1/2 := by
    rw [bin_reflect_iff hm hp hq,show p=1-q ↔ _ from complementary_iff D zero_lt_one b g]
    simp only [odds,one_mul,← exp_add,exp_eq_one_iff]
    rw [show (1-b)*D+(1-g)*D = (2-4*s.re)*D by dsimp [b,g]; ring,mul_eq_zero,or_iff_left hD.ne']
    constructor <;> intro h <;> linarith only [h]
  rw [split_isometric_iff,← refl]
  exact ⟨fun he j hj => (same j).mpr (he j hj),fun he j hj => (same j).mp (he j hj)⟩

private theorem grid_reflect (m : ℕ) (D : ℝ) (w : ℕ → ℝ) (f : ℝ → ℝ) :
    (∑ j ∈ Finset.range (m+1), w j*f ((m:ℝ)*D-(j:ℝ)*D)) =
      ∑ j ∈ Finset.range (m+1), w (m-j)*f ((j:ℝ)*D) := by
  rw [← Finset.sum_range_reflect (fun i => w i*f ((m:ℝ)*D-(i:ℝ)*D)) (m+1)]
  apply Finset.sum_congr rfl
  intro j hj
  have h := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  simp only [Nat.add_sub_cancel,Nat.cast_sub h]
  rw [show (m:ℝ)*D-((m:ℝ)-j)*D=j*D by ring]

private def levelTest (D : ℝ) (j : ℕ) (x : ℝ) := max 0 (1-|x/D-(j:ℝ)|)

private theorem level_value {D : ℝ} (hD : 0 < D) (i j : ℕ) :
    levelTest D j ((i:ℝ)*D) = if i=j then 1 else 0 := by
  unfold levelTest
  rw [mul_div_cancel_right₀ _ hD.ne']
  rcases lt_trichotomy i j with h | rfl | h
  · rw [if_neg h.ne,abs_of_neg (sub_neg.mpr (Nat.cast_lt.mpr h)),max_eq_left]
    have hh : (i:ℝ)+1 ≤ j := by exact_mod_cast (Nat.succ_le_of_lt h)
    linarith only [hh]
  · simp
  · rw [if_neg h.ne',abs_of_pos (sub_pos.mpr (Nat.cast_lt.mpr h)),max_eq_left]
    have hh : (j:ℝ)+1 ≤ i := by exact_mod_cast (Nat.succ_le_of_lt h)
    linarith only [hh]

private theorem isolate_level {D : ℝ} (hD : 0 < D) {m j : ℕ} (hj : j ≤ m) (w : ℕ → ℝ) :
    (∑ i ∈ Finset.range (m+1), w i*levelTest D j ((i:ℝ)*D)) = w j := by
  simp only [level_value hD,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_range,
    if_pos (Nat.lt_succ_of_le hj)]

/-- The total Hamiltonian alone identifies norm-preserving composition. Reflection of the
centered energy about mD/2 exchanges the limiting readings at symmetric inverse temperatures
for every continuous energy observable exactly at the isometric split. -/
theorem split_isometric_iff_reflected_energy {c d D : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D)
    {m : ℕ} (hm : 0 < m) (s : ℂ) (a : ℝ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      ∀ f : ℝ → ℝ, Continuous f → Tendsto (fun h =>
        energyRead c d D 1 (2*s.re-a) m f h-
          energyRead c d D 1 (2*s.re+a) m (fun x => f ((m:ℝ)*D-x)) h) criticalApproach (𝓝 0) := by
  letI := criticalApproach_neBot
  let b := 2*s.re-a
  let g := 2*s.re+a
  let P (i : ℕ) := bin m i (upperProbability D 1 b)
  let Q (i : ℕ) := bin m i (upperProbability D 1 g)
  have cell (j : ℕ) : Tendsto (fun h => read c d D 1 b m {j} h-read c d D 1 g m {m-j} h)
      criticalApproach (𝓝 0) ↔ P j=Q (m-j) :=
    difference_limit (cell_limit hc hcd hD zero_lt_one b m j) (cell_limit hc hcd hD zero_lt_one g m (m-j))
  have test (f : ℝ → ℝ) (hf : Continuous f) :
      Tendsto (fun h => energyRead c d D 1 b m f h-energyRead c d D 1 g m (fun x => f ((m:ℝ)*D-x)) h)
        criticalApproach (𝓝 0) ↔
      (∑ j ∈ Finset.range (m+1), P j*f ((j:ℝ)*D)) =
        ∑ j ∈ Finset.range (m+1), Q (m-j)*f ((j:ℝ)*D) := by
    rw [← grid_reflect m D Q f]
    exact difference_limit (energy_limit hc hcd hD zero_lt_one b m f hf)
      (energy_limit hc hcd hD zero_lt_one g m _ (hf.comp (continuous_const.sub continuous_id)))
  rw [split_isometric_iff_reflected_counts hc hcd hD hm s a]
  constructor
  · intro hc' f hf
    apply (test f hf).mpr
    exact Finset.sum_congr rfl fun j hj => congrArg (·*f ((j:ℝ)*D))
      ((cell j).mp (hc' j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))))
  · intro he j hj
    apply (cell j).mpr
    have hf : Continuous (levelTest D j) := by unfold levelTest; fun_prop
    have h := (test _ hf).mp (he _ hf)
    rw [isolate_level hD hj P,isolate_level hD hj (fun i => Q (m-i))] at h
    exact h

#print axioms split_isometric_iff_reflected_energy
#print axioms bin_reflect_iff
#print axioms split_isometric_iff_reflected_counts

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation
