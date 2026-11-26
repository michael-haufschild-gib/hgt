import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Mass

/-! # Two endpoint packets inside an energy interval of prescribed width -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets

open Filter Topology Real

def low (t : ℝ) := packet t 0 1

def offset (D k t : ℝ) := D-log (1+k/t)

def high (D k t : ℝ) := packet t (offset D k t) k

def both (D k t : ℝ) := low t ∪ high D k t

theorem offset_limit (D k : ℝ) : Tendsto (offset D k) atTop (𝓝 D) := by
  change Tendsto (fun t : ℝ => D-log (1+k/t)) atTop (𝓝 D)
  simpa only [sub_zero] using (tendsto_const_nhds (x := D)).sub (logWidth_limit k)

theorem low_energy {t : ℝ} (ht : 0 < t) {p : ℕ} (hp : p ∈ low t) :
    p.Prime ∧ t < log (p:ℝ) ∧ log (p:ℝ) ≤ t+log (1+1/t) := by
  simpa only [add_zero] using packet_energy ht zero_lt_one hp

theorem high_energy {D k t : ℝ} (hk : 0 < k) (ht : 0 < t) {p : ℕ} (hp : p ∈ high D k t) :
    p.Prime ∧ t+offset D k t < log (p:ℝ) ∧ log (p:ℝ) ≤ t+D := by
  obtain ⟨hP,hl,hu⟩ := packet_energy ht hk hp
  exact ⟨hP,hl,by unfold offset at hu; linarith only [hu]⟩

private theorem packet_nonempty {v : ℝ → ℝ} {V a : ℝ} (hv : Tendsto v atTop (𝓝 V)) (ha : 0 < a) :
    ∀ᶠ t in atTop, (packet t (v t) a).Nonempty := by
  filter_upwards [(count_limit hv ha).eventually_const_lt (mul_pos ha (exp_pos V))] with t hp
  by_contra hn
  rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.card_empty,Nat.cast_zero,mul_zero] at hp
  exact lt_irrefl _ hp

/-- Eventually both packets are populated, separated and contained in the open-left energy window. -/
theorem windows {D k : ℝ} (hD : 0 < D) (hk : 0 < k) :
    ∀ᶠ t : ℝ in atTop, (low t).Nonempty ∧ (high D k t).Nonempty ∧ Disjoint (low t) (high D k t) ∧
      ∀ p ∈ both D k t, p.Prime ∧ t < log (p:ℝ) ∧ log (p:ℝ) ≤ t+D := by
  have hs := (logWidth_limit 1).eventually_lt (offset_limit D k) hD
  filter_upwards [hs,eventually_gt_atTop (0:ℝ),packet_nonempty (tendsto_const_nhds (x := (0:ℝ))) zero_lt_one,
    packet_nonempty (offset_limit D k) hk] with t hsep ht hl hh
  have wl : 0 ≤ log (1+1/t) := log_nonneg (by linarith only [div_pos one_pos ht])
  have wh : 0 ≤ log (1+k/t) := log_nonneg (by linarith only [div_pos hk ht])
  have hz : offset D k t ≤ D := sub_le_self _ wh
  refine ⟨hl,hh,Finset.disjoint_left.mpr (fun p h₁ h₂ => ?_),?_⟩
  · linarith only [(low_energy ht h₁).2.2,(high_energy hk ht h₂).2.1,hsep]
  · intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · obtain ⟨hP,ha,hb⟩ := low_energy ht h
      exact ⟨hP,ha,by linarith only [hb,hsep,hz]⟩
    · obtain ⟨hP,ha,hb⟩ := high_energy hk ht h
      exact ⟨hP,by linarith only [wl,hsep,ha],hb⟩

/-- Upper-to-lower packet odds in the infinite-translation limit. -/
def odds (D k b : ℝ) := k*exp ((1-b)*D)

def upperProbability (D k b : ℝ) := odds D k b/(1+odds D k b)

theorem odds_pos (D : ℝ) {k : ℝ} (hk : 0 < k) (b : ℝ) : 0 < odds D k b := mul_pos hk (exp_pos _)

theorem low_mass (b : ℝ) :
    Tendsto (fun t => scale t*mass (shifted b t) (low t)) atTop (𝓝 1) := by
  simpa only [low,mul_zero,exp_zero,one_mul] using mass_limit (tendsto_const_nhds (x := (0:ℝ))) zero_lt_one b

theorem high_mass (D : ℝ) {k : ℝ} (hk : 0 < k) (b : ℝ) :
    Tendsto (fun t => scale t*mass (shifted b t) (high D k t)) atTop (𝓝 (odds D k b)) :=
  mass_limit (offset_limit D k) hk b

theorem both_mass {D k : ℝ} (hD : 0 < D) (hk : 0 < k) (b : ℝ) :
    Tendsto (fun t => scale t*mass (shifted b t) (both D k t)) atTop (𝓝 (1+odds D k b)) := by
  apply ((low_mass b).add (high_mass D hk b)).congr'
  filter_upwards [windows hD hk] with t hw
  simp only [both,mass,Finset.sum_union hw.2.2.1,mul_add]

theorem upper_limit {D k : ℝ} (hD : 0 < D) (hk : 0 < k) (b : ℝ) :
    Tendsto (fun t => share (shifted b t) (both D k t) (high D k t)) atTop (𝓝 (upperProbability D k b)) := by
  apply ((high_mass D hk b).div (both_mass hD hk b) (add_pos zero_lt_one (odds_pos D hk b)).ne').congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  exact mul_div_mul_left _ _ (div_pos (sq_pos_of_pos ht) (exp_pos t)).ne'

#print axioms windows
#print axioms upper_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets
