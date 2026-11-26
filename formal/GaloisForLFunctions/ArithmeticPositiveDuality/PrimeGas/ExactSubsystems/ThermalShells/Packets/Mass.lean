import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Counts
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Temperatures

/-! # Gibbs mass of a thin prime packet -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets

open Real Filter Topology _root_.RHTower.Sieve

/-- Removing the common energy translation leaves every conditional probability unchanged. -/
def shifted (b t : ℝ) (p : ℕ) := exp (-b*(log (p:ℝ)-t))

theorem shifted_pos (b t : ℝ) (p : ℕ) : 0 < shifted b t p := exp_pos _

theorem packet_energy {t v a : ℝ} (ht : 0 < t) (ha : 0 < a) {p : ℕ} (hp : p ∈ packet t v a) :
    p.Prime ∧ t+v < log (p:ℝ) ∧ log (p:ℝ) ≤ t+v+log (1+a/t) := by
  obtain ⟨hP,hlo,hhi⟩ := mem_primesIn (exp_pos _).le hp
  have hl := log_lt_log (exp_pos _) hlo
  have hu := log_le_log ((exp_pos _).trans hlo) hhi
  rw [log_exp] at hl
  rw [log_mul (exp_pos _).ne' (by positivity : (1+a/t:ℝ) ≠ 0),log_exp] at hu
  exact ⟨hP,hl,hu⟩

theorem packet_weight_bounds (b : ℝ) {t v a : ℝ} (ht : 0 < t) (ha : 0 < a)
    {p : ℕ} (hp : p ∈ packet t v a) :
    exp (-b*v-|b| * log (1+a/t)) ≤ shifted b t p ∧
      shifted b t p ≤ exp (-b*v+|b| * log (1+a/t)) := by
  obtain ⟨hl,hu⟩ := (packet_energy ht ha hp).2
  have err : |(-b*(log (p:ℝ)-t))-(-b*v)| ≤ |b| * log (1+a/t) := by
    rw [show -b*(log (p:ℝ)-t)-(-b*v) = -b*(log (p:ℝ)-(t+v)) by ring,
      abs_mul,abs_neg,abs_of_nonneg (sub_nonneg.mpr hl.le)]
    exact mul_le_mul_of_nonneg_left (by linarith only [hu]) (abs_nonneg _)
  constructor <;> apply exp_le_exp.mpr
  · linarith only [(abs_le.mp err).1]
  · linarith only [(abs_le.mp err).2]

private theorem mass_bounds (b t v a : ℝ) (ht : 0 < t) (ha : 0 < a) :
    let S := packet t v a
    let ε := |b| * log (1+a/t)
    (S.card:ℝ)*exp (-b*v-ε) ≤ mass (shifted b t) S ∧
      mass (shifted b t) S ≤ (S.card:ℝ)*exp (-b*v+ε) := by
  dsimp only
  have hl p (hp : p ∈ packet t v a) := (packet_weight_bounds b ht ha hp).1
  have hu p (hp : p ∈ packet t v a) := (packet_weight_bounds b ht ha hp).2
  exact ⟨by simpa only [mass,Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum hl,
    by simpa only [mass,Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum hu⟩

/-- The Gibbs exponent tilts translated prime density a exp(V) to a exp((1-b)V). -/
theorem mass_limit {v : ℝ → ℝ} {V a : ℝ} (hv : Tendsto v atTop (𝓝 V)) (ha : 0 < a) (b : ℝ) :
    Tendsto (fun t => scale t*mass (shifted b t) (packet t (v t) a)) atTop (𝓝 (a*exp ((1-b)*V))) := by
  have hc := count_limit hv ha
  have hm := hv.const_mul (-b)
  have he := (logWidth_limit a).const_mul |b|
  rw [mul_zero] at he
  have lo := hm.sub he
  have hi := hm.add he
  rw [sub_zero] at lo
  rw [add_zero] at hi
  have z : a*exp V*exp (-b*V) = a*exp ((1-b)*V) := by
    rw [mul_assoc,← exp_add]; congr 2; ring
  have h₁ := hc.mul ((continuous_exp.tendsto _).comp lo)
  have h₂ := hc.mul ((continuous_exp.tendsto _).comp hi)
  rw [z] at h₁ h₂
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h₁ h₂
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    simpa only [Function.comp_apply,mul_assoc] using
      mul_le_mul_of_nonneg_left (mass_bounds b t (v t) a ht ha).1 (scale_nonneg t)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    simpa only [Function.comp_apply,mul_assoc] using
      mul_le_mul_of_nonneg_left (mass_bounds b t (v t) a ht ha).2 (scale_nonneg t)

#print axioms packet_energy
#print axioms mass_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets
