import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary.Weights
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.FidelityMass

/-! # Dilution of elementary atoms at positive power index -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions.Selection

open Filter Finset Real
open scoped Topology

/-- Every reference power mass grows faster than the squared harmonic scale. -/
theorem small_inverse {b : ℝ} (hb : 0<b) (hb' : b<1) :
    Tendsto (fun N : ℕ => (log (log N))^2/powerMass b N) atTop (𝓝 0) := by
  have lim := ((log_prefactor_vanishes hb).const_mul b).div (powerMass_asymptotic hb hb') one_ne_zero
  rw [mul_zero,zero_div] at lim
  apply (lim.comp tendsto_natCast_atTop_atTop).congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hx : 1<(N:ℝ) := by exact_mod_cast (show 1<N by omega)
  change b*((log (log N))^2*log N/(N:ℝ)^b)/(powerMass b N*(b*log N)/(N:ℝ)^b)=_
  field_simp [hb.ne',(log_pos hx).ne',(rpow_pos_of_pos (one_pos.trans hx) b).ne',(powerMass_pos b N).ne']

/-- At increasing weights, every prime in the last half of the cutoff
has weight at least a fixed fraction of the largest elementary weight. -/
private theorem terminal_bound {a x : ℝ} (ha : 1≤a) (hx : 4≤x) (p : PrimeAt x) :
    Ordinary.primeProbability a x p * windowMass (1/2) (1/2) x ≤ (2:ℝ)^(a-1) := by
  have hx' : 2≤x := by linarith only [hx]
  have hhalf : 2≤(1/2:ℝ)*x := by linarith only [hx]
  have pu := ((mem_cutoff hx').mp p.property).2
  have hp := (Nat.mem_primesBelow.mp p.property).2
  have numerator : exp ((a-1)*energy (primeLabel p))=(p.val:ℝ)^(a-1) := by
    rw [rpow_def_of_pos (Nat.cast_pos.mpr hp.pos),mul_comm]
    rfl
  rw [Ordinary.primeProbability,numerator,div_mul_eq_mul_div,div_le_iff₀ (powerMass_pos a x)]
  have step (q : ℕ) (hq : q∈window (1/2) x) :
      (p.val:ℝ)^(a-1)*(q:ℝ)^((1/2:ℝ)-1) ≤ (2:ℝ)^(a-1)*(q:ℝ)^(a-1) := by
    obtain ⟨hq',half_lt,_⟩ := (mem_window hx' hhalf).mp hq
    have small : (q:ℝ)^((1/2:ℝ)-1)≤1 := by
      calc
        _ ≤ (q:ℝ)^(0:ℝ) := rpow_le_rpow_of_exponent_le (by exact_mod_cast hq'.one_lt.le) (by norm_num)
        _ = 1 := rpow_zero _
    calc
      _ ≤ (p.val:ℝ)^(a-1) := mul_le_of_le_one_right (rpow_nonneg (Nat.cast_nonneg _) _) small
      _ ≤ (2*(q:ℝ))^(a-1) := rpow_le_rpow (Nat.cast_nonneg _) (by linarith only [pu,half_lt]) (sub_nonneg.mpr ha)
      _ = _ := mul_rpow (by norm_num) (Nat.cast_nonneg _)
  calc
    _ = ∑ q ∈ window (1/2) x,(p.val:ℝ)^(a-1)*(q:ℝ)^((1/2:ℝ)-1) :=
      mul_sum _ _ _
    _ ≤ ∑ q ∈ window (1/2) x,(2:ℝ)^(a-1)*(q:ℝ)^(a-1) := sum_le_sum step
    _ = (2:ℝ)^(a-1)*windowMass a (1/2) x := (mul_sum _ _ _).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (rpow_nonneg (by norm_num) _)
      rw [windowMass_sub (show (1/2:ℝ)*x≤x by linarith only [hx])]
      exact sub_le_self _ (powerMass_pos _ _).le

/-- A uniform atom bound tends to zero even after multiplication by
the square of the harmonic scale, at every fixed positive index. -/
theorem atom_bound {a : ℝ} (ha : 0<a) :
    ∃ u : ℕ → ℝ, (∀ N, 0≤u N) ∧
      Tendsto (fun N : ℕ => (log (log N))^2*u N) atTop (𝓝 0) ∧
      ∀ᶠ N : ℕ in atTop, ∀ p : PrimeAt N, Ordinary.primeProbability a N p≤u N := by
  by_cases h : a≤1
  · let b := min a (1/2)
    have hb : 0<b := lt_min ha (by norm_num)
    have hb' : b<1 := (min_le_right _ _).trans_lt (by norm_num)
    refine ⟨fun N => 1/powerMass b N,fun N => (one_div_pos.mpr (powerMass_pos _ _)).le,?_,?_⟩
    · exact (small_inverse hb hb').congr fun _ => by ring
    · exact Eventually.of_forall fun N p => (Ordinary.primeProbability_le h N p).trans
        (one_div_le_one_div_of_le (powerMass_pos b N) (powerMass_index_mono (min_le_left _ _) N))
  · obtain ⟨d,hd,share⟩ := positive_window_share (a:=1/2) (c:=1/2) (by norm_num) (by norm_num) (by norm_num)
    let K := (2:ℝ)^(a-1)
    have hK : 0<K := rpow_pos_of_pos (by norm_num) _
    refine ⟨fun N => (K/d)/powerMass (1/2) N,fun N => (div_pos (div_pos hK hd) (powerMass_pos _ _)).le,?_,?_⟩
    · have lim := (small_inverse (b:=1/2) (by norm_num) (by norm_num)).const_mul (K/d)
      rw [mul_zero] at lim
      exact lim.congr fun _ => by ring
    · filter_upwards [tendsto_natCast_atTop_atTop.eventually share,eventually_ge_atTop 4] with N hN hn p
      have bound := (mul_le_mul_of_nonneg_left hN (Ordinary.primeProbability_nonneg a N p)).trans
        (terminal_bound (le_of_not_ge h) (by exact_mod_cast hn) p)
      apply (le_div_iff₀ (powerMass_pos _ _)).mpr
      apply (le_div_iff₀ hd).mpr
      calc
        _ = Ordinary.primeProbability a N p*(d*powerMass (1/2) N) := by ring
        _ ≤ K := bound

#print axioms small_inverse
#print axioms atom_bound

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions.Selection
