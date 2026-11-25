import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.Iterated.MeanWait
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance

/-! # The sharp occupation base as a lower bound for true elapsed waits -/

open Set Filter MeasureTheory Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.Iterated
open SharpOccupation
noncomputable section

/-- Subcritical budgets eventually fit within half the near-Hilbert budget. -/
theorem eventually_half_budget {S : ℕ → ℕ} (hs : subcriticalBudget S) :
    ∀ᶠ n : ℕ in atTop, S n ≤ nearHilbertContinuousCircuitBudget n/2 := by
  filter_upwards [hs.eventually_lt_const (by norm_num : (0:ℝ)<1/128)] with n hn
  have hh := (div_lt_iff₀ (by positivity : 0<(2:ℝ)^n)).mp hn
  apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
  apply (Nat.le_div_iff_mul_le (by positivity : 0<64*(n+1))).mpr
  exact_mod_cast (show (S n:ℝ)*2*(64*((n:ℝ)+1))≤(2:ℝ)^n by
    nlinarith only [hh,Nat.cast_nonneg (α:=ℝ) n])

/-- For every subcritical budget, including every polynomial budget,
the mean of the actual post-crossing waits has lower exponential base
at least the inverse scalar arc width. The time before each crossing
has been subtracted, including in the first excursion. -/
theorem gaussian_subcritical_mean_wait :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ S : ℕ → ℕ, subcriticalBudget S →
      ∀ b : ℝ, physicalArc (1/10)<b → ∀ᶠ k : ℕ in atTop, let N := k+3
        let D := 2^N
        let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
        let P := nearHilbertContinuousCircuitBudget N
        ∀ s≤S N, ∀ᶠ n : ℕ in atTop,
          (1:ℝ)/b^D < totalWait (lowDate H P s) (highDate H P s) n/n := by
  obtain ⟨c,hbal⟩ := gaussian_finite_wait_balance
  filter_upwards [hbal,gaussian_physical_return_rates] with ω hw hrec
  intro S hs b hb
  have he : (1/10:ℝ)∈Ioo (0:ℝ) (Real.sqrt 2) := by
    constructor
    · norm_num
    · exact (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hx := (physicalArc_spec he.1 he.2).1.1
  obtain ⟨a,hxa,hab⟩ := exists_between hb
  have ha := hx.trans hxa
  have hr := hrec S hs _ he (physicalArc (1/10)/2) a (half_pos hx) (half_lt_self hx) hxa
  have hdim : Tendsto (fun k : ℕ => (2:ℕ)^(k+3)) atTop atTop :=
    tendsto_atTop_mono (fun k => (show k≤k+3 by omega).trans (Nat.lt_two_pow_self (n:=k+3)).le) tendsto_id
  have hratio : 1<b/a := (lt_div_iff₀ ha).mpr (by rwa [one_mul])
  filter_upwards [hw,hr,(tendsto_add_atTop_nat 3).eventually (eventually_half_budget hs),
    ((tendsto_pow_atTop_atTop_of_one_lt hratio).comp hdim).eventually_gt_atTop 2] with k hk hrk hcap hslack
  intro N D H P s hS
  let v := lowDate H P s
  let σ := highDate H P s
  let E := (2:ℝ)^(7*D/16)
  let G := (2:ℝ)^(D^c)
  have hD : 8≤D := by
    dsimp only [D,N]
    exact Nat.pow_le_pow_right (by decide : 0<2) (by omega : 3≤k+3)
  have hE : (4:ℝ)≤E := by
    calc
      (4:ℝ) = 2^2 := by norm_num
      _ ≤ E := pow_le_pow_right₀ (by norm_num) (by omega : 2≤7*D/16)
  obtain ⟨hd,hbalance⟩ := hk s (hS.trans hcap)
  obtain ⟨r,hrec',hr'⟩ := (hrk s hS 0).2
  have inc (i : ℕ) : v i+1≤v (i+1) := by have H := hd i; linarith only [H.1,H.2.2.2.2.1]
  have hnv (n : ℕ) : (n:ℝ)≤v n := by
    induction n with
    | zero => change (↑(0:ℕ):ℝ)≤0; norm_num
    | succ n ih => exact_mod_cast (show (n:ℝ)+1≤v (n+1) from (add_le_add_left ih 1).trans (inc n))
  have hrv (n : ℕ) : r n≤v n := by
    induction n with
    | zero => exact hrec'.1.le
    | succ n ih => exact (hrec'.2 n).2 ⟨(add_le_add_left ih 1).trans (inc n),low_visit H P s (n+1)⟩
  obtain ⟨m,hm⟩ := exists_nat_gt G
  filter_upwards [hr',eventually_ge_atTop m] with n hn hmn
  have hnG : G<(n:ℝ) := hm.trans_le (by exact_mod_cast hmn)
  have hn0 := (show 0<G by dsimp only [G]; positivity).trans hnG
  have hR : 0≤totalRise v σ n := Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hd i).1.le
  have htel := cycle_telescope v σ n
  rw [show v 0=0 from rfl,sub_zero] at htel
  have hhalf : v n≤2*totalWait v σ n := by
    have h1 := (hbalance n).1
    change (n:ℝ)*E+(E-1)*totalRise v σ n≤totalWait v σ n+G at h1
    nlinarith only [h1,htel,hnG,hnv n,
      mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) (by linarith only [hE] : 0≤E),
      mul_nonneg (sub_nonneg.mpr hE) hR]
  have hlt : (1:ℝ)/a^D < v n/n := by
    have hlow := hn.1
    rw [sub_zero] at hlow
    exact hlow.trans_le (div_le_div_of_nonneg_right (hrv n) hn0.le)
  have hlast := div_le_div_of_nonneg_right hhalf hn0.le
  rw [mul_div_assoc] at hlast
  change 2<(b/a)^D at hslack
  rw [div_pow] at hslack
  have hpower := (lt_div_iff₀ (pow_pos ha D)).mp hslack
  have hsmall : (1:ℝ)/b^D < 1/(2*a^D) :=
    one_div_lt_one_div_of_lt (by positivity) hpower
  apply hsmall.trans
  rw [show (1:ℝ)/(2*a^D)=(1/a^D)/2 by ring]
  linarith only [hlt,hlast]

#print axioms gaussian_subcritical_mean_wait
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.Iterated

