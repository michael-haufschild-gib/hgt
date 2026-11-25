import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.Iterated.PhysicalCharge

/-! # Mean elapsed time from genuine near-Hilbert crossings to the following low visits -/

open Set Filter MeasureTheory Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.Iterated
noncomputable section

def totalRise (v σ : ℕ → ℝ) (n : ℕ) := ∑ i ∈ range n, (σ i-v i)
def totalWait (v σ : ℕ → ℝ) (n : ℕ) := ∑ i ∈ range n, (v (i+1)-σ i)

/-- Rising and waiting parts partition the entire elapsed record. -/
theorem cycle_telescope (v σ : ℕ → ℝ) (n : ℕ) : totalRise v σ n+totalWait v σ n=v n-v 0 := by
  induction n with
  | zero => simp [totalRise,totalWait]
  | succ n ih =>
    simp only [totalRise,totalWait,Finset.sum_range_succ] at ih ⊢
    linarith only [ih]

/-- Every finite record satisfies the time balance. Its error depends
on the frozen prefix but is independent of the number of excursions.
The included first wait starts at the canonical crossing from identity. -/
theorem gaussian_finite_wait_balance :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let N := k+3
      let D := 2^N
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let G := (2:ℝ)^(D^c)
      let E := (2:ℝ)^(7*D/16)
      ∀ s≤P/2, let v := lowDate H P s
        let σ := highDate H P s
        (∀ i : ℕ, v i<σ i ∧ orbitCircuitDistance H P (σ i)=9/80 ∧
          IsLeast {t | v i≤t ∧ 9/80≤orbitCircuitDistance H P t} (σ i) ∧
          IsLeast {t | σ i≤t ∧ HasProjectiveCircuitApproximation N (1/10) s (unitaryEvolution H.val t)} (v (i+1)) ∧
          1<v (i+1)-σ i ∧ v (i+1)-σ i≤G) ∧
        ∀ n : ℕ, (n:ℝ)*E+(E-1)*totalRise v σ n≤totalWait v σ n+G ∧ totalWait v σ n≤n*G := by
  obtain ⟨c,h⟩ := gaussian_cycle_windows
  refine ⟨c,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw] with k hk
  intro N D H P G E s hs v σ
  obtain ⟨hd,hcharge⟩ := hk s hs
  refine ⟨hd,?_⟩
  intro n
  have gain := hcharge 0 (7*D/16) n (by
    simp only [zero_add]; rw [Nat.mul_comm 16]; exact Nat.div_mul_le_self ..)
  have hmin (i : ℕ) : min (1:ℝ) (v (i+1)-σ i)=1 := min_eq_left (hd i).2.2.2.2.1.le
  change (2:ℝ)^(7*D/16)*(∑ i∈range n, ((σ i-v i)+min ((2:ℝ)^0) (v (i+1)-σ i)))≤v n+G at gain
  simp only [pow_zero,hmin,sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at gain
  have htel := cycle_telescope v σ n
  rw [show v 0=0 from rfl,sub_zero] at htel
  change E*(totalRise v σ n+n)≤v n+G at gain
  constructor
  · rw [←htel] at gain
    linarith only [show E*totalRise v σ n+E*n≤totalRise v σ n+totalWait v σ n+G by
      rwa [mul_add] at gain]
  · calc
      _ ≤ ∑ _i∈range n, G := Finset.sum_le_sum fun i _ => (hd i).2.2.2.2.2
      _ = _ := by simp

/-- The mean of the actual elapsed waits lies on the doubly exponential
scale for every budget through half the near-Hilbert budget. The limit
in excursion count is taken on each frozen prefix. -/
theorem gaussian_mean_wait_bounds :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let N := k+3
      let D := 2^N
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∀ s≤P/2, ∀ᶠ n : ℕ in atTop,
        let mean := totalWait (lowDate H P s) (highDate H P s) n / n
        (2:ℝ)^(7*D/16)-1 < mean ∧ mean ≤ (2:ℝ)^(D^c) := by
  obtain ⟨c,h⟩ := gaussian_finite_wait_balance
  refine ⟨c,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw] with k hk
  intro N D H P s hs
  let E := (2:ℝ)^(7*D/16)
  let G := (2:ℝ)^(D^c)
  let v := lowDate H P s
  let σ := highDate H P s
  obtain ⟨hd,hb⟩ := hk s hs
  obtain ⟨m,hm⟩ := exists_nat_gt G
  filter_upwards [eventually_ge_atTop m] with n hn
  have hG : G<(n:ℝ) := hm.trans_le (by exact_mod_cast hn)
  have hpos : (0:ℝ)<n := (show 0<G by dsimp only [G]; positivity).trans hG
  have hr : 0≤totalRise v σ n := Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hd i).1.le
  have hc : 0≤(E-1)*totalRise v σ n := mul_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num))) hr
  have hl := (hb n).1
  have hu := (hb n).2
  change _<totalWait v σ n/n ∧ totalWait v σ n/n≤G
  exact ⟨(lt_div_iff₀ hpos).mpr (by linarith only [hl,hc,hG]),(div_le_iff₀ hpos).mpr (by simpa only [mul_comm G] using hu)⟩

#print axioms gaussian_mean_wait_bounds
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.Iterated

