import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpanningRecords.PhysicalSteps
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FirstCrossing

/-! # Physical-time spacing of successive genuine spanning-budget excursions -/

open Set Filter MeasureTheory Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpanningRecords
open RepeatedGates.PhysicalBlocks PrecisionReturns SharpOccupation
noncomputable section

private theorem wait_totals (t u : ℕ → ℝ) (hu : ∀ i, u i∈Icc (0:ℝ) 1) (n : ℕ) :
    let W := ∑ i∈range n, (t (i+1)-(t i+u i))
    t n-t 0-(n:ℝ)≤W ∧ W≤t n-t 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ,Nat.cast_succ]
    constructor <;> linarith only [ih.1,ih.2,(hu n).1,(hu n).2]

/-- Start at the actual first low dip after the near-Hilbert crossing.
Thereafter the first passage above the spanning budget and the next
first low visit give sharp mean spacing in physical time. All eligible
choices of excess budget and crossing height give the same visit dates.
Subtracting the actual ascent on each step preserves the sharp exponential base. -/
theorem gaussian_robust_excursion_spacing :
    ∃ c>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ l b : ℝ, 0<l → l<physicalArc (1/10) → physicalArc (1/10)<b →
      ∀ᶠ k : ℕ in atTop, let N := k+3
        let H := prefix ω (k+1)
        let P := nearHilbertContinuousCircuitBudget N
        ∃ σ>0, orbitCircuitDistance H P σ=9/80 ∧ (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
          ∀ s : ℕ, ((2*s:ℕ):ℝ)≤c*(k+2:ℕ) →
            let v := firstVisit H σ s (1/10)
            ∃ t : ℕ → ℝ, t 0=v ∧ (∀ i, ∀ (q : ℕ) (η : ℝ),
              ((2*s+q:ℕ):ℝ)≤c*(k+2:ℕ) → η∈Icc (9/80:ℝ) (1/8) →
              let u := firstExcessAfter ω (k+1) (s+q) (t i) η
              0<u ∧ u≤1 ∧ orbitCircuitDistance H (k+2+(s+q)) (t i+u)=η ∧
                (∀ h∈Ico 0 u, orbitCircuitDistance H (k+2+(s+q)) (t i+h)<η) ∧
                t (i+1)=firstVisit H (t i+u) s (1/10)) ∧
              ∀ u : ℕ → ℝ, (∀ i, u i∈Icc (0:ℝ) 1) → ∀ᶠ n : ℕ in atTop,
                let W := ∑ i∈range n, (t (i+1)-(t i+u i))
                1/b^(2^N) < W/n ∧ W/n < 1/l^(2^N) := by
  obtain ⟨c,hc,g,hg,hstep⟩ := gaussian_exact_robust_step
  obtain ⟨_,hcross⟩ := gaussian_hilbert_first_crossing
  let c' := min c 1
  have he : (1/10:ℝ)∈Ioo (0:ℝ) (Real.sqrt 2) := by
    constructor
    · norm_num
    · exact (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  refine ⟨c',lt_min hc zero_lt_one,?_⟩
  filter_upwards [hstep,hcross,gaussian_physical_return_rates] with ω hsteps hσ hrate
  intro l b hl hlx hxb
  let x := physicalArc (1/10)
  have hx := (physicalArc_spec he.1 he.2).1
  have hx1 : x<1 := hx.2.trans (by norm_num)
  obtain ⟨a,hxa,ham⟩ := exists_between (lt_min hxb hx1)
  have ha := hx.1.trans hxa
  have hab := ham.trans_le (min_le_left ..)
  have ha1 := ham.trans_le (min_le_right ..)
  have hr := hrate (fun n => n^1) (polynomial_subcritical 1) _ he l a hl hlx hxa
  have hdim : Tendsto (fun k : ℕ => (2:ℕ)^(k+3)) atTop atTop :=
    tendsto_atTop_mono (fun k => (show k≤k+3 by omega).trans (Nat.lt_two_pow_self (n:=k+3)).le) tendsto_id
  have hba : 1<b/a := (lt_div_iff₀ ha).mpr (by simpa only [one_mul] using hab)
  have ha' : 1<1/a := (lt_div_iff₀ ha).mpr (by simpa only [one_mul] using ha1)
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hsteps,hσ,hr,eventually_ge_atTop g,
    ((tendsto_pow_atTop_atTop_of_one_lt hba).comp hdim).eventually_gt_atTop 2,
    ((tendsto_pow_atTop_atTop_of_one_lt ha').comp hdim).eventually_gt_atTop 2] with k hk hσk hrk hgk hslack hsize
  intro N H P
  have hp : P≤2^N/(16*(N+1)) := by
    apply Nat.div_le_div_left <;> dsimp [P,nearHilbertContinuousCircuitBudget,N] <;> omega
  obtain ⟨σ,hpos,hcσ,hpre,_⟩ := hσk P hp
  refine ⟨σ,hpos,hcσ,hpre,?_⟩
  intro s hs v
  have hN : (0:ℝ)≤(k+2:ℕ) := by positivity
  have hsn : s≤N^1 := by
    have ht := hs.trans (mul_le_mul_of_nonneg_right (min_le_right c (1:ℝ)) hN)
    rw [one_mul] at ht
    have hh : 2*s≤k+2 := by exact_mod_cast ht
    simp only [pow_one]; dsimp only [N]; omega
  obtain ⟨t,hrec,hmean⟩ := (hrk s hsn v).2
  have hfit (i : ℕ) : HasProjectiveCircuitApproximation N (1/10) s (unitaryEvolution H.val (t i)) := by
    cases i with
    | zero => rw [hrec.1]; exact (firstVisit_isLeast H σ s (by norm_num : (0:ℝ)<1/10)).1.2
    | succ i => exact (hrec.2 i).1.2
  have hlog : 1≤Nat.log g (k+1) :=
    (Nat.le_log_iff_pow_le hg (by omega)).mpr (by simpa only [pow_one] using hgk.trans (Nat.le_succ k))
  refine ⟨t,hrec.1,?_,?_⟩
  · intro i q η hq hη u
    have hh := hk (t i) s q η hη (hq.trans (mul_le_mul_of_nonneg_right (min_le_left c (1:ℝ)) hN)) (hfit i)
    refine ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,?_⟩
    have hd := hh.2.2.2.2 1 ⟨le_rfl,by exact_mod_cast hlog⟩
    exact ((hrec.2 i).unique (firstVisit_isLeast H (t i+1) s (by norm_num : (0:ℝ)<1/10))).trans hd.symm
  · intro u hu
    let D := 2^N
    change 2<(b/a)^D at hslack
    change 2<(1/a)^D at hsize
    rw [div_pow] at hslack
    rw [div_pow,one_pow] at hsize
    have hsep : (1:ℝ)/b^D < (1/a^D)/2 := by
      rw [div_div]
      apply one_div_lt_one_div_of_lt (by positivity)
      rw [mul_comm (a^D) 2]
      exact (lt_div_iff₀ (pow_pos ha D)).mp hslack
    filter_upwards [hmean,eventually_gt_atTop (0:ℕ)] with n hn hn'
    have hn0 : (0:ℝ)<n := by exact_mod_cast hn'
    let W := ∑ i∈range n, (t (i+1)-(t i+u i))
    obtain ⟨hw,hw'⟩ := wait_totals t u hu n
    rw [hrec.1] at hw hw'
    have hlow := div_le_div_of_nonneg_right hw hn0.le
    rw [sub_div,div_self hn0.ne'] at hlow
    exact ⟨by linarith only [hn.1,hsep,hsize,hlow],
      (div_le_div_of_nonneg_right hw' hn0.le).trans_lt hn.2⟩

#print axioms gaussian_robust_excursion_spacing
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpanningRecords

