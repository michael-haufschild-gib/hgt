import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticNotchGoodScales
import GaloisForLFunctions.RHTower.WeilWorkExposingRaySublogEnvelope
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Simultaneous arithmetic scales from actual weighted separators

Square blocks package both cumulative coefficient masses into one
nonnegative sequence. Its shifted harmonic envelope is bounded by the
original envelope at N and N squared. The corpus good-scale theorem then
selects the SAME arbitrarily late cutoff for both remote error terms.

The capstone applies the envelope already derived from an actual weighted
polar spectral separator. No extra coefficient growth or sign assumption
is imposed. This supplies the two-scale input for exact weighted fibre
recovery; it is not the universal WP02 energy inequality.

Paper: docs/reports/weil-work/results/02-exposing-ray/SUBHALF-LOG-FIBRE-PROOF.md,
section4a.
-/

open Finset Filter Topology Set MeasureTheory
noncomputable section
namespace RHTower.ExposingRayTransfer
open WeilOneSided

private theorem sum_successors (a : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ range N, a (j+1)) = ∑ m ∈ Finset.Ioc 0 N, a m := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, sum_Ioc_succ_top (Nat.zero_le N), ih]

private theorem sum_square_blocks (a : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ range N, ∑ m ∈ Finset.Ioc (j^2) ((j+1)^2), a m) = ∑ m ∈ Finset.Ioc 0 (N^2), a m := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    exact sum_Ioc_consecutive a (Nat.zero_le _) (by
      simp only [pow_two,Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.one_mul]
      omega)

private def squareBlockWeight (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  a (j+1)+(∑ m ∈ Finset.Ioc (j^2) ((j+1)^2), a m)/Real.sqrt ((j:ℝ)+1)

private theorem squareBlockWeight_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (j : ℕ) :
    0 ≤ squareBlockWeight a j := by
  unfold squareBlockWeight
  exact add_nonneg (ha _) (div_nonneg (sum_nonneg fun m _ => ha m) (Real.sqrt_nonneg _))

private theorem squareBlockWeight_mass {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (N : ℕ) :
    (∑ m ∈ Finset.Ioc 0 N, a m)+(∑ m ∈ Finset.Ioc 0 (N^2), a m)/Real.sqrt N ≤
      ∑ j ∈ range N, squareBlockWeight a j := by
  simp only [squareBlockWeight, sum_add_distrib]
  rw [sum_successors, ← sum_square_blocks a N, sum_div]
  apply add_le_add le_rfl
  apply sum_le_sum
  intro j hj
  have hjN : (j:ℝ)+1 ≤ N := by exact_mod_cast (show j+1 ≤ N by have := mem_range.mp hj; omega)
  exact div_le_div_of_nonneg_left (sum_nonneg fun m _ => ha m)
    (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_le_sqrt hjN)

private theorem squareBlockWeight_harmonic {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (N : ℕ) :
    (∑ j ∈ range N, (Real.sqrt ((j:ℝ)+1))⁻¹*squareBlockWeight a j) ≤
      (∑ m ∈ Finset.Ioc 0 N, a m/Real.sqrt m)+
        (∑ m ∈ Finset.Ioc 0 (N^2), a m/Real.sqrt m) := by
  have hpoint (j : ℕ) : (Real.sqrt ((j:ℝ)+1))⁻¹*squareBlockWeight a j ≤
      a (j+1)/Real.sqrt ((j:ℝ)+1)+
        ∑ m ∈ Finset.Ioc (j^2) ((j+1)^2), a m/Real.sqrt m := by
    have hj : 0 < (j:ℝ)+1 := by positivity
    have hs := Real.sqrt_pos.mpr hj
    have he : (Real.sqrt ((j:ℝ)+1))⁻¹*squareBlockWeight a j =
        a (j+1)/Real.sqrt ((j:ℝ)+1)+(∑ m ∈ Finset.Ioc (j^2) ((j+1)^2), a m)/((j:ℝ)+1) := by
      unfold squareBlockWeight
      field_simp [hs.ne',hj.ne']
      linear_combination -(∑ m ∈ Finset.Ioc (j^2) ((j+1)^2), a m)*(Real.sq_sqrt hj.le)
    rw [he, sum_div]
    apply add_le_add le_rfl
    apply sum_le_sum
    intro m hm
    have hmpos : 0 < (m:ℝ) := by
      exact_mod_cast (show 0 < m by have := (Finset.mem_Ioc.mp hm).1; omega)
    have hms : Real.sqrt (m:ℝ) ≤ (j:ℝ)+1 := by
      apply (Real.sqrt_le_iff).mpr
      refine ⟨hj.le, ?_⟩
      exact_mod_cast (Finset.mem_Ioc.mp hm).2
    exact div_le_div_of_nonneg_left (ha m) (Real.sqrt_pos.mpr hmpos) hms
  have h := sum_le_sum fun j (_ : j∈range N) => hpoint j
  rw [sum_add_distrib, sum_square_blocks] at h
  have he : (∑ j ∈ range N, a (j+1)/Real.sqrt ((j:ℝ)+1)) =
      ∑ m ∈ Finset.Ioc 0 N, a m/Real.sqrt m := by
    simpa only [Nat.cast_add,Nat.cast_one] using sum_successors (fun m => a m/Real.sqrt m) N
  rwa [he] at h

/-- A sublogarithmic harmonic envelope gives the SAME arbitrarily late
cutoff for both square-root mass at N and ordinary mass at N squared. -/
theorem exists_two_scale_small_mass {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hsmall : ∀ η : ℝ, 0 < η → ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ m ∈ Finset.Ioc 0 N, a m/Real.sqrt m) ≤ A+η*Real.log N)
    {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ K ≤ N ∧
      (∑ m ∈ Finset.Ioc 0 N, a m)/Real.sqrt N+(∑ m ∈ Finset.Ioc 0 (N^2), a m)/(N:ℝ) < ε := by
  have hw : ∀ η : ℝ, 0 < η → ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ,
      (∑ j ∈ range (N+1), (Real.sqrt ((j:ℝ)+1))⁻¹*squareBlockWeight a j) ≤
        A+η*Real.log ((N:ℝ)+1) := by
    intro η hη
    obtain ⟨A,hA,hbound⟩ := hsmall (η/3) (by positivity)
    refine ⟨2*A,by positivity,fun N => ?_⟩
    have h1 := hbound (N+1) (by omega)
    have hNN : 1 ≤ (N+1)^2 := by
      have hp : 0 < (N+1)^2 := by positivity
      omega
    have h2 := hbound ((N+1)^2) hNN
    have hW := squareBlockWeight_harmonic ha (N+1)
    rw [Nat.cast_pow,Real.log_pow] at h2
    push_cast at h1 h2
    linarith
  obtain ⟨J,hJ,hJsmall⟩ := WeilSingularArithmetic.exists_small_sqrt_mass_of_sublog_envelope
    (squareBlockWeight_nonneg ha) hw hε K
  refine ⟨J+1,by omega,by omega,?_⟩
  have hmass := (squareBlockWeight_mass ha (J+1)).trans_lt hJsmall
  have hs : 0 < Real.sqrt ((J:ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
  have hj : 0 < (J:ℝ)+1 := by positivity
  have he : (∑ m ∈ Finset.Ioc 0 (J+1), a m)/Real.sqrt ((J+1:ℕ):ℝ)+
      (∑ m ∈ Finset.Ioc 0 ((J+1)^2), a m)/((J+1:ℕ):ℝ) =
      ((∑ m ∈ Finset.Ioc 0 (J+1), a m)+
        (∑ m ∈ Finset.Ioc 0 ((J+1)^2), a m)/Real.sqrt ((J:ℝ)+1))/Real.sqrt ((J:ℝ)+1) := by
    push_cast
    field_simp [hs.ne',hj.ne']
    linear_combination (∑ m ∈ Finset.Ioc 0 ((J+1)^2), a m)*(Real.sq_sqrt hj.le)
  rw [he]
  apply (div_lt_iff₀ hs).mpr
  simpa only [Nat.cast_add,Nat.cast_one] using hmass

private theorem exists_affine_power_bound {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    {C : ℝ} (hC : 0 ≤ C) {η : ℝ} (hη : 0 < η) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 0 ≤ x → C*(1+x)^θ ≤ A+η*x := by
  have ht : Tendsto (fun x : ℝ => C*x^(θ-1)) atTop (𝓝 0) := by
    simpa only [neg_sub,mul_zero] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hθ1)).const_mul C
  have he : ∀ᶠ x : ℝ in atTop, C*x^(θ-1) < η := ht.eventually (Iio_mem_nhds hη)
  obtain ⟨T,hT⟩ := eventually_atTop.mp he
  let U := max T 1
  have hU : 0 < U := lt_of_lt_of_le zero_lt_one (le_max_right T 1)
  refine ⟨C*U^θ+η,by positivity,fun x hx => ?_⟩
  by_cases hlarge : U ≤ 1+x
  · have hbound := hT (1+x) ((le_max_left T 1).trans hlarge)
    have hp : 0 < 1+x := by positivity
    have hmul : C*(1+x)^θ < η*(1+x) := by
      have h := mul_lt_mul_of_pos_right hbound hp
      rw [Real.rpow_sub_one hp.ne',mul_assoc,div_mul_cancel₀ _ hp.ne'] at h
      exact h
    have hbase : 0 ≤ C*U^θ := mul_nonneg hC (Real.rpow_nonneg hU.le θ)
    linarith
  · have hr := Real.rpow_le_rpow (by positivity : 0 ≤ 1+x) (le_of_not_ge hlarge) hθ
    have hb := mul_le_mul_of_nonneg_left hr hC
    have hh := mul_nonneg hη.le hx
    linarith

/-- Power envelopes with exponent strictly below one supply simultaneous
smallness on both arithmetic scales. -/
theorem exists_two_scale_small_mass_of_power {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {C θ : ℝ} (hC : 0 ≤ C) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hbound : ∀ N : ℕ, 1 ≤ N →
      (∑ m ∈ Finset.Ioc 0 N, a m/Real.sqrt m) ≤ C*(1+Real.log N)^θ)
    {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ K ≤ N ∧
      (∑ m ∈ Finset.Ioc 0 N, a m)/Real.sqrt N+(∑ m ∈ Finset.Ioc 0 (N^2), a m)/(N:ℝ) < ε := by
  apply exists_two_scale_small_mass ha ?_ hε K
  intro η hη
  obtain ⟨A,hA,hpow⟩ := exists_affine_power_bound hθ hθ1 hC hη
  refine ⟨A,hA,fun N hN => (hbound N hN).trans ?_⟩
  exact hpow _ (Real.log_nonneg (by exact_mod_cast hN))

private theorem sum_cutoff_abs (b : ℕ → ℝ) (g : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (if 2 ≤ n then |b n| else 0)*g n) =
      ∑ n ∈ Finset.Icc 2 N, |b n| *g n := by
  classical
  have hsub : Finset.Icc 2 N ⊆ Finset.Ioc 0 N := by
    intro n hn
    obtain ⟨hn2,hnN⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Ioc.mpr ⟨by omega,hnN⟩
  have he : (∑ n ∈ Finset.Icc 2 N, (if 2 ≤ n then |b n| else 0)*g n) =
      ∑ n ∈ Finset.Ioc 0 N, (if 2 ≤ n then |b n| else 0)*g n := by
    apply sum_subset hsub
    intro n hn hnot
    have hn2 : ¬2 ≤ n := fun h => hnot (Finset.mem_Icc.mpr ⟨h,(Finset.mem_Ioc.mp hn).2⟩)
    simp [hn2]
  rw [← he]
  exact sum_congr rfl fun n hn => by rw [if_pos (Finset.mem_Icc.mp hn).1]

/-- Actual polar weighted separators admit arbitrarily late cutoffs that
simultaneously control the two remote arithmetic correlation windows. -/
theorem exists_small_two_scales_of_polar_log_bound {β : ℝ}
    (hβ : 0 ≤ β) (hβhalf : β < 1/2)
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 hβ (by linarith) f))
    {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ K ≤ N ∧
      (∑ n ∈ Finset.Icc 2 N, |b n|)/Real.sqrt N+(∑ n ∈ Finset.Icc 2 (N^2), |b n|)/(N:ℝ) < ε := by
  obtain ⟨C,hC,θ,hθ,hθ1,hbound⟩ := exists_sublog_envelope_of_polar_log_bound hβ hβhalf h
  let a : ℕ → ℝ := fun n => if 2 ≤ n then |b n| else 0
  have ha : ∀ n, 0 ≤ a n := by intro n; dsimp [a]; split_ifs <;> positivity
  have hsum (N : ℕ) : (∑ n ∈ Finset.Ioc 0 N, a n) = ∑ n ∈ Finset.Icc 2 N, |b n| := by
    simpa only [mul_one] using sum_cutoff_abs b (fun _ => 1) N
  have hharm (N : ℕ) : (∑ n ∈ Finset.Ioc 0 N, a n/Real.sqrt n) =
      ∑ n ∈ Finset.Icc 2 N, |b n|/Real.sqrt n := by
    simpa only [div_eq_mul_inv] using sum_cutoff_abs b (fun n => (Real.sqrt n)⁻¹) N
  have hb (N : ℕ) (hN : 1 ≤ N) :
      (∑ n ∈ Finset.Ioc 0 N, a n/Real.sqrt n) ≤ C*(1+Real.log N)^θ := by
    rw [hharm]
    by_cases hn2 : 2 ≤ N
    · exact hbound N hn2
    · have hn1 : N=1 := by omega
      subst N
      simp only [Nat.cast_one,Real.log_one,add_zero,Real.one_rpow]
      simpa using hC.le
  obtain ⟨N,hN,hKN,hsmall⟩ := exists_two_scale_small_mass_of_power ha hC.le hθ.le hθ1 hb hε (max K 2)
  refine ⟨N,(le_max_right K 2).trans hKN,(le_max_left K 2).trans hKN,?_⟩
  simpa only [hsum] using hsmall

end RHTower.ExposingRayTransfer
