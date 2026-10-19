import GaloisForLFunctions.BiScaleUncertainty.SieveParityAmplitudeScaling
import GaloisForLFunctions.BiScaleUncertainty.SieveResonantVisibility
import GaloisForLFunctions.HTGeometry.BanachTriangularExponential

/-! Local physical Lipschitz recovery from first-order arithmetic visibility. -/

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.LinearVisibility
open ParityNeighborhood
set_option autoImplicit false

/-- A unit neighborhood of a nonzero normalized base preserves its signed sixth-root branch. -/
theorem signed_sixth_error (a b A ε : ℝ) (hA : 2 ≤ |A|)
    (ha : |a-A| ≤ 1) (hb : |b-A| ≤ 1) (h6 : |a^6-b^6| ≤ ε) :
    |a-b| ≤ ε := by
  by_cases hA0 : 0 ≤ A
  · have hA2 : 2 ≤ A := by simpa only [abs_of_nonneg hA0] using hA
    have ha1 : 1 ≤ a := by have := (abs_le.mp ha).1; linarith
    have hb1 : 1 ≤ b := by have := (abs_le.mp hb).1; linarith
    exact (anchor_gaps a b ε ha1 hb1 h6).1
  · have hA2 : A ≤ -2 := by
      rw [abs_of_nonpos (le_of_not_ge hA0)] at hA
      linarith
    have ha1 : 1 ≤ -a := by have := (abs_le.mp ha).2; linarith
    have hb1 : 1 ≤ -b := by have := (abs_le.mp hb).2; linarith
    have hh := (anchor_gaps (-a) (-b) ε ha1 hb1 (by
      simpa only [neg_pow, show (-1 : ℝ)^6 = 1 by norm_num, one_mul] using h6)).1
    simpa only [neg_sub_neg, abs_sub_comm] using hh

/-- Reuse the corpus's normed-ring product estimate for at most six bounded factors. -/
theorem bounded_product_error {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a b : ι → ℝ) (M ε : ℝ) (hcard : s.card ≤ 6) (hM : 1 ≤ M) (hε : 0 ≤ ε)
    (ha : ∀ i ∈ s, |a i| ≤ M) (hb : ∀ i ∈ s, |b i| ≤ M)
    (he : ∀ i ∈ s, |a i-b i| ≤ ε) :
    |(∏ i ∈ s, a i)-(∏ i ∈ s, b i)| ≤ 6*M^6*ε := by
  have hp := GaloisForLFunctions.HTGeometry.FormationDust.norm_prod_sub_prod_le
    s a b (fun _ => M) (fun _ _ => hM)
    (fun i hi => by simpa only [Real.norm_eq_abs] using ha i hi)
    (fun i hi => by simpa only [Real.norm_eq_abs] using hb i hi)
  simp only [Real.norm_eq_abs, Finset.prod_const] at hp
  have hs : (∑ i ∈ s, |a i-b i|) ≤ 6*ε := by
    calc
      _ ≤ ∑ _i ∈ s, ε := Finset.sum_le_sum he
      _ = (s.card : ℝ)*ε := by simp
      _ ≤ 6*ε := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hε
  have hm : M^s.card ≤ M^6 := pow_le_pow_right₀ hM hcard
  calc
    _ ≤ M^s.card*(∑ i ∈ s, |a i-b i|) := hp
    _ ≤ M^6*(6*ε) := mul_le_mul hm hs (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- A linear resonant factor is stable when its other factors stay away from zero. -/
theorem linear_factor_error (a b A B M ε : ℝ) (hA : 1 ≤ |A|)
    (hM : 0 ≤ M) (hb : |b| ≤ M) (hAB : |A-B| ≤ 6*M^6*ε)
    (hp : |a*A-b*B| ≤ ε) : |a-b| ≤ (1+6*M^7)*ε := by
  calc
    |a-b| ≤ |a-b| * |A| := le_mul_of_one_le_right (abs_nonneg _) hA
    _ = |(a*A-b*B)+(-b)*(A-B)| := by rw [← abs_mul]; congr 1; ring
    _ ≤ |a*A-b*B| + |b| * |A-B| := by
      simpa only [abs_mul, abs_neg] using abs_add_le (a*A-b*B) ((-b)*(A-B))
    _ ≤ ε+M*(6*M^6*ε) := add_le_add hp (mul_le_mul hb hAB (abs_nonneg _) hM)
    _ = _ := by ring

/-- Isolate a visible coordinate without imposing support on either perturbed signal. -/
theorem coordinate_error_of_visible (N : ℕ) (S : Finset ℕ) (c e : ℕ → ℝ)
    (M ε : ℝ) (hS : S ⊆ Icc 1 N) (hM : 1 ≤ M) (hε : 0 ≤ ε)
    (hcS : ∀ q ∈ S, 1 ≤ |selbergMultiplesCoord N c q|)
    (hc : ∀ q ∈ Icc 1 N, |selbergMultiplesCoord N c q| ≤ M)
    (he : ∀ q ∈ Icc 1 N, |selbergMultiplesCoord N e q| ≤ M)
    (hclose : ∀ q ∈ S,
      |selbergMultiplesCoord N c q-selbergMultiplesCoord N e q| ≤ ε)
    (h5 : ∀ v : Fin 5 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ ε)
    (h6 : ∀ v : Fin 6 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ ε)
    (q : ℕ) (hq : q ∈ Icc 1 N) (hv : Visible N S q) :
    |selbergMultiplesCoord N c q-selbergMultiplesCoord N e q| ≤ (1+6*M^7)*ε := by
  classical
  obtain ⟨m, hm, r, hz, i, hi, hr⟩ := hv
  let s : Finset (Fin m) := univ.erase i
  have hm6 : m ≤ 6 := by rcases hm with rfl | rfl <;> omega
  have hs6 : s.card ≤ 6 := card_erase_le.trans (by simpa using hm6)
  have hs (j : Fin m) (hj : j ∈ s) : addOrderOf (r j) ∈ S :=
    hr j (mem_erase.mp hj).1
  have hA : 1 ≤ |∏ j ∈ s, selbergMultiplesCoord N c (addOrderOf (r j))| := by
    rw [Finset.abs_prod]
    exact Finset.one_le_prod (fun j hj => hcS _ (hs j hj))
  have hAB := bounded_product_error s
    (fun j => selbergMultiplesCoord N c (addOrderOf (r j)))
    (fun j => selbergMultiplesCoord N e (addOrderOf (r j))) M ε hs6 hM hε
    (fun j hj => hc _ (hS (hs j hj))) (fun j hj => he _ (hS (hs j hj)))
    (fun j hj => hclose _ (hs j hj))
  have hraw : ∀ v : Fin m → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ ε := by
    rcases hm with rfl | rfl
    · exact h5
    · exact h6
  have hp := resonant_product_error N c e m ε hraw r hz
  have hpc : selbergMultiplesCoord N c q *
      (∏ j ∈ s, selbergMultiplesCoord N c (addOrderOf (r j))) =
      ∏ j, selbergMultiplesCoord N c (addOrderOf (r j)) := by
    rw [← hi]
    exact Finset.mul_prod_erase univ
      (fun j => selbergMultiplesCoord N c (addOrderOf (r j))) (mem_univ i)
  have hpe : selbergMultiplesCoord N e q *
      (∏ j ∈ s, selbergMultiplesCoord N e (addOrderOf (r j))) =
      ∏ j, selbergMultiplesCoord N e (addOrderOf (r j)) := by
    rw [← hi]
    exact Finset.mul_prod_erase univ
      (fun j => selbergMultiplesCoord N e (addOrderOf (r j))) (mem_univ i)
  rw [← hpc, ← hpe] at hp
  exact linear_factor_error _ _ _ _ M ε hA (by linarith) (he q hq) hAB hp

open GaloisForLFunctions.BezoutValuationIncidence ValuationPhase

/-- A physical unit ball bounds every admitted Fourier coordinate by one finite budget. -/
theorem coordinate_unit_ball_bound (N : ℕ) (b c : ℕ → ℝ)
    (hc : ∀ n, |sieveSeq N c n-sieveSeq N b n| ≤ 1)
    (q : ℕ) (hq : q ∈ Icc 1 N) :
    |selbergMultiplesCoord N c q| ≤ 1+∑ u ∈ Icc 1 N, |selbergMultiplesCoord N b u| := by
  have hclose := coordinate_sup_error N b c 1 hc q hq
  calc
    _ ≤ |selbergMultiplesCoord N c q-selbergMultiplesCoord N b q|+
        |selbergMultiplesCoord N b q| := by
      simpa only [sub_zero] using abs_sub_le (selbergMultiplesCoord N c q)
        (selbergMultiplesCoord N b q) 0
    _ ≤ 1+|selbergMultiplesCoord N b q| := add_le_add_right hclose _
    _ ≤ _ := by
      have := single_le_sum (s := Icc 1 N)
        (f := fun u => |selbergMultiplesCoord N b u|) (fun _ _ => abs_nonneg _) hq
      linarith

/-- Visibility yields pairwise local Lipschitz recovery, including changing support. -/
theorem normalized_local_lipschitz (N : ℕ) (b : ℕ → ℝ)
    (hb : ∀ q ∈ activeModes N b, 2 ≤ |selbergMultiplesCoord N b q|)
    (hv : ∀ q ∈ Icc 1 N, q ∉ activeModes N b → Visible N (activeModes N b) q) :
    LocalPairwiseHolder N b 1 := by
  classical
  let M : ℝ := 1+∑ q ∈ Icc 1 N, |selbergMultiplesCoord N b q|
  have hM : 1 ≤ M := by
    have := Finset.sum_nonneg (s := Icc 1 N)
      (f := fun q => |selbergMultiplesCoord N b q|) (fun _ _ => abs_nonneg _)
    dsimp [M]
    linarith
  have hM0 : 0 ≤ M := by linarith
  have hK : 1 ≤ 1+6*M^7 := le_add_of_nonneg_right (by positivity)
  refine ⟨1, by norm_num, (∑ q ∈ Icc 1 N, (q.totient : ℝ))*(1+6*M^7),
    by positivity, ?_⟩
  intro c e ε hε hc he h5 h6
  have hS : activeModes N b ⊆ Icc 1 N := by
    intro q hq
    exact (mem_filter.mp hq).1
  have hcclose (q : ℕ) (hq : q ∈ Icc 1 N) :
      |selbergMultiplesCoord N c q-selbergMultiplesCoord N b q| ≤ 1 :=
    coordinate_sup_error N b c 1 hc q hq
  have heclose (q : ℕ) (hq : q ∈ Icc 1 N) :
      |selbergMultiplesCoord N e q-selbergMultiplesCoord N b q| ≤ 1 :=
    coordinate_sup_error N b e 1 he q hq
  have hlinear (q : ℕ) (hq : q ∈ activeModes N b) :
      |selbergMultiplesCoord N c q-selbergMultiplesCoord N e q| ≤ ε :=
    signed_sixth_error _ _ _ ε (hb q hq) (hcclose q (hS hq)) (heclose q (hS hq))
      (coordinate_sixth_error N c e ε h6 q (hS hq))
  have hcS (q : ℕ) (hq : q ∈ activeModes N b) : 1 ≤ |selbergMultiplesCoord N c q| := by
    have ht : |selbergMultiplesCoord N b q| ≤
        |selbergMultiplesCoord N c q-selbergMultiplesCoord N b q|+
          |selbergMultiplesCoord N c q| := by
      simpa only [sub_zero, abs_sub_comm] using abs_sub_le
        (selbergMultiplesCoord N b q) (selbergMultiplesCoord N c q) 0
    have hbase := hb q hq
    have hnear := hcclose q (hS hq)
    linarith
  have hall (q : ℕ) (hq : q ∈ Icc 1 N) :
      |selbergMultiplesCoord N c q-selbergMultiplesCoord N e q| ≤ (1+6*M^7)*ε := by
    by_cases hs : q ∈ activeModes N b
    · exact (hlinear q hs).trans (le_mul_of_one_le_left hε hK)
    · exact coordinate_error_of_visible N (activeModes N b) c e M ε hS hM hε hcS
        (coordinate_unit_ball_bound N b c hc) (coordinate_unit_ball_bound N b e he)
        hlinear h5 h6 q hq (hv q hq hs)
  refine ⟨0, fun n => ?_⟩
  have hh := sieveSeq_error_le_totient_sum N e c ((1+6*M^7)*ε)
    (fun q hq => by simpa only [abs_sub_comm] using hall q hq) n
  simpa only [Nat.add_zero, Real.rpow_one, mul_assoc] using hh

/-- Scaling actual divisor weights scales each multiples coordinate. -/
theorem coordinate_scale (N : ℕ) (b : ℕ → ℝ) (scl : ℝ) (q : ℕ) :
    selbergMultiplesCoord N (fun d => scl*b d) q = scl*selbergMultiplesCoord N b q := by
  simp [selbergMultiplesCoord, Finset.mul_sum, mul_div_assoc]

theorem activeModes_scale (N : ℕ) (b : ℕ → ℝ) (scl : ℝ) (hscl : scl ≠ 0) :
    activeModes N (fun d => scl*b d) = activeModes N b := by
  ext q
  simp [activeModes, coordinate_scale, hscl]

/-- Remove amplitude normalization; only the arithmetic visibility criterion remains. -/
theorem local_lipschitz_of_visibility (N : ℕ) (b : ℕ → ℝ)
    (hv : ∀ q ∈ Icc 1 N, q ∉ activeModes N b → Visible N (activeModes N b) q) :
    LocalPairwiseHolder N b 1 := by
  classical
  let scl : ℝ := 1+∑ q ∈ Icc 1 N, 2/|selbergMultiplesCoord N b q|
  have hscl1 : 1 ≤ scl := by
    have := Finset.sum_nonneg (s := Icc 1 N)
      (f := fun q => 2/|selbergMultiplesCoord N b q|) (fun _ _ => by positivity)
    dsimp [scl]
    linarith
  have hscl : 0 < scl := by linarith
  have hs := activeModes_scale N b scl hscl.ne'
  have hb : ∀ q ∈ activeModes N (fun d => scl*b d),
      2 ≤ |selbergMultiplesCoord N (fun d => scl*b d) q| := by
    intro q hq
    rw [hs] at hq
    obtain ⟨hqN, hq0⟩ := mem_filter.mp hq
    have hterm : 2/|selbergMultiplesCoord N b q| ≤ scl := by
      have := single_le_sum (s := Icc 1 N)
        (f := fun u => 2/|selbergMultiplesCoord N b u|) (fun _ _ => by positivity) hqN
      dsimp [scl]
      linarith
    rw [coordinate_scale, abs_mul, abs_of_pos hscl]
    calc
      2 = (2/|selbergMultiplesCoord N b q|)*|selbergMultiplesCoord N b q| :=
        (div_mul_cancel₀ _ (abs_ne_zero.mpr hq0)).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hterm (abs_nonneg _)
  have hv' : ∀ q ∈ Icc 1 N, q ∉ activeModes N (fun d => scl*b d) →
      Visible N (activeModes N (fun d => scl*b d)) q := by
    simpa only [hs] using hv
  exact (local_holder_scale_iff N b 1 scl hscl.ne').mp
    (normalized_local_lipschitz N _ hb hv')

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.LinearVisibility
