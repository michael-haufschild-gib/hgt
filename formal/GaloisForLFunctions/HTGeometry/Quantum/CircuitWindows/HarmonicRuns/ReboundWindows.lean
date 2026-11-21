import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.HarmonicRuns.DoublingRebound
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitWindows

/-! # Long uninterrupted hard windows at twice an affordable date -/
open Filter Set MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.HarmonicRuns
noncomputable section
open SharpOccupation

/-- A unit of local simulation fits between the two exponential budgets. -/
theorem unit_budget :
    ∀ᶠ n : ℕ in atTop, 2^n/(256*(n+1))+n^4 ≤ 2^n/(128*(n+1)) := by
  filter_upwards [(polynomial_subcritical 4).eventually_lt_const (by norm_num : (0:ℝ)<1/256)] with n hn
  have h := (div_lt_iff₀ (by positivity : 0 < (2:ℝ)^n)).mp hn
  push_cast at h
  have he : (n:ℝ)^4*(256*((n:ℝ)+1)) ≤ (2:ℝ)^n := by nlinarith only [h,Nat.cast_nonneg (α := ℝ) n]
  let j := 2^n/(256*(n+1))
  have hj : n^4 ≤ j := (Nat.le_div_iff_mul_le (by positivity)).mpr (by exact_mod_cast he)
  apply (Nat.le_div_iff_mul_le (by positivity)).mpr
  calc
    _ ≤ (j+j)*(128*(n+1)) := Nat.mul_le_mul_right _ (Nat.add_le_add_left hj j)
    _ = j*(256*(n+1)) := by ring
    _ ≤ _ := Nat.div_mul_le_self _ _

/-- A base visit and a continuous second-window hit give one of finitely
many offset two-harmonic tests. The offsets may be much larger than the
time needed to compile the first unitary. -/
private theorem window_cover {n j J : ℕ} (H : selfAdjoint (Register n)) (W : ℝ)
    (hunit : windowHits H j (1/10) 1 ⊆ visitSet H J (101/1000)) :
    ∃ u : Fin (⌊W⌋₊+1) → Fin 2 → ℝ,
      {t | t ∈ visitSet H J (101/1000) ∧ 2*t ∈ windowHits H j (1/10) W} ⊆
        ⋃ i, offsetRunSet H J (101/1000) (u i) := by
  let u (i : Fin (⌊W⌋₊+1)) (l : Fin 2) : ℝ := if l.val=0 then 0 else (i.val:ℝ)
  refine ⟨u,?_⟩
  rintro t ⟨hbase,v,hv,hcheap⟩
  let i : Fin (⌊W⌋₊+1) := ⟨⌊v-2*t⌋₊,Nat.lt_succ_of_le (Nat.floor_mono (by linarith only [hv.2]))⟩
  have hl : (i.val:ℝ) ≤ v-2*t := Nat.floor_le (sub_nonneg.mpr hv.1)
  have hr : v-2*t < (i.val:ℝ)+1 := Nat.lt_floor_add_one _
  have hhit : 2*t+(i.val:ℝ) ∈ visitSet H J (101/1000) :=
    hunit ⟨v,⟨by linarith only [hl],by linarith only [hr]⟩,hcheap⟩
  refine mem_iUnion.mpr ⟨i,?_⟩
  intro l
  fin_cases l
  · simpa [u] using hbase
  · simpa [u,one_add_one_eq_two] using hhit

/-- The absolute frequency of paired hits pays one offset test per unit of
the second window. The first test has spare error for moving its date. -/
theorem paired_window_mass :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let J := D/(128*(N+1))
      let j := D/(256*(N+1))
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ W : ℝ, 0 ≤ W → ∀ a : ℝ, ∀ᶠ T : ℝ in atTop,
        volume.real (({t | t ∈ visitSet H J (101/1000) ∧
          2*t ∈ windowHits H j (1/10) W} : Set ℝ) ∩ Icc a T)/(T-a) ≤ (W+1)*(1/36:ℝ)^D := by
  filter_upwards [offset_pair_upper,gaussian_unit_hit_enlargement] with ω hp hloc
  filter_upwards [hp,hloc (1/1000) (by norm_num),(tendsto_add_atTop_nat 3).eventually unit_budget]
    with k hk hs hbudget
  intro N D J j H W hW a
  have hstep := hs j (1/10)
  rw [show (1/10:ℝ)+1/1000=101/1000 by norm_num] at hstep
  obtain ⟨u,hu⟩ := window_cover H W (hstep.trans (visit_mono H _ hbudget))
  have hb (i : Fin (⌊W⌋₊+1)) := hk (u i) a
  filter_upwards [Filter.eventually_all.mpr hb,eventually_gt_atTop a] with T hT hTa
  let S := {t | t ∈ visitSet H J (101/1000) ∧ 2*t ∈ windowHits H j (1/10) W}
  let C (i : Fin (⌊W⌋₊+1)) := offsetRunSet H J (101/1000) (u i) ∩ Icc a T
  have hC : (⋃ i, C i) ⊆ Icc a T := iUnion_subset fun _ => inter_subset_right
  have hinc : S ∩ Icc a T ⊆ ⋃ i, C i := by
    rintro t ⟨ht,hI⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hu ht)
    exact mem_iUnion.mpr ⟨i,hi,hI⟩
  have hsum := (measureReal_mono (μ := volume) hinc (measure_ne_top_of_subset hC measure_Icc_lt_top.ne)).trans
    (measureReal_iUnion_fintype_le C)
  have heach (i : Fin (⌊W⌋₊+1)) : volume.real (C i)/(T-a) ≤ (1/36:ℝ)^D := (hT i).le
  calc
    _ ≤ (∑ i, volume.real (C i))/(T-a) := div_le_div_of_nonneg_right hsum (sub_nonneg.mpr hTa.le)
    _ ≤ ((⌊W⌋₊+1:ℕ):ℝ)*(1/36:ℝ)^D := by
      rw [Finset.sum_div]
      simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by push_cast; linarith only [Nat.floor_le hW]) (by positivity)

/-- At error 1/10, condition on t admitting s≤D/[128(N+1)] gates.
Outside a fraction 2(17/18)ᴰ, the entire interval from 2t through
2t+(17/16)ᴰ exceeds D/[256(N+1)] gates. -/
theorem gaussian_conditional_hard_window :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let J := D/(128*(N+1))
      let j := D/(256*(N+1))
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ a : ℝ, ∀ᶠ T : ℝ in atTop, ∀ s ≤ J,
        volume.real (({t | t ∈ visitSet H s (1/10) ∧
          2*t ∈ windowHits H j (1/10) ((17/16:ℝ)^D)} : Set ℝ) ∩ Icc a T) /
          volume.real (visitSet H s (1/10) ∩ Icc a T) ≤ 2*(17/18:ℝ)^D := by
  filter_upwards [paired_window_mass,gaussian_path_all_prefixes_maximally_projective] with ω hmass hω
  filter_upwards [hmass] with k hk
  intro N D J j H a
  let W := (17/16:ℝ)^D
  have hW : 1 ≤ W := one_le_pow₀ (by norm_num)
  filter_upwards [hk W (zero_le_one.trans hW) a,affordable_lower H (hω k) a,eventually_gt_atTop a]
    with T hT hlo hTa s hsj
  let S := {t | t ∈ visitSet H s (1/10) ∧ 2*t ∈ windowHits H j (1/10) W}
  have hinc : S ⊆ {t | t ∈ visitSet H J (101/1000) ∧ 2*t ∈ windowHits H j (1/10) W} := by
    rintro t ⟨⟨c,hc,C,hC,he⟩,hhit⟩
    exact ⟨⟨c,hc,C,hC.trans hsj,he.trans (by norm_num)⟩,hhit⟩
  have hnum : volume.real (S ∩ Icc a T)/(T-a) ≤ 2*W*(1/36:ℝ)^D :=
    (div_le_div_of_nonneg_right (measureReal_mono (inter_subset_inter_left _ hinc)
      (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)) (sub_nonneg.mpr hTa.le)).trans
      (hT.trans (mul_le_mul_of_nonneg_right (by linarith only [hW]) (by positivity)))
  have hl := hlo s
  have hlp : 0 < (1/32:ℝ)^D := by positivity
  rw [←div_div_div_cancel_right₀ (sub_pos.mpr hTa).ne']
  apply (div_le_div_of_nonneg_right hnum (hlp.trans hl).le).trans
  apply (div_le_div_of_nonneg_left (by positivity) hlp hl.le).trans_eq
  dsimp only [W]
  rw [mul_assoc,←mul_pow,mul_div_assoc,←div_pow]
  norm_num

#print axioms gaussian_conditional_hard_window
end
end GaloisForLFunctions.HTGeometry.HarmonicRuns
