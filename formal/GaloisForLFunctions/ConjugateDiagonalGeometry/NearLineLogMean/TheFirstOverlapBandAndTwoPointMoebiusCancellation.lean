import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.FourEnergyMeasurementsRecoverAdjacentCorrelations
import GaloisForLFunctions.RHTower.SquareSampledDivisorLogKernel

/-!
# The first overlap band and two-point Möbius cancellation

Four measurements recover each short block of signed adjacent Gram
products. Abel summation removes their square-root weights. Repeated
splitting at three quarters of the upper endpoint then recovers the
ordinary Cesàro mean of μ(n)μ(n+1). Conversely that mean controls
every first-band measurement by two applications of Abel summation.
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
open Finset Filter Topology
open _root_.RHTower
open GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
noncomputable section

private theorem cesaro_of_short_blocks (f : ℕ → ℝ)
    (hb : ∀ η : ℝ, 0<η → ∀ᶠ A : ℕ in atTop, ∀ B : ℕ, A≤B → 3*(B+1)≤4*(A+1) →
      |∑ j ∈ Ico A B, f j| ≤ η*((B:ℝ)+1)) :
    Tendsto (fun N : ℕ => (∑ j ∈ range N, f j)/((N:ℝ)+1)) atTop (𝓝 0) := by
  have hprefix (η : ℝ) (hη : 0<η) : ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ,
      |∑ j ∈ range N, f j| ≤ C+5*η*((N:ℝ)+1) := by
    obtain ⟨K,hK⟩ := eventually_atTop.mp (hb η hη)
    let J := 4*K+32
    let C := ∑ j ∈ range J, |f j|
    have hC : 0≤C := sum_nonneg fun _ _ => abs_nonneg _
    refine ⟨C,hC,fun N => ?_⟩
    induction N using Nat.strong_induction_on with
    | h N ih =>
      by_cases hsmall : N≤J
      · exact (abs_sum_le_sum_abs _ _).trans ((sum_le_sum_of_subset_of_nonneg
          (range_mono hsmall) (fun j _ _ => abs_nonneg (f j))).trans
          (le_add_of_nonneg_right (by positivity)))
      let A := 3*(N+1)/4
      have hnat : K≤A ∧ A<N ∧ 3*(N+1)≤4*(A+1) ∧ 5*(A+1)≤4*(N+1) := by
        dsimp only [A,J] at *
        omega
      have hratio : 5*((A:ℝ)+1)≤4*((N:ℝ)+1) := by exact_mod_cast hnat.2.2.2
      have hstep := hK A hnat.1 N hnat.2.1.le hnat.2.2.1
      have hpaid := mul_le_mul_of_nonneg_left hratio hη.le
      rw [←sum_range_add_sum_Ico f hnat.2.1.le]
      exact (abs_add_le _ _).trans (by nlinarith only [ih A hnat.2.1,hstep,hpaid])
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨C,hC,hp⟩ := hprefix (ε/12) (by positivity)
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (2*C/ε)] with N hn
  change dist ((∑ j ∈ range N, f j)/((N:ℝ)+1)) 0 < ε
  have hpos : 0<(N:ℝ)+1 := by positivity
  have hcut := (div_le_iff₀ hε).mp hn
  rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos hpos,div_lt_iff₀ hpos]
  have hx := mul_pos hε hpos
  nlinarith only [hp N,hcut,hx,hε]

private def neighborProduct (j : ℕ) := mobiusRealCoefficient (j+2)*mobiusRealCoefficient (j+1)
private def edgeScale (j : ℕ) := Real.sqrt (j+2 : ℕ)*Real.sqrt (j+1 : ℕ)
private abbrev amplitude (n : ℕ) : ℂ := coeff n

private theorem unweighted_edge (j : ℕ) :
    gram (amplitude (j+2)) (amplitude (j+1))*edgeScale j = neighborProduct j := by
  have h₁ : Real.sqrt (j+1 : ℕ)≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos j))).ne'
  have h₂ : Real.sqrt (j+2 : ℕ)≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos (j+1)))).ne'
  simp only [gram,amplitude,Complex.conj_ofReal,←Complex.ofReal_mul,Complex.ofReal_re,
    coeff,edgeScale,neighborProduct]
  field_simp [h₁,h₂]

private theorem edgeScale_mono : Monotone edgeScale := by
  intro j k h
  exact mul_le_mul (Real.sqrt_le_sqrt (Nat.cast_le.mpr (Nat.add_le_add_right h 2)))
    (Real.sqrt_le_sqrt (Nat.cast_le.mpr (Nat.add_le_add_right h 1))) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

private theorem edgeScale_le (j : ℕ) : edgeScale j≤(j+2:ℕ) := by
  calc
    _ ≤ Real.sqrt (j+2 : ℕ)*Real.sqrt (j+2 : ℕ) := mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (Nat.cast_le.mpr (Nat.le_succ (j+1)))) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt (Nat.cast_nonneg _)

/-- If the normalized energy approaches its diagonal uniformly from
bandwidth 1/N through 2/N, the ordinary unweighted adjacent Möbius
correlation has Cesàro mean zero. -/
theorem near_diagonal_implies_two_point_moebius :
    (∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, ∀ d : ℝ,
      1 ≤ d*((N+1 : ℕ) : ℝ) → d*((N+1 : ℕ) : ℝ) ≤ 2 →
      |normalizedExcess (fun n => (coeff n : ℂ)) (N+1) d| ≤ η) →
    Tendsto (fun N : ℕ => (∑ j ∈ range N, mobiusRealCoefficient (j+2)*mobiusRealCoefficient (j+1))/
      ((N:ℝ)+1)) atTop (𝓝 0) := by
  intro h
  apply cesaro_of_short_blocks neighborProduct
  intro η hη
  filter_upwards [adjacent_block_cancellation_of_near_diagonal amplitude h (η/2) (half_pos hη)] with A hA
  intro B hab hr
  let g (j : ℕ) := gram (amplitude (j+2)) (amplitude (j+1))
  have hprefix (m : ℕ) (hm : m≤B-A) : |∑ j ∈ range m, g (A+j)|≤η/2 := by
    have hh := hA (A+m) (Nat.le_add_right _ _) (by omega)
    unfold adjacentBlock at hh
    rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left] at hh
    exact hh
  have hm : Monotone (fun j => edgeScale (A+j)) :=
    edgeScale_mono.comp (fun _ _ h => Nat.add_le_add_left h A)
  have hbound (j : ℕ) (hj : j<B-A) : edgeScale (A+j) ≤ (B:ℝ)+1 := by
    have hh : A+j+2≤B+1 := by omega
    exact (edgeScale_le _).trans (by exact_mod_cast hh)
  have hw := abs_sum_mul_monotone_le_of_prefix_bound (fun j => g (A+j)) (fun j => edgeScale (A+j))
    (η/2) ((B:ℝ)+1) (B-A) (by positivity) (fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    hm hbound hprefix
  rw [sum_Ico_eq_sum_range]
  simp only [g,unweighted_edge] at hw
  exact hw.trans_eq (by ring)

private theorem decreasing_weight_bound (f w : ℕ → ℝ) (B W : ℝ) (N : ℕ)
    (hW : 0 ≤ W) (hw : ∀ j, 0 ≤ w j) (hm : Antitone w) (ht : ∀ j<N, w j ≤ W)
    (hf : ∀ m≤N, |∑ j ∈ range m, f j| ≤ B) :
    |∑ j ∈ range N, f j*w j| ≤ 3*B*W := by
  have hu := abs_sum_mul_monotone_le_of_prefix_bound f (fun j => W-w j) B W N hW
    (fun j hj => sub_nonneg.mpr (ht j hj)) (fun i j hij => sub_le_sub_left (hm hij) W)
    (fun j _ => sub_le_self W (hw j)) hf
  have hs : (∑ j ∈ range N, f j*w j)=
      W*(∑ j ∈ range N, f j)-∑ j ∈ range N, f j*(W-w j) := by
    rw [mul_sum,←sum_sub_distrib]
    exact sum_congr rfl fun _ _ => by ring
  rw [hs]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul,abs_of_nonneg hW]
  refine (add_le_add (mul_le_mul_of_nonneg_left (hf N le_rfl) hW) hu).trans_eq ?_
  ring

private theorem le_edgeScale (j : ℕ) : ((j : ℝ)+1) ≤ edgeScale j := by
  have h := Real.mul_self_sqrt (Nat.cast_nonneg (j+1) : 0 ≤ ((j+1 : ℕ) : ℝ))
  calc
    _ = Real.sqrt (j+1 : ℕ)*Real.sqrt (j+1 : ℕ) := by simpa only [Nat.cast_add,Nat.cast_one] using h.symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (Nat.cast_le.mpr (Nat.le_succ (j+1)))) (Real.sqrt_nonneg _)

private theorem edgeScale_pos (j : ℕ) : 0 < edgeScale j :=
  (by positivity : (0 : ℝ)<(j:ℝ)+1).trans_le (le_edgeScale j)

private def triangularEdge (d : ℝ) (j : ℕ) := max (d-adjacentLogGap (j+1)) 0

private theorem triangularEdge_mono (d : ℝ) : Monotone (triangularEdge d) := by
  intro i j hij
  rcases hij.lt_or_eq with h|rfl
  · exact max_le_max_right _ (sub_le_sub_left (adjacent_log_gap_strict (Nat.succ_pos i) (Nat.succ_lt_succ h)).le d)
  · exact le_rfl

private theorem triangularEdge_le {d : ℝ} (hd : 0≤d) (j : ℕ) : triangularEdge d j ≤ d :=
  max_le (sub_le_self _ ((by positivity : 0 ≤ 1/(((j+1:ℕ):ℝ)+1)).trans
    (adjacent_log_gap_bounds (Nat.succ_pos j)).1)) hd

/-- Conversely, ordinary two-point cancellation removes all surviving
off-diagonal energy uniformly through the first overlap band. -/
theorem two_point_moebius_implies_near_diagonal :
    Tendsto (fun N : ℕ => (∑ j ∈ range N, mobiusRealCoefficient (j+2)*mobiusRealCoefficient (j+1))/
      ((N:ℝ)+1)) atTop (𝓝 0) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ d : ℝ,
      1 ≤ d*((N+1 : ℕ) : ℝ) → d*((N+1 : ℕ) : ℝ) ≤ 2 →
      |normalizedExcess (fun n => (coeff n : ℂ)) (N+1) d| ≤ ε := by
  intro h ε hε
  let η := ε/100
  have hη : 0<η := by dsimp only [η]; positivity
  obtain ⟨K,hK⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp h) η hη)
  have hprefix (n : ℕ) (hn : K ≤ n) : |∑ j ∈ range n, neighborProduct j| ≤ η*((n:ℝ)+1) := by
    have hh := hK n hn
    have hp : (0:ℝ)<(n:ℝ)+1 := by positivity
    change dist ((∑ j ∈ range n, neighborProduct j)/((n:ℝ)+1)) 0 < η at hh
    rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos hp,div_lt_iff₀ hp] at hh
    exact hh.le
  filter_upwards [eventually_ge_atTop (4*K+8)] with N hN
  intro d hlo hhi
  let L := (N+1)/4
  have hL : K≤L ∧ L≤N ∧ N+1≤4*(L+1) := by dsimp only [L]; omega
  have hp : (0 : ℝ)<(L:ℝ)+1 := by positivity
  have hd : 0<d := by
    by_contra! hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg (Nat.cast_nonneg (N+1) : 0≤((N+1:ℕ):ℝ))
    linarith only [this,hlo]
  let g (j : ℕ) := gram (amplitude (j+2)) (amplitude (j+1))
  have hg (j : ℕ) : g j = neighborProduct j*(edgeScale j)⁻¹ := by
    rw [←unweighted_edge j,mul_assoc,mul_inv_cancel₀ (edgeScale_pos _).ne',mul_one]
  let P := 2*η*((N:ℝ)+1)
  let W := ((L:ℝ)+1)⁻¹
  have hraw (m : ℕ) (hm : m≤N-L) : |∑ i ∈ range m, neighborProduct (L+i)| ≤ P := by
    have hle : L+m≤N := by omega
    have he := sum_Ico_eq_sub neighborProduct (Nat.le_add_right L m)
    rw [sum_Ico_eq_sum_range,Nat.add_sub_cancel_left] at he
    rw [he]
    have hf := hprefix (L+m) (by omega)
    have hl := hprefix L hL.1
    have hcast : ((L+m:ℕ):ℝ)≤N := Nat.cast_le.mpr hle
    have hcast' : (L:ℝ)≤N := Nat.cast_le.mpr hL.2.1
    refine (abs_sub _ _).trans ((add_le_add hf hl).trans ?_)
    dsimp only [P]
    nlinarith only [mul_le_mul_of_nonneg_left hcast hη.le,mul_le_mul_of_nonneg_left hcast' hη.le]
  have hw (j : ℕ) : (edgeScale (L+j))⁻¹≤W := inv_anti₀ hp
    ((by exact_mod_cast (show L+1≤(L+j)+1 by omega) : (L:ℝ)+1≤((L+j:ℕ):ℝ)+1).trans (le_edgeScale _))
  have hgm (m : ℕ) (hm : m≤N-L) : |∑ j ∈ range m, g (L+j)| ≤ 24*η := by
    simp only [hg]
    have hh := decreasing_weight_bound (fun i => neighborProduct (L+i)) (fun i => (edgeScale (L+i))⁻¹)
      P W m (inv_nonneg.mpr hp.le) (fun _ => inv_nonneg.mpr (edgeScale_pos _).le)
      (fun i j hij => inv_anti₀ (edgeScale_pos _) (edgeScale_mono (Nat.add_le_add_left hij L)))
      (fun j _ => hw j) (fun i hi => hraw i (hi.trans hm))
    have hratio : ((N:ℝ)+1)*W ≤ 4 := by
      rw [show ((N:ℝ)+1)*W=((N:ℝ)+1)/((L:ℝ)+1) from (div_eq_mul_inv ..).symm,div_le_iff₀ hp]
      exact_mod_cast hL.2.2
    refine hh.trans ?_
    dsimp only [P]
    nlinarith only [mul_le_mul_of_nonneg_left hratio hη.le]
  have hh := abs_sum_mul_monotone_le_of_prefix_bound (fun i => g (L+i))
    (fun i => triangularEdge d (L+i)) (24*η) d (N-L) hd.le
    (fun _ _ => le_max_right _ _) ((triangularEdge_mono d).comp (fun _ _ h => Nat.add_le_add_left h L))
    (fun i _ => triangularEdge_le hd.le _) hgm
  have hzero : (∑ j ∈ range L, g j*triangularEdge d j)=0 := by
    apply sum_eq_zero
    intro j hj
    have hsmall : 2*(j+2)≤N+1 := by have := mem_range.mp hj; dsimp only [L] at this; omega
    have hreal : 2*(((j+1:ℕ):ℝ)+1) ≤ ((N+1:ℕ):ℝ) := by exact_mod_cast hsmall
    have hdj : d ≤ 1/(((j+1:ℕ):ℝ)+1) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hreal hd.le,hhi]
    rw [triangularEdge,max_eq_right (sub_nonpos.mpr (hdj.trans (adjacent_log_gap_bounds (Nat.succ_pos _)).1)),mul_zero]
  have hfull : |∑ j ∈ range N, g j*triangularEdge d j| ≤ 2*(24*η)*d := by
    rw [←sum_range_add_sum_Ico _ hL.2.1,hzero,zero_add,sum_Ico_eq_sum_range]
    exact hh
  rw [normalizedExcess,excess_energy_adjacent_spectrum _ N hd.le hhi,
    abs_div,abs_of_pos hd,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2),div_le_iff₀ hd]
  change 2*|∑ j ∈ range N, g j*triangularEdge d j| ≤ ε*d
  dsimp only [η] at hfull
  nlinarith only [hfull,mul_pos hε hd]

/-- The usual two-point Chowla statement is exactly uniform disappearance
of the first off-diagonal band of the critical Möbius window energy. -/
theorem two_point_moebius_iff_near_diagonal :
    Tendsto (fun N : ℕ => (∑ j ∈ range N, mobiusRealCoefficient (j+2)*mobiusRealCoefficient (j+1))/
      ((N:ℝ)+1)) atTop (𝓝 0) ↔
    ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, ∀ d : ℝ,
      1 ≤ d*((N+1 : ℕ) : ℝ) → d*((N+1 : ℕ) : ℝ) ≤ 2 →
      |normalizedExcess (fun n => (coeff n : ℂ)) (N+1) d| ≤ η :=
  ⟨two_point_moebius_implies_near_diagonal,near_diagonal_implies_two_point_moebius⟩

#print axioms two_point_moebius_implies_near_diagonal
#print axioms two_point_moebius_iff_near_diagonal
#print axioms near_diagonal_implies_two_point_moebius
end
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
