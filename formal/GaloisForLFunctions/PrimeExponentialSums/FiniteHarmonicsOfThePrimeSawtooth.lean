import GaloisForLFunctions.HTGeometry.SmoothedSawtoothFourier
import GaloisForLFunctions.RHTower.LogLatticePoissonAnticoncentration
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import GaloisForLFunctions.RHTower.SquarefreeCountingAsymptotic

/-!
# Finite harmonic control of a weighted sawtooth

A uniform estimate for the first H harmonics costs their harmonic sum.
Beyond H the second-order decay of the smoothing kernels costs only the
total mass divided by the product of the smoothing width and H.
-/

noncomputable section
open Finset Filter Topology
open GaloisForLFunctions.HTGeometry.SmoothedSawtooth
namespace GaloisForLFunctions.PrimeExponentialSums

private def splitWeight (H : ℕ) (L M δ : ℝ) (j : ℕ) :=
  if j ≤ H then L/(j:ℝ) else M/δ / (j:ℝ)^2

private theorem split_weight_sum {H : ℕ} (hH : 0 < H) {L M δ : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hδ : 0 < δ) (N : ℕ) :
    (∑ j ∈ Ioo 0 N,splitWeight H L M δ j) ≤ L*(1+Real.log H)+M/δ / H := by
  let s := Ioo 0 N
  have hl : s.filter (· ≤ H) ⊆ Icc 1 H := fun j hj =>
    mem_Icc.mpr ⟨(mem_Ioo.mp (mem_filter.mp hj).1).1,(mem_filter.mp hj).2⟩
  have hu : s.filter (fun j => ¬j≤H) ⊆ Icc (H+1) N := by
    intro j hj
    obtain ⟨hi,hj⟩ := mem_filter.mp hj
    exact mem_Icc.mpr ⟨by omega,(mem_Ioo.mp hi).2.le⟩
  have hls : (∑ j ∈ s.filter (· ≤ H),1/(j:ℝ)) ≤ ∑ j ∈ Icc 1 H,1/(j:ℝ) :=
    sum_le_sum_of_subset_of_nonneg hl fun _ _ _ => by positivity
  have hus : (∑ j ∈ s.filter (fun j => ¬j≤H),1/(j:ℝ)^2) ≤ ∑ j ∈ Icc (H+1) N,1/(j:ℝ)^2 :=
    sum_le_sum_of_subset_of_nonneg hu fun _ _ _ => by positivity
  have ls := hls.trans (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log H)
  have us := hus.trans (_root_.RHTower.sum_inv_sq_tail_le hH N)
  change (∑ j ∈ s,_) ≤ _
  rw [←sum_filter_add_sum_filter_not s (· ≤ H) (splitWeight H L M δ)]
  have he : (∑ j ∈ s.filter (· ≤ H),splitWeight H L M δ j)=L*∑ j ∈ s.filter (· ≤ H),1/(j:ℝ) := by
    rw [mul_sum]
    exact sum_congr rfl fun j hj => by rw [splitWeight,if_pos (mem_filter.mp hj).2,mul_one_div]
  have he' : (∑ j ∈ s.filter (fun j => ¬j≤H),splitWeight H L M δ j)=
      (M/δ)*∑ j ∈ s.filter (fun j => ¬j≤H),1/(j:ℝ)^2 := by
    rw [mul_sum]
    exact sum_congr rfl fun j hj => by rw [splitWeight,if_neg (mem_filter.mp hj).2,mul_one_div]
  rw [he,he',←mul_one_div (M/δ)]
  exact add_le_add (mul_le_mul_of_nonneg_left ls hL) (mul_le_mul_of_nonneg_left us (div_nonneg hM hδ.le))

private theorem harmonic_coefficient_bounds {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ) {h : ℤ} (hh : h ≠ 0)
    {a k : ℂ} (ha : ‖a‖ ≤ A*(1+((h:ℝ)*δ)^2)⁻¹/|(h:ℝ)|)
    (hk : ‖k‖ ≤ A*δ*(1+((h:ℝ)*δ)^2)⁻¹) :
    ‖a‖+‖k‖ ≤ 2*A/|(h:ℝ)| ∧ ‖a‖+‖k‖ ≤ 2*A/(δ*|(h:ℝ)|^2) := by
  let u := |(h:ℝ)|
  have hu : 0 < u := abs_pos.mpr (by exact_mod_cast hh)
  have hprod := mul_pos hu hδ
  have he : ((h:ℝ)*δ)^2=(u*δ)^2 := by dsimp only [u]; rw [mul_pow,mul_pow,sq_abs]
  rw [he] at ha hk
  have h1 : u*δ ≤ 1+(u*δ)^2 := by nlinarith only [sq_nonneg (u*δ-1/2)]
  have hl1 : ‖a‖ ≤ A/u := by
    apply ha.trans
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_right hA (inv_le_one_of_one_le₀ (by nlinarith only [sq_nonneg (u*δ)]))) hu.le
  have hl2 : ‖k‖ ≤ A/u := by
    apply hk.trans
    apply (mul_le_mul_of_nonneg_left (inv_anti₀ hprod h1) (mul_nonneg hA hδ.le)).trans_eq
    field_simp [hu.ne',hδ.ne']
  have hu1 : ‖a‖ ≤ A/(δ*u^2) := by
    apply ha.trans
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (inv_anti₀ hprod h1) hA) hu.le).trans_eq
    field_simp [hu.ne',hδ.ne']
  have hu2 : ‖k‖ ≤ A/(δ*u^2) := by
    apply hk.trans
    apply (mul_le_mul_of_nonneg_left (inv_anti₀ (sq_pos_of_pos hprod) (le_add_of_nonneg_left zero_le_one))
      (mul_nonneg hA hδ.le)).trans_eq
    field_simp [hu.ne',hδ.ne']
  exact ⟨(add_le_add hl1 hl2).trans_eq (by dsimp only [u]; ring),
    (add_le_add hu1 hu2).trans_eq (by dsimp only [u]; ring)⟩

/-- A bound for the first H harmonics of a positive finite measure
controls its sharp centered fractional-part sum, including atoms at jumps. -/
theorem sawtooth_from_finite_harmonics :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type} (s : Finset ι) (y w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
      {H : ℕ} (hH : 0 < H) {δ L M : ℝ}, 0 < δ → 0 ≤ L → (∑ i ∈ s,w i) ≤ M →
      (∀ h : ℤ, h ≠ 0 → h.natAbs ≤ H →
        ‖∑ i ∈ s,(w i:ℂ)*fourier h (y i : UnitAddCircle)‖ ≤ L) →
      ‖∑ i ∈ s,(w i:ℂ)*(saw (y i):ℂ)‖ ≤ C*(δ*M+L*(1+Real.log H)+M/δ / H) := by
  obtain ⟨A,hA,hdec⟩ := exists_saw_decomposition
  refine ⟨4*A,by positivity,?_⟩
  intro ι s y w hw H hH δ L M hδ hL hmass hfreq
  have hM := (sum_nonneg fun i (_ : i ∈ s) => hw i).trans hmass
  obtain ⟨a,k,has,hks,ha,hk,hd⟩ := hdec δ hδ
  let E (h : ℤ) := ‖∑ i ∈ s,(w i:ℂ)*fourier h (y i : UnitAddCircle)‖
  have heM (h : ℤ) : E h ≤ M := by
    apply (norm_sum_le ..).trans
    calc _ = ∑ i ∈ s,w i := by
              apply sum_congr rfl
              intro i _
              rw [norm_mul,norm_fourier_apply,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw i)]
         _ ≤ _ := hmass
  have hmain := hd s y (fun i => (w i:ℂ)) w (fun i => by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw i)])
  have sa := summable_mul_norm_sum s (fun i => (w i:ℂ)) y has
  have sk := summable_mul_norm_sum s (fun i => (w i:ℂ)) y hks
  rw [←sa.tsum_add sk] at hmain
  apply hmain.trans
  apply le_of_tendsto (sa.add sk).hasSum
  apply Filter.Eventually.of_forall
  intro t
  let g := splitWeight H L M δ
  have hgn (j : ℕ) : 0 ≤ g j := by
    dsimp only [g,splitWeight]; split_ifs <;> positivity
  have hsum := _root_.RHTower.LogLatticePoisson.sum_int_natAbs_le hgn (split_weight_sum hH hL hM hδ) t
  have zbound : (∑ h ∈ t,if h=0 then A*δ*M else 0) ≤ A*δ*M := by
    rw [sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (mul_nonneg hA hδ.le) hM
  have hfin : (∑ h ∈ t,(‖a h‖*E h+‖k h‖*E h)) ≤
      (∑ h ∈ t,if h=0 then A*δ*M else 0)+2*A*∑ h ∈ t.filter (fun h => h≠0),g h.natAbs := by
    rw [sum_filter,mul_sum,←sum_add_distrib]
    apply sum_le_sum
    intro h _
    by_cases hh : h=0
    · subst h
      have ha0 : ‖a 0‖=0 := le_antisymm (by simpa using ha 0) (norm_nonneg _)
      have hk0 : ‖k 0‖ ≤ A*δ := by simpa using hk 0
      simpa [ha0] using (mul_le_mul hk0 (heM 0) (norm_nonneg _) (mul_nonneg hA hδ.le))
    · have hnat : (h.natAbs:ℝ)=|(h:ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
      obtain ⟨hlow,hhigh⟩ := harmonic_coefficient_bounds hA hδ hh (ha h) (hk h)
      simp only [if_neg hh,if_pos hh,zero_add,←add_mul]
      by_cases hlowH : h.natAbs ≤ H
      · apply (mul_le_mul hlow (hfreq h hh hlowH) (norm_nonneg _) (by positivity)).trans_eq
        dsimp only [g,splitWeight]; rw [if_pos hlowH,hnat]; ring
      · apply (mul_le_mul hhigh (heM h) (norm_nonneg _) (by positivity)).trans_eq
        dsimp only [g,splitWeight]; rw [if_neg hlowH,hnat]
        simp only [div_eq_mul_inv,mul_inv_rev]; ring
  apply hfin.trans ((add_le_add zbound (mul_le_mul_of_nonneg_left hsum (by positivity))).trans ?_)
  linarith only [mul_nonneg (mul_nonneg hA hδ.le) hM]

#print axioms sawtooth_from_finite_harmonics

end GaloisForLFunctions.PrimeExponentialSums
