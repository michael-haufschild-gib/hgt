import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerPrimitiveWordCoding

/-! Expanding multipliers of actual Gauss pair words descend to cyclic words
and turn whole-word repetition into ordinary positive powers. -/

open Matrix
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCoding MayerHyperbolic MayerConjugacy MayerIntegralWords MayerGaussCoding MayerWords
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerPairMultiplier

def pairMultiplier (ps : List (ℕ × ℕ)) : ℝ :=
  expandingMultiplier (actualPairedMatrix ps 0 0 + actualPairedMatrix ps 1 1)

theorem actualPairedMatrix_det (ps : List (ℕ × ℕ)) : (actualPairedMatrix ps).det = 1 := by
  rw [actualPairedMatrix_eq]
  exact (unimodular_iff_det _).mp (matrixWord_unimodular _)

theorem actualPairedMatrix_append (ps qs : List (ℕ × ℕ)) :
    actualPairedMatrix (ps++qs) = actualPairedMatrix ps * actualPairedMatrix qs := by
  simp only [actualPairedMatrix_eq,pairedRunWord_append,matrixWord_append,intMatrix_mul]

theorem actualPairedMatrix_nil : actualPairedMatrix [] = 1 := by
  rw [actualPairedMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pairedRunWord,matrixWord,intMatrix]

theorem actualPairedMatrix_wordPower (ps : List (ℕ × ℕ)) (n : ℕ) :
    actualPairedMatrix (wordPower ps n) = actualPairedMatrix ps^n := by
  induction n with
  | zero => exact actualPairedMatrix_nil
  | succ n ih => rw [wordPower,actualPairedMatrix_append,ih,pow_succ']

theorem actualPairedMatrix_trace_gt_two (ps : List (ℕ × ℕ)) (hps : ps ≠ []) :
    2 < actualPairedMatrix ps 0 0 + actualPairedMatrix ps 1 1 := by
  have hpos (i j : Fin 2) : 0 < actualPairedMatrix ps i j := by
    rw [actualPairedMatrix_eq]
    change (0 : ℤ) < (matrixWord (pairedRunWord ps) i j : ℤ)
    exact_mod_cast pairedRunWord_pos ps hps i j
  have hdet := actualPairedMatrix_det ps
  rw [Matrix.det_fin_two] at hdet
  have ha := hpos 0 0
  have hb := hpos 0 1
  have hc := hpos 1 0
  have hd := hpos 1 1
  by_contra hn
  have hae : actualPairedMatrix ps 0 0 = 1 := by omega
  have hde : actualPairedMatrix ps 1 1 = 1 := by omega
  rw [hae,hde] at hdet
  nlinarith only [hdet,mul_pos hb hc]

theorem pairMultiplier_gt_one (ps : List (ℕ × ℕ)) (hps : ps ≠ []) :
    1 < pairMultiplier ps := (expandingMultiplier_spec (actualPairedMatrix_trace_gt_two ps hps)).1

private theorem expanding_root_unique {t x y : ℝ} (hx : 1 < x) (hy : 1 < y)
    (hpx : x^2-t*x+1=0) (hpy : y^2-t*y+1=0) : x = y := by
  have hprod : (x-y)*(x+y-t) = 0 := by nlinarith only [hpx,hpy]
  rcases mul_eq_zero.mp hprod with he | he
  · exact sub_eq_zero.mp he
  · have ht : t = x+y := by linarith only [he]
    rw [ht] at hpx
    have hxy : 1 < x*y := by
      nlinarith only [mul_pos (sub_pos.mpr hx) (sub_pos.mpr hy),hx,hy]
    nlinarith only [hpx,hxy]

/-- Cyclic pair rotation preserves the actual expanding multiplier. -/
theorem pairMultiplier_rotate (ps : List (ℕ × ℕ)) (k : ℕ) :
    pairMultiplier (ps.rotate k) = pairMultiplier ps := by
  by_cases hz : ps.length = 0
  · have hps : ps = [] := List.length_eq_zero_iff.mp hz
    subst ps
    simp only [List.rotate_nil]
  rw [← List.rotate_mod ps k]
  have hk : k%ps.length ≤ ps.length := (Nat.mod_lt _ (Nat.pos_of_ne_zero hz)).le
  rw [List.rotate_eq_drop_append_take hk]
  unfold pairMultiplier
  have ht := Matrix.trace_mul_comm (actualPairedMatrix (ps.drop (k%ps.length)))
    (actualPairedMatrix (ps.take (k%ps.length)))
  rw [← actualPairedMatrix_append,← actualPairedMatrix_append,List.take_append_drop] at ht
  simpa only [Matrix.trace,Matrix.diag,Fin.sum_univ_two] using congrArg expandingMultiplier ht

private theorem spectral_trace (A : IntMatrix) (hdet : A.det = 1)
    (ht : 2 < A 0 0+A 1 1) (n : ℕ) :
    ((A^n) 0 0 : ℝ)+(A^n) 1 1 =
      expandingMultiplier (A 0 0+A 1 1)^n +
        ((expandingMultiplier (A 0 0+A 1 1))⁻¹)^n := by
  let l := expandingMultiplier (A 0 0+A 1 1)
  have hl := expandingMultiplier_spec ht
  have hl0 : 0 < l := zero_lt_one.trans hl.1
  have hmu : l⁻¹ < 1 := (inv_lt_one₀ hl0).mpr hl.1
  have hgap : l-l⁻¹ ≠ 0 := ne_of_gt (sub_pos.mpr (hmu.trans hl.1))
  have hsum : l+l⁻¹ = (A 0 0 : ℝ)+A 1 1 := by
    apply mul_right_cancel₀ (ne_of_gt hl0)
    rw [add_mul,inv_mul_cancel₀ (ne_of_gt hl0)]
    have he := hl.2
    rw [Int.cast_add] at he
    nlinarith only [he]
  have hp : expandingProjection A 0 0 + expandingProjection A 1 1 = 1 := by
    simp only [expandingProjection,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply,
      realMatrix,Matrix.one_apply_eq]
    change (l-l⁻¹)⁻¹*((A 0 0 : ℝ)-l⁻¹*1)+
      (l-l⁻¹)⁻¹*((A 1 1 : ℝ)-l⁻¹*1) = 1
    simp only [mul_one]
    rw [← mul_add,show ((A 0 0 : ℝ)-l⁻¹)+((A 1 1 : ℝ)-l⁻¹) = l-l⁻¹ by
      linarith only [hsum],inv_mul_cancel₀ hgap]
  have he := congrArg (fun M : RealMatrix => M 0 0+M 1 1)
    (realMatrix_pow_spectral A hdet ht n)
  rw [← realMatrix_pow] at he
  simp only [realMatrix,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.sub_apply,Matrix.one_apply_eq] at he
  rw [he]
  calc
    _ = l^n*(expandingProjection A 0 0+expandingProjection A 1 1) +
        (l⁻¹)^n*(2-(expandingProjection A 0 0+expandingProjection A 1 1)) := by
      dsimp [l]
      ring
    _ = _ := by rw [hp]; ring

/-- Repetition raises the expanding pair multiplier to the repetition exponent. -/
theorem pairMultiplier_wordPower (ps : List (ℕ × ℕ)) (hps : ps ≠ [])
    {n : ℕ} (hn : 0 < n) : pairMultiplier (wordPower ps n) = pairMultiplier ps^n := by
  have hne : wordPower ps n ≠ [] := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    intro he
    have hlen := congrArg List.length he
    simp only [wordPower,List.length_append,List.length_nil] at hlen
    have hpos := List.length_pos_iff.mpr hps
    omega
  have hp := expandingMultiplier_spec (actualPairedMatrix_trace_gt_two (wordPower ps n) hne)
  apply expanding_root_unique hp.1 (one_lt_pow₀ (pairMultiplier_gt_one ps hps) (Nat.ne_of_gt hn)) hp.2
  have he := spectral_trace (actualPairedMatrix ps) (actualPairedMatrix_det ps)
    (actualPairedMatrix_trace_gt_two ps hps) n
  have hln : pairMultiplier ps^n ≠ 0 := pow_ne_zero n
    (ne_of_gt (zero_lt_one.trans (pairMultiplier_gt_one ps hps)))
  rw [actualPairedMatrix_wordPower,Int.cast_add]
  rw [he]
  change (pairMultiplier ps^n)^2 -
    (pairMultiplier ps^n+(pairMultiplier ps)⁻¹^n)*pairMultiplier ps^n+1=0
  rw [inv_pow]
  field_simp [hln]
  ring

/-- The fixed-point multiplier in the source trace is exactly the pair-matrix multiplier. -/
theorem wordMultiplier_eq_pairMultiplier (n : ℕ) (a : Word (2*n+2)) :
    wordMultiplier (2*n+1) a = pairMultiplier (evenWordPairs (n+1) a) := by
  have hne : evenWordPairs (n+1) a ≠ [] := by
    intro he
    have h := congrArg List.length he
    rw [evenWordPairs_length] at h
    simp only [List.length_nil] at h
    omega
  have hp := expandingMultiplier_spec (actualPairedMatrix_trace_gt_two _ hne)
  apply expanding_root_unique (one_lt_wordMultiplier _ _) hp.1 ?_ hp.2
  have he := wordMultiplier_quadratic (2*n+1) a
  have hm : actualPairedMatrix (evenWordPairs (n+1) a) = intMatrix (wordMatrix (2*n+2) a) := by
    change actualPairedMatrix (evenWordPairs (n+1) a) = intMatrix (wordMatrix (2*(n+1)) a)
    rw [actualPairedMatrix_eq,evenWordPairs_matrix]
  rw [hm]
  simp only [intMatrix,Int.cast_add,Int.cast_natCast]
  simpa only [Nat.cast_add,show 2*n+1+1=2*(n+1) by omega,pow_mul,
    neg_one_sq,one_pow] using he

#print axioms actualPairedMatrix_trace_gt_two
#print axioms pairMultiplier_rotate
#print axioms pairMultiplier_wordPower
#print axioms wordMultiplier_eq_pairMultiplier
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerPairMultiplier
