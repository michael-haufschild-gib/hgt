import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheMicroscopicCovarianceOfSharpMoebiusSections
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheRegularPartOfSquarefreeSections

/-!
# Zeta zeros from sharp two-length Möbius correlations

The local-gap endpoint estimate applies to samples on the vertical
lines translated by s/2 and its conjugate. Their common diagonal is
the ordinary squarefree Dirichlet section. A dyadic cutoff difference
eliminates its density term, on arbitrary moving height intervals of
length X², and recovers the squarefree zeta quotient in the right strip.
-/
noncomputable section
open Finset Complex MeasureTheory Filter
open scoped ComplexConjugate Topology
open _root_.HTGeometry (genPoly)
open _root_.RHTower (edPoly mobCoeff)
open GaloisForLFunctions.MultiscaleMollifiedZetaField (moebiusPoly)
open GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval (local_log_spacing)
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private def row (z : ℂ) (n : ℕ) := mobCoeff n * ((n:ℝ):ℂ)^(-z)
private theorem vertical (N : ℕ) (z : ℂ) (t : ℝ) :
    moebiusPoly N (z+(t:ℂ)*I) = genPoly (row z) (fun n => -Real.log n) (Icc 1 N) t := by
  unfold moebiusPoly edPoly genPoly
  apply sum_congr rfl
  intro n hn
  have hp : 0<(n:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hn).1
  rw [row,show -(z+(t:ℂ)*I)=-z+(-(t:ℂ)*I) by ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hp.ne'),
    Complex.cpow_def_of_ne_zero (y:=(-(t:ℂ)*I)) (Complex.ofReal_ne_zero.mpr hp.ne'),
    ← Complex.ofReal_log hp.le,mul_assoc]
  congr 2
  push_cast
  ring

private theorem conjugate_row (z : ℂ) {n : ℕ} (hn : 0<n) :
    conj (row (conj z) n)=row z n := by
  have hp : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  have ha : (((n:ℝ):ℂ)).arg≠Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hp.le];exact Real.pi_ne_zero.symm
  unfold row mobCoeff
  rw [map_mul,←map_neg,←Complex.conj_cpow _ _ ha,Complex.conj_ofReal,map_intCast]

private theorem row_diagonal {X : ℝ} (s : ℂ) :
    (∑ n∈Icc 1 ⌊X⌋₊,row (s/2) n*conj (row (conj (s/2)) n))=squarefreeSection X s := by
  rw [squarefreeSection_eq_positive]
  apply sum_congr rfl
  intro n hn
  have hp : 0<(n:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hn).1
  rw [conjugate_row _ (mem_Icc.mp hn).1,row,mul_mul_mul_comm,
    ←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hp.ne'),show -(s/2)+-(s/2)=-s by ring]
  simp only [mobCoeff,Complex.ofReal_pow,Complex.ofReal_mul,Complex.ofReal_intCast,Complex.ofReal_natCast,
    pow_two,mul_comm]

private theorem row_gap_energy {X : ℝ} (hX : 1≤X) {z : ℂ} (hz : 1/2≤2*z.re) :
    (∑ n∈Icc 1 ⌊X⌋₊, ‖row z n‖^2/((n:ℝ)+1)⁻¹) ≤ 2*X*Real.sqrt X := by
  have hX0 := zero_le_one.trans hX
  have hterm (n : ℕ) (hn : n∈Icc 1 ⌊X⌋₊) :
      ‖row z n‖^2/((n:ℝ)+1)⁻¹ ≤ 2*Real.sqrt X := by
    have hN : (1:ℝ)≤n := by exact_mod_cast (mem_Icc.mp hn).1
    have hp := zero_lt_one.trans_le hN
    have hupper := (Nat.cast_le.mpr (mem_Icc.mp hn).2).trans (Nat.floor_le hX0)
    have hmu : ‖mobCoeff n‖^2≤1 := by
      rcases ArithmeticFunction.moebius_eq_or n with hh|hh|hh <;> simp [mobCoeff,hh]
    rw [row,norm_mul,mul_pow,Complex.norm_cpow_eq_rpow_re_of_pos hp,Complex.neg_re,
      ←Real.rpow_natCast ((n:ℝ)^(-z.re)) 2,←Real.rpow_mul hp.le,div_inv_eq_mul]
    have hpow : (n:ℝ)^(-z.re*(2:ℕ))≤(n:ℝ)^(-(1/2:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hN (by push_cast;linarith)
    calc
      _ ≤ (n:ℝ)^(-(1/2:ℝ))*((n:ℝ)+1) := by
        gcongr
        exact (mul_le_mul_of_nonneg_right hmu (Real.rpow_nonneg hp.le _)).trans (by rwa [one_mul])
      _ ≤ (n:ℝ)^(-(1/2:ℝ))*(2*n) := mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hp.le _)
      _ = 2*Real.sqrt n := by
        rw [Real.sqrt_eq_rpow,show (n:ℝ)^(-(1/2:ℝ))*(2*n)=2*((n:ℝ)^(-(1/2:ℝ))*n) by ring]
        conv_lhs => enter [2,2];rw [←Real.rpow_one (n:ℝ)]
        rw [←Real.rpow_add hp,show -(1/2:ℝ)+1=1/2 by norm_num]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hupper) (by norm_num)
  have hsum := sum_le_sum hterm
  simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel] at hsum
  exact hsum.trans (by nlinarith only [mul_le_mul_of_nonneg_right (Nat.floor_le hX0) (Real.sqrt_nonneg X)])

/-- Height correlation on an interval of length X², with section length
floor X and independent starting height. Its two vertical translates
are centered at s/2 and its complex conjugate. -/
def complexMoebiusReading (X A : ℝ) (s : ℂ) : ℂ :=
  (∫ t in A..(A+X^2),moebiusPoly ⌊X⌋₊ (s/2+(t:ℂ)*I)*conj
    (moebiusPoly ⌊X⌋₊ (conj (s/2)+(t:ℂ)*I)))/((X^2:ℝ):ℂ)

/-- Absolute error uniform in both vertical coordinates, including the
height of the spectral parameter, throughout the closed right half strip. -/
theorem complex_moebius_reading_error {X : ℝ} (hX : 1≤X) (A : ℝ) {s : ℂ} (hs : 1/2≤ s.re) :
    ‖complexMoebiusReading X A s-squarefreeSection X s‖ ≤ 104*X^(-(1/2:ℝ)) := by
  let S := Icc 1 ⌊X⌋₊
  let δ := fun n : ℕ => ((n:ℝ)+1)⁻¹
  have hp := zero_lt_one.trans_le hX
  have hx2 := sq_pos_of_pos hp
  have hgap (n : ℕ) (hn : n∈S) (m : ℕ) (hm : m∈S) (hh : n≠m) :
      δ n≤|(-Real.log n)-(-Real.log m)| := by
    simpa only [neg_sub_neg] using local_log_spacing (mem_Icc.mp hn).1 (mem_Icc.mp hm).1 hh.symm
  have ht := interval_mixed_gram_error (row (s/2)) (row (conj (s/2))) _ δ S
    (fun n _ => inv_pos.mpr (by positivity)) hgap A (X^2)
  have hz : 1/2≤2*(s/2).re := by rw [Complex.div_ofNat_re];linarith only [hs]
  have ha := Real.sqrt_le_sqrt (row_gap_energy hX hz)
  have hb := Real.sqrt_le_sqrt (row_gap_energy (z:=conj (s/2)) hX (by simpa only [Complex.conj_re] using hz))
  rw [row_diagonal] at ht
  unfold complexMoebiusReading
  simp only [vertical]
  rw [div_sub' (Complex.ofReal_ne_zero.mpr hx2.ne'),
    norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx2,div_le_iff₀ hx2]
  apply ht.trans
  calc
    _ ≤ 52*Real.sqrt (2*X*Real.sqrt X)*Real.sqrt (2*X*Real.sqrt X) := by gcongr
    _ = 104*X^(-(1/2:ℝ))*X^2 := by
      rw [mul_assoc,Real.mul_self_sqrt (by positivity),Real.sqrt_eq_rpow]
      rw [show 104*X^(-(1/2:ℝ))*X^2=104*(X^(-(1/2:ℝ))*X^2) by ring,
        ← Real.rpow_natCast X 2,←Real.rpow_add hp,show -(1/2:ℝ)+(2:ℕ)=1+1/2 by norm_num,
        Real.rpow_add hp,Real.rpow_one]
      ring

/-- Two moving height intervals, measured independently, recover the
same quotient as the algebraic dyadic difference. -/
theorem dyadic_moebius_reading_limit (A B : ℝ → ℝ) {s : ℂ} (hlo : 1/2<s.re) (hhi : s.re<1) :
    Tendsto (fun X : ℝ => complexMoebiusReading (2*X) (B X) s -
      (2:ℂ)^(1-s)*complexMoebiusReading X (A X) s) atTop
      (𝓝 ((1-(2:ℂ)^(1-s))*(riemannZeta s/riemannZeta (2*s)))) := by
  have err (Y H : ℝ → ℝ) (hY : Tendsto Y atTop atTop) :
      Tendsto (fun X => complexMoebiusReading (Y X) (H X) s-squarefreeSection (Y X) s) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hb := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).comp hY).const_mul 104
    rw [mul_zero] at hb
    exact squeeze_zero' (.of_forall fun _ => norm_nonneg _) ((hY.eventually_ge_atTop 1).mono
      fun X hx => complex_moebius_reading_error hx (H X) hlo.le) hb
  have he := (err _ B (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<2))).sub
    ((err id A tendsto_id).const_mul ((2:ℂ)^(1-s)))
  have h := (dyadic_squarefree_limit hlo hhi).add he
  simp only [mul_zero,sub_zero,add_zero] at h
  exact h.congr' (.of_forall fun X => by dsimp only [dyadicSquarefreeDifference,id];ring)

/-- RH is equivalent to absence of a vanishing dyadic two-length
correlation sequence for any choices of starting heights. -/
theorem rh_iff_dyadic_moebius_readings (A B : ℝ → ℝ) :
    RiemannHypothesis ↔ ∀ s : ℂ,1/2<s.re → s.re<1 →
      ¬∃ X : ℕ → ℝ,Tendsto X atTop atTop ∧ Tendsto (fun n =>
        complexMoebiusReading (2*X n) (B (X n)) s -
          (2:ℂ)^(1-s)*complexMoebiusReading (X n) (A (X n)) s) atTop (𝓝 0) := by
  rw [rh_iff_dyadic_squarefree_separation]
  apply forall_congr';intro s;apply forall_congr';intro hlo;apply forall_congr';intro hhi
  apply not_congr
  apply exists_congr;intro X
  constructor
  · rintro ⟨hX,hvan⟩
    have heq := tendsto_nhds_unique ((dyadic_squarefree_limit hlo hhi).comp hX) hvan
    exact ⟨hX,heq ▸ (dyadic_moebius_reading_limit A B hlo hhi).comp hX⟩
  · rintro ⟨hX,hvan⟩
    have heq := tendsto_nhds_unique ((dyadic_moebius_reading_limit A B hlo hhi).comp hX) hvan
    exact ⟨hX,heq ▸ (dyadic_squarefree_limit hlo hhi).comp hX⟩

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
