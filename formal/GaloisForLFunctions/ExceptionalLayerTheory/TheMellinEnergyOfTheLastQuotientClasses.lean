import GaloisForLFunctions.ExceptionalLayerTheory.TheLastQuotientClassDetectsEveryRightZero
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheHalfDampedReceiverIsTheBoundaryEnergyOfItsDirichletSeries
import GaloisForLFunctions.ArithmeticDefectRigidity.TheRenormalizedCofactorActsOnPowerRowsByZeta
import GaloisForLFunctions.RHTower.MellinLinePolarization

/-!
# Mellin energy of the last quotient classes

The last-class symbol is the sum of Mellin cells immediately preceding a
multiple of the width. Its squared line norm after division by the frequency
is another value of the same symbol: the cell indicator is idempotent.
-/

noncomputable section

open Complex MeasureTheory Filter Finset Set
open scoped Interval
open GaloisForLFunctions.TransHorizonIncidenceMechanics

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The quotient cell immediately preceding a multiple of the width. -/
def lastCellIndicator (q n : ℕ) : ℝ := if q ∣ n+1 then 1 else 0

private theorem lastCellIndicator_zero {q : ℕ} (hq : 2≤q) : lastCellIndicator q 0=0 :=
  if_neg (fun h => by have := Nat.le_of_dvd (by omega : 0<0+1) h; omega)

private theorem lastCellIndicator_bound (q : ℕ) {n : ℕ} (hn : 1≤n) :
    |lastCellIndicator q n| ≤ 1*(n:ℝ)^(1/2:ℝ) := by
  have h := Real.one_le_rpow (by exact_mod_cast hn : 1≤(n:ℝ)) (by norm_num : (0:ℝ)≤1/2)
  unfold lastCellIndicator
  split <;> simp only [abs_one,abs_zero,one_mul] <;> linarith only [h]

/-- The indicator selects exactly the Mellin cells contributing to the
Hurwitz difference, throughout its half-plane of absolute cell convergence. -/
theorem lastQuotientClassSymbol_eq_tsum_cells {q : ℕ} (hq : 2≤q) {s : ℂ} (hs : 0<s.re) :
    lastQuotientClassSymbol q s = ∑' n : ℕ, (lastCellIndicator q n : ℂ)*cmellinCell s n := by
  let u := 1/(q:ℝ)
  have hqR : 2≤(q:ℝ) := by exact_mod_cast hq
  have hp : 0<(q:ℝ) := by linarith only [hqR]
  have hu : 0<u := one_div_pos.mpr hp
  have hhalf : u≤1/2 := one_div_le_one_div_of_le (by norm_num) hqR
  let f := fun k : ℕ => q*(k+1)-1
  have hf (k : ℕ) : f k+1=q*(k+1) := by
    have hh := Nat.mul_pos (by omega : 0<q) (Nat.succ_pos k)
    dsimp only [f]; omega
  have hinj : Function.Injective f := by
    intro i j e
    have hh := congrArg (·+1) e
    rw [hf,hf] at hh
    exact Nat.succ.inj (Nat.eq_of_mul_eq_mul_left (by omega : 0<q) hh)
  let F := fun n : ℕ => (lastCellIndicator q n : ℂ)*cmellinCell s n
  have hsupport : Function.support F ⊆ Set.range f := by
    intro n hn
    by_cases hd : q ∣ n+1
    · obtain ⟨k,he⟩ := hd
      cases k with
      | zero => simp at he
      | succ k => exact ⟨k,by have := hf k; omega⟩
    · exact (hn (by simp [F,lastCellIndicator,hd])).elim
  have hreduce : (∑' n : ℕ, F n) = ∑' k : ℕ, F (f k) := by
    rw [← tsum_subtype_eq_of_support_subset hsupport]
    exact ((Equiv.ofInjective f hinj).tsum_eq fun i => F i.val).symm
  change _ = ∑' n : ℕ, F n
  rw [hreduce,lastQuotientClassSymbol,_root_.RHTower.hurwitzZeta_neg_sub_riemannZeta_eq hu hhalf hs,
    _root_.RHTower.shiftDiffSeries,← tsum_mul_left]
  apply tsum_congr
  intro k
  have hd : q ∣ f k+1 := ⟨k+1,hf k⟩
  have hscale : (f k:ℝ)=(q:ℝ)*((k:ℝ)+1-u) := by
    have hcast : (f k:ℝ)+1=(q:ℝ)*((k:ℝ)+1) := by exact_mod_cast hf k
    dsimp only [u]; field_simp; linear_combination (q:ℝ)*hcast
  have hnext : (f k:ℝ)+1=(q:ℝ)*((k:ℝ)+1) := by exact_mod_cast hf k
  have hl : 0≤(k:ℝ)+1-u := by linarith only [hhalf,Nat.cast_nonneg k]
  simp only [F,lastCellIndicator,if_pos hd,ofReal_one,one_mul,cmellinCell,
    _root_.RHTower.shiftDiffTerm,← sub_eq_add_neg]
  rw [hnext,hscale,ofReal_mul,ofReal_mul,Complex.mul_cpow_ofReal_nonneg hp.le hl,
    Complex.mul_cpow_ofReal_nonneg hp.le (by positivity),mul_sub,ofReal_natCast]

private theorem bounded_step_mellin {A : ℕ → ℝ} (hA0 : A 0 = 0) (hA : ∀ n, |A n| ≤ 1)
    {s : ℂ} (hs0 : 0 < s.re) :
    mellin (stepSource A) (-s) = (∑' n, (A n:ℂ)*cmellinCell s n)/s := by
  have hsne : s ≠ 0 := by intro h; rw [h] at hs0; simp at hs0
  set k : ℝ → ℂ := fun y => (y : ℂ) ^ (-s - 1)
  have hk : ContinuousOn k (Ici 1) := fun y hy => by
    have hy0 : (0 : ℝ) < y := by linarith [mem_Ici.mp hy]
    exact ((hasDerivAt_ofReal_cpow_neg (w := s + 1) hy0).continuousAt.congr
      (Eventually.of_forall fun z => by simp only [k]; congr 1; ring)).continuousWithinAt
  have hkpiece : ∀ n : ℕ, ∫ y in ((n : ℝ) + 1)..((n : ℝ) + 2), k y = cmellinCell s (n + 1) / s := by
    intro n
    have h0 : (0 : ℝ) ∉ uIcc ((n : ℝ) + 1) ((n : ℝ) + 2) := by
      rw [uIcc_of_le (by linarith)]; intro h; linarith [h.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [integral_cpow (Or.inr ⟨by intro h; apply hsne; linear_combination -h, h0⟩)]
    simp only [cmellinCell, show -s - 1 + 1 = -s by ring]
    push_cast
    field_simp
    ring_nf
  have hknorm : ∀ n : ℕ, ∫ y in ((n : ℝ) + 1)..((n : ℝ) + 2), ‖k y‖ ≤ ((n : ℝ) + 1) ^ (-s.re - 1) := by
    intro n
    have hconst : ∫ _y in ((n : ℝ) + 1)..((n : ℝ) + 2), ((n : ℝ) + 1) ^ (-s.re - 1) =
        ((n : ℝ) + 1) ^ (-s.re - 1) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    rw [← hconst]
    refine intervalIntegral.integral_mono_on (by linarith) ?_ (by simp) fun y hy => ?_
    · exact (hk.mono (by
        rw [← uIcc_of_le (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith)]
        intro z hz; rw [uIcc_of_le (by linarith)] at hz
        exact le_trans (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hz.1)).norm.intervalIntegrable_of_Icc
          (by linarith)
    · have hy0 : (0 : ℝ) < y := by linarith [hy.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      simp only [k]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]
      simp only [sub_re, neg_re, one_re]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hy.1 (by linarith)
  have hseries := Real.summable_nat_rpow.mpr (show -s.re-1 < -1 by linarith only [hs0])
  have hsum : Summable (fun n : ℕ => |A (n+1)| * ∫ y in ((n:ℝ)+1)..((n:ℝ)+2), ‖k y‖) := by
    have hb : Summable (fun n : ℕ => ((n:ℝ)+1)^(-s.re-1)) := by
      simpa only [Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr hseries
    refine hb.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (intervalIntegral.integral_nonneg
      (by linarith) (fun _ _ => norm_nonneg _))) (fun n => ?_)
    exact (mul_le_of_le_one_left (intervalIntegral.integral_nonneg (by linarith)
      (fun _ _ => norm_nonneg _)) (hA (n+1))).trans (hknorm n)
  obtain ⟨hint, heq⟩ := integral_Ioi_one_stepSource_mul A hk hsum
  have hmel : mellin (stepSource A) (-s) = ∫ y in Ioi (1 : ℝ), stepSource A y * k y := by
    rw [mellin]
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi zero_le_one) fun y hy => ?_]
    · refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
      simp only [k, smul_eq_mul]; rw [mul_comm]
    · have hy1 : ¬ 1 < y := hy.2
      simp [stepSource, hy1]
  rw [hmel, heq]
  simp_rw [hkpiece]
  have hser : Summable (fun n : ℕ => (A n:ℂ)*cmellinCell s n) := by
    apply (hseries.mul_left ‖s‖).of_norm_bounded
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hA0]; positivity
    · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      apply (mul_le_of_le_one_left (norm_nonneg _) (hA _)).trans
      have hb := (norm_cmellinCell_le hs0 hn).trans (mul_le_mul_of_nonneg_left
        (mellinCell_bounds hs0 hn).2 (div_nonneg (norm_nonneg _) hs0.le))
      exact hb.trans_eq (by field_simp)
  rw [hser.tsum_eq_zero_add,hA0]
  simp only [ofReal_zero,zero_mul,zero_add]
  rw [← tsum_div_const]
  exact tsum_congr fun n => by ring

private theorem indicator_abs_le_one (q n : ℕ) : |lastCellIndicator q n| ≤ 1 := by
  unfold lastCellIndicator
  split <;> norm_num

theorem mellin_lastCellIndicator {q : ℕ} (hq : 2≤q) {s : ℂ} (hs : 0<s.re) :
    mellin (stepSource (lastCellIndicator q)) (-s)=lastQuotientClassSymbol q s/s := by
  rw [bounded_step_mellin (lastCellIndicator_zero hq) (indicator_abs_le_one q) hs,
    lastQuotientClassSymbol_eq_tsum_cells hq hs]

private theorem bounded_log_step {A : ℕ → ℝ} (hA : ∀ n, |A n| ≤ 1) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (_root_.RHTower.logMellinLineSource (stepSource A) (-σ)) ∧
      MemLp (_root_.RHTower.logMellinLineSource (stepSource A) (-σ)) 2 volume := by
  let g := logStepSource A σ
  have he : _root_.RHTower.logMellinLineSource (stepSource A) (-σ) = g := by
    funext u
    simp [_root_.RHTower.logMellinLineSource,g,logStepSource,Complex.real_smul]
  rw [he]
  have hmeas := aestronglyMeasurable_logStepSource A σ
  let H (a u : ℝ) := (Iic (0:ℝ)).indicator (fun t => Real.exp (a*t)) u
  have hI {a : ℝ} (ha : 0 < a) : Integrable (H a) :=
    IntegrableOn.integrable_indicator (integrableOn_exp_mul_Iic ha 0) measurableSet_Iic
  have hnorm (u : ℝ) : ‖g u‖ ≤ H σ u := by
    by_cases hu : u ≤ 0
    · rw [show H σ u=Real.exp (σ*u) from indicator_of_mem hu _]
      simp only [g,logStepSource,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply mul_le_of_le_one_right (Real.exp_pos _).le
      unfold stepSource
      split
      · simpa using hA _
      · simp
    · have he : ¬1 < Real.exp (-u) := by rw [not_lt,Real.exp_le_one_iff]; linarith only [not_le.mp hu]
      simp [g,logStepSource,stepSource,he,H,hu]
  refine ⟨(hI hσ).mono' hmeas (Eventually.of_forall hnorm),?_⟩
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  apply (hI (show 0 < 2*σ by linarith only [hσ])).mono' (hmeas.norm.pow 2)
  apply Eventually.of_forall
  intro u
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  apply (pow_le_pow_left₀ (norm_nonneg _) (hnorm u) 2).trans_eq
  by_cases hu : u ≤ 0
  · simp only [H,Set.indicator_of_mem (mem_Iic.mpr hu),← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  · simp [H,hu]

/-- Pairing two quotient classes intersects their divisibility conditions,
so their whole-line Mellin inner product is the symbol for their lcm. -/
theorem lastQuotientClassSymbol_crossEnergy {q r : ℕ} (hq : 2 ≤ q) (hr : 2 ≤ r) {σ : ℝ}
    (hσ : 0 < σ) :
    (∫ t : ℝ, (starRingEnd ℂ) (lastQuotientClassSymbol r ((σ:ℂ)+t*I)/((σ:ℂ)+t*I)) *
      (lastQuotientClassSymbol q ((σ:ℂ)+t*I)/((σ:ℂ)+t*I))) =
      (Real.pi/σ:ℝ)*lastQuotientClassSymbol (q.lcm r) (2*σ:ℝ) := by
  let A := fun q => stepSource (lastCellIndicator q)
  have hL := bounded_log_step (indicator_abs_le_one r) hσ
  have hR := bounded_log_step (indicator_abs_le_one q) hσ
  have h := _root_.RHTower.integral_conj_mellin_line_mul_mellin_line hL.1 hL.2 hR.1 hR.2
  have hab : (fun x : ℝ => (starRingEnd ℂ) (A r x)*A q x)=A (q.lcm r) := by
    funext x
    simp only [A,stepSource]
    split_ifs
    · unfold lastCellIndicator
      simp only [Nat.lcm_dvd_iff]
      split_ifs <;> simp_all
    · simp
  change (∫ t : ℝ, (starRingEnd ℂ) (mellin (A r) ((-σ:ℝ)+t*I)) *
    mellin (A q) ((-σ:ℝ)+t*I)) = _ at h
  rw [hab] at h
  have hlcm : 2 ≤ q.lcm r := hq.trans (Nat.le_of_dvd
    (Nat.lcm_pos (by omega : 0 < q) (by omega : 0 < r)) (Nat.dvd_lcm_left q r))
  have hs : (2*( -σ):ℝ) = -(2*σ) := by ring
  rw [hs,ofReal_neg,mellin_lastCellIndicator hlcm (by simp; linarith only [hσ])] at h
  have ht (a : ℕ) (ha : 2 ≤ a) (t : ℝ) :
      mellin (A a) ((-σ:ℝ)+t*I) =
      lastQuotientClassSymbol a ((σ:ℂ)+(-t)*I)/((σ:ℂ)+(-t)*I) := by
    rw [show ((-σ:ℝ):ℂ)+t*I = -((σ:ℂ)+(-t)*I) by push_cast; ring]
    exact mellin_lastCellIndicator ha (by simpa using hσ)
  simp_rw [ht r hr,ht q hq] at h
  let f (t : ℝ) := (starRingEnd ℂ) (lastQuotientClassSymbol r ((σ:ℂ)+t*I)/((σ:ℂ)+t*I)) *
    (lastQuotientClassSymbol q ((σ:ℂ)+t*I)/((σ:ℂ)+t*I))
  change (∫ t : ℝ, f (-t)) = _ at h
  rw [MeasureTheory.integral_neg_eq_self] at h
  exact h.trans (by push_cast; field_simp)

/-- Exact energy on a vertical line. Its dependence on the width is given by
the real symbol at twice the real part. -/
theorem lastQuotientClassSymbol_lineEnergy {q : ℕ} (hq : 2≤q) {σ : ℝ} (hσ : 1/2<σ) :
    (∫ t : ℝ, ‖lastQuotientClassSymbol q ((σ:ℂ)+t*I)/((σ:ℂ)+t*I)‖^2) =
      Real.pi/σ*(lastQuotientClassSymbol q (2*σ:ℝ)).re := by
  have he := lineEnergy_stepSource_eq (lastCellIndicator_zero hq)
    (fun _ hn => lastCellIndicator_bound q hn) hσ
  have hpt (t : ℝ) := mellin_lastCellIndicator hq (s := (σ:ℂ)+t*I) (by simp; linarith only [hσ])
  simp_rw [hpt] at he
  rw [he,lastQuotientClassSymbol_eq_tsum_cells hq (by simp only [ofReal_re]; linarith only [hσ])]
  congr 1
  have hcast (n : ℕ) : (lastCellIndicator q n:ℂ)*cmellinCell (2*σ:ℝ) n =
      ((lastCellIndicator q n^2*mellinCell (2*σ) n : ℝ):ℂ) := by
    rw [ofReal_mul,ArithmeticDefectRigidity.ofReal_mellinCell]
    unfold lastCellIndicator
    split <;> simp [cmellinCell]
  simp_rw [hcast]
  rw [← ofReal_tsum,ofReal_re]

/-- The weighted square sum over widths converges precisely below the real
part of the frequency. Equality gives harmonic divergence. -/
theorem lastQuotientClassSymbol_weighted_square_summable {s : ℂ} (hs : 0 < s.re) (σ : ℝ) :
    Summable (fun q : ℕ => (q:ℝ)^(2*σ+1)*‖lastQuotientClassSymbol q s‖^2) ↔ σ<s.re := by
  let A := ‖s*riemannZeta (s+1)‖
  have hn : s ≠ 0 := fun e => by simpa [e] using hs
  have hA : 0<A := norm_pos_iff.mpr (mul_ne_zero hn
    (riemannZeta_ne_zero_of_one_lt_re (by simpa using hs)))
  let F (q : ℕ) := (q:ℝ)^(2*σ+1)*‖lastQuotientClassSymbol q s‖^2
  let e := 2*σ-2*s.re-1
  let U (q : ℕ) := (q:ℂ)^(s+1)*lastQuotientClassSymbol q s
  have hF (q : ℕ) : 0 ≤ F q := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _)
  obtain ⟨C,h⟩ := lastQuotientClassSymbol_scaled_error hs
  obtain ⟨B,hB⟩ := exists_nat_gt (C/(A/2))
  have hcmp : ∀ᶠ q : ℕ in atTop, (A/2)^2*(q:ℝ)^e ≤ F q ∧ F q ≤ (2*A)^2*(q:ℝ)^e := by
    filter_upwards [eventually_ge_atTop B,eventually_ge_atTop 2] with q hq h2
    have hqp : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
    have he := h q h2
    have hBq : (B:ℝ)≤q := by exact_mod_cast hq
    have hc := (div_lt_iff₀ (half_pos hA)).mp (hB.trans_le hBq)
    have hdiff := ((abs_norm_sub_norm_le (U q) (s*riemannZeta (s+1))).trans he).trans
      ((div_le_iff₀ hqp).mpr (le_of_lt (by linarith only [hc] : C < A/2*q)))
    change |‖U q‖-A| ≤ A/2 at hdiff
    have hv := abs_le.mp hdiff
    have hl := (sq_le_sq₀ (half_pos hA).le (norm_nonneg _)).mpr (by linarith only [hv.1] : A/2 ≤ ‖U q‖)
    have hu := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (by linarith only [hv.2,hA] : ‖U q‖ ≤ 2*A)
    have heq : F q=‖U q‖^2*(q:ℝ)^e := by
      simp only [F,U,norm_mul,mul_pow]
      have hz : ‖(q:ℂ)^(s+1)‖=(q:ℝ)^(s.re+1) := by
        simpa only [Complex.ofReal_natCast,Complex.add_re,Complex.one_re] using
          Complex.norm_cpow_eq_rpow_re_of_pos hqp (s+1)
      rw [hz,← Real.rpow_natCast ((q:ℝ)^(s.re+1)),← Real.rpow_mul hqp.le]
      rw [mul_right_comm,← Real.rpow_add hqp]
      congr 2
      dsimp only [e]; push_cast; ring
    rw [heq]
    exact ⟨mul_le_mul_of_nonneg_right hl (Real.rpow_nonneg hqp.le _),
      mul_le_mul_of_nonneg_right hu (Real.rpow_nonneg hqp.le _)⟩
  change Summable F ↔ _
  have hpow : Summable (fun q : ℕ => (q:ℝ)^e) ↔ σ<s.re := by
    rw [Real.summable_nat_rpow]
    dsimp only [e]
    constructor <;> intro h <;> linarith only [h]
  constructor
  · intro hf
    apply hpow.mp
    apply (hf.div_const ((A/2)^2)).of_norm_bounded_eventually_nat
    filter_upwards [hcmp] with q hq
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
      le_div_iff₀ (sq_pos_of_pos (half_pos hA)),mul_comm]
    exact hq.1
  · intro hsig
    apply ((hpow.mpr hsig).mul_left ((2*A)^2)).of_norm_bounded_eventually_nat
    filter_upwards [hcmp] with q hq
    rw [Real.norm_eq_abs,abs_of_nonneg (hF q)]
    exact hq.2

end GaloisForLFunctions.ExceptionalLayerTheory
