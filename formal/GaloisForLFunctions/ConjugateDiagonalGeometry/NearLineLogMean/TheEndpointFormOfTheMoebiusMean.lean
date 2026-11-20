import GaloisForLFunctions.HTGeometry.RiemannGaussian.MontgomeryVaughan.Final
import GaloisForLFunctions.HTGeometry.GeneralizedDirichletMeanValue
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheSharpHolderExponentForInfiniteGramRecovery
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheConstantTermOfTheSquarefreeHarmonicDiagonal
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheZeroForcesALogarithmicFloor

/-!
# A height-independent error for the sharp Möbius mean square

The two jumps of the interval window contribute two Hilbert forms, as in
the weighted Gram method of Gabet, Ferreira Da Costa and Lee
(arXiv:2611.18900, Proposition 2.4). Individual logarithmic spacings
charge each squarefree site a bounded price. This remains effective
when the section length reaches the full height interval.
-/

noncomputable section

open Finset Complex MeasureTheory Filter
open scoped Topology ComplexConjugate
open _root_.HTGeometry (genPoly genPoly_meanValue oscInt oscInt_eq)
open GaloisForLFunctions.HTGeometry (cdpoly cdterm)
open _root_.RHTower (edPoly edPoly_line mobCoeff)
open _root_.RHTower.Sieve (squarefreeDensity)
open GaloisForLFunctions.MultiscaleMollifiedZetaField
open GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval (local_log_spacing)
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private def phased (a : ℕ → ℂ) (f : ℕ → ℝ) (t : ℝ) (n : ℕ) : ℂ :=
  a n * cexp (I * ((f n : ℂ) * t))

private theorem phased_norm (a : ℕ → ℂ) (f : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    ‖phased a f t n‖ = ‖a n‖ := by simp [phased, norm_mul, Complex.norm_exp]

private theorem phased_cross (a : ℕ → ℂ) (f : ℕ → ℝ) (t : ℝ) (m n : ℕ) :
    phased a f t m * conj (phased a f t n) = a m * conj (a n) *
      cexp (I * ((f m-f n : ℝ) : ℂ) * t) := by
  simp only [phased, map_mul, ←Complex.exp_conj, Complex.conj_I, Complex.conj_ofReal]
  rw [show ∀ A B C D : ℂ, A*B*(C*D) = A*C*(B*D) by intros; ring, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private def endpointForm (a : ℕ → ℂ) (f : ℕ → ℝ) (S : Finset ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, ∑ m ∈ S.erase n, phased a f t m * conj (phased a f t n) / ((f m-f n : ℝ) : ℂ)

private theorem endpoint_bound (a : ℕ → ℂ) (f δ : ℕ → ℝ) (S : Finset ℕ)
    (hp : ∀ n ∈ S, 0 < δ n) (hgap : ∀ n ∈ S, ∀ m ∈ S, n ≠ m → δ n ≤ |f n-f m|) (t : ℝ) :
    ‖endpointForm a f S t‖ ≤ 13*∑ n ∈ S, ‖a n‖^2/δ n := by
  classical
  have hinj : Function.Injective (fun n : S => f n) := by
    intro n m he
    by_contra h
    have h' : (n:ℕ) ≠ m := fun hh => h (Subtype.ext hh)
    have := hgap n n.2 m m.2 h'
    have he' : f (n:ℕ) = f m := he
    rw [he', sub_self, abs_zero] at this
    exact (hp n n.2).not_ge this
  have hb := RiemannGaussian.MontgomeryVaughan.mvDiag_thirteen S (fun n => f n) (fun n => δ n)
    (fun n => phased a f t n) hinj (fun n => hp n n.2)
    (fun n m h => hgap n n.2 m m.2 (fun h' => h (Subtype.ext h')))
  -- The (m,n) term of the endpoint form; it vanishes on the diagonal.
  let g : ℕ → ℕ → ℂ := fun m n => phased a f t m * conj (phased a f t n) / ((f m - f n : ℝ) : ℂ)
  have hdiag (n : ℕ) : g n n = 0 := by simp [g]
  have hz (r s : S) : (if r = s then (0:ℂ) else
      phased a f t r * conj (phased a f t s) / ((f r - f s : ℝ) : ℂ)) = g r s := by
    split_ifs with he
    · subst he; exact (hdiag _).symm
    · rfl
  have hL : (∑ r : S, ∑ s : S, g r s) = ∑ m ∈ S, ∑ n ∈ S, g m n := by
    have h1 : ∀ r : S, (∑ s : S, g r s) = ∑ n ∈ S, g r n := fun r =>
      (Finset.sum_subtype S (fun _ => Iff.rfl) (g r)).symm
    rw [Fintype.sum_congr _ _ h1]
    exact (Finset.sum_subtype S (fun _ => Iff.rfl) (fun m => ∑ n ∈ S, g m n)).symm
  have hR : (∑ r : S, ‖phased a f t r‖ ^ 2 / δ r) = ∑ n ∈ S, ‖a n‖^2/δ n := by
    simp only [phased_norm]
    exact (Finset.sum_subtype S (fun _ => Iff.rfl) (fun n => ‖a n‖^2/δ n)).symm
  have hE : endpointForm a f S t = ∑ m ∈ S, ∑ n ∈ S, g m n := by
    rw [Finset.sum_comm (s := S) (t := S)]
    exact sum_congr rfl fun n _ => Finset.sum_erase S (f := fun m => g m n) (hdiag n)
  simp only [hz] at hb
  rw [hL, hR] at hb
  rw [hE]
  exact hb

/-- Signed interval error controlled by the weighted coefficient energy
with the local, rather than global, separation of each frequency. -/
theorem interval_gram_error_by_individual_gaps (a : ℕ → ℂ) (f δ : ℕ → ℝ) (S : Finset ℕ)
    (hp : ∀ n ∈ S, 0 < δ n) (hgap : ∀ n ∈ S, ∀ m ∈ S, n ≠ m → δ n ≤ |f n-f m|)
    (A L : ℝ) :
    |(∫ t in A..(A+L), ‖genPoly a f S t‖^2) - L*(∑ n ∈ S, ‖a n‖^2)| ≤
      26 * ∑ n ∈ S, ‖a n‖^2/δ n := by
  let B := A+L
  have hdiff (n : ℕ) (hn : n ∈ S) (m : ℕ) (hm : m ∈ S.erase n) :
      a m*conj (a n)*oscInt (f m-f n) A L =
        I⁻¹*(phased a f B m*conj (phased a f B n)/((f m-f n : ℝ) : ℂ)-
          phased a f A m*conj (phased a f A n)/((f m-f n : ℝ) : ℂ)) := by
    have hpos := (hp m (mem_erase.mp hm).2).trans_le (hgap _ (mem_erase.mp hm).2 _ hn (mem_erase.mp hm).1)
    rw [oscInt_eq _ _ _ (abs_pos.mp hpos), phased_cross, phased_cross]
    dsimp only [B]
    ring
  have hsum : (∑ n ∈ S, ∑ m ∈ S.erase n, a m*conj (a n)*oscInt (f m-f n) A L) =
      I⁻¹*(endpointForm a f S B-endpointForm a f S A) := by
    simp only [endpointForm, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact sum_congr rfl fun n hn => sum_congr rfl fun m hm => hdiff n hn m hm
  have hg := genPoly_meanValue a f S A L
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, ←Complex.ofReal_sum,
    ←Complex.ofReal_mul, intervalIntegral.integral_ofReal, hsum] at hg
  have hsig := congrArg Complex.re hg
  simp only [Complex.add_re, Complex.ofReal_re] at hsig
  rw [hsig, add_sub_cancel_left]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_inv, Complex.norm_I, inv_one, one_mul]
  have h1 := endpoint_bound a f δ S hp hgap A
  have h2 := endpoint_bound a f δ S hp hgap B
  exact (norm_sub_le _ _).trans (by linarith only [h1, h2])

/-- The initial value of an arbitrary Dirichlet polynomial identifies the
coefficient of each logarithmic frequency on a vertical translate. -/
theorem dirichlet_section_as_log_polynomial (a : ℕ → ℂ) (N : ℕ) (σ t : ℝ) :
    edPoly a (Icc 1 N) ((σ:ℂ)+(t:ℂ)*I) =
      genPoly (fun n => a n*((n:ℝ)^(-σ):ℝ)) (fun n => -Real.log n) (Icc 1 N) t := by
  rw [edPoly_line a (fun _ h => (mem_Icc.mp h).1)]
  unfold cdpoly cdterm genPoly
  refine sum_congr rfl fun n _ => ?_
  push_cast
  congr 2
  ring

/-- Coefficient of the nth critical-line Möbius frequency. -/
def criticalMoebiusAmplitude (n : ℕ) : ℂ := mobCoeff n * ((n:ℝ)^(-(1/2:ℝ)):ℝ)

theorem criticalMoebiusAmplitude_sq {n : ℕ} (hn : 0 < n) :
    ‖criticalMoebiusAmplitude n‖^2 = ((ArithmeticFunction.moebius n:ℤ):ℝ)^2 / n := by
  have hp : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  rw [criticalMoebiusAmplitude,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hp.le _),
    mul_pow, ←Real.rpow_natCast ((n:ℝ)^(-(1/2:ℝ))) 2, ←Real.rpow_mul hp.le,
    show -(1/2:ℝ)*(2:ℕ) = -1 by norm_num, Real.rpow_neg_one]
  simp [mobCoeff, ←Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv]

theorem critical_moebius_frequency_section (N : ℕ) (t : ℝ) :
    moebiusPoly N (linePoint t) = genPoly criticalMoebiusAmplitude (fun n => -Real.log n) (Icc 1 N) t := by
  rw [show criticalMoebiusAmplitude = fun n => mobCoeff n * ((n:ℝ)^(-(1/2:ℝ)):ℝ) from rfl]
  simpa [moebiusPoly, linePoint] using dirichlet_section_as_log_polynomial mobCoeff N (1/2) t

theorem critical_moebius_frequency_diagonal (N : ℕ) :
    (∑ n ∈ Icc 1 N, ‖criticalMoebiusAmplitude n‖^2) = harmonicMoebiusDiagonal N := by
  simp only [harmonicMoebiusDiagonal, Nat.floor_natCast]
  exact sum_congr rfl fun n hn => criticalMoebiusAmplitude_sq (mem_Icc.mp hn).1

/-- With the individual gaps 1/(n+1), the squared Möbius amplitudes
have total Hilbert cost at most two per integer. -/
theorem critical_moebius_gap_energy (N : ℕ) :
    (∑ n∈Icc 1 N, ‖criticalMoebiusAmplitude n‖^2/((n:ℝ)+1)⁻¹) ≤ 2*N := by
  let S := Icc 1 N
  let δ := fun n : ℕ => ((n:ℝ)+1)⁻¹
  have hterm (n : ℕ) (hn : n ∈ S) : ‖criticalMoebiusAmplitude n‖^2/δ n ≤ 2 := by
    have hpos := (mem_Icc.mp hn).1
    have hp : (1:ℝ) ≤ n := by exact_mod_cast hpos
    have hμ : ((ArithmeticFunction.moebius n : ℤ) : ℝ)^2 ≤ 1 := by
      rcases ArithmeticFunction.moebius_eq_or n with h|h|h <;> simp [h]
    rw [criticalMoebiusAmplitude_sq hpos]
    dsimp only [δ]
    rw [div_inv_eq_mul, div_mul_eq_mul_div, div_le_iff₀ (zero_lt_one.trans_le hp)]
    exact (mul_le_mul_of_nonneg_right hμ (by positivity)).trans (by linarith)
  have hsum := sum_le_sum hterm
  have hcard : S.card=N := by simp [S,Nat.card_Icc]
  rw [sum_const,hcard,nsmul_eq_mul,mul_comm (N:ℝ)] at hsum
  exact hsum

/-- The error in every sharp Möbius interval, with any starting point and
orientation, is at most 52 times the section length. -/
theorem sharp_moebius_diagonal_error (N : ℕ) (A L : ℝ) :
    |(∫ t in A..(A+L), ‖moebiusPoly N (linePoint t)‖^2) - L*harmonicMoebiusDiagonal N| ≤ 52*N := by
  let S := Icc 1 N
  let δ := fun n : ℕ => ((n:ℝ)+1)⁻¹
  have hgap (n : ℕ) (hn : n ∈ S) (m : ℕ) (hm : m ∈ S) (hne : n ≠ m) :
      δ n ≤ |(-Real.log n)-(-Real.log m)| := by
    simpa only [neg_sub_neg] using local_log_spacing (mem_Icc.mp hn).1 (mem_Icc.mp hm).1 hne.symm
  have hsum : (∑ n ∈ Icc 1 N, ‖criticalMoebiusAmplitude n‖^2 / δ n) ≤ 2*N :=
    critical_moebius_gap_energy N
  have ht := interval_gram_error_by_individual_gaps criticalMoebiusAmplitude (fun n => -Real.log n) δ
    (Icc 1 N) (fun _ _ => inv_pos.mpr (by positivity)) hgap A L
  rw [critical_moebius_frequency_diagonal N] at ht
  simp only [critical_moebius_frequency_section N]
  refine ht.trans ?_
  linarith only [hsum]

/-- Uniform in the starting height, the entire local mean equals the
squarefree density times log X plus the squarefree Laurent constant,
up to the endpoint cost X/L and the arithmetic error X⁻¹ᐟ². -/
theorem sharp_moebius_mean_two_errors (A : ℝ) {X L : ℝ} (hX : 1 ≤ X) (hL : 0 < L) :
    |(∫ t in A..(A+L), ‖moebiusPoly ⌊X⌋₊ (linePoint t)‖^2)/L -
      (squarefreeDensity*Real.log X+squarefreeHarmonicConstant)| ≤
      52*X/L+12*X^(-(1/2:ℝ)) := by
  let E := ∫ t in A..(A+L), ‖moebiusPoly ⌊X⌋₊ (linePoint t)‖^2
  let D := harmonicMoebiusDiagonal X
  have hfloor : harmonicMoebiusDiagonal ⌊X⌋₊ = D := by
    simp only [D,harmonicMoebiusDiagonal,Nat.floor_natCast]
  have hI := sharp_moebius_diagonal_error ⌊X⌋₊ A L
  rw [hfloor] at hI
  have hlow : |E/L-D| ≤ 52*X/L := by
    rw [div_sub' hL.ne',abs_div,abs_of_pos hL]
    exact div_le_div_of_nonneg_right (hI.trans (mul_le_mul_of_nonneg_left
      (Nat.floor_le (zero_le_one.trans hX)) (by norm_num))) hL.le
  have hD : |D-(squarefreeDensity*Real.log X+squarefreeHarmonicConstant)| ≤
      12*X^(-(1/2:ℝ)) := by
    simpa only [D,sub_add_eq_sub_sub] using squarefree_harmonic_finite_part hX
  exact (abs_sub_le (E/L) D _).trans (add_le_add hlow hD)

/-- At every sublinear power length the ordinary second-order constant
has a limit, uniformly along arbitrary moving starting heights. -/
theorem sublinear_moebius_mean_constant (A : ℝ → ℝ) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    Tendsto (fun T : ℝ => (∫ t in (A T)..(A T+T), ‖moebiusPoly ⌊T^θ⌋₊ (linePoint t)‖^2)/T -
      squarefreeDensity*θ*Real.log T) atTop (𝓝 squarefreeHarmonicConstant) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hx := tendsto_rpow_neg_atTop (sub_pos.mpr hθ1)
  have hy := tendsto_rpow_neg_atTop (div_pos hθ (by norm_num : (0:ℝ) < 2))
  have hzero := (hx.const_mul 52).add (hy.const_mul 12)
  simp only [mul_zero,add_zero] at hzero
  refine squeeze_zero' (.of_forall fun T => norm_nonneg _) ?_ hzero
  filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
  have hp := zero_lt_one.trans_le hT
  have hb := sharp_moebius_mean_two_errors (A T) (Real.one_le_rpow hT hθ.le) hp
  rw [Real.log_rpow hp,←Real.rpow_mul hp.le,
    show θ * -(1/2:ℝ) = -(θ/2) by ring] at hb
  rw [Real.norm_eq_abs, show squarefreeDensity*θ*Real.log T =
    squarefreeDensity*(θ*Real.log T) by ring,←sub_add_eq_sub_sub]
  refine hb.trans_eq ?_
  congr 1
  rw [show -(1-θ)=θ-1 by ring, Real.rpow_sub hp,Real.rpow_one]
  ring

/-- At section length equal to interval length the logarithmic leading
coefficient is still 6/π², uniformly in the starting point. -/
theorem full_height_moebius_mean_leading (A : ℝ → ℝ) :
    Tendsto (fun T : ℝ => (∫ t in (A T)..(A T+T), ‖moebiusPoly ⌊T⌋₊ (linePoint t)‖^2)/(T*Real.log T))
      atTop (𝓝 squarefreeDensity) := by
  have hlog := Real.tendsto_log_atTop
  have hzero := hlog.inv_tendsto_atTop.const_mul (64+|squarefreeHarmonicConstant|)
  simp only [mul_zero] at hzero
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero' (.of_forall fun _ => norm_nonneg _) ?_ hzero
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  have hp := zero_lt_one.trans hT
  have hl := Real.log_pos hT
  have hb := sharp_moebius_mean_two_errors (A T) hT.le hp
  let W := (∫ t in (A T)..(A T+T), ‖moebiusPoly ⌊T⌋₊ (linePoint t)‖^2)/T
  have hbnd : |W-squarefreeDensity*Real.log T| ≤ 64+|squarefreeHarmonicConstant| := by
    have htail := Real.rpow_le_one_of_one_le_of_nonpos hT.le (by norm_num : -(1/2:ℝ) ≤ 0)
    have hc : 52*T/T = 52 := mul_div_cancel_right₀ _ hp.ne'
    rw [hc] at hb
    change |W - _| ≤ _ at hb
    have hdiff := abs_sub_le W (squarefreeDensity*Real.log T+squarefreeHarmonicConstant) (squarefreeDensity*Real.log T)
    rw [add_sub_cancel_left] at hdiff
    linarith only [hb,htail,hdiff]
  change ‖_/(T*Real.log T)-squarefreeDensity‖ ≤ _
  rw [Real.norm_eq_abs, ←div_div,show W/Real.log T-squarefreeDensity =
    (W-squarefreeDensity*Real.log T)/Real.log T by field_simp,abs_div,abs_of_pos hl]
  exact (div_le_div_of_nonneg_right hbnd hl.le).trans_eq (div_eq_mul_inv _ _)


end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
