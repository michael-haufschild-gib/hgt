import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheEndpointFormOfTheMoebiusMean
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheShiftedSquarefreeHarmonicDiagonal

/-!
# Microscopic shifts of the critical Möbius polynomial

The bilinear Montgomery–Vaughan inequality bounds both endpoints of
the time average. Its diagonal is the Fourier transform of squarefree
harmonic mass. At a shift of order one over log X the uniform frequency
law gives the leading term and the Laurent constant gives the next term.
-/

noncomputable section
open Finset Complex MeasureTheory Filter
open scoped ComplexConjugate Topology
open _root_.HTGeometry (genPoly genPoly_meanValue_bilinear oscInt oscInt_eq oscInt_zero)
open _root_.RHTower (logPhase norm_logPhase)
open _root_.RHTower.Sieve (squarefreeDensity)
open GaloisForLFunctions.MultiscaleMollifiedZetaField
open GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval (local_log_spacing)
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private def mixedPhase (a : ℕ → ℂ) (f : ℕ → ℝ) (t : ℝ) (n : ℕ) :=
  a n * Complex.exp (I*((f n:ℂ)*(t:ℂ)))

private theorem mixedPhase_norm (a : ℕ → ℂ) (f : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    ‖mixedPhase a f t n‖ = ‖a n‖ := by
  simp [mixedPhase,norm_mul,Complex.norm_exp,Complex.mul_re,Complex.mul_im]

private theorem mixedPhase_product (a b : ℕ → ℂ) (f : ℕ → ℝ) (t : ℝ) (n m : ℕ) :
    mixedPhase a f t n * conj (mixedPhase b f t m) =
      a n * conj (b m) * Complex.exp (I*((f n-f m:ℝ):ℂ)*t) := by
  simp only [mixedPhase,map_mul,←Complex.exp_conj,Complex.conj_I,Complex.conj_ofReal]
  rw [show ∀ A B C D : ℂ,A*B*(C*D)=A*C*(B*D) by intros;ring,←Complex.exp_add]
  congr 2
  push_cast
  ring

private def mixedBoundary (a b : ℕ → ℂ) (f : ℕ → ℝ) (S : Finset ℕ) (t : ℝ) : ℂ :=
  ∑ n∈S,∑ m∈S,mixedPhase a f t n*conj (mixedPhase b f t m)/((f n-f m:ℝ):ℂ)

private theorem mixedBoundary_bound (a b : ℕ → ℂ) (f δ : ℕ → ℝ) (S : Finset ℕ)
    (hp : ∀ n∈S,0<δ n) (hgap : ∀ n∈S,∀ m∈S,n≠m → δ n≤|f n-f m|) (t : ℝ) :
    ‖mixedBoundary a b f S t‖ ≤
      26*Real.sqrt (∑ n∈S,‖a n‖^2/δ n)*Real.sqrt (∑ n∈S,‖b n‖^2/δ n) := by
  classical
  have hinj : Function.Injective (fun n : S => f n) := by
    intro n m he
    by_contra hh
    have h := hgap n n.2 m m.2 (fun h => hh (Subtype.ext h))
    rw [he,sub_self,abs_zero] at h
    exact (hp n n.2).not_ge h
  have h := RiemannGaussian.MontgomeryVaughan.mvHilbert_twentySix S (fun n => f n)
    (fun n => δ n) (fun n => mixedPhase a f t n) (fun n => mixedPhase b f t n) hinj
    (fun n => hp n n.2) (fun n m hh => hgap n n.2 m m.2 (fun h => hh (Subtype.ext h)))
  have hz (n m : S) : (if n=m then (0:ℂ) else
      mixedPhase a f t n*conj (mixedPhase b f t m)/((f n-f m:ℝ):ℂ)) =
        mixedPhase a f t n*conj (mixedPhase b f t m)/((f n-f m:ℝ):ℂ) := by
    split_ifs with he
    · subst m; simp
    · rfl
  simpa only [hz,mixedPhase_norm,Finset.sum_coe_sort,mixedBoundary] using h

/-- The covariance of two arbitrary finite coefficient rows has a
location-independent error governed by their individual gap energies. -/
theorem interval_mixed_gram_error (a b : ℕ → ℂ) (f δ : ℕ → ℝ) (S : Finset ℕ)
    (hp : ∀ n∈S,0<δ n) (hgap : ∀ n∈S,∀ m∈S,n≠m → δ n≤|f n-f m|) (A L : ℝ) :
    ‖(∫ t in A..(A+L),genPoly a f S t*conj (genPoly b f S t)) -
      (L:ℂ)*(∑ n∈S,a n*conj (b n))‖ ≤
      52*Real.sqrt (∑ n∈S,‖a n‖^2/δ n)*Real.sqrt (∑ n∈S,‖b n‖^2/δ n) := by
  let B := A+L
  let D := fun (t:ℝ) n m => mixedPhase a f t n*conj (mixedPhase b f t m)/((f n-f m:ℝ):ℂ)
  have he (n : ℕ) (hn : n∈S) (m : ℕ) (hm : m∈S) :
      a n*conj (b m)*oscInt (f n-f m) A L =
        (if m=n then (L:ℂ)*(a n*conj (b n)) else 0) + I⁻¹*(D B n m-D A n m) := by
    by_cases hh : m=n
    · subst m; simp [D,oscInt_zero,mul_comm (L:ℂ)]
    · have hpos := (hp n hn).trans_le (hgap n hn m hm hh.symm)
      rw [if_neg hh,zero_add,oscInt_eq _ _ _ (abs_pos.mp hpos)]
      dsimp only [D,B]
      rw [mixedPhase_product,mixedPhase_product]
      ring
  have h := genPoly_meanValue_bilinear a b f f S S A L
  rw [h]
  have hsum : (∑ n∈S,∑ m∈S,a n*conj (b m)*oscInt (f n-f m) A L) =
      (L:ℂ)*(∑ n∈S,a n*conj (b n))+I⁻¹*(mixedBoundary a b f S B-mixedBoundary a b f S A) := by
    calc
      _ = ∑ n∈S,∑ m∈S,((if m=n then (L:ℂ)*(a n*conj (b n)) else 0)+I⁻¹*(D B n m-D A n m)) :=
        sum_congr rfl fun n hn => sum_congr rfl fun m hm => he n hn m hm
      _ = _ := by
        simp only [sum_add_distrib,Finset.sum_ite_eq',Finset.mul_sum,mixedBoundary,D,
          Finset.sum_sub_distrib,mul_sub]
        congr 1
        exact sum_congr rfl fun n hn => if_pos hn
  rw [hsum,add_sub_cancel_left,norm_mul,norm_inv,Complex.norm_I,inv_one,one_mul]
  exact (norm_sub_le _ _).trans (by linarith only [mixedBoundary_bound a b f δ S hp hgap B,
    mixedBoundary_bound a b f δ S hp hgap A])

private theorem shifted_frequency_section (N : ℕ) (h t : ℝ) :
    moebiusPoly N (linePoint (t+h)) =
      genPoly (fun n => criticalMoebiusAmplitude n * logPhase h n)
        (fun n => -Real.log n) (Icc 1 N) t := by
  rw [critical_moebius_frequency_section]
  unfold genPoly
  refine sum_congr rfl fun n _ => ?_
  rw [mul_assoc,logPhase,←Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Uniform error for the literal two-height critical-line correlation.
The shift and the initial height can vary independently. -/
theorem critical_moebius_covariance_error (N : ℕ) (A L h : ℝ) :
    ‖(∫ t in A..(A+L),moebiusPoly N (linePoint (t+h))*conj (moebiusPoly N (linePoint t))) -
      (L:ℂ)*weightedSquarefree N (logPhase h)‖ ≤ 104*N := by
  let a := criticalMoebiusAmplitude
  let b := fun n : ℕ => a n*logPhase h n
  let f := fun n : ℕ => -Real.log n
  let δ := fun n : ℕ => ((n:ℝ)+1)⁻¹
  let S := Icc 1 N
  have hg (n : ℕ) (hn : n∈S) (m : ℕ) (hm : m∈S) (hh : n≠m) : δ n ≤ |f n-f m| := by
    simpa only [δ,f,neg_sub_neg] using local_log_spacing (mem_Icc.mp hn).1 (mem_Icc.mp hm).1 hh.symm
  have hb (n : ℕ) : ‖b n‖=‖a n‖ := by simp only [b,norm_mul,norm_logPhase,mul_one]
  have hd : (∑ n∈S,b n*conj (a n))=weightedSquarefree N (logPhase h) := by
    unfold weightedSquarefree
    rw [Nat.floor_natCast]
    refine sum_congr rfl fun n hn => ?_
    rw [b,mul_right_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq]
    rw [show a n=criticalMoebiusAmplitude n by rfl,criticalMoebiusAmplitude_sq (mem_Icc.mp hn).1]
    rw [mul_comm]
    rfl
  have ht := interval_mixed_gram_error b a f δ S (fun _ _ => inv_pos.mpr (by positivity)) hg A L
  simp only [hb,hd,mul_assoc,Real.mul_self_sqrt (Finset.sum_nonneg (fun n _ =>
    div_nonneg (sq_nonneg _) (inv_nonneg.mpr (by positivity))))] at ht
  have hsum : (∑ n∈S, ‖a n‖^2/δ n) ≤ 2*N := critical_moebius_gap_energy N
  simp only [shifted_frequency_section,critical_moebius_frequency_section]
  exact ht.trans (by linarith only [hsum])


/-- Mean correlation for the sharp section through X, on an interval
of length L starting at A. The first factor carries the signed shift. -/
def sharpMoebiusCovariance (X A L h : ℝ) : ℂ :=
  (∫ t in A..(A+L),moebiusPoly ⌊X⌋₊ (linePoint (t+h))*conj (moebiusPoly ⌊X⌋₊ (linePoint t)))/(L:ℂ)

/-- All three finite-scale errors: the two Hilbert endpoints, the cutoff
tail of squarefree mass, and the variation of the phase. -/
theorem sharp_covariance_microscopic_estimate {X L : ℝ} (hX : 1<X) (hL : 0<L) (A h : ℝ) :
    ‖sharpMoebiusCovariance X A L h -
      (squarefreeDensity:ℂ)*(Real.log X:ℂ)*unitLogWindow (h*Real.log X) -
      (squarefreeHarmonicConstant:ℂ)‖ ≤ 104*X/L+12*X^(-(1/2:ℝ))+24*|h| := by
  let D := weightedSquarefree X (logPhase h)
  let W := sharpMoebiusCovariance X A L h
  let U := (squarefreeDensity:ℂ)*(Real.log X:ℂ)*unitLogWindow (h*Real.log X)
  have hlc := Complex.ofReal_ne_zero.mpr hL.ne'
  have hg := critical_moebius_covariance_error ⌊X⌋₊ A L h
  have hd : weightedSquarefree (⌊X⌋₊:ℝ) (logPhase h) = D := by
    simp only [D,weightedSquarefree,Nat.floor_natCast]
  rw [hd] at hg
  have he : ‖W-D‖≤104*X/L := by
    dsimp only [W,sharpMoebiusCovariance]
    rw [div_sub' hlc,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL,mul_comm D]
    exact div_le_div_of_nonneg_right (hg.trans (mul_le_mul_of_nonneg_left
      (Nat.floor_le (zero_lt_one.trans hX).le) (by norm_num))) hL.le
  have ha : ‖D-U-(squarefreeHarmonicConstant:ℂ)‖≤12*X^(-(1/2:ℝ))+24*|h| :=
    squarefree_shifted_diagonal hX h
  change ‖W-U-_‖≤_
  rw [show W-U-(squarefreeHarmonicConstant:ℂ)=(W-D)+(D-U-(squarefreeHarmonicConstant:ℂ)) by ring,
    add_assoc (104*X/L)]
  exact (norm_add_le _ _).trans (add_le_add he ha)

/-- For section lengths little-o of the averaging length, every
vanishing height shift has the same second-order constant once the
finite-frequency Fourier term is removed. Initial heights are arbitrary. -/
theorem sharp_covariance_regular_part (A L h : ℝ → ℝ)
    (hL : ∀ᶠ X in atTop,0<L X) (hshort : Tendsto (fun X => X/L X) atTop (𝓝 0))
    (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun X : ℝ => sharpMoebiusCovariance X (A X) (L X) (h X) -
      (squarefreeDensity:ℂ)*(Real.log X:ℂ)*unitLogWindow (h X*Real.log X))
      atTop (𝓝 (squarefreeHarmonicConstant:ℂ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hcut := (tendsto_rpow_neg_atTop (by norm_num : 0<(1/2:ℝ))).const_mul 12
  have he := ((hshort.const_mul 104).add hcut).add (hh.abs.const_mul 24)
  simp only [abs_zero,mul_zero,add_zero] at he
  refine squeeze_zero' (.of_forall fun X => norm_nonneg _) ?_ he
  filter_upwards [hL,eventually_gt_atTop (1:ℝ)] with X hl hx
  simpa only [mul_div_assoc] using sharp_covariance_microscopic_estimate hx hl (A X) (h X)

/-- On any nonzero lattice harmonic growing more slowly than log X,
the raw mean correlation converges to the zeta-derivative constant. -/
theorem sharp_covariance_at_harmonic (A L : ℝ → ℝ) (k : ℝ → ℤ)
    (hL : ∀ᶠ X in atTop,0<L X) (hshort : Tendsto (fun X => X/L X) atTop (𝓝 0))
    (hk : ∀ᶠ X in atTop,k X≠0)
    (hslow : Tendsto (fun X : ℝ => (k X:ℝ)/Real.log X) atTop (𝓝 0)) :
    Tendsto (fun X : ℝ => sharpMoebiusCovariance X (A X) (L X) ((k X:ℝ)/Real.log X*(2*Real.pi)))
      atTop (𝓝 (squarefreeHarmonicConstant:ℂ)) := by
  have ht := sharp_covariance_regular_part A L _ hL hshort
    (by simpa only [zero_mul] using hslow.mul_const (2*Real.pi))
  apply ht.congr'
  filter_upwards [hk,eventually_gt_atTop (1:ℝ)] with X hn hx
  rw [show (k X:ℝ)/Real.log X*(2*Real.pi)*Real.log X=(k X:ℝ)*(2*Real.pi) by
    field_simp [(Real.log_pos hx).ne'],unitLogWindow_nonzero_harmonic hn,mul_zero,sub_zero]



end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
