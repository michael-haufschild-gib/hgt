import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheSharpHolderExponentForInfiniteGramRecovery

/-!
# Sharp bandwidth for reading an anchored Dirichlet coefficient

Fourier support separation in Gabet, Ferreira Da Costa and Lee
(arXiv:2611.18900, Lemma 4.1) isolates the first coefficient as a reference.
Two rotations and three bandwidths suffice at each of two successive cutoffs.
The amplification depends only on the excess bandwidth above log n.
-/
noncomputable section
open Finset Complex
open scoped ComplexConjugate
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval

/-- A quarter turn of the nth frequency relative to the unit frequency. -/
def anchorTime (n : ℕ) := Real.pi/(2*Real.log n)

private theorem quarter_turn {n : ℕ} (hn : 2 ≤ n) :
    anchorTime n * (Real.log n-Real.log (1:ℕ)) = Real.pi/2 := by
  have hlog : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  simp only [Nat.cast_one,Real.log_one,sub_zero,anchorTime]
  field_simp [hlog.ne']

/-- All the translations fit inside a fixed aperture. -/
theorem anchor_time_range {n : ℕ} (hn : 2 ≤ n) :
    anchorTime n ∈ Set.Ioc 0 (Real.pi/(2*Real.log 2)) := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have ht := Real.log_le_log (by norm_num : 0 < (2:ℝ)) (by exact_mod_cast hn : (2:ℝ) ≤ n)
  exact ⟨div_pos Real.pi_pos (mul_pos (by norm_num) (hlog.trans_le ht)),
    div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) (by linarith only [ht])⟩

/-- Six real energy samples of an array of observed prefix curves. -/
def anchoredRead (Y : ℕ → ℝ → ℝ) (k : ℕ) (h : ℝ) : ℝ :=
  second (fun d => Y (k+1) d-Y k d) (gap k 1) h/(2*h)

private theorem exact_read (a : ℕ → ℂ) {k : ℕ} (hk : 1 ≤ k) {h : ℝ} (hp : 0 < h) (hh : h ≤ 1/2) :
    anchoredRead (energy a) k h = gram (a (k+1)) (a 1) := by
  exact read_gram_local a (mem_Icc.mpr ⟨le_rfl,hk⟩) hp (by norm_num; exact hh)

/-- The unshifted observation gives the real coordinate. A single
frequency-dependent shift gives the imaginary coordinate with unit gain. -/
theorem two_reads_reconstruct_anchor_product (a : ℕ → ℂ) {k : ℕ} (hk : 1 ≤ k)
    {h : ℝ} (hp : 0 < h) (hh : h ≤ 1/2) :
    (anchoredRead (energy a) k h : ℂ) -
      (anchoredRead (energy (translated a (anchorTime (k+1)))) k h : ℂ)*I =
      a (k+1)*conj (a 1) := by
  rw [exact_read a hk hp hh,exact_read _ hk hp hh,translated_gram,quarter_turn (by omega),
    Real.cos_pi_div_two,Real.sin_pi_div_two,mul_zero,zero_sub,mul_one]
  apply Complex.ext <;> simp [gram,Complex.mul_re,Complex.mul_im]

private theorem read_error {Y Z : ℕ → ℝ → ℝ} {k : ℕ} {h δ : ℝ} (hp : 0 < h)
    (he : ∀ N ∈ ({k,k+1} : Finset ℕ), ∀ d ∈ ({gap k 1-h,gap k 1,gap k 1+h} : Finset ℝ),
      |Y N d-Z N d| ≤ δ) :
    |anchoredRead Y k h-anchoredRead Z k h| ≤ 4*δ/h := by
  let g := gap k 1
  have hd (d : ℝ) (hd : d ∈ ({g-h,g,g+h} : Finset ℝ)) :
      |(Y (k+1) d-Y k d)-(Z (k+1) d-Z k d)| ≤ 2*δ := by
    rw [show ∀ a b c e : ℝ, (a-b)-(c-e)=(a-c)-(b-e) by intros; ring]
    exact (abs_sub _ _).trans (by linarith only [he k (by simp) d hd,he (k+1) (by simp) d hd])
  have hl := abs_le.mp (hd (g-h) (by simp))
  have hm := abs_le.mp (hd g (by simp))
  have hr := abs_le.mp (hd (g+h) (by simp))
  unfold anchoredRead
  rw [←sub_div,abs_div,abs_of_pos (mul_pos (by norm_num) hp)]
  apply (div_le_iff₀ (mul_pos (by norm_num) hp)).mpr
  rw [show 4*δ/h*(2*h)=8*δ by field_simp; ring]
  rw [abs_le]
  change -(8*δ) ≤ second _ g h-second _ g h ∧ _
  dsimp only [second]
  constructor <;> linarith only [hl.1,hl.2,hm.1,hm.2,hr.1,hr.2]

/-- A noisy reconstruction from twelve scalar measurements. Only the two
adjacent prefixes and the three indicated bandwidths have to be observed. -/
theorem twelve_sample_anchor_error (a : ℕ → ℂ) {k : ℕ} (hk : 1 ≤ k)
    {h δ : ℝ} (hp : 0 < h) (hh : h ≤ 1/2) (U V : ℕ → ℝ → ℝ)
    (hU : ∀ N ∈ ({k,k+1} : Finset ℕ), ∀ d ∈ ({gap k 1-h,gap k 1,gap k 1+h} : Finset ℝ),
      |U N d-energy a N d| ≤ δ)
    (hV : ∀ N ∈ ({k,k+1} : Finset ℕ), ∀ d ∈ ({gap k 1-h,gap k 1,gap k 1+h} : Finset ℝ),
      |V N d-energy (translated a (anchorTime (k+1))) N d| ≤ δ) :
    ‖(anchoredRead U k h : ℂ)-(anchoredRead V k h : ℂ)*I-a (k+1)*conj (a 1)‖ ≤ 8*δ/h := by
  rw [←two_reads_reconstruct_anchor_product a hk hp hh]
  rw [show ∀ x y z w : ℝ, (x:ℂ)-y*I-(z-w*I)=((x-z:ℝ):ℂ)-((y-w:ℝ):ℂ)*I by
    intros; push_cast; ring]
  refine (norm_sub_le _ _).trans ?_
  simp only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  have h1 := read_error hp hU
  have h2 := read_error hp hV
  have h8 : 8*δ/h = 4*δ/h+4*δ/h := by ring
  linarith only [h1,h2,h8]

/-- A unit reference at 1 and a free complex amplitude at n. -/
def anchorPair (n : ℕ) (z : ℂ) (j : ℕ) : ℂ :=
  if j=1 then 1 else if j=n then z else 0

private theorem last_pair_row {k : ℕ} (hk : 1 ≤ k) (s t d : ℝ) :
    row (translated (anchorPair (k+1) s) t) k d =
      s^2*max d 0+2*(s*Real.cos (t*Real.log (k+1:ℕ)))*max (d-Real.log (k+1:ℕ)) 0 := by
  have hn : k+1 ≠ 1 := by omega
  have hz : ‖translated (anchorPair (k+1) s) t (k+1)‖^2 = s^2 := by
    rw [translated,anchorPair,if_neg hn,if_pos rfl,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,
      Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [row_spectrum,hz,sum_eq_single 1]
  · have hA : anchorPair (k+1) (s:ℂ) (k+1) = s := by simp [anchorPair]
    have hB : anchorPair (k+1) (s:ℂ) 1 = 1 := by simp [anchorPair]
    rw [translated_gram,hA,hB]
    simp [gram,gap]
    <;> ring
  · intro j hj hj₁
    have hjn : j ≠ k+1 := (Nat.lt_succ_of_le (mem_Icc.mp hj).2).ne
    simp [translated,anchorPair,hj₁,hjn,gram]
  · exact fun hmem => False.elim (hmem (mem_Icc.mpr ⟨le_rfl,hk⟩))

/-- Exact indistinguishability of opposite signs below the log gap.
Above the gap the largest difference over every time shift is exactly
four times the excess bandwidth, attained by the unshifted pair. -/
theorem opposite_anchors_energy {n : ℕ} (hn : 2 ≤ n) (t d : ℝ) (N : ℕ) :
    energy (translated (anchorPair n 1) t) N d-energy (translated (anchorPair n (-1)) t) N d =
      if n ≤ N then 4*Real.cos (t*Real.log n)*max (d-Real.log n) 0 else 0 := by
  induction N with
  | zero => simp [energy,RHTower.Sieve.logWindowSum,show ¬n ≤ 0 by omega]
  | succ k ih =>
    let A := translated (anchorPair n 1) t
    let B := translated (anchorPair n (-1)) t
    have hs : energy A (k+1) d-energy B (k+1) d =
        (energy A k d-energy B k d)+(row A k d-row B k d) := by unfold row; ring
    rw [hs,ih]
    by_cases he : k+1=n
    · subst n
      rw [if_neg (by omega : ¬k+1 ≤ k),if_pos le_rfl,zero_add]
      have h1 := last_pair_row (k := k) (by omega) 1 t d
      have h2 := last_pair_row (k := k) (by omega) (-1) t d
      dsimp only [A,B]
      push_cast at h1 h2 ⊢
      rw [h1,h2]
      ring
    · have hrow : row A k d=row B k d := by
        by_cases hk : k=0
        · subst k
          simp [A,B,row_spectrum,translated,anchorPair]
        have h0 (u : ℂ) : translated (anchorPair n u) t (k+1)=0 := by
          simp [translated,anchorPair,he,hk]
        simp [A,B,row_spectrum,h0,gram]
      rw [hrow,sub_self,add_zero]
      by_cases hle : n ≤ k <;> simp [hle,show n ≤ k+1 ↔ n ≤ k by omega]

/-- With arbitrarily many translates and arbitrary prefix cutoffs, a
window ending at log n+h cannot distinguish the two signals by more than 4h. -/
theorem opposite_anchors_noise_floor {n : ℕ} (hn : 2 ≤ n) {h : ℝ} (hh : 0 ≤ h) :
    (∀ t d : ℝ, d ≤ Real.log n+h → ∀ N,
      |energy (translated (anchorPair n 1) t) N d-energy (translated (anchorPair n (-1)) t) N d| ≤ 4*h) ∧
    |energy (translated (anchorPair n 1) 0) n (Real.log n+h)-
      energy (translated (anchorPair n (-1)) 0) n (Real.log n+h)| = 4*h := by
  constructor
  · intro t d hd N
    rw [opposite_anchors_energy hn]
    split_ifs
    · rw [abs_mul,abs_mul,abs_of_nonneg (le_max_right (d-Real.log n) (0:ℝ))]
      norm_num
      have hcos := abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
      have hle := mul_le_mul hcos (max_le (by linarith only [hd] : d-Real.log n ≤ h) hh)
        (le_max_right _ _) zero_le_one
      linarith only [hle]
    · rw [abs_zero]; positivity
  · rw [opposite_anchors_energy hn,if_pos le_rfl]
    simp [max_eq_left hh,abs_of_nonneg hh]

end GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
