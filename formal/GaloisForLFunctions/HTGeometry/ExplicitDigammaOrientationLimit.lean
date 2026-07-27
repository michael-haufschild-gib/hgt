import GaloisForLFunctions.HTGeometry.ExplicitDigammaHerglotzPalette

/-!
# The infinite signed digamma orientation limit

Every Boolean residue sequence defines the regularized Gauss carrier from
`ExplicitDigammaHerglotzPalette`.  This file proves the missing infinite-tail chamber law: after
deleting one selected half-integer pole, the remaining series is normally convergent near that
pole, and the full carrier is Herglotz exactly for the all-positive sign sequence.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology
open scoped Topology BigOperators

noncomputable section

/-- Delete the selected Gauss-series atom while retaining the original indexing. -/
def signedDigammaRegularTerm (ε : ℕ → ℝ) (k : ℕ) (n : ℕ) (z : ℂ) : ℂ :=
  if n = k then 0 else signedDigammaCompletionTerm ε z n

/-- The regular background after deletion of the `k`th half-integer pole. -/
def signedDigammaRegular (ε : ℕ → ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, signedDigammaRegularTerm ε k n z

/-- **Uniform quadratic decay of the signed Gauss palette.**  On `‖z‖ ≤ R₀` and for
`n ≥ 2R₀ + 2` the `n`th signed completion term is `O(R₀ / n²)` with the explicit constant
`4(R₀+1)`.  The shifted denominator `z + 1/2 + n` has norm at least `(n+1)/2`, so the Gauss term
`1/(n+1) − 1/(z+1/2+n)` contributes two powers of `n`. -/
private theorem norm_signedDigammaCompletionTerm_le
    (ε : ℕ → ℝ) (hε : ∀ n, |ε n| ≤ 1) {R0 : ℝ} {z : ℂ} {n : ℕ}
    (hzNorm : ‖z‖ ≤ R0) (hnLower : 2 * R0 + 2 ≤ (n : ℝ)) :
    ‖signedDigammaCompletionTerm ε z n‖ ≤ 4 * (R0 + 1) / ((n : ℝ) + 1) ^ 2 := by
  have hR0nonneg : 0 ≤ R0 := (norm_nonneg z).trans hzNorm
  have hn1pos : 0 < (n : ℝ) + 1 := by positivity
  have hnum : ‖z - (1 / 2 : ℂ)‖ ≤ R0 + 1 := by
    calc
      ‖z - (1 / 2 : ℂ)‖ ≤ ‖z‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
      _ ≤ R0 + 1 := by norm_num; linarith
  have hden2 : ((n : ℝ) + 1) / 2 ≤
      ‖z + (1 / 2 : ℂ) + (n : ℂ)‖ := by
    calc
      ((n : ℝ) + 1) / 2 ≤ ((n : ℝ) + 1 / 2) - R0 := by linarith
      _ ≤ ‖((((n : ℝ) + 1 / 2 : ℝ) : ℂ))‖ - ‖z‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1 / 2)]
        linarith
      _ ≤ ‖z + (1 / 2 : ℂ) + (n : ℂ)‖ := by
        have h := norm_sub_norm_le (((n : ℝ) + 1 / 2 : ℝ) : ℂ) (-z)
        rw [norm_neg, show (((n : ℝ) + 1 / 2 : ℝ) : ℂ) - (-z) =
          z + (1 / 2 : ℂ) + (n : ℂ) by push_cast; ring] at h
        exact h
  have hden2pos : 0 < ‖z + (1 / 2 : ℂ) + (n : ℂ)‖ :=
    (by positivity : 0 < ((n : ℝ) + 1) / 2) |>.trans_le hden2
  have hn1ne : ((n : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (ne_of_gt hn1pos)
  have hden2ne : z + (1 / 2 : ℂ) + (n : ℂ) ≠ 0 :=
    norm_pos_iff.mp hden2pos
  have hterm : RHTower.gaussDigammaSeriesTerm (z + (1 / 2 : ℂ)) n =
      (z - (1 / 2 : ℂ)) /
        (((n : ℂ) + 1) * (z + (1 / 2 : ℂ) + (n : ℂ))) := by
    unfold RHTower.gaussDigammaSeriesTerm
    rw [div_sub_div _ _ hn1ne hden2ne]
    ring
  rw [signedDigammaCompletionTerm, hterm, norm_mul, norm_div, norm_mul]
  have hεnorm : ‖(ε n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hε n
  have hn1norm : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    rw [show (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn1pos]
  rw [hn1norm]
  have hquot :
      ‖z - (1 / 2 : ℂ)‖ /
          (((n : ℝ) + 1) * ‖z + (1 / 2 : ℂ) + (n : ℂ)‖) ≤
        2 * (R0 + 1) / ((n : ℝ) + 1) ^ 2 := by
    calc
      ‖z - (1 / 2 : ℂ)‖ /
          (((n : ℝ) + 1) * ‖z + (1 / 2 : ℂ) + (n : ℂ)‖)
          ≤ (R0 + 1) / (((n : ℝ) + 1) ^ 2 / 2) := by
            apply div_le_div₀ (by linarith) hnum (by positivity)
            nlinarith
      _ = 2 * (R0 + 1) / ((n : ℝ) + 1) ^ 2 := by
            field_simp
  have hquotnonneg : 0 ≤
      ‖z - (1 / 2 : ℂ)‖ /
        (((n : ℝ) + 1) * ‖z + (1 / 2 : ℂ) + (n : ℂ)‖) :=
    div_nonneg (norm_nonneg _) (mul_nonneg hn1pos.le (norm_nonneg _))
  have hmul := mul_le_mul hεnorm hquot hquotnonneg (by norm_num)
  
  calc
    ‖(ε n : ℂ)‖ *
        (‖z - (1 / 2 : ℂ)‖ /
          (((n : ℝ) + 1) * ‖z + (1 / 2 : ℂ) + (n : ℂ)‖)) ≤
      1 * (2 * (R0 + 1) / ((n : ℝ) + 1) ^ 2) := hmul
    _ ≤ 4 * (R0 + 1) / ((n : ℝ) + 1) ^ 2 := by
      rw [one_mul]
      have hdenpos : 0 < ((n : ℝ) + 1) ^ 2 := sq_pos_of_pos hn1pos
      apply (div_le_div_iff_of_pos_right hdenpos).2
      nlinarith

/-- **Normal convergence from domination by the signed Gauss palette.**  Any family dominated
termwise by the signed completion terms converges locally normally on every open set: the
majorant `4(R₀+1)/(n+1)²` is summable and, on a compact subset of norm at most `R₀`, bounds all
but finitely many terms. -/
theorem summableLocallyUniformlyOn_of_norm_le_signedDigammaCompletionTerm
    (ε : ℕ → ℝ) (hε : ∀ n, |ε n| ≤ 1) {f : ℕ → ℂ → ℂ}
    (hf : ∀ n z, ‖f n z‖ ≤ ‖signedDigammaCompletionTerm ε z n‖)
    {U : Set ℂ} (hU : IsOpen U) :
    SummableLocallyUniformlyOn f U := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually hU
  intro K _hKsub hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  let R0 : ℝ := max R 0
  let C : ℝ := 4 * (R0 + 1)
  refine ⟨fun n : ℕ => C / ((n : ℝ) + 1) ^ 2, ?_, ?_⟩
  · have hbase : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
      have h := (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
      apply h.congr
      intro n
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
      simp only [Real.rpow_two]
    have hmul := hbase.mul_left C
    apply hmul.congr
    intro n
    rw [mul_one_div]
  · have hfinite : {n : ℕ | n < Nat.ceil (2 * R0 + 2)}.Finite :=
      Set.finite_lt_nat _
    filter_upwards [hfinite.eventually_cofinite_notMem] with n hn
    intro z hz
    have hzNorm : ‖z‖ ≤ R0 := (hR z hz).trans (le_max_left _ _)
    have hnNat : Nat.ceil (2 * R0 + 2) ≤ n := Nat.le_of_not_gt hn
    have hnLower : 2 * R0 + 2 ≤ (n : ℝ) := by
      calc
        2 * R0 + 2 ≤ (Nat.ceil (2 * R0 + 2) : ℝ) := Nat.le_ceil _
        _ ≤ n := by exact_mod_cast hnNat
    exact (hf n z).trans (norm_signedDigammaCompletionTerm_le ε hε hzNorm hnLower)

/-- The deleted-pole background converges normally on a fixed neighborhood of its center. -/
theorem summableLocallyUniformlyOn_signedDigammaRegular
    (ε : ℕ → ℝ) (k : ℕ) (hε : ∀ n, |ε n| ≤ 1) :
    SummableLocallyUniformlyOn
      (fun n z => signedDigammaRegularTerm ε k n z)
      (Metric.ball (-((k : ℝ) + 1 / 2) : ℂ) (1 / 3)) :=
  summableLocallyUniformlyOn_of_norm_le_signedDigammaCompletionTerm ε hε
    (fun n z => by
      rw [signedDigammaRegularTerm]
      split_ifs
      · rw [norm_zero]
        exact norm_nonneg _
      · exact le_rfl)
    Metric.isOpen_ball

/-- The deleted-pole background is holomorphic on the fixed pole neighborhood. -/
theorem differentiableOn_signedDigammaRegular
    (ε : ℕ → ℝ) (k : ℕ) (hε : ∀ n, |ε n| ≤ 1) :
    DifferentiableOn ℂ (signedDigammaRegular ε k)
      (Metric.ball (-((k : ℝ) + 1 / 2) : ℂ) (1 / 3)) := by
  apply SummableLocallyUniformlyOn.differentiableOn Metric.isOpen_ball
    (summableLocallyUniformlyOn_signedDigammaRegular ε k hε)
  intro n z hz
  simp only [signedDigammaRegularTerm]
  split_ifs with hnk
  · exact differentiableAt_const (c := (0 : ℂ))
  · have hden : z + (1 / 2 : ℂ) + (n : ℂ) ≠ 0 := by
      intro hzero
      have hzEq : z = -((n : ℝ) + 1 / 2 : ℂ) := by
        apply eq_of_sub_eq_zero
        push_cast at hzero ⊢
        linear_combination hzero
      have hzdist := Metric.mem_ball.mp hz
      rw [hzEq, dist_eq] at hzdist
      have habs : |(n : ℝ) - (k : ℝ)| < 1 / 3 := by
        have hreal : ‖((((k : ℝ) - (n : ℝ)) : ℝ) : ℂ)‖ < 1 / 3 := by
          convert hzdist using 1
          push_cast
          ring_nf
        rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] at hreal
        exact hreal
      rcases lt_or_gt_of_ne hnk with hlt | hgt
      · have hgapNat : n + 1 ≤ k := Nat.succ_le_iff.mpr hlt
        have hgapCast : (n : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hgapNat
        have hgap : (1 : ℝ) ≤ (k : ℝ) - (n : ℝ) := by linarith
        have hsignCast : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.le_of_lt hlt)
        rw [abs_of_nonpos (by linarith : (n : ℝ) - (k : ℝ) ≤ 0)] at habs
        linarith
      · have hgapNat : k + 1 ≤ n := Nat.succ_le_iff.mpr hgt
        have hgapCast : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hgapNat
        have hgap : (1 : ℝ) ≤ (n : ℝ) - (k : ℝ) := by linarith
        have hsignCast : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.le_of_lt hgt)
        rw [abs_of_nonneg (by linarith : 0 ≤ (n : ℝ) - (k : ℝ))] at habs
        linarith
    unfold signedDigammaCompletionTerm RHTower.gaussDigammaSeriesTerm
    have hfirst : ((n : ℂ) + 1) ≠ 0 := by
      exact_mod_cast (by positivity : (n : ℝ) + 1 ≠ 0)
    simp only [one_div]
    change DifferentiableAt ℂ (fun w : ℂ => (ε n : ℂ) *
      (((n : ℂ) + 1)⁻¹ - (w + (2 : ℂ)⁻¹ + (n : ℂ))⁻¹)) z
    have hden' : z + (2 : ℂ)⁻¹ + (n : ℂ) ≠ 0 := by simpa [one_div] using hden
    have hconst : DifferentiableAt ℂ (fun _ : ℂ => ((n : ℂ) + 1)⁻¹) z := by fun_prop
    have hlinear : DifferentiableAt ℂ
        (fun w : ℂ => w + (2 : ℂ)⁻¹ + (n : ℂ)) z := by fun_prop
    have hinv : DifferentiableAt ℂ
        (fun w : ℂ => (w + (2 : ℂ)⁻¹ + (n : ℂ))⁻¹) z := hlinear.inv hden'
    exact (hconst.sub hinv).const_mul _

/-- The deleted-pole background is continuous at the selected half-integer pole. -/
theorem continuousAt_signedDigammaRegular
    (ε : ℕ → ℝ) (k : ℕ) (hε : ∀ n, |ε n| ≤ 1) :
    ContinuousAt (signedDigammaRegular ε k) (-((k : ℝ) + 1 / 2) : ℂ) := by
  have hcenter : (-((k : ℝ) + 1 / 2) : ℂ) ∈
      Metric.ball (-((k : ℝ) + 1 / 2) : ℂ) (1 / 3) := by
    simp [Metric.mem_ball]
  exact ((differentiableOn_signedDigammaRegular ε k hε) _ hcenter).differentiableAt
    (Metric.isOpen_ball.mem_nhds hcenter) |>.continuousAt

/-- Exact splitting into the selected atom and its regular background. -/
theorem signedDigammaCompletion_eq_term_add_regular
    (ε : ℕ → ℝ) (k : ℕ) (z : ℂ) (hε : ∀ n, |ε n| ≤ 1) :
    signedDigammaCompletion ε z =
      signedDigammaCompletionTerm ε z k + signedDigammaRegular ε k z := by
  exact (summable_signedDigammaCompletionTerm ε z hε).tsum_eq_add_tsum_ite k

/-- Boolean `true` reverses the corresponding Gauss residue. -/
def signedDigammaBooleanWeight (ε : ℕ → Bool) (n : ℕ) : ℝ :=
  if ε n = true then -1 else 1

theorem abs_signedDigammaBooleanWeight_le_one (ε : ℕ → Bool) (n : ℕ) :
    |signedDigammaBooleanWeight ε n| ≤ 1 := by
  by_cases h : ε n = true <;> simp [signedDigammaBooleanWeight, h]

/-- The canonical signed Gauss carrier attached to a Boolean orientation. -/
def signedDigammaBooleanCompletion (ε : ℕ → Bool) (z : ℂ) : ℂ :=
  signedDigammaCompletion (signedDigammaBooleanWeight ε) z

/-- A reversed Boolean coordinate contributes exactly one negative Cauchy atom. -/
theorem signedDigammaBooleanCompletion_eq_regular_sub_atom
    {ε : ℕ → Bool} {k : ℕ} (hk : ε k = true) (z : ℂ) :
    signedDigammaBooleanCompletion ε z =
      (signedDigammaRegular (signedDigammaBooleanWeight ε) k z -
        1 / ((k : ℂ) + 1)) -
          ((-((k : ℝ) + 1 / 2) : ℂ) - z)⁻¹ := by
  rw [signedDigammaBooleanCompletion,
    signedDigammaCompletion_eq_term_add_regular _ k z
      (abs_signedDigammaBooleanWeight_le_one ε)]
  simp only [signedDigammaCompletionTerm, signedDigammaBooleanWeight, if_pos hk,
    RHTower.gaussDigammaSeriesTerm]
  have hinv : ((-((k : ℝ) + 1 / 2) : ℂ) - z)⁻¹ =
      -(z + (1 / 2 : ℂ) + (k : ℂ))⁻¹ := by
    rw [show (-((k : ℝ) + 1 / 2) : ℂ) - z =
      -(z + (1 / 2 : ℂ) + (k : ℂ)) by push_cast; ring, inv_neg]
  rw [hinv]
  norm_num
  ring

/-- Any reversed coordinate destroys the Herglotz inequality, even for an infinite sign tail. -/
theorem signedDigammaBooleanCompletion_not_nonneg_of_nonempty
    (ε : ℕ → Bool) (hε : ∃ k, ε k = true) :
    ¬ ∀ z : ℂ, 0 < z.im → 0 ≤ (signedDigammaBooleanCompletion ε z).im := by
  obtain ⟨k, hk⟩ := hε
  let a : ℝ := -((k : ℝ) + 1 / 2)
  let g : ℂ → ℂ := fun z =>
    signedDigammaRegular (signedDigammaBooleanWeight ε) k z - 1 / ((k : ℂ) + 1)
  have hg : ContinuousAt g (a : ℂ) := by
    apply ContinuousAt.sub
    · simpa [a] using continuousAt_signedDigammaRegular
        (signedDigammaBooleanWeight ε) k (abs_signedDigammaBooleanWeight_le_one ε)
    · fun_prop
  obtain ⟨z, hz, hneg⟩ :=
    exists_upper_im_neg_of_continuous_add_negativeAtom a g hg
  intro hnonneg
  have h := hnonneg z hz
  rw [signedDigammaBooleanCompletion_eq_regular_sub_atom hk z] at h
  have hshape :
      (signedDigammaRegular (signedDigammaBooleanWeight ε) k z - 1 / ((k : ℂ) + 1) -
        ((-((k : ℝ) + 1 / 2) : ℂ) - z)⁻¹).im =
        (g z - ((a : ℂ) - z)⁻¹).im := by
    dsimp [a, g]
    push_cast
    rfl
  rw [hshape] at h
  exact (not_lt_of_ge h) hneg

/-- The all-positive Gauss carrier has nonnegative imaginary part on the upper half-plane. -/
theorem signedDigammaBooleanCompletion_empty_im_nonneg (z : ℂ) (hz : 0 < z.im) :
    0 ≤ (signedDigammaBooleanCompletion (fun _ => false) z).im := by
  have hs := summable_signedDigammaCompletionTerm (fun _ => 1) z (fun _ => by simp)
  change 0 ≤ (∑' n : ℕ, signedDigammaCompletionTerm (fun _ => 1) z n).im
  rw [Complex.im_tsum hs]
  apply tsum_nonneg
  intro n
  simp only [signedDigammaCompletionTerm, Complex.ofReal_one, one_mul,
    RHTower.gaussDigammaSeriesTerm]
  rw [Complex.sub_im]
  have hfirst : (1 / ((n : ℂ) + 1)).im = 0 := by
    rw [one_div, Complex.inv_im]
    simp
  rw [hfirst, zero_sub, one_div, Complex.inv_im, neg_div, neg_neg]
  have him : (z + (1 / 2 : ℂ) + (n : ℂ)).im = z.im := by simp
  rw [him]
  exact div_nonneg hz.le (Complex.normSq_nonneg (z + (1 / 2 : ℂ) + (n : ℂ)))

/-- **Infinite signed digamma chamber law.** The all-positive sequence is the unique Herglotz
point of the entire signed Gauss completion, including infinitely reversed orientations. -/
theorem signedDigammaBooleanCompletion_nonneg_iff_allPositive (ε : ℕ → Bool) :
    (∀ z : ℂ, 0 < z.im → 0 ≤ (signedDigammaBooleanCompletion ε z).im) ↔
      ε = fun _ => false := by
  constructor
  · intro h
    apply funext
    intro k
    apply Bool.eq_false_of_not_eq_true
    intro hk
    exact signedDigammaBooleanCompletion_not_nonneg_of_nonempty ε ⟨k, hk⟩ h
  · rintro rfl z hz
    exact signedDigammaBooleanCompletion_empty_im_nonneg z hz

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology
open scoped Topology BigOperators

noncomputable section

/-- Every bounded signed Gauss palette converges locally normally, uniformly on compact subsets of
the entire parameter plane. Poles affect finitely many summands on a bounded compact and therefore
do not affect normal convergence of the tail. -/
theorem summableLocallyUniformlyOn_signedDigammaCompletionTerm
    (ε : ℕ → ℝ) (hε : ∀ n, |ε n| ≤ 1) :
    SummableLocallyUniformlyOn
      (fun n z => signedDigammaCompletionTerm ε z n) Set.univ :=
  summableLocallyUniformlyOn_of_norm_le_signedDigammaCompletionTerm ε hε
    (fun _ _ => le_rfl) isOpen_univ

/-- The canonical signed completion is the locally normal sum of its finite chambers. -/
theorem hasSumLocallyUniformlyOn_signedDigammaCompletionTerm
    (ε : ℕ → ℝ) (hε : ∀ n, |ε n| ≤ 1) :
    HasSumLocallyUniformlyOn
      (fun n z => signedDigammaCompletionTerm ε z n)
      (signedDigammaCompletion ε) Set.univ := by
  simpa only [signedDigammaCompletion] using
    (summableLocallyUniformlyOn_signedDigammaCompletionTerm ε hε).hasSumLocallyUniformlyOn

/-- Every bounded signed completion is holomorphic on the upper half-plane. -/
theorem differentiableOn_signedDigammaCompletion_upperHalf
    (ε : ℕ → ℝ) (hε : ∀ n, |ε n| ≤ 1) :
    DifferentiableOn ℂ (signedDigammaCompletion ε) {z : ℂ | 0 < z.im} := by
  apply SummableLocallyUniformlyOn.differentiableOn
    (isOpen_lt continuous_const Complex.continuous_im)
    ((summableLocallyUniformlyOn_signedDigammaCompletionTerm ε hε).mono
      (Set.subset_univ _))
  intro n z hz
  unfold signedDigammaCompletionTerm RHTower.gaussDigammaSeriesTerm
  have hfirst : ((n : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (by positivity : (n : ℝ) + 1 ≠ 0)
  have hden : z + (1 / 2 : ℂ) + (n : ℂ) ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    change 0 < z.im at hz
    linarith
  change DifferentiableAt ℂ (fun w : ℂ => (ε n : ℂ) *
    (1 / ((n : ℂ) + 1) - 1 / (w + (1 / 2 : ℂ) + (n : ℂ)))) z
  fun_prop

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The all-positive Boolean orientation is the closed-form shifted-digamma Herglotz source at every
point off the half-integer pole lattice. -/
theorem signedDigammaBooleanCompletion_allPositive_eq_explicitDigammaHerglotzSource
    {z : ℂ} (hz : ∀ n : ℕ, z + (1 / 2 : ℂ) ≠ -(n : ℂ)) :
    signedDigammaBooleanCompletion (fun _ => false) z =
      explicitDigammaHerglotzSource z := by
  rw [signedDigammaBooleanCompletion]
  have hweight : signedDigammaBooleanWeight (fun _ => false) = fun _ => 1 := by
    funext n
    simp [signedDigammaBooleanWeight]
  rw [hweight]
  exact signedDigammaCompletion_one_eq_explicitDigammaHerglotzSource hz

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every Boolean signed completion is the locally normal sum of its finite chambers.  The
residue-bound hypothesis is discharged: Boolean weights are `±1`, hence bounded by one. -/
theorem hasSumLocallyUniformlyOn_signedDigammaBooleanCompletion (ε : ℕ → Bool) :
    HasSumLocallyUniformlyOn
      (fun n z => signedDigammaCompletionTerm (signedDigammaBooleanWeight ε) z n)
      (signedDigammaBooleanCompletion ε) Set.univ :=
  hasSumLocallyUniformlyOn_signedDigammaCompletionTerm
    (signedDigammaBooleanWeight ε) (abs_signedDigammaBooleanWeight_le_one ε)

/-- Every Boolean signed completion is holomorphic on the upper half-plane.  The
residue-bound hypothesis is discharged: Boolean weights are `±1`, hence bounded by one. -/
theorem differentiableOn_signedDigammaBooleanCompletion_upperHalf (ε : ℕ → Bool) :
    DifferentiableOn ℂ (signedDigammaBooleanCompletion ε) {z : ℂ | 0 < z.im} :=
  differentiableOn_signedDigammaCompletion_upperHalf
    (signedDigammaBooleanWeight ε) (abs_signedDigammaBooleanWeight_le_one ε)

end

end GaloisForLFunctions.HTGeometry
