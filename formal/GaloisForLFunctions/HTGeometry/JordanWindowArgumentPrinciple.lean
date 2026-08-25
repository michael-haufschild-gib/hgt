import GaloisForLFunctions.HTGeometry.DivisorPairing
import GaloisForLFunctions.RHTower.WindingFull
import GaloisForLFunctions.RHTower.WindingHomotopy

open Complex Metric Set

namespace GaloisForLFunctions.HTGeometry

open scoped Classical in
noncomputable def unitDiscZeroMultiplicity (f : ℂ → ℂ) : ℕ :=
  ∑ᶠ z : ℂ, if z ∈ ball (0 : ℂ) 1 then zeroMult f z else 0

theorem exists_inner_radius_enclosing_zeros
    {f : ℂ → ℂ}
    (hf : ContinuousOn f (closedBall (0 : ℂ) 1))
    (hne : ∀ z ∈ sphere (0 : ℂ) 1, f z ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, f z = 0 → ‖z‖ < r := by
  let X := ↥(closedBall (0 : ℂ) 1)
  letI : CompactSpace X := isCompact_iff_compactSpace.mp
    (isCompact_closedBall (0 : ℂ) 1)
  let g : X → ℂ := fun z => f z
  have hg : Continuous g := continuousOn_iff_continuous_restrict.mp hf
  let Z : Set X := {z | g z = 0}
  have hZclosed : IsClosed Z := isClosed_eq hg continuous_const
  have hZcompact : IsCompact Z := hZclosed.isCompact
  by_cases hZne : Z.Nonempty
  · obtain ⟨z, hzZ, hzmax⟩ := hZcompact.exists_isMaxOn hZne
        ((continuous_norm.comp continuous_subtype_val).continuousOn)
    have hznorm_le : ‖(z : ℂ)‖ ≤ 1 := by
      have hz := z.property
      change dist (z : ℂ) 0 ≤ 1 at hz
      simpa [dist_eq_norm] using hz
    have hznorm_lt : ‖(z : ℂ)‖ < 1 := lt_of_le_of_ne hznorm_le (by
      intro heq
      have hzsphere : (z : ℂ) ∈ sphere (0 : ℂ) 1 := by
        simpa [mem_sphere, dist_eq_norm] using heq
      exact hne z hzsphere (by simpa [Z, g] using hzZ))
    refine ⟨(‖(z : ℂ)‖ + 1) / 2, by positivity, by linarith, ?_⟩
    intro w hw hw0
    let wx : X := ⟨w, hw⟩
    have hwZ : wx ∈ Z := by simpa [Z, g, wx] using hw0
    have hwle : ‖w‖ ≤ ‖(z : ℂ)‖ := hzmax hwZ
    linarith
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    intro z hz hz0
    exfalso
    apply hZne
    exact ⟨⟨z, hz⟩, by simpa [Z, g] using hz0⟩

/-- Argument principle for a function analytic on the open unit disc and merely continuous on its
closure. Boundary nonvanishing forces all zeros into one strict inner circle, so no smoothness of
the Jordan boundary is needed. -/
theorem windingNumber_unitCircle_eq_unitDiscZeroMultiplicity
    {f : ℂ → ℂ}
    (hfan : AnalyticOnNhd ℂ f (ball (0 : ℂ) 1))
    (hfc : ContinuousOn f (closedBall (0 : ℂ) 1))
    (hne : ∀ z ∈ sphere (0 : ℂ) 1, f z ≠ 0) :
    RHTower.windingNumber
        (fun θ : ℝ => f (Complex.exp (Complex.I * (θ : ℂ))))
        0 (2 * Real.pi) = (unitDiscZeroMultiplicity f : ℤ) := by
  classical
  obtain ⟨r, hr0, hr1, hzeros⟩ := exists_inner_radius_enclosing_zeros hfc hne
  let R : ℝ := (r + 1) / 2
  have hrR : r < R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hR0 : 0 < R := lt_trans hr0 hrR
  have hclosedR : closedBall (0 : ℂ) R ⊆ ball (0 : ℂ) 1 := by
    intro z hz
    exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) hR1)
  have hfR : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R) :=
    fun z hz => hfan z (hclosedR hz)
  let q : ℝ := (r + R) / 2
  have hrq : r < q := by dsimp [q]; linarith
  have hqR : q < R := by dsimp [q]; linarith
  have hq0 : 0 < q := lt_trans hr0 hrq
  let z₀ : ℂ := q
  have hz₀R : z₀ ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_eq_norm]
    simpa [z₀, abs_of_pos hq0] using hqR
  have hz₀closed : z₀ ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall, dist_eq_norm]
    have hq1 : q ≤ 1 := (lt_trans hqR hR1).le
    simpa [z₀, abs_of_pos hq0] using hq1
  have hfz₀ : f z₀ ≠ 0 := by
    intro hz
    have hlt := hzeros z₀ hz₀closed hz
    dsimp [z₀] at hlt
    have hqr : q < r := by
      simpa [Complex.norm_real, abs_of_pos hq0] using hlt
    exact (not_lt_of_ge hrq.le) hqr
  obtain ⟨Z, m, g, hZR, hmpos, hZzero, hgan, hgne, hfact⟩ :=
    HTGeometry.exists_finset_zeroFree_factorization hfR hz₀R hfz₀
  have hZr : ∀ z ∈ Z, ‖z‖ < r := by
    intro z hz
    have hzballR := hZR z hz
    have hzclosed1 : z ∈ closedBall (0 : ℂ) 1 := by
      exact ball_subset_closedBall (ball_subset_ball hR1.le hzballR)
    exact hzeros z hzclosed1 ((hZzero z hzballR).mpr hz)
  have hwInner : RHTower.windingNumber
      (fun θ : ℝ => f ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      0 (2 * Real.pi) = ∑ z ∈ Z, (m z : ℤ) := by
    simpa only [zero_add] using
      RHTower.windingNumber_argument_principle Z id m hrR hr0
      (by intro z hz; simpa using hZr z hz)
      hgan.continuousOn hgne hfact
  have hmult : ∀ z ∈ Z, zeroMult f z = m z := by
    intro z hz
    have hzR := hZR z hz
    have h := zeroMult_of_factorization isOpen_ball Z m hgan.differentiableOn hgne hfact hzR
    simpa [hz] using h
  have hcount : unitDiscZeroMultiplicity f = ∑ z ∈ Z, m z := by
    rw [unitDiscZeroMultiplicity]
    rw [finsum_eq_finset_sum_of_support_subset
      (s := Z) (f := fun z : ℂ => if z ∈ ball (0 : ℂ) 1 then zeroMult f z else 0)]
    · apply Finset.sum_congr rfl
      intro z hz
      have hzunit : z ∈ ball (0 : ℂ) 1 := ball_subset_ball hR1.le (hZR z hz)
      simp [hzunit, hmult z hz]
    · intro z hzsupport
      simp only [Function.mem_support, ne_eq] at hzsupport
      by_cases hzunit : z ∈ ball (0 : ℂ) 1
      · simp only [hzunit, if_true] at hzsupport
        have hzero : f z = 0 := eq_zero_of_zeroMult_ne_zero hzsupport
        have hzclosed : z ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hzunit
        have hzlt := hzeros z hzclosed hzero
        have hzR : z ∈ ball (0 : ℂ) R := by
          rw [mem_ball, dist_eq_norm]
          exact lt_trans (by simpa [dist_eq_norm] using hzlt) hrR
        exact (hZzero z hzR).mp hzero
      · simp [hzunit] at hzsupport
  have hrestrict : Continuous ((closedBall (0 : ℂ) 1).restrict f) :=
    continuousOn_iff_continuous_restrict.mp hfc
  let clamp : ℝ → ℝ := fun s => max 0 (min 1 s)
  let radius : ℝ → ℝ := fun s => (1 - clamp s) * r + clamp s
  have hclamp : ∀ s, clamp s ∈ Set.Icc (0 : ℝ) 1 := by
    intro s
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hradius : ∀ s, radius s ∈ Set.Icc r 1 := by
    intro s
    have hs := hclamp s
    have hgap : 0 ≤ 1 - r := by linarith
    have hleft : 0 ≤ clamp s * (1 - r) := mul_nonneg hs.1 hgap
    have hright : 0 ≤ (1 - clamp s) * (1 - r) :=
      mul_nonneg (sub_nonneg.mpr hs.2) hgap
    constructor <;> dsimp [radius] <;> nlinarith
  let radial : ℝ × ℝ → closedBall (0 : ℂ) 1 := fun p =>
    ⟨(radius p.1 : ℂ) * Complex.exp (Complex.I * (p.2 : ℂ)), by
      rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
        Real.norm_eq_abs]
      have hrad := hradius p.1
      simp only [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
        Complex.ofReal_re, one_mul, Complex.ofReal_im, mul_zero, sub_zero, Real.exp_zero, mul_one]
      rw [abs_of_nonneg (le_trans hr0.le hrad.1)]
      exact hrad.2⟩
  have hclampc : Continuous clamp :=
    continuous_const.max (continuous_const.min continuous_id)
  have hradiusc : Continuous radius := by
    dsimp [radius]
    fun_prop
  have hradialc : Continuous radial := by
    apply Continuous.subtype_mk
    fun_prop
  let H : ℝ → ℝ → ℂ := fun s θ => f (radial (s, θ))
  have hHc : Continuous (fun p : ℝ × ℝ => H p.1 p.2) := by
    exact hrestrict.comp hradialc
  have hH0 : ∀ s θ, H s θ ≠ 0 := by
    intro s θ hzero
    have hmem : ((radial (s, θ) : closedBall (0 : ℂ) 1) : ℂ) ∈
        closedBall (0 : ℂ) 1 := (radial (s, θ)).property
    have hlt := hzeros _ hmem hzero
    have hnorm : ‖((radial (s, θ) : closedBall (0 : ℂ) 1) : ℂ)‖ = radius s := by
      dsimp [radial]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hrad := hradius s
      simp only [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
        Complex.ofReal_re, one_mul, Complex.ofReal_im, mul_zero, sub_zero, Real.exp_zero, mul_one]
      rw [abs_of_nonneg (le_trans hr0.le hrad.1)]
    rw [hnorm] at hlt
    exact (not_lt_of_ge (hradius s).1) hlt
  have hHloop : ∀ s, H s 0 = H s (2 * Real.pi) := by
    intro s
    apply congrArg f
    dsimp [radial]
    rw [mul_zero, Complex.exp_zero]
    have hexp : Complex.exp (Complex.I * (((2 * Real.pi : ℝ) : ℂ))) = 1 := by
      convert Complex.exp_two_pi_mul_I using 1 <;> push_cast <;> ring
    rw [hexp]
  have hhom := RHTower.windingNumber_homotopy_invariant hHc hH0 hHloop 0 1
  have hHzero : H 0 = fun θ : ℝ =>
      f ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
    funext θ
    simp [H, radial, radius, clamp]
  have hHone : H 1 = fun θ : ℝ =>
      f (Complex.exp (Complex.I * (θ : ℂ))) := by
    funext θ
    simp [H, radial, radius, clamp]
  rw [hHzero, hHone] at hhom
  rw [← hhom, hwInner, hcount]
  norm_cast

/-- The nonnegative total divisor in the unit disc vanishes exactly when the analytic function is
zero-free there. -/
theorem unitDiscZeroMultiplicity_eq_zero_iff
    {f : ℂ → ℂ}
    (hfan : AnalyticOnNhd ℂ f (ball (0 : ℂ) 1))
    (hfc : ContinuousOn f (closedBall (0 : ℂ) 1))
    (hne : ∀ z ∈ sphere (0 : ℂ) 1, f z ≠ 0) :
    unitDiscZeroMultiplicity f = 0 ↔
      ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0 := by
  classical
  obtain ⟨r, hr0, hr1, hzeros⟩ := exists_inner_radius_enclosing_zeros hfc hne
  let R : ℝ := (r + 1) / 2
  have hrR : r < R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hR0 : 0 < R := lt_trans hr0 hrR
  have hclosedR : closedBall (0 : ℂ) R ⊆ ball (0 : ℂ) 1 := by
    intro z hz
    exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) hR1)
  have hfR : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R) :=
    fun z hz => hfan z (hclosedR hz)
  let q : ℝ := (r + R) / 2
  have hrq : r < q := by dsimp [q]; linarith
  have hqR : q < R := by dsimp [q]; linarith
  have hq0 : 0 < q := lt_trans hr0 hrq
  let z₀ : ℂ := q
  have hz₀R : z₀ ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_eq_norm]
    simpa [z₀, abs_of_pos hq0] using hqR
  have hz₀closed : z₀ ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall, dist_eq_norm]
    have hq1 : q ≤ 1 := (lt_trans hqR hR1).le
    simpa [z₀, abs_of_pos hq0] using hq1
  have hfz₀ : f z₀ ≠ 0 := by
    intro hz
    have hlt := hzeros z₀ hz₀closed hz
    dsimp [z₀] at hlt
    have hqr : q < r := by
      simpa [Complex.norm_real, abs_of_pos hq0] using hlt
    exact (not_lt_of_ge hrq.le) hqr
  obtain ⟨Z, m, g, hZR, hmpos, hZzero, hgan, hgne, hfact⟩ :=
    HTGeometry.exists_finset_zeroFree_factorization hfR hz₀R hfz₀
  have hZr : ∀ z ∈ Z, ‖z‖ < r := by
    intro z hz
    have hzballR := hZR z hz
    have hzclosed1 : z ∈ closedBall (0 : ℂ) 1 :=
      ball_subset_closedBall (ball_subset_ball hR1.le hzballR)
    exact hzeros z hzclosed1 ((hZzero z hzballR).mpr hz)
  have hmult : ∀ z ∈ Z, zeroMult f z = m z := by
    intro z hz
    have hzR := hZR z hz
    have h := zeroMult_of_factorization isOpen_ball Z m hgan.differentiableOn hgne hfact hzR
    simpa [hz] using h
  have hcount : unitDiscZeroMultiplicity f = ∑ z ∈ Z, m z := by
    rw [unitDiscZeroMultiplicity]
    rw [finsum_eq_finsetSum_of_support_subset
      (s := Z) (f := fun z : ℂ => if z ∈ ball (0 : ℂ) 1 then zeroMult f z else 0)]
    · apply Finset.sum_congr rfl
      intro z hz
      have hzunit : z ∈ ball (0 : ℂ) 1 := ball_subset_ball hR1.le (hZR z hz)
      simp [hzunit, hmult z hz]
    · intro z hzsupport
      simp only [Function.mem_support, ne_eq] at hzsupport
      by_cases hzunit : z ∈ ball (0 : ℂ) 1
      · simp only [hzunit, if_true] at hzsupport
        have hzero : f z = 0 := eq_zero_of_zeroMult_ne_zero hzsupport
        have hzclosed : z ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hzunit
        have hzlt := hzeros z hzclosed hzero
        have hzR : z ∈ ball (0 : ℂ) R := by
          rw [mem_ball, dist_eq_norm]
          exact lt_trans (by simpa [dist_eq_norm] using hzlt) hrR
        exact (hZzero z hzR).mp hzero
      · simp [hzunit] at hzsupport
  constructor
  · intro hcount0 z hzball hz0
    have hzclosed : z ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hzball
    have hzlt := hzeros z hzclosed hz0
    have hzR : z ∈ ball (0 : ℂ) R := by
      rw [mem_ball, dist_eq_norm]
      exact lt_trans (by simpa [dist_eq_norm] using hzlt) hrR
    have hzZ : z ∈ Z := (hZzero z hzR).mp hz0
    have hmle : m z ≤ ∑ w ∈ Z, m w := by
      exact Finset.single_le_sum (fun w _ => Nat.zero_le (m w)) hzZ
    rw [← hcount, hcount0] at hmle
    have hmpositive := hmpos z hzZ
    omega
  · intro hfree
    rw [hcount]
    apply Finset.sum_eq_zero
    intro z hz
    exfalso
    have hzball : z ∈ ball (0 : ℂ) 1 := ball_subset_ball hR1.le (hZR z hz)
    exact hfree z hzball ((hZzero z (hZR z hz)).mpr hz)

end GaloisForLFunctions.HTGeometry
