import GaloisForLFunctions.RHTower.PowerLagLandauSeries

/-!
# The lag sequence on the `k`-th powers: the zero-side continuation

`G_k(u) = M ζ(k + u) − Σ_ρ w_ρ ζ(u + 3k/2 − kρ)` is differentiable on every open set on which the
shifted arguments stay right of `Re = ½`, the arguments of the copies with a fixed ordinate `t₀`
avoid `1`, and the remaining arguments keep a fixed distance from `1` (their imaginary parts are
bounded away from zero).  The far terms are controlled by the exponent-`½` vertical bound for `ζ`
and the summability of `|w_ρ| √(2 + |γ|)`.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- The term of the copy `q`. -/
def powTerm (k : ℕ) (q : XiZeroCopy) (u : ℂ) : ℂ := lagWeight q * riemannZeta (powShift k q u)

/-- The zero-side continuation. -/
def powLandauG (k : ℕ) (M : ℝ) (u : ℂ) : ℂ :=
  (M : ℂ) * riemannZeta ((k : ℂ) + u) - ∑' q : XiZeroCopy, powTerm k q u

theorem LSeries_powLagCoeff_eq_powLandauG {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ2 : 1 / 2 ≤ θ) (k : ℕ) {M : ℝ} {u : ℂ} (hu : powAbscissa k θ < u.re) :
    LSeries (fun m => (powLagCoeff k M m : ℂ)) u = powLandauG k M u :=
  LSeries_powLagCoeff_eq hθ hθ2 k hu

/-- The copies with ordinate exactly `t₀`. -/
def sameOrdinate (t₀ : ℝ) : Set XiZeroCopy := {q | zeroOrdinate q = t₀}

theorem finite_sameOrdinate (t₀ : ℝ) : (sameOrdinate t₀).Finite :=
  (finite_nearSet t₀).subset fun q hq => by
    show |zeroOrdinate q - t₀| < 5
    rw [show zeroOrdinate q = t₀ from hq, sub_self, abs_zero]; norm_num

/-- An open box `a < Re u < b`, `|Im u − t₀| < r`. -/
def powBox (a b t₀ r : ℝ) : Set ℂ := {u | a < u.re ∧ u.re < b ∧ |u.im - t₀| < r}

theorem isOpen_powBox (a b t₀ r : ℝ) : IsOpen (powBox a b t₀ r) := by
  unfold powBox
  refine (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter ?_)
  exact isOpen_lt (continuous_abs.comp (Complex.continuous_im.sub continuous_const)) continuous_const

/-! ## The far-term bound -/

/-- The constant of the far majorant. -/
def powFarConst (k : ℕ) (g B : ℝ) : ℝ :=
  (2 + 1 / (k * g / 2) + 2) * Real.sqrt (B + 5 * k / 2 + 2 + k)

theorem powFarConst_nonneg {k : ℕ} {g B : ℝ} (hg : 0 < g) (hk : 1 ≤ k) (hB : 0 ≤ B) :
    0 ≤ powFarConst k g B := by
  unfold powFarConst
  have : (0 : ℝ) < k := by exact_mod_cast hk
  positivity

/-- **The far-term bound.**  If `Re u ≥ k(θ − 3/2) + 1 − η` with `η ≤ ½`, `|Im u − k t₀| ≤ kg/2`,
`‖u‖ ≤ B`, and `|γ_q − t₀| ≥ g`, then `‖term_q(u)‖ ≤ ‖w_q‖ · C · √(2 + |γ_q|)`. -/
theorem norm_powTerm_le_far {θ η : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) (hη : η ≤ 1 / 2)
    {k : ℕ} (hk : 1 ≤ k) {t₀ g B : ℝ} (hg : 0 < g) {u : ℂ} (hu1 : powAbscissa k θ - η ≤ u.re)
    (hu2 : |u.im - k * t₀| ≤ k * g / 2) (hB : ‖u‖ ≤ B) {q : XiZeroCopy}
    (hq : g ≤ |zeroOrdinate q - t₀|) :
    ‖powTerm k q u‖ ≤ ‖lagWeight q‖ * (powFarConst k g B * Real.sqrt (2 + |zeroOrdinate q|)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set w : ℂ := powShift k q u with hw
  have hre : 1 / 2 ≤ w.re := by
    have := one_add_le_powShift_re hθ k q u
    rw [← hw] at this
    linarith
  have hd : 0 < k * g / 2 := by positivity
  have hsep : k * g / 2 ≤ ‖w - 1‖ := by
    have him : (w - 1).im = u.im - k * zeroOrdinate q := by
      rw [Complex.sub_im, Complex.one_im, sub_zero, hw, powShift_im]
    have htri : |k * zeroOrdinate q - k * t₀| ≤ |k * zeroOrdinate q - u.im| + |u.im - k * t₀| :=
      abs_sub_le _ _ _
    have hkq : |k * zeroOrdinate q - k * t₀| = k * |zeroOrdinate q - t₀| := by
      rw [← mul_sub, abs_mul, abs_of_pos hk0]
    have h1 : k * g ≤ |k * zeroOrdinate q - u.im| + k * g / 2 := by
      have := mul_le_mul_of_nonneg_left hq hk0.le
      linarith
    have h2 : |k * zeroOrdinate q - u.im| = |(w - 1).im| := by rw [him, abs_sub_comm]
    calc k * g / 2 ≤ |(w - 1).im| := by rw [← h2]; linarith
      _ ≤ ‖w - 1‖ := Complex.abs_im_le_norm _
  have hζ := norm_riemannZeta_le_sqrt_norm_add_two_half hre hd hsep
  -- `‖w‖ + 2 ≤ (B + 5k/2 + 2 + k)(2 + |γ_q|)`
  have hρ : ‖(q.1 : ℂ)‖ ≤ 1 + |zeroOrdinate q| := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (q.1 : ℂ)
    have h2 : |(q.1 : ℂ).re| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [xiZeroCopy_re_pos q], (xiZeroCopy_re_lt_one q).le⟩
    unfold zeroOrdinate
    linarith
  have hnormw : ‖w‖ ≤ B + 3 * k / 2 + k * (1 + |zeroOrdinate q|) := by
    have e : w = u + (3 * (k : ℝ) / 2 : ℝ) - (k : ℂ) * (q.1 : ℂ) := by
      rw [hw]; unfold powShift; push_cast; ring
    rw [e]
    calc ‖u + ((3 * (k : ℝ) / 2 : ℝ) : ℂ) - (k : ℂ) * (q.1 : ℂ)‖
        ≤ ‖u + ((3 * (k : ℝ) / 2 : ℝ) : ℂ)‖ + ‖(k : ℂ) * (q.1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ (‖u‖ + ‖((3 * (k : ℝ) / 2 : ℝ) : ℂ)‖) + ‖(k : ℂ) * (q.1 : ℂ)‖ := by
          gcongr; exact norm_add_le _ _
      _ = ‖u‖ + 3 * k / 2 + k * ‖(q.1 : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul,
            Complex.norm_natCast]
      _ ≤ B + 3 * k / 2 + k * (1 + |zeroOrdinate q|) := by gcongr
  have hB0 : 0 ≤ B := (norm_nonneg u).trans hB
  have hA : ‖w‖ + 2 ≤ (B + 5 * k / 2 + 2 + k) * (2 + |zeroOrdinate q|) := by
    have := abs_nonneg (zeroOrdinate q)
    nlinarith
  have hsqrt : Real.sqrt (‖w‖ + 2)
      ≤ Real.sqrt (B + 5 * k / 2 + 2 + k) * Real.sqrt (2 + |zeroOrdinate q|) := by
    rw [← Real.sqrt_mul (by linarith)]
    exact Real.sqrt_le_sqrt hA
  unfold powTerm powFarConst
  rw [norm_mul]
  calc ‖lagWeight q‖ * ‖riemannZeta w‖
      ≤ ‖lagWeight q‖ * ((2 + 1 / (k * g / 2) + 2) * Real.sqrt (‖w‖ + 2)) := by gcongr
    _ ≤ ‖lagWeight q‖ * ((2 + 1 / (k * g / 2) + 2)
          * (Real.sqrt (B + 5 * k / 2 + 2 + k) * Real.sqrt (2 + |zeroOrdinate q|))) := by
        gcongr
    _ = _ := by ring

/-- The far majorant is summable. -/
theorem summable_powFar_majorant (C : ℝ) :
    Summable fun q : XiZeroCopy => ‖lagWeight q‖ * (C * Real.sqrt (2 + |zeroOrdinate q|)) := by
  have := summable_lagWeight_mul_sqrt.mul_left C
  refine this.congr fun q => ?_
  ring

/-! ## Differentiability -/

theorem differentiableOn_powTerm (k : ℕ) (q : XiZeroCopy) {U : Set ℂ}
    (hU : ∀ u ∈ U, powShift k q u ≠ 1) : DifferentiableOn ℂ (powTerm k q) U := by
  intro u hu
  have h1 : DifferentiableAt ℂ (powShift k q) u := by
    unfold powShift
    fun_prop
  have h2 : DifferentiableAt ℂ riemannZeta (powShift k q u) := differentiableAt_riemannZeta (hU u hu)
  exact ((h2.comp u h1).const_mul _).differentiableWithinAt

/-- Summability of the full family at a point where the far terms are dominated. -/
theorem summable_powTerm_family {θ η : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) (hη : η ≤ 1 / 2)
    {k : ℕ} (hk : 1 ≤ k) {t₀ g B : ℝ} (hg : 0 < g)
    (hgap : ∀ q : XiZeroCopy, zeroOrdinate q ≠ t₀ → g ≤ |zeroOrdinate q - t₀|) {u : ℂ}
    (hu1 : powAbscissa k θ - η ≤ u.re) (hu2 : |u.im - k * t₀| ≤ k * g / 2) (hB : ‖u‖ ≤ B) :
    Summable fun q : XiZeroCopy => powTerm k q u := by
  have hfar : Summable fun q : ↑(sameOrdinate t₀)ᶜ => powTerm k q u :=
    Summable.of_norm_bounded ((summable_powFar_majorant (powFarConst k g B)).subtype _)
      fun q => norm_powTerm_le_far hθ hη hk hg hu1 hu2 hB (hgap q.1 q.2)
  have hnear : Summable fun q : sameOrdinate t₀ => powTerm k q u := by
    haveI : Finite (sameOrdinate t₀) := (finite_sameOrdinate t₀).to_subtype
    exact Summable.of_finite
  exact summable_subtype_and_compl.mp ⟨hnear, hfar⟩

theorem tsum_powTerm_split {θ η : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) (hη : η ≤ 1 / 2)
    {k : ℕ} (hk : 1 ≤ k) {t₀ g B : ℝ} (hg : 0 < g)
    (hgap : ∀ q : XiZeroCopy, zeroOrdinate q ≠ t₀ → g ≤ |zeroOrdinate q - t₀|) {u : ℂ}
    (hu1 : powAbscissa k θ - η ≤ u.re) (hu2 : |u.im - k * t₀| ≤ k * g / 2) (hB : ‖u‖ ≤ B) :
    ∑' q, powTerm k q u
      = ∑ q ∈ (finite_sameOrdinate t₀).toFinset, powTerm k q u
        + ∑' q : ↑(sameOrdinate t₀)ᶜ, powTerm k q u := by
  have hsum := summable_powTerm_family hθ hη hk hg hgap hu1 hu2 hB
  rw [← hsum.tsum_subtype_add_tsum_subtype_compl (sameOrdinate t₀)]
  congr 1
  rw [← tsum_congr_set_coe (fun q => powTerm k q u) (Set.Finite.coe_toFinset (finite_sameOrdinate t₀))]
  exact Finset.tsum_subtype' _ (fun q => powTerm k q u)

/-- **The continuation is differentiable on any open set on which the far terms are dominated, the
same-ordinate terms avoid their poles, and `k + u ≠ 1`.** -/
theorem differentiableOn_powLandauG {θ η : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hη : η ≤ 1 / 2) {k : ℕ} (hk : 1 ≤ k) {M : ℝ} {t₀ g B : ℝ} (hg : 0 < g)
    (hgap : ∀ q : XiZeroCopy, zeroOrdinate q ≠ t₀ → g ≤ |zeroOrdinate q - t₀|) {U : Set ℂ}
    (hUopen : IsOpen U) (hUre : ∀ u ∈ U, powAbscissa k θ - η ≤ u.re)
    (hUim : ∀ u ∈ U, |u.im - k * t₀| ≤ k * g / 2) (hUB : ∀ u ∈ U, ‖u‖ ≤ B)
    (hUk : ∀ u ∈ U, (k : ℂ) + u ≠ 1)
    (hS : ∀ q ∈ sameOrdinate t₀, ∀ u ∈ U, powShift k q u ≠ 1) :
    DifferentiableOn ℂ (powLandauG k M) U := by
  have hfun : ∀ u ∈ U, powLandauG k M u
      = (M : ℂ) * riemannZeta ((k : ℂ) + u)
        - (∑ q ∈ (finite_sameOrdinate t₀).toFinset, powTerm k q u
          + ∑' q : ↑(sameOrdinate t₀)ᶜ, powTerm k q u) := by
    intro u hu
    unfold powLandauG
    rw [tsum_powTerm_split hθ hη hk hg hgap (hUre u hu) (hUim u hu) (hUB u hu)]
  refine DifferentiableOn.congr ?_ hfun
  -- the `M` term
  have hM : DifferentiableOn ℂ (fun u : ℂ => (M : ℂ) * riemannZeta ((k : ℂ) + u)) U := by
    intro u hu
    have h1 : DifferentiableAt ℂ (fun u : ℂ => (k : ℂ) + u) u := by fun_prop
    have h2 : DifferentiableAt ℂ riemannZeta ((k : ℂ) + u) := differentiableAt_riemannZeta (hUk u hu)
    exact ((h2.comp u h1).const_mul _).differentiableWithinAt
  -- the same-ordinate terms
  have hnearD : DifferentiableOn ℂ
      (fun u => ∑ q ∈ (finite_sameOrdinate t₀).toFinset, powTerm k q u) U := by
    have := DifferentiableOn.sum (𝕜 := ℂ) (s := U) (u := (finite_sameOrdinate t₀).toFinset)
      (A := fun q => powTerm k q) fun q hq => ?_
    · refine this.congr fun u _ => ?_
      simp [Finset.sum_apply]
    · have hqn : q ∈ sameOrdinate t₀ := (Set.Finite.mem_toFinset _).mp hq
      exact differentiableOn_powTerm k q fun u hu => hS q hqn u hu
  -- the far terms
  have hfarD : DifferentiableOn ℂ (fun u => ∑' q : ↑(sameOrdinate t₀)ᶜ, powTerm k q u) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun q : ↑(sameOrdinate t₀)ᶜ =>
        ‖lagWeight q‖ * (powFarConst k g B * Real.sqrt (2 + |zeroOrdinate q|)))
      ((summable_powFar_majorant _).subtype _) (fun q => ?_) hUopen
      (fun q u hu => norm_powTerm_le_far hθ hη hk hg (hUre u hu) (hUim u hu) (hUB u hu)
        (hgap q.1 q.2))
    refine differentiableOn_powTerm k q.1 fun u hu h1 => ?_
    -- the argument is not `1`: its imaginary part is nonzero
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have him : (powShift k q.1 u).im = u.im - k * zeroOrdinate q.1 := powShift_im k q.1 u
    rw [h1, Complex.one_im] at him
    have hq := hgap q.1 q.2
    have hu2 := hUim u hu
    have hkq : |k * zeroOrdinate q.1 - k * t₀| = k * |zeroOrdinate q.1 - t₀| := by
      rw [← mul_sub, abs_mul, abs_of_pos hk0]
    have htri : |k * zeroOrdinate q.1 - k * t₀| ≤ |k * zeroOrdinate q.1 - u.im| + |u.im - k * t₀| :=
      abs_sub_le _ _ _
    have h0 : |k * zeroOrdinate q.1 - u.im| = 0 := by
      rw [abs_eq_zero]; linarith
    have := mul_le_mul_of_nonneg_left hq hk0.le
    have hkg : 0 < k * g := mul_pos hk0 hg
    linarith
  exact hM.sub (hnearD.add hfarD)

end

end RHTower
