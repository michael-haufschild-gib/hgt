import GaloisForLFunctions.ArithmeticPolarization.HeckeInvarianceOfTheCollidedPolarizationIsRH

/-!
# The depth profile carries the global collision

The global collision of conjugate zeros has no analytic carrier (`TheCollisionLaw`). It has a
positive one. For a test `f`, the **depth profile** `L ↦ D(T_L f) = Σ_ρ m_ρ e^{2(Re ρ − ½)L} |f̂(ρ)|²`
is the two-sided Laplace transform of the **depth measure** `Σ_ρ m_ρ |f̂(ρ)|² δ_{2(Re ρ − ½)}`: the
collided points `2 Re ρ − ½` of `TheCollisionLaw`, weighted by what `f` sees of them.

* **Two-sided bounds** (`term_le_depthProfile`, `depthProfile_le_of_depth_le`): every seen zero of
  depth `a` contributes `m |f̂(ρ)|² e^{2aL}`; if every seen zero has depth `≤ a`, the profile is at
  most `e^{2aL} D(f)` for `L ≥ 0`.
* **The rate law** (`tendsto_log_depthProfile_div`): `(1/L) log D(T_L f) → 2 a_f` as `L → ∞`, where
  `a_f` is the supremum of the depths of the zeros that `f` sees. No genericity is needed: the
  profile is a positive combination of real exponentials.

For `ζ` the depth measure of every test is a point mass at `0` iff RH: the collided polarization is
Hecke invariant (`HeckeInvarianceOfTheCollidedPolarizationIsRH`), equivalently every depth profile
is constant, equivalently every rate vanishes.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open Zeta23

variable (Z : Zeta23.ZeroConfig)

/-- The **depth profile** `L ↦ D(T_L f)`. -/
def depthProfile (f : ℝ → ℂ) (L : ℝ) : ℝ := collidedForm Z (translate L f)

/-- The weight `m_ρ |f̂(ρ)|²` of a zero in the depth measure of `f`. -/
def depthWeight (f : ℝ → ℂ) (ρ : Z.carrier) : ℝ := (Z.mult ρ : ℝ) * Complex.normSq (tr f ρ)

/-- The depth `Re ρ − ½`. -/
def depth (ρ : Z.carrier) : ℝ := (ρ : ℂ).re - 1 / 2

variable {Z}

theorem depthWeight_nonneg (f : ℝ → ℂ) (ρ : Z.carrier) : 0 ≤ depthWeight Z f ρ :=
  mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

theorem depthProfile_eq (f : ℝ → ℂ) (L : ℝ) :
    depthProfile Z f L = ∑' ρ : Z.carrier, depthWeight Z f ρ * Real.exp (2 * depth Z ρ * L) := by
  rw [depthProfile, collidedForm_translate]
  exact tsum_congr fun ρ => by simp only [depthWeight, depth]; ring

theorem depth_le_half (ρ : Z.carrier) : |depth Z ρ| ≤ 1 / 2 := by
  have := Z.strip ρ ρ.2
  rw [depth, abs_le]; constructor <;> linarith [this.1, this.2]

/-- The profile series converges whenever the collided series of `f` does. -/
theorem summable_depthProfile {f : ℝ → ℂ} (hs : Summable (depthWeight Z f)) (L : ℝ) :
    Summable fun ρ : Z.carrier => depthWeight Z f ρ * Real.exp (2 * depth Z ρ * L) := by
  refine Summable.of_nonneg_of_le (fun ρ => mul_nonneg (depthWeight_nonneg f ρ) (Real.exp_pos _).le)
    (fun ρ => ?_) (hs.mul_right (Real.exp |L|))
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (depthWeight_nonneg f ρ)
  have h := depth_le_half (Z := Z) ρ
  calc 2 * depth Z ρ * L ≤ |2 * depth Z ρ * L| := le_abs_self _
    _ = 2 * |depth Z ρ| * |L| := by rw [abs_mul, abs_mul]; norm_num
    _ ≤ 2 * (1 / 2) * |L| := by gcongr
    _ = |L| := by ring

/-- Every seen zero contributes its own exponential to the profile. -/
theorem term_le_depthProfile {f : ℝ → ℂ} (hs : Summable (depthWeight Z f)) (L : ℝ)
    (ρ : Z.carrier) :
    depthWeight Z f ρ * Real.exp (2 * depth Z ρ * L) ≤ depthProfile Z f L := by
  rw [depthProfile_eq]
  exact (summable_depthProfile hs L).le_tsum ρ fun ρ' _ =>
    mul_nonneg (depthWeight_nonneg f ρ') (Real.exp_pos _).le

/-- If every seen zero has depth `≤ a`, the profile grows at most like `e^{2aL}`. -/
theorem depthProfile_le_of_depth_le {f : ℝ → ℂ} (hs : Summable (depthWeight Z f)) {a L : ℝ}
    (hL : 0 ≤ L) (ha : ∀ ρ : Z.carrier, depthWeight Z f ρ ≠ 0 → depth Z ρ ≤ a) :
    depthProfile Z f L ≤ Real.exp (2 * a * L) * collidedForm Z f := by
  rw [depthProfile_eq, collidedForm, ← tsum_mul_left]
  refine (summable_depthProfile hs L).tsum_le_tsum (fun ρ => ?_) (hs.mul_left _)
  by_cases h0 : depthWeight Z f ρ = 0
  · rw [h0, zero_mul]
    exact mul_nonneg (Real.exp_pos _).le (depthWeight_nonneg f ρ)
  · rw [mul_comm (Real.exp _)]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (depthWeight_nonneg f ρ)
    have := ha ρ h0
    nlinarith

/-- The supremum of the depths of the zeros seen by `f`. -/
def seenDepth (Z : Zeta23.ZeroConfig) (f : ℝ → ℂ) : ℝ :=
  sSup (depth Z '' {ρ | depthWeight Z f ρ ≠ 0})

theorem translate_zero (f : ℝ → ℂ) : translate 0 f = f := by
  funext u; simp [translate]

theorem bddAbove_seen (f : ℝ → ℂ) : BddAbove (depth Z '' {ρ | depthWeight Z f ρ ≠ 0}) :=
  ⟨1 / 2, by rintro _ ⟨ρ, -, rfl⟩; exact (abs_le.mp (depth_le_half ρ)).2⟩

/-- **The rate law.** For a test that sees some zero, `(1/L) log D(T_L f) → 2 a_f`. -/
theorem tendsto_log_depthProfile_div {f : ℝ → ℂ} (hs : Summable (depthWeight Z f))
    (hseen : ∃ ρ : Z.carrier, depthWeight Z f ρ ≠ 0) :
    Tendsto (fun L => Real.log (depthProfile Z f L) / L) atTop (𝓝 (2 * seenDepth Z f)) := by
  obtain ⟨ρ₀, hρ₀⟩ := hseen
  have hne : (depth Z '' {ρ | depthWeight Z f ρ ≠ 0}).Nonempty := ⟨_, ρ₀, hρ₀, rfl⟩
  have hbdd := bddAbove_seen (Z := Z) f
  have hw₀ : 0 < depthWeight Z f ρ₀ := lt_of_le_of_ne (depthWeight_nonneg f ρ₀) (Ne.symm hρ₀)
  have hD : 0 < collidedForm Z f := by
    have := term_le_depthProfile hs 0 ρ₀
    rw [mul_zero, Real.exp_zero, mul_one, depthProfile, translate_zero] at this
    exact lt_of_lt_of_le hw₀ this
  have hpos : ∀ L, 0 < depthProfile Z f L := fun L =>
    lt_of_lt_of_le (mul_pos hw₀ (Real.exp_pos _)) (term_le_depthProfile hs L ρ₀)
  rw [tendsto_order]
  constructor
  · -- lower bound through one deep seen zero
    intro b hb
    have hb2 : b / 2 < seenDepth Z f := by linarith
    obtain ⟨_, ⟨ρ₁, hρ₁, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne hb2
    have hw₁ : 0 < depthWeight Z f ρ₁ := lt_of_le_of_ne (depthWeight_nonneg f ρ₁) (Ne.symm hρ₁)
    have hlim : Tendsto (fun L : ℝ => Real.log (depthWeight Z f ρ₁) / L + 2 * depth Z ρ₁) atTop
        (𝓝 (0 + 2 * depth Z ρ₁)) :=
      (tendsto_const_nhds.div_atTop tendsto_id).add tendsto_const_nhds
    have hev := hlim.eventually (lt_mem_nhds (show b < 0 + 2 * depth Z ρ₁ by linarith))
    filter_upwards [hev, eventually_gt_atTop 0] with L hL hL0
    refine lt_of_lt_of_le hL ?_
    rw [le_div_iff₀ hL0]
    have h1 := term_le_depthProfile hs L ρ₁
    have h2 := Real.log_le_log (mul_pos hw₁ (Real.exp_pos _)) h1
    rw [Real.log_mul hw₁.ne' (Real.exp_pos _).ne', Real.log_exp] at h2
    have : (Real.log (depthWeight Z f ρ₁) / L + 2 * depth Z ρ₁) * L =
        Real.log (depthWeight Z f ρ₁) + 2 * depth Z ρ₁ * L := by field_simp
    linarith
  · -- upper bound through the supremum
    intro b hb
    have hlim : Tendsto (fun L : ℝ => 2 * seenDepth Z f + Real.log (collidedForm Z f) / L) atTop
        (𝓝 (2 * seenDepth Z f + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
    have hev := hlim.eventually (gt_mem_nhds (show 2 * seenDepth Z f + 0 < b by linarith))
    filter_upwards [hev, eventually_gt_atTop 0] with L hL hL0
    refine lt_of_le_of_lt ?_ hL
    rw [div_le_iff₀ hL0]
    have hle := depthProfile_le_of_depth_le hs hL0.le (a := seenDepth Z f) fun ρ hρ =>
      le_csSup hbdd ⟨ρ, hρ, rfl⟩
    have h2 := Real.log_le_log (hpos L) hle
    rw [Real.log_mul (Real.exp_pos _).ne' hD.ne', Real.log_exp] at h2
    have : (2 * seenDepth Z f + Real.log (collidedForm Z f) / L) * L =
        2 * seenDepth Z f * L + Real.log (collidedForm Z f) := by field_simp
    linarith

end GaloisForLFunctions.ArithmeticPolarization
