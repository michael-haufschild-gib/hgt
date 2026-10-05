import GaloisForLFunctions.RHTower.MaassBesselHolomorphicLines

/-!
# From the imaginary axis to `SL₂(ℤ)`-invariance

Let `u = maassFun g a b` be the Maass function of a coefficient sequence of polynomial growth.

**Theorem** (`maassFun_inv_eq_of_axis`).  If `u(i/y) = u(iy)` for every `y > 0`, then
`u(−1/z) = u(z)` on the whole upper half-plane.  Together with `u(z + 1) = u(z)` this is invariance
under `SL₂(ℤ)` (`S` and `T` generate it).

**Proof.**  `V(z) = u(z) − u(−1/z)` is smooth, satisfies the quarter equation (the Laplacian is
conformally covariant: `Δ(F ∘ S) = |S'|² (ΔF) ∘ S`, and `y²|S'|² = (Im Sz)²`), is even under
`z ↦ −z̄` (because `u` is and `S` commutes with this reflection), vanishes on the imaginary axis, and
is real-analytic along horizontal lines (both summands extend holomorphically in `x`).  The unique
continuation theorem `MaassAxisContinuation.eq_zero_of_axis` gives `V = 0`.
-/

open Complex Set Filter
open scoped ContDiff

noncomputable section

namespace RHTower.MaassBesselSeries

open BesselKZero MaassAxisContinuation GaloisForLFunctions.HTGeometry.ComplexC2Laplacian

variable {g : ℕ → ℂ}

/-! ## The inversion `S(z) = −1/z` -/

/-- `S(z) = −1/z`. -/
def invS (z : ℂ) : ℂ := -z⁻¹

theorem invS_im (z : ℂ) : (invS z).im = z.im / Complex.normSq z := by
  simp [invS, Complex.inv_im, neg_div]

theorem invS_mem_upper {z : ℂ} (hz : z ∈ upper) : invS z ∈ upper := by
  have hz' : 0 < z.im := hz
  have hn : 0 < Complex.normSq z := Complex.normSq_pos.mpr (fun h => by simp [h] at hz')
  show 0 < (invS z).im
  rw [invS_im]
  positivity

theorem ne_zero_of_mem_upper {z : ℂ} (hz : z ∈ upper) : z ≠ 0 := by
  intro h; have : (0 : ℝ) < z.im := hz; simp [h] at this

theorem contDiffAt_invS {z : ℂ} (hz : z ≠ 0) : ContDiffAt ℂ ∞ invS z := by
  unfold invS
  exact (contDiffAt_inv ℂ hz).neg

theorem deriv_invS (z : ℂ) : deriv invS z = (z ^ 2)⁻¹ := by
  unfold invS
  rw [deriv.fun_neg, deriv_inv]
  ring

theorem contDiffOn_comp_invS {F : ℂ → ℂ} (hF : ContDiffOn ℝ ∞ F upper) :
    ContDiffOn ℝ ∞ (fun z => F (invS z)) upper := by
  intro z hz
  have hS : ContDiffAt ℝ ∞ invS z :=
    (contDiffAt_invS (ne_zero_of_mem_upper hz)).restrict_scalars ℝ
  have hFS : ContDiffAt ℝ ∞ F (invS z) := hF.contDiffAt (isOpen_upper.mem_nhds (invS_mem_upper hz))
  exact (hFS.comp z hS).contDiffWithinAt

/-- **The quarter equation is invariant under `S`.** -/
theorem quarterDefect_comp_invS {F : ℂ → ℂ} (hF : ContDiffOn ℝ ∞ F upper)
    (hpde : ∀ w ∈ upper, quarterDefect F w = 0) {z : ℂ} (hz : z ∈ upper) :
    quarterDefect (fun w => F (invS w)) z = 0 := by
  have hz0 := ne_zero_of_mem_upper hz
  have hSz := invS_mem_upper hz
  have hFS : ContDiffAt ℝ 2 F (invS z) :=
    (hF.contDiffAt (isOpen_upper.mem_nhds hSz)).of_le (le_of_lt (by decide))
  have hS2 : ContDiffAt ℂ 2 invS z := (contDiffAt_invS hz0).of_le (le_of_lt (by decide))
  have hlap := laplacian_holomorphic_comp hFS hS2
  have hq := hpde _ hSz
  unfold quarterDefect at hq ⊢
  have hlapF : laplacian F (invS z) = -(quarterWeight (invS z) • F (invS z)) := by
    have : laplacian F (invS z) = dirD 1 (dirD 1 F) (invS z) + dirD I (dirD I F) (invS z) := rfl
    rw [this]
    linear_combination hq
  have hlhs : dirD 1 (dirD 1 (fun w => F (invS w))) z + dirD I (dirD I (fun w => F (invS w))) z =
      laplacian (F ∘ invS) z := rfl
  have hn : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
  have hy : 0 < z.im := hz
  have key : Complex.normSq ((z ^ 2)⁻¹) * quarterWeight (invS z) = quarterWeight z := by
    rw [Complex.normSq_inv, map_pow, quarterWeight, quarterWeight, invS_im]
    field_simp
  rw [hlhs, hlap, hlapF, deriv_invS z, Complex.real_smul, Complex.real_smul]
  have key' : ((Complex.normSq ((z ^ 2)⁻¹) : ℝ) : ℂ) * ((quarterWeight (invS z) : ℝ) : ℂ) =
      ((quarterWeight z : ℝ) : ℂ) := by rw [← Complex.ofReal_mul, key]
  linear_combination (-(F (invS z))) * key'

/-! ## Real-analyticity along horizontal lines -/

/-- Restriction to the real axis of a function holomorphic near a real point is real-analytic. -/
theorem analyticAt_ofReal_comp {h : ℂ → ℂ} {x : ℝ} (hA : AnalyticAt ℂ h (x : ℂ)) :
    AnalyticAt ℝ (fun t : ℝ => h (t : ℂ)) x :=
  (hA.restrictScalars (𝕜 := ℝ)).comp (ofRealCLM.analyticAt x)

/-- `x ↦ u(x + iy₀)` is real-analytic. -/
theorem analyticOnNhd_maassFun_line (hg : PolyGrowth g) (a b : ℂ) {y₀ : ℝ} (hy₀ : 0 < y₀) :
    AnalyticOnNhd ℝ (fun x : ℝ => maassFun g a b ((x : ℂ) + (y₀ : ℂ) * I)) univ := by
  intro x _
  set D : Set ℂ := {s | |s.im| < y₀ / 2} with hD
  have hDo : IsOpen D := isOpen_lt (continuous_abs.comp continuous_im) continuous_const
  have hdiff := differentiableOn_maassC_comp (g := g) hg a b (X := id) (Y := fun _ => (y₀ : ℂ))
    hDo differentiableOn_id (differentiableOn_const _) (δ := y₀) (M := y₀) hy₀
    (fun s _ => by simp) (fun s _ => by simp [abs_of_pos hy₀]) (fun s hs => le_of_lt hs)
  have hxD : (x : ℂ) ∈ D := by simp [hD]; positivity
  have hA := hdiff.analyticAt (hDo.mem_nhds hxD)
  have h := analyticAt_ofReal_comp hA
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [id]
  exact maassC_ofReal a b t hy₀

/-- The real and imaginary parts of `−1/(s + iy₀)` as holomorphic functions of `s`. -/
def invX (y₀ : ℝ) (s : ℂ) : ℂ := -s / (s ^ 2 + (y₀ : ℂ) ^ 2)

/-- See `invX`. -/
def invY (y₀ : ℝ) (s : ℂ) : ℂ := (y₀ : ℂ) / (s ^ 2 + (y₀ : ℂ) ^ 2)

theorem invXY_ofReal (y₀ : ℝ) (x : ℝ) :
    invX y₀ x = (((-x / (x ^ 2 + y₀ ^ 2)) : ℝ) : ℂ) ∧
      invY y₀ x = (((y₀ / (x ^ 2 + y₀ ^ 2)) : ℝ) : ℂ) := by
  constructor <;> simp [invX, invY]

theorem invS_line {y₀ : ℝ} (hy₀ : 0 < y₀) (x : ℝ) :
    invS ((x : ℂ) + (y₀ : ℂ) * I) =
      (((-x / (x ^ 2 + y₀ ^ 2)) : ℝ) : ℂ) + (((y₀ / (x ^ 2 + y₀ ^ 2)) : ℝ) : ℂ) * I := by
  have hden : (x : ℂ) ^ 2 + (y₀ : ℂ) ^ 2 ≠ 0 := by
    have : (0 : ℝ) < x ^ 2 + y₀ ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hne : (x : ℂ) + (y₀ : ℂ) * I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  unfold invS
  push_cast
  field_simp
  ring_nf
  simp only [I_sq]
  ring

/-- `x ↦ u(−1/(x + iy₀))` is real-analytic. -/
theorem analyticOnNhd_maassFun_inv_line (hg : PolyGrowth g) (a b : ℂ) {y₀ : ℝ} (hy₀ : 0 < y₀) :
    AnalyticOnNhd ℝ (fun x : ℝ => maassFun g a b (invS ((x : ℂ) + (y₀ : ℂ) * I))) univ := by
  intro x₀ _
  set q₀ : ℝ := y₀ / (x₀ ^ 2 + y₀ ^ 2) with hq₀
  have hq₀pos : 0 < q₀ := by positivity
  set U₀ : Set ℂ := {s | s ^ 2 + (y₀ : ℂ) ^ 2 ≠ 0} with hU₀
  have hU₀o : IsOpen U₀ := isOpen_ne_fun (by fun_prop) continuous_const
  have hden : ∀ s : ℂ, DifferentiableAt ℂ (fun s : ℂ => s ^ 2 + (y₀ : ℂ) ^ 2) s := fun s =>
    (differentiableAt_id.pow 2).add (differentiableAt_const _)
  have hXd : DifferentiableOn ℂ (invX y₀) U₀ := fun s hs =>
    (differentiableAt_id.neg.div (hden s) hs).differentiableWithinAt
  have hYd : DifferentiableOn ℂ (invY y₀) U₀ := fun s hs =>
    ((differentiableAt_const _).div (hden s) hs).differentiableWithinAt
  set D : Set ℂ := (U₀ ∩ invY y₀ ⁻¹' {w | q₀ / 2 < w.re ∧ ‖w‖ < q₀ + 1}) ∩
    invX y₀ ⁻¹' {w | |w.im| < q₀ / 4} with hD
  have hDo : IsOpen D := by
    have ht1 : IsOpen {w : ℂ | q₀ / 2 < w.re ∧ ‖w‖ < q₀ + 1} :=
      (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_norm continuous_const)
    have ht2 : IsOpen {w : ℂ | |w.im| < q₀ / 4} :=
      isOpen_lt (continuous_abs.comp continuous_im) continuous_const
    have h1 := hYd.continuousOn.isOpen_inter_preimage hU₀o ht1
    exact (hXd.continuousOn.mono inter_subset_left).isOpen_inter_preimage h1 ht2
  have hDU : D ⊆ U₀ := fun s hs => hs.1.1
  have hx₀D : (x₀ : ℂ) ∈ D := by
    obtain ⟨hX, hY⟩ := invXY_ofReal y₀ x₀
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show (x₀ : ℂ) ^ 2 + (y₀ : ℂ) ^ 2 ≠ 0
      have : (0 : ℝ) < x₀ ^ 2 + y₀ ^ 2 := by positivity
      exact_mod_cast this.ne'
    · show q₀ / 2 < (invY y₀ x₀).re ∧ ‖invY y₀ x₀‖ < q₀ + 1
      rw [hY]
      simp only [ofReal_re, Complex.norm_real, Real.norm_eq_abs]
      rw [← hq₀, abs_of_pos hq₀pos]
      constructor <;> linarith
    · show |(invX y₀ x₀).im| < q₀ / 4
      rw [hX]; simp only [ofReal_im, abs_zero]; linarith
  have hdiff := differentiableOn_maassC_comp (g := g) hg a b (X := invX y₀) (Y := invY y₀)
    hDo (hXd.mono hDU) (hYd.mono hDU) (δ := q₀ / 2) (M := q₀ + 1) (by positivity)
    (fun s hs => le_of_lt hs.1.2.1) (fun s hs => le_of_lt hs.1.2.2)
    (fun s hs => by have := hs.2; simp only [mem_preimage, mem_setOf_eq] at this; linarith)
  have hA := hdiff.analyticAt (hDo.mem_nhds hx₀D)
  have h := analyticAt_ofReal_comp hA
  refine h.congr (Eventually.of_forall fun t => ?_)
  obtain ⟨hX, hY⟩ := invXY_ofReal y₀ t
  simp only
  rw [hX, hY, maassC_ofReal a b _ (by positivity), invS_line hy₀ t]

/-! ## The automorphy theorem -/

theorem invS_neg_conj (z : ℂ) : invS (-(starRingEnd ℂ) z) = -(starRingEnd ℂ) (invS z) := by
  simp [invS, map_neg, map_inv₀]

theorem invS_I_mul (y : ℝ) : invS ((y : ℂ) * I) = ((1 / y : ℝ) : ℂ) * I := by
  unfold invS
  rw [mul_inv, Complex.inv_I]
  push_cast
  ring

/-- **Axis symmetry implies `S`-invariance.** -/
theorem maassFun_inv_eq_of_axis (hg : PolyGrowth g) (a b : ℂ)
    (haxis : ∀ y : ℝ, 0 < y → maassFun g a b ((1 / y : ℝ) * I) = maassFun g a b ((y : ℂ) * I))
    {z : ℂ} (hz : 0 < z.im) : maassFun g a b (invS z) = maassFun g a b z := by
  set V : ℂ → ℂ := fun w => maassFun g a b w - maassFun g a b (invS w) with hV
  have hu := contDiffOn_maassFun hg a b
  have hVs : ContDiffOn ℝ ∞ V upper := hu.sub (contDiffOn_comp_invS hu)
  have hVpde : ∀ w ∈ upper, quarterDefect V w = 0 := by
    intro w hw
    have hG : ContDiffOn ℝ ∞ (fun w => (-1 : ℂ) * maassFun g a b (invS w)) upper :=
      ((contDiffOn_comp_invS hu).const_smul (-1 : ℂ)).congr fun w _ => by simp [smul_eq_mul]
    have h1 := quarterDefect_maassFun hg a b (show 0 < w.im from hw)
    have h2 := quarterDefect_comp_invS hu (fun v hv => quarterDefect_maassFun hg a b hv) hw
    have hsum := quarterDefect_add (F := maassFun g a b)
      (G := fun w => (-1 : ℂ) * maassFun g a b (invS w)) hu hG hw
    have hneg := quarterDefect_const_mul (contDiffOn_comp_invS hu) (-1 : ℂ) hw
    have hVeq : V = fun w => maassFun g a b w + (-1 : ℂ) * maassFun g a b (invS w) := by
      funext w; simp only [hV]; ring
    rw [hVeq, hsum, hneg, h1, h2]
    ring
  have hVeven : ∀ w ∈ upper, V (-(starRingEnd ℂ) w) = V w := by
    intro w _
    simp only [hV, maassFun_neg_conj, invS_neg_conj]
  have hVax : ∀ y : ℝ, 0 < y → V ((y : ℂ) * I) = 0 := by
    intro y hy
    simp only [hV, invS_I_mul y, haxis y hy, sub_self]
  have hVana : ∀ y : ℝ, 0 < y → AnalyticOnNhd ℝ (fun x : ℝ => V ((x : ℂ) + (y : ℂ) * I)) univ := by
    intro y hy x hx
    exact (analyticOnNhd_maassFun_line hg a b hy x hx).sub
      (analyticOnNhd_maassFun_inv_line hg a b hy x hx)
  have h0 := eq_zero_of_axis hVs hVpde hVeven hVax hVana z hz
  simp only [hV] at h0
  exact (sub_eq_zero.mp h0).symm

end RHTower.MaassBesselSeries
