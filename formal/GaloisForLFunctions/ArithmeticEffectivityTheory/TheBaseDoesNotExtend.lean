import GaloisForLFunctions.ArithmeticEffectivityTheory.TheEffectivityCalculus
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheThetaH0OfSpecZ

/-!
# The base `h⁰` does not extend to the surface

The theta `h⁰` of `Spec ℤ`, `h⁰(d) = log Σ_{n ∈ ℤ} e^{−π n² e^{−2d}}`, has an exact Riemann–Roch
`h⁰(d) − h⁰(−d) = d` from Poisson summation. Its Euler characteristic is linear in the degree. A
surface needs one that is quadratic in the class.

* **Hilbert–Samuel is forced** (`hilbertSamuel_of_riemannInequality`). On every polar surface the
  Riemann inequality makes `h(nA) + h(κ − nA) ≥ c n²` eventually, for every `c < 1`: the Euler
  characteristic of `nA` is `n² − O(n)`. A function with affine growth in the degree violates the
  Riemann inequality (`not_riemannInequality_of_affine_bound`).
* **The theta `h⁰` of the degree** (`thetaEffectivity`, `h(x) = h⁰(x · A)`). On every polar surface —
  curve windows, the golden datum, the scaling surface of `ℤ` whether or not RH holds — it is
  positive, satisfies the linear Riemann–Roch `h(x) − h(−x) = x · A`, is constant on degree levels
  and vanishes in very negative degree (`thetaEffectivity_linear_laws`); it satisfies the quadratic
  Riemann inequality on none (`thetaEffectivity_not_riemannInequality`).
* **Degree functions** (`exists_degree_effectivity_iff_hodgeIndex`). A function of the degree alone
  is an effectivity function only on surfaces with the Hodge index, and there the quadratic level
  bound `t ↦ max(0, (t − (a − b)/2)²/4 − bt/2 + χ₀)` is one. The sign is whether the degree controls
  the Euler characteristic on its level sets, and the control is quadratic.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

open ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (S : PolarSurface E)

/-- **Hilbert–Samuel along the ample class.** The Riemann inequality forces quadratic growth along
`nA`, at every rate `c < 1 = ½ A²`. -/
theorem hilbertSamuel_of_riemannInequality {κ : E} {χ₀ : ℝ} {h : E → ℝ}
    (hRI : RiemannInequality S κ χ₀ h) {c : ℝ} (hc : c < 1) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ 2 ≤ h ((n : ℝ) • S.ample) + h (κ - (n : ℝ) • S.ample) :=
  eventually_le_of_riemannInequality S hRI (by rw [S.pair_ample_ample]; linarith)

/-- A function bounded by an affine function of `|degree|` has no Riemann inequality: along `nA` it
grows linearly while the Euler characteristic grows like `n²`. -/
theorem not_riemannInequality_of_affine_bound {κ : E} {χ₀ α β : ℝ} {h : E → ℝ}
    (hb : ∀ x, h x ≤ α + β * |S.pair x S.ample|) : ¬ RiemannInequality S κ χ₀ h := by
  intro hRI
  set k := S.pair κ S.ample
  obtain ⟨n, hn1, hn2⟩ := ((hilbertSamuel_of_riemannInequality S hRI
    (by norm_num : (1 / 2 : ℝ) < 1)).and (eventually_affine_lt_quadratic
      (by norm_num : (0 : ℝ) < 1 / 2) (4 * |β|) (2 * α + |β| * |k|))).exists
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have e1 : S.pair ((n : ℝ) • S.ample) S.ample = 2 * n := by
    rw [pair_smul_ample, S.pair_ample_ample]; ring
  have e2 : S.pair (κ - (n : ℝ) • S.ample) S.ample = k - 2 * n := by
    rw [map_sub, LinearMap.sub_apply, e1]
  have b1 := hb ((n : ℝ) • S.ample)
  have b2 := hb (κ - (n : ℝ) • S.ample)
  rw [e1, abs_of_nonneg (by linarith)] at b1
  rw [e2] at b2
  have a1 : β * (2 * n) ≤ |β| * (2 * n) :=
    mul_le_mul_of_nonneg_right (le_abs_self β) (by linarith)
  have a2 : β * |k - 2 * n| ≤ |β| * (|k| + 2 * n) := by
    calc β * |k - 2 * n| ≤ |β| * |k - 2 * n| :=
          mul_le_mul_of_nonneg_right (le_abs_self β) (abs_nonneg _)
      _ ≤ |β| * (|k| + 2 * n) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg β)
          have := abs_sub_le k 0 (2 * n)
          rw [sub_zero, zero_sub, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * n)] at this
          exact this
  nlinarith [abs_nonneg β]

/-- The **theta `h⁰` of the degree**, `x ↦ h⁰(x · A)`. -/
def thetaEffectivity (x : E) : ℝ := arithH0 (S.pair x S.ample)

/-- `h⁰(t) ≤ h⁰(0) + |t|`: by Riemann–Roch and monotonicity. -/
theorem arithH0_le_add_abs (t : ℝ) : arithH0 t ≤ arithH0 0 + |t| := by
  rcases le_total 0 t with ht | ht
  · have hRR := arithH0_riemannRoch t
    have hm : arithH0 (-t) ≤ arithH0 0 := arithH0_strictMono.monotone (by linarith)
    rw [abs_of_nonneg ht]
    linarith
  · have hm : arithH0 t ≤ arithH0 0 := arithH0_strictMono.monotone ht
    linarith [abs_nonneg t]

/-- **The linear laws of the base hold on every polar surface**: positivity, the linear
Riemann–Roch `h(x) − h(−x) = x · A`, constancy on degree levels, vanishing in very negative
degree. -/
theorem thetaEffectivity_linear_laws :
    (∀ x, 0 < thetaEffectivity S x) ∧
      (∀ x, thetaEffectivity S x - thetaEffectivity S (-x) = S.pair x S.ample) ∧
      DegreeBounded S (thetaEffectivity S) ∧
      (∀ x, 0 < S.pair x S.ample →
        Tendsto (fun t : ℝ => thetaEffectivity S (t • x)) atBot (𝓝 0)) := by
  refine ⟨fun x => arithH0_pos _, fun x => ?_, fun t => ⟨arithH0 t, fun x hx => ?_⟩, fun x hx => ?_⟩
  · simp only [thetaEffectivity, map_neg, LinearMap.neg_apply]
    exact arithH0_riemannRoch _
  · rw [thetaEffectivity, hx]
  · simp only [thetaEffectivity, pair_smul_ample]
    exact tendsto_arithH0_atBot.comp (tendsto_id.atBot_mul_const hx)

/-- **The base does not extend.** The theta `h⁰` of the degree satisfies the quadratic Riemann
inequality on no polar surface. -/
theorem thetaEffectivity_not_riemannInequality (κ : E) (χ₀ : ℝ) :
    ¬ RiemannInequality S κ χ₀ (thetaEffectivity S) :=
  not_riemannInequality_of_affine_bound S (α := arithH0 0) (β := 1) fun x => by
    rw [one_mul]
    exact arithH0_le_add_abs (S.pair x S.ample)

/-- **Effectivity functions of the degree.** With `κ = aH + bV`, a function of the degree alone
satisfies the Riemann inequality iff the Hodge index holds; then the level bound is one. -/
theorem exists_degree_effectivity_iff_hodgeIndex (a b χ₀ : ℝ) :
    (∃ g : ℝ → ℝ, RiemannInequality S (a • S.H + b • S.V) χ₀ (fun x => g (S.pair x S.ample))) ↔
      S.HodgeIndex := by
  constructor
  · rintro ⟨g, hg⟩
    exact hodgeIndex_of_riemannInequality S hg (degreeZeroSubquadratic_of_degreeBounded S
      fun t => ⟨g t, fun x hx => (congrArg g hx).le⟩)
  · intro hH
    refine ⟨fun t => max 0 (levelBound a b χ₀ t), fun x => ?_⟩
    exact (le_max_of_le_right (eulerChar_le_levelBound S hH a b χ₀ rfl)).trans
      (le_add_of_nonneg_right (le_max_left _ _))

/-- A function of the degree with the Riemann inequality grows quadratically:
`g(2n) + g(κ · A − 2n) ≥ c n²` eventually, for every `c < 1`. -/
theorem degree_effectivity_quadratic {κ : E} {χ₀ : ℝ} {g : ℝ → ℝ}
    (hg : RiemannInequality S κ χ₀ (fun x => g (S.pair x S.ample))) {c : ℝ} (hc : c < 1) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ 2 ≤ g (2 * n) + g (S.pair κ S.ample - 2 * n) := by
  filter_upwards [hilbertSamuel_of_riemannInequality S hg hc] with n hn
  have e1 : S.pair ((n : ℝ) • S.ample) S.ample = 2 * n := by
    rw [pair_smul_ample, S.pair_ample_ample]; ring
  have e2 : S.pair (κ - (n : ℝ) • S.ample) S.ample = S.pair κ S.ample - 2 * n := by
    rw [map_sub, LinearMap.sub_apply, e1]
  simpa only [e1, e2] using hn

/-- **On the scaling surface of `ℤ`** the theta `h⁰` of the degree obeys every linear law and
fails the quadratic Riemann inequality, independently of RH. -/
theorem scalingSurface_thetaEffectivity (κ : ScalingCycle) (χ₀ : ℝ) :
    (∀ x, thetaEffectivity scalingSurface x - thetaEffectivity scalingSurface (-x) =
      scalingSurface.pair x scalingSurface.ample) ∧
      ¬ RiemannInequality scalingSurface κ χ₀ (thetaEffectivity scalingSurface) :=
  ⟨(thetaEffectivity_linear_laws scalingSurface).2.1,
    thetaEffectivity_not_riemannInequality scalingSurface κ χ₀⟩

end GaloisForLFunctions.ArithmeticEffectivityTheory
