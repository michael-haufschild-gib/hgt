import GaloisForLFunctions.ArithmeticEffectivityTheory.TheBaseDoesNotExtend
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheProjectiveSquareCalibration

/-!
# The Künneth Riemann–Roch of a polar surface

The base `Spec ℤ` has the theta count `h⁰_ℤ(d) = log Σ_n e^{−π n² e^{−2d}}` with the exact
Riemann–Roch `h⁰_ℤ(d) − h⁰_ℤ(−d) = d` (Poisson summation): canonical degree `0`, Euler
characteristic `χ_ℤ(d) = d`. Its tensor square is the **Künneth count** of a polar surface,

    h_K(x) = h⁰_ℤ(x · H) · h⁰_ℤ(x · V),

the real dimension of a tensor product of the two fibre section spaces.

* **Künneth Riemann–Roch** (`kunnethH0_add_neg`). With `κ = 0`, `χ₀ = 0`, so `χ(x) = ½ x²` (the
  Riemann–Roch of an abelian surface),

      h_K(x) + h_K(−x) = ½ x² + h¹_K(x) + ½ δ(x, x),
      h¹_K(x) = h⁰_ℤ(x·H) h⁰_ℤ(−x·V) + h⁰_ℤ(−x·H) h⁰_ℤ(x·V) > 0.

  The `h¹` of the count splits into a **Künneth part**, positive because counts are positive,
  and a **primitive part**, half of the Castelnuovo–Severi defect. The base Riemann–Roch pays the
  whole quadratic Euler characteristic of the pole plane; nothing pays the primitive part.
* **Effectivity is the Hodge index** (`riemannInequality_kunnethH0_iff`,
  `kunnethH0_degreeBounded`). The Künneth count is bounded on degree levels on every polar surface
  (the base count decays like `exp(−π e^{−2d})` in negative degree, `arithH0_le_of_nonpos`), and it
  satisfies the Riemann inequality iff the Hodge index holds. On the hyperbolic plane `⟨H, V⟩` it
  is an effectivity unconditionally (`hyperbolicPlane_kunneth_effectivity`); on the scaling surface
  of `ℤ`, iff RH (`riemannHypothesis_iff_kunneth_effectivity`).

So Serre duality on the pole plane is the product of two one-dimensional Poisson summations, and
the sign problem is exactly the nonnegativity of the primitive `h¹`.
-/

noncomputable section

open Real

namespace GaloisForLFunctions.LatticeSectionTheory

open ArithmeticCastelnuovoSeveri ArithmeticEffectivityTheory ArithmeticOrientationGeometry

/-! ### The base count in negative degree -/

/-- The Gaussian lattice count decays exponentially above height one: `θ(u) − 1 ≤ 4 e^{−πu}`. -/
theorem thetaSum_sub_one_le {u : ℝ} (hu : 1 ≤ u) : thetaSum u - 1 ≤ 4 * Real.exp (-π * u) := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hJ : ((thetaSum u : ℝ) : ℂ) = jacobiTheta ((u : ℂ) * Complex.I) := by
    rw [thetaSum, Complex.ofReal_tsum, jacobiTheta]
    refine tsum_congr fun n => ?_
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hle := norm_jacobiTheta_sub_one_le (τ := (u : ℂ) * Complex.I) (by simpa using hu0)
  have him : ((u : ℂ) * Complex.I).im = u := by simp
  rw [him, ← hJ, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at hle
  have hexp : Real.exp (-π * u) ≤ Real.exp (-π) := by
    rw [Real.exp_le_exp]; nlinarith [Real.pi_pos]
  have hpi : Real.exp (-π) < 1 / 2 := by
    have h1 := Real.add_one_le_exp π
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith [Real.pi_gt_three]
  have hden : 1 / 2 ≤ 1 - Real.exp (-π * u) := by linarith
  have hcoef : 2 / (1 - Real.exp (-π * u)) ≤ 4 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  calc thetaSum u - 1 ≤ |thetaSum u - 1| := le_abs_self _
    _ ≤ 2 / (1 - Real.exp (-π * u)) * Real.exp (-π * u) := hle
    _ ≤ 4 * Real.exp (-π * u) := mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le

/-- **Superexponential vanishing in negative degree**: `(1 − d) h⁰_ℤ(d) ≤ 4` for `d ≤ 0`. -/
theorem arithH0_le_of_nonpos {d : ℝ} (hd : d ≤ 0) : (1 - d) * arithH0 d ≤ 4 := by
  set u := Real.exp (-2 * d) with hu_def
  have hu1 : 1 + -2 * d ≤ u := by rw [hu_def]; linarith [Real.add_one_le_exp (-2 * d)]
  have hu : 1 ≤ u := by linarith
  have hlog : arithH0 d ≤ thetaSum u - 1 :=
    (Real.log_le_sub_one_of_pos (thetaSum_pos (by linarith))).trans le_rfl
  have hθ := thetaSum_sub_one_le hu
  have hexp : Real.exp (-π * u) ≤ Real.exp (-(1 - d)) := by
    rw [Real.exp_le_exp]; nlinarith [Real.pi_gt_three]
  have hdecay : (1 - d) * Real.exp (-(1 - d)) ≤ 1 := by
    have := Real.add_one_le_exp (1 - d)
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    linarith
  have hpos := arithH0_pos d
  calc (1 - d) * arithH0 d ≤ (1 - d) * (4 * Real.exp (-(1 - d))) :=
        mul_le_mul_of_nonneg_left (hlog.trans (hθ.trans (by nlinarith [Real.exp_pos (-π * u)])))
          (by linarith)
    _ = 4 * ((1 - d) * Real.exp (-(1 - d))) := by ring
    _ ≤ 4 := by linarith

/-- The base count is at most `h⁰_ℤ(0) + max(d, 0)`. -/
theorem arithH0_le_zero_add_pos (d : ℝ) : arithH0 d ≤ arithH0 0 + max d 0 := by
  rcases le_total 0 d with hd | hd
  · rw [max_eq_left hd]; simpa [abs_of_nonneg hd] using arithH0_le_add_abs d
  · rw [max_eq_right hd]; linarith [arithH0_strictMono.monotone hd]

/-! ### The Künneth count -/

section Kunneth

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (S : PolarSurface E)

/-- **The Künneth count** `h_K(x) = h⁰_ℤ(x·H) h⁰_ℤ(x·V)`: the tensor square of the base. -/
def kunnethH0 (x : E) : ℝ := arithH0 (S.pair x S.H) * arithH0 (S.pair x S.V)

/-- **The Künneth `h¹`**: `H⁰ ⊗ H¹ ⊕ H¹ ⊗ H⁰`, with the base `h¹(d) = h⁰_ℤ(−d)` (canonical
degree `0`). -/
def kunnethH1 (x : E) : ℝ :=
  arithH0 (S.pair x S.H) * arithH0 (-S.pair x S.V) + arithH0 (-S.pair x S.H) * arithH0 (S.pair x S.V)

theorem kunnethH0_pos (x : E) : 0 < kunnethH0 S x :=
  mul_pos (arithH0_pos _) (arithH0_pos _)

theorem kunnethH1_pos (x : E) : 0 < kunnethH1 S x :=
  add_pos (mul_pos (arithH0_pos _) (arithH0_pos _)) (mul_pos (arithH0_pos _) (arithH0_pos _))

/-- **Künneth identity of the base**: `h(a)h(b) + h(−a)h(−b) = ab + h(a)h(−b) + h(−a)h(b)`.
Only the base Riemann–Roch `h(d) = d + h(−d)` is used. -/
theorem arithH0_kunneth (a b : ℝ) :
    arithH0 a * arithH0 b + arithH0 (-a) * arithH0 (-b) =
      a * b + (arithH0 a * arithH0 (-b) + arithH0 (-a) * arithH0 b) := by
  have ha := arithH0_riemannRoch a
  have hb := arithH0_riemannRoch b
  have ha' : arithH0 a = a + arithH0 (-a) := by linarith
  have hb' : arithH0 b = b + arithH0 (-b) := by linarith
  rw [ha', hb']
  ring

/-- **Künneth Riemann–Roch.** `h_K(x) + h_K(−x) = χ(x) + h¹_K(x) + ½ δ(x, x)` with `κ = 0`,
`χ₀ = 0`: the `h¹` of the count is the Künneth `h¹` plus half of the Castelnuovo–Severi defect. -/
theorem kunnethH0_add_neg (x : E) :
    kunnethH0 S x + kunnethH0 S (0 - x) =
      eulerChar S 0 0 x + kunnethH1 S x + S.defect x x / 2 := by
  have hK := arithH0_kunneth (S.pair x S.H) (S.pair x S.V)
  simp only [kunnethH0, kunnethH1, eulerChar, zero_sub, map_neg, LinearMap.neg_apply, sub_zero,
    add_zero, S.defect_self] at hK ⊢
  linarith

/-- **The primitive `h¹`**: with `h¹ := h⁰ + h² − χ`, the part of `h¹` beyond the Künneth part is
`½ δ(x, x)`. -/
theorem kunneth_h1_sub_eq_half_defect (x : E) :
    kunnethH0 S x + kunnethH0 S (0 - x) - eulerChar S 0 0 x - kunnethH1 S x = S.defect x x / 2 := by
  rw [kunnethH0_add_neg]; ring

/-- **The Künneth count satisfies the Riemann inequality iff the Hodge index holds.** -/
theorem riemannInequality_kunnethH0_iff :
    RiemannInequality S 0 0 (kunnethH0 S) ↔ S.HodgeIndex := by
  constructor
  · intro hRI x hH hV
    by_contra hpos
    push Not at hpos
    set c := arithH0 0
    -- along `t • x` the count is constant while `χ` grows like `t²`
    set t : ℝ := Real.sqrt ((4 * c ^ 2 + 1) / S.pair x x)
    have ht : t ^ 2 = (4 * c ^ 2 + 1) / S.pair x x :=
      Real.sq_sqrt (div_nonneg (by positivity) hpos.le)
    have h := hRI (t • x)
    simp only [kunnethH0, eulerChar, zero_sub, map_neg, map_smul, LinearMap.neg_apply,
      LinearMap.smul_apply, smul_eq_mul, hH, hV, mul_zero, neg_zero, sub_zero, add_zero] at h
    have hq : t ^ 2 * S.pair x x = 4 * c ^ 2 + 1 := by
      rw [ht, div_mul_cancel₀ _ hpos.ne']
    nlinarith
  · intro hHI x
    have hδ := (S.castelnuovoSeveri_iff_defect_nonneg.mp
      (S.hodgeIndex_iff_castelnuovoSeveri.mp hHI)) x
    have := kunnethH0_add_neg S x
    linarith [kunnethH1_pos S x]

/-- **The Künneth count is bounded on degree levels**, on every polar surface: on `x·A = t` it is
at most `(h⁰_ℤ(0) + |t| + 2)²`. -/
theorem kunnethH0_degreeBounded : DegreeBounded S (kunnethH0 S) := by
  intro t
  set c := arithH0 0
  have hc : 0 < c := arithH0_pos 0
  refine ⟨(c + |t| + 2) ^ 2, fun x hx => ?_⟩
  rw [S.pair_ample] at hx
  set a := S.pair x S.H
  set b := S.pair x S.V
  have key : ∀ a b : ℝ, a + b = t → b ≤ a → arithH0 a * arithH0 b ≤ (c + |t| + 2) ^ 2 := by
    intro a b hab hba
    have hapos := arithH0_pos a
    have hbpos := arithH0_pos b
    have hta := arithH0_le_zero_add_pos a
    rcases le_or_gt 0 b with hb | hb
    · have hb' : b ≤ |t| := by rw [abs_of_nonneg (by linarith)]; linarith
      have ha' : a ≤ |t| := by rw [abs_of_nonneg (by linarith)]; linarith
      have h1 : arithH0 a ≤ c + |t| := by
        have := arithH0_le_zero_add_pos a; rw [max_eq_left (by linarith)] at this; linarith
      have h2 : arithH0 b ≤ c + |t| := by
        have := arithH0_le_zero_add_pos b; rw [max_eq_left hb] at this; linarith
      nlinarith
    · have hdec := arithH0_le_of_nonpos hb.le
      have hb4 : arithH0 b ≤ 4 := by nlinarith
      have hbb : -b * arithH0 b ≤ 4 := by nlinarith
      have ha_le : arithH0 a ≤ c + |t| + -b := by
        have : max a 0 ≤ |t| + -b := by
          rw [max_le_iff]; constructor <;> [linarith [le_abs_self t]; linarith [abs_nonneg t]]
        linarith
      have ht0 : 0 ≤ |t| := abs_nonneg t
      calc arithH0 a * arithH0 b ≤ (c + |t| + -b) * arithH0 b :=
            mul_le_mul_of_nonneg_right ha_le hbpos.le
        _ = (c + |t|) * arithH0 b + -b * arithH0 b := by ring
        _ ≤ (c + |t|) * 4 + 4 := by nlinarith
        _ ≤ (c + |t| + 2) ^ 2 := by nlinarith
  rcases le_total b a with hba | hab
  · exact key a b hx hba
  · have := key b a (by linarith) hab
    simpa only [kunnethH0, mul_comm] using this

/-- **Effectivity of the Künneth count is the Hodge index**: it satisfies the Riemann inequality
and is bounded on degree levels iff the Hodge index holds. -/
theorem kunneth_effectivity_iff :
    (RiemannInequality S 0 0 (kunnethH0 S) ∧ DegreeBounded S (kunnethH0 S)) ↔ S.HodgeIndex :=
  ⟨fun h => (riemannInequality_kunnethH0_iff S).mp h.1,
    fun h => ⟨(riemannInequality_kunnethH0_iff S).mpr h, kunnethH0_degreeBounded S⟩⟩

end Kunneth

/-! ### Calibration -/

/-- **The pole plane.** On the hyperbolic plane `⟨H, V⟩` the Künneth count is an effectivity
function unconditionally: its `h¹` is the Künneth part alone. -/
theorem hyperbolicPlane_kunneth_effectivity :
    RiemannInequality hyperbolicPlane 0 0 (kunnethH0 hyperbolicPlane) ∧
      DegreeBounded hyperbolicPlane (kunnethH0 hyperbolicPlane) :=
  (kunneth_effectivity_iff hyperbolicPlane).mpr hyperbolicPlane_hodgeIndex

/-- **The scaling surface of `ℤ`.** The Künneth count is an effectivity function iff RH. -/
theorem riemannHypothesis_iff_kunneth_effectivity :
    RiemannHypothesis ↔
      RiemannInequality scalingSurface 0 0 (kunnethH0 scalingSurface) ∧
        DegreeBounded scalingSurface (kunnethH0 scalingSurface) :=
  scalingSurface_hodgeIndex_iff.symm.trans (kunneth_effectivity_iff scalingSurface).symm

end GaloisForLFunctions.LatticeSectionTheory
