import GaloisForLFunctions.LatticeSectionTheory.TheSiegelMajorantIsTheHodgeIndex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The boost transform restores the Euler product

At a fixed boost `u` the split plane is the rectangular lattice with form
`P_u(m, n) = e^{2u} m² + e^{−2u} n²`, and its Epstein function can have zeros off the line
(`TheSiegelMajorantIsTheHodgeIndex`). The scaling flow moves `u`. Averaging the positive-cone
Epstein series of the majorants against the characters `e^{2wu}` of the flow,

    Z⁺(s, u) = Σ_{m,n ≥ 1} (e^{2u} m² + e^{−2u} n²)^{−s},

gives (`integral_splitSeries_mul_exp`)

    ∫_ℝ Z⁺(s, u) e^{2wu} du = K(s, w) · ζ(s + w) · ζ(s − w),      |w| < s − 1,

with the archimedean constant `K(s, w) = ∫_ℝ (e^{2v} + e^{−2v})^{−s} e^{2wv} dv > 0`.

* **Mechanism.** Each term `(m² e^{2u} + n² e^{−2u})^{−s} e^{2wu}` is a translate, by
  `½ log(n/m)`, of the single kernel `(e^{2v} + e^{−2v})^{−s} e^{2wv}`, times
  `m^{−(s+w)} n^{−(s−w)}`. The integral over the flow forgets the translation and keeps the
  Dirichlet coefficients: the lattice factorizes into its two isotropic lines.
* **Selection.** A fixed boost is a definite lattice and may be a fake; the boost-equivariant part
  of the split count is the product of two copies of `ζ`, with its Euler product.
* **Hecke.** Translating the boost by `c` multiplies the transform by `e^{−2wc}`
  (`integral_boost_translate`); for the index-`p` boost `c = ½ log p` this is `p^{−w}`.
-/

noncomputable section

open Real MeasureTheory Filter

namespace GaloisForLFunctions.LatticeSectionTheory

/-! ### The boost kernel -/

/-- The boost kernel `g_{s,w}(v) = (e^{2v} + e^{−2v})^{−s} e^{2wv}`. -/
def boostKernel (s w v : ℝ) : ℝ :=
  (Real.exp (2 * v) + Real.exp (-(2 * v))) ^ (-s) * Real.exp (2 * w * v)

theorem boostKernel_pos (s w v : ℝ) : 0 < boostKernel s w v :=
  mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

theorem continuous_boostKernel (s w : ℝ) : Continuous (boostKernel s w) := by
  unfold boostKernel
  refine Continuous.mul ?_ (by fun_prop)
  exact Continuous.rpow_const (by fun_prop) fun v => Or.inl (by positivity)

/-- The kernel decays like `e^{−2(s − |w|)|v|}`. -/
theorem boostKernel_le {s : ℝ} (hs : 0 ≤ s) (w v : ℝ) :
    boostKernel s w v ≤ Real.exp (-(2 * (s - |w|)) * |v|) := by
  have hbase : Real.exp (2 * |v|) ≤ Real.exp (2 * v) + Real.exp (-(2 * v)) := by
    rcases le_total 0 v with h | h
    · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-(2 * v))]
    · rw [abs_of_nonpos h, show 2 * -v = -(2 * v) by ring]; linarith [Real.exp_pos (2 * v)]
  have h1 : (Real.exp (2 * v) + Real.exp (-(2 * v))) ^ (-s) ≤ Real.exp (2 * |v|) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hbase (by linarith)
  rw [← Real.exp_mul] at h1
  have h2 : Real.exp (2 * w * v) ≤ Real.exp (2 * |w| * |v|) := by
    rw [Real.exp_le_exp]
    have := le_abs_self (w * v)
    rw [abs_mul] at this
    linarith
  calc boostKernel s w v ≤ Real.exp (2 * |v| * -s) * Real.exp (2 * |w| * |v|) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (-(2 * (s - |w|)) * |v|) := by rw [← Real.exp_add]; congr 1; ring

/-- `e^{−c|v|} ≤ min(1, c²/2)⁻¹ (1 + v²)⁻¹`. -/
theorem exp_neg_mul_abs_le {c : ℝ} (hc : 0 < c) (v : ℝ) :
    Real.exp (-c * |v|) ≤ (min 1 (c ^ 2 / 2))⁻¹ * (1 + v ^ 2)⁻¹ := by
  set m := min 1 (c ^ 2 / 2)
  have hm : 0 < m := lt_min one_pos (by positivity)
  have hq := Real.quadratic_le_exp_of_nonneg (mul_nonneg hc.le (abs_nonneg v))
  have hlow : m * (1 + v ^ 2) ≤ Real.exp (c * |v|) := by
    have hv2 : (c * |v|) ^ 2 = c ^ 2 * v ^ 2 := by rw [mul_pow, sq_abs]
    have a1 : m ≤ 1 := min_le_left _ _
    have a2 : m ≤ c ^ 2 / 2 := min_le_right _ _
    have : m * v ^ 2 ≤ c ^ 2 / 2 * v ^ 2 := mul_le_mul_of_nonneg_right a2 (sq_nonneg v)
    nlinarith [mul_nonneg hc.le (abs_nonneg v)]
  rw [neg_mul, Real.exp_neg, ← mul_inv]
  exact inv_anti₀ (by positivity) hlow

theorem integrable_boostKernel {s w : ℝ} (hw : |w| < s) : Integrable (boostKernel s w) := by
  have hc : 0 < 2 * (s - |w|) := by linarith
  refine (integrable_inv_one_add_sq.const_mul (min 1 ((2 * (s - |w|)) ^ 2 / 2))⁻¹).mono'
    (continuous_boostKernel s w).aestronglyMeasurable (ae_of_all _ fun v => ?_)
  rw [Real.norm_of_nonneg (boostKernel_pos s w v).le]
  exact (boostKernel_le (by linarith [abs_nonneg w]) w v).trans (exp_neg_mul_abs_le hc v)

/-- **The archimedean constant** `K(s, w) = ∫ (e^{2v} + e^{−2v})^{−s} e^{2wv} dv`. -/
def boostConstant (s w : ℝ) : ℝ := ∫ v, boostKernel s w v

theorem boostConstant_pos {s w : ℝ} (hw : |w| < s) : 0 < boostConstant s w := by
  rw [boostConstant, integral_pos_iff_support_of_nonneg (fun v => (boostKernel_pos s w v).le)
    (integrable_boostKernel hw)]
  have : Function.support (boostKernel s w) = Set.univ :=
    Set.eq_univ_of_forall fun v => (boostKernel_pos s w v).ne'
  rw [this]; simp

/-! ### One term of the split series -/

/-- **One split term is a translated kernel.** For `A = e^α`, `B = e^β`:
`(A e^{2u} + B e^{−2u})^{−s} e^{2wu} = e^{−s(α+β)/2 + w(β−α)/2} g_{s,w}(u − (β − α)/4)`. -/
theorem splitTerm_eq (α β s w u : ℝ) :
    (Real.exp α * Real.exp (2 * u) + Real.exp β * Real.exp (-(2 * u))) ^ (-s) *
        Real.exp (2 * w * u) =
      Real.exp (-s * (α + β) / 2 + w * (β - α) / 2) * boostKernel s w (u - (β - α) / 4) := by
  set v := u - (β - α) / 4
  have e1 : Real.exp α * Real.exp (2 * u) = Real.exp ((α + β) / 2) * Real.exp (2 * v) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; simp only [v]; ring
  have e2 : Real.exp β * Real.exp (-(2 * u)) = Real.exp ((α + β) / 2) * Real.exp (-(2 * v)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; simp only [v]; ring
  rw [e1, e2, ← mul_add, Real.mul_rpow (Real.exp_pos _).le (by positivity), ← Real.exp_mul,
    boostKernel]
  have e3 : Real.exp (2 * w * u) = Real.exp (w * (β - α) / 2) * Real.exp (2 * w * v) := by
    rw [← Real.exp_add]; congr 1; simp only [v]; ring
  rw [e3]
  have e4 : Real.exp ((α + β) / 2 * -s) = Real.exp (-s * (α + β) / 2) := by congr 1; ring
  rw [e4, show -s * (α + β) / 2 + w * (β - α) / 2 = -s * (α + β) / 2 + w * (β - α) / 2 from rfl,
    Real.exp_add]
  ring

/-- The `(m, n)` term of the split series at boost `u`, with `m, n ≥ 1` written `m + 1, n + 1`. -/
def splitTerm (s u : ℝ) (i : ℕ × ℕ) : ℝ :=
  (((i.1 : ℝ) + 1) ^ 2 * Real.exp (2 * u) + ((i.2 : ℝ) + 1) ^ 2 * Real.exp (-(2 * u))) ^ (-s)

/-- The Dirichlet coefficient `m^{−(s+w)} n^{−(s−w)}`. -/
def splitCoeff (s w : ℝ) (i : ℕ × ℕ) : ℝ :=
  ((i.1 : ℝ) + 1) ^ (-(s + w)) * ((i.2 : ℝ) + 1) ^ (-(s - w))

theorem splitTerm_mul_exp (s w u : ℝ) (i : ℕ × ℕ) :
    splitTerm s u i * Real.exp (2 * w * u) =
      splitCoeff s w i * boostKernel s w
        (u - (2 * Real.log ((i.2 : ℝ) + 1) - 2 * Real.log ((i.1 : ℝ) + 1)) / 4) := by
  have hm : (0 : ℝ) < (i.1 : ℝ) + 1 := by positivity
  have hn : (0 : ℝ) < (i.2 : ℝ) + 1 := by positivity
  have hA : ((i.1 : ℝ) + 1) ^ 2 = Real.exp (2 * Real.log ((i.1 : ℝ) + 1)) := by
    rw [show 2 * Real.log ((i.1 : ℝ) + 1) = Real.log (((i.1 : ℝ) + 1) ^ 2) by
      rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]
  have hB : ((i.2 : ℝ) + 1) ^ 2 = Real.exp (2 * Real.log ((i.2 : ℝ) + 1)) := by
    rw [show 2 * Real.log ((i.2 : ℝ) + 1) = Real.log (((i.2 : ℝ) + 1) ^ 2) by
      rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]
  rw [splitTerm, hA, hB, splitTerm_eq, splitCoeff, Real.rpow_def_of_pos hm,
    Real.rpow_def_of_pos hn, ← Real.exp_add]
  congr 2
  ring

/-- **The integral of one split term**: `∫ term · e^{2wu} du = m^{−(s+w)} n^{−(s−w)} K(s, w)`. -/
theorem integral_splitTerm_mul_exp (s w : ℝ) (i : ℕ × ℕ) :
    ∫ u, splitTerm s u i * Real.exp (2 * w * u) = splitCoeff s w i * boostConstant s w := by
  simp_rw [splitTerm_mul_exp]
  rw [integral_const_mul, MeasureTheory.integral_sub_right_eq_self (boostKernel s w), boostConstant]

theorem integrable_splitTerm_mul_exp {s w : ℝ} (hw : |w| < s) (i : ℕ × ℕ) :
    Integrable fun u => splitTerm s u i * Real.exp (2 * w * u) := by
  simp_rw [splitTerm_mul_exp]
  exact ((integrable_boostKernel hw).comp_sub_right _).const_mul _

theorem splitCoeff_nonneg (s w : ℝ) (i : ℕ × ℕ) : 0 ≤ splitCoeff s w i :=
  mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)

theorem summable_nat_add_one_rpow {a : ℝ} (ha : 1 < a) :
    Summable fun m : ℕ => ((m : ℝ) + 1) ^ (-a) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 a).mpr ha
  refine h.congr fun m => ?_
  rw [abs_of_pos (by positivity), Real.rpow_neg (by positivity), one_div]

theorem summable_splitCoeff {s w : ℝ} (hw : |w| < s - 1) : Summable (splitCoeff s w) := by
  have h1 : 1 < s + w := by linarith [neg_abs_le w]
  have h2 : 1 < s - w := by linarith [le_abs_self w]
  exact (summable_nat_add_one_rpow h1).mul_of_nonneg (summable_nat_add_one_rpow h2)
    (fun _ => Real.rpow_nonneg (by positivity) _) (fun _ => Real.rpow_nonneg (by positivity) _)

/-! ### The boost transform -/

/-- **The positive-cone Epstein series of the split plane at boost `u`**:
`Z⁺(s, u) = Σ_{m,n ≥ 1} (e^{2u} m² + e^{−2u} n²)^{−s}`. -/
def splitSeries (s u : ℝ) : ℝ := ∑' i : ℕ × ℕ, splitTerm s u i

/-- **The boost transform restores the Euler product.** For `|w| < s − 1`,
`∫ Z⁺(s, u) e^{2wu} du = K(s, w) · Σ_m m^{−(s+w)} · Σ_n n^{−(s−w)}`. -/
theorem integral_splitSeries_mul_exp {s w : ℝ} (hw : |w| < s - 1) :
    ∫ u, splitSeries s u * Real.exp (2 * w * u) =
      boostConstant s w * ((∑' m : ℕ, ((m : ℝ) + 1) ^ (-(s + w))) *
        ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(s - w))) := by
  have hw' : |w| < s := by linarith
  have hint := integrable_splitTerm_mul_exp hw'
  have hnorm : Summable fun i : ℕ × ℕ => ∫ u, ‖splitTerm s u i * Real.exp (2 * w * u)‖ := by
    refine ((summable_splitCoeff hw).mul_right (boostConstant s w)).congr fun i => ?_
    rw [← integral_splitTerm_mul_exp]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    exact (Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.exp_pos _).le)).symm
  have hswap := integral_tsum_of_summable_integral_norm hint hnorm
  have hlhs : (fun u => splitSeries s u * Real.exp (2 * w * u)) =
      fun u => ∑' i : ℕ × ℕ, splitTerm s u i * Real.exp (2 * w * u) := by
    funext u; rw [splitSeries, tsum_mul_right]
  rw [hlhs, ← hswap]
  simp_rw [integral_splitTerm_mul_exp]
  rw [tsum_mul_right, mul_comm]
  congr 1
  have h1 : 1 < s + w := by linarith [neg_abs_le w]
  have h2 : 1 < s - w := by linarith [le_abs_self w]
  rw [tsum_mul_tsum_of_summable_norm]
  · rfl
  · exact summable_norm_iff.mpr (summable_nat_add_one_rpow h1)
  · exact summable_norm_iff.mpr (summable_nat_add_one_rpow h2)

/-- The real `p`-series is the Riemann zeta function. -/
theorem riemannZeta_ofReal_eq_tsum {a : ℝ} (ha : 1 < a) :
    riemannZeta (a : ℂ) = ((∑' m : ℕ, ((m : ℝ) + 1) ^ (-a) : ℝ) : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using ha), Complex.ofReal_tsum]
  refine tsum_congr fun m => ?_
  rw [Complex.ofReal_cpow (by positivity)]
  push_cast
  rw [Complex.cpow_neg, one_div]

/-- **Selection by the boosts.** The boost transform of the split counts is the archimedean
constant times `ζ(s + w) ζ(s − w)`. -/
theorem integral_splitSeries_mul_exp_eq_zeta {s w : ℝ} (hw : |w| < s - 1) :
    ((∫ u, splitSeries s u * Real.exp (2 * w * u) : ℝ) : ℂ) =
      (boostConstant s w : ℂ) * riemannZeta ((s + w : ℝ) : ℂ) * riemannZeta ((s - w : ℝ) : ℂ) := by
  have h1 : 1 < s + w := by linarith [neg_abs_le w]
  have h2 : 1 < s - w := by linarith [le_abs_self w]
  rw [integral_splitSeries_mul_exp hw, riemannZeta_ofReal_eq_tsum h1,
    riemannZeta_ofReal_eq_tsum h2]
  push_cast
  ring

/-- **Hecke acts on the boost transform by a character.** Translating the boost by `c` multiplies
the transform by `e^{−2wc}`; for the index-`p` boost `c = ½ log p` this is `p^{−w}`. -/
theorem integral_boost_translate (F : ℝ → ℝ) (w c : ℝ) :
    ∫ u, F (u + c) * Real.exp (2 * w * u) =
      Real.exp (-(2 * w * c)) * ∫ u, F u * Real.exp (2 * w * u) := by
  have h : (fun u => F (u + c) * Real.exp (2 * w * u)) =
      fun u => Real.exp (-(2 * w * c)) * (fun v => F v * Real.exp (2 * w * v)) (u + c) := by
    funext u
    have e : Real.exp (-(2 * w * c)) * Real.exp (2 * w * (u + c)) = Real.exp (2 * w * u) := by
      rw [← Real.exp_add]; congr 1; ring
    simp only
    rw [← e]
    ring
  rw [h, integral_const_mul, MeasureTheory.integral_add_right_eq_self
    (fun v => F v * Real.exp (2 * w * v))]

end GaloisForLFunctions.LatticeSectionTheory
