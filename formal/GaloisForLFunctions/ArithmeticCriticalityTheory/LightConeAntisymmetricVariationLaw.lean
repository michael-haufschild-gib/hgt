import GaloisForLFunctions.ArithmeticCriticalityTheory.ArchimedeanZTypeLaw
import GaloisForLFunctions.ArithmeticCriticalityTheory.ParityFoldedCurvedGaugeWeilPositivity
import GaloisForLFunctions.ArithmeticCriticalityTheory.ZeroFormJumpKernelGaugeFreedom

/-!
# The antisymmetric light-cone Weil jump law in odd shifted-ground-state coordinates

In an even curved gauge `M`, parity folding across the origin sums the Weil jump density
`κ(r) = ω_arch(r) − 2 cosh(r/2)` at `s` and `s + 2x`, producing the folded conductance
`κ(s) + κ(s + 2x)` which turns negative past the plastic fold boundary `x + s ≈ 0.2812`.

In an odd shifted ground state `ω_a` (`a > 0`), with test `m_a u = Φ(ω_a u)` and half-line pole
measure `μ_a(x) = m_a(x) sinh(x/2)` of mass `sinh(a/2)/2`, the profile variance folds onto ordered
positive pairs `0 < x < x + s` via the hyperbolic identity
`2 cosh((s + 2x)/2) − 2 cosh(s/2) = 4 sinh(x/2) sinh((x + s)/2)`:

    V_a(u) = 8 ∫_{x>0} ∫_{s>0} sinh(x/2) sinh((x + s)/2) J_s(x) ds dx
           = 2 ∫_{x>0} ∫_{s>0} (2 cosh((s + 2x)/2) − 2 cosh(s/2)) J_s(x) ds dx.

Combining `V_a(u)` with the Z-type archimedean surplus
`2 S_arch(ω_a, u) − D_arch(ω_a, u) = 2 ∫_{x>0} ∫_{s>0} (ω_arch(s) − ω_arch(s + 2x)) J_s(x) ds dx`
assembles the entire continuum and variance budget into the **antisymmetric** Weil jump difference:

    (2 S_arch(ω_a, u) − D_arch(ω_a, u)) + V_a(u)
      = 2 ∫_{x>0} ∫_{s>0} (κ(s) − κ(s + 2x)) J_s(x) ds dx.

Because `ω_arch` is strictly decreasing on `(0, ∞)` and `2 cosh(·/2)` is strictly increasing on
`[0, ∞)`, `κ = weilJumpDensity` is strictly decreasing on `(0, ∞)` (`strictAntiOn_weilJumpDensity`):
`κ(s) − κ(s + 2x) > 0` strictly on all of `(0, ∞)²`, with no plastic threshold and with exponential
growth `≥ 4 sinh(x/2) sinh((x + s)/2)` at large scales. Midpoint-folding the prime anti-diagonals
(`primeReflectedDifferenceEnergy_eq_two_mul_half`) gives the exact light-cone zero-form identity and
its completeness equivalence for `RiemannHypothesis`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### Strict antitonicity and hyperbolic decomposition of `weilJumpDensity` -/

/-- `cosh` is strictly increasing on `[0, ∞)`. -/
theorem strictMonoOn_cosh_Ici : StrictMonoOn Real.cosh (Ici (0 : ℝ)) := by
  intro a ha b hb hab
  have ha0 : 0 ≤ a := ha
  have h1 : 0 < Real.exp b - Real.exp a := sub_pos.mpr (Real.exp_lt_exp.mpr hab)
  have h2 : 0 < 1 - Real.exp (-(a + b)) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hid : Real.cosh b - Real.cosh a =
      (Real.exp b - Real.exp a) * (1 - Real.exp (-(a + b))) / 2 := by
    rw [Real.cosh_eq, Real.cosh_eq, show -(a + b) = -a + -b by ring, Real.exp_add]
    have ea : Real.exp a * Real.exp (-a) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have eb : Real.exp b * Real.exp (-b) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    linear_combination (Real.exp (-a) / 2) * eb - (Real.exp (-b) / 2) * ea
  linarith [div_pos (mul_pos h1 h2) two_pos]

/-- **Strict antitonicity of the Weil jump density.** On `(0, ∞)`, `ω_arch` is strictly decreasing
and `−2 cosh(·/2)` is strictly decreasing, so `κ(t) = ω_arch(t) − 2 cosh(t/2)` is strictly
decreasing across the entire positive half-line with no finite threshold. -/
theorem strictAntiOn_weilJumpDensity : StrictAntiOn weilJumpDensity (Ioi (0 : ℝ)) := by
  intro s hs t ht hst
  have hs0 : 0 < s := hs
  have hω : archLevyDensity t < archLevyDensity s := strictAntiOn_archLevyDensity hs ht hst
  have hc : Real.cosh (s / 2) < Real.cosh (t / 2) :=
    strictMonoOn_cosh_Ici (mem_Ici.mpr (by positivity)) (mem_Ici.mpr (by linarith)) (by linarith)
  unfold weilJumpDensity
  linarith

/-- Hyperbolic product-to-difference identity folding the odd pole product into `cosh` differences:
`2 cosh((s + 2x)/2) − 2 cosh(s/2) = 4 sinh(x/2) sinh((x + s)/2)`. -/
theorem two_mul_cosh_add_two_mul_sub_eq_four_mul_sinh_mul_sinh (s x : ℝ) :
    2 * Real.cosh ((s + 2 * x) / 2) - 2 * Real.cosh (s / 2) =
      4 * Real.sinh (x / 2) * Real.sinh ((x + s) / 2) := by
  rw [Real.cosh_eq, Real.cosh_eq, Real.sinh_eq, Real.sinh_eq,
    show (s + 2 * x) / 2 = x / 2 + (x / 2 + s / 2) by ring,
    show -(x / 2 + (x / 2 + s / 2)) = -(x / 2) + (-(x / 2) + -(s / 2)) by ring,
    show (x + s) / 2 = x / 2 + s / 2 by ring,
    show -(x / 2 + s / 2) = -(x / 2) + -(s / 2) by ring,
    Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add]
  have hx1 : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  linear_combination (Real.exp (s / 2) + Real.exp (-(s / 2))) * hx1

/-- Exact decomposition of the antisymmetric Weil jump kernel into the archimedean Lévy drop plus
the positive hyperbolic variance product. -/
theorem weilJumpDensity_sub_add_two_mul_eq (s x : ℝ) :
    weilJumpDensity s - weilJumpDensity (s + 2 * x) =
      (archLevyDensity s - archLevyDensity (s + 2 * x)) +
        4 * Real.sinh (x / 2) * Real.sinh ((x + s) / 2) := by
  unfold weilJumpDensity
  linarith [two_mul_cosh_add_two_mul_sub_eq_four_mul_sinh_mul_sinh s x]

/-- Pointwise strict positivity of the antisymmetric Weil jump kernel on `(0, ∞)²`. -/
theorem weilJumpDensity_sub_add_two_mul_pos {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    0 < weilJumpDensity s - weilJumpDensity (s + 2 * x) :=
  sub_pos.mpr (strictAntiOn_weilJumpDensity hs (show (0 : ℝ) < s + 2 * x by linarith)
    (by linarith))

/-- Exponential lower bound on the antisymmetric Weil jump kernel on `(0, ∞) × [0, ∞)`: discarding
the nonnegative archimedean Lévy drop retains the full hyperbolic product
`4 sinh(x/2) sinh((x + s)/2)`. -/
theorem four_mul_sinh_mul_sinh_le_weilJumpDensity_sub {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    4 * Real.sinh (x / 2) * Real.sinh ((x + s) / 2) ≤
      weilJumpDensity s - weilJumpDensity (s + 2 * x) := by
  have hω : archLevyDensity (s + 2 * x) ≤ archLevyDensity s :=
    strictAntiOn_archLevyDensity.antitoneOn hs (show (0 : ℝ) < s + 2 * x by linarith) (by linarith)
  rw [weilJumpDensity_sub_add_two_mul_eq]
  linarith

/-! ### Midpoint folding of the prime reflected difference energy -/

/-- **Midpoint folding of the prime anti-diagonals.** Every reflected prime collar `(0, log n)` is
symmetric around `(log n)/2`, so `D_prime(ω, u) = 2 ∑_n Λ(n) n^{−1/2} ∫_0^{(log n)/2} R_{log n}(x) dx`. -/
theorem primeReflectedDifferenceEnergy_eq_two_mul_half {ω u : ℝ → ℝ}
    (hω : Continuous ω) (hu : Continuous u) :
    primeReflectedDifferenceEnergy ω u =
      2 * ∑' n : ℕ, vonMangoldtAtom n *
        ∫ x in Ioo (0 : ℝ) (Real.log n / 2), reflectedDifferenceJump ω u (Real.log n) x := by
  unfold primeReflectedDifferenceEnergy
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rcases le_or_gt n 1 with hn | hn
  · have hlog : Real.log (n : ℝ) = 0 := by
      interval_cases n
      · simp
      · simp
    rw [hlog, zero_div, Ioo_self, setIntegral_empty, mul_zero, mul_zero]
  · have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    rw [integral_Ioo_reflectedDifferenceJump_eq_two_mul_half hω hu hlog]
    ring

/-! ### Double-integral representation of `profileVariance` and light-cone assembly -/

section ShiftedGroundState

variable {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}

/-- Pointwise identity relating the half-line variance integrand at `(x, x + s)` to
`sameSideGroundJump (shiftedGroundState a) u s x`. -/
theorem sinh_mul_sinh_mul_sameSideGroundJump_eq (s x : ℝ) :
    Real.sinh (x / 2) * Real.sinh ((x + s) / 2) *
        sameSideGroundJump (shiftedGroundState a) u s x =
      (u x - u (x + s)) ^ 2 *
        ((shiftDifference a x * Real.sinh (x / 2)) *
          (shiftDifference a (x + s) * Real.sinh ((x + s) / 2))) := by
  unfold sameSideGroundJump
  have hx := riemannKernelReal_mul_shiftedGroundState a x
  have hxs := riemannKernelReal_mul_shiftedGroundState a (x + s)
  linear_combination
    (Real.sinh (x / 2) * Real.sinh ((x + s) / 2) *
      (riemannKernelReal (x + s) * shiftedGroundState a (x + s)) * (u x - u (x + s)) ^ 2) * hx +
    (Real.sinh (x / 2) * Real.sinh ((x + s) / 2) * shiftDifference a x *
      (u x - u (x + s)) ^ 2) * hxs

include ha

/-- Product-measure integrability of the hyperbolic variance jump on `(0, ∞) × (0, ∞)`. -/
theorem integrable_sinh_mul_sinh_sameSideGroundJump_prod
    (hu : Continuous u) (huc : HasCompactSupport u) :
    Integrable (Function.uncurry fun x s =>
      Real.sinh (x / 2) * Real.sinh ((x + s) / 2) *
        sameSideGroundJump (shiftedGroundState a) u s x)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le_exp_sixteen
  obtain ⟨Z, hZ⟩ := huc.exists_bound_of_continuous hu
  have hZ' : ∀ y, |u y| ≤ Z := fun y => by simpa [Real.norm_eq_abs] using hZ y
  have hZ0 : 0 ≤ Z := (abs_nonneg (u 0)).trans (hZ' 0)
  set K : ℝ := C * Real.exp (16 * a)
  have hK0 : 0 ≤ K := mul_nonneg hC0 (Real.exp_pos _).le
  have hg_bound : ∀ y : ℝ, 0 ≤ y →
      shiftDifference a y * Real.sinh (y / 2) ≤ K * Real.exp (-(8 * y)) := by
    intro y hy
    have hm : shiftDifference a y ≤ K * Real.exp (-(16 * y)) := by
      refine (shiftDifference_le_kernel a y).trans ((hC _).trans ?_)
      dsimp [K]
      rw [mul_assoc, ← Real.exp_add]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [le_abs_self (y - a)])) hC0
    have hsh : Real.sinh (y / 2) ≤ Real.exp (8 * y) := by
      have := abs_sinh_half_le_exp_eight y
      rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr (by positivity)), abs_of_nonneg hy] at this
      exact this
    calc shiftDifference a y * Real.sinh (y / 2)
        ≤ (K * Real.exp (-(16 * y))) * Real.exp (8 * y) :=
          mul_le_mul hm hsh (Real.sinh_nonneg_iff.mpr (by positivity))
            (mul_nonneg hK0 (Real.exp_pos _).le)
      _ = K * (Real.exp (-(16 * y)) * Real.exp (8 * y)) := by ring
      _ = K * Real.exp (-(8 * y)) := by
          congr 1; rw [← Real.exp_add]; congr 1; ring
  have hexp8 : IntegrableOn (fun y : ℝ => Real.exp (-(8 * y))) (Ioi (0 : ℝ)) := by
    refine integrable_exp_neg_eight_mul_abs.integrableOn.congr_fun (fun y hy => ?_) measurableSet_Ioi
    dsimp only
    rw [abs_of_pos (mem_Ioi.mp hy)]
  have hdom : Integrable (fun p : ℝ × ℝ =>
      ((2 * Z) ^ 2 * K ^ 2) * (Real.exp (-(16 * p.1)) * Real.exp (-(8 * p.2))))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hexp16 : IntegrableOn (fun x : ℝ => Real.exp (-(16 * x))) (Ioi (0 : ℝ)) := by
      refine hexp8.mono' (by fun_prop) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hx
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (by linarith)
    exact (hexp16.integrable.mul_prod hexp8.integrable).const_mul _
  have hωc : Continuous (shiftedGroundState a) := (contDiff_shiftedGroundState a).continuous
  have hmeas : Measurable (Function.uncurry fun x s =>
      Real.sinh (x / 2) * Real.sinh ((x + s) / 2) *
        sameSideGroundJump (shiftedGroundState a) u s x) := by
    have hsh1 : Continuous fun p : ℝ × ℝ => Real.sinh (p.1 / 2) :=
      Real.continuous_sinh.comp (continuous_fst.div_const 2)
    have hsh2 : Continuous fun p : ℝ × ℝ => Real.sinh ((p.1 + p.2) / 2) :=
      Real.continuous_sinh.comp ((continuous_fst.add continuous_snd).div_const 2)
    have hj : Continuous fun p : ℝ × ℝ => sameSideGroundJump (shiftedGroundState a) u p.2 p.1 :=
      (continuous_sameSideGroundJump_uncurry hωc hu).comp (continuous_snd.prodMk continuous_fst)
    exact ((hsh1.mul hsh2).mul hj).measurable
  refine hdom.mono' hmeas.aestronglyMeasurable ?_
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with ⟨x, s⟩ hp
  have hx0 : 0 < x := hp.1
  have hs0 : 0 < s := hp.2
  have hpos : ∀ z, 0 < z → 0 ≤ shiftedGroundState a z := fun z hz => (shiftedGroundState_pos ha hz).le
  have hnn : 0 ≤ Real.sinh (x / 2) * Real.sinh ((x + s) / 2) *
      sameSideGroundJump (shiftedGroundState a) u s x :=
    mul_nonneg (mul_nonneg (Real.sinh_nonneg_iff.mpr (by positivity))
      (Real.sinh_nonneg_iff.mpr (by positivity)))
      (sameSideGroundJump_nonneg hpos hs0.le hx0)
  rw [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_of_nonneg hnn,
    sinh_mul_sinh_mul_sameSideGroundJump_eq]
  have hu_sq : (u x - u (x + s)) ^ 2 ≤ (2 * Z) ^ 2 := by
    rw [← sq_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    calc |u x - u (x + s)| ≤ |u x| + |u (x + s)| := abs_sub _ _
      _ ≤ Z + Z := add_le_add (hZ' x) (hZ' (x + s))
      _ = 2 * Z := by ring
  have hg1 := hg_bound x hx0.le
  have hg2 := hg_bound (x + s) (by linarith)
  have hg10 : 0 ≤ shiftDifference a x * Real.sinh (x / 2) :=
    mul_nonneg (shiftDifference_nonneg_of_nonneg ha.le hx0.le)
      (Real.sinh_nonneg_iff.mpr (by positivity))
  have hg20 : 0 ≤ shiftDifference a (x + s) * Real.sinh ((x + s) / 2) :=
    mul_nonneg (shiftDifference_nonneg_of_nonneg ha.le (by linarith))
      (Real.sinh_nonneg_iff.mpr (by positivity))
  dsimp only
  calc (u x - u (x + s)) ^ 2 *
        ((shiftDifference a x * Real.sinh (x / 2)) *
          (shiftDifference a (x + s) * Real.sinh ((x + s) / 2)))
      ≤ (2 * Z) ^ 2 * ((K * Real.exp (-(8 * x))) * (K * Real.exp (-(8 * (x + s))))) :=
        mul_le_mul hu_sq (mul_le_mul hg1 hg2 hg20 (mul_nonneg hK0 (Real.exp_pos _).le))
          (mul_nonneg hg10 hg20) (sq_nonneg _)
    _ = ((2 * Z) ^ 2 * K ^ 2) *
          (Real.exp (-(8 * x) + -(8 * (x + s)))) := by
        rw [Real.exp_add]; ring
    _ = ((2 * Z) ^ 2 * K ^ 2) * (Real.exp (-(16 * x)) * Real.exp (-(8 * s))) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **Ordered-pair representation of `profileVariance`.** Folding the half-line variance of `u`
against `μ_a(x) = m_a(x) sinh(x/2)` onto ordered pairs `0 < x < y = x + s` expresses
`profileVariance a u` purely in terms of `sameSideGroundJump`:
`V_a(u) = 8 ∫_{x>0} ∫_{s>0} sinh(x/2) sinh((x + s)/2) J_s(x) ds dx`. -/
theorem profileVariance_eq_eight_mul_sinh_sameSideGroundJump
    (hu : Continuous u) (huc : HasCompactSupport u) :
    profileVariance a u =
      8 * ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
        Real.sinh (x / 2) * Real.sinh ((x + s) / 2) *
          sameSideGroundJump (shiftedGroundState a) u s x := by
  obtain ⟨Z, hZ⟩ := huc.exists_bound_of_continuous hu
  have hZ' : ∀ x, |u x| ≤ Z := fun x => by simpa [Real.norm_eq_abs] using hZ x
  set g : ℝ → ℝ := fun x => shiftDifference a x * Real.sinh (x / 2)
  set μ : ℝ → ℝ := (Ioi (0 : ℝ)).indicator g
  have hgi : Integrable g := integrable_shiftDifference_mul_sinh_half a
  have hμi : Integrable μ := hgi.integrableOn.integrable_indicator measurableSet_Ioi
  have hμ0 : (∫ x, μ x) = Real.sinh (a / 2) / 2 := by
    rw [integral_indicator measurableSet_Ioi]
    exact integral_Ioi_shiftDifference_mul_sinh_half a
  have hμ1 : (∫ x, u x * μ x) = profileMoment a u := by
    have heq : (fun x => u x * μ x) = (Ioi (0 : ℝ)).indicator (fun x => u x * g x) := by
      funext x; by_cases hx : x ∈ Ioi (0 : ℝ) <;> simp [μ, hx]
    rw [heq, integral_indicator measurableSet_Ioi]
    exact setIntegral_congr_fun measurableSet_Ioi fun x _ => by simp only [g]; ring
  have hμ2 : (∫ x, u x ^ 2 * μ x) =
      ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) := by
    have heq : (fun x => u x ^ 2 * μ x) = (Ioi (0 : ℝ)).indicator (fun x => u x ^ 2 * g x) := by
      funext x; by_cases hx : x ∈ Ioi (0 : ℝ) <;> simp [μ, hx]
    rw [heq, integral_indicator measurableSet_Ioi]
    exact setIntegral_congr_fun measurableSet_Ioi fun x _ => by simp only [g]; ring
  have hvar : profileVariance a u = 4 * varianceEnergy μ u := by
    rw [varianceEnergy_eq hμi hu hZ', hμ0, hμ1, hμ2]
    unfold profileVariance
    ring
  -- Reduce `varianceEnergy μ u` to `(Ioi 0) × (Ioi 0)` and split into `x < y` and `y < x`
  set F : ℝ → ℝ → ℝ := fun x y => (u x - u y) ^ 2 * (g x * g y)
  have hF_symm : ∀ x y, F y x = F x y := fun x y => by simp only [F]; ring
  have hF_diag : ∀ x, F x x = 0 := fun x => by simp [F]
  have hve_Ioi : varianceEnergy μ u = ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), F x y := by
    unfold varianceEnergy
    have hin : ∀ x, (∫ y, (u x - u y) ^ 2 * (μ x * μ y)) =
        (Ioi (0 : ℝ)).indicator (fun x => ∫ y in Ioi (0 : ℝ), F x y) x := by
      intro x
      by_cases hx : x ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem hx]
        have hy_eq : (fun y => (u x - u y) ^ 2 * (μ x * μ y)) =
            (Ioi (0 : ℝ)).indicator (fun y => F x y) := by
          funext y
          by_cases hy : y ∈ Ioi (0 : ℝ)
          · simp [μ, hx, hy, F]
          · simp [μ, hx, hy]
        rw [hy_eq, integral_indicator measurableSet_Ioi]
      · rw [indicator_of_notMem hx]
        simp [μ, hx]
    simp_rw [hin]
    exact integral_indicator measurableSet_Ioi
  -- Split `F x y` pointwise into upper (`x < y`) and lower (`y < x`) triangles
  set U : ℝ × ℝ → ℝ := {q : ℝ × ℝ | q.1 < q.2}.indicator (fun q => F q.1 q.2)
  set L : ℝ × ℝ → ℝ := {q : ℝ × ℝ | q.2 < q.1}.indicator (fun q => F q.1 q.2)
  have hF_prod : Integrable (fun p : ℝ × ℝ => F p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hdom : Integrable (fun p : ℝ × ℝ => (2 * Z) ^ 2 * (g p.1 * g p.2))
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
      (hgi.integrableOn.integrable.mul_prod hgi.integrableOn.integrable).const_mul _
    have hcontF : Continuous (fun p : ℝ × ℝ => F p.1 p.2) :=
      (((hu.comp continuous_fst).sub (hu.comp continuous_snd)).pow 2).mul
        (((continuous_shiftDifference a).mul
          (Real.continuous_sinh.comp (continuous_id.div_const 2))).comp continuous_fst |>.mul
        (((continuous_shiftDifference a).mul
          (Real.continuous_sinh.comp (continuous_id.div_const 2))).comp continuous_snd))
    refine hdom.mono' hcontF.measurable.aestronglyMeasurable ?_
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
    have hp1 : 0 < p.1 := hp.1
    have hp2 : 0 < p.2 := hp.2
    have hg1 : 0 ≤ g p.1 := mul_nonneg (shiftDifference_nonneg_of_nonneg ha.le hp1.le)
      (Real.sinh_nonneg_iff.mpr (by positivity))
    have hg2 : 0 ≤ g p.2 := mul_nonneg (shiftDifference_nonneg_of_nonneg ha.le hp2.le)
      (Real.sinh_nonneg_iff.mpr (by positivity))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg hg1 hg2))]
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hg1 hg2)
    rw [← sq_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    calc |u p.1 - u p.2| ≤ |u p.1| + |u p.2| := abs_sub _ _
      _ ≤ Z + Z := add_le_add (hZ' p.1) (hZ' p.2)
      _ = 2 * Z := by ring
  have hU_int : Integrable U
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    hF_prod.indicator (measurableSet_lt measurable_fst measurable_snd)
  have hL_int : Integrable L
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    hF_prod.indicator (measurableSet_lt measurable_snd measurable_fst)
  have hpt_split : ∀ x y, F x y = U (x, y) + L (x, y) := by
    intro x y
    rcases lt_trichotomy x y with hxy | rfl | hyx
    · simp [U, L, hxy, not_lt_of_gt hxy]
    · simp [U, L, hF_diag]
    · simp [U, L, hyx, not_lt_of_gt hyx]
  have hLU : ∀ x y, L (x, y) = U (y, x) := by
    intro x y
    by_cases hyx : y < x
    · simp [L, U, hyx, hF_symm x y]
    · simp [L, U, hyx]
  have hswap : (∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), L (x, y)) =
      ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), U (x, y) := by
    rw [integral_integral_swap (f := fun x y => L (x, y)) hL_int]
    simp_rw [hLU]
  have hve_two : varianceEnergy μ u =
      2 * ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), U (x, y) := by
    rw [hve_Ioi]
    have hinner_eq : (∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), F x y) =
        (∫ x in Ioi (0 : ℝ), (∫ y in Ioi (0 : ℝ), U (x, y)) +
          ∫ y in Ioi (0 : ℝ), L (x, y)) := by
      refine integral_congr_ae ?_
      filter_upwards [hU_int.prod_right_ae, hL_int.prod_right_ae] with x hUx hLx
      simp_rw [hpt_split x]
      exact integral_add hUx hLx
    rw [hinner_eq, integral_add hU_int.integral_prod_left hL_int.integral_prod_left, hswap]
    ring
  have hU_shift : ∀ x : ℝ, 0 < x →
      (∫ y in Ioi (0 : ℝ), U (x, y)) =
        ∫ s in Ioi (0 : ℝ),
          Real.sinh (x / 2) * Real.sinh ((x + s) / 2) *
            sameSideGroundJump (shiftedGroundState a) u s x := by
    intro x hx
    have h1 : (∫ y in Ioi (0 : ℝ), U (x, y)) = ∫ y in Ioi x, F x y := by
      rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
      congr 1
      funext y
      by_cases hxy : x < y
      · simp [U, hxy, hx.trans hxy]
      · simp [U, hxy]
    rw [h1, setIntegral_Ioi_translate]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    dsimp only [F, g]
    rw [add_comm s x, ← sinh_mul_sinh_mul_sameSideGroundJump_eq]
  rw [hvar, hve_two, setIntegral_congr_fun measurableSet_Ioi fun x hx => hU_shift x hx]
  ring

/-- `profileVariance` expressed via the hyperbolic `cosh` jump difference. -/
theorem profileVariance_eq_cosh_sub_sameSideGroundJump
    (hu : Continuous u) (huc : HasCompactSupport u) :
    profileVariance a u =
      2 * ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
        (2 * Real.cosh ((s + 2 * x) / 2) - 2 * Real.cosh (s / 2)) *
          sameSideGroundJump (shiftedGroundState a) u s x := by
  rw [profileVariance_eq_eight_mul_sinh_sameSideGroundJump ha hu huc]
  have hmul : (8 : ℝ) = 2 * 4 := by norm_num
  rw [hmul, mul_assoc, ← integral_const_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [two_mul_cosh_add_two_mul_sub_eq_four_mul_sinh_mul_sinh]
  ring

/-- **Light-cone assembly of the archimedean surplus and profile variance.**
Adding `profileVariance a u` to `2 S_arch(ω_a, u) − D_arch(ω_a, u)` folds both into a single
double integral against the strictly positive antisymmetric Weil jump difference
`weilJumpDensity s − weilJumpDensity (s + 2x)`. -/
theorem archSurplus_add_profileVariance_eq_weilJumpDensity_sub
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    (2 * archSameSideEnergy (shiftedGroundState a) u -
        archReflectedDifferenceEnergy (shiftedGroundState a) u) +
      profileVariance a u =
      2 * ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
        (weilJumpDensity s - weilJumpDensity (s + 2 * x)) *
          sameSideGroundJump (shiftedGroundState a) u s x := by
  have hpos : ∀ z, 0 < z → 0 ≤ shiftedGroundState a z := fun z hz => (shiftedGroundState_pos ha hz).le
  have hS_prod : Integrable (Function.uncurry fun x s =>
      archLevyDensity s * sameSideGroundJump (shiftedGroundState a) u s x)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (integrable_archLevy_mul_sameSideGroundJump_prod ha hu huc).swap
  have hD_prod : Integrable (Function.uncurry fun x s =>
      archLevyDensity (s + 2 * x) * sameSideGroundJump (shiftedGroundState a) u s x)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hωc : Continuous (shiftedGroundState a) := (contDiff_shiftedGroundState a).continuous
    have hmeas : Measurable (Function.uncurry fun x s =>
        archLevyDensity (s + 2 * x) * sameSideGroundJump (shiftedGroundState a) u s x) :=
      (measurable_archLevyDensity.comp (measurable_snd.add (measurable_const.mul measurable_fst))).mul
        ((continuous_sameSideGroundJump_uncurry hωc hu.continuous).comp
          (continuous_snd.prodMk continuous_fst)).measurable
    refine hS_prod.mono' hmeas.aestronglyMeasurable ?_
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with ⟨x, s⟩ hp
    have hx0 : 0 < x := hp.1
    have hs0 : 0 < s := hp.2
    have hnn : 0 ≤ archLevyDensity (s + 2 * x) *
        sameSideGroundJump (shiftedGroundState a) u s x :=
      mul_nonneg (archLevyDensity_pos (by linarith)).le (sameSideGroundJump_nonneg hpos hs0.le hx0)
    rw [Function.uncurry_apply_pair, Function.uncurry_apply_pair, Real.norm_eq_abs, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_right
      (strictAntiOn_archLevyDensity.antitoneOn hs0 (show (0 : ℝ) < s + 2 * x by linarith)
        (by linarith))
      (sameSideGroundJump_nonneg hpos hs0.le hx0)
  have hV_prod : Integrable (Function.uncurry fun x s =>
      (4 * Real.sinh (x / 2) * Real.sinh ((x + s) / 2)) *
        sameSideGroundJump (shiftedGroundState a) u s x)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine ((integrable_sinh_mul_sinh_sameSideGroundJump_prod ha hu.continuous huc).const_mul 4).congr
      (Eventually.of_forall fun ⟨x, s⟩ => ?_)
    dsimp only [Function.uncurry]
    ring
  rw [archSameSideEnergy_eq ha hu huc, archReflectedDifferenceEnergy_eq ha hu huc,
    profileVariance_eq_eight_mul_sinh_sameSideGroundJump ha hu.continuous huc]
  have h8 : (8 : ℝ) * (∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
      Real.sinh (x / 2) * Real.sinh ((x + s) / 2) *
        sameSideGroundJump (shiftedGroundState a) u s x) =
      2 * ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
        (4 * Real.sinh (x / 2) * Real.sinh ((x + s) / 2)) *
          sameSideGroundJump (shiftedGroundState a) u s x := by
    rw [show (8 : ℝ) = 2 * 4 by norm_num, mul_assoc, ← integral_const_mul]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by ring
  rw [h8]
  have hS_left : Integrable (fun x => ∫ s in Ioi (0 : ℝ),
      archLevyDensity s * sameSideGroundJump (shiftedGroundState a) u s x)
      (volume.restrict (Ioi (0 : ℝ))) := hS_prod.integral_prod_left
  have hD_left : Integrable (fun x => ∫ s in Ioi (0 : ℝ),
      archLevyDensity (s + 2 * x) * sameSideGroundJump (shiftedGroundState a) u s x)
      (volume.restrict (Ioi (0 : ℝ))) := hD_prod.integral_prod_left
  have hsub : (∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
        archLevyDensity s * sameSideGroundJump (shiftedGroundState a) u s x) -
      (∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
        archLevyDensity (s + 2 * x) * sameSideGroundJump (shiftedGroundState a) u s x) =
      ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
        (archLevyDensity s - archLevyDensity (s + 2 * x)) *
          sameSideGroundJump (shiftedGroundState a) u s x := by
    rw [← integral_sub hS_left hD_left]
    refine integral_congr_ae ?_
    filter_upwards [hS_prod.prod_right_ae, hD_prod.prod_right_ae] with x hSx hDx
    have hSx' : Integrable (fun s =>
        archLevyDensity s * sameSideGroundJump (shiftedGroundState a) u s x)
        (volume.restrict (Ioi (0 : ℝ))) := hSx
    have hDx' : Integrable (fun s =>
        archLevyDensity (s + 2 * x) * sameSideGroundJump (shiftedGroundState a) u s x)
        (volume.restrict (Ioi (0 : ℝ))) := hDx
    rw [← integral_sub hSx' hDx']
    exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by ring
  have hSD_prod : Integrable (Function.uncurry fun x s =>
      (archLevyDensity s - archLevyDensity (s + 2 * x)) *
        sameSideGroundJump (shiftedGroundState a) u s x)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine (hS_prod.sub hD_prod).congr (Eventually.of_forall fun ⟨x, s⟩ => ?_)
    dsimp only [Pi.sub_apply, Function.uncurry]
    ring
  have hSD_left : Integrable (fun x => ∫ s in Ioi (0 : ℝ),
      (archLevyDensity s - archLevyDensity (s + 2 * x)) *
        sameSideGroundJump (shiftedGroundState a) u s x)
      (volume.restrict (Ioi (0 : ℝ))) := hSD_prod.integral_prod_left
  have hV_left : Integrable (fun x => ∫ s in Ioi (0 : ℝ),
      (4 * Real.sinh (x / 2) * Real.sinh ((x + s) / 2)) *
        sameSideGroundJump (shiftedGroundState a) u s x)
      (volume.restrict (Ioi (0 : ℝ))) := hV_prod.integral_prod_left
  have hadd : (∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
        (archLevyDensity s - archLevyDensity (s + 2 * x)) *
          sameSideGroundJump (shiftedGroundState a) u s x) +
      (∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
        (4 * Real.sinh (x / 2) * Real.sinh ((x + s) / 2)) *
          sameSideGroundJump (shiftedGroundState a) u s x) =
      ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
        (weilJumpDensity s - weilJumpDensity (s + 2 * x)) *
          sameSideGroundJump (shiftedGroundState a) u s x := by
    rw [← integral_add hSD_left hV_left]
    refine integral_congr_ae ?_
    filter_upwards [hSD_prod.prod_right_ae, hV_prod.prod_right_ae] with x hSDx hVx
    have hSDx' : Integrable (fun s =>
        (archLevyDensity s - archLevyDensity (s + 2 * x)) *
          sameSideGroundJump (shiftedGroundState a) u s x)
        (volume.restrict (Ioi (0 : ℝ))) := hSDx
    have hVx' : Integrable (fun s =>
        (4 * Real.sinh (x / 2) * Real.sinh ((x + s) / 2)) *
          sameSideGroundJump (shiftedGroundState a) u s x)
        (volume.restrict (Ioi (0 : ℝ))) := hVx
    rw [← integral_add hSDx' hVx']
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [weilJumpDensity_sub_add_two_mul_eq]
    ring
  linarith [hsub, hadd]

/-- **Exact antisymmetric light-cone representation of `zeroForm (Φ(ω_a u))`.**
For every shift `a > 0` and every even `u ∈ C²_c(ℝ)`, the pole-cancelled zero form decomposes into
the strictly positive continuum light-cone integral against `κ(s) − κ(s + 2x)` plus twice the
same-side prime jumps minus twice the half-collar reflected prime jumps. -/
theorem zeroForm_shiftedGroundState_eq_antisymmetric_weilJumpDensity_add_prime
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    zeroForm (phiDoobTest (fun y => shiftedGroundState a y * u y)) =
      2 * (∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
        (weilJumpDensity s - weilJumpDensity (s + 2 * x)) *
          sameSideGroundJump (shiftedGroundState a) u s x) +
      2 * primeSameSideEnergy (shiftedGroundState a) u -
      2 * ∑' n : ℕ, vonMangoldtAtom n *
        ∫ x in Ioo (0 : ℝ) (Real.log n / 2),
          reflectedDifferenceJump (shiftedGroundState a) u (Real.log n) x := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hωc : Continuous (shiftedGroundState a) := (contDiff_shiftedGroundState a).continuous
  rw [← poleFreeForm_eq_zeroForm ha hu huc heven,
    sameSideEnergy_eq_arch_add_prime, reflectedDifferenceEnergy_eq_arch_add_prime,
    primeReflectedDifferenceEnergy_eq_two_mul_half hωc hu.continuous]
  linarith [archSurplus_add_profileVariance_eq_weilJumpDensity_sub ha hu1 huc]

/-- **Completeness of the antisymmetric light-cone prime variation inequality.**
For every shift `a > 0`, `RiemannHypothesis` holds iff for every even `u ∈ C²_c(ℝ)` the folded
prime anti-diagonal sum is bounded by the antisymmetric `weilJumpDensity` continuum energy plus
the same-side prime jump energy. -/
theorem riemannHypothesis_iff_forall_prime_le_antisymmetric_weilJumpDensity :
    RiemannHypothesis ↔ ∀ u : ℝ → ℝ, ContDiff ℝ 2 u → HasCompactSupport u →
      (∀ x, u (-x) = u x) →
        (∑' n : ℕ, vonMangoldtAtom n *
          ∫ x in Ioo (0 : ℝ) (Real.log n / 2),
            reflectedDifferenceJump (shiftedGroundState a) u (Real.log n) x) ≤
          (∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
            (weilJumpDensity s - weilJumpDensity (s + 2 * x)) *
              sameSideGroundJump (shiftedGroundState a) u s x) +
            primeSameSideEnergy (shiftedGroundState a) u := by
  rw [riemannHypothesis_iff_forall_prime_variationInequality ha]
  refine forall_congr' fun u => forall_congr' fun hu => forall_congr' fun huc =>
    forall_congr' fun _ => ?_
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hωc : Continuous (shiftedGroundState a) := (contDiff_shiftedGroundState a).continuous
  rw [primeReflectedDifferenceEnergy_eq_two_mul_half hωc hu.continuous]
  have harch := archSurplus_add_profileVariance_eq_weilJumpDensity_sub ha hu1 huc
  constructor <;> intro h <;> linarith

end ShiftedGroundState

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
