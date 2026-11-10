import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ThePacketsOnTheDegreePointsCarryWeilsArchimedeanForm
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheDensityOfTheCarrierIsWeilsConstant

/-!
# The packets on the comb of squares carry Weil's archimedean form

The comb of squares has the degree points `n²`, with the masses `2/n` of its cells and the
logarithmic coordinate `2 log n`. It is not the image of the integers under a multiplication, and
its jets are not those of the integers: the unitary number of `Γ_{m²}` and `Γ_{n²}` is the Lévy
density at twice the displacement of `m` and `n`.

* **Two combs differ by a continuous kernel** (`combDefect_of_pos`, `two_div_mul_squareWeight`):
  `2ω(2x) − ω(x)` is a rational function of `e^{−x/2}` without a pole at `x = 0`, and the pairing
  of two square degree points with the masses of their comb is twice the pairing of `m`, `n` on
  the integers plus twice this kernel at `log(m/n)` over `mn`.
* **The pairing on the comb of squares** (`squareForm_eq`, `tendsto_squareForm_defect`): the
  pairing of a packet minus the masses times `log(n/4π)` is twice the form on the integers, plus
  twice a Riemann sum of the continuous kernel, plus `2 log 2` times the mass.
* **The primitive of the kernel** (`integral_combDefect`):
  `∫_0^y (2ω(2x) − ω(x)) dx = Ω(y) − Ω(2y) − ½ log 2`; the constant `½ log 2` is the value at `0`
  of the difference of the two primitives, and it is what the change of the counterterm from
  `log(n/2π)` to `log(n/4π)` pays.
* **Weil's form of the halved packet** (`weilArchRe_sub_pole_comp_div_two`): for `f(s) = g(s/2)`
  the archimedean form is twice that of `g`, minus twice the kernel on `g`, minus `2 log 2` times
  the mass. The window form of the jump integral is used on `[0, c]` for `g` and on `[0, 2c]` for
  `f`; the rows of the kernel on the window cancel against the primitives of the tails.
* **The packet theorem** (`tendsto_squareForm`): the form on the comb of squares tends to minus
  the archimedean part of Weil's functional, without the pole, of the packet in the logarithmic
  coordinate of the squares.

The counterterm `log(n/4π)` is the logarithm of the density `n/2` of the comb over `2π`. The
argument compares two combs whose Lévy densities differ by a continuous kernel; it uses nothing
else of the squares.
-/

open Finset Filter Topology MeasureTheory
open Zeta23

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

local notation "ω" => _root_.RHTower.archLevyDensity
local notation "Ω" => _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv

/-! ### The kernel between the two combs -/

/-- The difference `2ω(2x) − ω(x)` of the Lévy densities of the comb of squares and of the comb
of integers, as a rational function of `r = e^{−|x|/2}`. -/
def combDefect (x : ℝ) : ℝ :=
  -(Real.exp (-|x| / 2) *
      (1 - Real.exp (-|x| / 2) - Real.exp (-|x| / 2) ^ 2 - Real.exp (-|x| / 2) ^ 3)) /
    ((1 + Real.exp (-|x| / 2)) * (1 + Real.exp (-|x| / 2) ^ 2) * (1 + Real.exp (-|x| / 2) ^ 4))

theorem continuous_combDefect : Continuous combDefect := by
  unfold combDefect
  exact Continuous.div (by fun_prop) (by fun_prop) fun x => by positivity

theorem combDefect_abs (x : ℝ) : combDefect |x| = combDefect x := by
  unfold combDefect
  rw [abs_abs]

theorem combDefect_of_pos {x : ℝ} (hx : 0 < x) : combDefect x = 2 * ω (2 * x) - ω x := by
  have hr0 : 0 < Real.exp (-x / 2) := Real.exp_pos _
  have hr1 : Real.exp (-x / 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have e1 : Real.exp (-(2 * x) / 2) = Real.exp (-x / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have e2 : Real.exp (-2 * (2 * x)) = Real.exp (-x / 2) ^ 8 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have e3 : Real.exp (-2 * x) = Real.exp (-x / 2) ^ 4 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  unfold combDefect _root_.RHTower.archLevyDensity
  rw [abs_of_pos hx, e1, e2, e3]
  generalize Real.exp (-x / 2) = r at hr0 hr1
  have h4 : 1 - r ^ 4 ≠ 0 := (sub_pos.mpr (pow_lt_one₀ hr0.le hr1 (by norm_num))).ne'
  have h8 : 1 - r ^ 8 ≠ 0 := (sub_pos.mpr (pow_lt_one₀ hr0.le hr1 (by norm_num))).ne'
  have h1 : 1 + r ≠ 0 := by positivity
  have h2 : 1 + r ^ 2 ≠ 0 := by positivity
  have h3 : 1 + r ^ 4 ≠ 0 := by positivity
  field_simp
  ring

/-- The pairing of two square degree points with the masses of the comb of squares: twice the
pairing on the integers plus twice the kernel between the two combs. -/
theorem two_div_mul_squareWeight {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    2 / (n : ℝ) * squareWeight m n =
      2 * (levyKernel m n + combDefect (Real.log ((m : ℝ) / n)) / ((m : ℝ) * n)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : 0 < |Real.log ((m : ℝ) / n)| := abs_pos.mpr fun h0 => by
    have h1 := Real.eq_one_of_pos_of_log_eq_zero (div_pos hm' hn') h0
    rw [div_eq_one_iff_eq hn'.ne'] at h1
    exact hmn (by exact_mod_cast h1)
  rw [squareWeight_eq_archLevyDensity hm hn hmn, levyKernel_eq_archLevyDensity hm hn hmn,
    ← combDefect_abs, combDefect_of_pos hx]
  field_simp
  ring

/-! ### The pairing on the comb of squares -/

/-- The pairing of the jets on the comb of squares: the degree points `n²` of the window, the
masses `2/n` of their cells; the packet is sampled at `log(n/N)`, half the logarithmic coordinate
of the square. -/
def squarePairing (g : ℝ → ℝ) (L N : ℕ) : ℝ :=
  ∑ n ∈ Ioc N (N + L * N), ∑ m ∈ (Ioc N (N + L * N)).erase n,
    degreeSample g N m * degreeSample g N n * (2 / (n : ℝ) * squareWeight m n)

/-- The pairing with the counterterm of the comb of squares: the mass `2/n` times
`log(n/4π)`. -/
def squareForm (g : ℝ → ℝ) (L N : ℕ) : ℝ :=
  squarePairing g L N - ∑ n ∈ Ioc N (N + L * N),
    degreeSample g N n ^ 2 * (2 / (n : ℝ)) * Real.log ((n : ℝ) / (4 * Real.pi))

/-- The kernel between the two combs on a packet. -/
def defectSum (g : ℝ → ℝ) (L N : ℕ) : ℝ :=
  ∑ n ∈ Ioc N (N + L * N), ∑ m ∈ (Ioc N (N + L * N)).erase n,
    degreeSample g N m * degreeSample g N n *
      (combDefect (Real.log ((m : ℝ) / n)) / ((m : ℝ) * n))

/-- **The form on the comb of squares against the form on the integers.** -/
theorem squareForm_eq (g : ℝ → ℝ) (L N : ℕ) :
    squareForm g L N = 2 * degreeForm g L N + 2 * defectSum g L N +
      2 * Real.log 2 * ∑ n ∈ Ioc N (N + L * N), degreeSample g N n ^ 2 / n := by
  have hpair : squarePairing g L N = 2 * degreePairing g L N + 2 * defectSum g L N := by
    unfold squarePairing degreePairing defectSum
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hn0 : 0 < n := by
      have := (Finset.mem_Ioc.mp hn).1
      omega
    have hm0 : 0 < m := by
      have := (Finset.mem_Ioc.mp (Finset.mem_of_mem_erase hm)).1
      omega
    rw [two_div_mul_squareWeight hm0 hn0 (Finset.ne_of_mem_erase hm)]
    ring
  have hct : ∑ n ∈ Ioc N (N + L * N),
        degreeSample g N n ^ 2 * (2 / (n : ℝ)) * Real.log ((n : ℝ) / (4 * Real.pi)) =
      2 * ∑ n ∈ Ioc N (N + L * N),
          degreeSample g N n ^ 2 / n * Real.log ((n : ℝ) / (2 * Real.pi)) -
        2 * Real.log 2 * ∑ n ∈ Ioc N (N + L * N), degreeSample g N n ^ 2 / n := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : (0 : ℝ) < n := by
      have := (Finset.mem_Ioc.mp hn).1
      exact_mod_cast (by omega : 0 < n)
    have hlog : Real.log ((n : ℝ) / (4 * Real.pi)) =
        Real.log ((n : ℝ) / (2 * Real.pi)) - Real.log 2 := by
      rw [show (n : ℝ) / (4 * Real.pi) = (n : ℝ) / (2 * Real.pi) / 2 by ring,
        Real.log_div (by positivity) (by norm_num)]
    rw [hlog]
    ring
  rw [squareForm, hpair, hct, degreeForm]
  ring

/-- The kernel between the two combs on a packet is a Riemann sum. -/
theorem tendsto_defectSum {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ} (hB : ∀ u, |g u| ≤ B)
    (L : ℕ) :
    Tendsto (defectSum g L) atTop
      (𝓝 (∫ u in (0 : ℝ)..Real.log (1 + L), ∫ v in (0 : ℝ)..Real.log (1 + L),
        g u * g v * combDefect (u - v))) := by
  have hΨ : Continuous (Function.uncurry fun u v : ℝ => g u * g v * combDefect (u - v)) :=
    ((hg.comp continuous_fst).mul (hg.comp continuous_snd)).mul
      (continuous_combDefect.comp (continuous_fst.sub continuous_snd))
  have hfull := tendsto_degreePairSum hΨ L
  -- the diagonal terms of the full sum are of the order `1/N`
  have hdiag : Tendsto (fun N : ℕ => ∑ n ∈ Ioc N (N + L * N),
      degreeSample g N n ^ 2 * combDefect 0 / (n : ℝ) ^ 2) atTop (𝓝 0) := by
    have hbound : Tendsto (fun N : ℕ => (L : ℝ) * (B ^ 2 * |combDefect 0|) / N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Real.norm_eq_abs]
    calc |∑ n ∈ Ioc N (N + L * N), degreeSample g N n ^ 2 * combDefect 0 / (n : ℝ) ^ 2|
        ≤ ∑ n ∈ Ioc N (N + L * N),
            |degreeSample g N n ^ 2 * combDefect 0 / (n : ℝ) ^ 2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Ioc N (N + L * N), B ^ 2 * |combDefect 0| / (N : ℝ) ^ 2 :=
          Finset.sum_le_sum fun n hn => by
            have hn' : (N : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
            have hgn : degreeSample g N n ^ 2 ≤ B ^ 2 := by
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2
            rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg (degreeSample g N n)),
              abs_of_nonneg (sq_nonneg (n : ℝ))]
            exact div_le_div₀ (mul_nonneg (sq_nonneg B) (abs_nonneg _))
              (mul_le_mul_of_nonneg_right hgn (abs_nonneg _)) (by positivity)
              (pow_le_pow_left₀ hN'.le hn'.le 2)
      _ = (L : ℝ) * (B ^ 2 * |combDefect 0|) / N := by
          rw [Finset.sum_const, Nat.card_Ioc, Nat.add_sub_cancel_left, nsmul_eq_mul]
          push_cast
          field_simp
  have h := hfull.sub hdiag
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  unfold defectSum
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' : (0 : ℝ) < n := by
    have := (Finset.mem_Ioc.mp hn).1
    exact_mod_cast (by omega : 0 < n)
  rw [← Finset.add_sum_erase _ _ hn]
  have hdiagterm : g (Real.log ((n : ℝ) / N)) * g (Real.log ((n : ℝ) / N)) *
        combDefect (Real.log ((n : ℝ) / N) - Real.log ((n : ℝ) / N)) / ((n : ℝ) * n) =
      degreeSample g N n ^ 2 * combDefect 0 / (n : ℝ) ^ 2 := by
    rw [sub_self, degreeSample]
    ring
  rw [hdiagterm, add_sub_cancel_left]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : (0 : ℝ) < m := by
    have := (Finset.mem_Ioc.mp (Finset.mem_of_mem_erase hm)).1
    exact_mod_cast (by omega : 0 < m)
  have hlog : Real.log ((m : ℝ) / N) - Real.log ((n : ℝ) / N) = Real.log ((m : ℝ) / n) := by
    rw [Real.log_div hm'.ne' hN'.ne', Real.log_div hn'.ne' hN'.ne',
      Real.log_div hm'.ne' hn'.ne']
    ring
  rw [hlog, degreeSample, degreeSample]
  ring

/-- **The form on the comb of squares in terms of the form on the integers.** For a packet `g`
supported in `[log 3, log K]`, sampled at `log(n/N)` on the squares `n²`: the pairing with the
masses `2/n` minus the counterterm `log(n/4π)` tends to twice the limit on the integers, plus
twice the kernel between the combs on the packet, plus `2 log 2` times the mass. -/
theorem tendsto_squareForm_defect {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    {K : ℕ} (hK : 1 ≤ K) (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → g u = 0) :
    Tendsto (squareForm g (3 * K)) atTop
      (𝓝 (2 * -(_root_.RHTower.WeilOneSided.weilArchRe
              (EF.weilTest (packetTest g hg hgc).1 (packetTest g hg hgc).1) -
            (_root_.RHTower.weilPoleTerm
              (EF.weilTest (packetTest g hg hgc).1 (packetTest g hg hgc).1)).re) +
          2 * (∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)),
            ∫ v in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), g u * g v * combDefect (u - v)) +
          2 * Real.log 2 * ∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), g u ^ 2)) := by
  obtain ⟨B, hB⟩ := hg.continuous.bounded_above_of_compact_support hgc
  have hB' : ∀ u, |g u| ≤ B := fun u => by
    rw [← Real.norm_eq_abs]
    exact hB u
  have h1 := (tendsto_degreeForm hg hgc hK hsupp).const_mul 2
  have h2 := (tendsto_defectSum hg.continuous hB' (3 * K)).const_mul 2
  have h3 : Tendsto (fun N : ℕ => 2 * Real.log 2 *
        ∑ n ∈ Ioc N (N + 3 * K * N), degreeSample g N n ^ 2 / n) atTop
      (𝓝 (2 * Real.log 2 * ∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), g u ^ 2)) :=
    (tendsto_degreeSum (G := fun u => g u ^ 2) (hg.continuous.pow 2)
      (by omega : 1 ≤ 3 * K)).const_mul (2 * Real.log 2)
  refine ((h1.add h2).add h3).congr fun N => ?_
  exact (squareForm_eq g (3 * K) N).symm

/-! ### The primitive of the kernel -/

/-- The primitive `Ω(y) − Ω(2y)` of the kernel in closed form; it is continuous at `0`. -/
def combPrim (y : ℝ) : ℝ :=
  Real.log (1 + Real.exp (-y / 2)) - Real.log (1 + Real.exp (-y)) / 2 +
    Real.arctan (Real.exp (-y / 2)) - Real.arctan (Real.exp (-y))

theorem continuous_combPrim : Continuous combPrim := by
  have h1 : Continuous fun y : ℝ => Real.log (1 + Real.exp (-y / 2)) :=
    (continuous_const.add (Real.continuous_exp.comp (by fun_prop))).log fun y =>
      (add_pos one_pos (Real.exp_pos _)).ne'
  have h2 : Continuous fun y : ℝ => Real.log (1 + Real.exp (-y)) :=
    (continuous_const.add (Real.continuous_exp.comp continuous_neg)).log fun y =>
      (add_pos one_pos (Real.exp_pos _)).ne'
  have h3 : Continuous fun y : ℝ => Real.arctan (Real.exp (-y / 2)) :=
    Real.continuous_arctan.comp (Real.continuous_exp.comp (by fun_prop))
  have h4 : Continuous fun y : ℝ => Real.arctan (Real.exp (-y)) :=
    Real.continuous_arctan.comp (Real.continuous_exp.comp continuous_neg)
  exact ((h1.sub (h2.div_const 2)).add h3).sub h4

theorem combPrim_zero : combPrim 0 = Real.log 2 / 2 := by
  unfold combPrim
  simp only [neg_zero, zero_div, Real.exp_zero]
  rw [show (1 : ℝ) + 1 = 2 by norm_num]
  ring

theorem combPrim_of_pos {y : ℝ} (hy : 0 < y) : combPrim y = Ω y - Ω (2 * y) := by
  have hr0 : 0 < Real.exp (-y / 2) := Real.exp_pos _
  have hr1 : Real.exp (-y / 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have e1 : Real.exp (-(2 * y) / 2) = Real.exp (-y / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have e2 : Real.exp (-y) = Real.exp (-y / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  unfold combPrim _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv
  rw [e1, e2]
  generalize Real.exp (-y / 2) = r at hr0 hr1
  have hlog : Real.log (1 - r ^ 2) = Real.log (1 - r) + Real.log (1 + r) := by
    rw [← Real.log_mul (sub_pos.mpr hr1).ne' (by positivity)]
    congr 1
    ring
  rw [hlog]
  ring

theorem hasDerivAt_archLevyAntideriv_sub {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => Ω y - Ω (2 * y)) (combDefect x) x := by
  have h1 := _root_.RHTower.WeilLevyPoleGauss.hasDerivAt_archLevyAntideriv hx
  have h2 : HasDerivAt (fun y => Ω (2 * y)) (-ω (2 * x) * 2) x := by
    have hin : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
      simpa using (hasDerivAt_id x).const_mul 2
    exact (_root_.RHTower.WeilLevyPoleGauss.hasDerivAt_archLevyAntideriv
      (by positivity : 0 < 2 * x)).comp x hin
  rw [combDefect_of_pos hx]
  exact (h1.sub h2).congr_deriv (by ring)

theorem integral_combDefect_of_pos {ε y : ℝ} (hε : 0 < ε) (hεy : ε ≤ y) :
    ∫ x in ε..y, combDefect x = combPrim y - combPrim ε := by
  have hpos : ∀ x ∈ Set.uIcc ε y, 0 < x := fun x hx =>
    lt_of_lt_of_le (lt_min hε (hε.trans_le hεy)) hx.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hasDerivAt_archLevyAntideriv_sub (hpos x hx))
      (continuous_combDefect.intervalIntegrable _ _),
    combPrim_of_pos (hε.trans_le hεy), combPrim_of_pos hε]

/-- **The primitive of the kernel between the two combs**: `∫_0^y (2ω(2x) − ω(x)) dx =
Ω(y) − Ω(2y) − ½ log 2`. -/
theorem integral_combDefect {y : ℝ} (hy : 0 < y) :
    ∫ x in (0 : ℝ)..y, combDefect x = Ω y - Ω (2 * y) - Real.log 2 / 2 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable combDefect volume a b := fun a b =>
    continuous_combDefect.intervalIntegrable a b
  have hQ : Continuous fun ε : ℝ => (∫ x in (0 : ℝ)..ε, combDefect x) - combPrim ε :=
    (intervalIntegral.continuous_primitive hint 0).sub continuous_combPrim
  have hconst : ∀ ε ∈ Set.Ioc (0 : ℝ) y, (∫ x in (0 : ℝ)..ε, combDefect x) - combPrim ε =
      (∫ x in (0 : ℝ)..y, combDefect x) - combPrim y := by
    intro ε hε
    have h1 := integral_combDefect_of_pos hε.1 hε.2
    have h2 := intervalIntegral.integral_add_adjacent_intervals (hint 0 ε) (hint ε y)
    linarith
  have hlim1 : Tendsto (fun ε : ℝ => (∫ x in (0 : ℝ)..ε, combDefect x) - combPrim ε) (𝓝[>] 0)
      (𝓝 ((∫ x in (0 : ℝ)..(0 : ℝ), combDefect x) - combPrim 0)) :=
    (hQ.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto (fun ε : ℝ => (∫ x in (0 : ℝ)..ε, combDefect x) - combPrim ε) (𝓝[>] 0)
      (𝓝 ((∫ x in (0 : ℝ)..y, combDefect x) - combPrim y)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [Ioc_mem_nhdsGT hy] with ε hε
      exact (hconst ε hε).symm)
  have h := tendsto_nhds_unique hlim1 hlim2
  rw [intervalIntegral.integral_same, zero_sub, combPrim_zero] at h
  rw [← combPrim_of_pos hy]
  linarith

theorem combDefect_neg (x : ℝ) : combDefect (-x) = combDefect x := by
  unfold combDefect
  rw [abs_neg]

/-- A row of the kernel on a window. -/
theorem integral_combDefect_sub (u c : ℝ) :
    ∫ v in (0 : ℝ)..c, combDefect (u - v) =
      (∫ x in (0 : ℝ)..u, combDefect x) + ∫ x in (0 : ℝ)..(c - u), combDefect x := by
  have hint : ∀ a b : ℝ, IntervalIntegrable combDefect volume a b := fun a b =>
    continuous_combDefect.intervalIntegrable a b
  have h1 : ∫ v in (0 : ℝ)..c, combDefect (u - v) = ∫ x in (u - c)..u, combDefect x := by
    rw [intervalIntegral.integral_comp_sub_left (fun x => combDefect x) u, sub_zero]
  have h2 : ∫ x in (u - c)..(0 : ℝ), combDefect x = ∫ x in (0 : ℝ)..(c - u), combDefect x := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := c - u)
      (fun x => combDefect x)
    simp only [combDefect_neg, neg_zero, neg_sub] at h
    exact h.symm
  rw [h1, ← intervalIntegral.integral_add_adjacent_intervals (hint (u - c) 0) (hint 0 u), h2,
    add_comm]

/-! ### The kernel on a box -/

theorem combDefect_sub_comm (u v : ℝ) : combDefect (u - v) = combDefect (v - u) := by
  rw [← combDefect_neg, neg_sub]

/-- Linearity of a double integral over a box, for continuous kernels. -/
theorem integral_integral_two_mul_sub {F G : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F))
    (hG : Continuous (Function.uncurry G)) (a b : ℝ) :
    ∫ u in a..b, ∫ v in a..b, (2 * F u v - G u v) =
      2 * (∫ u in a..b, ∫ v in a..b, F u v) - ∫ u in a..b, ∫ v in a..b, G u v := by
  have hFu : ∀ u : ℝ, Continuous fun v : ℝ => F u v := fun u =>
    hF.comp (continuous_const.prodMk continuous_id)
  have hGu : ∀ u : ℝ, Continuous fun v : ℝ => G u v := fun u =>
    hG.comp (continuous_const.prodMk continuous_id)
  have hIF : Continuous fun u : ℝ => ∫ v in a..b, F u v :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF a b
  have hIG : Continuous fun u : ℝ => ∫ v in a..b, G u v :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG a b
  have hinner : ∀ u : ℝ, ∫ v in a..b, (2 * F u v - G u v) =
      2 * (∫ v in a..b, F u v) - ∫ v in a..b, G u v := fun u => by
    have i1 : IntervalIntegrable (fun v => 2 * F u v) volume a b :=
      ((hFu u).const_mul 2).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun v => G u v) volume a b := (hGu u).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul]
  have i3 : IntervalIntegrable (fun u => 2 * ∫ v in a..b, F u v) volume a b :=
    (hIF.const_mul 2).intervalIntegrable _ _
  have i4 : IntervalIntegrable (fun u => ∫ v in a..b, G u v) volume a b :=
    hIG.intervalIntegrable _ _
  rw [intervalIntegral.integral_congr (g := fun u => 2 * (∫ v in a..b, F u v) -
      ∫ v in a..b, G u v) (fun u _ => hinner u),
    intervalIntegral.integral_sub i3 i4, intervalIntegral.integral_const_mul]

/-- **The kernel between the combs on a box**, split into its rows and its mixed part. -/
theorem integral_combDefect_mul_sq_sub {g : ℝ → ℝ} (hg : Continuous g) {c : ℝ} (hc : 0 ≤ c) :
    ∫ u in (0 : ℝ)..c, ∫ v in (0 : ℝ)..c, combDefect (u - v) * (g u - g v) ^ 2 =
      2 * (∫ u in (0 : ℝ)..c, g u ^ 2 * ∫ v in (0 : ℝ)..c, combDefect (u - v)) -
        2 * ∫ u in (0 : ℝ)..c, ∫ v in (0 : ℝ)..c, g u * g v * combDefect (u - v) := by
  have hD : Continuous (Function.uncurry fun u v : ℝ => combDefect (u - v)) :=
    continuous_combDefect.comp (continuous_fst.sub continuous_snd)
  have hA : Continuous (Function.uncurry fun u v : ℝ => g u ^ 2 * combDefect (u - v)) :=
    ((hg.comp continuous_fst).pow 2).mul hD
  have hB : Continuous (Function.uncurry fun u v : ℝ => g v ^ 2 * combDefect (u - v)) :=
    ((hg.comp continuous_snd).pow 2).mul hD
  have hC : Continuous (Function.uncurry fun u v : ℝ => g u * g v * combDefect (u - v)) :=
    ((hg.comp continuous_fst).mul (hg.comp continuous_snd)).mul hD
  have hAB : Continuous (Function.uncurry fun u v : ℝ =>
      g u ^ 2 * combDefect (u - v) + g v ^ 2 * combDefect (u - v)) := hA.add hB
  -- the integrand is `(A + B) − 2C`
  have h1 : ∫ u in (0 : ℝ)..c, ∫ v in (0 : ℝ)..c, combDefect (u - v) * (g u - g v) ^ 2 =
      (∫ u in (0 : ℝ)..c, ∫ v in (0 : ℝ)..c,
          (g u ^ 2 * combDefect (u - v) + g v ^ 2 * combDefect (u - v))) -
        2 * ∫ u in (0 : ℝ)..c, ∫ v in (0 : ℝ)..c, g u * g v * combDefect (u - v) := by
    have h := integral_integral_two_mul_sub hC hAB 0 c
    have e : ∫ u in (0 : ℝ)..c, ∫ v in (0 : ℝ)..c, combDefect (u - v) * (g u - g v) ^ 2 =
        -∫ u in (0 : ℝ)..c, ∫ v in (0 : ℝ)..c, (2 * (g u * g v * combDefect (u - v)) -
          (g u ^ 2 * combDefect (u - v) + g v ^ 2 * combDefect (u - v))) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun u _ => ?_
      show (∫ v in (0 : ℝ)..c, combDefect (u - v) * (g u - g v) ^ 2) =
        -∫ v in (0 : ℝ)..c, (2 * (g u * g v * combDefect (u - v)) -
          (g u ^ 2 * combDefect (u - v) + g v ^ 2 * combDefect (u - v)))
      rw [← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_congr fun v _ => by ring
    rw [e, h]
    ring
  -- the two halves of `A + B` are equal after exchanging the variables
  have hAu : ∀ u : ℝ, Continuous fun v : ℝ => g u ^ 2 * combDefect (u - v) := fun u =>
    hA.comp (continuous_const.prodMk continuous_id)
  have hBu : ∀ u : ℝ, Continuous fun v : ℝ => g v ^ 2 * combDefect (u - v) := fun u =>
    hB.comp (continuous_const.prodMk continuous_id)
  have hIA : Continuous fun u : ℝ => ∫ v in (0 : ℝ)..c, g u ^ 2 * combDefect (u - v) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hA 0 c
  have hIB : Continuous fun u : ℝ => ∫ v in (0 : ℝ)..c, g v ^ 2 * combDefect (u - v) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hB 0 c
  have h2 : ∫ u in (0 : ℝ)..c, ∫ v in (0 : ℝ)..c,
        (g u ^ 2 * combDefect (u - v) + g v ^ 2 * combDefect (u - v)) =
      (∫ u in (0 : ℝ)..c, ∫ v in (0 : ℝ)..c, g u ^ 2 * combDefect (u - v)) +
        ∫ u in (0 : ℝ)..c, ∫ v in (0 : ℝ)..c, g v ^ 2 * combDefect (u - v) := by
    rw [← intervalIntegral.integral_add (hIA.intervalIntegrable _ _) (hIB.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun u _ => ?_
    exact intervalIntegral.integral_add ((hAu u).intervalIntegrable _ _)
      ((hBu u).intervalIntegrable _ _)
  have h3 : ∫ u in (0 : ℝ)..c, ∫ v in (0 : ℝ)..c, g u ^ 2 * combDefect (u - v) =
      ∫ u in (0 : ℝ)..c, g u ^ 2 * ∫ v in (0 : ℝ)..c, combDefect (u - v) :=
    intervalIntegral.integral_congr fun u _ => intervalIntegral.integral_const_mul _ _
  have h4 : ∫ u in (0 : ℝ)..c, ∫ v in (0 : ℝ)..c, g v ^ 2 * combDefect (u - v) =
      ∫ u in (0 : ℝ)..c, g u ^ 2 * ∫ v in (0 : ℝ)..c, combDefect (u - v) := by
    rw [_root_.RHTower.interval_integral_swap_of_continuous hc hc
      (F := fun u v => g v ^ 2 * combDefect (u - v)) hB]
    refine intervalIntegral.integral_congr fun v _ => ?_
    show (∫ u in (0 : ℝ)..c, g v ^ 2 * combDefect (u - v)) =
      g v ^ 2 * ∫ u in (0 : ℝ)..c, combDefect (v - u)
    rw [intervalIntegral.integral_const_mul]
    congr 1
    exact intervalIntegral.integral_congr fun u _ => combDefect_sub_comm u v
  rw [h1, h2, h3, h4]
  ring

/-! ### Halving the logarithmic coordinate -/

theorem integral_comp_div_two (φ : ℝ → ℝ) (c : ℝ) :
    ∫ s in (0 : ℝ)..(2 * c), φ (s / 2) = 2 * ∫ u in (0 : ℝ)..c, φ u := by
  rw [intervalIntegral.integral_comp_div φ two_ne_zero, zero_div,
    mul_div_cancel_left₀ c two_ne_zero, smul_eq_mul]

theorem contDiff_comp_div_two {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 fun s => g (s / 2) :=
  hg.comp (contDiff_id.div_const 2)

theorem hasCompactSupport_comp_div_two {g : ℝ → ℝ} (hgc : HasCompactSupport g) :
    HasCompactSupport fun s => g (s / 2) :=
  hgc.comp_homeomorph (Homeomorph.mulRight₀ (2⁻¹ : ℝ) (by norm_num))

/-! ### Weil's form of the halved packet -/

/-- **Weil's archimedean form of the packet `s ↦ g(s/2)`** against that of `g`: twice the form of
`g`, minus twice the kernel between the combs on `g`, minus `2 log 2` times the mass. -/
theorem weilArchRe_sub_pole_comp_div_two {g : ℝ → ℝ} {R : ℕ} {B L δ c : ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsuppR : ∀ u : ℝ, (R : ℝ) ≤ |u| → g u = 0) (hB : ∀ u, |g u| ≤ B)
    (hL : ∀ u v, |g u - g v| ≤ L * |u - v|) (hδ : 0 < δ) (hδc : δ ≤ c)
    (hsupp : ∀ u, u ≤ δ ∨ c - δ ≤ u → g u = 0) :
    _root_.RHTower.WeilOneSided.weilArchRe
          (EF.weilTest (packetTest (fun s => g (s / 2)) (contDiff_comp_div_two hg)
              (hasCompactSupport_comp_div_two hgc)).1
            (packetTest (fun s => g (s / 2)) (contDiff_comp_div_two hg)
              (hasCompactSupport_comp_div_two hgc)).1) -
        (_root_.RHTower.weilPoleTerm
          (EF.weilTest (packetTest (fun s => g (s / 2)) (contDiff_comp_div_two hg)
              (hasCompactSupport_comp_div_two hgc)).1
            (packetTest (fun s => g (s / 2)) (contDiff_comp_div_two hg)
              (hasCompactSupport_comp_div_two hgc)).1)).re =
      2 * (_root_.RHTower.WeilOneSided.weilArchRe
            (EF.weilTest (packetTest g hg hgc).1 (packetTest g hg hgc).1) -
          (_root_.RHTower.weilPoleTerm
            (EF.weilTest (packetTest g hg hgc).1 (packetTest g hg hgc).1)).re) -
        2 * (∫ u in (0 : ℝ)..c, ∫ v in (0 : ℝ)..c, g u * g v * combDefect (u - v)) -
        2 * Real.log 2 * ∫ u in (0 : ℝ)..c, g u ^ 2 := by
  have hcont := hg.continuous
  have hc : 0 < c := hδ.trans_le hδc
  have hf := contDiff_comp_div_two hg
  have hfc := hasCompactSupport_comp_div_two hgc
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hsuppRf : ∀ s : ℝ, ((2 * R : ℕ) : ℝ) ≤ |s| → (fun s => g (s / 2)) s = 0 := fun s hs => by
    refine hsuppR _ ?_
    rw [abs_div, abs_of_pos h2pos]
    push_cast at hs
    linarith
  have hBf : ∀ s, |(fun s => g (s / 2)) s| ≤ B := fun s => hB _
  have hLf : ∀ s t, |(fun s => g (s / 2)) s - (fun s => g (s / 2)) t| ≤ L / 2 * |s - t| :=
    fun s t => by
      have h := hL (s / 2) (t / 2)
      have e : s / 2 - t / 2 = (s - t) / 2 := by ring
      rw [e, abs_div, abs_of_pos h2pos] at h
      have e' : L * (|s - t| / 2) = L / 2 * |s - t| := by ring
      rw [e'] at h
      exact h
  have hsuppf : ∀ s, s ≤ 2 * δ ∨ 2 * c - 2 * δ ≤ s → (fun s => g (s / 2)) s = 0 := fun s hs =>
    hsupp _ (hs.imp (fun h => by linarith) (fun h => by linarith))
  have hweil_g := weilArchRe_sub_pole_packet hg hgc hsuppR hB hL
  have hbox_g := integral_levyJump_eq_window hcont hsuppR hB hL hδ hδc hsupp
  have hmass_g := packetAutocorr_zero_eq_integral_window (f := g) (c := c) hδ hsupp
  have hweil_f := weilArchRe_sub_pole_packet hf hfc hsuppRf hBf hLf
  have hbox_f := integral_levyJump_eq_window hf.continuous hsuppRf hBf hLf
    (by positivity : 0 < 2 * δ) (by linarith : 2 * δ ≤ 2 * c) hsuppf
  have hmass_f := packetAutocorr_zero_eq_integral_window (f := fun s => g (s / 2)) (c := 2 * c)
    (by positivity : 0 < 2 * δ) hsuppf
  -- the mass, the box and the tails of the halved packet, on the window of `g`
  have hM : ∫ s in (0 : ℝ)..(2 * c), g (s / 2) ^ 2 =
      2 * ∫ u in (0 : ℝ)..c, g u ^ 2 := integral_comp_div_two (fun u => g u ^ 2) c
  have hin : ∀ u : ℝ, ∫ t in (0 : ℝ)..(2 * c), ω |2 * u - t| * (g u - g (t / 2)) ^ 2 =
      2 * ∫ v in (0 : ℝ)..c, ω |2 * u - 2 * v| * (g u - g v) ^ 2 := fun u => by
    rw [← integral_comp_div_two (fun v => ω |2 * u - 2 * v| * (g u - g v) ^ 2) c]
    refine intervalIntegral.integral_congr fun t _ => ?_
    show ω |2 * u - t| * (g u - g (t / 2)) ^ 2 =
      ω |2 * u - 2 * (t / 2)| * (g u - g (t / 2)) ^ 2
    rw [show 2 * (t / 2) = t by ring]
  have hBox : ∫ s in (0 : ℝ)..(2 * c), ∫ t in (0 : ℝ)..(2 * c),
        boxKernel (fun s => g (s / 2)) s t =
      4 * ∫ u in (0 : ℝ)..c, ∫ v in (0 : ℝ)..c, ω |2 * u - 2 * v| * (g u - g v) ^ 2 := by
    have e1 : ∫ s in (0 : ℝ)..(2 * c), ∫ t in (0 : ℝ)..(2 * c),
          boxKernel (fun s => g (s / 2)) s t =
        ∫ s in (0 : ℝ)..(2 * c), ∫ t in (0 : ℝ)..(2 * c),
          ω |2 * (s / 2) - t| * (g (s / 2) - g (t / 2)) ^ 2 :=
      intervalIntegral.integral_congr fun s _ => by
        show (∫ t in (0 : ℝ)..(2 * c), boxKernel (fun s => g (s / 2)) s t) =
          ∫ t in (0 : ℝ)..(2 * c), ω |2 * (s / 2) - t| * (g (s / 2) - g (t / 2)) ^ 2
        refine intervalIntegral.integral_congr fun t _ => ?_
        show ω |s - t| * (g (s / 2) - g (t / 2)) ^ 2 =
          ω |2 * (s / 2) - t| * (g (s / 2) - g (t / 2)) ^ 2
        rw [show 2 * (s / 2) = s by ring]
    have e2 : ∫ s in (0 : ℝ)..(2 * c), ∫ t in (0 : ℝ)..(2 * c),
          ω |2 * (s / 2) - t| * (g (s / 2) - g (t / 2)) ^ 2 =
        2 * ∫ u in (0 : ℝ)..c, ∫ t in (0 : ℝ)..(2 * c),
          ω |2 * u - t| * (g u - g (t / 2)) ^ 2 :=
      integral_comp_div_two
        (fun u => ∫ t in (0 : ℝ)..(2 * c), ω |2 * u - t| * (g u - g (t / 2)) ^ 2) c
    have e3 : ∫ u in (0 : ℝ)..c, ∫ t in (0 : ℝ)..(2 * c),
          ω |2 * u - t| * (g u - g (t / 2)) ^ 2 =
        ∫ u in (0 : ℝ)..c, 2 * ∫ v in (0 : ℝ)..c, ω |2 * u - 2 * v| * (g u - g v) ^ 2 :=
      intervalIntegral.integral_congr fun u _ => hin u
    rw [e1, e2, e3, intervalIntegral.integral_const_mul]
    ring
  have hTail : ∫ s in (0 : ℝ)..(2 * c), g (s / 2) ^ 2 *
        (Ω (max (2 * c - s) (2 * δ)) + Ω (max s (2 * δ))) =
      2 * ∫ u in (0 : ℝ)..c, g u ^ 2 *
        (Ω (max (2 * c - 2 * u) (2 * δ)) + Ω (max (2 * u) (2 * δ))) := by
    rw [← integral_comp_div_two (fun u => g u ^ 2 *
      (Ω (max (2 * c - 2 * u) (2 * δ)) + Ω (max (2 * u) (2 * δ)))) c]
    refine intervalIntegral.integral_congr fun s _ => ?_
    show g (s / 2) ^ 2 * (Ω (max (2 * c - s) (2 * δ)) + Ω (max s (2 * δ))) =
      g (s / 2) ^ 2 * (Ω (max (2 * c - 2 * (s / 2)) (2 * δ)) + Ω (max (2 * (s / 2)) (2 * δ)))
    rw [show 2 * (s / 2) = s by ring]
  -- the two box kernels differ by the kernel between the combs
  have hΦ2 : Continuous (Function.uncurry fun u v : ℝ => ω |2 * u - 2 * v| * (g u - g v) ^ 2) := by
    have hmap : Continuous fun p : ℝ × ℝ => (2 * p.1, 2 * p.2) := by fun_prop
    have h := (continuous_boxKernel hf.continuous hLf).comp hmap
    refine h.congr fun p => ?_
    show ω |2 * p.1 - 2 * p.2| * (g (2 * p.1 / 2) - g (2 * p.2 / 2)) ^ 2 =
      ω |2 * p.1 - 2 * p.2| * (g p.1 - g p.2) ^ 2
    rw [mul_div_cancel_left₀ _ (two_ne_zero), mul_div_cancel_left₀ _ (two_ne_zero)]
  have hΦ1 : Continuous (Function.uncurry fun u v : ℝ => boxKernel g u v) :=
    continuous_boxKernel hcont hL
  have hpt : ∀ u v : ℝ, 2 * (ω |2 * u - 2 * v| * (g u - g v) ^ 2) - boxKernel g u v =
      combDefect (u - v) * (g u - g v) ^ 2 := by
    intro u v
    rcases eq_or_ne u v with rfl | hne
    · simp [boxKernel]
    · have hx : 0 < |u - v| := abs_pos.mpr (sub_ne_zero.mpr hne)
      have e : |2 * u - 2 * v| = 2 * |u - v| := by
        rw [← mul_sub, abs_mul, abs_of_pos h2pos]
      rw [boxKernel, e, ← combDefect_abs, combDefect_of_pos hx]
      ring
  have hF3 : 2 * (∫ u in (0 : ℝ)..c, ∫ v in (0 : ℝ)..c,
        ω |2 * u - 2 * v| * (g u - g v) ^ 2) -
        ∫ u in (0 : ℝ)..c, ∫ v in (0 : ℝ)..c, boxKernel g u v =
      ∫ u in (0 : ℝ)..c, ∫ v in (0 : ℝ)..c, combDefect (u - v) * (g u - g v) ^ 2 := by
    rw [← integral_integral_two_mul_sub hΦ2 hΦ1 0 c]
    exact intervalIntegral.integral_congr fun u _ =>
      intervalIntegral.integral_congr fun v _ => hpt u v
  have hF4 := integral_combDefect_mul_sq_sub hcont hc.le
  -- the rows of the kernel against the primitives of the two Lévy densities
  have hRow : ∀ u ∈ Set.uIcc (0 : ℝ) c,
      g u ^ 2 * (Ω (max (2 * c - 2 * u) (2 * δ)) + Ω (max (2 * u) (2 * δ))) -
          g u ^ 2 * (Ω (max (c - u) δ) + Ω (max u δ)) +
        g u ^ 2 * ∫ v in (0 : ℝ)..c, combDefect (u - v) = -Real.log 2 * g u ^ 2 := by
    intro u _
    by_cases h0 : g u = 0
    · rw [h0]
      ring
    · have h1 : δ < u := by
        by_contra h
        exact h0 (hsupp u (Or.inl (not_lt.mp h)))
      have h2 : u < c - δ := by
        by_contra h
        exact h0 (hsupp u (Or.inr (not_lt.mp h)))
      rw [max_eq_left (by linarith : 2 * δ ≤ 2 * c - 2 * u),
        max_eq_left (by linarith : 2 * δ ≤ 2 * u), max_eq_left (by linarith : δ ≤ c - u),
        max_eq_left h1.le, integral_combDefect_sub, integral_combDefect (hδ.trans h1),
        integral_combDefect (by linarith : 0 < c - u), show 2 * c - 2 * u = 2 * (c - u) by ring]
      ring
  have cT2 : Continuous fun u => g u ^ 2 *
      (Ω (max (2 * c - 2 * u) (2 * δ)) + Ω (max (2 * u) (2 * δ))) :=
    (hcont.pow 2).mul ((continuous_archLevyAntideriv_max
      (continuous_const.sub (continuous_const.mul continuous_id)) (by positivity)).add
      (continuous_archLevyAntideriv_max (continuous_const.mul continuous_id) (by positivity)))
  have cT : Continuous fun u => g u ^ 2 * (Ω (max (c - u) δ) + Ω (max u δ)) :=
    (hcont.pow 2).mul ((continuous_archLevyAntideriv_max
      (continuous_const.sub continuous_id) hδ).add
      (continuous_archLevyAntideriv_max continuous_id hδ))
  have cA : Continuous fun u => g u ^ 2 * ∫ v in (0 : ℝ)..c, combDefect (u - v) :=
    (hcont.pow 2).mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun u v => combDefect (u - v))
      (continuous_combDefect.comp (continuous_fst.sub continuous_snd)) 0 c)
  have hF5 : (∫ u in (0 : ℝ)..c, g u ^ 2 *
          (Ω (max (2 * c - 2 * u) (2 * δ)) + Ω (max (2 * u) (2 * δ)))) -
        (∫ u in (0 : ℝ)..c, g u ^ 2 * (Ω (max (c - u) δ) + Ω (max u δ))) +
        ∫ u in (0 : ℝ)..c, g u ^ 2 * ∫ v in (0 : ℝ)..c, combDefect (u - v) =
      -Real.log 2 * ∫ u in (0 : ℝ)..c, g u ^ 2 := by
    have i1 : IntervalIntegrable (fun u => g u ^ 2 *
        (Ω (max (2 * c - 2 * u) (2 * δ)) + Ω (max (2 * u) (2 * δ)))) volume 0 c :=
      cT2.intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun u => g u ^ 2 * (Ω (max (c - u) δ) + Ω (max u δ)))
        volume 0 c := cT.intervalIntegrable _ _
    have i12 : IntervalIntegrable (fun u => g u ^ 2 *
          (Ω (max (2 * c - 2 * u) (2 * δ)) + Ω (max (2 * u) (2 * δ))) -
        g u ^ 2 * (Ω (max (c - u) δ) + Ω (max u δ))) volume 0 c :=
      (cT2.sub cT).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun u => g u ^ 2 * ∫ v in (0 : ℝ)..c, combDefect (u - v))
        volume 0 c := cA.intervalIntegrable _ _
    have hsum : ∫ u in (0 : ℝ)..c, (g u ^ 2 *
            (Ω (max (2 * c - 2 * u) (2 * δ)) + Ω (max (2 * u) (2 * δ))) -
          g u ^ 2 * (Ω (max (c - u) δ) + Ω (max u δ)) +
          g u ^ 2 * ∫ v in (0 : ℝ)..c, combDefect (u - v)) =
        (∫ u in (0 : ℝ)..c, g u ^ 2 *
            (Ω (max (2 * c - 2 * u) (2 * δ)) + Ω (max (2 * u) (2 * δ)))) -
          (∫ u in (0 : ℝ)..c, g u ^ 2 * (Ω (max (c - u) δ) + Ω (max u δ))) +
          ∫ u in (0 : ℝ)..c, g u ^ 2 * ∫ v in (0 : ℝ)..c, combDefect (u - v) := by
      rw [intervalIntegral.integral_add i12 i3, intervalIntegral.integral_sub i1 i2]
    rw [← hsum, intervalIntegral.integral_congr hRow, intervalIntegral.integral_const_mul]
  rw [hweil_f, hbox_f, hmass_f, hM, hBox, hTail, hweil_g, hbox_g, hmass_g]
  linarith [hF3, hF4, hF5]

/-- **The packets on the comb of squares carry Weil's archimedean form.** For a packet `g`
supported in `[log 3, log K]`, sampled at `log(n/N)` on the squares `n²`, the pairing of the jets
with the masses `2/n`, minus the masses times `log(n/4π)`, tends to minus the archimedean part of
Weil's functional, without the pole, of the packet `s ↦ g(s/2)`: the packet in the logarithmic
coordinate of the squares. -/
theorem tendsto_squareForm {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    {K : ℕ} (hK : 1 ≤ K) (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → g u = 0) :
    Tendsto (squareForm g (3 * K)) atTop
      (𝓝 (-(_root_.RHTower.WeilOneSided.weilArchRe
            (EF.weilTest (packetTest (fun s => g (s / 2)) (contDiff_comp_div_two hg)
                (hasCompactSupport_comp_div_two hgc)).1
              (packetTest (fun s => g (s / 2)) (contDiff_comp_div_two hg)
                (hasCompactSupport_comp_div_two hgc)).1) -
          (_root_.RHTower.weilPoleTerm
            (EF.weilTest (packetTest (fun s => g (s / 2)) (contDiff_comp_div_two hg)
                (hasCompactSupport_comp_div_two hgc)).1
              (packetTest (fun s => g (s / 2)) (contDiff_comp_div_two hg)
                (hasCompactSupport_comp_div_two hgc)).1)).re))) := by
  have hcont := hg.continuous
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support hgc
  obtain ⟨C, hC⟩ := hg.lipschitzWith_of_hasCompactSupport hgc (by norm_num)
  have hB' : ∀ u, |g u| ≤ B := fun u => by
    rw [← Real.norm_eq_abs]
    exact hB u
  have hL : ∀ u v, |g u - g v| ≤ (C : ℝ) * |u - v| := fun u v => by
    have h := hC.dist_le_mul u v
    rwa [Real.dist_eq, Real.dist_eq] at h
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hδ : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have h3K : ((3 * K : ℕ) : ℝ) = 3 * K := by
    push_cast
    ring
  have hδc : Real.log 3 ≤ Real.log (1 + ((3 * K : ℕ) : ℝ)) := by
    rw [h3K]
    exact Real.log_le_log (by norm_num) (by linarith)
  have hcK : Real.log K ≤ Real.log (1 + ((3 * K : ℕ) : ℝ)) - Real.log 3 := by
    rw [h3K, ← Real.log_div (by linarith) (by norm_num)]
    exact Real.log_le_log (by linarith) (by
      rw [le_div_iff₀ (by norm_num)]
      linarith)
  have hsuppW : ∀ u, u ≤ Real.log 3 ∨ Real.log (1 + ((3 * K : ℕ) : ℝ)) - Real.log 3 ≤ u →
      g u = 0 := fun u hu => hsupp u (hu.imp id fun h => hcK.trans h)
  have hsuppR : ∀ u : ℝ, (K : ℝ) ≤ |u| → g u = 0 := fun u hu => by
    rcases le_abs.mp hu with h | h
    · exact hsupp u (Or.inr ((Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)))
    · exact hsupp u (Or.inl (by linarith))
  have hid := weilArchRe_sub_pole_comp_div_two hg hgc hsuppR hB' hL hδ hδc hsuppW
  have hlim := tendsto_squareForm_defect hg hgc hK hsupp
  rw [hid]
  convert hlim using 2
  ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
