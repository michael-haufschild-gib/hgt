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

The counterterm `log(n/4π)` is the logarithm of the density `n/2` of the comb over `2π`.
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

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
