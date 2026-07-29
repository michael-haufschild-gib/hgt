/-
# Real-slice dynamics: `K_c ∩ ℝ = [−β, β]` for real `c ∈ [−2, 1/4]` (OP4 prep A)

The elementary real-parameter facts behind the explicit imaginary-axis tip of open problem 04:
for real `c ∈ [−2, 1/4]` the interval `[−β, β]` (with `β = betaFixed c` the larger fixed point) is
forward invariant, real points beyond it escape monotonically, and hence a real point lies in the
filled Julia set exactly when `|x| ≤ β`.  In particular `0 ∈ K_c`, so the real slice `[−2, 1/4]`
lies in the Mandelbrot set.  Escape uses no growth estimate: a bounded increasing orbit would
converge to a real fixed point `> β`, and `β` is the largest one.  Extends the `c ≤ 0` bricks of
`DendriteTip.lean` to `c ≤ 1/4`.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.DendriteTip
import Mathlib.Topology.Order.MonotoneConvergence

open Set Metric Bornology Filter Topology

namespace Bottcher

/-- The real quadratic map `x ↦ x² + c`. -/
def quadraticReal (c : ℝ) : ℝ → ℝ := fun x => x ^ 2 + c

@[simp] theorem quadraticReal_apply (c x : ℝ) : quadraticReal c x = x ^ 2 + c := rfl

/-- The complex orbit of a real point is the real orbit. -/
theorem quadratic_iterate_ofReal (c x : ℝ) (n : ℕ) :
    (quadratic (c : ℂ))^[n] (x : ℂ) = (((quadraticReal c)^[n] x : ℝ) : ℂ) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        quadratic_apply, quadraticReal_apply]
      push_cast
      ring

theorem betaFixed_pos (c : ℝ) : 0 < betaFixed c := by
  unfold betaFixed
  have := Real.sqrt_nonneg (1 - 4 * c)
  linarith

/-- The fixed-point equation `β² + c = β`, on the full real slice `c ≤ 1/4`
(generalizing `betaFixed_sq` from `c ≤ 0`). -/
theorem betaFixed_sq' {c : ℝ} (hc4 : c ≤ 1 / 4) :
    betaFixed c ^ 2 + c = betaFixed c := by
  unfold betaFixed
  have h1 : Real.sqrt (1 - 4 * c) ^ 2 = 1 - 4 * c := Real.sq_sqrt (by linarith)
  linear_combination (1 / 4 : ℝ) * h1

theorem betaFixed_le_two {c : ℝ} (hc2 : -2 ≤ c) (hc4 : c ≤ 1 / 4) :
    betaFixed c ≤ 2 := by
  unfold betaFixed
  have hs : Real.sqrt (1 - 4 * c) ^ 2 = 1 - 4 * c := Real.sq_sqrt (by linarith)
  have hsnn := Real.sqrt_nonneg (1 - 4 * c)
  by_contra hcon
  push Not at hcon
  nlinarith

/-- `−β ≤ c`: the interval's lower endpoint is not overshot by the critical value. -/
theorem betaFixed_add_nonneg {c : ℝ} (hc2 : -2 ≤ c) (hc4 : c ≤ 1 / 4) :
    0 ≤ betaFixed c + c := by
  have h1 := betaFixed_sq' hc4
  have h2 := betaFixed_le_two hc2 hc4
  have h3 := betaFixed_pos c
  nlinarith [mul_nonneg h3.le (sub_nonneg.mpr h2)]

/-- **Forward invariance** of `[−β, β]` for real `c ∈ [−2, 1/4]`. -/
theorem abs_quadraticReal_le {c x : ℝ} (hc2 : -2 ≤ c) (hc4 : c ≤ 1 / 4)
    (hx : |x| ≤ betaFixed c) : |quadraticReal c x| ≤ betaFixed c := by
  have hβ := betaFixed_sq' hc4
  have hβc := betaFixed_add_nonneg hc2 hc4
  have hx2 : x ^ 2 ≤ betaFixed c ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rwa [sq_abs] at h
  rw [quadraticReal_apply, abs_le]
  constructor
  · nlinarith [sq_nonneg x]
  · nlinarith

/-- A real point of the invariant interval lies in the filled Julia set. -/
theorem real_mem_filledJulia_of_abs_le {c x : ℝ} (hc2 : -2 ≤ c) (hc4 : c ≤ 1 / 4)
    (hx : |x| ≤ betaFixed c) : (x : ℂ) ∈ filledJulia (c : ℂ) := by
  have horb : ∀ n, |(quadraticReal c)^[n] x| ≤ betaFixed c := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact abs_quadraticReal_le hc2 hc4 ih
  rw [mem_filledJulia_iff]
  refine isBounded_iff_forall_norm_le.mpr ⟨betaFixed c, ?_⟩
  rintro w ⟨n, rfl⟩
  dsimp only
  rw [quadratic_iterate_ofReal, Complex.norm_real, Real.norm_eq_abs]
  exact horb n

/-- **Strict increase beyond `β`**: for `c ≤ 1/4` and `x > β`, `f_c(x) > x`. -/
theorem lt_quadraticReal_of_betaFixed_lt {c x : ℝ} (hc4 : c ≤ 1 / 4)
    (hx : betaFixed c < x) : x < quadraticReal c x := by
  unfold betaFixed at hx
  set s := Real.sqrt (1 - 4 * c) with hsdef
  have hs : s ^ 2 = 1 - 4 * c := Real.sq_sqrt (by linarith)
  have hsnn : 0 ≤ s := Real.sqrt_nonneg _
  have h1 : (0 : ℝ) < 2 * x - 1 - s := by linarith
  have h2 : (0 : ℝ) < 2 * x - 1 + s := by linarith
  rw [quadraticReal_apply]
  nlinarith [mul_pos h1 h2]

/-- **Escape beyond `β`** (no growth estimate): a real point `x > β` leaves the filled Julia set —
a bounded orbit would be increasing and converge to a fixed point `> β`, but every real fixed
point is `≤ β`. -/
theorem not_mem_filledJulia_of_betaFixed_lt {c x : ℝ} (hc4 : c ≤ 1 / 4)
    (hx : betaFixed c < x) : (x : ℂ) ∉ filledJulia (c : ℂ) := by
  intro hmem
  set a : ℕ → ℝ := fun n => (quadraticReal c)^[n] x with hadef
  have hgt : ∀ n, betaFixed c < a n := by
    intro n
    induction n with
    | zero => simpa [hadef] using hx
    | succ m ih =>
        have hstep : a m < quadraticReal c (a m) := lt_quadraticReal_of_betaFixed_lt hc4 ih
        have hsucc : a (m + 1) = quadraticReal c (a m) :=
          Function.iterate_succ_apply' (quadraticReal c) m x
        rw [hsucc]
        exact ih.trans hstep
  have hmono : Monotone a := by
    refine monotone_nat_of_le_succ fun n => ?_
    have hsucc : a (n + 1) = quadraticReal c (a n) :=
      Function.iterate_succ_apply' (quadraticReal c) n x
    rw [hsucc]
    exact (lt_quadraticReal_of_betaFixed_lt hc4 (hgt n)).le
  have hbdd : BddAbove (Set.range a) := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp ((mem_filledJulia_iff _ _).mp hmem)
    refine ⟨C, ?_⟩
    rintro w ⟨n, rfl⟩
    have h := hC _ ⟨n, rfl⟩
    dsimp only at h
    rw [quadratic_iterate_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hL : Tendsto a atTop (𝓝 (⨆ n, a n)) := tendsto_atTop_ciSup hmono hbdd
  have hcont : Continuous (quadraticReal c) := by
    unfold quadraticReal
    fun_prop
  have hL2 : Tendsto (fun n => quadraticReal c (a n)) atTop
      (𝓝 (quadraticReal c (⨆ n, a n))) := (hcont.tendsto _).comp hL
  have hshift : Tendsto (fun n => quadraticReal c (a n)) atTop (𝓝 (⨆ n, a n)) := by
    have h := hL.comp (tendsto_add_atTop_nat 1)
    have heq : (fun n => a (n + 1)) = fun n => quadraticReal c (a n) := by
      funext n
      exact Function.iterate_succ_apply' (quadraticReal c) n x
    rwa [show a ∘ (fun n => n + 1) = fun n => a (n + 1) from rfl, heq] at h
  have hfix : quadraticReal c (⨆ n, a n) = ⨆ n, a n := tendsto_nhds_unique hL2 hshift
  have hβL : betaFixed c < ⨆ n, a n := (hgt 0).trans_le (le_ciSup hbdd 0)
  have hcontra := lt_quadraticReal_of_betaFixed_lt hc4 hβL
  rw [hfix] at hcontra
  exact lt_irrefl _ hcontra

/-- **Escape below `−β`**: one step maps `x < −β` beyond `β`. -/
theorem not_mem_filledJulia_of_lt_neg_betaFixed {c x : ℝ} (hc4 : c ≤ 1 / 4)
    (hx : x < -betaFixed c) : (x : ℂ) ∉ filledJulia (c : ℂ) := by
  intro hmem
  rw [mem_filledJulia_iff_quadratic_mem] at hmem
  have hcast : quadratic (c : ℂ) (x : ℂ) = ((quadraticReal c x : ℝ) : ℂ) := by
    rw [quadratic_apply, quadraticReal_apply]
    push_cast
    ring
  rw [hcast] at hmem
  have hβ := betaFixed_sq' hc4
  have hβpos := betaFixed_pos c
  have hgt : betaFixed c < quadraticReal c x := by
    rw [quadraticReal_apply]
    nlinarith
  exact not_mem_filledJulia_of_betaFixed_lt hc4 hgt hmem

/-- **The real slice of the filled Julia set**: for real `c ∈ [−2, 1/4]`,
`x ∈ K_c ↔ |x| ≤ β`, i.e. `K_c ∩ ℝ = [−β, β]`. -/
theorem real_mem_filledJulia_iff {c x : ℝ} (hc2 : -2 ≤ c) (hc4 : c ≤ 1 / 4) :
    (x : ℂ) ∈ filledJulia (c : ℂ) ↔ |x| ≤ betaFixed c := by
  refine ⟨fun hmem => ?_, real_mem_filledJulia_of_abs_le hc2 hc4⟩
  by_contra hcon
  push Not at hcon
  rcases lt_abs.mp hcon with h | h
  · exact not_mem_filledJulia_of_betaFixed_lt hc4 h hmem
  · exact not_mem_filledJulia_of_lt_neg_betaFixed hc4 (by linarith) hmem

/-- **The real slice `[−2, 1/4]` lies in the Mandelbrot set**: the critical orbit of a real
parameter stays in the invariant interval. -/
theorem real_mem_mandelbrot {c : ℝ} (hc2 : -2 ≤ c) (hc4 : c ≤ 1 / 4) :
    (c : ℂ) ∈ mandelbrot := by
  have h0 : ((0 : ℝ) : ℂ) ∈ filledJulia (c : ℂ) :=
    real_mem_filledJulia_of_abs_le hc2 hc4 (by simpa using (betaFixed_pos c).le)
  simpa using! h0

end Bottcher
