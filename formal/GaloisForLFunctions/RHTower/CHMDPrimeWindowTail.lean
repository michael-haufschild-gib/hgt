import GaloisForLFunctions.RHTower.CHMDThetaHarmonicIdentity
import GaloisForLFunctions.RHTower.CHMDPrimeRowBound

/-!
# Prime shifts landing inside and outside a central window

The symmetric prime shift sum of Riemann's kernel splits into the shifts landing inside the
window `|u| ≤ R` and the shifts landing outside. The outside part is controlled by logarithmic
shells together with Chebyshev's square-root prefix bound: it is at most
`A r^{⌊R⌋} (e^{x/2} + e^{−x/2})` with a fixed `r < 1`. Hence, by the pointwise harmonic identity,
the prime jumps from any point `x` into a window of radius `R` carry the polar rate `cosh(x/2)` up
to a uniformly bounded archimedean correction and a relative error `O(r^R)`.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph ThetaSourceWard

/-- Indicator of the central window `|u| ≤ R`. -/
def nearInd (R u : ℝ) : ℝ := if |u| ≤ R then 1 else 0

/-- Indicator of the far field `|u| > R`. -/
def farInd (R u : ℝ) : ℝ := if |u| ≤ R then 0 else 1

theorem nearInd_nonneg (R u : ℝ) : 0 ≤ nearInd R u := by unfold nearInd; split_ifs <;> norm_num
theorem nearInd_le_one (R u : ℝ) : nearInd R u ≤ 1 := by unfold nearInd; split_ifs <;> norm_num
theorem farInd_nonneg (R u : ℝ) : 0 ≤ farInd R u := by unfold farInd; split_ifs <;> norm_num
theorem farInd_le_one (R u : ℝ) : farInd R u ≤ 1 := by unfold farInd; split_ifs <;> norm_num
theorem nearInd_add_farInd (R u : ℝ) : nearInd R u + farInd R u = 1 := by
  unfold nearInd farInd; split_ifs <;> norm_num
theorem nearInd_zero_or_one (R u : ℝ) : nearInd R u = 0 ∨ nearInd R u = 1 := by
  unfold nearInd; split_ifs <;> simp
theorem nearInd_neg (R u : ℝ) : nearInd R (-u) = nearInd R u := by simp [nearInd]
theorem farInd_neg (R u : ℝ) : farInd R (-u) = farInd R u := by simp [farInd]
theorem measurable_nearInd (R : ℝ) : Measurable (nearInd R) := by
  unfold nearInd
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const) measurable_const
    measurable_const
theorem nearInd_eq_one_of_le {R u : ℝ} (h : |u| ≤ R) : nearInd R u = 1 := by simp [nearInd, h]
theorem farInd_eq_zero_of_le {R u : ℝ} (h : |u| ≤ R) : farInd R u = 0 := by simp [farInd, h]
theorem farInd_eq_zero_of_nearInd_eq_one {R u : ℝ} (h : nearInd R u = 1) : farInd R u = 0 := by
  have := nearInd_add_farInd R u
  linarith

/-- The far field of radius `R` sees the polar rate at least `cosh(R/2)` relative to the kernel. -/
theorem theta_le_mass_div_cosh {R x : ℝ} (hR : 0 ≤ R) (hx : farInd R x = 1) :
    riemannKernelReal x ≤ massDensity x / Real.cosh (R / 2) := by
  unfold massDensity
  have hxR : R < |x| := by
    by_contra h
    rw [not_lt] at h
    rw [farInd_eq_zero_of_le h] at hx
    norm_num at hx
  have hc : Real.cosh (R / 2) ≤ Real.cosh (x / 2) := by
    rw [Real.cosh_le_cosh, abs_div, abs_div, abs_of_nonneg hR, abs_two]
    exact div_le_div_of_nonneg_right hxR.le (by norm_num)
  rw [le_div_iff₀ (Real.cosh_pos _)]
  exact mul_le_mul_of_nonneg_left hc (riemannKernelReal_pos x).le

/-! ## Cross and tail sums -/

/-- Prime shifts of the kernel landing inside the window. -/
def primeCross (R x : ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n *
    (riemannKernelReal (x + Real.log n) * nearInd R (x + Real.log n) +
      riemannKernelReal (x - Real.log n) * nearInd R (x - Real.log n))

/-- Prime shifts of the kernel landing outside the window. -/
def primeTail (R x : ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n *
    (riemannKernelReal (x + Real.log n) * farInd R (x + Real.log n) +
      riemannKernelReal (x - Real.log n) * farInd R (x - Real.log n))

theorem summable_primeCross (R x : ℝ) :
    Summable fun n : ℕ => vonMangoldtAtom n *
      (riemannKernelReal (x + Real.log n) * nearInd R (x + Real.log n) +
        riemannKernelReal (x - Real.log n) * nearInd R (x - Real.log n)) := by
  refine (summable_primeKernelSum x).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg (vonMangoldtAtom_nonneg n) (add_nonneg
      (mul_nonneg (riemannKernelReal_pos _).le (nearInd_nonneg _ _))
      (mul_nonneg (riemannKernelReal_pos _).le (nearInd_nonneg _ _)))
  · refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (vonMangoldtAtom_nonneg n)
    · exact mul_le_of_le_one_right (riemannKernelReal_pos _).le (nearInd_le_one _ _)
    · exact mul_le_of_le_one_right (riemannKernelReal_pos _).le (nearInd_le_one _ _)

theorem summable_primeTail (R x : ℝ) :
    Summable fun n : ℕ => vonMangoldtAtom n *
      (riemannKernelReal (x + Real.log n) * farInd R (x + Real.log n) +
        riemannKernelReal (x - Real.log n) * farInd R (x - Real.log n)) := by
  refine (summable_primeKernelSum x).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg (vonMangoldtAtom_nonneg n) (add_nonneg
      (mul_nonneg (riemannKernelReal_pos _).le (farInd_nonneg _ _))
      (mul_nonneg (riemannKernelReal_pos _).le (farInd_nonneg _ _)))
  · refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (vonMangoldtAtom_nonneg n)
    · exact mul_le_of_le_one_right (riemannKernelReal_pos _).le (farInd_le_one _ _)
    · exact mul_le_of_le_one_right (riemannKernelReal_pos _).le (farInd_le_one _ _)

theorem primeCross_add_primeTail (R x : ℝ) : primeCross R x + primeTail R x = primeKernelSum x := by
  unfold primeCross primeTail primeKernelSum
  rw [← (summable_primeCross R x).tsum_add (summable_primeTail R x)]
  apply tsum_congr
  intro n
  have h1 := nearInd_add_farInd R (x + Real.log n)
  have h2 := nearInd_add_farInd R (x - Real.log n)
  linear_combination vonMangoldtAtom n * (riemannKernelReal (x + Real.log n) * h1 +
    riemannKernelReal (x - Real.log n) * h2)

theorem primeCross_nonneg (R x : ℝ) : 0 ≤ primeCross R x :=
  tsum_nonneg fun n => mul_nonneg (vonMangoldtAtom_nonneg n) (add_nonneg
    (mul_nonneg (riemannKernelReal_pos _).le (nearInd_nonneg _ _))
    (mul_nonneg (riemannKernelReal_pos _).le (nearInd_nonneg _ _)))

theorem primeTail_nonneg (R x : ℝ) : 0 ≤ primeTail R x :=
  tsum_nonneg fun n => mul_nonneg (vonMangoldtAtom_nonneg n) (add_nonneg
    (mul_nonneg (riemannKernelReal_pos _).le (farInd_nonneg _ _))
    (mul_nonneg (riemannKernelReal_pos _).le (farInd_nonneg _ _)))

/-! ## The shell bound on the tail -/

/-- The geometric shell ratio. -/
def shellRatio : ℝ := Real.exp (-(7 / 2 : ℝ))

theorem shellRatio_nonneg : 0 ≤ shellRatio := (Real.exp_pos _).le
theorem shellRatio_lt_one : shellRatio < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
theorem one_sub_shellRatio_pos : 0 < 1 - shellRatio := by linarith [shellRatio_lt_one]

/-- Partial tail sums over shells of index at least `K`. -/
theorem sum_pow_shellRatio_le {K : ℕ} (T : Finset ℕ) (hT : ∀ k ∈ T, K ≤ k) :
    ∑ k ∈ T, shellRatio ^ k ≤ shellRatio ^ K / (1 - shellRatio) := by
  have hr0 := shellRatio_nonneg
  have hrs : Summable (fun j : ℕ => shellRatio ^ j) :=
    summable_geometric_of_lt_one hr0 shellRatio_lt_one
  have hsplit : ∀ k ∈ T, shellRatio ^ k = shellRatio ^ K * shellRatio ^ (k - K) := by
    intro k hk
    rw [← pow_add, Nat.add_sub_cancel' (hT k hk)]
  rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum]
  have hinj : Set.InjOn (fun k : ℕ => k - K) (T : Set ℕ) := by
    intro a ha b hb hab
    have ha' := hT a ha
    have hb' := hT b hb
    simp only at hab
    omega
  rw [← Finset.sum_image hinj]
  have hle : ∑ j ∈ T.image (fun k => k - K), shellRatio ^ j ≤ ∑' j : ℕ, shellRatio ^ j :=
    hrs.sum_le_tsum _ fun j _ => pow_nonneg hr0 j
  rw [tsum_geometric_of_lt_one hr0 shellRatio_lt_one] at hle
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hle (pow_nonneg hr0 K)

/-- One-sided tail: shifts `x − log n` landing outside the window. -/
theorem primeTail_minus_le {C : ℝ} (hC : 0 ≤ C)
    (hθ : ∀ x, riemannKernelReal x ≤ C * Real.exp (-(4 * |x|))) (R x : ℝ) :
    (∑' n : ℕ, vonMangoldtAtom n * (riemannKernelReal (x - Real.log n) * farInd R (x - Real.log n))) ≤
      (34 * C * Real.exp (1 / 2) * Real.exp (x / 2)) * (shellRatio ^ ⌊R⌋₊ / (1 - shellRatio)) := by
  classical
  have hnonneg (n : ℕ) : 0 ≤ vonMangoldtAtom n * (riemannKernelReal (x - Real.log n) *
      farInd R (x - Real.log n)) :=
    mul_nonneg (vonMangoldtAtom_nonneg n) (mul_nonneg (riemannKernelReal_pos _).le (farInd_nonneg _ _))
  set A : ℝ := 34 * C * Real.exp (1 / 2) * Real.exp (x / 2) with hA
  have hA0 : 0 ≤ A := by positivity
  refine Real.tsum_le_of_sum_le hnonneg fun s => ?_
  -- restrict to the far terms
  have hterm : ∀ n, vonMangoldtAtom n * (riemannKernelReal (x - Real.log n) * farInd R (x - Real.log n)) =
      if ¬ |x - Real.log n| ≤ R then vonMangoldtAtom n * riemannKernelReal (x - Real.log n) else 0 := by
    intro n
    unfold farInd
    split_ifs <;> ring
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  set s' : Finset ℕ := s.filter (fun n : ℕ => ¬ |x - Real.log n| ≤ R) with hs'
  let shell : ℕ → ℕ := fun n => ⌊|x - Real.log n|⌋₊
  rw [← Finset.sum_fiberwise_of_maps_to (fun n hn => Finset.mem_image_of_mem shell hn)]
  have hshell : ∀ k ∈ s'.image shell, ⌊R⌋₊ ≤ k := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    have hfar : ¬ |x - Real.log n| ≤ R := (Finset.mem_filter.mp hn).2
    exact Nat.floor_le_floor (le_of_lt (lt_of_not_ge hfar))
  calc
    _ ≤ ∑ k ∈ s'.image shell, A * shellRatio ^ k := by
      apply Finset.sum_le_sum
      intro k _
      exact prime_shell_bound hC hθ x k _ (fun n hn => (Finset.mem_filter.mp hn).2)
    _ = A * ∑ k ∈ s'.image shell, shellRatio ^ k := (Finset.mul_sum ..).symm
    _ ≤ A * (shellRatio ^ ⌊R⌋₊ / (1 - shellRatio)) :=
      mul_le_mul_of_nonneg_left (sum_pow_shellRatio_le _ hshell) hA0

/-- **Tail bound.** Prime shifts landing outside a window of radius `R` are exponentially small in
`R` relative to the polar rate. -/
theorem exists_primeTail_bound : ∃ A : ℝ, 0 ≤ A ∧ ∀ R x : ℝ,
    primeTail R x ≤ A * shellRatio ^ ⌊R⌋₊ * (Real.exp (x / 2) + Real.exp (-x / 2)) := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le
  refine ⟨34 * C * Real.exp (1 / 2) / (1 - shellRatio), by
    have := one_sub_shellRatio_pos; positivity, fun R x => ?_⟩
  have hplus : Summable fun n : ℕ => vonMangoldtAtom n *
      (riemannKernelReal (x + Real.log n) * farInd R (x + Real.log n)) := by
    refine (summable_primeTail R x).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · exact mul_nonneg (vonMangoldtAtom_nonneg n)
        (mul_nonneg (riemannKernelReal_pos _).le (farInd_nonneg _ _))
    · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right
        (mul_nonneg (riemannKernelReal_pos _).le (farInd_nonneg _ _))) (vonMangoldtAtom_nonneg n)
  have hminus : Summable fun n : ℕ => vonMangoldtAtom n *
      (riemannKernelReal (x - Real.log n) * farInd R (x - Real.log n)) := by
    refine (summable_primeTail R x).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · exact mul_nonneg (vonMangoldtAtom_nonneg n)
        (mul_nonneg (riemannKernelReal_pos _).le (farInd_nonneg _ _))
    · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left
        (mul_nonneg (riemannKernelReal_pos _).le (farInd_nonneg _ _))) (vonMangoldtAtom_nonneg n)
  have hsplit : primeTail R x =
      (∑' n : ℕ, vonMangoldtAtom n * (riemannKernelReal (x + Real.log n) * farInd R (x + Real.log n))) +
        ∑' n : ℕ, vonMangoldtAtom n * (riemannKernelReal (x - Real.log n) * farInd R (x - Real.log n)) := by
    unfold primeTail
    rw [← hplus.tsum_add hminus]
    apply tsum_congr
    intro n
    ring
  have hreflect : (∑' n : ℕ, vonMangoldtAtom n *
      (riemannKernelReal (x + Real.log n) * farInd R (x + Real.log n))) =
      ∑' n : ℕ, vonMangoldtAtom n * (riemannKernelReal (-x - Real.log n) * farInd R (-x - Real.log n)) := by
    apply tsum_congr
    intro n
    rw [show -x - Real.log n = -(x + Real.log n) by ring, WeilExcess.riemannKernelReal_neg, farInd_neg]
  have h1 := primeTail_minus_le hC0 hC R x
  have h2 := primeTail_minus_le hC0 hC R (-x)
  rw [hsplit, hreflect]
  have hr := one_sub_shellRatio_pos
  calc _ ≤ (34 * C * Real.exp (1 / 2) * Real.exp (-x / 2)) * (shellRatio ^ ⌊R⌋₊ / (1 - shellRatio)) +
        (34 * C * Real.exp (1 / 2) * Real.exp (x / 2)) * (shellRatio ^ ⌊R⌋₊ / (1 - shellRatio)) :=
        add_le_add h2 h1
    _ = _ := by
        field_simp
        ring

/-- Cosh form of the tail bound. -/
theorem primeTail_le_cosh {A : ℝ} (hA : ∀ R x : ℝ,
      primeTail R x ≤ A * shellRatio ^ ⌊R⌋₊ * (Real.exp (x / 2) + Real.exp (-x / 2)))
    (R x : ℝ) :
    primeTail R x ≤ 2 * A * shellRatio ^ ⌊R⌋₊ * Real.cosh (x / 2) := by
  have := hA R x
  rw [Real.cosh_eq]
  have h : Real.exp (-x / 2) = Real.exp (-(x / 2)) := by ring_nf
  rw [h] at this
  linarith

/-- The shell factor tends to zero. -/
theorem shellRatio_pow_floor_tendsto : Tendsto (fun R : ℝ => shellRatio ^ ⌊R⌋₊) atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one shellRatio_nonneg shellRatio_lt_one
  exact h.comp tendsto_nat_floor_atTop

end RHTower.CHMDPolar
