import GaloisForLFunctions.HTGeometry.ComplexArtanhSeries
import GaloisForLFunctions.HTGeometry.OddHarmonicBoundaryValue
import GaloisForLFunctions.RHTower.OddHarmonicExpConvergence
import Mathlib.Analysis.Complex.AbelLimit

/-!
# The odd harmonic coefficients as a power series

Abel's limit theorem is stated for a power series `∑ f n z^n` indexed by all of `ℕ`.  The odd
harmonic series is supported on the odd indices, so this module packages it as such a sequence and
records the two bridges the gluing needs:

* the partial sums over `range N` collapse to the odd-indexed partial sums over `range (N/2)`,
  so convergence transfers from `RHTower.exists_tendsto_sum_oddHarmonicExp`;
* inside the disc the generating function is the complex `artanh` of `x e^{iθ}`, by
  `GaloisForLFunctions.HTGeometry.hasSum_oddPow_div`.
-/

open Finset Filter Topology

namespace RHTower

/-- The odd harmonic coefficients `e^{inθ}/n`, supported on the odd indices. -/
noncomputable def oddExpCoeff (θ : ℝ) (n : ℕ) : ℂ :=
  if Odd n then Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I) / (n : ℂ) else 0

theorem oddExpCoeff_even {θ : ℝ} {n : ℕ} (hn : Even n) : oddExpCoeff θ n = 0 := by
  rw [oddExpCoeff, if_neg (Nat.not_odd_iff_even.mpr hn)]

theorem oddExpCoeff_two_mul_add_one (θ : ℝ) (k : ℕ) :
    oddExpCoeff θ (2 * k + 1)
      = Complex.exp (((2 * (k : ℝ) + 1) * θ : ℝ) * Complex.I) / (2 * (k : ℂ) + 1) := by
  rw [oddExpCoeff, if_pos ⟨k, rfl⟩]
  push_cast
  ring_nf

/-- **Partial sums collapse to the odd-indexed ones.** -/
theorem sum_range_oddExpCoeff (θ : ℝ) (N : ℕ) :
    ∑ i ∈ range N, oddExpCoeff θ i
      = ∑ k ∈ range (N / 2),
          Complex.exp (((2 * (k : ℝ) + 1) * θ : ℝ) * Complex.I) / (2 * (k : ℂ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      rcases Nat.even_or_odd N with hev | hod
      · have hhalf : (N + 1) / 2 = N / 2 := by obtain ⟨j, hj⟩ := hev; omega
        rw [hhalf, oddExpCoeff_even hev, add_zero]
      · obtain ⟨j, hj⟩ := hod
        have hhalf : (N + 1) / 2 = j + 1 := by omega
        have hhalf' : N / 2 = j := by omega
        rw [hhalf, hhalf', Finset.sum_range_succ, hj, oddExpCoeff_two_mul_add_one]

/-- Convergence of the coefficient partial sums: Abel's hypothesis. -/
theorem exists_tendsto_sum_range_oddExpCoeff {θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    ∃ L : ℂ, Tendsto (fun N => ∑ i ∈ range N, oddExpCoeff θ i) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := exists_tendsto_sum_oddHarmonicExp hθ
  refine ⟨L, ?_⟩
  have hhalf : Tendsto (fun N : ℕ => N / 2) atTop atTop :=
    Filter.tendsto_atTop_atTop.2 fun b => ⟨2 * b, fun n hn => by omega⟩
  have hcomp := hL.comp hhalf
  refine hcomp.congr fun N => ?_
  exact (sum_range_oddExpCoeff θ N).symm

/-- **The generating function inside the disc** is the complex `artanh` of `x e^{iθ}`. -/
theorem hasSum_oddExpCoeff_mul_pow {θ x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => oddExpCoeff θ n * (x : ℂ) ^ n)
      ((Complex.log (1 + (x : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        - Complex.log (1 - (x : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) / 2) := by
  set z : ℂ := (x : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) with hz
  have hxnorm : ‖(x : ℂ)‖ = x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
  have hnorm : ‖z‖ < 1 := by
    rw [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, hxnorm]
    exact hx1
  have hbase := GaloisForLFunctions.HTGeometry.hasSum_oddPow_div hnorm
  have hginj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b hab
    have h : 2 * a + 1 = 2 * b + 1 := hab
    omega
  have hzero : ∀ n ∉ Set.range (fun k : ℕ => 2 * k + 1),
      oddExpCoeff θ n * (x : ℂ) ^ n = 0 := by
    intro n hn
    have hev : Even n := by
      rcases Nat.even_or_odd n with h | h
      · exact h
      · exfalso
        obtain ⟨j, hj⟩ := h
        exact hn ⟨j, by show 2 * j + 1 = n; omega⟩
    rw [oddExpCoeff_even hev, zero_mul]
  have hterm : ∀ k : ℕ,
      oddExpCoeff θ (2 * k + 1) * (x : ℂ) ^ (2 * k + 1) = z ^ (2 * k + 1) / (2 * (k : ℂ) + 1) := by
    intro k
    have hrot : Complex.exp (((2 * (k : ℝ) + 1) * θ : ℝ) * Complex.I)
        = Complex.exp ((θ : ℂ) * Complex.I) ^ (2 * k + 1) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [oddExpCoeff_two_mul_add_one, hrot, hz, mul_pow]
    ring
  exact (hginj.hasSum_iff hzero).mp (hbase.congr_fun fun k => hterm k)

/-! ## Abel's limit theorem at the boundary point -/

/-- The interior generating function, as a function of the radius variable. -/
noncomputable def oddExpGen (θ : ℝ) (w : ℂ) : ℂ :=
  (Complex.log (1 + w * Complex.exp ((θ : ℂ) * Complex.I))
    - Complex.log (1 - w * Complex.exp ((θ : ℂ) * Complex.I))) / 2

theorem continuousAt_oddExpGen {θ : ℝ} (hθ : Real.sin θ ≠ 0) : ContinuousAt (oddExpGen θ) 1 := by
  have hadd : ContinuousAt (fun w : ℂ => 1 + w * Complex.exp ((θ : ℂ) * Complex.I)) 1 :=
    continuousAt_const.add (continuousAt_id.mul continuousAt_const)
  have hsub : ContinuousAt (fun w : ℂ => 1 - w * Complex.exp ((θ : ℂ) * Complex.I)) 1 :=
    continuousAt_const.sub (continuousAt_id.mul continuousAt_const)
  have hslitAdd : (1 : ℂ) + 1 * Complex.exp ((θ : ℂ) * Complex.I) ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
    rw [one_mul]
    exact GaloisForLFunctions.HTGeometry.re_one_add_exp_pos hθ
  have hslitSub : (1 : ℂ) - 1 * Complex.exp ((θ : ℂ) * Complex.I) ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
    rw [one_mul]
    exact GaloisForLFunctions.HTGeometry.re_one_sub_exp_pos hθ
  exact ((hadd.clog hslitAdd).sub (hsub.clog hslitSub)).div_const 2

/-- **The odd harmonic exponential series sums to the boundary value of `artanh`.**

Abel's limit theorem transports the interior identity
`GaloisForLFunctions.HTGeometry.hasSum_oddPow_div` to the unit circle: the boundary series
converges by the Dirichlet test, so its sum is the radial limit of the interior closed form, and
`Complex.log` is continuous at `1 ± e^{iθ}` because both points avoid the slit. -/
theorem tendsto_sum_oddHarmonicExp {θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    Tendsto (fun N => ∑ k ∈ range N,
        Complex.exp (((2 * (k : ℝ) + 1) * θ : ℝ) * Complex.I) / (2 * (k : ℝ) + 1))
      atTop (𝓝 ((Complex.log (1 + Complex.exp ((θ : ℂ) * Complex.I))
        - Complex.log (1 - Complex.exp ((θ : ℂ) * Complex.I))) / 2)) := by
  obtain ⟨L, hL0⟩ := exists_tendsto_sum_oddHarmonicExp hθ
  have hL : Tendsto (fun N => ∑ i ∈ range N, oddExpCoeff θ i) atTop (𝓝 L) := by
    have hhalf : Tendsto (fun N : ℕ => N / 2) atTop atTop :=
      Filter.tendsto_atTop_atTop.2 fun b => ⟨2 * b, fun n hn => by omega⟩
    exact (hL0.comp hhalf).congr fun N => (sum_range_oddExpCoeff θ N).symm
  -- Abel: the power series converges to `L` as the radius increases to one.
  have hAbel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hL
  -- Along the radius the power series *is* the interior closed form.
  have hev : ∀ᶠ x : ℝ in 𝓝[<] (1 : ℝ), 0 ≤ x ∧ x < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))]
      with x hx1 hx0
    exact ⟨hx0.le, hx1⟩
  have hAbel' : Tendsto (fun x : ℝ => oddExpGen θ (x : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 L) := by
    have h := Filter.tendsto_map'_iff.mp hAbel
    refine h.congr' ?_
    filter_upwards [hev] with x hx
    exact (hasSum_oddExpCoeff_mul_pow hx.1 hx.2).tsum_eq
  -- Continuity of the closed form at the boundary point pins the limit down.
  have hcast : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
  have hcont : Tendsto (fun x : ℝ => oddExpGen θ (x : ℂ)) (𝓝[<] (1 : ℝ))
      (𝓝 (oddExpGen θ 1)) := (continuousAt_oddExpGen hθ).tendsto.comp hcast
  have hval : L = oddExpGen θ 1 := tendsto_nhds_unique hAbel' hcont
  have hgen : oddExpGen θ 1
      = (Complex.log (1 + Complex.exp ((θ : ℂ) * Complex.I))
        - Complex.log (1 - Complex.exp ((θ : ℂ) * Complex.I))) / 2 := by
    rw [oddExpGen, one_mul]
  rw [← hgen, ← hval]
  exact hL0

/-- **The square-wave Fourier series.**  Off the zeros of the sine the odd harmonic sine series
converges to `(π/4)·sgn (sin θ)`. -/
theorem tendsto_sum_oddHarmonicSine {θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    Tendsto (fun N => ∑ k ∈ range N, Real.sin ((2 * (k : ℝ) + 1) * θ) / (2 * (k : ℝ) + 1))
      atTop (𝓝 (Real.pi / 4 * Real.sign (Real.sin θ))) := by
  have hmain := (Complex.continuous_im.tendsto _).comp (tendsto_sum_oddHarmonicExp hθ)
  rw [Function.comp_def] at hmain
  rw [← GaloisForLFunctions.HTGeometry.im_half_log_ratio hθ]
  refine hmain.congr fun N => ?_
  rw [Complex.im_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hden : (2 * (((k : ℕ) : ℝ) : ℂ) + 1) = ((2 * ((k : ℕ) : ℝ) + 1 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hden, Complex.div_ofReal_im, Complex.exp_ofReal_mul_I_im]

end RHTower
