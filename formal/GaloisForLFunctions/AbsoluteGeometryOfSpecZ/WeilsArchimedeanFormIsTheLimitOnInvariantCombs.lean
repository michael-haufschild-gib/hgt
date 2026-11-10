import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheCombOfThePowersOfABase
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheTwistedDensityOfTheCarrierIsWeilsSymbol
import GaloisForLFunctions.HTGeometry.IntervalRiemannSum
import GaloisForLFunctions.BiScaleUncertainty.PrimeBlindLevySlackAndWindowCone

/-!
# Weil's archimedean form is the limit of the jets on invariant combs

For a real packet `f ∈ C²_c(ℝ)` in the logarithmic coordinate, the comb `e^{ℤ/N}` carries the
samples `f(j/N)` with mass `1/N`. Grouped by displacement, the pairing of the jets on the comb is

  `P_N(f) = Σ_{k ≥ 1} (2/N)·ω(k/N)·a_N(k)`,   `a_N(k) = (1/N) Σ_j f(j/N) f((j + k)/N)`,

and its counterterm is `a_N(0)·log(N/2π)`, the mass times the logarithm of the density of the
comb over `2π`.

* **The comb autocorrelation** (`abs_combAutocorr_sub_le`): `|a_N(k) − h(k/N)| ≤ 4RBL/N`,
  `h(x) = ∫ f(u) f(u + x) du`, uniformly in `k`.
* **Lévy–Khintchine on the comb** (`combForm_eq`): `P_N − a_N(0) log(N/2π)` is
  `a_N(0)·(U(1/N) − log(N/2π))` minus `Σ_k (2/N) ω(k/N)(a_N(0) − a_N(k))`.
* **The jump sum** (`tendsto_combJump`): it tends to `∫_0^∞ 2ω(x)(h(0) − h(x)) dx`. Below `2R` this
  is a Riemann sum of a bounded continuous function; beyond `2R` the autocorrelation vanishes and
  the sum is squeezed between two values of the primitive of `ω`.
* **The limit** (`tendsto_combForm`): `P_N(f) − a_N(0) log(N/2π)` tends to minus the archimedean
  part of Weil's functional of `f` without the pole.

So on the combs invariant under a subgroup of the torus, Weil's archimedean form of every packet
is the finite part of the pairing of the jets, with the counterterm of the comb and no other.
-/

open Finset Filter Topology MeasureTheory
open Zeta23

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### The Lévy density -/

theorem archLevyDensity_antitoneOn :
    AntitoneOn _root_.RHTower.archLevyDensity (Set.Ioi 0) := by
  intro x hx y _ hxy
  have hx0 : (0 : ℝ) < x := hx
  have h1 : Real.exp (-y / 2) ≤ Real.exp (-x / 2) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-2 * y) ≤ Real.exp (-2 * x) := Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  unfold _root_.RHTower.archLevyDensity
  exact div_le_div₀ (Real.exp_pos _).le h1 (by linarith) (by linarith)

/-- `x·ω(x) ≤ e^{x/2}/2`. -/
theorem mul_archLevyDensity_le {x : ℝ} (hx : 0 < x) :
    x * _root_.RHTower.archLevyDensity x ≤ Real.exp (x / 2) / 2 := by
  have h := _root_.RHTower.ArchimedeanAnomaly.exp_half_div_sinh_eq hx
  have hs : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx.le
  have hs0 : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hω : _root_.RHTower.archLevyDensity x = Real.exp (x / 2) / Real.sinh x / 2 := by
    rw [h]
    ring
  have h1 : x * (Real.exp (x / 2) / Real.sinh x) ≤ Real.exp (x / 2) := by
    rw [mul_div_assoc', div_le_iff₀ hs0]
    nlinarith [Real.exp_pos (x / 2)]
  rw [hω]
  linarith

/-! ### The autocorrelation of a packet -/

/-- The autocorrelation of a packet: `h(x) = ∫ f(u) f(u + x) du`. -/
def packetAutocorr (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ u, f u * f (u + x)

section Packet

variable {f : ℝ → ℝ} {R : ℕ} {B L : ℝ}

theorem packetAutocorr_eq_intervalIntegral (hsupp : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) (x : ℝ) :
    packetAutocorr f x = ∫ u in (-(R : ℝ))..R, f u * f (u + x) := by
  rw [packetAutocorr]
  refine (intervalIntegral.integral_eq_integral_of_support_subset fun u hu => ?_).symm
  have hfu : f u ≠ 0 := fun h0 => hu (by
    show f u * f (u + x) = 0
    rw [h0, zero_mul])
  have hlt : |u| < R := lt_of_not_ge fun hge => hfu (hsupp u hge)
  exact ⟨(abs_lt.mp hlt).1, (abs_lt.mp hlt).2.le⟩

/-- The autocorrelation is Lipschitz. -/
theorem abs_packetAutocorr_sub_le (hcont : Continuous f)
    (hsupp : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) (hB : ∀ u, |f u| ≤ B)
    (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) (x y : ℝ) :
    |packetAutocorr f x - packetAutocorr f y| ≤ 2 * R * B * L * |x - y| := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hi : ∀ z : ℝ, IntervalIntegrable (fun u => f u * f (u + z)) volume (-(R : ℝ)) R := fun z =>
    (hcont.mul (hcont.comp (continuous_id.add continuous_const))).intervalIntegrable _ _
  rw [packetAutocorr_eq_intervalIntegral hsupp, packetAutocorr_eq_intervalIntegral hsupp,
    ← intervalIntegral.integral_sub (hi x) (hi y)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -(R : ℝ)) (b := R)
    (C := B * (L * |x - y|)) (f := fun u => f u * f (u + x) - f u * f (u + y)) (fun u _ => by
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
      have h1 := hL (u + x) (u + y)
      rw [add_sub_add_left_eq_sub] at h1
      exact mul_le_mul (hB u) h1 (abs_nonneg _) hB0)
  have hR : |(R : ℝ) - -(R : ℝ)| = 2 * R := by
    rw [sub_neg_eq_add, abs_of_nonneg (by positivity)]
    ring
  rw [Real.norm_eq_abs, hR] at h
  linarith

/-- The autocorrelation vanishes beyond twice the radius of the support. -/
theorem packetAutocorr_eq_zero (hsupp : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) {x : ℝ}
    (hx : 2 * (R : ℝ) ≤ x) : packetAutocorr f x = 0 := by
  have h0 : ∀ u : ℝ, f u * f (u + x) = 0 := by
    intro u
    by_cases hu : (R : ℝ) ≤ |u|
    · rw [hsupp u hu, zero_mul]
    · rw [not_le] at hu
      have hux : (R : ℝ) ≤ |u + x| := by
        have h1 := abs_lt.mp hu
        rw [le_abs]
        left
        linarith
      rw [hsupp _ hux, mul_zero]
  simp [packetAutocorr, h0]

/-- `∫ (f(u) − f(u + x))² du = 2(h(0) − h(x))`. -/
theorem integral_sub_shift_sq (hcont : Continuous f) (hfc : HasCompactSupport f) (x : ℝ) :
    ∫ u, (f u - f (u + x)) ^ 2 = 2 * (packetAutocorr f 0 - packetAutocorr f x) := by
  have I1 : Integrable fun u => f u * f u :=
    (hcont.mul hcont).integrable_of_hasCompactSupport hfc.mul_right
  have I2 : Integrable fun u => f (u + x) * f (u + x) := I1.comp_add_right x
  have I3 : Integrable fun u => f u * f (u + x) :=
    (hcont.mul (hcont.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hfc.mul_right
  have hfun : (fun u => (f u - f (u + x)) ^ 2) =
      fun u => (f u * f u + f (u + x) * f (u + x)) - 2 * (f u * f (u + x)) :=
    funext fun u => by ring
  have hshift : ∫ u, f (u + x) * f (u + x) = ∫ u, f u * f u :=
    integral_add_right_eq_self (fun u => f u * f u) x
  have h0 : packetAutocorr f 0 = ∫ u, f u * f u := by
    simp only [packetAutocorr, add_zero]
  have I12 : Integrable fun u => f u * f u + f (u + x) * f (u + x) := I1.add I2
  have I32 : Integrable fun u => 2 * (f u * f (u + x)) := I3.const_mul 2
  rw [hfun, integral_sub I12 I32, integral_add I1 I2, integral_const_mul, hshift, h0,
    packetAutocorr]
  ring

end Packet

/-! ### Riemann sums on a uniform partition -/

/-- The corpus estimate for uniform Riemann sums, for a real integrand. -/
theorem abs_intervalIntegral_sub_uniformRiemannSum_le {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : Continuous g) {M : ℕ} (hM : 0 < M) {η : ℝ} (hη : 0 ≤ η)
    (hmod : ∀ i < M, ∀ x ∈ Set.uIoc (HTGeometry.uniformNode a b M i)
      (HTGeometry.uniformNode a b M (i + 1)), |g x - g (HTGeometry.uniformNode a b M i)| ≤ η) :
    |(∫ x in a..b, g x) - ∑ i ∈ range M, (b - a) / M * g (HTGeometry.uniformNode a b M i)| ≤
      (b - a) * η := by
  have h := HTGeometry.norm_intervalIntegral_sub_uniformRiemannSum_le hab
    (h := fun x => (g x : ℂ)) hM
    (fun i _ => (Complex.continuous_ofReal.comp hg).intervalIntegrable _ _) hη
    (fun i hi x hx => by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hmod i hi x hx)
  rw [intervalIntegral.integral_ofReal] at h
  simp only [Complex.real_smul, ← Complex.ofReal_mul] at h
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-! ### The comb -/

/-- The points of the comb `e^{ℤ/N}` in the window `[−R, R)`: `−R + i/N`. -/
def combNode (R N i : ℕ) : ℝ := -(R : ℝ) + (i : ℝ) / N

theorem uniformNode_eq_combNode {R N : ℕ} (hR : 1 ≤ R) (hN : 1 ≤ N) (i : ℕ) :
    HTGeometry.uniformNode (-(R : ℝ)) R (2 * R * N) i = combNode R N i := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold HTGeometry.uniformNode combNode
  push_cast
  field_simp
  ring

/-- The autocorrelation of the packet on the comb, at the displacement `k/N`. -/
def combAutocorr (f : ℝ → ℝ) (R N k : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i ∈ range (2 * R * N), f (combNode R N i) * f (combNode R N i + (k : ℝ) / N)

section Comb

variable {f : ℝ → ℝ} {R : ℕ} {B L : ℝ}

/-- **The comb autocorrelation is the autocorrelation up to `4RBL/N`**, uniformly in the
displacement. -/
theorem abs_combAutocorr_sub_le (hcont : Continuous f)
    (hsupp : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) (hB : ∀ u, |f u| ≤ B)
    (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) (hR : 1 ≤ R) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    |combAutocorr f R N k - packetAutocorr f ((k : ℝ) / N)| ≤ 4 * R * B * L / N := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hM : 0 < 2 * R * N := by positivity
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hL0 : 0 ≤ L := by
    have h := hL 0 1
    have h1 : |(0 : ℝ) - 1| = 1 := by norm_num
    rw [h1, mul_one] at h
    exact (abs_nonneg _).trans h
  have hcell : ∀ i : ℕ, HTGeometry.uniformNode (-(R : ℝ)) R (2 * R * N) (i + 1) -
      HTGeometry.uniformNode (-(R : ℝ)) R (2 * R * N) i = 1 / N := fun i => by
    rw [HTGeometry.uniformNode_succ_sub hM]
    push_cast
    field_simp
    ring
  have hmod : ∀ i < 2 * R * N, ∀ x ∈ Set.uIoc (HTGeometry.uniformNode (-(R : ℝ)) R (2 * R * N) i)
      (HTGeometry.uniformNode (-(R : ℝ)) R (2 * R * N) (i + 1)),
      |f x * f (x + (k : ℝ) / N) - f (HTGeometry.uniformNode (-(R : ℝ)) R (2 * R * N) i) *
        f (HTGeometry.uniformNode (-(R : ℝ)) R (2 * R * N) i + (k : ℝ) / N)| ≤ 2 * B * L / N := by
    intro i _ x hx
    have hc := hcell i
    have hpos : (0 : ℝ) < 1 / N := by positivity
    rw [Set.uIoc_of_le (by linarith)] at hx
    generalize HTGeometry.uniformNode (-(R : ℝ)) R (2 * R * N) i = v at hx hc ⊢
    have hdist : |x - v| ≤ 1 / N := by
      rw [abs_of_pos (sub_pos.mpr hx.1)]
      linarith [hx.2]
    have e : f x * f (x + (k : ℝ) / N) - f v * f (v + (k : ℝ) / N) =
        f x * (f (x + (k : ℝ) / N) - f (v + (k : ℝ) / N)) +
          f (v + (k : ℝ) / N) * (f x - f v) := by ring
    have h1 := hL (x + (k : ℝ) / N) (v + (k : ℝ) / N)
    rw [add_sub_add_right_eq_sub] at h1
    have hmul : B * L * |x - v| ≤ B * L * (1 / N) :=
      mul_le_mul_of_nonneg_left hdist (mul_nonneg hB0 hL0)
    rw [e]
    calc |f x * (f (x + (k : ℝ) / N) - f (v + (k : ℝ) / N)) +
          f (v + (k : ℝ) / N) * (f x - f v)|
        ≤ |f x| * |f (x + (k : ℝ) / N) - f (v + (k : ℝ) / N)| +
          |f (v + (k : ℝ) / N)| * |f x - f v| := by
          rw [← abs_mul, ← abs_mul]
          exact abs_add_le _ _
      _ ≤ B * (L * |x - v|) + B * (L * |x - v|) :=
          add_le_add (mul_le_mul (hB _) h1 (abs_nonneg _) hB0)
            (mul_le_mul (hB _) (hL _ _) (abs_nonneg _) hB0)
      _ ≤ 2 * B * L / N := by
          have e2 : 2 * B * L / N = 2 * (B * L * (1 / N)) := by ring
          rw [e2]
          linarith
  have h := abs_intervalIntegral_sub_uniformRiemannSum_le (a := -(R : ℝ)) (b := R) (by linarith)
    (g := fun u => f u * f (u + (k : ℝ) / N))
    (hcont.mul (hcont.comp (continuous_id.add continuous_const))) hM
    (η := 2 * B * L / N) (by positivity) hmod
  have hsum : ∑ i ∈ range (2 * R * N), ((R : ℝ) - -(R : ℝ)) / ((2 * R * N : ℕ) : ℝ) *
      (f (HTGeometry.uniformNode (-(R : ℝ)) R (2 * R * N) i) *
        f (HTGeometry.uniformNode (-(R : ℝ)) R (2 * R * N) i + (k : ℝ) / N)) =
      combAutocorr f R N k := by
    rw [combAutocorr, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [uniformNode_eq_combNode hR hN]
    congr 1
    push_cast
    field_simp
    ring
  rw [← packetAutocorr_eq_intervalIntegral hsupp, hsum, abs_sub_comm] at h
  refine h.trans (le_of_eq ?_)
  field_simp
  ring

theorem combAutocorr_eq_zero (hsupp : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) {N : ℕ} (hN : 1 ≤ N)
    {k : ℕ} (hk : 2 * R * N ≤ k) : combAutocorr f R N k = 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hkN : 2 * (R : ℝ) ≤ (k : ℝ) / N := by
    rw [le_div_iff₀ hN']
    exact_mod_cast hk
  rw [combAutocorr, Finset.sum_eq_zero, mul_zero]
  intro i _
  have hnode : -(R : ℝ) ≤ combNode R N i := by
    have : (0 : ℝ) ≤ (i : ℝ) / N := by positivity
    unfold combNode
    linarith
  have habs : (R : ℝ) ≤ |combNode R N i + (k : ℝ) / N| := by
    rw [le_abs]
    left
    linarith
  rw [hsupp _ habs, mul_zero]

end Comb

/-! ### The pairing on the comb, by displacement -/

/-- The rate of the comb `e^{ℤ/N}` at the displacement `(k + 1)/N`, both signs. -/
def combRate (N k : ℕ) : ℝ :=
  2 * (N : ℝ)⁻¹ * _root_.RHTower.archLevyDensity (((k : ℝ) + 1) * (N : ℝ)⁻¹)

theorem combRate_nonneg (N k : ℕ) : 0 ≤ combRate N k := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [combRate]
  · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hy : 0 < ((k : ℝ) + 1) * (N : ℝ)⁻¹ := by positivity
    exact mul_nonneg (by positivity) (_root_.RHTower.archLevyDensity_pos hy).le

theorem summable_combRate {N : ℕ} (hN : 1 ≤ N) : Summable (combRate N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.mpr hN'
  have hfun : combRate N = fun k => sinhTerm (N : ℝ)⁻¹ k + coshTerm (N : ℝ)⁻¹ k :=
    funext fun k => by
      have hy : 0 < ((k : ℝ) + 1) * (N : ℝ)⁻¹ := by positivity
      rw [combRate, sinhTerm, coshTerm, ← mul_add, ← two_mul_archLevyDensity hy]
      ring
  rw [hfun]
  exact (summable_sinhTerm hh).add (summable_coshTerm hh)

theorem tsum_combRate (N : ℕ) : ∑' k : ℕ, combRate N k = baseCombRate (N : ℝ)⁻¹ := rfl

/-- The pairing of the jets on the comb, grouped by displacement. -/
def combPairing (f : ℝ → ℝ) (R N : ℕ) : ℝ :=
  ∑' k : ℕ, combRate N k * combAutocorr f R N (k + 1)

/-- The pairing with the counterterm of the comb. -/
def combForm (f : ℝ → ℝ) (R N : ℕ) : ℝ :=
  combPairing f R N - combAutocorr f R N 0 * Real.log ((N : ℝ) / (2 * Real.pi))

/-- The jump sum of the packet on the comb. -/
def combJump (f : ℝ → ℝ) (R N : ℕ) : ℝ :=
  ∑' k : ℕ, combRate N k * (combAutocorr f R N 0 - combAutocorr f R N (k + 1))

section Limit

variable {f : ℝ → ℝ} {R : ℕ} {B L : ℝ}

theorem summable_combRate_mul_combAutocorr (hsupp : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) {N : ℕ}
    (hN : 1 ≤ N) : Summable fun k : ℕ => combRate N k * combAutocorr f R N (k + 1) :=
  summable_of_ne_finset_zero (s := range (2 * R * N)) fun k hk => by
    rw [combAutocorr_eq_zero hsupp hN (by
      have := Finset.mem_range.not.mp hk
      omega), mul_zero]

/-- **Lévy–Khintchine on the comb.** -/
theorem combForm_eq (hsupp : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) {N : ℕ} (hN : 1 ≤ N) :
    combForm f R N = combAutocorr f R N 0 *
      (baseCombRate (N : ℝ)⁻¹ + Real.log (2 * Real.pi * (N : ℝ)⁻¹)) - combJump f R N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := summable_combRate hN
  have hfin := summable_combRate_mul_combAutocorr hsupp hN
  have hjump : combJump f R N =
      combAutocorr f R N 0 * baseCombRate (N : ℝ)⁻¹ - combPairing f R N := by
    have hfun : (fun k : ℕ => combRate N k * (combAutocorr f R N 0 - combAutocorr f R N (k + 1))) =
        fun k => combAutocorr f R N 0 * combRate N k - combRate N k * combAutocorr f R N (k + 1) :=
      funext fun k => by ring
    rw [combJump, hfun, (hs.mul_left _).tsum_sub hfin, tsum_mul_left, tsum_combRate, combPairing]
  have hlog : Real.log ((N : ℝ) / (2 * Real.pi)) = -Real.log (2 * Real.pi * (N : ℝ)⁻¹) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
  rw [combForm, hjump, hlog]
  ring

/-- The jump density of the packet: `2ω(x)(h(0) − h(x))`. -/
def levyJump (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 * _root_.RHTower.archLevyDensity x * (packetAutocorr f 0 - packetAutocorr f x)

theorem continuous_packetAutocorr (hcont : Continuous f)
    (hsupp : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) (hB : ∀ u, |f u| ≤ B)
    (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) : Continuous (packetAutocorr f) := by
  have hK : 0 ≤ 2 * R * B * L * |(1 : ℝ) - 0| :=
    (abs_nonneg _).trans (abs_packetAutocorr_sub_le hcont hsupp hB hL 1 0)
  have hK' : 0 ≤ 2 * R * B * L := by simpa using hK
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (2 * R * B * L)) fun x y => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK']
  exact abs_packetAutocorr_sub_le hcont hsupp hB hL x y

theorem continuousOn_levyJump (hcont : Continuous f)
    (hsupp : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) (hB : ∀ u, |f u| ≤ B)
    (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) : ContinuousOn (levyJump f) (Set.Ioi 0) :=
  (continuousOn_const.mul _root_.RHTower.WeilLevyPoleGauss.continuousOn_archLevyDensity).mul
    (continuous_const.sub (continuous_packetAutocorr hcont hsupp hB hL)).continuousOn

theorem abs_levyJump_le (hcont : Continuous f) (hsupp : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0)
    (hB : ∀ u, |f u| ≤ B) (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) {x X : ℝ} (hx : 0 < x)
    (hxX : x ≤ X) : |levyJump f x| ≤ 2 * R * B * L * Real.exp (X / 2) := by
  have hω := _root_.RHTower.archLevyDensity_pos hx
  have hlip := abs_packetAutocorr_sub_le hcont hsupp hB hL 0 x
  rw [zero_sub, abs_neg, abs_of_pos hx] at hlip
  have hK : 0 ≤ 2 * R * B * L := by
    have h1 := (abs_nonneg _).trans hlip
    exact nonneg_of_mul_nonneg_left h1 hx
  have hmul := mul_archLevyDensity_le hx
  have hexp : Real.exp (x / 2) ≤ Real.exp (X / 2) := Real.exp_le_exp.mpr (by linarith)
  rw [levyJump, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * _root_.RHTower.archLevyDensity x)]
  calc 2 * _root_.RHTower.archLevyDensity x * |packetAutocorr f 0 - packetAutocorr f x|
      ≤ 2 * _root_.RHTower.archLevyDensity x * (2 * R * B * L * x) :=
        mul_le_mul_of_nonneg_left hlip (by positivity)
    _ = 2 * R * B * L * (2 * (x * _root_.RHTower.archLevyDensity x)) := by ring
    _ ≤ 2 * R * B * L * Real.exp (X / 2) := mul_le_mul_of_nonneg_left (by linarith) hK

theorem levyJump_of_le (hsupp : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) {x : ℝ}
    (hx : 2 * (R : ℝ) ≤ x) :
    levyJump f x = 2 * packetAutocorr f 0 * _root_.RHTower.archLevyDensity x := by
  rw [levyJump, packetAutocorr_eq_zero hsupp hx]
  ring

theorem levyJump_nonneg (hcont : Continuous f) (hfc : HasCompactSupport f) {x : ℝ} (hx : 0 < x) :
    0 ≤ levyJump f x := by
  have h := integral_sub_shift_sq hcont hfc x
  have hnn : 0 ≤ ∫ u, (f u - f (u + x)) ^ 2 := integral_nonneg fun u => sq_nonneg _
  rw [levyJump]
  have hω := _root_.RHTower.archLevyDensity_pos hx
  nlinarith

/-! ### The tail of the rates -/

/-- The rate into the comb point at distance `(j + 1)/N` beyond `X`. -/
def tailRate (X : ℝ) (N j : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * _root_.RHTower.archLevyDensity (X + ((j : ℝ) + 1) * (N : ℝ)⁻¹)

theorem archLevyAntideriv_step {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    _root_.RHTower.archLevyDensity (a + δ) * δ ≤
        _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv a -
          _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv (a + δ) ∧
      _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv a -
          _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv (a + δ) ≤
        _root_.RHTower.archLevyDensity a * δ := by
  have hab : a < a + δ := by linarith
  have hd : ∀ y : ℝ, 0 < y → HasDerivAt
      (fun y => -_root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv y)
      (_root_.RHTower.archLevyDensity y) y := fun y hy =>
    (_root_.RHTower.WeilLevyPoleGauss.hasDerivAt_archLevyAntideriv hy).fun_neg.congr_deriv
      (neg_neg _)
  have hF : ContinuousOn (fun y => -_root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv y)
      (Set.Icc a (a + δ)) := fun y hy =>
    (hd y (ha.trans_le hy.1)).continuousAt.continuousWithinAt
  have h1 := mul_le_sub_of_hasDerivAt hab hF (fun y hy => hd y (ha.trans hy.1))
    (fun y hy => archLevyDensity_antitoneOn (ha.trans hy.1) (ha.trans hab) hy.2.le)
  have h2 := sub_le_mul_of_hasDerivAt hab hF (fun y hy => hd y (ha.trans hy.1))
    (fun y hy => archLevyDensity_antitoneOn ha (ha.trans hy.1) hy.1.le)
  rw [add_sub_cancel_left] at h1 h2
  exact ⟨by linarith, by linarith⟩

theorem tailRate_nonneg {X : ℝ} (hX : 0 < X) (N j : ℕ) : 0 ≤ tailRate X N j := by
  have hy : 0 < X + ((j : ℝ) + 1) * (N : ℝ)⁻¹ := by positivity
  exact mul_nonneg (by positivity) (_root_.RHTower.archLevyDensity_pos hy).le

theorem sum_tailRate_le {X : ℝ} (hX : 0 < X) {N : ℕ} (hN : 1 ≤ N) (J : ℕ) :
    ∑ j ∈ range J, tailRate X N j ≤ _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv X := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.mpr hN'
  have hsum := Finset.sum_range_sub' (fun j : ℕ =>
    _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv (X + (j : ℝ) * (N : ℝ)⁻¹)) J
  simp only [Nat.cast_zero, zero_mul, add_zero] at hsum
  have hpos : 0 < _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv (X + (J : ℝ) * (N : ℝ)⁻¹) :=
    _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv_pos (by positivity)
  have hle : ∑ j ∈ range J, tailRate X N j ≤ ∑ j ∈ range J,
      (_root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv (X + (j : ℝ) * (N : ℝ)⁻¹) -
        _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv (X + ((j + 1 : ℕ) : ℝ) * (N : ℝ)⁻¹)) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have ha : 0 < X + (j : ℝ) * (N : ℝ)⁻¹ := by positivity
    have h := (archLevyAntideriv_step ha hδ).1
    have e : X + ((j + 1 : ℕ) : ℝ) * (N : ℝ)⁻¹ = X + (j : ℝ) * (N : ℝ)⁻¹ + (N : ℝ)⁻¹ := by
      push_cast
      ring
    have e' : X + ((j : ℝ) + 1) * (N : ℝ)⁻¹ = X + (j : ℝ) * (N : ℝ)⁻¹ + (N : ℝ)⁻¹ := by ring
    rw [tailRate, e, e']
    linarith [h]
  linarith

theorem summable_tailRate {X : ℝ} (hX : 0 < X) {N : ℕ} (hN : 1 ≤ N) :
    Summable (tailRate X N) :=
  summable_of_sum_range_le (tailRate_nonneg hX N) (sum_tailRate_le hX hN)

theorem tsum_tailRate_le {X : ℝ} (hX : 0 < X) {N : ℕ} (hN : 1 ≤ N) :
    ∑' j : ℕ, tailRate X N j ≤ _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv X :=
  Real.tsum_le_of_sum_range_le (tailRate_nonneg hX N) (sum_tailRate_le hX hN)

theorem le_tsum_tailRate {X : ℝ} (hX : 0 < X) {N : ℕ} (hN : 1 ≤ N) :
    _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv (X + (N : ℝ)⁻¹) ≤
      ∑' j : ℕ, tailRate X N j := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.mpr hN'
  have hJ : Tendsto (fun J : ℕ => X + (N : ℝ)⁻¹ + (J : ℝ) * (N : ℝ)⁻¹) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop.atTop_mul_const hδ)
  have hlim := (tendsto_const_nhds (x := _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv
    (X + (N : ℝ)⁻¹))).sub
    (_root_.RHTower.WeilLevyCoshCrossover.tendsto_archLevyAntideriv_atTop.comp hJ)
  rw [sub_zero] at hlim
  refine le_of_tendsto' hlim fun J => ?_
  have hsum := Finset.sum_range_sub' (fun j : ℕ =>
    _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv
      (X + (N : ℝ)⁻¹ + (j : ℝ) * (N : ℝ)⁻¹)) J
  simp only [Nat.cast_zero, zero_mul, add_zero] at hsum
  have hle : ∑ j ∈ range J,
      (_root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv (X + (N : ℝ)⁻¹ + (j : ℝ) * (N : ℝ)⁻¹) -
        _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv
          (X + (N : ℝ)⁻¹ + ((j + 1 : ℕ) : ℝ) * (N : ℝ)⁻¹)) ≤ ∑ j ∈ range J, tailRate X N j := by
    refine Finset.sum_le_sum fun j _ => ?_
    have ha : 0 < X + (N : ℝ)⁻¹ + (j : ℝ) * (N : ℝ)⁻¹ := by positivity
    have h := (archLevyAntideriv_step ha hδ).2
    have e : X + (N : ℝ)⁻¹ + ((j + 1 : ℕ) : ℝ) * (N : ℝ)⁻¹ =
        X + (N : ℝ)⁻¹ + (j : ℝ) * (N : ℝ)⁻¹ + (N : ℝ)⁻¹ := by
      push_cast
      ring
    have e' : X + ((j : ℝ) + 1) * (N : ℝ)⁻¹ = X + (N : ℝ)⁻¹ + (j : ℝ) * (N : ℝ)⁻¹ := by ring
    rw [tailRate, e, e']
    linarith [h]
  simp only [Function.comp_apply]
  rw [← hsum]
  exact hle.trans ((summable_tailRate hX hN).sum_le_tsum _ fun j _ => tailRate_nonneg hX N j)

/-- The tail of the rates beyond `X` tends to `∫_X^∞ ω`. -/
theorem tendsto_tsum_tailRate {X : ℝ} (hX : 0 < X) :
    Tendsto (fun N : ℕ => ∑' j : ℕ, tailRate X N j) atTop
      (𝓝 (_root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv X)) := by
  have hc : Tendsto (fun N : ℕ => _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv
      (X + (N : ℝ)⁻¹)) atTop (𝓝 (_root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv X)) := by
    have hcont := (_root_.RHTower.WeilLevyPoleGauss.hasDerivAt_archLevyAntideriv hX).continuousAt
    have h1 : Tendsto (fun N : ℕ => X + (N : ℝ)⁻¹) atTop (𝓝 X) := by
      have h := (tendsto_const_nhds (x := X) (f := (atTop : Filter ℕ))).add
        (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
      rwa [add_zero] at h
    exact hcont.tendsto.comp h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hc tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN using le_tsum_tailRate hX hN
  · filter_upwards [eventually_ge_atTop 1] with N hN using tsum_tailRate_le hX hN

/-! ### The mass and the rate -/

theorem tendsto_combAutocorr_zero (hcont : Continuous f)
    (hsupp : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) (hB : ∀ u, |f u| ≤ B)
    (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) (hR : 1 ≤ R) :
    Tendsto (fun N : ℕ => combAutocorr f R N 0) atTop (𝓝 (packetAutocorr f 0)) := by
  have hlim : Tendsto (fun N : ℕ => 4 * R * B * L / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have h := abs_combAutocorr_sub_le hcont hsupp hB hL hR hN 0
  rw [Nat.cast_zero, zero_div] at h
  rw [Real.norm_eq_abs]
  exact h

/-- The rate of the comb `e^{ℤ/N}` with its counterterm tends to Weil's constant. -/
theorem tendsto_baseCombRate_inv_nat :
    Tendsto (fun N : ℕ => baseCombRate (N : ℝ)⁻¹ + Real.log (2 * Real.pi * (N : ℝ)⁻¹)) atTop
      (𝓝 (-EF.gammaBracket 0)) := by
  have h0 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_inv_atTop_nhds_zero_nat, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    exact inv_pos.mpr hN'
  exact tendsto_baseCombRate_add_log.comp h0

/-- The rate of the comb is `o(N)`. -/
theorem tendsto_baseCombRate_div :
    Tendsto (fun N : ℕ => baseCombRate (N : ℝ)⁻¹ / N) atTop (𝓝 0) := by
  have h1 := tendsto_baseCombRate_inv_nat.div_atTop tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => Real.log N / (N : ℝ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    refine h.congr fun N => ?_
    simp
  have hc : Tendsto (fun N : ℕ => Real.log (2 * Real.pi) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h := (h1.sub hc).add hlog
  rw [sub_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h2π : (2 * Real.pi) ≠ 0 := by positivity
  rw [Real.log_mul h2π (inv_ne_zero hN'.ne'), Real.log_inv]
  ring

/-! ### The jump sum -/

theorem inv_mul_levyJump (f : ℝ → ℝ) (N k : ℕ) :
    (N : ℝ)⁻¹ * levyJump f (((k : ℝ) + 1) * (N : ℝ)⁻¹) =
      combRate N k * (packetAutocorr f 0 - packetAutocorr f (((k : ℝ) + 1) * (N : ℝ)⁻¹)) := by
  rw [levyJump, combRate]
  ring

theorem summable_sampleJump (hsupp : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) {N : ℕ} (hN : 1 ≤ N) :
    Summable fun k : ℕ => (N : ℝ)⁻¹ * levyJump f (((k : ℝ) + 1) * (N : ℝ)⁻¹) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hfin : Summable fun k : ℕ =>
      combRate N k * packetAutocorr f (((k : ℝ) + 1) * (N : ℝ)⁻¹) :=
    summable_of_ne_finset_zero (s := range (2 * R * N)) fun k hk => by
      have hk' : 2 * R * N ≤ k := by
        have := Finset.mem_range.not.mp hk
        omega
      have hk'' : ((2 * R * N : ℕ) : ℝ) ≤ k := by exact_mod_cast hk'
      push_cast at hk''
      have hy : 2 * (R : ℝ) ≤ ((k : ℝ) + 1) * (N : ℝ)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hN']
        linarith
      rw [packetAutocorr_eq_zero hsupp hy, mul_zero]
  have hfun : (fun k : ℕ => (N : ℝ)⁻¹ * levyJump f (((k : ℝ) + 1) * (N : ℝ)⁻¹)) =
      fun k => packetAutocorr f 0 * combRate N k -
        combRate N k * packetAutocorr f (((k : ℝ) + 1) * (N : ℝ)⁻¹) :=
    funext fun k => by
      rw [inv_mul_levyJump]
      ring
  rw [hfun]
  exact ((summable_combRate hN).mul_left _).sub hfin

/-- The jump sum of the autocorrelation sampled on the comb. -/
def sampleJump (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑' k : ℕ, (N : ℝ)⁻¹ * levyJump f (((k : ℝ) + 1) * (N : ℝ)⁻¹)

/-- Two series whose terms differ by at most the terms of a third. -/
theorem abs_tsum_sub_tsum_le {a b c : ℕ → ℝ} (ha : Summable a) (hb : Summable b)
    (hc : Summable c) (h : ∀ k, |a k - b k| ≤ c k) :
    |∑' k, a k - ∑' k, b k| ≤ ∑' k, c k := by
  have habs : Summable fun k => ‖a k - b k‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => (Real.norm_eq_abs _).trans_le (h k))
      hc
  rw [← ha.tsum_sub hb, ← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm habs).trans
    (Summable.tsum_le_tsum (fun k => (Real.norm_eq_abs _).trans_le (h k)) habs hc)

/-- The jump sum of the comb is the sampled jump sum up to `8RBL·U(1/N)/N`. -/
theorem abs_combJump_sub_sampleJump_le (hcont : Continuous f)
    (hsupp : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) (hB : ∀ u, |f u| ≤ B)
    (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) (hR : 1 ≤ R) {N : ℕ} (hN : 1 ≤ N) :
    |combJump f R N - sampleJump f N| ≤ 8 * R * B * L * (baseCombRate (N : ℝ)⁻¹ / N) := by
  have hs := summable_combRate hN
  have hJ : Summable fun k : ℕ =>
      combRate N k * (combAutocorr f R N 0 - combAutocorr f R N (k + 1)) := by
    have hfun : (fun k : ℕ => combRate N k * (combAutocorr f R N 0 - combAutocorr f R N (k + 1))) =
        fun k => combAutocorr f R N 0 * combRate N k - combRate N k * combAutocorr f R N (k + 1) :=
      funext fun k => by ring
    rw [hfun]
    exact (hs.mul_left _).sub (summable_combRate_mul_combAutocorr hsupp hN)
  have hS := summable_sampleJump (f := f) hsupp hN
  have hterm : ∀ k : ℕ, |combRate N k * (combAutocorr f R N 0 - combAutocorr f R N (k + 1)) -
      (N : ℝ)⁻¹ * levyJump f (((k : ℝ) + 1) * (N : ℝ)⁻¹)| ≤
        combRate N k * (8 * R * B * L / N) := by
    intro k
    have h0 := abs_combAutocorr_sub_le hcont hsupp hB hL hR hN 0
    have hk := abs_combAutocorr_sub_le hcont hsupp hB hL hR hN (k + 1)
    rw [Nat.cast_zero, zero_div] at h0
    have ey : ((k + 1 : ℕ) : ℝ) / N = ((k : ℝ) + 1) * (N : ℝ)⁻¹ := by
      push_cast
      rw [div_eq_mul_inv]
    rw [ey] at hk
    have e8 : 8 * (R : ℝ) * B * L / N = 4 * R * B * L / N + 4 * R * B * L / N := by ring
    rw [inv_mul_levyJump, ← mul_sub, abs_mul, abs_of_nonneg (combRate_nonneg N k)]
    refine mul_le_mul_of_nonneg_left ?_ (combRate_nonneg N k)
    rw [abs_le] at h0 hk ⊢
    constructor <;> linarith [h0.1, h0.2, hk.1, hk.2, e8]
  have hsum : Summable fun k : ℕ => combRate N k * (8 * R * B * L / N) := hs.mul_right _
  have h := abs_tsum_sub_tsum_le hJ hS hsum hterm
  rw [tsum_mul_right, tsum_combRate] at h
  rw [combJump, sampleJump]
  refine h.trans (le_of_eq ?_)
  ring

/-- Below `2R` the sampled jump sum is a Riemann sum of a bounded continuous function. -/
theorem tendsto_sum_levyJump_head (hcont : Continuous f)
    (hsupp : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) (hB : ∀ u, |f u| ≤ B)
    (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) (hR : 1 ≤ R) :
    Tendsto (fun N : ℕ => ∑ k ∈ range (2 * R * N),
        (N : ℝ)⁻¹ * levyJump f (((k : ℝ) + 1) * (N : ℝ)⁻¹)) atTop
      (𝓝 (∫ x in (0 : ℝ)..(2 * R), levyJump f x)) := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hX : (0 : ℝ) < 2 * R := by positivity
  have hg : ContinuousOn (fun s : ℝ => levyJump f (2 * (R : ℝ) * s)) (Set.Ioc 0 1) :=
    (continuousOn_levyJump hcont hsupp hB hL).comp
      (continuous_const.mul continuous_id).continuousOn fun s hs => mul_pos hX hs.1
  have hbound : ∀ s ∈ Set.Ioc (0 : ℝ) 1,
      |levyJump f (2 * (R : ℝ) * s)| ≤ 2 * R * B * L * Real.exp (2 * (R : ℝ) / 2) := fun s hs =>
    abs_levyJump_le hcont hsupp hB hL (mul_pos hX hs.1) (mul_le_of_le_one_right hX.le hs.2)
  have hsub : Tendsto (fun N : ℕ => 2 * R * N) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N (by omega)) tendsto_id
  have h1 := ((tendsto_riemannSum_of_continuousOn_Ioc hg hbound).comp hsub).const_mul
    (2 * (R : ℝ))
  rw [intervalIntegral.mul_integral_comp_mul_left, mul_zero, mul_one] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have e1 : 2 * (R : ℝ) * (((2 * R * N : ℕ) : ℝ))⁻¹ = (N : ℝ)⁻¹ := by
    push_cast
    field_simp
  simp only [Function.comp_apply]
  rw [← mul_assoc, e1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e2 : 2 * (R : ℝ) * (((k : ℝ) + 1) / ((2 * R * N : ℕ) : ℝ)) =
      ((k : ℝ) + 1) * (N : ℝ)⁻¹ := by
    push_cast
    field_simp
  rw [e2]

/-- Beyond `2R` the autocorrelation vanishes and the terms are the rates. -/
theorem tsum_levyJump_tail (hsupp : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) {N : ℕ} (hN : 1 ≤ N) :
    ∑' j : ℕ, (N : ℝ)⁻¹ * levyJump f ((((j + 2 * R * N : ℕ) : ℝ) + 1) * (N : ℝ)⁻¹) =
      2 * packetAutocorr f 0 * ∑' j : ℕ, tailRate (2 * R) N j := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  have e : (((j + 2 * R * N : ℕ) : ℝ) + 1) * (N : ℝ)⁻¹ =
      2 * (R : ℝ) + ((j : ℝ) + 1) * (N : ℝ)⁻¹ := by
    push_cast
    field_simp
    ring
  have hy : 2 * (R : ℝ) ≤ 2 * (R : ℝ) + ((j : ℝ) + 1) * (N : ℝ)⁻¹ := by
    have : (0 : ℝ) ≤ ((j : ℝ) + 1) * (N : ℝ)⁻¹ := by positivity
    linarith
  rw [e, levyJump_of_le hsupp hy, tailRate]
  ring

/-- The jump integral, split at twice the radius of the support. -/
theorem integral_levyJump_Ioi (hcont : Continuous f)
    (hsupp : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) (hB : ∀ u, |f u| ≤ B)
    (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) (hR : 1 ≤ R) :
    ∫ x in Set.Ioi 0, levyJump f x = (∫ x in (0 : ℝ)..(2 * R), levyJump f x) +
      2 * packetAutocorr f 0 * _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv (2 * R) := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hX : (0 : ℝ) < 2 * R := by positivity
  have hI1 : IntegrableOn (levyJump f) (Set.Ioc 0 (2 * (R : ℝ))) := by
    refine Integrable.mono' (integrableOn_const
        (C := 2 * R * B * L * Real.exp (2 * (R : ℝ) / 2)) measure_Ioc_lt_top.ne)
      (((continuousOn_levyJump hcont hsupp hB hL).mono fun x hx => hx.1).aestronglyMeasurable
        measurableSet_Ioc) ?_
    exact (ae_restrict_mem measurableSet_Ioc).mono fun x hx => by
      rw [Real.norm_eq_abs]
      exact abs_levyJump_le hcont hsupp hB hL hx.1 hx.2
  have heq : Set.EqOn (levyJump f)
      (fun x => 2 * packetAutocorr f 0 * _root_.RHTower.archLevyDensity x)
      (Set.Ioi (2 * (R : ℝ))) := fun x hx => levyJump_of_le hsupp (le_of_lt hx)
  have hI0 : IntegrableOn (fun x => 2 * packetAutocorr f 0 * _root_.RHTower.archLevyDensity x)
      (Set.Ioi (2 * (R : ℝ))) :=
    Integrable.const_mul (_root_.RHTower.WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hX) _
  have hI2 : IntegrableOn (levyJump f) (Set.Ioi (2 * (R : ℝ))) :=
    hI0.congr_fun heq.symm measurableSet_Ioi
  rw [← Set.Ioc_union_Ioi_eq_Ioi hX.le, setIntegral_union Set.Ioc_disjoint_Ioi_same
    measurableSet_Ioi hI1 hI2, intervalIntegral.integral_of_le hX.le,
    setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul,
    _root_.RHTower.WeilLevyCoshCrossover.integral_archLevyDensity_Ioi hX]

theorem tendsto_sampleJump (hcont : Continuous f)
    (hsupp : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) (hB : ∀ u, |f u| ≤ B)
    (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) (hR : 1 ≤ R) :
    Tendsto (sampleJump f) atTop (𝓝 (∫ x in Set.Ioi 0, levyJump f x)) := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  rw [integral_levyJump_Ioi hcont hsupp hB hL hR]
  have hhead := tendsto_sum_levyJump_head hcont hsupp hB hL hR
  have htail := (tendsto_tsum_tailRate (X := 2 * (R : ℝ)) (by positivity)).const_mul
    (2 * packetAutocorr f 0)
  refine (hhead.add htail).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [sampleJump, ← Summable.sum_add_tsum_nat_add (2 * R * N) (summable_sampleJump hsupp hN),
    tsum_levyJump_tail hsupp hN]

/-- **The jump sum of the comb tends to the jump integral of the packet.** -/
theorem tendsto_combJump (hcont : Continuous f)
    (hsupp : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) (hB : ∀ u, |f u| ≤ B)
    (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) (hR : 1 ≤ R) :
    Tendsto (combJump f R) atTop (𝓝 (∫ x in Set.Ioi 0, levyJump f x)) := by
  have h1 := tendsto_sampleJump hcont hsupp hB hL hR
  have h2 : Tendsto (fun N : ℕ => combJump f R N - sampleJump f N) atTop (𝓝 0) := by
    have hlim := tendsto_baseCombRate_div.const_mul (8 * R * B * L)
    rw [mul_zero] at hlim
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Real.norm_eq_abs]
    exact abs_combJump_sub_sampleJump_le hcont hsupp hB hL hR hN
  have h := h2.add h1
  rw [zero_add] at h
  refine h.congr fun N => ?_
  ring

/-! ### Weil's functional -/

/-- The packet as a test function of Weil's functional. -/
def packetTest (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    _root_.RHTower.WeilOneSided.WeilTestFn :=
  ⟨fun u => (f u : ℂ), Complex.ofRealCLM.contDiff.comp hf, hfc.comp_left Complex.ofReal_zero⟩

/-- The archimedean part of Weil's functional of a real packet, without the pole, is the mass
times `A(0)` plus the jump integral. -/
theorem weilArchRe_sub_pole_packet (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hsupp : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) (hB : ∀ u, |f u| ≤ B)
    (hL : ∀ u v, |f u - f v| ≤ L * |u - v|) :
    _root_.RHTower.WeilOneSided.weilArchRe
          (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1) -
        (_root_.RHTower.weilPoleTerm
          (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re =
      EF.gammaBracket 0 * packetAutocorr f 0 + ∫ x in Set.Ioi 0, levyJump f x := by
  have hcont := hf.continuous
  have h1 : ∫ u : ℝ, ‖(packetTest f hf hfc).1 u‖ ^ 2 = packetAutocorr f 0 := by
    rw [packetAutocorr]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show ‖((f u : ℝ) : ℂ)‖ ^ 2 = f u * f (u + 0)
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, add_zero]
    ring
  have h2 : ∀ x : ℝ, ∫ u : ℝ, ‖(packetTest f hf hfc).1 u - (packetTest f hf hfc).1 (u + x)‖ ^ 2 =
      2 * (packetAutocorr f 0 - packetAutocorr f x) := by
    intro x
    rw [← integral_sub_shift_sq hcont hfc x]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show ‖((f u : ℝ) : ℂ) - ((f (u + x) : ℝ) : ℂ)‖ ^ 2 = (f u - f (u + x)) ^ 2
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h3 : ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (_root_.RHTower.archLevyDensity x *
        ∫ u : ℝ, ‖(packetTest f hf hfc).1 u - (packetTest f hf hfc).1 (u + x)‖ ^ 2) =
      ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (levyJump f x) :=
    lintegral_congr fun x => by
      rw [h2 x, levyJump]
      congr 1
      ring
  rw [BiScaleUncertainty.weilArchRe_sub_pole_eq_levy_dirichlet, h1, h3,
    ← integral_eq_lintegral_of_nonneg_ae
      ((ae_restrict_mem measurableSet_Ioi).mono fun x hx => levyJump_nonneg hcont hfc hx)
      ((continuousOn_levyJump hcont hsupp hB hL).aestronglyMeasurable measurableSet_Ioi)]

/-- **Weil's archimedean form is the limit of the jets on invariant combs.** For a packet
`f ∈ C²_c(ℝ)`, the pairing of the jets on the comb `e^{ℤ/N}` minus the mass times
`log(N/2π)` tends to minus the archimedean part of Weil's functional of `f` without the pole. -/
theorem tendsto_combForm (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hR : 1 ≤ R)
    (hsupp : ∀ u : ℝ, (R : ℝ) ≤ |u| → f u = 0) :
    Tendsto (combForm f R) atTop
      (𝓝 (-(_root_.RHTower.WeilOneSided.weilArchRe
            (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1) -
          (_root_.RHTower.weilPoleTerm
            (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re))) := by
  have hcont := hf.continuous
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support hfc
  obtain ⟨C, hC⟩ := hf.lipschitzWith_of_hasCompactSupport hfc (by norm_num)
  have hB' : ∀ u, |f u| ≤ B := fun u => by
    rw [← Real.norm_eq_abs]
    exact hB u
  have hL : ∀ u v, |f u - f v| ≤ (C : ℝ) * |u - v| := fun u v => by
    have h := hC.dist_le_mul u v
    rwa [Real.dist_eq, Real.dist_eq] at h
  rw [weilArchRe_sub_pole_packet hf hfc hsupp hB' hL]
  have h1 := (tendsto_combAutocorr_zero hcont hsupp hB' hL hR).mul tendsto_baseCombRate_inv_nat
  have h2 := h1.sub (tendsto_combJump hcont hsupp hB' hL hR)
  have e : packetAutocorr f 0 * -EF.gammaBracket 0 - ∫ x in Set.Ioi 0, levyJump f x =
      -(EF.gammaBracket 0 * packetAutocorr f 0 + ∫ x in Set.Ioi 0, levyJump f x) := by ring
  rw [e] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (combForm_eq hsupp hN).symm

end Limit

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
