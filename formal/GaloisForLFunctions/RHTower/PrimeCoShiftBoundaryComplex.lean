import GaloisForLFunctions.RHTower.PrimeCoShiftModel
import GaloisForLFunctions.RHTower.DirichletAbel
import GaloisForLFunctions.RHTower.JonquiereExpansion

/-!
# The regularized additive boundary complex of the prime co-shift eigenline

For `1/2 < Re s < 1` every vector of the common prime eigenline `L_s = ℂ Ψ_s` has a boundary wave

```
F_x(θ) = ∑_{n ≥ 1} x_n e^{i n θ},
```

which converges for every phase `θ ∈ (0, π]` — its coefficients are `x_1 n^{-s}` and the geometric
partial sums are bounded, so summation by parts applies.  Its sum is `x_1 Li_s(e^{iθ})`.

Jonquière's expansion subtracts the universal singular branch:

```
RegEv_s(x) = lim_{θ → 0+} [ F_x(θ) - x_1 Γ(1-s) e^{iπ(1-s)/2} θ^{s-1} ] = x_1 ζ(s).
```

The two-term complex `0 → L_s → ℂ → 0` with differential `RegEv_s` is therefore an isomorphism off
the zeta divisor and has one-dimensional kernel and cokernel on it.  Its Fredholm index is `0` in
both cases: kernel and cokernel are born together, so no ordinary index can select the divisor.
-/

open Complex HurwitzZeta Filter Topology Set
open RHTower

namespace RHTower.PrimeCoShift

noncomputable section

/-- The `N`-th Fourier partial sum of the boundary wave of `x` at phase `θ`. -/
def boundaryPartialSum (x : H) (θ : ℝ) (N : ℕ) : ℂ :=
  ∑ i ∈ Finset.range N,
    x i.succPNat * Complex.exp (Complex.I * (((i : ℝ) + 1 : ℝ) : ℂ) * (θ : ℂ))

theorem phase_simp {θ : ℝ} :
    2 * (Real.pi : ℂ) * Complex.I * ((θ / (2 * Real.pi) : ℝ) : ℂ) = (θ : ℂ) * Complex.I := by
  have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

theorem exp_ne_one_of_mem_Ioc {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((θ / (2 * Real.pi) : ℝ) : ℂ)) ≠ 1 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [phase_simp]
  intro hcon
  rw [Complex.exp_eq_one_iff] at hcon
  obtain ⟨n, hn⟩ := hcon
  have h2 : ((θ : ℂ) - (n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I = 0 := by
    rw [sub_mul, hn]; ring
  have hth : (θ : ℂ) = (n : ℂ) * (2 * (Real.pi : ℂ)) := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h Complex.I_ne_zero
  have hthr : θ = (n : ℝ) * (2 * Real.pi) := by exact_mod_cast hth
  have hn0 : (0 : ℝ) < (n : ℝ) := by nlinarith
  have hn1 : (n : ℝ) < 1 := by nlinarith
  have hz0 : (0 : ℤ) < n := by exact_mod_cast hn0
  have hz1 : (n : ℤ) < 1 := by exact_mod_cast hn1
  omega

theorem coe_ne_zero_unitAddCircle {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi) :
    (((θ / (2 * Real.pi) : ℝ)) : UnitAddCircle) ≠ 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  intro hcon
  rw [AddCircle.coe_eq_zero_iff] at hcon
  obtain ⟨n, hn⟩ := hcon
  have hval : θ / (2 * Real.pi) = (n : ℝ) := by
    rw [← hn]; simp
  have hlt : (0 : ℝ) < θ / (2 * Real.pi) := by positivity
  have hlt1 : θ / (2 * Real.pi) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  rw [hval] at hlt hlt1
  have hz0 : (0 : ℤ) < n := by exact_mod_cast hlt
  have hz1 : (n : ℤ) < 1 := by exact_mod_cast hlt1
  omega

/-- **The boundary wave of an eigenvector.**  The Fourier partial sums converge to
`x_1 Li_s(e^{iθ})` for every phase in `(0, π]`. -/
theorem tendsto_boundaryPartialSum {s : ℂ} (hs : 0 < s.re) {x : H}
    (hx : x ∈ eigenSubmodule s) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi) :
    Tendsto (boundaryPartialSum x θ) atTop
      (𝓝 (x 1 * expZeta (((θ / (2 * Real.pi) : ℝ)) : UnitAddCircle) s)) := by
  set a : ℝ := θ / (2 * Real.pi) with ha
  have hane : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)) ≠ 1 :=
    exp_ne_one_of_mem_Ioc hθ0 hθ1
  have ha0 : ((a : ℝ) : UnitAddCircle) ≠ 0 := coe_ne_zero_unitAddCircle hθ0 hθ1
  have habel := tendsto_abelDirichlet (norm_coeffPartial_expCoeff_le hane) hs
  have hEq := abelDirichlet_eq_expZeta ha0 hane hs
  rw [hEq] at habel
  have hpart : ∀ N : ℕ, boundaryPartialSum x θ N
      = x 1 * ∑ i ∈ Finset.range N, (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s) * expCoeff a i := by
    intro N
    rw [Finset.mul_sum, boundaryPartialSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcoord := eigen_coordinate hx i.succPNat
    have hcast : (((i.succPNat : ℕ+) : ℕ) : ℂ) = (((i : ℝ) + 1 : ℝ) : ℂ) := by
      rw [Nat.succPNat_coe]
      push_cast
      ring
    have hexp : Complex.exp (Complex.I * (((i : ℝ) + 1 : ℝ) : ℂ) * (θ : ℂ)) = expCoeff a i := by
      rw [expCoeff, ← Complex.exp_nat_mul]
      congr 1
      rw [ha, phase_simp]
      push_cast
      ring
    rw [hcoord, hcast, hexp]
    ring
  have := habel.const_mul (x 1)
  exact this.congr fun N => (hpart N).symm

/-- **The regularized additive boundary value is `x₁ ζ(s)`.** -/
theorem tendsto_regularized_boundary {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (x : H) :
    Tendsto (fun θ : ℝ => x 1 * expZeta (((θ / (2 * Real.pi) : ℝ)) : UnitAddCircle) s
        - x 1 * (jonquiereLead s * ((θ : ℝ) : ℂ) ^ (s - 1)))
      (𝓝[>] (0 : ℝ)) (𝓝 (x 1 * riemannZeta s)) := by
  have hbound : ∀ θ ∈ Ioc (0 : ℝ) Real.pi,
      ‖(x 1 * expZeta (((θ / (2 * Real.pi) : ℝ)) : UnitAddCircle) s
          - x 1 * (jonquiereLead s * ((θ : ℝ) : ℂ) ^ (s - 1))) - x 1 * riemannZeta s‖
        ≤ ‖x 1‖ * (jonquiereConst s * θ) := by
    intro θ hθ
    have h := norm_expZeta_sub_jonquiere_le h0 h1 hθ.1 hθ.2
    have hrw : (x 1 * expZeta (((θ / (2 * Real.pi) : ℝ)) : UnitAddCircle) s
          - x 1 * (jonquiereLead s * ((θ : ℝ) : ℂ) ^ (s - 1))) - x 1 * riemannZeta s
        = x 1 * (expZeta (((θ / (2 * Real.pi) : ℝ)) : UnitAddCircle) s
            - (jonquiereLead s * ((θ : ℝ) : ℂ) ^ (s - 1) + riemannZeta s)) := by ring
    rw [hrw, norm_mul]
    exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
  have hsq : Tendsto (fun θ : ℝ => ‖x 1‖ * (jonquiereConst s * θ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have : Tendsto (fun θ : ℝ => ‖x 1‖ * (jonquiereConst s * θ)) (𝓝 (0 : ℝ)) (𝓝 0) := by
      have hc : Continuous fun θ : ℝ => ‖x 1‖ * (jonquiereConst s * θ) := by fun_prop
      simpa using hc.tendsto 0
    exact this.mono_left nhdsWithin_le_nhds
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hsq
  have hev : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Ioc (0 : ℝ) Real.pi := by
    have h1' : Ioo (0 : ℝ) Real.pi ∈ 𝓝[>] (0 : ℝ) :=
      Ioo_mem_nhdsGT Real.pi_pos
    filter_upwards [h1'] with θ hθ using ⟨hθ.1, hθ.2.le⟩
  filter_upwards [hev] with θ hθ using hbound θ hθ

/-! ### The two-term reduced boundary complex -/

/-- The regularized additive boundary evaluation on the common prime eigenline. -/
def regEv (s : ℂ) : eigenSubmodule s →ₗ[ℂ] ℂ where
  toFun x := (x : H) 1 * riemannZeta s
  map_add' x y := by
    simp only [Submodule.coe_add, lp.coeFn_add, Pi.add_apply]
    ring
  map_smul' c x := by
    simp only [Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

@[simp] theorem regEv_apply (s : ℂ) (x : eigenSubmodule s) :
    regEv s x = (x : H) 1 * riemannZeta s := rfl

/-- **The source definition of the regularized boundary evaluation computes `regEv`.** -/
theorem tendsto_regEv {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (x : eigenSubmodule s) :
    Tendsto (fun θ : ℝ => (x : H) 1 * expZeta (((θ / (2 * Real.pi) : ℝ)) : UnitAddCircle) s
        - (x : H) 1 * (jonquiereLead s * ((θ : ℝ) : ℂ) ^ (s - 1)))
      (𝓝[>] (0 : ℝ)) (𝓝 (regEv s x)) :=
  tendsto_regularized_boundary h0 h1 (x : H)

theorem eigen_eq_zero_of_apply_one_eq_zero {s : ℂ} {x : H} (hx : x ∈ eigenSubmodule s)
    (h1 : x 1 = 0) : x = 0 := by
  apply lp.ext
  funext n
  rw [eigen_coordinate hx n, h1]
  simp

theorem regEv_ker_eq_bot {s : ℂ} (hz : riemannZeta s ≠ 0) :
    LinearMap.ker (regEv s) = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  have h : (x : H) 1 * riemannZeta s = 0 := hx
  have h1 : (x : H) 1 = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h hz
  have : (x : H) = 0 := eigen_eq_zero_of_apply_one_eq_zero x.2 h1
  exact Submodule.mem_bot ℂ |>.mpr (Subtype.ext this)

theorem regEv_range_eq_top {s : ℂ} (hs : 1 / 2 < s.re) (hz : riemannZeta s ≠ 0) :
    LinearMap.range (regEv s) = ⊤ := by
  refine LinearMap.range_eq_top.mpr fun c => ?_
  refine ⟨⟨(c / riemannZeta s) • groundState s, Submodule.smul_mem _ _
    (groundState_mem_eigenSubmodule hs)⟩, ?_⟩
  have hval : (((c / riemannZeta s) • groundState s : H)) 1 = c / riemannZeta s := by
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, groundState_one hs, mul_one]
  show (((c / riemannZeta s) • groundState s : H)) 1 * riemannZeta s = c
  rw [hval]
  field_simp

theorem regEv_eq_zero_of_zeta_eq_zero {s : ℂ} (hz : riemannZeta s = 0) : regEv s = 0 := by
  ext x
  simp [regEv, hz]

theorem finiteDimensional_eigenSubmodule {s : ℂ} (hs : 1 / 2 < s.re) :
    FiniteDimensional ℂ (eigenSubmodule s) := by
  rw [eigenSubmodule_eq_span hs]
  exact FiniteDimensional.span_of_finite ℂ (Set.finite_singleton _)

theorem finrank_eigenSubmodule {s : ℂ} (hs : 1 / 2 < s.re) :
    Module.finrank ℂ (eigenSubmodule s) = 1 := by
  rw [eigenSubmodule_eq_span hs]
  exact finrank_span_singleton (groundState_ne_zero hs)

/-- **The reduced boundary complex is acyclic off the zeta divisor.** -/
theorem regEv_bijective {s : ℂ} (hs : 1 / 2 < s.re) (hz : riemannZeta s ≠ 0) :
    Function.Bijective (regEv s) := by
  constructor
  · exact LinearMap.ker_eq_bot.mp (regEv_ker_eq_bot hz)
  · exact LinearMap.range_eq_top.mp (regEv_range_eq_top hs hz)

/-- **On the divisor the kernel and cokernel are both one dimensional.** -/
theorem finrank_ker_regEv_of_zeta_eq_zero {s : ℂ} (hs : 1 / 2 < s.re)
    (hz : riemannZeta s = 0) : Module.finrank ℂ (LinearMap.ker (regEv s)) = 1 := by
  haveI := finiteDimensional_eigenSubmodule hs
  rw [regEv_eq_zero_of_zeta_eq_zero hz, LinearMap.ker_zero, finrank_top]
  exact finrank_eigenSubmodule hs

theorem finrank_quotient_range_add {s : ℂ} :
    Module.finrank ℂ (ℂ ⧸ LinearMap.range (regEv s))
      + Module.finrank ℂ (LinearMap.range (regEv s)) = 1 := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range (regEv s))
  simpa using h

/-- **The Fredholm index of the reduced boundary complex is always zero.** -/
theorem regEv_index_zero {s : ℂ} (hs : 1 / 2 < s.re) :
    (Module.finrank ℂ (LinearMap.ker (regEv s)) : ℤ)
      - (Module.finrank ℂ (ℂ ⧸ LinearMap.range (regEv s)) : ℤ) = 0 := by
  haveI := finiteDimensional_eigenSubmodule hs
  by_cases hz : riemannZeta s = 0
  · have hker := finrank_ker_regEv_of_zeta_eq_zero hs hz
    have hrange : LinearMap.range (regEv s) = ⊥ := by
      rw [regEv_eq_zero_of_zeta_eq_zero hz, LinearMap.range_zero]
    have hq : Module.finrank ℂ (ℂ ⧸ LinearMap.range (regEv s)) = 1 := by
      have h := finrank_quotient_range_add (s := s)
      rw [hrange] at h ⊢
      simpa using h
    rw [hker, hq]
    ring
  · have hker : Module.finrank ℂ (LinearMap.ker (regEv s)) = 0 := by
      rw [regEv_ker_eq_bot hz]
      simp
    have hrange : LinearMap.range (regEv s) = ⊤ := regEv_range_eq_top hs hz
    have hq : Module.finrank ℂ (ℂ ⧸ LinearMap.range (regEv s)) = 0 := by
      have h := finrank_quotient_range_add (s := s)
      rw [hrange] at h ⊢
      simp at h ⊢
      omega
    rw [hker, hq]
    ring

end

end RHTower.PrimeCoShift
