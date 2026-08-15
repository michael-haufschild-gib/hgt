import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCayleyDivisorLift

/-!
# The hard-edge Mehler--Heine law in the shifted-Xi Cayley coordinate

On the real line the Cayley coordinate

`z_a(α) = (a² − α²)/(a² + α²)`

is the cosine of twice the arctangent of `α/a`, so the first-kind Chebyshev polynomials evaluate to
pure phases,

`T_k(z_a(α)) = cos(2k·arctan(α/a))`.

Since `a·arctan(α/a) → α` as `a → ∞`, a degree growing at the hard-edge rate `2k/a → s` turns
Chebyshev waves into Fourier waves:

`T_k(z_a(α)) → cos(sα)`.

Polynomial degree becomes exponential type at exactly the scale `k ≍ a`.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- The real hard-edge Cayley coordinate is a cosine of twice an arctangent. -/
theorem xiHardEdgeCayleyCoordinate_real_eq_cos {a : ℝ} (ha : 0 < a) (α : ℝ) :
    (a ^ 2 - α ^ 2) / (a ^ 2 + α ^ 2) = Real.cos (2 * Real.arctan (α / a)) := by
  have hden : (0 : ℝ) < a ^ 2 + α ^ 2 := by positivity
  have hx : (1 : ℝ) + (α / a) ^ 2 = (a ^ 2 + α ^ 2) / a ^ 2 := by
    field_simp
  have hsqrt : Real.sqrt (1 + (α / a) ^ 2) ^ 2 = 1 + (α / a) ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [Real.cos_two_mul, Real.cos_arctan, div_pow, one_pow, hsqrt, hx]
  field_simp
  ring

/-- **(HEPW.4) The Chebyshev--Cayley phase identity on the real line.** -/
theorem chebyshevT_eval_xiHardEdgeCayleyCoordinate_real {a : ℝ} (ha : 0 < a) (α : ℝ) (k : ℕ) :
    (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval ((a ^ 2 - α ^ 2) / (a ^ 2 + α ^ 2))
      = Real.cos (2 * (k : ℝ) * Real.arctan (α / a)) := by
  rw [xiHardEdgeCayleyCoordinate_real_eq_cos ha α, Polynomial.Chebyshev.T_real_cos]
  congr 1
  push_cast
  ring

/-- The arctangent is asymptotically linear at the origin, in slope form. -/
theorem tendsto_arctan_slope_zero :
    Tendsto (fun u : ℝ => Real.arctan u / u) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
  have hderiv : HasDerivAt Real.arctan (1 / (1 + (0 : ℝ) ^ 2)) 0 := Real.hasDerivAt_arctan 0
  have hslope := hasDerivAt_iff_tendsto_slope.1 hderiv
  have hone : (1 : ℝ) / (1 + (0 : ℝ) ^ 2) = 1 := by norm_num
  rw [hone] at hslope
  refine hslope.congr fun u => ?_
  rw [slope_def_field, Real.arctan_zero]
  simp

/-- The hard-edge phase recovers the spectral coordinate: `a·arctan(α/a) → α`. -/
theorem tendsto_mul_arctan_div_atTop {A : ℕ → ℝ} (hA : Tendsto A atTop atTop) (α : ℝ) :
    Tendsto (fun j => A j * Real.arctan (α / A j)) atTop (nhds α) := by
  rcases eq_or_ne α 0 with rfl | hα
  · refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with j
    simp
  · have hpos : ∀ᶠ j in atTop, 0 < A j := hA.eventually_gt_atTop 0
    have hu : Tendsto (fun j => α / A j) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hA
    have huNe : ∀ᶠ j in atTop, α / A j ∈ ({(0 : ℝ)}ᶜ : Set ℝ) := by
      filter_upwards [hpos] with j hj
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact div_ne_zero hα (ne_of_gt hj)
    have huW : Tendsto (fun j => α / A j) atTop (nhdsWithin 0 {(0 : ℝ)}ᶜ) :=
      tendsto_nhdsWithin_iff.2 ⟨hu, huNe⟩
    have hcomp := tendsto_arctan_slope_zero.comp huW
    have hlimit : Tendsto
        (fun j => α * (Real.arctan (α / A j) / (α / A j))) atTop (nhds (α * 1)) :=
      hcomp.const_mul α
    rw [mul_one] at hlimit
    refine hlimit.congr' ?_
    filter_upwards [hpos] with j hj
    have hAj : A j ≠ 0 := ne_of_gt hj
    field_simp

/-- **(HEPW.5) The hard-edge Mehler--Heine law.**  When the degree grows at the hard-edge rate
`2k/a → s`, the Chebyshev wave in the Cayley coordinate becomes the Fourier wave `cos(sα)`. -/
theorem tendsto_chebyshevT_xiHardEdgeCayleyCoordinate_real
    {A : ℕ → ℝ} (hA : Tendsto A atTop atTop) (hApos : ∀ j, 0 < A j)
    {k : ℕ → ℕ} {s : ℝ} (hk : Tendsto (fun j => 2 * (k j : ℝ) / A j) atTop (nhds s)) (α : ℝ) :
    Tendsto (fun j =>
        (Polynomial.Chebyshev.T ℝ ((k j : ℕ) : ℤ)).eval
          ((A j ^ 2 - α ^ 2) / (A j ^ 2 + α ^ 2)))
      atTop (nhds (Real.cos (s * α))) := by
  have hphase := tendsto_mul_arctan_div_atTop hA α
  have harg : Tendsto (fun j => (2 * (k j : ℝ) / A j) * (A j * Real.arctan (α / A j)))
      atTop (nhds (s * α)) := hk.mul hphase
  have hcos := (Real.continuous_cos.tendsto (s * α)).comp harg
  refine hcos.congr fun j => ?_
  rw [Function.comp_apply, chebyshevT_eval_xiHardEdgeCayleyCoordinate_real (hApos j) α (k j)]
  congr 1
  have hAj : A j ≠ 0 := ne_of_gt (hApos j)
  field_simp

end RHTower

end
