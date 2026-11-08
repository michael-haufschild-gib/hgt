import GaloisForLFunctions.SurfaceOfSpecZ.TheArchimedeanPlaceIsNotToric

/-!
# The primes are the jumps of the Hecke kernel

A Hecke-equivariant geometry assigns to the Frobenius graphs `Γ_m, Γ_n` an intersection
`√(mn) F(log n − log m)` for a kernel `F` on the log-ratio line. Every geometry with continuous moduli
in the boost direction has a continuous kernel: the mixed area `A(K, B_u K)` of a planar convex body
and its boost, the hyperbolic orbital integral of a Green function, the toric cusp count
`e^{−|u|/2}`.

The Frobenius intersection of `Spec ℤ` is not of this kind (`not_exists_continuous_heckeKernel`). Its
archimedean part is the continuous function `ω(|u|)` (`frobeniusIntersection_div_sqrt_of_not_dvd`), and
its prime part lives on divisible pairs only: along the pairs `(2j + 1, j)`, whose ratios tend to `2`
and are never integers, there is no prime contribution, while at `(2, 1)` the point of `ℙ¹_ℤ` over
`2` adds `log 2/√2`. So a continuous `F` would have to equal `ω` at `log 2` and `ω + log 2/√2` there.

The primes are jump discontinuities of the Hecke kernel at the logarithms of prime powers. Geometries
whose Frobenius graphs move continuously with the real degree `log n` realize only archimedean
channels; the surface of `Spec ℤ` must see `n` as an integer, as the torsion orbits of `ℙ¹_ℤ` do.
-/

open Filter Topology
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticEffectivityTheory

/-- Off divisible pairs the Frobenius intersection is purely archimedean. -/
theorem frobeniusIntersection_div_sqrt_of_not_dvd {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h1 : ¬ m ∣ n) (h2 : ¬ n ∣ m) :
    frobeniusIntersection m n / Real.sqrt ((m : ℝ) * n) =
      RHTower.archLevyDensity |Real.log m - Real.log n| := by
  have hmn : m ≠ n := fun h => h1 (h ▸ dvd_rfl)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt ((m : ℝ) * n) := Real.sqrt_pos.mpr (mul_pos hm' hn')
  rw [frobeniusIntersection_eq hm hn hmn, orbitIntersection_eq hm hn hmn, if_neg h2, if_neg h1,
    mul_zero, add_zero, ← sqrt_mul_archLevyDensity hm' hn', mul_div_cancel_left₀ _ hs.ne']

/-- At `(2, 1)` the point over `2` adds `log 2` to the cusp and its jets. -/
theorem frobeniusIntersection_two_one : frobeniusIntersection 2 1 = 4 / 3 + Real.log 2 := by
  rw [frobeniusIntersection_eq (by norm_num) (by norm_num) (by norm_num),
    orbitIntersection_eq (by norm_num) (by norm_num) (by norm_num), gcdTwist_of_coprime (by norm_num)]
  norm_num [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]

/-- The archimedean density at `log 2`: one cusp and a jet tower, `√2 ω(log 2) = 4/3`. -/
theorem archLevyDensity_log_two : RHTower.archLevyDensity |Real.log 2| * Real.sqrt 2 = 4 / 3 := by
  have ha := sqrt_mul_archLevyDensity (m := (1 : ℝ)) (n := 2) one_pos (by norm_num)
  rw [Real.log_one, zero_sub, abs_neg, one_mul] at ha
  rw [mul_comm, ha]
  norm_num

/-- The ratios `(2j + 1)/j` tend to `2`. -/
theorem tendsto_log_ratio :
    Tendsto (fun j : ℕ => Real.log ((2 * j + 1 : ℕ) : ℝ) - Real.log (j : ℝ)) atTop
      (𝓝 (Real.log 2)) := by
  have hq : Tendsto (fun j : ℕ => ((2 * j + 1 : ℕ) : ℝ) / (j : ℝ)) atTop (𝓝 2) := by
    have h : Tendsto (fun j : ℕ => (2 : ℝ) + 1 / (j : ℝ)) atTop (𝓝 (2 + 0)) :=
      tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat)
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hj' : (0 : ℝ) < j := by exact_mod_cast hj
    push_cast
    field_simp
  have hlog := (Real.continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp hq
  refine hlog.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with j hj
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  simp only [Function.comp]
  rw [Real.log_div (by positivity) hj'.ne']

/-- `j ∤ 2j + 1` and `2j + 1 ∤ j` for `j ≥ 2`. -/
theorem not_dvd_pair {j : ℕ} (hj : 2 ≤ j) : ¬ j ∣ 2 * j + 1 ∧ ¬ (2 * j + 1) ∣ j := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : j ∣ 1 := (Nat.dvd_add_right (dvd_mul_left j 2)).mp h
    have := Nat.le_of_dvd one_pos this
    omega
  · have := Nat.le_of_dvd (by omega) h
    omega

/-- **The primes are the jumps of the Hecke kernel.** No continuous kernel `F` on the log-ratio line
gives the Frobenius intersections of `Spec ℤ` as `√(mn) F(log m − log n)`. -/
theorem not_exists_continuous_heckeKernel :
    ¬ ∃ F : ℝ → ℝ, Continuous F ∧ ∀ m n : ℕ, 0 < m → 0 < n → m ≠ n →
      frobeniusIntersection m n = Real.sqrt ((m : ℝ) * n) * F (Real.log m - Real.log n) := by
  rintro ⟨F, hF, hFI⟩
  have hdiv : ∀ m n : ℕ, 0 < m → 0 < n → m ≠ n →
      F (Real.log m - Real.log n) = frobeniusIntersection m n / Real.sqrt ((m : ℝ) * n) := by
    intro m n hm hn hmn
    have hs : 0 < Real.sqrt ((m : ℝ) * n) := Real.sqrt_pos.mpr (by positivity)
    rw [hFI m n hm hn hmn, mul_div_cancel_left₀ _ hs.ne']
  -- along `(2j + 1, j)` the kernel is the archimedean density
  have hseq : ∀ᶠ j : ℕ in atTop, F (Real.log ((2 * j + 1 : ℕ) : ℝ) - Real.log (j : ℝ)) =
      RHTower.archLevyDensity |Real.log ((2 * j + 1 : ℕ) : ℝ) - Real.log (j : ℝ)| := by
    filter_upwards [eventually_ge_atTop 2] with j hj
    obtain ⟨h1, h2⟩ := not_dvd_pair hj
    rw [hdiv _ _ (by omega) (by omega) (by omega),
      frobeniusIntersection_div_sqrt_of_not_dvd (by omega) (by omega) h2 h1]
  -- the archimedean density is continuous at `log 2 > 0`
  have hω : ContinuousAt (fun u : ℝ => RHTower.archLevyDensity |u|) (Real.log 2) := by
    have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hden : (1 : ℝ) - Real.exp (-2 * |Real.log 2|) ≠ 0 := by
      rw [abs_of_pos hpos]
      have : Real.exp (-2 * Real.log 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    unfold RHTower.archLevyDensity
    exact ((Real.continuous_exp.comp (continuous_abs.neg.div_const 2)).continuousAt).div
      ((continuous_const.sub (Real.continuous_exp.comp (continuous_abs.const_mul (-2)))).continuousAt)
      hden
  have hl := tendsto_log_ratio
  have hlim1 : Tendsto (fun j : ℕ => F (Real.log ((2 * j + 1 : ℕ) : ℝ) - Real.log (j : ℝ))) atTop
      (𝓝 (F (Real.log 2))) := (hF.tendsto _).comp hl
  have hlim2 : Tendsto (fun j : ℕ => F (Real.log ((2 * j + 1 : ℕ) : ℝ) - Real.log (j : ℝ))) atTop
      (𝓝 (RHTower.archLevyDensity |Real.log 2|)) := (hω.tendsto.comp hl).congr' (hseq.mono
        fun j hj => hj.symm)
  have heq := tendsto_nhds_unique hlim1 hlim2
  -- at `(2, 1)` the kernel carries the prime `2`
  have h21 := hdiv 2 1 (by norm_num) (by norm_num) (by norm_num)
  rw [frobeniusIntersection_two_one] at h21
  simp only [Nat.cast_ofNat, Nat.cast_one, Real.log_one, sub_zero, mul_one] at h21
  have ha := archLevyDensity_log_two
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [← heq, h21, div_mul_cancel₀ _ hs.ne'] at ha
  linarith [Real.log_pos (one_lt_two : (1 : ℝ) < 2)]

end GaloisForLFunctions.SurfaceOfSpecZ

#print axioms GaloisForLFunctions.SurfaceOfSpecZ.not_exists_continuous_heckeKernel
