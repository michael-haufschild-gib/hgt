import GaloisForLFunctions.RHTower.DirichletHalfPlane
import GaloisForLFunctions.RHTower.DirichletAbscissa
import GaloisForLFunctions.RHTower.DirichletBddHolo
import GaloisForLFunctions.HTGeometry.MultivariableVitali

/-!
# Abel summation is uniform on bounded parts of the half-plane

The corpus already has the pointwise Abel theorem: bounded coefficient partial sums give
convergence of an ordinary Dirichlet series throughout `Re s > 0`.  What the analytic use of that
theorem needs is the *uniform* form, because a locally uniform limit of holomorphic functions is
holomorphic while a pointwise limit need not be.

The block estimate is the pointwise proof run on the segment `[M, N)` instead of `[0, N)`:

```text
‖∑_{M ≤ n < N} a_n (n+1)^{-s}‖  ≤  2C (1 + ‖s‖ / Re s) (M+1)^{-Re s} ,
```

with `C` a bound for the coefficient partial sums.  On a set where `Re s ≥ x > 0` and `‖s‖ ≤ R`
the prefactor is bounded and `(M+1)^{-Re s} ≤ (M+1)^{-x} → 0`, so the partial sums are uniformly
Cauchy there.  Every point of `Re s > 0` has such a neighbourhood, so the convergence is locally
uniform and the sum is holomorphic.

Uniform convergence on a *whole* closed half-plane is false in this generality — the factor `‖s‖`
is unbounded — which is exactly why the abscissa of uniform convergence is a strictly finer
invariant than the abscissa of convergence.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- The Abel block estimate: the tail of the partial sums past `M` is uniformly small. -/
theorem norm_dirichletPartialSum_sub_le {a : ℕ → ℂ} {C : ℝ}
    (hC : ∀ N, ‖∑ n ∈ Finset.range N, a n‖ ≤ C) {s : ℂ} (hs : 0 < s.re) {M N : ℕ}
    (hMN : M ≤ N) :
    ‖dirichletPartialSum a N s - dirichletPartialSum a M s‖
      ≤ 2 * C * (1 + ‖s‖ / s.re) * ((M : ℝ) + 1) ^ (-s.re) := by
  classical
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  set b : ℕ → ℂ := fun i => (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s) with hbdef
  have hnormb : ∀ i : ℕ, ‖b i‖ = ((i : ℝ) + 1) ^ (-s.re) := by
    intro i
    rw [hbdef]
    exact Complex.norm_cpow_eq_rpow_re_of_pos (by positivity) _ |>.trans (by simp)
  set K := N - M with hK
  set av : ℕ → ℂ := fun j => a (M + j) with hav
  set bt : ℕ → ℂ := fun j => b (M + j) with hbt
  have hsplit : dirichletPartialSum a N s - dirichletPartialSum a M s
      = ∑ j ∈ Finset.range K, bt j * av j := by
    rw [dirichletPartialSum, dirichletPartialSum,
      ← Finset.sum_Ico_eq_sub (fun n => a n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) hMN,
      Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr rfl fun j _ => by rw [hbt, hav, hbdef]; ring
  have hÃ : ∀ k : ℕ, ‖∑ j ∈ Finset.range k, av j‖ ≤ 2 * C := by
    intro k
    have heq : ∑ j ∈ Finset.range k, av j
        = (∑ n ∈ Finset.range (M + k), a n) - ∑ n ∈ Finset.range M, a n := by
      rw [← Finset.sum_Ico_eq_sub a (Nat.le_add_right M k), Finset.sum_Ico_eq_sum_range]
      simp [hav]
    rw [heq]
    exact le_trans (norm_sub_le _ _) (by linarith [hC (M + k), hC M])
  have habel := Finset.sum_range_by_parts bt av K
  simp only [smul_eq_mul] at habel
  rw [hsplit, habel]
  have hb1 : ‖bt (K - 1) * ∑ j ∈ Finset.range K, av j‖ ≤ 2 * C * ((M : ℝ) + 1) ^ (-s.re) := by
    rw [norm_mul]
    have h1 : ‖bt (K - 1)‖ ≤ ((M : ℝ) + 1) ^ (-s.re) := by
      rw [hbt, hnormb]
      refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
      push_cast
      have hn : (0 : ℝ) ≤ ((K - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    calc ‖bt (K - 1)‖ * ‖∑ j ∈ Finset.range K, av j‖
        ≤ ((M : ℝ) + 1) ^ (-s.re) * (2 * C) :=
          mul_le_mul h1 (hÃ K) (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)
      _ = 2 * C * ((M : ℝ) + 1) ^ (-s.re) := by ring
  have hb2 : ‖∑ i ∈ Finset.range (K - 1), (bt (i + 1) - bt i) * ∑ j ∈ Finset.range (i + 1), av j‖
      ≤ 2 * C * (‖s‖ / s.re) * ((M : ℝ) + 1) ^ (-s.re) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ i ∈ Finset.range (K - 1),
        ‖(bt (i + 1) - bt i) * ∑ j ∈ Finset.range (i + 1), av j‖
          ≤ (2 * C) * ((‖s‖ / s.re) *
            (((M : ℝ) + i + 1) ^ (-s.re) - ((M : ℝ) + i + 2) ^ (-s.re))) := by
      intro i _
      rw [norm_mul]
      have hincr : ‖bt (i + 1) - bt i‖
          ≤ (‖s‖ / s.re) * (((M : ℝ) + i + 1) ^ (-s.re) - ((M : ℝ) + i + 2) ^ (-s.re)) := by
        rw [norm_sub_rev, hbt, hbdef]
        have hcast1 : ((M + i : ℕ) : ℝ) + 1 = (M : ℝ) + i + 1 := by push_cast; ring
        have hcast2 : ((M + (i + 1) : ℕ) : ℝ) + 1 = (M : ℝ) + i + 2 := by push_cast; ring
        simp only [hcast1, hcast2]
        exact norm_cpow_neg_sub_le hs (by positivity) (by linarith)
      have hnn : (0:ℝ) ≤ (‖s‖ / s.re) *
          (((M : ℝ) + i + 1) ^ (-s.re) - ((M : ℝ) + i + 2) ^ (-s.re)) :=
        le_trans (norm_nonneg _) hincr
      calc ‖bt (i + 1) - bt i‖ * ‖∑ j ∈ Finset.range (i + 1), av j‖
          ≤ ((‖s‖ / s.re) *
              (((M : ℝ) + i + 1) ^ (-s.re) - ((M : ℝ) + i + 2) ^ (-s.re))) * (2 * C) :=
            mul_le_mul hincr (hÃ (i + 1)) (norm_nonneg _) hnn
        _ = (2 * C) * ((‖s‖ / s.re) *
              (((M : ℝ) + i + 1) ^ (-s.re) - ((M : ℝ) + i + 2) ^ (-s.re))) := by ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have htel : ∑ i ∈ Finset.range (K - 1),
        (((M : ℝ) + i + 1) ^ (-s.re) - ((M : ℝ) + i + 2) ^ (-s.re))
        ≤ ((M : ℝ) + 1) ^ (-s.re) := by
      have hf : ∀ i : ℕ, ((M : ℝ) + (i : ℕ) + 2) = ((M : ℝ) + ((i + 1 : ℕ) : ℝ) + 1) := by
        intro i
        push_cast
        ring
      rw [Finset.sum_congr rfl fun i _ => by rw [hf i]]
      rw [Finset.sum_range_sub' (fun i : ℕ => ((M : ℝ) + (i : ℕ) + 1) ^ (-s.re))]
      have : (0:ℝ) ≤ ((M : ℝ) + ((K - 1 : ℕ) : ℝ) + 1) ^ (-s.re) :=
        Real.rpow_nonneg (by positivity) _
      simp only [Nat.cast_zero, add_zero]
      linarith [this]
    have hsnn : (0:ℝ) ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) hs.le
    have h2C : (0:ℝ) ≤ 2 * C := by linarith
    calc (2 * C) * ((‖s‖ / s.re) * ∑ i ∈ Finset.range (K - 1),
            (((M : ℝ) + i + 1) ^ (-s.re) - ((M : ℝ) + i + 2) ^ (-s.re)))
        ≤ (2 * C) * ((‖s‖ / s.re) * (((M : ℝ) + 1) ^ (-s.re))) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htel hsnn) h2C
      _ = 2 * C * (‖s‖ / s.re) * ((M : ℝ) + 1) ^ (-s.re) := by ring
  calc ‖bt (K - 1) * (∑ j ∈ Finset.range K, av j)
          - ∑ i ∈ Finset.range (K - 1), (bt (i + 1) - bt i) * ∑ j ∈ Finset.range (i + 1), av j‖
      ≤ ‖bt (K - 1) * ∑ j ∈ Finset.range K, av j‖
        + ‖∑ i ∈ Finset.range (K - 1), (bt (i + 1) - bt i) * ∑ j ∈ Finset.range (i + 1), av j‖ :=
        norm_sub_le _ _
    _ ≤ 2 * C * ((M : ℝ) + 1) ^ (-s.re) + 2 * C * (‖s‖ / s.re) * ((M : ℝ) + 1) ^ (-s.re) := by
        exact add_le_add hb1 hb2
    _ = 2 * C * (1 + ‖s‖ / s.re) * ((M : ℝ) + 1) ^ (-s.re) := by ring


/-- The sum of a convergent ordinary Dirichlet series. -/
noncomputable def dirichletSum (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  limUnder atTop fun N => dirichletPartialSum a N s

theorem tendsto_dirichletSum {a : ℕ → ℂ} {s : ℂ} (h : DirichletConvergesAt a s) :
    Tendsto (fun N => dirichletPartialSum a N s) atTop (𝓝 (dirichletSum a s)) := by
  obtain ⟨L, hL⟩ := h
  have : dirichletSum a s = L := hL.limUnder_eq
  rw [this]
  exact hL

/-- The shifted coefficients of an ordinary Dirichlet series. -/
private def shiftCoeff (a : ℕ → ℂ) (s₀ : ℂ) : ℕ → ℂ :=
  fun n => a n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s₀)

private theorem dirichletPartialSum_shiftCoeff (a : ℕ → ℂ) (s₀ s : ℂ) (N : ℕ) :
    dirichletPartialSum (shiftCoeff a s₀) N (s - s₀) = dirichletPartialSum a N s := by
  refine Finset.sum_congr rfl fun n _ => ?_
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hne : ((((n : ℝ) + 1 : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hpos)
  rw [shiftCoeff, mul_assoc, ← Complex.cpow_add _ _ hne]
  congr 2
  ring

/-- **The tail estimate after a shift.** -/
theorem norm_dirichletSum_sub_partialSum_le {a : ℕ → ℂ} {s₀ : ℂ} {C : ℝ}
    (hC : ∀ N, ‖dirichletPartialSum a N s₀‖ ≤ C) {s : ℂ} (hs : s₀.re < s.re)
    (hconv : DirichletConvergesAt a s) (M : ℕ) :
    ‖dirichletSum a s - dirichletPartialSum a M s‖
      ≤ 2 * C * (1 + ‖s - s₀‖ / (s - s₀).re) * ((M : ℝ) + 1) ^ (-(s - s₀).re) := by
  have hre : 0 < (s - s₀).re := by
    rw [Complex.sub_re]; linarith
  have hC' : ∀ N, ‖∑ n ∈ Finset.range N, shiftCoeff a s₀ n‖ ≤ C := by
    intro N
    have : ∑ n ∈ Finset.range N, shiftCoeff a s₀ n = dirichletPartialSum a N s₀ := by
      refine Finset.sum_congr rfl fun n _ => rfl
    rw [this]
    exact hC N
  have hblock : ∀ N, M ≤ N →
      ‖dirichletPartialSum a N s - dirichletPartialSum a M s‖
        ≤ 2 * C * (1 + ‖s - s₀‖ / (s - s₀).re) * ((M : ℝ) + 1) ^ (-(s - s₀).re) := by
    intro N hMN
    have h := norm_dirichletPartialSum_sub_le hC' hre (M := M) (N := N) hMN
    rwa [dirichletPartialSum_shiftCoeff, dirichletPartialSum_shiftCoeff] at h
  have hlim : Tendsto (fun N => ‖dirichletPartialSum a N s - dirichletPartialSum a M s‖) atTop
      (𝓝 ‖dirichletSum a s - dirichletPartialSum a M s‖) :=
    ((tendsto_dirichletSum hconv).sub tendsto_const_nhds).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop M] with N hN
  exact hblock N hN

/-- **Locally uniform convergence to the right of a point of convergence.** -/
theorem tendstoLocallyUniformlyOn_dirichletPartialSum {a : ℕ → ℂ} {s₀ : ℂ}
    (h₀ : DirichletConvergesAt a s₀) :
    TendstoLocallyUniformlyOn (dirichletPartialSum a) (dirichletSum a) atTop
      {s : ℂ | s₀.re < s.re} := by
  obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le).1
    (h₀.choose_spec.cauchySeq.isBounded_range)
  have hCb : ∀ N, ‖dirichletPartialSum a N s₀‖ ≤ C := fun N => hC _ (Set.mem_range_self N)
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε s₁ hs₁
  have hs₁' : s₀.re < s₁.re := hs₁
  set δ : ℝ := (s₁.re - s₀.re) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set R : ℝ := ‖s₁ - s₀‖ + 1 with hRdef
  have hR : 0 < R := by rw [hRdef]; positivity
  set t : Set ℂ := {s : ℂ | s₀.re + δ < s.re ∧ ‖s - s₀‖ < R} with htdef
  have htopen : IsOpen t := by
    have h1 : IsOpen {s : ℂ | s₀.re + δ < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have h2 : IsOpen {s : ℂ | ‖s - s₀‖ < R} :=
      isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
    exact h1.inter h2
  have hs₁t : s₁ ∈ t := by
    constructor
    · rw [hδdef]; linarith
    · rw [hRdef]; linarith
  refine ⟨t, mem_nhdsWithin_of_mem_nhds (htopen.mem_nhds hs₁t), ?_⟩
  -- the uniform tail bound on `t`
  have hbound : ∀ M : ℕ, ∀ s ∈ t,
      ‖dirichletSum a s - dirichletPartialSum a M s‖
        ≤ 2 * |C| * (1 + R / δ) * ((M : ℝ) + 1) ^ (-δ) := by
    intro M s hst
    have hre : s₀.re < s.re := by
      have := hst.1
      linarith
    have hconv : DirichletConvergesAt a s := tendsto_dirichlet_partialSum_of_re_lt h₀ hre
    have hCb' : ∀ N, ‖dirichletPartialSum a N s₀‖ ≤ |C| := fun N =>
      le_trans (hCb N) (le_abs_self C)
    refine le_trans (norm_dirichletSum_sub_partialSum_le hCb' hre hconv M) ?_
    have hsre : δ < (s - s₀).re := by
      rw [Complex.sub_re]
      have := hst.1
      linarith
    have hsn : ‖s - s₀‖ < R := hst.2
    have hCa : (0:ℝ) ≤ 2 * |C| := by positivity
    have hd : (0:ℝ) < (s - s₀).re := lt_trans hδ hsre
    have h1 : ‖s - s₀‖ / (s - s₀).re ≤ R / δ := by
      refine (div_le_div_iff₀ hd hδ).mpr ?_
      nlinarith [norm_nonneg (s - s₀)]
    have h2 : ((M : ℝ) + 1) ^ (-(s - s₀).re) ≤ ((M : ℝ) + 1) ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hnn : (0:ℝ) ≤ ((M : ℝ) + 1) ^ (-(s - s₀).re) := Real.rpow_nonneg (by positivity) _
    have hfac : (0:ℝ) ≤ 1 + ‖s - s₀‖ / (s - s₀).re := by
      have := div_nonneg (norm_nonneg (s - s₀)) hd.le
      linarith
    calc 2 * |C| * (1 + ‖s - s₀‖ / (s - s₀).re) * ((M : ℝ) + 1) ^ (-(s - s₀).re)
        ≤ 2 * |C| * (1 + R / δ) * ((M : ℝ) + 1) ^ (-(s - s₀).re) := by
          have hle : (1 + ‖s - s₀‖ / (s - s₀).re) ≤ 1 + R / δ := by linarith
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hCa) hnn
      _ ≤ 2 * |C| * (1 + R / δ) * ((M : ℝ) + 1) ^ (-δ) := by
          have hpos : (0:ℝ) ≤ 2 * |C| * (1 + R / δ) := by positivity
          exact mul_le_mul_of_nonneg_left h2 hpos
  -- choose the cut
  have htend : Tendsto (fun M : ℕ => 2 * |C| * (1 + R / δ) * ((M : ℝ) + 1) ^ (-δ)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_nat_atTop hδ).comp (tendsto_add_atTop_nat 1)
    have h' : Tendsto (fun M : ℕ => ((M : ℝ) + 1) ^ (-δ)) atTop (𝓝 0) := by
      refine h.congr fun M => ?_
      simp [Function.comp]
    simpa using h'.const_mul (2 * |C| * (1 + R / δ))
  obtain ⟨M₀, hM₀⟩ := ((htend.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop 0)).exists
  filter_upwards [eventually_ge_atTop M₀] with M hM s hst
  rw [Complex.dist_eq]
  refine lt_of_le_of_lt (hbound M s hst) ?_
  refine lt_of_le_of_lt ?_ hM₀.1
  have hmono : ((M : ℝ) + 1) ^ (-δ) ≤ ((M₀ : ℝ) + 1) ^ (-δ) := by
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
    have : (M₀ : ℝ) ≤ (M : ℝ) := Nat.cast_le.mpr hM
    linarith
  have hpos : (0:ℝ) ≤ 2 * |C| * (1 + R / δ) := by positivity
  exact mul_le_mul_of_nonneg_left hmono hpos

/-- **The sum of a Dirichlet series is holomorphic to the right of any point of convergence.** -/
theorem differentiableOn_dirichletSum {a : ℕ → ℂ} {s₀ : ℂ} (h₀ : DirichletConvergesAt a s₀) :
    DifferentiableOn ℂ (dirichletSum a) {s : ℂ | s₀.re < s.re} :=
  (tendstoLocallyUniformlyOn_dirichletPartialSum h₀).differentiableOn
    (Filter.Eventually.of_forall fun N => (differentiable_dirichletPartialSum a N).differentiableOn)
    (isOpen_lt continuous_const Complex.continuous_re)

end GaloisForLFunctions.RHTower

end
