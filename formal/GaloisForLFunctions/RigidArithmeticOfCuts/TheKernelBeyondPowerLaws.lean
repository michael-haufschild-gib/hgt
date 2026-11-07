import GaloisForLFunctions.RigidArithmeticOfCuts.ZerosAreTheKernelOfTheCutSystem
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.ReturnsAreReturnsOfThePrimes
import GaloisForLFunctions.RHTower.ZetaEulerRegionDiscSeamMargin
import GaloisForLFunctions.RHTower.NymanBeurlingCriterion

/-!
# The kernel beyond power laws

The kernel of the cut system contains the power tails at zeros. What else does it contain?

* **Superpositions.** Let `U = Σ_i c_i U_{s_i}` be an absolutely convergent superposition of modes in a strip `0 < σ₀ ≤ Re s ≤ σ₁ < 1`, with distinct `s_i` and well-ordered
  abscissae. Then `U` solves the homogeneous system iff `ζ(s_i) = 0` wherever `c_i ≠ 0` (`superposition_kernel_iff`). So in this class the kernel is exactly spanned by zeros.
  The mechanism is `ε ζ(1 + ε + b) → 1_{b = 0}` as `ε → 0+`, for `Re b ≥ 0`: a Dirichlet mean in `k` over the system `Σ d_i k^{w_i} = D`, which separates the
  exponents of the top abscissa (`eq_zero_of_sum_cpow_eq_const`).
* **Finite energy.** In the energy space `Σ (j+1)² |U(j)|² < ∞` the modes with `Re s > ½` lie in the kernel with mass `1`. So if every finite-energy kernel vector has mass `0`, RH holds
  (`riemannHypothesis_of_energy_kernel`). This is the Nyman–Beurling criterion read from the dual side: the sawteeth `(r mod k)/r` are the generators, and the kernel is their orthogonal complement.

The kernel is thus an equidistribution space: a kernel vector is a conditionally convergent measure on `ℕ` with `T(kℕ) = T(ℕ)/k`, and no absolutely convergent such measure exists (`eq_zero_of_uniform_multiples`).
-/

open Filter Topology Complex
open GaloisForLFunctions.ArithmeticAuxiliaryDynamics

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

variable {ι : Type*}

/-- `ε ζ(1 + ε + b)` is bounded for `Re b ≥ 0`, `0 < ε ≤ 1`. -/
private lemma norm_mul_zeta_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {b : ℂ} (hb : 0 ≤ b.re) :
    ‖(ε : ℂ) * riemannZeta (1 + ε + b)‖ ≤ 2 := by
  have hre : 1 + ε ≤ (1 + (ε : ℂ) + b).re := by
    simp
    linarith
  have h := _root_.RHTower.norm_riemannZeta_le_of_le_re (σ₁ := 1 + ε) (by linarith) hre
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.le]
  have h2 : (1 : ℝ) + ε - 1 = ε := by ring
  rw [h2] at h
  calc ε * ‖riemannZeta (1 + (ε : ℂ) + b)‖ ≤ ε * (1 + 1 / ε) := mul_le_mul_of_nonneg_left h hε.le
    _ = ε + 1 := by field_simp
    _ ≤ 2 := by linarith

private lemma tendsto_ofReal_nhdsGT : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
  have h : Continuous fun ε : ℝ => (ε : ℂ) := Complex.continuous_ofReal
  have h2 := h.tendsto 0
  rw [Complex.ofReal_zero] at h2
  exact h2.mono_left nhdsWithin_le_nhds

/-- The residue at `1`, along the real direction. -/
private lemma tendsto_mul_zeta_one :
    Tendsto (fun ε : ℝ => (ε : ℂ) * riemannZeta (1 + ε + 0)) (𝓝[>] 0) (𝓝 1) := by
  have h := riemannZeta_residue_one
  have hmap : Tendsto (fun ε : ℝ => (1 + (ε : ℂ) + 0)) (𝓝[>] 0) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := (tendsto_ofReal_nhdsGT.const_add (1 : ℂ))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : (0 : ℝ) < ε := hε
      intro h1
      have h2 : (ε : ℂ) = 0 := by simpa using h1
      exact hε0.ne' (by exact_mod_cast h2)
  refine (h.comp hmap).congr fun ε => ?_
  simp

/-- Off the pole the mean vanishes. -/
private lemma tendsto_mul_zeta_of_ne {b : ℂ} (hb : b ≠ 0) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * riemannZeta (1 + ε + b)) (𝓝[>] 0) (𝓝 0) := by
  have hpt : (1 : ℂ) + (0 : ℝ) + b ≠ 1 := by
    simpa using hb
  have hc : ContinuousAt riemannZeta (1 + ((0 : ℝ) : ℂ) + b) :=
    (differentiableAt_riemannZeta hpt).continuousAt
  have hf : Tendsto (fun ε : ℝ => (1 + (ε : ℂ) + b)) (𝓝[>] 0) (𝓝 (1 + ((0 : ℝ) : ℂ) + b)) := by
    have h1 : Continuous fun ε : ℝ => (1 + (ε : ℂ) + b) := by fun_prop
    exact (h1.tendsto 0).mono_left nhdsWithin_le_nhds
  have h2 := tendsto_ofReal_nhdsGT.mul (hc.tendsto.comp hf)
  rw [zero_mul] at h2
  exact h2

/-- **The top abscissa separates.** Suppose `Σ_i d_i k^{w_i} = D` for all `k ≥ 1`, with `d` absolutely summable. If `w_{i₀}` has maximal real part among the nonzero `d_i`, and
that real part is positive, then `d_{i₀} = 0`. -/
theorem eq_zero_of_sum_cpow_eq_const {d w : ι → ℂ} (hw : Function.Injective w)
    (hd : Summable fun i => ‖d i‖) {D : ℂ}
    (hrel : ∀ k : ℕ, HasSum (fun i => d i * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (w i)) D) {i₀ : ι}
    (hmax : ∀ i, d i ≠ 0 → (w i).re ≤ (w i₀).re) (hpos : 0 < (w i₀).re) : d i₀ = 0 := by
  classical
  set a := w i₀ with ha
  -- For `ε > 0`, the mean identity.
  have hmean : ∀ ε : ℝ, 0 < ε →
      ∑' i, d i * riemannZeta (1 + ε + (a - w i)) = D * riemannZeta (1 + ε + a) := by
    intro ε hε
    have hzeta : ∀ i, d i ≠ 0 → HasSum (zetaTerm (1 + ε + (a - w i))) (riemannZeta (1 + ε + (a - w i))) := by
      intro i hi
      refine hasSum_zetaTerm ?_
      have := hmax i hi
      simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.sub_re]
      linarith
    have hterm : ∀ (k : ℕ) (i : ι), d i * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (w i) * zetaTerm (1 + ε + a) k =
        d i * zetaTerm (1 + ε + (a - w i)) k := by
      intro k i
      have hk : ((((k : ℝ) + 1 : ℝ)) : ℂ) ≠ 0 := by
        have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        exact_mod_cast this.ne'
      rw [zetaTerm, zetaTerm, mul_assoc, ← Complex.cpow_add _ _ hk]
      congr 2
      ring
    -- The double series converges absolutely.
    have hbound : ∀ (k : ℕ) (i : ι), ‖d i * zetaTerm (1 + ε + (a - w i)) k‖ ≤
        ‖d i‖ * ((k : ℝ) + 1) ^ (-(1 + ε)) := by
      intro k i
      by_cases hi : d i = 0
      · simp [hi]
      · rw [norm_mul, norm_zetaTerm]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        refine Real.rpow_le_rpow_of_exponent_le ?_ ?_
        · have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          linarith
        · have := hmax i hi
          simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.sub_re]
          linarith
    have hsk : Summable fun k : ℕ => ((k : ℝ) + 1) ^ (-(1 + ε)) := by
      have h := (Real.summable_nat_rpow (p := -(1 + ε))).mpr (by linarith)
      have h2 := (summable_nat_add_iff 1).mpr h
      refine h2.congr fun k => ?_
      push_cast
      rfl
    have hprod : Summable (Function.uncurry fun (i : ι) (k : ℕ) => d i * zetaTerm (1 + ε + (a - w i)) k) := by
      refine Summable.of_norm_bounded (hd.mul_of_nonneg hsk (fun _ => norm_nonneg _)
        (fun _ => by positivity)) fun x => ?_
      exact hbound x.2 x.1
    have hswap := hprod.tsum_comm
    have hleft : ∀ k : ℕ, ∑' i, d i * zetaTerm (1 + ε + (a - w i)) k = D * zetaTerm (1 + ε + a) k := by
      intro k
      have h2 := (hrel k).mul_right (zetaTerm (1 + ε + a) k)
      rw [← h2.tsum_eq]
      exact tsum_congr fun i => (hterm k i).symm
    have hright : ∀ i : ι, ∑' k, d i * zetaTerm (1 + ε + (a - w i)) k =
        d i * riemannZeta (1 + ε + (a - w i)) := by
      intro i
      by_cases hi : d i = 0
      · simp [hi]
      · rw [tsum_mul_left, (hzeta i hi).tsum_eq]
    simp_rw [hleft, hright] at hswap
    rw [← hswap, tsum_mul_left, (hasSum_zetaTerm ?_).tsum_eq]
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
    linarith
  -- The limit `ε → 0+`.
  have hlimL : Tendsto (fun ε : ℝ => ∑' i, d i * ((ε : ℂ) * riemannZeta (1 + ε + (a - w i)))) (𝓝[>] 0)
      (𝓝 (∑' i, if i = i₀ then d i₀ else 0)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun i => ‖d i‖ * 2) (hd.mul_right 2) (fun i => ?_) ?_
    · by_cases hi : i = i₀
      · subst hi
        have h1 := tendsto_mul_zeta_one.const_mul (d i)
        rw [mul_one] at h1
        simp only [if_true]
        refine h1.congr fun ε => ?_
        rw [ha, sub_self]
      · rw [if_neg hi]
        by_cases hd0 : d i = 0
        · simp [hd0]
        · have hne : a - w i ≠ 0 := fun h => hi (hw (sub_eq_zero.mp h).symm)
          have h1 := (tendsto_mul_zeta_of_ne hne).const_mul (d i)
          rwa [mul_zero] at h1
    · filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε i
      by_cases hd0 : d i = 0
      · simp [hd0]
      · rw [norm_mul]
        refine mul_le_mul_of_nonneg_left (norm_mul_zeta_le hε.1 hε.2 ?_) (norm_nonneg _)
        have := hmax i hd0
        simp only [Complex.sub_re]
        linarith
  have hlimR : Tendsto (fun ε : ℝ => (ε : ℂ) * (D * riemannZeta (1 + ε + a))) (𝓝[>] 0) (𝓝 0) := by
    have hbd : ∀ᶠ ε : ℝ in 𝓝[>] 0, ‖D * riemannZeta (1 + ε + a)‖ ≤ ‖D‖ * (1 + 1 / a.re) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : (0 : ℝ) < ε := hε
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hre : 1 + a.re ≤ (1 + (ε : ℂ) + a).re := by
        simp
        linarith
      have h := _root_.RHTower.norm_riemannZeta_le_of_le_re (σ₁ := 1 + a.re) (by linarith) hre
      have h2 : (1 : ℝ) + a.re - 1 = a.re := by ring
      rwa [h2] at h
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hε : Tendsto (fun ε : ℝ => ‖(ε : ℂ)‖ * (‖D‖ * (1 + 1 / a.re))) (𝓝[>] 0) (𝓝 0) := by
      have := (tendsto_ofReal_nhdsGT.norm).mul_const (‖D‖ * (1 + 1 / a.re))
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hε
    filter_upwards [hbd] with ε h
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
  have heq : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∑' i, d i * ((ε : ℂ) * riemannZeta (1 + ε + (a - w i))) =
      (ε : ℂ) * (D * riemannZeta (1 + ε + a)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [← hmean ε hε, ← tsum_mul_left]
    exact tsum_congr fun i => by ring
  have hval := tendsto_nhds_unique hlimL (hlimR.congr' (heq.mono fun _ h => h.symm))
  rwa [tsum_ite_eq] at hval

/-! ### Superpositions in a strip -/

/-- An absolutely convergent superposition of modes in a strip, with distinct points and well-ordered abscissae. -/
structure IsStripSuperposition (c s : ι → ℂ) (σ₀ σ₁ : ℝ) : Prop where
  pos : 0 < σ₀
  lt_one : σ₁ < 1
  re_ge : ∀ i, σ₀ ≤ (s i).re
  re_le : ∀ i, (s i).re ≤ σ₁
  summable : Summable fun i => ‖c i‖ * ‖s i‖
  inj : Function.Injective s
  wf : (Set.range fun i => (s i).re).IsWF

private lemma summable_rpow_succ {σ : ℝ} (hσ : 0 < σ) : Summable fun j : ℕ => ((j : ℝ) + 1) ^ (-σ - 1) := by
  have h := (Real.summable_nat_rpow (p := -σ - 1)).mpr (by linarith)
  have h2 := (summable_nat_add_iff 1).mpr h
  refine h2.congr fun j => ?_
  push_cast
  rfl

private lemma rpow_succ_le {σ₀ σ : ℝ} (h : σ₀ ≤ σ) (j : ℕ) :
    ((j : ℝ) + 1) ^ (-σ - 1) ≤ ((j : ℝ) + 1) ^ (-σ₀ - 1) :=
  Real.rpow_le_rpow_of_exponent_le (by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith) (by linarith)

/-- **A uniform bound for `ζ` in the strip,** from the mode identity at `k = 2`. -/
theorem norm_zeta_le_strip {σ₀ σ₁ : ℝ} (h0 : 0 < σ₀) (h1 : σ₁ < 1) {s : ℂ} (hs0 : σ₀ ≤ s.re)
    (hs1 : s.re ≤ σ₁) :
    ‖riemannZeta s‖ ≤ (∑' j : ℕ, ((j : ℝ) + 1) ^ (-σ₀ - 1)) / ((2 : ℝ) ^ (1 - σ₁) - 1) * ‖s‖ := by
  have hσ : 0 < s.re := by linarith
  have hs1' : s ≠ 1 := fun h => by
    rw [h] at hs1
    simp at hs1
    linarith
  have hmode := hasSum_abelStep_mod (le_refl 2) hσ hs1'
  have hcast2 : (((2 : ℕ) : ℝ) : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [hcast2] at hmode
  have hκ : 0 < (2 : ℝ) ^ (1 - σ₁) - 1 := by
    have := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (by linarith : 0 < 1 - σ₁)
    linarith
  have hZ := summable_rpow_succ h0
  have hbd : ∀ j : ℕ, ‖abelStep s j * (((j + 1) % 2 : ℕ) : ℂ)‖ ≤ ‖s‖ * ((j : ℝ) + 1) ^ (-σ₀ - 1) := by
    intro j
    rw [norm_mul]
    have hmod : ‖(((j + 1) % 2 : ℕ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_natCast]
      exact_mod_cast Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    calc ‖abelStep s j‖ * ‖(((j + 1) % 2 : ℕ) : ℂ)‖ ≤ ‖s‖ * ((j : ℝ) + 1) ^ (-s.re - 1) * 1 :=
          mul_le_mul (norm_abelStep_le_rpow hσ j) hmod (norm_nonneg _) (by positivity)
      _ ≤ _ := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left (rpow_succ_le hs0 j) (norm_nonneg _)
  have hsum : ‖(1 - ((2 : ℝ) : ℂ) ^ (1 - s)) * riemannZeta s‖ ≤ ‖s‖ * ∑' j : ℕ, ((j : ℝ) + 1) ^ (-σ₀ - 1) := by
    rw [← hmode.tsum_eq, ← tsum_mul_left]
    exact tsum_of_norm_bounded (hZ.mul_left ‖s‖).hasSum hbd
  have hfac : (2 : ℝ) ^ (1 - σ₁) - 1 ≤ ‖1 - ((2 : ℝ) : ℂ) ^ (1 - s)‖ := by
    have h2 : ‖((2 : ℝ) : ℂ) ^ (1 - s)‖ = (2 : ℝ) ^ (1 - s.re) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
      simp
    have h3 : (2 : ℝ) ^ (1 - σ₁) ≤ (2 : ℝ) ^ (1 - s.re) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h4 := norm_sub_norm_le (((2 : ℝ) : ℂ) ^ (1 - s)) 1
    rw [h2, norm_one, norm_sub_rev] at h4
    linarith
  rw [norm_mul] at hsum
  rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
  nlinarith [norm_nonneg (riemannZeta s)]

/-- The cut moments of a superposition are the superposition of the cut moments. -/
private lemma superposition_moment {c s : ι → ℂ} {σ₀ σ₁ : ℝ} (hS : IsStripSuperposition c s σ₀ σ₁) {k : ℕ}
    (hk : 2 ≤ k) :
    HasSum (fun j : ℕ => (∑' i, c i * abelStep (s i) j) * (((j + 1) % k : ℕ) : ℂ))
      (∑' i, c i * ((1 - ((k : ℝ) : ℂ) ^ (1 - s i)) * riemannZeta (s i))) := by
  have hZ := summable_rpow_succ hS.pos
  set F : ι → ℕ → ℂ := fun i j => c i * abelStep (s i) j * (((j + 1) % k : ℕ) : ℂ) with hF
  have hbd : ∀ i j, ‖F i j‖ ≤ (‖c i‖ * ‖s i‖) * (k * ((j : ℝ) + 1) ^ (-σ₀ - 1)) := by
    intro i j
    have hσ : 0 < (s i).re := lt_of_lt_of_le hS.pos (hS.re_ge i)
    rw [hF, norm_mul, norm_mul]
    have hmod : ‖(((j + 1) % k : ℕ) : ℂ)‖ ≤ k := by
      rw [Complex.norm_natCast]
      exact_mod_cast (Nat.mod_lt _ (by omega)).le
    have h1 := (norm_abelStep_le_rpow hσ j).trans (mul_le_mul_of_nonneg_left (rpow_succ_le (hS.re_ge i) j)
      (norm_nonneg _))
    calc ‖c i‖ * ‖abelStep (s i) j‖ * ‖(((j + 1) % k : ℕ) : ℂ)‖
        ≤ ‖c i‖ * (‖s i‖ * ((j : ℝ) + 1) ^ (-σ₀ - 1)) * k :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) hmod (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hprod : Summable (Function.uncurry F) := by
    refine Summable.of_norm_bounded (hS.summable.mul_of_nonneg (hZ.mul_left (k : ℝ))
      (fun _ => by positivity) (fun _ => by positivity)) fun x => ?_
    exact hbd x.1 x.2
  have hrow : ∀ i, HasSum (F i) (c i * ((1 - ((k : ℝ) : ℂ) ^ (1 - s i)) * riemannZeta (s i))) := by
    intro i
    have hσ : 0 < (s i).re := lt_of_lt_of_le hS.pos (hS.re_ge i)
    have hs1 : s i ≠ 1 := fun h => by
      have := hS.re_le i
      rw [h] at this
      simp at this
      linarith [hS.lt_one]
    have := (hasSum_abelStep_mod hk hσ hs1).mul_left (c i)
    have hfun : F i = fun j => c i * (abelStep (s i) j * (((j + 1) % k : ℕ) : ℂ)) := by
      funext j
      simp only [hF]
      ring
    rw [hfun]
    exact this
  have hcol : ∀ j, HasSum (fun i => F i j) ((∑' i, c i * abelStep (s i) j) * (((j + 1) % k : ℕ) : ℂ)) := by
    intro j
    have hsj : Summable fun i => c i * abelStep (s i) j :=
      Summable.of_norm_bounded (hS.summable.mul_right (((j : ℝ) + 1) ^ (-σ₀ - 1))) fun i => by
        have hσ : 0 < (s i).re := lt_of_lt_of_le hS.pos (hS.re_ge i)
        rw [norm_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left ((norm_abelStep_le_rpow hσ j).trans
          (mul_le_mul_of_nonneg_left (rpow_succ_le (hS.re_ge i) j) (norm_nonneg _))) (norm_nonneg _)
    exact hsj.hasSum.mul_right (((j + 1) % k : ℕ) : ℂ)
  have htot := hprod.hasSum
  have hswap : HasSum (fun p : ℕ × ι => F p.2 p.1) (∑' x, Function.uncurry F x) :=
    (Equiv.prodComm ℕ ι).hasSum_iff.mpr htot
  have h1 := hswap.prod_fiberwise hcol
  have h2 := htot.prod_fiberwise hrow
  rwa [← h2.tsum_eq] at h1

/-- **The kernel of strip superpositions is carried by zeros.** -/
theorem superposition_kernel_iff {c s : ι → ℂ} {σ₀ σ₁ : ℝ} (hS : IsStripSuperposition c s σ₀ σ₁) :
    (∀ k : ℕ, 2 ≤ k → HasSum (fun j : ℕ => (∑' i, c i * abelStep (s i) j) * (((j + 1) % k : ℕ) : ℂ)) 0) ↔
      ∀ i, c i ≠ 0 → riemannZeta (s i) = 0 := by
  classical
  constructor
  · intro hker i hc
    by_contra hz
    set d : ι → ℂ := fun i => c i * riemannZeta (s i) with hd
    set w : ι → ℂ := fun i => 1 - s i with hw
    have hZ := summable_rpow_succ hS.pos
    set M : ℝ := (∑' j : ℕ, ((j : ℝ) + 1) ^ (-σ₀ - 1)) / ((2 : ℝ) ^ (1 - σ₁) - 1) with hM
    have hdsum : Summable fun i => ‖d i‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) (hS.summable.mul_left M)
      rw [hd, norm_mul]
      have := norm_zeta_le_strip hS.pos hS.lt_one (hS.re_ge i) (hS.re_le i)
      calc ‖c i‖ * ‖riemannZeta (s i)‖ ≤ ‖c i‖ * (M * ‖s i‖) := mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = M * (‖c i‖ * ‖s i‖) := by ring
    set D : ℂ := ∑' i, d i with hD
    have hrel : ∀ k : ℕ, HasSum (fun i => d i * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (w i)) D := by
      intro k
      have hk1 : (((k : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
        have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        exact_mod_cast this.ne'
      have hnorm : ∀ i, ‖d i * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (w i)‖ ≤ ‖d i‖ * ((k : ℝ) + 1) := by
        intro i
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have hre : (w i).re ≤ 1 := by
          simp only [hw, Complex.sub_re, Complex.one_re]
          linarith [hS.pos, hS.re_ge i]
        calc ((k : ℝ) + 1) ^ (w i).re ≤ ((k : ℝ) + 1) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith) hre
          _ = _ := Real.rpow_one _
      have hsum : Summable fun i => d i * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (w i) :=
        Summable.of_norm_bounded (hdsum.mul_right _) hnorm
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · have h1 : ∀ i, d i * ((((0 : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ (w i) = d i := fun i => by simp
        simp_rw [h1]
        exact (hdsum.of_norm).hasSum
      · have hmom := superposition_moment hS (k := k + 1) (by omega)
        have hzero := (hker (k + 1) (by omega)).unique hmom
        have hcast : (((k + 1 : ℕ) : ℝ) : ℂ) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
        rw [hcast] at hzero
        have hexp : ∀ i, c i * ((1 - (((k : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s i)) * riemannZeta (s i)) =
            d i - d i * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (w i) := fun i => by
          simp only [hd, hw]
          ring
        simp_rw [hexp] at hzero
        rw [Summable.tsum_sub (hdsum.of_norm) hsum] at hzero
        have hval : ∑' i, d i * (((k : ℝ) + 1 : ℝ) : ℂ) ^ (w i) = D := by
          rw [hD]
          linear_combination hzero
        rw [← hval]
        exact hsum.hasSum
    have hwinj : Function.Injective w := fun a b h => hS.inj (by
      have : 1 - s a = 1 - s b := h
      linear_combination -this)
    have hdi : d i ≠ 0 := mul_ne_zero hc hz
    set A : Set ℝ := {x | ∃ j, d j ≠ 0 ∧ (s j).re = x} with hA
    have hAsub : A ⊆ Set.range fun j => (s j).re := by
      rintro x ⟨j, _, rfl⟩
      exact ⟨j, rfl⟩
    have hAwf := hS.wf.mono hAsub
    have hAne : A.Nonempty := ⟨(s i).re, i, hdi, rfl⟩
    obtain ⟨i₀, hi₀, hmin⟩ := hAwf.min_mem hAne
    have hmax : ∀ j, d j ≠ 0 → (w j).re ≤ (w i₀).re := by
      intro j hj
      have h1 := hAwf.min_le hAne ⟨j, hj, rfl⟩
      simp only [hw, Complex.sub_re, Complex.one_re]
      linarith
    have hpos : 0 < (w i₀).re := by
      simp only [hw, Complex.sub_re, Complex.one_re]
      linarith [hS.re_le i₀, hS.lt_one]
    exact hi₀ (eq_zero_of_sum_cpow_eq_const hwinj hdsum hrel hmax hpos)
  · intro hzero k hk
    have hmom := superposition_moment hS hk
    have hfun : (fun i => c i * ((1 - ((k : ℝ) : ℂ) ^ (1 - s i)) * riemannZeta (s i))) = fun _ => 0 := by
      funext i
      by_cases hc : c i = 0
      · rw [hc, zero_mul]
      · rw [hzero i hc, mul_zero, mul_zero]
    rw [hfun, tsum_zero] at hmom
    exact hmom

/-! ### The energy space -/

/-- The modes have total mass `1`: `Σ_j U_s(j) = T(1) = 1`. -/
theorem hasSum_abelStep {s : ℂ} (hσ : 0 < s.re) : HasSum (abelStep s) 1 := by
  have hpart : ∀ N : ℕ, ∑ j ∈ Finset.range N, abelStep s j = 1 - (((N : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, abelStep]
      have h2 : (N : ℝ) + 2 = ((N + 1 : ℕ) : ℝ) + 1 := by
        push_cast
        ring
      rw [h2]
      ring
  have hsum : Summable (abelStep s) := by
    refine Summable.of_norm_bounded ((summable_rpow_succ hσ).mul_left ‖s‖) fun j => ?_
    exact norm_abelStep_le_rpow hσ j
  have hlim : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, abelStep s j) atTop (𝓝 1) := by
    simp_rw [hpart]
    have h0 : Tendsto (fun N : ℕ => (((N : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h1 : ∀ N : ℕ, ‖(((N : ℝ) + 1 : ℝ) : ℂ) ^ (-s)‖ = ((N : ℝ) + 1) ^ (-s.re) := fun N => by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
        simp
      simp_rw [h1]
      have h2 : Tendsto (fun N : ℕ => ((N : ℝ) + 1)) atTop atTop :=
        tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      exact (tendsto_rpow_neg_atTop hσ).comp h2
    have := (tendsto_const_nhds (x := (1 : ℂ))).sub h0
    rwa [sub_zero] at this
  have heq := tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlim
  rw [← heq]
  exact hsum.hasSum

/-- **The dual Nyman–Beurling criterion.** If every finite-energy kernel vector of the cut system has mass `0`, RH holds. -/
theorem riemannHypothesis_of_energy_kernel
    (h : ∀ U : ℕ → ℂ, Summable (fun j : ℕ => ((j : ℝ) + 1) ^ 2 * ‖U j‖ ^ 2) →
      (∀ k : ℕ, 2 ≤ k → HasSum (fun j : ℕ => U j * (((j + 1) % k : ℕ) : ℂ)) 0) →
      ∀ m : ℂ, HasSum U m → m = 0) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨ρ, hzero, hρ, hρ1⟩ := _root_.RHTower.exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
  have hσ : 0 < ρ.re := by linarith
  have hne1 : ρ ≠ 1 := fun h1 => by
    rw [h1] at hρ1
    simp at hρ1
  have henergy : Summable (fun j : ℕ => ((j : ℝ) + 1) ^ 2 * ‖abelStep ρ j‖ ^ 2) := by
    have hs2 : Summable fun j : ℕ => ((j : ℝ) + 1) ^ (-(2 * ρ.re)) := by
      have h1 := (Real.summable_nat_rpow (p := -(2 * ρ.re))).mpr (by linarith)
      have h2 := (summable_nat_add_iff 1).mpr h1
      refine h2.congr fun j => ?_
      push_cast
      rfl
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun j => ?_) (hs2.mul_left (‖ρ‖ ^ 2))
    have hx : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hb := norm_abelStep_le_rpow hσ j
    have hsq : ‖abelStep ρ j‖ ^ 2 ≤ (‖ρ‖ * ((j : ℝ) + 1) ^ (-ρ.re - 1)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hval : ((j : ℝ) + 1) ^ 2 * (‖ρ‖ * ((j : ℝ) + 1) ^ (-ρ.re - 1)) ^ 2 =
        ‖ρ‖ ^ 2 * ((j : ℝ) + 1) ^ (-(2 * ρ.re)) := by
      rw [Real.rpow_sub_one hx.ne', mul_pow, div_pow, ← Real.rpow_natCast (((j : ℝ) + 1) ^ (-ρ.re)) 2,
        ← Real.rpow_mul hx.le]
      have h3 : -ρ.re * ((2 : ℕ) : ℝ) = -(2 * ρ.re) := by push_cast; ring
      rw [h3]
      field_simp
    calc ((j : ℝ) + 1) ^ 2 * ‖abelStep ρ j‖ ^ 2
        ≤ ((j : ℝ) + 1) ^ 2 * (‖ρ‖ * ((j : ℝ) + 1) ^ (-ρ.re - 1)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = _ := hval
  have hker := (forall_hasSum_abelStep_mod_zero_iff hσ hne1).mpr hzero
  have hmass := h (abelStep ρ) henergy hker 1 (hasSum_abelStep hσ)
  exact one_ne_zero hmass

end GaloisForLFunctions.RigidArithmeticOfCuts
