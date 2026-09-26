import GaloisForLFunctions.HTGeometry.FejerWeightedAverage

/-!
# Real Fejér-weighted averages of unit distances and quadratic forms

The Fejér weight `F` is real; write `ψ = Re F ∈ [0, L^N]`.  For frequencies `ω'_n` (`n < M`) independent over
`ℤ`, targets `θ*_n` and continuous `y_n : ℝ → ℂ`:

* `(1/T) ∫₀ᵀ ψ → 1`;
* `(1/T) ∫₀ᵀ ψ(t) |e^{iω'_n t} - e^{iθ*_n}|² → 2/L` for `n < N`, since
  `|e^{ix} - e^{iy}|² = Re(2 - e^{-iy} e^{ix} - e^{iy} e^{-ix})`;
* `(1/T) ∫₀ᵀ ψ(t) ∫₀^{2π} |Σ_{N≤n<M} y_n(θ) e^{iω'_n t}|² dθ dt → Σ_{N≤n<M} ∫₀^{2π} |y_n|²`, since the inner
  integral is `Re Σ_{m,n} c_{mn} e^{i(ω'_m - ω'_n)t}` with `c_{mn} = ∫ y_m \bar y_n`.
-/

open Complex Real Filter Topology MeasureTheory

namespace RHTower.Weyl

noncomputable section

variable {M : ℕ} (N L : ℕ) (θs : Fin M → ℝ)

theorem continuous_trigPoly (S : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ) (k : ℕ × ℕ → ℤ) :
    Continuous (trigPoly S c k) := by
  unfold trigPoly
  fun_prop

theorem continuous_fejerWeight (ω : Fin M → ℝ) : Continuous (fejerWeight N L θs ω) := by
  unfold fejerWeight patProd
  exact continuous_finsetProd _ fun j _ =>
    (continuous_trigPoly _ _ _).comp (continuous_const.mul continuous_id)

theorem fejerWeight_eq_ofReal (hL : 0 < L) (ω : Fin M → ℝ) (t : ℝ) :
    fejerWeight N L θs ω t = ((fejerWeight N L θs ω t).re : ℂ) :=
  Complex.ext (by simp) (by simp [(fejerWeight_bounds N L θs hL ω t).1])

theorem continuous_fejerWeight_re (ω : Fin M → ℝ) : Continuous fun t => (fejerWeight N L θs ω t).re :=
  Complex.continuous_re.comp (continuous_fejerWeight N L θs ω)

/-- Real part of a time average. -/
theorem tendsto_average_re {F : ℝ → ℂ} (hF : Continuous F) {ℓ : ℂ}
    (h : Tendsto (fun T : ℝ => (↑T)⁻¹ * ∫ t in (0 : ℝ)..T, F t) atTop (𝓝 ℓ)) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, (F t).re) atTop (𝓝 ℓ.re) := by
  refine ((Complex.continuous_re.tendsto ℓ).comp h).congr fun T => ?_
  simp only [Function.comp]
  rw [← Complex.ofReal_inv, Complex.re_ofReal_mul]
  congr 1
  have := Complex.reCLM.intervalIntegral_comp_comm (hF.intervalIntegrable (μ := volume) 0 T)
  simp only [Complex.reCLM_apply] at this
  exact this.symm

/-- Time averages are additive on continuous functions. -/
theorem average_add {F G : ℝ → ℂ} (hF : Continuous F) (hG : Continuous G) (T : ℝ) :
    (↑T)⁻¹ * ∫ t in (0 : ℝ)..T, (F t + G t) =
      (↑T)⁻¹ * (∫ t in (0 : ℝ)..T, F t) + (↑T)⁻¹ * ∫ t in (0 : ℝ)..T, G t := by
  rw [intervalIntegral.integral_add (hF.intervalIntegrable _ _) (hG.intervalIntegrable _ _)]
  ring

theorem average_sub {F G : ℝ → ℂ} (hF : Continuous F) (hG : Continuous G) (T : ℝ) :
    (↑T)⁻¹ * ∫ t in (0 : ℝ)..T, (F t - G t) =
      (↑T)⁻¹ * (∫ t in (0 : ℝ)..T, F t) - (↑T)⁻¹ * ∫ t in (0 : ℝ)..T, G t := by
  rw [intervalIntegral.integral_sub (hF.intervalIntegrable _ _) (hG.intervalIntegrable _ _)]
  ring

theorem average_const_mul (c : ℂ) (F : ℝ → ℂ) (T : ℝ) :
    (↑T)⁻¹ * ∫ t in (0 : ℝ)..T, c * F t = c * ((↑T)⁻¹ * ∫ t in (0 : ℝ)..T, F t) := by
  rw [intervalIntegral.integral_const_mul]
  ring

theorem average_finset_sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℂ} (hF : ∀ i, Continuous (F i))
    (T : ℝ) :
    (↑T)⁻¹ * ∫ t in (0 : ℝ)..T, ∑ i ∈ s, F i t = ∑ i ∈ s, (↑T)⁻¹ * ∫ t in (0 : ℝ)..T, F i t := by
  rw [intervalIntegral.integral_finsetSum fun i _ => (hF i).intervalIntegrable _ _, Finset.mul_sum]

/-- **The weight has mean one** (real form). -/
theorem tendsto_fejerWeight_re (hL : 0 < L) (ω : Fin M → ℝ)
    (hω : ∀ m : Fin M → ℤ, ∑ i, (m i : ℝ) * ω i = 0 → m = 0) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, (fejerWeight N L θs ω t).re) atTop (𝓝 1) := by
  simpa using tendsto_average_re (continuous_fejerWeight N L θs ω) (tendsto_fejerWeight N L θs hL ω hω)

/-- `|e^{ix} - e^{iy}|² = Re(2 - e^{-iy} e^{ix} - e^{iy} e^{-ix})`. -/
theorem norm_exp_sub_exp_sq (x y : ℝ) :
    ‖Complex.exp (x * I) - Complex.exp (y * I)‖ ^ 2 =
      (2 - Complex.exp (-((y : ℂ) * I)) * Complex.exp (x * I) -
        Complex.exp (y * I) * Complex.exp (-((x : ℂ) * I))).re := by
  have hc : ∀ r : ℝ, Complex.exp (-((r : ℂ) * I)) = (starRingEnd ℂ) (Complex.exp (r * I)) := by
    intro r; rw [← Complex.exp_conj]; simp
  have hu : ∀ r : ℝ, Complex.exp (r * I) * (starRingEnd ℂ) (Complex.exp (r * I)) = 1 := by
    intro r
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    simp
  rw [hc, hc, ← Complex.normSq_eq_norm_sq, ← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj,
    map_sub]
  congr 1
  linear_combination hu x + hu y

/-- **Unit distances.** For `n < N`, `ψ(t) |e^{iω_n t} - e^{iθ*_n}|²` averages to `2/L`. -/
theorem tendsto_fejerWeight_mul_dist_sq (hL : 0 < L) (ω : Fin M → ℝ)
    (hω : ∀ m : Fin M → ℤ, ∑ i, (m i : ℝ) * ω i = 0 → m = 0) (n : Fin M) (hn : (n : ℕ) < N) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, (fejerWeight N L θs ω t).re *
        ‖Complex.exp (((ω n * t : ℝ) : ℂ) * I) - Complex.exp ((θs n : ℂ) * I)‖ ^ 2)
      atTop (𝓝 (2 / L)) := by
  have hFc : Continuous (fejerWeight N L θs ω) := continuous_fejerWeight N L θs ω
  have h1 := tendsto_fejerWeight N L θs hL ω hω
  have hp := tendsto_fejerWeight_mul_exp N L θs hL ω hω n hn 1 (Or.inl rfl)
  have hm := tendsto_fejerWeight_mul_exp N L θs hL ω hω n hn (-1) (Or.inr rfl)
  simp only [Int.cast_one, one_mul, Int.cast_neg, neg_mul, Complex.ofReal_neg, Complex.ofReal_one]
    at hp hm
  have hG1 : Continuous fun t => fejerWeight N L θs ω t * Complex.exp (((ω n * t : ℝ) : ℂ) * I) :=
    hFc.mul (by fun_prop)
  have hG2 : Continuous fun t =>
      fejerWeight N L θs ω t * Complex.exp (-(((ω n * t : ℝ) : ℂ) * I)) :=
    hFc.mul (by fun_prop)
  have hGc : Continuous fun t => 2 * fejerWeight N L θs ω t -
      Complex.exp (-((θs n : ℂ) * I)) *
        (fejerWeight N L θs ω t * Complex.exp (((ω n * t : ℝ) : ℂ) * I)) -
      Complex.exp ((θs n : ℂ) * I) *
        (fejerWeight N L θs ω t * Complex.exp (-(((ω n * t : ℝ) : ℂ) * I))) :=
    ((continuous_const.mul hFc).sub (continuous_const.mul hG1)).sub (continuous_const.mul hG2)
  have hlimG := ((h1.const_mul 2).sub (hp.const_mul (Complex.exp (-((θs n : ℂ) * I))))).sub
    (hm.const_mul (Complex.exp ((θs n : ℂ) * I)))
  have hlimG' : Tendsto (fun T : ℝ => (↑T)⁻¹ * ∫ t in (0 : ℝ)..T, (2 * fejerWeight N L θs ω t -
      Complex.exp (-((θs n : ℂ) * I)) *
        (fejerWeight N L θs ω t * Complex.exp (((ω n * t : ℝ) : ℂ) * I)) -
      Complex.exp ((θs n : ℂ) * I) *
        (fejerWeight N L θs ω t * Complex.exp (-(((ω n * t : ℝ) : ℂ) * I))))) atTop
      (𝓝 (2 * 1 - Complex.exp (-((θs n : ℂ) * I)) *
          (Complex.exp ((θs n : ℂ) * I) * ((((L : ℝ) - 1) / L : ℝ) : ℂ)) -
        Complex.exp ((θs n : ℂ) * I) *
          (Complex.exp (-((θs n : ℂ) * I)) * ((((L : ℝ) - 1) / L : ℝ) : ℂ)))) := by
    refine hlimG.congr fun T => ?_
    have i1 : IntervalIntegrable (fun t => 2 * fejerWeight N L θs ω t) volume 0 T :=
      (continuous_const.mul hFc).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun t => Complex.exp (-((θs n : ℂ) * I)) *
        (fejerWeight N L θs ω t * Complex.exp (((ω n * t : ℝ) : ℂ) * I))) volume 0 T :=
      (continuous_const.mul hG1).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun t => Complex.exp ((θs n : ℂ) * I) *
        (fejerWeight N L θs ω t * Complex.exp (-(((ω n * t : ℝ) : ℂ) * I)))) volume 0 T :=
      (continuous_const.mul hG2).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    ring
  have hval : (2 * 1 - Complex.exp (-((θs n : ℂ) * I)) *
          (Complex.exp ((θs n : ℂ) * I) * ((((L : ℝ) - 1) / L : ℝ) : ℂ)) -
        Complex.exp ((θs n : ℂ) * I) *
          (Complex.exp (-((θs n : ℂ) * I)) * ((((L : ℝ) - 1) / L : ℝ) : ℂ))).re = 2 / L := by
    have huu : Complex.exp (-((θs n : ℂ) * I)) * Complex.exp ((θs n : ℂ) * I) = 1 := by
      rw [← Complex.exp_add]; simp
    have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
    have h2 : 2 * 1 - Complex.exp (-((θs n : ℂ) * I)) *
          (Complex.exp ((θs n : ℂ) * I) * ((((L : ℝ) - 1) / L : ℝ) : ℂ)) -
        Complex.exp ((θs n : ℂ) * I) *
          (Complex.exp (-((θs n : ℂ) * I)) * ((((L : ℝ) - 1) / L : ℝ) : ℂ)) =
        ((2 - 2 * (((L : ℝ) - 1) / L) : ℝ) : ℂ) := by
      push_cast
      linear_combination (-2 * ((((L : ℂ) - 1) / L))) * huu
    rw [h2, Complex.ofReal_re]
    field_simp
    ring
  rw [← hval]
  refine (tendsto_average_re hGc hlimG').congr fun T => ?_
  congr 2
  funext t
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ, fejerWeight N L θs ω t = ψ := ⟨_, fejerWeight_eq_ofReal N L θs hL ω t⟩
  rw [hψ, Complex.ofReal_re, norm_exp_sub_exp_sq, ← Complex.re_ofReal_mul]
  congr 1
  ring

/-- `e^{ix} \overline{e^{iy}} = e^{i(x-y)}`. -/
theorem exp_mul_conj_exp (x y : ℝ) :
    Complex.exp (x * I) * (starRingEnd ℂ) (Complex.exp (y * I)) = Complex.exp (((x - y : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- **Expansion of the quadratic form.** -/
theorem integral_norm_sq_trig_sum_eq (s : Finset ℕ) (ω' : ℕ → ℝ) (y : ℕ → ℝ → ℂ)
    (hy : ∀ n, Continuous (y n)) (t : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, ‖∑ n ∈ s, y n θ * Complex.exp (((ω' n * t : ℝ) : ℂ) * I)‖ ^ 2 =
      (∑ m ∈ s, ∑ n ∈ s, (∫ θ in (0 : ℝ)..2 * π, y m θ * (starRingEnd ℂ) (y n θ)) *
        Complex.exp ((((ω' m - ω' n) * t : ℝ) : ℂ) * I)).re := by
  have hpt : ∀ θ, ‖∑ n ∈ s, y n θ * Complex.exp (((ω' n * t : ℝ) : ℂ) * I)‖ ^ 2 =
      (∑ m ∈ s, ∑ n ∈ s, y m θ * (starRingEnd ℂ) (y n θ) *
        Complex.exp ((((ω' m - ω' n) * t : ℝ) : ℂ) * I)).re := by
    intro θ
    rw [← Complex.normSq_eq_norm_sq, ← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj,
      map_sum, Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul]
    have := exp_mul_conj_exp (ω' m * t) (ω' n * t)
    rw [show (ω' m - ω' n) * t = ω' m * t - ω' n * t by ring, ← this]
    ring
  simp_rw [hpt]
  have hc : ∀ m n, Continuous fun θ => y m θ * (starRingEnd ℂ) (y n θ) *
      Complex.exp ((((ω' m - ω' n) * t : ℝ) : ℂ) * I) :=
    fun m n => ((hy m).mul (Complex.continuous_conj.comp (hy n))).mul continuous_const
  have hsum : Continuous fun θ => ∑ m ∈ s, ∑ n ∈ s, y m θ * (starRingEnd ℂ) (y n θ) *
      Complex.exp ((((ω' m - ω' n) * t : ℝ) : ℂ) * I) :=
    continuous_finsetSum _ fun m _ => continuous_finsetSum _ fun n _ => hc m n
  have := Complex.reCLM.intervalIntegral_comp_comm (hsum.intervalIntegrable (μ := volume) 0 (2 * π))
  simp only [Complex.reCLM_apply] at this
  rw [this]
  congr 1
  rw [intervalIntegral.integral_finsetSum fun m _ =>
    (continuous_finsetSum _ fun n _ => hc m n).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [intervalIntegral.integral_finsetSum fun n _ => (hc m n).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun n _ => ?_
  exact intervalIntegral.integral_mul_const _ _

theorem continuous_integral_norm_sq_trig_sum (s : Finset ℕ) (ω' : ℕ → ℝ) (y : ℕ → ℝ → ℂ)
    (hy : ∀ n, Continuous (y n)) :
    Continuous fun t : ℝ =>
      ∫ θ in (0 : ℝ)..2 * π, ‖∑ n ∈ s, y n θ * Complex.exp (((ω' n * t : ℝ) : ℂ) * I)‖ ^ 2 := by
  simp_rw [integral_norm_sq_trig_sum_eq s ω' y hy]
  refine Complex.continuous_re.comp (continuous_finsetSum _ fun m _ => continuous_finsetSum _ fun n _ => ?_)
  exact continuous_const.mul (by fun_prop)

/-- **Quadratic forms.** `ψ(t) ∫ |Σ_{N≤n<M} y_n e^{iω'_n t}|²` averages to `Σ_{N≤n<M} ∫ |y_n|²`. -/
theorem tendsto_fejerWeight_mul_quadratic (hL : 0 < L) (ω' : ℕ → ℝ)
    (hω : ∀ m : Fin M → ℤ, ∑ i, (m i : ℝ) * ω' i = 0 → m = 0) (y : ℕ → ℝ → ℂ)
    (hy : ∀ n, Continuous (y n)) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, (fejerWeight N L θs (fun j => ω' j) t).re *
        ∫ θ in (0 : ℝ)..2 * π,
          ‖∑ n ∈ Finset.Ico N M, y n θ * Complex.exp (((ω' n * t : ℝ) : ℂ) * I)‖ ^ 2)
      atTop (𝓝 (∑ n ∈ Finset.Ico N M, ∫ θ in (0 : ℝ)..2 * π, ‖y n θ‖ ^ 2)) := by
  classical
  set s := Finset.Ico N M with hs
  set F := fejerWeight N L θs (fun j : Fin M => ω' j) with hFdef
  have hFc : Continuous F := continuous_fejerWeight N L θs _
  set c : ℕ → ℕ → ℂ := fun m n => ∫ θ in (0 : ℝ)..2 * π, y m θ * (starRingEnd ℂ) (y n θ) with hc
  set E : ℕ → ℕ → ℝ → ℂ := fun m n t => Complex.exp ((((ω' m - ω' n) * t : ℝ) : ℂ) * I) with hE
  have hEc : ∀ m n, Continuous (E m n) := fun m n => by rw [hE]; fun_prop
  set G : ℝ → ℂ := fun t => ∑ m ∈ s, ∑ n ∈ s, c m n * (F t * E m n t) with hG
  have hterm : ∀ m n, Continuous fun t => c m n * (F t * E m n t) :=
    fun m n => continuous_const.mul (hFc.mul (hEc m n))
  have hGc : Continuous G :=
    continuous_finsetSum _ fun m _ => continuous_finsetSum _ fun n _ => hterm m n
  have hpair : ∀ m ∈ s, ∀ n ∈ s, Tendsto (fun T : ℝ => (↑T)⁻¹ * ∫ t in (0 : ℝ)..T, F t * E m n t)
      atTop (𝓝 (if m = n then 1 else 0)) := by
    intro m hm n hn
    rw [hs, Finset.mem_Ico] at hm hn
    have h := tendsto_fejerWeight_mul_pair N L θs hL (fun j : Fin M => ω' j) hω ⟨m, hm.2⟩ ⟨n, hn.2⟩
      hm.1 hn.1
    have hif : ((⟨m, hm.2⟩ : Fin M) = ⟨n, hn.2⟩) ↔ m = n := Fin.mk.injEq _ _ _ _ ▸ Iff.rfl
    simp only [hif] at h
    exact h
  have hlimG : Tendsto (fun T : ℝ => (↑T)⁻¹ * ∫ t in (0 : ℝ)..T, G t) atTop
      (𝓝 (∑ m ∈ s, ∑ n ∈ s, c m n * (if m = n then 1 else 0))) := by
    have : Tendsto (fun T : ℝ => ∑ m ∈ s, ∑ n ∈ s, c m n * ((↑T)⁻¹ * ∫ t in (0 : ℝ)..T, F t * E m n t))
        atTop (𝓝 (∑ m ∈ s, ∑ n ∈ s, c m n * (if m = n then 1 else 0))) :=
      tendsto_finsetSum _ fun m hm => tendsto_finsetSum _ fun n hn => (hpair m hm n hn).const_mul _
    refine this.congr fun T => ?_
    rw [hG]
    simp only
    rw [average_finset_sum s (fun m => continuous_finsetSum _ fun n _ => hterm m n)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [average_finset_sum s (fun n => hterm m n)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [average_const_mul]
  have hval : (∑ m ∈ s, ∑ n ∈ s, c m n * (if m = n then 1 else 0)).re =
      ∑ n ∈ s, ∫ θ in (0 : ℝ)..2 * π, ‖y n θ‖ ^ 2 := by
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Complex.re_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [if_pos hn, hc]
    simp only
    have hcont : Continuous fun θ => y n θ * (starRingEnd ℂ) (y n θ) :=
      (hy n).mul (Complex.continuous_conj.comp (hy n))
    have := Complex.reCLM.intervalIntegral_comp_comm (hcont.intervalIntegrable (μ := volume) 0 (2 * π))
    simp only [Complex.reCLM_apply] at this
    rw [← this]
    congr 1
    funext θ
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  rw [← hval]
  refine (tendsto_average_re hGc hlimG).congr fun T => ?_
  congr 2
  funext t
  rw [integral_norm_sq_trig_sum_eq s ω' y hy t, hG]
  simp only [hFdef]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ, fejerWeight N L θs (fun j : Fin M => ω' j) t = ψ :=
    ⟨_, fejerWeight_eq_ofReal N L θs hL _ t⟩
  rw [hψ, Complex.ofReal_re, ← Complex.re_ofReal_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hE]
  ring

/-- **Combined average.** `c₀ ψ - Σ_{n<N} d_n ψ |e^{iω'_n t} - e^{iθ'_n}|² - d_Y ψ ∫ |Σ_{N≤n<M} y_n e^{iω'_n t}|²`
averages to `c₀ - Σ_{n<N} d_n (2/L) - d_Y Σ_{N≤n<M} ∫ |y_n|²`. -/
theorem tendsto_fejerWeight_combination (hL : 0 < L) (hNM : N ≤ M) (ω' θ' : ℕ → ℝ)
    (hω : ∀ m : Fin M → ℤ, ∑ i, (m i : ℝ) * ω' i = 0 → m = 0) (c₀ dY : ℝ) (d : ℕ → ℝ)
    (y : ℕ → ℝ → ℂ) (hy : ∀ n, Continuous (y n)) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T,
        (c₀ * (fejerWeight N L (fun j : Fin M => θ' j) (fun j : Fin M => ω' j) t).re -
          ∑ n ∈ Finset.range N, d n *
            ((fejerWeight N L (fun j : Fin M => θ' j) (fun j : Fin M => ω' j) t).re *
              ‖Complex.exp (((ω' n * t : ℝ) : ℂ) * I) - Complex.exp ((θ' n : ℂ) * I)‖ ^ 2) -
          dY * ((fejerWeight N L (fun j : Fin M => θ' j) (fun j : Fin M => ω' j) t).re *
            ∫ θ in (0 : ℝ)..2 * π,
              ‖∑ n ∈ Finset.Ico N M, y n θ * Complex.exp (((ω' n * t : ℝ) : ℂ) * I)‖ ^ 2)))
      atTop (𝓝 (c₀ - ∑ n ∈ Finset.range N, d n * (2 / L) -
        dY * ∑ n ∈ Finset.Ico N M, ∫ θ in (0 : ℝ)..2 * π, ‖y n θ‖ ^ 2)) := by
  have hψc := continuous_fejerWeight_re N L (fun j : Fin M => θ' j) (fun j : Fin M => ω' j)
  have h1 := tendsto_fejerWeight_re N L (fun j : Fin M => θ' j) hL (fun j : Fin M => ω' j) hω
  have h2 : ∀ n ∈ Finset.range N, Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T,
      (fejerWeight N L (fun j : Fin M => θ' j) (fun j : Fin M => ω' j) t).re *
        ‖Complex.exp (((ω' n * t : ℝ) : ℂ) * I) - Complex.exp ((θ' n : ℂ) * I)‖ ^ 2) atTop
      (𝓝 (2 / L)) := by
    intro n hn
    rw [Finset.mem_range] at hn
    exact tendsto_fejerWeight_mul_dist_sq N L (fun j : Fin M => θ' j) hL (fun j : Fin M => ω' j) hω
      ⟨n, by omega⟩ hn
  have h3 := tendsto_fejerWeight_mul_quadratic N L (fun j : Fin M => θ' j) hL ω' hω y hy
  have hlim := ((h1.const_mul c₀).sub (tendsto_finsetSum _ fun n hn => (h2 n hn).const_mul (d n))).sub
    (h3.const_mul dY)
  rw [mul_one] at hlim
  refine hlim.congr fun T => ?_
  have hx : ∀ n, Continuous fun t : ℝ =>
      (fejerWeight N L (fun j : Fin M => θ' j) (fun j : Fin M => ω' j) t).re *
        ‖Complex.exp (((ω' n * t : ℝ) : ℂ) * I) - Complex.exp ((θ' n : ℂ) * I)‖ ^ 2 :=
    fun n => hψc.mul ((by fun_prop : Continuous fun t : ℝ =>
      Complex.exp (((ω' n * t : ℝ) : ℂ) * I) - Complex.exp ((θ' n : ℂ) * I)).norm.pow 2)
  have hq := continuous_integral_norm_sq_trig_sum (Finset.Ico N M) ω' y hy
  have i1 : IntervalIntegrable (fun t => c₀ *
      (fejerWeight N L (fun j : Fin M => θ' j) (fun j : Fin M => ω' j) t).re) volume 0 T :=
    (continuous_const.mul hψc).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t => ∑ n ∈ Finset.range N, d n *
      ((fejerWeight N L (fun j : Fin M => θ' j) (fun j : Fin M => ω' j) t).re *
        ‖Complex.exp (((ω' n * t : ℝ) : ℂ) * I) - Complex.exp ((θ' n : ℂ) * I)‖ ^ 2)) volume 0 T :=
    (continuous_finsetSum _ fun n _ => continuous_const.mul (hx n)).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun t => dY *
      ((fejerWeight N L (fun j : Fin M => θ' j) (fun j : Fin M => ω' j) t).re *
        ∫ θ in (0 : ℝ)..2 * π,
          ‖∑ n ∈ Finset.Ico N M, y n θ * Complex.exp (((ω' n * t : ℝ) : ℂ) * I)‖ ^ 2)) volume 0 T :=
    (continuous_const.mul (hψc.mul hq)).intervalIntegrable _ _
  have i2' : ∀ n, IntervalIntegrable (fun t => d n *
      ((fejerWeight N L (fun j : Fin M => θ' j) (fun j : Fin M => ω' j) t).re *
        ‖Complex.exp (((ω' n * t : ℝ) : ℂ) * I) - Complex.exp ((θ' n : ℂ) * I)‖ ^ 2)) volume 0 T :=
    fun n => (continuous_const.mul (hx n)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_finsetSum fun n _ => i2' n,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp only [intervalIntegral.integral_const_mul]
  rw [mul_sub, mul_sub, Finset.mul_sum]
  congr 1
  · congr 1
    · ring
    · exact Finset.sum_congr rfl fun n _ => by ring
  · ring

end

end RHTower.Weyl
