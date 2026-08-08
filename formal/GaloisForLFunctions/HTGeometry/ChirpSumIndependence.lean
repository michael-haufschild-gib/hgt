import GaloisForLFunctions.HTGeometry.TrigPolyLogVanishing

/-!
# Independence of factorial chirps

A finite sum of terms

`Aᵢ · N^{ρᵢ} · e^{i t kᵢ log N} · εᵢ(N)`,   `kᵢ ∈ ℤ`, `εᵢ → 1`,

whose normalisation by `N^{smax}` tends to zero, has vanishing coefficients at every index of
maximal real exponent, provided the integer frequencies separate those indices.

Two steps.  The indices with `ρᵢ < smax` contribute `N^{ρᵢ − smax} → 0` after the normalisation, so
only the maximal layer survives; and there `εᵢ → 1` leaves a trigonometric polynomial in `log N`
with distinct integer frequencies, which must vanish identically.

This is the endgame of a coefficient-chirp obstruction: the surviving layer is the set of endpoint
pairs realising the maximal exponent, and the frequencies separate them because equal complete
complex exponents force equal pairs.
-/

open Filter Topology Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One chirp term. -/
def chirpTerm (t ρ : ℝ) (k : ℤ) (A : ℂ) (x : ℝ) : ℂ :=
  A * ((Real.exp (ρ * x) : ℝ) : ℂ) * Complex.exp (((t * (k : ℝ) * x : ℝ)) * Complex.I)

theorem chirpTerm_div_exp (t ρ smax : ℝ) (k : ℤ) (A : ℂ) (x : ℝ) :
    chirpTerm t ρ k A x / ((Real.exp (smax * x) : ℝ) : ℂ)
      = A * ((Real.exp ((ρ - smax) * x) : ℝ) : ℂ)
        * Complex.exp (((t * (k : ℝ) * x : ℝ)) * Complex.I) := by
  have hne : ((Real.exp (smax * x) : ℝ) : ℂ) ≠ 0 := by
    simp
  have hsplit : Real.exp ((ρ - smax) * x) = Real.exp (ρ * x) / Real.exp (smax * x) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [chirpTerm, hsplit]
  push_cast
  field_simp

theorem norm_chirp_unit (t : ℝ) (k : ℤ) (x : ℝ) :
    ‖Complex.exp (((t * (k : ℝ) * x : ℝ)) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- **The chirp coefficients of the maximal layer vanish.** -/
theorem chirp_coeff_eq_zero_of_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι]
    {t : ℝ} (ht : t ≠ 0) {ρ : ι → ℝ} {k : ι → ℤ} {A : ι → ℂ} {ε : ι → ℕ → ℂ} {smax : ℝ}
    (hinj : ∀ i₁ i₂ : ι, ρ i₁ = smax → ρ i₂ = smax → k i₁ = k i₂ → i₁ = i₂)
    (hle : ∀ i, A i ≠ 0 → ρ i ≤ smax)
    (hε : ∀ i, Tendsto (ε i) atTop (𝓝 1))
    (hsum : Tendsto (fun N : ℕ =>
      (∑ i, chirpTerm t (ρ i) (k i) (A i) (Real.log N) * ε i N)
        / ((Real.exp (smax * Real.log N) : ℝ) : ℂ)) atTop (𝓝 0)) :
    ∀ i, ρ i = smax → A i = 0 := by
  classical
  set S₀ : Finset ι := Finset.univ.filter (fun i => ρ i = smax) with hS₀
  have hlogtop : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hεnorm : ∀ i, Tendsto (fun N : ℕ => ‖ε i N‖) atTop (𝓝 1) := by
    intro i
    have := (hε i).norm
    simpa using this
  -- rewrite each normalised term
  have hrw : ∀ (i : ι) (N : ℕ),
      chirpTerm t (ρ i) (k i) (A i) (Real.log N) * ε i N
          / ((Real.exp (smax * Real.log N) : ℝ) : ℂ)
        = A i * ((Real.exp ((ρ i - smax) * Real.log N) : ℝ) : ℂ)
          * Complex.exp (((t * (k i : ℝ) * Real.log N : ℝ)) * Complex.I) * ε i N := by
    intro i N
    rw [mul_div_right_comm, chirpTerm_div_exp]
  -- the sub-maximal terms vanish
  have hsmall : ∀ i ∉ S₀, Tendsto (fun N : ℕ =>
      chirpTerm t (ρ i) (k i) (A i) (Real.log N) * ε i N
        / ((Real.exp (smax * Real.log N) : ℝ) : ℂ)) atTop (𝓝 0) := by
    intro i hi
    have hne : ρ i ≠ smax := by
      intro hc
      exact hi (by simp [hS₀, hc])
    by_cases hA : A i = 0
    · refine Tendsto.congr (fun N => ?_) tendsto_const_nhds
      rw [hrw i N, hA]
      ring
    · have hlt : ρ i < smax := lt_of_le_of_ne (hle i hA) hne
      have hbot : Tendsto (fun N : ℕ => (ρ i - smax) * Real.log N) atTop atBot := by
        have hpos : Tendsto (fun N : ℕ => (smax - ρ i) * Real.log N) atTop atTop :=
          Filter.Tendsto.const_mul_atTop (by linarith : (0:ℝ) < smax - ρ i) hlogtop
        have hneg := Filter.tendsto_neg_atTop_atBot.comp hpos
        refine hneg.congr fun N => ?_
        simp only [Function.comp_apply]
        ring
      have hexp : Tendsto (fun N : ℕ => Real.exp ((ρ i - smax) * Real.log N)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp hbot
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hnormeq : ∀ N : ℕ, ‖chirpTerm t (ρ i) (k i) (A i) (Real.log N) * ε i N
          / ((Real.exp (smax * Real.log N) : ℝ) : ℂ)‖
          = ‖A i‖ * Real.exp ((ρ i - smax) * Real.log N) * ‖ε i N‖ := by
        intro N
        rw [hrw i N, norm_mul, norm_mul, norm_mul, norm_chirp_unit, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Tendsto.congr (fun N => (hnormeq N).symm) ?_
      have h1 : Tendsto (fun N : ℕ => ‖A i‖ * Real.exp ((ρ i - smax) * Real.log N))
          atTop (𝓝 0) := by
        have := hexp.const_mul ‖A i‖
        simpa using this
      have := h1.mul (hεnorm i)
      simpa using this
  -- the maximal layer survives
  have hsplit : ∀ N : ℕ,
      (∑ i, chirpTerm t (ρ i) (k i) (A i) (Real.log N) * ε i N)
          / ((Real.exp (smax * Real.log N) : ℝ) : ℂ)
        = (∑ i ∈ S₀, A i * Complex.exp (((t * (k i : ℝ) * Real.log N : ℝ)) * Complex.I) * ε i N)
          + ∑ i ∈ S₀ᶜ, chirpTerm t (ρ i) (k i) (A i) (Real.log N) * ε i N
            / ((Real.exp (smax * Real.log N) : ℝ) : ℂ) := by
    intro N
    have hdiv : (∑ i, chirpTerm t (ρ i) (k i) (A i) (Real.log N) * ε i N)
          / ((Real.exp (smax * Real.log N) : ℝ) : ℂ)
        = ∑ i, chirpTerm t (ρ i) (k i) (A i) (Real.log N) * ε i N
          / ((Real.exp (smax * Real.log N) : ℝ) : ℂ) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    rw [hdiv, ← Finset.sum_add_sum_compl S₀]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hρ : ρ i = smax := by simpa [hS₀] using hi
    rw [hrw i N, hρ, sub_self, zero_mul, Real.exp_zero]
    push_cast
    ring
  have hcompl : Tendsto (fun N : ℕ =>
      ∑ i ∈ S₀ᶜ, chirpTerm t (ρ i) (k i) (A i) (Real.log N) * ε i N
        / ((Real.exp (smax * Real.log N) : ℝ) : ℂ)) atTop (𝓝 0) := by
    have hterm : ∀ i ∈ S₀ᶜ, Tendsto (fun N : ℕ =>
        chirpTerm t (ρ i) (k i) (A i) (Real.log N) * ε i N
          / ((Real.exp (smax * Real.log N) : ℝ) : ℂ)) atTop (𝓝 0) :=
      fun i hi => hsmall i (Finset.mem_compl.mp hi)
    simpa using tendsto_finsetSum (S₀ᶜ) hterm
  have hlayerε : Tendsto (fun N : ℕ =>
      ∑ i ∈ S₀, A i * Complex.exp (((t * (k i : ℝ) * Real.log N : ℝ)) * Complex.I) * ε i N)
      atTop (𝓝 0) := by
    have hdiff := hsum.sub hcompl
    rw [sub_zero] at hdiff
    refine hdiff.congr fun N => ?_
    rw [hsplit N]
    ring
  -- drop the vanishing factors
  have hlayer : Tendsto (fun N : ℕ =>
      ∑ i ∈ S₀, A i * Complex.exp (((t * (k i : ℝ) * Real.log N : ℝ)) * Complex.I))
      atTop (𝓝 0) := by
    have hgap : Tendsto (fun N : ℕ =>
        ∑ i ∈ S₀, A i * Complex.exp (((t * (k i : ℝ) * Real.log N : ℝ)) * Complex.I)
          * (ε i N - 1)) atTop (𝓝 0) := by
      have hterm : ∀ i ∈ S₀, Tendsto (fun N : ℕ =>
          A i * Complex.exp (((t * (k i : ℝ) * Real.log N : ℝ)) * Complex.I)
            * (ε i N - 1)) atTop (𝓝 0) := by
        intro i _
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hnormeq : ∀ N : ℕ, ‖A i * Complex.exp (((t * (k i : ℝ) * Real.log N : ℝ)) * Complex.I)
            * (ε i N - 1)‖ = ‖A i‖ * ‖ε i N - 1‖ := by
          intro N
          rw [norm_mul, norm_mul, norm_chirp_unit, mul_one]
        refine Tendsto.congr (fun N => (hnormeq N).symm) ?_
        have hz : Tendsto (fun N : ℕ => ‖ε i N - 1‖) atTop (𝓝 0) := by
          rw [← tendsto_zero_iff_norm_tendsto_zero]
          have := (hε i).sub (tendsto_const_nhds (x := (1 : ℂ)) (f := atTop (α := ℕ)))
          simpa using this
        have := hz.const_mul ‖A i‖
        simpa using this
      simpa using tendsto_finsetSum S₀ hterm
    have hdiff := hlayerε.sub hgap
    rw [sub_zero] at hdiff
    refine hdiff.congr fun N => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- read the layer as a trigonometric polynomial
  set b : ℤ → ℂ := fun h => ∑ i ∈ S₀.filter (fun i => k i = h), A i with hb
  have hmemS₀ : ∀ i, i ∈ S₀ ↔ ρ i = smax := by
    intro i
    simp [hS₀]
  have hbval : ∀ i ∈ S₀, b (k i) = A i := by
    intro i hi
    have hfil : S₀.filter (fun i' => k i' = k i) = {i} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨by simp [Finset.mem_filter, hi], ?_⟩
      intro j hj
      rw [Finset.mem_filter] at hj
      exact hinj j i ((hmemS₀ j).mp hj.1) ((hmemS₀ i).mp hi) hj.2
    show (∑ i' ∈ S₀.filter (fun i' => k i' = k i), A i') = A i
    rw [hfil, Finset.sum_singleton]
  have hinjS : ∀ i₁ ∈ S₀, ∀ i₂ ∈ S₀, k i₁ = k i₂ → i₁ = i₂ := by
    intro i₁ h₁ i₂ h₂ hk
    exact hinj i₁ i₂ ((hmemS₀ i₁).mp h₁) ((hmemS₀ i₂).mp h₂) hk
  have htrig : ∀ x : ℝ, trigPoly (S₀.image k) b t x
      = ∑ i ∈ S₀, A i * Complex.exp (((t * (k i : ℝ) * x : ℝ)) * Complex.I) := by
    intro x
    rw [trigPoly, Finset.sum_image hinjS]
    exact Finset.sum_congr rfl fun i hi => by rw [hbval i hi]
  have hlim : Tendsto (fun N : ℕ => trigPoly (S₀.image k) b t (Real.log N)) atTop (𝓝 0) := by
    refine hlayer.congr fun N => (htrig (Real.log N)).symm
  have hzero := trigPoly_coeff_eq_zero_of_tendsto_natLog ht hlim
  intro i hi
  have hiS : i ∈ S₀ := (hmemS₀ i).mpr hi
  have := hzero (k i) (Finset.mem_image_of_mem k hiS)
  rwa [hbval i hiS] at this

end

end GaloisForLFunctions.HTGeometry
