import GaloisForLFunctions.HTGeometry.ChirpSumIndependence

/-!
# Glue for the endpoint chirp

Three elementary facts are needed to instantiate the chirp-independence lemma at the endpoint pairs
of a differential-polynomial coefficient identity.

* The descending-factorial weight of a jet is asymptotically the pure power: `(M+u)_j / M^j → 1`.
  This is the `j`-fold product of factors `1 + (u−i)/M`.
* Among finitely many indices with a nonzero coefficient there is one of maximal real exponent.
* The endpoint exponents separate the pairs: if `j₁ + r(j₁−q₁) = j₂ + r(j₂−q₂)` and the integer
  frequencies `j₁−q₁` and `j₂−q₂` agree, then the pairs agree.  This is why the surviving layer of
  the chirp sum is a trigonometric polynomial with *distinct* frequencies.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The descending-factorial weight -/

theorem tendsto_natCast_inv_zero : Tendsto (fun M : ℕ => ((M : ℂ))⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hval : ∀ M : ℕ, ‖((M : ℂ))⁻¹‖ = ((M : ℝ))⁻¹ := by
    intro M
    rw [norm_inv, Complex.norm_natCast]
  refine Tendsto.congr (fun M => (hval M).symm) ?_
  exact tendsto_natCast_atTop_atTop.inv_tendsto_atTop

/-- **The descending factorial is the pure power, asymptotically.** -/
theorem tendsto_descFactorial_div_pow (u j : ℕ) :
    Tendsto (fun M : ℕ => (((M + u).descFactorial j : ℕ) : ℂ) / ((M : ℂ) ^ j)) atTop (𝓝 1) := by
  induction j with
  | zero =>
      refine Tendsto.congr (fun M => ?_) tendsto_const_nhds
      simp
  | succ j ih =>
      have hstep : Tendsto (fun M : ℕ => (((M + u - j : ℕ)) : ℂ) / (M : ℂ)) atTop (𝓝 1) := by
        have hinv : Tendsto (fun M : ℕ => ((u : ℂ) - (j : ℂ)) * ((M : ℂ))⁻¹) atTop (𝓝 0) := by
          have := tendsto_natCast_inv_zero.const_mul ((u : ℂ) - (j : ℂ))
          simpa using this
        have hone : Tendsto (fun M : ℕ => (1 : ℂ) + ((u : ℂ) - (j : ℂ)) * ((M : ℂ))⁻¹)
            atTop (𝓝 1) := by
          have := (tendsto_const_nhds (x := (1 : ℂ)) (f := atTop (α := ℕ))).add hinv
          simpa using this
        refine hone.congr' ?_
        filter_upwards [eventually_ge_atTop (max 1 j)] with M hM
        have hMj : j ≤ M := le_trans (le_max_right _ _) hM
        have hM1 : 1 ≤ M := le_trans (le_max_left _ _) hM
        have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
        have hMne : (M : ℂ) ≠ 0 := by
          simpa using ne_of_gt hMpos
        have hle : j ≤ M + u := by omega
        have hcast : (((M + u - j : ℕ)) : ℂ) = (M : ℂ) + (u : ℂ) - (j : ℂ) := by
          rw [Nat.cast_sub hle]
          push_cast
          ring
        rw [hcast]
        field_simp
        ring
      have hprod := hstep.mul ih
      rw [one_mul] at hprod
      refine hprod.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with M hM
      have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
      have hMne : (M : ℂ) ≠ 0 := by simpa using ne_of_gt hMpos
      rw [Nat.descFactorial_succ, Nat.cast_mul]
      field_simp
      ring

/-! ## Selecting the maximal exponent -/

/-- Among finitely many indices with a nonzero coefficient there is one of maximal exponent. -/
theorem exists_max_exponent_of_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → ℂ}
    {ρ : ι → ℝ} {i₀ : ι} (hi₀ : A i₀ ≠ 0) :
    ∃ smax : ℝ, (∃ i, A i ≠ 0 ∧ ρ i = smax) ∧ ∀ i, A i ≠ 0 → ρ i ≤ smax := by
  classical
  set S : Finset ι := Finset.univ.filter (fun i => A i ≠ 0) with hS
  have hSne : S.Nonempty := ⟨i₀, by simp [hS, hi₀]⟩
  obtain ⟨i₁, hi₁, hsup⟩ := Finset.exists_mem_eq_sup' hSne ρ
  refine ⟨S.sup' hSne ρ, ⟨i₁, ?_, hsup.symm⟩, ?_⟩
  · simpa [hS] using hi₁
  · intro i hi
    exact Finset.le_sup' ρ (by simp [hS, hi])

/-! ## Separation of the endpoint pairs -/

/-- **The endpoint exponents separate the pairs.**  Equal real exponents together with equal
integer frequencies force the pairs to coincide. -/
theorem endpoint_pair_eq {r : ℝ} {j₁ q₁ j₂ q₂ : ℤ}
    (hρ : (j₁ : ℝ) + r * ((j₁ : ℝ) - (q₁ : ℝ)) = (j₂ : ℝ) + r * ((j₂ : ℝ) - (q₂ : ℝ)))
    (hk : j₁ - q₁ = j₂ - q₂) : j₁ = j₂ ∧ q₁ = q₂ := by
  have hkR : (j₁ : ℝ) - (q₁ : ℝ) = (j₂ : ℝ) - (q₂ : ℝ) := by exact_mod_cast hk
  have hjR : (j₁ : ℝ) = (j₂ : ℝ) := by
    rw [hkR] at hρ
    linarith
  have hj : j₁ = j₂ := by exact_mod_cast hjR
  refine ⟨hj, ?_⟩
  omega

end

end GaloisForLFunctions.HTGeometry
