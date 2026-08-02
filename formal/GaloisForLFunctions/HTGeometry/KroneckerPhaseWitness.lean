import GaloisForLFunctions.HTGeometry.CirclePowerEstimates
import GaloisForLFunctions.HTGeometry.KroneckerWeylDensity
import GaloisForLFunctions.HTGeometry.RationalBasisIntegerCombination
import GaloisForLFunctions.HTGeometry.PrimeEulerProductAperture

/-!
# A detectable phase outside the integral span

For a rationally independent base `β` and a real `μ` outside the *integral* span of `β`, there is a
fixed phase `φ ∉ 2πℤ` such that, at arbitrarily good tolerance, some `τ` makes every `e^{iβ_jτ}`
close to `1` while `e^{iμτ}` is close to `e^{iφ}`.

Two mechanisms.  If `μ` is not even in the rational span, the family `(β, μ)` is rationally
independent and Kronecker's theorem hits the target `(0,…,0,π)` directly.  Otherwise
`μ = ∑ q_jβ_j` with rational `q_j`, not all integral; running Kronecker on the scaled base `β/N`
(`N` a common denominator) with targets `2πa_j/N` leaves the integers `a_j` free, and the induced
phase of `μ` is `2π∑a_jq_j` — nonzero for `a` supported at an index where `q_j ∉ ℤ`.
-/

open Filter Topology

namespace GaloisForLFunctions

open scoped BigOperators

/-- The character of an integer multiple of a frequency is that integer power. -/
theorem expChar_int_mul (β u : ℝ) (c : ℤ) :
    expChar ((c : ℝ) * β) u = (expChar β u) ^ c := by
  simp only [expChar]
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/-- **A detectable phase outside the integral span.** -/
theorem exists_phase_witness {k : ℕ} {β : Fin k → ℝ} (hind : LinearIndependent ℚ β)
    {μ : ℝ} (hμ : μ ∉ Submodule.span ℤ (Set.range β)) :
    ∃ φ : ℝ, (∀ n : ℤ, φ ≠ 2 * Real.pi * n) ∧
      ∀ δ : ℝ, 0 < δ → ∃ τ : ℝ,
        (∀ i, ‖expChar (β i) τ - 1‖ < δ) ∧
          ‖expChar μ τ - Complex.exp ((φ : ℝ) * Complex.I)‖ < δ := by
  classical
  have hpi : 0 < Real.pi := Real.pi_pos
  by_cases hspan : μ ∈ Submodule.span ℚ (Set.range β)
  · -- the rational case: a fractional coordinate
    obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hspan
    have hnotall : ∃ i : Fin k, ∀ z : ℤ, q i ≠ (z : ℚ) := by
      by_contra hcon
      push Not at hcon
      choose z hz using hcon
      refine hμ ((Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨z, ?_⟩)
      rw [← hq]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hz i, Rat.smul_def, zsmul_eq_mul]
      push_cast
      ring
    obtain ⟨i₀, hi₀⟩ := hnotall
    refine ⟨2 * Real.pi * ((q i₀ : ℚ) : ℝ), ?_, ?_⟩
    · intro n hn
      have h2 : (2 * Real.pi) ≠ 0 := by positivity
      have hqn : ((q i₀ : ℚ) : ℝ) = (n : ℝ) := mul_left_cancel₀ h2 hn
      exact hi₀ n (by exact_mod_cast hqn)
    · intro δ hδ
      -- the common denominator and the integer coordinates
      set N : ℕ := ∏ i : Fin k, (q i).den with hN
      have hNpos : 0 < N := Finset.prod_pos fun i _ => (q i).pos
      have hNne : ((N : ℝ)) ≠ 0 := by
        have : (0 : ℝ) < N := by exact_mod_cast hNpos
        exact ne_of_gt this
      choose c hc using fun i : Fin k =>
        exists_int_nat_mul (q i) (Finset.dvd_prod_of_mem (fun i => (q i).den) (Finset.mem_univ i))
      rw [← hN] at hc
      -- the scaled base
      set γ : Fin k → ℝ := fun i => ((N : ℝ))⁻¹ * β i with hγ
      have hγind : LinearIndependent ℚ γ :=
        linearIndependent_const_mul hind (inv_ne_zero hNne)
      set a : Fin k → ℤ := fun i => if i = i₀ then 1 else 0 with ha
      set θ : Fin k → ℝ := fun i => 2 * Real.pi * (a i : ℝ) / (N : ℝ) with hθ
      set M : ℕ := ∑ i : Fin k, (c i).natAbs with hM
      set B : ℝ := ((k : ℝ) + 1) * ((M : ℝ) + 1) * ((N : ℝ) + 1) with hB
      have hBpos : 0 < B := by
        have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        have h2 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
        have h3 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
        rw [hB]; positivity
      obtain ⟨τ, hτ⟩ := kronecker_approx hγind θ (show (0:ℝ) < δ / B by positivity)
      refine ⟨τ, ?_, ?_⟩
      · -- every base character is close to one
        intro i
        have hβγ : β i = (N : ℝ) * γ i := by
          rw [hγ]
          field_simp
        have hpow : expChar (β i) τ = (expChar (γ i) τ) ^ N := by
          rw [hβγ, expChar_nat_mul]
        have htarget : (Complex.exp ((θ i : ℝ) * Complex.I)) ^ N = 1 := by
          rw [← Complex.exp_nat_mul]
          have hreal : (N : ℝ) * θ i = 2 * Real.pi * (a i : ℝ) := by
            rw [hθ]
            field_simp
          have hval : (N : ℂ) * ((θ i : ℝ) * Complex.I)
              = ((a i : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
            calc (N : ℂ) * ((θ i : ℝ) * Complex.I)
                = ((((N : ℝ) * θ i : ℝ)) : ℂ) * Complex.I := by push_cast; ring
              _ = (((2 * Real.pi * (a i : ℝ) : ℝ)) : ℂ) * Complex.I := by rw [hreal]
              _ = ((a i : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
          rw [hval, Complex.exp_int_mul_two_pi_mul_I]
        have hz : ‖expChar (γ i) τ‖ = 1 := norm_expChar _ _
        have hw : ‖Complex.exp ((θ i : ℝ) * Complex.I)‖ = 1 :=
          Complex.norm_exp_ofReal_mul_I _
        have hstep := norm_pow_sub_pow_le_of_norm_one hz hw N
        rw [hpow]
        calc ‖(expChar (γ i) τ) ^ N - 1‖
            = ‖(expChar (γ i) τ) ^ N - (Complex.exp ((θ i : ℝ) * Complex.I)) ^ N‖ := by
              rw [htarget]
          _ ≤ (N : ℝ) * ‖expChar (γ i) τ - Complex.exp ((θ i : ℝ) * Complex.I)‖ := hstep
          _ < (N : ℝ) * (δ / B) := by
              have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
              exact mul_lt_mul_of_pos_left (hτ i) hNR
          _ ≤ δ := by
              have hk1 : (1:ℝ) ≤ (k : ℝ) + 1 := by
                have := Nat.cast_nonneg (α := ℝ) k; linarith
              have hM1 : (1:ℝ) ≤ (M : ℝ) + 1 := by
                have := Nat.cast_nonneg (α := ℝ) M; linarith
              have hN1 : (0:ℝ) ≤ (N : ℝ) + 1 := by positivity
              have hkM : (1:ℝ) ≤ ((k : ℝ) + 1) * ((M : ℝ) + 1) := by nlinarith [hk1, hM1]
              have hstep := mul_le_mul_of_nonneg_right hkM hN1
              have hNB : (N : ℝ) ≤ B := by
                rw [hB]
                rw [one_mul] at hstep
                linarith
              calc (N : ℝ) * (δ / B) ≤ B * (δ / B) :=
                    mul_le_mul_of_nonneg_right hNB (by positivity)
                _ = δ := by field_simp
      · -- the character of `μ` picks up the fractional phase
        have hμγ : μ = ∑ i : Fin k, (c i : ℝ) * γ i := by
          rw [← hq]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hci : ((c i : ℤ) : ℝ) = (N : ℝ) * ((q i : ℚ) : ℝ) := by
            have := congrArg (fun x : ℚ => (x : ℝ)) (hc i)
            push_cast at this
            exact this.symm
          rw [hγ, hci, Rat.smul_def]
          field_simp
        have hprod : expChar μ τ = ∏ i : Fin k, (expChar (γ i) τ) ^ (c i) := by
          rw [hμγ, ← prod_expChar]
          exact Finset.prod_congr rfl fun i _ => expChar_int_mul (γ i) τ (c i)
        have hphase : ∏ i : Fin k, (Complex.exp ((θ i : ℝ) * Complex.I)) ^ (c i)
            = Complex.exp ((2 * Real.pi * ((q i₀ : ℚ) : ℝ) : ℝ) * Complex.I) := by
          have hterm : ∀ i : Fin k, (Complex.exp ((θ i : ℝ) * Complex.I)) ^ (c i)
              = Complex.exp ((((c i : ℝ) * θ i : ℝ)) * Complex.I) := by
            intro i
            rw [← Complex.exp_int_mul]
            congr 1
            push_cast
            ring
          rw [Finset.prod_congr rfl fun i _ => hterm i, ← Complex.exp_sum]
          congr 1
          have hsum : ∑ i : Fin k, ((((c i : ℝ) * θ i : ℝ)) * Complex.I)
              = ((∑ i : Fin k, (c i : ℝ) * θ i : ℝ)) * Complex.I := by
            rw [← Finset.sum_mul]
            push_cast
            ring
          rw [hsum]
          congr 1
          have hval : ∑ i : Fin k, (c i : ℝ) * θ i = 2 * Real.pi * ((q i₀ : ℚ) : ℝ) := by
            have hterm2 : ∀ i : Fin k, (c i : ℝ) * θ i
                = 2 * Real.pi * (a i : ℝ) * (c i : ℝ) / (N : ℝ) := by
              intro i
              rw [hθ]
              ring
            rw [Finset.sum_congr rfl fun i _ => hterm2 i]
            have hzero : ∀ i ∈ Finset.univ, i ≠ i₀ →
                2 * Real.pi * (a i : ℝ) * (c i : ℝ) / (N : ℝ) = 0 := by
              intro i _ hne
              rw [ha]
              simp [hne]
            rw [Finset.sum_eq_single i₀ hzero (by simp)]
            have hai : ((a i₀ : ℤ) : ℝ) = 1 := by rw [ha]; simp
            have hci : ((c i₀ : ℤ) : ℝ) = (N : ℝ) * ((q i₀ : ℚ) : ℝ) := by
              have := congrArg (fun x : ℚ => (x : ℝ)) (hc i₀)
              push_cast at this
              exact this.symm
            rw [hai, hci]
            field_simp
          rw [hval]
        -- the product estimate
        have hnorm_a : ∀ i ∈ (Finset.univ : Finset (Fin k)),
            ‖(expChar (γ i) τ) ^ (c i)‖ ≤ 1 := by
          intro i _
          rw [norm_zpow, norm_expChar, one_zpow]
        have hnorm_b : ∀ i ∈ (Finset.univ : Finset (Fin k)),
            ‖(Complex.exp ((θ i : ℝ) * Complex.I)) ^ (c i)‖ ≤ 1 := by
          intro i _
          rw [norm_zpow, Complex.norm_exp_ofReal_mul_I, one_zpow]
        have hdiff : ∀ i ∈ (Finset.univ : Finset (Fin k)),
            ‖(expChar (γ i) τ) ^ (c i) - (Complex.exp ((θ i : ℝ) * Complex.I)) ^ (c i)‖
              ≤ (M : ℝ) * (δ / B) := by
          intro i _
          have hz : ‖expChar (γ i) τ‖ = 1 := norm_expChar _ _
          have hw : ‖Complex.exp ((θ i : ℝ) * Complex.I)‖ = 1 :=
            Complex.norm_exp_ofReal_mul_I _
          have hstep := norm_zpow_sub_zpow_le_of_norm_one hz hw (c i)
          have hcM : ((c i).natAbs : ℝ) ≤ (M : ℝ) := by
            have : (c i).natAbs ≤ M :=
              Finset.single_le_sum (f := fun j : Fin k => (c j).natAbs)
                (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
            exact_mod_cast this
          refine hstep.trans ?_
          exact mul_le_mul hcM (hτ i).le (norm_nonneg _) (by positivity)
        have hprodbound := norm_prod_sub_prod_le
          (fun i : Fin k => (expChar (γ i) τ) ^ (c i))
          (fun i : Fin k => (Complex.exp ((θ i : ℝ) * Complex.I)) ^ (c i))
          (le_refl (1 : ℝ)) (by positivity : (0:ℝ) ≤ (M : ℝ) * (δ / B))
          Finset.univ hnorm_a hnorm_b hdiff
        rw [hprod, ← hphase]
        have hcard : (((Finset.univ : Finset (Fin k)).card : ℝ)
            * 1 ^ (Finset.univ : Finset (Fin k)).card * ((M : ℝ) * (δ / B)))
            = (k : ℝ) * ((M : ℝ) * (δ / B)) := by
          rw [Finset.card_univ, Fintype.card_fin, one_pow, mul_one]
        rw [hcard] at hprodbound
        refine lt_of_le_of_lt hprodbound ?_
        have hkM : (k : ℝ) * ((M : ℝ) * (δ / B)) = ((k : ℝ) * (M : ℝ)) * δ / B := by ring
        rw [hkM, div_lt_iff₀ hBpos]
        have hk0 : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
        have hM0 : (0:ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
        have hN0 : (0:ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
        have hkMB : (k : ℝ) * (M : ℝ) < B := by
          rw [hB]
          nlinarith [hk0, hM0, hN0]
        nlinarith [hδ, hkMB]
  · -- the irrational case: the family together with `μ` is rationally independent
    have hindsnoc : LinearIndependent ℚ (Fin.snoc β μ : Fin (k + 1) → ℝ) :=
      LinearIndependent.finSnoc hind hspan
    refine ⟨Real.pi, ?_, ?_⟩
    · intro n hn
      have h2 : (2 : ℝ) * (n : ℝ) = 1 := by
        have hpine : Real.pi ≠ 0 := ne_of_gt hpi
        field_simp at hn
        linarith [hn]
      have hn' : (2 * n : ℤ) = 1 := by exact_mod_cast h2
      omega
    · intro δ hδ
      set θ : Fin (k + 1) → ℝ := Fin.snoc (fun _ : Fin k => (0 : ℝ)) Real.pi with hθ
      obtain ⟨τ, hτ⟩ := kronecker_approx hindsnoc θ hδ
      refine ⟨τ, ?_, ?_⟩
      · intro i
        have h := hτ i.castSucc
        rw [Fin.snoc_castSucc] at h
        have hθi : θ i.castSucc = 0 := by
          rw [hθ, Fin.snoc_castSucc]
        rw [hθi] at h
        simpa using h
      · have h := hτ (Fin.last k)
        rw [Fin.snoc_last] at h
        have hθl : θ (Fin.last k) = Real.pi := by
          rw [hθ, Fin.snoc_last]
        rw [hθl] at h
        exact h

end GaloisForLFunctions
