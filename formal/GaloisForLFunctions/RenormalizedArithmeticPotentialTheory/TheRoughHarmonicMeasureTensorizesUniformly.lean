import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHarmonicMeasureTensorizesOverPrimes

/-!
# Uniform tensorization on harmonic rough intervals

The prime-peeling potential is nonpositive at every starting prime threshold.
The same shell bound therefore controls all rough intervals with one constant.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- Harmonic variance on every rough interval is bounded by its prime-ladder
Glauber form with one constant, independent of threshold and horizon. -/
theorem exists_rough_harmonicVar_le_glauberForm :
    ∃ C : ℝ, 0 < C ∧ ∀ Q X : ℕ, ∀ f : ℕ → ℝ,
      harmonicVar Q X f ≤ C * glauberForm Q X f := by
  obtain ⟨Cτ, hCτ1, hτ⟩ := exists_shellTau_le
  set η := 4 * Cτ
  have hη : 0 < η := by positivity
  set δs := (4 * Cτ + 1) / (4 * Cτ + 2)
  set A := (1 + 1 / η) * Cτ * (4 * Cτ + 2)
  have hA : 0 ≤ A := by positivity
  set K := (1 + η) * Real.exp (3 * A)
  have hK : 0 < K := by positivity
  set S : ℕ → ℝ := fun Q => ∑ q ∈ Nat.primesBelow Q, Real.log q / q
  have hS0 : ∀ Q, 0 ≤ S Q := fun Q => sum_nonneg fun q _ => div_nonneg
    (Real.log_natCast_nonneg q) (Nat.cast_nonneg q)
  set Ψ : ℕ → ℕ → ℝ := fun Q X => -A * S Q / Real.log X
  -- the claim, by strong induction on `X + 1 − Q`
  have claim : ∀ k Q X, X + 1 - Q ≤ k → 2 ≤ X → ∀ f : ℕ → ℝ,
      harmonicVar Q X f ≤ K * Real.exp (Ψ Q X) * glauberForm Q X f := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro Q X hk hX f
    have hlX : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    have hRHS : 0 ≤ K * Real.exp (Ψ Q X) * glauberForm Q X f :=
      mul_nonneg (by positivity) (glauberForm_nonneg _ _ _)
    by_cases hQX : X < Q
    · rw [harmonicVar_eq_zero_of_le_one (fun K hK => eq_one_of_mem_roughInterval_of_le hK hQX)]
      exact hRHS
    rw [not_lt] at hQX
    by_cases hQ : Q.Prime
    · -- peel `p = Q`
      have hp2 := hQ.two_le
      set p := Q
      set Bc := K * Real.exp (-A * S (p + 1) / Real.log X)
      have hBc : 0 ≤ Bc := by positivity
      have hSp : S (p + 1) = S p + Real.log p / p := by
        simp only [S, primesBelow_succ_eq, if_pos hQ]
        rw [sum_insert (fun h => by simp [Nat.primesBelow] at h)]
        ring
      -- the level bound
      have hlev : ∀ j ∈ range (X + 1), harmonicVar (p + 1) (X / p ^ j) (fun K => f (p ^ j * K)) ≤
          Bc * glauberForm (p + 1) (X / p ^ j) (fun K => f (p ^ j * K)) := by
        intro j _
        set Y := X / p ^ j
        by_cases hY : Y ≤ p
        · rw [harmonicVar_eq_zero_of_le_one (fun K hK => eq_one_of_mem_roughInterval_of_le hK
            (by omega))]
          exact mul_nonneg hBc (glauberForm_nonneg _ _ _)
        · have hYX : Y ≤ X := Nat.div_le_self _ _
          have hih := ih (Y + 1 - (p + 1)) (by omega) (p + 1) Y le_rfl (by omega)
            (fun K => f (p ^ j * K))
          refine hih.trans (mul_le_mul_of_nonneg_right ?_ (glauberForm_nonneg _ _ _))
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK.le
          have hlY : 0 < Real.log Y := Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
          have hlYX : Real.log Y ≤ Real.log X :=
            Real.log_le_log (by exact_mod_cast (show 0 < Y by omega)) (by exact_mod_cast hYX)
          simp only [Ψ]
          rw [div_le_div_iff₀ hlY hlX]
          have hmon := mul_nonneg (mul_nonneg hA (hS0 (p + 1))) (sub_nonneg.mpr hlYX)
          nlinarith only [hmon]
      -- the shell rate
      obtain ⟨hτ1, hτ2⟩ := hτ p X hQ hQX
      have hτ0 := shellTau_nonneg p X
      set δ := (1 + 1 / η) * shellTau p X
      have hδ0 : 0 ≤ δ := by positivity
      have hδs : δ ≤ δs := by
        have e : (1 + 1 / η) * (1 - 1 / (1 + 2 * Cτ)) = δs := by
          simp only [δs, η]; field_simp; ring
        calc δ ≤ (1 + 1 / η) * (1 - 1 / (1 + 2 * Cτ)) :=
              mul_le_mul_of_nonneg_left hτ2 (by positivity)
          _ = δs := e
      have hδs1 : 1 - δs = 1 / (4 * Cτ + 2) := by
        simp only [δs]; field_simp; ring
      have hδ1 : 0 < 1 - δ := by
        have : δs < 1 := by
          have : 0 < 1 / (4 * Cτ + 2) := by positivity
          linarith
        linarith
      have hδA : δ / (1 - δs) ≤ A * (Real.log p / (p * Real.log X)) := by
        rw [hδs1, div_div_eq_mul_div, div_one]
        have h := mul_le_mul_of_nonneg_left hτ1 (show 0 ≤ 1 + 1 / η by positivity)
        have hpos : 0 ≤ Real.log p / (p * Real.log X) := by
          have : 0 ≤ Real.log p := Real.log_natCast_nonneg p
          positivity
        calc δ * (4 * Cτ + 2) ≤ (1 + 1 / η) * (Cτ * (Real.log p / (p * Real.log X))) *
              (4 * Cτ + 2) := mul_le_mul_of_nonneg_right h (by positivity)
          _ = A * (Real.log p / (p * Real.log X)) := by simp only [A]; ring
      -- `B ≥ 1 + η`
      have hBη : 1 + η ≤ Bc := by
        have hm := RHTower.mertens_first_upper (n := p) (by have := hQ.two_le; omega)
        have hSle : S (p + 1) ≤ Real.log p + Real.log 4 := hm
        have hlp : Real.log p ≤ Real.log X :=
          Real.log_le_log (by exact_mod_cast hQ.pos) (by exact_mod_cast hQX)
        have hl2 : Real.log 2 ≤ Real.log X :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hX)
        have hl4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        have h3 : S (p + 1) / Real.log X ≤ 3 := by
          rw [div_le_iff₀ hlX]
          linarith only [hSle, hlp, hl4, hl2]
        have : 0 ≤ 3 * A + -A * S (p + 1) / Real.log X := by
          rw [neg_mul, neg_div, mul_div_assoc]
          nlinarith only [mul_nonneg hA (sub_nonneg.mpr h3)]
        calc 1 + η = (1 + η) * 1 := (mul_one _).symm
          _ ≤ (1 + η) * Real.exp (3 * A + -A * S (p + 1) / Real.log X) :=
              mul_le_mul_of_nonneg_left (Real.one_le_exp this) (by positivity)
          _ = Bc := by simp only [Bc, K]; rw [Real.exp_add]; ring
      have hpeel := peel hQ hQX f hη hBc hlev
      rw [max_eq_left hBη] at hpeel
      -- `V ≤ B/(1 − δ) G ≤ B e^{δ/(1−δ*)} G ≤ K e^{Ψ} G`
      have hV : harmonicVar p X f ≤ Bc / (1 - δ) * glauberForm p X f := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδ1]
        linarith
      have hexp : 1 / (1 - δ) ≤ Real.exp (A * (Real.log p / (p * Real.log X))) := by
        have h1 : 1 / (1 - δ) = 1 + δ / (1 - δ) := by field_simp; ring
        have h2 : δ / (1 - δ) ≤ δ / (1 - δs) :=
          div_le_div_of_nonneg_left hδ0 (by
            have : 0 < 1 / (4 * Cτ + 2) := by positivity
            linarith) (by linarith)
        rw [h1]
        linarith [Real.add_one_le_exp (A * (Real.log p / (p * Real.log X)))]
      have hBK : Bc * Real.exp (A * (Real.log p / (p * Real.log X))) = K * Real.exp (Ψ p X) := by
        simp only [Bc, Ψ, mul_assoc, ← Real.exp_add]
        congr 2
        rw [hSp]
        field_simp
        ring
      calc harmonicVar p X f ≤ Bc / (1 - δ) * glauberForm p X f := hV
        _ = Bc * (1 / (1 - δ)) * glauberForm p X f := by ring
        _ ≤ Bc * Real.exp (A * (Real.log p / (p * Real.log X))) * glauberForm p X f :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hBc)
              (glauberForm_nonneg _ _ _)
        _ = K * Real.exp (Ψ p X) * glauberForm p X f := by rw [hBK]
    · -- `Q` is not prime: pass to `Q + 1`
      have hR : roughInterval (Q + 1) X = roughInterval Q X := roughInterval_succ_of_not_prime hQ X
      have hP : (Icc (Q + 1) X).filter Nat.Prime = (Icc Q X).filter Nat.Prime := by
        ext q
        simp only [mem_filter, mem_Icc]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, h2⟩, h3⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩
          rcases h1.lt_or_eq with h | h
          · exact ⟨⟨h, h2⟩, h3⟩
          · exact absurd (h ▸ h3) hQ
      have hS : S (Q + 1) = S Q := by
        simp only [S, primesBelow_succ_eq, if_neg hQ]
      have hih := ih (X + 1 - (Q + 1)) (by omega) (Q + 1) X le_rfl hX f
      have hG : glauberForm (Q + 1) X f = glauberForm Q X f := by
        rw [glauberForm, glauberForm, hP, hR]
      rw [harmonicVar, ← hR]
      calc wVar (roughInterval (Q + 1) X) (fun n => 1 / (n : ℝ)) f = harmonicVar (Q + 1) X f := rfl
        _ ≤ K * Real.exp (Ψ (Q + 1) X) * glauberForm (Q + 1) X f := hih
        _ = K * Real.exp (Ψ Q X) * glauberForm Q X f := by simp only [Ψ, hS, hG]
  refine ⟨K, hK, fun Q X f => ?_⟩
  by_cases hX : 2 ≤ X
  · have h := claim (X + 1 - Q) Q X le_rfl hX f
    have hlog : 0 ≤ Real.log X := Real.log_natCast_nonneg X
    have hΨ : Ψ Q X ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hA) (hS0 Q)) hlog
    have hexp : Real.exp (Ψ Q X) ≤ 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hΨ
    exact h.trans (mul_le_mul_of_nonneg_right
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hK.le)
      (glauberForm_nonneg Q X f))
  · rw [harmonicVar_eq_zero_of_le_one fun n hn => by
      have := mem_roughInterval.mp hn; omega]
    exact mul_nonneg hK.le (glauberForm_nonneg _ _ _)


end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
