import GaloisForLFunctions.RHTower.ThetaArithmeticTerminalCusp
import GaloisForLFunctions.RHTower.ThetaCutoffCommutatorCofinalLimit

/-!
# The terminal squarefree word of finite theta deletion

Finite prime deletion is the literal arithmetic shift polynomial with
Möbius coefficients. Its full prime product is the unique terminal word,
and its negative-cusp sign is the parity of that complete word.
-/

open Filter Topology Set ArithmeticFunction

namespace RHTower

noncomputable section

/-- Every squarefree word of a finite prime alphabet, including the empty word. -/
def thetaPrimeDeletionWords (S : Finset ℕ) : Finset ℕ :=
  S.powerset.image (fun T => ∏ p ∈ T, p)

/-- The exact coefficient of an arithmetic word in finite theta deletion. -/
def thetaPrimeDeletionWordCoefficient (d : ℕ) : ℝ :=
  (moebius d : ℝ) * (d : ℝ) ^ (-(1 / 2 : ℝ))

@[simp] theorem thetaPrimeDeletionWordCoefficient_one :
    thetaPrimeDeletionWordCoefficient 1 = 1 := by
  simp [thetaPrimeDeletionWordCoefficient]

theorem thetaPrimeDeletionWords_one_mem (S : Finset ℕ) :
    1 ∈ thetaPrimeDeletionWords S := by
  classical
  exact Finset.mem_image.mpr ⟨∅, by simp, by simp⟩

theorem thetaPrimeDeletionWords_top_mem (S : Finset ℕ) :
    (∏ p ∈ S, p) ∈ thetaPrimeDeletionWords S := by
  classical
  exact Finset.mem_image.mpr ⟨S, by simp, rfl⟩

theorem thetaPrimeDeletionWords_positive
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∀ d ∈ thetaPrimeDeletionWords S, 0 < d := by
  classical
  intro d hd
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hd
  exact Finset.prod_pos fun p hp => (hS p (Finset.mem_powerset.mp hT hp)).pos

theorem thetaPrimeDeletionWords_le_top
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∀ d ∈ thetaPrimeDeletionWords S, d ≤ ∏ p ∈ S, p := by
  classical
  intro d hd
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hd
  exact Finset.prod_le_prod_of_subset_of_one_le (Finset.mem_powerset.mp hT)
    (fun p _ => Nat.zero_le p) (fun p hp _ => (hS p hp).one_lt.le)

/-- No formal divisor coefficients replace the actual deletion source. -/
theorem thetaPrimeDeletion_eq_arithmeticShift
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    thetaPrimeDeletion S thetaCuspFullSource =
      finiteArithmeticThetaShift (thetaPrimeDeletionWords S) thetaPrimeDeletionWordCoefficient := by
  classical
  funext x
  rw [finiteArithmeticThetaShift, thetaPrimeDeletionWords,
    Finset.sum_image (prod_primes_injOn hS), thetaPrimeDeletion]
  apply Finset.sum_congr rfl
  intro T hT
  have hmu : (moebius (∏ p ∈ T, p) : ℝ) = (-1 : ℝ) ^ T.card := by
    exact_mod_cast moebius_prod_distinct_primes
      (fun p hp => hS p (Finset.mem_powerset.mp hT hp))
  rw [thetaPrimeDeletionWordCoefficient, hmu]
  ring

theorem thetaPrimeDeletionWordCoefficient_top
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    thetaPrimeDeletionWordCoefficient (∏ p ∈ S, p) =
      (-1 : ℝ) ^ S.card * ((∏ p ∈ S, p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hmu : (moebius (∏ p ∈ S, p) : ℝ) = (-1 : ℝ) ^ S.card := by
    exact_mod_cast moebius_prod_distinct_primes hS
  rw [thetaPrimeDeletionWordCoefficient, hmu]

theorem thetaPrimeDeletionWordCoefficient_top_ne_zero
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    thetaPrimeDeletionWordCoefficient (∏ p ∈ S, p) ≠ 0 := by
  rw [thetaPrimeDeletionWordCoefficient_top S hS]
  have hprod : (0 : ℝ) < ((∏ p ∈ S, p : ℕ) : ℝ) := by
    exact_mod_cast (Finset.prod_pos fun p hp => (hS p hp).pos)
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (Real.rpow_pos_of_pos hprod _).ne'

/-- The exact negative-cusp terminal coefficient of every finite prime deletion. -/
theorem thetaPrimeDeletion_terminal_ratio
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Tendsto (fun x : ℝ => thetaPrimeDeletion S thetaCuspFullSource (-x) /
      thetaCuspFullSource (x - Real.log ((∏ p ∈ S, p : ℕ) : ℝ)))
      atTop (𝓝 (thetaPrimeDeletionWordCoefficient (∏ p ∈ S, p))) := by
  rw [thetaPrimeDeletion_eq_arithmeticShift S hS]
  exact finiteArithmeticThetaShift_terminal_ratio
    (thetaPrimeDeletionWords S) thetaPrimeDeletionWordCoefficient (∏ p ∈ S, p)
    (thetaPrimeDeletionWords_top_mem S) (thetaPrimeDeletionWords_positive S hS)
    (thetaPrimeDeletionWords_le_top S hS)

/-- The positive cusp of every finite deletion retains the complete source's first atom. -/
theorem thetaPrimeDeletion_positive_ratio
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Tendsto (fun x : ℝ => thetaPrimeDeletion S thetaCuspFullSource x / thetaCuspFullSource x)
      atTop (𝓝 1) := by
  rw [thetaPrimeDeletion_eq_arithmeticShift S hS]
  simpa only [if_pos (thetaPrimeDeletionWords_one_mem S),
    thetaPrimeDeletionWordCoefficient_one] using
      finiteArithmeticThetaShift_positive_ratio (thetaPrimeDeletionWords S)
        thetaPrimeDeletionWordCoefficient (thetaPrimeDeletionWords_positive S hS)

/-- The parity of the entire prime word is its eventual negative-cusp sign. -/
theorem thetaPrimeDeletion_terminal_sign
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∀ᶠ x : ℝ in atTop, 0 < (-1 : ℝ) ^ S.card * thetaPrimeDeletion S thetaCuspFullSource (-x) := by
  have hprod : (0 : ℝ) < ((∏ p ∈ S, p : ℕ) : ℝ) := by
    exact_mod_cast (Finset.prod_pos fun p hp => (hS p hp).pos)
  have h := (thetaPrimeDeletion_terminal_ratio S hS).const_mul ((-1 : ℝ) ^ S.card)
  have hconstant : (-1 : ℝ) ^ S.card * thetaPrimeDeletionWordCoefficient (∏ p ∈ S, p) =
      ((∏ p ∈ S, p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [thetaPrimeDeletionWordCoefficient_top S hS, ← mul_assoc, ← mul_pow]
    norm_num
  rw [hconstant] at h
  filter_upwards [h.eventually (Ioi_mem_nhds (Real.rpow_pos_of_pos hprod _))] with x hx
  have hden := thetaCuspFullSource_pos_all
    (x - Real.log ((∏ p ∈ S, p : ℕ) : ℝ))
  have hdiv : 0 < ((-1 : ℝ) ^ S.card * thetaPrimeDeletion S thetaCuspFullSource (-x)) /
      thetaCuspFullSource (x - Real.log ((∏ p ∈ S, p : ℕ) : ℝ)) := by
    simpa only [mul_div_assoc] using hx
  simpa only [zero_mul] using (lt_div_iff₀ hden).mp hdiv

end

end RHTower
