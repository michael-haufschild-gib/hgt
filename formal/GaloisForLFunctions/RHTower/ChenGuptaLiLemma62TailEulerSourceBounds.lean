import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailTruncatedBounds

/-!
# Chen--Gupta--Li Lemma 6.2: far-left source Euler bound

This sharpens the uniform tail-strip Euler envelope on the exact far-left
line.  It retains the source's elementary prime-power conductor loss.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

private theorem cglLemma62_farEuler_left_factor_source_bound
    (B : CGLLemma62InducedCharacter) (d : CGLLemma62TailContourDepth)
    (z : CGLLemma62TailEulerPoint d) (p : ↑B.ambient.value.primeFactors) :
    ‖1 - B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ ≤
      (p.1 : ℝ) ^ (2 * (d.value : ℝ) + 1) := by
  have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hpone : (1 : ℝ) ≤ p.1 := by exact_mod_cast hp.one_le
  have hptwo : (2 : ℝ) ≤ p.1 := by exact_mod_cast hp.two_le
  have hpow : ‖(p.1 : ℂ) ^ (-z.value)‖ =
      (p.1 : ℝ) ^ (2 * (d.value : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    congr 1
    simp only [neg_re]
    rw [z.real_eq]
    ring
  have hmul : ‖B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ ≤
      (p.1 : ℝ) ^ (2 * (d.value : ℝ)) := by
    rw [norm_mul, hpow]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _)
      (B.primitive.character.norm_le_one p.1)
  have hcore : 1 + (p.1 : ℝ) ^ (2 * (d.value : ℝ)) ≤
      (p.1 : ℝ) ^ (2 * (d.value : ℝ) + 1) := by
    have hpowone : 1 ≤ (p.1 : ℝ) ^ (2 * (d.value : ℝ)) := by
      exact Real.one_le_rpow hpone (by positivity)
    have hpow0 : 0 ≤ (p.1 : ℝ) ^ (2 * (d.value : ℝ)) :=
      Real.rpow_nonneg (by positivity) _
    calc
      1 + (p.1 : ℝ) ^ (2 * (d.value : ℝ)) ≤
          2 * (p.1 : ℝ) ^ (2 * (d.value : ℝ)) := by linarith
      _ ≤ (p.1 : ℝ) * (p.1 : ℝ) ^ (2 * (d.value : ℝ)) := by
        gcongr
      _ = (p.1 : ℝ) ^ (2 * (d.value : ℝ) + 1) := by
        calc
          (p.1 : ℝ) * (p.1 : ℝ) ^ (2 * (d.value : ℝ)) =
              (p.1 : ℝ) ^ (1 : ℝ) * (p.1 : ℝ) ^ (2 * (d.value : ℝ)) := by
                rw [Real.rpow_one]
          _ = (p.1 : ℝ) ^ ((1 : ℝ) + 2 * (d.value : ℝ)) :=
            (Real.rpow_add (by positivity) _ _).symm
          _ = _ := by congr 1; ring
  calc
    ‖1 - B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ ≤
        ‖(1 : ℂ)‖ + ‖B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ :=
      norm_sub_le _ _
    _ = 1 + ‖B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ := by norm_num
    _ ≤ 1 + (p.1 : ℝ) ^ (2 * (d.value : ℝ)) := by gcongr
    _ ≤ _ := hcore

private theorem cglLemma62_farEuler_right_factor_source_lower
    (B : CGLLemma62InducedCharacter) (d : CGLLemma62TailContourDepth)
    (z : CGLLemma62TailEulerPoint d) (p : ↑B.ambient.value.primeFactors) :
    (1 : ℝ) / 2 ≤
      ‖1 - B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z.value))‖ := by
  have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hpone : (1 : ℝ) ≤ p.1 := by exact_mod_cast hp.one_le
  have hptwo : (2 : ℝ) ≤ p.1 := by exact_mod_cast hp.two_le
  have hpow : ‖(p.1 : ℂ) ^ (-(1 - z.value))‖ =
      (p.1 : ℝ) ^ (-(1 + 2 * (d.value : ℝ))) := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    congr 1
    simp only [neg_re, sub_re, one_re]
    rw [z.real_eq]
    ring
  have hpowhalf : ‖(p.1 : ℂ) ^ (-(1 - z.value))‖ ≤ (1 : ℝ) / 2 := by
    rw [hpow]
    calc
      (p.1 : ℝ) ^ (-(1 + 2 * (d.value : ℝ))) ≤ (p.1 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hpone (by
          have hd : 0 ≤ (d.value : ℝ) := Nat.cast_nonneg _
          linarith)
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hptwo (by norm_num)
      _ = 1 / 2 := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_one]
        norm_num [div_eq_mul_inv]
  have hmul : ‖B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z.value))‖ ≤
      (1 : ℝ) / 2 := by
    rw [norm_mul]
    calc
      ‖B.primitive.character⁻¹ p.1‖ * ‖(p.1 : ℂ) ^ (-(1 - z.value))‖ ≤
          1 * ‖(p.1 : ℂ) ^ (-(1 - z.value))‖ := by
        gcongr
        exact B.primitive.character⁻¹.norm_le_one p.1
      _ ≤ 1 / 2 := by simpa using hpowhalf
  have htri : (1 : ℝ) ≤
      ‖1 - B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z.value))‖ +
        ‖B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z.value))‖ := by
    calc
      (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
      _ = ‖(1 - B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z.value)) +
          B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z.value)))‖ := by
            congr 1
            ring
      _ ≤ _ := norm_add_le _ _
  linarith

private theorem cglLemma62_farEuler_factor_source_bound
    (B : CGLLemma62InducedCharacter) (d : CGLLemma62TailContourDepth)
    (z : CGLLemma62TailEulerPoint d) (p : ↑B.ambient.value.primeFactors) :
    ‖1 - B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ /
        ‖1 - B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z.value))‖ ≤
      (p.1 : ℝ) ^ (2 * (d.value : ℝ) + 2) := by
  have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hptwo : (2 : ℝ) ≤ p.1 := by exact_mod_cast hp.two_le
  have hdenlower := cglLemma62_farEuler_right_factor_source_lower B d z p
  have hdenpos : 0 < ‖1 - B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^
      (-(1 - z.value))‖ := lt_of_lt_of_le (by norm_num) hdenlower
  apply (div_le_iff₀ hdenpos).mpr
  have hnum := cglLemma62_farEuler_left_factor_source_bound B d z p
  calc
    ‖1 - B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ ≤
        (p.1 : ℝ) ^ (2 * (d.value : ℝ) + 1) := hnum
    _ ≤ (p.1 : ℝ) ^ (2 * (d.value : ℝ) + 2) / 2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      have hpow0 : 0 ≤ (p.1 : ℝ) ^ (2 * (d.value : ℝ) + 1) :=
        Real.rpow_nonneg (by positivity) _
      calc
        (p.1 : ℝ) ^ (2 * (d.value : ℝ) + 1) * 2 ≤
            (p.1 : ℝ) ^ (2 * (d.value : ℝ) + 1) * p.1 := by gcongr
        _ = (p.1 : ℝ) ^ (2 * (d.value : ℝ) + 2) := by
          calc
            (p.1 : ℝ) ^ (2 * (d.value : ℝ) + 1) * p.1 =
                (p.1 : ℝ) ^ (2 * (d.value : ℝ) + 1) * (p.1 : ℝ) ^ (1 : ℝ) := by
                  rw [Real.rpow_one]
            _ = (p.1 : ℝ) ^ (2 * (d.value : ℝ) + 1 + 1) :=
              (Real.rpow_add (by positivity) _ _).symm
            _ = _ := by congr 1; ring
    _ = (p.1 : ℝ) ^ (2 * (d.value : ℝ) + 2) * (1 / 2) := by ring
    _ ≤ (p.1 : ℝ) ^ (2 * (d.value : ℝ) + 2) *
        ‖1 - B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z.value))‖ := by
          gcongr

/-- The elementary CGL far-line prime-power Euler budget. -/
def cglLemma62TailEulerSourceFactorBudget (B : CGLLemma62InducedCharacter)
    (d : CGLLemma62TailContourDepth) : ℝ :=
  ∏ p ∈ B.ambient.value.primeFactors,
    (p : ℝ) ^ (2 * (d.value : ℝ) + 2)

/-- On `Re(z)=-2k`, each Euler factor has the exact elementary source loss,
and their product is bounded by the displayed finite prime-power budget. -/
theorem cglLemma62EulerCorrectionAt_far_sourceFactor_norm_le
    (B : CGLLemma62InducedCharacter) (d : CGLLemma62TailContourDepth)
    (z : CGLLemma62TailEulerPoint d) :
    ‖cglLemma62EulerCorrectionAt B z.value‖ ≤
      cglLemma62TailEulerSourceFactorBudget B d := by
  unfold cglLemma62EulerCorrectionAt cglLemma62EulerLeftFactorAt cglLemma62EulerRightFactorAt
    cglLemma62TailEulerSourceFactorBudget
  rw [norm_div, norm_prod, norm_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_le_prod
  · intro p hp
    exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  · intro p hp
    exact cglLemma62_farEuler_factor_source_bound B d z ⟨p, hp⟩

/-- The coarser ambient-level collapse of the elementary far-line Euler budget. -/
theorem cglLemma62_tailEuler_sourceFactorBudget_le_ambient_power
    (B : CGLLemma62InducedCharacter) (d : CGLLemma62TailContourDepth) :
    cglLemma62TailEulerSourceFactorBudget B d ≤
      (B.ambient.value : ℝ) ^ (2 * (d.value : ℝ) + 2) := by
  have hprod_nat : ∏ p ∈ B.ambient.value.primeFactors, p ∣ B.ambient.value :=
    Nat.prod_primeFactors_dvd B.ambient.value
  have hprod_nat_le : ∏ p ∈ B.ambient.value.primeFactors, p ≤ B.ambient.value :=
    Nat.le_of_dvd B.ambient.positive hprod_nat
  have hprod : (∏ p ∈ B.ambient.value.primeFactors, (p : ℝ)) ≤
      (B.ambient.value : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast hprod_nat_le
  unfold cglLemma62TailEulerSourceFactorBudget
  rw [Real.finsetProd_rpow]
  · apply Real.rpow_le_rpow
    · positivity
    · exact hprod
    · positivity
  · intro p hp
    positivity

/-- Primes already present in the primitive conductor contribute the identity
factor to CGL's reflected Euler correction. -/
private theorem cglLemma62_primitiveCharacter_apply_eq_zero_of_dvd_modulus
    (B : CGLLemma62InducedCharacter) (p : ℕ)
    (hpprime : p.Prime) (hpdvd : p ∣ B.primitive.modulus.value) :
    B.primitive.character p = 0 := by
  rw [show (p : ZMod B.primitive.modulus.value) =
      ((p : ℤ) : ZMod B.primitive.modulus.value) from (Int.cast_natCast p).symm]
  apply (DirichletCharacter.apply_eq_zero_iff B.primitive.character (p : ℤ)).mpr
  intro hcoprime
  exact (hpprime.coprime_iff_not_dvd.mp
    (Nat.isCoprime_iff_coprime.mp hcoprime)) hpdvd

private theorem cglLemma62_primitiveCharacter_inverse_apply_eq_zero_of_dvd_modulus
    (B : CGLLemma62InducedCharacter) (p : ℕ)
    (hpprime : p.Prime) (hpdvd : p ∣ B.primitive.modulus.value) :
    B.primitive.character⁻¹ p = 0 := by
  rw [MulChar.inv_apply_eq_inv',
    cglLemma62_primitiveCharacter_apply_eq_zero_of_dvd_modulus B p hpprime hpdvd,
    inv_zero]

private theorem cglLemma62_farEuler_factor_conductor_bound
    (B : CGLLemma62InducedCharacter) (d : CGLLemma62TailContourDepth)
    (z : CGLLemma62TailEulerPoint d) (p : ↑B.ambient.value.primeFactors) :
    ‖1 - B.primitive.character p.1 * (p.1 : ℂ) ^ (-z.value)‖ /
        ‖1 - B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^ (-(1 - z.value))‖ ≤
      if p.1 ∣ B.primitive.modulus.value then 1 else
        (p.1 : ℝ) ^ (2 * (d.value : ℝ) + 2) := by
  by_cases hpdvd : p.1 ∣ B.primitive.modulus.value
  · rw [if_pos hpdvd]
    have hpprime : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
    have hchar := cglLemma62_primitiveCharacter_apply_eq_zero_of_dvd_modulus
      B p.1 hpprime hpdvd
    have hinv := cglLemma62_primitiveCharacter_inverse_apply_eq_zero_of_dvd_modulus
      B p.1 hpprime hpdvd
    simp [hchar, hinv]
  · rw [if_neg hpdvd]
    exact cglLemma62_farEuler_factor_source_bound B d z p

/-- The ambient primes that are not already in the primitive conductor. -/
noncomputable def cglLemma62TailEulerOuterPrimeSupport
    (B : CGLLemma62InducedCharacter) : Finset ℕ := by
  classical
  exact B.ambient.value.primeFactors.filter (fun p => ¬ p ∣ B.primitive.modulus.value)

/-- The exact far-left Euler budget after removing primitive-conductor primes. -/
def cglLemma62TailEulerConductorBudget (B : CGLLemma62InducedCharacter)
    (d : CGLLemma62TailContourDepth) : ℝ :=
  ∏ p ∈ cglLemma62TailEulerOuterPrimeSupport B,
    (p : ℝ) ^ (2 * (d.value : ℝ) + 2)

/-- The literal far-left CGL Euler correction needs only primes of `q/q*`. -/
theorem cglLemma62EulerCorrectionAt_far_conductorBudget_norm_le
    (B : CGLLemma62InducedCharacter) (d : CGLLemma62TailContourDepth)
    (z : CGLLemma62TailEulerPoint d) :
    ‖cglLemma62EulerCorrectionAt B z.value‖ ≤
      cglLemma62TailEulerConductorBudget B d := by
  classical
  unfold cglLemma62EulerCorrectionAt cglLemma62EulerLeftFactorAt cglLemma62EulerRightFactorAt
    cglLemma62TailEulerConductorBudget
  rw [norm_div, norm_prod, norm_prod, ← Finset.prod_div_distrib]
  calc
    ∏ p ∈ B.ambient.value.primeFactors,
        ‖1 - B.primitive.character p * (p : ℂ) ^ (-z.value)‖ /
          ‖1 - B.primitive.character⁻¹ p * (p : ℂ) ^ (-(1 - z.value))‖ ≤
      ∏ p ∈ B.ambient.value.primeFactors,
        if p ∣ B.primitive.modulus.value then 1 else
          (p : ℝ) ^ (2 * (d.value : ℝ) + 2) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact div_nonneg (norm_nonneg _) (norm_nonneg _)
        · intro p hp
          exact cglLemma62_farEuler_factor_conductor_bound B d z ⟨p, hp⟩
    _ = ∏ p ∈ cglLemma62TailEulerOuterPrimeSupport B,
        (p : ℝ) ^ (2 * (d.value : ℝ) + 2) := by
      rw [cglLemma62TailEulerOuterPrimeSupport, Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro p hp
      by_cases hpdvd : p ∣ B.primitive.modulus.value <;> simp [hpdvd]

theorem cglLemma62_tailEulerOuterPrimeSupport_product_dvd_conductorQuotient
    (B : CGLLemma62InducedCharacter) :
    (∏ p ∈ cglLemma62TailEulerOuterPrimeSupport B, p) ∣
      B.ambient.value / B.primitive.modulus.value := by
  classical
  apply dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ ?_)
    (Nat.prod_primeFactors_dvd _)
  intro p hp
  rw [Nat.mem_primeFactors]
  rcases Finset.mem_filter.mp hp with ⟨hpambient, hpnotdvd⟩
  refine ⟨Nat.prime_of_mem_primeFactors hpambient, ?_, ?_⟩
  · have hpdvdambient : p ∣ B.ambient.value := Nat.dvd_of_mem_primeFactors hpambient
    rw [← Nat.div_mul_cancel B.conductor_dvd_ambient] at hpdvdambient
    exact (Nat.Prime.dvd_mul (Nat.prime_of_mem_primeFactors hpambient)).mp hpdvdambient |>.resolve_right hpnotdvd
  · exact Nat.ne_of_gt (Nat.div_pos
      (Nat.le_of_dvd B.ambient.positive B.conductor_dvd_ambient) B.primitive.modulus.positive)

/-- CGL's conductor-sensitive far-left Euler budget. -/
theorem cglLemma62_tailEulerConductorBudget_le_conductorQuotient_power
    (B : CGLLemma62InducedCharacter) (d : CGLLemma62TailContourDepth) :
    cglLemma62TailEulerConductorBudget B d ≤
      ((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) ^
        (2 * (d.value : ℝ) + 2) := by
  have hquotient_pos : 0 < B.ambient.value / B.primitive.modulus.value :=
    Nat.div_pos (Nat.le_of_dvd B.ambient.positive B.conductor_dvd_ambient)
      B.primitive.modulus.positive
  have hprod_nat := cglLemma62_tailEulerOuterPrimeSupport_product_dvd_conductorQuotient B
  have hprod_nat_le : ∏ p ∈ cglLemma62TailEulerOuterPrimeSupport B, p ≤
      B.ambient.value / B.primitive.modulus.value :=
    Nat.le_of_dvd hquotient_pos hprod_nat
  have hprod : (∏ p ∈ cglLemma62TailEulerOuterPrimeSupport B, (p : ℝ)) ≤
      ((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast hprod_nat_le
  unfold cglLemma62TailEulerConductorBudget
  rw [Real.finsetProd_rpow]
  · exact Real.rpow_le_rpow (by positivity) hprod (by positivity)
  · intro p hp
    positivity

end

end RHTower
