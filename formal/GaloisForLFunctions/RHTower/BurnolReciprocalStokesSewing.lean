import GaloisForLFunctions.RHTower.BurnolAllPrimeCompletionWall

/-!
# Reciprocal-Stokes sewing of the all-prime Burnol source

The normalized reciprocal endpoint current `ν_p = (p δ_p - δ_1)/(p-1)` has Mellin multiplier
`m_p(w) = (p^{1-w} - 1)/(p-1)`.  Sewing it onto the prime window multiplies the window factor by
`m_p`, giving the reflection-invariant sewn factor

`S_p(w) = (p^w - 1)(p^{1-w} - 1)/(p - 1)`,

which is bounded by `6` on the closed critical strip.  Hence the sewn conormal
`Y_{ρ,p} = m_p(ρ) U_{ρ,p}` is square summable at every point of the open strip, while unsewing —
division by the null sequence `m_p(ρ)` — has exactly the inverse-completion domain wall
`Re ρ ≤ 1/2`.

The card's false route is also settled: the unique prime-log Green potential `Q_p` producing the
boundary `A_p = 1/(p log p)` is itself not square summable, so `A` is a closure-only class and no
ordinary closed-range statement is available.
-/

open Complex Real Filter Topology

noncomputable section

namespace RHTower

/-! ## The reciprocal endpoint multiplier -/

/-- Mellin multiplier of the normalized reciprocal endpoint current. -/
def burnolReciprocalEndpointMultiplier (p : ℕ) (w : ℂ) : ℂ :=
  ((p : ℂ) ^ (1 - w) - 1) / ((p : ℂ) - 1)

/-- The reflection-invariant sewn window factor. -/
def burnolSewnWindowFactor (p : ℕ) (w : ℂ) : ℂ :=
  ((p : ℂ) ^ w - 1) * ((p : ℂ) ^ (1 - w) - 1) / ((p : ℂ) - 1)

theorem burnolSewnWindowFactor_reflection (p : ℕ) (w : ℂ) :
    burnolSewnWindowFactor p (1 - w) = burnolSewnWindowFactor p w := by
  rw [burnolSewnWindowFactor, burnolSewnWindowFactor, show (1 : ℂ) - (1 - w) = w by ring]
  ring

theorem burnolSewnWindowFactor_eq_mul {p : ℕ} (w : ℂ) :
    burnolSewnWindowFactor p w =
      ((p : ℂ) ^ w - 1) * burnolReciprocalEndpointMultiplier p w := by
  rw [burnolSewnWindowFactor, burnolReciprocalEndpointMultiplier]
  ring

/-- **The sewn factor is uniformly bounded on the closed critical strip.** -/
theorem norm_burnolSewnWindowFactor_le {p : ℕ} (hp : 2 ≤ p) {w : ℂ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) :
    ‖burnolSewnWindowFactor p w‖ ≤ 6 := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1 : (1 : ℝ) < (p : ℝ) := by linarith
  have hcast : ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) := by push_cast; ring
  have hnorm : ‖(p : ℂ) ^ w‖ = (p : ℝ) ^ w.re := by
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hppos]
  have hnorm' : ‖(p : ℂ) ^ (1 - w)‖ = (p : ℝ) ^ (1 - w.re) := by
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hppos]
    congr 1
  have hle1 : (p : ℝ) ^ w.re ≤ (p : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hp1.le hhi
    rwa [Real.rpow_one] at this
  have hle2 : (p : ℝ) ^ (1 - w.re) ≤ (p : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith : (1 : ℝ) - w.re ≤ 1)
    rwa [Real.rpow_one] at this
  have hden : ‖((p : ℂ) - 1)‖ = (p : ℝ) - 1 := by
    rw [hcast, show (((p : ℕ) : ℝ) : ℂ) - 1 = (((p : ℝ) - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hpne : ((p : ℕ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hmul : ((p : ℂ)) ^ w * ((p : ℂ)) ^ (1 - w) = (p : ℂ) := by
    rw [← Complex.cpow_add _ _ hpne]
    simp
  have hexpand : ((p : ℂ) ^ w - 1) * ((p : ℂ) ^ (1 - w) - 1) =
      ((p : ℂ) + 1) - ((p : ℂ) ^ w + (p : ℂ) ^ (1 - w)) := by
    linear_combination hmul
  have hA : (1 : ℝ) ≤ (p : ℝ) ^ w.re := Real.one_le_rpow hp1.le hlo
  have hB : (1 : ℝ) ≤ (p : ℝ) ^ (1 - w.re) := Real.one_le_rpow hp1.le (by linarith)
  have hmulr : (p : ℝ) ^ w.re * (p : ℝ) ^ (1 - w.re) = (p : ℝ) := by
    rw [← Real.rpow_add hppos]
    norm_num
  have hsum : (p : ℝ) ^ w.re + (p : ℝ) ^ (1 - w.re) ≤ (p : ℝ) + 1 := by
    nlinarith [hA, hB, hmulr]
  have hpone : ‖((p : ℂ) + 1)‖ = (p : ℝ) + 1 := by
    rw [hcast, show (((p : ℕ) : ℝ) : ℂ) + 1 = (((p : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hnum : ‖((p : ℂ) ^ w - 1) * ((p : ℂ) ^ (1 - w) - 1)‖ ≤ 2 * ((p : ℝ) + 1) := by
    rw [hexpand]
    refine (norm_sub_le _ _).trans ?_
    have hpair : ‖(p : ℂ) ^ w + (p : ℂ) ^ (1 - w)‖ ≤ (p : ℝ) + 1 :=
      (norm_add_le _ _).trans (by rw [hnorm, hnorm']; exact hsum)
    rw [hpone]
    linarith
  rw [burnolSewnWindowFactor, norm_div, hden, div_le_iff₀ (by linarith)]
  linarith [hnum, hp2]

/-! ## The sewn conormal -/

/-- The reciprocal-Stokes sewn conormal `Y_{ρ,p} = m_p(ρ) U_{ρ,p}`. -/
def burnolSewnConormal (c ρ : ℂ) (p : ℕ) : ℂ :=
  burnolReciprocalEndpointMultiplier p ρ * burnolAllPrimeInverseCompletionCoefficient c ρ p

theorem burnolSewnConormal_eq {c ρ : ℂ} {p : ℕ} (hp : 2 ≤ p)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    burnolSewnConormal c ρ p =
      burnolAllPrimeInverseCompletionConstant c ρ *
        (burnolSewnWindowFactor p ρ / ((p : ℂ) * ((Real.log (p : ℝ) : ℝ) : ℂ))) := by
  rw [burnolSewnConormal, burnolAllPrimeInverseCompletionCoefficient_eq hp hρ0 hρ1,
    burnolSewnWindowFactor_eq_mul]
  ring

/-- **Unconditional square summability of the sewn conormal.** -/
theorem burnolSummable_sewnConormal_sq {c ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    Summable (fun p : Nat.Primes => ‖burnolSewnConormal c ρ (p : ℕ)‖ ^ 2) := by
  set K : ℝ := ‖burnolAllPrimeInverseCompletionConstant c ρ‖ with hK
  have hle : ∀ p : Nat.Primes, ‖burnolSewnConormal c ρ (p : ℕ)‖ ^ 2 ≤
      (36 * K ^ 2) * burnolSourceBoundary (p : ℕ) ^ 2 := by
    intro p
    have hp : 2 ≤ (p : ℕ) := p.2.two_le
    have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by
      have : (0 : ℕ) < (p : ℕ) := by omega
      exact_mod_cast this
    have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp.trans_lt' one_lt_two
    have hLpos : 0 < Real.log ((p : ℕ) : ℝ) := Real.log_pos hp1
    have hKnn : 0 ≤ K := norm_nonneg _
    have hnorm : ‖burnolSewnConormal c ρ (p : ℕ)‖ =
        K * (‖burnolSewnWindowFactor (p : ℕ) ρ‖ /
          (((p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ))) := by
      rw [burnolSewnConormal_eq hp hρ0 hρ1, norm_mul, norm_div, norm_mul, ← hK]
      congr 2
      rw [Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLpos]
    have hS : ‖burnolSewnWindowFactor (p : ℕ) ρ‖ ≤ 6 :=
      norm_burnolSewnWindowFactor_le hp hρ0.le hρ1.le
    have hbound : K * (‖burnolSewnWindowFactor (p : ℕ) ρ‖ /
        (((p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ))) ≤
        K * (6 / (((p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hS (by positivity)) hKnn
    have hnn : 0 ≤ K * (‖burnolSewnWindowFactor (p : ℕ) ρ‖ /
        (((p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ))) := by positivity
    rw [hnorm]
    refine (pow_le_pow_left₀ hnn hbound 2).trans_eq ?_
    rw [burnolSourceBoundary]
    field_simp
    ring
  exact Summable.of_nonneg_of_le (fun p => sq_nonneg _) hle
    (burnolSummable_sourceBoundary_sq.mul_left (36 * K ^ 2))

/-- **The unsewing domain wall.**  Recovering `U_ρ` from the sewn conormal is possible exactly on
the closed left half of the critical strip. -/
theorem burnolSewnConormal_unsewing_wall {c ρ : ℂ} (hc : c ≠ 0)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    Summable (fun p : Nat.Primes =>
        ‖burnolSewnConormal c ρ (p : ℕ) /
          burnolReciprocalEndpointMultiplier (p : ℕ) ρ‖ ^ 2) ↔ ρ.re ≤ 1 / 2 := by
  have hmne : ∀ p : Nat.Primes, burnolReciprocalEndpointMultiplier (p : ℕ) ρ ≠ 0 := by
    intro p
    have hp : 2 ≤ (p : ℕ) := p.2.two_le
    have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by
      have : (0 : ℕ) < (p : ℕ) := by omega
      exact_mod_cast this
    have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp.trans_lt' one_lt_two
    have hnum : ((p : ℕ) : ℂ) ^ (1 - ρ) - 1 ≠ 0 :=
      nat_cpow_sub_one_ne_zero hp (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    have hden : ((p : ℕ) : ℂ) - 1 ≠ 0 := by
      intro hz
      have : ((p : ℕ) : ℂ) = 1 := by linear_combination hz
      have hre : ((p : ℕ) : ℝ) = 1 := by exact_mod_cast congrArg Complex.re this
      linarith
    exact div_ne_zero hnum hden
  have hrewrite : (fun p : Nat.Primes =>
      ‖burnolSewnConormal c ρ (p : ℕ) /
        burnolReciprocalEndpointMultiplier (p : ℕ) ρ‖ ^ 2) =
      fun p : Nat.Primes => ‖burnolAllPrimeInverseCompletionCoefficient c ρ (p : ℕ)‖ ^ 2 := by
    funext p
    rw [burnolSewnConormal, mul_comm, mul_div_assoc, div_self (hmne p), mul_one]
  rw [hrewrite]
  exact summable_burnolAllPrimeInverseCompletionCoefficient_sq_iff hc hρ0 hρ1

/-! ## The singular potential is not square summable -/

/-- **The unique prime-log Green potential escapes `ℓ²`.**  Hence the strict boundary `A_p` is a
closure-only class and no ordinary closed-range statement is available. -/
theorem burnolNotSummable_primeLogGreenPotential_sq :
    ¬ Summable (fun p : Nat.Primes => burnolPrimeLogGreenPotential (p : ℕ) ^ 2) := by
  intro hsum
  obtain ⟨N, hN⟩ := (burnolEventually_log_pow_le_rpow (by norm_num : (0 : ℝ) < 1) 4)
    |>.exists_forall_of_atTop
  classical
  set s : Set Nat.Primes := {p : Nat.Primes | ((p : ℕ) : ℝ) < N} with hs
  have hsfin : s.Finite := by
    have himg : s ⊆ Subtype.val ⁻¹' (Set.Iio ⌈N⌉₊) := by
      intro p hp
      have hlt : ((p : ℕ) : ℝ) < N := hp
      have : ((p : ℕ) : ℝ) < (⌈N⌉₊ : ℝ) := lt_of_lt_of_le hlt (Nat.le_ceil N)
      exact_mod_cast this
    exact Set.Finite.subset
      (Set.Finite.preimage (Subtype.val_injective.injOn) (Set.finite_Iio ⌈N⌉₊)) himg
  have hsub : Summable (fun x : ↥sᶜ =>
      burnolPrimeLogGreenPotential ((x : Nat.Primes) : ℕ) ^ 2) := hsum.subtype _
  have hcomp : Summable (fun x : ↥sᶜ => 1 / (((x : Nat.Primes) : ℕ) : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun x => by positivity) ?_ hsub
    rintro ⟨p, hp⟩
    have hple : N ≤ ((p : ℕ) : ℝ) := by
      have : ¬ (((p : ℕ) : ℝ) < N) := hp
      linarith [not_lt.mp this]
    have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
    have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by
      have : (0 : ℕ) < (p : ℕ) := by omega
      exact_mod_cast this
    have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp2.trans_lt' one_lt_two
    have hLpos : 0 < Real.log ((p : ℕ) : ℝ) := Real.log_pos hp1
    have hlog4 : Real.log ((p : ℕ) : ℝ) ^ 4 ≤ ((p : ℕ) : ℝ) ^ (1 : ℝ) := hN _ hple
    rw [Real.rpow_one] at hlog4
    have hQ : burnolPrimeLogGreenPotential (p : ℕ) ^ 2 =
        (((p : ℕ) : ℝ) + 1) ^ 2 / (((p : ℕ) : ℝ) ^ 2 * Real.log ((p : ℕ) : ℝ) ^ 4) := by
      rw [burnolPrimeLogGreenPotential]
      field_simp
    rw [hQ, div_le_div_iff₀ hppos (by positivity)]
    nlinarith [hlog4, hppos, hLpos, sq_nonneg (((p : ℕ) : ℝ))]
  exact burnolNotSummable_prime_one_div ((Set.Finite.summable_compl_iff hsfin).mp hcomp)

end RHTower
