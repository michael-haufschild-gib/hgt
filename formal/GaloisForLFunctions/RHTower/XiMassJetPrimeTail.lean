import GaloisForLFunctions.RHTower.XiMassCausticFarField
import GaloisForLFunctions.RHTower.XiMassShellExteriorTail

/-!
# The jet-modified prime tail

The exterior tail estimate depends on the mass profile only through a pointwise envelope
`‖F(h)‖ ≤ B·e^{-a√(h²−u²)}` on the cone.  Stating it that way makes it reusable for the jet-modified
profile: the arithmetic — one von Mangoldt weight, one prime-log power series — is unchanged, and
the whole content of the jet is the size of `B`.
-/

open Complex Filter Finset Set

namespace RHTower

noncomputable section

/-- The jet-modified centred prime atom. -/
def xiMassJetPrimeAtom (a : ℝ) (τ : ℂ) (n : ℕ) (p : ℕ) : ℂ :=
  LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (1 / 2 : ℂ) p
    * xiMassJetIterate a τ n ((Real.log p : ℝ) : ℂ)

/-- **The pointwise atom majorant from an envelope.** -/
theorem norm_xiMassJetPrimeAtom_le {a sigma kappa u B : ℝ} {n : ℕ} {p : ℕ}
    (ha : 1 / 2 < a) (hkappa : 1 < kappa) (hu : 0 < u) (hB : 0 ≤ B) (hp : p.Prime)
    (hcone : Real.exp (kappa * u) < (p : ℝ))
    (henv : ‖xiMassJetIterate a ((sigma : ℂ) + (u : ℂ) * Complex.I) n ((Real.log p : ℝ) : ℂ)‖
      ≤ B * Real.exp (-(a * Real.sqrt ((Real.log p) ^ 2 - u ^ 2)))) :
    ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) n p‖
      ≤ B * Real.exp (-(xiMassBesselConeExponent a kappa * u))
          * Real.exp ((a - 1 / 2) * (kappa * u))
        * (Real.log p * (p : ℝ) ^ (-(1 + (a - 1 / 2)))) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  set h : ℝ := Real.log p with hh
  have hhpos : 0 < h := Real.log_pos hp1
  have hcone' : kappa * u ≤ h := by
    have hlog := Real.log_lt_log (Real.exp_pos (kappa * u)) hcone
    rw [Real.log_exp] at hlog
    linarith
  have hnorm : ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) n p‖
      = (Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ)))
        * ‖xiMassJetIterate a ((sigma : ℂ) + (u : ℂ) * Complex.I) n ((h : ℝ) : ℂ)‖ := by
    rw [xiMassJetPrimeAtom, norm_mul, norm_lseriesTerm_vonMangoldt_prime hp]
  have hweight0 : (0 : ℝ) ≤ Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (Real.log_nonneg hp1.le) (Real.rpow_pos_of_pos hp0 _).le
  have hstep : ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) n p‖
      ≤ (Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ)))
        * (B * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))) := by
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left henv hweight0
  refine hstep.trans ?_
  have hexpo := xiMassBessel_exterior_exponent_le (a := a) (kappa := kappa) (u := u) (h := h)
    ha hkappa hu.le hcone'
  have hhalf : (p : ℝ) ^ (-(1 / 2 : ℝ)) = Real.exp (-(h / 2)) := by
    rw [Real.rpow_def_of_pos hp0, ← hh]
    congr 1
    ring
  have hpow : (p : ℝ) ^ (-(1 + (a - 1 / 2))) = Real.exp (-((1 + (a - 1 / 2)) * h)) := by
    rw [Real.rpow_def_of_pos hp0, ← hh]
    congr 1
    ring
  rw [hhalf, hpow]
  have hexpprod : Real.exp (-(h / 2)) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))
      ≤ Real.exp (-(xiMassBesselConeExponent a kappa * u))
        * Real.exp ((a - 1 / 2) * (kappa * u)) * Real.exp (-((1 + (a - 1 / 2)) * h)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg hp1.le
  calc Real.log p * Real.exp (-(h / 2)) * (B * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))))
      = B * (Real.log p * (Real.exp (-(h / 2))
        * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))))) := by ring
    _ ≤ B * (Real.log p * (Real.exp (-(xiMassBesselConeExponent a kappa * u))
          * Real.exp ((a - 1 / 2) * (kappa * u)) * Real.exp (-((1 + (a - 1 / 2)) * h)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexpprod hlogp) hB
    _ = B * Real.exp (-(xiMassBesselConeExponent a kappa * u))
          * Real.exp ((a - 1 / 2) * (kappa * u))
        * (Real.log p * Real.exp (-((1 + (a - 1 / 2)) * h))) := by ring

/-- **The jet-modified exterior prime tail from an envelope.** -/
theorem sum_norm_xiMassJetPrimeAtom_le {a sigma kappa u B : ℝ} {n : ℕ}
    (ha : 1 / 2 < a) (hkappa : 1 < kappa) (hu : 0 < u) (hB : 0 ≤ B)
    (henv : ∀ h : ℝ, kappa * u ≤ h →
      ‖xiMassJetIterate a ((sigma : ℂ) + (u : ℂ) * Complex.I) n ((h : ℝ) : ℂ)‖
        ≤ B * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))) (M : ℕ) :
    ∑ p ∈ (Nat.primesBelow (M + 1)).filter (fun p : ℕ => Real.exp (kappa * u) < (p : ℝ)),
        ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) n p‖
      ≤ B * ((2 : ℝ) ^ (a - 1 / 2) * primeLogRpowTailConstant (a - 1 / 2))
        * Real.exp (-(xiMassBesselConeExponent a kappa * u)) := by
  classical
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hδ : (0 : ℝ) < a - 1 / 2 := by linarith
  have hA0 : (0 : ℝ) ≤ B * Real.exp (-(xiMassBesselConeExponent a kappa * u))
      * Real.exp ((a - 1 / 2) * (kappa * u)) := by positivity
  have hterm : ∀ p ∈ (Nat.primesBelow (M + 1)).filter
      (fun p : ℕ => Real.exp (kappa * u) < (p : ℝ)),
      ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) n p‖
        ≤ (B * Real.exp (-(xiMassBesselConeExponent a kappa * u))
            * Real.exp ((a - 1 / 2) * (kappa * u)))
          * (Real.log p * (p : ℝ) ^ (-(1 + (a - 1 / 2)))) := by
    intro p hp
    obtain ⟨hpmem, hgt⟩ := Finset.mem_filter.mp hp
    have hpp := (Nat.mem_primesBelow.mp hpmem).2
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.one_lt
    have hcone' : kappa * u ≤ Real.log p := by
      have hlog := Real.log_lt_log (Real.exp_pos (kappa * u)) hgt
      rw [Real.log_exp] at hlog
      linarith
    exact norm_xiMassJetPrimeAtom_le ha hkappa hu hB hpp hgt (henv (Real.log p) hcone')
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hX : (1 : ℝ) ≤ Real.exp (kappa * u) := Real.one_le_exp (by positivity)
  have htail := sum_prime_log_rpow_tail_le (δ := a - 1 / 2) (X := Real.exp (kappa * u)) hδ hX M
  have hstep := mul_le_mul_of_nonneg_left htail hA0
  refine hstep.trans (le_of_eq ?_)
  have hXpow : (Real.exp (kappa * u)) ^ (-(a - 1 / 2))
      = Real.exp (-((a - 1 / 2) * (kappa * u))) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  rw [hXpow]
  have hcancel : Real.exp ((a - 1 / 2) * (kappa * u)) * Real.exp (-((a - 1 / 2) * (kappa * u)))
      = 1 := by
    rw [← Real.exp_add]
    simp
  calc (B * Real.exp (-(xiMassBesselConeExponent a kappa * u))
        * Real.exp ((a - 1 / 2) * (kappa * u)))
      * ((2 : ℝ) ^ (a - 1 / 2) * primeLogRpowTailConstant (a - 1 / 2)
        * Real.exp (-((a - 1 / 2) * (kappa * u))))
      = (B * ((2 : ℝ) ^ (a - 1 / 2) * primeLogRpowTailConstant (a - 1 / 2))
          * Real.exp (-(xiMassBesselConeExponent a kappa * u)))
        * (Real.exp ((a - 1 / 2) * (kappa * u))
          * Real.exp (-((a - 1 / 2) * (kappa * u)))) := by ring
    _ = B * ((2 : ℝ) ^ (a - 1 / 2) * primeLogRpowTailConstant (a - 1 / 2))
        * Real.exp (-(xiMassBesselConeExponent a kappa * u)) := by rw [hcancel, mul_one]

/-- **The jet-modified exterior prime tail over a sub-range.**  Only the primes actually summed need
the envelope; the majorant is nonnegative, so the range may be widened to the full cone tail. -/
theorem sum_norm_xiMassJetPrimeAtom_subset_le {a sigma kappa u B : ℝ} {n M : ℕ}
    (ha : 1 / 2 < a) (hkappa : 1 < kappa) (hu : 0 < u) (hB : 0 ≤ B) (T : Finset ℕ)
    (hT : T ⊆ (Nat.primesBelow (M + 1)).filter (fun p : ℕ => Real.exp (kappa * u) < (p : ℝ)))
    (henv : ∀ p ∈ T,
      ‖xiMassJetIterate a ((sigma : ℂ) + (u : ℂ) * Complex.I) n ((Real.log p : ℝ) : ℂ)‖
        ≤ B * Real.exp (-(a * Real.sqrt ((Real.log p) ^ 2 - u ^ 2)))) :
    ∑ p ∈ T, ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) n p‖
      ≤ B * ((2 : ℝ) ^ (a - 1 / 2) * primeLogRpowTailConstant (a - 1 / 2))
        * Real.exp (-(xiMassBesselConeExponent a kappa * u)) := by
  classical
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hδ : (0 : ℝ) < a - 1 / 2 := by linarith
  set A : ℝ := B * Real.exp (-(xiMassBesselConeExponent a kappa * u))
      * Real.exp ((a - 1 / 2) * (kappa * u)) with hAdef
  have hA0 : (0 : ℝ) ≤ A := by rw [hAdef]; positivity
  have hterm : ∀ p ∈ T,
      ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) n p‖
        ≤ A * (Real.log p * (p : ℝ) ^ (-(1 + (a - 1 / 2)))) := by
    intro p hp
    obtain ⟨hpmem, hgt⟩ := Finset.mem_filter.mp (hT hp)
    exact norm_xiMassJetPrimeAtom_le ha hkappa hu hB (Nat.mem_primesBelow.mp hpmem).2 hgt
      (henv p hp)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hwiden : ∑ p ∈ T, A * (Real.log p * (p : ℝ) ^ (-(1 + (a - 1 / 2))))
      ≤ ∑ p ∈ (Nat.primesBelow (M + 1)).filter (fun p : ℕ => Real.exp (kappa * u) < (p : ℝ)),
          A * (Real.log p * (p : ℝ) ^ (-(1 + (a - 1 / 2)))) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hT (fun p hpmem _ => ?_)
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      have := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hpmem).1).2
      exact_mod_cast this.one_lt.le
    have hlog : (0 : ℝ) ≤ Real.log p := Real.log_nonneg hp1
    have hpow : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 + (a - 1 / 2))) :=
      Real.rpow_nonneg (by linarith) _
    positivity
  refine le_trans hwiden ?_
  rw [← Finset.mul_sum]
  have hX : (1 : ℝ) ≤ Real.exp (kappa * u) := Real.one_le_exp (by positivity)
  have htail := sum_prime_log_rpow_tail_le (δ := a - 1 / 2) (X := Real.exp (kappa * u)) hδ hX M
  have hstep := mul_le_mul_of_nonneg_left htail hA0
  refine hstep.trans (le_of_eq ?_)
  have hXpow : (Real.exp (kappa * u)) ^ (-(a - 1 / 2))
      = Real.exp (-((a - 1 / 2) * (kappa * u))) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  rw [hXpow, hAdef]
  have hcancel : Real.exp ((a - 1 / 2) * (kappa * u)) * Real.exp (-((a - 1 / 2) * (kappa * u)))
      = 1 := by
    rw [← Real.exp_add]
    simp
  calc (B * Real.exp (-(xiMassBesselConeExponent a kappa * u))
        * Real.exp ((a - 1 / 2) * (kappa * u)))
      * ((2 : ℝ) ^ (a - 1 / 2) * primeLogRpowTailConstant (a - 1 / 2)
        * Real.exp (-((a - 1 / 2) * (kappa * u))))
      = (B * ((2 : ℝ) ^ (a - 1 / 2) * primeLogRpowTailConstant (a - 1 / 2))
          * Real.exp (-(xiMassBesselConeExponent a kappa * u)))
        * (Real.exp ((a - 1 / 2) * (kappa * u))
          * Real.exp (-((a - 1 / 2) * (kappa * u)))) := by ring
    _ = B * ((2 : ℝ) ^ (a - 1 / 2) * primeLogRpowTailConstant (a - 1 / 2))
        * Real.exp (-(xiMassBesselConeExponent a kappa * u)) := by rw [hcancel, mul_one]

end

end RHTower
