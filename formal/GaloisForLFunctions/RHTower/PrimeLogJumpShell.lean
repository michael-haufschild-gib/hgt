import GaloisForLFunctions.RHTower.PrimeLogJumpMellinLimit
import GaloisForLFunctions.RHTower.PrimeLogJumpGradeLaw

/-!
# The two-prime source shell

The coefficient exposed by dividing the centered theta translation anomaly by the Xi conormal is the
interval window `h_n = n^{-1/2} 1_{[-log n/2, log n/2]}`, so for two distinct primes `p < q` the
difference `√q h_q − √p h_p` is the indicator of the symmetric annulus with endpoints

```text
A = log p / 2,      B = log q / 2.
```

Unique factorization makes `log p` and `log q` integrally independent, hence `A / B` irrational:
the two-frequency phase clock exists, and with it the two boundary channels of the jump packet.
-/

namespace GaloisForLFunctions.RHTower

open Complex Filter
open scoped Topology

/-- The source-normal shell endpoint attached to a prime. -/
noncomputable def primeShellEnd (p : ℕ) : ℝ := Real.log p / 2

theorem log_pos_of_prime {p : ℕ} (hp : p.Prime) : 0 < Real.log p :=
  Real.log_pos (by exact_mod_cast hp.one_lt)

theorem primeShellEnd_pos {p : ℕ} (hp : p.Prime) : 0 < primeShellEnd p := by
  rw [primeShellEnd]
  exact div_pos (log_pos_of_prime hp) (by norm_num)

theorem primeShellEnd_lt {p q : ℕ} (hp : 0 < p) (h : p < q) :
    primeShellEnd p < primeShellEnd q := by
  rw [primeShellEnd, primeShellEnd]
  have hlt : Real.log p < Real.log q := by
    refine Real.log_lt_log (by exact_mod_cast hp) ?_
    exact_mod_cast h
  linarith

/-- **The prime logarithms of two distinct primes are integrally independent.** -/
theorem linearIndependent_logPrime_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    LinearIndependent ℤ ![Real.log p, Real.log q] := by
  classical
  set v : Fin 2 → Nat.Primes := ![⟨p, hp⟩, ⟨q, hq⟩] with hv
  have hne : v 0 ≠ v 1 := by
    simp only [hv, Matrix.cons_val_zero, Matrix.cons_val_one]
    intro hcon
    exact hpq (congrArg Subtype.val hcon)
  have hinj : Function.Injective v := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij hne
    · exact absurd hij.symm hne
    · rfl
  have hcomp : (fun r : Nat.Primes => Real.log ((r : ℕ) : ℝ)) ∘ v
      = ![Real.log p, Real.log q] := by
    funext i
    fin_cases i <;> rfl
  have := logPrime_linearIndependent_int.comp v hinj
  rwa [hcomp] at this

/-- **`(4)`.**  The two shell endpoints have irrational ratio. -/
theorem irrational_primeShellEnd_ratio {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Irrational (primeShellEnd p / primeShellEnd q) := by
  have hlog : Irrational (Real.log p / Real.log q) :=
    HTGeometry.irrational_div_of_linearIndependent_pair
      (linearIndependent_logPrime_pair hp hq hpq)
  have hq0 : Real.log q ≠ 0 := ne_of_gt (log_pos_of_prime hq)
  have heq : primeShellEnd p / primeShellEnd q = Real.log p / Real.log q := by
    rw [primeShellEnd, primeShellEnd]
    field_simp
  rwa [heq]

/-- **The two-prime jump frame.**  For a two-prime source shell the two source-defined clocks
realise the two boundary phase channels as first Mellin boundary traces of the jump packet, and the
two channels are desingularized by two compact BV windows with no common zero. -/
theorem primeLogJumpFrame {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    (∃ κ : ℕ → ℝ, Tendsto κ atTop atTop ∧
        ∀ s : ℂ, Tendsto (fun j => ((κ j : ℝ) : ℂ) *
            jumpMellin (primeShellEnd p) (primeShellEnd q) (κ j) s) atTop
          (𝓝 (channelA (primeShellEnd p) (primeShellEnd q) s)))
      ∧ (∃ κ : ℕ → ℝ, Tendsto κ atTop atTop ∧
        ∀ s : ℂ, Tendsto (fun j => ((κ j : ℝ) : ℂ) *
            jumpMellin (primeShellEnd p) (primeShellEnd q) (κ j) s) atTop
          (𝓝 (channelB (primeShellEnd p) (primeShellEnd q) s)))
      ∧ (∀ s : ℂ, s * windowMellinA (primeShellEnd p) (primeShellEnd q) s
            = channelA (primeShellEnd p) (primeShellEnd q) s
          ∧ s * windowMellinB (primeShellEnd p) (primeShellEnd q) s
            = channelB (primeShellEnd p) (primeShellEnd q) s)
      ∧ (∀ s : ℂ, windowMellinA (primeShellEnd p) (primeShellEnd q) s ≠ 0
          ∨ windowMellinB (primeShellEnd p) (primeShellEnd q) s ≠ 0) := by
  have hA : 0 < primeShellEnd p := primeShellEnd_pos hp
  have hAB : primeShellEnd p < primeShellEnd q := primeShellEnd_lt hp.pos hpq
  have hirr : Irrational (primeShellEnd p / primeShellEnd q) :=
    irrational_primeShellEnd_ratio hp hq (ne_of_lt hpq)
  obtain ⟨κA, hκA, _, _, hlimA⟩ := exists_clock_tendsto_channelA hA hAB hirr
  obtain ⟨κB, hκB, _, _, hlimB⟩ := exists_clock_tendsto_channelB hA hAB hirr
  exact ⟨⟨κA, hκA, hlimA⟩, ⟨κB, hκB, hlimB⟩,
    fun s => ⟨mul_windowMellinA hA hAB s, mul_windowMellinB hA hAB s⟩,
    fun s => no_common_zero_windowMellin hA hAB s⟩

end GaloisForLFunctions.RHTower
