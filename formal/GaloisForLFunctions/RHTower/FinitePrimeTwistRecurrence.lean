import GaloisForLFunctions.RHTower.CCMPrimePoleFiniteCoherence

/-!
# A fixed finite prime packet has no twist gap

Every finite family of prime logarithms is a finite torus of frequencies, and a finite torus returns.
Simultaneous Dirichlet approximation produces, for each resolution `Q`, one integer clock `n` with

```text
Q ≤ n ≤ Q(Q²+1)^d,      max_i ‖p_i^{in} − 1‖ ≤ 2π/Q,
```

hence a twist energy bounded by half the squared tolerance times the harmonic mass of the packet:

```text
∑_i (1 − cos(n log p_i))/p_i ≤ (2π/Q)²/2 · ∑_i 1/p_i.
```

Consequently no statement about a fixed finite prime packet — at any fixed tolerance and any fixed jet
order, since differentiating a prime clock only multiplies its recurring phase by a fixed power of
`log p` — can force a positive twist gap at unbounded frequencies.  The recurrence clock is at most
`Q(Q²+1)^d`, so at a fixed tolerance the alignment already fits inside a polynomial horizon `x^B` unless
the number of active prime coordinates grows: aperture growth, not algebraic independence, is the
missing datum.
-/

open Finset

namespace RHTower

noncomputable section

/-- The real part of a unit phase is its cosine. -/
theorem re_exp_I_mul_ofReal (x : ℝ) :
    (Complex.exp (Complex.I * (x : ℂ))).re = Real.cos x := by
  rw [mul_comm, Complex.exp_ofReal_mul_I_re]

/-- A phase within `e` of an integral period costs at most `e²/2` in its cosine. -/
theorem one_sub_cos_le_sq_div_two {x e : ℝ} (r : ℤ) (he : 0 ≤ e)
    (hphase : |x - 2 * Real.pi * r| ≤ e) : 1 - Real.cos x ≤ e ^ (2 : ℕ) / 2 := by
  have h := one_sub_sq_phaseError_div_two_le_re_exp_I_mul_real x e r he hphase
  rw [re_exp_I_mul_ofReal] at h
  linarith

/-- The prime-clock twist energy carried by a finite prime packet. -/
def finitePrimeTwistEnergy {d : ℕ} (p : Fin d → ℕ) (t : ℝ) : ℝ :=
  ∑ i, (1 - Real.cos (t * Real.log (p i))) / (p i : ℝ)

/-- The harmonic mass of a finite prime packet. -/
def finitePrimeMass {d : ℕ} (p : Fin d → ℕ) : ℝ := ∑ i, 1 / (p i : ℝ)

theorem finitePrimeMass_nonneg {d : ℕ} (p : Fin d → ℕ) : 0 ≤ finitePrimeMass p :=
  Finset.sum_nonneg fun i _ => by positivity

/-- **(Z20) A simultaneous phase alignment collapses the twist energy.** -/
theorem finitePrimeTwistEnergy_le_of_phase {d : ℕ} (p : Fin d → ℕ) {t e : ℝ} (he : 0 ≤ e)
    (r : Fin d → ℤ) (hphase : ∀ i, |t * Real.log (p i) - 2 * Real.pi * r i| ≤ e) :
    finitePrimeTwistEnergy p t ≤ e ^ (2 : ℕ) / 2 * finitePrimeMass p := by
  rw [finitePrimeTwistEnergy, finitePrimeMass, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hcos := one_sub_cos_le_sq_div_two (r i) he (hphase i)
  have hp : (0 : ℝ) ≤ (p i : ℝ) := Nat.cast_nonneg _
  rcases eq_or_lt_of_le hp with hzero | hpos
  · rw [← hzero]
    simp
  · rw [div_le_iff₀ hpos]
    have hkey : e ^ (2 : ℕ) / 2 * (1 / (p i : ℝ)) * (p i : ℝ) = e ^ (2 : ℕ) / 2 := by
      field_simp
    rw [hkey]
    exact hcos

/-- **(Z19c) A cofinal alignment clock for a finite prime packet.**  One integer clock beyond `Q`, of
size at most `Q(Q²+1)^d`, brings every prime phase within `2π/Q` of the identity. -/
theorem exists_clock_norm_primeChar_sub_one_le {d Q : ℕ} (hQ : 0 < Q) (p : Fin d → ℕ) :
    ∃ n : ℕ, Q ≤ n ∧ n ≤ Q * (Q ^ (2 : ℕ) + 1) ^ d ∧
      ∀ i, ‖Complex.exp (Complex.I * (((n : ℝ) * Real.log (p i) : ℝ) : ℂ)) - 1‖
        ≤ 2 * Real.pi / (Q : ℝ) := by
  obtain ⟨n, hnQ, hn, r, hr⟩ :=
    exists_fin_simultaneous_two_pi_phase_approximation_annular_quantitative
      (Q := Q) hQ (fun i => Real.log (p i))
  exact ⟨n, hnQ, hn, fun i =>
    le_trans (norm_exp_I_mul_real_sub_one_le_mod_two_pi ((n : ℝ) * Real.log (p i)) (r i)) (hr i)⟩

/-- **(Z19)+(Z20) The quantitative aperture obstruction.**  At resolution `Q` a clock of size at most
`Q(Q²+1)^d` already drives the twist energy of the packet below `(2π/Q)²/2` times its harmonic mass. -/
theorem exists_clock_finitePrimeTwistEnergy_le {d Q : ℕ} (hQ : 0 < Q) (p : Fin d → ℕ) :
    ∃ n : ℕ, Q ≤ n ∧ n ≤ Q * (Q ^ (2 : ℕ) + 1) ^ d ∧
      finitePrimeTwistEnergy p (n : ℝ)
        ≤ (2 * Real.pi / (Q : ℝ)) ^ (2 : ℕ) / 2 * finitePrimeMass p := by
  obtain ⟨n, hnQ, hn, r, hr⟩ :=
    exists_fin_simultaneous_two_pi_phase_approximation_annular_quantitative
      (Q := Q) hQ (fun i => Real.log (p i))
  have he : (0 : ℝ) ≤ 2 * Real.pi / (Q : ℝ) := by positivity
  exact ⟨n, hnQ, hn, finitePrimeTwistEnergy_le_of_phase p he r hr⟩

/-- **(Z19d) The alignment fits inside a polynomial horizon.**  Whenever the recurrence clock bound of
the packet is smaller than the horizon, a near-complete alignment occurs inside `[Q, x^B]`. -/
theorem exists_clock_in_horizon {d Q : ℕ} (hQ : 0 < Q) (p : Fin d → ℕ) {x B : ℝ}
    (hfit : ((Q * (Q ^ (2 : ℕ) + 1) ^ d : ℕ) : ℝ) ≤ x ^ B) :
    ∃ t : ℝ, (Q : ℝ) ≤ t ∧ t ≤ x ^ B ∧
      finitePrimeTwistEnergy p t ≤ (2 * Real.pi / (Q : ℝ)) ^ (2 : ℕ) / 2 * finitePrimeMass p := by
  obtain ⟨n, hnQ, hn, hE⟩ := exists_clock_finitePrimeTwistEnergy_le hQ p
  refine ⟨(n : ℝ), by exact_mod_cast hnQ, ?_, hE⟩
  exact le_trans (by exact_mod_cast hn) hfit

/-- **(Z19) No fixed finite prime packet has a twist gap.**  Beyond every frequency threshold and below
every tolerance there is a clock at which the packet is fully recurrent. -/
theorem exists_clock_finitePrimeTwistEnergy_lt {d : ℕ} (p : Fin d → ℕ) {ε T₀ : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, T₀ ≤ (n : ℝ) ∧ finitePrimeTwistEnergy p (n : ℝ) < ε := by
  have hmass := finitePrimeMass_nonneg p
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = max (max T₀ 1)
      ((2 * Real.pi) ^ (2 : ℕ) * finitePrimeMass p / (2 * ε) + 1) := ⟨_, rfl⟩
  obtain ⟨Q, hQgt⟩ := exists_nat_gt R
  have hleft : max T₀ 1 ≤ R := by rw [hR]; exact le_max_left _ _
  have hright : (2 * Real.pi) ^ (2 : ℕ) * finitePrimeMass p / (2 * ε) + 1 ≤ R := by
    rw [hR]; exact le_max_right _ _
  have hT₀R : T₀ ≤ R := le_trans (le_max_left T₀ 1) hleft
  have hR1 : (1 : ℝ) ≤ R := le_trans (le_max_right T₀ 1) hleft
  have hQ1 : (1 : ℝ) < (Q : ℝ) := lt_of_le_of_lt hR1 hQgt
  have hQpos : 0 < Q := by exact_mod_cast lt_trans zero_lt_one hQ1
  have hQR : (0 : ℝ) < (Q : ℝ) := by linarith
  obtain ⟨n, hnQ, _, hE⟩ := exists_clock_finitePrimeTwistEnergy_le hQpos p
  have hQn : (Q : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnQ
  refine ⟨n, by linarith, lt_of_le_of_lt hE ?_⟩
  have hbig : (2 * Real.pi) ^ (2 : ℕ) * finitePrimeMass p / (2 * ε) < (Q : ℝ) := by linarith
  have hsq : (Q : ℝ) ≤ (Q : ℝ) ^ (2 : ℕ) := by nlinarith
  have hkey : (2 * Real.pi) ^ (2 : ℕ) * finitePrimeMass p < 2 * ε * (Q : ℝ) ^ (2 : ℕ) := by
    have h := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * ε)).1 hbig
    nlinarith
  have hexpand : (2 * Real.pi / (Q : ℝ)) ^ (2 : ℕ) / 2 * finitePrimeMass p
      = (2 * Real.pi) ^ (2 : ℕ) * finitePrimeMass p / (2 * (Q : ℝ) ^ (2 : ℕ)) := by
    field_simp
  rw [hexpand, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (Q : ℝ) ^ (2 : ℕ))]
  nlinarith

end

end RHTower
