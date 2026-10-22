import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonFloquetNormalForm

/-!
# An eigen-clock in a weak static potential keeps exact time

For a weak static real potential the powers of the monodromy are bounded above and below by the same
constant `K = √((1+b)/(1−b))`. Along an eigen-solution the stroboscopic growth is *exactly* geometric
with ratio `|k|`, so `|k|ⁿ` is confined to `[1/K, K]` for every `n` — which forces `|k| = 1`.

The energy of such a solution is therefore not merely trapped in a band: it returns to its initial
value exactly, at every period. A clock that repeats itself stroboscopically in a weak static
potential keeps exact time.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A nonnegative real whose powers stay in `[1/c, c]` is one. -/
theorem eq_one_of_pow_mem_Icc {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c)
    (hub : ∀ n : ℕ, x ^ n ≤ c) (hlb : ∀ n : ℕ, 1 / c ≤ x ^ n) : x = 1 := by
  rcases lt_trichotomy x 1 with hlt | heq | hgt
  · exfalso
    have htend := tendsto_pow_atTop_nhds_zero_of_lt_one hx hlt
    have hzero : (1 : ℝ) / c ≤ 0 := ge_of_tendsto htend (Eventually.of_forall hlb)
    have hpos : (0 : ℝ) < 1 / c := by positivity
    linarith
  · exact heq
  · exfalso
    obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop c).exists
    exact absurd (hub n) (not_le.mpr hn)

section EigenClock

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b T : ℝ}

/-- **A Floquet multiplier attained in a weak static real potential lies on the unit circle.** -/
theorem norm_floquet_multiplier_eq_one_of_small_potential (hb0 : 0 ≤ b) (hb1 : b < 1) (hW : ‖W₀‖ ≤ b)
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W₀ x) y : ℂ) = inner ℂ x (W₀ y))
    (hWb : ∀ r : ℝ, ‖(fun _ : ℝ => W₀) r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => (fun _ : ℝ => W₀) r x)
    {k : ℂ} (g h : Lp ℂ 2 (volume : Measure E)) (hv : kgPair E (g, h) ≠ 0)
    (heig : kgMonodromy (fun _ : ℝ => W₀) b hb0 hWb hWs T (kgPair E (g, h))
      = k • kgPair E (g, h)) :
    ‖k‖ = 1 := by
  have hb1' : (0 : ℝ) < 1 - b := by linarith
  have hK : 0 < Real.sqrt ((1 + b) / (1 - b)) := Real.sqrt_pos.mpr (by positivity)
  have hP : 0 < ‖kgPair E (g, h)‖ := norm_pos_iff.mpr hv
  have hexact : ∀ n : ℕ, ‖kgFieldStateT (fun _ : ℝ => W₀) g h ((n : ℝ) * T)‖
      = ‖k‖ ^ n * ‖kgPair E (g, h)‖ := fun n =>
    norm_kgFieldStateT_eigen hb0 hWb hWs (periodic_const W₀ T) g h heig n
  have hub : ∀ n : ℕ, ‖k‖ ^ n ≤ Real.sqrt ((1 + b) / (1 - b)) := by
    intro n
    have hstate : kgFieldStateT (fun _ : ℝ => W₀) g h ((n : ℝ) * T)
        = (kgMonodromy (fun _ : ℝ => W₀) b hb0 hWb hWs T ^ n) (kgPair E (g, h)) :=
      kgFieldStateT_monodromy_pow hb0 hWb hWs (periodic_const W₀ T) g h n
    have hup : ‖kgFieldStateT (fun _ : ℝ => W₀) g h ((n : ℝ) * T)‖
        ≤ Real.sqrt ((1 + b) / (1 - b)) * ‖kgPair E (g, h)‖ := by
      rw [hstate]
      exact (kgMonodromy (fun _ : ℝ => W₀) b hb0 hWb hWs T ^ n).le_of_opNorm_le
        (norm_kgMonodromy_pow_le_of_small (T := T) hb0 hb1 hW hsa hWb hWs n) _
    rw [hexact n] at hup
    exact le_of_mul_le_mul_right hup hP
  have hlb : ∀ n : ℕ, 1 / Real.sqrt ((1 + b) / (1 - b)) ≤ ‖k‖ ^ n := by
    intro n
    have hlo := norm_kgFieldStateT_ge_of_small_potential (T := T) hb0 hb1 hW hsa hWb hWs g h n
    rw [hexact n] at hlo
    have h1 : 1 / Real.sqrt ((1 + b) / (1 - b)) * ‖kgPair E (g, h)‖
        ≤ ‖k‖ ^ n * ‖kgPair E (g, h)‖ := by
      rw [one_div, inv_mul_eq_div]
      exact hlo
    exact le_of_mul_le_mul_right h1 hP
  exact eq_one_of_pow_mem_Icc (norm_nonneg k) hK hub hlb

/-- **An eigen-clock in a weak static real potential keeps exact time**: its energy returns to its
initial value at every period, not merely to a band around it. -/
theorem kgFieldEnergy_eigen_conserved_of_small_potential (hb0 : 0 ≤ b) (hb1 : b < 1) (hW : ‖W₀‖ ≤ b)
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W₀ x) y : ℂ) = inner ℂ x (W₀ y))
    (hWb : ∀ r : ℝ, ‖(fun _ : ℝ => W₀) r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => (fun _ : ℝ => W₀) r x)
    {k : ℂ} (g h : Lp ℂ 2 (volume : Measure E)) (hv : kgPair E (g, h) ≠ 0)
    (heig : kgMonodromy (fun _ : ℝ => W₀) b hb0 hWb hWs T (kgPair E (g, h))
      = k • kgPair E (g, h)) (n : ℕ) :
    ‖kgFieldGradT (fun _ : ℝ => W₀) g h ((n : ℝ) * T)‖ ^ (2 : ℕ)
        + ‖kgFieldVelT (fun _ : ℝ => W₀) g h ((n : ℝ) * T)‖ ^ (2 : ℕ)
      = ‖g‖ ^ (2 : ℕ) + ‖h‖ ^ (2 : ℕ) := by
  have hone : ‖k‖ = 1 :=
    norm_floquet_multiplier_eq_one_of_small_potential hb0 hb1 hW hsa hWb hWs g h hv heig
  rw [kgFieldEnergyT_eigen hb0 hWb hWs (periodic_const W₀ T) g h heig n, hone]
  simp

/-- The same, in the autonomous register. -/
theorem kgFieldEnergy_eigen_conserved (hb0 : 0 ≤ b) (hb1 : b < 1) (hW : ‖W₀‖ ≤ b)
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W₀ x) y : ℂ) = inner ℂ x (W₀ y))
    (hWb : ∀ r : ℝ, ‖(fun _ : ℝ => W₀) r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => (fun _ : ℝ => W₀) r x)
    {k : ℂ} (g h : Lp ℂ 2 (volume : Measure E)) (hv : kgPair E (g, h) ≠ 0)
    (heig : kgMonodromy (fun _ : ℝ => W₀) b hb0 hWb hWs T (kgPair E (g, h))
      = k • kgPair E (g, h)) (n : ℕ) :
    ‖kgFieldGrad W₀ g h ((n : ℝ) * T)‖ ^ (2 : ℕ) + ‖kgFieldVel W₀ g h ((n : ℝ) * T)‖ ^ (2 : ℕ)
      = ‖g‖ ^ (2 : ℕ) + ‖h‖ ^ (2 : ℕ) := by
  have hmain := kgFieldEnergy_eigen_conserved_of_small_potential hb0 hb1 hW hsa hWb hWs g h hv
    heig n
  rwa [kgFieldGradT_const, kgFieldVelT_const] at hmain

end EigenClock

end GaloisForLFunctions.HTGeometry
