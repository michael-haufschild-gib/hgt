import GaloisForLFunctions.HTGeometry.TorsionPolygonCircuitDepth

/-!
# Asymptotics of the circuit-depth cap

At Hilbert dimension `D = 2^n` with a gate alphabet of size linear in `n` and bounded dependence
degree, the depth-`cD` trace dictionary has logarithm `c Δ D log 2 + O(n²)`.  The quadratic
correction is negligible against `D`, so as soon as the torsion cap exponent exceeds
`c Δ log 2` the cap condition holds for all large `n` -- and it still holds when the torsion order
itself grows like `e^{ηD}`, provided `η + c Δ log 2` stays below the cap exponent.

Bertrand's postulate then supplies a prime of that size, so one recurrence cycle carries
exponentially many equally spaced hard interior slices.
-/

open Real Filter Topology RHTower

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Domination

/-- A quadratic is eventually dominated by any positive multiple of `2^n`. -/
theorem eventually_quadratic_lt_two_pow {θ : ℝ} (hθ : 0 < θ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, B * ((n : ℝ) ^ 2 + (n : ℝ) + 1) < θ * 2 ^ n := by
  set B' : ℝ := max B 1 with hB'def
  have hB'pos : (0 : ℝ) < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hBle : B ≤ B' := le_max_left _ _
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 / 2 ^ n) atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num)
  have hev := hlim.eventually_lt_const (show (0 : ℝ) < θ / (3 * B') by positivity)
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  rw [div_lt_iff₀ h2n] at hn
  have hkey : 3 * B' * (n : ℝ) ^ 2 < θ * 2 ^ n := by
    have hmul := mul_lt_mul_of_pos_left hn (show (0 : ℝ) < 3 * B' by positivity)
    calc 3 * B' * (n : ℝ) ^ 2 < 3 * B' * (θ / (3 * B') * 2 ^ n) := hmul
      _ = θ * 2 ^ n := by field_simp
  have hq : (n : ℝ) ^ 2 + (n : ℝ) + 1 ≤ 3 * (n : ℝ) ^ 2 := by nlinarith
  have hqnn : (0 : ℝ) ≤ (n : ℝ) ^ 2 + (n : ℝ) + 1 := by positivity
  calc B * ((n : ℝ) ^ 2 + (n : ℝ) + 1) ≤ B' * ((n : ℝ) ^ 2 + (n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hBle hqnn
    _ ≤ B' * (3 * (n : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hq hB'pos.le
    _ = 3 * B' * (n : ℝ) ^ 2 := by ring
    _ < θ * 2 ^ n := hkey

end Domination

section HeapSize

/-- **`(23)`.**  The heap-capacity bound on the number of circuit traces of length at most `s` over
an alphabet of `M` gates with dependence degree `Δ`. -/
def heapCapacity (M s Δ : ℕ) : ℕ := (s + 1) * (M + s - 1).choose s * 2 ^ (Δ * s)

/-- **`(31)`.**  The multiset factor is polynomial in the depth, of degree the alphabet size. -/
theorem choose_le_pow_alphabet {M : ℕ} (hM : 1 ≤ M) (s : ℕ) :
    (M + s - 1).choose s ≤ (M + s) ^ M := by
  have h1 : M + s - 1 - s = M - 1 := by omega
  have hsym := Nat.choose_symm (n := M + s - 1) (k := s) (by omega)
  rw [h1] at hsym
  calc (M + s - 1).choose s = (M + s - 1).choose (M - 1) := hsym.symm
    _ ≤ (M + s - 1) ^ (M - 1) := Nat.choose_le_pow _ _
    _ ≤ (M + s) ^ (M - 1) := Nat.pow_le_pow_left (by omega) _
    _ ≤ (M + s) ^ M := Nat.pow_le_pow_right (by omega) (by omega)

/-- The heap capacity in exponential form. -/
theorem heapCapacity_le_exp {M : ℕ} (hM : 1 ≤ M) (s Δ : ℕ) :
    ((heapCapacity M s Δ : ℕ) : ℝ)
      ≤ Real.exp (Real.log ((s : ℝ) + 1) + (M : ℝ) * Real.log ((M : ℝ) + (s : ℝ))
        + (Δ : ℝ) * (s : ℝ) * Real.log 2) := by
  have hs1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMs : (0 : ℝ) < (M : ℝ) + (s : ℝ) := by
    have : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
    linarith
  have hnat : heapCapacity M s Δ ≤ (s + 1) * (M + s) ^ M * 2 ^ (Δ * s) := by
    refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (choose_le_pow_alphabet hM s))
  have hcast : ((heapCapacity M s Δ : ℕ) : ℝ)
      ≤ ((s : ℝ) + 1) * ((M : ℝ) + (s : ℝ)) ^ M * (2 : ℝ) ^ (Δ * s) := by
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this
    exact this
  refine hcast.trans (le_of_eq ?_)
  rw [Real.exp_add, Real.exp_add, Real.exp_log hs1]
  congr 1
  · congr 1
    rw [Real.exp_nat_mul, Real.exp_log hMs]
  · rw [show (Δ : ℝ) * (s : ℝ) = ((Δ * s : ℕ) : ℝ) by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]

end HeapSize

section CapAsymptotics

/-- **`(28)` and `(24)`.**  With Hilbert dimension `D = 2^n`, alphabet size linear in `n`, depth
`s <= cD`, and a prefactor at most `K₀ e^{ηD}`, the torsion cap condition holds for every large `n`
as soon as `η + cΔ log 2` stays below the cap exponent `γ`. -/
theorem eventually_heapCapacity_cap
    {γ η c Cm K₀ : ℝ} {Δ : ℕ} (hc : 0 < c) (hCm : 0 ≤ Cm) (hK₀ : 0 < K₀)
    (hθ : η + c * (Δ : ℝ) * Real.log 2 < γ)
    (Mfun : ℕ → ℕ) (hM1 : ∀ n, 1 ≤ Mfun n) (hM : ∀ n, ((Mfun n : ℕ) : ℝ) ≤ Cm * (n : ℝ) + Cm)
    (Kfun : ℕ → ℝ) (hK : ∀ n, Kfun n ≤ K₀ * Real.exp (η * 2 ^ n)) :
    ∀ᶠ n : ℕ in atTop,
      Kfun n * ((heapCapacity (Mfun n) ⌊c * 2 ^ n⌋₊ Δ : ℕ) : ℝ) * Real.exp (-γ * 2 ^ n) < 1 := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set W : ℝ := 2 * Cm + c + 1 with hWdef
  have hWpos : (0 : ℝ) < W := by simp only [hWdef]; linarith
  set B : ℝ := Cm * (|Real.log W| + Real.log 2) with hBdef
  set θ : ℝ := γ - η - c * (Δ : ℝ) * Real.log 2 with hθdef
  have hθpos : 0 < θ := by simp only [hθdef]; linarith
  set C₀ : ℝ := Real.log K₀ + Real.log (c + 1) with hC₀def
  set B' : ℝ := B + Real.log 2 + |C₀| with hB'def
  filter_upwards [eventually_quadratic_lt_two_pow hθpos B'] with n hquad
  set s : ℕ := ⌊c * 2 ^ n⌋₊ with hsdef
  set M : ℕ := Mfun n with hMdef
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have h2npos : (0 : ℝ) < 2 ^ n := by positivity
  have hnnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hnle : (n : ℝ) ≤ 2 ^ n := by
    have h1 : ((n : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast (Nat.lt_two_pow_self).le
    simpa using h1
  have hs : (s : ℝ) ≤ c * 2 ^ n := Nat.floor_le (by positivity)
  have hsnn : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
  have hM' : (M : ℝ) ≤ Cm * (n : ℝ) + Cm := hM n
  have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1 n
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := by linarith
  have hMs1 : (1 : ℝ) ≤ (M : ℝ) + (s : ℝ) := by linarith
  -- the depth factor
  have hlog1 : Real.log ((s : ℝ) + 1) ≤ Real.log (c + 1) + (n : ℝ) * Real.log 2 := by
    have hle : (s : ℝ) + 1 ≤ (c + 1) * 2 ^ n := by nlinarith
    have h := Real.log_le_log (by positivity) hle
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h
  -- the alphabet factor
  have hlogMs : Real.log ((M : ℝ) + (s : ℝ)) ≤ Real.log W + (n : ℝ) * Real.log 2 := by
    have hle : (M : ℝ) + (s : ℝ) ≤ W * 2 ^ n := by
      have h1 : Cm * (n : ℝ) + Cm ≤ 2 * Cm * 2 ^ n := by nlinarith
      simp only [hWdef]
      nlinarith
    have h := Real.log_le_log (by linarith) hle
    rwa [Real.log_mul (ne_of_gt hWpos) (by positivity), Real.log_pow] at h
  have hlogMsnn : (0 : ℝ) ≤ Real.log ((M : ℝ) + (s : ℝ)) := Real.log_nonneg hMs1
  have hlogW : Real.log W ≤ |Real.log W| := le_abs_self _
  have hquadbound : (M : ℝ) * Real.log ((M : ℝ) + (s : ℝ)) ≤ B * ((n : ℝ) ^ 2 + (n : ℝ) + 1) := by
    have hstep : (M : ℝ) * Real.log ((M : ℝ) + (s : ℝ))
        ≤ (Cm * (n : ℝ) + Cm) * (Real.log W + (n : ℝ) * Real.log 2) :=
      mul_le_mul hM' hlogMs hlogMsnn (by nlinarith)
    refine hstep.trans ?_
    simp only [hBdef]
    nlinarith [mul_nonneg (mul_nonneg hCm (sub_nonneg.mpr hlogW)) hnnn,
      mul_nonneg hCm (sub_nonneg.mpr hlogW),
      mul_nonneg (mul_nonneg hCm (abs_nonneg (Real.log W))) (sq_nonneg (n : ℝ)),
      mul_nonneg hCm hlog2pos.le]
  -- the gate factor
  have hΔnn : (0 : ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg _
  have hdelta : (Δ : ℝ) * (s : ℝ) * Real.log 2 ≤ c * (Δ : ℝ) * Real.log 2 * 2 ^ n := by
    calc (Δ : ℝ) * (s : ℝ) * Real.log 2 = (Δ : ℝ) * Real.log 2 * (s : ℝ) := by ring
      _ ≤ (Δ : ℝ) * Real.log 2 * (c * 2 ^ n) :=
          mul_le_mul_of_nonneg_left hs (mul_nonneg hΔnn hlog2pos.le)
      _ = c * (Δ : ℝ) * Real.log 2 * 2 ^ n := by ring
  -- assemble
  have hHle : ((heapCapacity M s Δ : ℕ) : ℝ)
      ≤ Real.exp (Real.log (c + 1) + (n : ℝ) * Real.log 2 + B * ((n : ℝ) ^ 2 + (n : ℝ) + 1)
          + c * (Δ : ℝ) * Real.log 2 * 2 ^ n) := by
    refine (heapCapacity_le_exp (hM1 n) s Δ).trans (Real.exp_le_exp.mpr ?_)
    linarith
  have hKle : Kfun n ≤ Real.exp (Real.log K₀ + η * 2 ^ n) := by
    rw [Real.exp_add, Real.exp_log hK₀]
    exact hK n
  have hprod : Kfun n * ((heapCapacity M s Δ : ℕ) : ℝ) * Real.exp (-γ * 2 ^ n)
      ≤ Real.exp ((Real.log K₀ + η * 2 ^ n)
          + (Real.log (c + 1) + (n : ℝ) * Real.log 2 + B * ((n : ℝ) ^ 2 + (n : ℝ) + 1)
            + c * (Δ : ℝ) * Real.log 2 * 2 ^ n) + (-γ * 2 ^ n)) := by
    rw [Real.exp_add, Real.exp_add]
    exact mul_le_mul (mul_le_mul hKle hHle (by positivity) (Real.exp_pos _).le)
      le_rfl (Real.exp_pos _).le (by positivity)
  refine lt_of_le_of_lt hprod ?_
  have hrw : (Real.log K₀ + η * 2 ^ n)
      + (Real.log (c + 1) + (n : ℝ) * Real.log 2 + B * ((n : ℝ) ^ 2 + (n : ℝ) + 1)
        + c * (Δ : ℝ) * Real.log 2 * 2 ^ n) + (-γ * 2 ^ n)
      = C₀ + (n : ℝ) * Real.log 2 + B * ((n : ℝ) ^ 2 + (n : ℝ) + 1) - θ * 2 ^ n := by
    simp only [hC₀def, hθdef]
    ring
  rw [hrw]
  have hb : C₀ + (n : ℝ) * Real.log 2 + B * ((n : ℝ) ^ 2 + (n : ℝ) + 1)
      ≤ B' * ((n : ℝ) ^ 2 + (n : ℝ) + 1) := by
    have h1 : C₀ ≤ |C₀| := le_abs_self C₀
    have h2 : (0 : ℝ) ≤ |C₀| * ((n : ℝ) ^ 2 + (n : ℝ)) :=
      mul_nonneg (abs_nonneg _) (by positivity)
    have h3 : (0 : ℝ) ≤ Real.log 2 * (n : ℝ) ^ 2 :=
      mul_nonneg hlog2pos.le (sq_nonneg _)
    have hexpand : B' * ((n : ℝ) ^ 2 + (n : ℝ) + 1)
        = B * ((n : ℝ) ^ 2 + (n : ℝ) + 1) + Real.log 2 * (n : ℝ) ^ 2
          + Real.log 2 * (n : ℝ) + Real.log 2 + |C₀| * ((n : ℝ) ^ 2 + (n : ℝ)) + |C₀| := by
      simp only [hB'def]
      ring
    rw [hexpand]
    linarith
  have hneg : C₀ + (n : ℝ) * Real.log 2 + B * ((n : ℝ) ^ 2 + (n : ℝ) + 1) - θ * 2 ^ n < 0 := by
    linarith
  calc Real.exp (C₀ + (n : ℝ) * Real.log 2 + B * ((n : ℝ) ^ 2 + (n : ℝ) + 1) - θ * 2 ^ n)
      < Real.exp 0 := Real.exp_lt_exp.mpr hneg
    _ = 1 := Real.exp_zero

/-- **`(24)` for a fixed torsion order.**  For every fixed prime `k` the cap condition holds at all
large `n`. -/
theorem eventually_cap_fixed_prime {γ c Cm : ℝ} {Δ k : ℕ} (hc : 0 < c) (hCm : 0 ≤ Cm)
    (hk : 2 ≤ k) (hcΔ : c * (Δ : ℝ) * Real.log 2 < γ)
    (Mfun : ℕ → ℕ) (hM1 : ∀ n, 1 ≤ Mfun n) (hM : ∀ n, ((Mfun n : ℕ) : ℝ) ≤ Cm * (n : ℝ) + Cm) :
    ∀ᶠ n : ℕ in atTop,
      4 * ((k : ℝ) - 1) * ((heapCapacity (Mfun n) ⌊c * 2 ^ n⌋₊ Δ : ℕ) : ℝ)
        * Real.exp (-γ * 2 ^ n) < 1 := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  refine eventually_heapCapacity_cap (γ := γ) (η := 0) (K₀ := 4 * ((k : ℝ) - 1)) hc hCm
    (by linarith) (by simpa using hcΔ) Mfun hM1 hM _ (fun n => ?_)
  rw [zero_mul, Real.exp_zero, mul_one]

/-- **`(30)`.**  Bertrand's postulate supplies, at every large `n`, a prime torsion order of size at
least `e^{ηD}` for which the cap condition still holds. -/
theorem eventually_exists_prime_cap {γ η c Cm : ℝ} {Δ : ℕ} (hc : 0 < c) (hη : 0 < η)
    (hCm : 0 ≤ Cm) (hθ : η + c * (Δ : ℝ) * Real.log 2 < γ)
    (Mfun : ℕ → ℕ) (hM1 : ∀ n, 1 ≤ Mfun n) (hM : ∀ n, ((Mfun n : ℕ) : ℝ) ≤ Cm * (n : ℝ) + Cm) :
    ∀ᶠ n : ℕ in atTop, ∃ k : ℕ, k.Prime ∧ Real.exp (η * 2 ^ n) ≤ (k : ℝ) ∧
      4 * ((k : ℝ) - 1) * ((heapCapacity (Mfun n) ⌊c * 2 ^ n⌋₊ Δ : ℕ) : ℝ)
        * Real.exp (-γ * 2 ^ n) < 1 := by
  have hcap := eventually_heapCapacity_cap (γ := γ) (η := η) (K₀ := 16) hc hCm
    (by norm_num) hθ Mfun hM1 hM (fun n => 16 * Real.exp (η * 2 ^ n)) (fun n => le_rfl)
  filter_upwards [hcap] with n hn
  set Eexp : ℝ := Real.exp (η * 2 ^ n) with hEdef
  have hEpos : (0 : ℝ) < Eexp := Real.exp_pos _
  have hEone : (1 : ℝ) ≤ Eexp := by
    rw [hEdef, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hceilne : ⌈Eexp⌉₊ ≠ 0 := by
    have hpos : 0 < ⌈Eexp⌉₊ := Nat.ceil_pos.mpr hEpos
    omega
  obtain ⟨p, hp, hlt, hple⟩ := Nat.exists_prime_lt_and_le_two_mul ⌈Eexp⌉₊ hceilne
  have hpR : Eexp ≤ (p : ℝ) := by
    refine le_trans (Nat.le_ceil Eexp) ?_
    exact_mod_cast hlt.le
  refine ⟨p, hp, hpR, ?_⟩
  have hceil_lt : (⌈Eexp⌉₊ : ℝ) < Eexp + 1 := Nat.ceil_lt_add_one hEpos.le
  have hp2 : (p : ℝ) ≤ 2 * (⌈Eexp⌉₊ : ℝ) := by exact_mod_cast hple
  have hpbound : 4 * ((p : ℝ) - 1) ≤ 16 * Eexp := by nlinarith
  have hHnn : (0 : ℝ) ≤ ((heapCapacity (Mfun n) ⌊c * 2 ^ n⌋₊ Δ : ℕ) : ℝ) := Nat.cast_nonneg _
  refine lt_of_le_of_lt ?_ hn
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpbound hHnn)
    (Real.exp_pos _).le

end CapAsymptotics

section CorollaryB1

/-- **Corollary B.1.**  At every large `n` there is a prime torsion order `k` of size at least
`e^{ηD}` such that every autonomous trajectory of maximal projective rational rank on a Hilbert space
of dimension `D = 2^n` has arbitrarily late recurrence cycles all of whose `k-1` equally spaced
interior rational slices have robust circuit complexity above the depth `⌊cD⌋`. -/
theorem eventually_exists_prime_late_recurrence_hard_slices
    {δ c η Cm : ℝ} {Δ : ℕ} (hδ : 0 ≤ δ) (hδ2 : 2 * δ ^ 2 ≤ 1) (hc : 0 < c) (hη : 0 < η)
    (hCm : 0 ≤ Cm) (hθ : η + c * (Δ : ℝ) * Real.log 2 < (1 - 4 * δ ^ 2) / 4)
    (Mfun : ℕ → ℕ) (hM1 : ∀ n, 1 ≤ Mfun n) (hM : ∀ n, ((Mfun n : ℕ) : ℝ) ≤ Cm * (n : ℝ) + Cm) :
    ∀ᶠ n : ℕ in atTop, ∃ k : ℕ, k.Prime ∧ Real.exp (η * 2 ^ n) ≤ (k : ℝ) ∧
      ∀ d : ℕ, d + 1 = 2 ^ n →
      ∀ E : Fin (d + 1) → ℝ, LinearIndependent ℚ (projectiveGapPacket E) →
      ∀ dict : ℕ → Finset (EuclideanSpace ℂ (Fin (d + 1))), Monotone dict →
      (∀ y ∈ dict ⌊c * 2 ^ n⌋₊, ‖y‖ = 1) →
      (dict ⌊c * 2 ^ n⌋₊).card ≤ heapCapacity (Mfun n) ⌊c * 2 ^ n⌋₊ Δ →
      ∀ ρ : ℝ, 0 < ρ → ∀ A : ℝ, ∃ R : ℝ, A < R ∧
        pureStateTraceDistance (flowRay E R) (flowRay E 0) < ρ ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ k - 1 →
          ((⌊c * 2 ^ n⌋₊ : ℕ) : ℕ∞) < robustCircuitComplexity dict δ
            (flowRay E ((j : ℝ) * R / (k : ℝ))) := by
  filter_upwards [eventually_exists_prime_cap (γ := (1 - 4 * δ ^ 2) / 4) hc hη hCm hθ Mfun hM1 hM]
    with n hn
  obtain ⟨k, hk, hklarge, hcap⟩ := hn
  refine ⟨k, hk, hklarge, ?_⟩
  intro d hd E hind dict hmono hunit hcard ρ hρ A
  haveI : NeZero k := ⟨hk.pos.ne'⟩
  have hD : ((d : ℝ) + 1) = 2 ^ n := by
    have hcast := congrArg (fun m : ℕ => (m : ℝ)) hd
    push_cast at hcast
    exact hcast
  refine exists_late_recurrence_depthHard hk E hind dict hmono ⌊c * 2 ^ n⌋₊ (Mfun n) Δ hunit
    hcard hδ hδ2 ?_ hρ A
  rw [hD]
  exact hcap

end CorollaryB1

end

end GaloisForLFunctions.HTGeometry
