import GaloisForLFunctions.RHTower.CommonProfilePoissonVacuum

/-!
# The anchored response of a physical profile and its vacuum-subtracted occupancy

The frequency weight of a Schwartz profile is its Fourier transform sampled at the reduced
frequencies.  With that weight the anchored response of the Möbius layer is exactly the
occupancy defect in the card's normalization, and the complete future Bernoulli average becomes a
sieved physical occupancy minus its Euler vacuum.
-/

open scoped BigOperators FourierTransform SchwartzMap
open ArithmeticFunction

noncomputable section

namespace RHTower

/-! ## The frequency weight of a physical profile -/

/-- The frequency weight of a Schwartz profile: its Fourier transform on the rationals. -/
def schwartzFrequencyWeight (W : 𝓢(ℝ, ℂ)) : ℚ → ℂ :=
  fun x => 𝓕 (W : ℝ → ℂ) (x : ℝ)

theorem schwartzFrequencyWeight_apply (W : 𝓢(ℝ, ℂ)) (u : ℤ) (q : ℕ) :
    schwartzFrequencyWeight W ((u : ℚ) / (q : ℚ)) = 𝓕 (W : ℝ → ℂ) ((u : ℝ) / (q : ℝ)) := by
  rw [schwartzFrequencyWeight]
  push_cast
  rfl

/-- The transform of a Schwartz profile is summable along every reduced-frequency lattice. -/
theorem summable_schwartzFrequencyWeight (W : 𝓢(ℝ, ℂ)) {q : ℕ} (hq : q ≠ 0) :
    Summable fun u : ℤ => ‖𝓕 (W : ℝ → ℂ) ((u : ℝ) / (q : ℝ))‖ := by
  have hqR : ((q : ℕ) : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr hq)
  have h := GaloisForLFunctions.RHTower.ccmRationalArchimedeanSchwartz_lattice_summable
    (𝓕 W) (a := ((q : ℕ) : ℝ)⁻¹) hqR
  refine h.congr fun u => ?_
  rw [SchwartzMap.fourier_coe, inv_mul_eq_div]

/-- The nonzero-frequency response of a Schwartz profile is summable at every modulus. -/
theorem summable_responseTerm_schwartz (W : 𝓢(ℝ, ℂ)) (q : ℕ) (h : ℤ) :
    Summable (responseTerm (schwartzFrequencyWeight W) q h) := by
  rcases eq_or_ne q 0 with rfl | hq
  · refine summable_zero.congr fun u => ?_
    rcases eq_or_ne u 0 with rfl | hu
    · rw [responseTerm_zero]
    · rw [responseTerm_of_ne_zero _ _ _ hu,
        show quadraticCongruenceRootSumTotal 0 h u = 0 from by
          simp [quadraticCongruenceRootSumTotal],
        mul_zero]
  · refine Summable.of_norm_bounded
      (g := fun u : ℤ => (quadraticCongruenceRootCountTotal q h : ℝ) *
        ‖𝓕 (W : ℝ → ℂ) ((u : ℝ) / (q : ℝ))‖)
      ((summable_schwartzFrequencyWeight W hq).mul_left _) fun u => ?_
    rcases eq_or_ne u 0 with rfl | hu
    · rw [responseTerm_zero, norm_zero]
      positivity
    · rw [responseTerm_of_ne_zero _ _ _ hu, schwartzFrequencyWeight_apply, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (norm_quadraticCongruenceRootSumTotal_le_count q h u) (norm_nonneg _)

/-! ## `(PF1)` in the anchored normalization -/

/-- The unnormalized anchored response of a physical profile is the modulus times its occupancy
defect. -/
theorem anchoredResponseRaw_schwartz (W : 𝓢(ℝ, ℂ)) (Q : CGLPositiveModulus) (h : ℤ) :
    anchoredResponseRaw (schwartzFrequencyWeight W) Q.value h =
      (Q.value : ℂ) * occupancyDefect W Q.value h := by
  have hq : ((Q.value : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne Q.value)
  rw [occupancyDefect_eq_tsum W Q h, anchoredResponseRaw, ← tsum_mul_left]
  refine tsum_congr fun u => ?_
  rcases eq_or_ne u 0 with rfl | hu
  · rw [responseTerm_zero, if_pos rfl, mul_zero]
  · rw [responseTerm_of_ne_zero _ _ _ hu, if_neg hu, schwartzFrequencyWeight_apply]
    field_simp

/-- **`(PF1)`.**  The anchored response of a physical profile is the modulus over the root count
times the occupancy defect. -/
theorem anchoredResponse_schwartz (W : 𝓢(ℝ, ℂ)) (Q : CGLPositiveModulus) (h : ℤ) :
    anchoredResponse (schwartzFrequencyWeight W) Q.value h =
      ((Q.value : ℂ) / (quadraticCongruenceRootCountTotal Q.value h : ℂ)) *
        occupancyDefect W Q.value h := by
  rw [anchoredResponse, anchoredResponseRaw_schwartz W Q h, mul_comm_div, mul_div_assoc]

/-! ## The sieved physical occupancy -/

/-- `P_N(m)`: the indicator that no prime of the packet divides `m`. -/
def sieveIndicator (N : ℕ) (m : ℤ) : ℂ :=
  ∏ p ∈ N.primeFactors, (if (p : ℤ) ∣ m then 0 else 1)

theorem sieveIndicator_eq_ite (N : ℕ) (m : ℤ) :
    sieveIndicator N m = if ∀ p ∈ N.primeFactors, ¬ ((p : ℤ) ∣ m) then 1 else 0 := by
  classical
  rw [sieveIndicator, ← Finset.prod_boole (p := fun p : ℕ => ¬ ((p : ℤ) ∣ m))]
  exact Finset.prod_congr rfl fun p _ => by
    by_cases hp : (p : ℤ) ∣ m
    · rw [if_pos hp, if_neg (by simpa using hp)]
    · rw [if_neg hp, if_pos hp]

/-- The coprimality of the packet with the reducible quadratic is exactly the double sieve
condition. -/
theorem coprime_iff_sieve {N : ℕ} (hN : N ≠ 0) (h : ℤ) (m : ℤ) :
    ((m * (m + h)).natAbs).Coprime N ↔
      (∀ p ∈ N.primeFactors, ¬ ((p : ℤ) ∣ m)) ∧ (∀ p ∈ N.primeFactors, ¬ ((p : ℤ) ∣ (m + h))) := by
  constructor
  · intro hcop
    constructor <;>
    · intro p hp hdvd
      obtain ⟨hpp, hpN, -⟩ := Nat.mem_primeFactors.1 hp
      have hpq : (p : ℤ) ∣ m * (m + h) := by
        first
        | exact hdvd.mul_right _
        | exact hdvd.mul_left _
      have hpnat : p ∣ (m * (m + h)).natAbs := Int.natCast_dvd.1 hpq
      exact Nat.Prime.not_coprime_iff_dvd.2 ⟨p, hpp, hpnat, hpN⟩ hcop
  · rintro ⟨h1, h2⟩
    by_contra hcop
    obtain ⟨p, hpp, hpm, hpN⟩ := Nat.Prime.not_coprime_iff_dvd.1 hcop
    have hmem : p ∈ N.primeFactors := Nat.mem_primeFactors.2 ⟨hpp, hpN, hN⟩
    have hpz : (p : ℤ) ∣ m * (m + h) := Int.natCast_dvd.2 hpm
    rcases (Nat.prime_iff_prime_int.mp hpp).dvd_mul.1 hpz with hcase | hcase
    · exact h1 p hmem hcase
    · exact h2 p hmem hcase

/-- **Finite inclusion--exclusion for the future packet.** -/
theorem sum_divisors_moebius_dvd_eq_sieve {N : ℕ} (hN : N ≠ 0) (h : ℤ) (m : ℤ) :
    ∑ e ∈ N.divisors, ((moebius e : ℤ) : ℂ) * (if (e : ℤ) ∣ m * (m + h) then 1 else 0) =
      sieveIndicator N m * sieveIndicator N (m + h) := by
  classical
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  rw [divisors_filter_dvd_natAbs hN (m * (m + h)), sum_divisors_moebius_complex,
    sieveIndicator_eq_ite, sieveIndicator_eq_ite]
  by_cases hcop : ((m * (m + h)).natAbs).Coprime N
  · obtain ⟨h1, h2⟩ := (coprime_iff_sieve hN h m).1 hcop
    rw [if_pos hcop, if_pos h1, if_pos h2, mul_one]
  · rw [if_neg hcop]
    have hnot := fun hc => hcop ((coprime_iff_sieve hN h m).2 hc)
    by_cases h1 : ∀ p ∈ N.primeFactors, ¬ ((p : ℤ) ∣ m)
    · rw [if_pos h1, if_neg (fun h2 => hnot ⟨h1, h2⟩), mul_zero]
    · rw [if_neg h1, zero_mul]

/-- The sieved physical occupancy of the anchor `c` inside the future packet `N`. -/
def siftedOccupancy (W : 𝓢(ℝ, ℂ)) (c N : ℕ) (h : ℤ) : ℂ :=
  ∑' m : ℤ, (if (c : ℤ) ∣ m * (m + h) then
    W (m : ℝ) * (sieveIndicator N m * sieveIndicator N (m + h)) else 0)

/-- **Möbius-sifted occupancy.**  The alternating sum of anchored occupancies over the packet is
the doubly sieved physical occupancy. -/
theorem sum_divisors_moebius_occupancy (W : 𝓢(ℝ, ℂ)) {c N : ℕ} (hN : Squarefree N)
    (hcN : c.Coprime N) (h : ℤ) :
    ∑ e ∈ N.divisors, ((moebius e : ℤ) : ℂ) * occupancy W (c * e) h =
      siftedOccupancy W c N h := by
  classical
  have hsummable : ∀ e ∈ N.divisors,
      Summable (fun m : ℤ => ((moebius e : ℤ) : ℂ) *
        (if ((c * e : ℕ) : ℤ) ∣ m * (m + h) then W (m : ℝ) else 0)) := fun e _ =>
    (summable_occupancyTerm W (c * e) h).mul_left _
  have hstep : ∀ e ∈ N.divisors, ((moebius e : ℤ) : ℂ) * occupancy W (c * e) h =
      ∑' m : ℤ, ((moebius e : ℤ) : ℂ) *
        (if ((c * e : ℕ) : ℤ) ∣ m * (m + h) then W (m : ℝ) else 0) := fun e _ => by
    rw [occupancy, tsum_mul_left]
  rw [Finset.sum_congr rfl hstep, ← Summable.tsum_finsetSum hsummable, siftedOccupancy]
  refine tsum_congr fun m => ?_
  have hsplit : ∀ e ∈ N.divisors, (((c * e : ℕ) : ℤ) ∣ m * (m + h)) ↔
      ((c : ℤ) ∣ m * (m + h) ∧ (e : ℤ) ∣ m * (m + h)) := by
    intro e he
    obtain ⟨heN, -⟩ := Nat.mem_divisors.1 he
    have hce : c.Coprime e := hcN.coprime_dvd_right heN
    rw [Int.natCast_dvd, Int.natCast_dvd, Int.natCast_dvd]
    constructor
    · intro hdvd
      exact ⟨dvd_trans ⟨e, rfl⟩ hdvd, dvd_trans ⟨c, mul_comm c e⟩ hdvd⟩
    · rintro ⟨h1, h2⟩
      exact hce.mul_dvd_of_dvd_of_dvd h1 h2
  have hcongr : ∀ e ∈ N.divisors,
      ((moebius e : ℤ) : ℂ) * (if ((c * e : ℕ) : ℤ) ∣ m * (m + h) then W (m : ℝ) else 0) =
      (if (c : ℤ) ∣ m * (m + h) then W (m : ℝ) else 0) *
        (((moebius e : ℤ) : ℂ) * (if (e : ℤ) ∣ m * (m + h) then 1 else 0)) := by
    intro e he
    rw [if_congr (hsplit e he) rfl rfl]
    by_cases h1 : (c : ℤ) ∣ m * (m + h)
    · by_cases h2 : (e : ℤ) ∣ m * (m + h)
      · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2]
        ring
      · rw [if_neg (fun hcon => h2 hcon.2), if_pos h1, if_neg h2]
        ring
    · rw [if_neg (fun hcon => h1 hcon.1), if_neg h1]
      ring
  rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum,
    sum_divisors_moebius_dvd_eq_sieve hN.ne_zero h m]
  by_cases h1 : (c : ℤ) ∣ m * (m + h)
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1, zero_mul]

/-- `(PF1)` at a bare nondegenerate modulus. -/
theorem anchoredResponse_schwartz' (W : 𝓢(ℝ, ℂ)) {q : ℕ} (hq : q ≠ 0) (h : ℤ) :
    anchoredResponse (schwartzFrequencyWeight W) q h =
      ((q : ℂ) / (quadraticCongruenceRootCountTotal q h : ℂ)) * occupancyDefect W q h :=
  anchoredResponse_schwartz W ⟨q, Nat.pos_of_ne_zero hq⟩ h

/-- The root density is multiplicative at coprime moduli. -/
theorem rootDensity_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) (h : ℤ) :
    rootDensity (a * b) h = rootDensity a h * rootDensity b h := by
  have haC : ((a : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hbC : ((b : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  rw [rootDensity, rootDensity, rootDensity, quadraticCongruenceRootCountTotal_mul ha hb hab h]
  push_cast
  field_simp

/-- **The Euler vacuum of the packet.**  The alternating sum of anchored root densities is the
anchor density times the local survival product. -/
theorem sum_divisors_moebius_rootDensity {c N : ℕ} (hc : c ≠ 0) (hN : Squarefree N)
    (hcN : c.Coprime N) (h : ℤ) :
    ∑ e ∈ N.divisors, ((moebius e : ℤ) : ℂ) * rootDensity (c * e) h =
      rootDensity c h * survivalProduct N h := by
  have hstep : ∀ e ∈ N.divisors, ((moebius e : ℤ) : ℂ) * rootDensity (c * e) h =
      rootDensity c h * (((moebius e : ℤ) : ℂ) * rootDensity e h) := by
    intro e he
    obtain ⟨heN, -⟩ := Nat.mem_divisors.1 he
    have he0 : e ≠ 0 := ne_zero_of_dvd_ne_zero hN.ne_zero heN
    rw [rootDensity_mul hc he0 (hcN.coprime_dvd_right heN) h]
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  congr 1
  rw [survivalProduct]
  simpa only [rootDensity] using quadraticCongruenceRootDensity_squarefree_euler hN h

/-! ## `(CG3)` and `(CG4)` -/

/-- **`(CG3)`.**  The complete future Bernoulli average of the anchored primitive response of a
physical profile is the anchor-normalized sieved occupancy minus the Euler vacuum. -/
theorem futureResponse_schwartz_eq (W : 𝓢(ℝ, ℂ)) {c N : ℕ} (hc : c ≠ 0) (hN : Squarefree N)
    (hcN : c.Coprime N) (h : ℤ) :
    futureResponse (schwartzFrequencyWeight W) c N h =
      ((c : ℂ) / (quadraticCongruenceRootCountTotal c h : ℂ)) * siftedOccupancy W c N h -
        𝓕 (W : ℝ → ℂ) 0 * survivalProduct N h := by
  have hcC : ((c : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc
  have hCc : ((quadraticCongruenceRootCountTotal c h : ℕ) : ℂ) ≠ 0 :=
    quadraticCongruenceRootCountTotal_cast_ne_zero hc h
  have hstep : ∀ e ∈ N.divisors,
      ((moebius e : ℤ) : ℂ) * rootDensity e h *
          anchoredResponse (schwartzFrequencyWeight W) (c * e) h =
        ((c : ℂ) / (quadraticCongruenceRootCountTotal c h : ℂ)) *
          (((moebius e : ℤ) : ℂ) * occupancyDefect W (c * e) h) := by
    intro e he
    obtain ⟨heN, -⟩ := Nat.mem_divisors.1 he
    have he0 : e ≠ 0 := ne_zero_of_dvd_ne_zero hN.ne_zero heN
    have heC : ((e : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr he0
    have hCe : ((quadraticCongruenceRootCountTotal e h : ℕ) : ℂ) ≠ 0 :=
      quadraticCongruenceRootCountTotal_cast_ne_zero he0 h
    rw [anchoredResponse_schwartz' W (Nat.mul_ne_zero hc he0) h,
      quadraticCongruenceRootCountTotal_mul hc he0 (hcN.coprime_dvd_right heN) h, rootDensity]
    push_cast
    field_simp
  rw [futureResponse_eq_sum_divisors hc hN hcN h (schwartzFrequencyWeight W)
      (fun q => summable_responseTerm_schwartz W q h),
    Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  have hdefect : ∑ e ∈ N.divisors, ((moebius e : ℤ) : ℂ) * occupancyDefect W (c * e) h =
      siftedOccupancy W c N h -
        𝓕 (W : ℝ → ℂ) 0 * (rootDensity c h * survivalProduct N h) := by
    have hsplit : ∀ e ∈ N.divisors, ((moebius e : ℤ) : ℂ) * occupancyDefect W (c * e) h =
        ((moebius e : ℤ) : ℂ) * occupancy W (c * e) h -
          𝓕 (W : ℝ → ℂ) 0 * (((moebius e : ℤ) : ℂ) * rootDensity (c * e) h) := by
      intro e _
      rw [occupancyDefect]
      ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib,
      sum_divisors_moebius_occupancy W hN hcN h, ← Finset.mul_sum,
      sum_divisors_moebius_rootDensity hc hN hcN h]
  rw [hdefect, mul_sub, rootDensity]
  congr 1
  field_simp

/-- **`(CG4)`.**  The density-weighted normalization of `(CG3)`. -/
theorem rootDensity_mul_futureResponse_schwartz (W : 𝓢(ℝ, ℂ)) {c N : ℕ} (hc : c ≠ 0)
    (hN : Squarefree N) (hcN : c.Coprime N) (h : ℤ) :
    rootDensity c h * futureResponse (schwartzFrequencyWeight W) c N h =
      siftedOccupancy W c N h -
        rootDensity c h * (𝓕 (W : ℝ → ℂ) 0 * survivalProduct N h) := by
  have hcC : ((c : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc
  have hCc : ((quadraticCongruenceRootCountTotal c h : ℕ) : ℂ) ≠ 0 :=
    quadraticCongruenceRootCountTotal_cast_ne_zero hc h
  rw [futureResponse_schwartz_eq W hc hN hcN h, mul_sub, rootDensity]
  congr 1
  field_simp

end RHTower
