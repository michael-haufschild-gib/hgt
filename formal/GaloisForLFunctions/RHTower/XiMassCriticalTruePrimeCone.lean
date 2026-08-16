import GaloisForLFunctions.RHTower.XiMassCriticalIntegerFace
import GaloisForLFunctions.RHTower.XiMassCriticalPrimeSquareTail
import GaloisForLFunctions.RHTower.XiMassPrimePowerVerticalIdeal

/-!
# The prime-atom cone in centered-atom form

The prime-atom cone sum weights the damped Fourier profile by von Mangoldt.  Because the profile
already carries the critical damping `e^{-h/2}`, that weighted profile is exactly the depth-free
centered prime atom:

`Λ(n) · e^{-log n/2} · stripFourier(...)(log n) = LSeries.term Λ (1/2) n · stripFourier(...)`.

Rewriting the cone in that form is what lets the prime-power layer theorems — the vertical
prime-square layer, its beyond-cone tail, and the high prime-power tail — act on the moving cone.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- **The cone summand is the centered prime atom.**  The critical damping inside the profile is
exactly the critical Dirichlet weight. -/
theorem vonMangoldt_mul_dampedProfile_eq_centeredPrimeAtom
    (a sigma u : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        xiMassCriticalDampedFourierProfile a sigma u (Real.log n)
      = xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := Nat.pos_of_ne_zero hn
    exact_mod_cast this
  have hne : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hEP : ((Real.exp (-Real.log n / 2) : ℝ) : ℂ) = ((n : ℂ) ^ ((1 : ℂ) / 2))⁻¹ := by
    rw [Complex.cpow_def_of_ne_zero hne, ← Complex.exp_neg, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [xiMassCriticalDampedFourierProfile, xiMassCenteredPrimeAtom,
    LSeries.term_of_ne_zero hn, hEP]
  ring

/-- The prime-atom cone sum, written with centered prime atoms. -/
theorem xiMassCriticalPrimeAtomConeSum_eq_sum_centeredAtom (a sigma d u : ℝ) :
    xiMassCriticalPrimeAtomConeSum a sigma d u
      = ∑ k ∈ Finset.range (⌊Real.exp (d * u / (d - 1 / 2))⌋₊ - 1),
          xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2) := by
  rw [xiMassCriticalPrimeAtomConeSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcast : ((k : ℝ) + 2) = ((k + 2 : ℕ) : ℝ) := by push_cast; ring
  rw [hcast]
  exact vonMangoldt_mul_dampedProfile_eq_centeredPrimeAtom a sigma u (by omega)

/-! ## The cone atom -/

open scoped Classical in
/-- The centered prime atom truncated at the moving cone. -/
def xiMassCriticalConeAtom (a sigma d u : ℝ) (n : ℕ) : ℂ :=
  if (n : ℝ) ≤ Real.exp (d * u / (d - 1 / 2)) then
    xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) n
  else 0

theorem xiMassCenteredPrimeAtom_eq_zero_of_lt_two {a : ℝ} {τ : ℂ} {n : ℕ} (hn : n < 2) :
    xiMassCenteredPrimeAtom a τ n = 0 := by
  interval_cases n
  · rw [xiMassCenteredPrimeAtom, LSeries.term_zero, zero_mul]
  · rw [xiMassCenteredPrimeAtom, LSeries.term_of_ne_zero one_ne_zero]
    simp

theorem xiMassCriticalConeAtom_eq_zero_of_lt_two {a sigma d u : ℝ} {n : ℕ} (hn : n < 2) :
    xiMassCriticalConeAtom a sigma d u n = 0 := by
  classical
  rw [xiMassCriticalConeAtom]
  split_ifs
  · exact xiMassCenteredPrimeAtom_eq_zero_of_lt_two hn
  · rfl

theorem xiMassCriticalConeAtom_eq_zero_of_gt {a sigma d u : ℝ} {n : ℕ}
    (hn : ⌊Real.exp (d * u / (d - 1 / 2))⌋₊ < n) :
    xiMassCriticalConeAtom a sigma d u n = 0 := by
  classical
  rw [xiMassCriticalConeAtom, if_neg]
  intro hle
  have := Nat.le_floor hle
  omega

/-- **The cone sum is the total of the cone atoms.** -/
theorem xiMassCriticalPrimeAtomConeSum_eq_tsum_coneAtom (a sigma d u : ℝ) :
    xiMassCriticalPrimeAtomConeSum a sigma d u
      = ∑' n : ℕ, xiMassCriticalConeAtom a sigma d u n := by
  classical
  have hzero : ∀ n ∉ Finset.Icc 2 ⌊Real.exp (d * u / (d - 1 / 2))⌋₊,
      xiMassCriticalConeAtom a sigma d u n = 0 := by
    intro n hn
    rw [Finset.mem_Icc, not_and_or] at hn
    rcases hn with hn | hn
    · exact xiMassCriticalConeAtom_eq_zero_of_lt_two (by omega)
    · exact xiMassCriticalConeAtom_eq_zero_of_gt (by omega)
  rw [tsum_eq_sum hzero, xiMassCriticalPrimeAtomConeSum_eq_sum_centeredAtom]
  have hval : ∀ n ∈ Finset.Icc 2 ⌊Real.exp (d * u / (d - 1 / 2))⌋₊,
      xiMassCriticalConeAtom a sigma d u n
        = xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [xiMassCriticalConeAtom, if_pos]
    exact le_trans (Nat.cast_le.2 hn.2) (Nat.floor_le (Real.exp_pos _).le)
  rw [Finset.sum_congr rfl hval]
  refine Finset.sum_nbij' (i := fun k => k + 2) (j := fun n => n - 2) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [Finset.mem_Icc]
    omega
  · intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_range]
    omega
  · intro k _
    omega
  · intro n hn
    rw [Finset.mem_Icc] at hn
    omega
  · intro k _
    rfl

/-! ## Reindexing the cone by prime powers -/

theorem xiMassCriticalConeAtom_support_primePower {a sigma d u : ℝ} :
    Function.support (xiMassCriticalConeAtom a sigma d u) ⊆ {n : ℕ | IsPrimePow n} := by
  classical
  intro n hn
  have hatom : xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) n ≠ 0 := by
    intro h0
    apply hn
    rw [xiMassCriticalConeAtom]
    split_ifs
    · exact h0
    · rfl
  exact xiMassCenteredPrimeAtom_support_primePower hatom

theorem summable_xiMassCriticalConeAtom (a sigma d u : ℝ) :
    Summable (xiMassCriticalConeAtom a sigma d u) := by
  classical
  refine summable_of_ne_finset_zero
    (s := Finset.Icc 2 ⌊Real.exp (d * u / (d - 1 / 2))⌋₊) ?_
  intro n hn
  rw [Finset.mem_Icc, not_and_or] at hn
  rcases hn with hn | hn
  · exact xiMassCriticalConeAtom_eq_zero_of_lt_two (by omega)
  · exact xiMassCriticalConeAtom_eq_zero_of_gt (by omega)

/-- **The cone reindexed by prime powers.** -/
theorem tsum_xiMassCriticalConeAtom_eq_primePower (a sigma d u : ℝ) :
    (∑' n : ℕ, xiMassCriticalConeAtom a sigma d u n)
      = ∑' (p : Nat.Primes) (k : ℕ),
          xiMassCriticalConeAtom a sigma d u ((p : ℕ) ^ (k + 1)) :=
  tsum_eq_tsum_primes_of_support_subset_prime_powers
    (summable_xiMassCriticalConeAtom a sigma d u) xiMassCriticalConeAtom_support_primePower

/-- Only finitely many primes contribute a nonzero cone atom at a fixed exponent. -/
theorem finite_support_coneAtom_primePow (a sigma d u : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    (Function.support (fun p : Nat.Primes =>
      xiMassCriticalConeAtom a sigma d u ((p : ℕ) ^ m))).Finite := by
  classical
  have hpre : (Function.support (fun p : Nat.Primes =>
      xiMassCriticalConeAtom a sigma d u ((p : ℕ) ^ m)))
      ⊆ (fun p : Nat.Primes => (p : ℕ)) ⁻¹'
        (Set.Iic ⌊Real.exp (d * u / (d - 1 / 2))⌋₊) := by
    intro p hp
    by_contra hcon
    apply hp
    simp only [Set.mem_preimage, Set.mem_Iic, not_le] at hcon
    refine xiMassCriticalConeAtom_eq_zero_of_gt ?_
    exact lt_of_lt_of_le hcon (Nat.le_self_pow (by omega) _)
  refine Set.Finite.subset ?_ hpre
  refine Set.Finite.preimage ?_ (Set.finite_Iic _)
  intro p _ q _ hpq
  exact Subtype.ext hpq

theorem summable_coneAtom_primePow (a sigma d u : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    Summable (fun p : Nat.Primes => xiMassCriticalConeAtom a sigma d u ((p : ℕ) ^ m)) :=
  summable_of_hasFiniteSupport (finite_support_coneAtom_primePow a sigma d u hm)

theorem summable_coneAtom_exponent (a sigma d u : ℝ) (p : Nat.Primes) (j : ℕ) :
    Summable (fun k : ℕ => xiMassCriticalConeAtom a sigma d u ((p : ℕ) ^ (k + 1 + j))) := by
  classical
  refine summable_of_ne_finset_zero
    (s := Finset.range (⌊Real.exp (d * u / (d - 1 / 2))⌋₊ + 1)) ?_
  intro k hk
  rw [Finset.mem_range, not_lt] at hk
  refine xiMassCriticalConeAtom_eq_zero_of_gt ?_
  have hp2 : 2 ≤ (p : ℕ) := p.prop.two_le
  have h1 : (k : ℕ) + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
  have h2 : (2 : ℕ) ^ (k + 1) ≤ (p : ℕ) ^ (k + 1) := Nat.pow_le_pow_left hp2 _
  have h3 : (p : ℕ) ^ (k + 1) ≤ (p : ℕ) ^ (k + 1 + j) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- The high-power cone family vanishes past the cone. -/
theorem coneAtom_high_eq_zero_of_gt {a sigma d u : ℝ} {p : Nat.Primes} {k : ℕ}
    (hp : ⌊Real.exp (d * u / (d - 1 / 2))⌋₊ < (p : ℕ)) :
    xiMassCriticalConeAtom a sigma d u ((p : ℕ) ^ (k + 3)) = 0 := by
  refine xiMassCriticalConeAtom_eq_zero_of_gt ?_
  exact lt_of_lt_of_le hp (Nat.le_self_pow (by omega) _)

/-! ## The three layers of the cone -/

/-- The true-prime part of the cone. -/
def xiMassCriticalTruePrimeCone (a sigma d u : ℝ) : ℂ :=
  ∑' p : Nat.Primes, xiMassCriticalConeAtom a sigma d u (p : ℕ)

/-- The prime-square part of the cone. -/
def xiMassCriticalSquareCone (a sigma d u : ℝ) : ℂ :=
  ∑' p : Nat.Primes, xiMassCriticalConeAtom a sigma d u ((p : ℕ) ^ 2)

/-- The high prime-power part of the cone. -/
def xiMassCriticalHighCone (a sigma d u : ℝ) : ℂ :=
  ∑' (p : Nat.Primes) (k : ℕ), xiMassCriticalConeAtom a sigma d u ((p : ℕ) ^ (k + 3))

theorem summable_highCone_prime (a sigma d u : ℝ) :
    Summable (fun p : Nat.Primes =>
      ∑' k : ℕ, xiMassCriticalConeAtom a sigma d u ((p : ℕ) ^ (k + 3))) := by
  classical
  refine summable_of_hasFiniteSupport ?_
  have hpre : (Function.support (fun p : Nat.Primes =>
      ∑' k : ℕ, xiMassCriticalConeAtom a sigma d u ((p : ℕ) ^ (k + 3))))
      ⊆ (fun p : Nat.Primes => (p : ℕ)) ⁻¹'
        (Set.Iic ⌊Real.exp (d * u / (d - 1 / 2))⌋₊) := by
    intro p hp
    by_contra hcon
    apply hp
    simp only [Set.mem_preimage, Set.mem_Iic, not_le] at hcon
    have hz : ∀ k : ℕ, xiMassCriticalConeAtom a sigma d u ((p : ℕ) ^ (k + 3)) = 0 :=
      fun k => coneAtom_high_eq_zero_of_gt hcon
    simp only [hz]
    exact tsum_zero
  refine Set.Finite.subset ?_ hpre
  refine Set.Finite.preimage ?_ (Set.finite_Iic _)
  intro p _ q _ hpq
  exact Subtype.ext hpq

theorem summable_coneAtom_prime (a sigma d u : ℝ) :
    Summable (fun p : Nat.Primes => xiMassCriticalConeAtom a sigma d u (p : ℕ)) := by
  simpa using summable_coneAtom_primePow a sigma d u (le_refl 1)

/-- **The exponent split at one prime.** -/
theorem tsum_coneAtom_exponent_split (a sigma d u : ℝ) (p : Nat.Primes) :
    (∑' k : ℕ, xiMassCriticalConeAtom a sigma d u ((p : ℕ) ^ (k + 1)))
      = xiMassCriticalConeAtom a sigma d u (p : ℕ)
        + (xiMassCriticalConeAtom a sigma d u ((p : ℕ) ^ 2)
          + ∑' k : ℕ, xiMassCriticalConeAtom a sigma d u ((p : ℕ) ^ (k + 3))) := by
  have h0 : Summable (fun k : ℕ =>
      xiMassCriticalConeAtom a sigma d u ((p : ℕ) ^ (k + 1))) := by
    simpa using summable_coneAtom_exponent a sigma d u p 0
  have h1 : Summable (fun k : ℕ =>
      xiMassCriticalConeAtom a sigma d u ((p : ℕ) ^ (k + 2))) := by
    simpa [Nat.add_assoc] using summable_coneAtom_exponent a sigma d u p 1
  rw [h0.tsum_eq_zero_add]
  have hstep : (∑' k : ℕ, xiMassCriticalConeAtom a sigma d u ((p : ℕ) ^ (k + 1 + 1)))
      = xiMassCriticalConeAtom a sigma d u ((p : ℕ) ^ 2)
        + ∑' k : ℕ, xiMassCriticalConeAtom a sigma d u ((p : ℕ) ^ (k + 1 + 1 + 1)) := by
    have := h1.tsum_eq_zero_add
    simpa [Nat.add_assoc] using this
  rw [hstep]
  norm_num

/-- **The three-layer split of the cone.** -/
theorem tsum_xiMassCriticalConeAtom_eq_three (a sigma d u : ℝ) :
    (∑' n : ℕ, xiMassCriticalConeAtom a sigma d u n)
      = xiMassCriticalTruePrimeCone a sigma d u
        + xiMassCriticalSquareCone a sigma d u
        + xiMassCriticalHighCone a sigma d u := by
  rw [tsum_xiMassCriticalConeAtom_eq_primePower,
    tsum_congr (tsum_coneAtom_exponent_split a sigma d u)]
  rw [Summable.tsum_add (summable_coneAtom_prime a sigma d u)
    ((summable_coneAtom_primePow a sigma d u (by norm_num : 1 ≤ 2)).add
      (summable_highCone_prime a sigma d u))]
  rw [Summable.tsum_add (summable_coneAtom_primePow a sigma d u (by norm_num : 1 ≤ 2))
    (summable_highCone_prime a sigma d u)]
  rw [xiMassCriticalTruePrimeCone, xiMassCriticalSquareCone, xiMassCriticalHighCone]
  ring

/-! ## Bounding the two higher layers -/

theorem norm_xiMassCriticalConeAtom_le (a sigma d u : ℝ) (n : ℕ) :
    ‖xiMassCriticalConeAtom a sigma d u n‖
      ≤ ‖xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) n‖ := by
  classical
  rw [xiMassCriticalConeAtom]
  split_ifs
  · exact le_refl _
  · rw [norm_zero]
    exact norm_nonneg _

theorem summable_coneAtom_high_prod {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (d u : ℝ) :
    Summable (fun pk : Nat.Primes × ℕ =>
      xiMassCriticalConeAtom a sigma d u ((pk.1 : ℕ) ^ (pk.2 + 3))) := by
  refine Summable.of_norm ?_
  refine (summable_norm_xiMassHighPrimePowerAtom ha hsigma u).of_nonneg_of_le
    (fun _ => norm_nonneg _) ?_
  rintro ⟨p, k⟩
  exact norm_xiMassCriticalConeAtom_le a sigma d u _

/-- **The high prime-power layer of the cone is uniformly bounded.** -/
theorem norm_xiMassCriticalHighCone_le {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma)
    (d u : ℝ) :
    ‖xiMassCriticalHighCone a sigma d u‖
      ≤ (∑' pk : Nat.Primes × ℕ, xiMassPrimePowerCriticalWeight pk.1 (pk.2 + 2))
        * (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by
  have hprod := summable_coneAtom_high_prod ha hsigma d u
  have hslice : ∀ p : Nat.Primes, Summable (fun k : ℕ =>
      xiMassCriticalConeAtom a sigma d u ((p : ℕ) ^ (k + 3))) := by
    intro p
    simpa [Nat.add_assoc] using summable_coneAtom_exponent a sigma d u p 2
  have hcone : xiMassCriticalHighCone a sigma d u
      = ∑' pk : Nat.Primes × ℕ,
          xiMassCriticalConeAtom a sigma d u ((pk.1 : ℕ) ^ (pk.2 + 3)) := by
    rw [xiMassCriticalHighCone, hprod.tsum_prod' hslice]
  have hnorm := summable_norm_xiMassHighPrimePowerAtom ha hsigma u
  have hmajorant : Summable (fun pk : Nat.Primes × ℕ =>
      xiMassPrimePowerCriticalWeight pk.1 (pk.2 + 2) *
        (∫ x : ℝ, Real.exp (-(sigma * |x|)))) :=
    summable_xiMassPrimePowerCriticalWeight_high.mul_right _
  have hconeNorm : Summable (fun pk : Nat.Primes × ℕ =>
      ‖xiMassCriticalConeAtom a sigma d u ((pk.1 : ℕ) ^ (pk.2 + 3))‖) :=
    hnorm.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun pk => norm_xiMassCriticalConeAtom_le a sigma d u _)
  rw [hcone]
  calc ‖∑' pk : Nat.Primes × ℕ,
        xiMassCriticalConeAtom a sigma d u ((pk.1 : ℕ) ^ (pk.2 + 3))‖
      ≤ ∑' pk : Nat.Primes × ℕ,
          ‖xiMassCriticalConeAtom a sigma d u ((pk.1 : ℕ) ^ (pk.2 + 3))‖ :=
        norm_tsum_le_tsum_norm hconeNorm
    _ ≤ ∑' pk : Nat.Primes × ℕ,
          xiMassPrimePowerCriticalWeight pk.1 (pk.2 + 2) *
            (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by
        refine hconeNorm.tsum_le_tsum ?_ hmajorant
        rintro ⟨p, k⟩
        refine le_trans (norm_xiMassCriticalConeAtom_le a sigma d u _) ?_
        simpa only [Prod.fst, Prod.snd, add_assoc] using
          norm_xiMassCenteredPrimeAtom_primePower_le ha hsigma u p (k + 2)
    _ = _ := tsum_mul_right

/-! ## The prime-square layer of the cone -/

theorem summable_coneAtom_square (a sigma d u : ℝ) :
    Summable (fun p : Nat.Primes => xiMassCriticalConeAtom a sigma d u ((p : ℕ) ^ 2)) :=
  summable_coneAtom_primePow a sigma d u (by norm_num)

/-- **The square layer splits at the cone.** -/
theorem xiMassPrimeSquareLayer_eq_cone_add_tail {a sigma d u : ℝ}
    (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma) (hu : 0 ≤ u) :
    xiMassPrimeSquareLayer a ((sigma : ℂ) + u * I)
      = xiMassCriticalSquareCone a sigma d u
        + xiMassCriticalPrimeSquareConeTail a sigma d u := by
  classical
  rw [xiMassPrimeSquareLayer, xiMassCriticalSquareCone, xiMassCriticalPrimeSquareConeTail,
    ← Summable.tsum_add (summable_coneAtom_square a sigma d u)
      (summable_xiMassCriticalPrimeSquareConeTail hdhalf hda hsigma hu)]
  refine tsum_congr fun p => ?_
  have hppos : (0 : ℝ) < ((((p : ℕ) ^ 2 : ℕ)) : ℝ) := by
    have : 0 < ((p : ℕ) ^ 2 : ℕ) := pow_pos p.prop.pos 2
    exact_mod_cast this
  by_cases hle : ((((p : ℕ) ^ 2 : ℕ)) : ℝ) ≤ Real.exp (d * u / (d - 1 / 2))
  · rw [xiMassCriticalConeAtom, if_pos hle, if_neg (by
      rw [not_lt]
      exact (Real.log_le_iff_le_exp hppos).2 hle)]
    ring
  · rw [xiMassCriticalConeAtom, if_neg hle, if_pos (by
      rw [← not_le, Real.log_le_iff_le_exp hppos]
      exact hle)]
    ring

/-- **The prime-square layer of the cone is uniformly bounded.** -/
theorem exists_norm_xiMassCriticalSquareCone_bound {a sigma d : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a) :
    ∃ B : ℝ, ∀ u : ℝ, 0 ≤ u → ‖xiMassCriticalSquareCone a sigma d u‖ ≤ B := by
  obtain ⟨B₀, hB₀⟩ := exists_norm_xiMassPrimeSquareLayer_vertical_bound ha hsigma
  refine ⟨B₀ + (∑' p : Nat.Primes, xiMassPrimeSquareEulerWeight (1 / 2) p) *
    (∫ x : ℝ, Real.exp (-(sigma * |x|))), fun u hu => ?_⟩
  have hsplit := xiMassPrimeSquareLayer_eq_cone_add_tail hdhalf hda hsigma hu
  have hsolve : xiMassCriticalSquareCone a sigma d u
      = xiMassPrimeSquareLayer a ((sigma : ℂ) + u * I)
        - xiMassCriticalPrimeSquareConeTail a sigma d u := by
    rw [hsplit]; ring
  rw [hsolve]
  exact (norm_sub_le _ _).trans
    (add_le_add (hB₀ u) (norm_xiMassCriticalPrimeSquareConeTail_le hdhalf hda hsigma hu))

/-! ## The true-prime cone criterion -/

/-- **The exact three-layer form of the moving prime cone.** -/
theorem xiMassCriticalPrimeAtomConeSum_eq_three (a sigma d u : ℝ) :
    xiMassCriticalPrimeAtomConeSum a sigma d u
      = xiMassCriticalTruePrimeCone a sigma d u
        + xiMassCriticalSquareCone a sigma d u
        + xiMassCriticalHighCone a sigma d u := by
  rw [xiMassCriticalPrimeAtomConeSum_eq_tsum_coneAtom,
    tsum_xiMassCriticalConeAtom_eq_three]

/-- The line-bound property of the true-prime cone. -/
def XiMassCriticalTruePrimeConeLineBound (a sigma d : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → ‖xiMassCriticalTruePrimeCone a sigma d u‖ ≤ C

/-- **(6.1) The finite true-prime cone criterion, line-bound form.**  Removing the prime-square and
higher prime-power layers changes the moving cone by one uniformly bounded family. -/
theorem xiMassCriticalPrimeAtomConeLineBound_iff_truePrimeCone {a sigma d : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a) :
    XiMassCriticalPrimeAtomConeLineBound a sigma d
      ↔ XiMassCriticalTruePrimeConeLineBound a sigma d := by
  obtain ⟨B, hB⟩ := exists_norm_xiMassCriticalSquareCone_bound ha hsigma hdhalf hda
  set D : ℝ := (∑' pk : Nat.Primes × ℕ, xiMassPrimePowerCriticalWeight pk.1 (pk.2 + 2))
    * (∫ x : ℝ, Real.exp (-(sigma * |x|))) with hD
  have hhigh : ∀ u : ℝ, ‖xiMassCriticalHighCone a sigma d u‖ ≤ D := fun u => by
    simpa only [hD] using norm_xiMassCriticalHighCone_le ha hsigma d u
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + (B + D), fun u hu => ?_⟩
    have hsplit := xiMassCriticalPrimeAtomConeSum_eq_three a sigma d u
    have hsolve : xiMassCriticalTruePrimeCone a sigma d u
        = xiMassCriticalPrimeAtomConeSum a sigma d u
          - (xiMassCriticalSquareCone a sigma d u + xiMassCriticalHighCone a sigma d u) := by
      rw [hsplit]; ring
    rw [hsolve]
    exact (norm_sub_le _ _).trans
      (add_le_add (hC u hu) ((norm_add_le _ _).trans (add_le_add (hB u hu) (hhigh u))))
  · rintro ⟨C, hC⟩
    refine ⟨C + (B + D), fun u hu => ?_⟩
    rw [xiMassCriticalPrimeAtomConeSum_eq_three]
    calc ‖xiMassCriticalTruePrimeCone a sigma d u + xiMassCriticalSquareCone a sigma d u
          + xiMassCriticalHighCone a sigma d u‖
        ≤ ‖xiMassCriticalTruePrimeCone a sigma d u + xiMassCriticalSquareCone a sigma d u‖
            + ‖xiMassCriticalHighCone a sigma d u‖ := norm_add_le _ _
      _ ≤ (‖xiMassCriticalTruePrimeCone a sigma d u‖
            + ‖xiMassCriticalSquareCone a sigma d u‖) + ‖xiMassCriticalHighCone a sigma d u‖ := by
          linarith [norm_add_le (xiMassCriticalTruePrimeCone a sigma d u)
            (xiMassCriticalSquareCone a sigma d u)]
      _ ≤ (C + B) + D := add_le_add (add_le_add (hC u hu) (hB u hu)) (hhigh u)
      _ = C + (B + D) := by ring

/-- **(6.1) The finite true-prime cone criterion.**  RH is equivalent to uniform boundedness of the
moving cone supported on true primes only. -/
theorem riemannHypothesis_iff_xiMassCriticalTruePrimeConeLineBound
    {a c sigma d : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a) :
    RiemannHypothesis ↔ XiMassCriticalTruePrimeConeLineBound a sigma d :=
  (riemannHypothesis_iff_xiMassCriticalPrimeAtomConeLineBound hhalf hca hsigma hdhalf hda).trans
    (xiMassCriticalPrimeAtomConeLineBound_iff_truePrimeCone
      (lt_trans (lt_trans (by norm_num : (0:ℝ) < 1/2) hdhalf) hda) hsigma hdhalf hda)

/-! ## The true-prime cone as a finite sum -/

/-- **The true-prime cone is a finite sum over the cone.** -/
theorem xiMassCriticalTruePrimeCone_eq_finsetSum (a sigma d u : ℝ) :
    xiMassCriticalTruePrimeCone a sigma d u
      = ∑ k ∈ (Finset.range (⌊Real.exp (d * u / (d - 1 / 2))⌋₊ - 1)).filter
          (fun k => Nat.Prime (k + 2)),
        xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2) := by
  classical
  have hsub : (∑' p : Nat.Primes, xiMassCriticalConeAtom a sigma d u (p : ℕ))
      = ∑' n : ℕ, Set.indicator {n : ℕ | n.Prime}
          (xiMassCriticalConeAtom a sigma d u) n := by
    exact tsum_subtype {n : ℕ | n.Prime} (xiMassCriticalConeAtom a sigma d u)
  rw [xiMassCriticalTruePrimeCone, hsub]
  have hzero : ∀ n ∉ (Finset.Icc 2 ⌊Real.exp (d * u / (d - 1 / 2))⌋₊).filter
      (fun n => Nat.Prime n),
      Set.indicator {n : ℕ | n.Prime} (xiMassCriticalConeAtom a sigma d u) n = 0 := by
    intro n hn
    rw [Finset.mem_filter, not_and_or] at hn
    rcases hn with hn | hn
    · rw [Finset.mem_Icc, not_and_or] at hn
      rw [Set.indicator_apply]
      split_ifs with hp
      · rcases hn with hn | hn
        · exact xiMassCriticalConeAtom_eq_zero_of_lt_two (by omega)
        · exact xiMassCriticalConeAtom_eq_zero_of_gt (by omega)
      · rfl
    · rw [Set.indicator_apply, if_neg (by simpa using hn)]
  rw [tsum_eq_sum hzero]
  have hval : ∀ n ∈ (Finset.Icc 2 ⌊Real.exp (d * u / (d - 1 / 2))⌋₊).filter
      (fun n => Nat.Prime n),
      Set.indicator {n : ℕ | n.Prime} (xiMassCriticalConeAtom a sigma d u) n
        = xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) n := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Set.indicator_apply, if_pos (by simpa using hn.2), xiMassCriticalConeAtom, if_pos]
    exact le_trans (Nat.cast_le.2 hn.1.2) (Nat.floor_le (Real.exp_pos _).le)
  rw [Finset.sum_congr rfl hval]
  refine (Finset.sum_nbij' (i := fun k => k + 2) (j := fun n => n - 2) ?_ ?_ ?_ ?_ ?_).symm
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, hk.2⟩
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have : n - 2 + 2 = n := by omega
    rw [this]
    exact hn.2
  · intro k _
    omega
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    omega
  · intro k _
    rfl

/-! ## The exact prime-supported Dirichlet face -/

/-- Each critical atom times the analytic mass propagator is genuinely integrable. -/
theorem integrable_xiMassAnalyticTest_mul_criticalAtom
    {a sigma u : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (c : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ =>
      xiMassAnalyticTest a ((sigma : ℂ) + u * I) (x : ℂ) *
        (((c * Real.exp (-Real.log ((n : ℝ) + 2) / 2) : ℝ) : ℂ) *
          Complex.exp (-(I * (Real.log ((n : ℝ) + 2) : ℂ) * (x : ℂ))))) := by
  let C : ℝ := |c| * Real.exp (-Real.log ((n : ℝ) + 2) / 2)
  apply Integrable.mono' ((integrable_exp_neg_mul_abs hsigma).const_mul C)
  · have hg : Continuous (fun x : ℝ =>
        xiMassAnalyticTest a ((sigma : ℂ) + u * I) (x : ℂ)) := by
      rw [continuous_iff_continuousAt]
      intro x
      have hz : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
        change HasDerivAt (⇑Complex.ofRealCLM) 1 x
        exact Complex.ofRealCLM.hasDerivAt
      have hmem : (x : ℂ) ∈ xiMassStrip a := by
        change |((x : ℂ)).im| < a
        simpa using ha
      exact ((hasDerivAt_xiMassAnalyticTest ha _ hmem).comp x hz).continuousAt
    exact (hg.mul (continuous_const.mul
      (Complex.continuous_exp.comp (by fun_prop)))).aestronglyMeasurable
  · refine ae_of_all _ fun x => ?_
    have hmem : (x : ℂ) ∈ xiMassStrip a := by
      change |((x : ℂ)).im| < a
      simpa using ha
    have hg := norm_xiMassAnalyticTest_le
      (τ := ((sigma : ℂ) + u * I)) ha (by simpa using hsigma.le) hmem
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp]
    have hphase :
        (-(I * (Real.log ((n : ℝ) + 2) : ℂ) * (x : ℂ))).re = 0 := by simp
    rw [hphase, Real.exp_zero, mul_one]
    have hg' : ‖xiMassAnalyticTest a ((sigma : ℂ) + u * I) (x : ℂ)‖ ≤
        Real.exp (-(sigma * |x|)) := by
      simpa using hg
    dsimp only [C]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-(sigma * |x|)) *
          (|c| * Real.exp (-Real.log ((n : ℝ) + 2) / 2)) :=
        mul_le_mul_of_nonneg_right hg'
          (mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))
      _ = _ := by ring

/-- The moving finite true-prime Dirichlet polynomial. -/
def xiMassCriticalTruePrimeDirichletConePolynomial (d u x : ℝ) : ℂ :=
  ∑ k ∈ (Finset.range (⌊Real.exp (d * u / (d - 1 / 2))⌋₊ - 1)).filter
      (fun k => Nat.Prime (k + 2)),
    (((ArithmeticFunction.vonMangoldt (k + 2) *
      Real.exp (-Real.log ((k : ℝ) + 2) / 2) : ℝ) : ℂ) *
      Complex.exp (-(I * (Real.log ((k : ℝ) + 2) : ℂ) * (x : ℂ))))

/-- **(7.1) The exact prime-supported Dirichlet face.**  The true-prime cone is the integral
pairing of the mass propagator with its moving finite prime Dirichlet polynomial. -/
theorem xiMassCriticalTruePrimeCone_eq_integral_dirichlet {a sigma d u : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) :
    xiMassCriticalTruePrimeCone a sigma d u
      = ∫ x : ℝ, xiMassAnalyticTest a ((sigma : ℂ) + u * I) (x : ℂ) *
          xiMassCriticalTruePrimeDirichletConePolynomial d u x := by
  classical
  rw [xiMassCriticalTruePrimeCone_eq_finsetSum]
  have hback : ∀ k ∈ (Finset.range (⌊Real.exp (d * u / (d - 1 / 2))⌋₊ - 1)).filter
      (fun k => Nat.Prime (k + 2)),
      xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)
        = ((ArithmeticFunction.vonMangoldt (k + 2) : ℝ) : ℂ) *
          xiMassCriticalDampedFourierProfile a sigma u (Real.log ((k : ℝ) + 2)) := by
    intro k _
    have hcast : ((k : ℝ) + 2) = ((k + 2 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast]
    exact (vonMangoldt_mul_dampedProfile_eq_centeredPrimeAtom a sigma u (by omega)).symm
  rw [Finset.sum_congr rfl hback]
  simp only [xiMassCriticalTruePrimeDirichletConePolynomial]
  simp only [xiMassCriticalDampedFourierProfile, stripFourier]
  simp_rw [Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    have hfun : (fun x : ℝ =>
        xiMassAnalyticTest a ((sigma : ℂ) + u * I) (x : ℂ) *
          (((ArithmeticFunction.vonMangoldt (k + 2) *
            Real.exp (-Real.log ((k : ℝ) + 2) / 2) : ℝ) : ℂ) *
            Complex.exp (-(I * (Real.log ((k : ℝ) + 2) : ℂ) * (x : ℂ))))) =
        fun x : ℝ =>
          ((ArithmeticFunction.vonMangoldt (k + 2) : ℝ) : ℂ) *
            (Real.exp (-Real.log ((k : ℝ) + 2) / 2) : ℂ) *
            (xiMassAnalyticTest a ((sigma : ℂ) + u * I) (x : ℂ) *
              Complex.exp (-(I * (Real.log ((k : ℝ) + 2) : ℂ) * (x : ℂ)))) := by
      funext x
      push_cast
      ring
    rw [hfun, MeasureTheory.integral_const_mul]
    ring
  · intro k _
    exact integrable_xiMassAnalyticTest_mul_criticalAtom ha hsigma
      (ArithmeticFunction.vonMangoldt (k + 2)) k

/-- Uniform bound on the exact prime mass/Dirichlet-polynomial cone pairing. -/
def XiMassCriticalTruePrimeDirichletConePairingLineBound (a sigma d : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    ‖∫ x : ℝ, xiMassAnalyticTest a ((sigma : ℂ) + u * I) (x : ℂ) *
      xiMassCriticalTruePrimeDirichletConePolynomial d u x‖ ≤ C

theorem xiMassCriticalTruePrimeConeLineBound_iff_dirichletPairing
    {a sigma d : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    XiMassCriticalTruePrimeConeLineBound a sigma d
      ↔ XiMassCriticalTruePrimeDirichletConePairingLineBound a sigma d := by
  constructor <;> rintro ⟨C, hC⟩ <;> refine ⟨C, fun u hu => ?_⟩
  · rw [← xiMassCriticalTruePrimeCone_eq_integral_dirichlet ha hsigma]
    exact hC u hu
  · rw [xiMassCriticalTruePrimeCone_eq_integral_dirichlet ha hsigma]
    exact hC u hu

/-- **(7.1) The prime-supported Dirichlet exact open core.**  RH is equivalent to uniform
boundedness of the exact finite mass/true-prime-Dirichlet pairing on one nonnegative vertical
cone. -/
theorem riemannHypothesis_iff_xiMassCriticalTruePrimeDirichletConePairingLineBound
    {a c sigma d : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a) :
    RiemannHypothesis ↔ XiMassCriticalTruePrimeDirichletConePairingLineBound a sigma d := by
  have ha : 0 < a := lt_trans (by norm_num) (lt_trans hdhalf hda)
  exact (riemannHypothesis_iff_xiMassCriticalTruePrimeConeLineBound
    hhalf hca hsigma hdhalf hda).trans
      (xiMassCriticalTruePrimeConeLineBound_iff_dirichletPairing ha hsigma)

/-! ## The prime-log quadrature defect -/

/-- The cone edge in the logarithmic variable. -/
noncomputable def xiMassCriticalConeEdge (d u : ℝ) : ℝ :=
  Real.log ((⌊Real.exp (d * u / (d - 1 / 2))⌋₊ : ℝ) + 1)

theorem xiMassCriticalConeEdge_ge (d u : ℝ) :
    d * u / (d - 1 / 2) ≤ xiMassCriticalConeEdge d u := by
  have hupper : Real.exp (d * u / (d - 1 / 2))
      < ((⌊Real.exp (d * u / (d - 1 / 2))⌋₊ : ℝ) + 1) := Nat.lt_floor_add_one _
  have hlog := Real.log_lt_log (Real.exp_pos _) hupper
  rw [Real.log_exp] at hlog
  exact hlog.le

/-- **(9.1) The prime-log quadrature defect.**  The true-prime cone minus the continuum integral of
the growing profile over the cone. -/
noncomputable def xiMassCriticalPrimeQuadratureDefect (a sigma d u : ℝ) : ℂ :=
  xiMassCriticalTruePrimeCone a sigma d u
    - ∫ h in (0 : ℝ)..xiMassCriticalConeEdge d u,
        xiMassCriticalGrowingFourierProfile a sigma u h

/-- The finite true-prime logarithmic Stieltjes measure inside the cone,
`dΘ = ∑_{p ≤ M} (log p) δ_{log p}`. -/
noncomputable def xiMassCriticalPrimeLogMeasure (d u : ℝ) : Measure ℝ := by
  classical
  exact ∑ k ∈ (Finset.range (⌊Real.exp (d * u / (d - 1 / 2))⌋₊ - 1)).filter
      (fun k => Nat.Prime (k + 2)),
    (ENNReal.ofReal (Real.log ((k : ℝ) + 2))) • Measure.dirac (Real.log ((k : ℝ) + 2))

/-- **(9.1) The atomic Stieltjes pairing is the true-prime cone.** -/
theorem integral_dampedProfile_primeLogMeasure (a sigma d u : ℝ) :
    (∫ h, xiMassCriticalDampedFourierProfile a sigma u h
        ∂(xiMassCriticalPrimeLogMeasure d u))
      = xiMassCriticalTruePrimeCone a sigma d u := by
  classical
  rw [xiMassCriticalPrimeLogMeasure,
    MeasureTheory.integral_finsetSum_measure (fun i _ => by
      refine MeasureTheory.Integrable.smul_measure ?_ (by simp)
      exact MeasureTheory.integrable_dirac (by simp [enorm_eq_nnnorm]))]
  rw [xiMassCriticalTruePrimeCone_eq_finsetSum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_filter] at hk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hlog : 0 ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith)
  rw [MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac,
    ENNReal.toReal_ofReal hlog]
  have hcast : ((k : ℝ) + 2) = ((k + 2 : ℕ) : ℝ) := by push_cast; ring
  rw [hcast, ← vonMangoldt_mul_dampedProfile_eq_centeredPrimeAtom a sigma u (n := k + 2)
    (by omega), ArithmeticFunction.vonMangoldt_apply_prime hk.2]
  simp [Complex.real_smul]

/-- Uniform bound on the prime-log quadrature defect. -/
def XiMassCriticalPrimeQuadratureDefectLineBound (a sigma d : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → ‖xiMassCriticalPrimeQuadratureDefect a sigma d u‖ ≤ C

/-- **(9.2) The quadrature-defect criterion.**  RH is equivalent to uniform boundedness of the
critical quadrature defect between the true-prime logarithmic measure and its continuum density,
tested against one outgoing mass family. -/
theorem xiMassCriticalTruePrimeConeLineBound_iff_quadratureDefect {a sigma d : ℝ}
    (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a) :
    XiMassCriticalTruePrimeConeLineBound a sigma d
      ↔ XiMassCriticalPrimeQuadratureDefectLineBound a sigma d := by
  set B : ℝ := 2 * Real.pi +
    2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) / (d - 1 / 2) +
    2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) with hB
  have hcont : ∀ u : ℝ, 0 ≤ u →
      ‖∫ h in (0 : ℝ)..xiMassCriticalConeEdge d u,
        xiMassCriticalGrowingFourierProfile a sigma u h‖ ≤ B := by
    intro u hu
    simpa only [hB] using norm_integral_xiMassCriticalGrowingFourierProfile_at_cone_le
      hdhalf hda hsigma hu (xiMassCriticalConeEdge_ge d u)
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u hu => ?_⟩
    rw [xiMassCriticalPrimeQuadratureDefect]
    exact (norm_sub_le _ _).trans (add_le_add (hC u hu) (hcont u hu))
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u hu => ?_⟩
    have hsolve : xiMassCriticalTruePrimeCone a sigma d u
        = xiMassCriticalPrimeQuadratureDefect a sigma d u
          + ∫ h in (0 : ℝ)..xiMassCriticalConeEdge d u,
              xiMassCriticalGrowingFourierProfile a sigma u h := by
      rw [xiMassCriticalPrimeQuadratureDefect]
      ring
    rw [hsolve]
    exact (norm_add_le _ _).trans (add_le_add (hC u hu) (hcont u hu))

/-- **(9.2) The exact quadrature-defect open core.** -/
theorem riemannHypothesis_iff_xiMassCriticalPrimeQuadratureDefectLineBound
    {a c sigma d : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a) :
    RiemannHypothesis ↔ XiMassCriticalPrimeQuadratureDefectLineBound a sigma d :=
  (riemannHypothesis_iff_xiMassCriticalTruePrimeConeLineBound hhalf hca hsigma hdhalf hda).trans
    (xiMassCriticalTruePrimeConeLineBound_iff_quadratureDefect hsigma hdhalf hda)

/-! ## The true-prime cone and its complement -/

/-- The cone sum restricted to true primes. -/
def xiMassCriticalTruePrimeConeSum (a sigma d u : ℝ) : ℂ :=
  ∑ k ∈ (Finset.range (⌊Real.exp (d * u / (d - 1 / 2))⌋₊ - 1)).filter
      (fun k => Nat.Prime (k + 2)),
    xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)

/-- The cone sum restricted to the higher prime powers. -/
def xiMassCriticalHigherPrimeConeSum (a sigma d u : ℝ) : ℂ :=
  ∑ k ∈ (Finset.range (⌊Real.exp (d * u / (d - 1 / 2))⌋₊ - 1)).filter
      (fun k => ¬ Nat.Prime (k + 2)),
    xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)

/-- **The exact cone split.**  Every cone term is either a true prime or a higher prime power. -/
theorem xiMassCriticalPrimeAtomConeSum_eq_truePrime_add_higher (a sigma d u : ℝ) :
    xiMassCriticalPrimeAtomConeSum a sigma d u
      = xiMassCriticalTruePrimeConeSum a sigma d u
        + xiMassCriticalHigherPrimeConeSum a sigma d u := by
  classical
  rw [xiMassCriticalPrimeAtomConeSum_eq_sum_centeredAtom,
    xiMassCriticalTruePrimeConeSum, xiMassCriticalHigherPrimeConeSum]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- **The line-bound transfer.**  If the higher prime-power part of the cone is uniformly bounded,
the prime-atom cone is uniformly bounded exactly when the true-prime cone is. -/
theorem primeAtomConeLineBound_iff_truePrime {a sigma d : ℝ} {B : ℝ}
    (hB : ∀ u : ℝ, 0 ≤ u → ‖xiMassCriticalHigherPrimeConeSum a sigma d u‖ ≤ B) :
    XiMassCriticalPrimeAtomConeLineBound a sigma d
      ↔ ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
          ‖xiMassCriticalTruePrimeConeSum a sigma d u‖ ≤ C := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u hu => ?_⟩
    have hsplit := xiMassCriticalPrimeAtomConeSum_eq_truePrime_add_higher a sigma d u
    have hsolve : xiMassCriticalTruePrimeConeSum a sigma d u
        = xiMassCriticalPrimeAtomConeSum a sigma d u
          - xiMassCriticalHigherPrimeConeSum a sigma d u := by
      rw [hsplit]; ring
    rw [hsolve]
    exact (norm_sub_le _ _).trans (add_le_add (hC u hu) (hB u hu))
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u hu => ?_⟩
    rw [xiMassCriticalPrimeAtomConeSum_eq_truePrime_add_higher]
    exact (norm_add_le _ _).trans (add_le_add (hC u hu) (hB u hu))

end

end RHTower
