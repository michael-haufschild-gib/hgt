import GaloisForLFunctions.RHTower.PutnamPeriodizationLimits
import GaloisForLFunctions.RHTower.PutnamExponentMonoid

/-!
# The jump of the periodised kernel is never zero

The difference between the left and the right limit of the periodisation at the origin is

`∑_{k ∈ ℤ} [e^{kP} ∈ ℤ] · e^{-(½+ia)kP}` ,

and the indicator is supported exactly on the exponent monoid, which is `k₀ℕ` by the cyclicity
theorem.  The sum is therefore a geometric series of ratio `e^{-(½+ia)k₀P}`, of modulus
`e^{-k₀P/2} < 1`, so it equals `(1 - ratio)^{-1}` and in particular never vanishes.
-/

open Complex Filter Topology Set

noncomputable section

namespace RHTower

/-- The `k`-th jump term of the periodisation at the origin. -/
def putnamJumpTerm (a d : ℝ) (k : ℤ) : ℂ :=
  ((⌊Real.exp ((k : ℝ) * putnamPeriod d)⌋ - ⌈Real.exp ((k : ℝ) * putnamPeriod d)⌉ + 1 : ℤ) : ℂ) *
    Complex.exp (-(1 / 2 + (a : ℂ) * I) * ((k : ℝ) * putnamPeriod d))

theorem putnamJumpTerm_eq_zero_of_neg {a d : ℝ} (hd : 0 < d) {k : ℤ} (hk : k < 0) :
    putnamJumpTerm a d k = 0 := by
  have hP : 0 < putnamPeriod d := putnamPeriod_pos hd
  have hneg : ((k : ℝ) * putnamPeriod d) < 0 := by
    have : (k : ℝ) < 0 := by exact_mod_cast hk
    nlinarith
  have hlt : Real.exp ((k : ℝ) * putnamPeriod d) < 1 := by
    simpa using Real.exp_lt_one_iff.mpr hneg
  have hpos : (0 : ℝ) < Real.exp ((k : ℝ) * putnamPeriod d) := Real.exp_pos _
  have hfl : ⌊Real.exp ((k : ℝ) * putnamPeriod d)⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    exact ⟨hpos.le, hlt⟩
  have hce : ⌈Real.exp ((k : ℝ) * putnamPeriod d)⌉ = 1 := by
    refine Int.ceil_eq_iff.mpr ⟨?_, ?_⟩
    · push_cast
      linarith
    · push_cast
      linarith
  rw [putnamJumpTerm, hfl, hce]
  norm_num

theorem putnamJumpTerm_of_mem {a d : ℝ} {k : ℤ} (hk : 0 ≤ k)
    (hmem : k.toNat ∈ expNatSet (putnamPeriod d)) :
    putnamJumpTerm a d k
      = Complex.exp (-(1 / 2 + (a : ℂ) * I) * ((k : ℝ) * putnamPeriod d)) := by
  obtain ⟨m, hm⟩ := hmem
  have hcast : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk
  rw [hcast] at hm
  have hfl : ⌊Real.exp ((k : ℝ) * putnamPeriod d)⌋ = (m : ℤ) := by
    rw [hm]
    simp
  have hce : ⌈Real.exp ((k : ℝ) * putnamPeriod d)⌉ = (m : ℤ) := by
    rw [hm]
    simp
  rw [putnamJumpTerm, hfl, hce]
  norm_num

theorem putnamJumpTerm_eq_zero_of_notMem {a d : ℝ} {k : ℤ} (hk : 0 ≤ k)
    (hmem : k.toNat ∉ expNatSet (putnamPeriod d)) :
    putnamJumpTerm a d k = 0 := by
  have hnotint : Real.exp ((k : ℝ) * putnamPeriod d) ∉ Set.range ((↑) : ℤ → ℝ) := by
    rintro ⟨n, hn⟩
    have hpos : (0 : ℝ) < Real.exp ((k : ℝ) * putnamPeriod d) := Real.exp_pos _
    have hn0 : (0 : ℤ) < n := by
      by_contra hcon
      have hle : n ≤ 0 := not_lt.mp hcon
      have hle' : ((n : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hle
      rw [hn] at hle'
      linarith
    refine hmem ⟨n.toNat, ?_⟩
    have hcast : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk
    rw [hcast, ← hn]
    exact_mod_cast (Int.toNat_of_nonneg hn0.le).symm
  have hce : ⌈Real.exp ((k : ℝ) * putnamPeriod d)⌉
      = ⌊Real.exp ((k : ℝ) * putnamPeriod d)⌋ + 1 :=
    (Int.ceil_eq_floor_add_one_iff_notMem _).mpr hnotint
  rw [putnamJumpTerm, hce]
  norm_num

theorem putnamJumpTerm_zero (a d : ℝ) : putnamJumpTerm a d 0 = 1 := by
  rw [putnamJumpTerm]
  norm_num

theorem mul_mem_expNatSet {P : ℝ} {k₀ : ℕ} (h : k₀ ∈ expNatSet P) (j : ℕ) :
    k₀ * j ∈ expNatSet P := by
  induction j with
  | zero => simpa using zero_mem_expNatSet P
  | succ j ih =>
      have : k₀ * (j + 1) = k₀ * j + k₀ := by ring
      rw [this]
      exact add_mem_expNatSet ih h

/-- **The jump of the periodisation at the origin is never zero.** -/
theorem tsum_putnamJumpTerm_ne_zero {a d : ℝ} (hd : 0 < d) :
    (∑' k : ℤ, putnamJumpTerm a d k) ≠ 0 := by
  classical
  have hP : 0 < putnamPeriod d := putnamPeriod_pos hd
  by_cases hex : ∃ k : ℕ, 0 < k ∧ k ∈ expNatSet (putnamPeriod d)
  · obtain ⟨k₀, hk₀pos, hk₀mem, hk₀min⟩ :
        ∃ k₀ : ℕ, 0 < k₀ ∧ k₀ ∈ expNatSet (putnamPeriod d) ∧
          ∀ j : ℕ, 0 < j → j ∈ expNatSet (putnamPeriod d) → k₀ ≤ j :=
      ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
        fun j hj hjmem => Nat.find_min' hex ⟨hj, hjmem⟩⟩
    set w : ℂ := Complex.exp (-(1 / 2 + (a : ℂ) * I) * ((k₀ : ℝ) * putnamPeriod d)) with hw
    have hk₀R : (0 : ℝ) < (k₀ : ℝ) := by exact_mod_cast hk₀pos
    have hwnorm : ‖w‖ < 1 := by
      rw [hw, Complex.norm_exp, Real.exp_lt_one_iff]
      simp [Complex.mul_re]
      nlinarith
    have hinj : Function.Injective (fun j : ℕ => (k₀ : ℤ) * (j : ℤ)) := by
      intro i j hij
      simp only at hij
      have hk₀ne : ((k₀ : ℤ)) ≠ 0 := by exact_mod_cast hk₀pos.ne'
      have := mul_left_cancel₀ hk₀ne hij
      exact_mod_cast this
    have hsupp : ∀ k : ℤ, k ∉ Set.range (fun j : ℕ => (k₀ : ℤ) * (j : ℤ)) →
        putnamJumpTerm a d k = 0 := by
      intro k hk
      rcases lt_or_ge k 0 with h | h
      · exact putnamJumpTerm_eq_zero_of_neg hd h
      · refine putnamJumpTerm_eq_zero_of_notMem h ?_
        intro hmem
        obtain ⟨j, hj⟩ := dvd_of_mem_expNatSet hk₀pos hk₀min hmem hk₀mem
        refine hk ⟨j, ?_⟩
        simp only
        have hkt : k = ((k.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg h).symm
        rw [hkt, hj]
        push_cast
        ring
    have hterm : ∀ j : ℕ, putnamJumpTerm a d ((k₀ : ℤ) * (j : ℤ)) = w ^ j := by
      intro j
      have hnn : (0 : ℤ) ≤ (k₀ : ℤ) * (j : ℤ) := by positivity
      have htn : ((k₀ : ℤ) * (j : ℤ)).toNat = k₀ * j := by omega
      rw [putnamJumpTerm_of_mem hnn (by rw [htn]; exact mul_mem_expNatSet hk₀mem j)]
      rw [hw, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hsupport : Function.support (putnamJumpTerm a d)
        ⊆ Set.range (fun j : ℕ => (k₀ : ℤ) * (j : ℤ)) := by
      intro k hk
      by_contra hcon
      exact hk (hsupp k hcon)
    have h1 : ∑' (x : Set.range (fun j : ℕ => (k₀ : ℤ) * (j : ℤ))), putnamJumpTerm a d x
        = ∑' k : ℤ, putnamJumpTerm a d k :=
      tsum_subtype_eq_of_support_subset hsupport
    have h2 : ∑' j : ℕ, putnamJumpTerm a d ((k₀ : ℤ) * (j : ℤ))
        = ∑' (x : Set.range (fun j : ℕ => (k₀ : ℤ) * (j : ℤ))), putnamJumpTerm a d x :=
      (Equiv.ofInjective _ hinj).tsum_eq (fun x => putnamJumpTerm a d x)
    rw [← h1, ← h2, tsum_congr hterm, tsum_geometric_of_norm_lt_one hwnorm]
    refine inv_ne_zero ?_
    intro hcon
    have hw1 : w = 1 := by linear_combination -hcon
    rw [hw1] at hwnorm
    simp at hwnorm
  · have hsingle : ∀ k : ℤ, k ≠ 0 → putnamJumpTerm a d k = 0 := by
      intro k hk
      rcases lt_or_ge k 0 with h | h
      · exact putnamJumpTerm_eq_zero_of_neg hd h
      · refine putnamJumpTerm_eq_zero_of_notMem h ?_
        intro hmem
        exact hex ⟨k.toNat, by omega, hmem⟩
    rw [tsum_eq_single 0 hsingle, putnamJumpTerm_zero]
    exact one_ne_zero

end RHTower

end
