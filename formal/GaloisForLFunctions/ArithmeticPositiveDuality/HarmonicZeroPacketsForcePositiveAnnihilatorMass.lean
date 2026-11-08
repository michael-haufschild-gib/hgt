import GaloisForLFunctions.ArithmeticPositiveDuality.TheUnitMassBoundaryOfPositiveAnnihilators

/-!
# Harmonic zero packets force positive annihilator mass

Zeros at the first `m` multiples of one ordinate prescribe `m` Fourier moments
of the positive coefficient measure. Its geometric-sum energy is exactly
`(m + 1) (H - m)`, giving the sharp mass bound and its equality case.
-/

noncomputable section
set_option autoImplicit false

open Complex Finset
open scoped NNReal ComplexConjugate

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

private theorem unit_pow_pair {u : ℂ} (hu : ‖u‖ = 1) {i j : ℕ} (hij : i ≤ j) :
    conj (u ^ i) * u ^ j = u ^ (j - i) := by
  have hunit : conj (u ^ i) * u ^ i = 1 := by
    rw [Complex.conj_mul', norm_pow, hu, one_pow]
    norm_num
  calc
    conj (u ^ i) * u ^ j = conj (u ^ i) * (u ^ i * u ^ (j - i)) := by
      rw [← pow_add, Nat.add_sub_of_le hij]
    _ = u ^ (j - i) := by rw [← mul_assoc, hunit, one_mul]

private theorem weighted_pair_moment {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (u : ι → ℂ) {m : ℕ} (hu : ∀ d ∈ S, ‖u d‖ = 1)
    (hm : ∀ k : ℕ, 1 ≤ k → k ≤ m → ∑ d ∈ S, (w d : ℂ) * u d ^ k = -1)
    (i j : Fin (m + 1)) :
    (∑ d ∈ S, (w d : ℂ) * conj (u d ^ (i : ℕ)) * u d ^ (j : ℕ)) =
      if i = j then ((∑ d ∈ S, w d : ℝ) : ℂ) else -1 := by
  classical
  have hforward (a b : Fin (m + 1)) (hab : (a : ℕ) < b) :
      (∑ d ∈ S, (w d : ℂ) * conj (u d ^ (a : ℕ)) * u d ^ (b : ℕ)) = -1 := by
    calc
      _ = ∑ d ∈ S, (w d : ℂ) * u d ^ ((b : ℕ) - a) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [mul_assoc, unit_pow_pair (hu d hd) hab.le]
      _ = -1 := hm _ (by omega) (by omega)
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [mul_assoc, unit_pow_pair (hu d hd) le_rfl, Nat.sub_self, pow_zero, mul_one]
  · rw [if_neg hij]
    rcases lt_or_gt_of_ne (show (i : ℕ) ≠ j from fun h => hij (Fin.ext h)) with h | h
    · exact hforward i j h
    · have hc := congrArg conj (hforward j i h)
      simp only [map_sum, map_mul, Complex.conj_ofReal, conj_conj, map_neg, map_one] at hc
      convert hc using 1
      apply Finset.sum_congr rfl
      intro d _
      ring

private theorem weighted_geometric_energy {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (u : ι → ℂ) {m : ℕ} (hu : ∀ d ∈ S, ‖u d‖ = 1)
    (hm : ∀ k : ℕ, 1 ≤ k → k ≤ m → ∑ d ∈ S, (w d : ℂ) * u d ^ k = -1) :
    (∑ d ∈ S, w d * ‖∑ j : Fin (m + 1), u d ^ (j : ℕ)‖ ^ 2) =
      (m + 1 : ℝ) * ((∑ d ∈ S, w d) - m) := by
  classical
  have hrow (i : Fin (m + 1)) :
      (∑ j : Fin (m + 1), if i = j then ((∑ d ∈ S, w d : ℝ) : ℂ) else -1) =
        ((∑ d ∈ S, w d : ℝ) : ℂ) - m := by
    calc
      _ = ∑ j : Fin (m + 1),
          ((if i = j then ((∑ d ∈ S, w d : ℝ) : ℂ) + 1 else 0) - 1) := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring
      _ = _ := by rw [Finset.sum_sub_distrib]; simp
  have hc :
      (((∑ d ∈ S, w d * ‖∑ j : Fin (m + 1), u d ^ (j : ℕ)‖ ^ 2) : ℝ) : ℂ) =
        ((m + 1 : ℝ) * ((∑ d ∈ S, w d) - m) : ℝ) := by
    calc
      _ = ∑ d ∈ S, ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
          (w d : ℂ) * conj (u d ^ (i : ℕ)) * u d ^ (j : ℕ) := by
        rw [Complex.ofReal_sum]
        apply Finset.sum_congr rfl
        intro d _
        rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.conj_mul']
        simp only [map_sum, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
      _ = ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
          ∑ d ∈ S, (w d : ℂ) * conj (u d ^ (i : ℕ)) * u d ^ (j : ℕ) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = ∑ i : Fin (m + 1), (((∑ d ∈ S, w d : ℝ) : ℂ) - m) := by
        apply Finset.sum_congr rfl
        intro i _
        simp_rw [weighted_pair_moment S w u hu hm]
        exact hrow i
      _ = _ := by simp; push_cast; ring
  exact Complex.ofReal_injective hc

/-- The unit phase of a supported monomial at ordinate `γ`. -/
def monomialPhase (γ : ℝ) (d : Fin 2 →₀ ℕ) : ℂ :=
  Complex.exp (-(monomialLog d : ℂ) * (γ : ℂ) * I)

/-- The `k`th point in a harmonic packet on the line of real part `β`. -/
def harmonicPacketPoint (β γ : ℝ) (k : ℕ) : ℂ :=
  (β : ℂ) + (k : ℂ) * (γ : ℂ) * I

theorem norm_monomialPhase (γ : ℝ) (d : Fin 2 →₀ ℕ) : ‖monomialPhase γ d‖ = 1 := by
  simp [monomialPhase, Complex.norm_exp]

private theorem harmonic_monomial (c β γ : ℝ) (d : Fin 2 →₀ ℕ) (k : ℕ) :
    (c : ℂ) * Complex.exp (-(monomialLog d : ℂ) * harmonicPacketPoint β γ k) =
      ((c * Real.exp (-monomialLog d * β) : ℝ) : ℂ) * monomialPhase γ d ^ k := by
  have he : -(monomialLog d : ℂ) * harmonicPacketPoint β γ k =
      ((-monomialLog d * β : ℝ) : ℂ) +
        (k : ℂ) * (-(monomialLog d : ℂ) * (γ : ℂ) * I) := by
    unfold harmonicPacketPoint
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_nat_mul]
  simp only [Complex.ofReal_mul, Complex.ofReal_exp, monomialPhase]
  ring

/-- The exact positive energy of a harmonic packet. -/
theorem harmonic_zero_packet_energy {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) (β γ : ℝ) (m : ℕ)
    (hz : ∀ k : ℕ, 1 ≤ k → k ≤ m → dirichletEval (harmonicPacketPoint β γ k) P = 0) :
    (∑ d ∈ P.support.erase 0, ((P.coeff d : ℝ≥0) : ℝ) *
      Real.exp (-monomialLog d * β) *
        ‖∑ j : Fin (m + 1), monomialPhase γ d ^ (j : ℕ)‖ ^ 2) =
      (m + 1 : ℝ) * (dirichletTailMass P β - m) := by
  apply weighted_geometric_energy
  · intro d _
    exact norm_monomialPhase γ d
  · intro k hk hkm
    have he := dirichletEval_eq_one_add_tail hP (harmonicPacketPoint β γ k)
    rw [hz k hk hkm] at he
    simp_rw [harmonic_monomial] at he
    linear_combination -he

/-- Cancelling the first `m` harmonic ordinates costs at least `m` in positive tail mass. -/
theorem harmonic_zero_packet_mass_le {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) (β γ : ℝ) (m : ℕ)
    (hz : ∀ k : ℕ, 1 ≤ k → k ≤ m → dirichletEval (harmonicPacketPoint β γ k) P = 0) :
    (m : ℝ) ≤ dirichletTailMass P β := by
  have he := harmonic_zero_packet_energy hP β γ m hz
  have hn : 0 ≤ ∑ d ∈ P.support.erase 0, ((P.coeff d : ℝ≥0) : ℝ) *
      Real.exp (-monomialLog d * β) *
        ‖∑ j : Fin (m + 1), monomialPhase γ d ^ (j : ℕ)‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro d _
    exact mul_nonneg (mul_nonneg (P.coeff d).coe_nonneg (Real.exp_pos _).le) (sq_nonneg _)
  rw [he] at hn
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hn (by positivity : (0 : ℝ) < m + 1))

private theorem geometric_sum_eq_zero_iff (u : ℂ) (m : ℕ) :
    (∑ j : Fin (m + 1), u ^ (j : ℕ)) = 0 ↔ u ^ (m + 1) = 1 ∧ u ≠ 1 := by
  rw [Fin.sum_univ_eq_sum_range]
  have hg := geom_sum_mul u (m + 1)
  constructor
  · intro hs
    refine ⟨?_, ?_⟩
    · rw [hs, zero_mul] at hg
      exact sub_eq_zero.mp hg.symm
    · intro hu
      subst u
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hs
      have hzero : m + 1 = 0 := by exact_mod_cast hs
      omega
  · rintro ⟨hu, hne⟩
    rw [hu, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_right (sub_ne_zero.mpr hne)

/-- Equality forces every supported phase to be a nontrivial `(m+1)`st root of unity. -/
theorem harmonic_zero_packet_mass_eq_iff {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) (β γ : ℝ) (m : ℕ)
    (hz : ∀ k : ℕ, 1 ≤ k → k ≤ m → dirichletEval (harmonicPacketPoint β γ k) P = 0) :
    dirichletTailMass P β = m ↔ ∀ d ∈ P.support.erase 0,
      monomialPhase γ d ^ (m + 1) = 1 ∧ monomialPhase γ d ≠ 1 := by
  have he := harmonic_zero_packet_energy hP β γ m hz
  have hw (d : Fin 2 →₀ ℕ) (hd : d ∈ P.support.erase 0) :
      0 < ((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * β) := by
    refine mul_pos ?_ (Real.exp_pos _)
    have hn := MvPolynomial.mem_support_iff.mp (Finset.mem_of_mem_erase hd)
    exact_mod_cast (pos_iff_ne_zero.mpr hn : 0 < P.coeff d)
  have hnonneg (d : Fin 2 →₀ ℕ) (hd : d ∈ P.support.erase 0) :
      0 ≤ ((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * β) *
        ‖∑ j : Fin (m + 1), monomialPhase γ d ^ (j : ℕ)‖ ^ 2 :=
    mul_nonneg (hw d hd).le (sq_nonneg _)
  constructor
  · intro hmass
    rw [hmass, sub_self, mul_zero] at he
    intro d hd
    have ht := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp he d hd
    have hn := (mul_eq_zero.mp ht).resolve_left (hw d hd).ne'
    exact (geometric_sum_eq_zero_iff _ _).mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
  · intro hphase
    have hzero : (∑ d ∈ P.support.erase 0, ((P.coeff d : ℝ≥0) : ℝ) *
        Real.exp (-monomialLog d * β) *
          ‖∑ j : Fin (m + 1), monomialPhase γ d ^ (j : ℕ)‖ ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      rw [(geometric_sum_eq_zero_iff _ _).mpr (hphase d hd), norm_zero, zero_pow (by decide),
        mul_zero]
    rw [hzero] at he
    have hm : (m + 1 : ℝ) ≠ 0 := by positivity
    exact sub_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_left hm)

/-- The geometric polynomial attains the harmonic-packet mass bound. -/
def harmonicPacketAnnihilator (β : ℝ) (m : ℕ) : MvPolynomial (Fin 2) ℝ≥0 :=
  ∑ j ∈ Finset.range (m + 1), scaledTwoMonomial β ^ j

/-- The positive ordinate spacing of the extremal packet. -/
def harmonicPacketStep (m : ℕ) : ℝ := 2 * Real.pi / (((m : ℝ) + 1) * Real.log 2)

theorem harmonicPacketAnnihilator_constantCoeff (β : ℝ) (m : ℕ) :
    MvPolynomial.constantCoeff (harmonicPacketAnnihilator β m) = 1 := by
  induction m with
  | zero => simp [harmonicPacketAnnihilator]
  | succ m ih =>
      rw [harmonicPacketAnnihilator, Finset.sum_range_succ, map_add]
      change MvPolynomial.constantCoeff (harmonicPacketAnnihilator β m) + _ = 1
      rw [ih, map_pow]
      simp [scaledTwoMonomial]

theorem dirichletEval_harmonicPacketAnnihilator (β : ℝ) (m : ℕ) (s : ℂ) :
    dirichletEval s (harmonicPacketAnnihilator β m) =
      ∑ j ∈ Finset.range (m + 1), dirichletEval s (scaledTwoMonomial β) ^ j := by
  simp only [harmonicPacketAnnihilator, map_sum, map_pow]

theorem harmonicPacketAnnihilator_tail_mass (β : ℝ) (m : ℕ) :
    dirichletTailMass (harmonicPacketAnnihilator β m) β = m := by
  have he := dirichletEval_ofReal_eq_one_add_tail
    (harmonicPacketAnnihilator_constantCoeff β m) β
  rw [dirichletEval_harmonicPacketAnnihilator, scaledTwoMonomial_at_real] at he
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at he
  have hr := congrArg Complex.re he
  simp only [Complex.natCast_re, Complex.ofReal_re, Nat.cast_add, Nat.cast_one] at hr
  linarith only [hr]

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
