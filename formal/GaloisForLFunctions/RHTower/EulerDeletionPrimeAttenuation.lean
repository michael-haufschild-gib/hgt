import GaloisForLFunctions.RHTower.EulerDeletionPairedPrimeFreedom
import GaloisForLFunctions.RHTower.DirichletUniformAbel
import GaloisForLFunctions.HTGeometry.HarmonicResidueTransfer

/-!
# Prime attenuation changes the ordinary deletion domain

The literal positive completely multiplicative coefficients c^(v_p(n)) have an exact
bounded digit remainder. The deletion normalization is uniquely forced by bounded
coefficient prefixes: its multiplier must satisfy ell*c=p. Keeping the literal multiplier
p after attenuation creates a positive harmonic drift and excludes ordinary Dirichlet
convergence throughout Re(s)<1. The repaired multiplier recovers convergence for Re(s)>0.

This is an admission audit for a changed arithmetic source, not a relation forced by a zeta
zero. No computational certificate or additional axiom enters the proof.
-/

noncomputable section
open Filter Topology
open scoped BigOperators
namespace RHTower.DeletionPrimeAttenuation

def weight (p : ℕ) (c : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else c ^ n.factorization p

theorem weight_one (p : ℕ) (c : ℝ) : weight p c 1 = 1 := by simp [weight]

theorem weight_mul (p : ℕ) (c : ℝ) (a b : ℕ) :
    weight p c (a*b) = weight p c a * weight p c b := by
  by_cases ha : a = 0
  · subst a; simp [weight]
  by_cases hb : b = 0
  · subst b; simp [weight]
  simp [weight, ha, hb, Nat.factorization_mul ha hb, pow_add]

theorem weight_nonneg (p : ℕ) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    0 ≤ weight p c n := by
  simp only [weight]
  split_ifs <;> positivity

theorem weight_pos (p : ℕ) {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 0 < n) :
    0 < weight p c n := by
  simp only [weight, if_neg (by omega : n ≠ 0)]
  positivity

theorem weight_le_one (p : ℕ) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    weight p c n ≤ 1 := by
  simp only [weight]
  split_ifs
  · norm_num
  · exact pow_le_one₀ hc hc1

theorem weight_prime {p : ℕ} (hp : p.Prime) (c : ℝ) : weight p c p = c := by
  simp [weight, hp.ne_zero, hp.factorization_self]

theorem weight_prime_mul {p : ℕ} (hp : p.Prime) (c : ℝ) (n : ℕ) :
    weight p c (p*n) = c * weight p c n := by
  rw [weight_mul, weight_prime hp]

theorem weight_of_not_dvd {p n : ℕ} (h : ¬p ∣ n) (c : ℝ) : weight p c n = 1 := by
  have hn : n ≠ 0 := by intro hn; simp [hn] at h
  simp [weight, hn, Nat.factorization_eq_zero_of_not_dvd h]

def massPrefix (p : ℕ) (c : ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, weight p c n

theorem sum_indicator (p N : ℕ) (hp : 0 < p) :
    (∑ n ∈ Finset.Icc 1 N, if p ∣ n then (1 : ℝ) else 0) = (N / p : ℕ) := by
  rw [← Finset.sum_filter, sum_Icc_filter_dvd_reindex p N hp]
  simp

theorem prefix_recursion {p : ℕ} (hp : p.Prime) (c : ℝ) (N : ℕ) :
    massPrefix p c N = (N : ℝ) - (N / p : ℕ) + c * massPrefix p c (N / p) := by
  have point (n : ℕ) : weight p c n =
      1 - (if p ∣ n then 1 else 0) + (if p ∣ n then weight p c n else 0) := by
    by_cases h : p ∣ n
    · simp [h]
    · simp [h, weight_of_not_dvd h]
  have hsum : (∑ n ∈ Finset.Icc 1 N, if p ∣ n then weight p c n else 0) =
      c * massPrefix p c (N / p) := by
    rw [← Finset.sum_filter, sum_Icc_filter_dvd_reindex p N hp.pos]
    simp_rw [weight_prime_mul hp]
    rw [← Finset.mul_sum]
    rfl
  rw [massPrefix, Finset.sum_congr rfl (fun n _ => point n), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sum_indicator p N hp.pos, hsum]
  simp

def remainder (p : ℕ) (c : ℝ) (N : ℕ) : ℝ :=
  ((p : ℝ)-c) * massPrefix p c N - ((p : ℝ)-1) * N

theorem remainder_recursion {p : ℕ} (hp : p.Prime) (c : ℝ) (N : ℕ) :
    remainder p c N = c * remainder p c (N / p) + (1-c) * (N % p : ℕ) := by
  have hN : (N : ℝ) = (N % p : ℕ) + (p : ℝ) * (N / p : ℕ) := by
    exact_mod_cast (Nat.mod_add_div N p).symm
  simp only [remainder]
  rw [prefix_recursion hp]
  rw [hN]
  ring

/-- Exact bounded digit remainder of the literal valuation weights. -/
theorem remainder_bounds {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (N : ℕ) : 0 ≤ remainder p c N ∧ remainder p c N ≤ (p : ℝ)-1 := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hN : N = 0
    · subst N
      simp only [remainder, massPrefix, Finset.Icc_eq_empty_of_lt (by omega : 0 < 1),
        Finset.sum_empty, Nat.cast_zero, mul_zero, sub_self]
      constructor
      · rfl
      · have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
        linarith
    have hdiv := ih (N / p) (Nat.div_lt_self (by omega) hp.one_lt)
    have hmod : ((N % p : ℕ) : ℝ) ≤ (p : ℝ)-1 := by
      have := Nat.mod_lt N hp.pos
      have : N % p + 1 ≤ p := by omega
      have hcast : ((N % p : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast this
      linarith
    have hmod0 : (0 : ℝ) ≤ (N % p : ℕ) := Nat.cast_nonneg _
    rw [remainder_recursion hp]
    constructor
    · exact add_nonneg (mul_nonneg hc hdiv.1) (mul_nonneg (by linarith) hmod0)
    · nlinarith

def deletionPrefix (p : ℕ) (c ell : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (1 - ell * if p ∣ n then 1 else 0) * weight p c n

theorem deletionPrefix_eq {p : ℕ} (hp : p.Prime) (c ell : ℝ) (N : ℕ) :
    deletionPrefix p c ell N = massPrefix p c N - ell*c*massPrefix p c (N/p) := by
  have hsum : (∑ n ∈ Finset.Icc 1 N, if p ∣ n then weight p c n else 0) =
      c * massPrefix p c (N / p) := by
    rw [← Finset.sum_filter, sum_Icc_filter_dvd_reindex p N hp.pos]
    simp_rw [weight_prime_mul hp]
    rw [← Finset.mul_sum]
    rfl
  have point (n : ℕ) : (1 - ell * if p ∣ n then 1 else 0) * weight p c n =
      weight p c n - ell * (if p ∣ n then weight p c n else 0) := by
    split_ifs <;> ring
  rw [deletionPrefix, Finset.sum_congr rfl (fun n _ => point n), Finset.sum_sub_distrib,
    ← Finset.mul_sum, hsum]
  simp only [massPrefix]
  ring

/-- The exact residual identity isolates the normalization mismatch before taking any limit. -/
theorem deletionPrefix_scaled {p : ℕ} (hp : p.Prime) (c ell : ℝ) (N : ℕ) :
    ((p : ℝ)-c) * deletionPrefix p c ell (p*N) =
      ((p : ℝ)-1)*((p : ℝ)-ell*c)*N + c*(1-ell)*remainder p c N := by
  rw [deletionPrefix_eq hp, Nat.mul_div_cancel_left N hp.pos]
  have h := remainder_recursion hp c (p*N)
  simp only [Nat.mul_div_cancel_left N hp.pos, Nat.mul_mod_right, Nat.cast_zero,
    mul_zero, add_zero] at h
  simp only [remainder, Nat.cast_mul] at h ⊢
  nlinarith



/-- The uniquely normalized deletion is a remainder minus the next digit tail. -/
theorem normalized_deletion_exact {p : ℕ} (hp : p.Prime) (c ell : ℝ)
    (hcancel : ell*c = p) (N : ℕ) :
    deletionPrefix p c ell N = (N % p : ℕ) - remainder p c (N/p) := by
  rw [deletionPrefix_eq hp, hcancel, prefix_recursion hp]
  have hN : (N : ℝ) = (N % p : ℕ) + (p : ℝ) * (N/p : ℕ) := by
    exact_mod_cast (Nat.mod_add_div N p).symm
  simp only [remainder]
  rw [hN]
  ring

theorem normalized_deletion_bound {p : ℕ} (hp : p.Prime) {c : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1) {ell : ℝ} (hcancel : ell*c = p) (N : ℕ) :
    |deletionPrefix p c ell N| ≤ (p : ℝ)-1 := by
  rw [normalized_deletion_exact hp c ell hcancel]
  have hR := remainder_bounds hp hc hc1 (N/p)
  have hmod : ((N % p : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by
    exact_mod_cast (show N % p + 1 ≤ p by have := Nat.mod_lt N hp.pos; omega)
  have h0 : (0 : ℝ) ≤ (N % p : ℕ) := Nat.cast_nonneg _
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Boundedness of all literal prefixes forces the exact normalization; no asymptotic premise. -/
theorem bounded_deletion_iff {p : ℕ} (hp : p.Prime) {c : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (ell : ℝ) :
    (∃ C : ℝ, ∀ N, |deletionPrefix p c ell N| ≤ C) ↔ ell*c = p := by
  constructor
  · rintro ⟨C, hC⟩
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hpc : 0 ≤ (p : ℝ)-c := by linarith
    have hR (N : ℕ) : |remainder p c N| ≤ (p : ℝ)-1 := by
      have h := remainder_bounds hp hc hc1 N
      simpa [abs_of_nonneg h.1] using h.2
    have hb (N : ℕ) :
        |((p : ℝ)-1)*((p : ℝ)-ell*c)| * (N : ℝ) ≤
          ((p : ℝ)-c)*C + |c*(1-ell)| *((p : ℝ)-1) := by
      have hNabs : |(N : ℝ)| = (N : ℝ) := abs_of_nonneg (Nat.cast_nonneg N)
      have heq : ((p : ℝ)-1)*((p : ℝ)-ell*c)*N =
          ((p : ℝ)-c)*deletionPrefix p c ell (p*N) - c*(1-ell)*remainder p c N := by
        linarith [deletionPrefix_scaled hp c ell N]
      calc
        _ = |((p : ℝ)-1)*((p : ℝ)-ell*c)*(N : ℝ)| := by
          rw [abs_mul (((p : ℝ)-1)*((p : ℝ)-ell*c)) (N : ℝ),
            hNabs]
        _ = _ := congrArg abs heq
        _ ≤ |((p : ℝ)-c)*deletionPrefix p c ell (p*N)| +
            |c*(1-ell)*remainder p c N| := abs_sub _ _
        _ = ((p : ℝ)-c)*|deletionPrefix p c ell (p*N)| +
            |c*(1-ell)| *|remainder p c N| := by rw [abs_mul, abs_mul, abs_of_nonneg hpc]
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hC _) hpc)
          (mul_le_mul_of_nonneg_left (hR _) (abs_nonneg _))
    have ha : ((p : ℝ)-1)*((p : ℝ)-ell*c) = 0 := by
      by_contra hne
      have habs := abs_pos.mpr hne
      obtain ⟨N, hN⟩ := exists_nat_gt
        ((((p : ℝ)-c)*C + |c*(1-ell)| *((p : ℝ)-1)) /
          |((p : ℝ)-1)*((p : ℝ)-ell*c)|)
      have hlt := (div_lt_iff₀ habs).mp hN
      nlinarith [hb N]
    have hdiff : (p : ℝ)-ell*c = 0 := (mul_eq_zero.mp ha).resolve_left (by linarith)
    linarith
  · intro h
    exact ⟨(p : ℝ)-1, normalized_deletion_bound hp hc hc1 h⟩



def harmonicPrefix (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ)

def harmonicMass (p : ℕ) (c : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, weight p c n / n

def harmonicDeletion (p : ℕ) (c : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (blockDeletionCoefficient p n : ℝ) * weight p c n / n

theorem harmonicPrefix_mono : Monotone harmonicPrefix := by
  intro N M h
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right h)
  intro n _ _
  positivity

theorem harmonicMass_mono (p : ℕ) {c : ℝ} (hc : 0 ≤ c) : Monotone (harmonicMass p c) := by
  intro N M h
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right h)
  intro n _ _
  exact div_nonneg (weight_nonneg p hc n) (Nat.cast_nonneg _)

theorem harmonic_multiples {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, if p ∣ n then 1/(n : ℝ) else 0) =
      (1/(p : ℝ))*harmonicPrefix (N/p) := by
  rw [← Finset.sum_filter, sum_Icc_filter_dvd_reindex p N hp]
  simp only [Nat.cast_mul, one_div, mul_inv_rev, harmonicPrefix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem harmonic_weight_multiples {p : ℕ} (hp : p.Prime) (c : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, if p ∣ n then weight p c n / n else 0) =
      (c/(p : ℝ))*harmonicMass p c (N/p) := by
  rw [← Finset.sum_filter, sum_Icc_filter_dvd_reindex p N hp.pos]
  simp_rw [weight_prime_mul hp]
  simp only [Nat.cast_mul, harmonicMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- The unchanged nonmultiples supply a fixed fraction of harmonic mass. -/
theorem harmonicMass_lower {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : 0 ≤ c) (N : ℕ) :
    (1-1/(p : ℝ))*harmonicPrefix N ≤ harmonicMass p c N := by
  have hl : harmonicPrefix N - (1/(p : ℝ))*harmonicPrefix (N/p) ≤ harmonicMass p c N := by
    rw [← harmonic_multiples hp.pos N]
    dsimp only [harmonicPrefix, harmonicMass]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro n hn
    by_cases hd : p ∣ n
    · simp only [hd, if_true, sub_self]
      exact div_nonneg (weight_nonneg p hc n) (Nat.cast_nonneg _)
    · simp [hd, weight_of_not_dvd hd]
  have hm := harmonicPrefix_mono (Nat.div_le_self N p)
  have hp0 : (0 : ℝ) ≤ 1/(p : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hm hp0
  nlinarith

theorem harmonicDeletion_eq {p : ℕ} (hp : p.Prime) (c : ℝ) (N : ℕ) :
    harmonicDeletion p c N = harmonicMass p c N - c*harmonicMass p c (N/p) := by
  have hpoint (n : ℕ) : (blockDeletionCoefficient p n : ℝ)*weight p c n/n =
      weight p c n/n - (p : ℝ)*(if p ∣ n then weight p c n/n else 0) := by
    by_cases hd : p ∣ n
    · simp [blockDeletionCoefficient, hd]
      ring
    · simp [blockDeletionCoefficient, hd]
  rw [harmonicDeletion, Finset.sum_congr rfl (fun n _ => hpoint n), Finset.sum_sub_distrib,
    ← Finset.mul_sum, harmonic_weight_multiples hp]
  change harmonicMass p c N - (p : ℝ)*(c/(p : ℝ)*harmonicMass p c (N/p)) = _
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp

/-- Positive harmonic drift caused by retaining the literal deletion normalization. -/
theorem harmonicDeletion_lower {p : ℕ} (hp : p.Prime) {c : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (N : ℕ) :
    (1-c)*(1-1/(p : ℝ))*harmonicPrefix N ≤ harmonicDeletion p c N := by
  rw [harmonicDeletion_eq hp]
  have hm := harmonicMass_mono p hc (Nat.div_le_self N p)
  have hl := harmonicMass_lower hp hc N
  have hmc := mul_le_mul_of_nonneg_left hm hc
  have hcl := mul_le_mul_of_nonneg_left hl (show 0 ≤ 1-c by linarith)
  nlinarith

theorem harmonicPrefix_tendsto : Tendsto harmonicPrefix atTop atTop := by
  have heq (N : ℕ) : harmonicPrefix N = (harmonic N : ℝ) := by
    simp [harmonicPrefix, harmonic_eq_sum_Icc, Rat.cast_sum, one_div]
  simpa only [funext heq] using GaloisForLFunctions.tendsto_harmonic_cast_atTop

theorem harmonicDeletion_tendsto {p : ℕ} (hp : p.Prime) {c : ℝ}
    (hc : 0 ≤ c) (hc1 : c < 1) : Tendsto (harmonicDeletion p c) atTop atTop := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpp : (0 : ℝ) < p := by linarith
  have hcoef : 0 < (1-c)*(1-1/(p : ℝ)) := by
    apply mul_pos (by linarith)
    have := (div_lt_one hpp).mpr hpR
    linarith
  exact tendsto_atTop_mono (fun N => harmonicDeletion_lower hp hc hc1.le N)
    (harmonicPrefix_tendsto.const_mul_atTop hcoef)



/-- Zero-indexed coefficients for the actual ordinary Dirichlet-series interface. -/
def deletionCoefficient (p : ℕ) (c ell : ℝ) (n : ℕ) : ℂ :=
  ((1 - ell * if p ∣ n+1 then 1 else 0) * weight p c (n+1) : ℝ)

theorem coefficient_partialSum (p : ℕ) (c ell : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, deletionCoefficient p c ell n) = (deletionPrefix p c ell N : ℂ) := by
  rw [deletionPrefix, sum_Icc_eq_sum_range_succ, Complex.ofReal_sum]
  rfl

/-- The uniquely repaired normalization recovers the full positive-half-plane admission. -/
theorem repaired_converges {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    {ell : ℝ} (hcancel : ell*c = p) {s : ℂ} (hs : 0 < s.re) :
    GaloisForLFunctions.RHTower.DirichletConvergesAt (deletionCoefficient p c ell) s := by
  apply GaloisForLFunctions.RHTower.tendsto_dirichlet_partialSum_of_bounded
    (C := (p : ℝ)-1) (s := s) ?_ hs
  intro N
  rw [coefficient_partialSum, Complex.norm_real, Real.norm_eq_abs]
  exact normalized_deletion_bound hp hc hc1 hcancel N

theorem literal_partialSum_one (p : ℕ) (c : ℝ) (N : ℕ) :
    GaloisForLFunctions.RHTower.dirichletPartialSum (deletionCoefficient p c p) N 1 =
      (harmonicDeletion p c N : ℂ) := by
  rw [GaloisForLFunctions.RHTower.dirichletPartialSum, harmonicDeletion,
    sum_Icc_eq_sum_range_succ, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hd : p ∣ n+1
  · simp [deletionCoefficient, blockDeletionCoefficient, hd, Complex.cpow_neg_one,
      div_eq_mul_inv, Nat.cast_add, Nat.cast_one]
  · simp [deletionCoefficient, blockDeletionCoefficient, hd, Complex.cpow_neg_one,
      div_eq_mul_inv, Nat.cast_add, Nat.cast_one]

theorem literal_not_convergent_at_one {p : ℕ} (hp : p.Prime) {c : ℝ}
    (hc : 0 ≤ c) (hc1 : c < 1) :
    ¬GaloisForLFunctions.RHTower.DirichletConvergesAt (deletionCoefficient p c p) 1 := by
  rintro ⟨L, hL⟩
  simp_rw [literal_partialSum_one] at hL
  have hr := Complex.continuous_re.tendsto L |>.comp hL
  simp only [Function.comp_def, Complex.ofReal_re] at hr
  exact not_tendsto_nhds_of_tendsto_atTop (harmonicDeletion_tendsto hp hc hc1) L.re hr

/-- A finite prime attenuation is excluded from the literal deletion domain throughout the strip. -/
theorem literal_not_convergent_of_re_lt_one {p : ℕ} (hp : p.Prime) {c : ℝ}
    (hc : 0 ≤ c) (hc1 : c < 1) {s : ℂ} (hs : s.re < 1) :
    ¬GaloisForLFunctions.RHTower.DirichletConvergesAt (deletionCoefficient p c p) s := by
  intro h
  apply literal_not_convergent_at_one hp hc hc1
  exact GaloisForLFunctions.RHTower.tendsto_dirichlet_partialSum_of_re_lt h (by simpa using hs)

/-- A closed concrete separation: same positive multiplicative weights, failed literal deletion,
uniquely repaired deletion, and an explicit bounded-prefix certificate. -/
theorem fifth_attenuation_admission_separation :
    weight 5 (1/5) 1 = 1 ∧
    (∀ a b, weight 5 (1/5) (a*b) = weight 5 (1/5) a * weight 5 (1/5) b) ∧
    (∀ n, 0 < n → 0 < weight 5 (1/5) n ∧ weight 5 (1/5) n ≤ 1) ∧
    (∀ N, |deletionPrefix 5 (1/5) 25 N| ≤ 4) ∧
    (∀ ell : ℝ, (∃ C : ℝ, ∀ N, |deletionPrefix 5 (1/5) ell N| ≤ C) ↔ ell = 25) ∧
    (∀ s : ℂ, 0 < s.re →
      GaloisForLFunctions.RHTower.DirichletConvergesAt (deletionCoefficient 5 (1/5) 25) s) ∧
    (∀ s : ℂ, s.re < 1 →
      ¬GaloisForLFunctions.RHTower.DirichletConvergesAt (deletionCoefficient 5 (1/5) 5) s) := by
  refine ⟨weight_one _ _, weight_mul _ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    exact ⟨weight_pos 5 (by norm_num) hn, weight_le_one 5 (by norm_num) (by norm_num) n⟩
  · intro N
    have h := normalized_deletion_bound (p := 5) (c := (1/5 : ℝ)) (ell := 25)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) N
    norm_num at h ⊢
    exact h
  · intro ell
    rw [bounded_deletion_iff (by norm_num : Nat.Prime 5) (by norm_num) (by norm_num)]
    constructor <;> intro h <;> linarith
  · intro s hs
    exact repaired_converges (by norm_num) (by norm_num) (by norm_num) (by norm_num) hs
  · intro s hs
    exact literal_not_convergent_of_re_lt_one (by norm_num) (by norm_num) (by norm_num) hs

end RHTower.DeletionPrimeAttenuation
