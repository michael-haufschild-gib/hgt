import GaloisForLFunctions.RHTower.EisensteinHeckeFactorizationAtI
import GaloisForLFunctions.RHTower.Sieve.DivisorBound

/-!
# Positive coefficients of the rectangular Epstein series

The form `m² + 64n²` is the Gaussian norm restricted to imaginary parts divisible
by eight. Its representation fibers give nonnegative normalized Dirichlet
coefficients. The fibers at five and thirteen are empty, while sixty-five is
represented, so the coefficient stream is not multiplicative.
-/

noncomputable section

open Complex Finset
open RHTower.GaussianTwoSquares

namespace GaloisForLFunctions.SelbergClass.PositiveEpstein

/-- Gaussian integers of norm `n` whose imaginary part is divisible by eight. -/
def normFiber (n : ℕ) : Finset GaussianInt :=
  (normSet n).filter fun z => (8 : ℤ) ∣ z.im

theorem mem_normFiber {n : ℕ} {z : GaussianInt} :
    z ∈ normFiber n ↔ z.norm = n ∧ (8 : ℤ) ∣ z.im := by
  simp only [normFiber, Finset.mem_filter, mem_normSet]

/-- Half the representation count, with the zero Dirichlet coefficient suppressed. -/
def coeff (n : ℕ) : ℝ := if n = 0 then 0 else (normFiber n).card / 2

@[simp] theorem coeff_zero : coeff 0 = 0 := by simp [coeff]

theorem coeff_nonneg (n : ℕ) : 0 ≤ coeff n := by
  by_cases hn : n = 0
  · simp only [coeff, if_pos hn, le_refl]
  · simp only [coeff, if_neg hn]
    positivity

/-- Below norm sixty-four, a represented Gaussian integer lies on the real axis. -/
theorem im_eq_zero_of_mem_normFiber {n : ℕ} {z : GaussianInt}
    (hn : n < 64) (hz : z ∈ normFiber n) : z.im = 0 := by
  obtain ⟨hz, v, hv⟩ := mem_normFiber.mp hz
  rw [norm_eq, hv] at hz
  have hn' : (n : ℤ) < 64 := by exact_mod_cast hn
  have hvbound : 64 * v ^ 2 ≤ (n : ℤ) := by nlinarith only [hz, sq_nonneg z.re]
  have hv2 : v ^ 2 = 0 := by have := sq_nonneg v; omega
  have hv0 : v = 0 := by
    rw [pow_two] at hv2
    rcases mul_eq_zero.mp hv2 with h | h <;> exact h
  simpa only [hv0, mul_zero] using hv

theorem normFiber_one : normFiber 1 = {⟨1, 0⟩, ⟨-1, 0⟩} := by
  ext z
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hz
    have him := im_eq_zero_of_mem_normFiber (by norm_num : 1 < 64) hz
    have hnorm := (mem_normFiber.mp hz).1
    rw [norm_eq, him] at hnorm
    norm_num only [zero_pow, Nat.cast_one, add_zero] at hnorm
    have hfactor : (z.re - 1) * (z.re + 1) = 0 := by nlinarith only [hnorm]
    rcases mul_eq_zero.mp hfactor with h | h
    · left
      have hre : z.re = 1 := by linarith only [h]
      cases z
      simp_all
    · right
      have hre : z.re = -1 := by linarith only [h]
      cases z
      simp_all
  · rintro (rfl | rfl) <;> norm_num [mem_normFiber, norm_eq]

@[simp] theorem coeff_one : coeff 1 = 1 := by
  norm_num [coeff, normFiber_one]

private theorem not_square_five (m : ℤ) : m ^ 2 ≠ 5 := by
  intro hm
  have hlo : -3 < m := by nlinarith only [hm, sq_nonneg (m + 3)]
  have hhi : m < 3 := by nlinarith only [hm, sq_nonneg (m - 3)]
  have hmlo : 0 ≤ m + 2 := by omega
  have hmhi : 0 ≤ 2 - m := by omega
  nlinarith only [hm, mul_nonneg hmlo hmhi]

private theorem not_square_thirteen (m : ℤ) : m ^ 2 ≠ 13 := by
  intro hm
  have hlo : -4 < m := by nlinarith only [hm, sq_nonneg (m + 4)]
  have hhi : m < 4 := by nlinarith only [hm, sq_nonneg (m - 4)]
  have hmlo : 0 ≤ m + 3 := by omega
  have hmhi : 0 ≤ 3 - m := by omega
  nlinarith only [hm, mul_nonneg hmlo hmhi]

theorem normFiber_five : normFiber 5 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have him := im_eq_zero_of_mem_normFiber (by norm_num : 5 < 64) hz
  have hnorm := (mem_normFiber.mp hz).1
  apply not_square_five z.re
  simpa [norm_eq, him] using hnorm

theorem normFiber_thirteen : normFiber 13 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have him := im_eq_zero_of_mem_normFiber (by norm_num : 13 < 64) hz
  have hnorm := (mem_normFiber.mp hz).1
  apply not_square_thirteen z.re
  simpa [norm_eq, him] using hnorm

@[simp] theorem coeff_five : coeff 5 = 0 := by simp [coeff, normFiber_five]

@[simp] theorem coeff_thirteen : coeff 13 = 0 := by simp [coeff, normFiber_thirteen]

theorem coeff_pos_of_mem {n : ℕ} (hn : n ≠ 0) {z : GaussianInt}
    (hz : z ∈ normFiber n) : 0 < coeff n := by
  have hcard : 0 < (normFiber n).card := Finset.card_pos.mpr ⟨z, hz⟩
  rw [coeff, if_neg hn]
  exact div_pos (by exact_mod_cast hcard) (by norm_num)

theorem coeff_sixtyfive_pos : 0 < coeff 65 := by
  apply coeff_pos_of_mem (n := 65) (z := ⟨1, 8⟩) (by norm_num)
  norm_num [mem_normFiber, norm_eq]

/-- The normalized positive coefficient stream fails multiplicativity at `5 · 13`. -/
theorem coeff_not_multiplicative :
    Nat.Coprime 5 13 ∧ coeff (5 * 13) ≠ coeff 5 * coeff 13 := by
  refine ⟨by norm_num, ?_⟩
  rw [coeff_five, coeff_thirteen, zero_mul]
  exact coeff_sixtyfive_pos.ne'


/-! ### Grouping lattice points into ordinary Dirichlet coefficients -/

abbrev LatticePoint := {p : ℤ × ℤ // p ≠ (0, 0)}

/-- Embed the rectangular lattice in the Gaussian lattice. -/
def scalePair (p : LatticePoint) : LatticePoint :=
  ⟨(p.1.1, 8 * p.1.2), by
    intro h
    have hre : p.1.1 = 0 := congrArg (fun z : ℤ × ℤ => z.1) h
    have him : 8 * p.1.2 = 0 := congrArg (fun z : ℤ × ℤ => z.2) h
    exact p.2 (Prod.ext hre (by omega))⟩

theorem scalePair_injective : Function.Injective scalePair := by
  intro p q h
  have hp := congrArg (fun z : LatticePoint => z.1.1) h
  have hq := congrArg (fun z : LatticePoint => z.1.2) h
  change p.1.1 = q.1.1 at hp
  apply Subtype.ext
  apply Prod.ext hp
  dsimp [scalePair] at hq
  omega

/-- The positive integer represented by a nonzero rectangular lattice point. -/
def qNorm (p : LatticePoint) : ℕ := RHTower.HeckeFactorization.latNorm (scalePair p).1

theorem qNorm_pos (p : LatticePoint) : 0 < qNorm p :=
  RHTower.HeckeFactorization.latNorm_pos (scalePair p).2

theorem qNorm_cast (p : LatticePoint) :
    (qNorm p : ℤ) = p.1.1 ^ 2 + 64 * p.1.2 ^ 2 := by
  rw [qNorm, RHTower.HeckeFactorization.latNorm_cast]
  dsimp [scalePair]
  ring

def latticeTerm (s : ℂ) (p : LatticePoint) : ℂ := (qNorm p : ℂ) ^ (-s)

theorem summable_latticeTerm {s : ℂ} (hs : 1 < s.re) : Summable (latticeTerm s) :=
  (RHTower.HeckeFactorization.summable_latTerm hs).comp_injective scalePair_injective

private def fiberMap (n : ℕ) (p : ↑(qNorm ⁻¹' {n})) : ↥(normFiber n) :=
  ⟨⟨p.1.1.1, 8 * p.1.1.2⟩, mem_normFiber.mpr ⟨by
    have hp : qNorm p.1 = n := p.2
    rw [norm_eq]
    change p.1.1.1 ^ 2 + (8 * p.1.1.2) ^ 2 = (n : ℤ)
    calc p.1.1.1 ^ 2 + (8 * p.1.1.2) ^ 2 = (qNorm p.1 : ℤ) := by
        rw [qNorm_cast]
        ring
      _ = (n : ℤ) := congrArg (fun m : ℕ => (m : ℤ)) hp,
    ⟨p.1.1.2, rfl⟩⟩⟩

/-- A representation fiber is exactly the finite Gaussian norm fiber. -/
def fiberEquiv {n : ℕ} (hn : 0 < n) : ↑(qNorm ⁻¹' {n}) ≃ ↥(normFiber n) :=
  Equiv.ofBijective (fiberMap n) ⟨by
    intro p q h
    have hre := congrArg (fun z : ↥(normFiber n) => z.1.re) h
    have him := congrArg (fun z : ↥(normFiber n) => z.1.im) h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext hre
    dsimp [fiberMap] at him
    omega, by
    intro z
    obtain ⟨hz, v, hv⟩ := mem_normFiber.mp z.2
    have hp : (z.1.re, v) ≠ (0, 0) := by
      intro h
      have hre : z.1.re = 0 := congrArg Prod.fst h
      have hv0 : v = 0 := congrArg Prod.snd h
      rw [norm_eq, hre, hv, hv0] at hz
      norm_num at hz
      omega
    let p : LatticePoint := ⟨(z.1.re, v), hp⟩
    have hpn : qNorm p = n := by
      have hh : (qNorm p : ℤ) = n := by
        rw [qNorm_cast]
        dsimp [p]
        rw [norm_eq, hv] at hz
        nlinarith only [hz]
      exact_mod_cast hh
    refine ⟨⟨p, hpn⟩, ?_⟩
    apply Subtype.ext
    exact Zsqrtd.ext rfl hv.symm⟩

theorem tsum_fiber (s : ℂ) (n : ℕ) :
    ∑' p : ↑(qNorm ⁻¹' {n}), latticeTerm s p.1 / 2 =
      LSeries.term (fun n => (coeff n : ℂ)) s n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : IsEmpty ↑(qNorm ⁻¹' {0}) := ⟨fun p => (qNorm_pos p.1).ne' p.2⟩
    rw [tsum_empty, LSeries.term_zero]
  · have hconst : ∀ p : ↑(qNorm ⁻¹' {n}), latticeTerm s p.1 / 2 =
        (n : ℂ) ^ (-s) / 2 := by
      intro p
      have hp : qNorm p.1 = n := p.2
      rw [latticeTerm, hp]
    simp_rw [hconst]
    rw [(fiberEquiv hn).tsum_eq (fun _ => (n : ℂ) ^ (-s) / 2),
      Finset.tsum_subtype (normFiber n) (fun _ => (n : ℂ) ^ (-s) / 2),
      Finset.sum_const, nsmul_eq_mul, LSeries.term_of_ne_zero hn.ne', coeff, if_neg hn.ne']
    push_cast
    rw [cpow_neg]
    ring

/-- The normalized lattice series is an absolutely convergent ordinary Dirichlet series. -/
theorem lSeriesSummable_and_eq {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (coeff n : ℂ)) s ∧
      LSeries (fun n => (coeff n : ℂ)) s = (∑' p, latticeTerm s p) / 2 := by
  have h := ((summable_latticeTerm hs).hasSum.div_const (2 : ℂ)).tsum_fiberwise qNorm
  simp_rw [tsum_fiber] at h
  exact ⟨h.summable, h.tsum_eq⟩

/-! ### Ramanujan bounds -/

/-- Restriction to a sublattice can only decrease the Gaussian representation count. -/
theorem coeff_le_two_mul_divisors (n : ℕ) : coeff n ≤ 2 * n.divisors.card := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [coeff_zero, Nat.divisors_zero, Finset.card_empty, Nat.cast_zero, mul_zero, le_refl]
  have hχ (d : ℕ) : ZMod.χ₄ d ≤ 1 := by
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    split_ifs <;> norm_num
  have hsum : divisorChar n ≤ (n.divisors.card : ℤ) := by
    calc divisorChar n ≤ ∑ d ∈ n.divisors, (1 : ℤ) := Finset.sum_le_sum fun d _ => hχ d
      _ = n.divisors.card := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (normFiber n).card ≤ (normSet n).card := Finset.card_filter_le _ _
  have hcount := card_normSet hn
  have hcountR : ((normSet n).card : ℝ) = 4 * (divisorChar n : ℝ) := by exact_mod_cast hcount
  have hcardR : ((normFiber n).card : ℝ) ≤ (normSet n).card := by exact_mod_cast hcard
  have hsumR : (divisorChar n : ℝ) ≤ n.divisors.card := by exact_mod_cast hsum
  rw [coeff, if_neg hn.ne']
  linarith only [hcountR, hcardR, hsumR]

/-- The positive coefficients satisfy every Ramanujan power bound. -/
theorem ramanujan_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ‖(coeff n : ℂ)‖ ≤ C * (n : ℝ) ^ ε := by
  refine ⟨2 * RHTower.Sieve.divisorBoundConst ε,
    mul_pos (by norm_num) (RHTower.Sieve.divisorBoundConst_pos hε), ?_⟩
  intro n hn
  rw [Complex.norm_real, Real.norm_of_nonneg (coeff_nonneg n)]
  have h := RHTower.Sieve.card_divisors_le_rpow hε hn.ne'
  calc coeff n ≤ 2 * n.divisors.card := coeff_le_two_mul_divisors n
    _ ≤ (2 * RHTower.Sieve.divisorBoundConst ε) * (n : ℝ) ^ ε := by linarith only [h]

end GaloisForLFunctions.SelbergClass.PositiveEpstein
