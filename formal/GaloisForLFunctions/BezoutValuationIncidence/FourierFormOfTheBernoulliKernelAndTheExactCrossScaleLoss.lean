import GaloisForLFunctions.BezoutValuationIncidence.CoherentNearMultipleObstructionToCrossScaleDispersion

/-!
# The Fourier form of the Bernoulli kernel and the exact cross-scale loss

Over the nontrivial `d`-th roots of unity `T_d`, orthogonality `Σ_{η ∈ T_d} η^k = d [d ∣ k] - 1` and
the inversion pairing `1/(η - 1) + 1/(η⁻¹ - 1) = -1` give the spectral forms

`r_d(M) = (M mod d) - (d-1)/2 = -Σ_{η ∈ T_d} η^{M+1}/(η - 1)`,
`Φ_d(M) = Σ_{η ∈ T_d} η^M / |η - 1|²`.

The residue potential is a positive-definite function on `ℤ/d`: its Fourier coefficients
`|η - 1|^{-2} = 1/(4 sin²(πk/d))` are positive and sum to `Φ_d(0) = (d² - 1)/12`. For a large-scale row
`c'` put `S(z) = Σ_n (c'(n)/n²) zⁿ` and `S₀ = Σ_n |c'(n)|/n²`. Then

`Σ_n (c'(n)/n²) Φ_d(jn) = Σ_{η ∈ T_d} |η - 1|^{-2} S(η^j)`,

and for a prime `p` with `|S(ζ)| ≤ σ_p` on the nontrivial `p`-th roots,

`|Σ_n c'(n) 𝔅(p, n)/n²| ≤ ((p² - 1)/12)(π²σ_p/6 + 2 S₀/p²)`.

With the second-order law this bounds the cross-scale remainder of every row `c` on primes:

`|B + m R' + β H'| ≤ (π²/72) Σ_p |c(p)| p σ_p + (S₀/6) Σ_p |c(p)|/p + ¾ Σ_p |c(p)| p² Σ_n |c'(n)|/n³`.

The rank-two remainder bound `(Σ|c(p)| p) S₀` improves exactly by the normalized Fourier mass
`σ_p/S₀` of the large-scale coefficients at the rationals `k/p`. Coherent windows have `σ_p ≍ S₀` and
attain the rank-two remainder bound. The Type-II input at one modulus is the size of
`Σ_n c'(n) e(kn/p)/n²`, and its loss is `σ_p/S₀`.
-/

open Finset Filter Topology Complex RHTower GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Nontrivial roots of unity -/

/-- The nontrivial `d`-th roots of unity. -/
def nontrivialRoots (d : ℕ) : Finset ℂ := (Polynomial.nthRootsFinset d (1 : ℂ)).erase 1

theorem mem_nontrivialRoots {d : ℕ} (hd : 0 < d) {η : ℂ} :
    η ∈ nontrivialRoots d ↔ η ≠ 1 ∧ η ^ d = 1 := by
  rw [nontrivialRoots, mem_erase, Polynomial.mem_nthRootsFinset hd]

theorem norm_eq_one_of_mem_nontrivialRoots {d : ℕ} (hd : 0 < d) {η : ℂ}
    (hη : η ∈ nontrivialRoots d) : ‖η‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one ((mem_nontrivialRoots hd).mp hη).2 hd.ne'

theorem card_nontrivialRoots {d : ℕ} (hd : 0 < d) : (nontrivialRoots d).card = d - 1 := by
  rw [nontrivialRoots, card_erase_of_mem ((Polynomial.mem_nthRootsFinset hd 1).mpr (one_pow d)),
    (Complex.isPrimitiveRoot_exp d hd.ne').card_nthRootsFinset]

/-- Orthogonality on the nontrivial roots: `Σ_{η ∈ T_d} η^k = d [d ∣ k] - 1`. -/
theorem sum_nontrivialRoots_pow {d : ℕ} (hd : 0 < d) (k : ℕ) :
    ∑ η ∈ nontrivialRoots d, η ^ k = (if d ∣ k then (d : ℂ) else 0) - 1 := by
  rw [nontrivialRoots, ← sum_nthRootsFinset_pow hd k,
    ← add_sum_erase _ _ ((Polynomial.mem_nthRootsFinset hd 1).mpr (one_pow d)), one_pow]
  ring

/-- The inversion pairing: `Σ_{η ∈ T_d} 1/(η - 1) = -(d - 1)/2`. -/
theorem sum_nontrivialRoots_inv_sub_one {d : ℕ} (hd : 0 < d) :
    ∑ η ∈ nontrivialRoots d, 1 / (η - 1) = -((d : ℂ) - 1) / 2 := by
  have hne : ∀ η ∈ nontrivialRoots d, η ≠ 0 := fun η hη h => by
    have := ((mem_nontrivialRoots hd).mp hη).2
    rw [h, zero_pow hd.ne'] at this
    exact zero_ne_one this
  have hinv : ∑ η ∈ nontrivialRoots d, 1 / (η - 1) = ∑ η ∈ nontrivialRoots d, 1 / (η⁻¹ - 1) := by
    refine sum_nbij' (fun η => η⁻¹) (fun η => η⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro η hη
      obtain ⟨h1, hd'⟩ := (mem_nontrivialRoots hd).mp hη
      exact (mem_nontrivialRoots hd).mpr ⟨fun h => h1 (inv_eq_one.mp h), by rw [inv_pow, hd', inv_one]⟩
    · intro η hη
      obtain ⟨h1, hd'⟩ := (mem_nontrivialRoots hd).mp hη
      exact (mem_nontrivialRoots hd).mpr ⟨fun h => h1 (inv_eq_one.mp h), by rw [inv_pow, hd', inv_one]⟩
    · intro η _; simp
    · intro η _; simp
    · intro η _; simp
  have hpair : ∀ η ∈ nontrivialRoots d, 1 / (η - 1) + 1 / (η⁻¹ - 1) = -1 := fun η hη => by
    have h1 : η - 1 ≠ 0 := sub_ne_zero.mpr ((mem_nontrivialRoots hd).mp hη).1
    have h0 := hne η hη
    have h3 : 1 - η ≠ 0 := sub_ne_zero.mpr (Ne.symm ((mem_nontrivialRoots hd).mp hη).1)
    rw [show η⁻¹ - 1 = (1 - η) / η by field_simp, one_div_div,
      show 1 - η = -(η - 1) by ring, div_neg, ← sub_eq_add_neg, div_sub_div_same]
    rw [show 1 - η = -(η - 1) by ring, neg_div, div_self h1]
  have h2 : 2 * ∑ η ∈ nontrivialRoots d, 1 / (η - 1) = -((d : ℂ) - 1) := by
    rw [two_mul]
    nth_rewrite 2 [hinv]
    rw [← sum_add_distrib, sum_congr rfl hpair, sum_const, card_nontrivialRoots hd, nsmul_eq_mul,
      Nat.cast_sub hd, Nat.cast_one, mul_neg_one]
  linear_combination h2 / 2

/-! ## §2. Spectral forms of the residue and of its potential -/

/-- `r_d(M + 1) - r_d(M) = 1 - d [d ∣ M + 1]`. -/
theorem centeredResidue_succ_sub {d : ℕ} (hd : 0 < d) (M : ℕ) :
    centeredResidue d (M + 1) - centeredResidue d M = if d ∣ M + 1 then 1 - (d : ℝ) else 1 := by
  have hlt := Nat.mod_lt M hd
  unfold centeredResidue
  rcases Nat.lt_or_ge (M % d + 1) d with h | h
  · have hm : (M + 1) % d = M % d + 1 := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < d by omega), Nat.mod_eq_of_lt h]
    have hndvd : ¬ d ∣ M + 1 := fun hdvd => by
      rw [Nat.dvd_iff_mod_eq_zero] at hdvd; omega
    rw [if_neg hndvd, hm]
    push_cast
    ring
  · have hr : M % d + 1 = d := by omega
    have hm : (M + 1) % d = 0 := by
      have h' : M + 1 = d * (M / d + 1) := by
        have := Nat.div_add_mod M d
        rw [mul_add, mul_one]; omega
      rw [h', Nat.mul_mod_right]
    have hdvd : d ∣ M + 1 := Nat.dvd_of_mod_eq_zero hm
    have hrR : ((M % d : ℕ) : ℝ) = (d : ℝ) - 1 := by
      have := congrArg (Nat.cast : ℕ → ℝ) hr
      push_cast at this; linarith
    rw [if_pos hdvd, hm, hrR]
    push_cast
    ring

/-- `r_d(M) = -Σ_{η ∈ T_d} η^{M+1}/(η - 1)`. -/
theorem centeredResidue_eq_spectral {d : ℕ} (hd : 0 < d) (M : ℕ) :
    (centeredResidue d M : ℂ) = -∑ η ∈ nontrivialRoots d, η ^ (M + 1) / (η - 1) := by
  have h1 : ∀ η ∈ nontrivialRoots d, η - 1 ≠ 0 := fun η hη =>
    sub_ne_zero.mpr ((mem_nontrivialRoots hd).mp hη).1
  induction M with
  | zero =>
    have h : ∑ η ∈ nontrivialRoots d, η ^ (0 + 1) / (η - 1) =
        ∑ η ∈ nontrivialRoots d, (1 + 1 / (η - 1)) := sum_congr rfl fun η hη => by
      field_simp [h1 η hη]; ring
    rw [h, sum_add_distrib, sum_nontrivialRoots_inv_sub_one hd, sum_const, card_nontrivialRoots hd,
      nsmul_eq_mul, Nat.cast_sub hd]
    simp [centeredResidue]
    ring
  | succ M ih =>
    have hstep : ∑ η ∈ nontrivialRoots d, η ^ (M + 1 + 1) / (η - 1) -
        ∑ η ∈ nontrivialRoots d, η ^ (M + 1) / (η - 1) = ∑ η ∈ nontrivialRoots d, η ^ (M + 1) := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun η hη => by field_simp [h1 η hη]; ring
    rw [sum_nontrivialRoots_pow hd] at hstep
    have hcr := centeredResidue_succ_sub hd M
    have hcrC : (centeredResidue d (M + 1) : ℂ) = (centeredResidue d M : ℂ) +
        (if d ∣ M + 1 then 1 - (d : ℂ) else 1) := by
      rw [← sub_eq_iff_eq_add', ← Complex.ofReal_sub, hcr]
      split_ifs <;> push_cast <;> ring
    rw [hcrC, ih]
    split_ifs at hstep ⊢ <;> linear_combination hstep

/-- `|η - 1|^{-2} = -η/(η - 1)²` on the unit circle. -/
theorem inv_norm_sub_one_sq_eq {η : ℂ} (hη : ‖η‖ = 1) (h1 : η ≠ 1) :
    (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) = -η / (η - 1) ^ 2 := by
  have h0 : η ≠ 0 := fun h => by rw [h, norm_zero] at hη; exact zero_ne_one hη
  have hsub : η - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hconj : conj η = η⁻¹ := (Complex.inv_eq_conj hη).symm
  have hn : ((‖η - 1‖ ^ 2 : ℝ) : ℂ) = (η - 1) * (η⁻¹ - 1) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sub, map_one, hconj]
  rw [Complex.ofReal_inv, hn]
  field_simp
  ring

/-- **Fourier form of the residue potential.** `Φ_d(M) = Σ_{η ∈ T_d} η^M/|η - 1|²`. -/
theorem residuePotential_eq_spectral {d : ℕ} (hd : 0 < d) (M : ℕ) :
    (residuePotential d M : ℂ) =
      ∑ η ∈ nontrivialRoots d, (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * η ^ M := by
  set Ψ : ℕ → ℂ := fun M => ∑ η ∈ nontrivialRoots d, (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * η ^ M
  have hw : ∀ η ∈ nontrivialRoots d, (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) = -η / (η - 1) ^ 2 :=
    fun η hη => inv_norm_sub_one_sq_eq (norm_eq_one_of_mem_nontrivialRoots hd hη)
      ((mem_nontrivialRoots hd).mp hη).1
  have hstep : ∀ M, Ψ (M + 1) - Ψ M = (centeredResidue d M : ℂ) := by
    intro M
    rw [centeredResidue_eq_spectral hd, ← sum_neg_distrib]
    simp only [Ψ, ← sum_sub_distrib]
    refine sum_congr rfl fun η hη => ?_
    rw [hw η hη]
    have h1 : η - 1 ≠ 0 := sub_ne_zero.mpr ((mem_nontrivialRoots hd).mp hη).1
    field_simp
    ring
  have hconst : ∀ M, (residuePotential d M : ℂ) - Ψ M = (residuePotential d 0 : ℂ) - Ψ 0 := by
    intro M
    induction M with
    | zero => rfl
    | succ M ih =>
      rw [← ih]
      have h := residuePotential_succ_sub hd M
      have hC : (residuePotential d (M + 1) : ℂ) = residuePotential d M + centeredResidue d M := by
        rw [← h]; push_cast; ring
      rw [hC, ← hstep M]
      ring
  have hperΨ : ∑ M ∈ range d, Ψ M = 0 := by
    simp only [Ψ]
    rw [sum_comm]
    refine sum_eq_zero fun η hη => ?_
    rw [← mul_sum]
    obtain ⟨h1, hdη⟩ := (mem_nontrivialRoots hd).mp hη
    rw [geom_sum_eq h1, hdη, sub_self, zero_div, mul_zero]
  have hperΦ : ∑ M ∈ range d, (residuePotential d M : ℂ) = 0 := by
    have h := sum_Ico_residuePotential_period hd 0
    rw [zero_add, ← range_eq_Ico] at h
    exact_mod_cast h
  have hsum : ∑ M ∈ range d, ((residuePotential d M : ℂ) - Ψ M) = 0 := by
    rw [sum_sub_distrib, hperΦ, hperΨ, sub_zero]
  rw [sum_congr rfl fun M _ => hconst M, sum_const, card_range, nsmul_eq_mul] at hsum
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have h0 := (mul_eq_zero.mp hsum).resolve_left hd0
  have := hconst M
  rw [h0] at this
  exact sub_eq_zero.mp this

/-- The Fourier coefficients sum to `Φ_d(0) = (d² - 1)/12`. -/
theorem sum_nontrivialRoots_inv_norm_sq {d : ℕ} (hd : 0 < d) :
    ∑ η ∈ nontrivialRoots d, (‖η - 1‖ ^ 2)⁻¹ = ((d : ℝ) ^ 2 - 1) / 12 := by
  have h := residuePotential_eq_spectral hd 0
  simp only [pow_zero, mul_one] at h
  have h' : (residuePotential d 0 : ℂ) = ((∑ η ∈ nontrivialRoots d, (‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [h]; push_cast; rfl
  have := Complex.ofReal_injective h'
  rw [← this, residuePotential]
  simp

/-! ## §3. The Bernoulli kernel against a large-scale row -/

/-- The weighted Fourier transform `S(z) = Σ_n (c'(n)/n²) zⁿ` of a large-scale row. -/
def rowTransform (N : ℕ) (c' : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N, ((c' n / (n : ℝ) ^ 2 : ℝ) : ℂ) * z ^ n

theorem norm_rowTransform_one_le (N : ℕ) (c' : ℕ → ℝ) :
    ‖rowTransform N c' 1‖ ≤ ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2 := by
  refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n _ => ?_))
  rw [one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]

/-- `Σ_n (c'(n)/n²) Φ_d(jn) = Σ_{η ∈ T_d} |η - 1|^{-2} S(η^j)`. -/
theorem sum_mul_residuePotential_eq_spectral {d : ℕ} (hd : 0 < d) (N j : ℕ) (c' : ℕ → ℝ) :
    ((∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * residuePotential d (j * n) : ℝ) : ℂ) =
      ∑ η ∈ nontrivialRoots d, (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * rowTransform N c' (η ^ j) := by
  push_cast
  simp_rw [residuePotential_eq_spectral hd, rowTransform, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun η _ => sum_congr rfl fun n _ => ?_
  rw [pow_mul]
  push_cast
  ring

/-- For a prime `p`, the powers `η^m` with `p ∤ m` of a nontrivial `p`-th root are nontrivial. -/
theorem pow_mem_nontrivialRoots {p : ℕ} (hp : p.Prime) {η : ℂ} (hη : η ∈ nontrivialRoots p) {m : ℕ}
    (hm : ¬ p ∣ m) : η ^ m ∈ nontrivialRoots p := by
  obtain ⟨h1, hpη⟩ := (mem_nontrivialRoots hp.pos).mp hη
  haveI := Fact.mk hp
  have hord : orderOf η = p := orderOf_eq_prime hpη h1
  refine (mem_nontrivialRoots hp.pos).mpr ⟨fun h => hm ?_, by rw [← pow_mul, mul_comm, pow_mul,
    hpη, one_pow]⟩
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one h

/-- The `j`-th Bernoulli layer: `|Σ_n (c'(n)/n²) Φ_p(jn)| ≤ ((p² - 1)/12)(σ or S₀)`. -/
theorem abs_sum_mul_residuePotential_le {p : ℕ} (hp : p.Prime) (N j : ℕ) (c' : ℕ → ℝ) {σ : ℝ}
    (hσ : ∀ ζ ∈ nontrivialRoots p, ‖rowTransform N c' ζ‖ ≤ σ) :
    |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * residuePotential p (j * n)| ≤
      ((p : ℝ) ^ 2 - 1) / 12 * (if p ∣ j then ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2 else σ) := by
  rw [← Real.norm_eq_abs, ← Complex.norm_real, sum_mul_residuePotential_eq_spectral hp.pos,
    ← sum_nontrivialRoots_inv_norm_sq hp.pos, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun η hη => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  split_ifs with hpj
  · obtain ⟨t, rfl⟩ := hpj
    rw [pow_mul, ((mem_nontrivialRoots hp.pos).mp hη).2, one_pow]
    exact norm_rowTransform_one_le N c'
  · exact hσ _ (pow_mem_nontrivialRoots hp hη hpj)

theorem sum_range_ite_dvd_div_sq_le {p : ℕ} (hp : 0 < p) (K : ℕ) :
    ∑ j ∈ range K, (if p ∣ j + 1 then 1 / ((j : ℝ) + 1) ^ 2 else 0) ≤ 2 / (p : ℝ) ^ 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hre : ∑ j ∈ range K, (if p ∣ j + 1 then 1 / ((j : ℝ) + 1) ^ 2 else 0) =
      ∑ m ∈ (Icc 1 K).filter (fun m => p ∣ m), 1 / (m : ℝ) ^ 2 := by
    rw [sum_filter]
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, ih, sum_Icc_succ_top (by omega)]
      push_cast
      rfl
  rw [hre]
  have hsub : (Icc 1 K).filter (fun m => p ∣ m) ⊆ (Icc 1 K).image (fun k => p * k) := by
    intro m hm
    obtain ⟨hmI, ⟨k, rfl⟩⟩ := mem_filter.mp hm
    have := mem_Icc.mp hmI
    refine mem_image.mpr ⟨k, mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos k with h | h
      · subst h; omega
      · exact h
    · nlinarith
  calc ∑ m ∈ (Icc 1 K).filter (fun m => p ∣ m), 1 / (m : ℝ) ^ 2
      ≤ ∑ m ∈ (Icc 1 K).image (fun k => p * k), 1 / (m : ℝ) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => by positivity
    _ = ∑ k ∈ Icc 1 K, 1 / ((p : ℝ) ^ 2) * (1 / (k : ℝ) ^ 2) := by
        rw [sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp h]
        refine sum_congr rfl fun k _ => ?_
        push_cast
        rw [mul_pow, one_div_mul_one_div]
    _ = 1 / (p : ℝ) ^ 2 * ∑ k ∈ Icc 1 K, 1 / (k : ℝ) ^ 2 := by rw [mul_sum]
    _ ≤ 1 / (p : ℝ) ^ 2 * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rcases Nat.eq_zero_or_pos K with h0 | hK
        · subst h0; simp
        · have := sum_Icc_one_div_sq_le hK
          have : 0 ≤ 1 / (K : ℝ) := by positivity
          linarith
    _ = 2 / (p : ℝ) ^ 2 := by ring

/-- **The Bernoulli kernel against a large-scale row.** If `|S(ζ)| ≤ σ` on the nontrivial `p`-th
roots, then `|Σ_n c'(n) 𝔅(p, n)/n²| ≤ ((p² - 1)/12)(π² σ/6 + 2 S₀/p²)`. -/
theorem abs_sum_mul_bernoulliKernel_le {p : ℕ} (hp : p.Prime) (N : ℕ) (c' : ℕ → ℝ) {σ : ℝ}
    (hσ : ∀ ζ ∈ nontrivialRoots p, ‖rowTransform N c' ζ‖ ≤ σ) :
    |∑ n ∈ Icc 1 N, c' n * (bernoulliKernel p n / (n : ℝ) ^ 2)| ≤
      ((p : ℝ) ^ 2 - 1) / 12 * (Real.pi ^ 2 / 6 * σ +
        2 / (p : ℝ) ^ 2 * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2) := by
  set S₀ := ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2
  have hS₀ : 0 ≤ S₀ := sum_nonneg fun n _ => by positivity
  have hσ0 : 0 ≤ σ := by
    have hmem : Complex.exp (2 * Real.pi * Complex.I / p) ∈ nontrivialRoots p :=
      (mem_nontrivialRoots hp.pos).mpr ⟨(Complex.isPrimitiveRoot_exp p hp.ne_zero).ne_one
        hp.one_lt, (Complex.isPrimitiveRoot_exp p hp.ne_zero).pow_eq_one⟩
    exact (norm_nonneg _).trans (hσ _ hmem)
  have hz : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  set t : ℕ → ℝ := fun j => ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
    (residuePotential p ((j + 1) * n) / ((j : ℝ) + 1) ^ 2)
  have ht : HasSum t (∑ n ∈ Icc 1 N, c' n * (bernoulliKernel p n / (n : ℝ) ^ 2)) := by
    have h := hasSum_sum fun n (_ : n ∈ Icc 1 N) =>
      (hasSum_bernoulliKernel hp.pos n).mul_left (c' n / (n : ℝ) ^ 2)
    have he : ∑ n ∈ Icc 1 N, c' n * (bernoulliKernel p n / (n : ℝ) ^ 2) =
        ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * bernoulliKernel p n :=
      sum_congr rfl fun n _ => by ring
    rw [he]
    exact h
  have hbound : ∀ K, |∑ j ∈ range K, t j| ≤ ((p : ℝ) ^ 2 - 1) / 12 *
      (Real.pi ^ 2 / 6 * σ + 2 / (p : ℝ) ^ 2 * S₀) := by
    intro K
    have hp2 : (0 : ℝ) ≤ ((p : ℝ) ^ 2 - 1) / 12 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      nlinarith
    calc |∑ j ∈ range K, t j| ≤ ∑ j ∈ range K, |t j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range K, ((p : ℝ) ^ 2 - 1) / 12 *
            (σ * (1 / ((j : ℝ) + 1) ^ 2) +
              S₀ * (if p ∣ j + 1 then 1 / ((j : ℝ) + 1) ^ 2 else 0)) := by
          refine sum_le_sum fun j _ => ?_
          have h := abs_sum_mul_residuePotential_le hp N (j + 1) c' hσ
          have hrw : t j = (∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * residuePotential p ((j + 1) * n)) *
              (1 / ((j : ℝ) + 1) ^ 2) := by
            simp only [t, sum_mul]
            exact sum_congr rfl fun n _ => by ring
          rw [hrw, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((j : ℝ) + 1) ^ 2)]
          refine (mul_le_mul_of_nonneg_right h (by positivity)).trans ?_
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hp2
          split_ifs <;> nlinarith [show (0 : ℝ) ≤ 1 / ((j : ℝ) + 1) ^ 2 by positivity]
      _ = ((p : ℝ) ^ 2 - 1) / 12 * (σ * ∑ j ∈ range K, 1 / ((j : ℝ) + 1) ^ 2 +
            S₀ * ∑ j ∈ range K, (if p ∣ j + 1 then 1 / ((j : ℝ) + 1) ^ 2 else 0)) := by
          rw [← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum]
      _ ≤ ((p : ℝ) ^ 2 - 1) / 12 * (σ * (Real.pi ^ 2 / 6) + S₀ * (2 / (p : ℝ) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hp2
          · exact mul_le_mul_of_nonneg_left
              (sum_le_hasSum _ (fun j _ => by positivity) hz) hσ0
          · exact mul_le_mul_of_nonneg_left (sum_range_ite_dvd_div_sq_le hp.pos K) hS₀
      _ = _ := by ring
  exact le_of_tendsto' (ht.tendsto_sum_nat.abs) hbound

/-! ## §4. The exact cross-scale loss -/

/-- **The exact cross-scale loss.** For a row `c` on a set `S` of primes `≤ N`, a large-scale row
`c'`, and bounds `|S(ζ)| ≤ σ_p` on the nontrivial `p`-th roots,
`|B + m R' + β H'| ≤ (π²/72) Σ_p |c(p)| p σ_p + (S₀/6) Σ_p |c(p)|/p + ¾ Σ_p |c(p)| p² Σ_n |c'(n)|/n³`. -/
theorem abs_rowBilinear_add_mean_add_beta_le_fourier {N : ℕ} {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N) {c c' : ℕ → ℝ} (hsupp : ∀ n, c n ≠ 0 → n ∈ S)
    (σ : ℕ → ℝ) (hσ : ∀ p ∈ S, ∀ ζ ∈ nontrivialRoots p, ‖rowTransform N c' ζ‖ ≤ σ p) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c'| ≤
      Real.pi ^ 2 / 72 * ∑ p ∈ S, |c p| * p * σ p +
        (∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2) / 6 * ∑ p ∈ S, |c p| / p +
        3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 := by
  set S₀ := ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2
  have hsub : S ⊆ Icc 1 N := fun p hp => mem_Icc.mpr ⟨(hS p hp).1.one_lt.le, (hS p hp).2⟩
  have hlaw := abs_rowBilinear_add_mean_add_beta_sub_bernoulli_le N c c'
  set M := ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) * (bernoulliKernel d n / (n : ℝ) ^ 2)
  have hM : M = ∑ p ∈ S, c p / p * ∑ n ∈ Icc 1 N, c' n * (bernoulliKernel p n / (n : ℝ) ^ 2) := by
    simp only [M]
    rw [sum_comm, ← sum_subset hsub fun d _ hd => by
      have : c d = 0 := by by_contra h; exact hd (hsupp d h)
      simp [this]]
    refine sum_congr rfl fun p _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun n _ => by ring
  have hMb : |M| ≤ Real.pi ^ 2 / 72 * ∑ p ∈ S, |c p| * p * σ p + S₀ / 6 * ∑ p ∈ S, |c p| / p := by
    rw [hM, mul_sum, mul_sum, ← sum_add_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p hpS => ?_)
    have hp := (hS p hpS).1
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hk := abs_sum_mul_bernoulliKernel_le hp N c' (hσ p hpS)
    have hσ0 : 0 ≤ σ p := by
      have hmem : Complex.exp (2 * Real.pi * Complex.I / p) ∈ nontrivialRoots p :=
        (mem_nontrivialRoots hp.pos).mpr ⟨(Complex.isPrimitiveRoot_exp p hp.ne_zero).ne_one
          hp.one_lt, (Complex.isPrimitiveRoot_exp p hp.ne_zero).pow_eq_one⟩
      exact (norm_nonneg _).trans (hσ p hpS _ hmem)
    have hS₀ : 0 ≤ S₀ := sum_nonneg fun n _ => by positivity
    rw [abs_mul, abs_div, abs_of_pos (by linarith : (0 : ℝ) < p)]
    calc |c p| / p * |∑ n ∈ Icc 1 N, c' n * (bernoulliKernel p n / (n : ℝ) ^ 2)|
        ≤ |c p| / p * (((p : ℝ) ^ 2 - 1) / 12 * (Real.pi ^ 2 / 6 * σ p + 2 / (p : ℝ) ^ 2 * S₀)) :=
          mul_le_mul_of_nonneg_left hk (by positivity)
      _ ≤ Real.pi ^ 2 / 72 * (|c p| * p * σ p) + S₀ / 6 * (|c p| / p) := by
          have hc := abs_nonneg (c p)
          have hpi := Real.pi_pos
          have e1 : |c p| / p * (((p : ℝ) ^ 2 - 1) / 12 * (Real.pi ^ 2 / 6 * σ p)) ≤
              Real.pi ^ 2 / 72 * (|c p| * p * σ p) := by
            rw [show |c p| / p * (((p : ℝ) ^ 2 - 1) / 12 * (Real.pi ^ 2 / 6 * σ p)) =
              Real.pi ^ 2 / 72 * (|c p| * p * σ p) - Real.pi ^ 2 / 72 * (|c p| * σ p / p) by
                field_simp; ring]
            have : 0 ≤ Real.pi ^ 2 / 72 * (|c p| * σ p / p) := by positivity
            linarith
          have e2 : |c p| / p * (((p : ℝ) ^ 2 - 1) / 12 * (2 / (p : ℝ) ^ 2 * S₀)) ≤
              S₀ / 6 * (|c p| / p) := by
            rw [show |c p| / p * (((p : ℝ) ^ 2 - 1) / 12 * (2 / (p : ℝ) ^ 2 * S₀)) =
              S₀ / 6 * (|c p| / p) - S₀ / 6 * (|c p| / p) / (p : ℝ) ^ 2 by field_simp; ring]
            have : 0 ≤ S₀ / 6 * (|c p| / p) / (p : ℝ) ^ 2 := by positivity
            linarith
          nlinarith [e1, e2]
  calc |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c'|
      ≤ |M| + 3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 := by
        have := abs_sub_abs_le_abs_sub (rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
          rowBeta N c * finiteHarmonicSum N c') M
        linarith
    _ ≤ _ := by linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
