import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.LiouvilleBoundaryPath
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.PrimeAbelCutoff
import GaloisForLFunctions.HTGeometry.PrimeOccupationCompletionProduct
import GaloisForLFunctions.RHTower.MertensThirdTheorem

/-!
# The sharp Liouville product at a moving prime cutoff

The finite Liouville residue product is the square of Mertens' product
times the prime-square Euler product. Its logarithm approximates the
actual boundary-path residue with an error tending to zero.
-/

open Complex Filter Topology Metric Set Finset
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- The prime-by-prime logarithm of the sharp Liouville residue ratio. -/
def liouvillePrimeLog (p : Nat.Primes) : ℂ :=
  Complex.log (1 - (p : ℂ)⁻¹) - Complex.log (1 + (p : ℂ)⁻¹)

/-- The marked primes at or below a natural cutoff. -/
def residuePrimeCutoff (N : ℕ) : Finset Nat.Primes := (range (N + 1)).subtype Nat.Prime

/-- The finite sharp-cutoff logarithm of the Liouville residue product. -/
def liouvilleCutoffLog (N : ℕ) : ℂ :=
  ∑ p ∈ residuePrimeCutoff N, liouvillePrimeLog p

theorem mem_residuePrimeCutoff {N : ℕ} {p : Nat.Primes} :
    p ∈ residuePrimeCutoff N ↔ (p : ℕ) ≤ N := by
  change (show Subtype Nat.Prime from p) ∈ (Finset.range (N + 1)).subtype Nat.Prime ↔ _
  simp only [Finset.mem_subtype, Finset.mem_range, Nat.lt_succ_iff]

theorem card_residuePrimeCutoff (N : ℕ) : (residuePrimeCutoff N).card = Nat.primeCounting N := by
  change ((Finset.range (N + 1)).subtype Nat.Prime).card = _
  rw [Finset.card_subtype]
  exact Nat.primesLE_card_eq_primeCounting N

private theorem image_residuePrimeCutoff (N : ℕ) :
    (residuePrimeCutoff N).image (fun p : Nat.Primes => (p : ℕ)) = Nat.primesLE N := by
  ext n
  simp only [Finset.mem_image, mem_residuePrimeCutoff, Nat.mem_primesLE]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨hp, p.2⟩
  · rintro ⟨hn, hp⟩
    exact ⟨⟨n, hp⟩, hn, rfl⟩

private theorem prod_residuePrimeCutoff {A : Type*} [CommMonoid A] (N : ℕ) (f : ℕ → A) :
    (∏ p ∈ residuePrimeCutoff N, f (p : ℕ)) = ∏ n ∈ Nat.primesLE N, f n := by
  rw [← image_residuePrimeCutoff N, Finset.prod_image
    (fun (p : Nat.Primes) _ (q : Nat.Primes) _ h => Subtype.ext h)]

private theorem boundaryPhase_real (p : Nat.Primes) (t : ℝ) :
    liouvilleBoundaryPhase p (t : ℂ) =
      Complex.exp (I * ((Real.pi * t ^ (p : ℕ) : ℝ) : ℂ)) := by
  unfold liouvilleBoundaryPhase
  congr 1
  push_cast
  ring

private theorem norm_boundaryPhase_real (p : Nat.Primes) (t : ℝ) :
    ‖liouvilleBoundaryPhase p (t : ℂ)‖ = 1 := by
  rw [liouvilleBoundaryPhase_eq_twist]
  exact norm_twist_prime _ p p.2

/-- The perturbation of the trivial phase has geometric decay on the real interval. -/
theorem boundaryPhase_sub_one_le (p : Nat.Primes) {t : ℝ} (ht : 0 ≤ t) :
    ‖liouvilleBoundaryPhase p (t : ℂ) - 1‖ ≤ Real.pi * t ^ (p : ℕ) := by
  rw [boundaryPhase_real]
  have hh := Real.norm_exp_I_mul_ofReal_sub_one_le (x := Real.pi * t ^ (p : ℕ))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg Real.pi_pos.le (pow_nonneg ht _))]
    using hh

/-- Below the transition cutoff, the perturbation of the Liouville phase is linear in p(1-t). -/
theorem boundaryPhase_add_one_le (p : Nat.Primes) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖liouvilleBoundaryPhase p (t : ℂ) + 1‖ ≤ Real.pi * (p : ℝ) * (1 - t) := by
  have hp : t ^ (p : ℕ) ≤ 1 := pow_le_one₀ ht ht1
  have he : liouvilleBoundaryPhase p (t : ℂ) =
      -Complex.exp (I * ((Real.pi * (t ^ (p : ℕ) - 1) : ℝ) : ℂ)) := by
    rw [boundaryPhase_real, show I * ((Real.pi * t ^ (p : ℕ) : ℝ) : ℂ) =
      I * ((Real.pi * (t ^ (p : ℕ) - 1) : ℝ) : ℂ) + (Real.pi : ℂ) * I by
        push_cast; ring, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]
  rw [he, show -Complex.exp (I * ((Real.pi * (t ^ (p : ℕ) - 1) : ℝ) : ℂ)) + 1 =
      -(Complex.exp (I * ((Real.pi * (t ^ (p : ℕ) - 1) : ℝ) : ℂ)) - 1) by ring, norm_neg]
  have hh := Real.norm_exp_I_mul_ofReal_sub_one_le (x := Real.pi * (t ^ (p : ℕ) - 1))
  have hnorm : ‖Real.pi * (t ^ (p : ℕ) - 1)‖ = Real.pi * (1 - t ^ (p : ℕ)) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos, abs_of_nonpos (sub_nonpos.mpr hp)]
    ring
  rw [hnorm] at hh
  have hsum : (∑ i ∈ range (p : ℕ), t ^ i) ≤ (p : ℝ) := by
    calc _ ≤ ∑ _i ∈ range (p : ℕ), (1 : ℝ) := sum_le_sum (fun i _ => pow_le_one₀ ht ht1)
         _ = _ := by simp
  have hpow : 1 - t ^ (p : ℕ) ≤ (p : ℝ) * (1 - t) := by
    rw [← geom_sum_mul_neg t (p : ℕ)]
    exact mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr ht1)
  exact hh.trans ((mul_le_mul_of_nonneg_left hpow Real.pi_pos.le).trans_eq (by ring))

private theorem prime_decay_at_one (p : Nat.Primes) :
    Complex.exp (-(primeFrequency p : ℂ)) = (p : ℂ)⁻¹ := by
  change Complex.exp (-((Real.log (p : ℝ) : ℝ) : ℂ)) = (p : ℂ)⁻¹
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg,
    Real.exp_log (by exact_mod_cast p.2.pos : (0 : ℝ) < (p : ℝ))]
  push_cast
  rfl

theorem jointEulerChange_at_one (p : Nat.Primes) (z : ℂ) :
    jointEulerChange liouvilleBoundaryPhase p (z, 1) =
      Complex.log (1 - (p : ℂ)⁻¹) -
        Complex.log (1 - liouvilleBoundaryPhase p z * (p : ℂ)⁻¹) := by
  simp only [jointEulerChange, one_mul, prime_decay_at_one]

private theorem prime_inv_norm (p : Nat.Primes) : ‖(p : ℂ)⁻¹‖ = (p : ℝ)⁻¹ := by
  rw [norm_inv, Complex.norm_natCast]

private theorem prime_inv_le_half (p : Nat.Primes) : (p : ℝ)⁻¹ ≤ 1 / 2 := by
  rw [← one_div]
  exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast p.2.two_le)

/-- Above the cutoff, the Euler logarithm change is bounded by the geometric prime tail. -/
theorem norm_boundaryEulerChange_le (p : Nat.Primes) {t : ℝ} (ht : 0 ≤ t) :
    ‖jointEulerChange liouvilleBoundaryPhase p ((t : ℂ), 1)‖ ≤
      2 * Real.pi * t ^ (p : ℕ) * (p : ℝ)⁻¹ := by
  rw [jointEulerChange_at_one]
  have hh := norm_log_euler_change_le (by norm_num : (1 : ℝ) ≤ 1)
    (norm_boundaryPhase_real p t).le
    ((prime_inv_norm p).le.trans (prime_inv_le_half p)) (by norm_num : (1 : ℝ) * (1 / 2) < 1)
  norm_num only at hh
  rw [prime_inv_norm] at hh
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (boundaryPhase_sub_one_le p ht) (by norm_num : (0 : ℝ) ≤ 2))
    (show 0 ≤ (p : ℝ)⁻¹ by positivity)
  exact hh.trans (hb.trans_eq (by ring))

/-- Below the cutoff, each logarithm differs from its Liouville limit by at most 2π(1-t). -/
theorem norm_boundaryEulerChange_sub_liouville_le (p : Nat.Primes) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖jointEulerChange liouvilleBoundaryPhase p ((t : ℂ), 1) - liouvillePrimeLog p‖ ≤
      2 * Real.pi * (1 - t) := by
  have hd : ‖-(p : ℂ)⁻¹‖ ≤ 1 / 2 := by
    rw [norm_neg, prime_inv_norm]
    exact prime_inv_le_half p
  have hu : ‖-liouvilleBoundaryPhase p (t : ℂ)‖ ≤ 1 := by
    rw [norm_neg, norm_boundaryPhase_real]
  have hh := norm_log_euler_change_le (by norm_num : (1 : ℝ) ≤ 1) hu hd
    (by norm_num : (1 : ℝ) * (1 / 2) < 1)
  norm_num only at hh
  rw [norm_neg, prime_inv_norm, sub_neg_eq_add, neg_mul_neg,
    show -liouvilleBoundaryPhase p (t : ℂ) - 1 = -(liouvilleBoundaryPhase p (t : ℂ) + 1) by ring,
    norm_neg] at hh
  rw [jointEulerChange_at_one, liouvillePrimeLog,
    show (Complex.log (1 - (p : ℂ)⁻¹) -
      Complex.log (1 - liouvilleBoundaryPhase p (t : ℂ) * (p : ℂ)⁻¹)) -
      (Complex.log (1 - (p : ℂ)⁻¹) - Complex.log (1 + (p : ℂ)⁻¹)) =
      Complex.log (1 + (p : ℂ)⁻¹) -
        Complex.log (1 - liouvilleBoundaryPhase p (t : ℂ) * (p : ℂ)⁻¹) by ring]
  apply hh.trans
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (boundaryPhase_add_one_le p ht ht1) (by norm_num : (0 : ℝ) ≤ 2))
    (show 0 ≤ (p : ℝ)⁻¹ by positivity)
  apply hb.trans_eq
  have hpne : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  field_simp

private theorem summable_boundaryEulerChange {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    Summable (fun p => jointEulerChange liouvilleBoundaryPhase p ((t : ℂ), 1)) := by
  apply ((summable_prime_geometric ht ht1).mul_left (2 * Real.pi)).of_norm_bounded
  intro p
  have hb := norm_boundaryEulerChange_le p ht
  have hc : 0 ≤ 2 * Real.pi * t ^ (p : ℕ) := by positivity
  have hinv : (p : ℝ)⁻¹ ≤ 1 := (prime_inv_le_half p).trans (by norm_num)
  exact hb.trans ((mul_le_mul_of_nonneg_left hinv hc).trans_eq (mul_one _))

/-- The complete complex logarithm error is controlled by prime counting and Abel mass. -/
theorem norm_boundaryExponent_sub_cutoff_le {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    {N : ℕ} (hN : 0 < N) :
    ‖jointDeformationExponent liouvilleBoundaryPhase ((t : ℂ), 1) - liouvilleCutoffLog N‖ ≤
      2 * Real.pi * (1 - t) * Nat.primeCounting N +
        (2 * Real.pi / N) * primeAbelMass t := by
  let S := residuePrimeCutoff N
  let v : Nat.Primes → ℂ := fun p => if p ∈ S then liouvillePrimeLog p else 0
  have hv : Summable v := summable_of_ne_finset_zero (s := S) (by
    intro p hp
    simp only [v, if_neg hp])
  have hvs : (∑' p, v p) = liouvilleCutoffLog N := by
    rw [tsum_eq_sum (s := S) (by intro p hp; simp only [v, if_neg hp])]
    exact sum_congr rfl (fun p hp => if_pos hp)
  let g : Nat.Primes → ℂ := fun p =>
    jointEulerChange liouvilleBoundaryPhase p ((t : ℂ), 1) - v p
  have hg : Summable g := (summable_boundaryEulerChange ht ht1).sub hv
  have hgs : (∑' p, g p) =
      jointDeformationExponent liouvilleBoundaryPhase ((t : ℂ), 1) - liouvilleCutoffLog N := by
    dsimp only [g]
    rw [Summable.tsum_sub (summable_boundaryEulerChange ht ht1) hv, hvs]
    rfl
  let b : Nat.Primes → ℝ := fun p =>
    (if p ∈ S then 2 * Real.pi * (1 - t) else 0) + (2 * Real.pi / N) * t ^ (p : ℕ)
  have hbfinite : Summable (fun p : Nat.Primes => if p ∈ S then 2 * Real.pi * (1 - t) else 0) :=
    summable_of_ne_finset_zero (s := S) (by intro p hp; simp only [if_neg hp])
  have hbgeom := (summable_prime_geometric ht ht1).mul_left (2 * Real.pi / N)
  have hb : Summable b := hbfinite.add hbgeom
  have hNb : 0 < (N : ℝ) := by exact_mod_cast hN
  have hbound (p : Nat.Primes) : ‖g p‖ ≤ b p := by
    by_cases hp : p ∈ S
    · simpa only [g, v, b, if_pos hp] using
        (norm_boundaryEulerChange_sub_liouville_le p ht ht1.le).trans
          (le_add_of_nonneg_right (by positivity : 0 ≤ (2 * Real.pi / N) * t ^ (p : ℕ)))
    · have hNp : (N : ℝ) ≤ (p : ℝ) := by
        have hnot : ¬ (p : ℕ) ≤ N := fun h => hp (mem_residuePrimeCutoff.mpr h)
        exact_mod_cast (le_of_lt (Nat.lt_of_not_ge hnot))
      have hinv : (p : ℝ)⁻¹ ≤ (N : ℝ)⁻¹ := inv_anti₀ hNb hNp
      have hle := mul_le_mul_of_nonneg_left hinv
        (show 0 ≤ 2 * Real.pi * t ^ (p : ℕ) by positivity)
      have he : 2 * Real.pi * t ^ (p : ℕ) * (N : ℝ)⁻¹ =
          (2 * Real.pi / N) * t ^ (p : ℕ) := by ring
      simpa only [g, v, b, if_neg hp, sub_zero, zero_add] using
        (norm_boundaryEulerChange_le p ht).trans (hle.trans_eq he)
  have hsum : (∑' p, b p) =
      2 * Real.pi * (1 - t) * Nat.primeCounting N + (2 * Real.pi / N) * primeAbelMass t := by
    dsimp only [b]
    rw [Summable.tsum_add hbfinite hbgeom, tsum_mul_left,
      tsum_eq_sum (s := S) (by intro p hp; simp only [if_neg hp])]
    simp only [sum_ite_of_true (fun p hp => hp), sum_const, nsmul_eq_mul, S,
      card_residuePrimeCutoff, primeAbelMass]
    ring
  rw [← hgs, ← hsum]
  exact (norm_tsum_le_tsum_norm hg.norm).trans (Summable.tsum_le_tsum hbound hg.norm hb)

/-- Exponentiating one sharp-cutoff logarithm gives the exact finite Euler ratio. -/
theorem exp_liouvillePrimeLog (p : Nat.Primes) :
    Complex.exp (liouvillePrimeLog p) =
      (1 - (p : ℂ)⁻¹) ^ 2 * (1 - ((p : ℂ) ^ 2)⁻¹)⁻¹ := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hm : (1 - (p : ℂ)⁻¹) ≠ 0 := by
    have hh : 0 < 1 - (p : ℝ)⁻¹ := by linarith only [prime_inv_le_half p]
    have hc := Complex.ofReal_ne_zero.mpr hh.ne'
    simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv,
      Complex.ofReal_natCast] using hc
  have ha : (1 + (p : ℂ)⁻¹) ≠ 0 := by
    have hh : 0 < 1 + (p : ℝ)⁻¹ := by positivity
    have hc := Complex.ofReal_ne_zero.mpr hh.ne'
    simpa only [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_inv,
      Complex.ofReal_natCast] using hc
  rw [liouvillePrimeLog, Complex.exp_sub, Complex.exp_log hm, Complex.exp_log ha, ← inv_pow,
    show 1 - (p : ℂ)⁻¹ ^ 2 = (1 - (p : ℂ)⁻¹) * (1 + (p : ℂ)⁻¹) by ring]
  field_simp

/-- The finite Liouville ratio splits into the square of Mertens' product and the square-prime product. -/
theorem exp_liouvilleCutoffLog (N : ℕ) :
    Complex.exp (liouvilleCutoffLog N) = (mertensPrimeProduct N : ℂ) ^ 2 *
      ∏ n ∈ Nat.primesLE N, (1 - ((n : ℂ) ^ 2)⁻¹)⁻¹ := by
  have hmR : (∏ p ∈ residuePrimeCutoff N, (1 - (p : ℝ)⁻¹)) = mertensPrimeProduct N := by
    calc
      _ = ∏ n ∈ Nat.primesLE N, (1 - (n : ℝ)⁻¹) :=
        prod_residuePrimeCutoff N (fun n : ℕ => 1 - (n : ℝ)⁻¹)
      _ = _ := by
        rw [Nat.primesLE_eq_filter_Icc_zero, prod_filter]
        rfl
  have hmC : (∏ p ∈ residuePrimeCutoff N, (1 - (p : ℂ)⁻¹)) = (mertensPrimeProduct N : ℂ) := by
    rw [← hmR]
    push_cast
    rfl
  rw [liouvilleCutoffLog, Complex.exp_sum]
  simp_rw [exp_liouvillePrimeLog]
  rw [prod_mul_distrib, Finset.prod_pow, hmC]
  congr 1
  exact prod_residuePrimeCutoff N (fun n : ℕ => (1 - ((n : ℂ) ^ 2)⁻¹)⁻¹)

/-- The sharp Liouville product has the exact logarithmic-square Mertens normalization. -/
theorem tendsto_liouvilleCutoffProduct_normalized :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) : ℂ) ^ 2 * Complex.exp (liouvilleCutoffLog N))
      atTop (𝓝 (riemannZeta 2 * (Real.exp (-2 * Real.eulerMascheroniConstant) : ℂ))) := by
  have hM : Tendsto (fun N : ℕ => ((mertensPrimeProduct N * Real.log N : ℝ) : ℂ)) atTop
      (𝓝 ((Real.exp (-Real.eulerMascheroniConstant) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_mertensPrimeProduct_mul_log
  have hQ := (_root_.HTGeometry.tendsto_prod_primesBelow_riemannZeta (k := 2) (by omega)).comp
    (tendsto_add_atTop_nat 1)
  norm_num only at hQ
  have hh := (hM.pow 2).mul hQ
  have he : ((Real.exp (-Real.eulerMascheroniConstant) : ℝ) : ℂ) ^ 2 * riemannZeta 2 =
      riemannZeta 2 * (Real.exp (-2 * Real.eulerMascheroniConstant) : ℂ) := by
    have hx : Real.exp (-Real.eulerMascheroniConstant) ^ 2 =
        Real.exp (-2 * Real.eulerMascheroniConstant) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [← Complex.ofReal_pow, hx, mul_comm]
  rw [he] at hh
  refine hh.congr (fun N => ?_)
  rw [exp_liouvilleCutoffLog]
  rw [Complex.ofReal_mul]
  change ((mertensPrimeProduct N : ℂ) * (Real.log (N : ℝ) : ℂ)) ^ 2 *
    (∏ n ∈ (N + 1).primesBelow, (1 - ((n : ℂ) ^ 2)⁻¹)⁻¹) = _
  rw [Nat.primesLE]
  ring

#print axioms norm_boundaryExponent_sub_cutoff_le
#print axioms tendsto_liouvilleCutoffProduct_normalized

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
