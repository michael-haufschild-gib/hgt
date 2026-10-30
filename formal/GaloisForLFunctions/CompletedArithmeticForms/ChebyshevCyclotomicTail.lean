import GaloisForLFunctions.CompletedArithmeticForms.ChebyshevCyclotomicCompletion
import GaloisForLFunctions.RHTower.Sieve.InverseSquareTail
import GaloisForLFunctions.RHTower.Sieve.KuzminLandau

/-!
# A square-root band carries the unpaid cyclotomic energy

Outside the first and last `K` roots of unity, the actual Chebyshev cyclotomic
remainder costs at most `288 N (N+1) / K`. The coefficient envelope, the exact
cyclic difference, and an inverse-square tail give this bound.
-/

noncomputable section

open Finset Polynomial

namespace GaloisForLFunctions.CompletedArithmeticForms

/-- The `k`th root of unity in a conductor-`Q` period. -/
def cyclotomicMode (Q k : ℕ) : ℂ :=
  Complex.exp (Complex.I * ((2 * Real.pi * (k : ℝ) / Q : ℝ) : ℂ))

/-- Energy in the modes more than `K` steps from the constant mode. -/
def chebyshevCyclotomicFar (N K : ℕ) : ℝ :=
  (∑ k ∈ (Ico 1 (N + 1)).filter (fun k => K < k ∧ K < N + 1 - k),
    ‖(1 + cyclotomicMode (N + 1) k) *
      prefixPacket (N + 1) chebyshevConductorCoeff (cyclotomicMode (N + 1) k)‖ ^ 2) /
    ((N : ℝ) + 1)

/-- The remaining modes adjacent to the constant mode. -/
def chebyshevCyclotomicNear (N K : ℕ) : ℝ :=
  (∑ k ∈ (Ico 1 (N + 1)).filter (fun k => ¬ (K < k ∧ K < N + 1 - k)),
    ‖(1 + cyclotomicMode (N + 1) k) *
      prefixPacket (N + 1) chebyshevConductorCoeff (cyclotomicMode (N + 1) k)‖ ^ 2) /
    ((N : ℝ) + 1)

private theorem sum_abs_coeff_le (N : ℕ) :
    ∑ j ∈ Icc 1 N, |chebyshevConductorCoeff j| ≤ 12 * Real.sqrt (N : ℝ) := by
  calc
    _ ≤ ∑ j ∈ Icc 1 N, 6 / Real.sqrt (j : ℝ) :=
      sum_le_sum fun j hj => abs_chebyshevConductorCoeff_le (mem_Icc.mp hj).1
    _ = 6 * ∑ j ∈ Icc 1 N, 1 / Real.sqrt (j : ℝ) := by
      rw [mul_sum]
      simp only [mul_one_div]
    _ ≤ 6 * (2 * Real.sqrt (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (_root_.RHTower.sum_inv_sqrt_le N) (by norm_num)
    _ = _ := by ring

theorem norm_cyclotomicMode (Q k : ℕ) : ‖cyclotomicMode Q k‖ = 1 := by
  simp [cyclotomicMode, Complex.norm_exp]

private theorem cyclotomicMode_eq_pow (Q k : ℕ) :
    cyclotomicMode Q k = (Complex.exp (2 * Real.pi * Complex.I / Q)) ^ k := by
  rw [← Complex.exp_nat_mul]
  unfold cyclotomicMode
  congr 1
  push_cast
  ring

/-- The primitive conductor of a mode is its period divided by the numerator gcd. -/
theorem orderOf_cyclotomicMode {Q k : ℕ} (hQ : 0 < Q) (hk : 0 < k) :
    orderOf (cyclotomicMode Q k) = Q / Q.gcd k := by
  rw [cyclotomicMode_eq_pow, orderOf_pow' _ hk.ne',
    ← (Complex.isPrimitiveRoot_exp Q hQ.ne').eq_orderOf]

/-- A mode close to the constant root must have large primitive conductor. -/
theorem le_orderOf_cyclotomicMode_mul_min {Q k : ℕ} (hk0 : 0 < k) (hkQ : k < Q) :
    Q ≤ orderOf (cyclotomicMode Q k) * min k (Q - k) := by
  rw [orderOf_cyclotomicMode (hk0.trans hkQ) hk0]
  have hg : Q.gcd k ≤ min k (Q - k) := le_min
    (Nat.le_of_dvd hk0 (Nat.gcd_dvd_right Q k))
    (Nat.le_of_dvd (Nat.sub_pos_of_lt hkQ)
      (Nat.dvd_sub (Nat.gcd_dvd_left Q k) (Nat.gcd_dvd_right Q k)))
  calc
    Q = Q / Q.gcd k * Q.gcd k := (Nat.div_mul_cancel (Nat.gcd_dvd_left Q k)).symm
    _ ≤ _ := Nat.mul_le_mul_left _ hg

/-- Every conductor at most `L` lies outside the `K`-mode band when `K L < Q`. -/
theorem cyclotomicMode_far_of_orderOf_le {Q k K L : ℕ} (hk0 : 0 < k) (hkQ : k < Q)
    (horder : orderOf (cyclotomicMode Q k) ≤ L) (hKL : K * L < Q) :
    K < k ∧ K < Q - k := by
  have hr : K < min k (Q - k) := by
    by_contra h
    have hrK : min k (Q - k) ≤ K := by omega
    have hbound := (le_orderOf_cyclotomicMode_mul_min hk0 hkQ).trans
      (Nat.mul_le_mul horder hrK)
    rw [Nat.mul_comm L K] at hbound
    omega
  exact ⟨hr.trans_le (min_le_left _ _), hr.trans_le (min_le_right _ _)⟩

private theorem nontrivial_roots_sum_modes {Q : ℕ} (hQ : 0 < Q) (f : ℂ → ℝ) :
    (∑ m ∈ Q.divisors.erase 1, ∑ ζ ∈ primitiveRoots m ℂ, f ζ) =
      ∑ k ∈ Ico 1 Q, f (cyclotomicMode Q k) := by
  classical
  letI : NeZero Q := ⟨hQ.ne'⟩
  let root : ℂ := Complex.exp (2 * Real.pi * Complex.I / Q)
  have hp : IsPrimitiveRoot root Q := Complex.isPrimitiveRoot_exp Q hQ.ne'
  have hroots : nthRootsFinset Q (1 : ℂ) = (range Q).image (fun k => root ^ k) := by
    ext ζ
    rw [Polynomial.mem_nthRootsFinset hQ, mem_image]
    constructor
    · intro hζ
      obtain ⟨k, hk, heq⟩ := hp.eq_pow_of_pow_eq_one hζ
      exact ⟨k, mem_range.mpr hk, heq⟩
    · rintro ⟨k, _, rfl⟩
      rw [← pow_mul, mul_comm k Q, pow_mul, hp.pow_eq_one, one_pow]
  have hperiod : (∑ ζ ∈ nthRootsFinset Q (1 : ℂ), f ζ) =
      ∑ k ∈ range Q, f (cyclotomicMode Q k) := by
    rw [hroots, sum_image (fun k hk l hl heq => hp.pow_inj (mem_range.mp hk) (mem_range.mp hl) heq)]
    exact sum_congr rfl fun k _ => by rw [cyclotomicMode_eq_pow]
  have hall := congrArg Complex.re
    (ArithmeticEffectivityTheory.sum_nthRoots_eq_sum_divisors Q (fun ζ => (f ζ : ℂ)))
  simp only [Complex.re_sum, Complex.ofReal_re] at hall
  have herase := sum_erase_add Q.divisors (fun m => ∑ ζ ∈ primitiveRoots m ℂ, f ζ)
    (Nat.one_mem_divisors.mpr hQ.ne')
  simp only [IsPrimitiveRoot.primitiveRoots_one, sum_singleton] at herase
  have hset : range Q = insert 0 (Ico 1 Q) := by
    ext k
    simp only [mem_range, mem_insert, mem_Ico]
    omega
  rw [hset, sum_insert (by simp)] at hperiod
  have hzero : cyclotomicMode Q 0 = 1 := by simp [cyclotomicMode]
  rw [hzero] at hperiod
  linarith only [hall, herase, hperiod]

/-- The full arithmetic remainder is exactly its near and far root packets. -/
theorem chebyshevCyclotomicRemainder_eq_far_add_near (N K : ℕ) :
    chebyshevCyclotomicRemainder N =
      chebyshevCyclotomicFar N K + chebyshevCyclotomicNear N K := by
  rw [chebyshevCyclotomicRemainder, cyclotomicRemainder,
    nontrivial_roots_sum_modes (by omega : 0 < N + 1)]
  unfold chebyshevCyclotomicFar chebyshevCyclotomicNear
  rw [← add_div, sum_filter_add_sum_filter_not]

private theorem norm_difference_packet_le (N : ℕ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    ‖(1 - ζ) * prefixPacket (N + 1) chebyshevConductorCoeff ζ‖ ≤
      24 * Real.sqrt (N : ℝ) := by
  rw [prefixPacket_difference]
  have hset : Ico 1 (N + 1) = Icc 1 N := by ext j; simp
  rw [hset]
  have hsum : ‖∑ j ∈ Icc 1 N, (chebyshevConductorCoeff j : ℂ)‖ ≤
      12 * Real.sqrt (N : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Icc 1 N, ‖(chebyshevConductorCoeff j : ℂ)‖ := norm_sum_le _ _
      _ ≤ _ := by simpa only [Complex.norm_real, Real.norm_eq_abs] using sum_abs_coeff_le N
  have htwist : ‖∑ j ∈ Icc 1 N, (chebyshevConductorCoeff j : ℂ) * ζ ^ j‖ ≤
      12 * Real.sqrt (N : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Icc 1 N, ‖(chebyshevConductorCoeff j : ℂ) * ζ ^ j‖ := norm_sum_le _ _
      _ ≤ _ := by
        simpa only [norm_mul, norm_pow, hζ, one_pow, mul_one,
          Complex.norm_real, Real.norm_eq_abs] using sum_abs_coeff_le N
  exact (norm_sub_le _ _).trans (by linarith only [hsum, htwist])

/-- Distance from the constant root is bounded below by distance to either end of the period. -/
theorem cyclotomicMode_gap {Q k : ℕ} (hk0 : 0 < k) (hkQ : k < Q) :
    4 * ((min k (Q - k) : ℕ) : ℝ) / Q ≤ ‖1 - cyclotomicMode Q k‖ := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast (hk0.trans hkQ)
  have hk : (0 : ℝ) < k := by exact_mod_cast hk0
  have hklt : (k : ℝ) < Q := by exact_mod_cast hkQ
  have hsub : ((Q - k : ℕ) : ℝ) = (Q : ℝ) - k := Nat.cast_sub hkQ.le
  have hr : (0 : ℝ) < (min k (Q - k) : ℕ) := by
    exact_mod_cast (lt_min hk0 (Nat.sub_pos_of_lt hkQ))
  have hrk : ((min k (Q - k) : ℕ) : ℝ) ≤ k := by exact_mod_cast min_le_left k (Q - k)
  have hrQ : ((min k (Q - k) : ℕ) : ℝ) ≤ (Q : ℝ) - k := by
    rw [← hsub]
    exact_mod_cast min_le_right k (Q - k)
  have hs := _root_.RHTower.Sieve.two_mul_le_sin_pi_mul
    (div_pos hr hQ) (div_le_div_of_nonneg_right hrk hQ.le)
    (show (k : ℝ) / Q ≤ 1 - ((min k (Q - k) : ℕ) : ℝ) / Q by
      apply (le_sub_iff_add_le).mpr
      rw [← add_div, div_le_one hQ]
      linarith only [hrQ])
  have hs0 : 0 ≤ Real.sin (Real.pi * ((k : ℝ) / Q)) :=
    (by positivity : 0 ≤ 2 * (((min k (Q - k) : ℕ) : ℝ) / Q)).trans hs
  have hnorm : ‖1 - cyclotomicMode Q k‖ =
      2 * Real.sin (Real.pi * ((k : ℝ) / Q)) := by
    rw [norm_sub_rev, cyclotomicMode, Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show (2 * Real.pi * (k : ℝ) / Q) / 2 = Real.pi * ((k : ℝ) / Q) by ring]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hs0)]
  rw [hnorm]
  calc
    _ = 2 * (2 * (((min k (Q - k) : ℕ) : ℝ) / Q)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by norm_num)

/-- Each nonconstant mode has an inverse-square bound in its distance from the ends. -/
theorem chebyshevCyclotomic_mode_le {N k : ℕ} (hk0 : 0 < k) (hkN : k < N + 1) :
    ‖(1 + cyclotomicMode (N + 1) k) *
      prefixPacket (N + 1) chebyshevConductorCoeff (cyclotomicMode (N + 1) k)‖ ^ 2 ≤
      144 * ((N : ℝ) + 1) ^ 2 * N *
        (1 / (k : ℝ) ^ 2 + 1 / ((N + 1 - k : ℕ) : ℝ) ^ 2) := by
  let ζ := cyclotomicMode (N + 1) k
  let P := prefixPacket (N + 1) chebyshevConductorCoeff ζ
  let r : ℝ := (min k (N + 1 - k) : ℕ)
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast lt_min hk0 (Nat.sub_pos_of_lt hkN)
  have hQ : 0 < (N : ℝ) + 1 := by positivity
  have hζ : ‖ζ‖ = 1 := norm_cyclotomicMode (N + 1) k
  have hd := norm_difference_packet_le N ζ hζ
  change ‖(1 - ζ) * P‖ ≤ 24 * Real.sqrt (N : ℝ) at hd
  rw [norm_mul] at hd
  have hg := cyclotomicMode_gap hk0 hkN
  rw [Nat.cast_add, Nat.cast_one] at hg
  change 4 * r / ((N : ℝ) + 1) ≤ ‖1 - ζ‖ at hg
  have hg' : 4 * r ≤ ((N : ℝ) + 1) * ‖1 - ζ‖ := by
    have h := (div_le_iff₀ hQ).mp hg
    simpa only [mul_comm] using h
  have hnorm : r * ‖P‖ ≤ 6 * ((N : ℝ) + 1) * Real.sqrt (N : ℝ) := by
    have h₁ := mul_le_mul_of_nonneg_right hg' (norm_nonneg P)
    have h₂ := mul_le_mul_of_nonneg_left hd hQ.le
    nlinarith only [h₁, h₂]
  have hsq := pow_le_pow_left₀ (mul_nonneg hr.le (norm_nonneg P)) hnorm 2
  simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)] at hsq
  have hplus : ‖(1 + ζ) * P‖ ≤ 2 * ‖P‖ := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg P)
    have h := norm_add_le (1 : ℂ) ζ
    simpa only [norm_one, hζ, one_add_one_eq_two] using h
  have hplusSq := pow_le_pow_left₀ (norm_nonneg ((1 + ζ) * P)) hplus 2
  rw [mul_pow] at hplusSq
  have hscaled := mul_le_mul_of_nonneg_left hplusSq (sq_nonneg r)
  have hmode : ‖(1 + ζ) * P‖ ^ 2 ≤
      (144 * ((N : ℝ) + 1) ^ 2 * N) / r ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
    nlinarith only [hsq, hscaled]
  have hinv : 1 / r ^ 2 ≤ 1 / (k : ℝ) ^ 2 + 1 / ((N + 1 - k : ℕ) : ℝ) ^ 2 := by
    by_cases h : k ≤ N + 1 - k
    · dsimp [r]
      rw [min_eq_left h]
      exact le_add_of_nonneg_right (by positivity)
    · dsimp [r]
      rw [min_eq_right (le_of_not_ge h)]
      exact le_add_of_nonneg_left (by positivity)
  calc
    _ ≤ (144 * ((N : ℝ) + 1) ^ 2 * N) / r ^ 2 := hmode
    _ = (144 * ((N : ℝ) + 1) ^ 2 * N) * (1 / r ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by positivity)

private theorem finite_inv_sq_tail {K : ℕ} (hK : 1 ≤ K) (S : Finset ℕ)
    (hS : ∀ n ∈ S, K < n) :
    ∑ n ∈ S, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / (K : ℝ) := by
  let f : ℕ → ℝ := fun n => 1 / ((n : ℝ) + K + 1) ^ 2
  have he (n : ℕ) (hn : n ∈ S) : f (n - (K + 1)) = 1 / (n : ℝ) ^ 2 := by
    have hid : n - (K + 1) + K + 1 = n := by have := hS n hn; omega
    have hcast : ((n - (K + 1) : ℕ) : ℝ) + K + 1 = (n : ℝ) := by exact_mod_cast hid
    dsimp [f]
    rw [hcast]
  have hinj : Set.InjOn (fun n : ℕ => n - (K + 1)) (↑S) := by
    intro n hn m hm heq
    have hnK := hS n hn
    have hmK := hS m hm
    change n - (K + 1) = m - (K + 1) at heq
    omega
  calc
    _ = ∑ n ∈ S, f (n - (K + 1)) := sum_congr rfl fun n hn => (he n hn).symm
    _ = ∑ n ∈ S.image (fun n => n - (K + 1)), f n := (sum_image hinj).symm
    _ ≤ ∑' n : ℕ, f n :=
      (_root_.RHTower.Sieve.summable_inv_sq_shift K).sum_le_tsum _ (fun _ _ => by positivity)
    _ ≤ 1 / (K : ℝ) := _root_.RHTower.Sieve.tsum_inv_sq_shift_le hK

/-- The actual far modes have a conductor-over-bandwidth bound. -/
theorem chebyshevCyclotomicFar_le (N : ℕ) {K : ℕ} (hK : 1 ≤ K) :
    chebyshevCyclotomicFar N K ≤ 288 * (N : ℝ) * ((N : ℝ) + 1) / K := by
  let S := (Ico 1 (N + 1)).filter (fun k => K < k ∧ K < N + 1 - k)
  have hleft : ∑ k ∈ S, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / (K : ℝ) :=
    finite_inv_sq_tail hK S fun k hk => (mem_filter.mp hk).2.1
  have hinj : Set.InjOn (fun k => N + 1 - k) (↑S) := by
    intro k hk l hl heq
    have hkN := (mem_Ico.mp (mem_filter.mp hk).1).2
    have hlN := (mem_Ico.mp (mem_filter.mp hl).1).2
    change N + 1 - k = N + 1 - l at heq
    omega
  have hright : ∑ k ∈ S, (1 : ℝ) / ((N + 1 - k : ℕ) : ℝ) ^ 2 ≤ 1 / (K : ℝ) := by
    calc
      _ = ∑ k ∈ S.image (fun k => N + 1 - k), (1 : ℝ) / (k : ℝ) ^ 2 :=
        (sum_image (f := fun k : ℕ => (1 : ℝ) / (k : ℝ) ^ 2) hinj).symm
      _ ≤ _ := by
        apply finite_inv_sq_tail hK
        intro l hl
        obtain ⟨k, hk, rfl⟩ := mem_image.mp hl
        exact (mem_filter.mp hk).2.2
  have hsum :
      (∑ k ∈ S, ‖(1 + cyclotomicMode (N + 1) k) *
        prefixPacket (N + 1) chebyshevConductorCoeff (cyclotomicMode (N + 1) k)‖ ^ 2) ≤
      144 * ((N : ℝ) + 1) ^ 2 * N * (2 / (K : ℝ)) := by
    calc
      _ ≤ ∑ k ∈ S, 144 * ((N : ℝ) + 1) ^ 2 * N *
          (1 / (k : ℝ) ^ 2 + 1 / ((N + 1 - k : ℕ) : ℝ) ^ 2) := by
        apply sum_le_sum
        intro k hk
        obtain ⟨hk0, hkN⟩ := mem_Ico.mp (mem_filter.mp hk).1
        exact chebyshevCyclotomic_mode_le hk0 hkN
      _ = 144 * ((N : ℝ) + 1) ^ 2 * N *
          ((∑ k ∈ S, 1 / (k : ℝ) ^ 2) + ∑ k ∈ S, 1 / ((N + 1 - k : ℕ) : ℝ) ^ 2) := by
        rw [← mul_sum, sum_add_distrib]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((add_le_add hleft hright).trans_eq (by ring)) (by positivity)
  unfold chebyshevCyclotomicFar
  change _ / ((N : ℝ) + 1) ≤ _
  apply (div_le_iff₀ (by positivity : 0 < (N : ℝ) + 1)).mpr
  exact hsum.trans_eq (by ring)

/-- Removing a square-root number of modes leaves energy of order `N^(3/2)`. -/
theorem chebyshevCyclotomicFar_sqrt_le (N : ℕ) :
    chebyshevCyclotomicFar N ⌈Real.sqrt ((N : ℝ) + 1)⌉₊ ≤
      288 * (N : ℝ) * Real.sqrt ((N : ℝ) + 1) := by
  let K : ℕ := ⌈Real.sqrt ((N : ℝ) + 1)⌉₊
  have hroot : 0 < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hceil : Real.sqrt ((N : ℝ) + 1) ≤ (K : ℝ) := Nat.le_ceil _
  have hKpos : (0 : ℝ) < K := hroot.trans_le hceil
  have hK : 1 ≤ K := by exact_mod_cast hKpos
  have hprod : (N : ℝ) + 1 ≤ Real.sqrt ((N : ℝ) + 1) * (K : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hceil hroot.le
    nlinarith only [h, Real.sq_sqrt (show 0 ≤ (N : ℝ) + 1 by positivity)]
  refine (chebyshevCyclotomicFar_le N hK).trans ?_
  apply (div_le_iff₀ hKpos).mpr
  have h := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 288 * (N : ℝ))
  simpa only [mul_assoc] using h

/-- At most twice the chosen bandwidth remains outside the far packet. -/
theorem chebyshevCyclotomicNear_card_le (N K : ℕ) :
    ((Ico 1 (N + 1)).filter (fun k => ¬ (K < k ∧ K < N + 1 - k))).card ≤ 2 * K := by
  let S := Icc 1 K
  have hsub : (Ico 1 (N + 1)).filter (fun k => ¬ (K < k ∧ K < N + 1 - k)) ⊆
      S ∪ S.image (fun k => N + 1 - k) := by
    intro k hk
    obtain ⟨hkI, hknear⟩ := mem_filter.mp hk
    obtain ⟨hk0, hkN⟩ := mem_Ico.mp hkI
    by_cases hkK : k ≤ K
    · exact mem_union_left _ (mem_Icc.mpr ⟨hk0, hkK⟩)
    · apply mem_union_right
      apply mem_image.mpr
      refine ⟨N + 1 - k, mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      omega
  calc
    _ ≤ (S ∪ S.image (fun k => N + 1 - k)).card := card_le_card hsub
    _ ≤ S.card + (S.image (fun k => N + 1 - k)).card := card_union_le _ _
    _ ≤ S.card + S.card := Nat.add_le_add_left (card_image_le) _
    _ = 2 * K := by simp [S, Nat.card_Icc]; omega

end GaloisForLFunctions.CompletedArithmeticForms
