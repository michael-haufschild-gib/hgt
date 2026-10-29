import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OnePrimeSeesTheWholeDefectOfZeta
import GaloisForLFunctions.HeckeKreinToeplitz.TheFiniteIndexStratumOfZetaIsLindelofDeep
import GaloisForLFunctions.RHTower.ZetaZeroCountUpperBound
import GaloisForLFunctions.RHTower.GelfondSchneider

/-!
# The Hasse principle with heights

A cyclic subgroup `⟨u⟩ ⊂ ℚ_{>0}` samples the ordinates of the spectrum of the Weil kernel at spacing
`2π/log u`: two right zeros alias on it iff they have the same real part and ordinates differing by
a nonzero multiple of `2π/log u`. This file makes the local-to-global law effective in the height.

* **The height filtration** (`rightZerosBelow`, `heightIndex`). `κ_T` is the number of zeros right
  of the critical line with `|Im ρ| ≤ T`. It is finite, monotone, at most `2N(0, T) + c₀`, hence
  `O(T log T)` by Riemann–von Mangoldt (`heightIndex_le_zeroCount`, `heightIndex_le_rvm`), and it
  exhausts the index: `κ(K_ζ) = sup_T κ_T` (`negIndex_zetaKernel_eq_iSup_heightIndex`).
* **Nyquist separation** (`injOn_frobEig_of_mul_lt_pi`). On a tower of scale `ℓ` with `ℓT < π`,
  points of ordinate at most `T` never alias. The constant `π` is sharp: for `ℓT ≥ π` two points of
  ordinate `±π/ℓ` alias (`exists_alias_of_pi_le`).
* **Certifying towers** (`exists_window_certifies_height`). By the deep-sparse tower law, some window
  of the `ℓ`-tower of some `C²` compactly supported test carries `κ_T` negative squares of Weil's
  prime-side Gram matrix whenever `ℓT < π`.
* **An explicit certificate in `⟨2, 3⟩`** (`twoPrime_tower_certifies_height`). Dirichlet's theorem
  gives `k ≤ ⌊T log 2/π⌋ + 1`, `k ≤ j ≤ 2k`, with `0 < |log(3^k/2^j)| < π/T`; the tower of
  `3^k/2^j` certifies height `T`. The generator has size `O(T)`; no prime tower can be certified
  this way, since `log p ≥ log 2 > π/T` once `T > π/log 2`.
* **Primes** (`ncard_heightBlindPrimes_le`, `exists_prime_certifies_height`). A pair of distinct
  points aliases at most at one prime, so at most `binom(κ_T, 2)` prime towers fail to separate the
  right zeros of ordinate at most `T`; among any `binom(κ_T, 2) + 1` primes one tower carries all of
  them. Which prime is a Diophantine question about `log p` and the ordinates.

Everything is unconditional and prime-side: the Gram matrices are those of the explicit formula.
-/

open Complex Finset Filter
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (rightZeros frobEig outerEig weilGram
  deepSparse_tower_law deepSparse_zeta weilGram_eq_zeroGram translate_contDiff
  translate_hasCompactSupport subsingleton_resonantPrimes)
open GaloisForLFunctions.SquareRootThreshold (temperedConfig_zetaZeroConfig)

noncomputable section

namespace GaloisForLFunctions.EffectiveArithmeticHodgeTheory

local notation "Tr" => ArithmeticCastelnuovoSeveri.translate

/-! ### The height filtration -/

/-- The zeros of `ζ` right of the critical line with ordinate at most `T` in absolute value. -/
def rightZerosBelow (T : ℝ) : Set ℂ := {ρ ∈ rightZeros zetaZeroConfig | |ρ.im| ≤ T}

theorem rightZerosBelow_subset_lowZeros (T : ℝ) : rightZerosBelow T ⊆ RHTower.lowZeros T :=
  fun _ hρ => ⟨hρ.1.1, hρ.2⟩

theorem rightZerosBelow_finite (T : ℝ) : (rightZerosBelow T).Finite :=
  (RHTower.lowZeros_finite T).subset (rightZerosBelow_subset_lowZeros T)

/-- **The height filtration of the index**: `κ_T`, the number of right zeros of ordinate at most
`T`. -/
def heightIndex (T : ℝ) : ℕ := (rightZerosBelow T).ncard

theorem heightIndex_mono {S T : ℝ} (h : S ≤ T) : heightIndex S ≤ heightIndex T :=
  Set.ncard_le_ncard (fun _ hρ => ⟨hρ.1, hρ.2.trans h⟩) (rightZerosBelow_finite T)

/-- `κ_T ≤ 2N(0, T) + c₀`. -/
theorem heightIndex_le_zeroCount : ∃ c₀ : ℕ, ∀ T : ℝ, 0 ≤ T →
    heightIndex T ≤ 2 * zetaZeroConfig.N 0 T + c₀ := by
  obtain ⟨c₀, h⟩ := RHTower.ncard_lowZeros_le
  exact ⟨c₀, fun T hT => (Set.ncard_le_ncard (rightZerosBelow_subset_lowZeros T)
    (RHTower.lowZeros_finite T)).trans (h T hT)⟩

/-- **Riemann–von Mangoldt for the height filtration**: `κ_T ≤ 2F(T) + C log²T + c₀` with
`F(T) = (T/2π)(log(T/2π) − 1)`. -/
theorem heightIndex_le_rvm : ∃ C T₁ c₀ : ℝ, 0 ≤ C ∧ 3 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
    (heightIndex T : ℝ) ≤ 2 * RHTower.zeroCountMain T + C * Real.log T ^ 2 + c₀ := by
  obtain ⟨c₀, hc⟩ := heightIndex_le_zeroCount
  obtain ⟨C, T₁, hC, hT₁, hN⟩ := RHTower.zeroCount_upper
  refine ⟨2 * C, T₁, c₀, by positivity, hT₁, fun T hT => ?_⟩
  have h1 : (heightIndex T : ℝ) ≤ 2 * (zetaZeroConfig.N 0 T : ℝ) + c₀ := by
    exact_mod_cast hc T (by linarith)
  have h2 := hN T hT
  linarith

/-- **The height filtration exhausts the right zeros.** -/
theorem encard_rightZeros_eq_iSup_heightIndex :
    (rightZeros zetaZeroConfig).encard = ⨆ n : ℕ, (heightIndex n : ℕ∞) := by
  refine le_antisymm (ENat.forall_natCast_le_iff_le.mp fun m hm => ?_)
    (iSup_le fun n => ?_)
  · obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq hm
    have htfin : t.Finite := Set.finite_of_encard_eq_coe htc
    obtain ⟨n, hn⟩ := (htfin.image fun ρ : ℂ => |ρ.im|).bddAbove
    obtain ⟨N, hN⟩ := exists_nat_ge n
    have hsub : t ⊆ rightZerosBelow N := fun ρ hρ =>
      ⟨hts hρ, (hn ⟨ρ, hρ, rfl⟩).trans hN⟩
    refine le_trans ?_ (le_iSup (fun n : ℕ => (heightIndex n : ℕ∞)) N)
    rw [heightIndex, (rightZerosBelow_finite _).cast_ncard_eq, ← htc]
    exact Set.encard_le_encard hsub
  · rw [heightIndex, (rightZerosBelow_finite _).cast_ncard_eq]
    exact Set.encard_le_encard fun ρ hρ => hρ.1

/-- **The index is the supremum of the height filtration**: `κ(K_ζ) = sup_T κ_T`. -/
theorem negIndex_zetaKernel_eq_iSup_heightIndex :
    HeckeKreinToeplitz.negIndex HeckeKreinToeplitz.zetaKernel =
      ⨆ n : ℕ, (heightIndex n : ℕ∞) := by
  rw [HeckeKreinToeplitz.negIndex_zetaKernel, encard_rightZeros_eq_iSup_heightIndex]

/-! ### Nyquist separation -/

/-- **Nyquist separation.** On a tower of scale `ℓ` with `ℓT < π`, points of ordinate at most `T`
have distinct Frobenius values `e^{ℓ(τ − ½)}`: equal values force `ℓ(Im τ − Im τ') ∈ 2πℤ`, and
`|ℓ(Im τ − Im τ')| ≤ 2ℓT < 2π`. -/
theorem injOn_frobEig_of_mul_lt_pi {ℓ T : ℝ} (hℓ : 0 < ℓ) (hT : ℓ * T < Real.pi) {S : Set ℂ}
    (hS : ∀ τ ∈ S, |τ.im| ≤ T) : Set.InjOn (frobEig ℓ) S := by
  intro τ hτ τ' hτ' he
  obtain ⟨hre, k, hk⟩ :=
    (ArithmeticCastelnuovoSeveri.frobEig_eq_frobEig_iff hℓ τ τ').mp he
  have h1 : |ℓ * (τ.im - τ'.im)| ≤ ℓ * (2 * T) := by
    rw [abs_mul, abs_of_pos hℓ]
    refine mul_le_mul_of_nonneg_left ?_ hℓ.le
    have := abs_sub τ.im τ'.im
    linarith [hS τ hτ, hS τ' hτ']
  have hk0 : k = 0 := by
    have h2 : |(2 * Real.pi) * (k : ℝ)| < 2 * Real.pi := by
      rw [← hk]; linarith
    rw [abs_mul, abs_of_pos Real.two_pi_pos] at h2
    have h3 : |(k : ℝ)| < 1 := by
      have := Real.two_pi_pos
      by_contra h
      push Not at h
      nlinarith
    have h4 : |k| < 1 := by exact_mod_cast h3
    exact Int.abs_lt_one_iff.mp h4
  rw [hk0, Int.cast_zero, mul_zero] at hk
  have him : τ.im = τ'.im := by
    rcases mul_eq_zero.mp hk with h | h
    · exact absurd h hℓ.ne'
    · linarith
  exact Complex.ext hre him

/-- **The Nyquist constant is sharp.** For `ℓT ≥ π`, the points `σ ± iπ/ℓ` have ordinate at most
`T` and the same Frobenius value at scale `ℓ`. -/
theorem exists_alias_of_pi_le {ℓ T : ℝ} (hℓ : 0 < ℓ) (hT : Real.pi ≤ ℓ * T) (σ : ℝ) :
    ∃ τ τ' : ℂ, τ ≠ τ' ∧ τ.re = σ ∧ τ'.re = σ ∧ |τ.im| ≤ T ∧ |τ'.im| ≤ T ∧
      frobEig ℓ τ = frobEig ℓ τ' := by
  have hπℓ : 0 < Real.pi / ℓ := div_pos Real.pi_pos hℓ
  have hle : Real.pi / ℓ ≤ T := by rw [div_le_iff₀ hℓ]; linarith
  refine ⟨⟨σ, Real.pi / ℓ⟩, ⟨σ, -(Real.pi / ℓ)⟩, fun h => ?_, rfl, rfl, ?_, ?_, ?_⟩
  · have := congrArg Complex.im h
    simp only at this
    linarith
  · simpa [abs_of_pos hπℓ] using hle
  · simpa [abs_neg, abs_of_pos hπℓ] using hle
  · refine (ArithmeticCastelnuovoSeveri.frobEig_eq_frobEig_iff hℓ _ _).mpr ⟨rfl, 1, ?_⟩
    simp only [Int.cast_one, mul_one]
    field_simp
    ring

/-! ### Certifying towers -/

/-- On a tower of scale `ℓ < π/T` the right zeros of ordinate at most `T` give distinct outer
eigenvalues. -/
theorem heightIndex_le_encard_outerEig {ℓ T : ℝ} (hℓ : 0 < ℓ) (hT : ℓ * T < Real.pi) :
    (heightIndex T : ℕ∞) ≤ (outerEig zetaZeroConfig ℓ).encard := by
  have hinj := injOn_frobEig_of_mul_lt_pi hℓ hT (S := rightZerosBelow T) fun _ hτ => hτ.2
  rw [heightIndex, (rightZerosBelow_finite T).cast_ncard_eq, ← hinj.encard_image]
  exact Set.encard_le_encard (Set.image_mono fun _ hρ => hρ.1)

/-- **A tower of scale `ℓ < π/T` certifies height `T`.** Some window of the `ℓ`-tower of some `C²`
compactly supported test carries, in Weil's prime-side Gram matrix, one negative square for every
right zero of ordinate at most `T`. -/
theorem exists_window_certifies_height {ℓ T : ℝ} (hℓ : 0 < ℓ) (hT : ℓ * T < Real.pi) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∃ K : Finset ℤ,
      heightIndex T ≤ hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        fun k : K => Tr (((k : ℤ) : ℝ) * ℓ) g) := by
  obtain ⟨g, hg, hgc, K, hK⟩ := (deepSparse_tower_law _ temperedConfig_zetaZeroConfig
    deepSparse_zeta hℓ (heightIndex T)).mpr (heightIndex_le_encard_outerEig hℓ hT)
  refine ⟨g, hg, hgc, K, ?_⟩
  rw [weilGram_eq_zeroGram _ (fun _ => translate_contDiff hg _)
    fun _ => translate_hasCompactSupport hgc _]
  exact hK

/-! ### An explicit certificate in the two-prime lattice -/

/-- `log(3^k/2^j) = k log 3 − j log 2`. -/
theorem log_three_pow_div_two_pow (j k : ℕ) :
    Real.log ((3 : ℝ) ^ k / 2 ^ j) = k * Real.log 3 - j * Real.log 2 := by
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]

/-- **A small scale in `⟨2, 3⟩`.** For `T ≥ 0` there are `k ≤ ⌊T log 2/π⌋ + 1` and `k ≤ j ≤ 2k`
with `0 < |log(3^k/2^j)|` and `|log(3^k/2^j)|·T < π` (Dirichlet's approximation theorem applied to
the irrational `log 3/log 2`). -/
theorem exists_twoPrime_scale (T : ℝ) (hT : 0 ≤ T) :
    ∃ j k : ℕ, 0 < k ∧ k ≤ ⌊T * Real.log 2 / Real.pi⌋₊ + 1 ∧ k ≤ j ∧ j ≤ 2 * k ∧
      0 < |Real.log ((3 : ℝ) ^ k / 2 ^ j)| ∧ |Real.log ((3 : ℝ) ^ k / 2 ^ j)| * T < Real.pi := by
  set n := ⌊T * Real.log 2 / Real.pi⌋₊ + 1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hl34 : Real.log 3 < 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  set ξ := Real.log 3 / Real.log 2
  have hξ1 : 1 < ξ := by rw [lt_div_iff₀ hl2]; linarith
  have hξ2 : ξ < 2 := by rw [div_lt_iff₀ hl2]; linarith
  obtain ⟨j, k, hk0, hkn, hjk⟩ := Real.exists_int_int_abs_mul_sub_le ξ (n := n) (show 0 < n from Nat.succ_pos _)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_pos _
  have hsmall : |(k : ℝ) * ξ - j| ≤ 1 / 2 := by
    refine hjk.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
  have hjlo : k ≤ j := by
    have : (k : ℝ) - 1 / 2 < j := by
      have := (abs_le.mp hsmall).2
      nlinarith
    have : (k : ℝ) - 1 < j := by linarith
    have : k - 1 < j := by exact_mod_cast this
    omega
  have hjhi : j ≤ 2 * k := by
    have : (j : ℝ) < 2 * k + 1 := by
      have := (abs_le.mp hsmall).1
      nlinarith
    have : j < 2 * k + 1 := by exact_mod_cast this
    omega
  have hj0 : 0 ≤ j := by omega
  refine ⟨j.toNat, k.toNat, by omega, by omega, by omega, by omega, ?_⟩
  have hcastk : ((k.toNat : ℕ) : ℝ) = k := by exact_mod_cast Int.toNat_of_nonneg hk0.le
  have hcastj : ((j.toNat : ℕ) : ℝ) = j := by exact_mod_cast Int.toNat_of_nonneg hj0
  rw [log_three_pow_div_two_pow, hcastk, hcastj]
  have heq : (k : ℝ) * Real.log 3 - j * Real.log 2 = Real.log 2 * ((k : ℝ) * ξ - j) := by
    simp only [ξ]; field_simp
  rw [heq, abs_mul, abs_of_pos hl2]
  have hirr : Irrational ξ := RHTower.irrational_log_ratio Nat.prime_two Nat.prime_three
    (by norm_num)
  have hne : (k : ℝ) * ξ - j ≠ 0 := by
    intro h
    have hξq : ξ = ((j : ℚ) / k : ℚ) := by
      push_cast
      field_simp
      linarith
    exact hirr ⟨(j : ℚ) / k, hξq.symm⟩
  refine ⟨mul_pos hl2 (abs_pos.mpr hne), ?_⟩
  -- `T log 2 < π n` since `n = ⌊T log 2/π⌋ + 1`
  have hfl : T * Real.log 2 / Real.pi < n := by
    simp only [n]; push_cast; exact Nat.lt_floor_add_one _
  have hTn : T * Real.log 2 < Real.pi * n := by
    rw [div_lt_iff₀ Real.pi_pos] at hfl; linarith
  have hjk' : |(k : ℝ) * ξ - j| * ((n : ℝ) + 1) ≤ 1 := by
    have := hjk
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hab : 0 ≤ |(k : ℝ) * ξ - j| := abs_nonneg _
  have hA : 0 ≤ T * Real.log 2 := mul_nonneg hT hl2.le
  have h1 : Real.log 2 * |(k : ℝ) * ξ - j| * T * ((n : ℝ) + 1) ≤ T * Real.log 2 := by
    have := mul_le_mul_of_nonneg_left hjk' hA
    nlinarith
  have h2 : Real.log 2 * |(k : ℝ) * ξ - j| * T * ((n : ℝ) + 1) < Real.pi * ((n : ℝ) + 1) := by
    nlinarith [Real.pi_pos]
  exact lt_of_mul_lt_mul_right h2 (by positivity)

/-- **An explicit certifying tower in `⟨2, 3⟩`.** For every height `T ≥ 0` there are
`k ≤ ⌊T log 2/π⌋ + 1` and `k ≤ j ≤ 2k` such that some window of the tower of `3^k/2^j` (scale
`|log(3^k/2^j)|`) carries one negative square of Weil's prime-side Gram matrix for every right zero of
ordinate at most `T`. -/
theorem twoPrime_tower_certifies_height (T : ℝ) (hT : 0 ≤ T) :
    ∃ j k : ℕ, 0 < k ∧ k ≤ ⌊T * Real.log 2 / Real.pi⌋₊ + 1 ∧ k ≤ j ∧ j ≤ 2 * k ∧
      ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∃ K : Finset ℤ,
        heightIndex T ≤ hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          fun m : K => Tr (((m : ℤ) : ℝ) * |Real.log ((3 : ℝ) ^ k / 2 ^ j)|) g) := by
  obtain ⟨j, k, hk, hkn, hjk, hjk2, hpos, hlt⟩ := exists_twoPrime_scale T hT
  exact ⟨j, k, hk, hkn, hjk, hjk2, exists_window_certifies_height hpos hlt⟩

/-! ### Blind primes at height `T` -/

/-- The primes whose tower aliases two right zeros of ordinate at most `T`. -/
def heightBlindPrimes (T : ℝ) : Set ℕ :=
  {p | p.Prime ∧ ¬ Set.InjOn (frobEig (Real.log p)) (rightZerosBelow T)}

/-- **At most `binom(κ_T, 2)` primes are blind at height `T`.** Each blind prime is the unique
prime at which some pair of distinct right zeros of ordinate at most `T` aliases. -/
theorem ncard_heightBlindPrimes_le (T : ℝ) :
    (heightBlindPrimes T).Finite ∧ (heightBlindPrimes T).ncard ≤ (heightIndex T).choose 2 := by
  classical
  set S := (rightZerosBelow_finite T).toFinset
  have hpair : ∀ p : heightBlindPrimes T, ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧
      frobEig (Real.log p) a = frobEig (Real.log p) b := fun p => by
    obtain ⟨-, hni⟩ := p.2
    simp only [Set.InjOn, not_forall] at hni
    obtain ⟨a, ha, b, hb, h, hab⟩ := hni
    exact ⟨a, (Set.Finite.mem_toFinset _).mpr ha, b, (Set.Finite.mem_toFinset _).mpr hb, hab, h⟩
  choose a ha b hb hab heq using hpair
  let F : heightBlindPrimes T → powersetCard 2 S := fun p =>
    ⟨{a p, b p}, mem_powersetCard.mpr ⟨by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact ha p
      · rw [mem_singleton.mp hx]; exact hb p, card_pair (hab p)⟩⟩
  have hF : Function.Injective F := fun p p' h => by
    have hset : ({a p, b p} : Finset ℂ) = {a p', b p'} := congrArg Subtype.val h
    have h1 : a p ∈ ({a p', b p'} : Finset ℂ) := hset ▸ mem_insert_self _ _
    have h2 : b p ∈ ({a p', b p'} : Finset ℂ) := hset ▸ mem_insert_of_mem (mem_singleton_self _)
    have hp' : frobEig (Real.log p') (a p) = frobEig (Real.log p') (b p) := by
      simp only [mem_insert, mem_singleton] at h1 h2
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (h1.trans h2.symm) (hab p)
      · rw [h1, h2]; exact heq p'
      · rw [h1, h2]; exact (heq p').symm
      · exact absurd (h1.trans h2.symm) (hab p)
    exact Subtype.ext (subsingleton_resonantPrimes (hab p) ⟨p.2.1, heq p⟩ ⟨p'.2.1, hp'⟩)
  have hfin : Finite (heightBlindPrimes T) := Finite.of_injective F hF
  refine ⟨Set.toFinite _, ?_⟩
  rw [← Nat.card_coe_set_eq]
  calc Nat.card (heightBlindPrimes T) ≤ Nat.card (powersetCard 2 S) :=
        Nat.card_le_card_of_injective F hF
    _ = (heightIndex T).choose 2 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_powersetCard, heightIndex,
          Set.ncard_eq_toFinset_card _ (rightZerosBelow_finite T)]

/-- **Among any `binom(κ_T, 2) + 1` primes one tower certifies height `T`.** -/
theorem exists_prime_certifies_height (T : ℝ) {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hcard : (heightIndex T).choose 2 < P.card) :
    ∃ p ∈ P, ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∃ K : Finset ℤ,
      heightIndex T ≤ hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        fun k : K => Tr (((k : ℤ) : ℝ) * Real.log p) g) := by
  classical
  obtain ⟨hfin, hle⟩ := ncard_heightBlindPrimes_le T
  have hex : ∃ p ∈ P, p ∉ heightBlindPrimes T := by
    by_contra h
    push Not at h
    have hsub : (P : Set ℕ) ⊆ heightBlindPrimes T := fun p hp => h p hp
    have := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset] at this
    omega
  obtain ⟨p, hpP, hpb⟩ := hex
  have hp := hP p hpP
  have hinj : Set.InjOn (frobEig (Real.log p)) (rightZerosBelow T) := by
    by_contra h
    exact hpb ⟨hp, h⟩
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hcount : (heightIndex T : ℕ∞) ≤ (outerEig zetaZeroConfig (Real.log p)).encard := by
    rw [heightIndex, (rightZerosBelow_finite T).cast_ncard_eq, ← hinj.encard_image]
    exact Set.encard_le_encard (Set.image_mono fun _ hρ => hρ.1)
  obtain ⟨g, hg, hgc, K, hK⟩ := (deepSparse_tower_law _ temperedConfig_zetaZeroConfig
    deepSparse_zeta hlog (heightIndex T)).mpr hcount
  refine ⟨p, hpP, g, hg, hgc, K, ?_⟩
  rw [weilGram_eq_zeroGram _ (fun _ => translate_contDiff hg _)
    fun _ => translate_hasCompactSupport hgc _]
  exact hK

end GaloisForLFunctions.EffectiveArithmeticHodgeTheory
