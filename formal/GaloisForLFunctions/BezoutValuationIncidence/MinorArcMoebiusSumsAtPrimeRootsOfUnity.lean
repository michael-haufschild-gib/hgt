import GaloisForLFunctions.BezoutValuationIncidence.FourierFormOfTheCubicKernelAndFourthOrderLargeSieve
import GaloisForLFunctions.RHTower.Sieve.TypeIICoefficientEnergy
import GaloisForLFunctions.RHTower.Sieve.DirichletConvolutionRearrange
import GaloisForLFunctions.RHTower.RootOfUnityIntervalCompletion

/-!
# Möbius sums at prime roots of unity: the minor-arc law

Let `p` be prime and `ζ ≠ 1` a `p`-th root of unity. Every such `ζ` is a primitive root, so the
frequency of `n ↦ ζⁿ` has exact denominator `p`. Vinogradov's bilinear method bounds
`S(N) = Σ_{n ≤ N} μ(n) ζⁿ` with no input beyond the additive structure of `ℕ`.

* **Decomposition.** With `μ_U = μ·𝟙_{≤U}` and `g = δ - 1 ∗ μ_U` (`typeIIShort U`, zero on `[1, U]`),
  `μ = 2μ_U - μ_U ∗ μ_U ∗ 1 + (μ - μ_U) ∗ g` is a ring identity, from `μ ∗ 1 = δ`.
* **Type I.** For `U < p` no product `d₁d₂` of two moduli `≤ U` is divisible by `p`, so every inner
  geometric sum is at most `2/|ζ^{d₁d₂} - 1|`; for fixed `d₁` the map `d₂ ↦ ζ^{d₁d₂}` is injective
  into the nontrivial roots. The Type-I part is at most `U W_p`, `W_p = Σ_{η ≠ 1} 2/|η - 1| ≤ p(1 + log p)`.
* **Type II.** On a dyadic block `d ∈ (D, 2D]`, Cauchy–Schwarz in the long variable `k` leaves
  `Σ_{d, d'} min(N/D, 2/|ζ^{d-d'} - 1|)`; an interval of length `D` meets each residue class modulo
  `p` at most `D/p + 1` times, so this is at most `D(D/p + 1)(N/D + W_p)`.

The outcome (`norm_sum_moebius_mul_pow_le`) is, for `1 ≤ U < p`,

`|S(N)| ≤ 2U + U W_p + (log₂ N + 1) √(2(1 + H_N³)(N²/p + N²/U + N² W_p/(Up) + N W_p))`,

`H_N = Σ_{k ≤ N} 1/k`: a power saving over the trivial bound `N` whenever `N^δ ≤ p ≤ N^{1-δ}`.
-/

open Finset ArithmeticFunction RHTower.Sieve
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Harmonic sums over the nontrivial roots of unity -/

/-- `W_d = Σ_{η ∈ T_d} 2/‖η - 1‖` over the nontrivial `d`-th roots of unity. -/
def rootHarmonicSum (d : ℕ) : ℝ := ∑ η ∈ nontrivialRoots d, 2 / ‖η - 1‖

theorem rootHarmonicSum_nonneg (d : ℕ) : 0 ≤ rootHarmonicSum d :=
  sum_nonneg fun _ _ => by positivity

/-- `W_d ≤ d (1 + log d)`: Jordan's inequality and the harmonic series. -/
theorem rootHarmonicSum_le (d : ℕ) : rootHarmonicSum d ≤ d * (1 + Real.log d) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [rootHarmonicSum, nontrivialRoots]
  set e : ℕ → ℂ := fun j => Complex.exp (2 * Real.pi * Complex.I * j / d)
  have hsub : nontrivialRoots d ⊆ (Ioo 0 d).image e := by
    intro η hη
    obtain ⟨h1, hd'⟩ := (mem_nontrivialRoots hd).mp hη
    haveI : NeZero d := ⟨hd.ne'⟩
    obtain ⟨i, hi, hiη⟩ := (Complex.isPrimitiveRoot_exp d hd.ne').eq_pow_of_pow_eq_one hd'
    refine mem_image.mpr ⟨i, mem_Ioo.mpr ⟨Nat.pos_of_ne_zero ?_, hi⟩, ?_⟩
    · rintro rfl
      exact h1 (by rw [← hiη, pow_zero])
    · rw [← hiη, ← Complex.exp_nat_mul]
      simp only [e]
      congr 1
      ring
  calc rootHarmonicSum d ≤ ∑ η ∈ (Ioo 0 d).image e, 2 / ‖η - 1‖ :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ ∑ j ∈ Ioo 0 d, 2 / ‖e j - 1‖ := sum_image_le_of_nonneg fun _ _ => by positivity
    _ ≤ _ := GaloisForLFunctions.RHTower.RootOfUnityCompletion.sum_two_div_norm_exp_sub_one_le d

/-! ## §2. Prime roots of unity -/

/-- A nontrivial `p`-th root of unity is primitive when `p` is prime. -/
theorem isPrimitiveRoot_of_mem_nontrivialRoots {p : ℕ} (hp : p.Prime) {ζ : ℂ}
    (hζ : ζ ∈ nontrivialRoots p) : IsPrimitiveRoot ζ p := by
  rw [nontrivialRoots_eq_primitiveRoots hp] at hζ
  exact (mem_primitiveRoots hp.pos).mp hζ

theorem pow_mem_nontrivialRoots_of_not_dvd {p : ℕ} (hp : p.Prime) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ p) {m : ℕ} (hm : ¬ p ∣ m) : ζ ^ m ∈ nontrivialRoots p := by
  rw [mem_nontrivialRoots hp.pos]
  refine ⟨fun h => hm ((hζ.pow_eq_one_iff_dvd m).mp h), ?_⟩
  rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

theorem isPrimitiveRoot_pow_of_not_dvd {p : ℕ} (hp : p.Prime) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ p) {m : ℕ} (hm : ¬ p ∣ m) : IsPrimitiveRoot (ζ ^ m) p :=
  isPrimitiveRoot_of_mem_nontrivialRoots hp (pow_mem_nontrivialRoots_of_not_dvd hp hζ hm)

/-- **Injective harmonic sums.** For `V < p` the powers `ζ^m`, `1 ≤ m ≤ V`, are distinct
nontrivial roots, so `Σ_{1 ≤ m ≤ V} 2/‖ζ^m - 1‖ ≤ W_p`. -/
theorem sum_Icc_two_div_norm_pow_sub_one_le {p : ℕ} (hp : p.Prime) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ p) {V : ℕ} (hV : V < p) :
    ∑ m ∈ Icc 1 V, 2 / ‖ζ ^ m - 1‖ ≤ rootHarmonicSum p := by
  have hinj : Set.InjOn (fun m => ζ ^ m) (Icc 1 V : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_Icc, Set.mem_Icc] at ha hb
    exact hζ.pow_inj (by omega) (by omega) hab
  rw [← sum_image (f := fun η => 2 / ‖η - 1‖) hinj]
  refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
  intro η hη
  obtain ⟨m, hm, rfl⟩ := mem_image.mp hη
  rw [mem_Icc] at hm
  exact pow_mem_nontrivialRoots_of_not_dvd hp hζ (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))

/-! ## §3. Residue classes in an interval -/

/-- An interval of length `L` meets each residue class modulo `p` at most `L/p + 1` times. -/
theorem card_filter_mod_eq_le {p : ℕ} (hp : 0 < p) (a L r : ℕ) :
    ((((Ioc a (a + L)).filter (fun x => x % p = r)).card : ℕ) : ℝ) ≤ (L : ℝ) / p + 1 := by
  set s := (Ioc a (a + L)).filter (fun x => x % p = r)
  have hmaps : Set.MapsTo (fun x => (x - (a + 1)) / p) (s : Set ℕ)
      (range ((L - 1) / p + 1) : Set ℕ) := by
    intro x hx
    simp only [s, coe_filter, mem_Ioc, Set.mem_setOf_eq] at hx
    simp only [coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
  have hinj : Set.InjOn (fun x => (x - (a + 1)) / p) (s : Set ℕ) := by
    intro x hx y hy hxy
    simp only [s, coe_filter, mem_Ioc, Set.mem_setOf_eq] at hx hy
    have hmod : (x - (a + 1)) % p = (y - (a + 1)) % p := by
      have hxy' : (a + 1) + (x - (a + 1)) ≡ (a + 1) + (y - (a + 1)) [MOD p] := by
        rw [Nat.add_sub_cancel' (by omega : a + 1 ≤ x), Nat.add_sub_cancel' (by omega : a + 1 ≤ y)]
        exact hx.2.trans hy.2.symm
      exact Nat.ModEq.add_left_cancel' _ hxy'
    have hx' := Nat.div_add_mod (x - (a + 1)) p
    have hy' := Nat.div_add_mod (y - (a + 1)) p
    simp only at hxy
    rw [hxy, hmod] at hx'
    omega
  have hcard := card_le_card_of_injOn _ hmaps hinj
  rw [card_range] at hcard
  have h1 : ((s.card : ℕ) : ℝ) ≤ (((L - 1) / p : ℕ) : ℝ) + 1 := by exact_mod_cast hcard
  have h2 : (((L - 1) / p : ℕ) : ℝ) ≤ (L : ℝ) / p := by
    refine (Nat.cast_div_le).trans ?_
    gcongr
    exact_mod_cast Nat.sub_le L 1
  linarith

/-- **Equidistribution of a geometric orbit over an interval.** For a primitive `p`-th root `ξ`, a
`p`-th root `z` and `F ≥ 0`, `Σ_{a < d ≤ a+L} F(z ξ^d) ≤ (L/p + 1) Σ_{η^p = 1} F(η)`. -/
theorem sum_Ioc_root_mul_pow_le {p : ℕ} (hp : 0 < p) {ξ z : ℂ} (hξ : IsPrimitiveRoot ξ p)
    (hz : z ^ p = 1) (F : ℂ → ℝ) (hF : ∀ η, 0 ≤ F η) (a L : ℕ) :
    ∑ d ∈ Ioc a (a + L), F (z * ξ ^ d) ≤
      ((L : ℝ) / p + 1) * ∑ η ∈ Polynomial.nthRootsFinset p (1 : ℂ), F η := by
  classical
  have hmodpow : ∀ d, ξ ^ d = ξ ^ (d % p) := fun d => by
    conv_lhs => rw [← Nat.mod_add_div d p]
    rw [pow_add, pow_mul, hξ.pow_eq_one, one_pow, mul_one]
  rw [← sum_fiberwise_of_maps_to (t := range p) (g := fun d => d % p)
    (fun d _ => mem_range.mpr (Nat.mod_lt d hp))]
  have hinner : ∀ r ∈ range p, ∑ d ∈ (Ioc a (a + L)).filter (fun d => d % p = r), F (z * ξ ^ d) =
      (((Ioc a (a + L)).filter (fun d => d % p = r)).card : ℝ) * F (z * ξ ^ r) := by
    intro r _
    rw [sum_congr rfl fun d hd => by rw [hmodpow d, (mem_filter.mp hd).2], sum_const, nsmul_eq_mul]
  rw [sum_congr rfl hinner]
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne'] at hz
    exact zero_ne_one hz
  have hinj : Set.InjOn (fun r => z * ξ ^ r) (range p : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    exact hξ.pow_inj ha hb (mul_left_cancel₀ hz0 hab)
  have himg : (range p).image (fun r => z * ξ ^ r) ⊆ Polynomial.nthRootsFinset p (1 : ℂ) := by
    intro η hη
    obtain ⟨r, _, rfl⟩ := mem_image.mp hη
    rw [Polynomial.mem_nthRootsFinset hp, mul_pow, hz, one_mul, ← pow_mul, mul_comm r p, pow_mul,
      hξ.pow_eq_one, one_pow]
  calc ∑ r ∈ range p, (((Ioc a (a + L)).filter (fun d => d % p = r)).card : ℝ) * F (z * ξ ^ r)
      ≤ ∑ r ∈ range p, ((L : ℝ) / p + 1) * F (z * ξ ^ r) :=
        sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (card_filter_mod_eq_le hp a L r) (hF _)
    _ = ((L : ℝ) / p + 1) * ∑ η ∈ (range p).image (fun r => z * ξ ^ r), F η := by
        rw [sum_image hinj, mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg himg fun _ _ _ => hF _)
        (by positivity)

/-! ## §4. The geometric majorant -/

/-- The majorant of a geometric sum `Σ_{1 ≤ k ≤ m} w^k`, `m ≤ K`: `K` at `w = 1`, else `2/‖w - 1‖`. -/
def geomMajorant (K : ℝ) (w : ℂ) : ℝ := if w = 1 then K else 2 / ‖w - 1‖

theorem geomMajorant_nonneg {K : ℝ} (hK : 0 ≤ K) (w : ℂ) : 0 ≤ geomMajorant K w := by
  unfold geomMajorant; split_ifs <;> positivity

theorem norm_sum_Icc_pow_le_geomMajorant {w : ℂ} (hw : ‖w‖ = 1) {m K : ℕ} (hmK : m ≤ K) :
    ‖∑ k ∈ Icc 1 m, w ^ k‖ ≤ geomMajorant K w := by
  unfold geomMajorant
  split_ifs with h
  · subst h
    simp only [one_pow, sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mul_one,
      Complex.norm_natCast]
    exact_mod_cast hmK
  · exact GaloisForLFunctions.RHTower.RootOfUnityCompletion.norm_sum_Icc_pow_le hw.le h m

/-- Over all `p`-th roots the majorant sums to `K + W_p`. -/
theorem sum_nthRootsFinset_geomMajorant {p : ℕ} (hp : 0 < p) (K : ℝ) :
    ∑ η ∈ Polynomial.nthRootsFinset p (1 : ℂ), geomMajorant K η = K + rootHarmonicSum p := by
  rw [← add_sum_erase _ _ ((Polynomial.mem_nthRootsFinset hp 1).mpr (one_pow p))]
  congr 1
  · simp [geomMajorant]
  · refine sum_congr rfl fun η hη => ?_
    rw [geomMajorant, if_neg (ne_of_mem_erase hη)]

/-- **Row sums of the Type-II correlation matrix.** For `d` fixed and `d'` over `(D, 2D]`,
`Σ_{d'} F_K(ζ^d conj(ζ)^{d'}) ≤ (D/p + 1)(K + W_p)`. -/
theorem sum_Ioc_geomMajorant_le {p : ℕ} (hp : p.Prime) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p)
    {K : ℝ} (hK : 0 ≤ K) (d D : ℕ) :
    ∑ d' ∈ Ioc D (2 * D), geomMajorant K (ζ ^ d * conj ζ ^ d') ≤
      ((D : ℝ) / p + 1) * (K + rootHarmonicSum p) := by
  have hξ : IsPrimitiveRoot (conj ζ) p :=
    hζ.map_of_injective (f := starRingEnd ℂ) (starRingEnd ℂ).injective
  have hz : (ζ ^ d) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have h := sum_Ioc_root_mul_pow_le hp.pos hξ hz (geomMajorant K) (geomMajorant_nonneg hK) D D
  rw [sum_nthRootsFinset_geomMajorant hp.pos, show D + D = 2 * D by ring] at h
  exact h

/-! ## §5. The Type-II block: Cauchy–Schwarz in the long variable -/

theorem filter_Icc_div_eq {N D d d' : ℕ} (hD : 0 < D) (hd : D < d) :
    (Icc 1 (N / D)).filter (fun k => k ≤ N / d ∧ k ≤ N / d') = Icc 1 (min (N / d) (N / d')) := by
  have h1 : N / d ≤ N / D := Nat.div_le_div_left hd.le hD
  ext k
  simp only [mem_filter, mem_Icc, le_min_iff]
  constructor
  · rintro ⟨⟨hk, _⟩, h⟩; exact ⟨hk, h⟩
  · rintro ⟨hk, h, h'⟩; exact ⟨⟨hk, h.trans h1⟩, h, h'⟩

/-- `f_d(k) conj f_{d'}(k)` for the masked phases `f_d(k) = 𝟙[k ≤ N/d] α(d) ζ^{dk}`. -/
theorem masked_mul_conj (N d d' k : ℕ) (a a' : ℝ) (ζ : ℂ) :
    (if k ≤ N / d then (a : ℂ) * ζ ^ (d * k) else 0) *
        conj (if k ≤ N / d' then (a' : ℂ) * ζ ^ (d' * k) else 0) =
      if k ≤ N / d ∧ k ≤ N / d' then ((a * a' : ℝ) : ℂ) * (ζ ^ d * conj ζ ^ d') ^ k else 0 := by
  by_cases h1 : k ≤ N / d <;> by_cases h2 : k ≤ N / d'
  · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩, map_mul, Complex.conj_ofReal, map_pow, mul_pow,
      ← pow_mul, ← pow_mul]
    push_cast
    ring
  · rw [if_pos h1, if_neg h2, _root_.map_zero, mul_zero,
      if_neg (show ¬(k ≤ N / d ∧ k ≤ N / d') from fun h => h2 h.2)]
  · rw [if_neg h1, zero_mul, if_neg (show ¬(k ≤ N / d ∧ k ≤ N / d') from fun h => h1 h.1)]
  · rw [if_neg h1, zero_mul, if_neg (show ¬(k ≤ N / d ∧ k ≤ N / d') from fun h => h1 h.1)]

/-- **The Type-II block bound.** For `|α| ≤ 1`, a primitive `p`-th root `ζ` and `D ≥ 1`,
`‖Σ_{D<d≤2D} Σ_{k≤N/d} α(d) β(k) ζ^{dk}‖² ≤ (Σ_{k≤N/D} β(k)²) · D (D/p + 1)(N/D + W_p)`. -/
theorem norm_sq_typeII_block_le {p : ℕ} (hp : p.Prime) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p)
    (N : ℕ) {D : ℕ} (hD : 0 < D) (α β : ℕ → ℝ) (hα : ∀ d, |α d| ≤ 1) :
    ‖∑ d ∈ Ioc D (2 * D), ∑ k ∈ Icc 1 (N / d), ((α d * β k : ℝ) : ℂ) * ζ ^ (d * k)‖ ^ 2 ≤
      (∑ k ∈ Icc 1 (N / D), β k ^ 2) *
        ((D : ℝ) * (((D : ℝ) / p + 1) * (((N / D : ℕ) : ℝ) + rootHarmonicSum p))) := by
  set X : ℕ → ℂ := fun k => ∑ d ∈ Ioc D (2 * D),
    if k ≤ N / d then ((α d : ℝ) : ℂ) * ζ ^ (d * k) else 0 with hX
  have hswap : ∑ d ∈ Ioc D (2 * D), ∑ k ∈ Icc 1 (N / d), ((α d * β k : ℝ) : ℂ) * ζ ^ (d * k) =
      ∑ k ∈ Icc 1 (N / D), ((β k : ℝ) : ℂ) * X k := by
    have h1 : ∀ d ∈ Ioc D (2 * D), ∑ k ∈ Icc 1 (N / d), ((α d * β k : ℝ) : ℂ) * ζ ^ (d * k) =
        ∑ k ∈ Icc 1 (N / D), if k ≤ N / d then ((α d * β k : ℝ) : ℂ) * ζ ^ (d * k) else 0 := by
      intro d hd
      rw [← sum_filter]
      congr 1
      ext k
      simp only [mem_filter, mem_Icc]
      have : N / d ≤ N / D := Nat.div_le_div_left (mem_Ioc.mp hd).1.le hD
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans this⟩, h2⟩
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    rw [sum_congr rfl h1, sum_comm]
    refine sum_congr rfl fun k _ => ?_
    simp only [hX, mul_sum]
    refine sum_congr rfl fun d _ => ?_
    split_ifs <;> push_cast <;> ring
  have hCS : ‖∑ k ∈ Icc 1 (N / D), ((β k : ℝ) : ℂ) * X k‖ ^ 2 ≤
      (∑ k ∈ Icc 1 (N / D), β k ^ 2) * ∑ k ∈ Icc 1 (N / D), ‖X k‖ ^ 2 := by
    have h1 : ‖∑ k ∈ Icc 1 (N / D), ((β k : ℝ) : ℂ) * X k‖ ≤ ∑ k ∈ Icc 1 (N / D), |β k| * ‖X k‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun k _ => ?_))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 := sum_mul_sq_le_sq_mul_sq (Icc 1 (N / D)) (fun k => |β k|) (fun k => ‖X k‖)
    simp only [sq_abs] at h2
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hexp : ((∑ k ∈ Icc 1 (N / D), ‖X k‖ ^ 2 : ℝ) : ℂ) = ∑ d ∈ Ioc D (2 * D), ∑ d' ∈ Ioc D (2 * D),
      ((α d * α d' : ℝ) : ℂ) * ∑ k ∈ Icc 1 (min (N / d) (N / d')), (ζ ^ d * conj ζ ^ d') ^ k := by
    rw [Complex.ofReal_sum]
    simp_rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, hX, map_sum, sum_mul_sum,
      masked_mul_conj]
    rw [sum_comm]
    refine sum_congr rfl fun d hd => ?_
    rw [sum_comm]
    refine sum_congr rfl fun d' _ => ?_
    rw [← sum_filter, filter_Icc_div_eq hD (mem_Ioc.mp hd).1, mul_sum]
  have hnormζ : ‖ζ‖ = 1 := hζ.norm'_eq_one hp.ne_zero
  have hK0 : (0 : ℝ) ≤ ((N / D : ℕ) : ℝ) := Nat.cast_nonneg _
  have hdiag : ∑ k ∈ Icc 1 (N / D), ‖X k‖ ^ 2 ≤
      ∑ d ∈ Ioc D (2 * D), ∑ d' ∈ Ioc D (2 * D), geomMajorant (N / D : ℕ) (ζ ^ d * conj ζ ^ d') := by
    have hnn : 0 ≤ ∑ k ∈ Icc 1 (N / D), ‖X k‖ ^ 2 := sum_nonneg fun _ _ => by positivity
    rw [← Real.norm_of_nonneg hnn, ← Complex.norm_real, hexp]
    refine (norm_sum_le _ _).trans (sum_le_sum fun d hd => (norm_sum_le _ _).trans
      (sum_le_sum fun d' hd' => ?_))
    have hw : ‖ζ ^ d * conj ζ ^ d'‖ = 1 := by
      rw [norm_mul, norm_pow, norm_pow, Complex.norm_conj, hnormζ, one_pow, one_pow, mul_one]
    have hm : min (N / d) (N / d') ≤ N / D :=
      (min_le_left _ _).trans (Nat.div_le_div_left (mem_Ioc.mp hd).1.le hD)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    calc |α d| * |α d'| * ‖∑ k ∈ Icc 1 (min (N / d) (N / d')), (ζ ^ d * conj ζ ^ d') ^ k‖
        ≤ 1 * 1 * geomMajorant (N / D : ℕ) (ζ ^ d * conj ζ ^ d') :=
          mul_le_mul (mul_le_mul (hα d) (hα d') (abs_nonneg _) zero_le_one)
            (norm_sum_Icc_pow_le_geomMajorant hw hm) (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  have hrows : ∑ d ∈ Ioc D (2 * D), ∑ d' ∈ Ioc D (2 * D), geomMajorant (N / D : ℕ) (ζ ^ d * conj ζ ^ d') ≤
      (D : ℝ) * (((D : ℝ) / p + 1) * (((N / D : ℕ) : ℝ) + rootHarmonicSum p)) := by
    calc _ ≤ ∑ _d ∈ Ioc D (2 * D), ((D : ℝ) / p + 1) * (((N / D : ℕ) : ℝ) + rootHarmonicSum p) :=
          sum_le_sum fun d _ => sum_Ioc_geomMajorant_le hp hζ hK0 d D
      _ = _ := by rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, show 2 * D - D = D by omega]
  rw [hswap]
  refine hCS.trans (mul_le_mul_of_nonneg_left (hdiag.trans hrows) (sum_nonneg fun _ _ => sq_nonneg _))

/-! ## §6. Convolution sums and the Vinogradov decomposition of `μ` -/

/-- `Σ_{n ≤ N} (f ∗ g)(n) w(n) = Σ_{d ≤ N} Σ_{k ≤ N/d} f(d) g(k) w(dk)`. -/
theorem sum_Icc_mul_conv (f g : ArithmeticFunction ℝ) (w : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (((f * g) n : ℝ) : ℂ) * w n =
      ∑ d ∈ Icc 1 N, ∑ k ∈ Icc 1 (N / d), ((f d * g k : ℝ) : ℂ) * w (d * k) := by
  have hI : ∀ n ∈ Icc 1 N, 1 ≤ n ∧ n ≤ N := fun n hn => mem_Icc.mp hn
  have h := sum_conv_mul_eq hI (fun d => (f d : ℂ)) (fun k => (g k : ℂ)) w
  have hlhs : ∀ n, (((f * g) n : ℝ) : ℂ) =
      ∑ x ∈ n.divisorsAntidiagonal, (f x.1 : ℂ) * (g x.2 : ℂ) := by
    intro n
    rw [ArithmeticFunction.mul_apply]
    push_cast
    rfl
  simp_rw [hlhs]
  rw [h, sum_filter, sum_product]
  refine sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := (mem_Icc.mp hd).1
  rw [← sum_filter]
  have hfilt : (Icc 1 N).filter (fun k => d * k ∈ Icc 1 N) = Icc 1 (N / d) := by
    ext k
    simp only [mem_filter, mem_Icc]
    rw [Nat.le_div_iff_mul_le hd1, mul_comm k d]
    constructor
    · rintro ⟨⟨hk1, _⟩, _, h2⟩
      exact ⟨hk1, h2⟩
    · rintro ⟨hk1, hk2⟩
      refine ⟨⟨hk1, le_trans (Nat.le_mul_of_pos_left k hd1) hk2⟩, Nat.mul_pos hd1 hk1, hk2⟩
  rw [hfilt]
  push_cast
  rfl

/-- **Vinogradov's decomposition of `μ`.** With `μ_U = μ·𝟙_{≤U}` and `g = δ - 1 ∗ μ_U`,
`μ = 2μ_U - μ_U ∗ μ_U ∗ 1 + (μ - μ_U) ∗ g`, a consequence of `μ ∗ 1 = δ`. -/
theorem moebius_eq_vinogradov_decomposition (U : ℕ) :
    (moebius : ArithmeticFunction ℝ) =
      truncAF (moebius : ArithmeticFunction ℝ) U + truncAF (moebius : ArithmeticFunction ℝ) U -
        truncAF (moebius : ArithmeticFunction ℝ) U * truncAF (moebius : ArithmeticFunction ℝ) U *
          (zeta : ArithmeticFunction ℝ) +
        ((moebius : ArithmeticFunction ℝ) - truncAF (moebius : ArithmeticFunction ℝ) U) *
          typeIIShort U := by
  have hkey : (moebius : ArithmeticFunction ℝ) * (zeta : ArithmeticFunction ℝ) = 1 :=
    coe_moebius_mul_coe_zeta
  unfold typeIIShort
  linear_combination (truncAF (moebius : ArithmeticFunction ℝ) U) * hkey

theorem abs_moebius_real_le_one (n : ℕ) : |(moebius : ArithmeticFunction ℝ) n| ≤ 1 := by
  rw [intCoe_apply]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

theorem abs_truncAF_moebius_le (U n : ℕ) :
    |truncAF (moebius : ArithmeticFunction ℝ) U n| ≤ if n ≤ U then 1 else 0 := by
  rw [truncAF_apply]
  split_ifs
  · exact abs_moebius_real_le_one n
  · simp

theorem abs_moebius_sub_truncAF_le (U n : ℕ) :
    |((moebius : ArithmeticFunction ℝ) - truncAF (moebius : ArithmeticFunction ℝ) U) n| ≤ 1 := by
  rw [show ((moebius : ArithmeticFunction ℝ) - truncAF (moebius : ArithmeticFunction ℝ) U) n =
      (moebius : ArithmeticFunction ℝ) n - truncAF (moebius : ArithmeticFunction ℝ) U n from rfl,
    truncAF_apply]
  split_ifs
  · simp
  · rw [sub_zero]; exact abs_moebius_real_le_one n

/-- `Σ_{1 ≤ n ≤ N} c·𝟙[n ≤ U] ≤ U c`. -/
theorem sum_Icc_ite_le_le (N U : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    ∑ n ∈ Icc 1 N, (if n ≤ U then c else 0) ≤ U * c := by
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ hc
  have h : (Icc 1 N).filter (· ≤ U) ⊆ Icc 1 U := fun n hn => by
    simp only [mem_filter, mem_Icc] at hn ⊢; omega
  have := card_le_card h
  rw [Nat.card_Icc, Nat.add_sub_cancel] at this
  exact_mod_cast this

/-! ## §7. Type-I sums at a prime root -/

/-- **Type-I sums.** For `c` supported on `[1, V]`, `V < p`, `|c| ≤ 1` and a primitive `p`-th root
`ξ`, `‖Σ_{d ≤ M} c(d) Σ_{m ≤ N/d} (ξ^d)^m‖ ≤ W_p`. -/
theorem norm_typeI_le {p : ℕ} (hp : p.Prime) {ξ : ℂ} (hξ : IsPrimitiveRoot ξ p) {V : ℕ}
    (hV : V < p) (c : ℕ → ℝ) (hc : ∀ d, |c d| ≤ 1) (hcs : ∀ d, V < d → c d = 0) (M N : ℕ) :
    ‖∑ d ∈ Icc 1 M, (c d : ℂ) * ∑ m ∈ Icc 1 (N / d), (ξ ^ d) ^ m‖ ≤ rootHarmonicSum p := by
  have hterm : ∀ d ∈ Icc 1 M, ‖(c d : ℂ) * ∑ m ∈ Icc 1 (N / d), (ξ ^ d) ^ m‖ ≤
      if d ≤ V then 2 / ‖ξ ^ d - 1‖ else 0 := by
    intro d hd
    split_ifs with hdV
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hne : ξ ^ d ≠ 1 := fun h =>
        Nat.not_dvd_of_pos_of_lt (mem_Icc.mp hd).1 (by omega) ((hξ.pow_eq_one_iff_dvd d).mp h)
      have hnorm : ‖ξ ^ d‖ ≤ 1 := by rw [norm_pow, hξ.norm'_eq_one hp.ne_zero, one_pow]
      calc |c d| * ‖∑ m ∈ Icc 1 (N / d), (ξ ^ d) ^ m‖ ≤ 1 * (2 / ‖ξ ^ d - 1‖) :=
            mul_le_mul (hc d)
              (GaloisForLFunctions.RHTower.RootOfUnityCompletion.norm_sum_Icc_pow_le hnorm hne _)
              (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    · rw [hcs d (by omega)]; simp
  calc _ ≤ ∑ d ∈ Icc 1 M, (if d ≤ V then 2 / ‖ξ ^ d - 1‖ else 0) :=
        (norm_sum_le _ _).trans (sum_le_sum hterm)
    _ = ∑ d ∈ (Icc 1 M).filter (· ≤ V), 2 / ‖ξ ^ d - 1‖ := (sum_filter _ _).symm
    _ ≤ ∑ d ∈ Icc 1 V, 2 / ‖ξ ^ d - 1‖ :=
        sum_le_sum_of_subset_of_nonneg (fun d hd => by
          simp only [mem_filter, mem_Icc] at hd ⊢; omega) fun _ _ _ => by positivity
    _ ≤ _ := sum_Icc_two_div_norm_pow_sub_one_le hp hξ hV

/-- **The Type-I part of `μ`.** `‖Σ_{n ≤ N} (μ_U ∗ μ_U ∗ 1)(n) ζⁿ‖ ≤ U W_p` for `U < p`. -/
theorem norm_sum_moebius_typeI_le {p : ℕ} (hp : p.Prime) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p)
    {U : ℕ} (hUp : U < p) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, (((truncAF (moebius : ArithmeticFunction ℝ) U *
        truncAF (moebius : ArithmeticFunction ℝ) U * (zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ) *
        ζ ^ n‖ ≤ U * rootHarmonicSum p := by
  set a := truncAF (moebius : ArithmeticFunction ℝ) U
  set G : ℕ → ℂ := fun e => ∑ m ∈ Icc 1 (N / e), (ζ ^ e) ^ m
  have h1 : ∑ n ∈ Icc 1 N, (((a * a * (zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ) * ζ ^ n =
      ∑ e ∈ Icc 1 N, (((a * a) e : ℝ) : ℂ) * G e := by
    rw [sum_Icc_mul_conv]
    refine sum_congr rfl fun e _ => ?_
    simp only [G, mul_sum]
    refine sum_congr rfl fun m hm => ?_
    rw [natCoe_apply, zeta_apply, if_neg (by have := (mem_Icc.mp hm).1; omega), pow_mul]
    push_cast
    ring
  have h2 : ∑ e ∈ Icc 1 N, (((a * a) e : ℝ) : ℂ) * G e =
      ∑ d ∈ Icc 1 N, (a d : ℂ) * ∑ k ∈ Icc 1 (N / d), (a k : ℂ) *
        ∑ m ∈ Icc 1 ((N / d) / k), ((ζ ^ d) ^ k) ^ m := by
    rw [sum_Icc_mul_conv]
    refine sum_congr rfl fun d _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    simp only [G, Nat.div_div_eq_div_mul, ← pow_mul]
    push_cast
    ring
  rw [h1, h2]
  have hterm : ∀ d ∈ Icc 1 N, ‖(a d : ℂ) * ∑ k ∈ Icc 1 (N / d), (a k : ℂ) *
      ∑ m ∈ Icc 1 ((N / d) / k), ((ζ ^ d) ^ k) ^ m‖ ≤
      (if d ≤ U then 1 else 0) * rootHarmonicSum p := by
    intro d hd
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hdU : d ≤ U
    · have hξ : IsPrimitiveRoot (ζ ^ d) p := isPrimitiveRoot_pow_of_not_dvd hp hζ
        (Nat.not_dvd_of_pos_of_lt (mem_Icc.mp hd).1 (by omega))
      have hI := norm_typeI_le hp hξ hUp a (fun k => (abs_truncAF_moebius_le U k).trans
        (by split_ifs <;> norm_num)) (fun k hk => by simp only [a, truncAF_apply_of_gt hk])
        (N / d) (N / d)
      exact mul_le_mul ((abs_truncAF_moebius_le U d).trans (le_of_eq rfl)) hI (norm_nonneg _)
        (by split_ifs <;> norm_num)
    · rw [show a d = 0 from truncAF_apply_of_gt (by omega), abs_zero, zero_mul, if_neg hdU,
        zero_mul]
  calc _ ≤ ∑ d ∈ Icc 1 N, (if d ≤ U then 1 else 0) * rootHarmonicSum p :=
        (norm_sum_le _ _).trans (sum_le_sum hterm)
    _ = ∑ d ∈ Icc 1 N, (if d ≤ U then rootHarmonicSum p else 0) :=
        sum_congr rfl fun d _ => by rw [ite_mul, one_mul, zero_mul]
    _ ≤ U * rootHarmonicSum p := sum_Icc_ite_le_le N U (rootHarmonicSum_nonneg p)

/-! ## §8. The Type-II part of `μ` on dyadic blocks, and the minor-arc law -/

/-- Telescoping `(U, 2^I U]` into the dyadic blocks `(2^i U, 2·2^i U]`, `i < I`. -/
theorem sum_Ioc_eq_sum_dyadic (F : ℕ → ℂ) (U I : ℕ) :
    ∑ d ∈ Ioc U (2 ^ I * U), F d =
      ∑ i ∈ range I, ∑ d ∈ Ioc (2 ^ i * U) (2 * (2 ^ i * U)), F d := by
  induction I with
  | zero => simp
  | succ I ih =>
    have h1 : U ≤ 2 ^ I * U := Nat.le_mul_of_pos_left U (Nat.two_pow_pos I)
    have h2 : 2 ^ I * U ≤ 2 * (2 ^ I * U) := Nat.le_mul_of_pos_left _ (by norm_num)
    rw [Finset.sum_range_succ, ← ih, show 2 ^ (I + 1) * U = 2 * (2 ^ I * U) by ring,
      sum_Ioc_consecutive _ h1 h2]

/-- The Type-II block majorant `2(1 + H_N³)(N²/p + N²/U + N² W_p/(Up) + N W_p)`. -/
def typeIIBlockBound (p U N : ℕ) : ℝ :=
  2 * (1 + invSum N ^ 3) * ((N : ℝ) ^ 2 / p + (N : ℝ) ^ 2 / U +
    (N : ℝ) ^ 2 * rootHarmonicSum p / (U * p) + N * rootHarmonicSum p)

theorem typeIIBlockBound_nonneg (p U N : ℕ) : 0 ≤ typeIIBlockBound p U N := by
  unfold typeIIBlockBound
  have := rootHarmonicSum_nonneg p
  have := invSum_nonneg N
  positivity

/-- **One dyadic Type-II block of `μ`.** On `d ∈ (D, 2D]`, `D = 2^i U ≥ U`, the block is empty
unless `N/D > U` (since `g = 0` on `[1, U]`), and then `D ≤ N/U`, `N/D ≤ N/U`. -/
theorem norm_sq_moebius_typeII_block_le {p : ℕ} (hp : p.Prime) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ p) {U : ℕ} (hU : 1 ≤ U) (N i : ℕ) :
    ‖∑ d ∈ Ioc (2 ^ i * U) (2 * (2 ^ i * U)), ∑ k ∈ Icc 1 (N / d),
        ((((moebius : ArithmeticFunction ℝ) - truncAF (moebius : ArithmeticFunction ℝ) U) d *
          typeIIShort U k : ℝ) : ℂ) * ζ ^ (d * k)‖ ^ 2 ≤ typeIIBlockBound p U N := by
  have hD1 : U ≤ 2 ^ i * U := Nat.le_mul_of_pos_left U (Nat.two_pow_pos i)
  have hD0 : 0 < 2 ^ i * U := by omega
  refine (norm_sq_typeII_block_le hp hζ N hD0 _ (typeIIShort U)
    (abs_moebius_sub_truncAF_le U)).trans ?_
  set D := 2 ^ i * U
  set L := N / D
  set W := rootHarmonicSum p
  have hW : 0 ≤ W := rootHarmonicSum_nonneg p
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hUR : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hDR : (U : ℝ) ≤ D := by exact_mod_cast hD1
  have hH : 0 ≤ invSum N := invSum_nonneg N
  by_cases hLU : L ≤ U
  · have h0 : ∑ k ∈ Icc 1 L, typeIIShort U k ^ 2 = 0 := sum_eq_zero fun k hk => by
      rw [show typeIIShort U k = 0 from one_sub_zeta_mul_truncAF_moebius_apply_eq_zero
        (mem_Icc.mp hk).1 ((mem_Icc.mp hk).2.trans hLU)]
      ring
    rw [h0, zero_mul]
    exact typeIIBlockBound_nonneg p U N
  push Not at hLU
  have hE : ∑ k ∈ Icc 1 L, typeIIShort U k ^ 2 ≤ 2 * L * (1 + invSum N ^ 3) := by
    have h := sum_typeIIShort_sq_le U L
    have hsq : ∀ k, ‖((typeIIShort U k : ℝ) : ℂ)‖ ^ (2 : ℕ) = typeIIShort U k ^ 2 := fun k => by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp_rw [hsq] at h
    have h3 : invSum L ^ 3 ≤ invSum N ^ 3 :=
      pow_le_pow_left₀ (invSum_nonneg L) (invSum_mono (Nat.div_le_self N D)) 3
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    nlinarith
  have hLD : (L : ℝ) * D ≤ N := by exact_mod_cast Nat.div_mul_le_self N D
  have hLUR : (U : ℝ) < L := by exact_mod_cast hLU
  have hDle : (D : ℝ) ≤ N / U := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) D]
  have hLle : (L : ℝ) ≤ N / U := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) L]
  have hx0 : (0 : ℝ) ≤ L * D := by positivity
  have hX0 : (0 : ℝ) ≤ D * (((D : ℝ) / p + 1) * ((L : ℝ) + W)) := by positivity
  have hkey : (L : ℝ) * (D * (((D : ℝ) / p + 1) * ((L : ℝ) + W))) ≤
      (N : ℝ) ^ 2 / p + (N : ℝ) ^ 2 / U + (N : ℝ) ^ 2 * W / (U * p) + N * W := by
    have e : (L : ℝ) * (D * (((D : ℝ) / p + 1) * ((L : ℝ) + W))) =
        (L * D) * (L * D) / p + (L * D) * L + (L * D) * D * W / p + (L * D) * W := by
      field_simp
      ring
    have t1 : ((L : ℝ) * D) * (L * D) / p ≤ N * N / p :=
      div_le_div_of_nonneg_right (mul_le_mul hLD hLD hx0 (Nat.cast_nonneg _)) hpR.le
    have t2 : ((L : ℝ) * D) * L ≤ N * (N / U) :=
      mul_le_mul hLD hLle (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have t3 : ((L : ℝ) * D) * D * W / p ≤ N * (N / U) * W / p :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul hLD hDle (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hW) hpR.le
    have t4 : ((L : ℝ) * D) * W ≤ N * W := mul_le_mul_of_nonneg_right hLD hW
    have e2 : (N : ℝ) * N / p + N * (N / U) + N * (N / U) * W / p + N * W =
        (N : ℝ) ^ 2 / p + (N : ℝ) ^ 2 / U + (N : ℝ) ^ 2 * W / (U * p) + N * W := by
      field_simp
    rw [e, ← e2]
    linarith
  calc (∑ k ∈ Icc 1 L, typeIIShort U k ^ 2) * (D * (((D : ℝ) / p + 1) * ((L : ℝ) + W)))
      ≤ 2 * L * (1 + invSum N ^ 3) * (D * (((D : ℝ) / p + 1) * ((L : ℝ) + W))) :=
        mul_le_mul_of_nonneg_right hE hX0
    _ = 2 * (1 + invSum N ^ 3) * ((L : ℝ) * (D * (((D : ℝ) / p + 1) * ((L : ℝ) + W)))) := by ring
    _ ≤ 2 * (1 + invSum N ^ 3) * ((N : ℝ) ^ 2 / p + (N : ℝ) ^ 2 / U +
          (N : ℝ) ^ 2 * W / (U * p) + N * W) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = typeIIBlockBound p U N := rfl

/-- **The Type-II part of `μ`.** `‖Σ_{n ≤ N} ((μ - μ_U) ∗ g)(n) ζⁿ‖ ≤ (log₂ N + 1) √(block bound)`. -/
theorem norm_sum_moebius_typeII_le {p : ℕ} (hp : p.Prime) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p)
    {U : ℕ} (hU : 1 ≤ U) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, (((((moebius : ArithmeticFunction ℝ) -
        truncAF (moebius : ArithmeticFunction ℝ) U) * typeIIShort U) n : ℝ) : ℂ) * ζ ^ n‖ ≤
      (Nat.log 2 N + 1) * Real.sqrt (typeIIBlockBound p U N) := by
  set b := (moebius : ArithmeticFunction ℝ) - truncAF (moebius : ArithmeticFunction ℝ) U
  set F : ℕ → ℂ := fun d => ∑ k ∈ Icc 1 (N / d), ((b d * typeIIShort U k : ℝ) : ℂ) * ζ ^ (d * k)
  have hb0 : ∀ d, d ≤ U → b d = 0 := fun d hd => by
    show (moebius : ArithmeticFunction ℝ) d - truncAF (moebius : ArithmeticFunction ℝ) U d = 0
    rw [truncAF_apply, if_pos hd, sub_self]
  have hNI : N < 2 ^ (Nat.log 2 N + 1) * U := lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) N)
    (Nat.le_mul_of_pos_right _ hU)
  have hconv : ∑ n ∈ Icc 1 N, (((b * typeIIShort U) n : ℝ) : ℂ) * ζ ^ n = ∑ d ∈ Icc 1 N, F d := by
    rw [sum_Icc_mul_conv]
  have hext : ∑ d ∈ Icc 1 N, F d = ∑ d ∈ Ioc U (2 ^ (Nat.log 2 N + 1) * U), F d := by
    have hFbig : ∀ d, N < d → F d = 0 := fun d hd => by
      simp only [F]
      rw [Nat.div_eq_of_lt hd]
      simp
    have hFsmall : ∀ d, d ≤ U → F d = 0 := fun d hd => by
      simp only [F, hb0 d hd, zero_mul, Complex.ofReal_zero]
      simp
    have hIcc : Icc 1 N = Ioc 0 N := Finset.Icc_add_one_left_eq_Ioc 0 N
    rw [hIcc, sum_subset (show Ioc 0 N ⊆ Ioc 0 (2 ^ (Nat.log 2 N + 1) * U) from
        Ioc_subset_Ioc_right hNI.le) (fun d hd hdN => hFbig d (by
          simp only [mem_Ioc, not_and, not_le] at hd hdN; exact hdN hd.1)),
      ← sum_Ioc_consecutive _ (Nat.zero_le U) (Nat.le_mul_of_pos_left U (Nat.two_pow_pos _)),
      sum_eq_zero (s := Ioc 0 U) (f := F) (fun d hd => hFsmall d (mem_Ioc.mp hd).2), zero_add]
  rw [hconv, hext, sum_Ioc_eq_sum_dyadic]
  calc ‖∑ i ∈ range (Nat.log 2 N + 1), ∑ d ∈ Ioc (2 ^ i * U) (2 * (2 ^ i * U)), F d‖
      ≤ ∑ i ∈ range (Nat.log 2 N + 1), Real.sqrt (typeIIBlockBound p U N) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
        have h := norm_sq_moebius_typeII_block_le hp hζ hU N i
        have := Real.abs_le_sqrt h
        rwa [abs_of_nonneg (norm_nonneg _)] at this
    _ = (Nat.log 2 N + 1) * Real.sqrt (typeIIBlockBound p U N) := by
        rw [sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring

/-- **The minor-arc law for Möbius at prime roots of unity.** For `p` prime, `ζ ≠ 1` a `p`-th root
of unity and `1 ≤ U < p`,
`‖Σ_{n ≤ N} μ(n) ζⁿ‖ ≤ 2U + U W_p + (log₂ N + 1) √(2(1 + H_N³)(N²/p + N²/U + N² W_p/(Up) + N W_p))`. -/
theorem norm_sum_moebius_mul_pow_le {p : ℕ} (hp : p.Prime) {ζ : ℂ} (hζ : ζ ∈ nontrivialRoots p)
    {U : ℕ} (hU : 1 ≤ U) (hUp : U < p) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, (moebiusReal n : ℂ) * ζ ^ n‖ ≤
      2 * U + U * rootHarmonicSum p + (Nat.log 2 N + 1) * Real.sqrt (typeIIBlockBound p U N) := by
  have hprim := isPrimitiveRoot_of_mem_nontrivialRoots hp hζ
  have hnorm : ‖ζ‖ = 1 := hprim.norm'_eq_one hp.ne_zero
  set a := truncAF (moebius : ArithmeticFunction ℝ) U
  set b := (moebius : ArithmeticFunction ℝ) - a
  have hdec : ∀ n, (moebiusReal n : ℂ) = (((a + a) n : ℝ) : ℂ) -
      (((a * a * (zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ) +
        (((b * typeIIShort U) n : ℝ) : ℂ) := by
    intro n
    have h : (moebius : ArithmeticFunction ℝ) n =
        (a + a) n - (a * a * (zeta : ArithmeticFunction ℝ)) n + (b * typeIIShort U) n :=
      congrArg (fun f : ArithmeticFunction ℝ => f n) (moebius_eq_vinogradov_decomposition U)
    have hm : moebiusReal n = (moebius : ArithmeticFunction ℝ) n := by
      rw [intCoe_apply]; rfl
    rw [hm, h]
    push_cast
    ring
  rw [sum_congr rfl fun n _ => by rw [hdec n]]
  simp_rw [add_mul, sub_mul]
  rw [sum_add_distrib, sum_sub_distrib]
  have hA : ‖∑ n ∈ Icc 1 N, (((a + a) n : ℝ) : ℂ) * ζ ^ n‖ ≤ 2 * U := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ Icc 1 N, ‖(((a + a) n : ℝ) : ℂ) * ζ ^ n‖
        ≤ ∑ n ∈ Icc 1 N, (if n ≤ U then (2 : ℝ) else 0) := by
          refine sum_le_sum fun n _ => ?_
          rw [norm_mul, norm_pow, hnorm, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs]
          have h := abs_truncAF_moebius_le U n
          have h2 : |(a + a) n| ≤ |a n| + |a n| := abs_add_le _ _
          split_ifs at h ⊢ <;> linarith
      _ ≤ U * 2 := sum_Icc_ite_le_le N U (by norm_num)
      _ = 2 * U := by ring
  have hB := norm_sum_moebius_typeI_le hp hprim hUp N
  have hC := norm_sum_moebius_typeII_le hp hprim hU N
  calc _ ≤ ‖∑ n ∈ Icc 1 N, (((a + a) n : ℝ) : ℂ) * ζ ^ n -
          ∑ n ∈ Icc 1 N, (((a * a * (zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ) * ζ ^ n‖ +
        ‖∑ n ∈ Icc 1 N, (((b * typeIIShort U) n : ℝ) : ℂ) * ζ ^ n‖ := norm_add_le _ _
    _ ≤ ‖∑ n ∈ Icc 1 N, (((a + a) n : ℝ) : ℂ) * ζ ^ n‖ +
          ‖∑ n ∈ Icc 1 N, (((a * a * (zeta : ArithmeticFunction ℝ)) n : ℝ) : ℂ) * ζ ^ n‖ +
        ‖∑ n ∈ Icc 1 N, (((b * typeIIShort U) n : ℝ) : ℂ) * ζ ^ n‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ _ := by linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
