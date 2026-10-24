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

end

end GaloisForLFunctions.BezoutValuationIncidence
