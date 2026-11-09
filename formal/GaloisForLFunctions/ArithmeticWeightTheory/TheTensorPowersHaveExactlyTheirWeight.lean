import GaloisForLFunctions.SurfaceOfSpecZ.TheRankinSquareDivergesAtTwiceTheTopWeight
import GaloisForLFunctions.SurfaceOfSpecZ.TheTensorPowerTrick

/-!
# The tensor powers have exactly their weight

Over a curve the a priori control of `L(F^{⊗2k})` comes from `H²_c`, the coinvariants of the
geometric monodromy, whose Frobenius weight is fixed independently of `k`. For the virtual motive
`M = Σ_z e_z ℤ(−z)` of a zero configuration nothing plays this role: `M` is geometrically
constant (its Frobenius at `n` acts through `log n`), every constituent of `M^{⊗2k}` is a Tate
twist with a pole, and the top pole of `−L′/L(M^{⊗2k})` sits exactly where the weight puts it.

**Theorem** (`summable_tensorTerm_iff_of_max`). Let `Z` be a tempered configuration whose top
`ρ₀` (a zero of maximal real part, off the line) is attained, `b = Re ρ₀ − ½`. For every `k ≥ 1`
the series `Σ_n Λ(n) (2 Re S(log n))^{2k} n^{−σ}` converges for `σ > 1 + 2kb` and diverges for
`σ < 1 + 2kb`: the abscissa of the `2k`-th tensor power is exactly `1 + 2kb`.

**Proof.** Above: `|2 Re S(u)| ≤ E e^{bu}`. Below: weighted AM–GM,
`c² x^{−(σ/k + (1+δ)(1−1/k))} ≤ (1/k) c^{2k} x^{−σ} + (1 − 1/k) x^{−(1+δ)}`
(`sq_mul_rpow_le_tensor`), dominates the Rankin square at `1 + 2b` by the `2k`-th tensor series
plus `Σ Λ(n) n^{−1−δ}`; the Rankin square diverges at `1 + 2b`
(`not_summable_rankinSquare_of_max`).

**Milestone M4 is RH** (`riemannHypothesis_iff_tensorExponent_sublinear`). The moment exponents
`A_k` of `Σ_{p≤N} log p (2 Re S(log p))^{2k} ≪ N^{1+A_k}` satisfy `A_k ≥ 2k·width − 1`
(`zetaZeroWidth_le_of_primeTraceMoment_le`), so `A_k = o(k)` already forces width `0`. The tensor
trick for `M` alone carries the weight and nothing else; uniformity must come from a family.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticWeightTheory

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
open SurfaceOfSpecZ ArithmeticFunction

/-- The `j`-th term of `−L′/L(M_Z^{⊗2k}, σ)`, at `n = j + 1`. -/
def tensorTerm (Z : ZeroConfig) (k : ℕ) (σ : ℝ) (j : ℕ) : ℝ :=
  Λ (j + 1) * (2 * (lagStructure Z (boxSpline 1 3) (Real.log (j + 1))).re) ^ (2 * k) *
    ((j : ℝ) + 1) ^ (-σ)

theorem tensorTerm_nonneg (Z : ZeroConfig) (k : ℕ) (σ : ℝ) (j : ℕ) : 0 ≤ tensorTerm Z k σ j := by
  unfold tensorTerm
  refine mul_nonneg (mul_nonneg vonMangoldt_nonneg ?_) (by positivity)
  rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _

/-- **Above the weight.** The `2k`-th tensor series converges for `σ > 1 + 2kb`. -/
theorem summable_tensorTerm {Z : ZeroConfig} (hZ : TemperedConfig Z) {b : ℝ} (htop : TopDepth Z b)
    (k : ℕ) {σ : ℝ} (hσ : 1 + 2 * k * b < σ) : Summable (tensorTerm Z k σ) := by
  set E := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖
  have hσ' : 1 < σ - 2 * k * b := by linarith
  refine Summable.of_nonneg_of_le (tensorTerm_nonneg Z k σ) (fun j => ?_)
    ((summable_vonMangoldt_rpow hσ').mul_left (E ^ (2 * k)))
  have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hu : 0 ≤ Real.log ((j : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j])
  have hN := abs_normTrace_le hZ htop hu
  have hexp : Real.exp (b * Real.log ((j : ℝ) + 1)) = ((j : ℝ) + 1) ^ b := by
    rw [Real.rpow_def_of_pos hj0]; ring_nf
  set c := 2 * (lagStructure Z (boxSpline 1 3) (Real.log ((j : ℝ) + 1))).re with hc
  have hcN : c = normTrace Z b (Real.log ((j : ℝ) + 1)) * Real.exp (b * Real.log ((j : ℝ) + 1)) := by
    rw [normTrace, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hcabs : |c| ≤ E * ((j : ℝ) + 1) ^ b := by
    rw [hcN, abs_mul, abs_of_pos (Real.exp_pos _), hexp]
    exact mul_le_mul_of_nonneg_right hN (by positivity)
  have hpow : c ^ (2 * k) ≤ (E * ((j : ℝ) + 1) ^ b) ^ (2 * k) := by
    rw [pow_mul, pow_mul, ← sq_abs c]
    exact pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀ (abs_nonneg _) hcabs 2) k
  have hsplit : (E * ((j : ℝ) + 1) ^ b) ^ (2 * k) * ((j : ℝ) + 1) ^ (-σ) =
      E ^ (2 * k) * ((j : ℝ) + 1) ^ (-(σ - 2 * k * b)) := by
    rw [mul_pow, ← Real.rpow_natCast (((j : ℝ) + 1) ^ b), ← Real.rpow_mul hj0.le, mul_assoc,
      ← Real.rpow_add hj0]
    congr 2
    push_cast; ring
  have hΛ : 0 ≤ Λ (j + 1) := vonMangoldt_nonneg
  calc tensorTerm Z k σ j = Λ (j + 1) * (c ^ (2 * k) * ((j : ℝ) + 1) ^ (-σ)) := by
        unfold tensorTerm; ring
    _ ≤ Λ (j + 1) * ((E * ((j : ℝ) + 1) ^ b) ^ (2 * k) * ((j : ℝ) + 1) ^ (-σ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (by positivity)) hΛ
    _ = E ^ (2 * k) * (Λ (j + 1) * ((j : ℝ) + 1) ^ (-(σ - 2 * k * b))) := by rw [hsplit]; ring

/-- **Weighted AM–GM between the Rankin square and the `2k`-th power.** For `x ≥ 1`, `k ≥ 1`,
`c² x^{−(σ/k + (1+δ)(1−1/k))} ≤ (1/k) c^{2k} x^{−σ} + (1 − 1/k) x^{−(1+δ)}`. -/
theorem sq_mul_rpow_le_tensor (c : ℝ) {x : ℝ} (hx : 1 ≤ x) {k : ℕ} (hk : 1 ≤ k) (σ δ : ℝ) :
    c ^ 2 * x ^ (-(σ / k + (1 + δ) * (1 - 1 / k))) ≤
      1 / k * (c ^ (2 * k) * x ^ (-σ)) + (1 - 1 / k) * x ^ (-(1 + δ)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hx0 : 0 < x := by linarith
  have hw₁ : 0 ≤ 1 / (k : ℝ) := by positivity
  have hw₂ : 0 ≤ 1 - 1 / (k : ℝ) := by
    rw [sub_nonneg, div_le_one hk0]; exact_mod_cast hk
  have hp₁ : 0 ≤ c ^ (2 * k) * x ^ (-σ) := by
    rw [pow_mul]; exact mul_nonneg (pow_nonneg (sq_nonneg _) _) (by positivity)
  have hp₂ : 0 ≤ x ^ (-(1 + δ)) := by positivity
  have hgm := Real.geom_mean_le_arith_mean2_weighted hw₁ hw₂ hp₁ hp₂ (by ring)
  have hk' : k ≠ 0 := by omega
  have h1 : (c ^ (2 * k) * x ^ (-σ)) ^ (1 / (k : ℝ)) = c ^ 2 * x ^ (-σ / k) := by
    rw [Real.mul_rpow (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _) (by positivity),
      pow_mul, one_div, Real.pow_rpow_inv_natCast (sq_nonneg c) hk', ← Real.rpow_mul hx0.le]
    congr 2
  have h2 : (x ^ (-(1 + δ))) ^ (1 - 1 / (k : ℝ)) = x ^ (-(1 + δ) * (1 - 1 / k)) := by
    rw [← Real.rpow_mul hx0.le]
  rw [h1, h2, mul_assoc, ← Real.rpow_add hx0] at hgm
  calc c ^ 2 * x ^ (-(σ / k + (1 + δ) * (1 - 1 / k)))
      = c ^ 2 * x ^ (-σ / k + -(1 + δ) * (1 - 1 / k)) := by congr 2; ring
    _ ≤ _ := hgm

/-- **Below the weight.** At an attained off-line top the `2k`-th tensor series diverges for every
`σ < 1 + 2k(Re ρ₀ − ½)`. -/
theorem not_summable_tensorTerm_of_max {Z : ZeroConfig} (hZ : TemperedConfig Z) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ Z.carrier) (hoff : 1 / 2 < ρ₀.re) (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re)
    {k : ℕ} (hk : 1 ≤ k) {σ : ℝ} (hσ : σ < 1 + 2 * k * (ρ₀.re - 1 / 2)) :
    ¬ Summable (tensorTerm Z k σ) := by
  intro hsum
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set δ : ℝ := (1 + 2 * k * (ρ₀.re - 1 / 2) - σ) / k with hδ
  have hδ0 : 0 < δ := by rw [hδ]; exact div_pos (by linarith) hk0
  have hw₂ : 0 ≤ 1 - 1 / (k : ℝ) := by
    rw [sub_nonneg, div_le_one hk0]; exact_mod_cast hk
  have hw₂' : 1 - 1 / (k : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith
  -- the comparison exponent is at most twice the top
  have hexp : σ / k + (1 + δ) * (1 - 1 / k) ≤ 2 * ρ₀.re := by
    have hδk : δ * k = 1 + 2 * k * (ρ₀.re - 1 / 2) - σ := by
      rw [hδ]; field_simp
    have h1 : δ * (1 - 1 / k) ≤ δ := by nlinarith
    have h2 : σ / k + (1 - 1 / k) + δ = 2 * ρ₀.re := by
      field_simp
      nlinarith
    nlinarith
  have hR := not_summable_rankinSquare_of_max Z hZ hρ₀ hoff hmax
  apply hR
  have hS : Summable fun j : ℕ => 1 / (k : ℝ) * tensorTerm Z k σ j +
      (1 - 1 / (k : ℝ)) * (Λ (j + 1) * ((j : ℝ) + 1) ^ (-(1 + δ))) :=
    (hsum.mul_left (1 / (k : ℝ))).add ((summable_vonMangoldt_rpow
      (show 1 < 1 + δ by linarith)).mul_left (1 - 1 / (k : ℝ)))
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hS
  · exact mul_nonneg (mul_nonneg vonMangoldt_nonneg (sq_nonneg _)) (by positivity)
  · have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
    have hΛ : 0 ≤ Λ (j + 1) := vonMangoldt_nonneg
    set c := 2 * (lagStructure Z (boxSpline 1 3) (Real.log ((j : ℝ) + 1))).re
    have hmono : ((j : ℝ) + 1) ^ (-(2 * ρ₀.re)) ≤
        ((j : ℝ) + 1) ^ (-(σ / k + (1 + δ) * (1 - 1 / k))) :=
      Real.rpow_le_rpow_of_exponent_le hj1 (by linarith)
    have hamgm := sq_mul_rpow_le_tensor c hj1 hk σ δ
    calc Λ (j + 1) * c ^ 2 * ((j : ℝ) + 1) ^ (-(2 * ρ₀.re))
        ≤ Λ (j + 1) * (c ^ 2 * ((j : ℝ) + 1) ^ (-(σ / k + (1 + δ) * (1 - 1 / k)))) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmono (sq_nonneg _)) hΛ
      _ ≤ Λ (j + 1) * (1 / k * (c ^ (2 * k) * ((j : ℝ) + 1) ^ (-σ)) +
            (1 - 1 / k) * ((j : ℝ) + 1) ^ (-(1 + δ))) := mul_le_mul_of_nonneg_left hamgm hΛ
      _ = 1 / k * tensorTerm Z k σ j + (1 - 1 / k) * (Λ (j + 1) * ((j : ℝ) + 1) ^ (-(1 + δ))) := by
          unfold tensorTerm; push_cast; ring

/-- **The abscissa of every tensor power is `1 + 2kb`.** -/
theorem summable_tensorTerm_iff_of_max {Z : ZeroConfig} (hZ : TemperedConfig Z) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ Z.carrier) (hoff : 1 / 2 < ρ₀.re) (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re)
    {k : ℕ} (hk : 1 ≤ k) {σ : ℝ} (hσ : σ ≠ 1 + 2 * k * (ρ₀.re - 1 / 2)) :
    Summable (tensorTerm Z k σ) ↔ 1 + 2 * k * (ρ₀.re - 1 / 2) < σ := by
  have htop : TopDepth Z (ρ₀.re - 1 / 2) := by
    intro z hz
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · have h1 := hmax _ h; simp at h1; linarith
    · have h1 := hmax _ h; simp at h1; linarith
  constructor
  · intro hs
    by_contra hle
    push Not at hle
    exact not_summable_tensorTerm_of_max hZ hρ₀ hoff hmax hk (lt_of_le_of_ne hle hσ) hs
  · exact summable_tensorTerm hZ htop k

/-! ### Milestone M4 is the Riemann hypothesis -/

/-- One moment bound at `k` bounds the width by `(1 + |A|)/(2k)`. -/
theorem zetaZeroWidth_le_of_primeTraceMoment_le {k : ℕ} {A C : ℝ}
    (hC : ∀ N : ℕ, primeTraceMoment k N ≤ C * (N : ℝ) ^ (1 + A)) (hA : 1 + |A| < k) :
    zetaZeroWidth ≤ (1 + |A|) / (2 * k) := by
  have hk0 : (0 : ℝ) < k := by linarith [abs_nonneg A]
  set a : ℝ := (1 + |A|) / (2 * k) with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have ha1 : a < 1 / 2 := by
    rw [ha, div_lt_iff₀ (by positivity)]; linarith
  rw [zetaZeroWidth_le_iff_bddBelow_primeDegrees ha0 ha1]
  set B : ℝ := |C| / Real.log 2 with hB
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  refine ⟨B ^ ((1 : ℝ) / (2 * k)), fun p hp => ?_⟩
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  have hlogp : Real.log 2 ≤ Real.log p :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  set c := 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re with hc
  have hone : Real.log p * c ^ (2 * k) ≤ C * (p : ℝ) ^ (1 + A) := by
    have hmem : p ∈ (Finset.range (p + 1)).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self p), hp⟩
    have h := hC p
    unfold primeTraceMoment at h
    refine le_trans (Finset.single_le_sum (f := fun q : ℕ => Real.log q *
      (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log q)).re) ^ (2 * k))
      (fun q hq => mul_nonneg (Real.log_nonneg (by
        exact_mod_cast (Finset.mem_filter.mp hq).2.one_lt.le)) (by
          rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)) hmem) h
  have hpA : (p : ℝ) ^ (1 + A) ≤ (p : ℝ) ^ (1 + |A|) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith [le_abs_self A])
  have hc2k : |c| ^ (2 * k) ≤ B * (p : ℝ) ^ (1 + |A|) := by
    rw [show |c| ^ (2 * k) = c ^ (2 * k) by rw [pow_mul, pow_mul, sq_abs]]
    have h1 : Real.log 2 * c ^ (2 * k) ≤ Real.log p * c ^ (2 * k) :=
      mul_le_mul_of_nonneg_right hlogp (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)
    have h2 : C * (p : ℝ) ^ (1 + A) ≤ |C| * (p : ℝ) ^ (1 + |A|) :=
      mul_le_mul (le_abs_self C) hpA (by positivity) (abs_nonneg C)
    rw [hB, div_mul_eq_mul_div, le_div_iff₀ hlog2]
    linarith
  have hroot : |c| ≤ B ^ ((1 : ℝ) / (2 * k)) * (p : ℝ) ^ a := by
    have h1 := Real.rpow_le_rpow (by positivity) hc2k (by positivity : (0 : ℝ) ≤ 1 / (2 * k))
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg c),
      show ((2 * k : ℕ) : ℝ) * (1 / (2 * k)) = 1 by push_cast; field_simp, Real.rpow_one,
      Real.mul_rpow hB0 (by positivity), ← Real.rpow_mul hp0.le] at h1
    rw [ha]
    convert h1 using 3
    ring
  linarith [neg_abs_le c]

/-- **M4 is RH.** The tensor moment exponents are sublinear in `k` iff RH. -/
theorem riemannHypothesis_iff_tensorExponent_sublinear :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      ∃ C : ℝ, ∀ N : ℕ, primeTraceMoment k N ≤ C * (N : ℝ) ^ (1 + ε * k) := by
  constructor
  · intro hRH ε hε
    obtain ⟨A, hA⟩ := riemannHypothesis_iff_moments_primeTraces.mp hRH
    obtain ⟨k₀, hk₀⟩ := exists_nat_ge (|A| / ε)
    filter_upwards [eventually_ge_atTop (max k₀ 1)] with k hk
    have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
    obtain ⟨C, hC⟩ := hA k hk1
    have hAk : A ≤ ε * k := by
      have : |A| / ε ≤ k := hk₀.trans (by exact_mod_cast le_trans (le_max_left _ _) hk)
      rw [div_le_iff₀ hε] at this
      linarith [le_abs_self A]
    refine ⟨|C|, fun N => ?_⟩
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      have h0 : primeTraceMoment k 0 = 0 := by
        simp [primeTraceMoment, Finset.range_one, Finset.filter_singleton, Nat.not_prime_zero]
      rw [h0, Nat.cast_zero, Real.zero_rpow (by positivity), mul_zero]
    · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      calc primeTraceMoment k N ≤ C * (N : ℝ) ^ (1 + A) := hC N
        _ ≤ |C| * (N : ℝ) ^ (1 + A) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ |C| * (N : ℝ) ^ (1 + ε * k) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
              (abs_nonneg C)
  · intro h
    rw [riemannHypothesis_iff_zetaZeroWidth_le_zero]
    refine le_of_forall_pos_le_add fun η hη => ?_
    set ε : ℝ := min η (1 / 2) with hεdef
    have hε : 0 < ε := lt_min hη (by norm_num)
    have hεη : ε ≤ η := min_le_left _ _
    have hε2 : ε ≤ 1 / 2 := min_le_right _ _
    obtain ⟨k₀, hk₀⟩ := exists_nat_ge (1 / η + 3)
    obtain ⟨k, ⟨C, hC⟩, hk⟩ := ((h ε hε).and (eventually_ge_atTop k₀)).exists
    have hkR : 1 / η + 3 ≤ (k : ℝ) := hk₀.trans (by exact_mod_cast hk)
    have hk0 : (0 : ℝ) < k := by have : 0 < 1 / η := by positivity
                                 linarith
    have habs : |ε * k| = ε * k := abs_of_nonneg (by positivity)
    have hlt : 1 + |ε * k| < k := by rw [habs]; nlinarith
    have hw := zetaZeroWidth_le_of_primeTraceMoment_le hC hlt
    rw [habs] at hw
    have hsplit : (1 + ε * k) / (2 * k) = 1 / (2 * k) + ε / 2 := by field_simp; ring
    have hinv : 1 / (2 * (k : ℝ)) ≤ η / 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : 1 / η ≤ k := by linarith
      rw [div_le_iff₀ hη] at this
      nlinarith
    linarith

end GaloisForLFunctions.ArithmeticWeightTheory
