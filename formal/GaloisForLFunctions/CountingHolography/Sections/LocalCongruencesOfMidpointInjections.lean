import GaloisForLFunctions.CountingHolography.Sections.MidpointProductsOfSmallSections
import GaloisForLFunctions.CountingHolography.Sections.TwoPlacePrecisionOnIntegerIntervals

/-!
# Local congruences of midpoint injections

Use a positive divisor b and the three rays 2b, 3b and 4b. Their section
intervals have exponents 4Q(b), 9Q(b) and 16Q(b). One prescribed place
allows a congruence-preserving packing. At two places every packing must
lose precision of positive quadratic logarithmic size.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology ArithmeticScatteringHolography

/-- Cardinality of the section interval on the kth multiple of a ray. -/
def rayCard {N : ℕ} (b : Fin N → ℤ) (k m : ℕ) : ℕ := (divisorSections (m • (k • b))).card

theorem rayCard_pos {N : ℕ} (b : Fin N → ℤ) (k m : ℕ) : 0 < rayCard b k m := by
  rw [rayCard, divisorSections, card_smallSections]
  omega

/-- Consecutive indices translate the actual integer sections by their
common left endpoint. -/
def rayOrdinal {N : ℕ} (b : Fin N → ℤ) (k m : ℕ) :
    ↥(divisorSections (m • (k • b))) ≃ Fin (rayCard b k m) :=
  sectionOrdinal _ _

private def logRate (f : ℕ → ℕ) (v : ℝ) : Prop :=
  Tendsto (fun m : ℕ => Real.log (f m : ℝ)/(m : ℝ)^2) atTop (𝓝 v)

theorem rayCard_tateLimit {N : ℕ} {b : Fin N → ℤ} (hb : 0 < integerProbe N b) (k : ℕ) :
    Tendsto (fun m : ℕ => Real.log (rayCard b k m)/(m : ℝ)^2) atTop
      (𝓝 ((k : ℝ)^2 * integerProbe N b)) := by
  have h := logCard_tateLimit (k • b)
  rw [integerProbe_smul, max_eq_left (mul_nonneg (sq_nonneg _) hb.le)] at h
  exact h

private theorem logRate_const (c : ℕ) : logRate (fun _ => c) 0 := by
  have hi : Tendsto (fun m : ℕ => ((m : ℝ)^2)⁻¹) atTop (𝓝 0) :=
    ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  simpa only [logRate, div_eq_mul_inv, mul_zero] using hi.const_mul (Real.log c)

private theorem logRate_mul {f g : ℕ → ℕ} {v w : ℝ} (hf : logRate f v) (hg : logRate g w)
    (hf₀ : ∀ m, 0 < f m) (hg₀ : ∀ m, 0 < g m) : logRate (fun m => f m * g m) (v+w) := by
  apply (hf.add hg).congr
  intro m
  rw [Nat.cast_mul, Real.log_mul (Nat.cast_pos.mpr (hf₀ m)).ne' (Nat.cast_pos.mpr (hg₀ m)).ne', add_div]

private theorem eventually_lt_of_logRate {f g : ℕ → ℕ} {v w : ℝ}
    (hf : logRate f v) (hg : logRate g w) (hf₀ : ∀ m, 0 < f m) (hg₀ : ∀ m, 0 < g m)
    (hv : v < w) : ∀ᶠ m : ℕ in atTop, f m < g m := by
  have hl := (hg.sub hf).eventually_const_lt (sub_pos.mpr hv)
  filter_upwards [hl, eventually_ge_atTop 1] with m hm hm1
  have he := sub_pos.mp hm
  rw [div_lt_div_iff_of_pos_right (by positivity : 0 < (m : ℝ)^2),
    Real.log_lt_log_iff (Nat.cast_pos.mpr (hf₀ m)) (Nat.cast_pos.mpr (hg₀ m))] at he
  exact_mod_cast he

theorem eventually_wide_lt_square {N : ℕ} {b : Fin N → ℤ} (hb : 0 < integerProbe N b) :
    ∀ᶠ m : ℕ in atTop, rayCard b 4 m < rayCard b 3 m * rayCard b 3 m := by
  have hn := rayCard_tateLimit hb 3
  exact eventually_lt_of_logRate (rayCard_tateLimit hb 4) (logRate_mul hn hn (rayCard_pos b 3) (rayCard_pos b 3))
    (rayCard_pos b 4) (fun m => Nat.mul_pos (rayCard_pos b 3 m) (rayCard_pos b 3 m)) (by push_cast; linarith)

/-- Every fixed multiple of the narrow interval eventually fits inside the middle interval. -/
theorem eventually_narrow_mul_lt_middle {N : ℕ} {b : Fin N → ℤ} (hb : 0 < integerProbe N b)
    (C : ℕ) (hC : 0 < C) : ∀ᶠ m : ℕ in atTop, C * rayCard b 2 m < rayCard b 3 m := by
  apply eventually_lt_of_logRate (logRate_mul (logRate_const C) (rayCard_tateLimit hb 2)
    (fun _ => hC) (rayCard_pos b 2)) (rayCard_tateLimit hb 3)
    (fun m => Nat.mul_pos hC (rayCard_pos b 2 m)) (rayCard_pos b 3)
  push_cast
  linarith

private theorem eventually_one_place_area {N : ℕ} {b : Fin N → ℤ} (hb : 0 < integerProbe N b)
    {p : ℕ} (hp : 1 < p) : ∀ᶠ m : ℕ in atTop,
      4*p*(rayCard b 3 m)^2 ≤ rayCard b 4 m * rayCard b 2 m := by
  have hn := rayCard_tateLimit hb 3
  have hnn := logRate_mul hn hn (rayCard_pos b 3) (rayCard_pos b 3)
  have hn₀ (m : ℕ) := Nat.mul_pos (rayCard_pos b 3 m) (rayCard_pos b 3 m)
  have hc : 0 < 4*p := by omega
  have hl := logRate_mul (logRate_const (4*p)) hnn (fun _ => hc) hn₀
  have hr := logRate_mul (rayCard_tateLimit hb 4) (rayCard_tateLimit hb 2) (rayCard_pos b 4) (rayCard_pos b 2)
  have h := eventually_lt_of_logRate hl hr (fun m => Nat.mul_pos hc (hn₀ m))
    (fun m => Nat.mul_pos (rayCard_pos b 4 m) (rayCard_pos b 2 m)) (by push_cast; linarith)
  exact h.mono fun m hm => by simpa only [sq] using hm.le

/-- Embeddings between products of the actual section intervals. -/
abbrev rayProductEmbedding {N : ℕ} (b : Fin N → ℤ) (m : ℕ) :=
  (↥(divisorSections (m • (3 • b))) × ↥(divisorSections (m • (3 • b)))) ↪
    (↥(divisorSections (m • (4 • b))) × ↥(divisorSections (m • (2 • b))))

/-- Express an actual section embedding in consecutive interval coordinates. -/
def ordinalEmbedding {N : ℕ} (b : Fin N → ℤ) (m : ℕ) (e : rayProductEmbedding b m) :
    (Fin (rayCard b 3 m) × Fin (rayCard b 3 m)) ↪ (Fin (rayCard b 4 m) × Fin (rayCard b 2 m)) :=
  (((rayOrdinal b 3 m).prodCongr (rayOrdinal b 3 m)).symm.toEmbedding.trans e).trans
    ((rayOrdinal b 4 m).prodCongr (rayOrdinal b 2 m)).toEmbedding

/-- Any one prescribed place admits a congruence-preserving section
injection at every sufficiently high multiplicity on a positive ray. -/
theorem eventually_onePlace_sectionEmbedding {N : ℕ} {b : Fin N → ℤ} (hb : 0 < integerProbe N b)
    {p : ℕ} (hp : 1 < p) : ∀ᶠ m : ℕ in atTop,
      ∃ e : rayProductEmbedding b m, preservesPlace (ordinalEmbedding b m e) p := by
  have hsn := eventually_lt_of_logRate (rayCard_tateLimit hb 2) (rayCard_tateLimit hb 3)
    (rayCard_pos b 2) (rayCard_pos b 3) (by push_cast; linarith)
  filter_upwards [hsn, eventually_one_place_area hb hp] with m hs harea
  obtain ⟨e,he⟩ := exists_embedding_preserving_one_place hp (rayCard_pos b 2 m) hs.le harea
  let S := (rayOrdinal b 3 m).prodCongr (rayOrdinal b 3 m)
  let D := (rayOrdinal b 4 m).prodCongr (rayOrdinal b 2 m)
  let e' : rayProductEmbedding b m := (S.toEmbedding.trans e).trans D.symm.toEmbedding
  have he' : ordinalEmbedding b m e' = e := by
    ext x : 1
    change D (D.symm (e (S (S.symm x)))) = e x
    rw [D.apply_symm_apply, S.apply_symm_apply]
  exact ⟨e', by rwa [he']⟩

private theorem log_nat_product (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Real.log ((a*b : ℕ) : ℝ) = Real.log a + Real.log b := by
  rw [Nat.cast_mul, Real.log_mul (Nat.cast_pos.mpr ha).ne' (Nat.cast_pos.mpr hb).ne']

/-- Every section injection loses positive quadratic logarithmic precision
at two coprime places, even if only the narrower coordinate is constrained. -/
theorem eventually_twoPlace_precision_cost {N : ℕ} {b : Fin N → ℤ} (hb : 0 < integerProbe N b)
    {p q : ℕ} (hp : 1 < p) (hq : 1 < q) (hc : p.Coprime q)
    {δ : ℝ} (hδ : δ < integerProbe N b) :
    ∀ᶠ m : ℕ in atTop, ∀ (e : rayProductEmbedding b m) (i j : ℕ),
      secondPrecisionLoss (ordinalEmbedding b m e) p i →
      secondPrecisionLoss (ordinalEmbedding b m e) q j →
      δ * (m : ℝ)^2 < (i : ℝ)*Real.log p + (j : ℝ)*Real.log q := by
  have hs := rayCard_tateLimit hb 2
  have ht := (((rayCard_tateLimit hb 3).sub (hs.const_mul 2)).sub (logRate_const (p*q))).eventually_const_lt
    (show δ < (3 : ℝ)^2*integerProbe N b - 2*((2 : ℝ)^2*integerProbe N b) - 0 by linarith)
  filter_upwards [eventually_wide_lt_square hb, ht, eventually_ge_atTop 1] with m hL hm hm1
  intro e i j hi hj
  let s := rayCard b 2 m
  let n := rayCard b 3 m
  have hs' : 0 < s := rayCard_pos _ _ _
  have hn' : 0 < n := rayCard_pos _ _ _
  have hp' : 0 < p := by omega
  have hq' : 0 < q := by omega
  have hh := two_place_precision_loss (ordinalEmbedding b m e) hp hq hc hs' hL hi hj
  have hlog := Real.log_lt_log (Nat.cast_pos.mpr hn' : 0 < (n : ℝ)) (Nat.cast_lt.mpr hh)
  change Real.log n < Real.log (((p*q*s^2)*(p^i*q^j) : ℕ) : ℝ) at hlog
  rw [log_nat_product _ _ (by positivity) (by positivity),
    log_nat_product (p*q) (s^2) (by positivity) (by positivity),
    log_nat_product (p^i) (q^j) (by positivity) (by positivity),
    Nat.cast_pow, Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  change δ < Real.log n/(m : ℝ)^2 - 2*(Real.log s/(m : ℝ)^2) - Real.log (p*q : ℕ)/(m : ℝ)^2 at hm
  have he : δ < (Real.log n - 2*Real.log s - Real.log (p*q : ℕ))/(m : ℝ)^2 := by
    convert hm using 1
    ring
  have hm' := (lt_div_iff₀ (by positivity : 0 < (m : ℝ)^2)).mp he
  push_cast at hlog hm'
  linarith only [hm',hlog]

/-- A positive two-atom divisor exhibits both the one-place construction
and the two-place obstruction without assuming any zero distribution. -/
theorem exists_prime_ray_with_onePlace_only :
    ∃ (p : ℕ) (b : Fin (p+1) → ℤ), p.Prime ∧ (b = primePair p ∨ b = primeDifference p) ∧
      (∀ t : ℕ, 1 < t → ∀ᶠ m : ℕ in atTop,
        ∃ e : rayProductEmbedding b m, preservesPlace (ordinalEmbedding b m e) t) ∧
      ∀ᶠ m : ℕ in atTop, ¬ ∃ e : rayProductEmbedding b m,
        secondPrecisionLoss (ordinalEmbedding b m e) 2 0 ∧ secondPrecisionLoss (ordinalEmbedding b m e) 3 0 := by
  obtain ⟨p,b,hp,he,hb,_⟩ := exists_prime_background_midpointTest
  refine ⟨p,b,hp,he,fun t ht => eventually_onePlace_sectionEmbedding hb ht,?_⟩
  filter_upwards [eventually_twoPlace_precision_cost hb (by decide : 1 < 2) (by decide : 1 < 3)
    (by decide : Nat.Coprime 2 3) hb] with m hm
  rintro ⟨e,h₂,h₃⟩
  simpa using hm e 0 0 h₂ h₃

#print axioms exists_prime_ray_with_onePlace_only
#print axioms eventually_twoPlace_precision_cost

end GaloisForLFunctions.CountingHolography.Sections
