import GaloisForLFunctions.VerifiedHeightRungs.JensenEntries
import GaloisForLFunctions.RHTower.XiGaussianHeatTwoPrimeSourceSampling
import GaloisForLFunctions.RHTower.ZetaLocalZeroCount
import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.HeatGridDegrees

/-!
# Heat grid forms of degree `≲ T` from verified zeros

**Theorem.** If RH holds through `X ≥ heatGridHeight h` and `deg p + 1 ≤ X/4800`, then at every offset `K`
the sampled heat form of `p²` on the grid `(2K+1+n)h` is nonnegative. On the pole hyperplane the same holds
for the literal archimedean-minus-prime source.

A verified zero gives a positive atom. To dominate the atoms above `X`, the mass of a polynomial on a small disc
is compared with its mass on `deg p + 1` verified nodes, by Lagrange interpolation. Local zero counts extract
nodes whose absolute ordinates are `1`-separated; for such nodes every Lagrange factor is at most `2/(1 - e^{-h})`
on the disc, with no loss from the size of the nodes.
-/

open Polynomial Filter Topology Complex Set
open RHTower
open scoped ComplexConjugate

namespace GaloisForLFunctions.VerifiedHeightRungs

noncomputable section

/-! ## Lagrange comparison on separated nodes -/

/-- The mass of a real polynomial on a small disc is controlled by its values at relatively separated nodes. -/
theorem norm_evalRealPolynomial_sq_le_of_separated {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℝ)
    {ℓ κ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ) (hv : ∀ i ∈ s, ℓ ≤ v i)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → v i * κ ≤ |v i - v j|) (p : ℝ[X]) (hp : p.natDegree < s.card)
    {z : ℂ} (hz : ‖z‖ ≤ ℓ) :
    ‖evalRealPolynomial p z‖ ^ 2 ≤
      (s.card : ℝ) * (2 / κ) ^ (2 * (s.card - 1)) * ∑ i ∈ s, p.eval (v i) ^ 2 := by
  classical
  have hvpos : ∀ i ∈ s, 0 < v i := fun i hi => hℓ.trans_le (hv i hi)
  set w : ι → ℂ := fun i => algebraMap ℝ ℂ (v i) with hw
  have hinj : Set.InjOn w s := by
    intro i hi j hj hij
    by_contra hne
    have h1 := hsep i hi j hj hne
    have hvij : v i = v j := Complex.ofReal_injective hij
    rw [hvij, sub_self, abs_zero] at h1
    have hpos : 0 < v j * κ := mul_pos (hvpos j hj) hκ
    linarith only [h1, hpos]
  set P := p.map (algebraMap ℝ ℂ) with hP
  have hdeg : P.degree < s.card := by
    rw [hP, degree_map]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast hp)
  have hinterp := Lagrange.eq_interpolate hinj hdeg
  have hnode (i : ι) : P.eval (w i) = algebraMap ℝ ℂ (p.eval (v i)) := by
    rw [hP, hw]
    exact eval_map_apply _ _
  -- Every Lagrange basis value is at most `(2/κ)^(|s|-1)`.
  have hfactor : ∀ i ∈ s, ∀ j ∈ s.erase i,
      ‖(Lagrange.basisDivisor (w i) (w j)).eval z‖ ≤ 2 / κ := by
    intro i hi j hj
    have hjs : j ∈ s := Finset.mem_of_mem_erase hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hvj := hvpos j hjs
    rw [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X, eval_C, norm_mul, norm_inv]
    have hsub : w i - w j = ((v i - v j : ℝ) : ℂ) := by
      simp [hw]
    have hnorm : ‖w i - w j‖ = |v j - v i| := by
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    have hlow := hsep j hjs i hi hji
    have hzw : ‖z - w j‖ ≤ 2 * v j := by
      have h1 : ‖w j‖ = v j := by
        simp [hw, abs_of_pos hvj]
      have h2 := norm_sub_le z (w j)
      linarith only [h1, h2, hz, hv j hjs]
    rw [hnorm, inv_mul_eq_div]
    have hpos : 0 < v j * κ := mul_pos hvj hκ
    have e : 2 / κ = 2 * v j / (v j * κ) := by
      field_simp
    rw [e]
    exact div_le_div₀ (by positivity) hzw hpos hlow
  have hbasis : ∀ i ∈ s, ‖(Lagrange.basis s w i).eval z‖ ≤ (2 / κ) ^ (s.card - 1) := by
    intro i hi
    rw [Lagrange.basis, eval_prod, norm_prod, ← Finset.card_erase_of_mem hi]
    calc
      ∏ j ∈ s.erase i, ‖(Lagrange.basisDivisor (w i) (w j)).eval z‖ ≤ ∏ _j ∈ s.erase i, 2 / κ :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (hfactor i hi)
      _ = _ := by rw [Finset.prod_const]
  have hexp : P.eval z = ∑ i ∈ s, algebraMap ℝ ℂ (p.eval (v i)) * (Lagrange.basis s w i).eval z := by
    conv_lhs => rw [hinterp]
    rw [Lagrange.interpolate_apply, eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eval_mul, eval_C, hnode]
  have hsum : ‖P.eval z‖ ≤ (2 / κ) ^ (s.card - 1) * ∑ i ∈ s, |p.eval (v i)| := by
    rw [hexp, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul, mul_comm]
    have e : ‖algebraMap ℝ ℂ (p.eval (v i))‖ = |p.eval (v i)| := by
      simp
    rw [e]
    exact mul_le_mul_of_nonneg_right (hbasis i hi) (abs_nonneg _)
  have hCS := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => |p.eval (v i)|)
  simp only [sq_abs] at hCS
  have hB : 0 ≤ (2 / κ) ^ (s.card - 1) := by positivity
  change ‖P.eval z‖ ^ 2 ≤ _
  calc
    ‖P.eval z‖ ^ 2 ≤ ((2 / κ) ^ (s.card - 1) * ∑ i ∈ s, |p.eval (v i)|) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hsum 2
    _ = ((2 / κ) ^ (s.card - 1)) ^ 2 * (∑ i ∈ s, |p.eval (v i)|) ^ 2 := by ring
    _ ≤ ((2 / κ) ^ (s.card - 1)) ^ 2 * ((s.card : ℝ) * ∑ i ∈ s, p.eval (v i) ^ 2) :=
      mul_le_mul_of_nonneg_left hCS (by positivity)
    _ = _ := by
      rw [← pow_mul, mul_comm (s.card - 1) 2]
      ring

theorem exp_neg_lt_one {h : ℝ} (hh : 0 < h) : Real.exp (-h) < 1 := by
  have h1 := Real.exp_lt_exp.2 (neg_lt_zero.2 hh)
  rwa [Real.exp_zero] at h1

/-- Gaussian values at `1`-separated abscissas are relatively separated. -/
theorem exp_mul_le_abs_sub_exp {h a b : ℝ} (hh : 0 < h) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : 1 ≤ |a - b|) :
    Real.exp (-h * a ^ 2) * (1 - Real.exp (-h)) ≤
      |Real.exp (-h * a ^ 2) - Real.exp (-h * b ^ 2)| := by
  have hexp : 0 < Real.exp (-h) := Real.exp_pos _
  have hlt : Real.exp (-h) < 1 := exp_neg_lt_one hh
  rcases le_abs.1 hab with h1 | h1
  · -- `a ≥ b + 1`: the larger value is the one at `b`.
    have hsq : b ^ 2 + 1 ≤ a ^ 2 := by nlinarith only [h1, ha, hb]
    have hle : Real.exp (-h * a ^ 2) ≤ Real.exp (-h * b ^ 2) * Real.exp (-h) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith only [hh, hsq]
    have hba : Real.exp (-h * a ^ 2) ≤ Real.exp (-h * b ^ 2) :=
      hle.trans (mul_le_of_le_one_right (Real.exp_pos _).le hlt.le)
    rw [abs_sub_comm]
    refine le_trans ?_ (le_abs_self _)
    nlinarith only [hle, hba, hlt, hexp]
  · -- `b ≥ a + 1`.
    have hsq : a ^ 2 + 1 ≤ b ^ 2 := by nlinarith only [h1, ha, hb]
    have hle : Real.exp (-h * b ^ 2) ≤ Real.exp (-h * a ^ 2) * Real.exp (-h) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith only [hh, hsq]
    refine le_trans ?_ (le_abs_self _)
    linarith only [hle]

/-! ## Separated verified nodes -/

/-- The absolute ordinate of a zero copy. -/
def absOrdinate (q : XiZeroCopy) : ℝ := |(xiSpectralPoint q).re|

/-- A unit fibre of the absolute ordinate has at most `160 log T` copies. -/
theorem card_fibre_le {T : ℝ} (hT : 360 ≤ T) {n : ℕ} (hn : 4 ≤ n) (hn2 : (n : ℝ) ≤ 2 * T)
    (F : Finset XiZeroCopy) (hF : ∀ q ∈ F, ⌊absOrdinate q⌋₊ = n) :
    (F.card : ℝ) ≤ 160 * Real.log T := by
  classical
  have hT0 : 0 < T := by linarith only [hT]
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith only [hn4]
  have hfloor (q : XiZeroCopy) (hq : q ∈ F) :
      (n : ℝ) ≤ absOrdinate q ∧ absOrdinate q < n + 1 := by
    have h := hF q hq
    have h0 : 0 ≤ absOrdinate q := abs_nonneg _
    constructor
    · rw [← h]
      exact Nat.floor_le h0
    · rw [← h]
      exact Nat.lt_floor_add_one _
  have hlog : Real.log (180 * (n : ℝ)) ≤ 2 * Real.log T := by
    have h1 : 180 * (n : ℝ) ≤ T ^ 2 := by nlinarith only [hn2, hT]
    calc
      Real.log (180 * (n : ℝ)) ≤ Real.log (T ^ 2) := Real.log_le_log (by positivity) h1
      _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
  have hpos : ((F.filter fun q => 0 < (xiSpectralPoint q).re).card : ℝ) ≤ 80 * Real.log T := by
    have h := card_le_of_ordinates_in_window (t := (n : ℝ))
      (by rw [abs_of_pos hn0]; exact hn4) (F.filter fun q => 0 < (xiSpectralPoint q).re) (by
        intro q hq
        rw [Finset.mem_filter] at hq
        have hb := hfloor q hq.1
        rw [absOrdinate, abs_of_pos hq.2, re_xiSpectralPoint] at hb
        rw [abs_le]
        constructor <;> linarith only [hb.1, hb.2])
    rw [abs_of_pos hn0] at h
    linarith only [h, hlog]
  have hneg : ((F.filter fun q => ¬ 0 < (xiSpectralPoint q).re).card : ℝ) ≤ 80 * Real.log T := by
    have h := card_le_of_ordinates_in_window (t := -(n : ℝ))
      (by rw [abs_neg, abs_of_pos hn0]; exact hn4) (F.filter fun q => ¬ 0 < (xiSpectralPoint q).re) (by
        intro q hq
        rw [Finset.mem_filter] at hq
        have hb := hfloor q hq.1
        rw [absOrdinate, abs_of_nonpos (not_lt.1 hq.2), re_xiSpectralPoint] at hb
        rw [abs_le]
        constructor <;> linarith only [hb.1, hb.2])
    rw [abs_neg, abs_of_pos hn0] at h
    linarith only [h, hlog]
  have hsplit := Finset.card_filter_add_card_filter_not (s := F)
    (fun q => 0 < (xiSpectralPoint q).re)
  have hcast : (F.card : ℝ) = ((F.filter fun q => 0 < (xiSpectralPoint q).re).card : ℝ) +
      ((F.filter fun q => ¬ 0 < (xiSpectralPoint q).re).card : ℝ) := by
    rw [← hsplit]
    push_cast
    rfl
  rw [hcast]
  linarith only [hpos, hneg]

/-- A set of natural numbers contains a same-parity half. -/
theorem exists_same_parity_half (I : Finset ℕ) :
    ∃ J ⊆ I, I.card ≤ 2 * J.card ∧ ∀ n ∈ J, ∀ m ∈ J, n ≠ m → n + 2 ≤ m ∨ m + 2 ≤ n := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := I) (fun n => n % 2 = 0)
  by_cases hc : (I.filter fun n => ¬ n % 2 = 0).card ≤ (I.filter fun n => n % 2 = 0).card
  · refine ⟨I.filter fun n => n % 2 = 0, Finset.filter_subset _ _, by omega, ?_⟩
    intro n hn m hm hnm
    have h1 := (Finset.mem_filter.1 hn).2
    have h2 := (Finset.mem_filter.1 hm).2
    omega
  · refine ⟨I.filter fun n => ¬ n % 2 = 0, Finset.filter_subset _ _, by omega, ?_⟩
    intro n hn m hm hnm
    have h1 := (Finset.mem_filter.1 hn).2
    have h2 := (Finset.mem_filter.1 hm).2
    omega

/-- **Separated nodes.** The band `(T, 2T]` contains `T/1200` copies whose absolute ordinates are `1`-separated. -/
theorem exists_separated_nodes {T : ℝ} (hT : xiMassHeight (1 / 100) ≤ T) (hT360 : 360 ≤ T) {n : ℕ}
    (hn : 1200 * (n : ℝ) ≤ T) :
    ∃ s : Finset XiZeroCopy, s.card = n ∧ (∀ q ∈ s, T < absOrdinate q ∧ absOrdinate q ≤ 2 * T) ∧
      ∀ q ∈ s, ∀ q' ∈ s, q ≠ q' → 1 ≤ |absOrdinate q - absOrdinate q'| := by
  classical
  have hT0 : 0 < T := by linarith only [hT360]
  have hL : 0 < Real.log T := Real.log_pos (by linarith only [hT360])
  set B := xiCopiesBand T (2 * T) with hB
  have hmem : ∀ q ∈ B, T < absOrdinate q ∧ absOrdinate q ≤ 2 * T := by
    intro q hq
    rw [hB, mem_xiCopiesBand, ← re_xiSpectralPoint] at hq
    exact hq
  set f : XiZeroCopy → ℕ := fun q => ⌊absOrdinate q⌋₊ with hf
  set I := B.image f with hI
  have hcard : (B.card : ℝ) ≤ I.card * (160 * Real.log T) := by
    rw [Finset.card_eq_sum_card_image f B, ← nsmul_eq_mul]
    push_cast
    refine Finset.sum_le_card_nsmul _ _ _ fun k hk => ?_
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hk
    have hb := hmem q hq
    have h0 : 0 ≤ absOrdinate q := abs_nonneg _
    refine card_fibre_le hT360 ?_ ?_ _ fun q' hq' => (Finset.mem_filter.1 hq').2
    · exact Nat.le_floor (by push_cast; linarith only [hb.1, hT360])
    · exact (Nat.floor_le h0).trans hb.2
  have hlow := le_card_band hT
  have hI_low : T / 600 ≤ (I.card : ℝ) := by
    have h1 : T / 600 * (160 * Real.log T) ≤ I.card * (160 * Real.log T) := by
      refine le_trans ?_ (hlow.trans hcard)
      have : 0 ≤ T * Real.log T := by positivity
      nlinarith only [this]
    exact le_of_mul_le_mul_right h1 (by positivity)
  obtain ⟨J, hJI, hJcard, hJsep⟩ := exists_same_parity_half I
  have hrep : ∀ k : J, ∃ q ∈ B, f q = k := fun k => Finset.mem_image.1 (hJI k.2)
  choose rep hrepB hrepf using hrep
  have hinj : Function.Injective rep := by
    intro a b hab
    apply Subtype.ext
    rw [← hrepf a, ← hrepf b, hab]
  have hNcard : (Finset.univ.image rep).card = J.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]
  have hle : n ≤ (Finset.univ.image rep).card := by
    rw [hNcard]
    have h2 : (I.card : ℝ) ≤ 2 * J.card := by exact_mod_cast hJcard
    have h3 : (n : ℝ) ≤ J.card := by linarith only [h2, hI_low, hn]
    exact_mod_cast h3
  obtain ⟨s, hsN, hs⟩ := Finset.exists_subset_card_eq hle
  have hsrep : ∀ q ∈ s, ∃ k : J, rep k = q := fun q hq => by
    obtain ⟨k, -, hk⟩ := Finset.mem_image.1 (hsN hq)
    exact ⟨k, hk⟩
  refine ⟨s, hs, fun q hq => ?_, fun q hq q' hq' hne => ?_⟩
  · obtain ⟨k, rfl⟩ := hsrep q hq
    exact hmem _ (hrepB k)
  · obtain ⟨a, rfl⟩ := hsrep q hq
    obtain ⟨b, rfl⟩ := hsrep q' hq'
    have hab : (a : ℕ) ≠ b := fun h => hne (congrArg rep (Subtype.ext h))
    have h0a : 0 ≤ absOrdinate (rep a) := abs_nonneg _
    have h0b : 0 ≤ absOrdinate (rep b) := abs_nonneg _
    have hfa := hrepf a
    have hfb := hrepf b
    have ha1 : ((a : ℕ) : ℝ) ≤ absOrdinate (rep a) := by
      rw [← hfa]
      exact Nat.floor_le h0a
    have ha2 : absOrdinate (rep a) < (a : ℕ) + 1 := by
      rw [← hfa]
      exact Nat.lt_floor_add_one _
    have hb1 : ((b : ℕ) : ℝ) ≤ absOrdinate (rep b) := by
      rw [← hfb]
      exact Nat.floor_le h0b
    have hb2 : absOrdinate (rep b) < (b : ℕ) + 1 := by
      rw [← hfb]
      exact Nat.lt_floor_add_one _
    rcases hJsep a a.2 b b.2 hab with h | h
    · have h' : ((a : ℕ) : ℝ) + 2 ≤ (b : ℕ) := by exact_mod_cast h
      rw [abs_sub_comm]
      exact (by linarith only [h', ha2, hb1] :
        (1 : ℝ) ≤ absOrdinate (rep b) - absOrdinate (rep a)).trans (le_abs_self _)
    · have h' : ((b : ℕ) : ℝ) + 2 ≤ (a : ℕ) := by exact_mod_cast h
      exact (by linarith only [h', hb2, ha1] :
        (1 : ℝ) ≤ absOrdinate (rep a) - absOrdinate (rep b)).trans (le_abs_self _)

/-! ## Heat atoms -/

theorem norm_heatTerm (h : ℝ) (q : XiZeroCopy) :
    ‖xiGaussianHeatTerm h q‖ =
      Real.exp (-h * ((xiSpectralPoint q).re ^ 2 - (xiSpectralPoint q).im ^ 2)) := by
  rw [xiGaussianHeatTerm, Complex.norm_exp]
  congr 1
  simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, sq]

theorem norm_heatTerm_le {h : ℝ} (hh : 0 < h) (q : XiZeroCopy) :
    ‖xiGaussianHeatTerm h q‖ ≤ Real.exp (h / 4 - h * absOrdinate q ^ 2) := by
  rw [norm_heatTerm]
  apply Real.exp_le_exp.2
  rw [absOrdinate, sq_abs]
  have h1 := abs_im_xiSpectralPoint_lt q
  have h2 : (xiSpectralPoint q).im ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]
    nlinarith only [h1, abs_nonneg (xiSpectralPoint q).im]
  nlinarith only [hh, h2]

/-- On a verified zero the heat atom is the real Gaussian of the absolute ordinate. -/
theorem heatTerm_of_im_eq_zero (h : ℝ) {q : XiZeroCopy} (hq : (xiSpectralPoint q).im = 0) :
    xiGaussianHeatTerm h q = algebraMap ℝ ℂ (Real.exp (-h * absOrdinate q ^ 2)) := by
  have hw : xiSpectralPoint q = ((xiSpectralPoint q).re : ℂ) :=
    Complex.ext (by simp) (by simp [hq])
  rw [xiGaussianHeatTerm, hw, absOrdinate, sq_abs, Complex.coe_algebraMap]
  push_cast
  try rfl

/-- The real part of a verified atom of the form. -/
theorem form_term_of_real {K : ℕ} {p : ℝ[X]} {r : ℝ} :
    (algebraMap ℝ ℂ r * evalRealPolynomial (X ^ K * p) (algebraMap ℝ ℂ r) ^ 2).re =
      r ^ (2 * K + 1) * p.eval r ^ 2 := by
  have h1 : evalRealPolynomial (X ^ K * p) (algebraMap ℝ ℂ r) = algebraMap ℝ ℂ ((X ^ K * p).eval r) :=
    eval_map_apply _ _
  rw [h1, ← map_pow, ← map_mul, Complex.coe_algebraMap, Complex.ofReal_re, eval_mul, eval_pow, eval_X]
  ring

/-- Lower bound for a general atom of the form. -/
theorem neg_form_term_le {K : ℕ} {p : ℝ[X]} (z : ℂ) :
    -(‖z‖ ^ (2 * K + 1) * ‖evalRealPolynomial p z‖ ^ 2) ≤
      (z * evalRealPolynomial (X ^ K * p) z ^ 2).re := by
  have hX : evalRealPolynomial (X ^ K * p) z = z ^ K * evalRealPolynomial p z := by
    rw [evalRealPolynomial_mul, evalRealPolynomial_pow]
    simp [evalRealPolynomial]
  have h := Complex.abs_re_le_norm (z * evalRealPolynomial (X ^ K * p) z ^ 2)
  have hn : ‖z * evalRealPolynomial (X ^ K * p) z ^ 2‖ =
      ‖z‖ ^ (2 * K + 1) * ‖evalRealPolynomial p z‖ ^ 2 := by
    rw [hX, norm_mul, norm_pow, norm_mul, norm_pow]
    ring
  rw [hn] at h
  exact neg_le_of_abs_le h

/-! ## The height and the main inequality -/

/-- The constant governing the height of a grid of spacing `h`. -/
def heatGridConstant (h : ℝ) : ℝ :=
  |Real.log (12 / h)| + 1 + 2 * Real.log (2 / (1 - Real.exp (-h))) + h / 8

/-- The explicit height above which verified zeros control the grid of spacing `h`. -/
def heatGridHeight (h : ℝ) : ℝ :=
  max (4 * xiMassHeight (1 / 100)) (max 1440 (4 * heatGridConstant h / h))

/-- Numerical domination of the Lagrange constant by the Gaussian gap. -/
theorem heat_numeric {h X : ℝ} (hh : 0 < h) (hX1 : 1 ≤ X) (hXh : 4 * heatGridConstant h / h ≤ X) {D : ℕ}
    (hD : (D : ℝ) ≤ X) :
    Real.exp (h / 8 - h * X ^ 2 / 2) *
        (((D : ℝ) + 1) * (2 / (1 - Real.exp (-h))) ^ (2 * D) * (12 / h)) ≤
      Real.exp (-h * (X / 2) ^ 2) := by
  have hlt : Real.exp (-h) < 1 := exp_neg_lt_one hh
  have hexp : 0 < Real.exp (-h) := Real.exp_pos _
  have hκ : 0 < 1 - Real.exp (-h) := by linarith only [hlt]
  have hκ1 : 1 - Real.exp (-h) < 1 := by linarith only [hexp]
  have hq : 1 ≤ 2 / (1 - Real.exp (-h)) := by
    rw [le_div_iff₀ hκ]
    linarith only [hκ1]
  set L := Real.log (2 / (1 - Real.exp (-h))) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hq
  have hqe : 2 / (1 - Real.exp (-h)) = Real.exp L := by
    rw [hL, Real.exp_log (by positivity)]
  have h1 : (D : ℝ) + 1 ≤ Real.exp D := Real.add_one_le_exp _
  have h2 : (2 / (1 - Real.exp (-h))) ^ (2 * D) = Real.exp ((2 * D : ℕ) * L) := by
    rw [hqe, ← Real.exp_nat_mul]
  have h3 : 12 / h ≤ Real.exp |Real.log (12 / h)| := by
    calc
      12 / h = Real.exp (Real.log (12 / h)) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.2 (le_abs_self _)
  have hprod : ((D : ℝ) + 1) * (2 / (1 - Real.exp (-h))) ^ (2 * D) * (12 / h) ≤
      Real.exp D * Real.exp ((2 * D : ℕ) * L) * Real.exp |Real.log (12 / h)| := by
    rw [h2]
    have h12 : 0 < 12 / h := by positivity
    gcongr
  refine (mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le).trans ?_
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  push_cast
  have hA : heatGridConstant h = |Real.log (12 / h)| + 1 + 2 * L + h / 8 := rfl
  have hXA : 4 * heatGridConstant h ≤ h * X := by
    have := (div_le_iff₀ hh).1 hXh
    linarith only [this]
  have habs := abs_nonneg (Real.log (12 / h))
  -- All terms are at most `X · A`, and `4A ≤ hX`.
  have hmul : X * (4 * heatGridConstant h) ≤ X * (h * X) :=
    mul_le_mul_of_nonneg_left hXA (by linarith only [hX1])
  have hD1 : (D : ℝ) * (1 + 2 * L) ≤ X * (1 + 2 * L) :=
    mul_le_mul_of_nonneg_right hD (by linarith only [hL0])
  have hrest : |Real.log (12 / h)| + h / 8 ≤ X * (|Real.log (12 / h)| + h / 8) :=
    le_mul_of_one_le_left (by positivity) hX1
  rw [hA] at hmul
  nlinarith only [hmul, hD1, hrest]

/-- The Gaussian value attached to a zero copy. -/
def heatAtom (h : ℝ) (q : XiZeroCopy) : ℝ := Real.exp (-h * absOrdinate q ^ 2)

/-- An atom of the sampled heat form. -/
def formTerm (h : ℝ) (K : ℕ) (p : ℝ[X]) (q : XiZeroCopy) : ℂ :=
  xiGaussianHeatTerm h q * evalRealPolynomial (X ^ K * p) (xiGaussianHeatTerm h q) ^ 2

theorem formTerm_re_of_im_eq_zero (h : ℝ) (K : ℕ) (p : ℝ[X]) {q : XiZeroCopy}
    (hq : (xiSpectralPoint q).im = 0) :
    (formTerm h K p q).re = heatAtom h q ^ (2 * K + 1) * p.eval (heatAtom h q) ^ 2 := by
  rw [formTerm, heatTerm_of_im_eq_zero h hq]
  exact form_term_of_real

theorem summable_norm_heatTerm {h : ℝ} (hh : 0 < h) :
    Summable fun q : XiZeroCopy => ‖xiGaussianHeatTerm h q‖ := by
  have := summable_norm_xiGaussianHeatTermC (τ := ((h : ℝ) : ℂ)) (by simpa using hh)
  simpa only [xiGaussianHeatTermC, xiGaussianHeatTerm] using this

theorem summable_formTerm {h : ℝ} (hh : 0 < h) (K : ℕ) (p : ℝ[X]) : Summable (formTerm h K p) := by
  refine Summable.of_norm_bounded
    ((summable_norm_heatTerm hh).mul_right
      (evalRealPolynomialNormBound (X ^ K * p) (Real.exp (h / 4)) ^ 2)) fun q => ?_
  have hbd : ‖xiGaussianHeatTerm h q‖ ≤ Real.exp (h / 4) := by
    refine (norm_heatTerm_le hh q).trans (Real.exp_le_exp.2 ?_)
    have : 0 ≤ h * absOrdinate q ^ 2 := by positivity
    linarith only [this]
  rw [formTerm, norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_evalRealPolynomial_le _ hbd) 2) (norm_nonneg _)

/-- Sizes of the heat atoms above height `Y`. -/
theorem heat_tail_sizes {h Y : ℝ} (hh : 0 < h) (hY : 0 < Y) {q : XiZeroCopy} (hq : Y < absOrdinate q) :
    ‖xiGaussianHeatTerm h q‖ ≤ Real.exp (h / 4 - h * Y ^ 2) ∧
      ‖xiGaussianHeatTerm h q‖ ≤
        Real.exp (h / 8 - h * Y ^ 2 / 2) * ‖xiGaussianHeatTerm (h / 2) q‖ := by
  have hh2 : 0 < h / 2 := by positivity
  have hsq : Y ^ 2 ≤ absOrdinate q ^ 2 := pow_le_pow_left₀ hY.le hq.le 2
  constructor
  · refine (norm_heatTerm_le hh q).trans (Real.exp_le_exp.2 ?_)
    nlinarith only [hh, hsq]
  · have hhalf : ‖xiGaussianHeatTerm h q‖ =
        ‖xiGaussianHeatTerm (h / 2) q‖ * ‖xiGaussianHeatTerm (h / 2) q‖ := by
      rw [norm_heatTerm, norm_heatTerm, ← Real.exp_add]
      congr 1
      ring
    rw [hhalf]
    refine mul_le_mul_of_nonneg_right ((norm_heatTerm_le hh2 q).trans (Real.exp_le_exp.2 ?_))
      (norm_nonneg _)
    nlinarith only [hh, hsq]

/-- Bound for a tail atom from the size of the atom and the Lagrange bound. -/
theorem tail_real_bound {a ε E v n C : ℝ} (ha : 0 ≤ a) (h1 : a ≤ ε) (h2 : a ≤ E * v) (hn : 0 ≤ n) (hnC : n ≤ C)
    (K : ℕ) : a ^ (2 * K + 1) * n ≤ ε ^ (2 * K) * E * C * v := by
  have hpow : a ^ (2 * K) ≤ ε ^ (2 * K) := pow_le_pow_left₀ ha h1 _
  have hε : 0 ≤ ε ^ (2 * K) := pow_nonneg (ha.trans h1) _
  have hEv : 0 ≤ E * v := ha.trans h2
  calc
    a ^ (2 * K + 1) * n = a ^ (2 * K) * a * n := by rw [pow_succ]
    _ ≤ ε ^ (2 * K) * (E * v) * C := by
      apply mul_le_mul _ hnC hn (mul_nonneg hε hEv)
      exact mul_le_mul hpow h2 ha hε
    _ = _ := by ring

/-- **Comparison of the sum with its atoms.** Verified atoms are nonnegative, the nodes are at least `ℓ^(2K+1) p²`,
and tail atoms are at least `-c |λ(h/2)|`. -/
theorem heat_form_re_ge {h Y ℓ c : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (hc0 : 0 ≤ c) (hRH : RHVerifiedThrough Y) (K : ℕ)
    (p : ℝ[X]) (s : Finset XiZeroCopy) (hs : ∀ q ∈ s, ℓ ≤ heatAtom h q ∧ absOrdinate q ≤ Y)
    (htail : ∀ q, Y < absOrdinate q → -(c * ‖xiGaussianHeatTerm (h / 2) q‖) ≤ (formTerm h K p q).re) :
    ℓ ^ (2 * K + 1) * ∑ q ∈ s, p.eval (heatAtom h q) ^ 2 - c * (12 / h) ≤
      (∑' q, formTerm h K p q).re := by
  classical
  have hh2 : 0 < h / 2 := by positivity
  let u : XiZeroCopy → ℝ := fun q => if q ∈ s then ℓ ^ (2 * K + 1) * p.eval (heatAtom h q) ^ 2 else 0
  have hterm (q : XiZeroCopy) : u q - c * ‖xiGaussianHeatTerm (h / 2) q‖ ≤ (formTerm h K p q).re := by
    have hnn : 0 ≤ c * ‖xiGaussianHeatTerm (h / 2) q‖ := mul_nonneg hc0 (norm_nonneg _)
    by_cases hqs : q ∈ s
    · have hval := formTerm_re_of_im_eq_zero h K p (im_xiSpectralPoint_eq_zero hRH q (hs q hqs).2)
      have hu : u q = ℓ ^ (2 * K + 1) * p.eval (heatAtom h q) ^ 2 := if_pos hqs
      have hpow : ℓ ^ (2 * K + 1) ≤ heatAtom h q ^ (2 * K + 1) :=
        pow_le_pow_left₀ hℓ.le (hs q hqs).1 _
      have := mul_le_mul_of_nonneg_right hpow (sq_nonneg (p.eval (heatAtom h q)))
      rw [hval, hu]
      linarith only [this, hnn]
    · have hu : u q = 0 := if_neg hqs
      rw [hu, zero_sub]
      by_cases hqY : absOrdinate q ≤ Y
      · have hval := formTerm_re_of_im_eq_zero h K p (im_xiSpectralPoint_eq_zero hRH q hqY)
        have : 0 ≤ heatAtom h q ^ (2 * K + 1) * p.eval (heatAtom h q) ^ 2 :=
          mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (sq_nonneg _)
        rw [hval]
        linarith only [this, hnn]
      · exact htail q (not_le.1 hqY)
  have hsumv := (summable_norm_heatTerm hh2).mul_left c
  have hsumg := summable_formTerm hh K p
  have hsumu : Summable u := summable_of_finite_support (s.finite_toSet.subset fun q hq => by
    by_contra hc
    exact hq (if_neg hc))
  have hsumre : Summable fun q => (formTerm h K p q).re := (Complex.hasSum_re hsumg.hasSum).summable
  rw [Complex.re_tsum hsumg]
  have hcmp := Summable.tsum_le_tsum hterm (hsumu.sub hsumv) hsumre
  rw [hsumu.tsum_sub hsumv, tsum_mul_left] at hcmp
  have hutsum : ∑' q, u q = ℓ ^ (2 * K + 1) * ∑ q ∈ s, p.eval (heatAtom h q) ^ 2 := by
    rw [tsum_eq_sum (s := s) (fun q hq => if_neg hq), Finset.mul_sum]
    exact Finset.sum_congr rfl fun q hq => if_pos hq
  rw [hutsum] at hcmp
  have hmass : c * ∑' q, ‖xiGaussianHeatTerm (h / 2) q‖ ≤ c * (12 / h) := by
    refine mul_le_mul_of_nonneg_left ((tsum_norm_xiGaussianHeatTerm_le_six_div hh2).trans (le_of_eq ?_)) hc0
    field_simp
    norm_num
  linarith only [hcmp, hmass]

/-- Abstract form of the final inequality. -/
theorem final_numeric {ℓ ε E B S t : ℝ} (hε : 0 ≤ ε) (hεℓ : ε ≤ ℓ) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hS : 0 ≤ S) (ht : 0 ≤ t) (hnum : E * (B * t) ≤ ℓ) (K : ℕ) :
    ε ^ (2 * K) * E * (B * S) * t ≤ ℓ ^ (2 * K + 1) * S := by
  have h1 : ε ^ (2 * K) ≤ ℓ ^ (2 * K) := pow_le_pow_left₀ hε hεℓ _
  have h2 : ε ^ (2 * K) * E * (B * S) * t = ε ^ (2 * K) * ((E * (B * t)) * S) := by ring
  rw [h2, pow_succ, mul_assoc (ℓ ^ (2 * K)) ℓ S]
  have hnn : 0 ≤ E * (B * t) * S := by positivity
  have hℓ : 0 ≤ ℓ := hε.trans hεℓ
  exact mul_le_mul h1 (mul_le_mul_of_nonneg_right hnum hS) hnn (by positivity)

/-- The heat form is nonnegative as soon as `deg p + 1` separated verified nodes below `Y/2` are given. -/
theorem heat_form_nonneg_of_nodes {h Y : ℝ} (hh : 0 < h) (hY : 1440 ≤ Y)
    (hYh : 4 * heatGridConstant h / h ≤ Y) (hRH : RHVerifiedThrough Y) (K : ℕ) {p : ℝ[X]}
    (hD : (p.natDegree : ℝ) ≤ Y) {s : Finset XiZeroCopy} (hs : s.card = p.natDegree + 1)
    (hband : ∀ q ∈ s, 1 ≤ absOrdinate q ∧ absOrdinate q ≤ Y / 2)
    (hsep : ∀ q ∈ s, ∀ q' ∈ s, q ≠ q' → 1 ≤ |absOrdinate q - absOrdinate q'|) :
    0 ≤ (∑' q, formTerm h K p q).re := by
  have hY0 : 0 < Y := by linarith only [hY]
  have hκ : 0 < 1 - Real.exp (-h) := by linarith only [exp_neg_lt_one hh]
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = Real.exp (-h * (Y / 2) ^ 2) := ⟨_, rfl⟩
  have hℓ : 0 < ℓ := by rw [hℓdef]; exact Real.exp_pos _
  have hvℓ : ∀ q ∈ s, ℓ ≤ heatAtom h q := fun q hq => by
    rw [hℓdef]
    apply Real.exp_le_exp.2
    have hsq : absOrdinate q ^ 2 ≤ (Y / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hband q hq).2 2
    nlinarith only [hh, hsq]
  have hsepv : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      heatAtom h i * (1 - Real.exp (-h)) ≤ |heatAtom h i - heatAtom h j| := fun i hi j hj hne =>
    exp_mul_le_abs_sub_exp hh (hband i hi).1 (hband j hj).1 (hsep i hi j hj hne)
  obtain ⟨S, hSdef⟩ : ∃ S, S = ∑ q ∈ s, p.eval (heatAtom h q) ^ 2 := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨B, hBdef⟩ : ∃ B, B = ((p.natDegree : ℝ) + 1) * (2 / (1 - Real.exp (-h))) ^ (2 * p.natDegree) :=
    ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hLag : ∀ z : ℂ, ‖z‖ ≤ ℓ → ‖evalRealPolynomial p z‖ ^ 2 ≤ B * S := fun z hz => by
    have h1 := norm_evalRealPolynomial_sq_le_of_separated s (heatAtom h) hκ hℓ hvℓ hsepv p
      (by rw [hs]; omega) hz
    rw [hs] at h1
    push_cast at h1
    rw [hBdef, hSdef]
    simpa only [add_tsub_cancel_right] using h1
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = Real.exp (h / 4 - h * Y ^ 2) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; exact Real.exp_pos _
  obtain ⟨E, hEdef⟩ : ∃ E, E = Real.exp (h / 8 - h * Y ^ 2 / 2) := ⟨_, rfl⟩
  have hE : 0 < E := by rw [hEdef]; exact Real.exp_pos _
  have hεℓ : ε ≤ ℓ := by
    rw [hεdef, hℓdef]
    apply Real.exp_le_exp.2
    have : 1 ≤ Y ^ 2 := by nlinarith only [hY]
    nlinarith only [hh, this]
  have hc0 : 0 ≤ ε ^ (2 * K) * E * (B * S) := by positivity
  have hmain := heat_form_re_ge hh hℓ hc0 hRH K p s
    (fun q hq => ⟨hvℓ q hq, (hband q hq).2.trans (by linarith only [hY0])⟩) (fun q hq => by
      have hsz := heat_tail_sizes hh hY0 hq
      rw [← hεdef, ← hEdef] at hsz
      refine le_trans ?_ (neg_form_term_le (K := K) (p := p) (xiGaussianHeatTerm h q))
      apply neg_le_neg
      exact tail_real_bound (norm_nonneg _) hsz.1 hsz.2 (by positivity)
        (hLag _ (hsz.1.trans hεℓ)) K)
  rw [← hSdef] at hmain
  refine le_trans ?_ hmain
  have hnum : E * (B * (12 / h)) ≤ ℓ := by
    rw [hEdef, hℓdef, hBdef]
    have h1 := heat_numeric hh (by linarith only [hY]) hYh hD
    rw [mul_assoc (((p.natDegree : ℝ) + 1)) _ (12 / h)] at h1
    rw [mul_assoc (((p.natDegree : ℝ) + 1)) _ (12 / h)]
    exact h1
  have hfinal := final_numeric hε.le hεℓ hE.le hB0 hS0 (by positivity : (0 : ℝ) ≤ 12 / h) hnum K
  linarith only [hfinal]

/-- **Heat rung.** If RH holds through `Y ≥ heatGridHeight h` and `4800 (deg p + 1) ≤ Y`, the sampled heat form
of `p²` is nonnegative at every offset. -/
theorem heatGridForm_nonneg_of_rhVerifiedThrough {h Y : ℝ} (hh : 0 < h) (hY : heatGridHeight h ≤ Y)
    (hRH : RHVerifiedThrough Y) (K : ℕ) {p : ℝ[X]} (hp : 4800 * ((p.natDegree : ℝ) + 1) ≤ Y) :
    0 ≤ HTGeometry.momentFunctional (xiHeatGridMoment h K) (p ^ 2) := by
  have hYm : 4 * xiMassHeight (1 / 100) ≤ Y := (le_max_left _ _).trans hY
  have hY2 : max 1440 (4 * heatGridConstant h / h) ≤ Y := (le_max_right _ _).trans hY
  have hY1440 : 1440 ≤ Y := (le_max_left _ _).trans hY2
  have hYh : 4 * heatGridConstant h / h ≤ Y := (le_max_right _ _).trans hY2
  have hd0 : (0 : ℝ) ≤ p.natDegree := Nat.cast_nonneg _
  obtain ⟨s, hs, hsband, hssep⟩ := exists_separated_nodes (T := Y / 4)
    (by linarith only [hYm]) (by linarith only [hY1440]) (n := p.natDegree + 1)
    (by push_cast; linarith only [hp])
  rw [momentFunctional_xiHeatGridMoment_square hh]
  exact heat_form_nonneg_of_nodes hh hY1440 hYh hRH K (by linarith only [hp, hd0]) hs
    (fun q hq => by
      have hb := hsband q hq
      exact ⟨by linarith only [hb.1, hY1440], by linarith only [hb.2]⟩) hssep

/-- **Source rung.** If RH holds through `Y ≥ heatGridHeight h`, then on the pole hyperplane the literal
archimedean-minus-prime source form of `p²` is nonnegative at every offset, for `4800 (deg p + 1) ≤ Y`. -/
theorem primeArchHeatGridForm_nonneg_of_rhVerifiedThrough {h Y : ℝ} (hh : 0 < h) (hY : heatGridHeight h ≤ Y)
    (hRH : RHVerifiedThrough Y) (K : ℕ) {p : ℝ[X]} (hp : 4800 * ((p.natDegree : ℝ) + 1) ≤ Y)
    (hpole : p.eval (xiHeatGridPole h) = 0) :
    0 ≤ HTGeometry.momentFunctional (xiPrimeArchHeatGridMoment h K) (p ^ 2) := by
  rw [momentFunctional_xiPrimeArchHeatGridMoment_square_of_pole_zero hh K p hpole]
  exact heatGridForm_nonneg_of_rhVerifiedThrough hh hY hRH K hp

end

end GaloisForLFunctions.VerifiedHeightRungs

#print axioms GaloisForLFunctions.VerifiedHeightRungs.exists_separated_nodes
#print axioms GaloisForLFunctions.VerifiedHeightRungs.heatGridForm_nonneg_of_rhVerifiedThrough
#print axioms GaloisForLFunctions.VerifiedHeightRungs.primeArchHeatGridForm_nonneg_of_rhVerifiedThrough
