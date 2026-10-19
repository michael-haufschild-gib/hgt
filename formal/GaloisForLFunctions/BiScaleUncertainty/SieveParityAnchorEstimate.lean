import GaloisForLFunctions.BiScaleUncertainty.SieveThresholdRounding
import GaloisForLFunctions.BiScaleUncertainty.SieveHighestDyadicCoordinate

/-! Positive parity anchors and rounded sign-sensitive products. -/

noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
set_option autoImplicit false

private theorem ordered_anchor_gaps (u v : ℝ) (hv : 1 ≤ v) (hvu : v ≤ u) :
    u-v ≤ u^6-v^6 ∧ u^4-v^4 ≤ u^6-v^6 := by
  have hu : 1 ≤ u := hv.trans hvu
  have hv0 : 0 ≤ v := by linarith
  have hu0 : 0 ≤ u := by linarith
  have h2 : v^2 ≤ u^2 := pow_le_pow_left₀ hv0 hvu 2
  have hu2 : 1 ≤ u^2 := one_le_pow₀ hu
  have hv2 : 1 ≤ v^2 := one_le_pow₀ hv
  have hu4 : u^2 ≤ u^4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hu2) (sq_nonneg u)]
  have hv4 : v^2 ≤ v^4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hv2) (sq_nonneg v)]
  have hbase : u-v ≤ u^2-v^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hvu) (show 0 ≤ u+v-1 by linarith)]
  have hlarge : u^2-v^2 ≤ u^6-v^6 := by
    have hp := mul_nonneg (sub_nonneg.mpr h2)
      (show 0 ≤ u^4+u^2*v^2+v^4-1 by
        nlinarith [mul_nonneg (sq_nonneg u) (sq_nonneg v)])
    nlinarith only [hp]
  refine ⟨hbase.trans hlarge, ?_⟩
  have hp := mul_nonneg (sub_nonneg.mpr h2)
    (show 0 ≤ u^4+u^2*v^2+v^4-u^2-v^2 by
      nlinarith [mul_nonneg (sq_nonneg u) (sq_nonneg v)])
  nlinarith only [hp]

/-- A positive parity anchor transfers sixth-power error to first and fourth powers. -/
theorem anchor_gaps (A B ε : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B)
    (h : |A^6-B^6| ≤ ε) : |A-B| ≤ ε ∧ |A^4-B^4| ≤ ε := by
  have step (u v : ℝ) (hv : 1 ≤ v) (hvu : v ≤ u)
      (he : u^6-v^6 ≤ ε) : |u-v| ≤ ε ∧ |u^4-v^4| ≤ ε := by
    have hh := ordered_anchor_gaps u v hv hvu
    have hv0 : 0 ≤ v := by linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hvu),
      abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hv0 hvu 4))]
    exact ⟨hh.1.trans he, hh.2.trans he⟩
  rcases le_total B A with hBA | hAB
  · exact step A B hB hBA ((le_abs_self _).trans h)
  · have hh := step B A hA hAB (by
      have := (neg_le_abs (A^6-B^6)).trans h
      linarith)
    simpa only [abs_sub_comm] using hh

/-- Mixed sixth products recover every magnitude on a bounded parity neighborhood. -/
theorem anchored_magnitude (a b A B δ : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hb : |b| ≤ 3) (hδ : 0 ≤ δ)
    (h6 : |A^6-B^6| ≤ δ^2) (hm : |a^2*A^4-b^2*B^4| ≤ δ^2) :
    |abs a-abs b| ≤ 4*δ := by
  have hg := (anchor_gaps A B (δ^2) hA hB h6).2
  have hA4 : 1 ≤ A^4 := one_le_pow₀ hA
  have hb2 : b^2 ≤ 9 := by nlinarith [sq_abs b, abs_nonneg b]
  have ht : |a^2-b^2| * A^4 ≤ 10*δ^2 := by
    calc
      _ = |(a^2-b^2)*A^4| := by
        rw [abs_mul, abs_of_nonneg (show 0 ≤ A^4 by positivity)]
      _ = |(a^2*A^4-b^2*B^4) + b^2*(B^4-A^4)| := by
        congr 1
        ring
      _ ≤ |a^2*A^4-b^2*B^4| + |b^2*(B^4-A^4)| := abs_add_le _ _
      _ ≤ δ^2 + 9*δ^2 := by
        apply add_le_add hm
        rw [abs_mul, abs_of_nonneg (sq_nonneg b), abs_sub_comm]
        exact mul_le_mul hb2 hg (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hs : |a^2-b^2| ≤ 10*δ^2 := by
    nlinarith [mul_nonneg (abs_nonneg (a^2-b^2)) (sub_nonneg.mpr hA4)]
  have hroot : (|a|-|b|)^2 ≤ |a^2-b^2| := by
    have ha0 := abs_nonneg a
    have hb0 := abs_nonneg b
    rcases le_total |a| |b| with hab | hba
    · have hp := mul_nonneg ha0 (sub_nonneg.mpr hab)
      nlinarith [sq_abs a, sq_abs b, neg_le_abs (a^2-b^2)]
    · have hp := mul_nonneg hb0 (sub_nonneg.mpr hba)
      nlinarith [sq_abs a, sq_abs b, le_abs_self (a^2-b^2)]
  have hab0 := abs_nonneg (|a|-|b|)
  nlinarith [sq_abs (|a|-|b|)]

/-- The constant coordinate has a linear readout once parity is bounded away from zero. -/
theorem anchored_linear (a b A B ε : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hb : |b| ≤ 3)
    (h6 : |A^6-B^6| ≤ ε) (hm : |a*A^4-b*B^4| ≤ ε) :
    |a-b| ≤ 4*ε := by
  have hg := (anchor_gaps A B ε hA hB h6).2
  have hA4 : 1 ≤ A^4 := one_le_pow₀ hA
  have ht : |a-b| * A^4 ≤ 4*ε := by
    calc
      _ = |(a-b)*A^4| := by
        rw [abs_mul, abs_of_nonneg (show 0 ≤ A^4 by positivity)]
      _ = |(a*A^4-b*B^4) + b*(B^4-A^4)| := by
        congr 1
        ring
      _ ≤ |a*A^4-b*B^4| + |b*(B^4-A^4)| := abs_add_le _ _
      _ ≤ ε + 3*ε := by
        apply add_le_add hm
        rw [abs_mul, abs_sub_comm]
        exact mul_le_mul hb hg (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  nlinarith [mul_nonneg (abs_nonneg (a-b)) (sub_nonneg.mpr hA4)]

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
open ValuationPhase
set_option autoImplicit false
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- Opposite pairs compare every squared coordinate against a common fourth-power anchor. -/
theorem anchored_square_error (N : ℕ) (c e : ℕ → ℝ) (ε : ℝ)
    (h6 : ∀ v : Fin 6 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ ε)
    {q u : ℕ} (hq : q ∈ Icc 1 N) (hu : u ∈ Icc 1 N) :
    |selbergMultiplesCoord N c q^2*selbergMultiplesCoord N c u^4 -
      selbergMultiplesCoord N e q^2*selbergMultiplesCoord N e u^4| ≤ ε := by
  let r : ZMod N.factorial := (N.factorial/q : ℕ)
  let s : ZMod N.factorial := (N.factorial/u : ℕ)
  have hr : addOrderOf r = q := frequency_order hq
  have hs : addOrderOf s = u := frequency_order hu
  have hh := resonant_product_error N c e 6 ε h6 ![r,-r,s,-s,s,-s]
    (by simp [Fin.sum_univ_succ])
  simpa [Fin.prod_univ_succ, addOrderOf_neg, hr, hs, pow_succ, mul_assoc] using hh

/-- A zero frequency gives a linear constant-coordinate readout. -/
theorem anchored_constant_error (N : ℕ) (c e : ℕ → ℝ) (ε : ℝ)
    (h5 : ∀ v : Fin 5 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ ε)
    {u : ℕ} (hu : u ∈ Icc 1 N) :
    |selbergMultiplesCoord N c 1*selbergMultiplesCoord N c u^4 -
      selbergMultiplesCoord N e 1*selbergMultiplesCoord N e u^4| ≤ ε := by
  let s : ZMod N.factorial := (N.factorial/u : ℕ)
  have hs : addOrderOf s = u := frequency_order hu
  have hh := resonant_product_error N c e 5 ε h5 ![0,s,-s,s,-s]
    (by simp [Fin.sum_univ_succ])
  simpa [Fin.prod_univ_succ, addOrderOf_neg, hs, pow_succ, mul_assoc] using hh

/-- Existing valuation triples provide a noisy same-block product at an arbitrary cutoff. -/
theorem same_depth_product_error (N : ℕ) (c e : ℕ → ℝ) (ε : ℝ)
    (h6 : ∀ v : Fin 6 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ ε)
    {d u : ℕ} (hd : d ∈ Icc 1 N) (hu : u ∈ Icc 1 N)
    (hdu : d.factorization 2 = u.factorization 2) :
    |(selbergMultiplesCoord N c d*selbergMultiplesCoord N c u)^3 -
      (selbergMultiplesCoord N e d*selbergMultiplesCoord N e u)^3| ≤ ε := by
  obtain ⟨p, hp⟩ := order_odd_decomposition (mem_Icc.mp hd).1
  obtain ⟨q, hq⟩ := order_odd_decomposition (mem_Icc.mp hu).1
  let k := d.factorization 2
  have hlow : 2^k*(2*p+1) = d := hp.symm
  have hupp : 2^k*(2*q+1) = u := by
    dsimp [k]
    rw [hdu]
    exact hq.symm
  have hpodd : Odd (2*p+1) := ⟨p, by omega⟩
  have hqodd : Odd (2*q+1) := ⟨q, by omega⟩
  have hd' : 2^k*(2*p+1) ∈ Icc 1 N := hlow ▸ hd
  have hu' : 2^k*(2*q+1) ∈ Icc 1 N := hupp ▸ hu
  have hh := resonant_product_error N c e 6 ε h6
    (valuationSix N k (2*p+1) (2*q+1))
    (valuationSix_sum hpodd hqodd hd' hu')
  have hprod (v : ℕ → ℝ) :
      (∏ i, v (addOrderOf (valuationSix N k (2*p+1) (2*q+1) i))) =
        (v d*v u)^3 := by
    have he := valuationSix_order_product hpodd hqodd hd' hu' (fun j => (v j : ℂ))
    rw [hlow, hupp] at he
    exact_mod_cast he
  simpa only [hprod] using hh

/-- The only higher-depth interaction below twelve has perturbation degree three. -/
theorem four_eight_error (N : ℕ) (hN : 8 ≤ N) (c e : ℕ → ℝ) (ε : ℝ)
    (h5 : ∀ v : Fin 5 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ ε) :
    |selbergMultiplesCoord N c 4*selbergMultiplesCoord N c 8^2*
        selbergMultiplesCoord N c 2^2 -
      selbergMultiplesCoord N e 4*selbergMultiplesCoord N e 8^2*
        selbergMultiplesCoord N e 2^2| ≤ ε := by
  let r : ZMod N.factorial := (N.factorial/4 : ℕ)
  let s : ZMod N.factorial := (N.factorial/8 : ℕ)
  let p : ZMod N.factorial := (N.factorial/2 : ℕ)
  have hr : addOrderOf r = 4 := frequency_order (by simp; omega)
  have hs : addOrderOf s = 8 := frequency_order (by simp; omega)
  have hp : addOrderOf p = 2 := frequency_order (by simp; omega)
  have hdiv : 8 ∣ N.factorial := Nat.dvd_factorial (by omega) hN
  obtain ⟨k, hk⟩ := hdiv
  have hn : N.factorial/4 = 2*(N.factorial/8) := by omega
  have hrs : r = 2*s := by
    dsimp [r, s]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      congrArg (fun j : ℕ => (j : ZMod N.factorial)) hn
  have hh := resonant_product_error N c e 5 ε h5 ![-r,s,s,p,-p]
    (by simp [Fin.sum_univ_succ, hrs]; ring)
  simpa [Fin.prod_univ_succ, addOrderOf_neg, hr, hs, hp, pow_succ, mul_assoc] using hh

/-- Orders four and twelve are the only repeated higher-depth block below twenty. -/
theorem four_twelve_error (N : ℕ) (hN : 12 ≤ N) (c e : ℕ → ℝ) (ε : ℝ)
    (h6 : ∀ v : Fin 6 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ ε) :
    |selbergMultiplesCoord N c 12^3*selbergMultiplesCoord N c 4*
        selbergMultiplesCoord N c 2^2 -
      selbergMultiplesCoord N e 12^3*selbergMultiplesCoord N e 4*
        selbergMultiplesCoord N e 2^2| ≤ ε := by
  let r : ZMod N.factorial := (N.factorial/4 : ℕ)
  let s : ZMod N.factorial := (N.factorial/12 : ℕ)
  let p : ZMod N.factorial := (N.factorial/2 : ℕ)
  have hr : addOrderOf r = 4 := frequency_order (by simp; omega)
  have hs : addOrderOf s = 12 := frequency_order (by simp; omega)
  have hp : addOrderOf p = 2 := frequency_order (by simp; omega)
  have hdiv : 12 ∣ N.factorial := Nat.dvd_factorial (by omega) hN
  obtain ⟨k, hk⟩ := hdiv
  have hn : N.factorial/4 = 3*(N.factorial/12) := by omega
  have hrs : r = 3*s := by
    dsimp [r, s]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      congrArg (fun j : ℕ => (j : ZMod N.factorial)) hn
  have hh := resonant_product_error N c e 6 ε h6 ![s,s,s,-r,p,-p]
    (by simp [Fin.sum_univ_succ, hrs]; ring)
  simpa [Fin.prod_univ_succ, addOrderOf_neg, hr, hs, hp, pow_succ, mul_assoc] using hh

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
set_option autoImplicit false

private theorem close_product_sign (a b : ℝ) (h : |a-b| < |a|) : 0 < a*b := by
  have hab := abs_lt.mp h
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha] at hab
    have ha' : 0 < a := lt_of_le_of_lt (abs_nonneg _) (by simpa [abs_of_nonneg ha] using h)
    have hb : 0 < b := by linarith
    exact mul_pos ha' hb
  · have ha' : a < 0 := lt_of_not_ge ha
    rw [abs_of_neg ha'] at hab
    have hb : b < 0 := by linarith
    exact mul_pos_of_neg_of_neg ha' hb

theorem rounded_abs (τ a b : ℝ) : |Threshold.target τ a b| = |Threshold.source τ a| := by
  unfold Threshold.target Threshold.source
  split_ifs <;> simp

theorem rounded_of_positive (τ a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Threshold.target τ a b = Threshold.source τ a := by
  simp [Threshold.target, Threshold.source, hb, abs_of_nonneg ha]

/-- Retained products need only a strict relative error, allowing fixed anchor factors. -/
theorem rounded_products {ι : Type*} [Fintype ι]
    (τ : ℝ) (hτ : 0 ≤ τ) (a b : ι → ℝ)
    (hmag : ∀ i, abs (|a i|-|b i|) ≤ τ)
    (herr : (∀ i, τ < |a i|) → |(∏ i, a i)-(∏ i, b i)| < |∏ i, a i|) :
    (∏ i, Threshold.source τ (a i)) = ∏ i, Threshold.target τ (a i) (b i) := by
  classical
  by_cases hz : ∃ i, ¬τ < |a i|
  · obtain ⟨i, hi⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ i)
        (show Threshold.source τ (a i) = 0 by simp [Threshold.source, hi]),
      Finset.prod_eq_zero (Finset.mem_univ i)
        (show Threshold.target τ (a i) (b i) = 0 by simp [Threshold.target, hi])]
  · have ha : ∀ i, τ < |a i| := fun i => by by_contra hi; exact hz ⟨i, hi⟩
    have hab : 0 < (∏ i, a i)*(∏ i, b i) := close_product_sign _ _ (herr ha)
    have htb : 0 < (∏ i, Threshold.target τ (a i) (b i))*(∏ i, b i) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_pos
      intro i _
      have hgap := (abs_le.mp (hmag i)).2
      have hbabs : 0 < |b i| := by linarith [ha i]
      have haabs : 0 < |a i| := lt_of_le_of_lt hτ (ha i)
      by_cases hb : 0 ≤ b i
      · have hbpos : 0 < b i := by rwa [abs_of_nonneg hb] at hbabs
        simpa [Threshold.target, ha i, hb] using mul_pos haabs hbpos
      · have hbneg : b i < 0 := lt_of_not_ge hb
        simpa [Threshold.target, ha i, hb] using
          mul_pos_of_neg_of_neg (neg_neg_of_pos haabs) hbneg
    have habs : |∏ i, Threshold.target τ (a i) (b i)| = |∏ i, a i| := by
      rw [Finset.abs_prod, Finset.abs_prod]
      apply Finset.prod_congr rfl
      intro i _
      simp only [Threshold.target, if_pos (ha i)]
      split_ifs <;> simp
    have heq : (∏ i, Threshold.target τ (a i) (b i)) = ∏ i, a i := by
      rcases abs_eq_abs.mp habs with he | he
      · exact he
      · rw [he] at htb
        nlinarith only [hab, htb]
    simpa [Threshold.source, ha] using heq.symm

/-- Only perturbation factors enter the noise degree; the anchor contributes a unit lower bound. -/
theorem large_monomial (δ a x A : ℝ) (r s t d : ℕ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hr : r ≠ 0) (hdegree : r+s ≤ d)
    (ha : δ < |a|) (hx : δ < |x|) (hA : 1 ≤ |A|) :
    δ^d < |a^r*x^s*A^t| := by
  have hxpos : 0 < |x| := hδ.trans_lt hx
  have hsmall : δ^(r+s) < |a|^r*|x|^s := by
    rw [pow_add]
    exact mul_lt_mul_of_nonneg_of_pos
      (pow_lt_pow_left₀ ha hδ hr) (pow_le_pow_left₀ hδ hx.le s)
      (pow_nonneg hδ r) (pow_pos hxpos s)
  have hanchor : 1 ≤ |A|^t := one_le_pow₀ hA
  have hlarge : |a|^r*|x|^s ≤ |a|^r*|x|^s*|A|^t := by
    nlinarith [mul_nonneg (pow_nonneg (abs_nonneg a) r) (pow_nonneg (abs_nonneg x) s)]
  rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_pow]
  exact (pow_le_pow_of_le_one hδ hδ1 hdegree).trans_lt (hsmall.trans_le hlarge)

/-- A noisy anchored monomial becomes an exact identity on the rounded profiles. -/
theorem rounded_monomial (δ a b x y A B : ℝ) (r s t d : ℕ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hr : r ≠ 0) (hdegree : r+s ≤ d)
    (hA : 1 ≤ |A|)
    (ha : abs (|a|-|b|) ≤ 4*δ) (hx : abs (|x|-|y|) ≤ 4*δ)
    (hanchor : abs (|A|-|B|) ≤ 4*δ)
    (herr : |a^r*x^s*A^t-b^r*y^s*B^t| ≤ δ^d) :
    (Threshold.source (4*δ) a)^r*(Threshold.source (4*δ) x)^s*
        (Threshold.source (4*δ) A)^t =
      (Threshold.target (4*δ) a b)^r*(Threshold.target (4*δ) x y)^s*
        (Threshold.target (4*δ) A B)^t := by
  let f : (Fin r ⊕ (Fin s ⊕ Fin t)) → ℝ :=
    Sum.elim (fun _ => a) (Sum.elim (fun _ => x) (fun _ => A))
  let g : (Fin r ⊕ (Fin s ⊕ Fin t)) → ℝ :=
    Sum.elim (fun _ => b) (Sum.elim (fun _ => y) (fun _ => B))
  have hmag : ∀ i, abs (|f i|-|g i|) ≤ 4*δ := by
    intro i
    rcases i with i | i
    · exact ha
    · rcases i with i | i
      · exact hx
      · exact hanchor
  have hclose (hret : ∀ i, 4*δ < |f i|) :
      |(∏ i, f i)-(∏ i, g i)| < |∏ i, f i| := by
    have hra := hret (Sum.inl ⟨0, Nat.pos_of_ne_zero hr⟩)
    change 4*δ < |a| at hra
    have hda : δ < |a| := by linarith
    have hlarge : δ^d < |a^r*x^s*A^t| := by
      by_cases hs : s = 0
      · subst s
        simpa only [pow_zero, mul_one] using
          large_monomial δ a a A r 0 t d hδ hδ1 hr hdegree hda hda hA
      · have hrx := hret (Sum.inr (Sum.inl ⟨0, Nat.pos_of_ne_zero hs⟩))
        change 4*δ < |x| at hrx
        have hdx : δ < |x| := by linarith
        exact large_monomial δ a x A r s t d hδ hδ1 hr hdegree hda hdx hA
    have hh := herr.trans_lt hlarge
    simpa [f, g, Fintype.prod_sum_type, mul_assoc] using hh
  have hh := rounded_products (4*δ) (by linarith) f g hmag hclose
  simpa [f, g, Fintype.prod_sum_type, mul_assoc] using hh

theorem rounded_anchor_cube (δ a b A B : ℝ) (k d : ℕ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hsmall : 4*δ < 1) (hdegree : 3 ≤ d)
    (hA : 1 ≤ A) (hB : 0 ≤ B)
    (ha : abs (|a|-|b|) ≤ 4*δ) (hanchor : abs (|A|-|B|) ≤ 4*δ)
    (herr : |a^3*A^k-b^3*B^k| ≤ δ^d) :
    Threshold.source (4*δ) a = Threshold.target (4*δ) a b := by
  have hA0 : 0 ≤ A := by linarith
  have hAa : 1 ≤ |A| := by rwa [abs_of_nonneg hA0]
  have hh := rounded_monomial δ a b a b A B 3 0 k d hδ hδ1 (by decide)
    (by simpa using hdegree) hAa ha ha hanchor (by simpa using herr)
  simp only [pow_zero, mul_one, rounded_of_positive (4*δ) A B hA0 hB] at hh
  have hret : 4*δ < |A| := hsmall.trans_le hAa
  have hne : Threshold.source (4*δ) A ≠ 0 := by
    rw [Threshold.source, if_pos hret]
    linarith
  exact (show Odd (3 : ℕ) from ⟨1, rfl⟩).pow_injective
    (mul_right_cancel₀ (pow_ne_zero k hne) hh)

/-- A retained square factor fixes the sign of every odd-power factor. -/
theorem rounded_orient (δ a b x y A B : ℝ) (r t d : ℕ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hsmall : 4*δ < 1)
    (hr : Odd r) (hdegree : r+2 ≤ d) (hretx : 4*δ < |x|)
    (hA : 1 ≤ A) (hB : 0 ≤ B)
    (ha : abs (|a|-|b|) ≤ 4*δ) (hx : abs (|x|-|y|) ≤ 4*δ)
    (hanchor : abs (|A|-|B|) ≤ 4*δ)
    (herr : |a^r*x^2*A^t-b^r*y^2*B^t| ≤ δ^d) :
    Threshold.source (4*δ) a = Threshold.target (4*δ) a b := by
  have hA0 : 0 ≤ A := by linarith
  have hAa : 1 ≤ |A| := by rwa [abs_of_nonneg hA0]
  have hr0 : r ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := hr
    omega
  have hh := rounded_monomial δ a b x y A B r 2 t d hδ hδ1 hr0
    hdegree hAa ha hx hanchor herr
  have hxsq : (Threshold.target (4*δ) x y)^2 = (Threshold.source (4*δ) x)^2 := by
    have he := congrArg (fun u : ℝ => u^2) (rounded_abs (4*δ) x y)
    simpa only [sq_abs] using he
  rw [hxsq, rounded_of_positive (4*δ) A B hA0 hB] at hh
  have hAne : Threshold.source (4*δ) A ≠ 0 := by
    rw [Threshold.source, if_pos (hsmall.trans_le hAa)]
    linarith
  have hxne : Threshold.source (4*δ) x ≠ 0 := by
    rw [Threshold.source, if_pos hretx]
    intro hx0
    rw [hx0, abs_zero] at hretx
    linarith
  exact hr.pow_injective (mul_right_cancel₀ (pow_ne_zero 2 hxne)
    (mul_right_cancel₀ (pow_ne_zero t hAne) hh))

/-- The cubic-linear readout fixes the relative sign of a same-depth pair. -/
theorem rounded_pair (δ a b x y A B : ℝ) (d : ℕ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hsmall : 4*δ < 1) (hdegree : 4 ≤ d)
    (hA : 1 ≤ A) (hB : 0 ≤ B)
    (ha : abs (|a|-|b|) ≤ 4*δ) (hx : abs (|x|-|y|) ≤ 4*δ)
    (hanchor : abs (|A|-|B|) ≤ 4*δ)
    (herr : |a^3*x*A^2-b^3*y*B^2| ≤ δ^d) :
    Threshold.source (4*δ) a*Threshold.source (4*δ) x =
      Threshold.target (4*δ) a b*Threshold.target (4*δ) x y := by
  have hA0 : 0 ≤ A := by linarith
  have hAa : 1 ≤ |A| := by rwa [abs_of_nonneg hA0]
  have hh := rounded_monomial δ a b x y A B 3 1 2 d hδ hδ1 (by decide)
    hdegree hAa ha hx hanchor (by simpa using herr)
  simp only [pow_one, rounded_of_positive (4*δ) A B hA0 hB] at hh
  have hAne : Threshold.source (4*δ) A ≠ 0 := by
    rw [Threshold.source, if_pos (hsmall.trans_le hAa)]
    linarith
  have hc := mul_right_cancel₀ (pow_ne_zero 2 hAne) hh
  have hsq : (Threshold.target (4*δ) a b)^2 = (Threshold.source (4*δ) a)^2 := by
    have he := congrArg (fun u : ℝ => u^2) (rounded_abs (4*δ) a b)
    simpa only [sq_abs] using he
  by_cases hz : Threshold.source (4*δ) a = 0
  · have ht : Threshold.target (4*δ) a b = 0 := by
      apply abs_eq_zero.mp
      rw [rounded_abs, hz, abs_zero]
    simp [hz, ht]
  · apply mul_left_cancel₀ (pow_ne_zero 2 hz)
    calc
      (Threshold.source (4*δ) a)^2*
          (Threshold.source (4*δ) a*Threshold.source (4*δ) x) =
        (Threshold.source (4*δ) a)^3*Threshold.source (4*δ) x := by ring
      _ = (Threshold.target (4*δ) a b)^3*Threshold.target (4*δ) x y := hc
      _ = (Threshold.target (4*δ) a b)^2*
          (Threshold.target (4*δ) a b*Threshold.target (4*δ) x y) := by ring
      _ = _ := by rw [hsq]

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
