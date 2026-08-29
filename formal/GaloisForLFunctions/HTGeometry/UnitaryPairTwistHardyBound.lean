import GaloisForLFunctions.HTGeometry.StripThreeLinesTransfer

/-!
# Unitary pair-word Hardy bounds

Hadamard three-lines turns real-axis unitarity and fixed-strip bounds into a loss proportional to
the imaginary displacement of each two-body factor.  On an `O(1/n)` all-particle tube, a
bounded-multiplicity word over the `n(n-1)/2` unordered pairs therefore has total loss `O(n)`, not
`O(n²)`.  The reverse word of pointwise inverses is certified as the two-sided inverse without any
commutativity assumption.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Closed-strip regularity after rotating a horizontal strip to mathlib's vertical strip. -/
def DiffContOnHorizontalCl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : ℂ → E) (l u : ℝ) : Prop :=
  DiffContOnCl ℂ (fun w => F (Complex.I * w))
    (Complex.HadamardThreeLines.verticalStrip l u)

theorem norm_le_rpow_abs_im_div_of_horizontal_threeLines
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : ℂ → E} {rho M : ℝ}
    (hrho : 0 < rho) (_hM : 1 ≤ M)
    (hupper : DiffContOnHorizontalCl F 0 rho)
    (hlower : DiffContOnHorizontalCl F (-rho) 0)
    (hreal : ∀ x : ℝ, ‖F x‖ ≤ 1)
    (hstrip : ∀ z : ℂ, |z.im| ≤ rho → ‖F z‖ ≤ M)
    (z : ℂ) (hz : |z.im| ≤ rho) :
    ‖F z‖ ≤ M ^ (|z.im| / rho) := by
  let w : ℂ := (z.im : ℂ) - Complex.I * (z.re : ℂ)
  have hwre : w.re = z.im := by simp [w]
  have hIw : Complex.I * w = z := by
    apply Complex.ext <;> simp [w]
  have hB : ∀ l u : ℝ, -rho ≤ l → u ≤ rho →
      BddAbove ((norm ∘ fun q => F (Complex.I * q)) ''
        Complex.HadamardThreeLines.verticalClosedStrip l u) := by
    intro l u hl hu
    refine ⟨M, ?_⟩
    rintro y ⟨q, hq, rfl⟩
    apply hstrip
    rw [abs_le]
    constructor
    · simpa using (hl.trans hq.1)
    · simpa using (hq.2.trans hu)
  rcases le_total 0 z.im with him | him
  · have hwmem : w ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 rho := by
      simpa [Complex.HadamardThreeLines.verticalClosedStrip, hwre] using
        And.intro him (abs_le.mp hz).2
    have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
      (f := fun q => F (Complex.I * q)) (z := w) (a := 1) (b := M)
      hrho hwmem hupper (hB 0 rho (by linarith) (by linarith))
      (fun q hq => by
        have hqre : q.re = 0 := hq
        have hIq : Complex.I * q = (-q.im : ℝ) := by
          apply Complex.ext <;> simp [hqre]
        rw [hIq]
        exact hreal (-q.im))
      (fun q hq => by
        apply hstrip
        have hqre : q.re = rho := hq
        simp [hqre, abs_of_pos hrho])
    rw [hIw] at h
    simpa [hwre, abs_of_nonneg him] using h
  · have hwmem : w ∈ Complex.HadamardThreeLines.verticalClosedStrip (-rho) 0 := by
      simpa [Complex.HadamardThreeLines.verticalClosedStrip, hwre] using
        And.intro (abs_le.mp hz).1 him
    have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
      (f := fun q => F (Complex.I * q)) (z := w) (a := M) (b := 1)
      (by linarith) hwmem hlower (hB (-rho) 0 (by linarith) (by linarith))
      (fun q hq => by
        apply hstrip
        have hqre : q.re = -rho := hq
        simp [hqre, abs_of_pos hrho])
      (fun q hq => by
        have hqre : q.re = 0 := hq
        have hIq : Complex.I * q = (-q.im : ℝ) := by
          apply Complex.ext <;> simp [hqre]
        rw [hIq]
        exact hreal (-q.im))
    rw [hIw] at h
    have habs : |z.im| = -z.im := abs_of_nonpos him
    have hexp : 1 - (w.re - -rho) / (0 - -rho) = -z.im / rho := by
      rw [hwre]
      simp only [sub_neg_eq_add]
      field_simp [ne_of_gt hrho]
      ring
    rw [hexp] at h
    simpa [habs] using h

end

section Unitary

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem norm_toContinuousLinearMap_le_one (U : V ≃ₗᵢ[ℂ] V) :
    ‖U.toLinearIsometry.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp

end Unitary

section OrderedWord

variable {ι A : Type*} [SeminormedRing A]

/-- Ordered noncommutative word product. -/
def orderedWordProduct (word : List ι) (F : ι → A) : A :=
  (word.map F).prod

/-- Reverse ordered product, as required for pointwise inverses. -/
def reverseWordProduct (word : List ι) (G : ι → A) : A :=
  (word.reverse.map G).prod

theorem reverseWordProduct_mul_orderedWordProduct
    (word : List ι) (F G : ι → A) (hGF : ∀ r, G r * F r = 1) :
    reverseWordProduct word G * orderedWordProduct word F = 1 := by
  induction word with
  | nil => simp [reverseWordProduct, orderedWordProduct]
  | cons r word ih =>
      simp only [reverseWordProduct, orderedWordProduct, List.reverse_cons,
        List.map_append, List.map_cons, List.prod_append, List.prod_cons,
        List.map_nil, List.prod_nil, mul_one]
      rw [mul_assoc, ← mul_assoc (G r), hGF, one_mul]
      exact ih

theorem orderedWordProduct_mul_reverseWordProduct
    (word : List ι) (F G : ι → A) (hFG : ∀ r, F r * G r = 1) :
    orderedWordProduct word F * reverseWordProduct word G = 1 := by
  induction word with
  | nil => simp [reverseWordProduct, orderedWordProduct]
  | cons r word ih =>
      simp only [reverseWordProduct, orderedWordProduct, List.reverse_cons,
        List.map_append, List.map_cons, List.prod_append, List.prod_cons,
        List.map_nil, List.prod_nil, mul_one]
      change (List.map F word).prod * (List.map G word.reverse).prod = 1 at ih
      rw [mul_assoc, ← mul_assoc (List.map F word).prod, ih, one_mul, hFG]

theorem norm_orderedWordProduct_le_rpow_sum
    [NormOneClass A] (word : List ι) (F : ι → A) {M : ℝ} (hM : 1 ≤ M) (e : ι → ℝ)
    (hF : ∀ r ∈ word, ‖F r‖ ≤ M ^ e r) :
    ‖orderedWordProduct word F‖ ≤ M ^ (word.map e).sum := by
  induction word with
  | nil => simp [orderedWordProduct]
  | cons r word ih =>
      have hr : ‖F r‖ ≤ M ^ e r := hF r (by simp)
      have htail : ∀ s ∈ word, ‖F s‖ ≤ M ^ e s := by
        intro s hs
        exact hF s (by simp [hs])
      have hi := ih htail
      calc
        ‖orderedWordProduct (r :: word) F‖ ≤ ‖F r‖ * ‖orderedWordProduct word F‖ := by
          simpa [orderedWordProduct] using norm_mul_le (F r) (orderedWordProduct word F)
        _ ≤ M ^ e r * M ^ (word.map e).sum :=
          mul_le_mul hr hi (norm_nonneg _) (Real.rpow_nonneg (zero_le_one.trans hM) _)
        _ = M ^ ((r :: word).map e).sum := by
          simp only [List.map_cons, List.sum_cons]
          exact (Real.rpow_add (lt_of_lt_of_le zero_lt_one hM) _ _).symm

/-- General `O(n²)` word / `O(1/n)` factor law from the card: quadratic word length and inverse
linear per-factor exponent produce a linear total exponent. -/
theorem norm_orderedWordProduct_le_of_quadratic_length
    [NormOneClass A] (word : List ι) (F : ι → A) {n : ℕ} (hn : 0 < n)
    {a b rho M : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) (hrho : 0 < rho) (hM : 1 ≤ M)
    (hlength : (word.length : ℝ) ≤ a * n ^ 2)
    (hF : ∀ r ∈ word, ‖F r‖ ≤ M ^ (b / ((n : ℝ) * rho))) :
    ‖orderedWordProduct word F‖ ≤ M ^ (a * b * n / rho) := by
  let e : ι → ℝ := fun _ => b / ((n : ℝ) * rho)
  have hmain := norm_orderedWordProduct_le_rpow_sum word F hM e (by
    intro r hr
    exact hF r hr)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have heNonneg : 0 ≤ b / ((n : ℝ) * rho) := by positivity
  have hsum : (word.map e).sum =
      (word.length : ℝ) * (b / ((n : ℝ) * rho)) := by
    simp [e, mul_comm]
  have hexp : (word.map e).sum ≤ a * b * n / rho := by
    rw [hsum]
    calc
      (word.length : ℝ) * (b / ((n : ℝ) * rho)) ≤
          (a * n ^ 2) * (b / ((n : ℝ) * rho)) :=
            mul_le_mul_of_nonneg_right hlength heNonneg
      _ = a * b * n / rho := by
        field_simp
  exact hmain.trans (Real.rpow_le_rpow_of_exponent_le hM hexp)

end OrderedWord

section PairMultiplicity

private theorem sum_card_Ioi_eq_choose (n : ℕ) :
    ∑ i : Fin n, (Finset.Ioi i).card = n.choose 2 := by
  have h2 : ∑ i : Fin n, (Finset.Ioi i).card = ∑ i : Fin n, (n - 1 - (i : ℕ)) :=
    Finset.sum_congr rfl fun i _ => Fin.card_Ioi i
  have h3 : ∑ i : Fin n, (n - 1 - (i : ℕ)) = ∑ j ∈ Finset.range n, (n - 1 - j) :=
    Fin.sum_univ_eq_sum_range (fun k => n - 1 - k) n
  have h4 : ∑ j ∈ Finset.range n, (n - 1 - j) = ∑ j ∈ Finset.range n, j :=
    Finset.sum_range_reflect (fun k => k) n
  rw [h2, h3, h4, Finset.sum_range_id, Nat.choose_two_right]

private theorem two_mul_choose_two_eq_mul_pred (n : ℕ) :
    2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  refine Nat.mul_div_cancel' ?_
  rcases n with _ | m
  · simp
  · rw [Nat.succ_sub_one]
    have h := (Nat.even_mul_succ_self m).two_dvd
    rwa [mul_comm] at h

/-- Strict unordered pairs represented by their increasing orientation. -/
def strictPairSet (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2

theorem strictPairSet_card (n : ℕ) :
    (strictPairSet n).card = n.choose 2 := by
  classical
  have hfiber : ∀ i : Fin n,
      ((strictPairSet n).filter fun p => p.1 = i).card = (Finset.Ioi i).card := by
    intro i
    apply Finset.card_bij (fun p _ => p.2)
    · intro p hp
      simp only [Finset.mem_Ioi]
      have hpi : p.1 = i := (Finset.mem_filter.mp hp).2
      have hinc : p.1 < p.2 :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      simpa [hpi] using hinc
    · intro p hp q hq hpq
      apply Prod.ext
      · exact ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)
      · exact hpq
    · intro j hj
      have hij : i < j := by simpa only [Finset.mem_Ioi] using hj
      refine ⟨(i, j), ?_, rfl⟩
      simp [strictPairSet, hij]
  have hsum := Finset.sum_card_fiberwise_eq_card_filter
    (strictPairSet n) (Finset.univ : Finset (Fin n)) Prod.fst
  have hsum' : ∑ i : Fin n,
      ((strictPairSet n).filter fun p => p.1 = i).card = (strictPairSet n).card := by
    simpa using hsum
  rw [← hsum']
  simp_rw [hfiber]
  exact sum_card_Ioi_eq_choose n

/-- An ordered factor word with no collision-diagonal entries. -/
structure PairWord (n L : ℕ) where
  left : Fin L → Fin n
  right : Fin L → Fin n
  increasing : ∀ r, left r < right r

/-- Number of occurrences of one unordered pair in a pair word. -/
def PairWord.pairMultiplicity {n L : ℕ} (W : PairWord n L) (i j : Fin n) : ℕ :=
  (Finset.univ.filter fun r => W.left r = i ∧ W.right r = j).card

theorem PairWord.length_le_of_pairMultiplicity {n L m : ℕ} (W : PairWord n L)
    (hm : ∀ i j, i < j → W.pairMultiplicity i j ≤ m) :
    L ≤ m * n.choose 2 := by
  classical
  let pair : Fin L → Fin n × Fin n := fun r => (W.left r, W.right r)
  have hsum := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin L)) (strictPairSet n) pair
  have hright : (Finset.univ.filter fun r => pair r ∈ strictPairSet n).card = L := by
    rw [show Finset.univ.filter (fun r => pair r ∈ strictPairSet n) = Finset.univ by
      ext r
      simp [pair, strictPairSet, W.increasing r]]
    simp
  rw [hright] at hsum
  rw [← hsum]
  calc
    ∑ p ∈ strictPairSet n, (Finset.univ.filter fun r => pair r = p).card
        ≤ ∑ _p ∈ strictPairSet n, m := by
          apply Finset.sum_le_sum
          intro p hp
          have hpinc : p.1 < p.2 := (Finset.mem_filter.mp hp).2
          have hmp := hm p.1 p.2 hpinc
          simpa [PairWord.pairMultiplicity, pair, Prod.ext_iff] using hmp
    _ = m * n.choose 2 := by simp [strictPairSet_card, mul_comm]

end PairMultiplicity

section ShrinkingTube

/-- Alazzawi--Lechner tube around the common line `Im z = -π/2`. -/
def InShrinkingTube {n : ℕ} (kappa : ℝ) (zeta : Fin n → ℂ) : Prop :=
  ∀ i, |(zeta i).im + Real.pi / 2| < kappa / (2 * n)

theorem abs_im_sub_lt_of_mem_shrinkingTube {n : ℕ} {kappa : ℝ}
    {zeta : Fin n → ℂ} (hzeta : InShrinkingTube kappa zeta) (i j : Fin n) :
    |(zeta i - zeta j).im| < kappa / n := by
  have hi := hzeta i
  have hj := hzeta j
  have htriangle :
      |((zeta i).im + Real.pi / 2) - ((zeta j).im + Real.pi / 2)| ≤
        |(zeta i).im + Real.pi / 2| + |(zeta j).im + Real.pi / 2| :=
    abs_sub _ _
  calc
    |(zeta i - zeta j).im| =
        |((zeta i).im + Real.pi / 2) - ((zeta j).im + Real.pi / 2)| := by
          congr 1
          simp
    _ ≤ |(zeta i).im + Real.pi / 2| + |(zeta j).im + Real.pi / 2| := htriangle
    _ < kappa / (2 * n) + kappa / (2 * n) := add_lt_add hi hj
    _ = kappa / n := by ring

end ShrinkingTube

section PairWordHardy

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedSpace ℂ A]

/-- Ordered all-particle product attached to a pair word. -/
def PairWord.forwardProduct {n L : ℕ} (W : PairWord n L)
    (F : Fin L → ℂ → A) (zeta : Fin n → ℂ) : A :=
  orderedWordProduct (List.ofFn fun r : Fin L => r) fun r =>
    F r (zeta (W.left r) - zeta (W.right r))

/-- Reverse product of the pointwise inverse factors. -/
def PairWord.inverseProduct {n L : ℕ} (W : PairWord n L)
    (G : Fin L → ℂ → A) (zeta : Fin n → ℂ) : A :=
  reverseWordProduct (List.ofFn fun r : Fin L => r) fun r =>
    G r (zeta (W.left r) - zeta (W.right r))

theorem PairWord.factorExponent_sum_le {n L m : ℕ} (hn : 0 < n)
    {kappa rho : ℝ} (hkappa : 0 < kappa) (hrho : 0 < rho)
    (W : PairWord n L) (hm : ∀ i j, i < j → W.pairMultiplicity i j ≤ m)
    {zeta : Fin n → ℂ} (hzeta : InShrinkingTube kappa zeta) :
    ((List.ofFn fun r : Fin L =>
      |(zeta (W.left r) - zeta (W.right r)).im| / rho).sum)
      ≤ m * kappa * (n - 1 : ℕ) / (2 * rho) := by
  have heach : ∀ r : Fin L,
      |(zeta (W.left r) - zeta (W.right r)).im| / rho ≤
        kappa / ((n : ℝ) * rho) := by
    intro r
    have hp := (abs_im_sub_lt_of_mem_shrinkingTube hzeta (W.left r) (W.right r)).le
    calc
      |(zeta (W.left r) - zeta (W.right r)).im| / rho
          ≤ (kappa / (n : ℝ)) / rho := div_le_div_of_nonneg_right hp hrho.le
      _ = kappa / ((n : ℝ) * rho) := by rw [div_div]
  have hsum :
      ((List.ofFn fun r : Fin L =>
        |(zeta (W.left r) - zeta (W.right r)).im| / rho).sum)
        ≤ (L : ℝ) * (kappa / ((n : ℝ) * rho)) := by
    rw [List.sum_ofFn]
    calc
      ∑ r : Fin L, |(zeta (W.left r) - zeta (W.right r)).im| / rho
          ≤ ∑ _r : Fin L, kappa / ((n : ℝ) * rho) :=
            Finset.sum_le_sum fun r _ => heach r
      _ = (L : ℝ) * (kappa / ((n : ℝ) * rho)) := by simp [mul_comm]
  have hL := W.length_le_of_pairMultiplicity hm
  have h2Lnat : 2 * L ≤ m * n * (n - 1) := by
    calc
      2 * L ≤ 2 * (m * n.choose 2) := Nat.mul_le_mul_left 2 hL
      _ = m * (2 * n.choose 2) := by ring
      _ = m * (n * (n - 1)) := by
        rw [two_mul_choose_two_eq_mul_pred]
      _ = m * n * (n - 1) := by ring
  have h2L : (2 : ℝ) * L ≤ (m : ℝ) * n * (n - 1 : ℕ) := by
    exact_mod_cast h2Lnat
  have hscale :
      (L : ℝ) * (kappa / ((n : ℝ) * rho)) ≤
        m * kappa * (n - 1 : ℕ) / (2 * rho) := by
    calc
      (L : ℝ) * (kappa / ((n : ℝ) * rho)) =
          (kappa / (2 * (n : ℝ) * rho)) * ((2 : ℝ) * L) := by
            field_simp
      _ ≤ (kappa / (2 * (n : ℝ) * rho)) *
          ((m : ℝ) * n * (n - 1 : ℕ)) :=
            mul_le_mul_of_nonneg_left h2L (by positivity)
      _ = m * kappa * (n - 1 : ℕ) / (2 * rho) := by
            field_simp
  exact hsum.trans hscale

theorem PairWord.norm_forwardProduct_le {n L m : ℕ} (hn : 0 < n)
    {kappa rho M : ℝ} (hkappa : 0 < kappa) (hrho : 0 < rho)
    (hkappaRho : kappa ≤ rho) (hM : 1 ≤ M)
    (W : PairWord n L) (hm : ∀ i j, i < j → W.pairMultiplicity i j ≤ m)
    (F : Fin L → ℂ → A)
    (hupper : ∀ r, DiffContOnHorizontalCl (F r) 0 rho)
    (hlower : ∀ r, DiffContOnHorizontalCl (F r) (-rho) 0)
    (hreal : ∀ r (x : ℝ), ‖F r x‖ ≤ 1)
    (hstrip : ∀ r z, |z.im| ≤ rho → ‖F r z‖ ≤ M)
    {zeta : Fin n → ℂ} (hzeta : InShrinkingTube kappa zeta) :
    ‖W.forwardProduct F zeta‖ ≤ M ^ (m * kappa * (n - 1 : ℕ) / (2 * rho)) := by
  let e : Fin L → ℝ := fun r =>
    |(zeta (W.left r) - zeta (W.right r)).im| / rho
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hkdiv : kappa / (n : ℝ) ≤ rho :=
    (div_le_self hkappa.le hnR).trans hkappaRho
  have hfactor : ∀ r : Fin L,
      ‖F r (zeta (W.left r) - zeta (W.right r))‖ ≤ M ^ e r := by
    intro r
    apply norm_le_rpow_abs_im_div_of_horizontal_threeLines hrho hM
      (hupper r) (hlower r) (hreal r) (hstrip r)
    exact (abs_im_sub_lt_of_mem_shrinkingTube hzeta (W.left r) (W.right r)).le.trans hkdiv
  have hprod := norm_orderedWordProduct_le_rpow_sum
    (List.ofFn fun r : Fin L => r)
    (fun r => F r (zeta (W.left r) - zeta (W.right r))) hM e
    (fun r _ => hfactor r)
  have hsum := W.factorExponent_sum_le hn hkappa hrho hm hzeta
  have hsumE : (((List.ofFn fun r : Fin L => r).map e).sum) ≤
      m * kappa * (n - 1 : ℕ) / (2 * rho) := by
    simpa [e, List.map_ofFn, Function.comp_def] using hsum
  have hpow := Real.rpow_le_rpow_of_exponent_le hM hsumE
  exact (by
    simpa [PairWord.forwardProduct, e, List.map_ofFn, Function.comp_def] using
      hprod.trans hpow)

theorem PairWord.norm_inverseProduct_le {n L m : ℕ} (hn : 0 < n)
    {kappa rho M : ℝ} (hkappa : 0 < kappa) (hrho : 0 < rho)
    (hkappaRho : kappa ≤ rho) (hM : 1 ≤ M)
    (W : PairWord n L) (hm : ∀ i j, i < j → W.pairMultiplicity i j ≤ m)
    (G : Fin L → ℂ → A)
    (hupper : ∀ r, DiffContOnHorizontalCl (G r) 0 rho)
    (hlower : ∀ r, DiffContOnHorizontalCl (G r) (-rho) 0)
    (hreal : ∀ r (x : ℝ), ‖G r x‖ ≤ 1)
    (hstrip : ∀ r z, |z.im| ≤ rho → ‖G r z‖ ≤ M)
    {zeta : Fin n → ℂ} (hzeta : InShrinkingTube kappa zeta) :
    ‖W.inverseProduct G zeta‖ ≤ M ^ (m * kappa * (n - 1 : ℕ) / (2 * rho)) := by
  let e : Fin L → ℝ := fun r =>
    |(zeta (W.left r) - zeta (W.right r)).im| / rho
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hkdiv : kappa / (n : ℝ) ≤ rho :=
    (div_le_self hkappa.le hnR).trans hkappaRho
  have hfactor : ∀ r : Fin L,
      ‖G r (zeta (W.left r) - zeta (W.right r))‖ ≤ M ^ e r := by
    intro r
    apply norm_le_rpow_abs_im_div_of_horizontal_threeLines hrho hM
      (hupper r) (hlower r) (hreal r) (hstrip r)
    exact (abs_im_sub_lt_of_mem_shrinkingTube hzeta (W.left r) (W.right r)).le.trans hkdiv
  have hprod := norm_orderedWordProduct_le_rpow_sum
    (List.ofFn fun r : Fin L => r).reverse
    (fun r => G r (zeta (W.left r) - zeta (W.right r))) hM e
    (fun r _ => hfactor r)
  have hsum := W.factorExponent_sum_le hn hkappa hrho hm hzeta
  have hsumReverse :
      (((List.ofFn fun r : Fin L => r).reverse.map e).sum) =
        (List.ofFn e).sum := by
    simp [List.map_reverse, List.map_ofFn, Function.comp_def]
  have hpow := Real.rpow_le_rpow_of_exponent_le hM hsum
  rw [← hsumReverse] at hpow
  simpa [PairWord.inverseProduct, reverseWordProduct, orderedWordProduct,
    List.map_reverse, List.map_ofFn, Function.comp_def] using hprod.trans hpow

/-- Base of the all-particle exponential Hardy bound. -/
noncomputable def pairWordHardyBase (M : ℝ) (m : ℕ) (kappa rho : ℝ) : ℝ :=
  M ^ (m * kappa / (2 * rho))

theorem rpow_pairWordExponent_le_hardyBase_pow {n m : ℕ}
    {M kappa rho : ℝ} (hM : 1 ≤ M) (hkappa : 0 < kappa) (hrho : 0 < rho) :
    M ^ (m * kappa * (n - 1 : ℕ) / (2 * rho)) ≤
      pairWordHardyBase M m kappa rho ^ n := by
  let c : ℝ := m * kappa / (2 * rho)
  have hc : 0 ≤ c := by positivity
  have hpred : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.pred_le n
  have hexp : m * kappa * (n - 1 : ℕ) / (2 * rho) ≤ c * n := by
    rw [show m * kappa * (n - 1 : ℕ) / (2 * rho) = c * (n - 1 : ℕ) by
      dsimp [c]
      field_simp]
    exact mul_le_mul_of_nonneg_left hpred hc
  calc
    M ^ (m * kappa * (n - 1 : ℕ) / (2 * rho)) ≤ M ^ (c * n) :=
      Real.rpow_le_rpow_of_exponent_le hM hexp
    _ = (M ^ c) ^ (n : ℝ) := Real.rpow_mul (zero_le_one.trans hM) c n
    _ = pairWordHardyBase M m kappa rho ^ n := by
      rw [Real.rpow_natCast]
      rfl

/-- Complete pair-word theorem: the reverse word is the two-sided inverse, and both products have
`exp(O(n))` norm with the exact card constants. -/
theorem unitaryPairWord_hardy_exponential_bound {n L m : ℕ} (hn : 0 < n)
    {kappa rho M Mtilde : ℝ} (hkappa : 0 < kappa) (hrho : 0 < rho)
    (hkappaRho : kappa ≤ rho) (hM : 1 ≤ M) (hMtilde : 1 ≤ Mtilde)
    (W : PairWord n L) (hm : ∀ i j, i < j → W.pairMultiplicity i j ≤ m)
    (F G : Fin L → ℂ → A)
    (hFG : ∀ r z, F r z * G r z = 1)
    (hGF : ∀ r z, G r z * F r z = 1)
    (hFupper : ∀ r, DiffContOnHorizontalCl (F r) 0 rho)
    (hFlower : ∀ r, DiffContOnHorizontalCl (F r) (-rho) 0)
    (hFreal : ∀ r (x : ℝ), ‖F r x‖ ≤ 1)
    (hFstrip : ∀ r z, |z.im| ≤ rho → ‖F r z‖ ≤ M)
    (hGupper : ∀ r, DiffContOnHorizontalCl (G r) 0 rho)
    (hGlower : ∀ r, DiffContOnHorizontalCl (G r) (-rho) 0)
    (hGreal : ∀ r (x : ℝ), ‖G r x‖ ≤ 1)
    (hGstrip : ∀ r z, |z.im| ≤ rho → ‖G r z‖ ≤ Mtilde)
    {zeta : Fin n → ℂ} (hzeta : InShrinkingTube kappa zeta) :
    W.forwardProduct F zeta * W.inverseProduct G zeta = 1 ∧
      W.inverseProduct G zeta * W.forwardProduct F zeta = 1 ∧
      ‖W.forwardProduct F zeta‖ ≤ pairWordHardyBase M m kappa rho ^ n ∧
      ‖W.inverseProduct G zeta‖ ≤ pairWordHardyBase Mtilde m kappa rho ^ n := by
  have hinvRight : W.forwardProduct F zeta * W.inverseProduct G zeta = 1 := by
    apply orderedWordProduct_mul_reverseWordProduct
    intro r
    exact hFG r _
  have hinvLeft : W.inverseProduct G zeta * W.forwardProduct F zeta = 1 := by
    apply reverseWordProduct_mul_orderedWordProduct
    intro r
    exact hGF r _
  have hforward := W.norm_forwardProduct_le hn hkappa hrho hkappaRho hM hm F
    hFupper hFlower hFreal hFstrip hzeta
  have hinverse := W.norm_inverseProduct_le hn hkappa hrho hkappaRho hMtilde hm G
    hGupper hGlower hGreal hGstrip hzeta
  exact ⟨hinvRight, hinvLeft,
    hforward.trans (rpow_pairWordExponent_le_hardyBase_pow hM hkappa hrho),
    hinverse.trans (rpow_pairWordExponent_le_hardyBase_pow hMtilde hkappa hrho)⟩

theorem unitaryPairWord_hardy_exponential_bound_of_realAxisUnitary
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [Nontrivial V]
    {n L m : ℕ} (hn : 0 < n)
    {kappa rho M Mtilde : ℝ} (hkappa : 0 < kappa) (hrho : 0 < rho)
    (hkappaRho : kappa ≤ rho) (hM : 1 ≤ M) (hMtilde : 1 ≤ Mtilde)
    (W : PairWord n L) (hm : ∀ i j, i < j → W.pairMultiplicity i j ≤ m)
    (F G : Fin L → ℂ → (V →L[ℂ] V))
    (hFG : ∀ r z, F r z * G r z = 1)
    (hGF : ∀ r z, G r z * F r z = 1)
    (hFupper : ∀ r, DiffContOnHorizontalCl (F r) 0 rho)
    (hFlower : ∀ r, DiffContOnHorizontalCl (F r) (-rho) 0)
    (hGupper : ∀ r, DiffContOnHorizontalCl (G r) 0 rho)
    (hGlower : ∀ r, DiffContOnHorizontalCl (G r) (-rho) 0)
    (hFstrip : ∀ r z, |z.im| ≤ rho → ‖F r z‖ ≤ M)
    (hGstrip : ∀ r z, |z.im| ≤ rho → ‖G r z‖ ≤ Mtilde)
    (hunitary : ∀ r (x : ℝ), ∃ U : V ≃ₗᵢ[ℂ] V,
      F r x = U.toLinearIsometry.toContinuousLinearMap ∧
      G r x = U.symm.toLinearIsometry.toContinuousLinearMap)
    {zeta : Fin n → ℂ} (hzeta : InShrinkingTube kappa zeta) :
    W.forwardProduct F zeta * W.inverseProduct G zeta = 1 ∧
      W.inverseProduct G zeta * W.forwardProduct F zeta = 1 ∧
      ‖W.forwardProduct F zeta‖ ≤ pairWordHardyBase M m kappa rho ^ n ∧
      ‖W.inverseProduct G zeta‖ ≤ pairWordHardyBase Mtilde m kappa rho ^ n := by
  apply unitaryPairWord_hardy_exponential_bound hn hkappa hrho hkappaRho hM hMtilde
    W hm F G hFG hGF hFupper hFlower
  · intro r x
    obtain ⟨U, hFU, -⟩ := hunitary r x
    rw [hFU]
    exact norm_toContinuousLinearMap_le_one U
  · exact hFstrip
  · exact hGupper
  · exact hGlower
  · intro r x
    obtain ⟨U, -, hGU⟩ := hunitary r x
    rw [hGU]
    exact norm_toContinuousLinearMap_le_one U.symm
  · exact hGstrip
  · exact hzeta

omit [NormedSpace ℂ A] in theorem norm_eq_one_of_twoSidedInverse_of_norm_le_one
    (a b : A) (hab : a * b = 1) (hba : b * a = 1)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a‖ = 1 ∧ ‖b‖ = 1 := by
  have haLower : 1 ≤ ‖a‖ := by
    have hprod : (1 : ℝ) ≤ ‖a‖ * ‖b‖ := by
      calc
        1 = ‖a * b‖ := by rw [hab, norm_one]
        _ ≤ ‖a‖ * ‖b‖ := norm_mul_le _ _
    nlinarith [norm_nonneg a, norm_nonneg b]
  have hbLower : 1 ≤ ‖b‖ := by
    have hprod : (1 : ℝ) ≤ ‖b‖ * ‖a‖ := by
      calc
        1 = ‖b * a‖ := by rw [hba, norm_one]
        _ ≤ ‖b‖ * ‖a‖ := norm_mul_le _ _
    nlinarith [norm_nonneg a, norm_nonneg b]
  exact ⟨le_antisymm ha haLower, le_antisymm hb hbLower⟩

omit [NormedSpace ℂ A] in
/-- On the central boundary every pair argument is real, so the word and its inverse have norm
exactly one. -/
theorem unitaryPairWord_centralBoundary_norm_eq_one {n L : ℕ}
    (W : PairWord n L) (F G : Fin L → ℂ → A)
    (hFG : ∀ r z, F r z * G r z = 1)
    (hGF : ∀ r z, G r z * F r z = 1)
    (hFreal : ∀ r (x : ℝ), ‖F r x‖ ≤ 1)
    (hGreal : ∀ r (x : ℝ), ‖G r x‖ ≤ 1)
    {zeta : Fin n → ℂ} (hcentral : ∀ i, (zeta i).im = -Real.pi / 2) :
    ‖W.forwardProduct F zeta‖ = 1 ∧ ‖W.inverseProduct G zeta‖ = 1 := by
  have hargReal : ∀ r : Fin L,
      zeta (W.left r) - zeta (W.right r) =
        ((zeta (W.left r) - zeta (W.right r)).re : ℂ) := by
    intro r
    apply Complex.ext
    · simp
    · simp [hcentral]
  have hforwardLe : ‖W.forwardProduct F zeta‖ ≤ 1 := by
    have h := norm_orderedWordProduct_le_rpow_sum
      (List.ofFn fun r : Fin L => r)
      (fun r => F r (zeta (W.left r) - zeta (W.right r)))
      (M := 1) (by norm_num) (fun _ => 0) (by
        intro r _
        rw [hargReal r]
        simpa using hFreal r (zeta (W.left r) - zeta (W.right r)).re)
    simpa [PairWord.forwardProduct] using h
  have hinverseLe : ‖W.inverseProduct G zeta‖ ≤ 1 := by
    have h := norm_orderedWordProduct_le_rpow_sum
      (List.ofFn fun r : Fin L => r).reverse
      (fun r => G r (zeta (W.left r) - zeta (W.right r)))
      (M := 1) (by norm_num) (fun _ => 0) (by
        intro r _
        rw [hargReal r]
        simpa using hGreal r (zeta (W.left r) - zeta (W.right r)).re)
    simpa [PairWord.inverseProduct, reverseWordProduct, orderedWordProduct] using h
  have hright : W.forwardProduct F zeta * W.inverseProduct G zeta = 1 := by
    apply orderedWordProduct_mul_reverseWordProduct
    intro r
    exact hFG r _
  have hleft : W.inverseProduct G zeta * W.forwardProduct F zeta = 1 := by
    apply reverseWordProduct_mul_orderedWordProduct
    intro r
    exact hGF r _
  exact norm_eq_one_of_twoSidedInverse_of_norm_le_one _ _ hright hleft hforwardLe hinverseLe

end PairWordHardy

end GaloisForLFunctions.HTGeometry
