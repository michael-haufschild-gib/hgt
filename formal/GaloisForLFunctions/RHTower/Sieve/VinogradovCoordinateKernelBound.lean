import GaloisForLFunctions.RHTower.Sieve.VinogradovFejerBlockPartition
import GaloisForLFunctions.RHTower.Sieve.VinogradovRectangularKernel

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

theorem vinogradovCoordinateKernelWeight_nonneg
    {X Y b k : ℕ} (α : Fin k → ℝ) (j : Fin k)
    (g : Fin (vinogradovDifferenceBoxSize X b k)) :
    0 ≤ vinogradovCoordinateKernelWeight (Y := Y) α j g := by
  unfold vinogradovCoordinateKernelWeight
  split_ifs
  · exact finiteFejerKernel_nonneg _ _
  · exact le_rfl

def vinogradovRationalCoordinateCost
    (X Y b q : ℕ) {k : ℕ} (j : Fin k) : ℝ :=
  2 * ((vinogradovFejerCoordinateBound X b j / ((q + 1) / 2) + 1 : ℕ) : ℝ) *
    vinogradovSeparatedBlockCost (vinogradovFejerLength Y b j) q

def vinogradovTrivialCoordinateCost
    (X Y b : ℕ) {k : ℕ} (j : Fin k) : ℝ :=
  4 * (vinogradovFejerCoordinateBound X b j + 1 : ℕ) *
    vinogradovFejerLength Y b j

theorem vinogradovTrivialCoordinateCost_nonneg
    (X Y b : ℕ) {k : ℕ} (j : Fin k) :
    0 ≤ vinogradovTrivialCoordinateCost X Y b j := by
  unfold vinogradovTrivialCoordinateCost
  positivity

theorem vinogradovRationalCoordinateCost_nonneg
    (X Y b q : ℕ) {k : ℕ} (j : Fin k) :
    0 ≤ vinogradovRationalCoordinateCost X Y b q j := by
  have hlog : 0 ≤ Real.log ((q : ℝ) + 1) := by
    apply Real.log_nonneg
    norm_num
  unfold vinogradovRationalCoordinateCost vinogradovSeparatedBlockCost
  positivity

theorem cast_fejerBlockCount_le
    {G q : ℕ} (hq : 0 < q) :
    ((G / ((q + 1) / 2) + 1 : ℕ) : ℝ) ≤
      2 * (G : ℝ) / (q : ℝ) + 1 := by
  let L : ℕ := (q + 1) / 2
  have hL : 0 < L := by dsimp [L]; omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hqL : (q : ℝ) ≤ 2 * (L : ℝ) := by
    exact_mod_cast (by dsimp [L]; omega : q ≤ 2 * L)
  have hinv : 1 / (L : ℝ) ≤ 2 / (q : ℝ) := by
    rw [div_le_div_iff₀ hLR hqR]
    nlinarith
  have hdiv : ((G / L : ℕ) : ℝ) ≤ 2 * (G : ℝ) / (q : ℝ) := by
    calc
      ((G / L : ℕ) : ℝ) ≤ (G : ℝ) / (L : ℝ) := Nat.cast_div_le
      _ = (G : ℝ) * (1 / (L : ℝ)) := by ring
      _ ≤ (G : ℝ) * (2 / (q : ℝ)) := by gcongr
      _ = 2 * (G : ℝ) / (q : ℝ) := by ring
  push_cast
  linarith

theorem vinogradovRationalCoordinateCost_le_explicit
    {X Y b q k : ℕ} (hq : 0 < q) (j : Fin k) :
    vinogradovRationalCoordinateCost X Y b q j ≤
      4 *
        (2 * (vinogradovFejerCoordinateBound X b j : ℝ) / (q : ℝ) + 1) *
        ((vinogradovFejerLength Y b j : ℝ) +
          2 * (q : ℝ) * (1 + Real.log ((q : ℝ) + 1))) := by
  have hblock := cast_fejerBlockCount_le
    (G := vinogradovFejerCoordinateBound X b j) hq
  have hinner : 0 ≤ (vinogradovFejerLength Y b j : ℝ) +
      2 * (q : ℝ) * (1 + Real.log ((q : ℝ) + 1)) := by
    have hlog : 0 ≤ Real.log ((q : ℝ) + 1) := by
      apply Real.log_nonneg
      norm_num
    positivity
  unfold vinogradovRationalCoordinateCost vinogradovSeparatedBlockCost
  nlinarith

def centeredAbsoluteIndex (C : ℕ) (g : Fin (2 * C + 1)) : Fin (C + 1) :=
  if h : g.val ≤ C then
    ⟨C - g.val, by omega⟩
  else
    ⟨g.val - C, by
      have hg := g.isLt
      omega⟩

theorem centeredAbsoluteIndex_val
    (C : ℕ) (g : Fin (2 * C + 1)) :
    (centeredAbsoluteIndex C g).val =
      if g.val ≤ C then C - g.val else g.val - C := by
  unfold centeredAbsoluteIndex
  split_ifs <;> rfl

def centeredAbsoluteIndexFiberEmbedding (C : ℕ) (n : Fin (C + 1)) :
    {g : Fin (2 * C + 1) // centeredAbsoluteIndex C g = n} ↪ Fin 2 where
  toFun g := if g.1.val ≤ C then ⟨0, by omega⟩ else ⟨1, by omega⟩
  inj' := by
    intro g h hsign
    have habs :
        (centeredAbsoluteIndex C g.1).val =
          (centeredAbsoluteIndex C h.1).val := by
      rw [g.2, h.2]
    apply Subtype.ext
    apply Fin.ext
    by_cases hg : g.1.val ≤ C
    · by_cases hh : h.1.val ≤ C
      · simp [centeredAbsoluteIndex_val, hg, hh] at habs
        omega
      · simp [hg, hh] at hsign
    · by_cases hh : h.1.val ≤ C
      · simp [hg, hh] at hsign
      · simp [centeredAbsoluteIndex_val, hg, hh] at habs
        omega

theorem card_centeredAbsoluteIndex_fiber_le_two
    (C : ℕ) (n : Fin (C + 1)) :
    Fintype.card {g : Fin (2 * C + 1) // centeredAbsoluteIndex C g = n} ≤ 2 := by
  calc
    _ ≤ Fintype.card (Fin 2) :=
      Fintype.card_le_of_embedding (centeredAbsoluteIndexFiberEmbedding C n)
    _ = 2 := Fintype.card_fin 2

theorem abs_centered_eq_centeredAbsoluteIndex
    (C : ℕ) (g : Fin (2 * C + 1)) :
    |(g.val : ℝ) - C| = (centeredAbsoluteIndex C g).val := by
  by_cases hg : g.val ≤ C
  · rw [centeredAbsoluteIndex_val, if_pos hg]
    have hgR : (g.val : ℝ) ≤ (C : ℝ) := Nat.cast_le.mpr hg
    have hnonpos : (g.val : ℝ) - (C : ℝ) ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos, Nat.cast_sub hg]
    ring
  · rw [centeredAbsoluteIndex_val, if_neg hg]
    have hge : C ≤ g.val := Nat.le_of_not_ge hg
    have hgeR : (C : ℝ) ≤ (g.val : ℝ) := Nat.cast_le.mpr hge
    have hnonneg : 0 ≤ (g.val : ℝ) - (C : ℝ) := by linarith
    rw [abs_of_nonneg hnonneg, Nat.cast_sub hge]

theorem finiteFejerKernel_centered_eq_absoluteIndex
    (H C : ℕ) (α : ℝ) (g : Fin (2 * C + 1)) :
    finiteFejerKernel H (α * ((g.val : ℝ) - C)) =
      finiteFejerKernel H (α * (centeredAbsoluteIndex C g).val) := by
  by_cases hg : g.val ≤ C
  · have harg :
        α * ((g.val : ℝ) - C) =
          -(α * ((centeredAbsoluteIndex C g).val : ℝ)) := by
      rw [centeredAbsoluteIndex_val, if_pos hg]
      rw [Nat.cast_sub hg]
      ring
    rw [harg, finiteFejerKernel_neg]
  · have harg :
        α * ((g.val : ℝ) - C) =
          α * ((centeredAbsoluteIndex C g).val : ℝ) := by
      rw [centeredAbsoluteIndex_val, if_neg hg]
      rw [Nat.cast_sub (Nat.le_of_not_ge hg)]
    rw [harg]

theorem sum_centered_finiteFejerKernel_le_two_mul_range
    {H C G : ℕ} (hGC : G ≤ C) (α : ℝ) :
    (∑ g : Fin (2 * C + 1),
      if |(g.val : ℝ) - C| ≤ (G : ℝ) then
        finiteFejerKernel H (α * ((g.val : ℝ) - C))
      else 0) ≤
      2 * ∑ n ∈ Finset.range (G + 1),
        finiteFejerKernel H (α * (n : ℝ)) := by
  let w : Fin (C + 1) → ℝ := fun n =>
    if n.val ≤ G then finiteFejerKernel H (α * (n.val : ℝ)) else 0
  have hw : ∀ n, 0 ≤ w n := by
    intro n
    unfold w
    split_ifs
    · exact finiteFejerKernel_nonneg _ _
    · exact le_rfl
  have hrewrite : ∀ g : Fin (2 * C + 1),
      (if |(g.val : ℝ) - C| ≤ (G : ℝ) then
          finiteFejerKernel H (α * ((g.val : ℝ) - C))
        else 0) = w (centeredAbsoluteIndex C g) := by
    intro g
    unfold w
    rw [finiteFejerKernel_centered_eq_absoluteIndex]
    rw [abs_centered_eq_centeredAbsoluteIndex]
    norm_cast
  rw [show (∑ g : Fin (2 * C + 1),
      if |(g.val : ℝ) - C| ≤ (G : ℝ) then
        finiteFejerKernel H (α * ((g.val : ℝ) - C)) else 0) =
      ∑ g : Fin (2 * C + 1), w (centeredAbsoluteIndex C g) by
        apply Finset.sum_congr rfl
        intro g _
        exact hrewrite g]
  calc
    (∑ g : Fin (2 * C + 1), w (centeredAbsoluteIndex C g)) ≤
        2 * ∑ n : Fin (C + 1), w n :=
      sum_comp_le_uniform_fiber_mul (centeredAbsoluteIndex C) w hw 2
        (card_centeredAbsoluteIndex_fiber_le_two C)
    _ = 2 * ∑ n ∈ Finset.range (G + 1),
        finiteFejerKernel H (α * (n : ℝ)) := by
      congr 1
      unfold w
      have hfin :
          (∑ n : Fin (C + 1),
              if n.val ≤ G then
                finiteFejerKernel H (α * (n.val : ℝ)) else 0) =
            ∑ n ∈ Finset.range (C + 1),
              if n ≤ G then finiteFejerKernel H (α * (n : ℝ)) else 0 := by
        rw [Finset.sum_fin_eq_sum_range]
        apply Finset.sum_congr rfl
        intro n hn
        simp only [Finset.mem_range] at hn
        simp only [hn, dite_true]
      rw [hfin]
      have hsub : Finset.range (G + 1) ⊆ Finset.range (C + 1) := by
        intro n hn
        simp only [Finset.mem_range] at hn ⊢
        omega
      symm
      calc
        (∑ n ∈ Finset.range (G + 1),
            finiteFejerKernel H (α * (n : ℝ))) =
            ∑ n ∈ Finset.range (G + 1),
              if n ≤ G then finiteFejerKernel H (α * (n : ℝ)) else 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [if_pos]
          simp only [Finset.mem_range] at hn
          omega
        _ = ∑ n ∈ Finset.range (C + 1),
              if n ≤ G then finiteFejerKernel H (α * (n : ℝ)) else 0 := by
          apply Finset.sum_subset hsub
          intro n hnC hnG
          have hnnot : ¬ n ≤ G := by
            intro hnle
            exact hnG (by simp only [Finset.mem_range]; omega)
          simp [hnnot]

theorem sum_vinogradovCoordinateKernelWeight_le_two_mul_range
    {X Y b k : ℕ} (hX : X ≠ 0)
    (α : Fin k → ℝ) (j : Fin k) :
    (∑ g : Fin (vinogradovDifferenceBoxSize X b k),
      vinogradovCoordinateKernelWeight (Y := Y) α j g) ≤
      2 * ∑ n ∈ Finset.range (vinogradovFejerCoordinateBound X b j + 1),
        finiteFejerKernel (vinogradovFejerLength Y b j)
          (α j * (n : ℝ)) := by
  let C : ℕ := b * X ^ k
  let G : ℕ := vinogradovFejerCoordinateBound X b j
  let H : ℕ := vinogradovFejerLength Y b j
  have hGC : G ≤ C := by
    have htwice := vinogradovFejerCoordinateBound_le_radius (b := b) hX j
    have htwice' : 2 * G ≤ 2 * C := by
      simpa [vinogradovFejerRadius, G, C, mul_assoc] using htwice
    omega
  have hsigned :=
    sum_centered_finiteFejerKernel_le_two_mul_range
      (H := H) hGC (α j)
  have hsize : vinogradovDifferenceBoxSize X b k = 2 * C + 1 := by
    unfold vinogradovDifferenceBoxSize C
    ring
  let e : Fin (vinogradovDifferenceBoxSize X b k) ≃ Fin (2 * C + 1) :=
    finCongr hsize
  have hsum :
      (∑ g : Fin (vinogradovDifferenceBoxSize X b k),
        vinogradovCoordinateKernelWeight (Y := Y) α j g) =
        ∑ g : Fin (2 * C + 1),
          if |(g.val : ℝ) - C| ≤ (G : ℝ) then
            finiteFejerKernel H (α j * ((g.val : ℝ) - C))
          else 0 := by
    refine Fintype.sum_equiv e _ _ ?_
    intro g
    simp [e, vinogradovCoordinateKernelWeight, C, G, H]
  rw [hsum]
  simpa [G, H] using hsigned

theorem sum_vinogradovCoordinateKernelWeight_le_trivial
    {X Y b k : ℕ} (hX : X ≠ 0)
    (α : Fin k → ℝ) (j : Fin k) :
    (∑ g : Fin (vinogradovDifferenceBoxSize X b k),
      vinogradovCoordinateKernelWeight (Y := Y) α j g) ≤
      vinogradovTrivialCoordinateCost X Y b j := by
  calc
    _ ≤ 2 * ∑ n ∈ Finset.range (vinogradovFejerCoordinateBound X b j + 1),
        finiteFejerKernel (vinogradovFejerLength Y b j)
          (α j * (n : ℝ)) :=
      sum_vinogradovCoordinateKernelWeight_le_two_mul_range hX α j
    _ ≤ 2 * ∑ _n ∈ Finset.range (vinogradovFejerCoordinateBound X b j + 1),
        2 * (vinogradovFejerLength Y b j : ℝ) := by
      gcongr with n hn
      exact finiteFejerKernel_le_two_mul_length
        (vinogradovFejerLength_ne_zero Y b j) _
    _ = vinogradovTrivialCoordinateCost X Y b j := by
      rw [Finset.sum_const, Finset.card_range]
      simp only [nsmul_eq_mul]
      unfold vinogradovTrivialCoordinateCost
      push_cast
      ring

/-- Rational approximation plus half-denominator blocking bounds one
coordinate of the rectangular Vinogradov kernel.  The only losses are the
two signs and the explicit separated-block cost. -/
theorem sum_vinogradovCoordinateKernelWeight_le_rationalApprox
    {X Y b k q a : ℕ} (hX : X ≠ 0) (hq : 0 < q)
    (α : Fin k → ℝ) (j : Fin k)
    (hcop : Nat.Coprime a q)
    (happrox : |α j - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    (∑ g : Fin (vinogradovDifferenceBoxSize X b k),
      vinogradovCoordinateKernelWeight (Y := Y) α j g) ≤
      vinogradovRationalCoordinateCost X Y b q j := by
  let C : ℕ := b * X ^ k
  let G : ℕ := vinogradovFejerCoordinateBound X b j
  let H : ℕ := vinogradovFejerLength Y b j
  have hGC : G ≤ C := by
    have htwice := vinogradovFejerCoordinateBound_le_radius (b := b) hX j
    have htwice' : 2 * G ≤ 2 * C := by
      simpa [vinogradovFejerRadius, G, C, mul_assoc] using htwice
    omega
  have hsigned :=
    sum_centered_finiteFejerKernel_le_two_mul_range
      (H := H) hGC (α j)
  have hblocks := sum_finiteFejerKernel_range_le_blockCost
    (G := G) (vinogradovFejerLength_ne_zero Y b j) hq hcop happrox
  have hcombined :
      (∑ g : Fin (2 * C + 1),
        if |(g.val : ℝ) - C| ≤ (G : ℝ) then
          finiteFejerKernel H (α j * ((g.val : ℝ) - C))
        else 0) ≤
        2 * ((G / ((q + 1) / 2) + 1 : ℕ) : ℝ) *
          vinogradovSeparatedBlockCost H q := by
    calc
      _ ≤ 2 * ∑ n ∈ Finset.range (G + 1),
          finiteFejerKernel H (α j * (n : ℝ)) := hsigned
      _ ≤ 2 * (((G / ((q + 1) / 2) + 1 : ℕ) : ℝ) *
          vinogradovSeparatedBlockCost H q) := by
        exact mul_le_mul_of_nonneg_left hblocks (by norm_num)
      _ = 2 * ((G / ((q + 1) / 2) + 1 : ℕ) : ℝ) *
          vinogradovSeparatedBlockCost H q := by ring
  have hsize : vinogradovDifferenceBoxSize X b k = 2 * C + 1 := by
    unfold vinogradovDifferenceBoxSize C
    ring
  let e : Fin (vinogradovDifferenceBoxSize X b k) ≃ Fin (2 * C + 1) :=
    finCongr hsize
  have hsum :
      (∑ g : Fin (vinogradovDifferenceBoxSize X b k),
        vinogradovCoordinateKernelWeight (Y := Y) α j g) =
        ∑ g : Fin (2 * C + 1),
          if |(g.val : ℝ) - C| ≤ (G : ℝ) then
            finiteFejerKernel H (α j * ((g.val : ℝ) - C))
          else 0 := by
    refine Fintype.sum_equiv e _ _ ?_
    intro g
    simp [e, vinogradovCoordinateKernelWeight, C, G, H]
  rw [hsum]
  simpa [vinogradovRationalCoordinateCost, G, H] using hcombined

end

end RHTower.Sieve
