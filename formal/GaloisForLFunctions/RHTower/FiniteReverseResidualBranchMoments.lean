import GaloisForLFunctions.RHTower.FiniteReverseResidualSelector

/-!
# Moment cone for each selected reverse residual branch

The strict lower and weak upper effective-rank inequalities ensure that the
small residual atom is nonnegative. They also give exact first and second
power sums, including at the integer-rank equality case.
-/

namespace RHTower
noncomputable section

/-- Every branch selected by its effective-rank interval has nonnegative
atoms and preserves the prescribed residual mass and energy. -/
theorem reverseResidual_branch_moments
    {A B : ℝ} {n : ℕ} (hA : 0 < A) (hB : 0 < B) (hn : 2 ≤ n)
    (hlo : (((n-1 : ℕ) : ℝ)) < A^2/B)
    (hhi : A^2/B ≤ (n : ℝ)) :
    0 ≤ reverseResidualSmall A B n ∧
    reverseResidualSmall A B n ≤ reverseResidualLarge A B n ∧
    ((n : ℝ)-1)*reverseResidualLarge A B n + reverseResidualSmall A B n = A ∧
    ((n : ℝ)-1)*(reverseResidualLarge A B n)^2 +
      (reverseResidualSmall A B n)^2 = B := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn0 : (n:ℝ) ≠ 0 := ne_of_gt hnpos
  have hn1pos : (0:ℝ) < (n:ℝ)-1 := by
    have : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    linarith
  have hn1ne : (n:ℝ)-1 ≠ 0 := ne_of_gt hn1pos
  have hn1cast : (((n-1 : ℕ) : ℝ)) = (n:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hlowB : ((n:ℝ)-1)*B < A^2 := by
    rw [hn1cast, lt_div_iff₀ hB] at hlo
    exact hlo
  have hhighB : A^2 ≤ (n:ℝ)*B := by
    exact (div_le_iff₀ hB).mp hhi
  let d := twoLevelDeviation A B n
  have hdnonneg : 0 ≤ d := twoLevelDeviation_nonneg A B n
  have hdsq : d^2 = ((n:ℝ)*B-A^2)/((n:ℝ)-1) := by
    dsimp [d, twoLevelDeviation]
    apply Real.sq_sqrt
    exact div_nonneg (by linarith) hn1pos.le
  have hdident : ((n:ℝ)-1)*d^2 = (n:ℝ)*B-A^2 := by
    simpa [mul_comm] using (eq_div_iff hn1ne).mp hdsq
  have hsqgap : 0 < A^2 - (((n:ℝ)-1)*d)^2 := by
    calc
      A^2 - (((n:ℝ)-1)*d)^2 =
          A^2 - ((n:ℝ)-1)*(((n:ℝ)-1)*d^2) := by ring
      _ = A^2 - ((n:ℝ)-1)*((n:ℝ)*B-A^2) := by rw [hdident]
      _ = (n:ℝ)*(A^2-((n:ℝ)-1)*B) := by ring
      _ > 0 := mul_pos hnpos (sub_pos.mpr hlowB)
  have hsmallnum : 0 ≤ A-((n:ℝ)-1)*d := by
    have hprod : 0 ≤ ((n:ℝ)-1)*d := mul_nonneg hn1pos.le hdnonneg
    nlinarith
  have hsmall : 0 ≤ reverseResidualSmall A B n := by
    rw [reverseResidualSmall]
    exact div_nonneg (by simpa [d] using hsmallnum) hnpos.le
  have horder : reverseResidualSmall A B n ≤ reverseResidualLarge A B n := by
    rw [reverseResidualSmall, reverseResidualLarge]
    apply (div_le_div_iff₀ hnpos hnpos).mpr
    have hprod : 0 ≤ ((n:ℝ)-1)*d := mul_nonneg hn1pos.le hdnonneg
    dsimp [d] at hdnonneg hprod ⊢
    nlinarith
  have hmass : ((n:ℝ)-1)*reverseResidualLarge A B n +
      reverseResidualSmall A B n = A := by
    rw [reverseResidualLarge, reverseResidualSmall]
    field_simp [hn0]
    ring
  have henergy : ((n:ℝ)-1)*(reverseResidualLarge A B n)^2 +
      (reverseResidualSmall A B n)^2 = B := by
    rw [reverseResidualLarge, reverseResidualSmall]
    change ((n:ℝ)-1)*((A+d)/(n:ℝ))^2 +
      ((A-((n:ℝ)-1)*d)/(n:ℝ))^2 = B
    rw [div_pow, div_pow, ← mul_div_assoc, ← add_div]
    apply (div_eq_iff (pow_ne_zero 2 hn0)).mpr
    calc
      ((n:ℝ)-1)*(A+d)^2+(A-((n:ℝ)-1)*d)^2 =
          (n:ℝ)*(A^2+((n:ℝ)-1)*d^2) := by ring
      _ = (n:ℝ)*((n:ℝ)*B) := by rw [hdident]; ring
      _ = B*(n:ℝ)^2 := by ring
  exact ⟨hsmall, horder, hmass, henergy⟩

/-- Adding zero slots to a reverse head does not alter a power sum. -/
theorem padded_reverse_sum (N n : ℕ) (hn : n ≤ N) (hn2 : 2 ≤ n) (a b : ℝ) :
    (∑ i : Fin N, if i.val < n-1 then a else if i.val = n-1 then b else 0) =
      ((n:ℝ)-1)*a+b := by
  rw [Finset.sum_fin_eq_sum_range]
  have hdrop :
      (∑ x ∈ Finset.range N,
        if h : x < N then
          if x < n-1 then a else if x = n-1 then b else 0
        else 0) =
      (∑ x ∈ Finset.range N,
        if x < n-1 then a else if x = n-1 then b else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_range] at hx
    simp [hx]
  rw [hdrop]
  have hN : N = n + (N-n) := by omega
  conv_lhs => rw [hN, Finset.sum_range_add]
  have htail : (∑ i ∈ Finset.range (N-n),
      if n+i < n-1 then a else if n+i = n-1 then b else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [show ¬ n+i < n-1 by omega, show n+i ≠ n-1 by omega]
  rw [htail, add_zero]
  have hn' : n = (n-1)+1 := by omega
  conv_lhs => rw [hn', Finset.sum_range_succ]
  have hnat : n - 1 + 1 - 1 = n - 1 := by omega
  simp only [hnat]
  have hprefix : (∑ i ∈ Finset.range (n-1),
      if i < n-1 then a else if i = n-1 then b else 0) = (n-1:ℕ)*a := by
    calc
      _ = ∑ i ∈ Finset.range (n-1), a := by
        apply Finset.sum_congr rfl
        intro i hi
        have hlt : i < n-1 := Finset.mem_range.mp hi
        simp [hlt]
      _ = (n-1:ℕ)*a := by simp
  rw [hprefix]
  simp
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  norm_num

theorem reverseResidualVector_pow_sum
    (A B : ℝ) (N n p : ℕ) (hn : n ≤ N) (hn2 : 2 ≤ n) (hp : 0 < p) :
    (∑ i : Fin N, (reverseResidualVector A B N n i)^p) =
      ((n:ℝ)-1)*(reverseResidualLarge A B n)^p +
        (reverseResidualSmall A B n)^p := by
  calc
    _ = ∑ i : Fin N,
        if i.val < n-1 then (reverseResidualLarge A B n)^p
        else if i.val = n-1 then (reverseResidualSmall A B n)^p else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      unfold reverseResidualVector
      split_ifs <;> simp [show p ≠ 0 by omega]
    _ = _ := padded_reverse_sum N n hn hn2 _ _

/-- The complete padded vector is positive and has the prescribed first two
power sums throughout its effective-rank branch. -/
theorem reverseResidualVector_branch_moments
    {A B : ℝ} {N n : ℕ} (hA : 0 < A) (hB : 0 < B)
    (hn : 2 ≤ n) (hnN : n ≤ N)
    (hlo : (((n-1 : ℕ) : ℝ)) < A^2/B)
    (hhi : A^2/B ≤ (n : ℝ)) :
    (∀ i : Fin N, 0 ≤ reverseResidualVector A B N n i) ∧
    (∑ i : Fin N, reverseResidualVector A B N n i) = A ∧
    (∑ i : Fin N, (reverseResidualVector A B N n i)^2) = B := by
  obtain ⟨hsmall, horder, hmass, henergy⟩ :=
    reverseResidual_branch_moments hA hB hn hlo hhi
  have hlarge : 0 ≤ reverseResidualLarge A B n := le_trans hsmall horder
  refine ⟨?_, ?_, ?_⟩
  · intro i
    unfold reverseResidualVector
    split_ifs <;> first | exact hlarge | exact hsmall | positivity
  · calc
      (∑ i : Fin N, reverseResidualVector A B N n i) =
          ∑ i : Fin N, (reverseResidualVector A B N n i)^1 := by simp
      _ = ((n:ℝ)-1)*(reverseResidualLarge A B n)^1 +
          (reverseResidualSmall A B n)^1 :=
        reverseResidualVector_pow_sum A B N n 1 hnN hn (by omega)
      _ = A := by simpa using hmass
  · exact (reverseResidualVector_pow_sum A B N n 2 hnN hn (by omega)).trans henergy

/-- The finite rank selector stays in the positive two-moment cone whenever
its entire rank window fits in the available padded slots. -/
theorem reverseResidualSelectorAux_branch_moments
    {A B : ℝ} {N j : ℕ} (hA : 0 < A) (hB : 0 < B)
    (hlo : (2 : ℝ) ≤ A^2/B)
    (hhi : A^2/B ≤ ((j+2 : ℕ) : ℝ)) (hjN : j+2 ≤ N) :
    (∀ i : Fin N, 0 ≤ reverseResidualSelectorAux A B N j i) ∧
    (∑ i : Fin N, reverseResidualSelectorAux A B N j i) = A ∧
    (∑ i : Fin N, (reverseResidualSelectorAux A B N j i)^2) = B := by
  obtain ⟨n, hn2, hnj, hnlo, hnhi, hsel⟩ :=
    reverseResidualSelectorAux_branch A B N j hlo hhi
  rw [hsel]
  exact reverseResidualVector_branch_moments hA hB hn2 (le_trans hnj hjN) hnlo hnhi

/-- Ordered two-level heads with a prescribed count and the same first two
moments are unique. This identifies endpoint witnesses with the canonical
reverse residual formulas. -/
theorem reverseResidual_unique
    {A B a b : ℝ} {n : ℕ} (hn : 2 ≤ n) (hba : b ≤ a)
    (hfirst : ((n:ℝ)-1)*a+b=A)
    (hsecond : ((n:ℝ)-1)*a^2+b^2=B) :
    a = reverseResidualLarge A B n ∧ b = reverseResidualSmall A B n := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn0 : (n:ℝ) ≠ 0 := ne_of_gt hnpos
  have hn1pos : (0:ℝ) < (n:ℝ)-1 := by
    have : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    linarith
  have hn1ne : (n:ℝ)-1 ≠ 0 := ne_of_gt hn1pos
  have hidentity : ((n:ℝ)-1)*(a-b)^2 = (n:ℝ)*B-A^2 := by
    rw [← hfirst, ← hsecond]
    ring
  have hrad : (((n:ℝ)*B-A^2)/((n:ℝ)-1)) = (a-b)^2 := by
    apply (div_eq_iff hn1ne).mpr
    nlinarith [hidentity]
  have hdev : twoLevelDeviation A B n = a-b := by
    unfold twoLevelDeviation
    rw [hrad, Real.sqrt_sq_eq_abs, abs_of_nonneg (sub_nonneg.mpr hba)]
  constructor
  · rw [reverseResidualLarge, hdev]
    apply (eq_div_iff hn0).mpr
    nlinarith [hfirst]
  · rw [reverseResidualSmall, hdev]
    apply (eq_div_iff hn0).mpr
    nlinarith [hfirst]

/-- An ordered two-level head has effective rank in its expected unit
interval. It hits the lower integer exactly when its exceptional atom is
zero, the sole case requiring a count-changing seam. -/
theorem ordered_twoLevel_effectiveRank_interval
    {A B a b : ℝ} {n : ℕ} (hn : 2 ≤ n) (ha : 0 < a)
    (hb : 0 ≤ b) (hba : b ≤ a)
    (hfirst : ((n:ℝ)-1)*a+b=A)
    (hsecond : ((n:ℝ)-1)*a^2+b^2=B) :
    0 < B ∧ ((n:ℝ)-1) ≤ A^2/B ∧ A^2/B ≤ (n:ℝ) ∧
      (((n:ℝ)-1) = A^2/B ↔ b=0) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2r : (0:ℝ) ≤ (n:ℝ)-2 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn1pos : (0:ℝ) < (n:ℝ)-1 := by linarith
  have hBpos : 0 < B := by
    rw [← hsecond]
    have hapos : 0 < a^2 := sq_pos_of_pos ha
    exact add_pos_of_pos_of_nonneg (mul_pos hn1pos hapos) (sq_nonneg b)
  have hupperGap : (n:ℝ)*B-A^2 = ((n:ℝ)-1)*(a-b)^2 := by
    rw [← hfirst, ← hsecond]
    ring
  have hupper : A^2/B ≤ (n:ℝ) := by
    apply (div_le_iff₀ hBpos).mpr
    nlinarith [mul_nonneg hn1pos.le (sq_nonneg (a-b))]
  have hcoef : 0 < 2*((n:ℝ)-1)*a-((n:ℝ)-2)*b := by
    have hfact : 2*((n:ℝ)-1)*a-((n:ℝ)-2)*b =
      (n:ℝ)*a+((n:ℝ)-2)*(a-b) := by ring
    rw [hfact]
    exact add_pos_of_pos_of_nonneg (mul_pos hnpos ha)
      (mul_nonneg hn2r (sub_nonneg.mpr hba))
  have hlowerGap : A^2-((n:ℝ)-1)*B =
      b*(2*((n:ℝ)-1)*a-((n:ℝ)-2)*b) := by
    rw [← hfirst, ← hsecond]
    ring
  have hlower : ((n:ℝ)-1) ≤ A^2/B := by
    apply (le_div_iff₀ hBpos).mpr
    nlinarith [mul_nonneg hb hcoef.le]
  have heq : ((n:ℝ)-1) = A^2/B ↔ b=0 := by
    constructor
    · intro h
      have hmul : ((n:ℝ)-1)*B = A^2 := by
        exact (eq_div_iff hBpos.ne').mp h
      have hprod : b*(2*((n:ℝ)-1)*a-((n:ℝ)-2)*b) = 0 := by
        linarith [hlowerGap]
      exact (mul_eq_zero.mp hprod).resolve_right hcoef.ne'
    · intro hb0
      rw [hb0] at hlowerGap
      apply (eq_div_iff hBpos.ne').mpr
      nlinarith [hlowerGap]
  exact ⟨hBpos, hlower, hupper, heq⟩

/-- Strict effective-rank bounds determine the finite fold's exact count. -/
theorem reverseResidualSelectorAux_at_rank_interval
    {A B : ℝ} {N j n : ℕ}
    (h2 : (2:ℝ) ≤ A^2/B) (hn : 2 ≤ n) (hnj : n ≤ j+2)
    (hlo : (((n-1:ℕ):ℝ)) < A^2/B)
    (hhi : A^2/B ≤ (n:ℝ)) :
    reverseResidualSelectorAux A B N j = reverseResidualVector A B N n := by
  have hmax : A^2/B ≤ ((j+2:ℕ):ℝ) :=
    le_trans hhi (by exact_mod_cast hnj)
  obtain ⟨m, hm2, hmj, hmlo, hmhi, hsel⟩ :=
    reverseResidualSelectorAux_branch A B N j h2 hmax
  have hmn : m=n := by
    by_contra hne
    by_cases hlt : m<n
    · have hc : (m:ℝ) ≤ (((n-1:ℕ):ℝ)) := by
        exact_mod_cast (show m ≤ n-1 by omega)
      linarith
    · have hlt' : n < m := by omega
      have hc : (n:ℝ) ≤ (((m-1:ℕ):ℝ)) := by
        exact_mod_cast (show n ≤ m-1 by omega)
      linarith
  subst m
  exact hsel

/-- Every ordered two-level residual endpoint is exactly the finite selector
vector. If its exceptional atom vanishes, the adjacent count is identified
through the padded integer-rank seam. -/
theorem ordered_twoLevel_selector_eq
    {A B a b : ℝ} {N j n : ℕ}
    (hn : 3 ≤ n) (hnj : n ≤ j+2) (hA : 0 < A)
    (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a)
    (hfirst : ((n:ℝ)-1)*a+b=A)
    (hsecond : ((n:ℝ)-1)*a^2+b^2=B)
    (h2 : (2:ℝ) ≤ A^2/B) :
    reverseResidualSelectorAux A B N j = reverseResidualVector A B N n := by
  obtain ⟨hB, hlo, hhi, heq⟩ :=
    ordered_twoLevel_effectiveRank_interval (show 2 ≤ n by omega)
      ha hb hba hfirst hsecond
  have hncast : (((n-1:ℕ):ℝ)) = (n:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  by_cases hb0 : b=0
  · have hrank : A^2/B = (((n-1:ℕ):ℝ)) := by
      rw [hncast]
      exact (heq.mpr hb0).symm
    have hk : 2 ≤ n-1 := by omega
    have hlowNat : (((n-1-1:ℕ):ℝ)) < (((n-1:ℕ):ℝ)) := by
      exact_mod_cast (show n-1-1<n-1 by omega)
    have hprev : reverseResidualSelectorAux A B N j =
        reverseResidualVector A B N (n-1) := by
      apply reverseResidualSelectorAux_at_rank_interval h2 hk (by omega)
      · rw [hrank]
        exact hlowNat
      · rw [hrank]
    have hkpos : (0:ℝ) < ((n-1:ℕ):ℝ) := by
      exact_mod_cast (show 0 < n-1 by omega)
    have hmul : A^2 = (((n-1:ℕ):ℝ))*B :=
      (div_eq_iff hB.ne').mp hrank
    have hBeq : B=A^2/((n-1:ℕ):ℝ) := by
      apply (eq_div_iff hkpos.ne').mpr
      nlinarith [hmul]
    calc
      reverseResidualSelectorAux A B N j =
          reverseResidualVector A B N (n-1) := hprev
      _ = reverseResidualVector A B N n := by
        rw [hBeq]
        simpa [show n-1+1=n by omega] using
          (reverseResidualVector_integerRank_seam (A:=A) (k:=n-1) (N:=N) hA hk)
  · have hlowStrict : (n:ℝ)-1 < A^2/B := by
      by_contra hnot
      have heqr : ((n:ℝ)-1)=A^2/B := le_antisymm hlo (le_of_not_gt hnot)
      exact hb0 (heq.mp heqr)
    apply reverseResidualSelectorAux_at_rank_interval h2
      (show 2 ≤ n by omega) hnj
    · rw [hncast]
      exact hlowStrict
    · exact hhi

end
end RHTower
