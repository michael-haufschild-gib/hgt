import GaloisForLFunctions.HTGeometry.JetGradientRecursion

/-!
# Degree in one coordinate, and the value at infinity

The peeling of the logarithmic Jacobian compares entries by their degree in the newest coordinate
and reads off the value at infinity.  Both are recorded here without any valuation theory: an
element of the model has degree at most `d` in the coordinate `m` when it is a quotient of
polynomials whose `m`-degrees differ by at most `d`, and it is free of that coordinate when both
degrees are zero.

The two facts the peel needs are that these classes are closed under the ring operations, and that a
coordinate-free element of negative degree is zero — which is uniqueness of the value at infinity.
Determinants then inherit limits entrywise.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-! ## Degree in one coordinate -/

/-- `f` has degree at most `d` in the coordinate `m`. -/
def TopDegLE (m : ℕ) (d : ℤ) (f : CascadeField) : Prop :=
  ∃ N D : MvPolynomial ℕ ℂ, D ≠ 0 ∧
    algebraMap (MvPolynomial ℕ ℂ) CascadeField D * f
      = algebraMap (MvPolynomial ℕ ℂ) CascadeField N ∧
    (degreeOf m N : ℤ) ≤ d + (degreeOf m D : ℤ)

/-- `f` involves the coordinate `m` in neither numerator nor denominator. -/
def TopFree (m : ℕ) (f : CascadeField) : Prop :=
  ∃ N D : MvPolynomial ℕ ℂ, D ≠ 0 ∧
    algebraMap (MvPolynomial ℕ ℂ) CascadeField D * f
      = algebraMap (MvPolynomial ℕ ℂ) CascadeField N ∧
    degreeOf m N = 0 ∧ degreeOf m D = 0

theorem TopFree.topDegLE {m : ℕ} {f : CascadeField} (h : TopFree m f) : TopDegLE m 0 f := by
  obtain ⟨N, D, hD, hf, hN0, hD0⟩ := h
  exact ⟨N, D, hD, hf, by rw [hN0, hD0]; simp⟩

theorem TopDegLE.mono {m : ℕ} {d d' : ℤ} (hdd : d ≤ d') {f : CascadeField}
    (h : TopDegLE m d f) : TopDegLE m d' f := by
  obtain ⟨N, D, hD, hf, hdeg⟩ := h
  exact ⟨N, D, hD, hf, by linarith⟩

theorem degreeOf_X_pow_self (m k : ℕ) :
    degreeOf m ((MvPolynomial.X m : MvPolynomial ℕ ℂ) ^ k) = k := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, degreeOf_mul_eq (pow_ne_zero k (MvPolynomial.X_ne_zero m))
        (MvPolynomial.X_ne_zero m), ih, degreeOf_X]
      simp

theorem topDegLE_zero (m : ℕ) (d : ℤ) : TopDegLE m d (0 : CascadeField) := by
  classical
  refine ⟨0, (MvPolynomial.X m : MvPolynomial ℕ ℂ) ^ (-d).toNat,
    pow_ne_zero _ (MvPolynomial.X_ne_zero m), by simp, ?_⟩
  rw [degreeOf_X_pow_self, MvPolynomial.degreeOf_zero]
  omega

theorem topFree_zero (m : ℕ) : TopFree m (0 : CascadeField) :=
  ⟨0, 1, one_ne_zero, by simp, by simp, by simp⟩

theorem topFree_one (m : ℕ) : TopFree m (1 : CascadeField) :=
  ⟨1, 1, one_ne_zero, by simp, by simp, by simp⟩

theorem topFree_algebraMap {m : ℕ} {N : MvPolynomial ℕ ℂ} (hN : degreeOf m N = 0) :
    TopFree m (algebraMap (MvPolynomial ℕ ℂ) CascadeField N) :=
  ⟨N, 1, one_ne_zero, by simp, hN, by simp⟩

theorem topDegLE_algebraMap (m : ℕ) (N : MvPolynomial ℕ ℂ) :
    TopDegLE m (degreeOf m N) (algebraMap (MvPolynomial ℕ ℂ) CascadeField N) :=
  ⟨N, 1, one_ne_zero, by simp, by simp⟩

/-! ## Closure under the ring operations -/

theorem TopDegLE.add {m : ℕ} {d : ℤ} {f g : CascadeField}
    (hf : TopDegLE m d f) (hg : TopDegLE m d g) : TopDegLE m d (f + g) := by
  obtain ⟨N₁, D₁, hD₁, hf₁, hd₁⟩ := hf
  obtain ⟨N₂, D₂, hD₂, hf₂, hd₂⟩ := hg
  refine ⟨N₁ * D₂ + N₂ * D₁, D₁ * D₂, mul_ne_zero hD₁ hD₂, ?_, ?_⟩
  · rw [map_mul, map_add, map_mul, map_mul, mul_add]
    rw [show algebraMap (MvPolynomial ℕ ℂ) CascadeField D₁
        * algebraMap (MvPolynomial ℕ ℂ) CascadeField D₂ * f
        = algebraMap (MvPolynomial ℕ ℂ) CascadeField D₂
          * (algebraMap (MvPolynomial ℕ ℂ) CascadeField D₁ * f) by ring,
      show algebraMap (MvPolynomial ℕ ℂ) CascadeField D₁
        * algebraMap (MvPolynomial ℕ ℂ) CascadeField D₂ * g
        = algebraMap (MvPolynomial ℕ ℂ) CascadeField D₁
          * (algebraMap (MvPolynomial ℕ ℂ) CascadeField D₂ * g) by ring,
      hf₁, hf₂]
    ring
  · have hDD : degreeOf m (D₁ * D₂) = degreeOf m D₁ + degreeOf m D₂ :=
      degreeOf_mul_eq hD₁ hD₂
    have h1 : degreeOf m (N₁ * D₂ + N₂ * D₁)
        ≤ max (degreeOf m (N₁ * D₂)) (degreeOf m (N₂ * D₁)) := degreeOf_add_le _ _ _
    have h2 : degreeOf m (N₁ * D₂) ≤ degreeOf m N₁ + degreeOf m D₂ := degreeOf_mul_le _ _ _
    have h3 : degreeOf m (N₂ * D₁) ≤ degreeOf m N₂ + degreeOf m D₁ := degreeOf_mul_le _ _ _
    rw [hDD]
    rcases max_cases (degreeOf m (N₁ * D₂)) (degreeOf m (N₂ * D₁)) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rw [he] at h1 <;> push_cast <;> omega

theorem TopDegLE.neg {m : ℕ} {d : ℤ} {f : CascadeField} (hf : TopDegLE m d f) :
    TopDegLE m d (-f) := by
  obtain ⟨N, D, hD, hf', hdeg⟩ := hf
  refine ⟨-N, D, hD, ?_, ?_⟩
  · rw [map_neg, ← hf']
    ring
  · rwa [degreeOf_neg]

theorem TopDegLE.sub {m : ℕ} {d : ℤ} {f g : CascadeField}
    (hf : TopDegLE m d f) (hg : TopDegLE m d g) : TopDegLE m d (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem TopDegLE.mul {m : ℕ} {d e : ℤ} {f g : CascadeField}
    (hf : TopDegLE m d f) (hg : TopDegLE m e g) : TopDegLE m (d + e) (f * g) := by
  obtain ⟨N₁, D₁, hD₁, hf₁, hd₁⟩ := hf
  obtain ⟨N₂, D₂, hD₂, hf₂, hd₂⟩ := hg
  refine ⟨N₁ * N₂, D₁ * D₂, mul_ne_zero hD₁ hD₂, ?_, ?_⟩
  · rw [map_mul, map_mul]
    calc algebraMap (MvPolynomial ℕ ℂ) CascadeField D₁
          * algebraMap (MvPolynomial ℕ ℂ) CascadeField D₂ * (f * g)
        = (algebraMap (MvPolynomial ℕ ℂ) CascadeField D₁ * f)
          * (algebraMap (MvPolynomial ℕ ℂ) CascadeField D₂ * g) := by ring
      _ = algebraMap (MvPolynomial ℕ ℂ) CascadeField N₁
          * algebraMap (MvPolynomial ℕ ℂ) CascadeField N₂ := by rw [hf₁, hf₂]
  · have hDD : degreeOf m (D₁ * D₂) = degreeOf m D₁ + degreeOf m D₂ :=
      degreeOf_mul_eq hD₁ hD₂
    have h1 : degreeOf m (N₁ * N₂) ≤ degreeOf m N₁ + degreeOf m N₂ := degreeOf_mul_le _ _ _
    rw [hDD]
    push_cast
    omega

theorem TopFree.add {m : ℕ} {f g : CascadeField} (hf : TopFree m f) (hg : TopFree m g) :
    TopFree m (f + g) := by
  obtain ⟨N₁, D₁, hD₁, hf₁, hn₁, hm₁⟩ := hf
  obtain ⟨N₂, D₂, hD₂, hf₂, hn₂, hm₂⟩ := hg
  refine ⟨N₁ * D₂ + N₂ * D₁, D₁ * D₂, mul_ne_zero hD₁ hD₂, ?_, ?_, ?_⟩
  · rw [map_mul, map_add, map_mul, map_mul, mul_add]
    rw [show algebraMap (MvPolynomial ℕ ℂ) CascadeField D₁
        * algebraMap (MvPolynomial ℕ ℂ) CascadeField D₂ * f
        = algebraMap (MvPolynomial ℕ ℂ) CascadeField D₂
          * (algebraMap (MvPolynomial ℕ ℂ) CascadeField D₁ * f) by ring,
      show algebraMap (MvPolynomial ℕ ℂ) CascadeField D₁
        * algebraMap (MvPolynomial ℕ ℂ) CascadeField D₂ * g
        = algebraMap (MvPolynomial ℕ ℂ) CascadeField D₁
          * (algebraMap (MvPolynomial ℕ ℂ) CascadeField D₂ * g) by ring,
      hf₁, hf₂]
    ring
  · have h1 : degreeOf m (N₁ * D₂ + N₂ * D₁)
        ≤ max (degreeOf m (N₁ * D₂)) (degreeOf m (N₂ * D₁)) := degreeOf_add_le _ _ _
    have h2 : degreeOf m (N₁ * D₂) ≤ degreeOf m N₁ + degreeOf m D₂ := degreeOf_mul_le _ _ _
    have h3 : degreeOf m (N₂ * D₁) ≤ degreeOf m N₂ + degreeOf m D₁ := degreeOf_mul_le _ _ _
    omega
  · rw [degreeOf_mul_eq hD₁ hD₂, hm₁, hm₂]

theorem TopFree.mul {m : ℕ} {f g : CascadeField} (hf : TopFree m f) (hg : TopFree m g) :
    TopFree m (f * g) := by
  obtain ⟨N₁, D₁, hD₁, hf₁, hn₁, hm₁⟩ := hf
  obtain ⟨N₂, D₂, hD₂, hf₂, hn₂, hm₂⟩ := hg
  refine ⟨N₁ * N₂, D₁ * D₂, mul_ne_zero hD₁ hD₂, ?_, ?_, ?_⟩
  · rw [map_mul, map_mul]
    calc algebraMap (MvPolynomial ℕ ℂ) CascadeField D₁
          * algebraMap (MvPolynomial ℕ ℂ) CascadeField D₂ * (f * g)
        = (algebraMap (MvPolynomial ℕ ℂ) CascadeField D₁ * f)
          * (algebraMap (MvPolynomial ℕ ℂ) CascadeField D₂ * g) := by ring
      _ = algebraMap (MvPolynomial ℕ ℂ) CascadeField N₁
          * algebraMap (MvPolynomial ℕ ℂ) CascadeField N₂ := by rw [hf₁, hf₂]
  · have h1 : degreeOf m (N₁ * N₂) ≤ degreeOf m N₁ + degreeOf m N₂ := degreeOf_mul_le _ _ _
    omega
  · rw [degreeOf_mul_eq hD₁ hD₂, hm₁, hm₂]

theorem TopFree.neg {m : ℕ} {f : CascadeField} (hf : TopFree m f) : TopFree m (-f) := by
  obtain ⟨N, D, hD, hf', hn, hm⟩ := hf
  refine ⟨-N, D, hD, ?_, ?_, hm⟩
  · rw [map_neg, ← hf']; ring
  · rwa [degreeOf_neg]

theorem TopFree.sub {m : ℕ} {f g : CascadeField} (hf : TopFree m f) (hg : TopFree m g) :
    TopFree m (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem topFree_sum {m : ℕ} {ι : Type*} (s : Finset ι) (F : ι → CascadeField)
    (h : ∀ i ∈ s, TopFree m (F i)) : TopFree m (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using topFree_zero m
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem topFree_prod {m : ℕ} {ι : Type*} (s : Finset ι) (F : ι → CascadeField)
    (h : ∀ i ∈ s, TopFree m (F i)) : TopFree m (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using topFree_one m
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ## Uniqueness of the value at infinity -/

/-- **A coordinate-free element of negative degree vanishes.** -/
theorem eq_zero_of_topFree_of_topDegLE_neg {m : ℕ} {f : CascadeField} (hfree : TopFree m f)
    (hd : TopDegLE m (-1) f) : f = 0 := by
  obtain ⟨N', D', hD', hf', hn', hm'⟩ := hfree
  obtain ⟨N, D, hD, hf, hdeg⟩ := hd
  have hD'ne : algebraMap (MvPolynomial ℕ ℂ) CascadeField D' ≠ 0 := by
    simpa using (IsFractionRing.injective (MvPolynomial ℕ ℂ) CascadeField).ne_iff.mpr hD'
  rcases eq_or_ne N' 0 with hN'0 | hN'0
  · rw [hN'0, map_zero] at hf'
    exact (mul_eq_zero.mp hf').resolve_left hD'ne
  · exfalso
    have hcross : D * N' = D' * N := by
      refine (IsFractionRing.injective (MvPolynomial ℕ ℂ) CascadeField) ?_
      rw [map_mul, map_mul, ← hf', ← hf]
      ring
    have hNne : N ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hcross
      rcases mul_eq_zero.mp hcross with h | h
      · exact hD h
      · exact hN'0 h
    have h1 : degreeOf m (D * N') = degreeOf m D + degreeOf m N' := degreeOf_mul_eq hD hN'0
    have h2 : degreeOf m (D' * N) = degreeOf m D' + degreeOf m N := degreeOf_mul_eq hD' hNne
    rw [hcross, h2, hn', hm'] at h1
    omega

/-! ## The value at infinity -/

/-- `f` tends to `a` as the coordinate `m` grows. -/
def TopLim (m : ℕ) (f a : CascadeField) : Prop := TopDegLE m (-1) (f - a)

theorem topLim_of_topFree_sub {m : ℕ} {f a : CascadeField} (h : TopDegLE m (-1) (f - a)) :
    TopLim m f a := h

theorem TopLim.topDegLE_zero {m : ℕ} {f a : CascadeField} (ha : TopFree m a)
    (h : TopLim m f a) : TopDegLE m 0 f := by
  have hsub : TopDegLE m 0 (f - a) := TopDegLE.mono (by norm_num) h
  have hadd := TopDegLE.add hsub (TopFree.topDegLE ha)
  simpa using hadd

/-- **The value at infinity is unique.** -/
theorem topLim_unique {m : ℕ} {f a b : CascadeField} (ha : TopFree m a) (hb : TopFree m b)
    (h1 : TopLim m f a) (h2 : TopLim m f b) : a = b := by
  have hsub : TopDegLE m (-1) (b - a) := by
    have hd := TopDegLE.sub h1 h2
    have heq : f - a - (f - b) = b - a := by ring
    rwa [heq] at hd
  have hfree : TopFree m (b - a) := hb.sub ha
  have := eq_zero_of_topFree_of_topDegLE_neg hfree hsub
  linear_combination -this

theorem topLim_const {m : ℕ} {a : CascadeField} : TopLim m a a := by
  rw [TopLim, sub_self]
  exact topDegLE_zero m (-1)

theorem TopLim.add {m : ℕ} {f g a b : CascadeField} (hf : TopLim m f a) (hg : TopLim m g b) :
    TopLim m (f + g) (a + b) := by
  have hsum : TopDegLE m (-1) ((f - a) + (g - b)) := TopDegLE.add hf hg
  have heq : (f - a) + (g - b) = f + g - (a + b) := by ring
  rw [heq] at hsum
  exact hsum

theorem TopLim.neg {m : ℕ} {f a : CascadeField} (hf : TopLim m f a) : TopLim m (-f) (-a) := by
  have hn : TopDegLE m (-1) (-(f - a)) := TopDegLE.neg hf
  have heq : -(f - a) = -f - -a := by ring
  rw [heq] at hn
  exact hn

theorem TopLim.mul {m : ℕ} {f g a b : CascadeField} (ha : TopFree m a) (hb : TopFree m b)
    (hf : TopLim m f a) (hg : TopLim m g b) : TopLim m (f * g) (a * b) := by
  have hg0 : TopDegLE m 0 g := TopLim.topDegLE_zero hb hg
  have h1 : TopDegLE m (-1) ((f - a) * g) := by
    have h := TopDegLE.mul hf hg0
    simpa using h
  have h2 : TopDegLE m (-1) (a * (g - b)) := by
    have h := TopDegLE.mul (TopFree.topDegLE ha) hg
    simpa using h
  have hsum : TopDegLE m (-1) ((f - a) * g + a * (g - b)) := TopDegLE.add h1 h2
  have heq : (f - a) * g + a * (g - b) = f * g - a * b := by ring
  rw [heq] at hsum
  exact hsum

theorem topLim_sum {m : ℕ} {ι : Type*} (s : Finset ι) (F L : ι → CascadeField)
    (h : ∀ i ∈ s, TopLim m (F i) (L i)) :
    TopLim m (∑ i ∈ s, F i) (∑ i ∈ s, L i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (topLim_const (m := m) (a := (0 : CascadeField)))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact TopLim.add (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem topLim_prod {m : ℕ} {ι : Type*} (s : Finset ι) (F L : ι → CascadeField)
    (hL : ∀ i ∈ s, TopFree m (L i)) (h : ∀ i ∈ s, TopLim m (F i) (L i)) :
    TopLim m (∏ i ∈ s, F i) (∏ i ∈ s, L i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (topLim_const (m := m) (a := (1 : CascadeField)))
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      refine TopLim.mul (hL a (Finset.mem_insert_self a s))
        (topFree_prod s L fun i hi => hL i (Finset.mem_insert_of_mem hi))
        (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => hL i (Finset.mem_insert_of_mem hi))
          fun i hi => h i (Finset.mem_insert_of_mem hi))


/-! ## The generators of the model -/

theorem coeff_univFactor_single (p : Polynomial ℂ) (m i : ℕ) :
    MvPolynomial.coeff (Finsupp.single m i) (univFactor p m) = p.coeff i := by
  classical
  induction p using Polynomial.induction_on with
  | C a =>
      have h : univFactor (Polynomial.C a) m = MvPolynomial.C a := by simp [univFactor]
      rw [h, MvPolynomial.coeff_C, Polynomial.coeff_C]
      by_cases hi : i = 0
      · subst hi; simp
      · rw [if_neg hi, if_neg]
        intro hc
        exact hi ((Finsupp.single_eq_zero).mp hc.symm ▸ rfl)
  | add p q hp hq =>
      have h : univFactor (p + q) m = univFactor p m + univFactor q m := by simp [univFactor]
      rw [h, MvPolynomial.coeff_add, hp, hq, Polynomial.coeff_add]
  | monomial n a _ =>
      have h : univFactor (Polynomial.C a * Polynomial.X ^ (n + 1)) m
          = MvPolynomial.C a * (MvPolynomial.X m : MvPolynomial ℕ ℂ) ^ (n + 1) := by
        simp [univFactor]
      rw [h, MvPolynomial.coeff_C_mul, MvPolynomial.X_pow_eq_monomial,
        MvPolynomial.coeff_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases hi : i = n + 1
      · subst hi; simp
      · rw [if_neg (fun hc => hi (by
          have := congrArg (fun t : ℕ →₀ ℕ => t m) hc
          simpa using this.symm)), if_neg (fun hc => hi hc.symm)]
        ring

theorem degreeOf_univFactor_le (m : ℕ) (p : Polynomial ℂ) :
    degreeOf m (univFactor p m) ≤ p.natDegree := by
  classical
  induction p using Polynomial.induction_on with
  | C a =>
      have h : univFactor (Polynomial.C a) m = MvPolynomial.C a := by simp [univFactor]
      rw [h]
      simp
  | add p q hp hq =>
      have h : univFactor (p + q) m = univFactor p m + univFactor q m := by simp [univFactor]
      rw [h]
      refine le_trans (degreeOf_add_le _ _ _) ?_
      have hd := Polynomial.natDegree_add_le p q
      omega
  | monomial n a _ =>
      rcases eq_or_ne a 0 with rfl | ha
      · have h : univFactor ((0 : Polynomial ℂ) * Polynomial.X ^ (n + 1)) m = 0 := by
          simp [univFactor]
        simp only [map_zero, zero_mul] at h ⊢
        rw [h]
        simp
      · have h : univFactor (Polynomial.C a * Polynomial.X ^ (n + 1)) m
            = MvPolynomial.C a * (MvPolynomial.X m : MvPolynomial ℕ ℂ) ^ (n + 1) := by
          simp [univFactor]
        have hdeg : (Polynomial.C a * Polynomial.X ^ (n + 1)).natDegree = n + 1 := by
          rw [Polynomial.natDegree_C_mul_X_pow _ _ ha]
        rw [h, hdeg]
        refine le_trans (degreeOf_mul_le _ _ _) ?_
        rw [degreeOf_C, degreeOf_X_pow_self]
        omega

theorem degreeOf_univFactor_eq (m : ℕ) {p : Polynomial ℂ} (hp : p ≠ 0) :
    degreeOf m (univFactor p m) = p.natDegree := by
  classical
  refine le_antisymm (degreeOf_univFactor_le m p) ?_
  have hcoeff : MvPolynomial.coeff (Finsupp.single m p.natDegree) (univFactor p m)
      = p.leadingCoeff := coeff_univFactor_single p m p.natDegree
  have hmem : (Finsupp.single m p.natDegree) ∈ (univFactor p m).support := by
    rw [MvPolynomial.mem_support_iff, hcoeff]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hle := (MvPolynomial.degreeOf_le_iff.mp (le_refl (degreeOf m (univFactor p m))))
    _ hmem
  simpa using hle

theorem degreeOf_univFactor_of_ne {m j : ℕ} (h : m ≠ j) (p : Polynomial ℂ) :
    degreeOf m (univFactor p j) = 0 := by
  classical
  induction p using Polynomial.induction_on with
  | C a =>
      have hC : univFactor (Polynomial.C a) j = MvPolynomial.C a := by simp [univFactor]
      rw [hC]
      simp
  | add p q hp hq =>
      have hadd : univFactor (p + q) j = univFactor p j + univFactor q j := by simp [univFactor]
      rw [hadd]
      have := degreeOf_add_le m (univFactor p j) (univFactor q j)
      omega
  | monomial n a _ =>
      have hmon : univFactor (Polynomial.C a * Polynomial.X ^ (n + 1)) j
          = MvPolynomial.C a * (MvPolynomial.X j : MvPolynomial ℕ ℂ) ^ (n + 1) := by
        simp [univFactor]
      have hX : degreeOf m ((MvPolynomial.X j : MvPolynomial ℕ ℂ) ^ (n + 1)) = 0 := by
        refine Nat.le_zero.mp (le_trans (degreeOf_pow_le _ _ _) ?_)
        rw [degreeOf_X, if_neg h]
        simp
      rw [hmon]
      have := degreeOf_mul_le m (MvPolynomial.C a : MvPolynomial ℕ ℂ)
        ((MvPolynomial.X j : MvPolynomial ℕ ℂ) ^ (n + 1))
      rw [degreeOf_C, hX] at this
      omega

/-! ## The classes of the model's elements -/

theorem topFree_fact {m j : ℕ} (h : m ≠ j) (p : Polynomial ℂ) : TopFree m (fact p j) :=
  topFree_algebraMap (degreeOf_univFactor_of_ne h p)

theorem topFree_inv_fact {m j : ℕ} (h : m ≠ j) (p : Polynomial ℂ) :
    TopFree m ((fact p j)⁻¹) := by
  rcases eq_or_ne (fact p j) 0 with h0 | h0
  · rw [h0, inv_zero]
    exact topFree_zero m
  · exact ⟨1, univFactor p j, ?_, ?_, by simp, degreeOf_univFactor_of_ne h p⟩
    · intro hc
      exact h0 (by rw [fact, hc, map_zero])
    · rw [show algebraMap (MvPolynomial ℕ ℂ) CascadeField (univFactor p j) = fact p j from rfl,
        mul_inv_cancel₀ h0, map_one]

theorem topDegLE_fact (m : ℕ) (p : Polynomial ℂ) :
    TopDegLE m (p.natDegree : ℤ) (fact p m) := by
  have h := topDegLE_algebraMap m (univFactor p m)
  refine TopDegLE.mono ?_ h
  exact_mod_cast degreeOf_univFactor_le m p

theorem topDegLE_inv_fact (m : ℕ) {p : Polynomial ℂ} (hp : p ≠ 0) :
    TopDegLE m (-(p.natDegree : ℤ)) ((fact p m)⁻¹) := by
  have hne : fact p m ≠ 0 := fact_ne_zero hp m
  refine ⟨1, univFactor p m, ?_, ?_, ?_⟩
  · intro hc
    exact hne (by rw [fact, hc, map_zero])
  · rw [show algebraMap (MvPolynomial ℕ ℂ) CascadeField (univFactor p m) = fact p m from rfl,
      mul_inv_cancel₀ hne, map_one]
  · rw [degreeOf_univFactor_eq m hp]
    simp

theorem topFree_logFactor {m j : ℕ} (h : m ≠ j) (p : Polynomial ℂ) :
    TopFree m (logFactor p j) := by
  rw [logFactor, div_eq_mul_inv]
  exact TopFree.mul (topFree_fact h _) (topFree_inv_fact h p)

/-- **A logarithmic factor has degree `-1` in its own coordinate.** -/
theorem topDegLE_logFactor (m : ℕ) {p : Polynomial ℂ} (hp : 1 ≤ p.natDegree) :
    TopDegLE m (-1) (logFactor p m) := by
  have hp0 : p ≠ 0 := fun h => by simp [h] at hp
  have hd : TopDegLE m ((p.derivative.natDegree : ℤ) + -(p.natDegree : ℤ))
      (fact p.derivative m * (fact p m)⁻¹) :=
    TopDegLE.mul (topDegLE_fact m p.derivative) (topDegLE_inv_fact m hp0)
  rw [logFactor, div_eq_mul_inv]
  refine TopDegLE.mono ?_ hd
  have hdd : p.derivative.natDegree = p.natDegree - 1 := natDegree_derivative_eq_sub_one hp
  rw [hdd]
  omega

theorem topFree_prodHead {Q : ℕ → Polynomial ℂ} {m k : ℕ} (h : k ≤ m) :
    TopFree m (prodHead Q k) := by
  rw [prodHead]
  refine topFree_prod _ _ fun j hj => ?_
  have hjk : j < k := Finset.mem_range.mp hj
  exact topFree_fact (by omega) (Q j)

/-! ## Determinants inherit the value at infinity -/

/-- **A matrix of limits has the limit determinant.** -/
theorem topLim_det {m n : ℕ} (A L : Matrix (Fin n) (Fin n) CascadeField)
    (hL : ∀ i j, TopFree m (L i j)) (h : ∀ i j, TopLim m (A i j) (L i j)) :
    TopLim m A.det L.det := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply]
  refine topLim_sum _ _ _ fun σ _ => ?_
  have hprod : TopLim m (∏ i, A (σ i) i) (∏ i, L (σ i) i) :=
    topLim_prod _ _ _ (fun i _ => hL (σ i) i) fun i _ => h (σ i) i
  have hsign : ((Equiv.Perm.sign σ : ℤ) : CascadeField) = 1 ∨
      ((Equiv.Perm.sign σ : ℤ) : CascadeField) = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs] <;> simp
  rcases hsign with hs | hs <;>
    simp only [Units.smul_def, zsmul_eq_mul, hs, one_mul, neg_mul] <;>
    [exact hprod; exact hprod.neg]

end GaloisForLFunctions.HTGeometry
