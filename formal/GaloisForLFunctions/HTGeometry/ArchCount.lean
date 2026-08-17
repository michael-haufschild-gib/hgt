import GaloisForLFunctions.HTGeometry.SturmComparisonArch

/-!
# Counting arches

Sturm comparison bounds arch *length* from below; disjointness turns that into a bound on arch
*number*.  Where `g'' + γ² g` keeps one sign, every positive arch of `g` is at least `π/γ` long, so
an interval of length `b - a` carries at most `(b-a)γ/π` pairwise disjoint positive arches.

This is the effective count the interval criterion of `IntervalSeparation` needs: the humps of a
comparison function are its positive arches, and their number is what determines how many separating
exponentials a certificate must exhibit.  Where the Sturm expression changes sign the interval must
first be split at its zeros — that expression is again an exponential polynomial, so the splitting is
finite, and each piece is counted by the bound below.
-/

open Set Real

namespace GaloisForLFunctions.HTGeometry

/-- **Arch-length bound.**  Where the Sturm expression is positive, a positive arch of `g` is at
least `π/γ` long. -/
theorem arch_length_ge {g gd gdd h : ℝ → ℝ} {γ a b p q : ℝ} (hγ : 0 < γ)
    (hg : ∀ t, HasDerivAt g (gd t) t) (hgd : ∀ t, HasDerivAt gd (gdd t) t)
    (hh : ∀ t, h t = gdd t + γ ^ 2 * g t)
    (hhpos : ∀ t ∈ Icc a b, 0 < h t)
    (hpa : a ≤ p) (hqb : q ≤ b) (hpq : p < q)
    (hgp : g p = 0) (hgq : g q = 0) (harch : ∀ t ∈ Ioo p q, 0 < g t) :
    π / γ ≤ q - p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ξ, hξ, hval⟩ := exists_sturm_neg hγ hg hgd hh hpq hcon hgp hgq harch
  have hmem : ξ ∈ Icc a b :=
    ⟨le_trans hpa (le_of_lt hξ.1), le_trans (le_of_lt hξ.2) hqb⟩
  linarith [hhpos ξ hmem]

/-! ## Disjoint intervals of a fixed minimal length -/

/-- Finitely many ordered, pairwise disjoint subintervals of `[a,b]`, each of length at least `d`,
number at most `(b-a)/d`. -/
theorem nsmul_le_of_disjoint_intervals :
    ∀ (n : ℕ) (p q : Fin n → ℝ) (a b d : ℝ), a ≤ b →
      (∀ k, a ≤ p k) → (∀ k, q k ≤ b) → (∀ k, p k ≤ q k) →
      (∀ k l : Fin n, k < l → q k ≤ p l) → (∀ k, d ≤ q k - p k) →
      (n : ℝ) * d ≤ b - a := by
  intro n
  induction n with
  | zero =>
    intro p q a b d hab _ _ _ _ _
    simp
    linarith
  | succ n ih =>
    intro p q a b d hab hpa hqb hpq hdisj hd
    set last : Fin (n + 1) := Fin.last n with hlast
    have hprev : ∀ k : Fin n, q (Fin.castSucc k) ≤ p last := by
      intro k
      exact hdisj _ _ (by rw [hlast]; exact Fin.castSucc_lt_last k)
    have hIH := ih (fun k => p (Fin.castSucc k)) (fun k => q (Fin.castSucc k)) a (p last) d
      (hpa last) (fun k => hpa _) hprev (fun k => hpq _)
      (fun k l hkl => hdisj _ _ (by exact Fin.castSucc_lt_castSucc_iff.mpr hkl))
      (fun k => hd _)
    have hlastarch : d ≤ q last - p last := hd last
    have hlastb : q last ≤ b := hqb last
    push_cast
    linarith

/-- **The arch count.**  Where the Sturm expression is positive on `[a,b]`, at most `(b-a)γ/π`
pairwise disjoint positive arches of `g` fit inside. -/
theorem card_arches_le {g gd gdd h : ℝ → ℝ} {γ a b : ℝ} (hγ : 0 < γ) (hab : a ≤ b)
    (hg : ∀ t, HasDerivAt g (gd t) t) (hgd : ∀ t, HasDerivAt gd (gdd t) t)
    (hh : ∀ t, h t = gdd t + γ ^ 2 * g t)
    (hhpos : ∀ t ∈ Icc a b, 0 < h t)
    {n : ℕ} (p q : Fin n → ℝ)
    (hpa : ∀ k, a ≤ p k) (hqb : ∀ k, q k ≤ b) (hpq : ∀ k, p k < q k)
    (hgp : ∀ k, g (p k) = 0) (hgq : ∀ k, g (q k) = 0)
    (harch : ∀ k, ∀ t ∈ Ioo (p k) (q k), 0 < g t)
    (hdisj : ∀ k l : Fin n, k < l → q k ≤ p l) :
    (n : ℝ) ≤ (b - a) * γ / π := by
  have hd : ∀ k, π / γ ≤ q k - p k := fun k =>
    arch_length_ge hγ hg hgd hh hhpos (hpa k) (hqb k) (hpq k) (hgp k) (hgq k) (harch k)
  have hsum := nsmul_le_of_disjoint_intervals n p q a b (π / γ) hab hpa hqb
    (fun k => le_of_lt (hpq k)) hdisj hd
  have hpi : (0 : ℝ) < π / γ := by positivity
  rw [le_div_iff₀ Real.pi_pos]
  have hmul : (n : ℝ) * (π / γ) * γ ≤ (b - a) * γ := by
    exact mul_le_mul_of_nonneg_right hsum hγ.le
  have hrw : (n : ℝ) * (π / γ) * γ = (n : ℝ) * π := by
    field_simp
  rw [hrw] at hmul
  linarith


/-- The mirrored arch-length bound: where the Sturm expression is negative, a negative arch of `g` is
at least `π/γ` long. -/
theorem arch_length_ge_neg {g gd gdd h : ℝ → ℝ} {γ a b p q : ℝ} (hγ : 0 < γ)
    (hg : ∀ t, HasDerivAt g (gd t) t) (hgd : ∀ t, HasDerivAt gd (gdd t) t)
    (hh : ∀ t, h t = gdd t + γ ^ 2 * g t)
    (hhneg : ∀ t ∈ Icc a b, h t < 0)
    (hpa : a ≤ p) (hqb : q ≤ b) (hpq : p < q)
    (hgp : g p = 0) (hgq : g q = 0) (harch : ∀ t ∈ Ioo p q, g t < 0) :
    π / γ ≤ q - p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ξ, hξ, hval⟩ := exists_sturm_pos hγ hg hgd hh hpq hcon hgp hgq harch
  have hmem : ξ ∈ Icc a b :=
    ⟨le_trans hpa (le_of_lt hξ.1), le_trans (le_of_lt hξ.2) hqb⟩
  linarith [hhneg ξ hmem]

/-- The mirrored arch count. -/
theorem card_arches_le_neg {g gd gdd h : ℝ → ℝ} {γ a b : ℝ} (hγ : 0 < γ) (hab : a ≤ b)
    (hg : ∀ t, HasDerivAt g (gd t) t) (hgd : ∀ t, HasDerivAt gd (gdd t) t)
    (hh : ∀ t, h t = gdd t + γ ^ 2 * g t)
    (hhneg : ∀ t ∈ Icc a b, h t < 0)
    {n : ℕ} (p q : Fin n → ℝ)
    (hpa : ∀ k, a ≤ p k) (hqb : ∀ k, q k ≤ b) (hpq : ∀ k, p k < q k)
    (hgp : ∀ k, g (p k) = 0) (hgq : ∀ k, g (q k) = 0)
    (harch : ∀ k, ∀ t ∈ Ioo (p k) (q k), g t < 0)
    (hdisj : ∀ k l : Fin n, k < l → q k ≤ p l) :
    (n : ℝ) ≤ (b - a) * γ / π := by
  have hd : ∀ k, π / γ ≤ q k - p k := fun k =>
    arch_length_ge_neg hγ hg hgd hh hhneg (hpa k) (hqb k) (hpq k) (hgp k) (hgq k) (harch k)
  have hsum := nsmul_le_of_disjoint_intervals n p q a b (π / γ) hab hpa hqb
    (fun k => le_of_lt (hpq k)) hdisj hd
  rw [le_div_iff₀ Real.pi_pos]
  have hmul : (n : ℝ) * (π / γ) * γ ≤ (b - a) * γ :=
    mul_le_mul_of_nonneg_right hsum hγ.le
  have hrw : (n : ℝ) * (π / γ) * γ = (n : ℝ) * π := by field_simp
  rw [hrw] at hmul
  linarith

end GaloisForLFunctions.HTGeometry
