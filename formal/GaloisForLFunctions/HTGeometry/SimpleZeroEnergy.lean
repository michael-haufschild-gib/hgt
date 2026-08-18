import GaloisForLFunctions.HTGeometry.ZeroSetCount

/-!
# Simple zeros from the energy, and the count they carry

Where the Sturm expression `h = f'' + γ² f` merely *vanishes* the sign arguments of `ZeroCountSturm`
break down: `not_isLocalMax_of_sturm_pos` needs `h > 0`, so nothing forbids two adjacent negative
arches and the alternation is lost.  Conservation of energy replaces it.

On a solution of `f'' + γ² f = 0` the energy `E = f'² + γ² f²` satisfies `E' = 2f'(f'' + γ²f) = 0`,
so it is constant.  At a zero of `f` the energy is `f'²`; if that vanished the energy would be zero
everywhere and `f` identically zero.  A nonzero solution therefore has only *simple* zeros, and a
simple zero cannot be a local maximum, which is exactly the input the arch alternation needs.

The arch-length bound itself already holds under `0 ≤ h`: the comparison produces a point where the
Sturm expression is strictly negative, and nonnegativity contradicts that.  So the whole count goes
through on an interval where `f'' + γ² f` vanishes identically.
-/

open Set Filter Real

namespace GaloisForLFunctions.HTGeometry

/-! ## Energy conservation -/

/-- The energy of a solution of `f'' + γ² f = 0`. -/
noncomputable def sturmEnergy (f fd : ℝ → ℝ) (γ : ℝ) : ℝ → ℝ :=
  fun t => fd t ^ 2 + γ ^ 2 * f t ^ 2

theorem hasDerivAt_sturmEnergy {f fd fdd : ℝ → ℝ} {γ : ℝ}
    (hf : ∀ t, HasDerivAt f (fd t) t) (hfd : ∀ t, HasDerivAt fd (fdd t) t) (t : ℝ) :
    HasDerivAt (sturmEnergy f fd γ) (2 * fd t * (fdd t + γ ^ 2 * f t)) t := by
  have h1 : HasDerivAt (fun s => fd s ^ 2) (2 * fd t ^ 1 * fdd t) t := (hfd t).pow 2
  have h2 : HasDerivAt (fun s => γ ^ 2 * f s ^ 2) (γ ^ 2 * (2 * f t ^ 1 * fd t)) t :=
    ((hf t).pow 2).const_mul _
  have heq : 2 * fd t ^ 1 * fdd t + γ ^ 2 * (2 * f t ^ 1 * fd t)
      = 2 * fd t * (fdd t + γ ^ 2 * f t) := by ring
  have h3 := h1.add h2
  rw [heq] at h3
  exact h3

/-- **Energy conservation.**  On a solution of `f'' + γ² f = 0` the energy `f'² + γ² f²` is
constant. -/
theorem sturmEnergy_const {f fd fdd : ℝ → ℝ} {γ : ℝ}
    (hf : ∀ t, HasDerivAt f (fd t) t) (hfd : ∀ t, HasDerivAt fd (fdd t) t)
    (hzero : ∀ t, fdd t + γ ^ 2 * f t = 0) (s t : ℝ) :
    sturmEnergy f fd γ s = sturmEnergy f fd γ t := by
  refine is_const_of_deriv_eq_zero
    (fun x => (hasDerivAt_sturmEnergy hf hfd x).differentiableAt) (fun x => ?_) s t
  rw [(hasDerivAt_sturmEnergy hf hfd x).deriv, hzero x, mul_zero]

/-- **Simple zeros.**  A solution of `f'' + γ² f = 0` which is somewhere nonzero has only simple
zeros: at a zero the energy is `f'²`, and if that vanished the constant energy would be zero
everywhere, forcing `f ≡ 0`. -/
theorem deriv_ne_zero_of_sturm_zero {f fd fdd : ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hf : ∀ t, HasDerivAt f (fd t) t) (hfd : ∀ t, HasDerivAt fd (fdd t) t)
    (hzero : ∀ t, fdd t + γ ^ 2 * f t = 0) {t₁ : ℝ} (hne : f t₁ ≠ 0)
    {t : ℝ} (hz : f t = 0) : fd t ≠ 0 := by
  intro hcon
  have hE : sturmEnergy f fd γ t = 0 := by
    rw [sturmEnergy, hcon, hz]; ring
  have hE1 := sturmEnergy_const hf hfd hzero t₁ t
  rw [hE, sturmEnergy] at hE1
  have hsq : (0 : ℝ) ≤ fd t₁ ^ 2 := sq_nonneg _
  have hγ2 : (0 : ℝ) < γ ^ 2 := by positivity
  have hf2 : (0 : ℝ) ≤ f t₁ ^ 2 := sq_nonneg _
  have h3 : f t₁ ^ 2 = 0 := by nlinarith
  exact hne (sq_eq_zero_iff.mp h3)

/-! ## Alternation from simplicity -/

/-- **Adjacent negative arches are impossible at a simple zero.**  The shared zero would be a local
maximum of `f`, and the derivative vanishes at a local maximum. -/
theorem not_two_negative_arches_of_simple {f fd : ℝ → ℝ} {p m q : ℝ}
    (hf : ∀ t, HasDerivAt f (fd t) t) (hsimple : fd m ≠ 0) (hz : f m = 0)
    (hpm : p < m) (hmq : m < q)
    (h1 : ∀ s ∈ Ioo p m, f s < 0) (h2 : ∀ s ∈ Ioo m q, f s < 0) : False := by
  refine hsimple (IsLocalMax.hasDerivAt_eq_zero ?_ (hf m))
  refine Filter.eventually_of_mem
    (isOpen_Ioo.mem_nhds (show m ∈ Ioo p q from ⟨hpm, hmq⟩)) (fun s hs => ?_)
  rw [hz]
  rcases lt_trichotomy s m with hlt | heq | hgt
  · exact le_of_lt (h1 s ⟨hs.1, hlt⟩)
  · rw [heq, hz]
  · exact le_of_lt (h2 s ⟨hgt, hs.2⟩)

/-! ## The count under nonnegativity plus simplicity -/

/-- **The zero count with simple zeros.**  Where `f'' + γ² f ≥ 0` on `[a,b]` and every zero of `f`
there is simple, consecutive zeros number at most `2(b-a)γ/π + 2`.  Simplicity replaces the strict
positivity of the Sturm expression as the source of arch alternation. -/
theorem zero_count_le_of_simple {f fd fdd h : ℝ → ℝ} {γ a b : ℝ} (hγ : 0 < γ) (hab : a ≤ b)
    (hf : ∀ t, HasDerivAt f (fd t) t) (hfd : ∀ t, HasDerivAt fd (fdd t) t)
    (hh : ∀ t, h t = fdd t + γ ^ 2 * f t)
    (hhnn : ∀ t ∈ Ioo a b, 0 ≤ h t)
    (hsimple : ∀ t ∈ Icc a b, f t = 0 → fd t ≠ 0)
    {n : ℕ} (t : ℕ → ℝ)
    (hmono : ∀ i j, i < j → j ≤ n → t i < t j)
    (hmem : ∀ i, i ≤ n → t i ∈ Icc a b)
    (hzero : ∀ i, i ≤ n → f (t i) = 0)
    (hgapfree : ∀ i, i < n → ∀ s ∈ Ioo (t i) (t (i + 1)), f s ≠ 0) :
    (n : ℝ) ≤ 2 * ((b - a) * γ / π) + 1 := by
  classical
  have hcont : Continuous f :=
    continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hsign : ∀ i, i < n → (∀ s ∈ Ioo (t i) (t (i + 1)), 0 < f s)
      ∨ (∀ s ∈ Ioo (t i) (t (i + 1)), f s < 0) :=
    fun i hi => sign_constant_of_no_zero hcont (hgapfree i hi)
  set k : ℕ := n / 2 with hk
  have hbound : ∀ j : Fin k, 2 * (j : ℕ) + 1 < n := by
    intro j
    have := j.2
    omega
  set σ : Fin k → ℕ := fun j =>
    if (∀ s ∈ Ioo (t (2 * (j : ℕ))) (t (2 * (j : ℕ) + 1)), 0 < f s) then 2 * (j : ℕ)
    else 2 * (j : ℕ) + 1 with hσ
  have hσlb : ∀ j : Fin k, 2 * (j : ℕ) ≤ σ j := by
    intro j
    simp only [hσ]
    split <;> omega
  have hσub : ∀ j : Fin k, σ j ≤ 2 * (j : ℕ) + 1 := by
    intro j
    simp only [hσ]
    split <;> omega
  have hσn : ∀ j : Fin k, σ j < n := fun j => lt_of_le_of_lt (hσub j) (by
    have := hbound j
    omega)
  have hσpos : ∀ j : Fin k, ∀ s ∈ Ioo (t (σ j)) (t (σ j + 1)), 0 < f s := by
    intro j
    simp only [hσ]
    split
    · rename_i hcase
      exact hcase
    · rename_i hcase
      have hlow : ∀ s ∈ Ioo (t (2 * (j : ℕ))) (t (2 * (j : ℕ) + 1)), f s < 0 := by
        rcases hsign (2 * (j : ℕ)) (by have := hbound j; omega) with hp | hn
        · exact absurd hp hcase
        · exact hn
      rcases hsign (2 * (j : ℕ) + 1) (hbound j) with hp | hn
      · exact hp
      · exfalso
        refine not_two_negative_arches_of_simple hf ?_ (hzero _ (by have := hbound j; omega))
          (hmono _ _ (by omega) (by have := hbound j; omega))
          (hmono _ _ (by omega) (by have := hbound j; omega)) hlow hn
        exact hsimple _ (hmem _ (by have := hbound j; omega))
          (hzero _ (by have := hbound j; omega))
  have hle : ∀ i j : ℕ, i ≤ j → j ≤ n → t i ≤ t j := by
    intro i j hij hjn
    rcases lt_or_eq_of_le hij with h1 | h1
    · exact le_of_lt (hmono i j h1 hjn)
    · rw [h1]
  have hcount := card_arches_le (g := f) (gd := fd) (gdd := fdd) (h := h) hγ hab hf hfd hh hhnn
    (fun j : Fin k => t (σ j)) (fun j : Fin k => t (σ j + 1))
    (fun j => (hmem _ (le_of_lt (hσn j))).1)
    (fun j => (hmem _ (hσn j)).2)
    (fun j => hmono _ _ (by omega) (hσn j))
    (fun j => hzero _ (le_of_lt (hσn j)))
    (fun j => hzero _ (hσn j))
    (fun j => hσpos j)
    (fun i j hij => by
      refine hle _ _ ?_ (le_of_lt (hσn j))
      have h1 := hσub i
      have h2 := hσlb j
      have h3 : (i : ℕ) < (j : ℕ) := hij
      omega)
  have hnk : (n : ℝ) ≤ 2 * (k : ℝ) + 1 := by
    have : n ≤ 2 * k + 1 := by rw [hk]; omega
    exact_mod_cast this
  linarith

/-- The zero-set form: enumerating the finite zero set in increasing order supplies the
gap-freeness hypothesis. -/
theorem card_zeros_le_of_simple {f fd fdd h : ℝ → ℝ} {γ a b : ℝ} (hγ : 0 < γ) (hab : a ≤ b)
    (hf : ∀ t, HasDerivAt f (fd t) t) (hfd : ∀ t, HasDerivAt fd (fdd t) t)
    (hh : ∀ t, h t = fdd t + γ ^ 2 * f t)
    (hhnn : ∀ t ∈ Ioo a b, 0 ≤ h t)
    (hsimple : ∀ t ∈ Icc a b, f t = 0 → fd t ≠ 0)
    (Z : Finset ℝ) (hZmem : ∀ x ∈ Z, x ∈ Icc a b) (hZzero : ∀ x ∈ Z, f x = 0)
    (hZall : ∀ x ∈ Icc a b, f x = 0 → x ∈ Z) :
    (Z.card : ℝ) ≤ 2 * ((b - a) * γ / π) + 2 := by
  have hnn : (0 : ℝ) ≤ (b - a) * γ / π := by
    have h1 : (0 : ℝ) ≤ b - a := by linarith
    exact div_nonneg (mul_nonneg h1 hγ.le) Real.pi_pos.le
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Z.card = m := ⟨Z.card, rfl⟩
  match m, hm with
  | 0, hm =>
    rw [hm]
    simp only [Nat.cast_zero]
    linarith
  | (n + 1), hm =>
    set e : Fin (n + 1) ↪o ℝ := Z.orderEmbOfFin hm with he
    set t : ℕ → ℝ := fun i => if hi : i < n + 1 then e ⟨i, hi⟩ else 0 with ht
    have hteq : ∀ i (hi : i < n + 1), t i = e ⟨i, hi⟩ := by
      intro i hi
      rw [ht]
      simp [hi]
    have hmono : ∀ i j, i < j → j ≤ n → t i < t j := by
      intro i j hij hjn
      rw [hteq i (by omega), hteq j (by omega)]
      exact (OrderEmbedding.lt_iff_lt e).mpr (by exact hij)
    have hmemZ : ∀ i, i ≤ n → t i ∈ Z := by
      intro i hi
      rw [hteq i (by omega)]
      exact Z.orderEmbOfFin_mem hm _
    have hmem : ∀ i, i ≤ n → t i ∈ Icc a b := fun i hi => hZmem _ (hmemZ i hi)
    have hzero : ∀ i, i ≤ n → f (t i) = 0 := fun i hi => hZzero _ (hmemZ i hi)
    have hgapfree : ∀ i, i < n → ∀ s ∈ Ioo (t i) (t (i + 1)), f s ≠ 0 := by
      intro i hi s hs hfs
      have hsab : s ∈ Icc a b := by
        refine ⟨le_trans (hmem i (by omega)).1 (le_of_lt hs.1),
          le_trans (le_of_lt hs.2) (hmem (i + 1) (by omega)).2⟩
      have hsZ : s ∈ Z := hZall s hsab hfs
      have hrange : s ∈ Set.range (e : Fin (n + 1) → ℝ) := by
        rw [Z.range_orderEmbOfFin hm]
        exact hsZ
      obtain ⟨j, hj⟩ := hrange
      have h1 : e ⟨i, by omega⟩ < e j := by
        rw [hj, ← hteq i (by omega)]
        exact hs.1
      have h2 : e j < e ⟨i + 1, by omega⟩ := by
        rw [hj, ← hteq (i + 1) (by omega)]
        exact hs.2
      have h1' : (⟨i, by omega⟩ : Fin (n + 1)) < j := (OrderEmbedding.lt_iff_lt e).mp h1
      have h2' : j < (⟨i + 1, by omega⟩ : Fin (n + 1)) := (OrderEmbedding.lt_iff_lt e).mp h2
      have : (i : ℕ) < (j : ℕ) := h1'
      have : (j : ℕ) < i + 1 := h2'
      omega
    have hcount := zero_count_le_of_simple hγ hab hf hfd hh hhnn hsimple t hmono hmem hzero hgapfree
    rw [hm]
    push_cast
    linarith

/-- **The degenerate count.**  A solution of `f'' + γ² f = 0` which is somewhere nonzero has at most
`2(b-a)γ/π + 2` zeros in `[a,b]`.  This is the branch of the exponential-polynomial descent on which
the Sturm expression vanishes identically, so that no finite set carries its zeros. -/
theorem card_zeros_le_of_sturm_zero {f fd fdd : ℝ → ℝ} {γ a b : ℝ} (hγ : 0 < γ) (hab : a ≤ b)
    (hf : ∀ t, HasDerivAt f (fd t) t) (hfd : ∀ t, HasDerivAt fd (fdd t) t)
    (hzero : ∀ t, fdd t + γ ^ 2 * f t = 0) {t₁ : ℝ} (hne : f t₁ ≠ 0)
    (Z : Finset ℝ) (hZmem : ∀ x ∈ Z, x ∈ Icc a b) (hZzero : ∀ x ∈ Z, f x = 0)
    (hZall : ∀ x ∈ Icc a b, f x = 0 → x ∈ Z) :
    (Z.card : ℝ) ≤ 2 * ((b - a) * γ / π) + 2 :=
  card_zeros_le_of_simple (h := fun t => fdd t + γ ^ 2 * f t) hγ hab hf hfd (fun _ => rfl)
    (fun s _ => (hzero s).ge)
    (fun _ _ hs => deriv_ne_zero_of_sturm_zero hγ hf hfd hzero hne hs)
    Z hZmem hZzero hZall

end GaloisForLFunctions.HTGeometry
