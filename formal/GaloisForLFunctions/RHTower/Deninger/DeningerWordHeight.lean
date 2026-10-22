import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeLogHeightKothe

/-!
# The entire word-height source

Words in the exponent lattice carry the product of the heights of their letters and their own
length.  Weighting a word by `H(w)^k (k+1)^{|w|}` produces a Köthe datum whose weights are
summable against later ones: the letterwise series `∑_m H(m)^{-α}` is bounded by `ζ(2)²` for every
`α ≥ 2`, so the word series is a geometric series whose ratio can be made smaller than one by
raising the index.

This is the topology in which a word is controlled by the *product* of its letter heights and by
every exponential length weight — the only choice for which the balanced sector, where the letters
cancel to total character zero, is still controlled.

* `deningerPi_summable_and_tsum` : the letterwise series of a fixed length is the power of the
  one-letter series.
* `DeningerWord`, `deningerWordHeight`, `deningerWordCharacter` : the index set and its data.
* `deningerWordKotheData`, `deningerWordKotheData_isNuclear` : **the entire word-height source is
  nuclear.**
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-! ## Words -/

/-- A word in the exponent lattice: a length together with a letter at each position. -/
abbrev DeningerWord : Type := Σ r : ℕ, Fin r → DeningerPrimeLattice

instance : Inhabited DeningerWord := ⟨⟨0, fun i => i.elim0⟩⟩

/-- The length of a word. -/
def deningerWordLength (w : DeningerWord) : ℕ := w.1

/-- The product of the heights of the letters of a word. -/
def deningerWordHeight (w : DeningerWord) : ℝ := ∏ j, deningerHeight (w.2 j)

/-- The total arithmetic character of a word. -/
def deningerWordCharacter (w : DeningerWord) : DeningerPrimeLattice := ∑ j, w.2 j

theorem one_le_deningerWordHeight (w : DeningerWord) : 1 ≤ deningerWordHeight w :=
  Finset.one_le_prod fun j _ => one_le_deningerHeight (w.2 j)

theorem deningerWordHeight_pos (w : DeningerWord) : 0 < deningerWordHeight w :=
  lt_of_lt_of_le zero_lt_one (one_le_deningerWordHeight w)

/-! ## The letterwise series -/

theorem deningerHeight_summable_inv_pow {α : ℕ} (hα : 2 ≤ α) :
    Summable fun m : DeningerPrimeLattice => (deningerHeight m)⁻¹ ^ α := by
  refine Summable.of_nonneg_of_le
    (fun m => pow_nonneg (inv_nonneg.mpr (deningerHeight_pos m).le) α) (fun m => ?_)
    deningerHeight_summable_inv_sq
  have h1 : (deningerHeight m)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    exact Or.inr (one_le_deningerHeight m)
  have h0 : (0 : ℝ) ≤ (deningerHeight m)⁻¹ := inv_nonneg.mpr (deningerHeight_pos m).le
  exact pow_le_pow_of_le_one h0 h1 hα

/-- The letterwise height series `∑_m H(m)^{-α}`. -/
def deningerHeightInvSum (α : ℕ) : ℝ := ∑' m : DeningerPrimeLattice, (deningerHeight m)⁻¹ ^ α

theorem one_le_deningerHeightInvSum {α : ℕ} (hα : 2 ≤ α) :
    1 ≤ deningerHeightInvSum α := by
  have hterm : (deningerHeight (0 : DeningerPrimeLattice))⁻¹ ^ α = 1 := by
    rw [deningerHeight_zero, inv_one, one_pow]
  have hle := (deningerHeight_summable_inv_pow hα).le_tsum (0 : DeningerPrimeLattice)
    (fun j _ => pow_nonneg (inv_nonneg.mpr (deningerHeight_pos j).le) α)
  rw [hterm] at hle
  exact hle

theorem deningerHeightInvSum_le {α : ℕ} (hα : 2 ≤ α) :
    deningerHeightInvSum α ≤ deningerHeightInvSum 2 := by
  refine Summable.tsum_le_tsum (fun m => ?_) (deningerHeight_summable_inv_pow hα)
    deningerHeight_summable_inv_sq
  have h1 : (deningerHeight m)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    exact Or.inr (one_le_deningerHeight m)
  have h0 : (0 : ℝ) ≤ (deningerHeight m)⁻¹ := inv_nonneg.mpr (deningerHeight_pos m).le
  exact pow_le_pow_of_le_one h0 h1 hα

/-! ## The word series -/

theorem deningerPi_summable_and_tsum {g : DeningerPrimeLattice → ℝ}
    (hg : Summable g) (hnn : ∀ m, 0 ≤ g m) (r : ℕ) :
    (Summable fun f : Fin r → DeningerPrimeLattice => ∏ j, g (f j)) ∧
      (∑' f : Fin r → DeningerPrimeLattice, ∏ j, g (f j)) = (∑' m, g m) ^ r := by
  induction r with
  | zero =>
      constructor
      · have hfun : (fun f : Fin 0 → DeningerPrimeLattice => ∏ j, g (f j))
            = fun _ => (1 : ℝ) := by
          funext f
          simp
        rw [hfun]
        exact summable_of_hasFiniteSupport (Set.toFinite _)
      · have hfun : (fun f : Fin 0 → DeningerPrimeLattice => ∏ j, g (f j))
            = fun _ => (1 : ℝ) := by
          funext f
          simp
        rw [hfun, pow_zero, tsum_eq_single default]
        · intro b hb
          exact absurd (Subsingleton.elim b default) hb
  | succ r ih =>
      obtain ⟨ihsum, ihtsum⟩ := ih
      have hprodSummable : Summable fun q : DeningerPrimeLattice × (Fin r → DeningerPrimeLattice) =>
          g q.1 * ∏ j, g (q.2 j) :=
        Summable.mul_of_nonneg (f := g)
          (g := fun f : Fin r → DeningerPrimeLattice => ∏ j, g (f j)) hg ihsum hnn
          (fun f => Finset.prod_nonneg fun j _ => hnn (f j))
      have hcons : ∀ q : DeningerPrimeLattice × (Fin r → DeningerPrimeLattice),
          (∏ j, g (Fin.consEquiv (fun _ => DeningerPrimeLattice) q j)) = g q.1 * ∏ j, g (q.2 j) := by
        intro q
        rw [Fin.prod_univ_succ]
        simp [Fin.consEquiv_apply]
      constructor
      · refine ((Fin.consEquiv (fun _ : Fin (r + 1) => DeningerPrimeLattice)).summable_iff
          (f := fun f : Fin (r + 1) → DeningerPrimeLattice => ∏ j, g (f j))).mp ?_
        refine hprodSummable.congr fun q => ?_
        exact (hcons q).symm
      · rw [← (Fin.consEquiv (fun _ : Fin (r + 1) => DeningerPrimeLattice)).tsum_eq
          (fun f : Fin (r + 1) → DeningerPrimeLattice => ∏ j, g (f j))]
        rw [tsum_congr hcons]
        have hnormg : Summable fun m => ‖g m‖ := by
          refine hg.congr fun m => ?_
          rw [Real.norm_of_nonneg (hnn m)]
        have hnormp : Summable fun f : Fin r → DeningerPrimeLattice => ‖∏ j, g (f j)‖ := by
          refine ihsum.congr fun f => ?_
          rw [Real.norm_of_nonneg (Finset.prod_nonneg fun j _ => hnn (f j))]
        rw [← tsum_mul_tsum_of_summable_norm hnormg hnormp, ihtsum, pow_succ]
        ring

theorem deningerWordPow_summable {α : ℕ} (hα : 2 ≤ α) (r : ℕ) :
    Summable fun f : Fin r → DeningerPrimeLattice =>
      ∏ j, (deningerHeight (f j))⁻¹ ^ α :=
  (deningerPi_summable_and_tsum (deningerHeight_summable_inv_pow hα)
    (fun m => pow_nonneg (inv_nonneg.mpr (deningerHeight_pos m).le) α) r).1

theorem deningerWordPow_tsum {α : ℕ} (hα : 2 ≤ α) (r : ℕ) :
    (∑' f : Fin r → DeningerPrimeLattice, ∏ j, (deningerHeight (f j))⁻¹ ^ α)
      = deningerHeightInvSum α ^ r :=
  (deningerPi_summable_and_tsum (deningerHeight_summable_inv_pow hα)
    (fun m => pow_nonneg (inv_nonneg.mpr (deningerHeight_pos m).le) α) r).2

/-! ## The word Köthe datum -/

/-- **The entire word-height Köthe datum**: the product of the letter heights raised to `k`,
times the `k`-th exponential length weight. -/
def deningerWordKotheData : DeningerKotheData DeningerWord where
  w k w := deningerWordHeight w ^ k * ((k : ℝ) + 1) ^ deningerWordLength w
  pos k w := by
    have h1 : (0 : ℝ) < deningerWordHeight w ^ k := pow_pos (deningerWordHeight_pos w) k
    have h2 : (0 : ℝ) < ((k : ℝ) + 1) ^ deningerWordLength w :=
      pow_pos (by positivity) _
    exact mul_pos h1 h2
  mono k w := by
    have h1 : deningerWordHeight w ^ k ≤ deningerWordHeight w ^ (k + 1) :=
      pow_le_pow_right₀ (one_le_deningerWordHeight w) (Nat.le_succ k)
    have h2 : ((k : ℝ) + 1) ^ deningerWordLength w
        ≤ (((k : ℝ) + 1) + 1) ^ deningerWordLength w := by
      refine pow_le_pow_left₀ (by positivity) (by linarith) _
    have h1nn : (0 : ℝ) ≤ deningerWordHeight w ^ k :=
      pow_nonneg (deningerWordHeight_pos w).le _
    have h2nn : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ deningerWordLength w :=
      pow_nonneg (by positivity) _
    have hkk : ((k : ℝ) + 1) + 1 = ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    calc deningerWordHeight w ^ k * ((k : ℝ) + 1) ^ deningerWordLength w
        ≤ deningerWordHeight w ^ (k + 1) * ((k : ℝ) + 1) ^ deningerWordLength w :=
          mul_le_mul_of_nonneg_right h1 h2nn
      _ ≤ deningerWordHeight w ^ (k + 1) * ((((k : ℝ) + 1) + 1) ^ deningerWordLength w) := by
          refine mul_le_mul_of_nonneg_left h2 ?_
          exact pow_nonneg (deningerWordHeight_pos w).le _
      _ = deningerWordHeight w ^ (k + 1) *
            (((k + 1 : ℕ) : ℝ) + 1) ^ deningerWordLength w := by rw [hkk]

@[simp]
theorem deningerWordKotheData_w (k : ℕ) (w : DeningerWord) :
    deningerWordKotheData.w k w
      = deningerWordHeight w ^ k * ((k : ℝ) + 1) ^ deningerWordLength w := rfl

/-- **The entire word-height source** -/
abbrev DeningerWordKothe : Submodule ℂ (DeningerWord → ℂ) :=
  DeningerKotheCarrier ℂ deningerWordKotheData

/-- **The entire word-height source is nuclear.**  The ratio of two word weights is a product of
letterwise inverse powers times a geometric length factor, so the whole series is geometric with
ratio below one once the later index is large enough. -/
theorem deningerWordKotheData_isNuclear : deningerWordKotheData.IsNuclear := by
  intro k
  obtain ⟨N, hN⟩ := exists_nat_gt (((k : ℝ) + 1) * deningerHeightInvSum 2)
  refine ⟨max (k + 2) N, le_trans (Nat.le_add_right k 2) (le_max_left _ _), ?_⟩
  set l := max (k + 2) N with hldef
  have hkl : k + 2 ≤ l := le_max_left _ _
  have hNl : N ≤ l := le_max_right _ _
  set α : ℕ := l - k with hαdef
  have hα : 2 ≤ α := by omega
  have hlk : l = k + α := by omega
  set c : ℝ := ((k : ℝ) + 1) / ((l : ℝ) + 1) with hcdef
  have hlpos : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  have hcnn : 0 ≤ c := by
    rw [hcdef]
    positivity
  -- the word ratio splits into a letterwise part and a geometric length part
  have hratio : ∀ w : DeningerWord,
      deningerWordKotheData.w k w / deningerWordKotheData.w l w
        = (∏ j, (deningerHeight (w.2 j))⁻¹ ^ α) * c ^ deningerWordLength w := by
    intro w
    have hHpos := deningerWordHeight_pos w
    have hsplit : (∏ j, (deningerHeight (w.2 j))⁻¹ ^ α)
        = (deningerWordHeight w)⁻¹ ^ α := by
      rw [Finset.prod_pow, Finset.prod_inv_distrib]
      rfl
    have hHne : deningerWordHeight w ≠ 0 := ne_of_gt hHpos
    have hlne : ((l : ℝ) + 1) ≠ 0 := ne_of_gt hlpos
    have hHpow : deningerWordHeight w ^ l
        = deningerWordHeight w ^ k * deningerWordHeight w ^ α := by
      rw [← pow_add, ← hlk]
    rw [deningerWordKotheData_w, deningerWordKotheData_w, hsplit, hcdef, div_pow, hHpow,
      inv_pow]
    field_simp
  -- the letterwise series
  have hfiber : ∀ r : ℕ, Summable fun f : Fin r → DeningerPrimeLattice =>
      deningerWordKotheData.w k (⟨r, f⟩ : DeningerWord) /
        deningerWordKotheData.w l (⟨r, f⟩ : DeningerWord) := by
    intro r
    refine ((deningerWordPow_summable hα r).mul_right (c ^ r)).congr fun f => ?_
    exact (hratio ⟨r, f⟩).symm
  have hfiberSum : ∀ r : ℕ,
      (∑' f : Fin r → DeningerPrimeLattice,
        deningerWordKotheData.w k (⟨r, f⟩ : DeningerWord) /
          deningerWordKotheData.w l (⟨r, f⟩ : DeningerWord))
        = (c * deningerHeightInvSum α) ^ r := by
    intro r
    have hcong : ∀ f : Fin r → DeningerPrimeLattice,
        deningerWordKotheData.w k (⟨r, f⟩ : DeningerWord) /
          deningerWordKotheData.w l (⟨r, f⟩ : DeningerWord)
          = (∏ j, (deningerHeight (f j))⁻¹ ^ α) * c ^ r := fun f => hratio ⟨r, f⟩
    rw [tsum_congr hcong,
      Summable.tsum_mul_right _ (deningerWordPow_summable hα r), deningerWordPow_tsum hα r,
      ← mul_pow, mul_comm]
  have hlt : c * deningerHeightInvSum α < 1 := by
    have hS : deningerHeightInvSum α ≤ deningerHeightInvSum 2 := deningerHeightInvSum_le hα
    have hSpos : 0 < deningerHeightInvSum 2 :=
      lt_of_lt_of_le zero_lt_one (one_le_deningerHeightInvSum (le_refl 2))
    have hstep : c * deningerHeightInvSum α ≤ c * deningerHeightInvSum 2 :=
      mul_le_mul_of_nonneg_left hS hcnn
    have hNle : ((N : ℝ)) ≤ (l : ℝ) := by exact_mod_cast hNl
    have hkey : ((k : ℝ) + 1) * deningerHeightInvSum 2 < (l : ℝ) + 1 := by
      linarith
    have hfin : c * deningerHeightInvSum 2 < 1 := by
      rw [hcdef, div_mul_eq_mul_div, div_lt_one hlpos]
      exact hkey
    linarith
  have hnn : ∀ w : DeningerWord,
      0 ≤ deningerWordKotheData.w k w / deningerWordKotheData.w l w := fun w =>
    le_of_lt (div_pos (deningerWordKotheData.pos k w) (deningerWordKotheData.pos l w))
  refine (summable_sigma_of_nonneg hnn).mpr ⟨hfiber, ?_⟩
  refine (summable_geometric_of_lt_one
    (mul_nonneg hcnn (le_trans zero_le_one (one_le_deningerHeightInvSum hα))) hlt).congr
    fun r => ?_
  exact (hfiberSum r).symm

/-- The `k`-th seminorm of the entire word-height source. -/
def deningerWordSeminorm (k : ℕ) : Seminorm ℂ DeningerWordKothe :=
  deningerKotheSeminorm deningerWordKotheData k

theorem deningerWordSeminorm_apply (k : ℕ) (a : DeningerWordKothe) :
    deningerWordSeminorm k a
      = ∑' w, deningerWordKotheData.w k w * ‖(a : DeningerWord → ℂ) w‖ := rfl

end

end RHTower
